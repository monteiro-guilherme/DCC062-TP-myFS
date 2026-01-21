/*
* myfs.c - Implementacao do sistema de arquivos MyFS
*
* Autor: Guilherme Monteiro / 202165562c , Gustavo Baldutti 202165566c
* Projeto: Trabalho Pratico II - Sistemas Operacionais
* Organizacao: Universidade Federal de Juiz de Fora
* Departamento: Dep. Ciencia da Computacao
*
*/

/*
Execução:
gcc main.c myfs.c vfs.c inode.c disk.c util.c -o myfs_sim -w
./myfs_sim 
ou 
./myfs_sim.exe
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "myfs.h"
#include "vfs.h"
#include "inode.h"
#include "util.h"

// --- Definições e Estruturas Internas ---

// Assinatura hexadecimal para validar se o disco pertence ao MyFS
#define MYFS_MAGIC 0xCAFEBABE

// Localizacao fisica do Superbloco (setor 1, pois o 0 eh boot)
#define SUPERBLOCK_SECTOR 1

// Setor onde se inicia a tabela de Inodes (logo apos o superbloco)
#define INODE_AREA_START 2

// Quantidade maxima de arquivos/diretorios suportados pelo disco
#define NUM_INODES 256

// ID fixo para o diretorio raiz "/" (convencao)
#define ROOT_INODE_NUMBER 1

// Limite de descritores de arquivos abertos na memoria (tabela openFiles)
#define MAX_OPEN_FILES 20

// Tamanho maximo do nome de um arquivo (bytes)
#define DIR_ENTRY_NAME_LEN 60

// Estrutura do Superbloco: contem os metadados globais do sistema de arquivos
typedef struct {
    unsigned int magic;           // Numero magico para identificacao
    unsigned int blockSize;       // Tamanho do bloco (setor)
    unsigned int numBlocks;       // Total de blocos no disco
    unsigned int numInodes;       // Total de inodes suportados
    unsigned int freeMapSector;   // Setor onde inicia o bitmap de livres
    unsigned int firstDataSector; // Primeiro setor da area de dados
} SuperBlock;

// Estrutura de Entrada de Diretório: mapeia nome do arquivo para numero de inode
typedef struct {
    unsigned int inode;           // Numero do inode (0 se livre)
    char name[DIR_ENTRY_NAME_LEN];// Nome do arquivo
} DirEntry;

// Descritor de Arquivo em Memória: mantem o estado de arquivos abertos
typedef struct {
    int isUsed;                   // Flag se o descritor esta em uso
    int inodeNum;                 // Inode associado
    unsigned int cursor;          // Posicao atual de leitura/escrita
    int type;                     // Tipo do arquivo (Regular ou Diretorio)
} FileHandle;

// --- Variáveis Globais ---

static FileHandle openFiles[MAX_OPEN_FILES]; // Tabela de arquivos abertos
static SuperBlock sbCache;                   // Cache do superbloco em memoria
static int isMounted = 0;                    // Flag de montagem
static Disk *mountedDisk = NULL;             // Ponteiro para o disco montado

// --- Funções Auxiliares Internas ---

// Carrega o superbloco do setor 1 do disco para a memoria (cache)
static int __loadSuperBlock(Disk *d) {
    unsigned char buffer[DISK_SECTORDATASIZE];
    if (diskReadSector(d, SUPERBLOCK_SECTOR, buffer) < 0) return -1;
    
    unsigned int *p = (unsigned int*)buffer;
    sbCache.magic = p[0];
    sbCache.blockSize = p[1];
    sbCache.numBlocks = p[2];
    sbCache.numInodes = p[3];
    sbCache.freeMapSector = p[4];
    sbCache.firstDataSector = p[5];
    return 0;
}

// Salva o superbloco da memoria (cache) para o setor 1 do disco
static int __saveSuperBlock(Disk *d) {
    unsigned char buffer[DISK_SECTORDATASIZE];
    memset(buffer, 0, DISK_SECTORDATASIZE);
    unsigned int *p = (unsigned int*)buffer;
    
    p[0] = sbCache.magic;
    p[1] = sbCache.blockSize;
    p[2] = sbCache.numBlocks;
    p[3] = sbCache.numInodes;
    p[4] = sbCache.freeMapSector;
    p[5] = sbCache.firstDataSector;
    
    return diskWriteSector(d, SUPERBLOCK_SECTOR, buffer);
}

// Percorre o bitmap para encontrar e alocar um bloco livre. Retorna o numero do bloco ou 0 se cheio.
static unsigned int __allocBlock(Disk *d) {
    unsigned char buffer[DISK_SECTORDATASIZE];
    if (diskReadSector(d, sbCache.freeMapSector, buffer) < 0) return 0;
    
    unsigned int totalMapBytes = (sbCache.numBlocks + 7) / 8;
    if (totalMapBytes > DISK_SECTORDATASIZE) totalMapBytes = DISK_SECTORDATASIZE;

    // Varre byte a byte, bit a bit procurando por 0
    for (int i = 0; i < totalMapBytes; i++) {
        if (buffer[i] != 0xFF) {
            for (int bit = 0; bit < 8; bit++) {
                if (!((buffer[i] >> bit) & 1)) {
                    unsigned int blockNum = i * 8 + bit;
                    // Protecao para nao alocar areas reservadas
                    if (blockNum < sbCache.firstDataSector) continue;
                    if (blockNum >= sbCache.numBlocks) return 0;

                    // Marca como ocupado (1) e salva
                    buffer[i] |= (1 << bit);
                    diskWriteSector(d, sbCache.freeMapSector, buffer);
                    return blockNum;
                }
            }
        }
    }
    return 0;
}

// Libera um bloco especifico no bitmap (marca como 0)
static void __freeBlock(Disk *d, unsigned int blockNum) {
    unsigned char buffer[DISK_SECTORDATASIZE];
    if (diskReadSector(d, sbCache.freeMapSector, buffer) < 0) return;
    
    int byteIndex = blockNum / 8;
    int bitIndex = blockNum % 8;
    
    buffer[byteIndex] &= ~(1 << bitIndex);
    diskWriteSector(d, sbCache.freeMapSector, buffer);
}

// Busca um arquivo pelo nome dentro de um diretorio (identificado pelo inode do diretorio)
static unsigned int __findFileInDir(Disk *d, unsigned int dirInodeNum, const char *name) {
    Inode *dir = inodeLoad(dirInodeNum, d);
    if (!dir) return 0;

    unsigned char buffer[DISK_SECTORDATASIZE];
    unsigned int fileSize = inodeGetFileSize(dir);
    unsigned int numBlocks = (fileSize + DISK_SECTORDATASIZE - 1) / DISK_SECTORDATASIZE;

    // Varre todos os blocos do diretorio
    for (unsigned int i = 0; i < numBlocks; i++) {
        unsigned int blockAddr = inodeGetBlockAddr(dir, i);
        if (blockAddr == 0) continue;
        
        diskReadSector(d, blockAddr, buffer);
        DirEntry *entries = (DirEntry*)buffer;
        
        // Varre as entradas dentro do bloco
        for (int j = 0; j < DISK_SECTORDATASIZE / sizeof(DirEntry); j++) {
            if (entries[j].inode != 0 && strcmp(entries[j].name, name) == 0) {
                free(dir);
                return entries[j].inode;
            }
        }
    }
    free(dir);
    return 0;
}

// Adiciona uma nova entrada (nome, inode) no diretorio raiz
static int __addDirEntry(Disk *d, const char *name, unsigned int inodeNum) {
    Inode *root = inodeLoad(ROOT_INODE_NUMBER, d);
    if (!root) return -1;

    unsigned char buffer[DISK_SECTORDATASIZE];
    unsigned int fileSize = inodeGetFileSize(root);
    unsigned int numBlocks = (fileSize + DISK_SECTORDATASIZE - 1) / DISK_SECTORDATASIZE;

    // Tenta encontrar um espaco vazio (inode == 0) nos blocos existentes
    for (unsigned int i = 0; i < numBlocks; i++) {
        unsigned int blockAddr = inodeGetBlockAddr(root, i);
        if (diskReadSector(d, blockAddr, buffer) < 0) continue;
        
        DirEntry *entries = (DirEntry*)buffer;
        for (int j = 0; j < DISK_SECTORDATASIZE / sizeof(DirEntry); j++) {
            if (entries[j].inode == 0) {
                entries[j].inode = inodeNum;
                strncpy(entries[j].name, name, DIR_ENTRY_NAME_LEN);
                diskWriteSector(d, blockAddr, buffer);
                free(root);
                return 0;
            }
        }
    }

    // Se nao achou espaco, aloca um novo bloco para o diretorio
    unsigned int newBlock = __allocBlock(d);
    if (newBlock == 0) {
        free(root);
        return -1;
    }
    
    memset(buffer, 0, DISK_SECTORDATASIZE);
    DirEntry *entries = (DirEntry*)buffer;
    entries[0].inode = inodeNum;
    strncpy(entries[0].name, name, DIR_ENTRY_NAME_LEN);
    
    if (diskWriteSector(d, newBlock, buffer) < 0) {
        free(root);
        return -1;
    }

    if (inodeAddBlock(root, newBlock) < 0) {
        __freeBlock(d, newBlock);
        free(root);
        return -1;
    }

    inodeSetFileSize(root, (numBlocks + 1) * DISK_SECTORDATASIZE);
    inodeSave(root);
    free(root);
    return 0;
}

// --- Implementação da API myFS ---

// Funcao para verificacao se o sistema de arquivos está ocioso
int myFSIsIdle (Disk *d) {
    for (int i = 0; i < MAX_OPEN_FILES; i++) {
        if (openFiles[i].isUsed) return 0;
    }
    return 1;
}

// Funcao para formatacao de um disco: limpa inodes, cria superbloco e inicializa bitmap
int myFSFormat (Disk *d, unsigned int blockSize) {
    unsigned long totalSectors = diskGetNumSectors(d);
    if (totalSectors < 100) return -1;

    // Calculo da area de inodes
    unsigned int inodesPerSector = DISK_SECTORDATASIZE / (sizeof(unsigned int) * 16);
    unsigned int sectorsForInodes = (NUM_INODES + inodesPerSector - 1) / inodesPerSector;
    
    unsigned int freeMapSector = INODE_AREA_START + sectorsForInodes;
    unsigned int firstDataSector = freeMapSector + 1;

    if (firstDataSector >= totalSectors) return -1;

    // 1. Limpar área de Inodes
    unsigned char zeros[DISK_SECTORDATASIZE];
    memset(zeros, 0, DISK_SECTORDATASIZE);
    for (unsigned int i = INODE_AREA_START; i < firstDataSector; i++) {
        diskWriteSector(d, i, zeros);
    }

    // 2. Criar e Salvar SuperBlock
    sbCache.magic = MYFS_MAGIC;
    sbCache.blockSize = DISK_SECTORDATASIZE;
    sbCache.numBlocks = totalSectors;
    sbCache.numInodes = NUM_INODES;
    sbCache.freeMapSector = freeMapSector;
    sbCache.firstDataSector = firstDataSector;
    
    if (__saveSuperBlock(d) < 0) return -1;

    // 3. Inicializar Bitmap (marcando metadados como ocupados)
    memset(zeros, 0, DISK_SECTORDATASIZE);
    for (unsigned int i = 0; i < firstDataSector; i++) {
        int byteIndex = i / 8;
        int bitIndex = i % 8;
        if (byteIndex < DISK_SECTORDATASIZE)
            zeros[byteIndex] |= (1 << bitIndex);
    }
    diskWriteSector(d, freeMapSector, zeros);

    // 4. Inicializar TODOS os Inodes com seus numeros
    for (unsigned int i = 1; i <= NUM_INODES; i++) {
        Inode *in = inodeCreate(i, d); 
        if (i == ROOT_INODE_NUMBER) {
            inodeSetFileType(in, FILETYPE_DIR);
            inodeSetOwner(in, 1000);
            inodeSetFileSize(in, 0);
        }
        inodeSave(in); 
        free(in);
    }

    return totalSectors - firstDataSector; 
}

// Funcao para montagem (carrega superbloco) e desmontagem (limpa cache)
int myFSxMount (Disk *d, int x) {
    if (x == 1) { // Mount
        if (__loadSuperBlock(d) < 0) return 0;
        if (sbCache.magic != MYFS_MAGIC) return 0;
        
        for (int i = 0; i < MAX_OPEN_FILES; i++) openFiles[i].isUsed = 0;
        
        mountedDisk = d; 
        isMounted = 1;
        return 1;
    } else { // Unmount
        if (!myFSIsIdle(d)) return 0;
        isMounted = 0;
        mountedDisk = NULL;
        return 1;
    }
}

// Funcao para abertura de um arquivo. Se nao existir, cria.
int myFSOpen (Disk *d, const char *path) {
    if (!isMounted) return -1;
    const char *name = path;
    if (name[0] == '/') name++;
    if (strlen(name) == 0 || strchr(name, '/')) return -1;

    unsigned int inodeNum = __findFileInDir(d, ROOT_INODE_NUMBER, name);
    
    // Cria arquivo se não existir
    if (inodeNum == 0) {
        inodeNum = inodeFindFreeInode(2, d);
        if (inodeNum == 0) return -1;
        
        Inode *newFile = inodeCreate(inodeNum, d);
        if (!newFile) return -1;
        inodeSetFileType(newFile, FILETYPE_REGULAR);
        inodeSetFileSize(newFile, 0);
        inodeSetRefCount(newFile, 1);
        inodeSave(newFile);
        free(newFile);

        if (__addDirEntry(d, name, inodeNum) < 0) return -1;
    }

    // Busca descritor livre na tabela de arquivos abertos
    int fd = -1;
    for (int i = 0; i < MAX_OPEN_FILES; i++) {
        if (!openFiles[i].isUsed) {
            fd = i + 1;
            openFiles[i].isUsed = 1;
            openFiles[i].inodeNum = inodeNum;
            openFiles[i].cursor = 0;
            openFiles[i].type = FILETYPE_REGULAR;
            break;
        }
    }
    return fd;
}

// Funcao para leitura de arquivo a partir da posicao do cursor
int myFSRead (int fd, char *buf, unsigned int nbytes) {
    if (!isMounted || !mountedDisk) return -1;
    if (fd < 1 || fd > MAX_OPEN_FILES || !openFiles[fd-1].isUsed) return -1;
    FileHandle *fh = &openFiles[fd-1];
    if (fh->type != FILETYPE_REGULAR) return -1;

    Inode *inode = inodeLoad(fh->inodeNum, mountedDisk); 
    if (!inode) return -1;

    unsigned int fileSize = inodeGetFileSize(inode);
    if (fh->cursor >= fileSize) {
        free(inode);
        return 0; // EOF
    }

    if (fh->cursor + nbytes > fileSize) nbytes = fileSize - fh->cursor;

    unsigned int bytesRead = 0;
    unsigned char sectorBuf[DISK_SECTORDATASIZE];

    // Loop de leitura bloco a bloco
    while (bytesRead < nbytes) {
        unsigned int blockIndex = (fh->cursor + bytesRead) / DISK_SECTORDATASIZE;
        unsigned int offset = (fh->cursor + bytesRead) % DISK_SECTORDATASIZE;
        unsigned int toCopy = DISK_SECTORDATASIZE - offset;
        if (toCopy > (nbytes - bytesRead)) toCopy = (nbytes - bytesRead);

        unsigned int blockAddr = inodeGetBlockAddr(inode, blockIndex);
        if (blockAddr == 0) {
            memset(sectorBuf, 0, DISK_SECTORDATASIZE);
        } else {
            diskReadSector(mountedDisk, blockAddr, sectorBuf);
        }

        memcpy(buf + bytesRead, sectorBuf + offset, toCopy);
        bytesRead += toCopy;
    }

    fh->cursor += bytesRead;
    free(inode);
    return bytesRead;
}

// Funcao para escrita em arquivo, alocando novos blocos se necessario
int myFSWrite (int fd, const char *buf, unsigned int nbytes) {
    if (!isMounted || !mountedDisk) return -1;
    if (fd < 1 || fd > MAX_OPEN_FILES || !openFiles[fd-1].isUsed) return -1;
    FileHandle *fh = &openFiles[fd-1];
    if (fh->type != FILETYPE_REGULAR) return -1;

    Inode *inode = inodeLoad(fh->inodeNum, mountedDisk);
    if (!inode) return -1;

    unsigned int bytesWritten = 0;
    unsigned char sectorBuf[DISK_SECTORDATASIZE];

    // Loop de escrita bloco a bloco
    while (bytesWritten < nbytes) {
        unsigned int currentPos = fh->cursor + bytesWritten;
        unsigned int blockIndex = currentPos / DISK_SECTORDATASIZE;
        unsigned int offset = currentPos % DISK_SECTORDATASIZE;
        unsigned int toCopy = DISK_SECTORDATASIZE - offset;
        if (toCopy > (nbytes - bytesWritten)) toCopy = (nbytes - bytesWritten);

        unsigned int blockAddr = inodeGetBlockAddr(inode, blockIndex);
        
        // Se bloco nao existe, aloca novo
        if (blockAddr == 0) {
            blockAddr = __allocBlock(mountedDisk);
            if (blockAddr == 0) break;
            memset(sectorBuf, 0, DISK_SECTORDATASIZE);
            if (inodeAddBlock(inode, blockAddr) < 0) {
                __freeBlock(mountedDisk, blockAddr);
                break;
            }
        } else {
            // Se escrita parcial, le o bloco antes de modificar
            if (toCopy < DISK_SECTORDATASIZE) {
                diskReadSector(mountedDisk, blockAddr, sectorBuf);
            }
        }

        memcpy(sectorBuf + offset, buf + bytesWritten, toCopy);
        diskWriteSector(mountedDisk, blockAddr, sectorBuf);

        bytesWritten += toCopy;
    }

    // Atualiza tamanho do arquivo se cresceu
    fh->cursor += bytesWritten;
    if (fh->cursor > inodeGetFileSize(inode)) {
        inodeSetFileSize(inode, fh->cursor);
        inodeSave(inode);
    }
    
    free(inode);
    return bytesWritten == 0 && nbytes > 0 ? -1 : bytesWritten;
}

// Funcao para fechar arquivo (libera descritor)
int myFSClose (int fd) {
    if (fd < 1 || fd > MAX_OPEN_FILES) return -1;
    if (openFiles[fd-1].isUsed) {
        openFiles[fd-1].isUsed = 0;
        return 0;
    }
    return -1;
}

// Funcao para abrir o diretorio raiz (unico suportado)
int myFSOpenDir (Disk *d, const char *path) {
    if (!isMounted) return -1;
    const char *name = path;
    if (name[0] == '/') name++;
    
    // Suporta apenas raiz (string vazia ou apenas /)
    if (strlen(name) > 0) return -1;

    int fd = -1;
    for (int i = 0; i < MAX_OPEN_FILES; i++) {
        if (!openFiles[i].isUsed) {
            fd = i + 1;
            openFiles[i].isUsed = 1;
            openFiles[i].inodeNum = ROOT_INODE_NUMBER;
            openFiles[i].cursor = 0;
            openFiles[i].type = FILETYPE_DIR;
            break;
        }
    }
    return fd;
}

// Funcao para ler entradas do diretorio sequencialmente
int myFSReadDir (int fd, char *filename, unsigned int *inumber) {
    if (!isMounted || !mountedDisk) return -1;
    if (fd < 1 || fd > MAX_OPEN_FILES || !openFiles[fd-1].isUsed) return -1;
    FileHandle *fh = &openFiles[fd-1];
    if (fh->type != FILETYPE_DIR) return -1;

    Inode *dir = inodeLoad(fh->inodeNum, mountedDisk);
    if (!dir) return -1;

    unsigned char buffer[DISK_SECTORDATASIZE];
    unsigned int fileSize = inodeGetFileSize(dir);
    
    // Itera sobre as entradas do diretorio
    while (fh->cursor < fileSize) {
        unsigned int blockIndex = fh->cursor / DISK_SECTORDATASIZE;
        unsigned int entryIndex = (fh->cursor % DISK_SECTORDATASIZE) / sizeof(DirEntry);
        
        unsigned int blockAddr = inodeGetBlockAddr(dir, blockIndex);
        if (blockAddr == 0) {
            fh->cursor += DISK_SECTORDATASIZE;
            continue;
        }

        diskReadSector(mountedDisk, blockAddr, buffer);
        DirEntry *entries = (DirEntry*)buffer;
        
        fh->cursor += sizeof(DirEntry); 

        if (entries[entryIndex].inode != 0) {
            strncpy(filename, entries[entryIndex].name, MAX_FILENAME_LENGTH);
            *inumber = entries[entryIndex].inode;
            free(dir);
            return 1;
        }
    }

    free(dir);
    return 0;
}

// Funcao para criar Hard Link: nova entrada de diretorio apontando para mesmo inode
int myFSLink (int fd, const char *filename, unsigned int inumber) {
    if (!isMounted || !mountedDisk) return -1;
    if (__findFileInDir(mountedDisk, ROOT_INODE_NUMBER, filename) != 0) return -1;
    
    // Atualiza contador de referências no inode original
    Inode *inode = inodeLoad(inumber, mountedDisk);
    if (!inode) return -1;
    inodeSetRefCount(inode, inodeGetRefCount(inode) + 1);
    inodeSave(inode);
    free(inode);

    return __addDirEntry(mountedDisk, filename, inumber);
}

// Funcao para remover arquivo (unlink). Apaga dados apenas se refCount zerar.
int myFSUnlink (int fd, const char *filename) {
    if (!isMounted || !mountedDisk) return -1;
    
    Inode *root = inodeLoad(ROOT_INODE_NUMBER, mountedDisk);
    if (!root) return -1;

    unsigned char buffer[DISK_SECTORDATASIZE];
    unsigned int fileSize = inodeGetFileSize(root);
    unsigned int numBlocks = (fileSize + DISK_SECTORDATASIZE - 1) / DISK_SECTORDATASIZE;
    int found = -1;
    unsigned int targetInodeNum = 0;

    // Remove a entrada do diretorio
    for (unsigned int i = 0; i < numBlocks; i++) {
        unsigned int blockAddr = inodeGetBlockAddr(root, i);
        if (blockAddr == 0) continue;
        
        diskReadSector(mountedDisk, blockAddr, buffer);
        DirEntry *entries = (DirEntry*)buffer;
        
        for (int j = 0; j < DISK_SECTORDATASIZE / sizeof(DirEntry); j++) {
            if (entries[j].inode != 0 && strcmp(entries[j].name, filename) == 0) {
                targetInodeNum = entries[j].inode;
                entries[j].inode = 0; // Marca entrada como livre
                diskWriteSector(mountedDisk, blockAddr, buffer);
                found = 0;
                break;
            }
        }
        if (found == 0) break;
    }
    
    free(root);
    
    // Se encontrou, atualiza o inode alvo
    if (found == 0 && targetInodeNum > 0) {
        Inode *target = inodeLoad(targetInodeNum, mountedDisk);
        if (target) {
            unsigned int refs = inodeGetRefCount(target);
            if (refs <= 1) {
                // Se era a ultima referencia, libera blocos e zera inode
                unsigned int fsize = inodeGetFileSize(target);
                unsigned int fblocks = (fsize + DISK_SECTORDATASIZE - 1) / DISK_SECTORDATASIZE;
                for(unsigned int b=0; b<fblocks; b++) {
                    unsigned int baddr = inodeGetBlockAddr(target, b);
                    if(baddr) __freeBlock(mountedDisk, baddr);
                }
                inodeClear(target);
            } else {
                // Se ainda existem links, apenas decrementa contador
                inodeSetRefCount(target, refs - 1);
                inodeSave(target);
            }
            free(target);
        }
    }

    return found;
}

// Funcao para fechar diretorio (mesma logica de arquivo)
int myFSCloseDir (int fd) {
    return myFSClose(fd);
}

// Estrutura de Informação do FS para registro no VFS
FSInfo myFSInfo = {
    .fsid = 'M',
    .fsname = "MyFS",
    .isidleFn = myFSIsIdle,
    .formatFn = myFSFormat,
    .xMountFn = myFSxMount,
    .openFn = myFSOpen,
    .readFn = myFSRead,
    .writeFn = myFSWrite,
    .closeFn = myFSClose,
    .opendirFn = myFSOpenDir,
    .readdirFn = myFSReadDir,
    .linkFn = myFSLink,
    .unlinkFn = myFSUnlink,
    .closedirFn = myFSCloseDir
};

// Funcao para instalar o sistema de arquivos no VFS
int installMyFS (void) {
    return vfsRegisterFS(&myFSInfo);
}