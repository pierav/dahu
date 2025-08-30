#include <iostream>
#include <fstream>
#include <vector>
#include <memory>
#include <cassert>
#include <cstring>
#include "tb/readelf.hh"

#define EI_MAG0       0x00
#define EI_MAG1       0x01
#define EI_MAG2       0x02
#define EI_MAG3       0x03
#define EI_CLASS      0x04
#define EI_DATA       0x05
#define EI_VERSION    0x06
#define EI_OSABI      0x07
#define EI_ABIVERSION 0x08
#define EI_PAD        0x09

#define SHT_NULL          0x0
#define SHT_PROGBITS      0x1
#define SHT_SYMTAB        0x2
#define SHT_STRTAB        0x3
#define SHT_RELA          0x4
#define SHT_HASH          0x5
#define SHT_DYNAMIC       0x6
#define SHT_NOTE          0x7
#define SHT_NOBITS        0x8
#define SHT_REL           0x9
#define SHT_SHLIB         0x0A
#define SHT_DYNSYM        0x0B
#define SHT_INIT_ARRAY    0x0E
#define SHT_FINI_ARRAY    0x0F
#define SHT_PREINIT_ARRAY 0x10
#define SHT_GROUP         0x11
#define SHT_SYMTAB_SHNDX  0x12
#define SHT_NUM           0x13

struct elf_t {
    uint8_t *data;
    size_t size;
    struct elf_header_t         *header;
    struct elf_program_header_t *phent;
    struct elf_section_header_t *shent;
};

struct elf_header_t {
    uint8_t  e_ident[16];
    uint16_t e_type;       /* Identifies object file type. */
    uint16_t e_machine;    /* Specifies target instruction set architecture. */
    uint32_t e_version;    /* Set to 1 for the original version of elf. */
    uint64_t e_entry;      /* entry point from where the process starts executing */
    uint64_t e_phoff;      /* Points to the start of the program header table. */
    uint64_t e_shoff;      /* Points to the start of the section header table. */
    uint32_t e_flags;      /* Flags. */
    uint16_t e_ehsize;     /* datasize of this header, normally 64 Bytes */
    uint16_t e_phentsize;  /* datasize of a program header table entry. */
    uint16_t e_phnum;      /* datanumber of entries in the program header table. */
    uint16_t e_shentsize;  /* datasize of a section header table entry. */
    uint16_t e_shnum;      /* datanumber of entries in the section header table. */
    uint16_t e_shstrndx;   /* index of the section header table entry */
};

struct elf_program_header_t {
    uint32_t p_type;
    uint32_t p_flags;
    uint64_t p_offset;
    uint64_t p_vaddr;
    uint64_t p_paddr;
    uint64_t p_filesz;
    uint64_t p_memsz;
    uint64_t p_align;
};

struct elf_section_header_t {
    uint32_t sh_name;
    uint32_t sh_type;
    uint64_t sh_flags;
    uint64_t sh_addr;
    uint64_t sh_offset;
    uint64_t sh_size;
    uint32_t sh_link;
    uint32_t sh_info;
    uint64_t sh_addralign;
    uint64_t sh_entsize;
};

struct elf_sim_t {
    uint32_t st_name;
    uint8_t  st_info;
    uint8_t  st_other;
    uint16_t st_shndx;
    uint64_t st_value;
    uint64_t st_size;
};

#define ST_BIND(info)       ((info) >> 4)
#define ST_TYPE(info)       ((info)&0xf)
#define ST_INFO(bind, type) (((bind) << 4) + ((type)&0xf))

#define PT_NULL     0
#define PT_LOAD     1
#define PT_DYNAMIC  2
#define PT_INTERP   3
#define PT_NOTE     4
#define PT_SHLIB    5
#define PT_PHDR     6
#define PT_TLS      7
#define PT_LOOS     0x60000000
#define PT_HIOS     0x6fffffff
#define PT_LOPROC   0x70000000
#define PT_HIPROC   0x7fffffff

elf_parser_t::elf_parser_t(std::string filename) {
    // Open file in binary mode, position at end
    std::ifstream file(filename, std::ios::binary | std::ios::ate);
    if(!file){
        throw std::runtime_error("Failed to open file " + filename);
    }
    std::streamsize size = file.tellg();
    if (size < 0) {
        throw std::runtime_error("Failed to determine size of " + filename);
    }
    file.seekg(0, std::ios::beg);

    elf = new elf_t();
    elf->size = static_cast<size_t>(size);
    elf->data = new uint8_t[elf->size];
    assert(elf->data);

    // Read file into buffer
    if (!file.read(reinterpret_cast<char*>(elf->data), size)) {
        std::cerr << "Failed to read file\n";
        exit(1);
    }

    // header
    elf->header = (struct elf_header_t *)elf->data;
    assert(elf->header->e_ident[EI_MAG0] == 0x7F);
    assert(elf->header->e_ident[EI_MAG1] == 'E');
    assert(elf->header->e_ident[EI_MAG2] == 'L');
    assert(elf->header->e_ident[EI_MAG3] == 'F');
    assert(elf->header->e_ident[EI_CLASS] == 2); // 64 bits
    assert(elf->header->e_ident[EI_DATA] == 1);  // Little endian
    assert(elf->header->e_ident[EI_VERSION] == 1);
    // assert(elf->header->e_ident[EI_OSABI] == 97); // Bare metal
    // assert(elf->header->e_ident[EI_ABIVERSION] == 10); // LP64D

    uint16_t ET_EXEC = 0x02; // 0 ok ?
    uint16_t EM_RISCV = 243;
    assert(elf->header->e_type == ET_EXEC);  /* Executable file. */
    // elf->header->e_version TODO
    // Detect architecture
    assert(elf->header->e_machine == EM_RISCV); // RISC-V
    // assert(!(elf->header->e_flags & 0x1)); // No RVC for now !
    // e_flags & 0x6 : Soft Fload, Single Fload, Double Fload, Quad float
    // program header
    assert(sizeof(elf_program_header_t) == elf->header->e_phentsize);
    assert(sizeof(elf_section_header_t) == elf->header->e_shentsize);
    assert(sizeof(elf_header_t) == elf->header->e_ehsize);
    elf->phent =(elf_program_header_t *)(elf->data + elf->header->e_phoff);
    // section header
    elf->shent = (elf_section_header_t *)(elf->data + elf->header->e_shoff);
    // TODO Must be true only for non PIC code ?
    assert(elf->header->e_entry == 0x80000000);

    fill_symmap();
}

void elf_parser_t::fill_symmap(){
    // Find the strtab
    uint64_t strtab = 0;
    uint64_t shstrtab_e = elf->shent[elf->header->e_shstrndx].sh_offset;
    for (uint16_t j = 0; j < elf->header->e_shnum; j++) {
        uint64_t name_offset = shstrtab_e + elf->shent[j].sh_name;
        const char* str = reinterpret_cast<const char*>(elf->data + name_offset);
        // std::string_view section_name(str);
        // String tables are SHT_STRTAB, but skip section header string table
        if (elf->shent[j].sh_type == SHT_STRTAB && j != elf->header->e_shstrndx) {
            // assert(section_name == ".strtab")
            assert(strtab == 0); // only one .strtab expected
            strtab = elf->shent[j].sh_offset;
        }

    }
    assert(strtab != 0);
    for (uint16_t j = 0; j < elf->header->e_shnum; j++) {
        if (elf->shent[j].sh_type == SHT_SYMTAB) {
            uint32_t name_off = shstrtab_e + elf->shent[j].sh_name;
            uint32_t count = elf->shent[j].sh_size / sizeof(elf_sim_t);
            // printf("Symbol table [%s] # %d\n", elf->data + name_off, count);
            for (uint32_t i = 0; i < count; i++) {
                elf_sim_t *sim = (elf_sim_t *)(elf->data + elf->shent[j].sh_offset) + i;
                char *sym_name = (char*)elf->data + strtab + sim->st_name;
                uint64_t addr = sim->st_value;
                // printf("- %20s = %lx\n", sym_name, addr);
                symmap[addr] = sym_name;
            }
        }
    }
}

char *elf_parser_t::get_name(uint64_t s_name){
    uint64_t shstrtab_e = elf->shent[elf->header->e_shstrndx].sh_offset;
    return (char *)elf->data + ((uint64_t)shstrtab_e + s_name);
}

uint8_t elf_parser_t::to_memory(
    std::vector<uint8_t>& memimage,
    const std::string& filename
) {
    uint64_t base_addr = elf->header->e_entry;
    uint64_t end_addr  = base_addr;

    // Find memory range
    for (uint16_t i = 0; i < elf->header->e_phnum; i++) {
        const auto& ph = elf->phent[i];
        // Only loadable segments
        if (ph.p_type != PT_LOAD || ph.p_filesz == 0) continue;
        end_addr = std::max(ph.p_vaddr + ph.p_filesz, end_addr);
    }
    uint64_t memimage_size = end_addr - base_addr;
    // Allocate zero-initialized memory
    memimage.assign(memimage_size, 0);
    // printf("memimage_size=%x\n",memimage.size());

    // Copy program segments into memory
    for (uint16_t i = 0; i < elf->header->e_phnum; i++) {
        const auto& ph = elf->phent[i];
        // Only loadable segments
        if (ph.p_type != PT_LOAD || ph.p_filesz == 0) continue;
        uint64_t dst_offset = ph.p_vaddr - base_addr;
        uint64_t size = ph.p_filesz;
        const uint8_t* src  = elf->data + ph.p_offset;
        // printf("PH: [%lx:+%lx]\n",  ph.p_vaddr, size);
        assert(ph.p_offset + size < elf->size);
        assert(dst_offset + size <= memimage.size());
        std::memcpy(memimage.data() + dst_offset, src, size);
    }

    // Optional: write to file
    if (!filename.empty()) {
        std::cout << "Write " << filename << "\n";
        std::ofstream ofs(filename, std::ios::binary);
        assert(ofs.is_open());
        ofs.write(reinterpret_cast<const char*>(memimage.data()), memimage.size());
    }
    return 0;
}

