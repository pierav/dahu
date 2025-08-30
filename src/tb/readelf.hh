#include <iostream>
#include <fstream>
#include <vector>
#include <memory>
#include <cassert>
#include <map>

struct elf_t;

class elf_parser_t {
    elf_t *elf;

    std::map<uint64_t, char*> symmap; // Ordered

    public:
    elf_parser_t(std::string filename);
    void fill_symmap();
    char *get_name(uint64_t s_name);

    uint8_t to_memory(
        std::vector<uint8_t>& memimage,
        const std::string& filename = ""
    );

    uint64_t  get_sym_addr(const char *sym) {
        for (const auto& it: symmap) {
            if (std::strcmp(sym, it.second) == 0) {
                return it.first;
            }
        }
        return 0;
    }
};
