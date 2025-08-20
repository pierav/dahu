/**
 * memory.hh
 *
 *  Author:   Pierre Ravenel
 * Created:   03/05/2024
 **/

#pragma once

#include <cstring>
#include <map>
#include <cstdint>
#include "core_oracle/utils.hh"

#define LINE_SIZE_LOG2 6
#define LINE_SIZE 64
#define CACHE_ADDR_F(addr) ((addr) >> LINE_SIZE_LOG2)

#if 1 << LINE_SIZE_LOG2 != LINE_SIZE
#error BAD CONFIG
#endif

struct entry_t {
  uint64_t _tag;
  uint8_t line[LINE_SIZE]; // Word data
  uint64_t bw;    // Mask > size/8
  uint64_t _bw_wbs; /* bw Write by store */
  uint64_t _bw_constant; /* bw Nostore < Constant */

  entry_t() : _tag(0), line{}, bw(0), _bw_wbs(0), _bw_constant(0) { }

  uint64_t getoffset(uint64_t addr){
    return addr & (LINE_SIZE - 1);
  }

  uint64_t getmaskbw(uint64_t addr, uint64_t vsize){
    return ((1ULL<<(vsize))-1) << getoffset(addr);
  }

  /* Write data in cache. Return true is access update cache */
  bool write(uint64_t addr, uint8_t vsize, uint8_t *data, bool isstore){
    /* Current access */
    uint64_t shift = getoffset(addr);
    uint64_t mask_bw = getmaskbw(addr, vsize);
    /* Entry initialisation */
    if (!_tag){
      _tag = CACHE_ADDR_F(addr);
      fatal_if(bw != 0, "Initial value fail\n");
    } else {
      fatal_if(_tag != CACHE_ADDR_F(addr), "Missmatch tag");
    }
    uint64_t _data = 0;
    memcpy(&_data, data, vsize);
    // printf("%16lx:[%c] @%16lx #%d : %16lx (%lx:%lx)\n",
    // _tag, isstore ? 'W' : 'R', addr, vsize, _data, bw, mask_bw);

    uint8_t* oldvalue = line + shift;
    bool missmatch = memcmp(oldvalue, data, vsize) != 0;
    uint64_t _data_ref = 0;
    memcpy(&_data_ref, oldvalue, vsize);
    bool match_bw = (~bw & mask_bw) == 0;
    // Memory valid and load
    // printf("Entry : bw = %16lx\n", bw);
    fatal_if(!isstore && match_bw && missmatch,
        "BAD VALUE! %16lx != %16lx\n", _data, _data_ref);

    if (missmatch){
        memcpy(oldvalue, data, vsize);
    }
    bw |= mask_bw;
    // Update mask
    if (isstore){
      _bw_wbs |= mask_bw;
    } else {
      _bw_wbs &= ~mask_bw;
    }
    if (missmatch) {
        _bw_constant &= ~mask_bw;
    } else {
        _bw_constant |= mask_bw;
    }
    return missmatch || !match_bw; // Is access updated cache
  }
};


class InfiniteMemory64 {
    struct InfiniteMemory64Stats {
        size_t req = 0;
        size_t storeReqs = 0;
        size_t storeSilent = 0;
        /* todo (not trivial !)size_t storeToStore; */
        size_t loadReqs = 0;
        size_t loadConstant = 0;
        size_t loadToLoad = 0;
    } stats;

    std::map<uint64_t, entry_t> mem;

    inline entry_t* entry(uint64_t addr){
        return &mem[CACHE_ADDR_F(addr)];
    }

    public:
    InfiniteMemory64() {}

    /**
     * @brief Performs a memory write. Returns true if the new value is equal
     * to the last one.
     *
     * @param addr
     * @param size
     * @param value
     * @return true
     * @return false
     */
    bool check_store(uint64_t addr, uint8_t size, uint64_t value){
        // printf("W @%16lx #%d : %16lx\n", addr, size, value);
        fatal_if(size > 8, "Invalid size : %d\n", size);
        entry_t *e = entry(addr);
        bool silent = !e->write(addr, size, (uint8_t*)&value, true);
        /* Statistics */
        stats.storeReqs +=1;
        stats.storeSilent += silent; /* Indempotance */
        return silent;
    }

    /**
     * @brief Check the load value. Returns true if the dw is const
     *
     * @param addr
     * @param size
     * @param value
     * @return true
     * @return false
     */
    bool check_load(uint64_t addr, uint8_t size, uint64_t value){
        entry_t *e = entry(addr);
        bool constant = !e->write(addr, size, (uint8_t*)&value, false);
        /* Statistics */
        stats.loadReqs += 1;
        stats.loadConstant += constant;
        // stats.loadToLoad += loadToLoad;// Todo
        return constant;
    }

    void invalidate(uint64_t addr){
        // printf("I @%16lx\n", addr);
        mem.erase(CACHE_ADDR_F(addr));
    }
};
