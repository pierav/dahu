#include "util.h"

int strcmp(const char *s1, const char *s2) {
    unsigned char c1, c2;
    do {
        c1 = *s1++;
        c2 = *s2++;
    } while (c1 != 0 && c1 == c2);

    return c1 - c2;
}

char *strcpy(char *dest, const char *src) {
    char *d = dest;
    while ((*d++ = *src++))
        ;
    return dest;
}

void *memcpy(void *dest, const void *src, unsigned long int len) {
    if ((((uintptr_t)dest | (uintptr_t)src | len) & (sizeof(uintptr_t) - 1)) ==
        0) {
        const uintptr_t *s = src;
        uintptr_t *d = dest;
        while (d < (uintptr_t *)(dest + len)) *d++ = *s++;
    } else {
        const char *s = src;
        char *d = dest;
        while (d < (char *)(dest + len)) *d++ = *s++;
    }
    return dest;
}

void *memset(void *dest, int byte, unsigned long int len) {
    if ((((uintptr_t)dest | len) & (sizeof(uintptr_t) - 1)) == 0) {
        uintptr_t word = byte & 0xFF;
        word |= word << 8;
        word |= word << 16;
        word |= word << 16 << 16;

        uintptr_t *d = dest;
        while (d < (uintptr_t *)(dest + len)) *d++ = word;
    } else {
        char *d = dest;
        while (d < (char *)(dest + len)) *d++ = byte;
    }
    return dest;
}
