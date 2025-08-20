#pragma once
#include <cstdarg>
#include <cstdio>
#include <string>
#include <vector>
#include <stdexcept>

inline std::string vformat_printf(const char* fmt, va_list ap) {
    va_list ap_copy;
    va_copy(ap_copy, ap);
    int needed = std::vsnprintf(nullptr, 0, fmt, ap_copy);
    va_end(ap_copy);
    if (needed < 0) {
        throw std::runtime_error("formatting error in vformat_printf");
    }
    std::vector<char> buf(static_cast<size_t>(needed) + 1);
    std::vsnprintf(buf.data(), buf.size(), fmt, ap);
    return std::string(buf.data());
}

inline std::string format_printf(const char* fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    std::string s = vformat_printf(fmt, ap);
    va_end(ap);
    return s;
}

inline void fatal(const char* fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    std::vfprintf(stderr, fmt, ap);
    std::fputc('\n', stderr);
    va_end(ap);
    std::abort();
}

template <typename... Args>
inline void fatal_if(bool cond, const char* fmt, Args&&... args) {
    if (cond) {
        std::string msg = format_printf(fmt, std::forward<Args>(args)...);
        fatal("fatal condition occurred: %s", msg.c_str());
    }
}