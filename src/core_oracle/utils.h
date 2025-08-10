#include <iostream>
#include <sstream>
#include <vector>
#include <cstdarg>
#include <cstdio>

inline std::string vformat_printf(const char* fmt, va_list ap) {
    va_list ap_copy;
    va_copy(ap_copy, ap);
    int needed = std::vsnprintf(nullptr, 0, fmt, ap_copy);
    va_end(ap_copy);

    if (needed < 0) return {}; // formatting error

    std::vector<char> buf(static_cast<size_t>(needed) + 1);
    std::vsnprintf(buf.data(), buf.size(), fmt, ap);
    return std::string(buf.data(), buf.size() - 1);
}

inline std::string format_printf(const char* fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    std::string s = vformat_printf(fmt, ap);
    va_end(ap);
    return s;
}