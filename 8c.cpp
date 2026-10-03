// 8c.cpp
// g++ -std=c++17 -O2 -Wall -Wextra -pedantic -static -mconsole 8c.cpp -o 8c.exe -lgdi32 -lwinmm

#include <algorithm>
#include <array>
#include <chrono>
#include <cctype>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <mutex>
#include <condition_variable>
#include <atomic>
#include <limits>
#include <sstream>
#include <stdexcept>
#include <string>
#include <thread>
#include <unordered_map>
#include <vector>

#ifdef _WIN32
#ifndef NOMINMAX
#define NOMINMAX
#endif
#include <windows.h>
#include <mmsystem.h>
#endif

namespace eightc {

constexpr int CUI_W = 32;
constexpr int CUI_H = 8;
constexpr int MEM_BLOCKS = 256;
constexpr int MEM_SPACES = 2;
constexpr size_t WIDE_INSTRUCTION_SIZE = 11;
constexpr uint8_t WIDE_INSTRUCTION_SEPARATOR = 0x24; // '$'

struct Cell {
    char ch = ' ';
    uint8_t bg = 0; // RGB bit order: R=4, G=2, B=1.
};

constexpr int WIDE_W = 512;
constexpr int WIDE_H = 192;

struct WideTextCommand {
    uint8_t x = 0;      // VGA X: 0..31
    uint8_t y = 0;      // VGA Y: 0..7
    uint16_t color565 = 0;
    uint8_t ch = 0;     // ASCII: 0..127
};

struct MachineInstruction {
    uint8_t opcode = 0;
    uint8_t input0 = 0;
    uint8_t input1 = 0;
    uint8_t input2 = 0;
    int line = 0;
};

struct WideInstruction {
    uint8_t opcode = 0;
    uint16_t input0 = 0;
    uint32_t input1 = 0;
    uint32_t input2 = 0;
    uint64_t fileOffset = 0;
};

enum class Kind {
    Machine,
    Set,
    Beep,
    RamWrite,
    RamRead,
    Vga,
    Arithmetic,
    Jump,
    ForJump
};

struct ScriptInstruction {
    Kind kind = Kind::Machine;
    MachineInstruction machine{};
    int line = 0;
    std::string name;
    std::array<std::string, 5> p{};
};

static std::string trim(std::string s) {
    const auto first = std::find_if_not(s.begin(), s.end(), [](char c) {
        return std::isspace(static_cast<unsigned char>(c)) != 0;
    });
    if (first == s.end()) return {};

    const auto last = std::find_if_not(s.rbegin(), s.rend(), [](char c) {
        return std::isspace(static_cast<unsigned char>(c)) != 0;
    }).base();
    return std::string(first, last);
}

static std::string lower(std::string s) {
    for (char& c : s) c = static_cast<char>(std::tolower(static_cast<unsigned char>(c)));
    return s;
}

static std::vector<std::string> splitWords(const std::string& s) {
    std::vector<std::string> v;
    std::istringstream in(s);
    std::string w;
    while (in >> w) v.push_back(w);
    return v;
}

static std::string removeComment(std::string line) {
    const size_t hash = line.find('#');
    const size_t slash = line.find("//");
    size_t cut = std::string::npos;
    if (hash != std::string::npos) cut = hash;
    if (slash != std::string::npos) cut = std::min(cut, slash);
    if (cut != std::string::npos) line.resize(cut);
    return trim(line);
}

static bool exactBinary(const std::string& s, size_t n) {
    if (s.size() != n) return false;
    return std::all_of(s.begin(), s.end(), [](char c) { return c == '0' || c == '1'; });
}

static int parseBinaryFixed(const std::string& s, int bits, const std::string& label) {
    if (!exactBinary(s, static_cast<size_t>(bits)))
        throw std::runtime_error(label + " must contain exactly " + std::to_string(bits) + " bits.");
    int value = 0;
    for (char c : s) value = (value << 1) | (c - '0');
    return value;
}

static uint64_t parseHexFixed(const std::string& s, int digits, const std::string& label) {
    if (s.size() != static_cast<size_t>(digits))
        throw std::runtime_error(label + " must contain exactly " + std::to_string(digits) + " hex digits.");
    uint64_t value = 0;
    for (char c : s) {
        int nibble = -1;
        if (c >= '0' && c <= '9') nibble = c - '0';
        else if (c >= 'a' && c <= 'f') nibble = c - 'a' + 10;
        else if (c >= 'A' && c <= 'F') nibble = c - 'A' + 10;
        if (nibble < 0) throw std::runtime_error(label + " contains a non-hex character.");
        value = (value << 4) | static_cast<uint64_t>(nibble);
    }
    return value;
}

static std::string hexFixed(uint64_t value, int digits) {
    if (digits < 1 || digits > 16)
        throw std::runtime_error("hexFixed digit count must be 1..16");
    static constexpr char hex[] = "0123456789ABCDEF";
    std::string out(static_cast<size_t>(digits), '0');
    for (int i = digits - 1; i >= 0; --i) {
        out[static_cast<size_t>(i)] = hex[value & 0xFULL];
        value >>= 4;
    }
    return out;
}

static int parseInteger(const std::string& s) {
    if (s.empty()) throw std::runtime_error("empty number");

    size_t pos = 0;
    bool negative = false;
    if (s[pos] == '+' || s[pos] == '-') {
        negative = s[pos] == '-';
        ++pos;
    }
    if (pos == s.size()) throw std::runtime_error("invalid number: " + s);

    int base = 10;
    if (pos + 2 <= s.size() && s[pos] == '0' && (s[pos + 1] == 'x' || s[pos + 1] == 'X' ||
                                                   s[pos + 1] == 'b' || s[pos + 1] == 'B')) {
        base = (s[pos + 1] == 'x' || s[pos + 1] == 'X') ? 16 : 2;
        pos += 2;
    }

    if (pos == s.size()) throw std::runtime_error("invalid number: " + s);

    const uint64_t limit = negative ? 2147483648ULL : 2147483647ULL;
    uint64_t value = 0;
    for (; pos < s.size(); ++pos) {
        const unsigned char c = static_cast<unsigned char>(s[pos]);
        int digit = -1;
        if (c >= '0' && c <= '9') digit = c - '0';
        else if (c >= 'a' && c <= 'f') digit = c - 'a' + 10;
        else if (c >= 'A' && c <= 'F') digit = c - 'A' + 10;

        if (digit < 0 || digit >= base)
            throw std::runtime_error("invalid number: " + s);
        if (value > (limit - static_cast<uint64_t>(digit)) / static_cast<uint64_t>(base))
            throw std::runtime_error("number out of 32-bit signed range: " + s);
        value = value * static_cast<uint64_t>(base) + static_cast<uint64_t>(digit);
    }

    if (negative) {
        if (value == 2147483648ULL) return std::numeric_limits<int>::min();
        return -static_cast<int>(value);
    }
    return static_cast<int>(value);
}

static double parseClockHz(const std::string& s) {
    size_t pos = 0;
    const double hz = std::stod(s, &pos);
    if (pos != s.size())
        throw std::runtime_error("invalid clock value: " + s);
    if (!(hz > 0.0) || !std::isfinite(hz))
        throw std::runtime_error("clock must be a positive finite Hz value");
    return hz;
}

static bool validIdentifier(const std::string& s) {
    if (s.empty()) return false;
    if (!(std::isalpha(static_cast<unsigned char>(s[0])) || s[0] == '_')) return false;
    for (size_t i = 1; i < s.size(); ++i) {
        const unsigned char c = static_cast<unsigned char>(s[i]);
        if (!(std::isalnum(c) || s[i] == '_')) return false;
    }
    return true;
}

static std::string binFixed(uint32_t value, int bits) {
    if (bits < 1 || bits > 32)
        throw std::runtime_error("binFixed bit count must be 1..32");
    std::string s(static_cast<size_t>(bits), '0');
    for (int i = 0; i < bits; ++i) {
        const int shift = bits - 1 - i;
        s[static_cast<size_t>(i)] = ((value >> shift) & 1U) ? '1' : '0';
    }
    return s;
}

class Display {
public:
    Display() {
        clear();
    }

    ~Display() {
        shutdown();
    }

    void setup() {
#ifdef _WIN32
        if (guiThread_.joinable()) return;
        {
            std::lock_guard<std::mutex> lock(guiMutex_);
            guiReadyFlag_ = false;
            guiError_.clear();
        }

        guiThread_ = std::thread([this] {
            try {
                guiMain();
            } catch (const std::exception& e) {
                std::lock_guard<std::mutex> lock(guiMutex_);
                guiError_ = e.what();
                guiReadyFlag_ = true;
                guiReady_.notify_one();
            } catch (...) {
                std::lock_guard<std::mutex> lock(guiMutex_);
                guiError_ = "unknown VGA thread error";
                guiReadyFlag_ = true;
                guiReady_.notify_one();
            }
        });

        std::unique_lock<std::mutex> lock(guiMutex_);
        guiReady_.wait(lock, [this] { return guiReadyFlag_; });
        if (!guiError_.empty()) {
            const std::string error = guiError_;
            lock.unlock();
            if (guiThread_.joinable()) guiThread_.join();
            throw std::runtime_error("VGA window initialization failed: " + error);
        }
#else
        std::cout << "VGA window is available only on Windows.\n";
#endif
    }

    void shutdown() {
#ifdef _WIN32
        HWND hwnd = nullptr;
        {
            std::lock_guard<std::mutex> lock(guiMutex_);
            hwnd = hwnd_;
        }
        if (hwnd != nullptr)
            PostMessageA(hwnd, WM_CLOSE, 0, 0);

        if (guiThread_.joinable())
            guiThread_.join();
#endif
    }

    // Clears only the legacy 32x8 CUI layer.
    void clear() {
        {
            std::lock_guard<std::mutex> lock(cellMutex_);
            for (auto& c : cells_) c = Cell{};
        }
        invalidate();
    }

    // Clears both the legacy CUI layer and the HEX VGA layer.
    void clearAll() {
        clear();
        clearWideStorage();
        invalidate();
    }

    void clearWide() {
        clearWideStorage();
        invalidate();
    }


    void clearWideStorage() {
        std::lock_guard<std::mutex> lock(wideMutex_);
        widePixels_.fill(0);
        wideTexts_.clear();
    }

    void widePixel(uint16_t x, uint16_t y, uint16_t color565) {
        if (x >= WIDE_W || y >= WIDE_H) return;
        {
            std::lock_guard<std::mutex> lock(wideMutex_);
            widePixels_[static_cast<size_t>(y) * WIDE_W + x] = 0x10000U | color565;
        }
        invalidate();
    }

    void wideText(uint8_t x, uint8_t y, uint16_t color565, uint8_t ch) {
        if (x >= CUI_W || y >= CUI_H) return;
        {
            std::lock_guard<std::mutex> lock(wideMutex_);
            bool replaced = false;
            for (auto& existing : wideTexts_) {
                if (existing.x == x && existing.y == y) {
                    existing = {x, y, color565, ch};
                    replaced = true;
                    break;
                }
            }
            if (!replaced)
                wideTexts_.push_back({x, y, color565, ch});
        }
        invalidate();
    }

    void put(int x, int y, char ch, uint8_t bg) {
        if (x < 0 || x >= CUI_W || y < 0 || y >= CUI_H) return;
        {
            std::lock_guard<std::mutex> lock(cellMutex_);
            Cell& c = cells_[static_cast<size_t>(y * CUI_W + x)];
            c.ch = ch;
            c.bg = static_cast<uint8_t>(bg & 7U);
        }
        invalidate();
    }

    void background(int x, int y, uint8_t bg) {
        if (x < 0 || x >= CUI_W || y < 0 || y >= CUI_H) return;
        {
            std::lock_guard<std::mutex> lock(cellMutex_);
            cells_[static_cast<size_t>(y * CUI_W + x)].bg = static_cast<uint8_t>(bg & 7U);
        }
        invalidate();
    }

    void render() const {
#ifdef _WIN32
        invalidate();
#else
        std::lock_guard<std::mutex> lock(cellMutex_);
        for (int y = 0; y < CUI_H; ++y) {
            for (int x = 0; x < CUI_W; ++x) {
                const Cell& c = cells_[static_cast<size_t>(y * CUI_W + x)];
                std::cout << (c.ch == '\0' ? ' ' : c.ch);
            }
            if (y != CUI_H - 1) std::cout << '\n';
        }
        std::cout << std::flush;
#endif
    }

#ifdef _WIN32
    bool windowOpen() const {
        std::lock_guard<std::mutex> lock(guiMutex_);
        return hwnd_ != nullptr;
    }
#endif

private:
    std::array<Cell, CUI_W * CUI_H> cells_{};
    mutable std::mutex cellMutex_;

    // Pixel state is kept as a fixed raster instead of an ever-growing command log.
    // 0 = untouched, otherwise bit 16 is the valid flag and bits 0..15 hold RGB565.
    std::array<uint32_t, static_cast<size_t>(WIDE_W) * WIDE_H> widePixels_{};
    std::vector<WideTextCommand> wideTexts_;
    mutable std::mutex wideMutex_;

#ifdef _WIN32
    std::thread guiThread_;
    mutable std::mutex guiMutex_;
    std::condition_variable guiReady_;
    bool guiReadyFlag_ = false;
    std::string guiError_;
    HWND hwnd_ = nullptr;
    HFONT font_ = nullptr;
    std::array<HBRUSH, 8> brushes_{};
    mutable std::atomic<bool> repaintQueued_{false};

    static constexpr UINT WM_VGA_INVALIDATE = WM_APP + 1;

    static int bgColor(uint8_t rgb) {
        switch (rgb & 7U) {
            case 0: return RGB(0, 0, 0);
            case 1: return RGB(0, 0, 170);
            case 2: return RGB(0, 170, 0);
            case 3: return RGB(0, 170, 170);
            case 4: return RGB(170, 0, 0);
            case 5: return RGB(170, 0, 170);
            case 6: return RGB(170, 170, 0);
            default: return RGB(192, 192, 192);
        }
    }

    static COLORREF color565(uint16_t c) {
        const unsigned r = ((c >> 11) & 0x1FU) * 255U / 31U;
        const unsigned g = ((c >> 5) & 0x3FU) * 255U / 63U;
        const unsigned b = (c & 0x1FU) * 255U / 31U;
        return RGB(r, g, b);
    }

    void invalidate() const {
        HWND hwnd = nullptr;
        {
            std::lock_guard<std::mutex> lock(guiMutex_);
            hwnd = hwnd_;
        }
        if (hwnd == nullptr) return;

        bool expected = false;
        if (!repaintQueued_.compare_exchange_strong(expected, true, std::memory_order_acq_rel))
            return;

        if (!PostMessageA(hwnd, WM_VGA_INVALIDATE, 0, 0))
            repaintQueued_.store(false, std::memory_order_release);
    }

    static LRESULT CALLBACK wndProc(HWND hwnd, UINT msg, WPARAM wp, LPARAM lp) {
        Display* self = reinterpret_cast<Display*>(GetWindowLongPtrA(hwnd, GWLP_USERDATA));
        if (msg == WM_NCCREATE) {
            const auto* cs = reinterpret_cast<const CREATESTRUCTA*>(lp);
            self = static_cast<Display*>(cs->lpCreateParams);
            SetWindowLongPtrA(hwnd, GWLP_USERDATA, reinterpret_cast<LONG_PTR>(self));
        }
        if (self == nullptr) return DefWindowProcA(hwnd, msg, wp, lp);

        switch (msg) {
            case WM_ERASEBKGND:
                return 1;

            case WM_VGA_INVALIDATE:
                self->repaintQueued_.store(false, std::memory_order_release);
                InvalidateRect(hwnd, nullptr, FALSE);
                return 0;

            case WM_PAINT: {
                PAINTSTRUCT ps{};
                HDC dc = BeginPaint(hwnd, &ps);
                if (dc == nullptr) return 0;

                RECT client{};
                if (!GetClientRect(hwnd, &client)) {
                    EndPaint(hwnd, &ps);
                    return 0;
                }

                const int clientW = client.right - client.left;
                const int clientH = client.bottom - client.top;
                const int cellW = std::max(1, clientW / CUI_W);
                const int cellH = std::max(1, clientH / CUI_H);

                std::array<Cell, CUI_W * CUI_H> copy{};
                {
                    std::lock_guard<std::mutex> lock(self->cellMutex_);
                    copy = self->cells_;
                }

                std::array<uint32_t, static_cast<size_t>(WIDE_W) * WIDE_H> widePixelCopy{};
                std::vector<WideTextCommand> wideTextCopy;
                {
                    std::lock_guard<std::mutex> lock(self->wideMutex_);
                    widePixelCopy = self->widePixels_;
                    wideTextCopy = self->wideTexts_;
                }

                HGDIOBJ oldFont = self->font_ != nullptr ? SelectObject(dc, self->font_) : nullptr;
                SetBkMode(dc, TRANSPARENT);
                SetTextColor(dc, RGB(255, 255, 255));

                for (int y = 0; y < CUI_H; ++y) {
                    for (int x = 0; x < CUI_W; ++x) {
                        const Cell& c = copy[static_cast<size_t>(y * CUI_W + x)];
                        RECT r{
                            x * cellW, y * cellH, (x + 1) * cellW, (y + 1) * cellH
                        };
                        HBRUSH brush = self->brushes_[c.bg & 7U];
                        if (brush != nullptr) FillRect(dc, &r, brush);

                        char text[2]{c.ch == '\0' ? ' ' : c.ch, '\0'};
                        DrawTextA(dc, text, 1, &r, DT_CENTER | DT_VCENTER | DT_SINGLELINE | DT_NOPREFIX);
                    }
                }

                // HEX VGA format: mode 0 = pixel, mode 1 = text, mode 2 = clear.
                for (int y = 0; y < WIDE_H; ++y) {
                    for (int x = 0; x < WIDE_W; ++x) {
                        const uint32_t packed = widePixelCopy[static_cast<size_t>(y) * WIDE_W + x];
                        if ((packed & 0x10000U) != 0)
                            SetPixelV(dc, x, y, self->color565(static_cast<uint16_t>(packed & 0xFFFFU)));
                    }
                }

                for (const WideTextCommand& cmd : wideTextCopy) {
                    SetBkMode(dc, TRANSPARENT);
                    SetTextColor(dc, self->color565(cmd.color565));
                    SetTextAlign(dc, TA_LEFT | TA_TOP);

                    // HEX VGA uses the same YYYXXXXX character-cell coordinates as
                    // legacy VGA. Convert the 32x8 cell position to the actual
                    // 16x24 pixel cell used by the window.
                    const int textX = static_cast<int>(cmd.x) * cellW;
                    const int textY = static_cast<int>(cmd.y) * cellH;
                    const wchar_t text[2]{
                        static_cast<wchar_t>(cmd.ch),
                        L'\0'
                    };

                    TextOutW(dc, textX, textY, text, 1);
                }

                if (oldFont != nullptr) SelectObject(dc, oldFont);
                EndPaint(hwnd, &ps);
                return 0;
            }

            case WM_CLOSE:
                DestroyWindow(hwnd);
                return 0;

            case WM_DESTROY: {
                {
                    std::lock_guard<std::mutex> lock(self->guiMutex_);
                    self->hwnd_ = nullptr;
                }

                if (self->font_ != nullptr) {
                    DeleteObject(self->font_);
                    self->font_ = nullptr;
                }
                for (HBRUSH& brush : self->brushes_) {
                    if (brush != nullptr) {
                        DeleteObject(brush);
                        brush = nullptr;
                    }
                }

                self->repaintQueued_.store(false, std::memory_order_release);
                PostQuitMessage(0);
                return 0;
            }

            case WM_NCDESTROY:
                SetWindowLongPtrA(hwnd, GWLP_USERDATA, 0);
                break;
        }
        return DefWindowProcA(hwnd, msg, wp, lp);
    }

    void guiMain() {
        const char* className = "8cVGAWindowClass";
        HINSTANCE instance = GetModuleHandleA(nullptr);
        if (instance == nullptr) {
            throw std::runtime_error("GetModuleHandleA failed. Error=" + std::to_string(GetLastError()));
        }

        WNDCLASSA wc{};
        wc.lpfnWndProc = wndProc;
        wc.hInstance = instance;
        wc.lpszClassName = className;
        wc.hCursor = LoadCursorA(nullptr, IDC_ARROW);
        wc.hbrBackground = reinterpret_cast<HBRUSH>(GetStockObject(BLACK_BRUSH));
        const ATOM atom = RegisterClassA(&wc);
        if (atom == 0 && GetLastError() != ERROR_CLASS_ALREADY_EXISTS)
            throw std::runtime_error("RegisterClassA failed. Error=" + std::to_string(GetLastError()));

        const int clientW = CUI_W * 16;
        const int clientH = CUI_H * 24;
        RECT wr{0, 0, clientW, clientH};
        if (!AdjustWindowRect(&wr, WS_OVERLAPPED | WS_CAPTION | WS_SYSMENU | WS_MINIMIZEBOX, FALSE))
            throw std::runtime_error("AdjustWindowRect failed. Error=" + std::to_string(GetLastError()));

        HWND hwnd = CreateWindowExA(
            0, className, "8c VGA 32x8",
            WS_OVERLAPPED | WS_CAPTION | WS_SYSMENU | WS_MINIMIZEBOX,
            CW_USEDEFAULT, CW_USEDEFAULT, wr.right - wr.left, wr.bottom - wr.top,
            nullptr, nullptr, instance, this);

        if (hwnd == nullptr)
            throw std::runtime_error("CreateWindowExA failed. Error=" + std::to_string(GetLastError()));

        font_ = CreateFontW(
            22, 0, 0, 0, FW_NORMAL, FALSE, FALSE, FALSE, DEFAULT_CHARSET,
            OUT_DEFAULT_PRECIS, CLIP_DEFAULT_PRECIS, DEFAULT_QUALITY,
            FIXED_PITCH | FF_MODERN, L"Consolas");

        for (size_t i = 0; i < brushes_.size(); ++i) {
            brushes_[i] = CreateSolidBrush(static_cast<COLORREF>(bgColor(static_cast<uint8_t>(i))));
            if (brushes_[i] == nullptr) {
                const DWORD error = GetLastError();
                DestroyWindow(hwnd);
                throw std::runtime_error("CreateSolidBrush failed. Error=" + std::to_string(error));
            }
        }

        if (font_ == nullptr) {
            const DWORD error = GetLastError();
            DestroyWindow(hwnd);
            throw std::runtime_error("CreateFontW failed. Error=" + std::to_string(error));
        }

        {
            std::lock_guard<std::mutex> lock(guiMutex_);
            hwnd_ = hwnd;
            guiReadyFlag_ = true;
        }
        guiReady_.notify_one();

        ShowWindow(hwnd, SW_SHOW);
        UpdateWindow(hwnd);

        MSG msg{};
        while (GetMessageA(&msg, nullptr, 0, 0) > 0) {
            TranslateMessage(&msg);
            DispatchMessageA(&msg);
        }
    }
#else
    void invalidate() const {}
#endif
};

class VM {
public:
    explicit VM(double hz) : hz_(hz) {
        if (!(hz_ > 0.0) || !std::isfinite(hz_))
            throw std::runtime_error("clock must be a positive finite Hz value");
    }

    Display& display() { return display_; }

    void run(const std::vector<ScriptInstruction>& code) {
        std::unordered_map<size_t, int> fjRemain;
        size_t pc = 0;
        auto nextTick = std::chrono::steady_clock::now();

        while (pc < code.size()) {
#ifdef _WIN32
            if (!display_.windowOpen())
                throw std::runtime_error("VGA window was closed while executing the program");
#endif
            const ScriptInstruction& s = code[pc];
            bool advance = true;

            switch (s.kind) {
                case Kind::Machine: {
                    MachineInstruction mi{};
                    mi.opcode = static_cast<uint8_t>(fixedOrValue(s.p[0], 4, "opcode"));
                    mi.input0 = static_cast<uint8_t>(fixedOrValue(s.p[1], 4, "input0"));
                    mi.input1 = static_cast<uint8_t>(fixedOrValue(s.p[2], 8, "input1"));
                    mi.input2 = static_cast<uint8_t>(fixedOrValue(s.p[3], 8, "input2"));
                    mi.line = s.line;
                    execute(mi);
                    waitClock(nextTick);
                    break;
                }

                case Kind::Set:
                    vars_[s.name] = evaluate(s.p[0]);
                    break;

                case Kind::Beep: {
                    const int volume = fixedOrValue(s.p[0], 4, "BEEP volume");
                    const int waveform = fixedOrValue(s.p[1], 8, "BEEP waveform");
                    const int duration = fixedOrValue(s.p[2], 8, "BEEP duration");
                    execute({1, static_cast<uint8_t>(volume), static_cast<uint8_t>(waveform), static_cast<uint8_t>(duration), s.line});
                    waitClock(nextTick);
                    break;
                }

                case Kind::RamWrite: {
                    const int space = fixedOrValue(s.p[0], 4, "RAM space");
                    const int address = fixedOrValue(s.p[1], 8, "RAM address");
                    const int value = fixedOrValue(s.p[2], 8, "RAM value");
                    execute({2, static_cast<uint8_t>(space), static_cast<uint8_t>(address), static_cast<uint8_t>(value), s.line});
                    waitClock(nextTick);
                    break;
                }

                case Kind::RamRead: {
                    const int space = fixedOrValue(s.p[0], 4, "RAM space");
                    const int address = fixedOrValue(s.p[1], 8, "RAM address");
                    (void)fixedOrValue(s.p[2], 8, "RAM read unused input");
                    execute({3, static_cast<uint8_t>(space), static_cast<uint8_t>(address), 0, s.line});
                    waitClock(nextTick);
                    break;
                }

                case Kind::Vga: {
                    // Legacy VGA uses input0=RGB(3bit)+mode(1bit), input1=YYYXXXXX, input2=ASCII(8bit).
                    const int input0 = fixedOrValue(s.p[0], 4, "VGA input0");
                    const int input1 = fixedOrValue(s.p[1], 8, "VGA input1");
                    const int input2 = fixedOrValue(s.p[2], 8, "VGA input2");
                    execute({4, static_cast<uint8_t>(input0), static_cast<uint8_t>(input1), static_cast<uint8_t>(input2), s.line});
                    waitClock(nextTick);
                    break;
                }

                case Kind::Arithmetic: {
                    const int opcode = parseInteger(s.p[0]);
                    const int a = requireU8(evaluate(s.p[1]), "operand1");
                    const int b = requireU8(evaluate(s.p[2]), "operand2");
                    execute({static_cast<uint8_t>(opcode), 0, static_cast<uint8_t>(a), static_cast<uint8_t>(b), s.line});
                    waitClock(nextTick);
                    break;
                }

                case Kind::Jump:
                    pc = targetIndex(evaluate(s.p[0]), code.size(), s.line);
                    advance = false;
                    break;

                case Kind::ForJump: {
                    auto it = fjRemain.find(pc);
                    if (it == fjRemain.end()) {
                        const int count = evaluate(s.p[1]);
                        if (count < 0) throw std::runtime_error("fj repeat count must be >= 0 at line " + std::to_string(s.line));
                        if (count == 0) break;
                        it = fjRemain.emplace(pc, count).first;
                    }

                    if (it->second > 0) {
                        --it->second;
                        pc = targetIndex(evaluate(s.p[0]), code.size(), s.line);
                        advance = false;
                    } else {
                        fjRemain.erase(it);
                    }
                    break;
                }
            }

            if (advance) ++pc;
        }
    }

    void run16(const std::vector<WideInstruction>& code) {
        auto nextTick = std::chrono::steady_clock::now();
        for (const WideInstruction& wi : code) {
#ifdef _WIN32
            if (!display_.windowOpen())
                throw std::runtime_error("VGA window was closed while executing the program");
#endif
            executeWide(wi);
            waitClock(nextTick);
        }
    }

    void prompt() {
        std::string line;
        for (;;) {
#ifdef _WIN32
            if (!display_.windowOpen())
                break;
#endif
            std::cout << "8c> " << std::flush;
            if (!std::getline(std::cin, line)) break;
            line = trim(line);
            if (line.empty()) continue;

            const auto words = splitWords(line);
            const std::string cmd = words.empty() ? std::string{} : lower(words[0]);
            if (cmd == "quit" || cmd == "exit") break;

            try {
                if (cmd == "hex") {
                    executeWide(parseHexPromptInstruction(line));
                } else {
                    execute(parsePromptInstruction(line));
                }
            } catch (const std::exception& e) {
                std::cout << "ERROR: " << e.what() << '\n' << std::flush;
            }
        }
    }

private:
    double hz_;
    std::array<std::array<uint8_t, MEM_BLOCKS>, MEM_SPACES> memory_{};
    std::unordered_map<uint64_t, uint32_t> wideMemory_;
    std::unordered_map<std::string, int> vars_;
    Display display_;

    class ExpressionParser {
    public:
        ExpressionParser(const VM& vm, const std::string& text) : vm_(vm), text_(text) {}

        int parse() {
            skipSpace();
            if (pos_ == text_.size()) throw std::runtime_error("empty expression");
            const int64_t result = parseAddSub();
            skipSpace();
            if (pos_ != text_.size())
                throw std::runtime_error("unexpected character in expression: " + std::string(1, text_[pos_]));
            if (result < std::numeric_limits<int>::min() || result > std::numeric_limits<int>::max())
                throw std::runtime_error("expression result is out of 32-bit signed range");
            return static_cast<int>(result);
        }

    private:
        const VM& vm_;
        const std::string& text_;
        size_t pos_ = 0;

        void skipSpace() {
            while (pos_ < text_.size() && std::isspace(static_cast<unsigned char>(text_[pos_]))) ++pos_;
        }

        static int64_t checkedAdd(int64_t a, int64_t b) {
            if ((b > 0 && a > std::numeric_limits<int64_t>::max() - b) ||
                (b < 0 && a < std::numeric_limits<int64_t>::min() - b))
                throw std::runtime_error("expression arithmetic overflow");
            return a + b;
        }

        static int64_t checkedSub(int64_t a, int64_t b) {
            if ((b < 0 && a > std::numeric_limits<int64_t>::max() + b) ||
                (b > 0 && a < std::numeric_limits<int64_t>::min() + b))
                throw std::runtime_error("expression arithmetic overflow");
            return a - b;
        }

        static int64_t checkedMul(int64_t a, int64_t b) {
            if (a == 0 || b == 0) return 0;
            if (a == -1 && b == std::numeric_limits<int64_t>::min())
                throw std::runtime_error("expression arithmetic overflow");
            if (b == -1 && a == std::numeric_limits<int64_t>::min())
                throw std::runtime_error("expression arithmetic overflow");
            if (a > 0) {
                if (b > 0 && a > std::numeric_limits<int64_t>::max() / b)
                    throw std::runtime_error("expression arithmetic overflow");
                if (b < 0 && b < std::numeric_limits<int64_t>::min() / a)
                    throw std::runtime_error("expression arithmetic overflow");
            } else {
                if (b > 0 && a < std::numeric_limits<int64_t>::min() / b)
                    throw std::runtime_error("expression arithmetic overflow");
                if (b < 0 && a < std::numeric_limits<int64_t>::max() / b)
                    throw std::runtime_error("expression arithmetic overflow");
            }
            return a * b;
        }

        static int64_t checkedDiv(int64_t a, int64_t b) {
            if (b == 0) throw std::runtime_error("division by zero");
            if (a == std::numeric_limits<int64_t>::min() && b == -1)
                throw std::runtime_error("expression arithmetic overflow");
            return a / b;
        }

        int64_t parseAddSub() {
            int64_t value = parseMulDiv();
            for (;;) {
                skipSpace();
                if (pos_ >= text_.size() || (text_[pos_] != '+' && text_[pos_] != '-')) return value;
                const char op = text_[pos_++];
                const int64_t rhs = parseMulDiv();
                value = (op == '+') ? checkedAdd(value, rhs) : checkedSub(value, rhs);
            }
        }

        int64_t parseMulDiv() {
            int64_t value = parseUnary();
            for (;;) {
                skipSpace();
                if (pos_ >= text_.size() || (text_[pos_] != '*' && text_[pos_] != '/')) return value;
                const char op = text_[pos_++];
                const int64_t rhs = parseUnary();
                value = (op == '*') ? checkedMul(value, rhs) : checkedDiv(value, rhs);
            }
        }

        int64_t parseUnary() {
            skipSpace();
            if (pos_ < text_.size() && (text_[pos_] == '+' || text_[pos_] == '-')) {
                const char op = text_[pos_++];
                const int64_t value = parseUnary();
                if (op == '-' && value == std::numeric_limits<int64_t>::min())
                    throw std::runtime_error("expression arithmetic overflow");
                return op == '-' ? -value : value;
            }
            return parsePrimary();
        }

        int64_t parsePrimary() {
            skipSpace();
            if (pos_ >= text_.size())
                throw std::runtime_error("missing expression operand");

            if (text_[pos_] == '(') {
                ++pos_;
                const int64_t value = parseAddSub();
                skipSpace();
                if (pos_ >= text_.size() || text_[pos_] != ')')
                    throw std::runtime_error("missing ')' in expression");
                ++pos_;
                return value;
            }

            const char first = text_[pos_];
            if (std::isdigit(static_cast<unsigned char>(first))) {
                const size_t begin = pos_;
                while (pos_ < text_.size() &&
                       (std::isalnum(static_cast<unsigned char>(text_[pos_])) || text_[pos_] == '_'))
                    ++pos_;
                return parseInteger(text_.substr(begin, pos_ - begin));
            }

            if (std::isalpha(static_cast<unsigned char>(first)) || first == '_') {
                const size_t begin = pos_;
                ++pos_;
                while (pos_ < text_.size()) {
                    const unsigned char c = static_cast<unsigned char>(text_[pos_]);
                    if (!std::isalnum(c) && text_[pos_] != '_') break;
                    ++pos_;
                }
                const std::string name = text_.substr(begin, pos_ - begin);
                const auto it = vm_.vars_.find(name);
                if (it == vm_.vars_.end())
                    throw std::runtime_error("unknown variable: " + name);
                return it->second;
            }

            throw std::runtime_error("invalid expression at position " + std::to_string(pos_));
        }
    };

    int evaluate(const std::string& expr) const {
        return ExpressionParser(*this, expr).parse();
    }

    static int requireU8(int value, const std::string& label) {
        if (value < 0 || value > 255)
            throw std::runtime_error(label + " must be 0..255");
        return value;
    }

    int fixedOrValue(const std::string& token, int bits, const std::string& label) const {
        if (bits < 1 || bits > 31)
            throw std::runtime_error("unsupported field width: " + std::to_string(bits));
        const int value = exactBinary(token, static_cast<size_t>(bits))
                               ? parseBinaryFixed(token, bits, label)
                               : evaluate(token);
        const int maxValue = static_cast<int>((uint32_t{1} << bits) - 1U);
        if (value < 0 || value > maxValue)
            throw std::runtime_error(label + " must fit in " + std::to_string(bits) + " bits");
        return value;
    }

    static size_t targetIndex(int line, size_t size, int sourceLine) {
        if (line < 0 || static_cast<size_t>(line) >= size)
            throw std::runtime_error("jump target " + std::to_string(line) + " is invalid at line " + std::to_string(sourceLine));
        return static_cast<size_t>(line);
    }

    static std::string binaryLine(uint32_t value) {
        return binFixed(value, 32);
    }

    void execute(const MachineInstruction& mi) {
        switch (mi.opcode) {
            case 1: {
                const uint8_t volume = static_cast<uint8_t>(mi.input0 & 0x0FU);
                const uint8_t waveform = mi.input1;
                const uint8_t durationMs = mi.input2;

#ifdef _WIN32
                if (durationMs == 0)
                    break;

                // One 8-bit pattern is one waveform period.
                // 8 samples per period at 8192 Hz -> 1024 Hz base frequency.
                constexpr DWORD sampleRate = 8192;
                constexpr int samplesPerPattern = 8;
                const size_t sampleCount =
                    static_cast<size_t>((static_cast<uint64_t>(sampleRate) * durationMs + 999U) / 1000U);

                std::vector<uint8_t> samples(sampleCount);
                const int amplitude = static_cast<int>((static_cast<unsigned>(volume) * 127U) / 15U);
                for (size_t i = 0; i < sampleCount; ++i) {
                    const int bit = (waveform >> (7 - static_cast<int>(i % samplesPerPattern))) & 1;
                    samples[i] = static_cast<uint8_t>(128 + (bit ? amplitude : -amplitude));
                }

                WAVEFORMATEX format{};
                format.wFormatTag = WAVE_FORMAT_PCM;
                format.nChannels = 1;
                format.nSamplesPerSec = sampleRate;
                format.wBitsPerSample = 8;
                format.nBlockAlign = 1;
                format.nAvgBytesPerSec = sampleRate;

                HWAVEOUT waveOut = nullptr;
                MMRESULT result = waveOutOpen(
                    &waveOut,
                    WAVE_MAPPER,
                    &format,
                    0,
                    0,
                    CALLBACK_NULL
                );
                if (result != MMSYSERR_NOERROR)
                    throw std::runtime_error("waveOutOpen failed: " + std::to_string(result));

                WAVEHDR header{};
                header.lpData = reinterpret_cast<LPSTR>(samples.data());
                header.dwBufferLength = static_cast<DWORD>(samples.size());

                result = waveOutPrepareHeader(waveOut, &header, sizeof(header));
                if (result != MMSYSERR_NOERROR) {
                    waveOutClose(waveOut);
                    throw std::runtime_error("waveOutPrepareHeader failed: " + std::to_string(result));
                }

                result = waveOutWrite(waveOut, &header, sizeof(header));
                if (result != MMSYSERR_NOERROR) {
                    waveOutUnprepareHeader(waveOut, &header, sizeof(header));
                    waveOutClose(waveOut);
                    throw std::runtime_error("waveOutWrite failed: " + std::to_string(result));
                }

                while ((header.dwFlags & WHDR_DONE) == 0)
                    std::this_thread::sleep_for(std::chrono::milliseconds(1));

                waveOutUnprepareHeader(waveOut, &header, sizeof(header));
                waveOutClose(waveOut);
#else
                (void)volume;
                (void)waveform;
                std::cout << '\a' << std::flush;
                std::this_thread::sleep_for(std::chrono::milliseconds(durationMs));
#endif
                break;
            }

            case 2: {
                // INPUT0: memory space (0000 = space 1, 0001 = space 2)
                // INPUT1: 8-bit block address (0..255)
                // INPUT2: 8-bit value
                if (mi.input0 > 1)
                    throw std::runtime_error("RAM space must be 0000 or 0001");
                memory_[mi.input0][mi.input1] = mi.input2;
                break;
            }

            case 3: {
                if (mi.input0 > 1)
                    throw std::runtime_error("RAM space must be 0000 or 0001");
                const uint8_t value = memory_[mi.input0][mi.input1];
                showMessage("RAM = " + binFixed(value, 8));
                break;
            }

            case 4: {
                const uint8_t rgb = static_cast<uint8_t>((mi.input0 >> 1) & 7U);
                const uint8_t mode = static_cast<uint8_t>(mi.input0 & 1U);
                const int y = mi.input1 >> 5;
                const int x = mi.input1 & 31;
                if (y >= CUI_H || x >= CUI_W)
                    throw std::runtime_error("VGA coordinate out of range");
                if (mode == 0)
                    display_.background(x, y, rgb);
                else
                    display_.put(x, y, static_cast<char>(mi.input2), rgb);
                display_.render();
                break;
            }

            case 5:
            case 6:
            case 7:
            case 8: {
                const uint32_t a = mi.input1;
                const uint32_t b = mi.input2;
                int64_t result = 0;
                switch (mi.opcode) {
                    case 5: result = static_cast<int64_t>(a) + b; break;
                    case 6: result = static_cast<int64_t>(a) - b; break;
                    case 7: result = static_cast<int64_t>(a) * b; break;
                    case 8:
                        if (b == 0) throw std::runtime_error("division by zero");
                        result = a / b;
                        break;
                }
                showMessage(operationName(mi.opcode) + " " + std::to_string(a) + operationSymbol(mi.opcode) + std::to_string(b) + "=" + std::to_string(result) + "\n" + binaryLine(static_cast<uint32_t>(result)) + "\nDEC=" + std::to_string(result));
                break;
            }

            default:
                throw std::runtime_error("unknown opcode: " + std::to_string(mi.opcode));
        }
    }

    void executeWide(const WideInstruction& wi) {
        switch (wi.opcode) {
            case 1: { // 1024Hz-equivalent programmable waveform
#ifdef _WIN32
                if (wi.input2 == 0)
                    break;

                // 32 samples per period at 32768 Hz -> 1024 Hz base frequency.
                constexpr DWORD sampleRate = 32768;
                constexpr size_t samplesPerPattern = 32;
                constexpr uint32_t chunkMs = 1000;
                constexpr size_t chunkSamples = sampleRate * chunkMs / 1000;

                const uint32_t durationMs = wi.input2;
                const int amplitude = static_cast<int>((static_cast<uint64_t>(wi.input0) * 127ULL) / 65535ULL);
                const uint32_t pattern = wi.input1;

                WAVEFORMATEX format{};
                format.wFormatTag = WAVE_FORMAT_PCM;
                format.nChannels = 1;
                format.nSamplesPerSec = sampleRate;
                format.wBitsPerSample = 8;
                format.nBlockAlign = 1;
                format.nAvgBytesPerSec = sampleRate;

                HWAVEOUT waveOut = nullptr;
                MMRESULT result = waveOutOpen(&waveOut, WAVE_MAPPER, &format, 0, 0, CALLBACK_NULL);
                if (result != MMSYSERR_NOERROR)
                    throw std::runtime_error("waveOutOpen failed: " + std::to_string(result));

                uint64_t totalSamples = (static_cast<uint64_t>(sampleRate) * durationMs + 999ULL) / 1000ULL;
                uint64_t generated = 0;

                while (generated < totalSamples) {
                    const size_t count = static_cast<size_t>(std::min<uint64_t>(chunkSamples, totalSamples - generated));
                    std::vector<uint8_t> samples(count);
                    for (size_t i = 0; i < count; ++i) {
                        const uint64_t sampleIndex = generated + i;
                        const int bitIndex = 31 - static_cast<int>(sampleIndex % samplesPerPattern);
                        const int bit = (pattern >> bitIndex) & 1U;
                        samples[i] = static_cast<uint8_t>(128 + (bit ? amplitude : -amplitude));
                    }

                    WAVEHDR header{};
                    header.lpData = reinterpret_cast<LPSTR>(samples.data());
                    header.dwBufferLength = static_cast<DWORD>(samples.size());

                    result = waveOutPrepareHeader(waveOut, &header, sizeof(header));
                    if (result != MMSYSERR_NOERROR) {
                        waveOutClose(waveOut);
                        throw std::runtime_error("waveOutPrepareHeader failed: " + std::to_string(result));
                    }

                    result = waveOutWrite(waveOut, &header, sizeof(header));
                    if (result != MMSYSERR_NOERROR) {
                        waveOutUnprepareHeader(waveOut, &header, sizeof(header));
                        waveOutClose(waveOut);
                        throw std::runtime_error("waveOutWrite failed: " + std::to_string(result));
                    }

                    while ((header.dwFlags & WHDR_DONE) == 0)
                        std::this_thread::sleep_for(std::chrono::milliseconds(1));

                    waveOutUnprepareHeader(waveOut, &header, sizeof(header));
                    generated += count;
                }

                waveOutClose(waveOut);
#else
                std::this_thread::sleep_for(std::chrono::milliseconds(wi.input2));
#endif
                break;
            }

            case 2: { // sparse 32-bit word RAM
                const uint64_t key = (static_cast<uint64_t>(wi.input0) << 32) | wi.input1;
                wideMemory_[key] = wi.input2;
                break;
            }

            case 3: {
                const uint64_t key = (static_cast<uint64_t>(wi.input0) << 32) | wi.input1;
                const uint32_t value = [&] {
                    const auto it = wideMemory_.find(key);
                    return it == wideMemory_.end() ? 0U : it->second;
                }();
                showMessage("RAM32=" + hexFixed(value, 8) + "\nDEC=" + std::to_string(value));
                break;
            }

            case 4: {
                // HEX VGA text format:
                //
                //   04 F800 10101010 00000041
                //    |  |    |        |
                //    |  |    |        +-- ASCII, exactly 8 HEX digits
                //    |  |    +----------- VGA coordinate, exactly 8 BIN bits
                //    |  +---------------- RGB565 color, exactly 4 HEX digits
                //    +------------------- VGA opcode, exactly 2 HEX digits
                //
                // Coordinate layout is the original VGA YYYXXXXX:
                //   Y = bits 7..5 (0..7)
                //   X = bits 4..0 (0..31)
                //
                // input0 = RGB565
                // input1 = 8-bit YYYXXXXX stored in the low byte of a 32-bit field
                // input2 = ASCII value stored as a 32-bit value
                const uint16_t color565 = wi.input0;

                if (wi.input1 > 0xFFU)
                    throw std::runtime_error("HEX VGA coordinate must use exactly 8 binary bits (YYYXXXXX)");

                if (wi.input2 > 0x7FU)
                    throw std::runtime_error("HEX VGA character must be ASCII (00..7F)");

                const uint8_t coord = static_cast<uint8_t>(wi.input1);
                const uint8_t y = static_cast<uint8_t>((coord >> 5) & 0x07U);
                const uint8_t x = static_cast<uint8_t>(coord & 0x1FU);
                const uint8_t ch = static_cast<uint8_t>(wi.input2);

                display_.wideText(x, y, color565, ch);
                break;
            }

            case 5:
            case 6:
            case 7:
            case 8: {
                const int64_t a = static_cast<int64_t>(wi.input1);
                const int64_t b = static_cast<int64_t>(wi.input2);
                int64_t result = 0;
                switch (wi.opcode) {
                    case 5:
                        if (b > 0 && a > INT64_MAX - b)
                            throw std::runtime_error("wide ADD overflow");
                        result = a + b;
                        break;
                    case 6:
                        if (b < 0 && a > INT64_MAX + b)
                            throw std::runtime_error("wide SUB overflow");
                        if (b > 0 && a < INT64_MIN + b)
                            throw std::runtime_error("wide SUB overflow");
                        result = a - b;
                        break;
                    case 7:
                        if (a != 0 && b > INT64_MAX / a)
                            throw std::runtime_error("wide MUL overflow");
                        result = a * b;
                        break;
                    case 8:
                        if (b == 0)
                            throw std::runtime_error("division by zero");
                        result = a / b;
                        break;
                }
                const uint64_t bits = static_cast<uint64_t>(result);
                showMessage("OP" + std::to_string(wi.opcode) + "=" + hexFixed(bits, 16) + "\nDEC=" + std::to_string(result));
                break;
            }

            default:
                throw std::runtime_error("unknown wide opcode: " + std::to_string(wi.opcode));
        }
    }

    void showMessage(const std::string& msg) {
        display_.clear();
        int x = 0;
        int y = 0;
        for (char ch : msg) {
            if (ch == '\n' || x >= CUI_W) {
                ++y;
                x = 0;
                if (ch == '\n') continue;
            }
            if (y >= CUI_H) break;
            display_.put(x++, y, ch, 0);
        }
        display_.render();
    }

    void waitClock(std::chrono::steady_clock::time_point& nextTick) const {
        auto period = std::chrono::duration_cast<std::chrono::steady_clock::duration>(
            std::chrono::duration<double>(1.0 / hz_));
        if (period <= std::chrono::steady_clock::duration::zero())
            period = std::chrono::nanoseconds(1);

        nextTick += period;
        const auto now = std::chrono::steady_clock::now();
        if (nextTick > now)
            std::this_thread::sleep_until(nextTick);
        else
            nextTick = now;
    }

    static std::string operationName(uint8_t opcode) {
        switch (opcode) {
            case 5: return "ADD ";
            case 6: return "SUB ";
            case 7: return "MUL ";
            case 8: return "DIV ";
            default: return "OP ";
        }
    }

    static std::string operationSymbol(uint8_t opcode) {
        switch (opcode) {
            case 5: return "+";
            case 6: return "-";
            case 7: return "*";
            case 8: return "/";
            default: return "?";
        }
    }

    static MachineInstruction parsePromptInstruction(const std::string& line) {
        const auto words = splitWords(line);
        if (words.size() != 4)
            throw std::runtime_error("use: <OP4> <IN0 4> <IN1 8> <IN2 8>");
        return {
            static_cast<uint8_t>(parseBinaryFixed(words[0], 4, "opcode")),
            static_cast<uint8_t>(parseBinaryFixed(words[1], 4, "input0")),
            static_cast<uint8_t>(parseBinaryFixed(words[2], 8, "input1")),
            static_cast<uint8_t>(parseBinaryFixed(words[3], 8, "input2")),
            0
        };
    }

    static WideInstruction parseHexPromptInstruction(const std::string& line) {
        const auto words = splitWords(line);
        if (words.size() != 5 || lower(words[0]) != "hex")
            throw std::runtime_error(
                "use: hex <OP2> <COLOR/INPUT0 4hex> <COORD 8bin for VGA> <ASCII 8hex for VGA>");

        const uint8_t opcode =
            static_cast<uint8_t>(parseHexFixed(words[1], 2, "hex opcode"));

        if (opcode == 0x04U) {
            // VGA is intentionally mixed-format:
            // opcode=2 HEX, color=4 HEX, coordinate=8 BIN, ASCII=8 HEX.
            const uint16_t color565 =
                static_cast<uint16_t>(parseHexFixed(words[2], 4, "HEX VGA color"));
            const uint32_t coord =
                static_cast<uint32_t>(parseBinaryFixed(words[3], 8, "HEX VGA coordinate"));
            const uint32_t ascii =
                static_cast<uint32_t>(parseHexFixed(words[4], 8, "HEX VGA ASCII"));

            if (ascii > 0x7FU)
                throw std::runtime_error("HEX VGA ASCII must fit in 00..7F");

            return {
                opcode,
                color565,
                coord,
                ascii,
                0
            };
        }

        // Other wide instructions retain the original all-HEX prompt format.
        return {
            opcode,
            static_cast<uint16_t>(parseHexFixed(words[2], 4, "hex input0")),
            static_cast<uint32_t>(parseHexFixed(words[3], 8, "hex input1")),
            static_cast<uint32_t>(parseHexFixed(words[4], 8, "hex input2")),
            0
        };
    }
};

class Parser {
public:
    std::vector<ScriptInstruction> parseFile(const std::string& path) const {
        std::ifstream file(path);
        if (!file) throw std::runtime_error("cannot open file: " + path);

        std::vector<ScriptInstruction> code;
        std::string line;
        int physicalLine = 0;
        int logicalLine = 0;

        while (std::getline(file, line)) {
            ++physicalLine;
            line = removeComment(line);
            if (line.empty()) continue;
            try {
                code.push_back(parse(line, logicalLine));
                ++logicalLine;
            } catch (const std::exception& e) {
                throw std::runtime_error(".8 line " + std::to_string(physicalLine) + ": " + e.what());
            }
        }
        if (file.bad())
            throw std::runtime_error("failed while reading .8 file: " + path);
        return code;
    }

private:
    static ScriptInstruction make(Kind kind, int line) {
        ScriptInstruction s{};
        s.kind = kind;
        s.line = line;
        return s;
    }

    static ScriptInstruction parse(const std::string& line, int logicalLine) {
        const size_t eq = line.find('=');
        if (eq != std::string::npos) {
            ScriptInstruction s = make(Kind::Set, logicalLine);
            s.name = trim(line.substr(0, eq));
            s.p[0] = trim(line.substr(eq + 1));
            if (!validIdentifier(s.name)) throw std::runtime_error("invalid variable name: " + s.name);
            if (s.p[0].empty()) throw std::runtime_error("empty assignment");
            return s;
        }

        const auto w = splitWords(line);
        if (w.empty()) throw std::runtime_error("empty command");
        const std::string cmd = lower(w[0]);

        if (cmd == "beep") {
            if (w.size() != 4) throw std::runtime_error("beep <volume4> <waveform8> <duration8>");
            ScriptInstruction s = make(Kind::Beep, logicalLine);
            s.p[0] = w[1];
            s.p[1] = w[2];
            s.p[2] = w[3];
            return s;
        }

        if (cmd == "bin") {
            if (w.size() != 5) throw std::runtime_error("bin <OP> <IN0> <IN1> <IN2>");
            ScriptInstruction s = make(Kind::Machine, logicalLine);
            // Fields are kept as expressions and converted to their exact widths at runtime.
            s.machine = {};
            s.p[0] = w[1]; s.p[1] = w[2]; s.p[2] = w[3]; s.p[3] = w[4];
            return s;
        }

        if (cmd == "ramw") {
            if (w.size() != 4) throw std::runtime_error("ramw <space4> <addr8> <value8>");
            ScriptInstruction s = make(Kind::RamWrite, logicalLine);
            s.p[0]=w[1]; s.p[1]=w[2]; s.p[2]=w[3];
            return s;
        }

        if (cmd == "ramr") {
            if (w.size() != 4) throw std::runtime_error("ramr <space4> <addr8> <unused8>");
            ScriptInstruction s = make(Kind::RamRead, logicalLine);
            s.p[0] = w[1];
            s.p[1] = w[2];
            s.p[2] = w[3];
            return s;
        }

        if (cmd == "vga") {
            if (w.size() != 4) throw std::runtime_error("vga <input0 4> <input1 8> <input2 8>");
            ScriptInstruction s = make(Kind::Vga, logicalLine);
            s.p[0] = w[1];
            s.p[1] = w[2];
            s.p[2] = w[3];
            return s;
        }

        const std::array<std::pair<const char*, int>, 4> ops{{
            {"add",5}, {"sub",6}, {"mul",7}, {"div",8}
        }};
        for (const auto& [name, opcode] : ops) {
            if (cmd == name) {
                if (w.size() != 3) throw std::runtime_error(std::string(name) + " <operand1> <operand2>");
                ScriptInstruction s = make(Kind::Arithmetic, logicalLine);
                s.p[0] = std::to_string(opcode);
                s.p[1] = w[1];
                s.p[2] = w[2];
                return s;
            }
        }

        if (cmd == "jump") {
            if (w.size() != 2) throw std::runtime_error("jump <line0>");
            ScriptInstruction s = make(Kind::Jump, logicalLine);
            s.p[0] = w[1];
            return s;
        }

        if (cmd == "fj") {
            if (w.size() != 3) throw std::runtime_error("fj <line0> <repeat_count>");
            ScriptInstruction s = make(Kind::ForJump, logicalLine);
            s.p[0] = w[1];
            s.p[1] = w[2];
            return s;
        }

        throw std::runtime_error("unknown .8 command: " + w[0]);
    }
};

enum class SourceKind { Script8, Machine16 };

static SourceKind requireSupportedFile(const std::string& path) {
    if (path.size() >= 2 && lower(path.substr(path.size() - 2)) == ".8")
        return SourceKind::Script8;
    if (path.size() >= 3 && lower(path.substr(path.size() - 3)) == ".16")
        return SourceKind::Machine16;
    throw std::runtime_error("first argument must be a .8 or .16 file");
}

static std::vector<WideInstruction> load16File(const std::string& path) {
    std::ifstream file(path, std::ios::binary);
    if (!file) throw std::runtime_error("cannot open .16 file: " + path);

    std::vector<WideInstruction> code;
    std::array<uint8_t, WIDE_INSTRUCTION_SIZE> raw{};
    uint64_t offset = 0;

    for (;;) {
        file.read(reinterpret_cast<char*>(raw.data()), static_cast<std::streamsize>(raw.size()));
        const std::streamsize got = file.gcount();

        if (got == 0) {
            if (file.bad() || (file.fail() && !file.eof()))
                throw std::runtime_error("failed while reading .16 file at offset " + std::to_string(offset));
            break;
        }

        if (got != static_cast<std::streamsize>(raw.size()))
            throw std::runtime_error(
                ".16 instruction at offset " + std::to_string(offset) +
                " must contain exactly 11 bytes"
            );

        WideInstruction wi{};
        wi.opcode = raw[0];
        wi.input0 = static_cast<uint16_t>((static_cast<uint16_t>(raw[1]) << 8) | raw[2]);
        wi.input1 = (static_cast<uint32_t>(raw[3]) << 24) |
                    (static_cast<uint32_t>(raw[4]) << 16) |
                    (static_cast<uint32_t>(raw[5]) << 8) |
                    static_cast<uint32_t>(raw[6]);
        wi.input2 = (static_cast<uint32_t>(raw[7]) << 24) |
                    (static_cast<uint32_t>(raw[8]) << 16) |
                    (static_cast<uint32_t>(raw[9]) << 8) |
                    static_cast<uint32_t>(raw[10]);
        wi.fileOffset = offset;
        code.push_back(wi);
        offset += WIDE_INSTRUCTION_SIZE;

        // '$' separates .16 commands. A final separator is optional.
        const int next = file.peek();
        if (next == EOF)
            break;

        if (static_cast<uint8_t>(next) != WIDE_INSTRUCTION_SEPARATOR) {
            throw std::runtime_error(
                ".16 commands must be separated by '$' (0x24) after instruction at offset " +
                std::to_string(wi.fileOffset)
            );
        }

        file.get();
        ++offset; // '$' is one byte in the .16 file, so include it in the next file offset.
    }

    return code;
}

} // namespace eightc

int main(int argc, char** argv) {
    using namespace eightc;

    try {
        std::string file;
        double hz = 1024.0;
        SourceKind sourceKind = SourceKind::Script8;

        if (argc == 1) {
            // Double-click / plain execution: open an idle 8c machine at 1024 Hz.
        } else if (argc == 3) {
            file = argv[1];
            sourceKind = requireSupportedFile(file);
            hz = parseClockHz(argv[2]);
        } else {
            std::cerr << "Usage: 8c [file.8|file.16 clock_hz]\n";
            return 2;
        }

        // Parse the program before creating the GUI so a source-file error does not
        // create a window only to destroy it again during exception unwinding.
        std::vector<ScriptInstruction> program8;
        std::vector<WideInstruction> program16;

        if (!file.empty()) {
            if (sourceKind == SourceKind::Script8)
                program8 = Parser{}.parseFile(file);
            else
                program16 = load16File(file);
        }

        VM vm(hz);

        vm.display().setup();
        vm.display().clearAll();

#ifdef _WIN32

        // Console and VGA are a single 8c instance. Closing either one
        // immediately terminates the whole process.
        std::atomic<bool> windowMonitorRunning{true};
        std::thread windowMonitor([&windowMonitorRunning]() {
            for (;;) {
                if (!windowMonitorRunning.load(std::memory_order_acquire))
                    return;

                const HWND console = GetConsoleWindow();
                if (console == nullptr || !IsWindow(console))
                    ExitProcess(0);

                const HWND vga = FindWindowA("8cVGAWindowClass", "8c VGA 32x8");
                if (vga == nullptr || !IsWindow(vga))
                    ExitProcess(0);

                std::this_thread::sleep_for(std::chrono::milliseconds(50));
            }
        });

        try {
            if (sourceKind == SourceKind::Script8) {
                if (!program8.empty())
                    vm.run(program8);
            } else {
                vm.run16(program16);
            }

            vm.prompt();
        } catch (...) {
            windowMonitorRunning.store(false, std::memory_order_release);
            if (windowMonitor.joinable())
                windowMonitor.join();
            throw;
        }

        windowMonitorRunning.store(false, std::memory_order_release);
        if (windowMonitor.joinable())
            windowMonitor.join();

#else

        if (sourceKind == SourceKind::Script8) {
            if (!program8.empty())
                vm.run(program8);
        } else {
            vm.run16(program16);
        }

        vm.prompt();

#endif

        return 0;

    } catch (const std::exception& e) {
        std::cerr << "8c: ERROR: " << e.what() << '\n';
        return 1;
    }
}
