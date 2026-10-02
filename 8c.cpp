// 8c.cpp
// g++ -std=c++17 -O2 -Wall -Wextra -pedantic -static -mconsole 8c.cpp version.o -o 8c.exe -lgdi32 -lwinmm

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
constexpr int MEM_BLOCKS = 8;
constexpr int MEM_SPACES = 2;

struct Cell {
    char ch = ' ';
    uint8_t bg = 0; // RGB bit order: R=4, G=2, B=1.
};

struct MachineInstruction {
    uint8_t opcode = 0;
    uint8_t input0 = 0;
    uint8_t input1 = 0;
    uint8_t input2 = 0;
    int line = 0;
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
    while (!s.empty() && std::isspace(static_cast<unsigned char>(s.front()))) s.erase(s.begin());
    while (!s.empty() && std::isspace(static_cast<unsigned char>(s.back()))) s.pop_back();
    return s;
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

static int parseInteger(const std::string& s) {
    if (s.empty()) throw std::runtime_error("empty number");
    size_t pos = 0;
    const long long value = std::stoll(s, &pos, 0);
    if (pos != s.size()) throw std::runtime_error("invalid number: " + s);
    if (value < -2147483648LL || value > 2147483647LL)
        throw std::runtime_error("number out of 32-bit signed range: " + s);
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
        if (hwnd != nullptr) {
            PostMessageA(hwnd, WM_CLOSE, 0, 0);
        }
        if (guiThread_.joinable()) {
            guiThread_.join();
        }
#endif
    }

    void clear() {
        std::lock_guard<std::mutex> lock(cellMutex_);
        for (auto& c : cells_) c = Cell{};
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

private:
    std::array<Cell, CUI_W * CUI_H> cells_{};
    mutable std::mutex cellMutex_;

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

        if (!PostMessageA(hwnd, WM_VGA_INVALIDATE, 0, 0)) {
            repaintQueued_.store(false, std::memory_order_release);
        }
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
                RECT client{};
                GetClientRect(hwnd, &client);

                const int cellW = std::max(1L, (client.right - client.left) / CUI_W);
                const int cellH = std::max(1L, (client.bottom - client.top) / CUI_H);

                std::array<Cell, CUI_W * CUI_H> copy{};
                {
                    std::lock_guard<std::mutex> lock(self->cellMutex_);
                    copy = self->cells_;
                }

                HGDIOBJ oldFont = self->font_ != nullptr ? SelectObject(dc, self->font_) : nullptr;
                SetBkMode(dc, TRANSPARENT);
                SetTextColor(dc, RGB(255, 255, 255));

                for (int y = 0; y < CUI_H; ++y) {
                    for (int x = 0; x < CUI_W; ++x) {
                        const Cell& c = copy[static_cast<size_t>(y * CUI_W + x)];
                        RECT r{
                            x * cellW,
                            y * cellH,
                            (x + 1) * cellW,
                            (y + 1) * cellH
                        };
                        HBRUSH brush = self->brushes_[c.bg & 7U];
                        if (brush != nullptr) FillRect(dc, &r, brush);

                        char text[2]{c.ch == '\0' ? ' ' : c.ch, '\0'};
                        DrawTextA(dc, text, 1, &r, DT_CENTER | DT_VCENTER | DT_SINGLELINE | DT_NOPREFIX);
                    }
                }

                if (oldFont != nullptr) SelectObject(dc, oldFont);
                EndPaint(hwnd, &ps);
                return 0;
            }

            case WM_CLOSE:
                DestroyWindow(hwnd);
                return 0;

            case WM_DESTROY:
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
        return DefWindowProcA(hwnd, msg, wp, lp);
    }

    void guiMain() {
        const char* className = "8cVGAWindowClass";
        HINSTANCE instance = GetModuleHandleA(nullptr);

        WNDCLASSA wc{};
        wc.lpfnWndProc = wndProc;
        wc.hInstance = instance;
        wc.lpszClassName = className;
        wc.hCursor = LoadCursorA(nullptr, IDC_ARROW);
        wc.hbrBackground = reinterpret_cast<HBRUSH>(GetStockObject(BLACK_BRUSH));
        const ATOM atom = RegisterClassA(&wc);
        if (atom == 0 && GetLastError() != ERROR_CLASS_ALREADY_EXISTS) {
            std::lock_guard<std::mutex> lock(guiMutex_);
            guiError_ = "RegisterClassA failed.";
            guiReadyFlag_ = true;
            guiReady_.notify_one();
            return;
        }

        // 16x24 logical cell size -> exact 32x8 character grid in the client area.
        const int clientW = 32 * 16;
        const int clientH = 8 * 24;
        RECT wr{0, 0, clientW, clientH};
        AdjustWindowRect(&wr, WS_OVERLAPPED | WS_CAPTION | WS_SYSMENU | WS_MINIMIZEBOX, FALSE);

        HWND hwnd = CreateWindowExA(
            0,
            className,
            "8c VGA 32x8",
            WS_OVERLAPPED | WS_CAPTION | WS_SYSMENU | WS_MINIMIZEBOX,
            CW_USEDEFAULT,
            CW_USEDEFAULT,
            wr.right - wr.left,
            wr.bottom - wr.top,
            nullptr,
            nullptr,
            instance,
            this
        );

        if (hwnd == nullptr) {
            std::lock_guard<std::mutex> lock(guiMutex_);
            guiError_ = "CreateWindowExA failed. Error=" + std::to_string(GetLastError());
            guiReadyFlag_ = true;
            guiReady_.notify_one();
            return;
        }

        font_ = CreateFontA(
            22, 0, 0, 0,
            FW_NORMAL,
            FALSE, FALSE, FALSE,
            ANSI_CHARSET,
            OUT_DEFAULT_PRECIS,
            CLIP_DEFAULT_PRECIS,
            DEFAULT_QUALITY,
            FIXED_PITCH | FF_MODERN,
            "Consolas"
        );

        for (size_t i = 0; i < brushes_.size(); ++i)
            brushes_[i] = CreateSolidBrush(static_cast<COLORREF>(bgColor(static_cast<uint8_t>(i))));

        if (font_ == nullptr) {
            {
                std::lock_guard<std::mutex> lock(guiMutex_);
                guiError_ = "CreateFontA failed.";
                guiReadyFlag_ = true;
            }
            guiReady_.notify_one();
            DestroyWindow(hwnd);
            return;
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
                    const int address = fixedOrValue(s.p[0], 4, "RAM address");
                    const int space = fixedOrValue(s.p[1], 8, "RAM space");
                    const int value = fixedOrValue(s.p[2], 8, "RAM value");
                    execute({2, static_cast<uint8_t>(address), static_cast<uint8_t>(space), static_cast<uint8_t>(value), s.line});
                    waitClock(nextTick);
                    break;
                }

                case Kind::RamRead: {
                    const int address = fixedOrValue(s.p[0], 4, "RAM address");
                    const int space = fixedOrValue(s.p[1], 8, "RAM space");
                    // RAMR keeps the same three input fields as RAMW; INPUT2 is unused by the CPU.
                    (void)fixedOrValue(s.p[2], 8, "RAM read unused input");
                    execute({3, static_cast<uint8_t>(address), static_cast<uint8_t>(space), 0, s.line});
                    waitClock(nextTick);
                    break;
                }

                case Kind::Vga: {
                    // VGA uses the same three fields as the 24-bit instruction format.
                    // input0 = RGB(3bit)+mode(1bit), input1 = Y(3bit)+X(5bit), input2 = ASCII(8bit).
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

    void prompt() {
        std::string line;
        for (;;) {
            std::cout << "8c> " << std::flush;
            if (!std::getline(std::cin, line)) break;
            line = trim(line);
            if (line.empty()) continue;

            const std::string cmd = lower(line);
            if (cmd == "quit" || cmd == "exit") break;

            try {
                const MachineInstruction mi = parsePromptInstruction(line);
                execute(mi);
                display_.render();
            } catch (const std::exception& e) {
                std::cout << "ERROR: " << e.what() << '\n' << std::flush;
            }
        }
    }

private:
    double hz_;
    std::array<std::array<uint8_t, MEM_BLOCKS>, MEM_SPACES> memory_{};
    std::unordered_map<std::string, int> vars_;
    Display display_;

    int evaluate(const std::string& expr) const {
        const std::string e = trim(expr);
        for (char op : std::string("+-*/")) {
            const size_t p = e.find(op, 1);
            if (p == std::string::npos) continue;
            const int left = evaluateAtom(trim(e.substr(0, p)));
            const int right = evaluateAtom(trim(e.substr(p + 1)));
            switch (op) {
                case '+': return left + right;
                case '-': return left - right;
                case '*': return left * right;
                case '/':
                    if (right == 0) throw std::runtime_error("division by zero");
                    return left / right;
            }
        }
        return evaluateAtom(e);
    }

    int evaluateAtom(const std::string& token) const {
        auto it = vars_.find(token);
        if (it != vars_.end()) return it->second;
        return parseInteger(token);
    }

    static int requireU8(int value, const std::string& label) {
        if (value < 0 || value > 255)
            throw std::runtime_error(label + " must be 0..255");
        return value;
    }

    int fixedOrValue(const std::string& token, int bits, const std::string& label) const {
        const int value = exactBinary(token, static_cast<size_t>(bits))
                               ? parseBinaryFixed(token, bits, label)
                               : evaluate(token);
        const int maxValue = (1 << bits) - 1;
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
                const int spaceCode = mi.input1 & 0x03;
                if (spaceCode != 1 && spaceCode != 2)
                    throw std::runtime_error("RAM space must be 01 or 10");
                if (mi.input0 > 7)
                    throw std::runtime_error("for the 128-bit layout, RAM address uses 0000..0111 per space");
                const int space = spaceCode - 1;
                memory_[static_cast<size_t>(space)][mi.input0] = mi.input2;
                break;
            }

            case 3: {
                const int spaceCode = mi.input1 & 0x03;
                if (spaceCode != 1 && spaceCode != 2)
                    throw std::runtime_error("RAM space must be 01 or 10");
                if (mi.input0 > 7)
                    throw std::runtime_error("for the 128-bit layout, RAM address uses 0000..0111 per space");
                const uint8_t value = memory_[static_cast<size_t>(spaceCode - 1)][mi.input0];
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
        const auto period = std::chrono::duration<double>(1.0 / hz_);
        nextTick += std::chrono::duration_cast<std::chrono::steady_clock::duration>(period);
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
            if (w.size() != 4) throw std::runtime_error("ramw <addr4> <space8> <value8>");
            ScriptInstruction s = make(Kind::RamWrite, logicalLine);
            s.p[0]=w[1]; s.p[1]=w[2]; s.p[2]=w[3];
            return s;
        }

        if (cmd == "ramr") {
            if (w.size() != 4) throw std::runtime_error("ramr <addr4> <space8> <unused8>");
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

static std::string requireExtension(const std::string& path) {
    if (path.size() < 2 || lower(path.substr(path.size()-2)) != ".8")
        throw std::runtime_error("first argument must be a .8 file");
    return path;
}

} // namespace eightc

int main(int argc, char** argv) {
    using namespace eightc;

    try {
        std::string file;
        double hz = 1024.0;

        if (argc == 1) {
            // Double-click / plain execution: open an idle 8c machine at 1024 Hz.
            file.clear();
        } else if (argc == 3) {
            file = requireExtension(argv[1]);
            hz = parseClockHz(argv[2]);
        } else {
            std::cerr << "Usage: 8c [file.8 clock_hz]\n";
            return 2;
        }

        VM vm(hz);
        vm.display().setup();
        vm.display().clear();

#ifdef _WIN32
        // Parse the program before creating the monitor thread so a .8 parse error
        // cannot destroy a joinable std::thread during stack unwinding.
        std::vector<ScriptInstruction> program;
        if (!file.empty())
            program = Parser{}.parseFile(file);

        // Keep the console and VGA window as one unit.
        // Closing either one immediately terminates the whole 8c process.
        std::atomic<bool> windowMonitorRunning{true};
        std::thread windowMonitor([&windowMonitorRunning]() {
            for (;;) {
                if (!windowMonitorRunning.load(std::memory_order_acquire))
                    return;

                HWND console = GetConsoleWindow();
                if (console == nullptr || !IsWindow(console)) {
                    ExitProcess(0);
                }

                HWND vga = FindWindowA("8cVGAWindowClass", "8c VGA 32x8");
                if (vga == nullptr || !IsWindow(vga)) {
                    ExitProcess(0);
                }

                std::this_thread::sleep_for(std::chrono::milliseconds(50));
            }
        });

        try {
            if (!file.empty())
                vm.run(program);

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
        if (!file.empty()) {
            const auto program = Parser{}.parseFile(file);
            vm.run(program);
        }

        vm.prompt();
#endif

        return 0;
    } catch (const std::exception& e) {
        std::cerr << "8c: ERROR: " << e.what() << '\n';
        return 1;
    }
}
