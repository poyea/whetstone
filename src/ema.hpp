#pragma once

#include <cstdint>

/// @brief Restart strategy for the CDCL search loop.
enum class RestartPolicy { Luby, Glucose };

/// @brief Exponential moving average with a warmup period.
///
/// Uses a running average for the first `1/alpha` samples, then
/// switches to exponential smoothing. Used by glucose-style restarts
/// to track recent vs. global LBD trends.
struct EMA {
    double value = 0;
    double alpha;
    uint64_t count = 0;

    explicit EMA(double a) : alpha(a) {}

    void update(double x) {
        count++;
        if (count < static_cast<uint64_t>(1.0 / alpha))
            value += (x - value) / static_cast<double>(count);
        else
            value += alpha * (x - value);
    }

    bool ready() const { return count >= static_cast<uint64_t>(1.0 / alpha); }
};
