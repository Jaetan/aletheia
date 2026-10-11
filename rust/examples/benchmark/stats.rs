// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Statistics over a lane's samples and the rounding the JSON report applies.

// ---------------------------------------------------------------------------
// Statistics helpers (matching the Go / C++ formulas: sample stdev, linear-
// interpolated percentiles, round-to-one-decimal for the wire).
// ---------------------------------------------------------------------------

pub(crate) fn mean(xs: &[f64]) -> f64 {
    if xs.is_empty() {
        return 0.0;
    }
    xs.iter().sum::<f64>() / xs.len() as f64
}

pub(crate) fn sample_stdev(xs: &[f64]) -> f64 {
    if xs.len() < 2 {
        return 0.0;
    }
    let m = mean(xs);
    let ss: f64 = xs.iter().map(|x| (x - m) * (x - m)).sum();
    (ss / (xs.len() as f64 - 1.0)).sqrt()
}

pub(crate) fn min_of(xs: &[f64]) -> f64 {
    xs.iter().copied().fold(f64::INFINITY, f64::min)
}

pub(crate) fn max_of(xs: &[f64]) -> f64 {
    xs.iter().copied().fold(f64::NEG_INFINITY, f64::max)
}

pub(crate) fn percentile(sorted: &[f64], p: f64) -> f64 {
    if sorted.is_empty() {
        return 0.0;
    }
    let k = (sorted.len() as f64 - 1.0) * p / 100.0;
    let f = k as usize;
    let c = if f + 1 < sorted.len() { f + 1 } else { f };
    sorted[f] + (k - f as f64) * (sorted[c] - sorted[f])
}

pub(crate) fn round1(x: f64) -> f64 {
    (x * 10.0).round() / 10.0
}

pub(crate) fn round3(x: f64) -> f64 {
    (x * 1000.0).round() / 1000.0
}

pub(crate) fn round4(x: f64) -> f64 {
    (x * 10_000.0).round() / 10_000.0
}
