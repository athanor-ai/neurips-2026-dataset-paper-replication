"""Reproduce the paper's headline numbers from benchmark.jsonl.

Usage:
    python3 tools/reproduce_headline.py path/to/benchmark.jsonl

Downloads benchmark.jsonl from the HuggingFace release, then
reconstructs the pass@5 closure matrix reported in
Table 1 (tab:headline) and the tier distribution in
Appendix tab:tier-dist.

Run:
    pip install huggingface_hub
    huggingface-cli download neurips-2026-avs-bench/formal-anytime-valid-stats
    python3 tools/reproduce_headline.py benchmark.jsonl
"""
import json
import sys
from collections import defaultdict


TIER_ORDER = [
    "T0_mathlib_canon",
    "T1_single_function_friendly",
    "T2_single_function_challenging",
    "T3_cross_function_wall",
    "T4_solver_hit_mathlib_gap",
    "T5_all_solver_capability_ceiling",
]

TIER_SHORT = {t: t.split("_")[0] for t in TIER_ORDER}

DRAFTER_FIELDS = {
    "Claude Sonnet 4.6": "drafter_close_rate_sonnet_4_6",
    "Kimi K2.5": "drafter_close_rate_kimi_k2_5",
    "Gemini 3 Pro": "drafter_close_rate_gemini_3_pro",
    "Mistral Large 3": "drafter_close_rate_mistral_large_3",
    "Claude Opus 4.6": "drafter_close_rate_opus_4_6",
    "Harmonic Aristotle": "drafter_close_rate_harmonic_aristotle",
}


def parse_rate(val):
    """'2/5' -> (2, 5). None or empty -> None."""
    if not val:
        return None
    try:
        num, denom = val.split("/")
        return int(num), int(denom)
    except Exception:
        return None


def load(path):
    with open(path) as f:
        return [json.loads(line) for line in f if line.strip()]


def tier_distribution(rows):
    by_tier = defaultdict(int)
    for r in rows:
        by_tier[r.get("tier", "unknown")] += 1
    return {t: by_tier.get(t, 0) for t in TIER_ORDER}


def closure_matrix(rows):
    """Per-tier, per-drafter close count (pass@5 regime)."""
    out = {d: {t: [0, 0] for t in TIER_ORDER} for d in DRAFTER_FIELDS}
    for r in rows:
        tier = r.get("tier")
        if tier not in TIER_ORDER:
            continue
        for drafter, field in DRAFTER_FIELDS.items():
            rate = parse_rate(r.get(field))
            if rate is None:
                continue
            closed, _ = rate
            out[drafter][tier][0] += min(closed, 1)
            out[drafter][tier][1] += 1
    return out


def main():
    if len(sys.argv) != 2:
        print("Usage: reproduce_headline.py path/to/benchmark.jsonl")
        sys.exit(1)

    rows = load(sys.argv[1])
    print(f"Loaded {len(rows)} benchmark rows.")

    print("\n=== Tier distribution (Appendix tab:tier-dist) ===")
    dist = tier_distribution(rows)
    for t in TIER_ORDER:
        print(f"  {TIER_SHORT[t]}: {dist[t]}")
    print(f"  Total: {sum(dist.values())}")

    print("\n=== Per-drafter pass@5 closure matrix (Table 1 tab:headline) ===")
    matrix = closure_matrix(rows)
    header = f"  {'Drafter':<22}" + "".join(f"{TIER_SHORT[t]:>8}" for t in TIER_ORDER) + "   overall"
    print(header)
    print("  " + "-" * (len(header) - 2))
    for drafter in DRAFTER_FIELDS:
        cells = []
        total_closed = 0
        total_tested = 0
        for t in TIER_ORDER:
            c, n = matrix[drafter][t]
            cells.append(f"{c}/{n}" if n else "n/t")
            total_closed += c
            total_tested += n
        row = f"  {drafter:<22}" + "".join(f"{cell:>8}" for cell in cells) + f"   {total_closed}/{total_tested}"
        print(row)

    print("\n=== Headline aggregates ===")
    generalists = ["Claude Sonnet 4.6", "Kimi K2.5", "Gemini 3 Pro", "Mistral Large 3"]
    t0_closed = sum(matrix[d]["T0_mathlib_canon"][0] for d in generalists)
    t0_tested = sum(matrix[d]["T0_mathlib_canon"][1] for d in generalists)
    t3_closed = sum(matrix[d]["T3_cross_function_wall"][0] for d in generalists)
    t3_tested = sum(matrix[d]["T3_cross_function_wall"][1] for d in generalists)
    print(f"  T0 generalist-aggregate: {t0_closed}/{t0_tested} "
          f"(paper reports 0/28)")
    print(f"  T3 generalist-aggregate: {t3_closed}/{t3_tested} "
          f"(paper reports 2/24)")
    aris_t3 = matrix["Harmonic Aristotle"]["T3_cross_function_wall"]
    print(f"  T3 Aristotle closure:    {aris_t3[0]}/{aris_t3[1]} "
          f"(paper reports 6/6 axiom-clean)")

    print("\n(Note: if Opus 4.6 or Aristotle rows show n/t, the local "
          "benchmark.jsonl")
    print(" predates those sweeps. The HF dataset push accompanying "
          "the final paper")
    print(" camera-ready adds the drafter_close_rate_opus_4_6 and "
          "_harmonic_aristotle")
    print(" fields. Refer to Table 1 and Table 2 in the paper for the "
          "full matrix.)")


if __name__ == "__main__":
    main()
