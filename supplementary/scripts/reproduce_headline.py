"""Reproduce the paper's headline numbers from benchmark.jsonl.

Usage:
    python3 scripts/reproduce_headline.py path/to/benchmark.jsonl

Reconstructs the pass@5 closure matrix reported in Table 1 (tab:headline)
and the tier distribution in Appendix tab:tier-dist.
"""
import json
import sys
from collections import defaultdict

TIER_MAP = {
    "trivial":     "T0",
    "friendly":    "T1",
    "challenging": "T2",
    "frontier":    "T3",
    "ceiling":     "T4/T5",
}

DRAFTERS = [
    ("Claude Sonnet 4.6",  "sonnet_4_6_pass5"),
    ("Kimi K2.5",          "kimi_k2_5_pass5"),
    ("Gemini 3 Pro",       "gemini_3_pro_pass5"),
    ("Mistral Large 3",    "mistral_large_3_pass5"),
    ("Claude Opus 4.6",    "opus_4_6_pass5"),
    ("DSPv2-7B neutral",   "dspv2_7b_neutral_pass5"),
    ("Goedel-V2 neutral",  "goedel_v2_q6k_neutral_pass5"),
    ("Harmonic Aristotle", "aristotle_verdict"),
]

PAPER_CLAIMS = {
    "Claude Sonnet 4.6":  18,
    "Kimi K2.5":          18,
    "Gemini 3 Pro":       22,
    "Mistral Large 3":     2,
    "Claude Opus 4.6":    13,
    "DSPv2-7B neutral":    9,
    "Goedel-V2 neutral":   5,
    "Harmonic Aristotle": 48,
}


def is_closed(val):
    if val is None:
        return False
    if val == "closed" or val is True or val == 1:
        return True
    if isinstance(val, str) and "/" in val:
        return int(val.split("/")[0]) > 0
    return False


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else "supplementary/data/benchmark.jsonl"
    rows = [json.loads(l) for l in open(path)]
    print(f"Loaded {len(rows)} benchmark rows.\n")

    # Tier distribution
    tiers = defaultdict(int)
    for r in rows:
        tiers[TIER_MAP.get(r.get("tier", "?"), r.get("tier", "?"))] += 1
    print("=== Tier distribution ===")
    for t, n in sorted(tiers.items()):
        print(f"  {t}: {n}")
    print(f"  Total: {sum(tiers.values())}\n")

    # Per-drafter closure counts
    print("=== Per-drafter pass@5 closure counts (Table 1) ===")
    print(f"  {'Drafter':<28} {'Closed':>6}  {'Paper':>6}  {'Match':>5}")
    print("  " + "-" * 52)
    all_match = True
    for name, field in DRAFTERS:
        closed = sum(1 for r in rows if is_closed(r.get(field)))
        paper = PAPER_CLAIMS.get(name, "?")
        match = "✓" if closed == paper else "✗ MISMATCH"
        if closed != paper:
            all_match = False
        print(f"  {name:<28} {closed:>6}  {paper:>6}  {match}")

    print()
    if all_match:
        print("All counts match paper Table 1. ✓")
    else:
        print("WARNING: some counts do not match paper Table 1.")


if __name__ == "__main__":
    main()
