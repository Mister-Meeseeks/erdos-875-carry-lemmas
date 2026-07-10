#!/usr/bin/env python3
"""Erdős #875 — staggered-AP / overlapping-scale probes (wide-window idea).

Four modes, all feeding the carry-lemma design of notes/01 §7 direction 1:

  lemma      Exact violation frontier of the local carry lemma for the pure
             Mazur AP block C_m = {1+i(m+1) : 0<=i<m}, Q = m^2+m+1.
             The lemma shape: Y ∈ Δ_t(C_m), Y = Qw − u, |u| < U  ⇒  t = w−u.
             NOTE: |w| ≤ (Σ(C_m)+U)/Q ≈ m/2 automatically (graded differences
             can't reach further), so the only load-bearing window is the
             carry window U. This mode computes U*(m) = the smallest |u| over
             all violations — the lemma is TRUE for U ≤ U*(m) and no larger.
             Mazur's proof uses U = m/4; the question is how U* really scales.

  lemma-scan Same U* computation for STAGGERED local sets: unions of two APs
             C = {1+i(m+1) : i<k1} ∪ {h + j*d2 : j<k2}, sweeping the second
             AP's height/step, and sweeping the anchor modulus Q down from
             Q_m. Figure of merit: U*·|C|/Q (Mazur's AP scores ≈ 1/4; bigger
             would lower the gap exponent AND relax the entry gap).

  two-scale  Admissibility map for a two-scale union B1 = C_{k1},
             B2 = M2·{s2 + i·d2 : i<k2} as M2 sweeps below Q_{k1} (overlap!),
             with stagger d2, s2. Reports admissible/not, the collision that
             kills it, and the max consecutive ratio (entry-gap metric).

  chain      Depth test: scales M_{j+1} = M_j·r with integer multiplier
             r = round(f·Q_k) for overlap fraction f ≤ 1, blocks M_j·C_k.
             Mazur is f = 1. Reports the deepest admissible scale count per f
             and where/how the first collision appears.

Examples (from repo root):
  python3 tools/875/staggered.py lemma --mmax 24
  python3 tools/875/staggered.py lemma-scan --m 10 --budget 60
  python3 tools/875/staggered.py two-scale --k1 8 --k2 8
  python3 tools/875/staggered.py two-scale --k1 12 --k2 6 --d2 5 6 7 8 13
  python3 tools/875/staggered.py chain --k 5 --scales 4
"""
from __future__ import annotations

import argparse
import math
import time

from admissible import SumProfile, first_conflict, is_admissible


def C(m: int) -> list[int]:
    return [1 + i * (m + 1) for i in range(m)]


def Q_of(m: int) -> int:
    return m * m + m + 1


# ---------------------------------------------------------------- Δ_t DP

def graded_differences(elems: list[int]) -> dict[int, int]:
    """dp[Y] = bitmask of achievable t (bit index t + n), where
    Y = ΣU − ΣV over disjoint U,V ⊆ elems and t = |U| − |V|."""
    n = len(elems)
    dp = {0: 1 << n}
    for c in elems:
        new = {}
        for y, mask in dp.items():
            for dy, sh in ((0, 0), (c, 1), (-c, -1)):
                t = y + dy
                m2 = (mask << sh) if sh >= 0 else (mask >> 1)
                new[t] = new.get(t, 0) | m2
        dp = new
    return dp


def lemma_frontier(elems: list[int], Q: int) -> dict:
    """Minimal |u| over all violations of  'Y = Qw − u ⇒ t = w − u'.

    Returns {"ustar": minimal violating |u| (lemma holds for U <= ustar),
             "witness": (Y, t, w, u), "wmax_reachable": max |w| seen}.
    Violations with |u| >= Q//2 are ignored (the (w,u) decomposition is only
    meaningful for u below Q/2)."""
    n = len(elems)
    dp = graded_differences(elems)
    ucap = Q // 2
    best = None
    wmax = 0
    for y, mask in dp.items():
        wlo = math.floor((y - ucap) / Q)
        whi = math.ceil((y + ucap) / Q)
        for w in range(wlo, whi + 1):
            u = Q * w - y
            if abs(u) > ucap:
                continue
            wmax = max(wmax, abs(w))
            m2 = mask
            while m2:
                b = (m2 & -m2).bit_length() - 1
                m2 &= m2 - 1
                t = b - n
                if t != w - u and (best is None or abs(u) < best[0]):
                    best = (abs(u), (y, t, w, u))
    return {"ustar": best[0] if best else ucap,
            "witness": best[1] if best else None,
            "wmax_reachable": wmax}


# ---------------------------------------------------------------- modes

def cmd_lemma(args) -> None:
    print("# local carry lemma frontier for pure AP C_m, Q=m^2+m+1")
    print("# U*(m) = min |u| over violations; lemma TRUE for U <= U*  "
          "(Mazur proof uses U=m/4)")
    print("| m | Q | U* | U*/m | m/4 | witness (Y,t,w,u) | max|w| |")
    print("|---|---|----|------|-----|-------------------|--------|")
    for m in range(3, args.mmax + 1):
        r = lemma_frontier(C(m), Q_of(m))
        print(f"| {m} | {Q_of(m)} | {r['ustar']} | {r['ustar']/m:.3f} | "
              f"{m/4:.2f} | {r['witness']} | {r['wmax_reachable']} |")


def cmd_lemma_scan(args) -> None:
    """Family zoo: which local sets support the best carry window?

    Metrics per (C, Q):
      U*          carry window (min violating |u|)
      merit_carry U*·|C|/Q   — Mazur's AP proof value is 1/4, its true value ~1/2
      merit_dens  |C|^2/Q    — the quadratic-cost driver of the 3+2√2 exponent;
                  pure AP ≈ 1; beating it while keeping U* >= |C|/2-ish is
                  exactly Remark 4's "more radical local structure"
      spread      max C/min C (ratio friendliness of the block itself)
    """
    m = args.m
    deadline = time.monotonic() + args.budget
    # Each family: (name, elems, step) — step d means all elems ≡ 1 (mod d),
    # so the anchor modulus must be ≡ 1 (mod d) for the mod-d cardinality
    # accounting to survive (misaligned Q gives U*=0 instantly).
    zoo: list[tuple[str, list[int], int]] = [("pure-AP C_m", C(m), m + 1)]
    # short AP: fewer elements, same step (does U* track k/2 or the step?)
    for k in (m // 2, 3 * m // 4):
        zoo.append((f"short-AP k={k}",
                    [1 + i * (m + 1) for i in range(k)], m + 1))
    # sparse AP: step g >> k (does U* track g/2 or k/2?)
    for g in (2 * (m + 1), 4 * (m + 1)):
        zoo.append((f"sparse-AP g={g}",
                    [1 + i * g for i in range(m)], g))
    # AP with a hole (residue-aligned staggered union — the wide-window shape)
    k1, k2 = m - m // 2, m // 2
    for H in (k1 + 2, 2 * k1, 4 * k1):
        idx = list(range(k1)) + list(range(H, H + k2))
        zoo.append((f"AP-hole H={H}",
                    [1 + i * (m + 1) for i in idx], m + 1))
    # negative controls: consecutive (Straus) blocks; misaligned 2AP
    for h in (m * m // 2, m * m):
        zoo.append((f"consec@{h}", [h + i for i in range(1, m + 1)], 1))
    zoo.append((f"2AP steps {m+1},{m+2}",
                sorted(set(C(m)[:k1])
                       | {1 + k1 * (m + 1) + j * (m + 2) for j in range(k2)}),
                1))
    rows = []
    for name, elems, step in zoo:
        top = max(elems)
        for Qf in (1.0, 1.15, 1.4, 2.0):
            Q = max(math.ceil(top * Qf), top + 1)
            Q += (1 - Q) % step  # align: smallest Q' >= Q with Q' ≡ 1 (mod step)
            if name == "pure-AP C_m" and Qf == 1.0:
                Q = Q_of(m)  # exact Mazur anchor for the baseline
            r = lemma_frontier(elems, Q)
            k = len(elems)
            gaps = [b - a for a, b in zip(elems, elems[1:])]
            rows.append((r["ustar"] * k / Q, k * k / Q, r["ustar"], min(gaps),
                         k, Q, max(elems) / min(elems), name, r["witness"]))
            if time.monotonic() > deadline:
                print("(budget hit — partial scan)")
                break
        if time.monotonic() > deadline:
            break
    rows.sort(key=lambda t: -t[0])
    print(f"# local-set family zoo at cardinality ~{m} "
          f"(sorted by merit_carry = U*|C|/Q)")
    print("# law check: U* <= min-gap always (Y=-gap ∈ Δ_0 violates at u=gap)")
    print("| merit_carry | merit_dens | U* | min-gap | |C| | Q | spread | "
          "family | witness (Y,t,w,u) |")
    print("|-------------|------------|----|---------|-----|---|--------|"
          "--------|----------|")
    for mc, md, us, gap, k, Q, sp, name, wit in rows:
        print(f"| {mc:.3f} | {md:.3f} | {us} | {gap} | {k} | {Q} | {sp:.1f} | "
              f"{name} | {wit} |")


def cmd_two_scale(args) -> None:
    k1, k2 = args.k1, args.k2
    B1 = C(k1)
    Q1 = Q_of(k1)
    top1 = max(B1)  # = k1^2 (since 1 + (k1-1)(k1+1) = k1^2)
    m2lo = args.m2min or 2
    m2hi = args.m2max or sum(B1) + 2  # cover the whole [Q_k1, Sigma(B1)] range
    d2s = args.d2 or [k2 + 1]
    s2s = args.s2 or [1]
    print(f"# two-scale map: B1=C_{k1} (max {top1}, Q_k1={Q1}, "
          f"Sigma={sum(B1)}), B2=M2*(s2+i*d2), i<{k2}")
    print(f"# M2 in [{m2lo},{m2hi}]; M2*s2<{top1} means the scales OVERLAP; "
          f"M2>Sigma(B1) is the trivial flat/ladder regime")
    survivors = []
    for d2 in d2s:
        for s2 in s2s:
            fails = 0
            conflicts = []
            for M2 in range(m2lo, m2hi + 1):
                B2 = [M2 * (s2 + i * d2) for i in range(k2)]
                union = sorted(set(B1) | set(B2))
                if len(union) != k1 + k2:
                    continue  # sets collide as integers; skip
                adm = is_admissible(union)
                ratios = [b / a for a, b in zip(union, union[1:])]
                # junction ratio: worst consecutive ratio from mid-B1 upward
                # (covers the B1->B2 jump and B2's entry spacing; excludes the
                # bottom of B1, which a previous scale would cover)
                jr = max((b / a for a, b in zip(union, union[1:])
                          if a >= top1 / 2), default=1.0)
                overlap = top1 / min(B2)
                if adm:
                    survivors.append((M2, d2, s2, overlap, max(ratios), jr))
                    if args.verbose:
                        print(f"  ADM M2={M2} d2={d2} s2={s2} "
                              f"overlap={overlap:.2f} junction={jr:.2f}")
                else:
                    fails += 1
                    if len(conflicts) < 4:
                        conflicts.append((M2, first_conflict(union)))
            print(f"d2={d2} s2={s2}: "
                  f"survivors {[s[0] for s in survivors if s[1] == d2 and s[2] == s2]} "
                  f"/ fails {fails}; sample conflicts (M2,(sum,r,s)): {conflicts}")
    print(f"\ntotal survivors: {len(survivors)} "
          f"(Q_k1={Q1}, Sigma(B1)={sum(B1)})")
    for M2, d2, s2, ov, mr, jr in survivors:
        regime = ("OVERLAP" if ov > 1 else
                  "ladder" if M2 > sum(B1) else "carry-window")
        print(f"  M2={M2:5d} d2={d2} s2={s2} overlap={ov:5.2f} "
              f"max-ratio={mr:6.2f} junction-ratio={jr:6.2f} [{regime}]")


def cmd_chain(args) -> None:
    k = args.k
    s, d = args.s, args.d
    block = [s + i * d for i in range(k)]  # local block shape (s=1, d=k+1 = Mazur)
    Qk = Q_of(k) if (s, d) == (1, k + 1) else max(block) + d
    print(f"# chained scales, blocks M_j*{{{s}+i*{d}}} (i<{k}, anchor Q={Qk}), "
          f"M_(j+1)=M_j*round(f*Q)")
    print("| f | multiplier r | max admissible scales | junction ratio | "
          "first conflict |")
    print("|---|--------------|-----------------------|----------------|"
          "----------------|")
    for f in args.fracs:
        r = max(2, round(f * Qk))
        p = SumProfile()
        M = 1
        depth = 0
        conf = None
        for j in range(args.scales):
            ok = True
            for c in block:
                x = M * c
                if x in p.elements:
                    ok = False
                    conf = ("element-collision", x)
                    break
                if not p.try_add(x):
                    ok = False
                    conf = first_conflict(sorted(set(p.elements) | {x}))
                    break
            if not ok:
                break
            depth += 1
            M *= r
            if len(p.card) > args.max_profile:
                conf = ("profile-cap",)
                break
        elems = sorted(p.elements)
        jr = max((b / a for a, b in zip(elems, elems[1:])), default=1.0) \
            if depth >= 2 else float("nan")
        print(f"| {f} | {r} | {depth}/{args.scales} | {jr:.2f} | "
              f"{conf if conf else 'none'} |")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    s = sub.add_parser("lemma", help="U*(m) frontier for pure AP C_m")
    s.add_argument("--mmax", type=int, default=22)
    s.set_defaults(fn=cmd_lemma)

    s = sub.add_parser("lemma-scan", help="U* for staggered two-AP local sets")
    s.add_argument("--m", type=int, default=10)
    s.add_argument("--budget", type=float, default=60.0)
    s.set_defaults(fn=cmd_lemma_scan)

    s = sub.add_parser("two-scale", help="admissibility map for B1 ∪ M2·B2")
    s.add_argument("--k1", type=int, default=8)
    s.add_argument("--k2", type=int, default=8)
    s.add_argument("--m2min", type=int, default=0)
    s.add_argument("--m2max", type=int, default=0)
    s.add_argument("--d2", type=int, nargs="*", default=None)
    s.add_argument("--s2", type=int, nargs="*", default=None)
    s.add_argument("--verbose", action="store_true")
    s.set_defaults(fn=cmd_two_scale)

    s = sub.add_parser("chain", help="overlapping-scale chain depth")
    s.add_argument("--k", type=int, default=5)
    s.add_argument("--s", type=int, default=1,
                   help="block start offset (blocks M_j*{s+i*d})")
    s.add_argument("--d", type=int, default=0,
                   help="block step (default k+1 = Mazur shape)")
    s.add_argument("--scales", type=int, default=5)
    s.add_argument("--fracs", type=float, nargs="*",
                   default=[0.2, 0.4, 0.6, 0.8, 1.0])
    s.add_argument("--max-profile", type=int, default=3_000_000)
    s.set_defaults(fn=cmd_chain)

    args = ap.parse_args()
    if getattr(args, "d", None) == 0:
        args.d = args.k + 1
    args.fn(args)


if __name__ == "__main__":
    main()
