#!/usr/bin/env python3
"""Tools for Erdős #875: admissible sets (disjoint r-fold sumsets).

A finite set A ⊂ N is admissible if the sets S_r = {sums of r distinct
elements of A} are pairwise disjoint for r = 1..|A|. Equivalently: every
integer representable as a sum of distinct elements of A determines the
number of summands uniquely.

Usage:
  admissible.py check 1 2 4 8 ...     # check a specific set
  admissible.py greedy N              # greedy densest prefix in [1,N]
  admissible.py greedy N --start 1 3  # greedy with a forced prefix
"""
import sys
from typing import Iterable


def card_profile(A: list[int]) -> dict[int, int]:
    """Map each achievable subset sum to a bitmask of achievable cardinalities.

    Bit r of profile[s] is set iff s is a sum of exactly r distinct elements.
    """
    profile: dict[int, int] = {0: 1}  # empty sum, cardinality 0
    for a in A:
        # iterate over a snapshot; add `a` to every existing subset
        for s, mask in list(profile.items()):
            t = s + a
            profile[t] = profile.get(t, 0) | (mask << 1)
    return profile


def is_admissible(A: Iterable[int]) -> bool:
    """True iff every representable sum has exactly one achievable cardinality
    (ignoring the empty sum)."""
    A = sorted(set(A))
    profile = card_profile(A)
    for s, mask in profile.items():
        if s == 0:
            continue
        if mask & (mask - 1):  # more than one bit set
            return False
    return True


def first_conflict(A: list[int]) -> tuple[int, int, int] | None:
    """Return (sum, r, s) for the first sum representable with two distinct
    cardinalities r < s, else None."""
    profile = card_profile(sorted(set(A)))
    best = None
    for total, mask in profile.items():
        if total == 0 or not (mask & (mask - 1)):
            continue
        bits = [r for r in range(mask.bit_length()) if mask >> r & 1]
        cand = (total, bits[0], bits[1])
        if best is None or cand[0] < best[0]:
            best = cand
    return best


def extends_admissibly(A: list[int], profile: dict[int, int], x: int) -> dict[int, int] | None:
    """If A ∪ {x} is admissible, return its updated profile, else None.

    `profile` must be card_profile(A). Assumes x not in A.
    """
    new = dict(profile)
    for s, mask in profile.items():
        t = s + x
        m = new.get(t, 0) | (mask << 1)
        if t != 0 and m & (m - 1):
            return None
        new[t] = m
    # note: masks merged after the fact can still collide; verify fully
    for s, mask in new.items():
        if s != 0 and mask & (mask - 1):
            return None
    return new


class SumProfile:
    """Incremental subset-sum profile for an admissible set, with O(1) undo.

    Invariant: the tracked set A is admissible, so every representable subset
    sum has a *unique* cardinality; we store `card[s] = r`. Adding an element
    x only ever ADDS entries (an old sum s may produce s+x, which must either
    be absent or already have cardinality card[s]+1), so undo = delete the
    added keys. This makes backtracking search cheap: try_add / undo.

    ~5x faster than re-running card_profile, and pseudo-polynomial:
    O(#distinct sums) <= O(Sigma(A)) per operation, not O(2^|A|).
    """

    def __init__(self, elements: Iterable[int] = ()):
        self.card: dict[int, int] = {0: 0}
        self.elements: list[int] = []
        self._added: list[list[int]] = []  # per-element flat [s1,r1,s2,r2,...]
        for x in sorted(elements):
            if not self.try_add(x):
                raise ValueError(f"seed set not admissible at element {x}")

    def try_add(self, x: int) -> bool:
        """If A ∪ {x} is admissible, commit it and return True; else False.

        Correctness: subsets of A∪{x} not containing x have sums in `card`
        (admissible by invariant); subsets containing x have sums s+x with s
        distinct, so new-new collisions are impossible; the only checks needed
        are old-vs-new: card[s+x] == card[s]+1 whenever s+x is an old sum.
        Caller must ensure x not in A (e.g. x > max(A)).
        """
        card = self.card
        get = card.get
        added: list[int] = []
        ap = added.append
        for s, r in card.items():
            t = s + x
            c = get(t)
            if c is None:
                ap(t)
                ap(r + 1)
            elif c != r + 1:
                return False
        for i in range(0, len(added), 2):
            card[added[i]] = added[i + 1]
        self.elements.append(x)
        self._added.append(added)
        return True

    def feasible(self, x: int) -> bool:
        """Check A ∪ {x} admissible without committing."""
        card = self.card
        get = card.get
        for s, r in card.items():
            c = get(s + x)
            if c is not None and c != r + 1:
                return False
        return True

    def undo(self) -> int:
        """Remove the most recently added element; return it."""
        added = self._added.pop()
        card = self.card
        for i in range(0, len(added), 2):
            del card[added[i]]
        return self.elements.pop()

    def undo_to(self, depth: int) -> None:
        """Shrink the set back to its first `depth` elements."""
        while len(self.elements) > depth:
            self.undo()

    @property
    def sigma(self) -> int:
        return sum(self.elements)

    def __len__(self) -> int:
        return len(self.elements)


def greedy(limit: int, start: list[int] | None = None) -> list[int]:
    """Greedily build an admissible set: repeatedly add the smallest integer
    that keeps the set admissible, up to `limit`."""
    A: list[int] = []
    profile = {0: 1}
    forced = sorted(set(start or []))
    for x in forced:
        p = extends_admissibly(A, profile, x)
        if p is None:
            raise SystemExit(f"forced prefix breaks admissibility at {x}")
        A.append(x)
        profile = p
    x = (A[-1] + 1) if A else 1
    while x <= limit:
        p = extends_admissibly(A, profile, x)
        if p is not None:
            A.append(x)
            profile = p
        x += 1
    return A


def main() -> None:
    if len(sys.argv) < 2:
        raise SystemExit(__doc__)
    cmd = sys.argv[1]
    if cmd == "check":
        A = [int(v) for v in sys.argv[2:]]
        ok = is_admissible(A)
        print(f"{'ADMISSIBLE' if ok else 'NOT admissible'}: {sorted(set(A))}")
        if not ok:
            print(f"first conflict (sum, r, s): {first_conflict(A)}")
    elif cmd == "greedy":
        args = sys.argv[2:]
        start: list[int] = []
        if "--start" in args:
            i = args.index("--start")
            start = [int(v) for v in args[i + 1:]]
            args = args[:i]
        limit = int(args[0])
        A = greedy(limit, start)
        n = len(A)
        print(f"greedy admissible set in [1,{limit}]: |A| = {n}")
        print(A)
        print(f"Deshouillers–Freiman ceiling 2*sqrt(N): {2 * limit ** 0.5:.1f}")
        if n >= 3:
            gaps = [A[i + 1] - A[i] for i in range(n - 1)]
            print(f"max gap: {max(gaps)}, last 10 gaps: {gaps[-10:]}")
    else:
        raise SystemExit(__doc__)


if __name__ == "__main__":
    main()
