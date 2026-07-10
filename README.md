# Sharp local carry lemmas for Erdős Problem 875

Companion repository for a short note on [Erdős Problem #875](https://www.erdosproblems.com/875)
(admissible sets: sequences whose $r$-fold sumsets are pairwise disjoint,
equivalently, every subset sum determines its cardinality).

**This is not a resolution of #875.** The note proves four self-contained
propositions that sharpen the *local machinery* used in the only modern
partial result on the problem (L. Mazur's May 2026 note and Lean
formalization, [lechmazur/erdos_875](https://github.com/lechmazur/erdos_875)),
and proves an impossibility theorem delimiting what that machinery can do:

1. **Sharp local carry lemma** (Prop 1) — for the AP block
   $C_m=\{1+i(m+1)\}$ with anchor $Q_m=m^2+m+1$, cardinality is recoverable
   from carry data at radius exactly $\lceil m/2 \rceil$, with **no quotient
   window** — strictly stronger than the prior lemma on both axes, and sharp.
2. **Containment-free closure** (Prop 2) — the block-extension step needs
   only a cardinality bound, no containment or mass hypotheses.
3. **Quadratic wall** (Prop 3) — any $k$-element block with the exact
   all-quotient scalar-carry property has anchor $Q \ge \lfloor k^2/4\rfloor+1$:
   the scalar-carry framework cannot be pushed below quadratic growth.
4. **Staggered-lift rigidity** (Prop 4) — lifts of the known residue system
   preserving unit-error carry are trivial; genuinely new residue systems are
   the only route to overlapping scales.

## Contents

| Path | What it is |
|---|---|
| `note/note.pdf`, `note/note.tex` | The note (self-contained proofs of Props 1–4) |
| `lean/` | Lean 4 formalization of Prop 1 (both directions — the lemma *and* its sharpness for every $m$) and Prop 2. Zero `sorry`s; axioms only `propext, Classical.choice, Quot.sound`. See `lean/STATUS.md` for the theorem inventory and build instructions. |
| `verification/` | Machine checks: exact violation-frontier computation confirming Prop 1's sharpness constant $\lceil m/2\rceil + 1$ for all $m \le 26$, plus the (stdlib-only) Python tools to reproduce them. |
| `provenance/` | Full transcripts of how these results were produced and vetted (see below). |

## Building the Lean project

```bash
cd lean
lake update        # first time: fetches mathlib (pinned v4.30.0-rc2)
lake exe cache get # first time: prebuilt mathlib oleans
lake build         # ~1–2 min: Erdos875.CarryLemma, Erdos875.Closure
```

Key theorems: `Erdos875.local_carry`, `Erdos875.local_carry_sharp`
(Prop 1), `Erdos875.weaklyCarryGood_union` (Prop 2). The toolchain is pinned
to the same versions as Mazur's repository so results are directly
comparable. No code from that repository is reused (it carries no license);
definitions here are written fresh from the note's statements.

## Provenance

These results were produced by frontier language models under human
orchestration, with a fixed adversarial pipeline: proofs found by one model
family (OpenAI gpt-5.6-sol) were line-by-line adversarially critiqued by a
different family (Anthropic Claude Fable 5) under a default-refute
instruction, then literature-checked, machine-checked, and formalized.
The unedited transcripts of the attack, the critique, and the literature
check are in `provenance/`. Errors that survive all that are ours; please
report them on the problem thread or as issues here.

## License

Code (`lean/`, `verification/`) is MIT-licensed; the note and other text are
CC BY 4.0. See `LICENSE`.
