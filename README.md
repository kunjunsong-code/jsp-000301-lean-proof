# JSP-000301 - Consecutive powerful numbers need not include a perfect square

**Justin Sun Prize - JSP-000301 - Lean 4.20.0 formalization (no Mathlib)**

## Overview

Problem (problem bank, `problems/catalog-0301-0400.md#JSP-000301`):

> If two consecutive positive integers are powerful, must at least one be a perfect square?

**Answer: No.** Counterexample: **12167 = 23^3** and **12168 = 2^3 * 3^2 * 13^2**.

Both are powerful (every prime divisor occurs with exponent >= 2), neither is a perfect square
(110^2 = 12100 < 12167 < 12168 < 12321 = 111^2), and they are consecutive.

## Definitions and formal statements

```lean
def PrimeP (p : Nat) : Prop := 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p
def Powerful (n : Nat) : Prop := ∀ p, PrimeP p → p ∣ n → p * p ∣ n
def IsSquare (n : Nat) : Prop := ∃ k, n = k * k

/-- Top-level result: the literal negation of the original question. -/
theorem jsp_000301 :
    ¬ (∀ n : Nat, 0 < n → Powerful n → Powerful (n + 1) →
        IsSquare n ∨ IsSquare (n + 1))

/-- The counterexample packaged as a single statement. -/
theorem jsp_000301_counterexample :
    Powerful 12167 ∧ Powerful 12168 ∧
    ¬ IsSquare 12167 ∧ ¬ IsSquare 12168 ∧
    12168 = 12167 + 1
```

`jsp_000301` is derived from `jsp_000301_counterexample`; a counterexample fully resolves a
yes/no question, so the full original problem is covered.

## Key features

- Zero Mathlib dependency - pure Lean 4 core only
- Zero package dependencies at all (`lake-manifest.json` has an empty `packages` array)
- Zero `sorry` / `admit` / added `axiom`
- No `native_decide` (`decide` on small bounded computations only)
- Axioms: `[propext, Quot.sound]` — Lean's standard classical-logic baseline

## Repository layout

| File | Lines | Role |
| --- | --- | --- |
| `Jsp000301.lean` | 266 | **The submitted proof.** Self-contained; imports nothing. |
| `PrimeEquiv.lean` | 116 | Proves `PrimeP ↔ Mathlib Prime` and restates the result in standard `Nat.Prime` vocabulary. Imports `Jsp000301`. |
| `IndependentCheck.lean` | 251 | Second, from-scratch derivation of every arithmetic fact by kernel-decided exhaustive enumeration. Imports `PrimeEquiv`. |
| `CATALOG_PROPOSAL.md` | — | Bibliographic evidence for the proposed `Date proposed` / `Elapsed years` values. |
| `CATALOG_PATCH.md` | — | Exact catalog table replacement plus per-field rationale. |
| `PR_BODY.md` | — | Completed PR template, ready to paste. |

`lake build` builds all three libraries (`defaultTargets`).

## Proof summary

### `Jsp000301.lean` — the submitted route

| Lemma | Method |
|---|---|
| `coprime_dvd` | From `gcd p a = 1` and `p ∣ a*b` conclude `p ∣ b`, via `gcd(p*b, a*b) = b * gcd p a`. |
| `euclid_general` | If `PrimeP p` and `p ∣ a*b` then `p ∣ a ∨ p ∣ b`. |
| `primeP_dvd_sq`, `primeP_dvd_cube` | Prime dividing `a*a` (resp. `a*a*a`) divides `a`. |
| `primeP_2/3/13/23` | Kernel `decide` primality certificates over bounded trial division. |
| `powerful_12167` | `12167 = 23^3`; the only prime divisor is 23, and `23^2 ∣ 23^3`. |
| `powerful_12168` | `12168 = 2^3 * 3^2 * 13^2`; prime divisors are exactly 2, 3, 13, whose squares divide 12168. |
| `sq_mono`, `sq_le_of_le` | Strict/weak monotonicity of squaring on `Nat`, proved from `Nat.mul_lt_mul_of_pos_*`. |
| `not_square_12167`, `not_square_12168` | Split on `k ≤ 110`; `110^2 = 12100` and `111^2 = 12321` are `decide`-checked literals, both branches close arithmetically. |

### `IndependentCheck.lean` — the independent route

Shares **no reasoning step** with the file above. Every arithmetic fact is
re-derived by kernel-decided exhaustive enumeration in the shape
`(List.range B).all (fun d => decide (P d)) = true`:

| Fact | Route in `IndependentCheck` |
|---|---|
| divisors of 12167 | scan over `0 … 12167`; the only divisors are `1, 23, 529, 12167` |
| `¬ IsSquare n` | scan: **no divisor `d` of `n` has `d*d = n`** (no monotonicity argument) |
| prime divisors | scan: every divisor other than `1`, 23 resp. 2/3/13 is composite, with an explicit witness factor in range `24` resp. `112` |
| `Powerful n` | from the prime-divisor result plus `decide`-checked `p² ∣ n` |

**What this does not replace.** The official `ComparatorChallenges` route
(comparator + nanoda, from `openai/ten-proofs`) could **not** be run here:
`landrun` / `lean4export` / `nanoda_bin` are absent, there is no Rust toolchain to
build them, only Lean 4.20.0 is installed where the challenges pin 4.32.0, and the
challenges themselves `import Mathlib`. Per the `lean-verify` skill's instruction —
*"unavailable tools leave a stated gap, not a claim of independent verification"* —
that gap is stated, not papered over. `IndependentCheck.lean` is a second
derivation, **not** a second independent proof checker, and is not claimed to be.

## Build and verify

```bash
# Lean 4.20.0 (see ./lean-toolchain)
rm -rf .lake/build      # clean rebuild
lake build              # builds all three defaultTargets
```

Measured: clean rebuild ≈ 22 s, exit code 0.

Axiom audit:

```bash
cat > Check.lean <<'EOF'
import Jsp000301
import PrimeEquiv
import IndependentCheck
#print axioms jsp_000301
#print axioms jsp_000301_counterexample
#print axioms PrimeEquiv.mathlibPrime_iff_primeP
#print axioms PrimeEquiv.jsp_000301_std
#print axioms IndependentCheck.jsp_000301_independent
EOF
lake env lean Check.lean
```

```
'jsp_000301' depends on axioms: [propext, Quot.sound]
'jsp_000301_counterexample' depends on axioms: [propext, Quot.sound]
'PrimeEquiv.mathlibPrime_iff_primeP' depends on axioms: [propext, Quot.sound]
'PrimeEquiv.jsp_000301_std' depends on axioms: [propext, Quot.sound]
'IndependentCheck.jsp_000301_independent' depends on axioms: [propext, Quot.sound]
```

`Quot.sound` enters only through `List.all` / `List.Mem`, which are implemented via
`Classical.choice` + `propext`. It is the standard Lean 4 baseline for any proof
that manipulates a `List`, and per the PR template, *"Standard Lean axioms are not
automatically disqualifying."*

## Mathematical attribution

The mathematical counterexample is due to published literature:

- S. W. Golomb, *Powerful numbers*, Amer. Math. Monthly 77(8) (1970), 848-852.
  <https://doi.org/10.2307/2317020> — introduces the term "powerful" and gives the
  counterexample in the same paper (Zentralblatt MATH 0218.10018).
- D. T. Walker, *Consecutive integer pairs of powerful numbers and related Diophantine equations*, Fibonacci Quart. (1976), 111-116.
- R. K. Guy, *Unsolved Problems in Number Theory* (2004).
- Attribution source: https://www.erdosproblems.com/latex/365

The `Date proposed` value proposed for the catalog is **`No later than 1970`**: the
question cannot postdate its own 1970 answer. No pre-1970 written statement has been
located, and none is claimed. See `CATALOG_PROPOSAL.md` for the full argument,
including why `[Er76d]` (1976) and `[ErGr80]` (1980) cannot serve as the origin
date.

This repository claims **formalization authorship only** (Lean 4.20.0). The
mathematical solution is Golomb's.