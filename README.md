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
- Zero `sorry` / `admit`
- No `native_decide` (`decide` on small bounded computations only)
- Axioms: `[propext, Quot.sound]`

## Proof summary

| Lemma | Method |
|---|---|
| `coprime_dvd` | From `gcd p a = 1` and `p ∣ a*b` conclude `p ∣ b`, via `gcd(p*b, a*b) = b * gcd p a`. |
| `euclid_general` | If `PrimeP p` and `p ∣ a*b` then `p ∣ a ∨ p ∣ b`. |
| `primeP_dvd_sq`, `primeP_dvd_cube` | Prime dividing `a*a` (resp. `a*a*a`) divides `a`. |
| `primeP_2/3/13/23` | Kernel `decide` primality certificates over bounded trial division. |
| `powerful_12167` | `12167 = 23^3`; the only prime divisor is 23, and `23^2 ∣ 23^3`. |
| `powerful_12168` | `12168 = 2^3 * 3^2 * 13^2`; prime divisors are exactly 2, 3, 13, whose squares divide 12168. |
| `not_square_12167`, `not_square_12168` | `110^2 < n < 111^2`, so `n` lies strictly between consecutive squares. |

## Build and verify

```bash
# Lean 4.20.0 (see ./lean-toolchain)
lake build          # builds the default target Jsp000301

# or directly
lean Jsp000301.lean
```

Axiom audit (inside Lean, or from the build log):

```
#print axioms jsp_000301
-- 'jsp_000301' depends on axioms: [propext, Quot.sound]
```

## Mathematical attribution

The mathematical counterexample is due to published literature:

- S. W. Golomb, *Powerful numbers*, Amer. Math. Monthly 77(8) (1970), 848-852.
- D. T. Walker, *Consecutive integer pairs of powerful numbers and related Diophantine equations*, Fibonacci Quart. (1976), 111-116.
- R. K. Guy, *Unsolved Problems in Number Theory* (2004).
- Attribution source: https://www.erdosproblems.com/latex/365

This repository claims **formalization authorship only** (Lean 4.20.0).