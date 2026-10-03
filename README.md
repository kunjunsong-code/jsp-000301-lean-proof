# JSP-000301 — Consecutive powerful numbers need not include a perfect square

**Justin Sun Prize · JSP-000301 · Lean 4 Formalization**

## Overview

This repository provides a complete machine-verified Lean 4 formalization of the counterexample to JSP-000301:

> If two consecutive positive integers are powerful, must at least one be a perfect square?

**Answer: No.** Counterexample: **12167 = 23³** and **12168 = 2³ × 3² × 13²**.

Both are powerful (every prime divisor has exponent ≥ 2), neither is a perfect square (110² = 12100 < both < 12321 = 111²), and they are consecutive (12168 = 12167 + 1).

## Key Features

- **Zero Mathlib dependency** — pure Lean 4 core only
- **Zero `sorry`** — complete proof from axioms
- **Standard axioms only** — `#print axioms jsp_000301` shows only `[propext, Quot.sound]`
- **No `native_decide`** — small kernel `decide` calls only (factorizations, primality checks over bounded ranges)

## Formal Statement

```lean
def PrimeP (p : Nat) : Prop := 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p
def Powerful (n : Nat) : Prop := ∀ p, PrimeP p → p ∣ n → p * p ∣ n
def IsSquare (n : Nat) : Prop := ∃ k, n = k * k

theorem jsp_000301 :
    Powerful 12167 ∧ Powerful 12168 ∧
    ¬ IsSquare 12167 ∧ ¬ IsSquare 12168 ∧
    12168 = 12167 + 1
```

## Proof Summary

| Lemma | Method |
|---|---|
| `coprime_dvd` | If `gcd(p, a) = 1` and `p ∣ a*b`, then `p ∣ b`. Proved by calculating `gcd(p*b, a*b) = b * gcd(p, a) = b` via `Nat.gcd_mul_left`. |
| `euclid_general` | If `PrimeP p` and `p ∣ a*b`, then `p ∣ a ∨ p ∣ b`. Case split: if `p ∣ a`, done; else `gcd(p, a) = 1` (since `PrimeP` means only divisors are `1` and `p`), apply `coprime_dvd`. |
| `primeP_dvd_sq` / `primeP_dvd_cube` | If `PrimeP p` and `p ∣ a²` / `p ∣ a³`, then `p ∣ a`. Direct from `euclid_general`. |
| Small prime certificates (2, 3, 13, 23) | Kernel `decide` on `List.range` bounded trial division. |
| `powerful_12167` | `12167 = 23³`. Any prime divisor `p` of 23³ equals 23; `23² ∣ 23³` ✓ |
| `powerful_12168` | `12168 = 2³ × 3² × 13²`. Factor out via `euclid_general`; only prime divisors are 2, 3, 13; their squares all divide 12168 ✓ |
| Non-square | `110² = 12100 < 12167 < 12168 < 12321 = 111²`. Bounded interval, no square possible ✓ |

## Build and Verify

```bash
# Install Lean 4.20.0
elan install leanprover/lean4:v4.20.0

# Verify the proof compiles
lean proof/Jsp000301.lean

# Check axioms (should show only propext + Quot.sound)
lean proof/Jsp000301.lean --print axioms
# or inside Lean: #print axioms jsp_000301
```

## Mathematical Attribution

The mathematical result (the counterexample 12167/12168) is due to published literature:
- S. W. Golomb, *Powerful numbers*, Amer. Math. Monthly 77 (1970), 848–855.
- D. T. Walker, *Consecutive integer pairs of powerful numbers and related Diophantine equations*, Fibonacci Quart. 14 (1976), 111–116.
- R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed. (2004), B16.

This repository claims **formalization authorship only**. Per Justin Sun Prize rules: problems solved before 2026-01-01 but formalized afterward entitle the formalizer to the formalization portion (30%) of the award.

## Axiom Audit

```
jsp_000301 depends on axioms: [propext, Quot.sound]
```

No `sorryAx`, no `Classical.choice`, no `native_decide` / `Lean.ofReduceBool`, no custom axioms.
