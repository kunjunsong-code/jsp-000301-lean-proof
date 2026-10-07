import PrimeEquiv

/-!
# JSP-000301 — supplementary file: independent arithmetic re-derivation

This file is **not** part of the submitted proof.  It exists to supply an
*independently defined* check of the arithmetic facts on which the refutation
rests, in the spirit of `skills/lean-verify/SKILL.md:75`:

> "Where compatible, also use an independently defined challenge with a
> comparator/external checker."

## Why this file exists, and what it does not replace

The official `ComparatorChallenges` route (comparator + nanoda, from
`openai/ten-proofs`) could **not** be run for this submission.  Verified
locally:

| Requirement | Available here |
| --- | --- |
| `landrun`, `lean4export`, `nanoda_bin` on `PATH` | none present |
| Rust toolchain to build them | absent |
| Toolchain `leanprover/lean4:v4.32.0` (per `ten-proofs/lean-toolchain`) | only `v4.20.0` installed |

The official challenges are also Mathlib-dependent (`import Mathlib`), whereas
this submission is deliberately dependency-free and pinned to `v4.20.0`.

Per the skill's own instruction — *"unavailable tools leave a stated gap, not a
claim of independent verification"* — that gap is **stated, not papered over.**

## What this file does instead

Every arithmetic fact below is re-established by **exhaustive enumeration
decided by the kernel**, in the shape
`(List.range B).all (fun d => decide (P d)) = true`.  This file shares **no
reasoning step** with `Jsp000301.lean`:

| Fact | Submitted file | This file |
| --- | --- | --- |
| which numbers are prime | primality certificates (`primeP_of_cert`) | scan: every divisor other than `1`, 23 resp. 2/3/13 is composite, with an explicit factor |
| `Powerful 12167` | `p ∣ 23^3 → p ∣ 23 → p = 23` (Euclid's lemma) | scan: the only non-composite divisors of 12167 are `1` and `23` |
| `¬ IsSquare 12167` | monotonicity (`sq_le_of_le`) + two `omega` bounds | scan: no divisor `d` of 12167 satisfies `d * d = 12167` |
| `¬ IsSquare 12168` | monotonicity + two `omega` bounds | scan: no divisor `d` of 12168 satisfies `d * d = 12168` |

`MathlibPrime` (from `PrimeEquiv`) is reused purely as the *statement
vocabulary*; its characterisation is consumed only in the direction "no
divisor strictly between 1 and p", never as a primality certificate.

No `sorry`, no `axiom`, no `native_decide`.  `#print axioms` at the bottom of
this file reports the trusted footprint.

## Implementation notes

* The two `set_option`s are **resource limits only** (kernel stack depth and
  evaluation budget for the `decide`-over-`List.range` scans, the largest of
  which walks 12 169 entries).  They introduce no axiom.
* In the composite scans of §4 the inner witness search is bounded by a
  **fixed** range (`24` for 12167, `112` for 12168) rather than
  `List.range d`.  The bound is sound because a composite `d ≤ 12168` has a
  factor `q` with `1 < q ≤ √d < 112`; the kernel confirms the resulting finite
  statement, so the bound is *checked*, not assumed.  The fixed bound also keeps
  the `decide` term small enough for the kernel stack.
* Each scan is read off by an explicit `List.all_eq_true.mp …` at the use site
  rather than through a generic helper.  A helper taking the predicate as an
  implicit argument makes the elaborator unfold the 12 169-element `List.range`
  during unification, which overflows the kernel stack.
-/

namespace IndependentCheck

open PrimeEquiv

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! ### 0. A divisor of a positive natural number does not exceed it

Re-derived here rather than imported: the submitted file's copy is `private`
and therefore invisible across module boundaries. -/

private theorem dvd_le {d n : Nat} (hn : 0 < n) (h : d ∣ n) : d ≤ n := by
  rcases h with ⟨k, hk⟩
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · rw [hk, hk0, Nat.mul_zero] at hn
    exact absurd hn (Nat.lt_irrefl 0)
  · rw [hk]
    exact Nat.le_mul_of_pos_right d hk0

/-- `MathlibPrime` rules out any factor strictly between 1 and `p`. -/
private theorem no_factor_of_prime {p q : Nat} (hp : MathlibPrime p)
    (h1 : 1 < q) (h2 : q < p) (h3 : q ∣ p) : False :=
  hp.2 q h3 h1 h2

/-! ### 1. The two numbers are consecutive, and their factorisations -/

theorem consecutive : (12168 : Nat) = 12167 + 1 := by decide

theorem fact_12167 : (12167 : Nat) = 23 * 23 * 23 := by decide

theorem fact_12168 : (12168 : Nat) = 2 * 2 * 2 * (3 * 3) * (13 * 13) := by decide

/-! ### 2. Exhaustive scan: the divisors of 12167

12167 = 23³, so its divisors are 1, 23, 529 and 12167 — **four** of them.
The scan decides, by kernel evaluation over `0 … 12167`, that no other `d`
divides 12167. -/

theorem scan_divisors_12167 :
    (List.range 12168).all (fun d =>
      decide (d ∣ 12167 → d = 1 ∨ d = 23 ∨ d = 529 ∨ d = 12167)) = true := by decide

theorem divisors_12167 :
    ∀ d : Nat, d ∣ 12167 → d = 1 ∨ d = 23 ∨ d = 529 ∨ d = 12167 := by
  intro d hd
  have hle : d ≤ 12167 := dvd_le (by decide) hd
  have hall : decide (d ∣ 12167 → d = 1 ∨ d = 23 ∨ d = 529 ∨ d = 12167) = true :=
    List.all_eq_true.mp scan_divisors_12167 d (by rw [List.mem_range]; omega)
  exact of_decide_eq_true hall hd

/-! ### 3. Exhaustive scan: neither number is a perfect square

If `12167 = k * k` then `k ∣ 12167`, so it suffices to check that **no divisor**
of 12167 has square 12167 — a closed, finite proposition.  The same holds for
12168.  This replaces the submitted file's monotonicity argument with a single
kernel-decided exhaustive statement. -/

theorem scan_nosq_12167 :
    (List.range 12168).all (fun d => decide (d ∣ 12167 → d * d ≠ 12167)) = true := by decide

theorem scan_nosq_12168 :
    (List.range 12169).all (fun d => decide (d ∣ 12168 → d * d ≠ 12168)) = true := by decide

theorem not_square_12167' : ¬ IsSquare 12167 := by
  intro h
  rcases h with ⟨k, hk⟩
  have hle : k ≤ 12167 := dvd_le (by decide) ⟨k, hk⟩
  have hall : decide (k ∣ 12167 → k * k ≠ 12167) = true :=
    List.all_eq_true.mp scan_nosq_12167 k (by rw [List.mem_range]; omega)
  exact absurd hk.symm ((of_decide_eq_true hall) ⟨k, hk⟩)

theorem not_square_12168' : ¬ IsSquare 12168 := by
  intro h
  rcases h with ⟨k, hk⟩
  have hle : k ≤ 12168 := dvd_le (by decide) ⟨k, hk⟩
  have hall : decide (k ∣ 12168 → k * k ≠ 12168) = true :=
    List.all_eq_true.mp scan_nosq_12168 k (by rw [List.mem_range]; omega)
  exact absurd hk.symm ((of_decide_eq_true hall) ⟨k, hk⟩)

/-! ### 4. Exhaustive scan: which divisors are prime

`MathlibPrime p` says `p ≥ 2` and that no `q` divides `p` with `1 < q < p`.
For a *fixed literal* `d`, "some q with `1 < q < d` divides `d`" is a bounded
`decide`.  So each scan enumerates all divisors of the number and records, for
every one of them, either that it is `1` (or 2, 3, 13), or that it is composite
with an explicit witness factor.

This replaces the submitted file's Euclid's lemma plus primality-certificate
chain (`primeP_dvd_cube` → `primeP_eq_of_dvd` → `primeP_23`). -/

theorem scan_composite_12167 :
    (List.range 12168).all (fun d =>
      decide (d ∣ 12167 →
        d = 1 ∨ d = 23 ∨ ∃ q ∈ List.range 24, 1 < q ∧ q < d ∧ q ∣ d)) = true := by decide

theorem scan_composite_12168 :
    (List.range 12169).all (fun d =>
      decide (d ∣ 12168 →
        d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 13 ∨
        ∃ q ∈ List.range 112, 1 < q ∧ q < d ∧ q ∣ d)) = true := by decide

theorem prime_div_12167 :
    ∀ p : Nat, MathlibPrime p → p ∣ 12167 → p = 23 := by
  intro p hp hpd
  have hle : p ≤ 12167 := dvd_le (by decide) hpd
  have hall : decide (p ∣ 12167 →
      p = 1 ∨ p = 23 ∨ ∃ q ∈ List.range 24, 1 < q ∧ q < p ∧ q ∣ p) = true :=
    List.all_eq_true.mp scan_composite_12167 p (by rw [List.mem_range]; omega)
  rcases of_decide_eq_true hall hpd with h1 | h23 | hex
  · have hp2 : p ≥ 2 := hp.1
    rw [h1] at hp2
    exact absurd hp2 (by decide)
  · exact h23
  · rcases hex with ⟨q, _, hq1, hq2, hq3⟩
    exact (no_factor_of_prime hp hq1 hq2 hq3).elim

theorem prime_div_12168 :
    ∀ p : Nat, MathlibPrime p → p ∣ 12168 → p = 2 ∨ p = 3 ∨ p = 13 := by
  intro p hp hpd
  have hle : p ≤ 12168 := dvd_le (by decide) hpd
  have hall : decide (p ∣ 12168 →
      p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 13 ∨
        ∃ q ∈ List.range 112, 1 < q ∧ q < p ∧ q ∣ p) = true :=
    List.all_eq_true.mp scan_composite_12168 p (by rw [List.mem_range]; omega)
  rcases of_decide_eq_true hall hpd with h1 | h2 | h3 | h13 | hex
  · have hp2 : p ≥ 2 := hp.1
    rw [h1] at hp2
    exact absurd hp2 (by decide)
  · exact Or.inl h2
  · exact Or.inr (Or.inl h3)
  · exact Or.inr (Or.inr h13)
  · rcases hex with ⟨q, _, hq1, hq2, hq3⟩
    exact (no_factor_of_prime hp hq1 hq2 hq3).elim

/-! ### 5. Powerful, in the standard `MathlibPrime` vocabulary -/

theorem sq23_dvd_12167 : (23 * 23 : Nat) ∣ 12167 := by decide
theorem sq2_dvd_12168 : (2 * 2 : Nat) ∣ 12168 := by decide
theorem sq3_dvd_12168 : (3 * 3 : Nat) ∣ 12168 := by decide
theorem sq13_dvd_12168 : (13 * 13 : Nat) ∣ 12168 := by decide

theorem powerful_12167_ind :
    ∀ p : Nat, MathlibPrime p → p ∣ 12167 → p * p ∣ 12167 := by
  intro p hp hpd
  rw [prime_div_12167 p hp hpd]
  exact sq23_dvd_12167

theorem powerful_12168_ind :
    ∀ p : Nat, MathlibPrime p → p ∣ 12168 → p * p ∣ 12168 := by
  intro p hp hpd
  rcases prime_div_12168 p hp hpd with h | h | h
  · rw [h]; exact sq2_dvd_12168
  · rw [h]; exact sq3_dvd_12168
  · rw [h]; exact sq13_dvd_12168

/-! ### 6. The same refutation, restated with Mathlib's `Prime` -/

theorem jsp_000301_independent :
    ¬ (∀ n : Nat, 0 < n →
        (∀ p : Nat, MathlibPrime p → p ∣ n → p * p ∣ n) →
        (∀ p : Nat, MathlibPrime p → p ∣ (n + 1) → p * p ∣ (n + 1)) →
        IsSquare n ∨ IsSquare (n + 1)) := by
  intro h
  have hc : (12168 : Nat) = 12167 + 1 := consecutive
  have h12168 : ∀ p : Nat, MathlibPrime p → p ∣ (12167 + 1) → p * p ∣ (12167 + 1) := by
    rw [← hc]
    exact powerful_12168_ind
  have hres := h 12167 (by decide) powerful_12167_ind h12168
  rcases hres with hs | hs
  · exact not_square_12167' hs
  · rw [← hc] at hs
    exact not_square_12168' hs

#print axioms divisors_12167
#print axioms not_square_12167'
#print axioms not_square_12168'
#print axioms prime_div_12167
#print axioms prime_div_12168
#print axioms powerful_12167_ind
#print axioms powerful_12168_ind
#print axioms jsp_000301_independent

end IndependentCheck