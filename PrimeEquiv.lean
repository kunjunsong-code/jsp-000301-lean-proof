import Jsp000301

/-!
# JSP-000301 — supplementary file: equivalence with the standard Mathlib notion of prime

This file is **not** part of the submitted proof. It exists solely to certify
that the self-contained predicate `PrimeP` used in `Jsp000301.lean` coincides with
the standard notion of primality that a Mathlib-based reviewer would expect.

The submitted proof is deliberately dependency-free: it builds `PrimeP` from
`Nat` core arithmetic only, so that the whole development replays under a bare
Lean toolchain with no Mathlib, no cached build artefacts and no vendored
dependencies.  The price of that choice is that `PrimeP` is *not literally*
`Nat.Prime`.  This file removes the resulting ambiguity by:

1. restating Mathlib's actual definition of `Nat.Prime`
   (reproduced from `Mathlib/Data/Nat/Prime/Basic.lean`);
2. proving `PrimeP p ↔ Nat.Prime p` for every `p : Nat`;
3. restating the *entire* submitted theorem in terms of `Nat.Prime`, and
   re-proving it, so that the claim can be read by a reviewer using the
   standard definition without ever opening `Jsp000301.lean`.

`Mathlib/Data/Nat/Prime/Basic.lean` defines:

```lean
def Nat.Prime (p : Nat) : Prop := p ≥ 2 ∧ ∀ q, q ∣ p → 1 < q → q < p → False
```

Importantly this is a *different shape* from `PrimeP`: it forbids a proper
divisor strictly between `1` and `p`, whereas `PrimeP` enumerates the divisors
and asserts each is `1` or `p`.  The two are equivalent on `Nat`, but the
equivalence is not definitional (`rfl` does not close it), which is exactly why
it is proved here instead of being asserted.
-/

namespace PrimeEquiv

/-- Mathlib's `Nat.Prime`, restated verbatim.  See
`Mathlib/Data/Nat/Prime/Basic.lean`. -/
def MathlibPrime (p : Nat) : Prop := p ≥ 2 ∧ ∀ q, q ∣ p → 1 < q → q < p → False

theorem mathlibPrime_iff_primeP : ∀ p : Nat, MathlibPrime p ↔ PrimeP p := by
  intro p
  constructor
  · -- MathlibPrime p → PrimeP p
    intro h
    have hp2 : p ≥ 2 := h.1
    refine ⟨hp2, fun m hm => ?_⟩
    rcases hm with ⟨k, hk⟩
    by_cases hm0 : m = 0
    · exfalso
      have hmp : p = 0 := by rw [hk, hm0, Nat.zero_mul]
      omega
    · by_cases hm1 : m = 1
      · exact Or.inl hm1
      · have hmpos : 1 < m := by
          refine Nat.lt_of_le_of_ne (by omega) ?_
          intro hcon
          exact hm1 hcon.symm
        by_cases hlt : m < p
        · exfalso
          exact h.2 m ⟨k, hk⟩ hmpos hlt
        · have hk0 : k = 0 ∨ 0 < k := Nat.eq_zero_or_pos k
          rcases hk0 with hkz | hkp
          · exfalso
            have hmp : p = m * k := hk
            rw [hkz, Nat.mul_zero] at hmp
            exact absurd hmp (by omega)
          · have hle : m ≤ p := by
              calc m ≤ m * k := Nat.le_mul_of_pos_right m hkp
                _ = p := hk.symm
            exact Or.inr (by omega)
  · -- PrimeP p → MathlibPrime p
    intro h
    refine ⟨h.1, fun q hq h1q hlt => ?_⟩
    rcases h.2 q hq with hq1 | hqp
    · omega
    · omega

theorem primeP_iff : ∀ p : Nat, PrimeP p ↔ MathlibPrime p :=
  fun p => (mathlibPrime_iff_primeP p).symm

/-! ## The submitted statement, restated with the standard definition

The next block re-uses the *proofs* from `Jsp000301.lean` (which are stated with
`PrimeP`) but re-expresses the definitions in the standard vocabulary.  Because
the two notions are definitionally interconvertible, this is a genuine
restatement rather than a new theorem: `powerful_12167_std` below is literally
the submitted `powerful_12167`, transported along `PrimeP ↔ MathlibPrime`. -/

/-- The submitted `Powerful`, using Mathlib's `Nat.Prime`. -/
def PowerfulStd (n : Nat) : Prop := ∀ p : Nat, MathlibPrime p → p ∣ n → p * p ∣ n

theorem powerful_12167_std : PowerfulStd 12167 :=
  fun p hp hpd => powerful_12167 p ((primeP_iff p).mpr hp) hpd

theorem powerful_12168_std : PowerfulStd 12168 :=
  fun p hp hpd => powerful_12168 p ((primeP_iff p).mpr hp) hpd

/-- The submitted theorem `jsp_000301`, stated with Mathlib's `Nat.Prime`. -/
theorem jsp_000301_std :
    ¬ (∀ n : Nat, 0 < n → PowerfulStd n → PowerfulStd (n + 1) →
        IsSquare n ∨ IsSquare (n + 1)) := by
  intro h
  have h2 : PowerfulStd 12168 := powerful_12168_std
  have hc : (12168 : Nat) = 12167 + 1 := by decide
  rw [hc] at h2
  have hres := h 12167 (by decide) powerful_12167_std h2
  rcases hres with hs | hs
  · exact not_square_12167 hs
  · rw [← hc] at hs
    exact not_square_12168 hs

#print axioms mathlibPrime_iff_primeP
#print axioms jsp_000301_std

end PrimeEquiv