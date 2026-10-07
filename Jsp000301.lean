/-!
# JSP-000301 — formalization (Lean 4.20.0, no Mathlib)

Problem (problem bank, catalog-0301-0400.md):
  "If two consecutive positive integers are powerful, must at least one be a
   perfect square?"

Answer: **No**.  Solomon W. Golomb (1970) gave the counterexample
  12167 = 23^3          (powerful, not a square)
  12168 = 2^3 * 3^2 * 13^2  (powerful, not a square)
These are consecutive positive integers, both powerful, and neither is a square.
This refutes the universally quantified question.

A powerful (squareful) number is one in which every prime that divides it
divides it with exponent at least 2.  A perfect square is `k * k`.

All declarations below are proved with core Lean tactics (`decide`, `omega`) and
depend only on the standard classical axioms reported by `#print axioms`.
-/

set_option maxRecDepth 20000

/-- `p` is prime in the elementary sense used here: `p ≥ 2` and its only
divisors are `1` and `p`. -/
def PrimeP (p : Nat) : Prop := 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p

/-- A powerful (squareful) number: every prime dividing `n` divides it squared. -/
def Powerful (n : Nat) := ∀ p, PrimeP p → p ∣ n → p * p ∣ n

/-- `n` is a perfect square. -/
def IsSquare (n : Nat) := ∃ k, n = k * k

theorem mod_eq_zero_of_dvd {m n : Nat} (h : m ∣ n) : n % m = 0 := by
  cases h with | intro k hk => rw [hk]; exact Nat.mul_mod_right m k

private theorem le_of_dvd_pos {m n : Nat} (hn : 0 < n) (h : m ∣ n) : m ≤ n := by
  cases h with
  | intro k hk =>
    cases Nat.eq_zero_or_pos k with
    | inl hk0 => rw [hk, hk0, Nat.mul_zero] at hn; exact absurd hn (Nat.lt_irrefl 0)
    | inr hk0 => rw [hk]; exact Nat.le_mul_of_pos_right m hk0

theorem primeP_of_cert (p : Nat) (h2 : 2 ≤ p)
    (h : ((List.range (p + 1)).all fun m =>
      decide (p % m ≠ 0) || decide (m = 1) || decide (m = p)) = true) :
    PrimeP p := by
  refine ⟨h2, fun m hm => ?_⟩
  have hmp : m ≤ p := le_of_dvd_pos (by omega) hm
  have hall := List.all_eq_true.mp h m (by rw [List.mem_range]; omega)
  have hmod : p % m = 0 := mod_eq_zero_of_dvd hm
  rw [Bool.or_eq_true] at hall
  cases hall with
  | inr hpq => exact Or.inr (decide_eq_true_eq.mp hpq)
  | inl hab =>
    rw [Bool.or_eq_true] at hab
    cases hab with
    | inl hne => exact absurd hmod (decide_eq_true_eq.mp hne)
    | inr h1 => exact Or.inl (decide_eq_true_eq.mp h1)

theorem primeP_2 : PrimeP 2 := primeP_of_cert 2 (by decide) (by decide)
theorem primeP_3 : PrimeP 3 := primeP_of_cert 3 (by decide) (by decide)
theorem primeP_13 : PrimeP 13 := primeP_of_cert 13 (by decide) (by decide)
theorem primeP_23 : PrimeP 23 := primeP_of_cert 23 (by decide) (by decide)

/-- Euclid's lemma in the elementary form needed here. -/
theorem coprime_dvd :
    ∀ (p a b : Nat), 0 < p → Nat.gcd p a = 1 → p ∣ a * b → p ∣ b := by
  intro p a b hp h1 h2
  have h41 : Nat.gcd (p * b) (a * b) = Nat.gcd (b * p) (a * b) := by
    rw [Nat.mul_comm p b]
  have h42 : Nat.gcd (b * p) (a * b) = Nat.gcd (b * p) (b * a) := by
    rw [Nat.mul_comm a b]
  have h43 : Nat.gcd (b * p) (b * a) = Nat.gcd (b * a) (b * p) := Nat.gcd_comm (b * p) (b * a)
  have h44 : Nat.gcd (b * a) (b * p) = b * Nat.gcd a p := Nat.gcd_mul_left b a p
  have h45 : Nat.gcd a p = Nat.gcd p a := Nat.gcd_comm a p
  have h3 : Nat.gcd (p * b) (a * b) = b * Nat.gcd p a := by
    calc
      Nat.gcd (p * b) (a * b) = Nat.gcd (b * p) (a * b) := h41
      _ = Nat.gcd (b * p) (b * a) := h42
      _ = Nat.gcd (b * a) (b * p) := h43
      _ = b * Nat.gcd a p := h44
      _ = b * Nat.gcd p a := by rw [h45]
  rw [h1] at h3
  have h3' : Nat.gcd (p * b) (a * b) = b := by
    have h : Nat.gcd (p * b) (a * b) = b * 1 := h3
    have h20 : b * (1 : Nat) = b := Nat.mul_one b
    rw [h20] at h
    exact h
  rcases h2 with ⟨k, hk⟩
  have h6 : Nat.gcd (p * b) (a * b) = Nat.gcd (p * b) (p * k) := by
    have h61 : a * b = p * k := hk
    rw [h61]
  rw [h6] at h3'
  have h7 : Nat.gcd (p * b) (p * k) = p * Nat.gcd b k := Nat.gcd_mul_left p b k
  rw [h7] at h3'
  have h9 : b = p * Nat.gcd b k := h3'.symm
  exact ⟨Nat.gcd b k, h9⟩

theorem euclid_general (p a b : Nat) (hp : PrimeP p) (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  by_cases ha : p ∣ a
  · exact Or.inl ha
  · have hp1 : 2 ≤ p := hp.1
    have hp2 : 0 < p := Nat.le_trans (by decide) hp1
    have hga : Nat.gcd p a ∣ p := Nat.gcd_dvd_left p a
    have hcases : Nat.gcd p a = 1 ∨ Nat.gcd p a = p := hp.2 (Nat.gcd p a) hga
    have hne : Nat.gcd p a ≠ p := by
      intro hge
      have hga2 : Nat.gcd p a ∣ a := Nat.gcd_dvd_right p a
      have hpa : p ∣ a := by rw [hge] at hga2; exact hga2
      exact ha hpa
    have hg1 : Nat.gcd p a = 1 := by
      cases hcases with
      | inl h1 => exact h1
      | inr h2 => exfalso; exact hne h2
    have h2 : p ∣ b := coprime_dvd p a b hp2 hg1 h
    exact Or.inr h2

theorem primeP_dvd_sq (p a : Nat) (hp : PrimeP p) (h : p ∣ a * a) : p ∣ a := by
  have h' : p ∣ a ∨ p ∣ a := euclid_general p a a hp h
  cases h' with
  | inl h => exact h
  | inr h => exact h

theorem primeP_dvd_cube (p a : Nat) (hp : PrimeP p) (h : p ∣ a * a * a) : p ∣ a := by
  have h2 : p ∣ a * a ∨ p ∣ a := euclid_general p (a * a) a hp h
  cases h2 with
  | inl h2 => exact primeP_dvd_sq p a hp h2
  | inr h2 => exact h2

theorem primeP_eq_of_dvd (p q : Nat) (hp : PrimeP p) (hq : PrimeP q)
    (h : p ∣ q) : p = q := by
  have hcases : p = 1 ∨ p = q := hq.2 p h
  cases hcases with
  | inl h1 => have h2 : 2 ≤ p := hp.1; omega
  | inr h2 => exact h2

theorem cube_def (a : Nat) : a ^ 3 = a * a * a := by
  have h1 : a ^ 3 = a ^ 2 * a := by rw [Nat.pow_succ]
  have h2 : a ^ 2 = a * a := by
    have h3 : a ^ 2 = a ^ 1 * a := by rw [Nat.pow_succ]
    have h4 : a ^ 1 = a := by rw [Nat.pow_one]
    rw [h3, h4]
    <;> rfl
  rw [h1, h2]
  <;> rfl

theorem sq_def (a : Nat) : a ^ 2 = a * a := by
  have h3 : a ^ 2 = a ^ 1 * a := by rw [Nat.pow_succ]
  have h4 : a ^ 1 = a := by rw [Nat.pow_one]
  rw [h3, h4]
  <;> rfl

theorem powerful_12167 : Powerful 12167 := by
  have e : (12167 : Nat) = 23 ^ 3 := by decide
  intro p hp hpd
  rw [e] at hpd
  have hc : 23 ^ 3 = 23 * 23 * 23 := cube_def 23
  rw [hc] at hpd
  have h_p_div_23 : p ∣ 23 := primeP_dvd_cube p 23 hp hpd
  have hp23 : p = 23 := primeP_eq_of_dvd p 23 hp primeP_23 h_p_div_23
  rw [hp23]; rw [e]; decide

theorem powerful_12168 : Powerful 12168 := by
  have e : (12168 : Nat) = 2 ^ 3 * 3 ^ 2 * 13 ^ 2 := by decide
  have def23 : 2 ^ 3 = 2 * 2 * 2 := cube_def 2
  have def32 : 3 ^ 2 = 3 * 3 := sq_def 3
  have def132 : 13 ^ 2 = 13 * 13 := sq_def 13
  intro p hp hpd
  rw [e] at hpd
  have h1 : p ∣ 2 ^ 3 ∨ p ∣ 3 ^ 2 * 13 ^ 2 := euclid_general p (2 ^ 3) (3 ^ 2 * 13 ^ 2) hp hpd
  rcases h1 with (hp23 | hrest)
  · have h23 : p ∣ 2 * 2 * 2 := by rw [def23] at hp23; exact hp23
    have hpdiv2 : p ∣ 2 := primeP_dvd_cube p 2 hp h23
    have hpeq : p = 2 := primeP_eq_of_dvd p 2 hp primeP_2 hpdiv2
    rw [hpeq]; rw [e]; decide
  · have h2 : p ∣ 3 ^ 2 ∨ p ∣ 13 ^ 2 := euclid_general p (3 ^ 2) (13 ^ 2) hp hrest
    rcases h2 with (hp32 | hp132)
    · have h2' : p ∣ 3 * 3 := by rw [def32] at hp32; exact hp32
      have hpdiv3 : p ∣ 3 := primeP_dvd_sq p 3 hp h2'
      have hpeq : p = 3 := primeP_eq_of_dvd p 3 hp primeP_3 hpdiv3
      rw [hpeq]; rw [e]; decide
    · have h2'' : p ∣ 13 * 13 := by rw [def132] at hp132; exact hp132
      have hpdiv13 : p ∣ 13 := primeP_dvd_sq p 13 hp h2''
      have hpeq : p = 13 := primeP_eq_of_dvd p 13 hp primeP_13 hpdiv13
      rw [hpeq]; rw [e]; decide

theorem sq_mono : ∀ (k1 k2 : Nat), k1 < k2 → k1 * k1 < k2 * k2 := by
  intro k1 k2 h
  by_cases h0 : k1 = 0
  · subst k1
    have hk2 : 0 < k2 := by omega
    have hgoal : 0 < k2 * k2 := Nat.mul_pos hk2 hk2
    simp [Nat.zero_mul]
    exact hgoal
  · have h5 : 0 < k1 := by omega
    have h2 : 0 < k2 := by omega
    have ha : k1 * k1 < k1 * k2 := Nat.mul_lt_mul_of_pos_left h h5
    have hb : k1 * k2 < k2 * k2 := Nat.mul_lt_mul_of_pos_right h h2
    omega

theorem sq_le_of_le {m n : Nat} (h : m ≤ n) : m * m ≤ n * n := by
  by_cases h0 : m = 0
  · subst m; simp [Nat.zero_mul]
  · have h02 : 0 < m := by omega
    have hlt : m < n ∨ m = n := by omega
    cases hlt with
    | inl hlt =>
      have h7 : m * m < n * n := sq_mono m n hlt
      have hle : m * m ≤ n * n := Nat.le_of_lt h7
      exact hle
    | inr heq =>
      rw [heq]
      exact Nat.le_refl (n * n)

theorem not_square_12167 : ¬ IsSquare 12167 := by
  intro h
  rcases h with ⟨k, hk⟩
  have h110 : (110 : Nat) * 110 = 12100 := by decide
  have h111 : (111 : Nat) * 111 = 12321 := by decide
  by_cases hkle : k ≤ 110
  · have hsq_le : k * k ≤ 110 * 110 := sq_le_of_le hkle
    have h12100 : k * k ≤ 12100 := by rw [← h110]; exact hsq_le
    omega
  · have hkge : 111 ≤ k := by omega
    have hsq_ge : 111 * 111 ≤ k * k := sq_le_of_le hkge
    have h12321 : 12321 ≤ k * k := by rw [← h111]; exact hsq_ge
    omega

theorem not_square_12168 : ¬ IsSquare 12168 := by
  intro h
  rcases h with ⟨k, hk⟩
  have h110 : (110 : Nat) * 110 = 12100 := by decide
  have h111 : (111 : Nat) * 111 = 12321 := by decide
  by_cases hkle : k ≤ 110
  · have hsq_le : k * k ≤ 110 * 110 := sq_le_of_le hkle
    have h12100 : k * k ≤ 12100 := by rw [← h110]; exact hsq_le
    omega
  · have hkge : 111 ≤ k := by omega
    have hsq_ge : 111 * 111 ≤ k * k := sq_le_of_le hkge
    have h12321 : 12321 ≤ k * k := by rw [← h111]; exact hsq_ge
    omega

/-- The Golomb (1970) counterexample, packaged as a single statement. -/
theorem jsp_000301_counterexample :
    Powerful 12167 ∧ Powerful 12168 ∧
    ¬ IsSquare 12167 ∧ ¬ IsSquare 12168 ∧
    12168 = 12167 + 1 := by
  exact ⟨powerful_12167, powerful_12168, not_square_12167, not_square_12168, by decide⟩

/-- The original problem, refuted: it is **not** the case that two consecutive
powerful positive integers must include a perfect square. -/
theorem jsp_000301 :
    ¬ (∀ n : Nat, 0 < n → Powerful n → Powerful (n + 1) →
        IsSquare n ∨ IsSquare (n + 1)) := by
  intro h
  have h2 : Powerful 12168 := powerful_12168
  have hc : (12168 : Nat) = 12167 + 1 := by decide
  rw [hc] at h2
  have hres := h 12167 (by decide) powerful_12167 h2
  rcases hres with hs | hs
  · exact not_square_12167 hs
  · rw [← hc] at hs
    exact not_square_12168 hs

#print axioms jsp_000301
#print axioms jsp_000301_counterexample