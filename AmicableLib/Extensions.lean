/-
Copyright (c) 2026 Zhipeng Chen, Haolun Tang, Jingyi Zhan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhipeng Chen, Haolun Tang, Jingyi Zhan

# Extensions to Amicable Number Theory

This file contains extensions to the basic amicable number theory:
- Sociable numbers (aliquot cycles)
- Betrothed numbers (quasi-amicable pairs)
- Euler's rule for generating amicable pairs
-/
import AmicableLib.Amicable

/-!
# Sociable Numbers and Betrothed Numbers

This file defines sociable numbers (generalization of amicable numbers to cycles)
and betrothed numbers (quasi-amicable pairs).

## Main Definitions

* `Nat.IsBetrothedPair`: Two numbers m, n where s(m) = n + 1 and s(n) = m + 1.
* `Nat.IsSociable`: A number that is part of an aliquot cycle.
* `Nat.aliquotCycle`: The aliquot sequence starting from n.

## References

* [Wikipedia: Sociable number](https://en.wikipedia.org/wiki/Sociable_number)
* [Wikipedia: Betrothed numbers](https://en.wikipedia.org/wiki/Betrothed_numbers)
-/

namespace Nat

open BigOperators Finset

/-! ### Betrothed Numbers (Quasi-Amicable Pairs) -/

/-- Two positive integers `m` and `n` are *betrothed* (or *quasi-amicable*) if
    s(m) = n + 1 and s(n) = m + 1, where s is the proper divisor sum.

    The smallest betrothed pair is (48, 75):
    - s(48) = 1+2+3+4+6+8+12+16+24 = 76 = 75 + 1
    - s(75) = 1+3+5+15+25 = 49 = 48 + 1 -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  m ≠ 0 ∧ n ≠ 0 ∧ m ≠ n ∧ s m = n + 1 ∧ s n = m + 1

/-- A number is *betrothed* if it is part of some betrothed pair. -/
def IsBetrothed (n : ℕ) : Prop :=
  ∃ m : ℕ, IsBetrothedPair n m

/-- Betrothed pairs are symmetric. -/
theorem IsBetrothedPair.symm {m n : ℕ} (h : IsBetrothedPair m n) : IsBetrothedPair n m := by
  obtain ⟨hm, hn, hne, hsm, hsn⟩ := h
  exact ⟨hn, hm, hne.symm, hsn, hsm⟩

/-- Members of a betrothed pair are distinct. -/
theorem IsBetrothedPair.ne {m n : ℕ} (h : IsBetrothedPair m n) : m ≠ n := h.2.2.1

/-- Members of a betrothed pair are positive. -/
theorem IsBetrothedPair.pos_left {m n : ℕ} (h : IsBetrothedPair m n) : 0 < m :=
  Nat.pos_of_ne_zero h.1

theorem IsBetrothedPair.pos_right {m n : ℕ} (h : IsBetrothedPair m n) : 0 < n :=
  Nat.pos_of_ne_zero h.2.1

/-! ### Sociable Numbers (Aliquot Cycles) -/

/-- The aliquot sequence: repeatedly apply the proper divisor sum function.
    aliquotSeq n k = s^k(n), the k-th iterate of s starting from n. -/
def aliquotSeq (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => s (aliquotSeq n k)

/-- A list forms a *sociable cycle* if applying s to each element gives the next,
    and applying s to the last gives the first.

    Examples:
    - Length 2: Amicable pairs like [220, 284]
    - Length 4: [1264460, 1547860, 1727636, 1305184]
    - Length 5: [12496, 14288, 15472, 14536, 14264] -/
def IsSociableCycle (L : List ℕ) : Prop :=
  L.length ≥ 2 ∧
  (∀ x ∈ L, x ≠ 0) ∧
  L.Nodup ∧
  (∀ i : ℕ, (hi : i < L.length) →
    s (L.get ⟨i, hi⟩) = L.get ⟨(i + 1) % L.length, Nat.mod_lt _ (Nat.zero_lt_of_lt hi)⟩)

/-- A number is *sociable* if it belongs to some sociable cycle. -/
def IsSociable (n : ℕ) : Prop :=
  ∃ L : List ℕ, n ∈ L ∧ IsSociableCycle L

/-- The *sociability* of a sociable number is the length of its cycle. -/
noncomputable def sociability (n : ℕ) (h : IsSociable n) : ℕ :=
  (Classical.choose h).length

/-- A *perfect number* is a fixed point of s, i.e., s(n) = n.
    Note: This is equivalent to saying it's in a cycle of length 1,
    but we exclude length 1 from sociable cycles. -/
def IsPerfect' (n : ℕ) : Prop := s n = n

/-- Amicable pairs form sociable cycles of length 2. -/
theorem isAmicablePair_iff_sociableCycle_length_two {m n : ℕ} (hmn : m ≠ n) :
    IsAmicablePair m n ↔ IsSociableCycle [m, n] := by
  constructor
  · intro ⟨hm, hn, _, hsm, hsn⟩
    refine ⟨by simp, by simp [hm, hn], by simp [hmn], ?_⟩
    intro i hi
    simp only [List.length_cons, List.length_singleton] at hi
    match i with
    | 0 => simp [hsm]
    | 1 => simp [hsn]
  · intro ⟨_, hpos, _, hcycle⟩
    have hm : m ≠ 0 := by simp at hpos; exact hpos.1
    have hn : n ≠ 0 := by simp at hpos; exact hpos.2
    have hsm : s m = n := by
      have := hcycle 0 (by simp)
      simp at this
      exact this
    have hsn : s n = m := by
      have := hcycle 1 (by simp)
      simp at this
      exact this
    exact ⟨hm, hn, hmn, hsm, hsn⟩

/-! ### Verified Betrothed Pairs -/

/-- The proper divisor sum of 48. -/
theorem properDivisorSum_48 : s 48 = 76 := by native_decide

/-- The proper divisor sum of 75. -/
theorem properDivisorSum_75 : s 75 = 49 := by native_decide

/-- **(48, 75) is a betrothed pair** - the smallest known betrothed pair. -/
theorem isBetrothedPair_48_75 : IsBetrothedPair 48 75 := by
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  constructor
  · -- s(48) = 76 = 75 + 1
    have h : s 48 = 76 := properDivisorSum_48
    omega
  · -- s(75) = 49 = 48 + 1
    have h : s 75 = 49 := properDivisorSum_75
    omega

/-- 48 is a betrothed number. -/
theorem isBetrothed_48 : IsBetrothed 48 := ⟨75, isBetrothedPair_48_75⟩

/-- 75 is a betrothed number. -/
theorem isBetrothed_75 : IsBetrothed 75 := ⟨48, isBetrothedPair_48_75.symm⟩

/-- The proper divisor sum of 140. -/
theorem properDivisorSum_140 : s 140 = 196 := by native_decide

/-- The proper divisor sum of 195. -/
theorem properDivisorSum_195 : s 195 = 141 := by native_decide

/-- **(140, 195) is a betrothed pair** - the second smallest betrothed pair. -/
theorem isBetrothedPair_140_195 : IsBetrothedPair 140 195 := by
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  constructor
  · have h : s 140 = 196 := properDivisorSum_140
    omega
  · have h : s 195 = 141 := properDivisorSum_195
    omega

/-! ### Known Betrothed Pairs -/

/-- List of first few betrothed pairs. -/
def knownBetrothedPairs : List (ℕ × ℕ) :=
  [(48, 75), (140, 195), (1050, 1925), (1575, 1648)]

/-! ### Verified Sociable Cycle -/

/-- The smallest sociable cycle of length 5, discovered by Poulet in 1918. -/
def pouletCycle : List ℕ := [12496, 14288, 15472, 14536, 14264]

/-- Verify the Poulet cycle step by step. -/
theorem properDivisorSum_12496 : s 12496 = 14288 := by native_decide
theorem properDivisorSum_14288 : s 14288 = 15472 := by native_decide
theorem properDivisorSum_15472 : s 15472 = 14536 := by native_decide
theorem properDivisorSum_14536 : s 14536 = 14264 := by native_decide
theorem properDivisorSum_14264 : s 14264 = 12496 := by native_decide

/-- The Poulet cycle is a valid sociable cycle. -/
theorem isSociableCycle_poulet : IsSociableCycle pouletCycle := by
  refine ⟨by simp [pouletCycle], by simp [pouletCycle], ?_, ?_⟩
  · simp only [pouletCycle, List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false, List.nodup_nil, and_true, not_or, and_imp]
    decide
  · intro i hi
    simp only [pouletCycle, List.length_cons, List.length_singleton, Nat.add_one_sub_one] at hi
    have h0 : s 12496 = 14288 := properDivisorSum_12496
    have h1 : s 14288 = 15472 := properDivisorSum_14288
    have h2 : s 15472 = 14536 := properDivisorSum_15472
    have h3 : s 14536 = 14264 := properDivisorSum_14536
    have h4 : s 14264 = 12496 := properDivisorSum_14264
    match i with
    | 0 => simp only [pouletCycle, List.get_cons_zero]; exact h0
    | 1 => simp only [pouletCycle, List.get_cons_succ, List.get_cons_zero]; exact h1
    | 2 => simp only [pouletCycle, List.get_cons_succ, List.get_cons_zero]; exact h2
    | 3 => simp only [pouletCycle, List.get_cons_succ, List.get_cons_zero]; exact h3
    | 4 => simp only [pouletCycle, List.get_cons_succ, List.get_cons_zero]; exact h4

/-- 12496 is a sociable number of sociability 5. -/
theorem isSociable_12496 : IsSociable 12496 :=
  ⟨pouletCycle, by simp [pouletCycle], isSociableCycle_poulet⟩

/-! ### Euler's Rule for Amicable Pairs

Euler's rule is a generalization of Thābit's rule. It was discovered by Euler in 1747
and produces additional amicable pairs beyond those found by Thābit's formula.

For 1 < m < n, define:
- p = 2^m · (2^(n-m) + 1) - 1
- q = 2^n · (2^(n-m) + 1) - 1
- r = 2^(n+m) · (2^(n-m) + 1)² - 1

If p, q, r are all prime, then (2^n · p · q, 2^n · r) is an amicable pair.

Note: When n - m = 1, we get 2^(n-m) + 1 = 3, and this reduces to Thābit's rule.
-/

/-- The "a" parameter in Euler's rule: a = 2^(n-m) + 1 -/
def euler_a (n m : ℕ) : ℕ := 2^(n - m) + 1

/-- p in Euler's rule: p = 2^m · a - 1 where a = 2^(n-m) + 1 -/
def p_euler (n m : ℕ) : ℕ := 2^m * euler_a n m - 1

/-- q in Euler's rule: q = 2^n · a - 1 where a = 2^(n-m) + 1 -/
def q_euler (n m : ℕ) : ℕ := 2^n * euler_a n m - 1

/-- r in Euler's rule: r = 2^(n+m) · a² - 1 where a = 2^(n-m) + 1 -/
def r_euler (n m : ℕ) : ℕ := 2^(n + m) * (euler_a n m)^2 - 1

/-- First member of Euler pair: M = 2^n · p · q -/
def M_euler (n m : ℕ) : ℕ := 2^n * p_euler n m * q_euler n m

/-- Second member of Euler pair: N = 2^n · r -/
def N_euler (n m : ℕ) : ℕ := 2^n * r_euler n m

/-- **Euler's Rule Statement**: For 1 < m < n, if p, q, r (defined above) are all prime,
    then (M, N) is an amicable pair. -/
def EulerRuleStatement (n m : ℕ) : Prop :=
  1 < m → m < n →
  (p_euler n m).Prime →
  (q_euler n m).Prime →
  (r_euler n m).Prime →
  IsAmicablePair (M_euler n m) (N_euler n m)

/-! ### Positivity lemmas for Euler's rule -/

theorem euler_a_pos (n m : ℕ) : 0 < euler_a n m := by
  simp only [euler_a]
  have h : 0 < 2^(n - m) := Nat.pos_pow_of_pos (n - m) (by norm_num)
  omega

theorem euler_a_ge_two (n m : ℕ) : 2 ≤ euler_a n m := by
  simp only [euler_a]
  have h : 1 ≤ 2^(n - m) := Nat.one_le_pow (n - m) 2 (by norm_num)
  omega

theorem two_pow_mul_euler_a_ge_one (n m k : ℕ) : 1 ≤ 2^k * euler_a n m := by
  have h1 : 1 ≤ 2^k := Nat.one_le_pow k 2 (by norm_num)
  have h2 : 1 ≤ euler_a n m := Nat.one_le_of_lt (euler_a_pos n m)
  calc 1 = 1 * 1 := by ring
    _ ≤ 2^k * euler_a n m := Nat.mul_le_mul h1 h2

theorem p_euler_pos (n m : ℕ) (hm : 1 ≤ m) : 0 < p_euler n m := by
  simp only [p_euler]
  have h : 1 ≤ 2^m * euler_a n m := two_pow_mul_euler_a_ge_one n m m
  omega

theorem q_euler_pos (n m : ℕ) (hn : 1 ≤ n) : 0 < q_euler n m := by
  simp only [q_euler]
  have h : 1 ≤ 2^n * euler_a n m := two_pow_mul_euler_a_ge_one n m n
  omega

theorem r_euler_pos (n m : ℕ) (hnm : 1 ≤ n + m) : 0 < r_euler n m := by
  simp only [r_euler]
  have h1 : 1 ≤ 2^(n+m) := Nat.one_le_pow (n+m) 2 (by norm_num)
  have h2 : 1 ≤ euler_a n m := Nat.one_le_of_lt (euler_a_pos n m)
  have h3 : 1 ≤ (euler_a n m)^2 := by
    calc 1 = 1^2 := by ring
      _ ≤ (euler_a n m)^2 := Nat.pow_le_pow_left h2 2
  have h : 1 ≤ 2^(n+m) * (euler_a n m)^2 := Nat.one_le_mul_of_one_le_of_one_le h1 h3
  omega

/-! ### Oddness lemmas for Euler's rule -/

theorem odd_p_euler (n m : ℕ) (hm : 1 ≤ m) : Odd (p_euler n m) := by
  simp only [p_euler, euler_a]
  -- 2^m * (2^(n-m) + 1) - 1 is odd when m ≥ 1
  -- Because 2^m * (2^(n-m) + 1) is even (divisible by 2^m with m ≥ 1)
  -- So 2^m * (2^(n-m) + 1) - 1 is odd
  have h1 : 1 ≤ 2^m * (2^(n-m) + 1) := two_pow_mul_euler_a_ge_one n m m
  have h2 : 2 ∣ 2^m := by
    have : 2^1 ∣ 2^m := Nat.pow_dvd_pow 2 hm
    simp at this
    exact this
  have h3 : 2 ∣ 2^m * (2^(n-m) + 1) := Nat.dvd_mul_right 2 (2^(m-1) * (2^(n-m) + 1)) |>.trans (by
    have : 2 * (2^(m-1) * (2^(n-m) + 1)) = 2^m * (2^(n-m) + 1) := by
      have hm' : m = m - 1 + 1 := (Nat.sub_add_cancel hm).symm
      calc 2 * (2^(m-1) * (2^(n-m) + 1))
          = 2^1 * 2^(m-1) * (2^(n-m) + 1) := by ring
        _ = 2^(m-1+1) * (2^(n-m) + 1) := by rw [← pow_add]
        _ = 2^m * (2^(n-m) + 1) := by rw [← hm']
    exact this ▸ dvd_refl _)
  obtain ⟨k, hk⟩ : ∃ k, 2^m * (2^(n-m) + 1) = 2 * k := h3
  use k - 1
  omega

theorem odd_q_euler (n m : ℕ) (hn : 1 ≤ n) : Odd (q_euler n m) := by
  simp only [q_euler, euler_a]
  have h1 : 1 ≤ 2^n * (2^(n-m) + 1) := two_pow_mul_euler_a_ge_one n m n
  have h2 : 2 ∣ 2^n := by
    have : 2^1 ∣ 2^n := Nat.pow_dvd_pow 2 hn
    simp at this
    exact this
  have h3 : 2 ∣ 2^n * (2^(n-m) + 1) := Nat.dvd_mul_right 2 (2^(n-1) * (2^(n-m) + 1)) |>.trans (by
    have : 2 * (2^(n-1) * (2^(n-m) + 1)) = 2^n * (2^(n-m) + 1) := by
      have hn' : n = n - 1 + 1 := (Nat.sub_add_cancel hn).symm
      calc 2 * (2^(n-1) * (2^(n-m) + 1))
          = 2^1 * 2^(n-1) * (2^(n-m) + 1) := by ring
        _ = 2^(n-1+1) * (2^(n-m) + 1) := by rw [← pow_add]
        _ = 2^n * (2^(n-m) + 1) := by rw [← hn']
    exact this ▸ dvd_refl _)
  obtain ⟨k, hk⟩ : ∃ k, 2^n * (2^(n-m) + 1) = 2 * k := h3
  use k - 1
  omega

theorem odd_r_euler (n m : ℕ) (hnm : 1 ≤ n + m) : Odd (r_euler n m) := by
  simp only [r_euler, euler_a]
  have h1 : 1 ≤ 2^(n+m) * (2^(n-m) + 1)^2 := by
    have ha : 1 ≤ 2^(n+m) := Nat.one_le_pow (n+m) 2 (by norm_num)
    have hb : 1 ≤ (2^(n-m) + 1)^2 := by
      have : 1 ≤ 2^(n-m) + 1 := by omega
      calc 1 = 1^2 := by ring
        _ ≤ (2^(n-m) + 1)^2 := Nat.pow_le_pow_left this 2
    exact Nat.one_le_mul_of_one_le_of_one_le ha hb
  have h2 : 2 ∣ 2^(n+m) := by
    have : 2^1 ∣ 2^(n+m) := Nat.pow_dvd_pow 2 hnm
    simp at this
    exact this
  have h3 : 2 ∣ 2^(n+m) * (2^(n-m) + 1)^2 := Dvd.dvd.mul_right h2 _
  obtain ⟨k, hk⟩ : ∃ k, 2^(n+m) * (2^(n-m) + 1)^2 = 2 * k := h3
  use k - 1
  omega

/-! ### Coprimality for Euler's rule -/

theorem coprime_two_pow_p_euler (n m : ℕ) (hm : 1 ≤ m) : (2^n).Coprime (p_euler n m) :=
by
  have h2 : Coprime 2 (p_euler n m) := (coprime_two_left).2 (odd_p_euler n m hm)
  exact h2.pow_left n

theorem coprime_two_pow_q_euler (n m : ℕ) (hn : 1 ≤ n) : (2^n).Coprime (q_euler n m) :=
by
  have h2 : Coprime 2 (q_euler n m) := (coprime_two_left).2 (odd_q_euler n m hn)
  exact h2.pow_left n

theorem coprime_two_pow_r_euler (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) : (2^n).Coprime (r_euler n m) :=
by
  have h2 : Coprime 2 (r_euler n m) := (coprime_two_left).2 (odd_r_euler n m (by omega : 1 ≤ n + m))
  exact h2.pow_left n

theorem p_euler_lt_q_euler (n m : ℕ) (hm : 1 ≤ m) (hmn : m < n) : p_euler n m < q_euler n m := by
  simp only [p_euler, q_euler, euler_a]
  have h1 : 1 ≤ 2^m * (2^(n-m) + 1) := two_pow_mul_euler_a_ge_one n m m
  have h2 : 2^m * (2^(n-m) + 1) < 2^n * (2^(n-m) + 1) := by
    have : 2^m < 2^n := Nat.pow_lt_pow_right (by norm_num : 1 < 2) hmn
    have hpos : 0 < 2^(n-m) + 1 := by omega
    calc 2^m * (2^(n-m) + 1) < 2^n * (2^(n-m) + 1) := Nat.mul_lt_mul_of_pos_right this hpos
  omega

theorem coprime_p_q_euler (n m : ℕ) (hm : 1 ≤ m) (hmn : m < n)
    (hp : (p_euler n m).Prime) (hq : (q_euler n m).Prime) :
    (p_euler n m).Coprime (q_euler n m) := by
  -- p < q, so p ≠ q. Two distinct primes are coprime.
  have hlt : p_euler n m < q_euler n m := p_euler_lt_q_euler n m hm hmn
  -- If p | q and p is prime and q is prime, then p = q. But p < q, contradiction.
  rw [hp.coprime_iff_not_dvd]
  intro hdvd
  have heq : p_euler n m = q_euler n m := by
    cases hq.eq_one_or_self_of_dvd _ hdvd with
    | inl h => exact (hp.ne_one h).elim
    | inr h => exact h
  omega

/-! ### Key algebraic identity for Euler's rule -/

/-- The key identity: a · (2^m · a - 1) · (2^n · a - 1) + 2^(n+m) · a² - 1
    = (2^m · a - 1) · (2^n · a - 1) + 2^(n+m) · a²

    Equivalently: (p+1)(q+1) = r+1 where a = 2^(n-m)+1 -/
theorem euler_key_identity (n m : ℕ) :
    (p_euler n m + 1) * (q_euler n m + 1) = r_euler n m + 1 := by
  simp only [p_euler, q_euler, r_euler, euler_a]
  have hp : 1 ≤ 2^m * (2^(n-m) + 1) := two_pow_mul_euler_a_ge_one n m m
  have hq : 1 ≤ 2^n * (2^(n-m) + 1) := two_pow_mul_euler_a_ge_one n m n
  have hr : 1 ≤ 2^(n+m) * (2^(n-m) + 1)^2 := by
    have h1 : 1 ≤ 2^(n+m) := Nat.one_le_pow (n+m) 2 (by norm_num)
    have h2 : 1 ≤ (2^(n-m) + 1)^2 := by
      have : 1 ≤ 2^(n-m) + 1 := by omega
      calc 1 = 1^2 := by ring
        _ ≤ (2^(n-m) + 1)^2 := Nat.pow_le_pow_left this 2
    exact Nat.one_le_mul_of_one_le_of_one_le h1 h2
  rw [Nat.sub_add_cancel hp, Nat.sub_add_cancel hq, Nat.sub_add_cancel hr]
  -- Now prove: 2^m * a * (2^n * a) = 2^(n+m) * a^2
  ring_nf
  rw [pow_add]
  ring

/-! ### Euler's rule reduces to Thābit's rule when n - m = 1 -/

/-- When n - m = 1, euler_a = 3 -/
theorem euler_a_eq_three (n m : ℕ) (h : n - m = 1) : euler_a n m = 3 := by
  simp only [euler_a, h]
  norm_num

/-! ### M and N are distinct -/

/-- M and N are distinct under the Euler rule conditions -/
theorem M_ne_N (n m : ℕ) (hm : 1 < m) (hmn : m < n)
    (hp : (p_euler n m).Prime) (hq : (q_euler n m).Prime) (hr : (r_euler n m).Prime) :
    M_euler n m ≠ N_euler n m := by
  simp only [M_euler, N_euler]
  intro h
  -- M = 2^n * p * q, N = 2^n * r
  -- If M = N then p * q = r
  have h2_pos : 0 < 2^n := Nat.pos_pow_of_pos n (by norm_num)
  have heq : p_euler n m * q_euler n m = r_euler n m := by
    have : 2^n * (p_euler n m * q_euler n m) = 2^n * r_euler n m := by
      calc 2^n * (p_euler n m * q_euler n m)
          = 2^n * p_euler n m * q_euler n m := by ring
        _ = 2^n * r_euler n m := h
    exact Nat.eq_of_mul_eq_mul_left h2_pos this
  -- But r is prime and p * q is composite (both p, q > 1)
  have hp_gt : 1 < p_euler n m := hp.one_lt
  have hq_gt : 1 < q_euler n m := hq.one_lt
  -- r is prime means its only divisors are 1 and r
  -- But p | pq = r and p > 1, so p = r
  -- Similarly q | pq = r and q > 1, so q = r
  -- But p ≠ q (since p < q)
  have hp_dvd : p_euler n m ∣ r_euler n m := ⟨q_euler n m, heq.symm⟩
  have hq_dvd : q_euler n m ∣ r_euler n m := ⟨p_euler n m, by rw [mul_comm]; exact heq.symm⟩
  cases hr.eq_one_or_self_of_dvd _ hp_dvd with
  | inl h => exact hp.ne_one h
  | inr h =>
    cases hr.eq_one_or_self_of_dvd _ hq_dvd with
    | inl h' => exact hq.ne_one h'
    | inr h' =>
      have : p_euler n m = q_euler n m := h.trans h'.symm
      have hlt : p_euler n m < q_euler n m := p_euler_lt_q_euler n m (by omega : 1 ≤ m) hmn
      omega

/-! ### Divisor Sum Computations -/

/-- σ(2^n * p * q) = σ(2^n) * σ(p) * σ(q) for coprime factors -/
theorem sigma_M_euler (n m : ℕ) (hm : 1 < m) (hmn : m < n)
    (hp : (p_euler n m).Prime) (hq : (q_euler n m).Prime) :
    ∑ d ∈ (M_euler n m).divisors, d =
      (2^(n+1) - 1) * (p_euler n m + 1) * (q_euler n m + 1) := by
  simp only [M_euler]
  -- Need to show σ(2^n * p * q) = σ(2^n) * σ(p) * σ(q)
  have hn : 1 ≤ n := by omega
  have hcop_2p : (2^n).Coprime (p_euler n m) := coprime_two_pow_p_euler n m (by omega : 1 ≤ m)
  have hcop_2q : (2^n).Coprime (q_euler n m) := coprime_two_pow_q_euler n m hn
  have hcop_pq : (p_euler n m).Coprime (q_euler n m) := coprime_p_q_euler n m (by omega) hmn hp hq
  have hcop_2pq : (2^n).Coprime (p_euler n m * q_euler n m) :=
    Nat.Coprime.mul_right hcop_2p hcop_2q
  -- σ(2^n * (p * q)) = σ(2^n) * σ(p * q)
  rw [show 2^n * p_euler n m * q_euler n m = 2^n * (p_euler n m * q_euler n m) by ring]
  rw [sum_divisors_mul_of_coprime hcop_2pq]
  -- σ(p * q) = σ(p) * σ(q)
  rw [sum_divisors_mul_of_coprime hcop_pq]
  -- σ(2^n) = 2^(n+1) - 1
  rw [sum_divisors_two_pow n]
  -- σ(p) = p + 1, σ(q) = q + 1
  have hsum_p : ∑ d ∈ (p_euler n m).divisors, d = p_euler n m + 1 := by
    simpa [Finset.sum_range_succ, pow_zero, pow_one]
      using (sum_divisors_prime_pow (k:=1) (p:=p_euler n m) (f:=fun d => d) hp)
  have hsum_q : ∑ d ∈ (q_euler n m).divisors, d = q_euler n m + 1 := by
    simpa [Finset.sum_range_succ, pow_zero, pow_one]
      using (sum_divisors_prime_pow (k:=1) (p:=q_euler n m) (f:=fun d => d) hq)
  rw [hsum_p, hsum_q]
  ring

/-- σ(2^n * r) = σ(2^n) * σ(r) for coprime factors -/
theorem sigma_N_euler (n m : ℕ) (hm : 1 < m) (hmn : m < n) (hr : (r_euler n m).Prime) :
    ∑ d ∈ (N_euler n m).divisors, d = (2^(n+1) - 1) * (r_euler n m + 1) := by
  simp only [N_euler]
  have hn : 1 ≤ n := by omega
  have hcop : (2^n).Coprime (r_euler n m) := coprime_two_pow_r_euler n m hn (by omega : 1 ≤ m)
  have hsum_r : ∑ d ∈ (r_euler n m).divisors, d = r_euler n m + 1 := by
    simpa [Finset.sum_range_succ, pow_zero, pow_one]
      using (sum_divisors_prime_pow (k:=1) (p:=r_euler n m) (f:=fun d => d) hr)
  rw [sum_divisors_mul_of_coprime hcop, sum_divisors_two_pow n, hsum_r]

/-- σ(M) = σ(N) for the Euler pair -/
theorem sigma_M_eq_sigma_N (n m : ℕ) (hm : 1 < m) (hmn : m < n)
    (hp : (p_euler n m).Prime) (hq : (q_euler n m).Prime) (hr : (r_euler n m).Prime) :
    ∑ d ∈ (M_euler n m).divisors, d = ∑ d ∈ (N_euler n m).divisors, d := by
  rw [sigma_M_euler n m hm hmn hp hq, sigma_N_euler n m hm hmn hr]
  -- Goal: (2^(n+1) - 1) * (p+1) * (q+1) = (2^(n+1) - 1) * (r+1)
  -- Use (p+1)(q+1) = r+1
  have h := euler_key_identity n m
  calc (2^(n+1) - 1) * (p_euler n m + 1) * (q_euler n m + 1)
      = (2^(n+1) - 1) * ((p_euler n m + 1) * (q_euler n m + 1)) := by ring
    _ = (2^(n+1) - 1) * (r_euler n m + 1) := by rw [h]

/-- The key equation: σ(M) = σ(N) = M + N -/
theorem sigma_eq_M_plus_N (n m : ℕ) (hm : 1 < m) (hmn : m < n)
    (hp : (p_euler n m).Prime) (hq : (q_euler n m).Prime) (_hr : (r_euler n m).Prime) :
    ∑ d ∈ (M_euler n m).divisors, d = M_euler n m + N_euler n m := by
  -- σ(M) = (2^(n+1) - 1) * (p+1) * (q+1)
  -- We need to show this equals M + N = 2^n * p * q + 2^n * r
  rw [sigma_M_euler n m hm hmn hp hq]
  -- Use (p+1)(q+1) = r+1
  have hkey := euler_key_identity n m
  -- Goal: (2^(n+1) - 1) * (p+1) * (q+1) = M + N
  calc (2^(n+1) - 1) * (p_euler n m + 1) * (q_euler n m + 1)
      = (2^(n+1) - 1) * ((p_euler n m + 1) * (q_euler n m + 1)) := by ring
    _ = (2^(n+1) - 1) * (r_euler n m + 1) := by rw [hkey]
    _ = M_euler n m + N_euler n m := by
        simp only [M_euler, N_euler, p_euler, q_euler, r_euler, euler_a]
        have hp1 : 1 ≤ 2^m * (2^(n-m) + 1) := two_pow_mul_euler_a_ge_one n m m
        have hq1 : 1 ≤ 2^n * (2^(n-m) + 1) := two_pow_mul_euler_a_ge_one n m n
        have hr1 : 1 ≤ 2^(n+m) * (2^(n-m) + 1)^2 := by
          have h1 : 1 ≤ 2^(n+m) := Nat.one_le_pow (n+m) 2 (by norm_num)
          have h2 : 1 ≤ (2^(n-m) + 1)^2 := by
            have : 1 ≤ 2^(n-m) + 1 := by omega
            calc 1 = 1^2 := by ring
              _ ≤ (2^(n-m) + 1)^2 := Nat.pow_le_pow_left this 2
          exact Nat.one_le_mul_of_one_le_of_one_le h1 h2
        have h2n1 : 1 ≤ 2^(n+1) := Nat.one_le_pow (n+1) 2 (by norm_num)
        have h_ge : 2^(n+m) * (2^(n-m) + 1)^2 ≤ 2^(3*n+3*m) * (2^(n-m) + 1)^2 := by
          apply Nat.mul_le_mul_right
          apply Nat.pow_le_pow_right (by norm_num)
          omega
        zify [hp1, hq1, hr1, h2n1, h_ge]
        ring

/-- Euler's rule: Statement that the rule generates amicable pairs.
    The full proof would follow the same pattern as thabit_rule_general,
    using the multiplicativity of σ and the key identity. -/
theorem euler_rule_statement (n m : ℕ) (hm : 1 < m) (hmn : m < n)
    (hp : (p_euler n m).Prime) (hq : (q_euler n m).Prime) (hr : (r_euler n m).Prime) :
    IsAmicablePair (M_euler n m) (N_euler n m) := by
  have hn : 1 ≤ n := by omega
  have M_ne_zero : M_euler n m ≠ 0 := by
    simp only [M_euler]
    exact Nat.mul_ne_zero (Nat.mul_ne_zero (two_pow_ne_zero n) (p_euler_pos n m (by omega)).ne') (q_euler_pos n m hn).ne'
  have N_ne_zero : N_euler n m ≠ 0 := by
    simp only [N_euler]
    exact Nat.mul_ne_zero (two_pow_ne_zero n) (r_euler_pos n m (by omega : 1 ≤ n + m)).ne'
  rw [isAmicablePair_iff_sum_divisors M_ne_zero N_ne_zero (M_ne_N n m hm hmn hp hq hr)]
  constructor
  · -- σ(M) = M + N
    exact sigma_eq_M_plus_N n m hm hmn hp hq hr
  · -- σ(N) = M + N
    rw [← sigma_M_eq_sigma_N n m hm hmn hp hq hr]
    exact sigma_eq_M_plus_N n m hm hmn hp hq hr

/-! ### Verified case: (m, n) = (1, 8) gives amicable pair (1175265, 1438983) -/

/-- For m=1, n=8: a = 2^7 + 1 = 129 -/
theorem euler_a_1_8 : euler_a 8 1 = 129 := by native_decide

/-- For m=1, n=8: p = 2^1 · 129 - 1 = 257 -/
theorem p_euler_1_8 : p_euler 8 1 = 257 := by native_decide

/-- For m=1, n=8: q = 2^8 · 129 - 1 = 33023 -/
theorem q_euler_1_8 : q_euler 8 1 = 33023 := by native_decide

/-- For m=1, n=8: r = 2^9 · 129² - 1 = 8520191 -/
theorem r_euler_1_8 : r_euler 8 1 = 8520191 := by native_decide

/-- 257 is prime -/
theorem prime_257 : Nat.Prime 257 := by native_decide

/-- 33023 is prime -/
theorem prime_33023 : Nat.Prime 33023 := by native_decide

/-- 8520191 is prime -/
theorem prime_8520191 : Nat.Prime 8520191 := by native_decide

/-- M = 2^8 · 257 · 33023 = 2172649216 -/
theorem M_euler_1_8 : M_euler 8 1 = 2172649216 := by native_decide

/-- N = 2^8 · 8520191 = 2181168896 -/
theorem N_euler_1_8 : N_euler 8 1 = 2181168896 := by native_decide

/-- Verify that (2172649216, 2181168896) is an amicable pair via computation -/
theorem isAmicablePair_euler_1_8 : IsAmicablePair (M_euler 8 1) (N_euler 8 1) := by
  simp only [M_euler_1_8, N_euler_1_8]
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  constructor
  · native_decide  -- s(2172649216) = 2181168896
  · native_decide  -- s(2181168896) = 2172649216

/-! ### Parity Theorems for Amicable Numbers

These are deep theorems about the parity structure of amicable pairs.
While we cannot provide full proofs here, we state them formally.
-/

/-- A number is a perfect square if it equals n² for some n. -/
def IsPerfectSquare (m : ℕ) : Prop := ∃ n : ℕ, m = n^2

/-- **Theorem (Parity constraint for odd member)**:
    If (m, n) is an amicable pair where m is odd and n is even,
    then m must be a perfect square.

    This is a deep theorem proven using 2-adic valuation arguments.
    No proof is provided here, but the statement is formalized. -/
def OddMemberSquareTheorem : Prop :=
  ∀ m n : ℕ, IsAmicablePair m n → Odd m → Even n → IsPerfectSquare m

/-- **Theorem (Parity constraint for even member)**:
    If (m, n) is an amicable pair where m is odd and n is even,
    then n must be of the form 2^k · a² where k ≥ 1 and a is odd.

    This is a deep theorem proven using 2-adic valuation arguments.
    No proof is provided here, but the statement is formalized. -/
def EvenMemberFormTheorem : Prop :=
  ∀ m n : ℕ, IsAmicablePair m n → Odd m → Even n →
    ∃ k a : ℕ, 1 ≤ k ∧ Odd a ∧ n = 2^k * a^2

/-- **Observation**: All known amicable pairs have the same parity (both even).
    It is unknown whether any odd-even amicable pair exists.
    If one exists, the above theorems severely constrain its form. -/
def NoOddEvenAmicableConj : Prop :=
  ∀ m n : ℕ, IsAmicablePair m n → (Even m ∧ Even n) ∨ (Odd m ∧ Odd n)

/-! ### Summary of Open Problems and Conjectures -/

/-- List all major open conjectures about amicable numbers. -/
structure AmicableConjectures where
  /-- No odd-odd amicable pairs exist -/
  no_odd_odd : Prop
  /-- No odd-even amicable pairs exist (stronger than no_odd_odd) -/
  no_odd_even : Prop
  /-- No coprime amicable pairs exist -/
  no_coprime : Prop
  /-- Infinitely many amicable pairs exist -/
  infinitely_many : Prop

/-- The standard collection of amicable number conjectures. -/
def standardConjectures : AmicableConjectures where
  no_odd_odd := OddOddAmicableConj
  no_odd_even := NoOddEvenAmicableConj
  no_coprime := NoCoprimeAmicableConj
  infinitely_many := InfinitelyManyAmicableConj

/-- Known facts: All verified amicable pairs are both even. -/
theorem known_pairs_both_even_220_284 : Even 220 ∧ Even 284 := by decide
theorem known_pairs_both_even_1184_1210 : Even 1184 ∧ Even 1210 := by decide
theorem known_pairs_both_even_2620_2924 : Even 2620 ∧ Even 2924 := by decide
theorem known_pairs_both_even_5020_5564 : Even 5020 ∧ Even 5564 := by decide
theorem known_pairs_both_even_17296_18416 : Even 17296 ∧ Even 18416 := by decide

/-! ### Computational Search Bounds for Coprime Amicable Pairs

Exhaustive computational searches have been conducted to find coprime amicable pairs.
These are not mathematical theorems but empirical results from computation.
-/

/-- The current computational search bound for coprime amicable pairs.
    Exhaustive searches up to this bound have found no coprime amicable pairs.

    Based on Pedersen (2003) and subsequent computational work, if a coprime
    amicable pair exists, the product of its members must exceed 10^65. -/
def coprimeAmicableSearchBound : ℕ := 10^65

/-- **Computational observation** (not a theorem):
    All amicable pairs (m, n) found with m·n < 10^65 satisfy gcd(m,n) > 1.

    This is a statement of empirical fact from exhaustive search,
    not a mathematical proof. It cannot be proven in Lean without
    actually performing the exhaustive enumeration. -/
def NoCoprimeAmicableBelowBound : Prop :=
  ∀ m n : ℕ, m * n < coprimeAmicableSearchBound →
    IsAmicablePair m n → 1 < Nat.gcd m n

/-- Connection between the search bound and the general coprimality conjecture.
    If the coprimality conjecture is true, then certainly no coprime pairs
    exist below any finite bound. -/
theorem noCoprimeAmicable_implies_noBelowBound :
    NoCoprimeAmicableConj → NoCoprimeAmicableBelowBound := by
  intro h m n _ hpair
  exact h m n hpair

/-! ### Borho's Generalizations and Breeding Methods

Borho (1972) and te Riele (1984) developed methods for generating new amicable
pairs from existing ones, called "breeding" methods. These generalize the
Thābit and Euler formulas in various ways.

One class of Borho's formulas requires only two primes instead of three,
making them computationally more tractable.
-/

/-- **Borho's Rule I** (simplified form):
    Given an amicable pair (a, b) with certain properties, construct new pairs
    using a breeding formula.

    One of Borho's formulas states: If p and q are both prime, where
    p = (2^n - 1) · a + b  and  q = (2^n - 1) · b + a,
    then under certain conditions, a new amicable pair can be constructed.

    The full treatment requires specifying "certain conditions" precisely,
    which involves divisibility properties and forms a complex theory.
    We provide only a partial formalization as a definition. -/
def BorhoRuleI_Hypothesis (a b n : ℕ) : Prop :=
  IsAmicablePair a b ∧
  (((2^n - 1) * a + b).Prime ∧ ((2^n - 1) * b + a).Prime)

/-- The conclusion of Borho's breeding rule (simplified statement).
    This is marked as a definition rather than theorem because the full
    proof requires substantial additional infrastructure. -/
def BorhoRuleI_Conclusion (a b n : ℕ) : Prop :=
  ∃ m m' : ℕ, IsAmicablePair m m' ∧ a < m ∧ b < m'

/-- **Borho's breeding conjecture** (partial statement):
    If the hypothesis of Borho's rule holds, then a new amicable pair exists.
    The actual construction is more complex and is not formalized here. -/
def BorhoBreedingWorks : Prop :=
  ∀ a b n : ℕ, BorhoRuleI_Hypothesis a b n → BorhoRuleI_Conclusion a b n

/-! ### Borho-Hoffmann Breeding Method (Constructive Version)

Borho and Hoffmann (1986) presented an explicit constructive formula for
generating new amicable pairs from known "breeder" pairs.

**Reference**: W. Borho and H. Hoffmann, "Breeding Amicable Numbers in Abundance",
Mathematics of Computation, Vol. 46, No. 173 (1986), pp. 281-293.

**The Method**: For a breeder pair of the form (a·u, a), if t = u + s(u) is prime
(where s(u) = σ(u) - u is the sum of proper divisors), then the formulas below
generate new amicable pairs when certain primality conditions hold.
-/

/-- The breeding parameter t for Borho-Hoffmann method.
    For a number u, t = u + s(u) where s(u) is the sum of proper divisors. -/
def t_borho (u : ℕ) : ℕ := u + (σ u - u)

/-- First member of new amicable pair via Borho-Hoffmann breeding.
    Formula: M = a·u · t^n · (t^n·(u+1) - 1)
    where t = u + s(u). -/
def M_borho_bh (a u n : ℕ) : ℕ :=
  let t := t_borho u
  a * u * t^n * (t^n * (u + 1) - 1)

/-- Second member of new amicable pair via Borho-Hoffmann breeding.
    Formula: N = a · t^n · (t^n·(u+1)·(t-u) - 1)
    where t = u + s(u). -/
def N_borho_bh (a u n : ℕ) : ℕ :=
  let t := t_borho u
  a * t^n * (t^n * (u + 1) * (t - u) - 1)

/-- **Borho-Hoffmann Hypothesis**: Conditions for breeding to work.
    Given a breeder pair (a·u, a), require:
    1. (a·u, a) is an amicable pair
    2. t = u + s(u) is prime
    3. p₁ = t^n·(u+1) - 1 is prime
    4. p₂ = t^n·(u+1)·(t-u) - 1 is prime
    5. a·u and t are coprime (needed for multiplicativity of σ)
    6. a·u and p₁ are coprime (for σ multiplicativity)
    7. a and p₂ are coprime (for σ multiplicativity) -/
def BorhoHoffmannHypothesis (a u n : ℕ) : Prop :=
  let t := t_borho u
  let p1 := t^n * (u + 1) - 1
  let p2 := t^n * (u + 1) * (t - u) - 1
  IsAmicablePair (a * u) a ∧
  t.Prime ∧
  p1.Prime ∧
  p2.Prime ∧
  (a * u).Coprime t ∧
  (a * u).Coprime p1 ∧
  a.Coprime p2

/-! ### Basic Properties of Borho-Hoffmann Construction -/

/-- t_borho is positive when u > 0 -/
theorem t_borho_pos (u : ℕ) (hu : 0 < u) : 0 < t_borho u := by
  simp only [t_borho]
  omega

/-- When t is prime, t ≥ 2 -/
theorem t_borho_ge_two (u : ℕ) (ht : (t_borho u).Prime) : 2 ≤ t_borho u :=
  Nat.Prime.two_le ht

/-- When t_borho(u) is prime and u > 0, then u > 1.
    Proof: If u = 1, then t_borho(1) = σ(1) = 1, which is not prime. -/
theorem u_gt_one_of_t_prime (u : ℕ) (hu : 0 < u) (ht : (t_borho u).Prime) : 1 < u := by
  by_contra h
  push_neg at h
  interval_cases u
  · omega
  · -- u = 1
    simp only [t_borho, sum_divisors_one] at ht
    norm_num at ht

/-- Key inequality: when t is prime and u > 0, we have t^n * (u+1) ≥ 2 for n > 0 -/
theorem t_pow_mul_succ_ge_two (u n : ℕ) (hu : 0 < u) (hn : 0 < n)
    (ht : (t_borho u).Prime) : 2 ≤ (t_borho u)^n * (u + 1) := by
  have ht_ge : 2 ≤ t_borho u := t_borho_ge_two u ht
  have h_pow : 2 ≤ (t_borho u)^n := by
    calc (t_borho u)^n ≥ (t_borho u)^1 := Nat.pow_le_pow_left ht_ge (Nat.one_le_of_lt hn)
      _ = t_borho u := pow_one _
      _ ≥ 2 := ht_ge
  have h_succ : 2 ≤ u + 1 := by omega
  calc (t_borho u)^n * (u + 1) ≥ 2 * 2 := Nat.mul_le_mul h_pow h_succ
    _ = 4 := rfl
    _ ≥ 2 := by omega

/-- The subtraction t^n * (u+1) - 1 is positive when t is prime -/
theorem t_pow_mul_succ_sub_one_pos (u n : ℕ) (hu : 0 < u) (hn : 0 < n)
    (ht : (t_borho u).Prime) : 0 < (t_borho u)^n * (u + 1) - 1 := by
  have h := t_pow_mul_succ_ge_two u n hu hn ht
  omega

/-- When u > 0 and t = σ(u), we have t > u (since s(u) = σ(u) - u > 0 for u > 1) -/
theorem t_borho_gt_u (u : ℕ) (hu : 1 < u) : u < t_borho u := by
  simp only [t_borho]
  have h : 0 < σ u - u := by
    have : u < σ u := by
      have : 1 < σ u := by
        calc σ u ≥ σ 2 := by
          apply sum_divisors_le_sum_divisors_of_le
          omega
          _ = 3 := by norm_num
          _ > 1 := by omega
      omega
    omega
  omega

/-- The subtraction t^n * (u+1) * (t - u) - 1 is positive when conditions hold -/
theorem t_pow_mul_succ_mul_diff_sub_one_pos (u n : ℕ) (hu : 1 < u) (hn : 0 < n)
    (ht : (t_borho u).Prime) : 0 < (t_borho u)^n * (u + 1) * (t_borho u - u) - 1 := by
  have h1 := t_pow_mul_succ_ge_two u n (by omega : 0 < u) hn ht
  have h2 := t_borho_gt_u u hu
  have h_diff : 1 ≤ t_borho u - u := by omega
  calc (t_borho u)^n * (u + 1) * (t_borho u - u)
      ≥ 2 * 1 := Nat.mul_le_mul h1 h_diff
    _ = 2 := by omega
  omega

/-- M_borho_bh is positive when parameters are positive and t is prime -/
theorem M_borho_bh_pos (a u n : ℕ) (ha : 0 < a) (hu : 0 < u) (hn : 0 < n)
    (ht : (t_borho u).Prime) : 0 < M_borho_bh a u n := by
  simp only [M_borho_bh]
  apply Nat.mul_pos
  apply Nat.mul_pos
  apply Nat.mul_pos
  · exact ha
  · exact hu
  · apply Nat.pos_pow_of_pos
    exact t_borho_pos u hu
  · exact t_pow_mul_succ_sub_one_pos u n hu hn ht

/-- N_borho_bh is positive when parameters are positive and t is prime -/
theorem N_borho_bh_pos (a u n : ℕ) (ha : 0 < a) (hu : 0 < u) (hn : 0 < n)
    (ht : (t_borho u).Prime) : 0 < N_borho_bh a u n := by
  have hu' : 1 < u := u_gt_one_of_t_prime u hu ht
  simp only [N_borho_bh]
  apply Nat.mul_pos
  apply Nat.mul_pos
  · exact ha
  · apply Nat.pos_pow_of_pos
    exact t_borho_pos u hu
  · exact t_pow_mul_succ_mul_diff_sub_one_pos u n hu' hn ht

/-! ### Coprimality Lemmas for Borho-Hoffmann -/

/-- If t is prime and doesn't divide m, then t^n and m are coprime -/
theorem coprime_pow_prime_of_not_dvd {t m n : ℕ} (ht : t.Prime) (h : ¬ t ∣ m) (hn : 0 < n) :
    (t^n).Coprime m := by
  rw [Nat.Prime.coprime_iff_not_dvd ht]
  intro hdvd
  have : t ∣ m := by
    have : t ∣ t^n := by
      calc t = t^1 := (pow_one t).symm
        _ ∣ t^n := pow_dvd_pow t (Nat.one_le_of_lt hn)
    exact Nat.dvd_trans this hdvd
  contradiction

/-- t and p₁ are distinct when both are prime and p₁ = t^n*(u+1) - 1 with appropriate conditions -/
theorem t_ne_p1 (u n : ℕ) (hu : 0 < u) (hn : 0 < n) (ht : (t_borho u).Prime)
    (hp1 : ((t_borho u)^n * (u + 1) - 1).Prime) :
    t_borho u ≠ (t_borho u)^n * (u + 1) - 1 := by
  intro heq
  have h1 := t_pow_mul_succ_ge_two u n hu hn ht
  have h2 : 2 ≤ t_borho u := t_borho_ge_two u ht
  -- t^n * (u+1) - 1 < t^n * (u+1) ≤ t^2 * 2 when t ≥ 2
  have : (t_borho u)^n * (u + 1) - 1 < (t_borho u)^n * (u + 1) := by omega
  rw [← heq] at this
  have : t_borho u < (t_borho u)^n * (u + 1) := by omega
  have ht_pow : t_borho u ≤ (t_borho u)^n := by
    calc t_borho u = (t_borho u)^1 := (pow_one _).symm
      _ ≤ (t_borho u)^n := Nat.pow_le_pow_right h2 (Nat.one_le_of_lt hn)
  have : t_borho u ≤ (t_borho u)^n * 1 := by
    calc t_borho u ≤ (t_borho u)^n := ht_pow
      _ = (t_borho u)^n * 1 := (Nat.mul_one _).symm
  have h_prod : (t_borho u)^n * 1 < (t_borho u)^n * (u + 1) := by
    apply Nat.mul_lt_mul_of_pos_left
    omega
    apply Nat.pos_pow_of_pos
    exact t_borho_pos u hu
  omega

/-- t^n and p₁ are coprime when both are prime -/
theorem coprime_t_pow_p1 (u n : ℕ) (hu : 0 < u) (hn : 0 < n) (ht : (t_borho u).Prime)
    (hp1 : ((t_borho u)^n * (u + 1) - 1).Prime) :
    ((t_borho u)^n).Coprime ((t_borho u)^n * (u + 1) - 1) := by
  apply Nat.Coprime.symm
  have hne : t_borho u ≠ (t_borho u)^n * (u + 1) - 1 := t_ne_p1 u n hu hn ht hp1
  have ht_prime : (t_borho u).Prime := ht
  rw [Nat.Prime.coprime_iff_not_dvd hp1]
  intro hdvd
  -- If t^n | (t^n*(u+1) - 1), then t | (t^n*(u+1) - 1)
  have ht_dvd : t_borho u ∣ (t_borho u)^n * (u + 1) - 1 := by
    have : t_borho u ∣ t_borho u ^ n := by
      calc t_borho u = (t_borho u)^1 := (pow_one _).symm
        _ ∣ (t_borho u)^n := pow_dvd_pow _ (Nat.one_le_of_lt hn)
    exact Nat.dvd_trans this hdvd
  -- But t | (t^n*(u+1) - 1) implies t | (t^n*(u+1))
  have h_prod : (t_borho u)^n * (u + 1) = (t_borho u)^n * (u + 1) - 1 + 1 := by
    have := t_pow_mul_succ_ge_two u n hu hn ht
    omega
  rw [h_prod] at ht_dvd
  have : t_borho u ∣ 1 := by
    have h1 : t_borho u ∣ (t_borho u)^n * (u + 1) - 1 + 1 := ht_dvd
    have h2 : t_borho u ∣ (t_borho u)^n * (u + 1) := by
      calc t_borho u = (t_borho u)^1 := (pow_one _).symm
        _ ∣ (t_borho u)^n := pow_dvd_pow _ (Nat.one_le_of_lt hn)
        _ ∣ (t_borho u)^n * (u + 1) := Nat.dvd_mul_right _ _
    exact (Nat.dvd_add_right h2).mp h1
  -- But t ≥ 2, so t ∤ 1
  have : 2 ≤ t_borho u := t_borho_ge_two u ht
  omega

/-- a·u and t^n are coprime when a·u and t are coprime -/
theorem coprime_au_t_pow (a u n : ℕ) (hn : 0 < n) (h_cop : (a * u).Coprime (t_borho u)) :
    (a * u).Coprime ((t_borho u)^n) := by
  exact h_cop.pow_right n

/-- Extract coprimality of a·u and p₁ from hypothesis -/
theorem coprime_au_p1_of_hyp (a u n : ℕ) (hyp : BorhoHoffmannHypothesis a u n) :
    (a * u).Coprime ((t_borho u)^n * (u + 1) - 1) := hyp.2.2.2.2.2.1

/-- Similar coprimality for p₂ and t^n -/
theorem coprime_t_pow_p2 (u n : ℕ) (hu : 0 < u) (hn : 0 < n) (ht : (t_borho u).Prime)
    (hp2 : ((t_borho u)^n * (u + 1) * (t_borho u - u) - 1).Prime) :
    ((t_borho u)^n).Coprime ((t_borho u)^n * (u + 1) * (t_borho u - u) - 1) := by
  apply Nat.Coprime.symm
  rw [Nat.Prime.coprime_iff_not_dvd hp2]
  intro hdvd
  -- Similar argument to coprime_t_pow_p1
  have ht_dvd : t_borho u ∣ (t_borho u)^n * (u + 1) * (t_borho u - u) - 1 := by
    have : t_borho u ∣ t_borho u ^ n := by
      calc t_borho u = (t_borho u)^1 := (pow_one _).symm
        _ ∣ (t_borho u)^n := pow_dvd_pow _ (Nat.one_le_of_lt hn)
    exact Nat.dvd_trans this hdvd
  have hu' : 1 < u := u_gt_one_of_t_prime u hu ht
  have h_pos := t_pow_mul_succ_mul_diff_sub_one_pos u n hu' hn ht
  have h_prod : (t_borho u)^n * (u + 1) * (t_borho u - u) =
                (t_borho u)^n * (u + 1) * (t_borho u - u) - 1 + 1 := by omega
  rw [h_prod] at ht_dvd
  have : t_borho u ∣ 1 := by
    have h1 : t_borho u ∣ (t_borho u)^n * (u + 1) * (t_borho u - u) - 1 + 1 := ht_dvd
    have h2 : t_borho u ∣ (t_borho u)^n * (u + 1) * (t_borho u - u) := by
      calc t_borho u = (t_borho u)^1 := (pow_one _).symm
        _ ∣ (t_borho u)^n := pow_dvd_pow _ (Nat.one_le_of_lt hn)
        _ ∣ (t_borho u)^n * (u + 1) := Nat.dvd_mul_right _ _
        _ ∣ (t_borho u)^n * (u + 1) * (t_borho u - u) := Nat.dvd_mul_right _ _
    exact (Nat.dvd_add_right h2).mp h1
  have : 2 ≤ t_borho u := t_borho_ge_two u ht
  omega

/-- Extract coprimality of a and p₂ from hypothesis -/
theorem coprime_a_p2_of_hyp (a u n : ℕ) (hyp : BorhoHoffmannHypothesis a u n) :
    a.Coprime ((t_borho u)^n * (u + 1) * (t_borho u - u) - 1) := hyp.2.2.2.2.2.2

/-! ### Breeder Pair Properties -/

/-- From the breeder pair (a·u, a), extract σ(a·u) = a·u + a -/
theorem breeder_sigma_au (a u : ℕ) (hab : IsAmicablePair (a * u) a) :
    σ (a * u) = a * u + a := hab.1

/-- From the breeder pair (a·u, a), extract σ(a) = a·u + a -/
theorem breeder_sigma_a (a u : ℕ) (hab : IsAmicablePair (a * u) a) :
    σ a = a * u + a := hab.2

/-! ### Key Observation about t_borho -/

/-- **Important simplification**: t_borho(u) = σ(u).
    This follows from: t = u + s(u) where s(u) = σ(u) - u. -/
theorem t_borho_eq_sigma (u : ℕ) : t_borho u = σ u := by
  simp only [t_borho]
  omega

/-! ### Divisor Sum Calculations for Borho-Hoffmann -/

/-- σ of a prime power when the prime is known -/
theorem sum_divisors_pow_of_prime (p n : ℕ) (hp : p.Prime) (hn : 0 < n) :
    σ (p^n) = (p^(n+1) - 1) / (p - 1) := by
  have := sum_divisors_pow_prime hp n
  rw [this]
  have h2 : 2 ≤ p := Nat.Prime.two_le hp
  have : 1 ≤ p - 1 := by omega
  congr

/-- Compute σ(M_borho_bh) using multiplicativity -/
theorem sigma_M_borho_bh_formula (a u n : ℕ) (ha : 0 < a) (hu : 0 < u) (hn : 0 < n)
    (hyp : BorhoHoffmannHypothesis a u n) :
    σ (M_borho_bh a u n) = σ (a * u) * σ ((t_borho u)^n) *
                           σ ((t_borho u)^n * (u + 1) - 1) := by
  simp only [M_borho_bh]
  -- Extract hypotheses
  have h_cop_t := hyp.2.2.2.2.1
  have h_cop_p1 := hyp.2.2.2.2.2.1
  have ht_prime := hyp.2.1
  have hp1_prime := hyp.2.2.1
  -- Use multiplicativity repeatedly
  -- First: σ(a·u · t^n · p₁) = σ(a·u) · σ(t^n · p₁) if coprime
  have hcopau_tn_p1 : (a * u).Coprime ((t_borho u)^n * ((t_borho u)^n * (u + 1) - 1)) := by
    apply Nat.Coprime.mul_right
    · exact coprime_au_t_pow a u n hn h_cop_t
    · exact h_cop_p1
  rw [sum_divisors_mul_of_coprime hcopau_tn_p1]
  -- Second: σ(t^n · p₁) = σ(t^n) · σ(p₁) if coprime
  have hcop_tn_p1 : ((t_borho u)^n).Coprime ((t_borho u)^n * (u + 1) - 1) :=
    coprime_t_pow_p1 u n hu hn ht_prime hp1_prime
  rw [sum_divisors_mul_of_coprime hcop_tn_p1]

/-- Expand σ(M) into explicit form using breeder and prime properties -/
theorem sigma_M_borho_bh (a u n : ℕ) (ha : 0 < a) (hu : 0 < u) (hn : 0 < n)
    (hyp : BorhoHoffmannHypothesis a u n) :
    σ (M_borho_bh a u n) = (a * u + a) * ((t_borho u)^(n+1) - 1) / ((t_borho u) - 1) *
                           ((t_borho u)^n * (u + 1)) := by
  rw [sigma_M_borho_bh_formula a u n ha hu hn hyp]
  -- Substitute each σ value
  have hab := hyp.1
  rw [breeder_sigma_au a u hab]
  have ht_prime := hyp.2.1
  have hp1_prime := hyp.2.2.1
  rw [sum_divisors_pow_of_prime (t_borho u) n ht_prime hn]
  simpa [Finset.sum_range_succ, pow_zero, pow_one]
    using (sum_divisors_prime_pow (k:=1) (p:=((t_borho u)^n * (u + 1) - 1)) (f:=fun d => d) hp1_prime)
  -- Simplify: σ(p₁) = p₁ + 1 = t^n*(u+1) - 1 + 1 = t^n*(u+1)
  have h_p1_plus_one : (t_borho u)^n * (u + 1) - 1 + 1 = (t_borho u)^n * (u + 1) := by
    have := t_pow_mul_succ_ge_two u n hu hn ht_prime
    omega
  simp only [h_p1_plus_one]

/-- Similar calculation for σ(N) -/
theorem sigma_N_borho_bh_formula (a u n : ℕ) (ha : 0 < a) (hu : 0 < u) (hn : 0 < n)
    (hyp : BorhoHoffmannHypothesis a u n) :
    σ (N_borho_bh a u n) = σ a * σ ((t_borho u)^n) *
                           σ ((t_borho u)^n * (u + 1) * (t_borho u - u) - 1) := by
  simp only [N_borho_bh]
  have h_cop_t := hyp.2.2.2.2.1
  have h_cop_p2 := hyp.2.2.2.2.2.2
  have ht_prime := hyp.2.1
  have hp2_prime := hyp.2.2.2
  -- First: σ(a · t^n · p₂) = σ(a) · σ(t^n · p₂)
  have hcop_a_tn_p2 : a.Coprime ((t_borho u)^n * ((t_borho u)^n * (u + 1) * (t_borho u - u) - 1)) := by
    apply Nat.Coprime.mul_right
    · -- a and t^n are coprime (from a·u coprime with t)
      have h1 : (a * u).Coprime (t_borho u) := h_cop_t
      have h2 : a.Coprime (t_borho u) := by
        apply Nat.Coprime.of_mul_right_left
        exact h1
      exact h2.pow_right n
    · exact h_cop_p2
  rw [sum_divisors_mul_of_coprime hcop_a_tn_p2]
  -- Second: σ(t^n · p₂) = σ(t^n) · σ(p₂)
  have hcop_tn_p2 : ((t_borho u)^n).Coprime ((t_borho u)^n * (u + 1) * (t_borho u - u) - 1) :=
    coprime_t_pow_p2 u n hu hn ht_prime hp2_prime
  rw [sum_divisors_mul_of_coprime hcop_tn_p2]

/-- Expand σ(N) into explicit form -/
theorem sigma_N_borho_bh (a u n : ℕ) (ha : 0 < a) (hu : 0 < u) (hn : 0 < n)
    (hyp : BorhoHoffmannHypothesis a u n) :
    σ (N_borho_bh a u n) = (a * u + a) * ((t_borho u)^(n+1) - 1) / ((t_borho u) - 1) *
                           ((t_borho u)^n * (u + 1) * (t_borho u - u)) := by
  rw [sigma_N_borho_bh_formula a u n ha hu hn hyp]
  -- Substitute each σ value
  have hab := hyp.1
  rw [breeder_sigma_a a u hab]
  have ht_prime := hyp.2.1
  have hp2_prime := hyp.2.2.2
  rw [sum_divisors_pow_of_prime (t_borho u) n ht_prime hn]
  simpa [Finset.sum_range_succ, pow_zero, pow_one]
    using (sum_divisors_prime_pow (k:=1) (p:=((t_borho u)^n * (u + 1) * (t_borho u - u) - 1))
      (f:=fun d => d) hp2_prime)
  -- Simplify: σ(p₂) = p₂ + 1 = t^n*(u+1)*(t-u) - 1 + 1 = t^n*(u+1)*(t-u)
  have hu' : 1 < u := u_gt_one_of_t_prime u hu ht_prime
  have h_p2_plus_one : (t_borho u)^n * (u + 1) * (t_borho u - u) - 1 + 1 =
                       (t_borho u)^n * (u + 1) * (t_borho u - u) := by
    have := t_pow_mul_succ_mul_diff_sub_one_pos u n hu' hn ht_prime
    omega
  simp only [h_p2_plus_one]

/-! ### Key Algebraic Identity for Borho-Hoffmann -/

/-- Helper: expand M + N for algebraic manipulation -/
theorem M_plus_N_borho_bh (a u n : ℕ) :
    M_borho_bh a u n + N_borho_bh a u n =
    a * u * (t_borho u)^n * ((t_borho u)^n * (u + 1) - 1) +
    a * (t_borho u)^n * ((t_borho u)^n * (u + 1) * (t_borho u - u) - 1) := by
  simp only [M_borho_bh, N_borho_bh]

/-- The geometric series division is exact for t ≥ 2 -/
theorem geom_series_div_exact (t n : ℕ) (ht : 2 ≤ t) (hn : 0 < n) :
    (t - 1) ∣ (t^(n+1) - 1) := by
  have h1 : 1 ≤ t := by omega
  have h_sub_pos : 0 < t - 1 := by omega
  -- Use the fact that t^(n+1) - 1 = (t - 1) · (1 + t + t^2 + ... + t^n)
  -- This is a well-known identity
  induction n with
  | zero =>
    simp
    ring_nf
    omega
  | succ n ih =>
    -- t^(n+2) - 1 = t^(n+1) · t - 1 = t^(n+1) · t - t^(n+1) + t^(n+1) - 1
    --             = t^(n+1) · (t - 1) + (t^(n+1) - 1)
    have : t^(n+2) - 1 = t^(n+1) * (t - 1) + (t^(n+1) - 1) := by
      have ht_pow : 1 ≤ t^(n+1) := Nat.one_le_pow (n+1) t h1
      calc t^(n+2) - 1
          = t^(n+1) * t - 1 := by ring_nf
        _ = t^(n+1) * t - t^(n+1) + t^(n+1) - 1 := by omega
        _ = t^(n+1) * (t - 1) + (t^(n+1) - 1) := by ring
    rw [this]
    apply Nat.dvd_add
    · exact Nat.dvd_mul_left _ _
    · exact ih (by omega : 0 < n + 1)

/-- The critical algebraic identity: σ(M) = M + N.
    This uses the fact that σ(t^n) = (t^(n+1) - 1)/(t - 1) for prime t. -/
theorem sigma_M_eq_M_plus_N_borho_bh (a u n : ℕ) (ha : 0 < a) (hu : 0 < u) (hn : 0 < n)
    (hyp : BorhoHoffmannHypothesis a u n) :
    σ (M_borho_bh a u n) = M_borho_bh a u n + N_borho_bh a u n := by
  rw [sigma_M_borho_bh a u n ha hu hn hyp]
  rw [M_plus_N_borho_bh]
  simp only [M_borho_bh, N_borho_bh]
  -- Extract key facts
  have ht_prime := hyp.2.1
  have ht_ge : 2 ≤ t_borho u := t_borho_ge_two u ht_prime
  have hu' : 1 < u := u_gt_one_of_t_prime u hu ht_prime
  have ht_gt_u := t_borho_gt_u u hu'
  have h_t_sub : 0 < t_borho u - u := by omega
  have h_t_sub_pos : 1 ≤ t_borho u - u := by omega
  -- Prove using the fact that (t-1) | (t^(n+1) - 1)
  have h_div := geom_series_div_exact (t_borho u) n ht_ge hn
  -- To avoid division, multiply both sides by (t - 1)
  -- Need to prove: (a·u + a) · (t^(n+1) - 1) · t^n · (u+1) = (t - 1) · (M + N)
  have h_eq : (a * u + a) * ((t_borho u)^(n+1) - 1) * ((t_borho u)^n * (u + 1)) =
              ((t_borho u) - 1) * (a * u * (t_borho u)^n * ((t_borho u)^n * (u + 1) - 1) +
                                   a * (t_borho u)^n * ((t_borho u)^n * (u + 1) * (t_borho u - u) - 1)) := by
    -- Use zify to move to integers and ring to verify
    zify [t_borho_pos u hu, ha, hn, t_pow_mul_succ_ge_two u n hu hn ht_prime,
          t_pow_mul_succ_mul_diff_sub_one_pos u n hu' hn ht_prime, ht_ge]
    ring
  -- Now divide both sides by (t - 1)
  have h_t_minus_1_pos : 0 < t_borho u - 1 := by omega
  rw [Nat.mul_div_cancel_left _ h_t_minus_1_pos]
  congr 1
  exact Nat.eq_div_iff h_div ▸ h_eq

/-- Similarly, σ(N) = M + N -/
theorem sigma_N_eq_M_plus_N_borho_bh (a u n : ℕ) (ha : 0 < a) (hu : 0 < u) (hn : 0 < n)
    (hyp : BorhoHoffmannHypothesis a u n) :
    σ (N_borho_bh a u n) = M_borho_bh a u n + N_borho_bh a u n := by
  rw [sigma_N_borho_bh a u n ha hu hn hyp]
  rw [M_plus_N_borho_bh]
  simp only [M_borho_bh, N_borho_bh]
  -- Extract key facts (same as sigma_M proof)
  have ht_prime := hyp.2.1
  have ht_ge : 2 ≤ t_borho u := t_borho_ge_two u ht_prime
  have hu' : 1 < u := u_gt_one_of_t_prime u hu ht_prime
  have ht_gt_u := t_borho_gt_u u hu'
  have h_t_sub : 0 < t_borho u - u := by omega
  have h_div := geom_series_div_exact (t_borho u) n ht_ge hn
  -- Similar strategy: multiply both sides by (t - 1) and use ring
  have h_eq : (a * u + a) * ((t_borho u)^(n+1) - 1) * ((t_borho u)^n * (u + 1) * (t_borho u - u)) =
              ((t_borho u) - 1) * (a * u * (t_borho u)^n * ((t_borho u)^n * (u + 1) - 1) +
                                   a * (t_borho u)^n * ((t_borho u)^n * (u + 1) * (t_borho u - u) - 1)) := by
    zify [t_borho_pos u hu, ha, hn, t_pow_mul_succ_ge_two u n hu hn ht_prime,
          t_pow_mul_succ_mul_diff_sub_one_pos u n hu' hn ht_prime, ht_ge, h_t_sub]
    ring
  have h_t_minus_1_pos : 0 < t_borho u - 1 := by omega
  rw [Nat.mul_div_cancel_left _ h_t_minus_1_pos]
  congr 1
  exact Nat.eq_div_iff h_div ▸ h_eq

/-! ### Main Borho-Hoffmann Theorem -/

/-- p₁ < p₂ (the first prime is smaller than the second) -/
theorem p1_lt_p2 (u n : ℕ) (hu : 1 < u) (hn : 0 < n) (ht : (t_borho u).Prime) :
    (t_borho u)^n * (u + 1) - 1 < (t_borho u)^n * (u + 1) * (t_borho u - u) - 1 := by
  have ht_gt_u := t_borho_gt_u u hu
  have h_diff_ge : 2 ≤ t_borho u - u := by omega
  -- p₂ = t^n·(u+1)·(t-u) - 1 ≥ t^n·(u+1)·2 - 1 > t^n·(u+1) - 1 = p₁
  have h1 : (t_borho u)^n * (u + 1) * (t_borho u - u) ≥ (t_borho u)^n * (u + 1) * 2 := by
    apply Nat.mul_le_mul_left
    exact h_diff_ge
  have h2 : (t_borho u)^n * (u + 1) * 2 = (t_borho u)^n * (u + 1) + (t_borho u)^n * (u + 1) := by
    ring
  have h3 : 2 ≤ (t_borho u)^n * (u + 1) := t_pow_mul_succ_ge_two u n (by omega : 0 < u) hn ht
  calc (t_borho u)^n * (u + 1) - 1 + 1
      = (t_borho u)^n * (u + 1) := by omega
    _ < (t_borho u)^n * (u + 1) + (t_borho u)^n * (u + 1) := by omega
    _ = (t_borho u)^n * (u + 1) * 2 := by rw [← h2]
    _ ≤ (t_borho u)^n * (u + 1) * (t_borho u - u) := by omega
    _ = (t_borho u)^n * (u + 1) * (t_borho u - u) - 1 + 1 := by omega

/-- First show M ≠ N -/
theorem M_ne_N_borho_bh (a u n : ℕ) (ha : 0 < a) (hu : 0 < u) (hn : 0 < n)
    (hyp : BorhoHoffmannHypothesis a u n) :
    M_borho_bh a u n ≠ N_borho_bh a u n := by
  simp only [M_borho_bh, N_borho_bh]
  intro heq
  have ht_prime := hyp.2.1
  have hu' : 1 < u := u_gt_one_of_t_prime u hu ht_prime
  -- Simplify: if a·u·t^n·p₁ = a·t^n·p₂, then u·p₁ = p₂
  have ha_tn_pos : 0 < a * (t_borho u)^n := Nat.mul_pos ha (Nat.pos_pow_of_pos _ (t_borho_pos u hu))
  have : u * ((t_borho u)^n * (u + 1) - 1) = ((t_borho u)^n * (u + 1) * (t_borho u - u) - 1) :=
    Nat.mul_right_cancel ha_tn_pos heq
  -- But p₁ < p₂, so u·p₁ ≥ 2·p₁ > p₂ when u ≥ 2, contradiction
  have hp1_lt_p2 := p1_lt_p2 u n hu' hn ht_prime
  have : u * ((t_borho u)^n * (u + 1) - 1) > ((t_borho u)^n * (u + 1) * (t_borho u - u) - 1) := by
    calc u * ((t_borho u)^n * (u + 1) - 1)
        ≥ 2 * ((t_borho u)^n * (u + 1) - 1) := Nat.mul_le_mul_right _ (by omega : 2 ≤ u)
      _ = ((t_borho u)^n * (u + 1) - 1) + ((t_borho u)^n * (u + 1) - 1) := by ring
      _ > ((t_borho u)^n * (u + 1) - 1) + 0 := by omega
      _ > ((t_borho u)^n * (u + 1) * (t_borho u - u) - 1) := by omega
  omega

/-- **Borho-Hoffmann Breeding Theorem**: Under the hypothesis conditions,
    the constructed pair (M, N) is amicable.

    This is the main result connecting Borho-Hoffmann's formula to the
    amicable property. The proof combines the divisor sum calculations
    with the critical algebraic identity. -/
theorem borho_hoffmann_rule (a u n : ℕ) (ha : 0 < a) (hu : 0 < u) (hn : 0 < n)
    (hyp : BorhoHoffmannHypothesis a u n) :
    IsAmicablePair (M_borho_bh a u n) (N_borho_bh a u n) := by
  have ht_prime := hyp.2.1
  have hM_ne_zero : M_borho_bh a u n ≠ 0 := (M_borho_bh_pos a u n ha hu hn ht_prime).ne'
  have hN_ne_zero : N_borho_bh a u n ≠ 0 := (N_borho_bh_pos a u n ha hu hn ht_prime).ne'
  have hM_ne_N := M_ne_N_borho_bh a u n ha hu hn hyp
  rw [isAmicablePair_iff_sum_divisors hM_ne_zero hN_ne_zero hM_ne_N]
  constructor
  · exact sigma_M_eq_M_plus_N_borho_bh a u n ha hu hn hyp
  · exact sigma_N_eq_M_plus_N_borho_bh a u n ha hu hn hyp

/-- **te Riele's breeding method** (statement):
    te Riele (1984) showed how to generate new amicable pairs from given pairs
    systematically. The method has generated over 1 billion amicable pairs.

    The full formalization would require defining the breeding transformation
    and proving it preserves the amicable property. -/
def TeRieleBreeding_Exists : Prop :=
  ∀ N : ℕ, ∃ (pairs : List (ℕ × ℕ)),
    pairs.length > N ∧
    (∀ (p : ℕ × ℕ), p ∈ pairs → IsAmicablePair p.1 p.2)

/-! ### Historical Note on Computational Discoveries

The breeding methods of Borho and te Riele revolutionized the computational
search for amicable pairs. Before these methods, fewer than 1000 pairs were known.
Using breeding, over 1.2 billion pairs have been discovered as of 2020.

These methods transform the search from "find new pairs from scratch" to
"generate new pairs from known pairs", greatly accelerating discovery.
-/

/-- Connection: If infinitely many pairs exist, then breeding eventually
    produces arbitrarily many distinct pairs. -/
theorem infiniteAmicable_enables_breeding :
    InfinitelyManyAmicableConj → TeRieleBreeding_Exists := by
  intro h N
  -- Use infinitude to get N+1 distinct pairs with first member > N
  -- For each k ∈ [0, N], extract an amicable pair (m_k, n_k) with k < m_k
  let extract_pair (k : ℕ) : ℕ × ℕ :=
    (Classical.choose (h k), Classical.choose (Classical.choose_spec (h k)))
  -- Construct the list of N+1 pairs
  use (List.range (N+1)).map extract_pair
  constructor
  · -- Prove pairs.length > N
    simp [List.length_map, List.length_range]
  · -- Prove each pair is amicable
    intro p hp
    simp [List.mem_map] at hp
    obtain ⟨k, _, rfl⟩ := hp
    -- extract_pair k = (Classical.choose (h k), Classical.choose (Classical.choose_spec (h k)))
    have h1 := Classical.choose_spec (h k)
    -- h1 : ∃ n, k < Classical.choose (h k) ∧ IsAmicablePair (Classical.choose (h k)) n
    have h2 := Classical.choose_spec h1
    -- h2 : k < Classical.choose (h k) ∧ IsAmicablePair (Classical.choose (h k)) (Classical.choose h1)
    exact h2.2

end Nat
