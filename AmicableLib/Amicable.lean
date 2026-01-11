/-
Copyright (c) 2026 Zhipeng Chen, Haolun Tang, Jingyi Zhan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhipeng Chen, Haolun Tang, Jingyi Zhan

# Mathlib Contribution Candidate

This file is designed to be suitable for contribution to Mathlib.
It contains the core definitions and theorems for amicable numbers.
-/
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.FactorisationProperties
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Amicable Numbers

This file defines amicable numbers and proves basic properties.

Two positive integers `m` and `n` are called *amicable* if each is the sum of the
proper divisors of the other, i.e., `s(m) = n` and `s(n) = m`, where `s(k)` denotes
the sum of proper divisors of `k`.

## Main Definitions

* `Nat.properDivisorSum`: The sum of proper divisors of `n` (i.e., `σ(n) - n`).
* `Nat.IsAmicablePair`: Predicate stating that `(m, n)` is an amicable pair.
* `Nat.IsAmicable`: Predicate stating that `n` is part of some amicable pair.

## Main Results

* `Nat.IsAmicablePair.symm`: Amicable pairs are symmetric.
* `Nat.IsAmicablePair.one_lt_left`: Members of amicable pairs are greater than 1.
* `Nat.not_isAmicable_prime`: Primes cannot be amicable.
* `Nat.properDivisorSum_eq_sum_divisors_sub`: `s(n) = σ(n) - n`.
* `Nat.isAmicablePair_iff_sum_divisors`: Characterization via divisor sum.
* `Nat.IsAmicablePair.lt_iff`: Connection with abundant/deficient numbers.

## Historical Notes

The study of amicable numbers dates back to the Pythagoreans (circa 500 BC).
The pair (220, 284) was known in ancient times. Thābit ibn Qurra (9th century)
discovered a rule for generating amicable pairs.

## References

* [Wikipedia: Amicable numbers](https://en.wikipedia.org/wiki/Amicable_numbers)
* [OEIS A063990](https://oeis.org/A063990)

## Tags

amicable numbers, divisor sum, number theory
-/

namespace Nat

open BigOperators Finset ArithmeticFunction

/-! ### Definitions -/

/-- The sum of proper divisors of `n`, i.e., divisors excluding `n` itself.
This equals `σ(n) - n` where `σ` is the divisor sum function. -/
def properDivisorSum (n : ℕ) : ℕ :=
  ∑ d ∈ n.properDivisors, d

/-- Notation for proper divisor sum. -/
scoped notation "s" => properDivisorSum

/-- Two positive integers `m` and `n` are *amicable* if each is the sum of
the proper divisors of the other. -/
def IsAmicablePair (m n : ℕ) : Prop :=
  m ≠ 0 ∧ n ≠ 0 ∧ m ≠ n ∧ s m = n ∧ s n = m

/-- A number is *amicable* if it is part of some amicable pair. -/
def IsAmicable (n : ℕ) : Prop :=
  ∃ m : ℕ, IsAmicablePair n m

/-! ### Basic Properties of Proper Divisor Sum -/

/-- Proper divisor sum of 0 is 0. -/
@[simp]
theorem properDivisorSum_zero : s 0 = 0 := by
  simp [properDivisorSum]

/-- Proper divisor sum of 1 is 0 (1 has no proper divisors). -/
@[simp]
theorem properDivisorSum_one : s 1 = 0 := by
  simp [properDivisorSum]

/-- For a prime `p`, the proper divisor sum is 1. -/
theorem properDivisorSum_prime {p : ℕ} (hp : Nat.Prime p) : s p = 1 := by
  simp [properDivisorSum, hp.properDivisors]

/-! ### Basic Properties of Amicable Pairs -/

/-- Amicable pairs are symmetric. -/
theorem IsAmicablePair.symm {m n : ℕ} (h : IsAmicablePair m n) : IsAmicablePair n m := by
  obtain ⟨hm, hn, hne, hsm, hsn⟩ := h
  exact ⟨hn, hm, hne.symm, hsn, hsm⟩

/-- Members of an amicable pair are greater than 1. -/
theorem IsAmicablePair.one_lt_left {m n : ℕ} (h : IsAmicablePair m n) : 1 < m := by
  rcases m with _ | _ | m
  · exact (h.1 rfl).elim
  · -- m = 1: s(1) = 0, so n = 0, contradiction
    have : s 1 = 0 := properDivisorSum_one
    obtain ⟨_, hn, _, hsm, _⟩ := h
    rw [this] at hsm
    exact (hn hsm.symm).elim
  · omega

theorem IsAmicablePair.one_lt_right {m n : ℕ} (h : IsAmicablePair m n) : 1 < n :=
  h.symm.one_lt_left

/-- A prime cannot be part of an amicable pair. -/
theorem not_isAmicable_prime {p : ℕ} (hp : Nat.Prime p) : ¬IsAmicable p := by
  intro ⟨m, hm0, hp0, hne, hsm, hsn⟩
  rw [properDivisorSum_prime hp] at hsm
  -- s(p) = 1, so m = 1
  subst hsm
  -- But s(1) = 0 ≠ p for prime p
  simp at hsn
  exact hp.ne_zero hsn.symm

/-- 1 is not an amicable number. -/
theorem not_isAmicable_one : ¬IsAmicable 1 := by
  intro ⟨m, h⟩
  exact Nat.lt_irrefl 1 h.one_lt_left

/-! ### Relation with Divisor Sum Function σ -/

/-- The proper divisor sum equals (sum of all divisors) - n.
This can also be expressed as s(n) = σ₁(n) - n. -/
theorem properDivisorSum_eq_sum_divisors_sub (n : ℕ) :
    s n = σ 1 n - n := by
  simp only [sigma_one_apply]
  rcases n with _ | n
  · simp [properDivisorSum]
  · rw [properDivisorSum, sum_divisors_eq_sum_properDivisors_add_self]
    omega

/-- Characterization: (m,n) is amicable iff σ₁(m) = σ₁(n) = m + n
(where σ₁ denotes the sum of all divisors). -/
theorem isAmicablePair_iff_sum_divisors {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hne : m ≠ n) :
    IsAmicablePair m n ↔
      σ 1 m = m + n ∧ σ 1 n = m + n := by
  simp only [sigma_one_apply]
  constructor
  · intro ⟨_, _, _, hsm, hsn⟩
    constructor
    · rw [properDivisorSum_eq_sum_divisors_sub] at hsm
      simp only [sigma_one_apply] at hsm
      omega
    · rw [properDivisorSum_eq_sum_divisors_sub] at hsn
      simp only [sigma_one_apply] at hsn
      omega
  · intro ⟨hdm, hdn⟩
    refine ⟨hm, hn, hne, ?_, ?_⟩
    · rw [properDivisorSum_eq_sum_divisors_sub]
      simp only [sigma_one_apply]
      omega
    · rw [properDivisorSum_eq_sum_divisors_sub]
      simp only [sigma_one_apply]
      omega

/-! ### Relation with Perfect, Abundant, and Deficient Numbers -/

/-- In an amicable pair, if m < n then m is abundant and n is deficient. -/
theorem IsAmicablePair.lt_iff {m n : ℕ} (h : IsAmicablePair m n) :
    m < n ↔ Abundant m ∧ Deficient n := by
  obtain ⟨_, _, _, hsm, hsn⟩ := h
  have hsm' : ∑ i ∈ m.properDivisors, i = n := by
    simpa [properDivisorSum] using hsm
  have hsn' : ∑ i ∈ n.properDivisors, i = m := by
    simpa [properDivisorSum] using hsn
  simp [Abundant, Deficient, hsm', hsn']

/-! ### Multiplicativity of Divisor Sum -/

/-- n ≤ sum of divisors of n when n > 0, i.e., n ≤ σ₁(n). -/
theorem le_sum_divisors {n : ℕ} (hn : n ≠ 0) : n ≤ σ 1 n := by
  rw [sigma_one_apply]
  have h : n ∈ n.divisors := mem_divisors_self n hn
  have : ∑ d ∈ ({n} : Finset ℕ), d ≤ ∑ d ∈ n.divisors, d :=
    Finset.sum_le_sum_of_subset (Finset.singleton_subset_iff.mpr h)
  simp at this
  exact this

/-- The sum of divisors function σ₁ is multiplicative for coprime arguments.
This is a key lemma for the Thābit ibn Qurra formula. -/
theorem sum_divisors_mul_of_coprime {m n : ℕ} (hmn : m.Coprime n) :
    σ 1 (m * n) = σ 1 m * σ 1 n :=
  isMultiplicative_sigma.map_mul_of_coprime hmn

/-- For the proper divisor sum, multiplicativity takes the form:
s(mn) + mn = (s(m) + m) * (s(n) + n) when gcd(m,n) = 1.
This is because σ₁(mn) = σ₁(m) · σ₁(n) and σ₁(k) = s(k) + k. -/
theorem sum_divisors_add_self_mul_of_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hmn : m.Coprime n) :
    s (m * n) + m * n = (s m + m) * (s n + n) := by
  -- Use the fact that σ₁(k) = s(k) + k
  have eq1 : s m + m = σ 1 m := by
    rw [properDivisorSum_eq_sum_divisors_sub]
    have : m ≤ σ 1 m := le_sum_divisors hm
    omega
  have eq2 : s n + n = σ 1 n := by
    rw [properDivisorSum_eq_sum_divisors_sub]
    have : n ≤ σ 1 n := le_sum_divisors hn
    omega
  have eq3 : s (m * n) + m * n = σ 1 (m * n) := by
    rw [properDivisorSum_eq_sum_divisors_sub]
    have : m * n ≤ σ 1 (m * n) := le_sum_divisors (mul_ne_zero hm hn)
    omega
  rw [eq1, eq2, eq3, sum_divisors_mul_of_coprime hmn]


/-- The sum of divisors of 2^n is 2^(n+1) - 1, i.e., σ₁(2^n) = 2^(n+1) - 1. -/
theorem sum_divisors_two_pow (n : ℕ) :
    σ 1 (2^n) = 2^(n+1) - 1 := by
  rw [sigma_one_apply, sum_divisors_prime_pow Nat.prime_two]
  have h := Nat.geomSum_eq (by norm_num : (2 : ℕ) ≥ 2) (n + 1)
  simp only [show (2 : ℕ) - 1 = 1 from rfl, Nat.div_one] at h
  exact h

/-- σ(2^n) - 2^n = 2^n - 1, i.e., the proper divisor sum of 2^n. -/
theorem properDivisorSum_two_pow (n : ℕ) :
    s (2^n) = 2^n - 1 := by
  rw [properDivisorSum_eq_sum_divisors_sub, sum_divisors_two_pow]
  have h1 : 2^n ≤ 2^(n+1) - 1 := by
    have : 2^(n+1) = 2 * 2^n := by ring
    omega
  omega

/-! ### Key Lemmas for Thābit ibn Qurra Formula -/

/-- Any number of the form 3·2^k - 1 is odd when k ≥ 1. -/
theorem odd_three_mul_two_pow_sub_one {k : ℕ} (hk : 1 ≤ k) : Odd (3 * 2^k - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  use 3 * 2^n - 1
  have h3 : 3 * 2^(1 + n) = 2 * 3 * 2^n := by ring
  have h4 : 3 * 2^n ≥ 1 := by
    have : 2^n ≥ 1 := Nat.one_le_pow n 2 (by norm_num)
    omega
  omega

/-- Any number of the form 9·2^k - 1 is odd when k ≥ 1. -/
theorem odd_nine_mul_two_pow_sub_one {k : ℕ} (hk : 1 ≤ k) : Odd (9 * 2^k - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  use 9 * 2^n - 1
  have h3 : 9 * 2^(1 + n) = 2 * 9 * 2^n := by ring
  have h4 : 9 * 2^n ≥ 1 := by
    have : 2^n ≥ 1 := Nat.one_le_pow n 2 (by norm_num)
    omega
  omega

end Nat
