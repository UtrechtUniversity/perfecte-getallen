import Mathlib

def sum_of_divisors (n : ℕ) : ℕ := ∑ i ∈ n.divisors, i

theorem sum_of_divisors_mul (p q : ℕ) (h : Nat.Coprime p q) : ∑ i ∈ (p*q).divisors, i = (∑ i ∈ p.divisors, i)*(∑ i ∈ q.divisors, i) := Nat.Coprime.sum_divisors_mul h

theorem sum_divisors_prime (p : ℕ) (h : Nat.Prime p) : ∑ i ∈ p.divisors, i = p + 1 := Nat.Prime.sum_divisors h


theorem sum_divisors_2_pow (p : ℕ) : ∑ i ∈ (2^(p - 1)).divisors, i = 2^p - 1 := by
  sorry


theorem euclid_euler (n : ℕ) (heven : Even n) (h : n > 0): Nat.Perfect n ↔ (∃ p : ℕ, Nat.Prime (2^p - 1) ∧ 2^(p - 1)*((2^p) - 1) = n) := by
  constructor
  · intro hp
    rw [Nat.perfect_iff_sum_divisors_eq_two_mul h] at hp
    -- Aanpak?
    have : ∃ k, n = 2^(multiplicity 2 n)*k := by

      sorry
    obtain ⟨k, hk⟩ := this
    rw [hk] at hp

    sorry
  · rintro ⟨p, hp⟩
    rw [Nat.perfect_iff_sum_divisors_eq_two_mul h]
    rw [← hp.2]
    have hp0 : 0 < p - 1 := by
      sorry
    have hcoprime : Nat.Coprime (2 ^ (p - 1)) (2^p - 1) := by
      refine (Nat.coprime_pow_left_iff hp0 2 (2 ^ p - 1)).mpr ?_
      rw [@Nat.coprime_two_left, @Nat.odd_iff]
      simp only [Nat.two_pow_sub_one_mod_two, Nat.one_mod_two_pow_eq_one]
      omega

    rw [Nat.Coprime.sum_divisors_mul hcoprime]
    rw [sum_divisors_2_pow]
    rw [Nat.Prime.sum_divisors hp.1]
    have : 2^p - 1 + 1 = 2^p := by
      exact succ_mersenne p

    rw [this]
    rw [← mul_assoc]
    have : 2 * 2^(p - 1) = 2^p := by
      sorry
    rw [this]
    apply mul_comm
