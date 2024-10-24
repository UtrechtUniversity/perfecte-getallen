import Mathlib

def sum_of_divisors (n : ℕ) : ℕ := ∑ i ∈ n.divisors, i

theorem sum_of_divisors_mul (p q : ℕ) (h : Nat.Coprime p q) : ∑ i ∈ (p*q).divisors, i = (∑ i ∈ p.divisors, i)*(∑ i ∈ q.divisors, i) := Nat.Coprime.sum_divisors_mul h

theorem sum_divisors_prime (p : ℕ) (h : Nat.Prime p) : ∑ i ∈ p.divisors, i = p + 1 := Nat.Prime.sum_divisors h


theorem sum_divisors_2_pow (p : ℕ) : ∑ i ∈ (2^(p - 1)).divisors, i = 2^p - 1 := by
  sorry

theorem sum_divisors_2_pow' (p : ℕ) : ∑ i ∈ (2^p).divisors, i = 2^(p+1) - 1 := by
  sorry

theorem properDivisors_eq_singleton_iff_prime (n k : ℕ) (hk : n.properDivisors = {k}) : n.Prime ∧ k = 1 := by

  rw [← @Nat.properDivisors_eq_singleton_one_iff_prime]
  have : n.properDivisors.Nonempty := by
    rw [hk]
    exact Finset.singleton_nonempty k
  rw [@Nat.nonempty_properDivisors] at this
  rw [← Nat.one_mem_properDivisors_iff_one_lt] at this
  rw [hk] at this
  simp only [Finset.mem_singleton] at this
  rw [this]
  exact ⟨hk, rfl⟩

theorem euclid_euler (n : ℕ) (heven : Even n) (h : n > 0): Nat.Perfect n ↔ (∃ p : ℕ, Nat.Prime (2^p - 1) ∧ 2^(p - 1)*((2^p) - 1) = n) := by
  constructor
  · intro hp
    rw [Nat.perfect_iff_sum_divisors_eq_two_mul h] at hp
    -- Aanpak?
    obtain hn : n = 2^(n.factorization 2)*(n / 2^(n.factorization 2)) := by
      exact Eq.symm (Nat.ord_proj_mul_ord_compl_eq_self n 2)

    have := Nat.coprime_ord_compl (Nat.prime_two) (Nat.not_eq_zero_of_lt h)
    rw [hn] at hp
    rw [sum_of_divisors_mul _ _ (by sorry)] at hp

    rw [sum_divisors_2_pow'] at hp
    rw [← mul_assoc] at hp
    rw [← Nat.pow_succ'] at hp

    have ho : Odd (2^(n.factorization 2 + 1) - 1) := by
      sorry

    have hprop : (n / 2^(n.factorization 2))/(2^(n.factorization 2 + 1) - 1) ∈ (n / 2^(n.factorization 2)).properDivisors := by
      rw [@Nat.mem_properDivisors]
      constructor
      · have hco : Nat.Coprime (2 ^ (n.factorization 2 + 1) - 1) (2^(n.factorization 2 + 1)) := by
          have := Odd.coprime_two_right ho
          exact Nat.Coprime.pow_right (n.factorization 2 + 1) this


        sorry
      ·
        sorry

    have : 2^(n.factorization 2 + 1) ∣ 2^(n.factorization 2  + 1)*(n / 2 ^ n.factorization 2) := by
      exact Nat.dvd_mul_right (2 ^ (n.factorization 2 + 1)) (n / 2 ^ n.factorization 2)

    have hsub : (n / 2^(n.factorization 2)).properDivisors = {(n / 2^(n.factorization 2))/(2^(n.factorization 2 + 1) - 1)} := by

      sorry
    have fact := properDivisors_eq_singleton_iff_prime _ _ hsub


    use n.factorization 2 + 1

    have : n / 2^(n.factorization 2) = 2^(n.factorization 2 + 1) - 1 := by
      sorry
    rw [← this]
    constructor
    · exact fact.1
    · simp only [add_tsub_cancel_right]
      exact hn.symm


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


    -- have hmem : 1 ∈ (n / 2^(n.factorization 2)).properDivisors := by
    --   refine Nat.one_mem_properDivisors_iff_one_lt.mpr ?_
    --   exact Nat.one_lt_div_of_mem_properDivisors (by sorry)

    -- have : 1 = (n / 2^(n.factorization 2))/(2^(n.factorization 2 + 1) - 1) := by
    --   rw [hsub] at hmem
    --   sorry


    -- have : ∑ i ∈  (n / 2^(n.factorization 2)).divisors, i ≥ (n / 2^(n.factorization 2)) + (n / 2^(n.factorization 2))/(2^(n.factorization 2 + 1) - 1) := by
    --   rw [@Nat.sum_divisors_eq_sum_properDivisors_add_self]
    --   rw [add_comm]
    --   refine Nat.add_le_add (by rfl) ?h₂
    --   exact Finset.single_le_sum (by simp : ∀ i ∈ (n / 2^(n.factorization 2)).properDivisors, 0 ≤ id i) hprop


    -- sorry
