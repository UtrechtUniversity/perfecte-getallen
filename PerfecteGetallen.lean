/-

Op basis van werk van Aaron Anderson (zie https://github.com/leanprover-community/mathlib4/blob/master/Archive/Wiedijk100Theorems/PerfectNumbers.lean)
-/
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.Algebra.GeomSum
import Mathlib.RingTheory.Multiplicity
import Mathlib.Tactic.NormNum.Prime

namespace Nat

open ArithmeticFunction Finset

-- Een getal van de vorm 2^k - 1 noemen we een mersenne getal. Als dat getal priem is, noemen we het een mersenne priemgetal.

-- Het zesde mersenne getal (0 telt ook mee) is 31. Dit kan je in de infoview zien als je cursor hierin staat.
#eval mersenne 5


-- Opdracht: Bereken met `#eval` het tiende mersenne getal.

-- Een natuurlijk getal `a` deelt een natuurlijk getal `b` als er een natuurlijk getal `k` bestaat zodat `a*k=b`. Dit schrijven we als: `a ∣ b`
-- Hierbij typen we in Lean de streep als `\|`. We zeggen ook wel dat `a` een deler is van `b`.

-- 5 deelt 10
#eval 5 ∣ 10

-- 6 deelt 31 niet
#eval 6 ∣ 31

-- Opdracht: Bereken met `#eval` of `13` een deler is van `91`

-- De delers van een getal n kan je berekenen met `divisors`
#eval (6 : Nat).divisors

-- Opdracht: Bereken met `#eval` de delers van 28

-- Opdracht: Bereken met `#eval` de delers van 2^8

def som_van_delers (n : ℕ) := ∑ d ∈ n.divisors, d

-- De som van de delers van 4 is 6
#eval som_van_delers 4

-- De som van de delers van 6 is 12
#eval som_van_delers 6

-- Bereken met `#eval` de som van de delers van `2^k` voor een paar verschillende getallen `k`

-- Deze rekenregel stelt dat de som van de eerste `k` tweemachten gelijk is aan `2^k - 1`
theorem feit1 (k : ℕ) : (∑ i ∈ range k, 2 ^ i)  = 2 ^ k - 1 := by
  rw [show 2 = 1 + 1 from rfl, ← geom_sum_mul_add 1 k]
  norm_num

-- Opdracht: Gebruik de tactiek `norm_num` en `feit1` om dit bewijs af te maken.
-- We bewijzen hier dat
theorem sigma_twee_macht_gelijk_mersenne_opv (k : ℕ) : som_van_delers (2 ^ k) = mersenne (k + 1) := by
  -- Met simp only herschrijven we de definities naar wat er onder ligt
  simp only [som_van_delers, mersenne]
  sorry
  -- Oplossing:
  -- norm_num
  -- exact feit1 (k + 1)

-- De definitie van een perfect getal is dat de som van alle delers, behalve het getal zelf, gelijk is aan het getal zelf.
-- In de wiskunde bibliotheek van Lean (Mathlib), worden deze delers `properDivisors` genoemd.
#reduce Perfect


-- Bij onze `som_van_delers` nemen we het getal zelf ook mee.
-- Dat betekent dat een getal perfect is, dan en slechts dan als de `som_van_delers` gelijk is aan twee keer het getal.
theorem perfect_desda_som_van_delers_gelijk_twee_keer (h : 0 < n) :
    Perfect n ↔ som_van_delers n = 2 * n := by
  simp [som_van_delers]
  exact perfect_iff_sum_divisors_eq_two_mul h


-- Twee natuurlijke getallen `p` en `q` zijn `Copriem` (Engels: `Coprime`) als er geen getal `k > 1` bestaat zodat `k ∣ p` en `k ∣ q`.

-- 15 en 28 zijn copriem
#eval Nat.Coprime 15 28

-- 32 en 54 zijn niet copriem (2 deelt beide)
#eval Nat.Coprime 32 54

-- Opdracht: Bereken met `#eval` of 4 en 7 copriem zijn.

#eval Nat.Coprime 4 7

-- Opdracht: Bereken de som van delers van 4, 7 en 28 met `#eval`


-- Als twee getallen Copriem zijn, dan kunnen we de som van de delers van het product uitrekenen door de sommen van delers van p en q los te vermenigvuldigen
theorem sum_van_delers_multiplicatief {p q : ℕ} (h : Nat.Coprime p q): som_van_delers (p * q) = som_van_delers p * som_van_delers q := by
  simp [som_van_delers]
  rw [Coprime.sum_divisors_mul h]

/-- Euclid's theorem that Mersenne primes induce perfect numbers -/
theorem perfect_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).Prime) :
    Nat.Perfect (2 ^ k * mersenne (k + 1)) := by
  rw [perfect_desda_som_van_delers_gelijk_twee_keer (by positivity), ← mul_assoc, ← pow_succ',
    mul_comm,
    sum_van_delers_multiplicatief ((Odd.coprime_two_right (by simp)).pow_right _),
    sigma_twee_macht_gelijk_mersenne_opv]
  simp [pr, Nat.prime_two, sigma_one_apply]


theorem ne_zero_of_prime_mersenne (k : ℕ) (pr : (mersenne (k + 1)).Prime) : k ≠ 0 := by
  intro H
  simp [H, mersenne, Nat.not_prime_one] at pr

theorem even_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).Prime) :
    Even (2 ^ k * mersenne (k + 1)) := by simp [ne_zero_of_prime_mersenne k pr, parity_simps]

theorem eq_two_pow_mul_odd {n : ℕ} (hpos : 0 < n) : ∃ k m : ℕ, n = 2 ^ k * m ∧ ¬Even m := by
  have h := Nat.multiplicity_finite_iff.2 ⟨Nat.prime_two.ne_one, hpos⟩
  cases' pow_multiplicity_dvd 2 n with m hm
  use multiplicity 2 n, m
  refine ⟨hm, ?_⟩
  rw [even_iff_two_dvd]
  have hg := h.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)
  contrapose! hg
  rcases hg with ⟨k, rfl⟩
  apply Dvd.intro k
  rw [pow_succ, mul_assoc, ← hm]

/-- **Perfect Number Theorem**: Euler's theorem that even perfect numbers can be factored as a
  power of two times a Mersenne prime. -/
theorem eq_two_pow_mul_prime_mersenne_of_even_perfect {n : ℕ} (ev : Even n) (perf : Nat.Perfect n) :
    ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧ n = 2 ^ k * mersenne (k + 1) := by
  have hpos := perf.2
  rcases eq_two_pow_mul_odd hpos with ⟨k, m, rfl, hm⟩
  use k
  rw [even_iff_two_dvd] at hm
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, ← sigma_one_apply,
    isMultiplicative_sigma.map_mul_of_coprime (Nat.prime_two.coprime_pow_of_not_dvd hm).symm,
    sigma_twee_macht_gelijk_mersenne_opv, ← mul_assoc, ← pow_succ'] at perf
  obtain ⟨j, rfl⟩ := ((Odd.coprime_two_right (by simp)).pow_right _).dvd_of_dvd_mul_left
    (Dvd.intro _ perf)
  rw [← mul_assoc, mul_comm _ (mersenne _), mul_assoc] at perf
  have h := mul_left_cancel₀ (by positivity) perf
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self, ← succ_mersenne, add_mul,
    one_mul, add_comm] at h
  have hj := add_left_cancel h
  cases Nat.sum_properDivisors_dvd (by rw [hj]; apply Dvd.intro_left (mersenne (k + 1)) rfl) with
  | inl h_1 =>
    have j1 : j = 1 := Eq.trans hj.symm h_1
    rw [j1, mul_one, Nat.sum_properDivisors_eq_one_iff_prime] at h_1
    simp [h_1, j1]
  | inr h_1 =>
    have jcon := Eq.trans hj.symm h_1
    rw [← one_mul j, ← mul_assoc, mul_one] at jcon
    have jcon2 := mul_right_cancel₀ ?_ jcon
    · exfalso
      match k with
      | 0 =>
        apply hm
        rw [← jcon2, pow_zero, one_mul, one_mul] at ev
        rw [← jcon2, one_mul]
        exact even_iff_two_dvd.mp ev
      | .succ k =>
        apply ne_of_lt _ jcon2
        rw [mersenne, ← Nat.pred_eq_sub_one, Nat.lt_pred_iff, ← pow_one (Nat.succ 1)]
        apply pow_lt_pow_right (Nat.lt_succ_self 1) (Nat.succ_lt_succ (Nat.succ_pos k))
    contrapose! hm
    simp [hm]

/-- The Euclid-Euler theorem characterizing even perfect numbers -/
theorem even_and_perfect_iff {n : ℕ} :
    Even n ∧ Nat.Perfect n ↔ ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧
      n = 2 ^ k * mersenne (k + 1) := by
  constructor
  · rintro ⟨ev, perf⟩
    exact Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect ev perf
  · rintro ⟨k, pr, rfl⟩
    exact ⟨even_two_pow_mul_mersenne_of_prime k pr, perfect_two_pow_mul_mersenne_of_prime k pr⟩

end Nat
