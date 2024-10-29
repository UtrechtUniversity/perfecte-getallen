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

-- We kunnen bewijzen dat 5 een deler is van 10: Door het geven van het getal 2 met `use`, want `5*2=10`
theorem vijf_deelt_tien : 5 ∣ 10 := by
  use 2

-- Opdracht: Bewijs dat 7 een deler is van 56
theorem zeven_deelt_zesenvijftig : 7 ∣ 56 := by
  sorry
  -- Oplossing : use 8

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
theorem som_van_tweemachten (k : ℕ) : (∑ i ∈ range k, 2 ^ i)  = 2 ^ k - 1 := by
  rw [show 2 = 1 + 1 from rfl, ← geom_sum_mul_add 1 k]
  norm_num

-- Opdracht: Gebruik de tactiek `norm_num` en `som_van_tweemachten` om dit bewijs af te maken.
-- We bewijzen hier dat
theorem som_van_delers_twee_macht_gelijk_mersenne_opv (k : ℕ) : som_van_delers (2 ^ k) = mersenne (k + 1) := by
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

-- Opdracht: Bereken de som van delers van 4, 7 en 28 met `#eval`


-- Als twee getallen copriem zijn, dan kunnen we de som van de delers van het product uitrekenen door de sommen van delers van p en q los te vermenigvuldigen
theorem som_van_delers_multiplicatief {p q : ℕ} (h : Nat.Coprime p q): som_van_delers (p * q) = som_van_delers p * som_van_delers q := by
  simp [som_van_delers]
  rw [Coprime.sum_divisors_mul h]

-- Als een getal `p` priem is, dan is de som van de delers `p + 1`.
-- De enige delers zijn tenslotte `1` en `p`\
theorem som_van_delers_priem {p : ℕ} (h : p.Prime) : som_van_delers p = p + 1 := by
  simp [som_van_delers, h]

-- Euclides had al bewezen dat een mersenne-priemgetal gebruikt kan worden om
-- een perfect getal te maken.
-- Opdracht: Bewijs deze stelling met gebruik van verschillende stellingen hierboven,
-- de stellingen `mul_assoc`, `pow_succ'`, `mul_comm`, en de tactieken `rw`, `simp` en `positivity` (die goed werkt om te bewijzen dat iets groter dan 0 is)
-- Tip: Als je niet weet wat een stelling doet kan je het bekijken met `#check`
#check mul_assoc
theorem perfect_twee_macht_prod_mersenne_van_priem (k : ℕ) (pr : (mersenne (k + 1)).Prime) :
    Nat.Perfect (2 ^ k * mersenne (k + 1)) := by
  sorry
  -- Oplossing:
  -- rw [perfect_desda_som_van_delers_gelijk_twee_keer (by positivity), ← mul_assoc, ← pow_succ',
  --   mul_comm,
  --   som_van_delers_multiplicatief ((Odd.coprime_two_right (by simp)).pow_right _),
  --   som_van_delers_twee_macht_gelijk_mersenne_opv]
  -- simp [pr, som_van_delers_priem]


-- Feitje: als we een mersenne priemgetal hebben met exponent `k + 1`, dan kan `k` niet gelijk zijn aan `0`.
theorem mersenne_priem_exponent_niet_nul (k : ℕ) (pr : (mersenne (k + 1)).Prime) : k ≠ 0 := by
  intro H
  simp [H, mersenne, Nat.not_prime_one] at pr

-- Dan weten we ook dat het perfecte getal dat we maken met het mersenne priemgetal even moet zijn
theorem perfect_getal_van_mersenne_priem_is_even (k : ℕ) (pr : (mersenne (k + 1)).Prime) :
    Even (2 ^ k * mersenne (k + 1)) := by simp [mersenne_priem_exponent_niet_nul k pr, parity_simps]

-- We kunnen elk getal schrijven als product van tweemacht en een oneven getal.
-- Dit doen we door herhaaldelijk factoren twee eruit te delen tot het overgebleven getal oneven is.
theorem ontbinding_met_tweemacht {n : ℕ} (hpos : 0 < n) : ∃ k m : ℕ, n = 2 ^ k * m ∧ ¬Even m := by
  have h := Nat.multiplicity_finite_iff.2 ⟨Nat.prime_two.ne_one, hpos⟩
  obtain ⟨m, hm⟩ := pow_multiplicity_dvd 2 n
  use multiplicity 2 n, m
  refine ⟨hm, ?_⟩
  rw [even_iff_two_dvd]
  have hg := h.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)
  contrapose! hg
  rcases hg with ⟨k, rfl⟩
  apply Dvd.intro k
  rw [pow_succ, mul_assoc, ← hm]

-- Euler had bewezen dat elk even perfect getal van de vorm van Euclides moet zijn
theorem eq_two_pow_mul_prime_mersenne_of_even_perfect {n : ℕ} (ev : Even n) (perf : Nat.Perfect n) :
    ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧ n = 2 ^ k * mersenne (k + 1) := by
  have hpos := perf.2
  rcases ontbinding_met_tweemacht hpos with ⟨k, m, rfl, hm⟩
  use k
  rw [even_iff_two_dvd] at hm
  rw [perfect_desda_som_van_delers_gelijk_twee_keer hpos,
    som_van_delers_multiplicatief (Nat.prime_two.coprime_pow_of_not_dvd hm).symm,
    som_van_delers_twee_macht_gelijk_mersenne_opv, ← mul_assoc, ← pow_succ'] at perf
  obtain ⟨j, rfl⟩ := ((Odd.coprime_two_right (by simp)).pow_right _).dvd_of_dvd_mul_left
    (Dvd.intro _ perf)
  rw [← mul_assoc, mul_comm _ (mersenne _), mul_assoc] at perf
  have h := mul_left_cancel₀ (by positivity) perf
  rw [som_van_delers, Nat.sum_divisors_eq_sum_properDivisors_add_self, ← succ_mersenne, add_mul,
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

-- Dus nu weten we de vorm van alle perfecte even getallen
theorem even_en_perfect_desda {n : ℕ} :
    Even n ∧ Nat.Perfect n ↔ ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧
      n = 2 ^ k * mersenne (k + 1) := by
  constructor
  · rintro ⟨ev, perf⟩
    exact Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect ev perf
  · rintro ⟨k, pr, rfl⟩
    exact ⟨perfect_getal_van_mersenne_priem_is_even k pr, perfect_twee_macht_prod_mersenne_van_priem k pr⟩

-- TODO: Clean up
theorem mersenne_priem_heeft_priem_exponent {k : ℕ} (h : (mersenne (k + 1)).Prime) : (k + 1).Prime := by
  by_contra! hc
  rw [@prime_def_lt] at hc
  push_neg at hc
  have : 2 ≤ k + 1:= by
    have := mersenne_priem_exponent_niet_nul k h
    omega
  specialize hc this
  obtain ⟨m, ⟨hmklein, hmdeelt⟩⟩ := hc
  obtain ⟨⟨l, hl⟩, hmnieteen⟩ := hmdeelt
  rw [hl] at h
  unfold mersenne at h
  rw [Nat.pow_mul] at h
  have := nat_sub_dvd_pow_sub_pow (2 ^ m) 1 l
  simp only [one_pow] at this
  cases' (Nat.dvd_prime h).mp this with h1 hp
  · rw [@pred_eq_succ_iff] at h1
    rw [propext (pow_eq_self_iff le.refl)] at h1
    exact hmnieteen h1
  · rw [← Nat.pow_mul] at hp
    rw [← hl] at hp
    have := Nat.sub_one_cancel (Nat.two_pow_pos _) (Nat.two_pow_pos _) hp
    have := Nat.pow_right_injective (by rfl) this
    omega

theorem even_en_perfect_eindigt_in_zes_of_acht {n : ℕ}
    (heven : Even n) (hperfect : n.Perfect) : n % 10 = 6 ∨ n % 10 = 8 := by
  obtain ⟨k, ⟨hk, hn⟩⟩ := even_en_perfect_desda.mp ⟨heven, hperfect⟩
  rw [hn]
  have : (k + 1).Prime := mersenne_priem_heeft_priem_exponent hk
  cases' this.eq_two_or_odd with h2 hodd
  · left
    have : k = 1 := by omega
    rw [h2, mersenne, this]
    norm_num
  · rw [Nat.odd_mod_four_iff] at hodd
    cases' hodd with h3 h4
    · left
      rw [mersenne]
      have : (2 ^ (k + 1) - 1) % 10 = 1 := by
        
        sorry
      sorry
    · sorry


end Nat
