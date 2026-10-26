import Mathlib

/-! Deterministic scale bands and the logarithmic lattice count from §§4.2 and 5. -/

set_option autoImplicit false
noncomputable section

namespace SupercriticalLFPPAS.Iteration

def annulusBase : ℝ := 4096

/-- The `j`-th upper exponent in the geometric band family. -/
def bandUpper (j : ℕ) : ℝ := (1 / 8 : ℝ) ^ j

/-- The `j`-th lower exponent in the geometric band family. -/
def bandLower (j : ℕ) : ℝ := bandUpper j / 4

theorem band_scales {j : ℕ} (hj : 1 ≤ j) :
    0 < bandLower j ∧ bandLower j ≤ bandUpper j / 4 ∧
      bandUpper j / 4 < bandUpper j ∧ bandUpper j / 4 > bandUpper (j + 1) ∧
      bandUpper j < 1 := by
  have hbase : (0 : ℝ) < 1 / 8 := by norm_num
  have hpow : 0 < (1 / 8 : ℝ) ^ j := pow_pos hbase _
  have hpowlt : (1 / 8 : ℝ) ^ j < 1 := by
    exact pow_lt_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 8)
      (by norm_num : (1 / 8 : ℝ) < 1) (by omega)
  have h4 : (0 : ℝ) < 4 := by norm_num
  have hnext : bandUpper (j + 1) = bandUpper j / 8 := by
    simp [bandUpper, pow_succ, div_eq_mul_inv, mul_comm]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hu : 0 < bandUpper j := by
      change 0 < (1 / 8 : ℝ) ^ j
      exact hpow
    change 0 < bandUpper j / 4
    exact div_pos hu h4
  · simp [bandLower]
  · dsimp [bandUpper]
    nlinarith [hpow]
  · rw [hnext]
    dsimp [bandUpper, bandLower]
    nlinarith [hpow]
  · simpa [bandUpper] using hpowlt

/-- Integer powers of `4096` whose logarithms lie strictly inside the requested scale
window. This finite exponent set is the index form of the paper's radius set
`{B^j : ε^t < B^j < ε^s}`. -/
def radiusExponents (ε s t : ℝ) : Finset ℤ :=
  Finset.Ioo (Int.floor (t * Real.log ε / Real.log annulusBase))
    (Int.ceil (s * Real.log ε / Real.log annulusBase))

/-- The actual finite family of dyadic-in-logarithmic-scale radii `B^j`. -/
def radiusSet (ε s t : ℝ) : Finset ℝ :=
  (radiusExponents ε s t).image fun j : ℤ => annulusBase ^ j

theorem radiusSet_card (ε s t : ℝ) :
    (radiusSet ε s t).card = (radiusExponents ε s t).card := by
  classical
  rw [radiusSet, Finset.card_image_iff]
  intro j hj k hk hpow
  have hB : 1 < annulusBase := by norm_num [annulusBase]
  exact (zpow_right_strictMono₀ hB).injective hpow

/-- Every radius in the finite family satisfies the open cutoff inequalities defining
`R_ε(s,t)`. -/
theorem radiusSet_mem_cutoffs {ε s t : ℝ} (hε : 0 < ε)
    {j : ℤ} (hj : j ∈ radiusExponents ε s t) :
    ε ^ t < annulusBase ^ j ∧ annulusBase ^ j < ε ^ s := by
  have hB : 1 < annulusBase := by norm_num [annulusBase]
  have hlogB : 0 < Real.log annulusBase := Real.log_pos hB
  have hindex := Finset.mem_Ioo.mp hj
  let a := t * Real.log ε / Real.log annulusBase
  let b := s * Real.log ε / Real.log annulusBase
  have hlow : a < (j : ℝ) := by
    have hstep : Int.floor a + 1 ≤ j := Int.add_one_le_iff.mpr hindex.1
    have hstep' : (Int.floor a : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hstep
    dsimp [a]
    exact (Int.lt_floor_add_one _).trans_le hstep'
  have hhigh : (j : ℝ) < b := by
    by_contra h
    have hbj : b ≤ (j : ℝ) := le_of_not_gt h
    have hceil : Int.ceil b ≤ j := Int.ceil_le.mpr hbj
    exact (not_le_of_gt hindex.2) hceil
  have hlow' : t * Real.log ε < (j : ℝ) * Real.log annulusBase := by
    dsimp [a] at hlow
    exact (div_lt_iff₀ hlogB).1 hlow
  have hhigh' : (j : ℝ) * Real.log annulusBase < s * Real.log ε := by
    dsimp [b] at hhigh
    exact (lt_div_iff₀ hlogB).1 hhigh
  constructor
  · apply (Real.log_lt_log_iff (Real.rpow_pos_of_pos hε t)
      (zpow_pos (by positivity : 0 < annulusBase) j)).1
    rw [Real.log_rpow hε, Real.log_zpow]
    exact hlow'
  · apply (Real.log_lt_log_iff (zpow_pos (by positivity : 0 < annulusBase) j)
      (Real.rpow_pos_of_pos hε s)).1
    rw [Real.log_zpow, Real.log_rpow hε]
    exact hhigh'

/-- The finite image construction is exactly the paper's open radius set, expressed by
its integer exponent indices. -/
theorem radiusExponents_mem_iff_cutoffs {ε s t : ℝ} (hε : 0 < ε)
    {j : ℤ} : j ∈ radiusExponents ε s t ↔
      ε ^ t < annulusBase ^ j ∧ annulusBase ^ j < ε ^ s := by
  constructor
  · exact radiusSet_mem_cutoffs hε
  · intro hcut
    have hB : 1 < annulusBase := by norm_num [annulusBase]
    have hlogB : 0 < Real.log annulusBase := Real.log_pos hB
    have hlowLog := (Real.log_lt_log_iff (Real.rpow_pos_of_pos hε t)
      (zpow_pos (by positivity : 0 < annulusBase) j)).2 hcut.1
    have hhighLog := (Real.log_lt_log_iff (zpow_pos (by positivity : 0 < annulusBase) j)
      (Real.rpow_pos_of_pos hε s)).2 hcut.2
    rw [Real.log_rpow hε, Real.log_zpow] at hlowLog
    rw [Real.log_zpow, Real.log_rpow hε] at hhighLog
    have hlow : t * Real.log ε / Real.log annulusBase < (j : ℝ) :=
      (div_lt_iff₀ hlogB).2 hlowLog
    have hhigh : (j : ℝ) < s * Real.log ε / Real.log annulusBase :=
      (lt_div_iff₀ hlogB).2 hhighLog
    have hfloor : Int.floor (t * Real.log ε / Real.log annulusBase) < j := by
      by_contra h
      have hji : j ≤ Int.floor (t * Real.log ε / Real.log annulusBase) := le_of_not_gt h
      have hji' : (j : ℝ) ≤ t * Real.log ε / Real.log annulusBase := by
        have hjiCast : (j : ℝ) ≤ (Int.floor (t * Real.log ε / Real.log annulusBase) : ℝ) := by
          exact_mod_cast hji
        exact hjiCast.trans (Int.floor_le _)
      exact (not_le_of_gt hlow) hji'
    have hceil : j < Int.ceil (s * Real.log ε / Real.log annulusBase) := by
      by_contra h
      have hbj : Int.ceil (s * Real.log ε / Real.log annulusBase) ≤ j := le_of_not_gt h
      have hbj' : s * Real.log ε / Real.log annulusBase ≤ (j : ℝ) :=
        (Int.le_ceil _).trans (by exact_mod_cast hbj)
      exact (not_le_of_gt hhigh) hbj'
    exact Finset.mem_Ioo.mpr ⟨hfloor, hceil⟩

theorem integer_open_interval_card_lower (a b : ℝ) (hab : a < b) :
    ((Finset.Ioo (Int.floor a) (Int.ceil b)).card : ℝ) ≥ b - a - 1 := by
  have hfloor : (Int.floor a : ℝ) ≤ a := Int.floor_le a
  have hceil : b ≤ (Int.ceil b : ℝ) := Int.le_ceil b
  by_cases h : Int.floor a < Int.ceil b
  · have hcard := Int.card_Ioo_of_lt (Int.floor a) (Int.ceil b) h
    have hcard' : ((Finset.Ioo (Int.floor a) (Int.ceil b)).card : ℝ) =
        (Int.ceil b : ℝ) - (Int.floor a : ℝ) - 1 := by exact_mod_cast hcard
    rw [hcard']
    linarith
  · have hceilfloor : Int.ceil b ≤ Int.floor a := le_of_not_gt h
    have hba : b < a + 1 := by
      have hceilfloor' : (Int.ceil b : ℝ) ≤ Int.floor a := by exact_mod_cast hceilfloor
      calc
        b ≤ Int.ceil b := hceil
        _ ≤ Int.floor a := hceilfloor'
        _ ≤ a := hfloor
        _ < a + 1 := by linarith
    have habound : b - a < 1 := by linarith
    have hempty : Finset.Ioo (Int.floor a) (Int.ceil b) = ∅ := by
      ext z
      have hzImpossible : ¬ (Int.floor a < z ∧ z < Int.ceil b) := by omega
      simp [Finset.mem_Ioo, hzImpossible]
    simp [hempty]
    linarith

/-- Corrected logarithmic count for the full open window: the number of admissible
integer exponents is at least its logarithmic width minus one. -/
theorem radiusExponents_count_lower {ε s t : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (_hs : 0 < s) (hst : s < t) :
    ((radiusExponents ε s t).card : ℝ) ≥
      (t - s) * (-Real.log ε) / Real.log annulusBase - 1 := by
  have hB : 1 < annulusBase := by norm_num [annulusBase]
  have hlogB : 0 < Real.log annulusBase := Real.log_pos hB
  have hlogε : Real.log ε < 0 := Real.log_neg hε hε1
  have hlowlt : t * Real.log ε / Real.log annulusBase <
      s * Real.log ε / Real.log annulusBase := by
    apply (div_lt_div_iff_of_pos_right hlogB).2
    nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr hst) hlogε]
  have hcount := integer_open_interval_card_lower
    (t * Real.log ε / Real.log annulusBase)
    (s * Real.log ε / Real.log annulusBase) hlowlt
  have hwidth : s * Real.log ε / Real.log annulusBase -
      t * Real.log ε / Real.log annulusBase =
      (t - s) * (-Real.log ε) / Real.log annulusBase := by ring
  simpa [radiusExponents, hwidth] using hcount

/-- When `s ≤ t/4`, the paper's coarser count follows from the corrected full-width
bound, after allowing an additive constant. -/
theorem radiusExponents_count_quarter {ε s t : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hs : 0 < s) (hst : s ≤ t / 4)
    (_ht : 0 < t) :
    ((radiusExponents ε s t).card : ℝ) ≥
      t / 4 * (-Real.log ε) / Real.log annulusBase - 1 := by
  have hst' : s < t := by linarith
  have hlogB : 0 < Real.log annulusBase := Real.log_pos (by norm_num [annulusBase])
  have hlogε : -Real.log ε > 0 := by linarith [Real.log_neg hε hε1]
  have h := radiusExponents_count_lower hε hε1 hs hst'
  have hwidth : (t - s) * (-Real.log ε) / Real.log annulusBase ≥
      t / 4 * (-Real.log ε) / Real.log annulusBase := by
    apply (div_le_div_iff_of_pos_right hlogB).2
    nlinarith
  linarith

/-- Corrected logarithmic count for the finite family of actual radii. -/
theorem radiusSet_count_lower {ε s t : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hs : 0 < s) (hst : s < t) :
    ((radiusSet ε s t).card : ℝ) ≥
      (t - s) * (-Real.log ε) / Real.log annulusBase - 1 := by
  rw [radiusSet_card]
  exact radiusExponents_count_lower hε hε1 hs hst

/-- The paper's coarser quarter-band count, with its bounded endpoint error explicit. -/
theorem radiusSet_count_quarter {ε s t : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hs : 0 < s) (hst : s ≤ t / 4) (ht : 0 < t) :
    ((radiusSet ε s t).card : ℝ) ≥
      t / 4 * (-Real.log ε) / Real.log annulusBase - 1 := by
  rw [radiusSet_card]
  exact radiusExponents_count_quarter hε hε1 hs hst ht

/-- Adjacent annular supports are disjoint when the smaller radius is at most `1/4096`
of the larger radius. -/
theorem annular_supports_disjoint {z : ℂ} {rsmall rlarge : ℝ}
    (hr : 0 < rlarge) (hscale : rsmall / rlarge ≤ 1 / annulusBase) :
    Disjoint {x : ℂ | rsmall / 16 < dist x z ∧ dist x z < 32 * rsmall}
      {x : ℂ | rlarge / 16 < dist x z ∧ dist x z < 32 * rlarge} := by
  rw [Set.disjoint_left]
  intro x hx hy
  have hratio' : rsmall ≤ (1 / annulusBase) * rlarge := (div_le_iff₀ hr).1 hscale
  have hratio : rsmall ≤ rlarge / annulusBase := by
    simpa [div_eq_mul_inv, annulusBase, mul_comm] using hratio'
  change rsmall / 16 < dist x z ∧ dist x z < 32 * rsmall at hx
  change rlarge / 16 < dist x z ∧ dist x z < 32 * rlarge at hy
  have hout : dist x z < rlarge / 16 := by
    calc
      dist x z < 32 * rsmall := hx.2
      _ ≤ 32 * (rlarge / annulusBase) := by gcongr
      _ < rlarge / 16 := by norm_num [annulusBase]; nlinarith [hr]
  linarith

end SupercriticalLFPPAS.Iteration
