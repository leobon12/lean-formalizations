import HigherDimLQGMetric.Events.ShellCoverTail
import HigherDimLQGMetric.Events.ShellCoverAnalytic

/-!
# Lemma 5.2: rounded-centre shell covering
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Metric
open HigherDimLFPP (Rd)
open HigherDimLFPP.DGZ (latPt roundLat)
open scoped ENNReal

variable {d : ℕ}

open Classical in
/-- **[S] Lemma 5.2**: rounded-centre shell covering. -/
def ShellCover (d : ℕ) : Prop :=
  ∀ ρ s : ℝ, 0 < ρ → 0 < s → ∃ p : ℝ, p < 1 ∧
  ∀ L C₀ : ℝ, 0 < L → 0 ≤ C₀ → ∃ C ε₁ : ℝ, 0 < ε₁ ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d), IsWholeSpaceLGF h P →
  ∀ E : Rd d → ℝ → Set Ω, IsShellLocal P h E →
  ∀ R ε : ℝ, 0 < R → 0 < ε → ε < ε₁ → ∀ T : Finset ℤ,
    (∀ j ∈ T, j ∈ scaleWin ε R) →
    ρ * Real.logb 64 ε⁻¹ - C₀ ≤ T.card →
    (∀ j ∈ T, ∀ z : Rd d, ENNReal.ofReal p ≤ P (E z ((64 : ℝ) ^ j))) →
    P {ω | ¬ ∀ x ∈ Metric.ball (0 : Rd d) (L * R), ∃ j ∈ T, ∃ k : Fin d → ℤ,
        ‖x - latPt ((64 : ℝ) ^ j / (100 * d)) k‖ < (64 : ℝ) ^ j / 2 ∧
        ω ∈ E (latPt ((64 : ℝ) ^ j / (100 * d)) k) ((64 : ℝ) ^ j)} ≤
      ENNReal.ofReal (C * ε ^ s)

private theorem shellCover_ball_mem_box {L R : ℝ} (_hL : 0 < L) (hR : 0 < R)
    {y : Rd d} (hy : y ∈ Metric.ball 0 (L * R)) :
    y ∈ HigherDimLFPP.Osc.box 0 ((L + 1) * R) := by
  intro i
  have hcoord := PiLp.norm_apply_le y i
  have hnorm : ‖y‖ < L * R := by simpa only [Metric.mem_ball, dist_zero_right] using hy
  have hB : L * R < (L + 1) * R := by nlinarith
  simpa only [PiLp.zero_apply, sub_zero] using
    (lt_of_le_of_lt (by simpa only [Real.norm_eq_abs] using hcoord) (hnorm.trans hB)).le

private theorem shellCover_near (hd : 1 ≤ d) {r η B : ℝ} (hr : 0 < r) (hη : 0 < η)
    (hηr : (d : ℝ) * η ≤ r / 1000) {y : Rd d}
    (hy : y ∈ HigherDimLFPP.Osc.box 0 B) :
    ‖y - latPt (r / (100 * d))
      (roundLat (r / (100 * d)) (HigherDimLFPP.Osc.gridOf 0 B η y))‖ < r / 2 := by
  let g := HigherDimLFPP.Osc.gridOf 0 B η y
  let z := latPt (r / (100 * d)) (roundLat (r / (100 * d)) g)
  have hg : ‖y - g‖ ≤ (d : ℝ) * η := shellCover_gridOf_dist_le_dim hd B hη hy
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hs : 0 < r / (100 * (d : ℝ)) := by positivity
  have hz : ‖g - z‖ ≤ r / 100 := by
    have h := shellCover_roundLat_dist_le_dim hd hs g
    have heq : (d : ℝ) * (r / (100 * d)) = r / 100 := by field_simp
    exact heq ▸ h
  calc
    ‖y - z‖ = ‖(y - g) + (g - z)‖ := by congr 1; abel
    _ ≤ ‖y - g‖ + ‖g - z‖ := norm_add_le _ _
    _ ≤ (d : ℝ) * η + r / 100 := add_le_add hg hz
    _ ≤ r / 1000 + r / 100 := add_le_add hηr le_rfl
    _ < r / 2 := by linarith

private theorem shellCover_bad_subset (hd : 1 ≤ d) {Ω : Type*} [MeasurableSpace Ω]
    (E : Rd d → ℝ → Set Ω) {L R ε : ℝ} (hL : 0 < L) (hR : 0 < R)
    (hε : 0 < ε) (T : Finset ℤ) (hT : ∀ j ∈ T, j ∈ scaleWin ε R) :
    {ω : Ω | ¬ ∀ y ∈ Metric.ball (0 : Rd d) (L * R), ∃ j ∈ T,
      ∃ k : Fin d → ℤ,
        ‖y - latPt ((64 : ℝ) ^ j / (100 * d)) k‖ < (64 : ℝ) ^ j / 2 ∧
        ω ∈ E (latPt ((64 : ℝ) ^ j / (100 * d)) k) ((64 : ℝ) ^ j)} ⊆
      ⋃ g ∈ HigherDimLFPP.Osc.grid (0 : Rd d) ((L + 1) * R)
        (ε ^ 2 * R / (1000 * d)),
        {ω | ∀ j ∈ T, ω ∉ E
          (latPt (((64 : ℝ) ^ j) / (100 * d))
            (roundLat (((64 : ℝ) ^ j) / (100 * d)) g)) ((64 : ℝ) ^ j)} := by
  classical
  intro ω hbad
  push Not at hbad
  obtain ⟨y, hy, hno⟩ := hbad
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  let η : ℝ := ε ^ 2 * R / (1000 * d)
  have hη : 0 < η := by dsimp [η]; positivity
  let B : ℝ := (L + 1) * R
  have hybox : y ∈ HigherDimLFPP.Osc.box 0 B := shellCover_ball_mem_box hL hR hy
  let g := HigherDimLFPP.Osc.gridOf 0 B η y
  have hg : g ∈ HigherDimLFPP.Osc.grid 0 B η :=
    HigherDimLFPP.Osc.gridOf_mem_grid 0 hη hybox
  refine mem_biUnion hg ?_
  intro j hj hjE
  have hscale := (hT j hj).1
  have hr : 0 < (64 : ℝ) ^ j := zpow_pos (by norm_num) _
  have hηr : (d : ℝ) * η ≤ ((64 : ℝ) ^ j) / 1000 := by
    have heq : (d : ℝ) * η = ε ^ 2 * R / 1000 := by
      dsimp [η]
      field_simp
    rw [heq]
    exact div_le_div_of_nonneg_right hscale (by norm_num)
  have hnear := shellCover_near hd hr hη hηr hybox
  exact (hno j hj (roundLat (((64 : ℝ) ^ j) / (100 * d)) g)) hnear hjE

private theorem shellCover_grid_card (hd : 1 ≤ d) {L R ε : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ((HigherDimLFPP.Osc.grid (0 : Rd d) ((L + 1) * R)
      (ε ^ 2 * R / (1000 * d))).card : ℝ) * ε ^ (2 * d) ≤
      (4000 * (d : ℝ) * (L + 1)) ^ d := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hdone : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hLp : 0 < L + 1 := by linarith
  have hε2 : 0 < ε ^ 2 := pow_pos hε 2
  have hε2one : ε ^ 2 ≤ 1 := pow_le_one₀ hε.le hε1
  have hη : 0 < ε ^ 2 * R / (1000 * (d : ℝ)) := by positivity
  have hB : 0 ≤ (L + 1) * R := by positivity
  have hcard := HigherDimLFPP.Osc.card_grid_le (0 : Rd d) hB hη
  have heq : (2 * ((L + 1) * R) / (ε ^ 2 * R / (1000 * d))) * ε ^ 2 =
      2000 * (d : ℝ) * (L + 1) := by field_simp; ring
  have hbase :
      (2 * ((L + 1) * R) / (ε ^ 2 * R / (1000 * d)) + 1) * ε ^ 2 ≤
        4000 * (d : ℝ) * (L + 1) := by
    rw [add_mul, one_mul, heq]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ d by positivity)
      (show (0 : ℝ) ≤ L + 1 by positivity)]
  have hpow := pow_le_pow_left₀
    (show 0 ≤ (2 * ((L + 1) * R) / (ε ^ 2 * R / (1000 * d)) + 1) * ε ^ 2 by positivity)
    hbase d
  calc
    ((HigherDimLFPP.Osc.grid (0 : Rd d) ((L + 1) * R)
      (ε ^ 2 * R / (1000 * d))).card : ℝ) * ε ^ (2 * d) =
        ((HigherDimLFPP.Osc.grid (0 : Rd d) ((L + 1) * R)
          (ε ^ 2 * R / (1000 * d))).card : ℝ) * (ε ^ 2) ^ d := by rw [pow_mul]
    _ ≤ (2 * ((L + 1) * R) / (ε ^ 2 * R / (1000 * d)) + 1) ^ d * (ε ^ 2) ^ d :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = ((2 * ((L + 1) * R) / (ε ^ 2 * R / (1000 * d)) + 1) * ε ^ 2) ^ d :=
      (mul_pow _ _ _).symm
    _ ≤ _ := hpow

/-- [S] Lemma 5.2, using the shell event tail of Lemma A.1. -/
theorem shellCover (hd : 1 ≤ d) : ShellCover d := by
  intro ρ s hρ hs
  let A : ℝ := (2 * (d : ℝ) + s + 1) * Real.log 64 / ρ
  have hA : 0 < A := by
    dsimp [A]
    have hlog : 0 < Real.log (64 : ℝ) := Real.log_pos (by norm_num)
    positivity
  obtain ⟨p, hp, H⟩ := lemmaA1 hd (1 / 4) 8 (1 / 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) A (1 / 2) hA (by norm_num) (by norm_num)
  refine ⟨p, hp, ?_⟩
  intro L C₀ hL hC₀
  let K : ℝ := 4000 * (d : ℝ) * (L + 1)
  let C : ℝ := K ^ d * Real.exp (A * C₀)
  let ε₁ : ℝ := Real.exp (-((C₀ + 1) * Real.log 64 / ρ))
  refine ⟨C, ε₁, Real.exp_pos _, ?_⟩
  intro Ω _ P _ h hh E hE R ε hR hε hεsmall T hTwin hcount hprob
  have hTcard : 0 < T.card := shellCover_count_pos hρ hε hεsmall hcount
  have hT : T.Nonempty := Finset.card_pos.mp hTcard
  have hlog64 : 0 < Real.log (64 : ℝ) := Real.log_pos (by norm_num)
  have hε1 : ε ≤ 1 := by
    have hneg : -((C₀ + 1) * Real.log 64 / ρ) ≤ 0 := by
      apply neg_nonpos.mpr
      positivity
    have hexp := Real.exp_le_exp.mpr hneg
    rw [Real.exp_zero] at hexp
    exact (le_of_lt hεsmall).trans hexp
  let η : ℝ := ε ^ 2 * R / (1000 * d)
  let G : Finset (Rd d) := HigherDimLFPP.Osc.grid 0 ((L + 1) * R) η
  let F : Rd d → Set Ω := fun g => {ω | ∀ j ∈ T, ω ∉ E
    (latPt (((64 : ℝ) ^ j) / (100 * d))
      (roundLat (((64 : ℝ) ^ j) / (100 * d)) g)) ((64 : ℝ) ^ j)}
  have hsub : {ω : Ω | ¬ ∀ x ∈ Metric.ball (0 : Rd d) (L * R), ∃ j ∈ T,
      ∃ k : Fin d → ℤ,
        ‖x - latPt ((64 : ℝ) ^ j / (100 * d)) k‖ < (64 : ℝ) ^ j / 2 ∧
        ω ∈ E (latPt ((64 : ℝ) ^ j / (100 * d)) k) ((64 : ℝ) ^ j)} ⊆
      ⋃ g ∈ G, F g := shellCover_bad_subset hd E hL hR hε T hTwin
  have hpoint : ∀ g ∈ G, P (F g) ≤ ENNReal.ofReal (Real.exp (-A * T.card)) := by
    intro g _
    exact shellCover_point_tail hd hp H P h hh E hE g T hT hprob
  have hgrid : (G.card : ℝ) * ε ^ (2 * d) ≤ K ^ d :=
    shellCover_grid_card hd hL hR hε hε1
  have hreal : (G.card : ℝ) * Real.exp (-A * T.card) ≤ C * ε ^ s := by
    exact shellCover_combine (d := d) hρ hs hε hε1 (Nat.cast_nonneg _)
      hgrid hcount
  calc
    P _ ≤ P (⋃ g ∈ G, F g) := measure_mono hsub
    _ ≤ ∑ g ∈ G, P (F g) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _g ∈ G, ENNReal.ofReal (Real.exp (-A * T.card)) :=
      Finset.sum_le_sum hpoint
    _ = ENNReal.ofReal ((G.card : ℝ) * Real.exp (-A * T.card)) := by
      rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (C * ε ^ s) := ENNReal.ofReal_le_ofReal hreal

end HigherDimLQGMetric
