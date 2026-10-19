import GaussianLQG.Uniform.Limit.Basic

/-!
# Passage to the limit (blueprint A.7), part 2: the normalizing constants

Blueprint A.7, item 3 (audit A5-02, step 3; Route U step U16 of
`planning/audits/B1-S6-feasibility.md`): first moments of the Hölder constant and of the inverse
separated distance of `X := c⁻¹ D^ε_h` pin the LFPP median `𝔞_ε = LQGMetric.aEps ξ ε` (the lower
median of the left–right crossing distance `LQGMetric.lfppCross ξ ε` under `normGFFLaw`) between
two multiples of `c` that depend only on the moment bound.

On the a.s. event where `h*_ε` is continuous, with `D₂ := B̄(0, 2)` (`normDisk`, which contains
both vertical sides of the unit square), the crossing distance `𝔠 = lfppCross ξ ε h` satisfies
`I_X(D₂, 1) ≤ c⁻¹ 𝔠 ≤ X(0, 1) ≤ A_X(D₂)` (`sepInf_normDisk_le`, `lfppCross_le_lfppDist_zero_one`,
`ofReal_le_holderConst_normDisk`), because every pair (left side, right side) is `1`-separated.
Markov's inequality for `A_X(D₂)` and for `I_X(D₂, 1)⁻¹` then gives (`aEps_bounds`)

  `(4B)⁻¹ c ≤ 𝔞_ε ≤ 2B c`, where `B := C.toReal + 1` and `C` bounds both first moments.

No identification of `𝔞_ε` with another normalization and no regularity of the law of the
crossing distance is used (blueprint A.7, final remark; erratum E15).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace GaussianLQG
namespace UniformLimit

open LQGMetric

/-! ## Geometry of the unit square -/

/-- The compact set used to compare the normalizations: the closed disk `B̄(0, 2)`, which contains
both vertical sides of the unit square. -/
def normDisk : Set ℂ := Metric.closedBall (0 : ℂ) 2

theorem isCompact_normDisk : IsCompact normDisk := isCompact_closedBall 0 2

theorem mem_normDisk_of_mem_leftSide {z : ℂ} (hz : z ∈ leftSide) : z ∈ normDisk := by
  rw [normDisk, Metric.mem_closedBall, dist_zero_right]
  exact LFPP.norm_le_two_of_side (c := 0) (by simp) hz

theorem mem_normDisk_of_mem_rightSide {z : ℂ} (hz : z ∈ rightSide) : z ∈ normDisk := by
  rw [normDisk, Metric.mem_closedBall, dist_zero_right]
  exact LFPP.norm_le_two_of_side (c := 1) (by simp) hz

/-- A point of the left side and a point of the right side are at distance at least `1`. -/
theorem one_le_norm_sub_of_sides {z w : ℂ} (hz : z ∈ leftSide) (hw : w ∈ rightSide) :
    1 ≤ ‖z - w‖ := by
  have h := Complex.abs_re_le_norm (z - w)
  rw [Complex.sub_re, hz.1, hw.1] at h
  norm_num at h
  exact h

theorem zero_mem_leftSide : (0 : ℂ) ∈ leftSide := ⟨by simp, by simp, by simp⟩

theorem one_mem_rightSide : (1 : ℂ) ∈ rightSide := ⟨by simp, by simp, by simp⟩

/-! ## Deterministic comparisons (on the event where `h*_ε` is continuous) -/

section Deterministic

variable {ξ ε : ℝ} {g : DistC}

theorem lfppDistE_ne_top (hg : Continuous (heatMollify ε g)) (z w : ℂ) :
    lfppDistE ξ ε g z w ≠ ⊤ := by
  rw [LFPP.lfppDistE_eq_lfppDOn]
  exact LFPP.lfppD_ne_top hg z w

/-- The left–right crossing distance is at most `D^ε_h(0, 1)`. -/
theorem lfppCross_le_lfppDist_zero_one (hg : Continuous (heatMollify ε g)) :
    lfppCross ξ ε g ≤ lfppDist ξ ε g (0, 1) :=
  ENNReal.toReal_mono (lfppDistE_ne_top hg 0 1)
    (iInf₂_le_of_le 0 zero_mem_leftSide (iInf₂_le 1 one_mem_rightSide))

/-- `a D^ε_h(0, 1) ≤ A_{a D^ε_h}(D₂)`, since `|0 - 1| = 1`. -/
theorem ofReal_le_holderConst_normDisk (a : ℝ) :
    ENNReal.ofReal (a * lfppDist ξ ε g (0, 1)) ≤
      holderConst (fun q => a * lfppDist ξ ε g q) normDisk := by
  have h := ofReal_le_holderConst (d := fun q => a * lfppDist ξ ε g q)
    (mem_normDisk_of_mem_leftSide zero_mem_leftSide)
    (mem_normDisk_of_mem_rightSide one_mem_rightSide) zero_ne_one
  have e : ‖(0 : ℂ) - 1‖ ^ (1 / 2 : ℝ) = 1 := by
    rw [zero_sub, norm_neg, norm_one, Real.one_rpow]
  rw [e, div_one] at h
  exact h

/-- `I_{a D^ε_h}(D₂, 1) ≤ a 𝔠`: every pair (left side, right side) is `1`-separated. -/
theorem sepInf_normDisk_le (hg : Continuous (heatMollify ε g)) {a : ℝ} (ha : 0 < a) :
    sepInf (fun q => a * lfppDist ξ ε g q) normDisk 1 ≤ ENNReal.ofReal (a * lfppCross ξ ε g) := by
  set m := ⨅ z ∈ leftSide, ⨅ w ∈ rightSide, lfppDistE ξ ε g z w with hm
  have hmtop : m ≠ ⊤ := ne_top_of_le_ne_top (lfppDistE_ne_top hg 0 1)
    (iInf₂_le_of_le 0 zero_mem_leftSide (iInf₂_le 1 one_mem_rightSide))
  have hcross : lfppCross ξ ε g = m.toReal := rfl
  have ha0 : ENNReal.ofReal a ≠ 0 := (ENNReal.ofReal_pos.2 ha).ne'
  rw [hcross, ENNReal.ofReal_mul ha.le, ENNReal.ofReal_toReal hmtop, hm]
  simp_rw [ENNReal.mul_iInf_of_ne ha0 ENNReal.ofReal_ne_top]
  refine le_iInf₂ fun z hz => le_iInf₂ fun w hw => ?_
  refine (sepInf_le_ofReal (mem_normDisk_of_mem_leftSide hz) (mem_normDisk_of_mem_rightSide hw)
    (one_le_norm_sub_of_sides hz hw)).trans_eq ?_
  show ENNReal.ofReal (a * (lfppDistE ξ ε g z w).toReal) = _
  rw [ENNReal.ofReal_mul ha.le, ENNReal.ofReal_toReal (lfppDistE_ne_top hg z w)]

end Deterministic

/-! ## Bounds on `𝔞_ε` -/

theorem ofReal_div_two_mul_self {B : ℝ} (hB : 0 < B) :
    ENNReal.ofReal B / ENNReal.ofReal (2 * B) = 2⁻¹ := by
  have e : B / (2 * B) = (2 : ℝ)⁻¹ := by field_simp
  rw [← ENNReal.ofReal_div_of_pos (by positivity), e, ENNReal.ofReal_inv_of_pos two_pos,
    ENNReal.ofReal_ofNat]

theorem ofReal_mul_inv_four_mul_self_lt {B : ℝ} (hB : 0 < B) :
    ENNReal.ofReal B * ENNReal.ofReal (4 * B)⁻¹ < 2⁻¹ := by
  have e : B * (4 * B)⁻¹ = (4 : ℝ)⁻¹ := by field_simp
  rw [← ENNReal.ofReal_mul hB.le, e, ENNReal.ofReal_inv_of_pos four_pos, ENNReal.ofReal_ofNat]
  exact ENNReal.inv_lt_inv.2 (by norm_num)

variable {ξ ε : ℝ}

/-- **Blueprint A.7, item 3**: if the first moments of `A_X(D₂)` and `I_X(D₂, 1)⁻¹` for
`X = c⁻¹ D^ε_h` are at most `C < ∞` under `normGFFLaw`, then
`(4B)⁻¹ c ≤ 𝔞_ε ≤ 2B c` with `B = C.toReal + 1`. -/
theorem aEps_bounds {c : ℝ} (hε : 0 < ε) (hc : 0 < c) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hA : ∫⁻ g, holderConst (fun q => c⁻¹ * lfppDist ξ ε g q) normDisk ∂normGFFLaw ≤ C)
    (hI : ∫⁻ g, (sepInf (fun q => c⁻¹ * lfppDist ξ ε g q) normDisk 1)⁻¹ ∂normGFFLaw ≤ C) :
    (4 * (C.toReal + 1))⁻¹ * c ≤ aEps ξ ε ∧ aEps ξ ε ≤ 2 * (C.toReal + 1) * c := by
  have := isProbabilityMeasure_normGFFLaw
  set B : ℝ := C.toReal + 1
  have hB : 0 < B := by positivity
  have hCB : C ≤ ENNReal.ofReal B := by
    rw [← ENNReal.ofReal_toReal hC]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hcont := LFPP.ae_continuous_heatMollify_normGFFLaw hε.ne'
  set M : Set ℝ := {m | (2 : ℝ≥0∞)⁻¹ ≤ normGFFLaw {g | lfppCross ξ ε g ≤ m}}
  have haEps : aEps ξ ε = sInf M := rfl
  -- the upper bound: `2B c` is a candidate median
  have hup : 2 * B * c ∈ M := by
    have h1 : normGFFLaw {g | ¬ lfppCross ξ ε g ≤ 2 * B * c} ≤ 2⁻¹ := by
      calc normGFFLaw {g | ¬ lfppCross ξ ε g ≤ 2 * B * c}
          ≤ normGFFLaw {g | ENNReal.ofReal (2 * B) ≤
              holderConst (fun q => c⁻¹ * lfppDist ξ ε g q) normDisk} := by
            refine measure_mono_ae ?_
            filter_upwards [hcont] with g hg hgt
            have hgt' : 2 * B * c < lfppCross ξ ε g := not_le.1 hgt
            show ENNReal.ofReal (2 * B) ≤ holderConst (fun q => c⁻¹ * lfppDist ξ ε g q) normDisk
            refine le_trans (ENNReal.ofReal_le_ofReal ?_) (ofReal_le_holderConst_normDisk c⁻¹)
            have h0 := lfppCross_le_lfppDist_zero_one (ξ := ξ) hg
            have hci : 0 < c⁻¹ := inv_pos.2 hc
            calc 2 * B = c⁻¹ * (2 * B * c) := by field_simp
              _ ≤ c⁻¹ * lfppCross ξ ε g := by gcongr
              _ ≤ c⁻¹ * lfppDist ξ ε g (0, 1) := by gcongr
        _ ≤ (∫⁻ g, holderConst (fun q => c⁻¹ * lfppDist ξ ε g q) normDisk ∂normGFFLaw) /
              ENNReal.ofReal (2 * B) :=
            meas_ge_le_lintegral_div (aemeasurable_holderConst_lfppDist hε.ne' _ _)
              (ENNReal.ofReal_pos.2 (by positivity)).ne' ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal B / ENNReal.ofReal (2 * B) := by gcongr; exact hA.trans hCB
        _ = 2⁻¹ := ofReal_div_two_mul_self hB
    have h2 : (1 : ℝ≥0∞) ≤ normGFFLaw {g | lfppCross ξ ε g ≤ 2 * B * c} +
        normGFFLaw {g | ¬ lfppCross ξ ε g ≤ 2 * B * c} := by
      rw [← measure_univ (μ := normGFFLaw)]
      refine le_trans (measure_mono fun g _ => ?_) (measure_union_le _ _)
      by_cases h : lfppCross ξ ε g ≤ 2 * B * c
      · exact Or.inl h
      · exact Or.inr h
    show (2 : ℝ≥0∞)⁻¹ ≤ normGFFLaw {g | lfppCross ξ ε g ≤ 2 * B * c}
    calc (2 : ℝ≥0∞)⁻¹ = 1 - 2⁻¹ := ENNReal.one_sub_inv_two.symm
      _ ≤ normGFFLaw {g | lfppCross ξ ε g ≤ 2 * B * c} := by
        rw [tsub_le_iff_right]
        exact h2.trans (add_le_add le_rfl h1)
  -- the lower bound: no candidate median is below `(4B)⁻¹ c`
  have hlow : ∀ m ∈ M, (4 * B)⁻¹ * c ≤ m := by
    intro m hm
    by_contra hlt
    have hlt' : m < (4 * B)⁻¹ * c := not_le.1 hlt
    have h1 : normGFFLaw {g | lfppCross ξ ε g ≤ m} < 2⁻¹ := by
      calc normGFFLaw {g | lfppCross ξ ε g ≤ m}
          ≤ normGFFLaw {g | (ENNReal.ofReal (4 * B)⁻¹)⁻¹ ≤
              (sepInf (fun q => c⁻¹ * lfppDist ξ ε g q) normDisk 1)⁻¹} := by
            refine measure_mono_ae ?_
            filter_upwards [hcont] with g hg hle
            have hle' : lfppCross ξ ε g ≤ m := hle
            show (ENNReal.ofReal (4 * B)⁻¹)⁻¹ ≤
              (sepInf (fun q => c⁻¹ * lfppDist ξ ε g q) normDisk 1)⁻¹
            refine ENNReal.inv_le_inv.2 ((sepInf_normDisk_le hg (inv_pos.2 hc)).trans
              (ENNReal.ofReal_le_ofReal ?_))
            have hci : 0 < c⁻¹ := inv_pos.2 hc
            calc c⁻¹ * lfppCross ξ ε g ≤ c⁻¹ * m := by gcongr
              _ ≤ c⁻¹ * ((4 * B)⁻¹ * c) := by gcongr
              _ = (4 * B)⁻¹ := by field_simp
        _ ≤ (∫⁻ g, (sepInf (fun q => c⁻¹ * lfppDist ξ ε g q) normDisk 1)⁻¹ ∂normGFFLaw) /
              (ENNReal.ofReal (4 * B)⁻¹)⁻¹ :=
            meas_ge_le_lintegral_div (aemeasurable_sepInf_lfppDist hε.ne' _ _ _).inv
              (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)
              (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (by positivity)).ne')
        _ ≤ ENNReal.ofReal B / (ENNReal.ofReal (4 * B)⁻¹)⁻¹ := by gcongr; exact hI.trans hCB
        _ = ENNReal.ofReal B * ENNReal.ofReal (4 * B)⁻¹ := by rw [div_eq_mul_inv, inv_inv]
        _ < 2⁻¹ := ofReal_mul_inv_four_mul_self_lt hB
    exact absurd hm (not_le.2 h1)
  refine ⟨?_, ?_⟩
  · rw [haEps]
    exact le_csInf ⟨_, hup⟩ hlow
  · rw [haEps]
    exact csInf_le ⟨_, hlow⟩ hup

end UniformLimit
end GaussianLQG
