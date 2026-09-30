import QuantumZipper.Proofs.Zipper.SWCoreA5Class
import QuantumZipper.Proofs.Analysis.Pushforward

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-A5-PULL: the pulled-back test function `f ∘ ψ⁻¹`, uniformly over an area class

Helper for SWC-A5. For `ψ ∈ AreaClass a b c d ρ M m` and `f` continuous with compact support in
`interior K`, `K = rectC a b c d`:

* `pullTest_equicont`: `f ∘ ψ⁻¹` (extended by `0`) is equicontinuous over the class;
* `pullTest_ne_zero`: on its support, `ψ⁻¹ w ∈ tsupport f`, `‖w‖ ≤ M`, `ρ ≤ Im w` and
  `m ≤ ‖ψ'(ψ⁻¹ w)‖ ≤ C`;
* `pullScale_logb_equicont`: `log₂ ‖ψ'(ψ⁻¹ ·)‖` is equicontinuous on that support;
* `lintegral_pull`: the change of variables `∫⁻_K ‖ψ'‖² G∘ψ = ∫⁻_{ψ(K)} G`.

Own elementary proofs from `SWCoreA5Class` (quantitative inverse function theorem) and mathlib's
change of variables formula `lintegral_image_eq_lintegral_abs_det_fderiv_mul`.
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal

namespace QuantumZipper
namespace SWCore

open scoped Classical in
/-- The test function `f ∘ ψ⁻¹` on `ψ(K)`, extended by `0`. -/
noncomputable def pullTest (ψ : ℂ → ℂ) (K : Set ℂ) (f : ℂ → ℝ) : ℂ → ℝ :=
  fun w => if w ∈ ψ '' K then f (Function.invFunOn ψ K w) else 0
/-- The scale `|ψ'(ψ⁻¹ w)|`. -/
noncomputable def pullScale (ψ : ℂ → ℂ) (K : Set ℂ) : ℂ → ℝ := fun w => ‖deriv ψ (Function.invFunOn ψ K w)‖

theorem swA5_invFunOn_image {a b c d ρ M m : ℝ} (hρ : 0 < ρ) {ψ : ℂ → ℂ}
    (hψ : ψ ∈ AreaClass a b c d ρ M m) {z : ℂ} (hz : z ∈ rectC a b c d) :
    Function.invFunOn ψ (rectC a b c d) (ψ z) = z :=
  (hψ.2.1.mono (self_subset_thickening hρ _)).leftInvOn_invFunOn hz

theorem swA5_pullTest_image {a b c d ρ M m : ℝ} (hρ : 0 < ρ) {ψ : ℂ → ℂ}
    (hψ : ψ ∈ AreaClass a b c d ρ M m) {z : ℂ} (hz : z ∈ rectC a b c d) (f : ℂ → ℝ) :
    pullTest ψ (rectC a b c d) f (ψ z) = f z := by
  unfold pullTest
  rw [if_pos (mem_image_of_mem ψ hz), swA5_invFunOn_image hρ hψ hz]

theorem swA5_pullTest_ne_zero_mem {ψ : ℂ → ℂ} {K : Set ℂ} {f : ℂ → ℝ} {w : ℂ}
    (hw : pullTest ψ K f w ≠ 0) :
    Function.invFunOn ψ K w ∈ K ∧ ψ (Function.invFunOn ψ K w) = w ∧
      f (Function.invFunOn ψ K w) ≠ 0 := by
  unfold pullTest at hw
  split_ifs at hw with h
  · exact ⟨Function.invFunOn_mem h, Function.invFunOn_eq h, hw⟩
  · exact absurd rfl hw

/-- **(F1)** Equicontinuity of `f ∘ ψ⁻¹` over the class. -/
theorem pullTest_equicont {a b c d ρ M m : ℝ} (hρ : 0 < ρ) (hm : 0 < m) {f : ℂ → ℝ}
    (hf : Continuous f) (hfs : HasCompactSupport f)
    (hfK : tsupport f ⊆ interior (rectC a b c d)) :
    ∀ ε > 0, ∃ δ > 0, ∀ ψ ∈ AreaClass a b c d ρ M m, ∀ w w', dist w w' < δ →
      |pullTest ψ (rectC a b c d) f w - pullTest ψ (rectC a b c d) f w'| ≤ ε := by
  intro ε hε
  obtain ⟨η, hη, hU⟩ := Metric.uniformContinuous_iff.1
    (hfs.uniformContinuous_of_continuous hf) ε hε
  obtain ⟨δ0, hδ0, hsub⟩ := hfs.isCompact.exists_cthickening_subset_open isOpen_interior hfK
  obtain ⟨r₁, κ, hr₁, -, hκ, Hb⟩ := areaClass_ball_subset_image (a := a) (b := b) (c := c)
    (d := d) (M := M) hρ hm
  set r := min r₁ (min (η / 2) δ0) with hr
  have hr0 : 0 < r := by positivity
  have hrr₁ : r ≤ r₁ := min_le_left _ _
  have hrη : r ≤ η / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hrδ : r ≤ δ0 := (min_le_right _ _).trans (min_le_right _ _)
  have key : ∀ ψ ∈ AreaClass a b c d ρ M m, ∀ w w', pullTest ψ (rectC a b c d) f w ≠ 0 →
      dist w' w < κ * r →
        |pullTest ψ (rectC a b c d) f w - pullTest ψ (rectC a b c d) f w'| ≤ ε := by
    intro ψ hψ w w' hw hww'
    obtain ⟨hzK, hψz, hfz⟩ := swA5_pullTest_ne_zero_mem hw
    set z := Function.invFunOn ψ (rectC a b c d) w
    have hzs : z ∈ tsupport f := subset_tsupport f (Function.mem_support.2 hfz)
    have hw'b : w' ∈ closedBall (ψ z) (κ * r) := by
      rw [hψz, mem_closedBall]; exact hww'.le
    obtain ⟨z'', hz''b, hψz''⟩ := Hb ψ hψ z hzK r hr0 hrr₁ hw'b
    have hdz : dist z'' z ≤ r := mem_closedBall.1 hz''b
    have hz''K : z'' ∈ rectC a b c d :=
      interior_subset (hsub (mem_cthickening_of_dist_le z'' z δ0 _ hzs (hdz.trans hrδ)))
    rw [← hψz, ← hψz'', swA5_pullTest_image hρ hψ hzK, swA5_pullTest_image hρ hψ hz''K]
    have h := hU (a := z) (b := z'') (by rw [dist_comm]; linarith)
    rw [Real.dist_eq] at h
    exact h.le
  refine ⟨κ * r, by positivity, ?_⟩
  intro ψ hψ w w' hd
  by_cases h1 : pullTest ψ (rectC a b c d) f w ≠ 0
  · exact key ψ hψ w w' h1 (by rw [dist_comm]; exact hd)
  by_cases h2 : pullTest ψ (rectC a b c d) f w' ≠ 0
  · rw [abs_sub_comm]; exact key ψ hψ w' w h2 hd
  simp only [ne_eq, not_not] at h1 h2
  rw [h1, h2]; simp [hε.le]

/-- **(F2)** Properties at points where `f ∘ ψ⁻¹ ≠ 0`. -/
theorem pullTest_ne_zero {a b c d ρ M m : ℝ} (hρ : 0 < ρ) {f : ℂ → ℝ} :
    ∃ C : ℝ, ∀ ψ ∈ AreaClass a b c d ρ M m, ∀ w, pullTest ψ (rectC a b c d) f w ≠ 0 →
      Function.invFunOn ψ (rectC a b c d) w ∈ tsupport f ∧
        ψ (Function.invFunOn ψ (rectC a b c d) w) = w ∧ ‖w‖ ≤ M ∧ ρ ≤ w.im ∧
        m ≤ pullScale ψ (rectC a b c d) w ∧ pullScale ψ (rectC a b c d) w ≤ C := by
  obtain ⟨C, L, r₀, -, -, hr₀, -, H⟩ := areaClass_deriv_bounds (a := a) (b := b) (c := c)
    (d := d) (M := M) (m := m) hρ
  refine ⟨C, ?_⟩
  intro ψ hψ w hw
  obtain ⟨hzK, hψz, hfz⟩ := swA5_pullTest_ne_zero_mem hw
  set z := Function.invFunOn ψ (rectC a b c d) w
  have hzT := self_subset_thickening hρ _ hzK
  have hb := hψ.2.2.1 z hzT
  rw [hψz] at hb
  exact ⟨subset_tsupport f (Function.mem_support.2 hfz), hψz, hb.1, hb.2, hψ.2.2.2 z hzK,
    (H ψ hψ z hzK z (mem_closedBall_self hr₀.le)).2.1⟩

/-- **(F3)** Equicontinuity of `log₂ ‖ψ'(ψ⁻¹ ·)‖` on the support of `f ∘ ψ⁻¹`. -/
theorem pullScale_logb_equicont {a b c d ρ M m : ℝ} (hρ : 0 < ρ) (hm : 0 < m) {f : ℂ → ℝ} :
    ∀ ε > 0, ∃ δ > 0, ∀ ψ ∈ AreaClass a b c d ρ M m, ∀ w w',
      pullTest ψ (rectC a b c d) f w ≠ 0 → pullTest ψ (rectC a b c d) f w' ≠ 0 →
      dist w w' < δ →
        |Real.logb 2 (pullScale ψ (rectC a b c d) w) -
          Real.logb 2 (pullScale ψ (rectC a b c d) w')| ≤ ε := by
  intro ε hε
  obtain ⟨r₁, κ, hr₁, hκ, Hi⟩ := areaClass_inv_modulus (a := a) (b := b) (c := c)
    (d := d) (M := M) hρ hm
  obtain ⟨C, L, r₀, -, hL, hr₀, -, H⟩ := areaClass_deriv_bounds (a := a) (b := b) (c := c)
    (d := d) (M := M) (m := m) hρ
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set r := min r₁ (min r₀ (min (m / (2 * L)) (ε * Real.log 2 * m / (2 * L)))) with hr
  have hr0 : 0 < r := by positivity
  have hrr₁ : r ≤ r₁ := min_le_left _ _
  have hrr₀ : r ≤ r₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hLr : L * r ≤ m / 2 := by
    have h : r ≤ m / (2 * L) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    rw [le_div_iff₀ (by positivity)] at h; linarith
  have hLε : 2 * (L * r) / m ≤ ε * Real.log 2 := by
    have h : r ≤ ε * Real.log 2 * m / (2 * L) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at h
    rw [div_le_iff₀ hm]; linarith
  refine ⟨κ * r, by positivity, ?_⟩
  intro ψ hψ w w' hw hw' hd
  obtain ⟨hzK, hψz, -⟩ := swA5_pullTest_ne_zero_mem hw
  obtain ⟨hz'K, hψz', -⟩ := swA5_pullTest_ne_zero_mem hw'
  set z := Function.invFunOn ψ (rectC a b c d) w
  set z' := Function.invFunOn ψ (rectC a b c d) w'
  have hzz' : ‖z' - z‖ ≤ r := by
    refine Hi ψ hψ z hzK z' (self_subset_thickening hρ _ hz'K) r hr0 hrr₁ ?_
    rw [hψz, hψz', ← dist_eq_norm, dist_comm]; exact hd.le
  have hz'b : z' ∈ closedBall z r₀ := by
    rw [mem_closedBall, dist_eq_norm]; exact hzz'.trans hrr₀
  have hder := (H ψ hψ z hzK z' hz'b).2.2
  have hdiff : |‖deriv ψ z'‖ - ‖deriv ψ z‖| ≤ L * r :=
    (abs_norm_sub_norm_le _ _).trans (hder.trans (by nlinarith [norm_nonneg (z' - z)]))
  have hlog := swA5_abs_log_sub_le hm (hψ.2.2.2 z hzK) hdiff hLr
  show |Real.logb 2 ‖deriv ψ z‖ - Real.logb 2 ‖deriv ψ z'‖| ≤ ε
  rw [Real.logb, Real.logb, ← sub_div, abs_div, abs_of_pos hl2, div_le_iff₀ hl2, abs_sub_comm]
  exact hlog.trans hLε

/-- **(F4)** Change of variables through `ψ` on `K`. -/
theorem lintegral_pull {a b c d ρ M m : ℝ} (hρ : 0 < ρ) {ψ : ℂ → ℂ}
    (hψ : ψ ∈ AreaClass a b c d ρ M m) (G : ℂ → ℝ≥0∞) :
    ∫⁻ z in rectC a b c d, ENNReal.ofReal (‖deriv ψ z‖ ^ 2) * G (ψ z) =
      ∫⁻ w in ψ '' rectC a b c d, G w := by
  have hK : MeasurableSet (rectC a b c d) := by
    have : rectC a b c d = Complex.re ⁻¹' Icc a b ∩ Complex.im ⁻¹' Icc c d := rfl
    rw [this]
    exact (measurableSet_Icc.preimage Complex.measurable_re).inter
      (measurableSet_Icc.preimage Complex.measurable_im)
  have hda : ∀ z ∈ rectC a b c d, DifferentiableAt ℂ ψ z := fun z hz =>
    hψ.1.differentiableAt (isOpen_thickening.mem_nhds (self_subset_thickening hρ _ hz))
  have hfd : ∀ z ∈ rectC a b c d,
      HasFDerivWithinAt ψ (fderiv ℝ ψ z) (rectC a b c d) z := fun z hz =>
    ((hda z hz).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hK hfd
    (hψ.2.1.mono (self_subset_thickening hρ _)) G]
  refine setLIntegral_congr_fun hK (fun z hz => ?_)
  rw [abs_det_fderiv_eq_normSq (hda z hz)]

end SWCore
end QuantumZipper
