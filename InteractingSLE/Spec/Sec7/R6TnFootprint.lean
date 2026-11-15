/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RelTransHull
import InteractingSLE.Spec.Sec7.SideHeightBoxSingle
import InteractingSLE.Foundations.Loewner.YuanCorollary13

/-!
# R.6: the left force-mark landing is the least real point of the closed hull

PROVE-R6-TWO, continuation. This boundary-correspondence statement follows
from the landed hull-image interval theorem, the slit bound, continuity of
the inverse boundary extension and its bounded displacement from identity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMapInv)

namespace InteractingSLE.Sec7.R6Tn

open WangWu (chartAL chartAR)

/-- On the original-real side of the left force mark, the inverse boundary
extension is real and nonpositive, including at the mark itself. -/
theorem left_boundary_real_nonpos {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {q x : ℝ} (hq : 0 ≤ q) (hx : x ≤ chartAL W q) :
    (extendFrom H (fwdMapInv W q) (x : ℂ)).im = 0 ∧
      (extendFrom H (fwdMapInv W q) (x : ℂ)).re ≤ 0 := by
  by_contra h
  have hlt := SideHeightBox.neg_rightImg_sub_lt_of_extendFrom
    (hη.hasBdryLimits hW hW0 hq) hW hW0 hq h
  exact (not_lt_of_ge hx) hlt

/-- The left force-mark landing is the least real point of the closed
curve-generated Loewner hull. No simplicity of the trace is assumed. -/
theorem left_force_landing_isLeast {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {q : ℝ} (hq : 0 < q) (hgap : chartAL W q < chartAR W q) :
    IsLeast {y : ℝ | (y : ℂ) ∈ closure (fwdHull W q)}
      (extendFrom H (fwdMapInv W q) (chartAL W q : ℂ)).re := by
  let F : ℂ → ℂ := extendFrom H (fwdMapInv W q)
  let a : ℝ := chartAL W q
  let f : ℝ → ℝ := fun x => (F x).re
  have hreal : ∀ x ≤ a, (F x).im = 0 := fun x hx =>
    (left_boundary_real_nonpos hη hW hW0 hq.le hx).1
  have hmem : F a ∈ closure (fwdHull W q) :=
    Supp8.RelTrans.Icc_subset_hullImage hη hW hW0 hq hgap ⟨le_rfl, hgap.le⟩
  have hFa : ((f a : ℝ) : ℂ) = F a := Complex.ext (by simp [f]) (by simp [hreal a le_rfl])
  refine ⟨by change ((f a : ℝ) : ℂ) ∈ closure (fwdHull W q); rwa [hFa], ?_⟩
  intro y hy
  change f a ≤ y
  by_contra h
  have hylt : y < f a := not_le.1 h
  obtain ⟨C, hC⟩ := hη.exists_norm_extendFrom_sub_le hW hW0 hq.le
  have hbound : ∀ x : ℝ, f x ≤ x + C := by
    intro x
    have hb := hC (x : ℂ) (show (x : ℂ) ∈ Hbar from by simp [QuantumZipper.Hbar])
    have hr := Complex.re_le_norm (F x - (x : ℂ))
    change (F x).re ≤ x + C
    simp only [Complex.sub_re, Complex.ofReal_re] at hr
    linarith
  let b : ℝ := min (a - 1) (y - C - 1)
  have hba : b ≤ a := (min_le_left _ _).trans (by linarith)
  have hbY : f b < y := by
    have h1 := hbound b
    have h2 : b ≤ y - C - 1 := min_le_right _ _
    linarith
  have hFc : ContinuousOn F Hbar := (hη.hasBdryLimits hW hW0 hq.le).continuousOn
  have hfc : Continuous f := Complex.continuous_re.comp
    (hFc.comp_continuous Complex.continuous_ofReal fun x => by simp [QuantumZipper.Hbar])
  obtain ⟨x, hx, hxy⟩ := intermediate_value_Icc hba hfc.continuousOn ⟨hbY.le, hylt.le⟩
  have hxa : x < a := lt_of_le_of_ne hx.2 fun he => hylt.ne (he ▸ hxy).symm
  have hFx : F x = (y : ℂ) := Complex.ext (by simpa [f] using hxy) (by simp [hreal x hx.2])
  have hy' : F x ∈ closure (fwdHull W q) := by rw [hFx]; exact hy
  exact Supp8.RelTrans.extendFrom_notMem_closure_of_lt_chartAL hη hW hW0 hq.le hxa hy'

end InteractingSLE.Sec7.R6Tn
