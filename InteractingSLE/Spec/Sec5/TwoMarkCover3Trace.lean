/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkCover3Geometry
import InteractingSLE.Spec.Sec5.TwoMarkLocal2Trace
import InteractingSLE.Spec.Zhan.TargetChangeProcessBrownianGood

/-!
# Coverage of the original stopped trace after first-mark separation

For the low-weight two-mark word, a collision of the first mark forces a
collision of the second. The swallowed-interval lemma and trace injectivity
therefore place every visit to the open interval before target separation.
This discharges the coverage hypothesis in the earlier transport theorem.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.TwoMark.Cover3

open Zhan.Retarget

/-- If separation precedes the local horizon, its value is a collision time. -/
theorem right_collision_at_sepTime {κ : ℝ} {nL nR : ℕ}
    {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ}
    {w β : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {T : ℝ≥0∞} (hp : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR β T)
    {j : Fin nR} (hsep : sepTime w (vR j) T < T) :
    vR j (sepTime w (vR j) T).toNNReal = w (sepTime w (vR j) T).toNNReal := by
  have hfin : sepTime w (vR j) T ≠ ⊤ := ne_top_of_lt hsep
  set u := (sepTime w (vR j) T).toNNReal
  have he : (u : ℝ≥0∞) = sepTime w (vR j) T := ENNReal.coe_toNNReal hfin
  have hu : (u : ℝ≥0∞) < T := he.trans_lt hsep
  by_contra hne
  have hpos : ∀ s ≤ u, w s < vR j s := by
    intro s hs
    rcases hs.lt_or_eq with hsu | rfl
    · exact lt_of_lt_sepTime (by rw [← he]; exact ENNReal.coe_lt_coe.2 hsu)
    · exact lt_of_le_of_ne (hp.w_le_vR hu j) (Ne.symm hne)
  have hlt := lt_sepTime_of_forall
    ((hp.continuousOn_vR j).sub hp.continuousOn_w) hu hpos
  rw [he] at hlt
  exact lt_irrefl _ hlt

variable {κ a b r : ℝ} {xL ρL : Fin 0 → ℝ}
  {w β : ℝ≥0 → ℝ} {vL : Fin 0 → ℝ≥0 → ℝ} {vR : Fin 2 → ℝ≥0 → ℝ}
  {T : ℝ≥0∞} {η Γ : ℝ≥0 → ℂ}

/-- Every interval visit of an injective low-weight two-mark trace occurs
no later than the first target separation, including a terminal visit. -/
theorem visit_le_sepTime (hκ4 : κ < 4) (hr : r ≤ κ / 2 - 4) (ha : 0 < a)
    (hp : Sec2.IsSLEPathUpTo κ xL ![a, b] ρL ![r, -r] w vL vR β T)
    (hη : IsGeneratingTrace w T η)
    (hinj : InjOn η {t : ℝ≥0 | (t : ℝ≥0∞) ≤ T}) :
    ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T → ∀ y ∈ Ioo a b,
      η t = (y : ℂ) → (t : ℝ≥0∞) ≤ sepTime w (vR 0) T := by
  intro t ht y hy hvis
  by_contra hlate
  have hst : sepTime w (vR 0) T < (t : ℝ≥0∞) := lt_of_not_ge hlate
  have hsT : sepTime w (vR 0) T < T := hst.trans_le ht
  have he : ((sepTime w (vR 0) T).toNNReal : ℝ≥0∞) = sepTime w (vR 0) T :=
    ENNReal.coe_toNNReal (ne_top_of_lt hst)
  have huT : ((sepTime w (vR 0) T).toNNReal : ℝ≥0∞) < T := he.trans_lt hsT
  have hcol := Local2.far_eq_of_first_eq hκ4 hr hp huT (right_collision_at_sepTime hp hsT)
  have hoff : ∀ s : ℝ≥0, s ≤ (sepTime w (vR 0) T).toNNReal → η s ≠ (y : ℂ) := by
    intro s hs hsy
    have hsT' : (s : ℝ≥0∞) ≤ T := (ENNReal.coe_le_coe.2 hs).trans huT.le
    have hsu : s < t := ENNReal.coe_lt_coe.1
      ((ENNReal.coe_le_coe.2 hs).trans_lt (he.trans_lt hst))
    exact hsu.ne (hinj hsT' ht (hsy.trans hvis.symm))
  exact trace_ne_of_right_collision (j := 1) hp hη (ha.trans hy.1)
    (show y < b from hy.2) huT hcol hoff t ht hvis

/-- The image-ray barrier excludes the original open interval through the
whole stopped horizon. The earlier coverage premise is proved here. -/
theorem avoid_interval_of_image_ray (hκ4 : κ < 4) (hr : r ≤ κ / 2 - 4)
    (ha : 0 < a) (hab : a < b)
    (hp : Sec2.IsSLEPathUpTo κ xL ![a, b] ρL ![r, -r] w vL vR β T)
    (hη : IsGeneratingTrace w T η)
    (hinj : InjOn η {t : ℝ≥0 | (t : ℝ≥0∞) ≤ T})
    (hΓ : IsGeneratingTrace (newDrv a w (vR 0))
      (newHorizon a w (vR 0) (sepTime w (vR 0) T)) Γ)
    (htr : newHorizon a w (vR 0) (sepTime w (vR 0) T) = ⊤ →
      Tendsto (fun s => ‖Γ s‖) atTop atTop)
    (hav : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ newHorizon a w (vR 0) (sepTime w (vR 0) T) →
      ∀ y < Sec7.targetChangeReal a b, Γ s ≠ (y : ℂ)) :
    ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T → ∀ y ∈ Ioo a b, η t ≠ (y : ℂ) :=
  Local2.avoid_interval_of_sep_cover ha hab hp hη hΓ htr hav (visit_le_sepTime hκ4 hr ha hp hη hinj)

end InteractingSLE.Sec5.TwoMark.Cover3
