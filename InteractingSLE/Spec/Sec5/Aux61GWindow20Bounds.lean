/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWindow20Rational

/-! # A transition limit and physical clearance imply landing admission -/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric MeasureTheory
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec5.Aux61GWindow20
open WangWu Aux61SlitW Aux61GWindow17 Aux61GInst Aux61Cpt LawUnique
universe u

/-- At a certified record, a positive finite counterflow transition limit
and a physical landing in H off the retained prefix give a rational
landing test containing the given chart coordinate. -/
theorem exists_landRecords_of_transition (S : SourceSetting.{u}) (t : GoodTime S)
    {r : SourceRecord S.nL S.nR} (hr : r ∈ certifiedRecords S t) {y x : ℝ}
    (hx : 0 < x) (hpole : boundedInverse (recordChart S t r) (y : ℂ) ≠ 1)
    (hphys : recPhys S t r (y : ℂ) ∈ H)
    (hclear : 0 < infDist (recPhys S t r (y : ℂ)) (recPrefix S t r))
    (htrans : Tendsto (fun z => revChart (recDrv S r) (rationalTime S.s) (recPhys S t r z))
      (𝓝[H] (y : ℂ)) (𝓝 (x : ℂ))) :
    ∃ L : LandParam, |y - L.1.1| < L.1.2.1 ∧ r ∈ landRecords S t L := by
  have hF : ContinuousAt (fun a : ℝ => boundedInverse (recordChart S t r) (a : ℂ)) y :=
    ((recordChart_extension S t hr).2 (y : ℂ) (ofReal_mem_Hbar y)).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨Complex.continuous_ofReal.continuousAt,
        Eventually.of_forall fun a => ofReal_mem_Hbar a⟩)
  have hP : ContinuousAt (fun a : ℝ => recPhys S t r (a : ℂ)) y :=
    (continuousAt_cayleyInv hpole).comp (f := fun a : ℝ =>
      boundedInverse (recordChart S t r) (a : ℂ)) hF
  let d : ℝ := min x (min ‖boundedInverse (recordChart S t r) (y : ℂ) - 1‖
    (min (recPhys S t r (y : ℂ)).im (infDist (recPhys S t r (y : ℂ)) (recPrefix S t r)))) / 2
  have hp : 0 < ‖boundedInverse (recordChart S t r) (y : ℂ) - 1‖ :=
    norm_pos_iff.2 (sub_ne_zero.2 hpole)
  have hIm : 0 < (recPhys S t r (y : ℂ)).im := hphys
  have hd : 0 < d := half_pos (lt_min hx (lt_min hp (lt_min hIm hclear)))
  have hdx : d < x := (half_lt_self (lt_min hx (lt_min hp (lt_min hIm hclear)))).trans_le
    (min_le_left _ _)
  have hdF : d < ‖boundedInverse (recordChart S t r) (y : ℂ) - 1‖ :=
    (half_lt_self (lt_min hx (lt_min hp (lt_min hIm hclear)))).trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
  have hdP : d < (recPhys S t r (y : ℂ)).im :=
    (half_lt_self (lt_min hx (lt_min hp (lt_min hIm hclear)))).trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hdK : d < infDist (recPhys S t r (y : ℂ)) (recPrefix S t r) :=
    (half_lt_self (lt_min hx (lt_min hp (lt_min hIm hclear)))).trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hev : ∀ᶠ a : ℝ in 𝓝 y,
      d ≤ ‖boundedInverse (recordChart S t r) (a : ℂ) - 1‖ ∧
      d ≤ (recPhys S t r (a : ℂ)).im ∧
      d ≤ infDist (recPhys S t r (a : ℂ)) (recPrefix S t r) := by
    filter_upwards [(tendsto_order.1 (hF.sub_const 1).norm).1 d hdF,
      (tendsto_order.1 (Complex.continuous_im.continuousAt.comp hP)).1 d hdP,
      (tendsto_order.1 ((continuous_infDist_pt _).continuousAt.comp hP)).1 d hdK]
      with a h₁ h₂ h₃
    exact ⟨h₁.le, h₂.le, h₃.le⟩
  obtain ⟨ε₁, hε₁, hreal⟩ := Metric.mem_nhds_iff.1 hev
  have hevH : ∀ᶠ z in 𝓝[H] (y : ℂ),
      ‖revChart (recDrv S r) (rationalTime S.s) (recPhys S t r z)‖ ≤ ‖(x : ℂ)‖ + 1 ∧
      d ≤ (revChart (recDrv S r) (rationalTime S.s) (recPhys S t r z)).re := by
    filter_upwards [(tendsto_order.1 htrans.norm).2 (‖(x : ℂ)‖ + 1) (by linarith),
      (tendsto_order.1 (Complex.continuous_re.continuousAt.tendsto.comp htrans)).1 d
        (by simpa only [Complex.ofReal_re] using hdx)] with z h₁ h₂
    exact ⟨h₁.le, h₂.le⟩
  obtain ⟨ε₂, hε₂, hupper⟩ := Metric.mem_nhdsWithin_iff.1 hevH
  obtain ⟨L, hy, -, hL⟩ := exists_landParam_of_bounds S t r (lt_min hε₁ hε₂) hd
    (fun z hz => hupper ⟨ball_subset_ball (min_le_right _ _) hz.2, hz.1⟩)
    (fun a ha => hreal (by
      rw [mem_ball, Real.dist_eq]
      exact ha.trans_le (min_le_left _ _)))
  exact ⟨L, hy, hr, hL⟩

end InteractingSLE.Sec5.Aux61GWindow20
