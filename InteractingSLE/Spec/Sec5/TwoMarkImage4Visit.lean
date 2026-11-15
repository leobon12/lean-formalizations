/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkImage4Endpoint
import InteractingSLE.Spec.Sec5.TwoMarkCover3Trace

/-!
# Image-trace witnesses at a possible interval visit

Coverage places every possible interval visit before first separation. At
that finite time the original trace ends away from the new target. The
preceding deterministic construction therefore supplies the image trace,
its finite horizon, injectivity and endpoint without an image trace premise.
The stochastic image evolution and stopped barrier remain separate inputs.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.TwoMark.Image4

open Zhan.Retarget

/-- At any possible interval visit the canonical image driver has an injective
trace through a finite horizon, ending at the target-changed visited point. -/
theorem exists_image_trace_at_visit {κ a b r : ℝ} {xL ρL : Fin 0 → ℝ}
    {w β : ℝ≥0 → ℝ} {vL : Fin 0 → ℝ≥0 → ℝ} {vR : Fin 2 → ℝ≥0 → ℝ}
    {T : ℝ≥0∞} {η : ℝ≥0 → ℂ}
    (hκ4 : κ < 4) (hr : r ≤ κ / 2 - 4) (ha : 0 < a) (hab : a < b)
    (hp : Sec2.IsSLEPathUpTo κ xL ![a, b] ρL ![r, -r] w vL vR β T)
    (hη : IsGeneratingTrace w T η) (hinj : InjOn η {s : ℝ≥0 | (s : ℝ≥0∞) ≤ T})
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ T) {y : ℝ} (hy : y ∈ Ioo a b) (hvis : η t = (y : ℂ)) :
    newHorizon a w (vR 0) t ≠ ⊤ ∧
      ∃ Γ : ℝ≥0 → ℂ, IsGeneratingTrace (newDrv a w (vR 0)) (newHorizon a w (vR 0) t) Γ ∧
        InjOn Γ {u : ℝ≥0 | (u : ℝ≥0∞) ≤ newHorizon a w (vR 0) t} ∧
        Γ (newHorizon a w (vR 0) t).toNNReal = Sec7.targetChange a (y : ℂ) ∧
        ∀ s : ℝ≥0, s < t →
          Γ (clk (rate a w (vR 0)) s).toNNReal = Sec7.targetChange a (η s) := by
  have hcov := Cover3.visit_le_sepTime hκ4 hr ha hp hη hinj t ht y hy hvis
  have hd := Local2.retargetData_first ha hab (hp.mono ht) (fun s hs =>
    lt_of_lt_sepTime (hs.trans_le hcov))
  have hpd : PullData w (vR 0) a t := ⟨ha, hp.w_zero, hd.sep, hd.target⟩
  have hηt := hη.mono_horizon ht
  have hinjt : InjOn η {s : ℝ≥0 | (s : ℝ≥0∞) ≤ (t : ℝ≥0∞)} :=
    hinj.mono fun s hs => hs.trans ht
  have hne : η t ≠ (a : ℂ) := by
    rw [hvis]
    exact_mod_cast hy.1.ne'
  have hfin := newHorizon_ne_top_of_endpoint_ne hpd hηt rfl hne
  set Γ : ℝ≥0 → ℂ := fun u =>
    if (u : ℝ≥0∞) < newHorizon a w (vR 0) t then imageTrace a w (vR 0) η u
    else Sec7.targetChange a (η t)
  have hgen : IsGeneratingTrace (newDrv a w (vR 0)) (newHorizon a w (vR 0) t) Γ :=
    isGeneratingTrace_imageTrace_endpoint hpd hηt rfl hne
  have hi : InjOn Γ {u : ℝ≥0 | (u : ℝ≥0∞) ≤ newHorizon a w (vR 0) t} :=
    injOn_imageTrace_endpoint hpd hηt hinjt rfl hne
  have hco : ((newHorizon a w (vR 0) t).toNNReal : ℝ≥0∞) = newHorizon a w (vR 0) t :=
    ENNReal.coe_toNNReal hfin
  have hvalue : Γ (newHorizon a w (vR 0) t).toNNReal = Sec7.targetChange a (y : ℂ) := by
    simp only [Γ, hco, lt_self_iff_false, ↓reduceIte, hvis]
  refine ⟨hfin, Γ, hgen, hi, hvalue, ?_⟩
  intro s hs
  have hst : (s : ℝ≥0∞) < (t : ℝ≥0∞) := ENNReal.coe_lt_coe.2 hs
  simp only [Γ, hpd.clk_lt hst, ↓reduceIte]
  exact imageTrace_clk hpd hst

end InteractingSLE.Sec5.TwoMark.Image4
