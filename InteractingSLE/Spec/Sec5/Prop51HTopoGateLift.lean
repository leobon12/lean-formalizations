/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51HTopoAccessNoWrap
import Mathlib.Topology.Order.ExtendFrom

/-!
# Both endpoint gates of a finite counterflow-complement excursion

The existing first-exit lifting theorem also gives incoming gates by reversing
the interval parameter. Completing a finite excursion at both gates then gives
an actual compact simple crosscut. The endpoint order is retained as data; it
is not assumed to agree with the orientation required by positive-gate exit.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Sec5.Prop51HTopo

open WangWu hiding ratPt exists_ratPt_dist_lt
open Prop51G

/-- The right-hand counterpart of the existing first-exit prime-end limit.
This is parameter reversal of `Sec6.exists_tendsto_lift`, not a new lifting
or boundary-regularity assumption. -/
theorem exists_tendsto_fwdMap_right {η α : ℝ → ℂ} {w : ℝ → ℝ} {s a b : ℝ}
    (hη : IsLoewnerTrace w η) (hw : Continuous w) (hw0 : w 0 = 0)
    (hs : 0 ≤ s) (hab : a < b) (hc : ContinuousOn α (Icc a b))
    (hD : MapsTo α (Ioc a b) (H \ fwdHull w s)) (ha : α a ∉ H \ fwdHull w s) :
    ∃ q : ℝ, extendFrom H (fwdMapInv w s) q = α a ∧
      Tendsto (fun t => fwdMap w s (α t)) (𝓝[>] a) (𝓝 (q : ℂ)) := by
  let φ : ℝ → ℝ := fun t => a + b - t
  have hφc : Continuous φ := continuous_const.sub continuous_id
  have hφI : MapsTo φ (Icc a b) (Icc a b) := by
    intro t ht
    dsimp [φ]
    constructor <;> linarith [ht.1, ht.2]
  obtain ⟨q, hq, hlim⟩ := Sec6.exists_tendsto_lift hη hw hw0 hs hab
    (hc.comp hφc.continuousOn hφI)
    (fun t ht => hD (by dsimp [φ]; constructor <;> linarith [ht.1, ht.2]))
    (by simpa only [Function.comp_apply, φ, add_sub_cancel_right] using ha)
  have hφlim : Tendsto φ (𝓝[>] a) (𝓝[<] b) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h : Tendsto φ (𝓝[>] a) (𝓝 (φ a)) :=
        (hφc.tendsto a).mono_left nhdsWithin_le_nhds
      simpa only [φ, add_sub_cancel_left] using h
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change a < t at ht
      change a + b - t < b
      linarith
  refine ⟨q, ?_, ?_⟩
  · simpa only [YuanSimpleApprox.trMap_zero_left hw0, Function.comp_apply,
      φ, add_sub_cancel_right] using hq
  · have h := hlim.comp hφlim
    change Tendsto (fun t => fwdMap w s (α (φ (φ t)))) (𝓝[>] a) (𝓝 (q : ℂ)) at h
    simpa only [Function.comp_apply, φ, show ∀ t : ℝ, a + b - (a + b - t) = t by
      intro t; ring] using h

/-- A finite completed excursion, retaining its actual physical parameter.
No ordering of the two real endpoints is assumed. -/
structure FiniteExcursionCrosscut (η : ℝ → ℂ) (w : ℝ → ℝ) (s a b : ℝ) where
  path : ℝ → ℂ
  continuous : ContinuousOn path (Icc a b)
  injective : InjOn path (Icc a b)
  start : ℝ
  finish : ℝ
  start_eq : path a = (start : ℂ)
  finish_eq : path b = (finish : ℂ)
  interior_eq : EqOn path (fun t => revChart w s (η t)) (Ioo a b)
  interior_H : MapsTo path (Ioo a b) H

end InteractingSLE.Sec5.Prop51HTopo
