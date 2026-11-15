/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1GoodTime
import InteractingSLE.Spec.ZhanGT4.A1MargClock
import InteractingSLE.Spec.ZhanGT4.A1SeedGeomLocal
import InteractingSLE.Spec.Ito.FiltrationBasic

/-!
# Zhan's A.1 under R83, (G3): generic tools for the stopped-record facts

Packet PROVE-A1-G3LAW2. Generic facts used to verify the record inputs of `ResStopInput` (both directions, any
configuration):

* **`isGoodTime_repl`**: a good horizon stays good for a replacement image driver that is continuous, has a larger
  lifetime and the same hull at the horizon, against a frozen driver with the same frozen hull (the replacement may
  differ from the original after the horizon: GOODTIME's right-continuity of closed hulls gives the margin);
* **`extPath_stop_eq`**: the extension of a path stopped at `S` is `stopDrv` of the extension;
* **`measurable_stop_self`**, **`measurableSet_stop_of_conull`**, **`measurable_stopped_at'`**,
  **`measurable_stoppedValue'`**: an `ℝ≥0`-valued stopping time is measurable for its stopped σ-algebra, measurable
  conull sets are events of every stopped σ-algebra of the usual augmentation, and progressive processes stopped at
  (resp. read at) a stopping time are measurable for its stopped σ-algebra (stopping times given in `WithTop` form).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3L2

open QuantumZipper (H fwdHull)
open A2X A1Ref

section Good

variable {xj xk τ T : ℝ} {wj wj' wk wk' : ℝ → ℝ} {ζj ζj' : ℝ≥0∞}

/-- At a good horizon the closed hulls are disjoint. -/
theorem disjoint_of_isGoodTime (hg : A1Ref.IsGoodTime xj wj ζj xk wk τ T) :
    Disjoint (closure (physHull xj wj T)) (closure (physHull xk wk τ)) := by
  rw [Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty]
  intro hne
  have hT0 : 0 ≤ T := hg.1.le
  have hle : contactTime xj wj ζj xk wk τ ≤ ((T.toNNReal : ℝ≥0) : ℝ≥0∞) := by
    refine (min_le_right _ _).trans (iInf₂_le (T.toNNReal) ?_)
    rwa [Real.coe_toNNReal _ hT0]
  have h2 := hg.2.trans_le hle
  rw [ENNReal.ofReal] at h2
  exact lt_irrefl _ h2

/-- **A good horizon is good for a continuous replacement image driver** with a larger lifetime and the same hull at
the horizon, against a frozen driver with the same frozen hull. -/
theorem isGoodTime_repl (hg : A1Ref.IsGoodTime xj wj ζj xk wk τ T) (hwj' : Continuous wj')
    (hζ' : ENNReal.ofReal T < ζj') (hj : physHull xj wj T = physHull xj wj' T)
    (hk : physHull xk wk τ = physHull xk wk' τ) : A1Ref.IsGoodTime xj wj' ζj' xk wk' τ T := by
  have hd := disjoint_of_isGoodTime hg
  rw [hj, hk] at hd
  refine A1Marg.isGoodTime_sub.2 (A1Good.isGoodTime_of_disjoint hwj' hg.1 hζ' ?_)
  have e1 : physHull 0 wj' T = (fun z : ℂ => z + (-xj : ℝ)) '' physHull xj wj' T := by
    simp only [physHull, image_image]
    congr 1
    funext z
    push_cast
    ring
  have e2 : physHull (xk - xj) wk' τ = (fun z : ℂ => z + (-xj : ℝ)) '' physHull xk wk' τ := by
    simp only [physHull, image_image]
    congr 1
    funext z
    push_cast
    ring
  have hc : ∀ s : Set ℂ, closure ((fun z : ℂ => z + ((-xj : ℝ) : ℂ)) '' s) =
      (fun z : ℂ => z + ((-xj : ℝ) : ℂ)) '' closure s :=
    fun s => ((Homeomorph.addRight ((-xj : ℝ) : ℂ)).image_closure s).symm
  rw [e1, e2, hc, hc]
  exact (disjoint_image_iff (add_left_injective _)).2 hd

end Good

/-- The extension of a path stopped at `S` is the stopped extension. -/
theorem extPath_stop_eq (w : ℝ≥0 → ℝ) (S : ℝ≥0) :
    Strip.extPath (fun t => w (min t S)) = A1Ref.stopDrv (Strip.extPath w) S := by
  funext u
  simp only [Strip.extPath, A1Ref.stopDrv]
  congr 1
  rcases le_or_gt 0 u with hu | hu
  · rw [max_eq_right (le_min hu S.coe_nonneg)]
    apply NNReal.eq
    rw [NNReal.coe_min, Real.coe_toNNReal _ hu, Real.coe_toNNReal _ (le_min hu S.coe_nonneg)]
  · rw [Real.toNNReal_of_nonpos hu.le, max_eq_left (min_le_left _ _ |>.trans hu.le), Real.toNNReal_zero,
      min_eq_left (zero_le : (0 : ℝ≥0) ≤ S)]

section Stopped

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- An `ℝ≥0`-valued stopping time is measurable for its own stopped σ-algebra. -/
theorem measurable_stop_self {S : Ω → ℝ≥0} {S' : Ω → WithTop ℝ≥0} (hS : IsStoppingTime 𝓕 S')
    (hSS : ∀ ω, S' ω = S ω) : Measurable[hS.measurableSpace] S := by
  refine measurable_of_Iic fun x => ?_
  have h := hS.measurableSet_le' x
  convert h using 1
  ext ω
  simp only [mem_preimage, mem_Iic, mem_ofPred_eq, hSS ω, WithTop.coe_le_coe]

/-- **A measurable conull set is an event of every stopped σ-algebra of the usual augmentation.** -/
theorem measurableSet_stop_of_conull {P : Measure Ω} {G : Set Ω} (hG : MeasurableSet G) (hG0 : P Gᶜ = 0)
    {S : Ω → WithTop ℝ≥0} (hS : IsStoppingTime (usualAugmentation 𝓕 P) S) :
    MeasurableSet[hS.measurableSpace] G := by
  have h0 : MeasurableSet[usualAugmentation 𝓕 P 0] G := by
    have h := (Ito.measurableSet_usualAugmentation_of_null (𝓕 := 𝓕) hG.compl hG0 0).compl
    rwa [compl_compl] at h
  exact hS.le_measurableSpace_of_const_le (i := 0) (fun ω => by simp) _ h0

/-- A progressive process stopped at a stopping time (in `WithTop` form) is measurable for its stopped σ-algebra. -/
theorem measurable_stopped_at' {u : ℝ≥0 → Ω → ℝ} (hu : IsStronglyProgressive 𝓕 u) {T : Ω → ℝ≥0}
    {T' : Ω → WithTop ℝ≥0} (hT : IsStoppingTime 𝓕 T') (hTT : ∀ ω, T' ω = T ω) (t : ℝ≥0) :
    Measurable[hT.measurableSpace] fun ω => u (min t (T ω)) ω := by
  have e : T' = fun ω => (T ω : WithTop ℝ≥0) := funext hTT
  subst e
  exact A1SeedGeom.measurable_stopped_at hu hT t

/-- A progressive process read at a stopping time is measurable for its stopped σ-algebra. -/
theorem measurable_stoppedValue' {u : ℝ≥0 → Ω → ℝ} (hu : IsStronglyProgressive 𝓕 u) {T : Ω → ℝ≥0}
    {T' : Ω → WithTop ℝ≥0} (hT : IsStoppingTime 𝓕 T') (hTT : ∀ ω, T' ω = T ω) :
    Measurable[hT.measurableSpace] fun ω => u (T ω) ω := by
  have hm := measurable_stoppedValue hu hT
  convert hm using 1
  funext ω
  simp only [stoppedValue, hTT ω]
  rw [WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]

end Stopped

end InteractingSLE.ZhanGT4.A1G3L2
