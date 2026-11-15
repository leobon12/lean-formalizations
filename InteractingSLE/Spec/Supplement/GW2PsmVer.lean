/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PsmCapB
import InteractingSLE.Spec.Sec6.DrivingCriterion
import InteractingSLE.Spec.Sec7.LocalExtGChart

/-!
# GW2's open lines: two versions of the relative driver give the same stage-start mean

Packet PROVE-GW2-STAGEMEAN, R121 round (version conversion of the Claim(k) step), deterministic:

* `loewner_congr_of_continuous`: a Loewner chart reads a continuous driver on `[0, q]` only;
* `stgChart_congr`: a stage chart reads the relative driver on `[0, a]` only;
* **`stgMeanR_zero_congr`**: the stage-start mean (`stgMeanR` at clock `0`) of two relative drivers agreeing up to
  the stage start is the same;
* **`eqOn_of_hull_clock`**: two continuous drivers whose hulls agree at every level `k t'` of a continuous clock
  `k` (`k 0 = 0`) on `[0, T]` agree up to `k T` (Loewner uniqueness, `Sec6.eqOn_of_fwdHull_eq`, and the intermediate
  value theorem).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal
open QuantumZipper (H fwdHull fwdMap fwdMapInv logDerivFwd chiC)

namespace InteractingSLE.Theorem14.GW2Psm

open Restart Exist.StagedLaw GW2Rd

/-- **A Loewner chart reads a continuous driver on `[0, q]` only.** -/
theorem loewner_congr_of_continuous (c : Chart) {w W : ℝ → ℝ} (hw : Continuous w) (hW : Continuous W) {q : ℝ}
    (hq : 0 ≤ q) (h : EqOn w W (Icc 0 q)) : c.loewner w q = c.loewner W q := by
  have h1 : (fun z => fwdMap w q (c.1 z)) = fun z => fwdMap W q (c.1 z) :=
    funext fun z => InteractingSLE.fwdMap_eq_of_eqOn hq fun r hr => h hr
  have h2 : fwdMapInv w q = fwdMapInv W q := funext fun z =>
    LocalExt.fwdMapInv_congr_of_continuousOn (t' := q + 1) hw.continuousOn hW.continuousOn hq (by linarith) h z
  have h3 : (fun z => (logDerivFwd w q (c.1 z)).im + c.2.2 z) =
      fun z => (logDerivFwd W q (c.1 z)).im + c.2.2 z :=
    funext fun z => by rw [Ito.logDerivFwd_congr_of_eqOn (T := q) h hq le_rfl]
  simp only [Chart.loewner, h1, h2, h3]

/-- **A stage chart reads the relative driver on `[0, a]` only.** -/
theorem stgChart_congr (c : Chart) {R R' : ℝ≥0 → ℝ} (hR : Continuous R) (hR' : Continuous R') {a : ℝ≥0}
    (h : ∀ u ≤ a, R u = R' u) : stgChart c R a = stgChart c R' a := by
  unfold stgChart
  refine loewner_congr_of_continuous c (hR.comp continuous_real_toNNReal) (hR'.comp continuous_real_toNNReal)
    a.coe_nonneg fun x hx => ?_
  exact h _ (Real.toNNReal_le_iff_le_coe.2 hx.2)

/-- **The stage-start mean of two relative drivers agreeing up to the stage start is the same.** -/
theorem stgMeanR_zero_congr (κ : ℝ) (rec : RecData) {R R' : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R 0 = 0)
    (hR' : Continuous R') {a : ℝ≥0} (h : ∀ u ≤ a, R u = R' u) (U u₀ : ℂ → ℝ) (σa : ℝ) {y : ℂ}
    (hy : y ∈ ((stgChart (Supp8.RelSafeS.relChart rec) R a).dom : Set ℂ)) :
    stgMeanR κ rec R a 0 U u₀ σa y = stgMeanR κ rec R' a 0 U u₀ σa y := by
  have hc := stgChart_congr (Supp8.RelSafeS.relChart rec) hR hR' h
  have hconf := isConformal_stgChart (Supp8.RelSafeS.isConformal_relChart rec) hR hR0 a
  have hH := hconf.fwd_mem hy
  have h0 : (stgChart (Supp8.RelSafeS.relChart rec) R a).1 y ≠ 0 := fun h0 => by
    rw [h0] at hH
    exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hH)
  have hw : Ito.rpath (stgDrv R a) 0 = 0 := by simp [Ito.rpath, stgDrv_zero]
  have hw' : Ito.rpath (stgDrv R' a) 0 = 0 := by simp [Ito.rpath, stgDrv_zero]
  unfold stgMeanR
  rw [Coupling.MartMeans2.couplingMean_zero κ hw U h0, ← hc,
    Coupling.MartMeans2.couplingMean_zero κ hw' U h0]

/-- **Loewner uniqueness along a clock**: two continuous drivers whose hulls agree at every level `k t'`,
`t' ∈ [0, T]`, of a continuous clock with `k 0 = 0` agree on `[0, k T]`. -/
theorem eqOn_of_hull_clock {W W' : ℝ → ℝ} (hW : Continuous W) (hW' : Continuous W') (hW0 : W 0 = 0)
    (hW0' : W' 0 = 0) {k : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (hk : ContinuousOn k (Icc 0 T)) (hk0 : k 0 = 0)
    (h : ∀ t' ∈ Icc 0 T, fwdHull W (k t') = fwdHull W' (k t')) : EqOn W W' (Icc 0 (k T)) := by
  rcases lt_or_ge (k T) 0 with hneg | hnn
  · intro x hx
    exact absurd (hx.1.trans hx.2) (not_le.2 hneg)
  refine Sec6.eqOn_of_fwdHull_eq hW hW' hW0 hW0' hnn fun r hr => ?_
  have hIVT := intermediate_value_Icc hT hk
  rw [hk0] at hIVT
  obtain ⟨t', ht', hrt'⟩ := hIVT hr
  rw [← hrt']
  exact h t' ht'

end InteractingSLE.Theorem14.GW2Psm
