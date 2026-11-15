/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvYFillMeas
import InteractingSLE.Spec.Sec5.CrossCondGenCloseDriver

/-!
# A total Borel mapping-out readout for GW2 inverse hulls

Compact caps and the landed dyadic map approximation define the readout on
every hitting-measurable set. On a half-plane hull it is its mapping-out map,
censored to zero outside the domain. No hull predicate is tested measurably.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2JDetR4

open Restart Restart.FlowStopIdentCMI

/-- The censored mapping-out map of a compact dyadic cover. -/
def coverMap (j : ℕ) (K : Set ℂ) (z : ℂ) : ℂ :=
  (H \ fillH (dyadicCover j K)).indicator
    (ConformalImage.mapOut (fillH (dyadicCover j K))) z

/-- The total readout, first refining compact caps, then increasing their size. -/
def hullMapRead (K : Set ℂ) (z : ℂ) : ℂ :=
  limUnder atTop fun n : ℕ => limUnder atTop fun j : ℕ =>
    coverMap j (hullCompactCap n K) z

theorem measurable_hullMapRead (z : ℂ) :
    Measurable[hittingSigma] (fun K => hullMapRead K z) := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.limUnder
  intro n
  apply StronglyMeasurable.limUnder
  intro j
  exact (measurable_comp_dyadicIdx (isDyadicHitMeasurable_hullCompactCap n)
    (fun K => (isCompact_hullCompactCap n K).isBounded) j
    (fun S => (H \ fillH (coverOf j S)).indicator
      (ConformalImage.mapOut (fillH (coverOf j S))) z)).stronglyMeasurable

theorem tendsto_coverMap {K : Set ℂ} (hK : IsCompact K)
    (hc : IsPreconnected (K ∪ lowerHalf)) (z : ℂ) :
    Tendsto (fun j => coverMap j K z) atTop
      (𝓝 ((H \ fillH K).indicator (ConformalImage.mapOut (fillH K)) z)) := by
  classical
  by_cases hz : z ∈ H \ fillH K
  · rw [indicator_of_mem hz]
    refine ((tendstoLocallyUniformlyOn_mapOut_dyadicCover hK hc).tendsto_at hz).congr' ?_
    filter_upwards [eventually_mem_H_diff_fillH_dyadicCover hK hz] with j hj
    exact (indicator_of_mem hj _).symm
  · rw [indicator_of_notMem hz]
    have hzj : ∀ j, z ∉ H \ fillH (dyadicCover j K) := by
      intro j hj
      exact hz ⟨hj.1, fun h => hj.2 (fillH_subset_fillH_dyadicCover j h)⟩
    simpa only [coverMap, indicator_of_notMem (hzj _)] using
      (tendsto_const_nhds (x := (0 : ℂ)))

/-- On every half-plane hull the total Borel readout is the normalized map. -/
theorem hullMapRead_eq {K : Set ℂ} (hK : IsHPHull K) (z : ℂ) :
    hullMapRead K z = (H \ K).indicator (ConformalImage.mapOut K) z := by
  obtain ⟨R, hR⟩ := hK.2.1.closure.subset_closedBall (0 : ℂ)
  obtain ⟨N, hN⟩ := exists_nat_ge R
  have hc : IsPreconnected (closure K ∪ lowerHalf) := by
    simpa only [closure_union, isClosed_lowerHalf.closure_eq, lowerHalf] using
      hK.isPreconnected_union_lowerHalf.closure
  have hf : fillH (closure K) = K := by
    rw [Sec7.SideHeight.fillH_closure, hK.fillH_eq]
  apply Filter.Tendsto.limUnder_eq
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  have he : hullCompactCap n K = closure K := by
    unfold hullCompactCap
    rw [inter_eq_left.2 hK.1]
    exact inter_eq_left.2 (hR.trans (Metric.closedBall_subset_closedBall
      (hN.trans (by exact_mod_cast hn))))
  rw [he, (tendsto_coverMap hK.2.1.isCompact_closure hc z).limUnder_eq, hf]

end InteractingSLE.Theorem14.GW2JDetR4
