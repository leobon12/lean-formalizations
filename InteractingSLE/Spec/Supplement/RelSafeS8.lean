/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RelSafeS7
import InteractingSLE.Spec.Sec5.CrossCond
import InteractingSLE.Spec.Sec5.CrossCondLaw
import InteractingSLE.Spec.Supplement.Q3ChainDet

/-!
# GB6's relative safe law, part 8: the counterflow half of the marked union locality

Packet PROVE-GB6-RELSAFE2. The physical union of GB6's lines is `A ∪ K_t` (`RelSafeS7`). For the counterflow hull
`K_t` (read from the killed history, `GlueCond.hullAt t`), the history-marked locality needed in the union holds with
the marks of the counterflow's own driving filtration at the deterministic time `t`, and these marks contain
everything the physical filtration `RelSafe.physFilt` asks of the counterflow: every measurable a.s. version of the
driver at times `≤ t`, and the null sets. Generic for an optional hull coupling with almost surely infinite lifetime:

* `measurable_cfHull`, `ae_cfHull_eq`: the hull read from the killed history is a hitting-measurable version of the
  physical hull `K_t`;
* **`isHistoryAvoidanceLocal_cfHull`**: marked locality for the centred coupling field with marks
  `drivingFiltration t` (`WholeField.isHistoryAvoidanceLocal_hull` at the constant stopping time `t`);
* `measurableSet_avoid_cfHull`: its avoidance events are marks;
* **`measurable_version_drivingFiltration`**: a measurable almost surely equal version of the driver is measurable for
  the marks at every time `r ≤ t`; `nullSets_le_drivingFiltration'`: the null sets are marks.

With Theorem 1.2 the marks are field-determined (`Q3Chain.drivingFiltration_le_aeSigma`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE.Supp8.RelSafeS

open LawUnique Sec5.GlueCond Coupling

section Counterflow

variable {k : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

theorem measurable_cfHull (hX : IsMeasurableKilledDriving W VL VR ζ) (t : ℝ≥0) :
    Measurable[mΩ, hittingSigma] fun ω => hullAt t (killedHistory W VL VR ζ ω) :=
  (measurable_hullAt t).comp (measurable_killedHistory hX)

omit [IsProbabilityMeasure P] in
theorem ae_cfHull_eq (hC : IsOptionalHullCoupling k xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    (t : ℝ≥0) :
    ∀ᵐ ω ∂P, hullAt t (killedHistory W VL VR ζ ω) = fwdHull (fun r : ℝ => W r.toNNReal ω) t := by
  filter_upwards [Aux50Hit.ae_isGoodPath hC.1 hζ] with ω hg
  exact Aux50Hit.regHull_stopHistory_cstop hg t

/-- **Marked locality of the counterflow hull with the marks of the driving filtration at `t`.** -/
theorem isHistoryAvoidanceLocal_cfHull (hC : IsOptionalHullCoupling k xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hk : 0 < k) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData k ρL ρR xL xR) (forceJumpSet xL xR) u₀) (t : ℝ≥0) :
    WholeField.IsHistoryAvoidanceLocal (drivingFiltration P hC.2.2.2.1 t)
      (fun ω => hullAt t (killedHistory W VL VR ζ ω)) (WholeField.centredField h u₀) P := by
  have hX := hC.2.2.2.1
  have hτ := isStoppingTime_const (drivingFiltration P hX) t
  have hτζ : ∀ᵐ ω ∂P, (((fun _ : Ω => ((t : ℝ≥0) : WithTop ℝ≥0)) ω : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := by
    filter_upwards [hζ] with ω hω
    rw [hω]
    exact ENNReal.coe_lt_top
  have hloc := WholeField.isHistoryAvoidanceLocal_hull hC hk hu₀ hX hτ hτζ
    (A := fun ω => hullAt t (killedHistory W VL VR ζ ω)) (measurable_cfHull hX t)
    (by
      filter_upwards [ae_cfHull_eq hC hζ t] with ω hω
      rw [WithTop.untopD_coe]
      exact hω)
  rw [IsStoppingTime.measurableSpace_const] at hloc
  exact hloc

omit [IsProbabilityMeasure P] in
/-- The avoidance events of the counterflow hull are marks. -/
theorem measurableSet_avoid_cfHull (hX : IsMeasurableKilledDriving W VL VR ζ) (t : ℝ≥0) {U : Set ℂ}
    (hU : IsOpen U) (hUH : U ⊆ H) :
    MeasurableSet[drivingFiltration P hX t] {ω | Disjoint (hullAt t (killedHistory W VL VR ζ ω)) U} := by
  have hm : Measurable[MeasurableSpace.comap (killedHistory W VL VR ζ) (WangWu.stopSigma t), hittingSigma]
      fun ω => hullAt t (killedHistory W VL VR ζ ω) :=
    (Sec5.CrossCond.measurable_hullAt_stopSigma t).comp (comap_measurable _)
  exact WangWu.comap_stopSigma_le hX t _ (hm (LocalSets.measurableSet_avoid hU hUH))

omit [IsProbabilityMeasure P] in
/-- The null sets are marks. -/
theorem nullSets_le_drivingFiltration' (hX : IsMeasurableKilledDriving W VL VR ζ) (t : ℝ≥0) :
    Ito.nullSets P ≤ drivingFiltration P hX t :=
  Ito.nullSets_le_usualAugmentation _ P t

omit [IsProbabilityMeasure P] in
/-- **A measurable almost surely equal version of the driver is measurable for the marks at `t`** (for `r ≤ t`, when
the lifetime is almost surely infinite). -/
theorem measurable_version_drivingFiltration (hX : IsMeasurableKilledDriving W VL VR ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {W' : ℝ≥0 → Ω → ℝ} (hW'm : ∀ r, Measurable (W' r)) (hW' : ∀ᵐ ω ∂P, ∀ r, W' r ω = W r ω) {r t : ℝ≥0}
    (hrt : r ≤ t) : Measurable[drivingFiltration P hX t] (W' r) := by
  intro A hA
  have hkill : MeasurableSet[drivingFiltration P hX t] {ω | (r : ℝ≥0∞) < ζ ω ∧ W r ω ∈ A} :=
    (drivingFiltration P hX).mono hrt _ (Ito.le_usualAugmentation _ P r _ (adaptedBefore_killedDriving_W hX r A hA))
  refine RelSafe.measurableSet_of_ae_eq ((drivingFiltration P hX).le t) (nullSets_le_drivingFiltration' hX t)
    (hW'm r hA) hkill ?_
  filter_upwards [hζ, hW'] with ω hω hWω
  change (W' r ω ∈ A) = ((r : ℝ≥0∞) < ζ ω ∧ W r ω ∈ A)
  rw [hω, hWω r]
  simp only [ENNReal.coe_lt_top, true_and]

end Counterflow

end InteractingSLE.Supp8.RelSafeS
