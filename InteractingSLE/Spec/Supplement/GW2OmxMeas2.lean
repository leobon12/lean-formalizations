/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OmxMeas
import InteractingSLE.Spec.Supplement.GW2SgChart
import InteractingSLE.Spec.Supplement.GW2ScheduleCanon
import InteractingSLE.Spec.Restart.DomainMarkovMain

/-!
# GW2's open lines: the stage-chart coupling mean paired with a test function is measurable

Packet PROVE-GW2-STAGEMEAN, R120 round (item 4). Root-generic: for any measurable random chart `cs` (the stage chart),
a continuous measurable driver `S` from `0` (the stage driver), a measurable time `Q` (the stage clock) and
continuous measurable positions `VL`, `VR` (the typed stage word flowed along `S`), the coupling mean of the bounded
harmonic extension read in `cs`,
`z ↦ couplingMean κ S Q (bheProc κ ρL ρR S VL VR · Q) (cs.1 z) − u₀ z − σa − kc · cs.2.2 z`,
is, on the domain `cs⁻¹(ℍ ∖ K_Q)` of the moved chart, the chart mean of `GW2OmxMeas` for the moved chart
`cs ∘ (record chart of S at Q)`; so its masked pairing with any test function is measurable.

* `movedChart`, `posAt`, `movedChart_eq` (`= cs.loewner S Q`), **`coe_dom_movedChart`**,
  **`isMeasChart_movedChart`**, **`measurable_posAt`**;
* **`chartMeanFn_moved_eq`**: the chart mean is the coupling-mean form;
* **`measurable_integral_moved`** and **`integral_moved_eq`**: the masked pairing is measurable and, for a test
  function supported in `cs⁻¹(ℍ ∖ K_Q)`, it is the pairing of the coupling-mean form.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H chiC fwdHull fwdMap fwdMapInv logDerivFwd)

namespace InteractingSLE.Theorem14.GW2Omx

variable {Ω : Type*} {nL nR : ℕ}

/-- The chart `cs` moved by the Loewner flow of `S` to the time `Q`. -/
def movedChart (cs : Ω → Chart) (S : ℝ≥0 → Ω → ℝ) (Q : Ω → ℝ≥0) (ω : Ω) : Chart :=
  (cs ω).trans (Exist.StagedLaw.recChart (Exist.StagedLaw.recOf (Q ω : ℝ≥0∞) (fun u => S u ω, ⊤)))

/-- The positions at the time `Q`, relative to the driver. -/
def posAt (S : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (Q : Ω → ℝ≥0) (ω : Ω) :
    (Fin nL → ℝ) × (Fin nR → ℝ) :=
  (fun i => VL i (Q ω) ω - S (Q ω) ω, fun j => VR j (Q ω) ω - S (Q ω) ω)

theorem movedChart_eq (cs : Ω → Chart) {S : ℝ≥0 → Ω → ℝ} (hSc : ∀ ω, Continuous fun u => S u ω)
    (hS0 : ∀ ω, S 0 ω = 0) (Q : Ω → ℝ≥0) (ω : Ω) :
    movedChart cs S Q ω = (cs ω).loewner (Ito.rpath fun u => S u ω) (Q ω) := by
  rw [movedChart, GW2Rd.recChart_recOf_top (hSc ω) (hS0 ω)]
  unfold Chart.loewner Chart.trans Chart.id
  simp only [add_zero]

theorem isConformal_movedChart {cs : Ω → Chart} (hcs : ∀ ω, (cs ω).IsConformal) {S : ℝ≥0 → Ω → ℝ}
    (hSc : ∀ ω, Continuous fun u => S u ω) (hS0 : ∀ ω, S 0 ω = 0) (Q : Ω → ℝ≥0) (ω : Ω) :
    (movedChart cs S Q ω).IsConformal := by
  rw [movedChart_eq cs hSc hS0]
  exact (hcs ω).loewner ((hSc ω).comp continuous_real_toNNReal) (by simp [hS0]) (Q ω).coe_nonneg

/-- **The domain of the moved chart** is the stage chart's preimage of the complement of the hull. -/
theorem coe_dom_movedChart {cs : Ω → Chart} (hcs : ∀ ω, (cs ω).IsConformal) {S : ℝ≥0 → Ω → ℝ}
    (hSc : ∀ ω, Continuous fun u => S u ω) (hS0 : ∀ ω, S 0 ω = 0) (Q : Ω → ℝ≥0) (ω : Ω) :
    ((movedChart cs S Q ω).dom : Set ℂ) =
      (cs ω).2.1 '' (H \ fwdHull (fun s : ℝ => S s.toNNReal ω) (Q ω)) := by
  rw [(isConformal_movedChart hcs hSc hS0 Q ω).coe_dom, movedChart_eq cs hSc hS0]
  have hW : Continuous fun s : ℝ => S s.toNNReal ω := (hSc ω).comp continuous_real_toNNReal
  have hW0 : (fun s : ℝ => S s.toNNReal ω) 0 = 0 := by simp [hS0]
  change (fun w => (cs ω).2.1 (fwdMapInv (fun s : ℝ => S s.toNNReal ω) (Q ω) w)) '' H = _
  rw [← Set.image_image, QuantumZipper.RS.image_fwdMapInv_H hW hW0 (Q ω).coe_nonneg]

theorem dom_movedChart_subset {cs : Ω → Chart} (hcs : ∀ ω, (cs ω).IsConformal) {S : ℝ≥0 → Ω → ℝ}
    (hSc : ∀ ω, Continuous fun u => S u ω) (hS0 : ∀ ω, S 0 ω = 0) (Q : Ω → ℝ≥0) (ω : Ω) :
    ((movedChart cs S Q ω).dom : Set ℂ) ⊆ (cs ω).dom := by
  rw [coe_dom_movedChart hcs hSc hS0 Q ω, (hcs ω).coe_dom]
  exact image_mono sdiff_subset

theorem isMeasChart_movedChart {m : MeasurableSpace Ω} {cs : Ω → Chart} (hcs : WalkInf.IsMeasChart m cs)
    {S : ℝ≥0 → Ω → ℝ} (hSc : ∀ ω, Continuous fun u => S u ω) (hS0 : ∀ ω, S 0 ω = 0)
    (hSm : ∀ u, Measurable[m] (S u)) {Q : Ω → ℝ≥0} (hQ : Measurable[m] Q) :
    WalkInf.IsMeasChart m (movedChart cs S Q) := by
  have hF : Measurable[m] fun ω => ((fun u => S u ω), (⊤ : ℝ≥0∞)) :=
    (@measurable_pi_iff Ω ℝ≥0 (fun _ => ℝ) m _ _).2 hSm |>.prodMk measurable_const
  have hr := @GW2Schedule.measurable_recOf_joint Ω m _ hF (fun ω => GW2Rd.isRegularDriver_top (hSc ω) (hS0 ω))
    _ (measurable_coe_nnreal_ennreal.comp hQ)
  exact hcs.trans_recChart hr

theorem measurable_posAt {m : MeasurableSpace Ω} {S : ℝ≥0 → Ω → ℝ} (hSc : ∀ ω, Continuous fun u => S u ω)
    (hSm : ∀ u, Measurable[m] (S u)) {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hVLc : ∀ i ω, Continuous fun u => VL i u ω) (hVLm : ∀ i u, Measurable[m] (VL i u))
    (hVRc : ∀ j ω, Continuous fun u => VR j u ω) (hVRm : ∀ j u, Measurable[m] (VR j u)) {Q : Ω → ℝ≥0}
    (hQ : Measurable[m] Q) : Measurable[m] (posAt S VL VR Q) := by
  let _ : MeasurableSpace Ω := m
  have hj : ∀ {X : ℝ≥0 → Ω → ℝ}, (∀ ω, Continuous fun u => X u ω) → (∀ u, Measurable (X u)) →
      Measurable fun ω => X (Q ω) ω := fun {X} hc hm =>
    (measurable_uncurry_of_continuous_of_measurable (u := fun t ω => X t ω) hc hm).comp (hQ.prodMk measurable_id)
  have hS := hj hSc hSm
  exact (measurable_pi_iff.2 fun i => (hj (hVLc i) (hVLm i)).sub hS).prodMk
    (measurable_pi_iff.2 fun j => (hj (hVRc j) (hVRm j)).sub hS)

/-- **The chart mean of the moved chart is the coupling-mean form.** -/
theorem chartMeanFn_moved_eq (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (cs : Ω → Chart)
    {S : ℝ≥0 → Ω → ℝ} (hSc : ∀ ω, Continuous fun u => S u ω) (hS0 : ∀ ω, S 0 ω = 0)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (Q : Ω → ℝ≥0) (u₀ : ℂ → ℝ) (σa kc : ℝ) (ω : Ω)
    (z : ℂ) :
    chartMeanFn κ ρL ρR (posAt S VL VR Q) (movedChart cs S Q) cs u₀ σa kc ω z =
      couplingMean κ (fun s : ℝ => S s.toNNReal ω) (Q ω : ℝ)
        (Restart.DomainMarkov.bheProc κ ρL ρR S VL VR ω (Q ω)) ((cs ω).1 z) - u₀ z - σa - kc * (cs ω).2.2 z := by
  rw [chartMeanFn, movedChart_eq cs hSc hS0]
  simp only [Chart.loewner, couplingMean, Restart.DomainMarkov.bheProc, posAt, add_sub_cancel_right]
  rfl

/-- **The masked stage-chart coupling-mean pairing is measurable.** -/
theorem measurable_integral_moved {m : MeasurableSpace Ω} (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    {cs : Ω → Chart} (hcs : WalkInf.IsMeasChart m cs) {S : ℝ≥0 → Ω → ℝ} (hSc : ∀ ω, Continuous fun u => S u ω)
    (hS0 : ∀ ω, S 0 ω = 0) (hSm : ∀ u, Measurable[m] (S u)) {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} (hVLc : ∀ i ω, Continuous fun u => VL i u ω)
    (hVLm : ∀ i u, Measurable[m] (VL i u)) (hVRc : ∀ j ω, Continuous fun u => VR j u ω)
    (hVRm : ∀ j u, Measurable[m] (VR j u)) {Q : Ω → ℝ≥0} (hQ : Measurable[m] Q) {u₀ : ℂ → ℝ}
    (hu₀ : ContinuousOn u₀ H) (σa kc : ℝ) (φ : TestOn upperHalfPlaneOpens) :
    Measurable[m] fun ω => ∫ z, ({p : Ω × ℂ | p.2 ∈ (movedChart cs S Q p.1).dom}.indicator
      (fun p => chartMeanFn κ ρL ρR (posAt S VL VR Q) (movedChart cs S Q) cs u₀ σa kc p.1 p.2)) (ω, z) * φ z :=
  measurable_integral_chartMeanFn κ ρL ρR (measurable_posAt hSc hSm hVLc hVLm hVRc hVRm hQ)
    (isMeasChart_movedChart hcs hSc hS0 hSm hQ) hcs (dom_movedChart_subset hcs.1 hSc hS0 Q) hu₀ σa kc φ

/-- **On test functions supported in the moved domain, the masked pairing is the coupling-mean pairing.** -/
theorem integral_moved_eq (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {cs : Ω → Chart}
    (hcs : ∀ ω, (cs ω).IsConformal) {S : ℝ≥0 → Ω → ℝ} (hSc : ∀ ω, Continuous fun u => S u ω)
    (hS0 : ∀ ω, S 0 ω = 0) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (Q : Ω → ℝ≥0)
    (u₀ : ℂ → ℝ) (σa kc : ℝ) {φ : TestOn upperHalfPlaneOpens} {ω : Ω}
    (hsupp : tsupport φ ⊆ (cs ω).2.1 '' (H \ fwdHull (fun s : ℝ => S s.toNNReal ω) (Q ω))) :
    ∫ z, ({p : Ω × ℂ | p.2 ∈ (movedChart cs S Q p.1).dom}.indicator
      (fun p => chartMeanFn κ ρL ρR (posAt S VL VR Q) (movedChart cs S Q) cs u₀ σa kc p.1 p.2)) (ω, z) * φ z =
      ∫ z, (couplingMean κ (fun s : ℝ => S s.toNNReal ω) (Q ω : ℝ)
        (Restart.DomainMarkov.bheProc κ ρL ρR S VL VR ω (Q ω)) ((cs ω).1 z) - u₀ z - σa - kc * (cs ω).2.2 z) *
          φ z := by
  rw [integral_masked_eq (C := movedChart cs S Q) (F := fun ω z => chartMeanFn κ ρL ρR (posAt S VL VR Q)
    (movedChart cs S Q) cs u₀ σa kc ω z) (by rw [coe_dom_movedChart hcs hSc hS0 Q ω]; exact hsupp)]
  simp only [chartMeanFn_moved_eq κ ρL ρR cs hSc hS0 VL VR Q u₀ σa kc]

end InteractingSLE.Theorem14.GW2Omx
