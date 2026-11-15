/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SqLocal
import InteractingSLE.Spec.Supplement.GW2SkStep

/-!
# GW2's stage identity: K2's relative safe law at a stage, wired

Packet PROVE-GW2-RELDET, ruling R106. This file assembles K2's inputs at stage `n` for GB6's relative exploration of the
WHOLE explored curve (at any instance: explored `W`, retained `Wα, ζα, α` at `s`, good set `GT`, an R-form version
`(R, V)`), stage start at the deterministic physical time `T`. All the stage-specific measurability is supplied by the
landed stage files:

* record: the augmented stage record `augRec x (stgPreRec … T R)` (`GW2SkRec`). The stage history `x` must be
  readable at `T`.
* chart: `stgChart (relChart (gb6Rec s Wα ζα)) R (stgStart T)`, with measurable data (`isMeasChart_stgChart`);
* clock: `stgClock T`, the filtration `shiftFilt (physFilt …) T`, `h𝓗'`, reach (`GW2SkFilt`);
* safe events (`GW2SkSafe`);
* kernels from the marked locality (`GW2Rd.hasRelSafe_of_local_rec`);
* **`compl_eq_stgChart_inv_image`** (this file): the stage shape from the WHOLE exploration's shape at `T + t`
  (`stgChart_inv_image`).

**`hasRelSafe_stage`**. The remaining inputs, listed as hypotheses, are:
* the version;
* the marked locality of the physical unions `B t` with marks containing `physFilt (T + t)`;
* the whole exploration's shape at `T + t`;
* the stage mean identification `hmeanL` (PROVE-GW2-STAGEMEAN);
* the chart field identity `hX`, the threshold clause and integrability.

Conditional helper with a distinct name.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull zeroGFFTestCov)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE.Theorem14.GW2Rd

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop Supp8.RelSafe Supp8.RelSafeS Restart
  Restart.DomainMarkov.K2 Restart.FCDet Sec7.PocketTraversal LocalSets

/-! ### The stage shape -/

/-- **The stage shape from the whole shape** (deterministic): if the complement of `B` is the chart's inverse image
of the complement of the whole relative hull at a finite `m ≥ S`, it is the stage chart's inverse image of the
complement of the stage hull at `m − S`. -/
theorem compl_eq_stgChart_inv_image {c : Chart} {R : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R 0 = 0) {B : Set ℂ}
    {S : ℝ≥0} {m : ℝ≥0∞} (hS : (S : ℝ≥0∞) ≤ m) (hm : m ≠ ⊤)
    (hB : H \ B = c.2.1 '' (H \ fwdHull (Ito.rpath R) m.toNNReal)) :
    H \ B = (stgChart c R S).2.1 '' (H \ fwdHull (Ito.rpath (stgDrv R S)) (m - S).toNNReal) := by
  rw [stgChart_inv_image c hR hR0 S, hB]
  have hM : m = ((m.toNNReal : ℝ≥0) : ℝ≥0∞) := (ENNReal.coe_toNNReal hm).symm
  have hSM : S ≤ m.toNNReal := by
    rw [hM] at hS
    exact ENNReal.coe_le_coe.1 hS
  have e : S + (m - S).toNNReal = m.toNNReal := by
    rw [hM, ← ENNReal.coe_sub, ENNReal.toNNReal_coe, ENNReal.toNNReal_coe]
    exact add_tsub_cancel_of_le hSM
  rw [e]

/-! ### The stage safe law -/

section Stage

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {s : ℝ≥0}
  {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
  {k : ℝ} {w : WordType} {β : RecData → BoundaryWord} {E : Set RecData}
  {h Hr : Ω → DistOn upperHalfPlaneOpens}

/-- **K2's relative safe law at a stage** (conditional helper: the version, the marked union locality with the whole
exploration's shape, the stage mean, the chart field identity, the threshold clause and integrability are
hypotheses; all stage-specific measurability is proved). -/
theorem hasRelSafe_stage (hβ : Measurable β) (hE : MeasurableSet E) (hhm : Measurable h) (hHrm : Measurable Hr)
    (hGT : ∀ ω ∈ GT, PhysGood s W Wα ζα γ α ω) (hrec : Measurable (gb6Rec s Wα ζα))
    (hWm : ∀ r, Measurable (W r)) (hGTm : MeasurableSet GT)
    (hGTae : ∀ᵐ ω ∂P, ω ∈ GT ↔ gb6Rec s Wα ζα ω ∈ gb6TS s)
    (hver : HullId.IsGB6RelVersionR s P W Wα ζα γ α R V) (T : ℝ≥0) {x : Ω → RecData}
    (hx : Measurable[physFilt hrec hWm P T] x) (σa kc : ℝ)
    (hX : ∀ᵐ ω ∂P, ω ∈ liveEvRec k w β E (augRec x (stgPreRec s W Wα ζα GT V T R)) →
      Chart.chartTransport (isConformal_stgChart (isConformal_relChart (gb6Rec s Wα ζα ω)) (hver.1.2.1 ω)
        (hver.1.2.2.1 ω) (stgStart s W Wα ζα GT V T ω)) 1 σa kc (h ω) = Hr ω)
    -- the live event lies in the good records, with a finite stage start
    (hF : ∀ᵐ ω ∂P, ω ∈ liveEvRec k w β E (augRec x (stgPreRec s W Wα ζα GT V T R)) →
      gb6Rec s Wα ζα ω ∈ gb6TS s)
    (hfin : ∀ᵐ ω ∂P, ω ∈ liveEvRec k w β E (augRec x (stgPreRec s W Wα ζα GT V T R)) →
      stgStartM s W Wα ζα GT V T ω ≠ ⊤)
    -- the marked union locality and the whole exploration's shape
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P)
    (ℋ : ℝ≥0 → MeasurableSpace Ω) (h𝓖ℋ : ∀ t, physFilt hrec hWm P (T + t) ≤ ℋ t) (hℋ : ∀ t, ℋ t ≤ mΩ)
    (B : ℝ≥0 → Ω → Set ℂ) (hBm : ∀ t, Measurable[mΩ, hittingSigma] (B t))
    (hBc : ∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω))
    (hloc : ∀ t, WholeField.IsHistoryAvoidanceLocal (ℋ t) (B t) (WholeField.centredField h u₀) P)
    (hBKw : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ liveEvRec k w β E (augRec x (stgPreRec s W Wα ζα GT V T R)) →
      min (physClock s W Wα ζα GT (T + t) ω) (V ω) < V ω →
      H \ B t ω = (relChart (gb6Rec s Wα ζα ω)).2.1 ''
        (H \ fwdHull (Ito.rpath fun u => R u ω) (min (physClock s W Wα ζα GT (T + t) ω) (V ω)).toNNReal))
    -- the stage mean
    (hmeanL : ∀ (t : ℝ≥0) (g : Ω → DistOn upperHalfPlaneOpens),
      IsLocalSetMean (B t) (WholeField.centredField h u₀) P g →
      ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ liveEvRec k w β E (augRec x (stgPreRec s W Wα ζα GT V T R)) →
        stgClock s W Wα ζα GT V T t ω < V ω - stgStart s W Wα ζα GT V T ω →
        Disjoint (tsupport ψ) (fwdHull (fun r : ℝ => stgDrv (fun v => R v ω) (stgStart s W Wα ζα GT V T ω)
          r.toNNReal) (stgClock s W Wα ζα GT V T t ω).toNNReal) →
        Chart.chartTransport (isConformal_stgChart (isConformal_relChart (gb6Rec s Wα ζα ω)) (hver.1.2.1 ω)
            (hver.1.2.2.1 ω) (stgStart s W Wα ζα GT V T ω)) 1 σa kc
            (g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) ψ =
          ∫ z, couplingMean k (fun r : ℝ => stgDrv (fun v => R v ω) (stgStart s W Wα ζα GT V T ω) r.toNNReal)
            (stgClock s W Wα ζα GT V T t ω).toNNReal
            (DomainMarkov.bheProc k (typedRhoL w) (typedRhoR w)
              (fun u ω => stgDrv (fun v => R v ω) (stgStart s W Wα ζα GT V T ω) u)
              (fun i t ω => geomLW canonDrv (fun y => typedXL k w (β y.1)) i t
                (augRec x (stgPreRec s W Wα ζα GT V T R) ω, relVar Hr
                  (fun u ω => stgDrv (fun v => R v ω) (stgStart s W Wα ζα GT V T ω) u)
                  (fun ω => V ω - stgStart s W Wα ζα GT V T ω) ω))
              (fun j t ω => geomRW canonDrv (fun y => typedXR k w (β y.1)) j t
                (augRec x (stgPreRec s W Wα ζα GT V T R) ω, relVar Hr
                  (fun u ω => stgDrv (fun v => R v ω) (stgStart s W Wα ζα GT V T ω) u)
                  (fun ω => V ω - stgStart s W Wα ζα GT V T ω) ω)) ω
              (stgClock s W Wα ζα GT V T t ω).toNNReal) z * ψ z)
    -- the threshold and integrability clauses
    (hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun y => canonFld y φ)
      ((P.map fun ω => (augRec x (stgPreRec s W Wα ζα GT V T R) ω, relVar Hr
        (fun u ω => stgDrv (fun v => R v ω) (stgStart s W Wα ζα GT V T ω) u)
        (fun ω => V ω - stgStart s W Wα ζα GT V T ω) ω))[|typeEvent k w β E]))
    (hthr : ∀ᵐ y ∂((P.map fun ω => (augRec x (stgPreRec s W Wα ζα GT V T R) ω, relVar Hr
        (fun u ω => stgDrv (fun v => R v ω) (stgStart s W Wα ζα GT V T ω) u)
        (fun ω => V ω - stgStart s W Wα ζα GT V T ω) ω))[|typeEvent k w β E]),
      canonStp y ≤ thr (typedRhoL w) (typedRhoR w) canonDrv (fun y => typedXL k w (β y.1))
        (fun y => typedXR k w (β y.1)) y) :
    HasRelSafe k w β E (P.map fun ω => (augRec x (stgPreRec s W Wα ζα GT V T R) ω, relVar Hr
      (fun u ω => stgDrv (fun v => R v ω) (stgStart s W Wα ζα GT V T ω) u)
      (fun ω => V ω - stgStart s W Wα ζα GT V T ω) ω)) := by
  have hv := hver.1
  have hRm := hv.1
  have hRc := hv.2.1
  have hR0 := hv.2.2.1
  have hVm := hv.2.2.2.2.1
  have hGTp : ∀ t, MeasurableSet[physFilt hrec hWm P t] GT := measurableSet_goodSet_physFilt hrec hWm hGTm hGTae
  have hT0 : physFilt hrec hWm P T ≤ shiftFilt (physFilt hrec hWm P) T 0 := by
    rw [shiftFilt_apply, add_zero]
  have hSM := measurable_stgStartM hGT hrec hWm hGTp hver T
  have hSa : Measurable (stgStart s W Wα ζα GT V T) :=
    ENNReal.measurable_toNNReal.comp (hSM.mono ((physFilt hrec hWm P).le T) le_rfl)
  have hpreT := measurable_stgPreRec hGT hrec hWm hGTp hver T
  have hzT : Measurable[physFilt hrec hWm P T] (augRec x (stgPreRec s W Wα ζα GT V T R)) :=
    measurable_augRec hx hpreT
  have hzm : Measurable (augRec x (stgPreRec s W Wα ζα GT V T R)) := hzT.mono ((physFilt hrec hWm P).le T) le_rfl
  -- the stage chart has measurable data at time `0` of the stage filtration
  have hcm := isMeasChart_stgChart (m := shiftFilt (physFilt hrec hWm P) T 0)
    ((measurable_rec_physFilt hrec hWm T).mono hT0 le_rfl) hRc hR0 (hpreT.mono hT0 le_rfl)
  -- the stage relative variable
  have hRm' : ∀ u, Measurable fun ω => stgDrv (fun v => R v ω) (stgStart s W Wα ζα GT V T ω) u :=
    fun u => measurable_stgDrv hRm hRc hSa u
  have hRc' : ∀ ω, Continuous fun u => stgDrv (fun v => R v ω) (stgStart s W Wα ζα GT V T ω) u :=
    fun ω => continuous_stgDrv (hRc ω) _
  have hR0' : ∀ ω, stgDrv (fun v => R v ω) (stgStart s W Wα ζα GT V T ω) 0 = 0 := fun ω => stgDrv_zero _ _
  have hVm' : Measurable fun ω => V ω - stgStart s W Wα ζα GT V T ω :=
    hVm.sub (measurable_coe_nnreal_ennreal.comp hSa)
  have hΦ : Measurable fun ω => (augRec x (stgPreRec s W Wα ζα GT V T R) ω, relVar Hr
      (fun u ω => stgDrv (fun v => R v ω) (stgStart s W Wα ζα GT V T ω) u)
      (fun ω => V ω - stgStart s W Wα ζα GT V T ω) ω) :=
    hzm.prodMk (measurable_relVar hHrm hRm' hVm')
  refine hasRelSafe_of_local_rec hβ hE hzm hhm hHrm hRm' hRc' hR0' hVm' (shiftFilt (physFilt hrec hWm P) T)
    (hzT.mono hT0 le_rfl) hcm.1 hcm.2.2.2.1 hcm.2.2.2.2.1 hcm.2.2.2.2.2.2 hcm.2.1 hcm.2.2.1 σa kc hX
    (continuous_stgClock hGT T) (monotone_stgClock hGT T) (stgClock_zero T)
    (fun t => measurable_stgClock hGT hrec hWm hGTp hver T t)
    (fun q D hD t => measurableSet_inter_le_stgClock_of_canonFilt hGT hrec hWm hGTp hver T hzT hΦ q hD t)
    (fun q => reach_stgClock hGT T hv hGTae hF hfin q) hu₀ hh0 ℋ (fun t => h𝓖ℋ t) hℋ B hBm hBc hloc ?_ hmeanL
    (hasStgSafeMeas hGT hrec hWm hGTm hGTae hver T).1 (hasStgSafeMeas hGT hrec hWm hGTm hGTae hver T).2 hint hthr
  -- the stage shape
  intro t
  filter_upwards [hBKw t, hfin] with ω hB hf hωF hlt
  have hle := stgStartM_le hGT (V := V) T t ω
  have hS : ((stgStart s W Wα ζα GT V T ω : ℝ≥0) : ℝ≥0∞) = stgStartM s W Wα ζα GT V T ω :=
    ENNReal.coe_toNNReal (hf hωF)
  have hmV : min (physClock s W Wα ζα GT (T + t) ω) (V ω) < V ω := by
    by_contra hc
    have h1 : V ω - stgStart s W Wα ζα GT V T ω ≤ stgClock s W Wα ζα GT V T t ω := by
      unfold stgClock
      rw [hS]
      exact tsub_le_tsub_right (le_of_not_gt hc) _
    exact (not_le.2 hlt) h1
  have hB' := hB hωF hmV
  have hst : stgClock s W Wα ζα GT V T t ω =
      min (physClock s W Wα ζα GT (T + t) ω) (V ω) - (stgStart s W Wα ζα GT V T ω : ℝ≥0∞) := by
    unfold stgClock
    rw [hS]
  rw [hst]
  exact compl_eq_stgChart_inv_image (hRc ω) (hR0 ω) (hS ▸ hle) (ne_top_of_lt hmV) hB'

end Stage

end InteractingSLE.Theorem14.GW2Rd
