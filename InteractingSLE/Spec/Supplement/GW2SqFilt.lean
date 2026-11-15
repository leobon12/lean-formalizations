/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SqStage

/-!
# GW2's stage identity: the stage filtration enlarged by the stage history

Packet PROVE-GW2-RELDET, ruling R106. `GW2Rd.hasRelSafe_stage` asks the stage history `x` (the counterflow record and
the earlier pieces) to be readable at the physical stage start (`hx : Measurable[physFilt T] x`). That is the HARD
direction: the past piece records read off the joined physical path. K2's lines do not need the filtration to be
physical. They need:
* the record readable at time `0`;
* the clock adapted;
* the canonical filtration compatible (`h𝓗'`);
* the safe events in it;
* the marks containing it.

So the stage filtration is ENLARGED by the stage history:

* `stgFilt 𝓕 T x hx`: `t ↦ 𝓕 (T + t) ⊔ σ(x)`;
* **`measurableSet_inter_le_stgClock_of_canonFilt'`**: `h𝓗'` for the enlarged filtration, with no readability of
  `x`. The record generators lie in `σ(x) ⊔ physFilt T`. The driver and stop generators do not read the record:
  `GW2Rd.measurableSet_inter_le_stgClock_of_canonFilt` applied with a constant record gives them;
* **`hasRelSafe_stage'`**: `hasRelSafe_stage` with the enlarged filtration. `hx` is dropped; the marks must contain
  `σ(x)` (for `exists_union_stageSet_gw2`: the counterflow marks and the schedule's past σ-algebra).

For JOINTDET's kernel ((II)) only the EASY direction remains: the joined physical path up to `T` is a measurable
function of the past records (ROOT2's `RootJ31.joinedRead`), so the augmented record generates `c.sigma r l` up to
null sets.
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

/-- **The stage filtration enlarged by the stage history.** -/
def stgFilt {Ω : Type*} [mΩ : MeasurableSpace Ω] (𝓕 : MeasureTheory.Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    {x : Ω → RecData} (hx : Measurable x) : MeasureTheory.Filtration ℝ≥0 mΩ where
  seq t := 𝓕 (T + t) ⊔ MeasurableSpace.comap x inferInstance
  mono' _ _ h := sup_le_sup_right (𝓕.mono (add_le_add le_rfl h)) _
  le' t := sup_le (𝓕.le (T + t)) hx.comap_le

theorem stgFilt_apply {Ω : Type*} [mΩ : MeasurableSpace Ω] (𝓕 : MeasureTheory.Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    {x : Ω → RecData} (hx : Measurable x) (t : ℝ≥0) :
    stgFilt 𝓕 T hx t = 𝓕 (T + t) ⊔ MeasurableSpace.comap x inferInstance := rfl

section Stage

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {s : ℝ≥0}
  {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
  {k : ℝ} {w : WordType} {β : RecData → BoundaryWord} {E : Set RecData}
  {h Hr : Ω → DistOn upperHalfPlaneOpens}
  (hGT : ∀ ω ∈ GT, PhysGood s W Wα ζα γ α ω) (hrec : Measurable (gb6Rec s Wα ζα)) (hWm : ∀ r, Measurable (W r))
  (hGTm : ∀ t, MeasurableSet[physFilt hrec hWm P t] GT)

omit [IsProbabilityMeasure P] in
include hGT hGTm in
/-- **`h𝓗'` for the enlarged stage filtration** (no readability of the stage history). -/
theorem measurableSet_inter_le_stgClock_of_canonFilt' (hver : HullId.IsGB6RelVersionR s P W Wα ζα γ α R V)
    (T : ℝ≥0) {x : Ω → RecData} (hxm : Measurable x) {Hr : Ω → DistOn upperHalfPlaneOpens}
    (hΦ : Measurable fun ω => (augRec x (stgPreRec s W Wα ζα GT V T R) ω,
      relVar Hr (fun u ω => stgDrv (fun v => R v ω) (stgStart s W Wα ζα GT V T ω) u)
        (fun ω => V ω - stgStart s W Wα ζα GT V T ω) ω))
    (q : ℝ≥0) {D : Set Ω} (hD : MeasurableSet[Coupling.filtrationComap canonFilt hΦ q] D) (t : ℝ≥0) :
    MeasurableSet[stgFilt (physFilt hrec hWm P) T hxm t]
      (D ∩ {ω | (q : ℝ≥0∞) ≤ stgClock s W Wα ζα GT V T t ω}) := by
  have hle : physFilt hrec hWm P (T + t) ≤ stgFilt (physFilt hrec hWm P) T hxm t := le_sup_left
  have hL : MeasurableSet[stgFilt (physFilt hrec hWm P) T hxm t]
      {ω | (q : ℝ≥0∞) ≤ stgClock s W Wα ζα GT V T t ω} :=
    hle _ (measurableSet_le measurable_const (measurable_stgClock hGT hrec hWm hGTm hver T t))
  -- the same stage variable with a constant record
  have hΦ₀ : Measurable fun ω => ((fun _ : Ω => (default : RecData)) ω,
      relVar Hr (fun u ω => stgDrv (fun v => R v ω) (stgStart s W Wα ζα GT V T ω) u)
        (fun ω => V ω - stgStart s W Wα ζα GT V T ω) ω) :=
    measurable_const.prodMk (measurable_snd.comp hΦ)
  have hcst : Measurable[physFilt hrec hWm P T] fun _ : Ω => (default : RecData) := measurable_const
  rw [inter_comm]
  refine Supp8.Q3Stop.measurableSet_inter_of_canonFilt hΦ hL (fun A hA => ?_) (fun u hu B hB => ?_) (fun u hu => ?_) hD
  · -- the record generators: the stage history and the prefix record
    have hpre := measurable_stgPreRec hGT hrec hWm hGTm hver T
    have hz : Measurable[stgFilt (physFilt hrec hWm P) T hxm t] (augRec x (stgPreRec s W Wα ζα GT V T R)) :=
      measurable_augRec (comap_measurable x |>.mono le_sup_right le_rfl)
        (hpre.mono (((physFilt hrec hWm P).mono le_self_add).trans le_sup_left) le_rfl)
    exact hL.inter (hz hA)
  · -- the driver generators do not read the record
    have hD₀ : MeasurableSet[Coupling.filtrationComap canonFilt hΦ₀ q]
        ((fun ω => canonDrv u ((fun _ : Ω => (default : RecData)) ω, relVar Hr
          (fun u ω => stgDrv (fun v => R v ω) (stgStart s W Wα ζα GT V T ω) u)
          (fun ω => V ω - stgStart s W Wα ζα GT V T ω) ω)) ⁻¹' B) :=
      ⟨_, measurable_canonDrv_canonFilt hu hB, rfl⟩
    have h1 := measurableSet_inter_le_stgClock_of_canonFilt hGT hrec hWm hGTm hver T hcst hΦ₀ q hD₀ t
    rw [inter_comm]
    exact hle _ h1
  · -- the stop generators do not read the record
    have hD₀ : MeasurableSet[Coupling.filtrationComap canonFilt hΦ₀ q]
        {ω | canonStp ((fun _ : Ω => (default : RecData)) ω, relVar Hr
          (fun u ω => stgDrv (fun v => R v ω) (stgStart s W Wα ζα GT V T ω) u)
          (fun ω => V ω - stgStart s W Wα ζα GT V T ω) ω) ≤ (u : ℝ≥0∞)} :=
      ⟨_, measurableSet_canonStp_le hu, rfl⟩
    have h1 := measurableSet_inter_le_stgClock_of_canonFilt hGT hrec hWm hGTm hver T hcst hΦ₀ q hD₀ t
    rw [inter_comm]
    exact hle _ h1

end Stage

section Stage2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {s : ℝ≥0}
  {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
  {k : ℝ} {w : WordType} {β : RecData → BoundaryWord} {E : Set RecData}
  {h Hr : Ω → DistOn upperHalfPlaneOpens}

/-- **K2's relative safe law at a stage, with the stage filtration enlarged by the stage history** (`hasRelSafe_stage`
without the readability of `x` at `T`; conditional helper: the version, the marked union locality with the whole
exploration's shape, the stage mean, the chart field identity, the threshold clause and integrability are
hypotheses; all stage-specific measurability is proved). -/
theorem hasRelSafe_stage' (hβ : Measurable β) (hE : MeasurableSet E) (hhm : Measurable h) (hHrm : Measurable Hr)
    (hGT : ∀ ω ∈ GT, PhysGood s W Wα ζα γ α ω) (hrec : Measurable (gb6Rec s Wα ζα))
    (hWm : ∀ r, Measurable (W r)) (hGTm : MeasurableSet GT)
    (hGTae : ∀ᵐ ω ∂P, ω ∈ GT ↔ gb6Rec s Wα ζα ω ∈ gb6TS s)
    (hver : HullId.IsGB6RelVersionR s P W Wα ζα γ α R V) (T : ℝ≥0) {x : Ω → RecData}
    (hxm : Measurable x) (σa kc : ℝ)
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
    (ℋ : ℝ≥0 → MeasurableSpace Ω) (h𝓖ℋ : ∀ t, stgFilt (physFilt hrec hWm P) T hxm t ≤ ℋ t)
    (hℋ : ∀ t, ℋ t ≤ mΩ)
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
  have hT0 : physFilt hrec hWm P T ≤ stgFilt (physFilt hrec hWm P) T hxm 0 := by
    rw [stgFilt_apply, add_zero]
    exact le_sup_left
  have hsh : ∀ t, shiftFilt (physFilt hrec hWm P) T t ≤ stgFilt (physFilt hrec hWm P) T hxm t := fun t => le_sup_left
  have hSM := measurable_stgStartM hGT hrec hWm hGTp hver T
  have hSa : Measurable (stgStart s W Wα ζα GT V T) :=
    ENNReal.measurable_toNNReal.comp (hSM.mono ((physFilt hrec hWm P).le T) le_rfl)
  have hpreT := measurable_stgPreRec hGT hrec hWm hGTp hver T
  have hz0 : Measurable[stgFilt (physFilt hrec hWm P) T hxm 0] (augRec x (stgPreRec s W Wα ζα GT V T R)) :=
    measurable_augRec (comap_measurable x |>.mono le_sup_right le_rfl) (hpreT.mono hT0 le_rfl)
  have hzm : Measurable (augRec x (stgPreRec s W Wα ζα GT V T R)) := measurable_augRec hxm
    (hpreT.mono ((physFilt hrec hWm P).le T) le_rfl)
  -- the stage chart has measurable data at time `0` of the stage filtration
  have hcm := isMeasChart_stgChart (m := stgFilt (physFilt hrec hWm P) T hxm 0)
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
  refine hasRelSafe_of_local_rec hβ hE hzm hhm hHrm hRm' hRc' hR0' hVm' (stgFilt (physFilt hrec hWm P) T hxm)
    hz0 hcm.1 hcm.2.2.2.1 hcm.2.2.2.2.1 hcm.2.2.2.2.2.2 hcm.2.1 hcm.2.2.1 σa kc hX
    (continuous_stgClock hGT T) (monotone_stgClock hGT T) (stgClock_zero T)
    (fun t => (measurable_stgClock hGT hrec hWm hGTp hver T t).mono (hsh t) le_rfl)
    (fun q D hD t => measurableSet_inter_le_stgClock_of_canonFilt' hGT hrec hWm hGTp hver T hxm hΦ q hD t)
    (fun q => reach_stgClock hGT T hv hGTae hF hfin q) hu₀ hh0 ℋ (fun t => h𝓖ℋ t) hℋ B hBm hBc hloc ?_ hmeanL
    (fun ψ t => hsh t _ ((hasStgSafeMeas hGT hrec hWm hGTm hGTae hver T).1 ψ t))
    (fun Fb t => hsh t _ ((hasStgSafeMeas hGT hrec hWm hGTm hGTae hver T).2 Fb t)) hint hthr
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

end Stage2

end InteractingSLE.Theorem14.GW2Rd
