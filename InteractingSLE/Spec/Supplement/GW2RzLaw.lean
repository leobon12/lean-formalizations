/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RzStage
import InteractingSLE.Spec.Supplement.GW2SqFilt


/-!
# GW2 at a root `x`: the stage K2 law in the re-centred chart (decision D8, layer 5, continued)

Packet PROVE-GW2-ROOTX, round 3. RELDET's `GW2SqFilt.hasRelSafe_stage'` at a root `x₀`. The chart is D8's:
GB6's relative chart re-centred at the root, then the centred Loewner map of the relative driver.

* **`relChartX x s r`**: `(relChart r).recenter (baseRead x s r)`, the recentring amount being ROOT2's measurable
  reader of the root's chart image (`relBase` on the good records); `isConformal_relChartX`,
  `isMeasChart_relChartX`, **`isMeasChart_stgChartX`** (`WalkInf.IsMeasChart.recenter`, `.trans_recChart`);
* `measurableSet_inter_le_stgClockX_of_canonFilt'` (`h𝓗'` for the stage filtration enlarged by the stage history);
* **`hasRelSafe_stageX'`**: K2's relative safe law at a stage at the root `x₀` from the marked union locality with
  the whole exploration's shape in the re-centred chart, the stage mean, the chart field identity, the threshold
  clause and integrability (conditional helper; all root-`x` stage measurability is proved).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull zeroGFFTestCov)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE.Theorem14.GW2Rz

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop Supp8.RelSafe Supp8.RelSafeS Restart
  Restart.DomainMarkov.K2 Restart.FCDet Sec7.PocketTraversal LocalSets GW2TipSystem GW2Rd

/-! ### The re-centred chart -/

/-- **GB6's relative chart re-centred at the root `x`** (decision D8): `relChart r` recentred at the measurable
reader `baseRead x s r` of the root's chart image (`relBase` on the good records). -/
def relChartX (x : ℝ) (s : ℝ≥0) (r : RecData) : Chart := (relChart r).recenter (baseRead x s r)

theorem isConformal_relChartX (x : ℝ) (s : ℝ≥0) (r : RecData) : (relChartX x s r).IsConformal :=
  (isConformal_relChart r).recenter _

/-- The re-centred chart of a measurable record has measurable data. -/
theorem isMeasChart_relChartX {Ω : Type*} {m : MeasurableSpace Ω} {x : ℝ} {s : ℝ≥0} {rec : Ω → RecData}
    (hr : Measurable[m] rec) : WalkInf.IsMeasChart m fun ω => relChartX x s (rec ω) :=
  (isMeasChart_relChart hr).recenter ((measurable_baseRead x s).comp hr)

/-- **The root-`x` stage chart has measurable data** for every σ-algebra reading the counterflow record and the
relative record at the start. -/
theorem isMeasChart_stgChartX {Ω : Type*} {m : MeasurableSpace Ω} {x₀ : ℝ} {s : ℝ≥0} {rec : Ω → RecData}
    (hr : Measurable[m] rec) {R : ℝ≥0 → Ω → ℝ} (hRc : ∀ ω, Continuous fun t => R t ω) (hR0 : ∀ ω, R 0 ω = 0)
    {a : Ω → ℝ≥0} (hra : Measurable[m] fun ω => recOf (a ω : ℝ≥0∞) (fun t => R t ω, ⊤)) :
    WalkInf.IsMeasChart m fun ω => stgChart (relChartX x₀ s (rec ω)) (fun t => R t ω) (a ω) := by
  have e : (fun ω => stgChart (relChartX x₀ s (rec ω)) (fun t => R t ω) (a ω)) =
      fun ω => (relChartX x₀ s (rec ω)).trans (recChart (recOf (a ω : ℝ≥0∞) (fun t => R t ω, ⊤))) :=
    funext fun ω => stgChart_eq_trans _ (hRc ω) (hR0 ω) _
  rw [e]
  exact (isMeasChart_relChartX hr).trans_recChart hra

section Stage

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {x₀ : ℝ} {s : ℝ≥0}
  {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
  {k : ℝ} {w : WordType} {β : RecData → BoundaryWord} {E : Set RecData}
  {h Hr : Ω → DistOn upperHalfPlaneOpens}
  (hGT : ∀ ω ∈ GT, PhysGoodX x₀ s Wα ζα W γ α ω) (hs₀ : 0 < s) (hx₀ : 0 ≤ x₀)
  (hrec : Measurable (cfRec s Wα ζα)) (hWm : ∀ r, Measurable (W r))
  (hGTm : ∀ t, MeasurableSet[physFilt hrec hWm P t] GT)

omit [IsProbabilityMeasure P] in
include hGT hs₀ hx₀ hGTm in
/-- **`h𝓗'` for the enlarged stage filtration** (no readability of the stage history). -/
theorem measurableSet_inter_le_stgClock_of_canonFiltX' (hver : IsRelVersionXR x₀ s P Wα ζα W γ α R V)
    (T : ℝ≥0) {x : Ω → RecData} (hxm : Measurable x) {Hr : Ω → DistOn upperHalfPlaneOpens}
    (hΦ : Measurable fun ω => (augRec x (stgPreRecX x₀ s Wα ζα W GT V T R) ω,
      relVar Hr (fun u ω => stgDrv (fun v => R v ω) (stgStartX x₀ s Wα ζα W GT V T ω) u)
        (fun ω => V ω - stgStartX x₀ s Wα ζα W GT V T ω) ω))
    (q : ℝ≥0) {D : Set Ω} (hD : MeasurableSet[Coupling.filtrationComap canonFilt hΦ q] D) (t : ℝ≥0) :
    MeasurableSet[stgFilt (physFilt hrec hWm P) T hxm t]
      (D ∩ {ω | (q : ℝ≥0∞) ≤ stgClockX x₀ s Wα ζα W GT V T t ω}) := by
  have hle : physFilt hrec hWm P (T + t) ≤ stgFilt (physFilt hrec hWm P) T hxm t := le_sup_left
  have hL : MeasurableSet[stgFilt (physFilt hrec hWm P) T hxm t]
      {ω | (q : ℝ≥0∞) ≤ stgClockX x₀ s Wα ζα W GT V T t ω} :=
    hle _ (measurableSet_le measurable_const (measurable_stgClockX hGT hs₀ hx₀ hrec hWm hGTm hver T t))
  -- the same stage variable with a constant record
  have hΦ₀ : Measurable fun ω => ((fun _ : Ω => (default : RecData)) ω,
      relVar Hr (fun u ω => stgDrv (fun v => R v ω) (stgStartX x₀ s Wα ζα W GT V T ω) u)
        (fun ω => V ω - stgStartX x₀ s Wα ζα W GT V T ω) ω) :=
    measurable_const.prodMk (measurable_snd.comp hΦ)
  have hcst : Measurable[physFilt hrec hWm P T] fun _ : Ω => (default : RecData) := measurable_const
  rw [inter_comm]
  refine Supp8.Q3Stop.measurableSet_inter_of_canonFilt hΦ hL (fun A hA => ?_) (fun u hu B hB => ?_) (fun u hu => ?_) hD
  · -- the record generators: the stage history and the prefix record
    have hpre := measurable_stgPreRecX hGT hs₀ hx₀ hrec hWm hGTm hver T
    have hz : Measurable[stgFilt (physFilt hrec hWm P) T hxm t] (augRec x (stgPreRecX x₀ s Wα ζα W GT V T R)) :=
      measurable_augRec (comap_measurable x |>.mono le_sup_right le_rfl)
        (hpre.mono (((physFilt hrec hWm P).mono le_self_add).trans le_sup_left) le_rfl)
    exact hL.inter (hz hA)
  · -- the driver generators do not read the record
    have hD₀ : MeasurableSet[Coupling.filtrationComap canonFilt hΦ₀ q]
        ((fun ω => canonDrv u ((fun _ : Ω => (default : RecData)) ω, relVar Hr
          (fun u ω => stgDrv (fun v => R v ω) (stgStartX x₀ s Wα ζα W GT V T ω) u)
          (fun ω => V ω - stgStartX x₀ s Wα ζα W GT V T ω) ω)) ⁻¹' B) :=
      ⟨_, measurable_canonDrv_canonFilt hu hB, rfl⟩
    have h1 := measurableSet_inter_le_stgClock_of_canonFiltX hGT hs₀ hx₀ hrec hWm hGTm hver T hcst hΦ₀ q hD₀ t
    rw [inter_comm]
    exact hle _ h1
  · -- the stop generators do not read the record
    have hD₀ : MeasurableSet[Coupling.filtrationComap canonFilt hΦ₀ q]
        {ω | canonStp ((fun _ : Ω => (default : RecData)) ω, relVar Hr
          (fun u ω => stgDrv (fun v => R v ω) (stgStartX x₀ s Wα ζα W GT V T ω) u)
          (fun ω => V ω - stgStartX x₀ s Wα ζα W GT V T ω) ω) ≤ (u : ℝ≥0∞)} :=
      ⟨_, measurableSet_canonStp_le hu, rfl⟩
    have h1 := measurableSet_inter_le_stgClock_of_canonFiltX hGT hs₀ hx₀ hrec hWm hGTm hver T hcst hΦ₀ q hD₀ t
    rw [inter_comm]
    exact hle _ h1

end Stage

section Stage2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {x₀ : ℝ} {s : ℝ≥0}
  {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
  {k : ℝ} {w : WordType} {β : RecData → BoundaryWord} {E : Set RecData}
  {h Hr : Ω → DistOn upperHalfPlaneOpens}

/-- **K2's relative safe law at a stage, with the stage filtration enlarged by the stage history** (`hasRelSafe_stageX`
without the readability of `x` at `T`; conditional helper: the version, the marked union locality with the whole
exploration's shape, the stage mean, the chart field identity, the threshold clause and integrability are
hypotheses; all stage-specific measurability is proved). -/
theorem hasRelSafe_stageX' (hβ : Measurable β) (hE : MeasurableSet E) (hhm : Measurable h) (hHrm : Measurable Hr)
    (hGT : ∀ ω ∈ GT, PhysGoodX x₀ s Wα ζα W γ α ω) (hs₀ : 0 < s) (hx₀ : 0 ≤ x₀) (hrec : Measurable (cfRec s Wα ζα))
    (hWm : ∀ r, Measurable (W r)) (hGTm : MeasurableSet GT)
    (hGTae : ∀ᵐ ω ∂P, ω ∈ GT ↔ cfRec s Wα ζα ω ∈ goodX x₀ s)
    (hver : IsRelVersionXR x₀ s P Wα ζα W γ α R V) (T : ℝ≥0) {x : Ω → RecData}
    (hxm : Measurable x) (σa kc : ℝ)
    (hX : ∀ᵐ ω ∂P, ω ∈ liveEvRec k w β E (augRec x (stgPreRecX x₀ s Wα ζα W GT V T R)) →
      Chart.chartTransport (isConformal_stgChart (isConformal_relChartX x₀ s (cfRec s Wα ζα ω)) (hver.1.2.1 ω)
        (hver.1.2.2.1 ω) (stgStartX x₀ s Wα ζα W GT V T ω)) 1 σa kc (h ω) = Hr ω)
    -- the live event lies in the good records, with a finite stage start
    (hF : ∀ᵐ ω ∂P, ω ∈ liveEvRec k w β E (augRec x (stgPreRecX x₀ s Wα ζα W GT V T R)) →
      cfRec s Wα ζα ω ∈ goodX x₀ s)
    (hfin : ∀ᵐ ω ∂P, ω ∈ liveEvRec k w β E (augRec x (stgPreRecX x₀ s Wα ζα W GT V T R)) →
      stgStartMX x₀ s Wα ζα W GT V T ω ≠ ⊤)
    -- the marked union locality and the whole exploration's shape
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P)
    (ℋ : ℝ≥0 → MeasurableSpace Ω) (h𝓖ℋ : ∀ t, stgFilt (physFilt hrec hWm P) T hxm t ≤ ℋ t)
    (hℋ : ∀ t, ℋ t ≤ mΩ)
    (B : ℝ≥0 → Ω → Set ℂ) (hBm : ∀ t, Measurable[mΩ, hittingSigma] (B t))
    (hBc : ∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω))
    (hloc : ∀ t, WholeField.IsHistoryAvoidanceLocal (ℋ t) (B t) (WholeField.centredField h u₀) P)
    (hBKw : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ liveEvRec k w β E (augRec x (stgPreRecX x₀ s Wα ζα W GT V T R)) →
      min (physClockX x₀ s Wα ζα W GT (T + t) ω) (V ω) < V ω →
      H \ B t ω = (relChartX x₀ s (cfRec s Wα ζα ω)).2.1 ''
        (H \ fwdHull (Ito.rpath fun u => R u ω) (min (physClockX x₀ s Wα ζα W GT (T + t) ω) (V ω)).toNNReal))
    -- the stage mean
    (hmeanL : ∀ (t : ℝ≥0) (g : Ω → DistOn upperHalfPlaneOpens),
      IsLocalSetMean (B t) (WholeField.centredField h u₀) P g →
      ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ liveEvRec k w β E (augRec x (stgPreRecX x₀ s Wα ζα W GT V T R)) →
        stgClockX x₀ s Wα ζα W GT V T t ω < V ω - stgStartX x₀ s Wα ζα W GT V T ω →
        Disjoint (tsupport ψ) (fwdHull (fun r : ℝ => stgDrv (fun v => R v ω) (stgStartX x₀ s Wα ζα W GT V T ω)
          r.toNNReal) (stgClockX x₀ s Wα ζα W GT V T t ω).toNNReal) →
        Chart.chartTransport (isConformal_stgChart (isConformal_relChartX x₀ s (cfRec s Wα ζα ω)) (hver.1.2.1 ω)
            (hver.1.2.2.1 ω) (stgStartX x₀ s Wα ζα W GT V T ω)) 1 σa kc
            (g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) ψ =
          ∫ z, couplingMean k (fun r : ℝ => stgDrv (fun v => R v ω) (stgStartX x₀ s Wα ζα W GT V T ω) r.toNNReal)
            (stgClockX x₀ s Wα ζα W GT V T t ω).toNNReal
            (DomainMarkov.bheProc k (typedRhoL w) (typedRhoR w)
              (fun u ω => stgDrv (fun v => R v ω) (stgStartX x₀ s Wα ζα W GT V T ω) u)
              (fun i t ω => geomLW canonDrv (fun y => typedXL k w (β y.1)) i t
                (augRec x (stgPreRecX x₀ s Wα ζα W GT V T R) ω, relVar Hr
                  (fun u ω => stgDrv (fun v => R v ω) (stgStartX x₀ s Wα ζα W GT V T ω) u)
                  (fun ω => V ω - stgStartX x₀ s Wα ζα W GT V T ω) ω))
              (fun j t ω => geomRW canonDrv (fun y => typedXR k w (β y.1)) j t
                (augRec x (stgPreRecX x₀ s Wα ζα W GT V T R) ω, relVar Hr
                  (fun u ω => stgDrv (fun v => R v ω) (stgStartX x₀ s Wα ζα W GT V T ω) u)
                  (fun ω => V ω - stgStartX x₀ s Wα ζα W GT V T ω) ω)) ω
              (stgClockX x₀ s Wα ζα W GT V T t ω).toNNReal) z * ψ z)
    -- the threshold and integrability clauses
    (hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun y => canonFld y φ)
      ((P.map fun ω => (augRec x (stgPreRecX x₀ s Wα ζα W GT V T R) ω, relVar Hr
        (fun u ω => stgDrv (fun v => R v ω) (stgStartX x₀ s Wα ζα W GT V T ω) u)
        (fun ω => V ω - stgStartX x₀ s Wα ζα W GT V T ω) ω))[|typeEvent k w β E]))
    (hthr : ∀ᵐ y ∂((P.map fun ω => (augRec x (stgPreRecX x₀ s Wα ζα W GT V T R) ω, relVar Hr
        (fun u ω => stgDrv (fun v => R v ω) (stgStartX x₀ s Wα ζα W GT V T ω) u)
        (fun ω => V ω - stgStartX x₀ s Wα ζα W GT V T ω) ω))[|typeEvent k w β E]),
      canonStp y ≤ thr (typedRhoL w) (typedRhoR w) canonDrv (fun y => typedXL k w (β y.1))
        (fun y => typedXR k w (β y.1)) y) :
    HasRelSafe k w β E (P.map fun ω => (augRec x (stgPreRecX x₀ s Wα ζα W GT V T R) ω, relVar Hr
      (fun u ω => stgDrv (fun v => R v ω) (stgStartX x₀ s Wα ζα W GT V T ω) u)
      (fun ω => V ω - stgStartX x₀ s Wα ζα W GT V T ω) ω)) := by
  have hv := hver.1
  have hRm := hv.1
  have hRc := hv.2.1
  have hR0 := hv.2.2.1
  have hVm := hv.2.2.2.2.1
  have hGTp : ∀ t, MeasurableSet[physFilt hrec hWm P t] GT := measurableSet_goodSetX_physFilt hrec hWm hGTm hGTae
  have hT0 : physFilt hrec hWm P T ≤ stgFilt (physFilt hrec hWm P) T hxm 0 := by
    rw [stgFilt_apply, add_zero]
    exact le_sup_left
  have hsh : ∀ t, shiftFilt (physFilt hrec hWm P) T t ≤ stgFilt (physFilt hrec hWm P) T hxm t := fun t => le_sup_left
  have hSM := measurable_stgStartMX hGT hs₀ hx₀ hrec hWm hGTp hver T
  have hSa : Measurable (stgStartX x₀ s Wα ζα W GT V T) :=
    ENNReal.measurable_toNNReal.comp (hSM.mono ((physFilt hrec hWm P).le T) le_rfl)
  have hpreT := measurable_stgPreRecX hGT hs₀ hx₀ hrec hWm hGTp hver T
  have hz0 : Measurable[stgFilt (physFilt hrec hWm P) T hxm 0] (augRec x (stgPreRecX x₀ s Wα ζα W GT V T R)) :=
    measurable_augRec (comap_measurable x |>.mono le_sup_right le_rfl) (hpreT.mono hT0 le_rfl)
  have hzm : Measurable (augRec x (stgPreRecX x₀ s Wα ζα W GT V T R)) := measurable_augRec hxm
    (hpreT.mono ((physFilt hrec hWm P).le T) le_rfl)
  -- the stage chart has measurable data at time `0` of the stage filtration
  have hcm := isMeasChart_stgChartX (x₀ := x₀) (s := s) (m := stgFilt (physFilt hrec hWm P) T hxm 0)
    ((measurable_rec_physFiltX hrec hWm T).mono hT0 le_rfl) hRc hR0 (hpreT.mono hT0 le_rfl)
  -- the stage relative variable
  have hRm' : ∀ u, Measurable fun ω => stgDrv (fun v => R v ω) (stgStartX x₀ s Wα ζα W GT V T ω) u :=
    fun u => measurable_stgDrv hRm hRc hSa u
  have hRc' : ∀ ω, Continuous fun u => stgDrv (fun v => R v ω) (stgStartX x₀ s Wα ζα W GT V T ω) u :=
    fun ω => continuous_stgDrv (hRc ω) _
  have hR0' : ∀ ω, stgDrv (fun v => R v ω) (stgStartX x₀ s Wα ζα W GT V T ω) 0 = 0 := fun ω => stgDrv_zero _ _
  have hVm' : Measurable fun ω => V ω - stgStartX x₀ s Wα ζα W GT V T ω :=
    hVm.sub (measurable_coe_nnreal_ennreal.comp hSa)
  have hΦ : Measurable fun ω => (augRec x (stgPreRecX x₀ s Wα ζα W GT V T R) ω, relVar Hr
      (fun u ω => stgDrv (fun v => R v ω) (stgStartX x₀ s Wα ζα W GT V T ω) u)
      (fun ω => V ω - stgStartX x₀ s Wα ζα W GT V T ω) ω) :=
    hzm.prodMk (measurable_relVar hHrm hRm' hVm')
  refine hasRelSafe_of_local_rec hβ hE hzm hhm hHrm hRm' hRc' hR0' hVm' (stgFilt (physFilt hrec hWm P) T hxm)
    hz0 hcm.1 hcm.2.2.2.1 hcm.2.2.2.2.1 hcm.2.2.2.2.2.2 hcm.2.1 hcm.2.2.1 σa kc hX
    (continuous_stgClockX hGT hs₀ hx₀ T) (monotone_stgClockX hGT hs₀ hx₀ T) (stgClock_zeroX T)
    (fun t => (measurable_stgClockX hGT hs₀ hx₀ hrec hWm hGTp hver T t).mono (hsh t) le_rfl)
    (fun q D hD t => measurableSet_inter_le_stgClock_of_canonFiltX' hGT hs₀ hx₀ hrec hWm hGTp hver T hxm hΦ q hD t)
    (fun q => reach_stgClockX hGT hs₀ hx₀ T hv hGTae hF hfin q) hu₀ hh0 ℋ (fun t => h𝓖ℋ t) hℋ B hBm hBc hloc ?_ hmeanL
    (fun ψ t => hsh t _ ((hasStgSafeMeasX hGT hs₀ hx₀ hrec hWm hGTm hGTae hver T).1 ψ t))
    (fun Fb t => hsh t _ ((hasStgSafeMeasX hGT hs₀ hx₀ hrec hWm hGTm hGTae hver T).2 Fb t)) hint hthr
  -- the stage shape
  intro t
  filter_upwards [hBKw t, hfin] with ω hB hf hωF hlt
  have hle := stgStartM_leX hGT hs₀ hx₀ (V := V) T t ω
  have hS : ((stgStartX x₀ s Wα ζα W GT V T ω : ℝ≥0) : ℝ≥0∞) = stgStartMX x₀ s Wα ζα W GT V T ω :=
    ENNReal.coe_toNNReal (hf hωF)
  have hmV : min (physClockX x₀ s Wα ζα W GT (T + t) ω) (V ω) < V ω := by
    by_contra hc
    have h1 : V ω - stgStartX x₀ s Wα ζα W GT V T ω ≤ stgClockX x₀ s Wα ζα W GT V T t ω := by
      unfold stgClockX
      rw [hS]
      exact tsub_le_tsub_right (le_of_not_gt hc) _
    exact (not_le.2 hlt) h1
  have hB' := hB hωF hmV
  have hst : stgClockX x₀ s Wα ζα W GT V T t ω =
      min (physClockX x₀ s Wα ζα W GT (T + t) ω) (V ω) - (stgStartX x₀ s Wα ζα W GT V T ω : ℝ≥0∞) := by
    unfold stgClockX
    rw [hS]
  rw [hst]
  exact compl_eq_stgChart_inv_image (hRc ω) (hR0 ω) (hS ▸ hle) (ne_top_of_lt hmV) hB'

end Stage2


end InteractingSLE.Theorem14.GW2Rz
