/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1SafeRead
import InteractingSLE.Spec.Supplement.RelSafeS3
import InteractingSLE.Spec.Supplement.BW1LifeMain

/-!
# BW1's relative safe law: assembly from the line data

Packet PROVE-BW1-SAFELAW. GB6's `RelSafeS3.hasRelSafe_of_lines` for BW1. For one version `(R, V)` in R-form with
hull identities (`IsBVer`), one record event `TS` and one word type `w`, K2's (S) and (L) for the joint law of
(record, relative variable) conditioned on the record event of type `w` follow from the data of K2's lines step at
deterministic PHYSICAL times (`BW1Lines.hasSafeLaw_life_of_lineKernel`, `hasSafeMembers_life_of_lineLocal`):

* the chart: the relative field `Hc` is, for every sample, the transport of a fixed field `h′` through GB6's
  relative chart of the record (`relChart`, a function of the record; for BW1 `Hc = bwRelField` and `h′` the
  counterflow-frame field: **`bwRelField_eq_chartTransport`**);
* the physical filtration `RelSafe.physFilt`, the relative clock `a(t) = min(bClock t, V)` (part 3: continuous,
  monotone, adapted, reaches every level below `V`; the relative filtration traced on `{q ≤ a(t)}` is physical);
* the threshold regularity of the typed flowed marks (`FCDet.isForceReg_thr`).

The remaining inputs of **`hasSafe_bw_of_lines`** are the line data proper: the line kernels and means (`hker`,
`hmean`), the marked locality of the physical union (`hloc`, `hBK`, …) and the measurability of the safe events
(`hSψ`, `hSb`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull chiC zeroGFFTestCov)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE.Theorem14.BW1Safe

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop Supp8.RelSafe Supp8.RelSafeS Restart
  Restart.DomainMarkov.K2 Restart.FCDet Sec7.PocketTraversal BW1Ver BW1Life

/-! ### The chart identity -/

/-- **BW1's relative field is the transport of the counterflow-frame field through the relative chart of the
record** (every record): `cfField(recField_r f) = (relChart r)_*(1, 2πχ′, χ′) cfField f`. -/
theorem cfField_recField_eq_chartTransport {κ : ℝ} (hκ : 0 < κ) (r : RecData) (f : DistOn upperHalfPlaneOpens) :
    GW4Traverse.cfField κ (recField κ r f) =
      Chart.chartTransport (isConformal_relChart r) 1 (2 * Real.pi * chiC (16 / κ)) (chiC (16 / κ))
        (GW4Traverse.cfField κ f) := by
  refine eq_chartTransport_relChart hκ (s := recS r) rfl (GW4Traverse.isChartTransport_cfField κ f) ?_
  have hL := isConformal_recChart r
  have hR := Chart.isConformal_infinitySourceChart
  have h5 := Chart.isChartTransport_chartTransport hL
    (Chart.locallyIntegrableOn_of_continuousOn (continuousOn_recChart_lift r)) 1 0 (chiC κ) f
  have h6 := GW4Traverse.isChartTransport_cfField κ (recField κ r f)
  have hχ : chiC (16 / κ) = -1 * chiC κ := by rw [Sec4.chiC_sixteen_div hκ]; ring
  rw [hχ] at h6
  have h7 := Theorem14.GW2JointKernel.isChartTransport_trans_sign hL hR (continuousOn_recChart_lift r)
    Chart.continuousOn_infinitySourceChart_lift h5 h6
  have e₃ : (-1 : ℝ) * 1 = -1 := by ring
  have e₄ : (-1 : ℝ) * 0 + -(Real.pi * chiC κ) = -(Real.pi * chiC κ) := by ring
  rw [e₃, e₄, ← hχ] at h7
  exact h7

/-- **`bwRelField` is the transport of `cfField h` through the relative chart of `bwRec`**, for every sample. -/
theorem bwRelField_eq_chartTransport {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*}
    (spec : ExplSpec) (hroot : spec.1 = 0) (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) :
    bwRelField κ b jumps spec h E ω =
      Chart.chartTransport (isConformal_relChart (bwRec κ b jumps spec E ω)) 1 (2 * Real.pi * chiC (16 / κ))
        (chiC (16 / κ)) (GW4Traverse.cfField κ (h ω)) := by
  unfold bwRelField bwField bwRec
  rw [hroot, Sec5.GlueCond.flowField_zero_zero]
  exact cfField_recField_eq_chartTransport hκ _ _

/-! ### The assembly -/

section Assembly

variable {κ θ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [hP : IsProbabilityMeasure P]
  {h' Hc : Ω → DistOn upperHalfPlaneOpens} {rec : Ω → RecData} {W : ℝ≥0 → Ω → ℝ} {GT : Set Ω}
  {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {TS : Set RecData} {c₀ : BoundaryWord}

/-- BW1's live event of the type `w`: the record lies in the record event and has type `w`. -/
def bLive (κ θ : ℝ) (c₀ : BoundaryWord) (rec : Ω → RecData) (TS : Set RecData) (w : WordType) : Set Ω :=
  rec ⁻¹' (TS ∩ {r | wordType (16 / κ) (bwRelWord κ θ c₀ r) = w})

/-- The typed left marks read from the record. -/
abbrev bTypedL (κ θ : ℝ) (c₀ : BoundaryWord) (w : WordType) (y : Supp8.Q3Stop.CanonSpace) : Fin w.1 → ℝ :=
  typedXL (16 / κ) w (bwRelWord κ θ c₀ y.1)

/-- The typed right marks read from the record. -/
abbrev bTypedR (κ θ : ℝ) (c₀ : BoundaryWord) (w : WordType) (y : Supp8.Q3Stop.CanonSpace) : Fin w.2.1 → ℝ :=
  typedXR (16 / κ) w (bwRelWord κ θ c₀ y.1)

/-- **K2's (S) and (L) for BW1's conditioned image law, from the line data at the physical lines.** -/
theorem hasSafe_bw_of_lines (hrec : Measurable rec) (hh'm : Measurable h') (hHcm : Measurable Hc)
    (hX : ∀ ω, Hc ω = Chart.chartTransport (isConformal_relChart (rec ω)) 1 (2 * Real.pi * chiC (16 / κ))
      (chiC (16 / κ)) (h' ω))
    (hTS : MeasurableSet TS) (hWm : ∀ r, Measurable (W r)) (hGT : ∀ ω ∈ GT, BGood rec W ω)
    (hGTm : ∀ t, MeasurableSet[physFilt hrec hWm P t] GT) (hv : IsBVer P rec W GT R V) (w : WordType)
    (hFGT : ∀ᵐ ω ∂P, ω ∈ bLive κ θ c₀ rec TS w → ω ∈ GT)
    -- the line data
    (𝒢L : ℝ≥0 → MeasurableSpace Ω) (h𝒢L : ∀ t, physFilt hrec hWm P t ≤ 𝒢L t) (h𝒢Lm : ∀ t, 𝒢L t ≤ mΩ)
    (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (hker : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ bLive κ θ c₀ rec TS w →
      min (bClock rec W GT t ω) (V ω) < V ω →
      tsupport φ ⊆ (relChart (rec ω)).2.1 ''
        (H \ fwdHull (fun r : ℝ => R r.toNNReal ω) (min (bClock rec W GT t ω) (V ω)).toNNReal) →
      P[fun ω => Complex.exp (Complex.I * (h' ω φ : ℂ)) | 𝒢L t] ω =
        Complex.exp (Complex.I * (M t ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((relChart (rec ω)).2.1 '' (H \ fwdHull
            (fun r : ℝ => R r.toNNReal ω) (min (bClock rec W GT t ω) (V ω)).toNNReal)) φ φ : ℝ) : ℂ)))
    (hmean : ∀ (t : ℝ≥0) (ψ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ bLive κ θ c₀ rec TS w →
      min (bClock rec W GT t ω) (V ω) < V ω →
      Disjoint (tsupport ψ) (fwdHull (fun r : ℝ => R r.toNNReal ω) (min (bClock rec W GT t ω) (V ω)).toNNReal) →
      Chart.chartTransport (isConformal_relChart (rec ω)) 1 (2 * Real.pi * chiC (16 / κ))
          (chiC (16 / κ)) (M t ω) ψ =
        ∫ z, couplingMean (16 / κ) (fun r : ℝ => R r.toNNReal ω) (min (bClock rec W GT t ω) (V ω)).toNNReal
          (DomainMarkov.bheProc (16 / κ) (typedRhoL w) (typedRhoR w) R
            (fun i t ω => geomLW canonDrv (bTypedL κ θ c₀ w) i t (rec ω, relVar Hc R V ω))
            (fun j t ω => geomRW canonDrv (bTypedR κ θ c₀ w) j t (rec ω, relVar Hc R V ω)) ω
            (min (bClock rec W GT t ω) (V ω)).toNNReal) z * ψ z)
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h' u₀) P)
    (ℋ : ℝ≥0 → MeasurableSpace Ω) (h𝓖ℋ : ∀ t, physFilt hrec hWm P t ≤ ℋ t)
    (hℋ : ∀ t, ℋ t ≤ mΩ) (B : ℝ≥0 → Ω → Set ℂ) (hBm : ∀ t, Measurable[mΩ, hittingSigma] (B t))
    (hBc : ∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω))
    (hloc : ∀ t, WholeField.IsHistoryAvoidanceLocal (ℋ t) (B t) (WholeField.centredField h' u₀) P)
    (hBK : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ bLive κ θ c₀ rec TS w → min (bClock rec W GT t ω) (V ω) < V ω →
      H \ B t ω = (relChart (rec ω)).2.1 ''
        (H \ fwdHull (fun r : ℝ => R r.toNNReal ω) (min (bClock rec W GT t ω) (V ω)).toNNReal))
    (hSψ : ∀ (ψ : TestOn upperHalfPlaneOpens) t,
      MeasurableSet[physFilt hrec hWm P t]
        {ω | min (bClock rec W GT t ω) (V ω) < V ω ∧ Disjoint (tsupport ψ)
          (fwdHull (fun r : ℝ => R r.toNNReal ω) (min (bClock rec W GT t ω) (V ω)).toNNReal)})
    (hSb : ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t,
      MeasurableSet[physFilt hrec hWm P t]
        {ω | min (bClock rec W GT t ω) (V ω) < V ω ∧ Disjoint (Coupling.ballsK Fb)
          (fwdHull (fun r : ℝ => R r.toNNReal ω) (min (bClock rec W GT t ω) (V ω)).toNNReal)}) :
    HasSafeLaw (16 / κ) (typedRhoL w) (typedRhoR w)
        ((P.map fun ω => (rec ω, relVar Hc R V ω))[|typeEvent (16 / κ) w (bwRelWord κ θ c₀) TS]) canonFilt univ
        canonStp canonDrv (geomLW canonDrv fun y => typedXL (16 / κ) w (bwRelWord κ θ c₀ y.1))
        (geomRW canonDrv fun y => typedXR (16 / κ) w (bwRelWord κ θ c₀ y.1)) canonFld ∧
      HasSafeMembers ((P.map fun ω => (rec ω, relVar Hc R V ω))[|typeEvent (16 / κ) w (bwRelWord κ θ c₀) TS])
        canonFilt univ canonStp canonDrv canonFld := by
  have hβ := measurable_bwRelWord κ θ c₀
  have hRm := hv.meas
  have hVm := hv.measV
  have hRc := hv.cont
  have hR0 := hv.zero
  set Φ : Ω → Supp8.Q3Stop.CanonSpace := fun ω => (rec ω, relVar Hc R V ω) with hΦdef
  have hΦ : Measurable Φ := hrec.prodMk (measurable_relVar hHcm hRm hVm)
  have hF : Φ ⁻¹' typeEvent (16 / κ) w (bwRelWord κ θ c₀) TS = bLive κ θ c₀ rec TS w := rfl
  have hF0 : MeasurableSet[physFilt hrec hWm P 0] (bLive κ θ c₀ rec TS w) :=
    measurable_rec_physFilt' hrec hWm 0 (hTS.inter ((measurable_wordType (16 / κ)).comp hβ
      (measurableSet_singleton w)))
  have hWd : (fun t ω => canonDrv t (Φ ω)) = R := by
    funext t ω
    exact relDrv_relVar (hRc ω) (hR0 ω) t
  have hXc : (fun ω => Chart.chartTransport (isConformal_relChart (rec ω)) 1 (2 * Real.pi * chiC (16 / κ))
      (chiC (16 / κ)) (h' ω)) = fun ω => canonFld (Φ ω) := by
    funext ω
    exact (hX ω).symm
  have hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ bLive κ θ c₀ rec TS w → (q : ℝ≥0∞) < V ω →
      ∃ t, (q : ℝ≥0∞) ≤ min (bClock rec W GT t ω) (V ω) := fun q =>
    reach_min_bClock hGT hv hFGT q
  have hreg : ∀ᵐ ω ∂P, ω ∈ bLive κ θ c₀ rec TS w → DomainMarkov.Aux79.IsForceReg R
      (fun i t ω => geomLW canonDrv (bTypedL κ θ c₀ w) i t (Φ ω))
      (fun j t ω => geomRW canonDrv (bTypedR κ θ c₀ w) j t (Φ ω)) V ω := by
    refine Eventually.of_forall fun ω _ => ?_
    have h1 := isForceReg_thr (fun y => canonDrv_zero y) (fun y => continuous_canonDrv y) (bTypedL κ θ c₀ w)
      (bTypedR κ θ c₀ w) canonStp (Φ ω)
    rw [← hWd]
    exact h1
  have hdom : ∀ z, MeasurableSet[physFilt hrec hWm P 0] {ω | z ∈ (relChart (rec ω)).dom} := fun z =>
    measurable_rec_physFilt' hrec hWm 0 (measurableSet_mem_dom_relChart z)
  have hfwd : ∀ z, Measurable[physFilt hrec hWm P 0]
      ({ω | z ∈ (relChart (rec ω)).dom}.indicator fun ω => (relChart (rec ω)).1 z) :=
    fun z => (measurable_indicator_fwd_relChart z).comp (measurable_rec_physFilt' hrec hWm 0)
  have hliftm : ∀ z, Measurable[physFilt hrec hWm P 0]
      ({ω | z ∈ (relChart (rec ω)).dom}.indicator fun ω => (relChart (rec ω)).2.2 z) :=
    fun z => (measurable_indicator_lift_relChart z).comp (measurable_rec_physFilt' hrec hWm 0)
  have h𝓗' := fun q D (hD : MeasurableSet[Coupling.filtrationComap canonFilt hΦ q] D) t =>
    measurableSet_inter_le_min_of_canonFilt hGT hrec hWm hGTm hv hHcm q hD t
  -- (S) on the space
  have hlaw : HasSafeLaw (16 / κ) (typedRhoL w) (typedRhoR w) P (Coupling.filtrationComap canonFilt hΦ)
      (bLive κ θ c₀ rec TS w) V R (fun i t ω => geomLW canonDrv (bTypedL κ θ c₀ w) i t (Φ ω))
      (fun j t ω => geomRW canonDrv (bTypedR κ θ c₀ w) j t (Φ ω))
      (fun ω => Chart.chartTransport (isConformal_relChart (rec ω)) 1 (2 * Real.pi * chiC (16 / κ))
        (chiC (16 / κ)) (h' ω)) :=
    Theorem14.BW1Lines.hasSafeLaw_life_of_lineKernel hF0 (fun ω => isConformal_relChart (rec ω))
      hdom hfwd hliftm (fun ω => continuousOn_lift_relChart (rec ω)) hh'm
      (2 * Real.pi * chiC (16 / κ)) (chiC (16 / κ)) (continuous_min_bClock hGT) (monotone_min_bClock hGT)
      (min_bClock_zero hGT) (measurable_min_bClock hGT hrec hWm hGTm hv) h𝓗' V hreach hreg hSψ 𝒢L h𝒢L
      h𝒢Lm M hker hmean
  -- (L) on the space
  have hmem : HasSafeMembers P (Coupling.filtrationComap canonFilt hΦ) (bLive κ θ c₀ rec TS w) V R
      (fun ω => Chart.chartTransport (isConformal_relChart (rec ω)) 1 (2 * Real.pi * chiC (16 / κ))
        (chiC (16 / κ)) (h' ω)) :=
    Theorem14.BW1Lines.hasSafeMembers_life_of_lineLocal
      (VL := fun i t ω => geomLW canonDrv (bTypedL κ θ c₀ w) i t (Φ ω))
      (VR := fun j t ω => geomRW canonDrv (bTypedR κ θ c₀ w) j t (Φ ω)) hh'm hu₀ hh0
      (fun ω => isConformal_relChart (rec ω)) hdom hfwd hliftm
      (fun ω => continuousOn_lift_relChart (rec ω))
      (fun ω => harmonicOnNhd_lift_relChart (rec ω)) (2 * Real.pi * chiC (16 / κ)) (chiC (16 / κ))
      (continuous_min_bClock hGT) (monotone_min_bClock hGT) (min_bClock_zero hGT)
      (measurable_min_bClock hGT hrec hWm hGTm hv) h𝓗' V hreach hreg hSb ℋ h𝓖ℋ hℋ B hBm hBc hloc hBK
  rw [← hF, ← hWd, hXc] at hlaw hmem
  -- transfer to the conditioned image law (the proof of `Q3Stop.hasRelSafe_of_space`)
  have hS := measurableSet_typeEvent_canonFilt (k := 16 / κ) (w := w) hβ hTS
  have hxL : Measurable[canonFilt 0] fun y : Supp8.Q3Stop.CanonSpace => typedXL (16 / κ) w (bwRelWord κ θ c₀ y.1) :=
    (((measurable_typedXL (16 / κ) w).comp hβ).comp measurable_fst_canonRec).mono (canonRec_le_canonFilt 0) le_rfl
  have hxR : Measurable[canonFilt 0] fun y : Supp8.Q3Stop.CanonSpace => typedXR (16 / κ) w (bwRelWord κ θ c₀ y.1) :=
    (((measurable_typedXR (16 / κ) w).comp hβ).comp measurable_fst_canonRec).mono (canonRec_le_canonFilt 0) le_rfl
  have hVst : ∀ t : ℝ≥0, MeasurableSet[canonFilt t] {y : Supp8.Q3Stop.CanonSpace | canonStp y ≤ t} := fun t =>
    measurableSet_canonStp_le le_rfl
  have hWa : AdaptedBefore canonFilt canonStp canonDrv :=
    MartChar.adaptedBefore_of_stronglyAdapted hVst stronglyAdapted_canonDrv
  have hVLa : ∀ i, AdaptedBefore canonFilt canonStp
      (geomLW canonDrv (fun y => typedXL (16 / κ) w (bwRelWord κ θ c₀ y.1)) i) := fun i =>
    MartChar.adaptedBefore_of_stronglyAdapted hVst
      (stronglyAdapted_geomLW stronglyAdapted_canonDrv continuous_canonDrv hxL i)
  have hVRa : ∀ j, AdaptedBefore canonFilt canonStp
      (geomRW canonDrv (fun y => typedXR (16 / κ) w (bwRelWord κ θ c₀ y.1)) j) := fun j =>
    MartChar.adaptedBefore_of_stronglyAdapted hVst
      (stronglyAdapted_geomRW stronglyAdapted_canonDrv continuous_canonDrv hxR j)
  exact ⟨hasSafeLaw_cond hS (hasSafeLaw_map hΦ (isWeakPath_canon _ _) hWa hVLa hVRa measurable_canonFld hlaw),
    hasSafeMembers_cond hS (hasSafeMembers_map hΦ measurable_canonFld hmem)⟩

end Assembly

end InteractingSLE.Theorem14.BW1Safe
