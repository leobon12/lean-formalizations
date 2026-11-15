/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RdSafeGood
import InteractingSLE.Spec.Supplement.GW2RdTop
import InteractingSLE.Spec.Supplement.RelSafeS3
import InteractingSLE.Spec.Supplement.Q3StopTransfer
import InteractingSLE.Spec.Supplement.GW2JointKernelProofC

/-!
# GW2's relative safe law (K2's (S), (L)), part 2: assembly from GW2's line data

Packet PROVE-GW2-RELDET. GB6's assembly `Supp8.RelSafeS.hasRelSafe_of_lines` with the curves exchanged. For one
R-form version `(R, V)` of GW2's relative exploration (explored: the extended flow line `regW s Wα ζα`, retained: the
counterflow `(W, ζ, γ)`) and one word type `w`, `HasRelSafe κ w (gw2Word κ θ c′) (gb6TS s)` for the joint law of the
counterflow record and the relative variable of the RAISED chart field `Hc + θχ(κ)` follows from:

* the generic engines of K2's lines step at deterministic physical times (`BW1Lines.hasSafeLaw_life_of_lineKernel`,
  `hasSafeMembers_life_of_lineLocal`), with the physical filtration of (counterflow record, extended flow driver), the
  clock `a(t) = min(physClock t, V)` of GB6's clock layer at the exchanged instance (good event: `GW2RdSafeGood`), the
  ORIGINAL field `h` read in the relative chart of the counterflow record with coefficients
  `1, specOffset κ + θχ(κ), χ(κ)` — which is the raised chart field on the live event
  (`ae_raised_eq_chartTransport_relChart`);
* GW2's line data proper (the hypotheses `hker`, `hmean`, `hloc`, `hBK`, …, `hSψ`, `hSb`): Aux. 77/79 at the physical
  lines and the marked locality of the physical union, read with the flow line explored;
* the threshold clause and the integrability clause, passed through unchanged (`hasRelSafe_of_space_cond`, the variant
  of `Q3Stop.hasRelSafe_of_space` taking the integrability under the conditioned law, as `GW2Sf.integrable_canonFld_gw2`
  provides it).

**`hasRelSafe_of_lines_gw2`** is a conditional helper with a distinct name; its line-data hypotheses are GW2's
analogue of GB6's `HasGB6LineData` and are not proved here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull chiC zeroGFFTestCov)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE.Theorem14.GW2Rd

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop Supp8.RelSafe Supp8.RelSafeS Restart
  Restart.DomainMarkov.K2 Restart.FCDet Sec7.PocketTraversal GW2TipSystem GW2JointKernel

/-! ### `HasRelSafe` from the space, with the integrability under the conditioned law -/

section Space

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {k : ℝ} {w : WordType}
  {β : RecData → BoundaryWord} {E : Set RecData} {rec : Ω → RecData} {Hc : Ω → DistOn upperHalfPlaneOpens}
  {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}

/-- **`HasRelSafe` from (S) and (L) on the space**, the threshold bound and the integrability both under the
conditioned image law (`Q3Stop.hasRelSafe_of_space` asks the integrability on the space itself). -/
theorem hasRelSafe_of_space_cond (hβ : Measurable β) (hE : MeasurableSet E) (hrec : Measurable rec)
    (hHc : Measurable Hc) (hRm : ∀ t, Measurable (R t)) (hVm : Measurable V)
    (hlaw : HasSafeLaw k (typedRhoL w) (typedRhoR w) P
      (Coupling.filtrationComap canonFilt (hrec.prodMk (measurable_relVar hHc hRm hVm)))
      ((fun ω => (rec ω, relVar Hc R V ω)) ⁻¹' typeEvent k w β E)
      (fun ω => canonStp (rec ω, relVar Hc R V ω)) (fun t ω => canonDrv t (rec ω, relVar Hc R V ω))
      (fun i t ω => geomLW canonDrv (fun y => typedXL k w (β y.1)) i t (rec ω, relVar Hc R V ω))
      (fun j t ω => geomRW canonDrv (fun y => typedXR k w (β y.1)) j t (rec ω, relVar Hc R V ω))
      (fun ω => canonFld (rec ω, relVar Hc R V ω)))
    (hmem : HasSafeMembers P (Coupling.filtrationComap canonFilt (hrec.prodMk (measurable_relVar hHc hRm hVm)))
      ((fun ω => (rec ω, relVar Hc R V ω)) ⁻¹' typeEvent k w β E)
      (fun ω => canonStp (rec ω, relVar Hc R V ω)) (fun t ω => canonDrv t (rec ω, relVar Hc R V ω))
      (fun ω => canonFld (rec ω, relVar Hc R V ω)))
    (hint : ∀ φ : TestOn upperHalfPlaneOpens,
      Integrable (fun y => canonFld y φ) ((P.map fun ω => (rec ω, relVar Hc R V ω))[|typeEvent k w β E]))
    (hthr : ∀ᵐ y ∂((P.map fun ω => (rec ω, relVar Hc R V ω))[|typeEvent k w β E]),
      canonStp y ≤ thr (typedRhoL w) (typedRhoR w) canonDrv (fun y => typedXL k w (β y.1))
        (fun y => typedXR k w (β y.1)) y) :
    HasRelSafe k w β E (P.map fun ω => (rec ω, relVar Hc R V ω)) := by
  have hΦ : Measurable fun ω => (rec ω, relVar Hc R V ω) := hrec.prodMk (measurable_relVar hHc hRm hVm)
  have hS := measurableSet_typeEvent_canonFilt (k := k) (w := w) hβ hE
  have hxL : Measurable[canonFilt 0] fun y : Supp8.Q3Stop.CanonSpace => typedXL k w (β y.1) :=
    (((measurable_typedXL k w).comp hβ).comp measurable_fst_canonRec).mono (canonRec_le_canonFilt 0) le_rfl
  have hxR : Measurable[canonFilt 0] fun y : Supp8.Q3Stop.CanonSpace => typedXR k w (β y.1) :=
    (((measurable_typedXR k w).comp hβ).comp measurable_fst_canonRec).mono (canonRec_le_canonFilt 0) le_rfl
  have hVst : ∀ t : ℝ≥0, MeasurableSet[canonFilt t] {y : Supp8.Q3Stop.CanonSpace | canonStp y ≤ t} := fun t =>
    measurableSet_canonStp_le le_rfl
  have hWa : AdaptedBefore canonFilt canonStp canonDrv :=
    MartChar.adaptedBefore_of_stronglyAdapted hVst stronglyAdapted_canonDrv
  have hVLa : ∀ i, AdaptedBefore canonFilt canonStp (geomLW canonDrv (fun y => typedXL k w (β y.1)) i) := fun i =>
    MartChar.adaptedBefore_of_stronglyAdapted hVst
      (stronglyAdapted_geomLW stronglyAdapted_canonDrv continuous_canonDrv hxL i)
  have hVRa : ∀ j, AdaptedBefore canonFilt canonStp (geomRW canonDrv (fun y => typedXR k w (β y.1)) j) := fun j =>
    MartChar.adaptedBefore_of_stronglyAdapted hVst
      (stronglyAdapted_geomRW stronglyAdapted_canonDrv continuous_canonDrv hxR j)
  exact ⟨hasSafeLaw_cond hS (hasSafeLaw_map hΦ (isWeakPath_canon _ _) hWa hVLa hVRa measurable_canonFld hlaw),
    hasSafeMembers_cond hS (hasSafeMembers_map hΦ measurable_canonFld hmem), hthr, hint⟩

end Space

/-! ### The raised chart field is a transport of the original field -/

section Field

variable {κ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h h' Hc : Ω → DistOn upperHalfPlaneOpens}
  {b' : ℝ → ℝ} {J' : Finset ℝ} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}

/-- **GW2's raised chart field is the original field read in the relative chart of the counterflow record**, with
coefficients `1, specOffset κ + θχ(κ), χ(κ)`, almost surely on `{s < ζ, γ(s) ∈ ℍ}`. -/
theorem ae_raised_eq_chartTransport_relChart (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω)) (s : ℝ≥0)
    (hHc : ∀ᵐ ω ∂P, γ ω s ∈ H →
      IsChartTransport (jointChart (fun r : ℝ => W r.toNNReal ω) s) 1 (specOffset κ) (chiC κ) (h ω) (Hc ω))
    (θ : ℝ) :
    ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζ ω → γ ω s ∈ H →
      Exist.flowField 0 (θ * chiC κ) (Hc ω) = Chart.chartTransport (isConformal_relChart (gb6Rec s W ζ ω)) 1
        (specOffset κ + θ * chiC κ) (chiC κ) (h ω) := by
  filter_upwards [ae_gb6RecGood hcf hγ s, hHc] with ω hg hHcω hs hsH
  obtain ⟨⟨-, hch, -⟩, -, hr⟩ := hg hs
  have hc : relChart (gb6Rec s W ζ ω) = jointChart (fun r : ℝ => W r.toNNReal ω) s := by
    rw [relChart_eq_jointChart hr]
    unfold jointChart
    rw [hch]
  have hT := hHcω hsH
  rw [← hc] at hT
  have hrel := isConformal_relChart (gb6Rec s W ζ ω)
  have e : Hc ω = Chart.chartTransport hrel 1 (specOffset κ) (chiC κ) (h ω) :=
    hT.unique hrel (CondDriverBridge.isChartTransport_chartTransport_of_continuousOn hrel
      (continuousOn_lift_relChart _) 1 (specOffset κ) (chiC κ) (h ω))
  rw [e]
  ext φ
  rw [WangWu.Shift.flowField_zero_apply, Chart.chartTransport_apply', Chart.chartTransport_apply',
    Chart.oneDist_apply]
  ring

end Field

/-! ### The assembly -/

section Assembly

variable {κ θ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h h' Hc : Ω → DistOn upperHalfPlaneOpens} {b b' : ℝ → ℝ} {J J' : Finset ℝ} {W Wα : ℝ≥0 → Ω → ℝ}
  {ζ ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {s : ℝ≥0} {c' : BoundaryWord} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
  {GT : Set Ω}

/-- GW2's live event of the type `w`: the counterflow record lies in the record event and its raised joint word has
type `w`. -/
def liveEvGW2 (κ θ : ℝ) (c' : BoundaryWord) (s : ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (w : WordType) : Set Ω :=
  gb6Rec s W ζ ⁻¹' (gb6TS s ∩ {r | wordType κ (gw2Word κ θ c' r) = w})

/-- The typed left marks of GW2's raised word, read from the record. -/
abbrev typedLGW2 (κ θ : ℝ) (c' : BoundaryWord) (w : WordType) (y : Supp8.Q3Stop.CanonSpace) : Fin w.1 → ℝ :=
  typedXL κ w (gw2Word κ θ c' y.1)

/-- The typed right marks of GW2's raised word, read from the record. -/
abbrev typedRGW2 (κ θ : ℝ) (c' : BoundaryWord) (w : WordType) (y : Supp8.Q3Stop.CanonSpace) : Fin w.2.1 → ℝ :=
  typedXR κ w (gw2Word κ θ c' y.1)

/-- GW2's clock at the physical lines: `a(t) = min(physClock t, V)` with the extended flow line explored and the
counterflow retained. -/
abbrev gw2LineClock (s : ℝ≥0) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (GT : Set Ω)
    (V : Ω → ℝ≥0∞) (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  min (physClock s (regW s Wα ζα) W ζ GT t ω) (V ω)

/-- **`HasRelSafe` for one GW2 version and one word type from GW2's line data** (GB6's `hasRelSafe_of_lines` with the
curves exchanged; conditional helper: the line data, the threshold clause and the integrability are hypotheses). -/
theorem hasRelSafe_of_lines_gw2 (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω))
    (hfl : IsFlowLineDriver κ b J θ P h Wα ζα) (hhm : Measurable h) (hHcm : Measurable Hc)
    (hHc : ∀ᵐ ω ∂P, γ ω s ∈ H →
      IsChartTransport (jointChart (fun r : ℝ => W r.toNNReal ω) s) 1 (specOffset κ) (chiC κ) (h ω) (Hc ω))
    (hver : HullId.IsGB6RelVersionR s P (regW s Wα ζα) W ζ (extTr s Wα ζα α) γ R V)
    (hGT : ∀ ω ∈ GT, PhysGood s (regW s Wα ζα) W ζ (extTr s Wα ζα α) γ ω) (hGTm : MeasurableSet GT)
    (hGTae : ∀ᵐ ω ∂P, ω ∈ GT ↔ gb6Rec s W ζ ω ∈ gb6TS s) (w : WordType)
    -- the line data
    (𝒢L : ℝ≥0 → MeasurableSpace Ω)
    (h𝒢L : ∀ t, physFilt (measurable_recOf_cfE hcf s).2 (measurable_regW hfl s) P t ≤ 𝒢L t)
    (h𝒢Lm : ∀ t, 𝒢L t ≤ mΩ) (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (hker : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ liveEvGW2 κ θ c' s W ζ w →
      gw2LineClock s Wα ζα W ζ GT V t ω < V ω →
      tsupport φ ⊆ (relChart (gb6Rec s W ζ ω)).2.1 ''
        (H \ fwdHull (fun r : ℝ => R r.toNNReal ω) (gw2LineClock s Wα ζα W ζ GT V t ω).toNNReal) →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢L t] ω =
        Complex.exp (Complex.I * (M t ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((relChart (gb6Rec s W ζ ω)).2.1 '' (H \ fwdHull
            (fun r : ℝ => R r.toNNReal ω) (gw2LineClock s Wα ζα W ζ GT V t ω).toNNReal)) φ φ : ℝ) : ℂ)))
    (hmean : ∀ (t : ℝ≥0) (ψ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ liveEvGW2 κ θ c' s W ζ w →
      gw2LineClock s Wα ζα W ζ GT V t ω < V ω →
      Disjoint (tsupport ψ) (fwdHull (fun r : ℝ => R r.toNNReal ω) (gw2LineClock s Wα ζα W ζ GT V t ω).toNNReal) →
      Chart.chartTransport (isConformal_relChart (gb6Rec s W ζ ω)) 1 (specOffset κ + θ * chiC κ) (chiC κ)
          (M t ω) ψ =
        ∫ z, couplingMean κ (fun r : ℝ => R r.toNNReal ω) (gw2LineClock s Wα ζα W ζ GT V t ω).toNNReal
          (DomainMarkov.bheProc κ (typedRhoL w) (typedRhoR w) R
            (fun i t ω => geomLW canonDrv (typedLGW2 κ θ c' w) i t
              (gb6Rec s W ζ ω, relVar (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω)) R V ω))
            (fun j t ω => geomRW canonDrv (typedRGW2 κ θ c' w) j t
              (gb6Rec s W ζ ω, relVar (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω)) R V ω)) ω
            (gw2LineClock s Wα ζα W ζ GT V t ω).toNNReal) z * ψ z)
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P)
    (ℋ : ℝ≥0 → MeasurableSpace Ω)
    (h𝓖ℋ : ∀ t, physFilt (measurable_recOf_cfE hcf s).2 (measurable_regW hfl s) P t ≤ ℋ t)
    (hℋ : ∀ t, ℋ t ≤ mΩ) (B : ℝ≥0 → Ω → Set ℂ) (hBm : ∀ t, Measurable[mΩ, hittingSigma] (B t))
    (hBc : ∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω))
    (hloc : ∀ t, WholeField.IsHistoryAvoidanceLocal (ℋ t) (B t) (WholeField.centredField h u₀) P)
    (hBK : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ liveEvGW2 κ θ c' s W ζ w → gw2LineClock s Wα ζα W ζ GT V t ω < V ω →
      H \ B t ω = (relChart (gb6Rec s W ζ ω)).2.1 ''
        (H \ fwdHull (fun r : ℝ => R r.toNNReal ω) (gw2LineClock s Wα ζα W ζ GT V t ω).toNNReal))
    (hSψ : ∀ (ψ : TestOn upperHalfPlaneOpens) t,
      MeasurableSet[physFilt (measurable_recOf_cfE hcf s).2 (measurable_regW hfl s) P t]
        {ω | gw2LineClock s Wα ζα W ζ GT V t ω < V ω ∧ Disjoint (tsupport ψ)
          (fwdHull (fun r : ℝ => R r.toNNReal ω) (gw2LineClock s Wα ζα W ζ GT V t ω).toNNReal)})
    (hSb : ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t,
      MeasurableSet[physFilt (measurable_recOf_cfE hcf s).2 (measurable_regW hfl s) P t]
        {ω | gw2LineClock s Wα ζα W ζ GT V t ω < V ω ∧ Disjoint (Coupling.ballsK Fb)
          (fwdHull (fun r : ℝ => R r.toNNReal ω) (gw2LineClock s Wα ζα W ζ GT V t ω).toNNReal)})
    -- the threshold and integrability clauses
    (hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun y => canonFld y φ)
      ((P.map fun ω => (gb6Rec s W ζ ω, relVar (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω)) R V ω))[|
        typeEvent κ w (gw2Word κ θ c') (gb6TS s)]))
    (hthr : ∀ᵐ y ∂((P.map fun ω => (gb6Rec s W ζ ω,
        relVar (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω)) R V ω))[|typeEvent κ w (gw2Word κ θ c') (gb6TS s)]),
      canonStp y ≤ thr (typedRhoL w) (typedRhoR w) canonDrv (fun y => typedXL κ w (gw2Word κ θ c' y.1))
        (fun y => typedXR κ w (gw2Word κ θ c' y.1)) y) :
    HasRelSafe κ w (gw2Word κ θ c') (gb6TS s)
      (P.map fun ω => (gb6Rec s W ζ ω, relVar (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω)) R V ω)) := by
  have hrec : Measurable (gb6Rec s W ζ) := (measurable_recOf_cfE hcf s).2
  have hWm : ∀ r, Measurable (regW s Wα ζα r) := measurable_regW hfl s
  have hβ := measurable_gw2Word κ θ c'
  have hE := measurableSet_gb6TS s
  have hRm := hver.1.1
  have hVm := hver.1.2.2.2.2.1
  have hRc := hver.1.2.1
  have hR0 := hver.1.2.2.1
  have hHrm : Measurable fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω) :=
    (Exist.measurable_flowField 0 _).comp hHcm
  have hGTm' : ∀ t, MeasurableSet[physFilt hrec hWm P t] GT := fun t =>
    measurableSet_goodSet_physFilt hrec hWm hGTm hGTae t
  set Φ : Ω → Supp8.Q3Stop.CanonSpace := fun ω =>
    (gb6Rec s W ζ ω, relVar (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω)) R V ω) with hΦdef
  have hΦ : Measurable Φ := hrec.prodMk (measurable_relVar hHrm hRm hVm)
  have hF : Φ ⁻¹' typeEvent κ w (gw2Word κ θ c') (gb6TS s) = liveEvGW2 κ θ c' s W ζ w := rfl
  have hF0 : MeasurableSet[physFilt hrec hWm P 0] (liveEvGW2 κ θ c' s W ζ w) :=
    measurable_rec_physFilt hrec hWm 0 (hE.inter ((measurable_wordType κ).comp hβ
      (measurableSet_singleton w)))
  have hWd : (fun t ω => canonDrv t (Φ ω)) = R := by
    funext t ω
    exact relDrv_relVar (hRc ω) (hR0 ω) t
  -- the raised chart field is the transport of `h` on the live event
  have hX : ∀ᵐ ω ∂P, ω ∈ liveEvGW2 κ θ c' s W ζ w →
      Chart.chartTransport (isConformal_relChart (gb6Rec s W ζ ω)) 1 (specOffset κ + θ * chiC κ) (chiC κ)
        (h ω) = canonFld (Φ ω) := by
    filter_upwards [ae_raised_eq_chartTransport_relChart hcf hγ s hHc θ, ae_gb6RecGood hcf hγ s]
      with ω hω hg hωF
    obtain ⟨hs, hsH⟩ := (mem_gb6TS_iff hg).2 hωF.1
    exact (hω hs hsH).symm
  have hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ liveEvGW2 κ θ c' s W ζ w → (q : ℝ≥0∞) < V ω →
      ∃ t, (q : ℝ≥0∞) ≤ gw2LineClock s Wα ζα W ζ GT V t ω := fun q =>
    reach_min_physClock hGT hver.1 hGTae (Eventually.of_forall fun ω hω => hω.1) q
  have hreg : ∀ᵐ ω ∂P, ω ∈ liveEvGW2 κ θ c' s W ζ w → DomainMarkov.Aux79.IsForceReg R
      (fun i t ω => geomLW canonDrv (typedLGW2 κ θ c' w) i t (Φ ω))
      (fun j t ω => geomRW canonDrv (typedRGW2 κ θ c' w) j t (Φ ω)) V ω := by
    refine Eventually.of_forall fun ω _ => ?_
    have h1 := isForceReg_thr (fun y => canonDrv_zero y) (fun y => continuous_canonDrv y) (typedLGW2 κ θ c' w)
      (typedRGW2 κ θ c' w) canonStp (Φ ω)
    rw [← hWd]
    exact h1
  have hdom : ∀ z, MeasurableSet[physFilt hrec hWm P 0]
      {ω | z ∈ (relChart (gb6Rec s W ζ ω)).dom} := fun z =>
    measurable_rec_physFilt hrec hWm 0 (measurableSet_mem_dom_relChart z)
  have hfwd : ∀ z, Measurable[physFilt hrec hWm P 0]
      ({ω | z ∈ (relChart (gb6Rec s W ζ ω)).dom}.indicator fun ω => (relChart (gb6Rec s W ζ ω)).1 z) :=
    fun z => (measurable_indicator_fwd_relChart z).comp (measurable_rec_physFilt hrec hWm 0)
  have hliftm : ∀ z, Measurable[physFilt hrec hWm P 0]
      ({ω | z ∈ (relChart (gb6Rec s W ζ ω)).dom}.indicator fun ω => (relChart (gb6Rec s W ζ ω)).2.2 z) :=
    fun z => (measurable_indicator_lift_relChart z).comp (measurable_rec_physFilt hrec hWm 0)
  have h𝓗' := fun q D (hD : MeasurableSet[Coupling.filtrationComap canonFilt hΦ q] D) t =>
    measurableSet_inter_le_min_of_canonFilt hGT hrec hWm hGTm' hver hHrm q hD t
  -- (S)
  have hlaw : HasSafeLaw κ (typedRhoL w) (typedRhoR w) P (Coupling.filtrationComap canonFilt hΦ)
      (liveEvGW2 κ θ c' s W ζ w) V R (fun i t ω => geomLW canonDrv (typedLGW2 κ θ c' w) i t (Φ ω))
      (fun j t ω => geomRW canonDrv (typedRGW2 κ θ c' w) j t (Φ ω))
      (fun ω => Chart.chartTransport (isConformal_relChart (gb6Rec s W ζ ω)) 1 (specOffset κ + θ * chiC κ)
        (chiC κ) (h ω)) :=
    Theorem14.BW1Lines.hasSafeLaw_life_of_lineKernel hF0 (fun ω => isConformal_relChart (gb6Rec s W ζ ω))
      hdom hfwd hliftm (fun ω => continuousOn_lift_relChart (gb6Rec s W ζ ω)) hhm
      (specOffset κ + θ * chiC κ) (chiC κ) (continuous_min_physClock hGT) (monotone_min_physClock hGT)
      (min_physClock_zero hGT) (measurable_min_physClock hGT hrec hWm hGTm' hver) h𝓗' V hreach hreg hSψ 𝒢L
      h𝒢L h𝒢Lm M hker hmean
  -- (L)
  have hmem : HasSafeMembers P (Coupling.filtrationComap canonFilt hΦ) (liveEvGW2 κ θ c' s W ζ w) V R
      (fun ω => Chart.chartTransport (isConformal_relChart (gb6Rec s W ζ ω)) 1 (specOffset κ + θ * chiC κ)
        (chiC κ) (h ω)) :=
    Theorem14.BW1Lines.hasSafeMembers_life_of_lineLocal
      (VL := fun i t ω => geomLW canonDrv (typedLGW2 κ θ c' w) i t (Φ ω))
      (VR := fun j t ω => geomRW canonDrv (typedRGW2 κ θ c' w) j t (Φ ω)) hhm hu₀ hh0
      (fun ω => isConformal_relChart (gb6Rec s W ζ ω)) hdom hfwd hliftm
      (fun ω => continuousOn_lift_relChart (gb6Rec s W ζ ω))
      (fun ω => harmonicOnNhd_lift_relChart (gb6Rec s W ζ ω)) (specOffset κ + θ * chiC κ) (chiC κ)
      (continuous_min_physClock hGT) (monotone_min_physClock hGT) (min_physClock_zero hGT)
      (measurable_min_physClock hGT hrec hWm hGTm' hver) h𝓗' V hreach hreg hSb ℋ h𝓖ℋ hℋ B hBm hBc hloc hBK
  refine hasRelSafe_of_space_cond hβ hE hrec hHrm hRm hVm ?_ ?_ hint hthr
  · rw [hF, hWd]
    exact hasSafeLaw_congr_fld hX hlaw
  · rw [hF, hWd]
    exact hasSafeMembers_congr_fld hX hmem

end Assembly

end InteractingSLE.Theorem14.GW2Rd
