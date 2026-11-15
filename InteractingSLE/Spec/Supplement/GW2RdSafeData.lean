/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RdSafeLines
import InteractingSLE.Spec.Supplement.GW2SfIntegrable
import InteractingSLE.Spec.Supplement.GW2RdHitEnd

/-!
# GW2's relative safe law (K2's (S), (L)), part 3: the reduction to GW2's line data

Packet PROVE-GW2-RELDET. `GW2RdSafeStatement` (the last input of GW2's root determination besides Theorems 1.2–1.3)
asks the four clauses of `Q3Stop.HasRelSafe` for every GW2 version and word type. This file reduces it to two named
statements, by GB6's route (`Supp8.RelSafeS.gb6RelSafeRStatement_of_lineData`) with the curves exchanged:

* **`HasGW2LineData`** (GW2's analogue of `HasGB6LineData` + `HasGB6SafeMeas`): the line kernels and means at the
  physical lines (Aux. 77/79 with the flow line explored), the history-marked locality of the physical union, and the
  physicality of the safe events, for the clock `a(t) = min(physClock t, V)` of the exchanged instance;
  **`GW2RdLineDataStatement`**: it, for every good event and version;
* **`GW2RdThrStatement`**: the threshold clause of `HasRelSafe` (the physical collision exclusion; PROVE-GW2-SAFE's
  `GW2Sf.ae_canonStp_le_thr_gw2_of_precontact_groups` gives it from its `hgroups`).

Everything else is proved: the good event (`exists_goodSet_gw2`), the clock layer and K2's engines
(`hasRelSafe_of_lines_gw2`), the chart field (`ae_raised_eq_chartTransport_relChart`), and the integrability
(`GW2Sf.integrable_canonFld_gw2`). **`gw2RdSafeStatement_of_lineData_thr`**, and with round 4 of this packet
**`gw2JointDetC2Statement_of_thm12_thm13_lineData_thr`**: GW2's root determination from Theorems 1.2–1.3, GW2's line
data and the threshold clause. Conditional helpers with distinct names.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull chiC zeroGFFTestCov)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop Supp8.RelSafe Supp8.RelSafeS Restart
  Restart.DomainMarkov.K2 Restart.FCDet Sec7.PocketTraversal GW2TipSystem GW2JointKernel

section Data

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **GW2's line data** (GB6's `HasGB6LineData` and `HasGB6SafeMeas` with the curves exchanged): for the extended flow
line explored in physical time and the counterflow retained, a good event `GT`, a version `(R, V)` and a type `w`,
with the clock `a(t) = gw2LineClock … t`: the conditioning σ-algebras `𝒢L t ⊇ 𝓖_t`, the line means `M t` with the
Gaussian line kernels of the ORIGINAL field `h` and the chart transport of `M t` (coefficients
`1, specOffset κ + θχ(κ), χ(κ)`) equal to the canonical relative mean, the history-marked locality of the physical
union `B t` for the centred field with marks `ℋ t ⊇ 𝓖_t`, and the physicality of the safe events. -/
def HasGW2LineData (κ θ : ℝ) (c' : BoundaryWord) (P : Measure Ω) (h Hc : Ω → DistOn upperHalfPlaneOpens)
    (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (GT : Set Ω) (s : ℝ≥0)
    (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (hrec : Measurable (gb6Rec s W ζ))
    (hWm : ∀ r, Measurable (regW s Wα ζα r)) (w : WordType) : Prop :=
  ∃ (𝒢L : ℝ≥0 → MeasurableSpace Ω) (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens) (u₀ : ℂ → ℝ)
    (ℋ : ℝ≥0 → MeasurableSpace Ω) (B : ℝ≥0 → Ω → Set ℂ),
    (∀ t, physFilt hrec hWm P t ≤ 𝒢L t) ∧ (∀ t, 𝒢L t ≤ mΩ) ∧
    (∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ liveEvGW2 κ θ c' s W ζ w →
      gw2LineClock s Wα ζα W ζ GT V t ω < V ω →
      tsupport φ ⊆ (relChart (gb6Rec s W ζ ω)).2.1 ''
        (H \ fwdHull (fun r : ℝ => R r.toNNReal ω) (gw2LineClock s Wα ζα W ζ GT V t ω).toNNReal) →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢L t] ω =
        Complex.exp (Complex.I * (M t ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((relChart (gb6Rec s W ζ ω)).2.1 '' (H \ fwdHull
            (fun r : ℝ => R r.toNNReal ω) (gw2LineClock s Wα ζα W ζ GT V t ω).toNNReal)) φ φ : ℝ) : ℂ))) ∧
    (∀ (t : ℝ≥0) (ψ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ liveEvGW2 κ θ c' s W ζ w →
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
            (gw2LineClock s Wα ζα W ζ GT V t ω).toNNReal) z * ψ z) ∧
    InnerProductSpace.HarmonicOnNhd u₀ H ∧
    LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P ∧
    (∀ t, physFilt hrec hWm P t ≤ ℋ t) ∧ (∀ t, ℋ t ≤ mΩ) ∧
    (∀ t, Measurable[mΩ, hittingSigma] (B t)) ∧ (∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω)) ∧
    (∀ t, WholeField.IsHistoryAvoidanceLocal (ℋ t) (B t) (WholeField.centredField h u₀) P) ∧
    (∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ liveEvGW2 κ θ c' s W ζ w → gw2LineClock s Wα ζα W ζ GT V t ω < V ω →
      H \ B t ω = (relChart (gb6Rec s W ζ ω)).2.1 ''
        (H \ fwdHull (fun r : ℝ => R r.toNNReal ω) (gw2LineClock s Wα ζα W ζ GT V t ω).toNNReal)) ∧
    (∀ (ψ : TestOn upperHalfPlaneOpens) t, MeasurableSet[physFilt hrec hWm P t]
      {ω | gw2LineClock s Wα ζα W ζ GT V t ω < V ω ∧ Disjoint (tsupport ψ)
        (fwdHull (fun r : ℝ => R r.toNNReal ω) (gw2LineClock s Wα ζα W ζ GT V t ω).toNNReal)}) ∧
    ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t, MeasurableSet[physFilt hrec hWm P t]
      {ω | gw2LineClock s Wα ζα W ζ GT V t ω < V ω ∧ Disjoint (Coupling.ballsK Fb)
        (fwdHull (fun r : ℝ => R r.toNNReal ω) (gw2LineClock s Wα ζα W ζ GT V t ω).toNNReal)}

end Data

/-! ### The named inputs -/

/-- **Named input: GW2's line data** (binders of `GW2RdSafeStatement`; for every good event of the exchanged instance,
every GW2 version and every type). -/
def GW2RdLineDataStatement : Prop :=
  ∀ (κ θ : ℝ), 0 < κ → κ < 4 → -(Real.pi / 2) ≤ θ → θ ≤ Real.pi / 2 →
  ∀ (Ω : Type u) (_mΩ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (h : Ω → DistOn upperHalfPlaneOpens) (b : ℝ → ℝ) (J : Finset ℝ)
    (W Wα : ℝ≥0 → Ω → ℝ) (ζ ζα : Ω → ℝ≥0∞) (γ α : Ω → ℝ≥0 → ℂ)
    (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
    IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J →
    IsPiecewiseConstantBoundaryData b' J' →
    (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω)) →
    ∀ (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ),
    (∀ i : Fin (flowLineNL b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) b' J' 0 0 l) →
    (∀ i : Fin (flowLineNR b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) b' J' 0 0 l) →
    (∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop) →
    ∀ (hfl : IsFlowLineDriver κ b J θ P h Wα ζα),
    (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) →
    ¬ ForceWord.ThresholdCondition (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) 0 (flowLineXL b J 0)
      (flowLineXR b J 0) →
    ∀ (s : ℝ≥0) (Hc : Ω → DistOn upperHalfPlaneOpens), Measurable Hc →
    (∀ᵐ ω ∂P, γ ω s ∈ H →
      IsChartTransport (jointChart (fun r : ℝ => W r.toNNReal ω) s) 1 (specOffset κ) (chiC κ) (h ω) (Hc ω)) →
    ∀ c' : BoundaryWord, c'.jumps = J' → (∀ y ∉ J', c'.fn y = b' y) →
    ∀ GT : Set Ω, (∀ ω ∈ GT, PhysGood s (regW s Wα ζα) W ζ (extTr s Wα ζα α) γ ω) → MeasurableSet GT →
      (∀ᵐ ω ∂P, ω ∈ GT ↔ gb6Rec s W ζ ω ∈ gb6TS s) →
    ∀ (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞), IsGW2RelVersion s P W Wα ζ ζα γ α R V →
    ∀ w : WordType,
      HasGW2LineData κ θ c' P h Hc W ζ Wα ζα GT s R V (measurable_recOf_cfE hcf s).2 (measurable_regW hfl s) w

/-- **Named input: the threshold clause of GW2's relative safe law** (binders of `GW2RdSafeStatement`): the version
stop is below the continuation threshold of the raised relative word, under the conditioned image law. -/
def GW2RdThrStatement : Prop :=
  ∀ (κ θ : ℝ), 0 < κ → κ < 4 → -(Real.pi / 2) ≤ θ → θ ≤ Real.pi / 2 →
  ∀ (Ω : Type u) (_mΩ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (h : Ω → DistOn upperHalfPlaneOpens) (b : ℝ → ℝ) (J : Finset ℝ)
    (W Wα : ℝ≥0 → Ω → ℝ) (ζ ζα : Ω → ℝ≥0∞) (γ α : Ω → ℝ≥0 → ℂ)
    (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
    IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J →
    IsPiecewiseConstantBoundaryData b' J' →
    (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω)) →
    IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ →
    (∀ i : Fin (flowLineNL b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) b' J' 0 0 l) →
    (∀ i : Fin (flowLineNR b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) b' J' 0 0 l) →
    (∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop) →
    IsFlowLineDriver κ b J θ P h Wα ζα →
    (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) →
    ¬ ForceWord.ThresholdCondition (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) 0 (flowLineXL b J 0)
      (flowLineXR b J 0) →
    ∀ (s : ℝ≥0) (Hc : Ω → DistOn upperHalfPlaneOpens), Measurable Hc →
    (∀ᵐ ω ∂P, γ ω s ∈ H →
      IsChartTransport (jointChart (fun r : ℝ => W r.toNNReal ω) s) 1 (specOffset κ) (chiC κ) (h ω) (Hc ω)) →
    ∀ c' : BoundaryWord, c'.jumps = J' → (∀ y ∉ J', c'.fn y = b' y) →
    ∀ (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞), IsGW2RelVersion s P W Wα ζ ζα γ α R V →
    ∀ w : WordType,
      ∀ᵐ y ∂((P.map fun ω => (gb6Rec s W ζ ω,
          relVar (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω)) R V ω))[|
            typeEvent κ w (gw2Word κ θ c') (gb6TS s)]),
        canonStp y ≤ thr (typedRhoL w) (typedRhoR w) canonDrv (fun y => typedXL κ w (gw2Word κ θ c' y.1))
          (fun y => typedXR κ w (gw2Word κ θ c' y.1)) y

/-! ### The wiring -/

/-- **`GW2RdSafeStatement` from GW2's line data and the threshold clause.** -/
theorem gw2RdSafeStatement_of_lineData_thr (hL : GW2RdLineDataStatement.{u}) (hT : GW2RdThrStatement.{u}) :
    GW2RdSafeStatement.{u} := by
  intro κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hh hb' hTr hcf hadmL hadmR hcomp hfl hα hseed
    s Hc hHcm hHc c' hcJ hcb R V hver w
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := hcomp.mono fun ω hω => hω.1
  have hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω) :=
    hcomp.mono fun ω hω => by rw [hω.1]; exact hω.2.1
  obtain ⟨GT, hGT, hGTm, hGTae⟩ := exists_goodSet_gw2 hκ hfl hα hseed hcf hγ hζ s
  obtain ⟨𝒢L, M, u₀, ℋ, B, h𝒢L, h𝒢Lm, hker, hmean, hu₀, hh0, h𝓖ℋ, hℋ, hBm, hBc, hloc, hBK, hSψ, hSb⟩ :=
    hL κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hh hb' hTr hcf hadmL hadmR hcomp hfl hα hseed
      s Hc hHcm hHc c' hcJ hcb GT hGT hGTm hGTae R V hver w
  exact hasRelSafe_of_lines_gw2 hcf hγ hfl hh.1 hHcm hHc hver.1.1 hGT hGTm hGTae w 𝒢L h𝒢L h𝒢Lm M hker hmean hu₀
    hh0 ℋ h𝓖ℋ hℋ B hBm hBc hloc hBK hSψ hSb
    (fun φ => GW2Sf.integrable_canonFld_gw2 hκ hb' hTr hcf hζ hγ s hHcm hHc θ c' hver.1.1.1.1
      hver.1.1.1.2.2.2.2.1 w φ)
    (hT κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hh hb' hTr hcf hadmL hadmR hcomp hfl hα
      hseed s Hc hHcm hHc c' hcJ hcb R V hver w)

/-- **GW2's root determination from Theorems 1.2–1.3, GW2's line data and the threshold clause.** -/
theorem gw2JointDetC2Statement_of_thm12_thm13_lineData_thr (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) (hL : GW2RdLineDataStatement.{u})
    (hT : GW2RdThrStatement.{u}) : GW2JointKernel.GW2JointDetC2Statement.{u} :=
  gw2JointDetC2Statement_of_thm12_thm13_safe h12p₀ h13₀ h13 (gw2RdSafeStatement_of_lineData_thr hL hT)

end InteractingSLE.Theorem14.GW2Rd
