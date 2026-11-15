/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RdSafeLocal
import InteractingSLE.Spec.Supplement.GB6LineL4

/-!
# GW2's relative safe law (K2's (S), (L)), part 5: the safe events are physical

Packet PROVE-GW2-RELDET. GB6's `GB6LineL.hasGB6SafeMeas_of` is stated for an arbitrary explored driver `W`, retained
curve `(Wα, ζα, α)`, good event and R-form version; at GW2's exchanged instance (explored: the extended flow line
`regW s Wα ζα`, retained: the counterflow) it gives the two safe-event clauses of `HasGW2LineLocal`. What remains of
GW2's line data is then:

* **`HasGW2UnionLocal`**: the history-marked locality of a physical union `B_t` for the centred original field, its
  complement the inverse relative chart image of the complement of the relative hull on `{a(t) < V}`, and the union
  mean identification;
* **`GW2RdUnionLocalStatement`** (binders of `GW2RdLineLocalStatement`), `gw2RdLineLocalStatement_of_union`,
  **`gw2RdSafeStatement_of_unionLocal_thr`**, **`gw2JointDetC2Statement_of_thm12_thm13_unionLocal_thr`**.

Conditional helpers with distinct names.
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
  Restart.DomainMarkov.K2 Restart.FCDet Sec7.PocketTraversal GW2TipSystem GW2JointKernel LocalSets

section Local

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- **GW2's marked union locality and union mean identification at the physical lines** (`HasGW2LineLocal` without its
safe-event clauses). -/
def HasGW2UnionLocal (κ θ : ℝ) (c' : BoundaryWord) (P : Measure Ω) (h Hc : Ω → DistOn upperHalfPlaneOpens)
    (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (GT : Set Ω) (s : ℝ≥0)
    (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (hrec : Measurable (gb6Rec s W ζ))
    (hWm : ∀ r, Measurable (regW s Wα ζα r)) (w : WordType) : Prop :=
  ∃ (u₀ : ℂ → ℝ) (ℋ : ℝ≥0 → MeasurableSpace Ω) (B : ℝ≥0 → Ω → Set ℂ),
    InnerProductSpace.HarmonicOnNhd u₀ H ∧
    LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P ∧
    (∀ t, physFilt hrec hWm P t ≤ ℋ t) ∧ (∀ t, ℋ t ≤ mΩ) ∧
    (∀ t, Measurable[mΩ, hittingSigma] (B t)) ∧ (∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω)) ∧
    (∀ t, WholeField.IsHistoryAvoidanceLocal (ℋ t) (B t) (WholeField.centredField h u₀) P) ∧
    (∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ liveEvGW2 κ θ c' s W ζ w → gw2LineClock s Wα ζα W ζ GT V t ω < V ω →
      H \ B t ω = (relChart (gb6Rec s W ζ ω)).2.1 ''
        (H \ fwdHull (fun r : ℝ => R r.toNNReal ω) (gw2LineClock s Wα ζα W ζ GT V t ω).toNNReal)) ∧
    ∀ (t : ℝ≥0) (g : Ω → DistOn upperHalfPlaneOpens),
      IsLocalSetMean (B t) (WholeField.centredField h u₀) P g →
      ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ liveEvGW2 κ θ c' s W ζ w →
        gw2LineClock s Wα ζα W ζ GT V t ω < V ω →
        Disjoint (tsupport ψ) (fwdHull (fun r : ℝ => R r.toNNReal ω)
          (gw2LineClock s Wα ζα W ζ GT V t ω).toNNReal) →
        Chart.chartTransport (isConformal_relChart (gb6Rec s W ζ ω)) 1 (specOffset κ + θ * chiC κ) (chiC κ)
            (g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) ψ =
          ∫ z, couplingMean κ (fun r : ℝ => R r.toNNReal ω) (gw2LineClock s Wα ζα W ζ GT V t ω).toNNReal
            (DomainMarkov.bheProc κ (typedRhoL w) (typedRhoR w) R
              (fun i t ω => geomLW canonDrv (typedLGW2 κ θ c' w) i t
                (gb6Rec s W ζ ω, relVar (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω)) R V ω))
              (fun j t ω => geomRW canonDrv (typedRGW2 κ θ c' w) j t
                (gb6Rec s W ζ ω, relVar (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω)) R V ω)) ω
              (gw2LineClock s Wα ζα W ζ GT V t ω).toNNReal) z * ψ z

/-- **`HasGW2UnionLocal ⇒ HasGW2LineLocal`**: the safe events are physical (`GB6LineL.hasGB6SafeMeas_of` at the
exchanged instance). -/
theorem hasGW2LineLocal_of_union {κ θ : ℝ} {c' : BoundaryWord} {P : Measure Ω}
    {h Hc : Ω → DistOn upperHalfPlaneOpens} {W Wα : ℝ≥0 → Ω → ℝ} {ζ ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}
    {GT : Set Ω} {s : ℝ≥0} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {hrec : Measurable (gb6Rec s W ζ)}
    {hWm : ∀ r, Measurable (regW s Wα ζα r)} {w : WordType}
    (hGT : ∀ ω ∈ GT, PhysGood s (regW s Wα ζα) W ζ (extTr s Wα ζα α) γ ω) (hGTm : MeasurableSet GT)
    (hGTae : ∀ᵐ ω ∂P, ω ∈ GT ↔ gb6Rec s W ζ ω ∈ gb6TS s)
    (hver : HullId.IsGB6RelVersionR s P (regW s Wα ζα) W ζ (extTr s Wα ζα α) γ R V)
    (hU : HasGW2UnionLocal κ θ c' P h Hc W ζ Wα ζα GT s R V hrec hWm w) :
    HasGW2LineLocal κ θ c' P h Hc W ζ Wα ζα GT s R V hrec hWm w := by
  obtain ⟨u₀, ℋ, B, hu₀, hh0, h𝓖ℋ, hℋ, hBm, hBc, hloc, hBK, hmean⟩ := hU
  obtain ⟨hSψ, hSb⟩ := Supp8.GB6LineL.hasGB6SafeMeas_of hGT hrec hWm hGTm hGTae hver
  exact ⟨u₀, ℋ, B, hu₀, hh0, h𝓖ℋ, hℋ, hBm, hBc, hloc, hBK, hmean, hSψ, hSb⟩

end Local

/-! ### The named input -/

/-- **Named input: GW2's marked union locality and union mean identification** (binders of
`GW2RdLineLocalStatement`). -/
def GW2RdUnionLocalStatement : Prop :=
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
      HasGW2UnionLocal κ θ c' P h Hc W ζ Wα ζα GT s R V (measurable_recOf_cfE hcf s).2 (measurable_regW hfl s) w

theorem gw2RdLineLocalStatement_of_union (hU : GW2RdUnionLocalStatement.{u}) : GW2RdLineLocalStatement.{u} := by
  intro κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hh hb' hTr hcf hadmL hadmR hcomp hfl hα hseed
    s Hc hHcm hHc c' hcJ hcb GT hGT hGTm hGTae R V hver w
  exact hasGW2LineLocal_of_union hGT hGTm hGTae hver.1.1 (hU κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J'
    h' hb hh hb' hTr hcf hadmL hadmR hcomp hfl hα hseed s Hc hHcm hHc c' hcJ hcb GT hGT hGTm hGTae R V hver w)

/-- **`GW2RdSafeStatement` from GW2's marked union locality and union mean identification and the threshold
clause.** -/
theorem gw2RdSafeStatement_of_unionLocal_thr (hU : GW2RdUnionLocalStatement.{u}) (hT : GW2RdThrStatement.{u}) :
    GW2RdSafeStatement.{u} :=
  gw2RdSafeStatement_of_lineLocal_thr (gw2RdLineLocalStatement_of_union hU) hT

/-- **GW2's root determination from Theorems 1.2–1.3, GW2's marked union locality and union mean identification, and
the threshold clause.** -/
theorem gw2JointDetC2Statement_of_thm12_thm13_unionLocal_thr (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) (hU : GW2RdUnionLocalStatement.{u})
    (hT : GW2RdThrStatement.{u}) : GW2JointKernel.GW2JointDetC2Statement.{u} :=
  gw2JointDetC2Statement_of_thm12_thm13_safe h12p₀ h13₀ h13 (gw2RdSafeStatement_of_unionLocal_thr hU hT)

end InteractingSLE.Theorem14.GW2Rd
