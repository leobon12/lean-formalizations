/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RdSafeUnion

/-!
# GW2's relative safe law (K2's (S), (L)), part 8: locality and union mean, split

Packet PROVE-GW2-RELDET. `GW2RdPhysUnionStatement` (the last input of K2's (S)/(L) for GW2) asks a marked-local
version of the physical union together with the union mean identification. The two halves are independent
mathematics; this file names them separately:

* **`HasGW2UnionLocality`**: `HasGW2PhysUnion` without its mean clause (harmonic `u₀`, the centred field a zero-boundary
  GFF, marks `ℋ t ⊇ 𝓖_t`, `B t` hitting-measurable and relatively closed, history-marked local at every `t`, and
  almost surely the physical union on `GT ∩ {a(t) < V}`); **`GW2RdUnionLocalityStatement`**: such `(u₀, ℋ, B)` exist;
* **`GW2RdUnionMeanStatement`**: for EVERY `(u₀, ℋ, B)` with `HasGW2UnionLocality`, the union mean identification
  (every local-set mean of `B t`, plus `u₀`, transported through the relative chart of the counterflow record, is the
  canonical relative mean at `a(t)` on the live event and `{a(t) < V}` for tests off the relative hull);
* **`gw2RdPhysUnionStatement_of_locality_mean`**, and the root determination
  **`gw2JointDetC2Statement_of_thm12_thm13_locality_mean_thr`**.

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

/-- **The locality half of `HasGW2PhysUnion`** for given `(u₀, ℋ, B)`. -/
def HasGW2UnionLocality (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (GT : Set Ω) (s : ℝ≥0) (V : Ω → ℝ≥0∞)
    (hrec : Measurable (gb6Rec s W ζ)) (hWm : ∀ r, Measurable (regW s Wα ζα r)) (u₀ : ℂ → ℝ)
    (ℋ : ℝ≥0 → MeasurableSpace Ω) (B : ℝ≥0 → Ω → Set ℂ) : Prop :=
  InnerProductSpace.HarmonicOnNhd u₀ H ∧
    LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P ∧
    (∀ t, physFilt hrec hWm P t ≤ ℋ t) ∧ (∀ t, ℋ t ≤ mΩ) ∧
    (∀ t, Measurable[mΩ, hittingSigma] (B t)) ∧ (∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω)) ∧
    (∀ t, WholeField.IsHistoryAvoidanceLocal (ℋ t) (B t) (WholeField.centredField h u₀) P) ∧
    ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ GT → gw2LineClock s Wα ζα W ζ GT V t ω < V ω →
      B t ω = Supp8.Q3Rel.invHull (rdrv (gb6Rec s W ζ ω)) s ∪ fwdHull (fun r : ℝ => regW s Wα ζα r.toNNReal ω) t

/-- **The union mean clause of `HasGW2PhysUnion`** for given `(u₀, B)`. -/
def HasGW2UnionMean (κ θ : ℝ) (c' : BoundaryWord) (P : Measure Ω) (h Hc : Ω → DistOn upperHalfPlaneOpens)
    (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (GT : Set Ω) (s : ℝ≥0)
    (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (w : WordType) (u₀ : ℂ → ℝ) (B : ℝ≥0 → Ω → Set ℂ) : Prop :=
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

theorem hasGW2PhysUnion_of_locality_mean {κ θ : ℝ} {c' : BoundaryWord} {P : Measure Ω}
    {h Hc : Ω → DistOn upperHalfPlaneOpens} {W Wα : ℝ≥0 → Ω → ℝ} {ζ ζα : Ω → ℝ≥0∞} {GT : Set Ω} {s : ℝ≥0}
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {hrec : Measurable (gb6Rec s W ζ)} {hWm : ∀ r, Measurable (regW s Wα ζα r)}
    {w : WordType} {u₀ : ℂ → ℝ} {ℋ : ℝ≥0 → MeasurableSpace Ω} {B : ℝ≥0 → Ω → Set ℂ}
    (hL : HasGW2UnionLocality P h W ζ Wα ζα GT s V hrec hWm u₀ ℋ B)
    (hM : HasGW2UnionMean κ θ c' P h Hc W ζ Wα ζα GT s R V w u₀ B) :
    HasGW2PhysUnion κ θ c' P h Hc W ζ Wα ζα GT s R V hrec hWm w := by
  obtain ⟨hu₀, hh0, h𝓖ℋ, hℋ, hBm, hBc, hloc, hBU⟩ := hL
  exact ⟨u₀, ℋ, B, hu₀, hh0, h𝓖ℋ, hℋ, hBm, hBc, hloc, hBU, hM⟩

end Local

/-! ### The named inputs -/

/-- **Named input: a marked-local version of GW2's physical union** (binders of `GW2RdPhysUnionStatement` without the
type). -/
def GW2RdUnionLocalityStatement : Prop :=
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
    ∃ (u₀ : ℂ → ℝ) (ℋ : ℝ≥0 → MeasurableSpace Ω) (B : ℝ≥0 → Ω → Set ℂ),
      HasGW2UnionLocality P h W ζ Wα ζα GT s V (measurable_recOf_cfE hcf s).2 (measurable_regW hfl s) u₀ ℋ B

/-- **Named input: GW2's union mean identification** (binders of `GW2RdPhysUnionStatement`), for every marked-local
version of the physical union. -/
def GW2RdUnionMeanStatement : Prop :=
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
    ∀ (u₀ : ℂ → ℝ) (ℋ : ℝ≥0 → MeasurableSpace Ω) (B : ℝ≥0 → Ω → Set ℂ),
      HasGW2UnionLocality P h W ζ Wα ζα GT s V (measurable_recOf_cfE hcf s).2 (measurable_regW hfl s) u₀ ℋ B →
      HasGW2UnionMean κ θ c' P h Hc W ζ Wα ζα GT s R V w u₀ B

theorem gw2RdPhysUnionStatement_of_locality_mean (hL : GW2RdUnionLocalityStatement.{u})
    (hM : GW2RdUnionMeanStatement.{u}) : GW2RdPhysUnionStatement.{u} := by
  intro κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hh hb' hTr hcf hadmL hadmR hcomp hfl hα hseed
    s Hc hHcm hHc c' hcJ hcb GT hGT hGTm hGTae R V hver w
  obtain ⟨u₀, ℋ, B, hloc⟩ := hL κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hh hb' hTr hcf hadmL
    hadmR hcomp hfl hα hseed s Hc hHcm hHc c' hcJ hcb GT hGT hGTm hGTae R V hver
  exact hasGW2PhysUnion_of_locality_mean hloc (hM κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hh
    hb' hTr hcf hadmL hadmR hcomp hfl hα hseed s Hc hHcm hHc c' hcJ hcb GT hGT hGTm hGTae R V hver w u₀ ℋ B hloc)

/-- **GW2's root determination from Theorems 1.2–1.3, the locality and union mean statements, and the threshold
clause.** -/
theorem gw2JointDetC2Statement_of_thm12_thm13_locality_mean_thr (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u})
    (hL : GW2RdUnionLocalityStatement.{u}) (hM : GW2RdUnionMeanStatement.{u}) (hT : GW2RdThrStatement.{u}) :
    GW2JointKernel.GW2JointDetC2Statement.{u} :=
  gw2JointDetC2Statement_of_thm12_thm13_physUnion_thr h12p₀ h13₀ h13
    (gw2RdPhysUnionStatement_of_locality_mean hL hM) hT

end InteractingSLE.Theorem14.GW2Rd
