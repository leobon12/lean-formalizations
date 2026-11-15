/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6LineL2
import InteractingSLE.Spec.Supplement.RelSafeS6
import InteractingSLE.Spec.Supplement.RelSafeS7
import InteractingSLE.Spec.Supplement.RelSafeS8
import InteractingSLE.Spec.Exist.Param12Kernel
import InteractingSLE.Spec.Theorem15Inputs
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvYClosure

/-!
# GB6's line locality, part 3: the marked union locality and the reduction of `GB6LineLocalStatement`

Packet PROVE-GB6-LINELOCAL. The physical union of GB6's lines at counterflow time `t` is the retained set (the
inverted flow hull read from the flow's record, `GB6LineL.retSet`) together with the counterflow hull `K_t` read from
the counterflow's killed history, closed in `ℍ` (`unionSet`). With Theorems 1.2–1.3 (both curves have
field-determined killed histories; R48 allows them for GB6, which serves Theorem 1.4):

* (L0) the centring `u₀` is the counterflow's initial bounded harmonic extension and `h′ − u₀` is a zero-boundary GFF;
* (L1) **`isHistoryAvoidanceLocal_unionSet`**: the union is history-marked local for the centred counterflow-frame
  field with the marks `𝓕^α_s ∨ 𝓕^cf_t` (the flow's stopped σ-algebra at `s`, which contains the flow's record,
  `GB6LineL.exists_retained_marks`, and the counterflow's driving filtration at `t`,
  `RelSafeS.isHistoryAvoidanceLocal_cfHull`), joined by `WalkLaw.isHistoryAvoidanceLocal_union_of_det`; these marks
  contain the physical filtration `RelSafe.physFilt` at `t`;
* (L2) the shape of the union on the live event (`RelSafeS.ae_compl_union_eq_relChart`);
* the remaining two clauses are named: **`GB6LineMeanStatement`** (L3, the union mean identification, Aux. 79 at the
  physical lines, for every version of the physical union) and **`GB6SafeMeasStatement`** (L4, the safe events are
  physical);
* **`gb6LineLocalStatement_of_mean_safe`**, **`gb6HullDetStatement_of_mean_safe`**: `GB6LineLocalStatement` and
  Theorem 1.4's `GB6HullDetStatement` from Theorems 1.2–1.3, (L3) and (L4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull chiC)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE.Supp8.GB6LineL

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop Supp8.RelSafe Supp8.RelSafeS Restart
  Restart.DomainMarkov.K2 Restart.FCDet Sec7.PocketTraversal Sec7.StripSysField LocalSets

/-! ### Closing a random set in `ℍ` -/

section Closure

theorem relClosureH_subset_H (S : Set ℂ) : relClosureH S ⊆ H := inter_subset_left

theorem isOpen_H_diff_relClosureH (S : Set ℂ) : IsOpen (H \ relClosureH S) := by
  have e : H \ relClosureH S = H ∩ (closure (S ∩ H))ᶜ := by
    ext z
    simp only [relClosureH, Set.mem_sdiff, mem_inter_iff, mem_compl_iff]
    tauto
  rw [e]
  exact QuantumZipper.isOpen_H.inter isClosed_closure.isOpen_compl

variable {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **Closing in `ℍ` keeps the history-marked avoidance criterion** (the avoidance events of open subsets of `ℍ` do not
change). -/
theorem isHistoryAvoidanceLocal_relClosureH {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}
    (hloc : WholeField.IsHistoryAvoidanceLocal ℋ A h P) :
    WholeField.IsHistoryAvoidanceLocal ℋ (fun ω => relClosureH (A ω)) h P := by
  intro U G hUH hG hd F hF
  have e : {ω | Disjoint (relClosureH (A ω)) U} = {ω | Disjoint (A ω) U} := by
    ext ω
    exact FlowStopIdentCMI.disjoint_relClosureH_open_iff U.isOpen hUH
  rw [e]
  exact hloc U G hUH hG hd F hF

/-- **The closure in `ℍ` of a union of hitting-measurable random sets is hitting-measurable.** -/
theorem measurable_relClosureH_union {A K : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hK : Measurable[mΩ, hittingSigma] K) :
    Measurable[mΩ, hittingSigma] fun ω => relClosureH (A ω ∪ K ω) := by
  refine @measurable_generateFrom _ _ mΩ _ _ ?_
  rintro _ ⟨U, hU, hUH, rfl⟩
  have e : (fun ω => relClosureH (A ω ∪ K ω)) ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} =
      ({ω | Disjoint (A ω) U} ∩ {ω | Disjoint (K ω) U})ᶜ := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, mem_compl_iff, mem_inter_iff]
    rw [← Set.not_disjoint_iff_nonempty_inter, FlowStopIdentCMI.disjoint_relClosureH_open_iff hU hUH,
      disjoint_union_left]
  rw [e]
  exact ((hA (measurableSet_avoid hU hUH)).inter (hK (measurableSet_avoid hU hUH))).compl

/-- On a set whose complement in `ℍ` is open, closing in `ℍ` does not change the complement. -/
theorem H_diff_relClosureH_of_isOpen {S : Set ℂ} (hS : IsOpen (H \ S)) : H \ relClosureH S = H \ S := by
  ext z
  simp only [relClosureH, Set.mem_sdiff, mem_inter_iff, not_and]
  constructor
  · rintro ⟨hz, hcl⟩
    exact ⟨hz, fun hzS => hcl hz (subset_closure ⟨hzS, hz⟩)⟩
  · rintro ⟨hz, hzS⟩
    refine ⟨hz, fun _ hcl => ?_⟩
    obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.1 hcl _ hS ⟨hz, hzS⟩
    exact hw1.2 hw2.1

end Closure

/-! ### The physical union -/

/-- **GB6's physical union at counterflow time `t`**: the retained set and the counterflow hull read from its killed
history, closed in `ℍ`. -/
def unionSet {Ω : Type*} {nL nR : ℕ} (s : ℝ≥0) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (t : ℝ≥0) (ω : Ω) : Set ℂ :=
  relClosureH (retSet s Wα ζα ω ∪ Sec5.GlueCond.hullAt t (LawUnique.killedHistory W VL VR ζ ω))

/-! ### The named inputs (L3) and (L4) -/

/-- **GB6's union mean identification at the physical lines** (Aux. 79 at the lines of K2's lines step): the clause
of `RelSafeS.HasGB6LineLocal` for a centring `u₀` and a physical union `B`. -/
def HasGB6UnionMean {Ω : Type*} [MeasurableSpace Ω] (κ θ : ℝ) (c : BoundaryWord) (P : Measure Ω)
    (h' Hc : Ω → DistOn upperHalfPlaneOpens) (W Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (GT : Set Ω) (s : ℝ≥0)
    (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (w : WordType) (u₀ : ℂ → ℝ) (B : ℝ≥0 → Ω → Set ℂ) : Prop :=
  ∀ (t : ℝ≥0) (g : Ω → DistOn upperHalfPlaneOpens),
    IsLocalSetMean (B t) (WholeField.centredField h' u₀) P g →
    ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ liveEv κ θ c s Wα ζα w →
      min (physClock s W Wα ζα GT t ω) (V ω) < V ω →
      Disjoint (tsupport ψ) (fwdHull (fun r : ℝ => R r.toNNReal ω)
        (min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal) →
      Chart.chartTransport (isConformal_relChart (gb6Rec s Wα ζα ω)) 1 (2 * Real.pi * chiC (16 / κ))
          (chiC (16 / κ)) (g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) ψ =
        ∫ z, couplingMean (16 / κ) (fun r : ℝ => R r.toNNReal ω)
          (min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal
          (DomainMarkov.bheProc (16 / κ) (typedRhoL w) (typedRhoR w) R
            (fun i t ω => geomLW canonDrv (typedL κ θ c w) i t (gb6Rec s Wα ζα ω, relVar Hc R V ω))
            (fun j t ω => geomRW canonDrv (typedR κ θ c w) j t (gb6Rec s Wα ζα ω, relVar Hc R V ω)) ω
            (min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal) z * ψ z

/-- **Named input (L3): GB6's union mean identification** (binders of `RelSafeS.GB6LineLocalStatement`): for the
counterflow's initial extension `u₀` (with `h′ − u₀` a zero-boundary GFF) and every version `B` of the physical union
`retSet ∪ K_t` (closed in `ℍ`) that is a local set of `h′ − u₀`, the transport of every local-set mean of `B t`
through the relative chart is the canonical relative mean at `a(t)` on the live event. -/
def GB6LineMeanStatement : Prop :=
  ∀ (κ θ : ℝ), 0 < κ → κ < 4 → -(Real.pi / 2) ≤ θ → θ ≤ Real.pi / 2 →
  ∀ (Ω : Type u) (_mΩ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (b : ℝ → ℝ) (J : Finset ℝ)
    (W Wα : ℝ≥0 → Ω → ℝ) (ζ ζα : Ω → ℝ≥0∞) (γ α : Ω → ℝ≥0 → ℂ)
    (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
    IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J →
    IsPiecewiseConstantBoundaryData b' J' →
    (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
      (QuantumZipper.chiC (16 / κ)) (h ω) (h' ω)) →
    IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ →
    (∀ i : Fin (flowLineNL b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) b' J' 0 0 l) →
    (∀ i : Fin (flowLineNR b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) b' J' 0 0 l) →
    (∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop) →
    ∀ (_hfl : IsFlowLineDriver κ b J θ P h Wα ζα),
    (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) →
    ∀ (s : ℝ≥0) (Hc : Ω → DistOn upperHalfPlaneOpens), Measurable Hc →
    (∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      IsChartTransport (ownComponentChart (fun r : ℝ => Wα r.toNNReal ω) s) (-1)
        (-(Real.pi * QuantumZipper.chiC κ)) (QuantumZipper.chiC (16 / κ)) (h ω) (Hc ω)) →
    ∀ c : BoundaryWord, c.jumps = J → (∀ y ∉ J, c.fn y = b y) →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (_hW'm : ∀ r, Measurable (W' r)), (∀ᵐ ω ∂P, ∀ t, W' t ω = W t ω) →
    ∀ GT : Set Ω, (∀ ω ∈ GT, PhysGood s W' Wα ζα γ α ω) → MeasurableSet GT →
      (∀ᵐ ω ∂P, ω ∈ GT ↔ gb6Rec s Wα ζα ω ∈ gb6TS s) →
    ∀ (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞), HullId.IsGB6RelVersionR s P W' Wα ζα γ α R V →
    ∀ w : WordType, ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension (Q3Chain.cfData (16 / κ) b' J')
      (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀ →
    LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h' u₀) P →
    ∀ B : ℝ≥0 → Ω → Set ℂ, (∀ t, Measurable[_mΩ, hittingSigma] (B t)) →
      (∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω)) →
      (∀ t, ∀ᵐ ω ∂P, B t ω = relClosureH (retSet s Wα ζα ω ∪ fwdHull (fun r : ℝ => W' r.toNNReal ω) t)) →
      (∀ t, IsLocalSet (B t) (WholeField.centredField h' u₀) P) →
      HasGB6UnionMean κ θ c P h' Hc W' Wα ζα GT s R V w u₀ B

/-- **Named input (L4): GB6's safe events are physical** (binders of `RelSafeS.GB6LineLocalStatement`; the second
conjunct of its conclusion). -/
def GB6SafeMeasStatement : Prop :=
  ∀ (κ θ : ℝ), 0 < κ → κ < 4 → -(Real.pi / 2) ≤ θ → θ ≤ Real.pi / 2 →
  ∀ (Ω : Type u) (_mΩ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (b : ℝ → ℝ) (J : Finset ℝ)
    (W Wα : ℝ≥0 → Ω → ℝ) (ζ ζα : Ω → ℝ≥0∞) (γ α : Ω → ℝ≥0 → ℂ)
    (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
    IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J →
    IsPiecewiseConstantBoundaryData b' J' →
    (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
      (QuantumZipper.chiC (16 / κ)) (h ω) (h' ω)) →
    IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ →
    (∀ i : Fin (flowLineNL b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) b' J' 0 0 l) →
    (∀ i : Fin (flowLineNR b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) b' J' 0 0 l) →
    (∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop) →
    ∀ (hfl : IsFlowLineDriver κ b J θ P h Wα ζα),
    (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) →
    ∀ (s : ℝ≥0) (Hc : Ω → DistOn upperHalfPlaneOpens), Measurable Hc →
    (∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      IsChartTransport (ownComponentChart (fun r : ℝ => Wα r.toNNReal ω) s) (-1)
        (-(Real.pi * QuantumZipper.chiC κ)) (QuantumZipper.chiC (16 / κ)) (h ω) (Hc ω)) →
    ∀ c : BoundaryWord, c.jumps = J → (∀ y ∉ J, c.fn y = b y) →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (hW'm : ∀ r, Measurable (W' r)), (∀ᵐ ω ∂P, ∀ t, W' t ω = W t ω) →
    ∀ GT : Set Ω, (∀ ω ∈ GT, PhysGood s W' Wα ζα γ α ω) → MeasurableSet GT →
      (∀ᵐ ω ∂P, ω ∈ GT ↔ gb6Rec s Wα ζα ω ∈ gb6TS s) →
    ∀ (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞), HullId.IsGB6RelVersionR s P W' Wα ζα γ α R V →
      HasGB6SafeMeas P W' Wα ζα GT s R V (measurable_recOf_cfE hfl s).2 hW'm

/-! ### The reduction -/

/-- **`GB6LineLocalStatement` from Theorems 1.2–1.3, the union mean identification (L3) and the physical safe events
(L4).** The centring is the counterflow's initial extension (L0), the marks are `𝓕^α_s ∨ 𝓕^cf_t` and the physical union
is `unionSet` (L1), its shape on the live event is `RelSafeS.ae_compl_union_eq_relChart` (L2). -/
theorem gb6LineLocalStatement_of_mean_safe (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hM : GB6LineMeanStatement.{u}) (hS : GB6SafeMeasStatement.{u}) :
    GB6LineLocalStatement.{u} := by
  intro κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' hT hcf hadmL hadmR hcomp hfl hα s Hc
    hHcm hHc c hcJ hcb W' hW'm hWW GT hGT hGTm hGTae R V hver w
  refine ⟨?_, hS κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' hT hcf hadmL hadmR hcomp hfl
    hα s Hc hHcm hHc c hcJ hcb W' hW'm hWW GT hGT hGTm hGTae R V hver⟩
  have hk : 0 < 16 / κ := by positivity
  have hcf' := hcf
  -- the flow line with the data of the word
  have hflc : IsFlowLineDriver κ c.fn c.jumps θ P h Wα ζα :=
    (Exist.StagedLaw.isFlowLineDriver_congr_of_eqOn hb c.isPiecewiseConstantBoundaryData J hcb).2 hfl
  have hG' : IsGFFWithBoundaryData P h' b' J' :=
    Theorem14.GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hk hb' hcf
  -- (L0) the centrings
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension c.isPiecewiseConstantBoundaryData
  have hu₀b : IsBoundedHarmonicExtension b J u₀ := by
    have h1 : IsBoundedHarmonicExtension c.fn J u₀ := by rw [← hcJ]; exact hu₀
    exact (Restart.isBoundedHarmonicExtension_congr (fun y hy => hcb y hy) u₀).1 h1
  obtain ⟨u₀', hu₀'⟩ := Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData (16 / κ)
    (flowLineRhoL (16 / κ) b' J' 0 0) (flowLineRhoR (16 / κ) b' J' 0 0) (flowLineXL b' J' 0) (flowLineXR b' J' 0)
  have hcen := Q3Chain.centredField_eq_reflect hκ hb hG hb' hG' hT hu₀b hu₀'
  -- the counterflow coupling
  obtain ⟨hcfF, 𝓕c, VLc, VRc, Bc, htrc, hCc⟩ := hcf
  have e3 : hcfF = h' := funext fun ω => Theorem14.GW2Cone.eq_of_isTranslateAddConst_zero (zero_mul _) (htrc ω)
  rw [e3] at hCc
  have hXc := hCc.2.2.2.1
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := hcomp.mono fun ω hω => hω.1
  have hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h' u₀') P :=
    WholeField.isZeroBoundaryGFF_centredField hCc hu₀'
  have hh₀m : Measurable (WholeField.centredField h' u₀') := hh0.measurable
  -- determination of both curves (Theorems 1.2–1.3)
  have hdetc := Exist.Param12.hasFieldDeterminedHistories h12 h13 hk (Theorem15.isOrderedForceWord_flowLine b' J' 0)
    P 𝓕c W VLc VRc Bc ζ h' hCc
  have hcomap' : MeasurableSpace.comap h' inferInstance ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField h' u₀') inferInstance) P :=
    KernelTower.comap_le_aeSigma_comap (WholeField.measurable_add_dist _)
      (Eventually.of_forall fun ω => (sub_add_cancel (h' ω)
        (SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀')).symm)
  have h𝓕c : ∀ t, drivingFiltration P hXc t ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField h' u₀') inferInstance) P := fun t =>
    (Q3Chain.drivingFiltration_le_aeSigma hdetc hXc t).trans (Q3Chain.aeSigma_le_of_le hcomap')
  have hdetα : LP.HasFieldDeterminedHistories.{u} κ (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
      (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) :=
    Exist.Param12.hasFieldDeterminedHistories h12 h13 hκ (Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0)
  -- (L1) the retained set with the flow's record among its marks
  obtain ⟨ℋ₁, hℋ₁n, hrecℋ₁, hℋ₁d, hloc₁⟩ := exists_retained_marks hκ hflc hdetα hu₀ hh₀m (fun ω => hcen ω) s
  have hrecm := (measurable_recOf_cfE hfl s).2
  -- (L1) the union
  have hloc : ∀ t, WholeField.IsHistoryAvoidanceLocal (ℋ₁.1 ⊔ drivingFiltration P hXc t)
      (unionSet s Wα ζα W VLc VRc ζ t) (WholeField.centredField h' u₀') P := fun t => by
    have hU := Theorem14.WalkLaw.isHistoryAvoidanceLocal_union_of_det hh₀m (A₁ := retSet s Wα ζα)
      (A₂ := fun ω => Sec5.GlueCond.hullAt t (LawUnique.killedHistory W VLc VRc ζ ω))
      (fun U hUH => hrecℋ₁ (measurable_retOfRec s (measurableSet_avoid U.isOpen hUH)))
      (fun U hUH => measurableSet_avoid_cfHull hXc t U.isOpen hUH) hℋ₁d (h𝓕c t) hloc₁
      (isHistoryAvoidanceLocal_cfHull hCc hk hζ hu₀' t)
    exact isHistoryAvoidanceLocal_relClosureH hU
  have hBm : ∀ t, Measurable[mΩ, hittingSigma] (unionSet s Wα ζα W VLc VRc ζ t) := fun t =>
    measurable_relClosureH_union ((measurable_retOfRec s).comp hrecm) (measurable_cfHull hXc t)
  have hBc : ∀ t ω, unionSet s Wα ζα W VLc VRc ζ t ω ⊆ H ∧ IsOpen (H \ unionSet s Wα ζα W VLc VRc ζ t ω) :=
    fun t ω => ⟨relClosureH_subset_H _, isOpen_H_diff_relClosureH _⟩
  have hBeq : ∀ t, ∀ᵐ ω ∂P, unionSet s Wα ζα W VLc VRc ζ t ω =
      relClosureH (retSet s Wα ζα ω ∪ fwdHull (fun r : ℝ => W' r.toNNReal ω) t) := fun t => by
    filter_upwards [ae_cfHull_eq hCc hζ t, hWW] with ω hK hW
    rw [unionSet, hK]
    simp only [hW]
  have hBloc : ∀ t, IsLocalSet (unionSet s Wα ζα W VLc VRc ζ t) (WholeField.centredField h' u₀') P := fun t =>
    ((isLocalSet_tfae hh0 (hBm t) (Eventually.of_forall (hBc t))).out 4 1).2 (hloc t).isAvoidanceLocal
  refine ⟨u₀', fun t => ℋ₁.1 ⊔ drivingFiltration P hXc t, unionSet s Wα ζα W VLc VRc ζ, hu₀'.1, hh0, ?_,
    fun t => sup_le ℋ₁.2 ((drivingFiltration P hXc).le t), hBm, hBc, hloc, ?_,
    hM κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' hT hcf' hadmL hadmR hcomp hfl hα s
      Hc hHcm hHc c hcJ hcb W' hW'm hWW GT hGT hGTm hGTae R V hver w u₀' hu₀' hh0 _ hBm hBc hBeq hBloc⟩
  · -- the marks contain the physical filtration
    intro t
    show (MeasurableSpace.comap (gb6Rec s Wα ζα) inferInstance ⊔
      ⨆ r, ⨆ (_ : r ≤ t), MeasurableSpace.comap (W' r) inferInstance) ⊔ Ito.nullSets P ≤
        ℋ₁.1 ⊔ drivingFiltration P hXc t
    refine sup_le (sup_le (hrecℋ₁.comap_le.trans le_sup_left) (iSup₂_le fun r hr => ?_)) (hℋ₁n.trans le_sup_left)
    exact (measurable_version_drivingFiltration hXc hζ hW'm hWW hr).comap_le.trans le_sup_right
  · -- (L2) the shape of the union on the live event
    intro t
    filter_upwards [ae_compl_union_eq_relChart hGT hver t, hGTae, ae_cfHull_eq hCc hζ t, hWW] with ω hsh hGTω hK hW
      hlive hlt
    have hrecTS : gb6Rec s Wα ζα ω ∈ gb6TS s := hlive.1
    have hωGT : ω ∈ GT := hGTω.2 hrecTS
    have hsζ : (s : ℝ≥0∞) < ζα ω := (flag_recOf_cfE s).1 hrecTS.1
    obtain ⟨⟨hWc, -, -⟩, -⟩ := hGT ω hωGT
    have hWpath : (fun r : ℝ => W r.toNNReal ω) = fun r : ℝ => W' r.toNNReal ω := funext fun r => (hW _).symm
    have hX : IsOpen (H \ (Q3Rel.invHull (rdrv (gb6Rec s Wα ζα ω)) s ∪
        fwdHull (fun r : ℝ => W' r.toNNReal ω) t)) := by
      have e : H \ (Q3Rel.invHull (rdrv (gb6Rec s Wα ζα ω)) s ∪ fwdHull (fun r : ℝ => W' r.toNNReal ω) t) =
          (H \ WangWu.negInv '' fwdHull (rdrv (gb6Rec s Wα ζα ω)) s) ∩
            (H \ fwdHull (fun r : ℝ => W' r.toNNReal ω) t) := by
        ext z
        simp only [Q3Rel.invHull, WangWu.negInv, Set.mem_sdiff, mem_union, mem_inter_iff, not_or]
        tauto
      rw [e, WangWu.H_diff_image_negInv]
      exact (WangWu.isOpen_image_negInv (QuantumZipper.FwdHolo.isOpen_compl_fwdHull (continuous_rdrv _)
        s.coe_nonneg) sdiff_subset).inter
        (QuantumZipper.FwdHolo.isOpen_compl_fwdHull (hWc.comp continuous_real_toNNReal) t.coe_nonneg)
    rw [unionSet, retSet_of_lt hsζ, hK, hWpath, H_diff_relClosureH_of_isOpen hX]
    exact hsh hωGT hlt

/-- **Theorem 1.4's `GB6HullDetStatement` from Theorems 1.2–1.3, the union mean identification (L3) and the physical
safe events (L4)** (`RelSafeS.gb6HullDetStatement_of_lineLocal`). -/
theorem gb6HullDetStatement_of_mean_safe (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hM : GB6LineMeanStatement.{u}) (hS : GB6SafeMeasStatement.{u}) :
    Supp8.GB6.GB6HullDetStatement.{u} :=
  gb6HullDetStatement_of_lineLocal (gb6LineLocalStatement_of_mean_safe h12 h13 hM hS)

end InteractingSLE.Supp8.GB6LineL
