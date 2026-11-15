/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2FbUnion
import InteractingSLE.Spec.Supplement.GW2FbDual
import InteractingSLE.Spec.Supplement.GB6LMeanDet

/-!
# GW2's union mean: the joint word flowed by the relative chain

Packet PROVE-GW2-FABLE. GB9, p. 525 ("Before a new flow prefix first meets the retained counterflow, the conditional
exploration has its full canonical word in this joint chart … Finite-exception uniqueness therefore gives the
canonical complete word at every pre-contact stop"). This file feeds the retained side of
`ae_eqOn_unionMean_invHull_stop` for GW2's actual objects, from Theorems 1.2–1.3:

* `isBoundedHarmonicExtension_sub_const'`: bounded harmonic extensions of data differing by a constant;
* **`exists_retained_marks_gw2`**, `exists_retained_local_gw2`: in the flow line's frame (the coupling field
  `X = h + θχ` centred by the bounded
  harmonic extension of its force data), the retained set `retSet s W ζ` (the inverted counterflow hull at `s`) is
  hitting-measurable, field-determined and a local set (GB6's (L1)(a), `Supp8.GB6LineL.exists_retained_marks`, at the
  dual parameter `16/κ`, read through `isChartTransport_dual`);
* **`ae_eqOn_unionMean_gw2`**: for a flow line of `h` at ANY angle `θ` (an optional hull coupling of `X`), a stopping
  time `τ < ζα` of its driving filtration, a hitting-measurable version `K` of its hull at `τ` with
  `retSet s W ζ ∪ K` a local set, and every local-set mean `g` of the union: almost surely on
  `{γ(s) ∈ ℍ, 0 < τ < T_c}`, the harmonic representative `w_U` of `g` satisfies
  `w_U + 𝔥⁰ = G ∘ g̃_u ∘ Ψ − χ(κ) (arg g̃_u′ ∘ Ψ + Im relLog)` with `Ψ = relMap W s` the joint chart's forward map,
  `(Wr, u)` the relative chain of the flow in the joint chart and `G` a bounded harmonic extension of the
  angle-`θ` flow-line word of the JOINT WORD `jointWordOfRec (specOffset κ) κ c′ (cfRec s W ζ)`, flowed by `Wr` to `u`.
  This is the canonical coupling mean of the relative flow line of the joint-chart field: the finite-word mean
  identification of GW2's joint (Det).

The one field input not discharged here is the locality of the union (`hlU`), which is
`Theorem14.WalkLaw.isHistoryAvoidanceLocal_union_of_det` for the two field-determined marked local sets.

R48: Theorems 1.2–1.3 enter as hypotheses; GW2 serves Theorem 1.4 only. Conditional helpers with distinct names;
they replace no source theorem. No `κ < 4` hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2Fb

open Restart Exist Exist.StagedLaw WholeField LocalSets
open Supp8.GB6 Supp8.GB6LineL Supp8.GB6LMean Supp8.Q3Chain
open Supp8.Q3Rel (invHull relLog relBad IsRelConfigOff)
open GW2JointKernel GW2TipSystem

/-! ### Bounded harmonic extensions of data differing by a constant -/

/-- If `g′ = g − c`, a bounded harmonic extension of `g` minus `c` is one of `g′`. -/
theorem isBoundedHarmonicExtension_sub_const' {g g' : ℝ → ℝ} {S : Set ℝ} {v : ℂ → ℝ} {c : ℝ}
    (hv : IsBoundedHarmonicExtension g S v) (hg : ∀ x, g' x = g x - c) :
    IsBoundedHarmonicExtension g' S (fun z => v z - c) := by
  obtain ⟨h1, ⟨C, hC⟩, h3⟩ := hv
  refine ⟨fun z hz => (h1 z hz).sub (InnerProductSpace.harmonicAt_const _), ⟨C + |c|, fun z hz => ?_⟩,
    fun x hx => ?_⟩
  · exact (abs_sub _ _).trans (add_le_add (hC z hz) le_rfl)
  · rw [hg x]
    exact (h3 x hx).sub_const c

/-! ### The retained set in the flow line's frame -/

section Retained

variable {κ θ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h h' X : Ω → DistOn upperHalfPlaneOpens} {b b' : ℝ → ℝ} {J J' : Finset ℝ}

omit mΩ in
/-- **The centred coupling field of a flow line at angle `θ` is the centred original field** (the constant `θχ` is
absorbed by the bounded harmonic extensions). -/
theorem centredField_flow_eq (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J)
    (htr : ∀ ω, IsTranslateAddConst 0 (θ * chiC κ) (h ω) (X ω)) {uh u₀ : ℂ → ℝ}
    (huh : IsBoundedHarmonicExtension (cfData κ b J) (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0)) uh)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
      (flowLineXL b J 0) (flowLineXR b J 0)) (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0)) u₀) :
    EqOn u₀ (fun z => uh z + θ * chiC κ) H ∧ centredField h uh = centredField X u₀ := by
  obtain ⟨ub, hub, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  have e1 := Exist.eqOn_flowLine_harmonicExtension hκ hb 0 θ hub hu₀
  have e2 := Exist.eqOn_flowLine_harmonicExtension hκ hb 0 0 hub huh
  have hrel : EqOn u₀ (fun z => uh (z + ((0 : ℝ) : ℂ)) + θ * chiC κ) H := fun z hz => by
    have h1 := e1 hz
    have h2 := e2 hz
    simp only [Complex.ofReal_zero, add_zero, zero_mul] at h1 h2 ⊢
    rw [h1, h2]
  refine ⟨fun z hz => by simpa only [Complex.ofReal_zero, add_zero] using hrel hz, funext fun ω => ?_⟩
  have h3 := Sec7.SideHeight.centredField_eq_flowField htr huh.1 hu₀.1 hrel ω
  rw [h3, neg_zero]
  simpa using Supp8.HullDetGen.flowField_zero_zero_mul 0 (centredField X u₀ ω)

/-- **The marks of GW2's retained set in the flow line's frame** (GB6's (L1)(a),
`Supp8.GB6LineL.exists_retained_marks`, at the dual parameter `16/κ`): field-determined marks for which the inverted
counterflow hull at `s` is hitting-measurable and history-marked local for the centred coupling field. -/
theorem exists_retained_marks_gw2 (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J) (hG : IsGFFWithBoundaryData P h b J)
    (hb' : IsPiecewiseConstantBoundaryData b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω))
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (htr : ∀ ω, IsTranslateAddConst 0 (θ * chiC κ) (h ω) (X ω)) {uh u₀ : ℂ → ℝ}
    (huh : IsBoundedHarmonicExtension (cfData κ b J) (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0)) uh)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
      (flowLineXL b J 0) (flowLineXR b J 0)) (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0)) u₀)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField X u₀) P) (s : ℝ≥0) :
    ∃ ℋ : {m : MeasurableSpace Ω // m ≤ mΩ}, Measurable[ℋ.1, hittingSigma] (retSet s W ζ) ∧
      ℋ.1 ≤ aeSigma (MeasurableSpace.comap (centredField X u₀) inferInstance) P ∧
      WholeField.IsHistoryAvoidanceLocal ℋ.1 (retSet s W ζ) (centredField X u₀) P := by
  have hk : (0 : ℝ) < 16 / κ := by positivity
  have e16 : 16 / (16 / κ) = κ := by field_simp
  obtain ⟨c', hc'J, hc'b⟩ := BoundaryWord.exists_fn_eq hb'
  have hG' : IsGFFWithBoundaryData P h' b' J' :=
    Theorem14.GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hk hb' hcf
  have hGc' : IsGFFWithBoundaryData P h' c'.fn c'.jumps := by
    rw [hc'J]
    exact WangWu.isGFFWithBoundaryData_congr (fun y hy => (hc'b y hy).symm) hG'
  have hcfc : IsFlowLineDriver (16 / κ) c'.fn c'.jumps 0 P h' W ζ :=
    (isFlowLineDriver_congr_of_eqOn hb' c'.isPiecewiseConstantBoundaryData J' hc'b).2 hcf
  have hdet : LP.HasFieldDeterminedHistories.{u} (16 / κ) (flowLineXL c'.fn c'.jumps 0)
      (flowLineXR c'.fn c'.jumps 0) (flowLineRhoL (16 / κ) c'.fn c'.jumps 0 0)
      (flowLineRhoR (16 / κ) c'.fn c'.jumps 0 0) :=
    Exist.Param12.hasFieldDeterminedHistories h12 h13 hk (Theorem15.isOrderedForceWord_flowLine c'.fn c'.jumps 0)
  have hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC (16 / κ)))
      (chiC (16 / (16 / κ))) (h' ω) (h ω) := fun ω => isChartTransport_dual hκ (hT ω)
  have huh' : IsBoundedHarmonicExtension (cfData (16 / (16 / κ)) b J)
      (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0)) uh := by
    rw [e16]
    exact huh
  obtain ⟨uc', huc', -⟩ :=
    PiecewiseConstant.existsUnique_isBoundedHarmonicExtension c'.isPiecewiseConstantBoundaryData
  have hcen := centredField_eq_reflect (κ := 16 / κ) hk c'.isPiecewiseConstantBoundaryData hGc' hb hG hT' huc' huh'
  have hcX := (centredField_flow_eq hκ hb htr huh hu₀).2
  have hcen' : ∀ ω, centredField X u₀ ω = WangWu.reflectField (centredField h' uc' ω) := fun ω => by
    rw [← hcX]
    exact hcen ω
  obtain ⟨ℋ, -, hrecℋ, hℋd, hloc⟩ :=
    exists_retained_marks (κ := 16 / κ) (θ := 0) hk hcfc hdet huc' hh0.measurable hcen' s
  exact ⟨ℋ, (measurable_retOfRec s).comp hrecℋ, hℋd, hloc⟩

/-- **GW2's retained set in the flow line's frame**: the inverted counterflow hull at `s` is hitting-measurable,
field-determined and a local set of the centred coupling field. -/
theorem exists_retained_local_gw2 (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J) (hG : IsGFFWithBoundaryData P h b J)
    (hb' : IsPiecewiseConstantBoundaryData b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω))
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (htr : ∀ ω, IsTranslateAddConst 0 (θ * chiC κ) (h ω) (X ω)) {uh u₀ : ℂ → ℝ}
    (huh : IsBoundedHarmonicExtension (cfData κ b J) (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0)) uh)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
      (flowLineXL b J 0) (flowLineXR b J 0)) (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0)) u₀)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField X u₀) P) (s : ℝ≥0) :
    Measurable[mΩ, hittingSigma] (retSet s W ζ) ∧
      MeasurableSpace.comap (retSet s W ζ) hittingSigma ≤
        aeSigma (MeasurableSpace.comap (centredField X u₀) inferInstance) P ∧
      IsLocalSet (retSet s W ζ) (centredField X u₀) P := by
  obtain ⟨ℋ, hAℋ, hℋd, hloc⟩ := exists_retained_marks_gw2 h12 h13 hκ hb hG hb' hT hcf htr huh hu₀ hh0 s
  have hAm : Measurable[mΩ, hittingSigma] (retSet s W ζ) := hAℋ.mono ℋ.2 le_rfl
  have hAc : ∀ᵐ ω ∂P, retSet s W ζ ω ⊆ H ∧ IsOpen (H \ retSet s W ζ ω) :=
    Eventually.of_forall fun ω => ⟨retSet_subset_H s W ζ ω, isOpen_H_diff_retSet s W ζ ω⟩
  exact ⟨hAm, hAℋ.comap_le.trans hℋd, ((isLocalSet_tfae hh0 hAm hAc).out 4 1).2 hloc.isAvoidanceLocal⟩

end Retained

/-! ### The union mean -/

/-- **GW2's union mean identification** (GB9, p. 525), from Theorems 1.2–1.3 and the locality of the union. -/
theorem ae_eqOn_unionMean_gw2 (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ θ : ℝ} (hκ : 0 < κ) {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' : Ω → DistOn upperHalfPlaneOpens} {b b' : ℝ → ℝ} {J J' : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (hG : IsGFFWithBoundaryData P h b J)
    (hb' : IsPiecewiseConstantBoundaryData b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω))
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ} (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (hcomp : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω)) (s : ℝ≥0)
    (hNR : ∀ᵐ ω ∂P, ∀ v : ℝ≥0, 0 < v → v ≤ s → γ ω v ≠ 0)
    {c' : BoundaryWord} (hc'J : c'.jumps = J') (hc'b : ∀ y ∉ J', c'.fn y = b' y)
    {X : Ω → DistOn upperHalfPlaneOpens} {𝓕 : Filtration ℝ≥0 mΩ} {Wα : ℝ≥0 → Ω → ℝ}
    {VL : Fin (flowLineNL b J 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR b J 0) → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {α : Ω → ℝ≥0 → ℂ}
    (htr : ∀ ω, IsTranslateAddConst 0 (θ * chiC κ) (h ω) (X ω))
    (hC : IsOptionalHullCoupling κ (flowLineXL b J 0) (flowLineXR b J 0) (flowLineRhoL κ b J 0 θ)
      (flowLineRhoR κ b J 0 θ) P 𝓕 Wα VL VR B ζα X)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    (hX : IsMeasurableKilledDriving Wα VL VR ζα) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζα ω) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
      (flowLineXL b J 0) (flowLineXR b J 0)) (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0)) u₀)
    {K : Ω → Set ℂ} (hKm : Measurable[mΩ, hittingSigma] K)
    (hKeq : ∀ᵐ ω ∂P, K ω = fwdHull (fun r : ℝ => Wα r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))
    (hlU : IsLocalSet (fun ω => retSet s W ζ ω ∪ K ω) (centredField X u₀) P)
    {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => retSet s W ζ ω ∪ K ω) (centredField X u₀) P g) :
    ∀ᵐ ω ∂P, γ ω s ∈ H → 0 < (τ ω).untopD 0 →
      (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < firstContactTime (fun u => (α ω u : OnePoint ℂ))
        ((fun u => sphereInv (γ ω u : OnePoint ℂ)) '' Icc 0 s) →
      ∃ (p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℂ) × (ℝ → ℝ) × (ℝ → ℂ)) (G : ℂ → ℝ),
        IsRelChainStop κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) (flowLineXL b J 0) (flowLineXR b J 0)
          (flowLineRhoL κ (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).fn
            (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).jumps 0 θ)
          (flowLineRhoR κ (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).fn
            (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).jumps 0 θ)
          (flowLineXL (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).fn
            (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).jumps 0)
          (flowLineXR (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).fn
            (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).jumps 0)
          (fun r : ℝ => W r.toNNReal ω) s (fun t => Wα t ω) ((τ ω).untopD 0) p ∧
        IsBoundedHarmonicExtension
          (flowedData κ
            (flowLineRhoL κ (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).fn
              (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).jumps 0 θ)
            (flowLineRhoR κ (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).fn
              (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).jumps 0 θ)
            (flowLineXL (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).fn
              (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).jumps 0)
            (flowLineXR (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).fn
              (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).jumps 0) p.2.2.1
            (relClock (fun r : ℝ => W r.toNNReal ω) s (fun r : ℝ => p.1 r.toNNReal)
              ((τ ω).untopD 0 : ℝ≥0)))
          (flowedJumps
            (flowLineXL (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).fn
              (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).jumps 0)
            (flowLineXR (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).fn
              (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).jumps 0) p.2.2.1
            (relClock (fun r : ℝ => W r.toNNReal ω) s (fun r : ℝ => p.1 r.toNNReal)
              ((τ ω).untopD 0 : ℝ≥0))) G ∧
        ∀ wU : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd wU (H \ (retSet s W ζ ω ∪ K ω)) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (retSet s W ζ ω ∪ K ω) →
            g ω φ = ∫ z, wU z * φ z) →
          EqOn (fun z => wU z + u₀ z)
            (fun z => G (fwdMap p.2.2.1
                (relClock (fun r : ℝ => W r.toNNReal ω) s (fun r : ℝ => p.1 r.toNNReal)
                  ((τ ω).untopD 0 : ℝ≥0)) (relMap (fun r : ℝ => W r.toNNReal ω) s z)) -
              chiC κ * ((logDerivFwd p.2.2.1
                (relClock (fun r : ℝ => W r.toNNReal ω) s (fun r : ℝ => p.1 r.toNNReal)
                  ((τ ω).untopD 0 : ℝ≥0)) (relMap (fun r : ℝ => W r.toNNReal ω) s z)).im +
                (relLog (fun r : ℝ => W r.toNNReal ω) s z).im))
            (H \ (retSet s W ζ ω ∪ K ω)) := by
  classical
  have hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField X u₀) P :=
    isZeroBoundaryGFF_centredField hC hu₀
  -- the bounded harmonic extension of the original data and the two frames
  obtain ⟨uh, huh⟩ := Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData κ
    (flowLineRhoL κ b J 0 0) (flowLineRhoR κ b J 0 0) (flowLineXL b J 0) (flowLineXR b J 0)
  have huh' : IsBoundedHarmonicExtension (cfData κ b J)
      (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0)) uh := huh
  obtain ⟨hrel, hcX⟩ := centredField_flow_eq hκ hb htr huh' hu₀
  -- the retained side
  obtain ⟨hAm, hdA, hlA⟩ := exists_retained_local_gw2 h12 h13 hκ hb hG hb' hT hcf htr huh' hu₀ hh0 s
  have hAc : ∀ᵐ ω ∂P, retSet s W ζ ω ⊆ H ∧ IsOpen (H \ retSet s W ζ ω) :=
    Eventually.of_forall fun ω => ⟨retSet_subset_H s W ζ ω, isOpen_H_diff_retSet s W ζ ω⟩
  obtain ⟨g₁, hg₁⟩ := isGermConditionalLaw_iff.1
    (IsAvoidanceLocal.isGermConditionalLaw hh0 hAm hAc (((isLocalSet_tfae hh0 hAm hAc).out 4 1).1 hlA))
  -- the explored side
  obtain ⟨hX', hker⟩ := hC.2.2.2
  have hlK : IsLocalSet K (centredField X u₀) P := by
    refine Coupling.IsLocalSet.congr_set
      (WholeField.IsLocalSet.sub_dist (hker τ hτ hτζ).1 (WholeField.isHarmonicDistOn_smoothDist hu₀.1)) ?_
    filter_upwards [hKeq] with ω hω
    simp only [hω]
  have hKc : ∀ᵐ ω ∂P, K ω ⊆ H ∧ IsOpen (H \ K ω) := hlK.2.1
  obtain ⟨g₂, hg₂⟩ := isGermConditionalLaw_iff.1
    (IsAvoidanceLocal.isGermConditionalLaw hh0 hKm hKc (((isLocalSet_tfae hh0 hKm hKc).out 4 1).1 hlK))
  -- the two curves
  have hWα : ∀ᵐ ω ∂P, Wα 0 ω = 0 ∧ ContinuousOn (fun t => Wα t ω) {t | (t : ℝ≥0∞) < ζα ω} := by
    filter_upwards [hC.1.2.2.2.2] with ω hp
    exact ⟨hp.1, hp.2.2.2.1⟩
  have hdrv := ae_driver_zero_continuousOn hcf
  have hW : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) := by
    filter_upwards [hdrv, hcomp] with ω hω hc
    have hcont : ContinuousOn (fun t => W t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := hω.2
    rw [hc.1] at hcont
    exact ⟨continuousOn_univ.1 (hcont.mono fun t _ => ENNReal.coe_lt_top), hω.1, hc.2⟩
  -- the retained mean in the frame of the coupling field
  have hg₁h : IsLocalSetMean (retSet s W ζ) (centredField h uh) P g₁ := by
    rw [hcX]
    exact hg₁
  have hh0h : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h uh) P := by
    rw [hcX]
    exact hh0
  have hret := ae_eqOn_retMean_gw2 h12 h13 hκ hb hG hb' hT hcf hc'J hc'b huh' hh0h s hg₁h
  have hmain := ae_eqOn_unionMean_invHull_stop hκ (Theorem14.GW3Word.flowLineXL_nonpos b J)
    (Theorem14.GW3Word.flowLineXR_nonneg b J) hC hWα hα hW (fun _ => s) hNR hu₀ hh0 hX hτ hτζ univ
    (A := retSet s W ζ)
    (by
      filter_upwards [hdrv, hcomp] with ω hω hc _
      exact retSet_eq_invHull (by rw [hc.1]; exact ENNReal.coe_lt_top) hω.1 hω.2)
    (Eventually.of_forall fun ω => not_isBounded_lowerUnion_retSet s W ζ ω) hKeq hAm hKm hdA hlA hlU hg hg₁ hg₂
    (nL' := fun ω => flowLineNL (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).fn
      (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).jumps 0)
    (nR' := fun ω => flowLineNR (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).fn
      (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).jumps 0)
    (ρL' := fun ω => flowLineRhoL κ (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).fn
      (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).jumps 0 θ)
    (ρR' := fun ω => flowLineRhoR κ (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).fn
      (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).jumps 0 θ)
    (yL := fun ω => flowLineXL (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).fn
      (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).jumps 0)
    (yR := fun ω => flowLineXR (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).fn
      (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).jumps 0)
    (fun ω => Theorem14.GW3Word.flowLineXL_nonpos _ _) (fun ω => Theorem14.GW3Word.flowLineXR_nonneg _ _)
    (by
      filter_upwards [hret, hcomp] with ω hω hc _ _ G₀ hG₀ w₁ hw₁ hr₁
      have hs : (s : ℝ≥0∞) < ζ ω := by rw [hc.1]; exact ENNReal.coe_lt_top
      -- the extension of the joint word at angle `0`
      have hG₀' : IsBoundedHarmonicExtension
          (cfData κ (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).fn
            (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).jumps)
          (cfJumps (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).fn
            (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)).jumps)
          (fun z => G₀ z - θ * chiC κ) :=
        isBoundedHarmonicExtension_sub_const' hG₀ fun x => by
          rw [cfData, Sec5.RestartGen.forceBoundaryData_flowLine_angle hκ _ _ θ 0 x]
          ring
      intro z hz
      have h1 := hω hs _ hG₀' w₁ hw₁ hr₁ hz
      have h2 := hrel hz.1
      simp only at h1 h2 ⊢
      rw [h2]
      linarith)
  filter_upwards [hmain] with ω hω hsH hT0 hTc
  exact hω trivial hsH hT0 hTc

end InteractingSLE.Theorem14.GW2Fb
