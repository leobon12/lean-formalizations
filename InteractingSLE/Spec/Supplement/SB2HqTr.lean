/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2HqInd

/-!
# SB2(1)'s late (S) line mean, part 14: FIN's set inputs in the coupling's coordinates

Packet PROVE-T14-SB2DRV (round 11). FIN's union mean is applied to the coupling field `h'` (`h' = h(· + u) + ψχ`)
centred at the flow-line word's extension `u₀'`; its retained set is the translated walk fill `A = walkFill − u`, its
hull the coupling hull `K` at the stopping time:

* **`centredField_coupling`**: `u₀' = u₀(· + u) + ψχ` on `ℍ`, and the two centred fields are translates of each other;
* **`walkFill_coupling`**: `A` is hitting-measurable, relatively closed, determined by the centred field `h'_c`
  (`hdA`), local for `h'_c` (`hlA`), and the translate of a walk-fill mean is a mean of `A` (`hg₁`);
* **`hull_coupling`**: a version `K` of the coupling hull at `τ` is relatively closed and local for `h'_c` (`hlK`);
* **`union_coupling`**: the translate of a mean `gU` of `walkFill ∪ (K + u)` is a mean of `A ∪ K`, which is local.

**R48.** Theorems 1.2–1.3 appear only as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (chiC H fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Restart Exist Exist.Staged Exist.StagedLaw GW1W GW1Conn WalkInf Restart.DomainMarkov Restart.DomainMarkov.K2
  Supp8.Q3Stop Sec7.PocketTraversal LocalSets Sec6

section Tr

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **The coupling's centred field is the translated centred field.** -/
theorem centredField_coupling (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {h' : Ω → DistOn upperHalfPlaneOpens}
    (htrans : ∀ ω, IsTranslateAddConst u (ψ * chiC κ) (h ω) (h' ω)) {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ (flowLineRhoL κ b jumps u ψ) (flowLineRhoR κ b jumps u ψ)
      (flowLineXL b jumps u) (flowLineXR b jumps u)) (forceJumpSet (flowLineXL b jumps u) (flowLineXR b jumps u))
      u₀') :
    EqOn u₀' (fun z => u₀ (z + u) + ψ * chiC κ) H ∧
      WholeField.centredField h' u₀' = (fun ω => Exist.flowField (-(-u)) 0 (WholeField.centredField h u₀ ω)) ∧
      WholeField.centredField h u₀ = (fun ω => Exist.flowField (-u) 0 (WholeField.centredField h' u₀' ω)) := by
  have hrel := Exist.eqOn_flowLine_harmonicExtension HP.kappa_pos HP.boundary u ψ hu₀ hu₀'
  have e2 : WholeField.centredField h u₀ = fun ω => Exist.flowField (-u) 0 (WholeField.centredField h' u₀' ω) :=
    funext fun ω => Sec7.SideHeight.centredField_eq_flowField htrans hu₀.1 hu₀'.1 hrel ω
  refine ⟨hrel, funext fun ω => ?_, e2⟩
  rw [e2, Sec7.SideHeight.flowField_neg_neg]

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- The centred field is determined by the coupling's centred field. -/
theorem comap_centredField_le {u₀ u₀' : ℂ → ℝ} {h' : Ω → DistOn upperHalfPlaneOpens}
    (e2 : WholeField.centredField h u₀ = (fun ω => Exist.flowField (-u) 0 (WholeField.centredField h' u₀' ω))) :
    MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField h' u₀') inferInstance) P := by
  rw [e2]
  refine le_trans ?_ (fun s hs => ⟨s, hs, EventuallyEq.rfl⟩)
  exact ((Exist.measurable_flowField (-u) 0).comp (comap_measurable _)).comap_le

/-- **FIN's retained-set inputs for the translated walk fill** (Theorems 1.2–1.3 as hypotheses). -/
theorem walkFill_coupling (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {A' : Ω → Set ℂ} (hA'H : ∀ ω, A' ω ⊆ H)
    (hA'm : ∀ U : TopologicalSpace.Opens ℂ, (U : Set ℂ) ⊆ H →
      MeasurableSet[pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)] {ω | Disjoint (A' ω) U})
    (hA'ae : ∀ᵐ ω ∂P, A' ω = WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω)
    {h' : Ω → DistOn upperHalfPlaneOpens} {u₀' : ℂ → ℝ}
    (e1 : WholeField.centredField h' u₀' = (fun ω => Exist.flowField (-(-u)) 0 (WholeField.centredField h u₀ ω)))
    (e2 : WholeField.centredField h u₀ = (fun ω => Exist.flowField (-u) 0 (WholeField.centredField h' u₀' ω))) :
    Measurable[mΩ, hittingSigma] (fun ω => (fun z : ℂ => z + (-u : ℝ)) '' walkFill κ b jumps E k A' ω) ∧
      (∀ ω, (fun z : ℂ => z + (-u : ℝ)) '' walkFill κ b jumps E k A' ω ⊆ H ∧
        IsOpen (H \ (fun z : ℂ => z + (-u : ℝ)) '' walkFill κ b jumps E k A' ω)) ∧
      MeasurableSpace.comap (fun ω => (fun z : ℂ => z + (-u : ℝ)) '' walkFill κ b jumps E k A' ω) hittingSigma ≤
        aeSigma (MeasurableSpace.comap (WholeField.centredField h' u₀') inferInstance) P ∧
      IsLocalSet (fun ω => (fun z : ℂ => z + (-u : ℝ)) '' walkFill κ b jumps E k A' ω)
        (WholeField.centredField h' u₀') P ∧
      ∃ gW : Ω → DistOn upperHalfPlaneOpens,
        IsLocalSetMean (walkFill κ b jumps E k A') (WholeField.centredField h u₀) P gW ∧
        IsLocalSetMean (fun ω => (fun z : ℂ => z + (-u : ℝ)) '' walkFill κ b jumps E k A' ω)
          (WholeField.centredField h' u₀') P (fun ω => Exist.flowField (-(-u)) 0 (gW ω)) := by
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hS := HP.staged _ (isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true)
  have hpastle := hS.2.1 (k + 1)
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData HP.field hu₀
  have hWev : ∀ V : TopologicalSpace.Opens ℂ, (V : Set ℂ) ⊆ H →
      MeasurableSet[pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)]
        {ω | Disjoint (walkFill κ b jumps E k A' ω) V} := fun V hV =>
    measurableSet_disjoint_walkFill HP hA'H hA'm hV
  have hWmp : Measurable[pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1), hittingSigma] (walkFill κ b jumps E k A') :=
    WalkMean.measurable_hitting_of_avoid (mΩ := pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)) le_rfl hWev
  have hWm : Measurable[mΩ, hittingSigma] (walkFill κ b jumps E k A') := hWmp.mono hpastle le_rfl
  have hAmp := (Sec7.SideHeight.measurable_image_add (-u)).comp hWmp
  have hWc : ∀ᵐ ω ∂P, walkFill κ b jumps E k A' ω ⊆ H ∧ IsOpen (H \ walkFill κ b jumps E k A' ω) :=
    ae_of_all _ fun ω => ⟨walkFill_subset_H A' ω, isOpen_H_sdiff_walkFill A' ω⟩
  have hWloc := isHistoryAvoidanceLocal_walkFill h12p h13 HP hu₀ hA'H hA'm hA'ae
  have htfae := isLocalSet_tfae hh0 hWm hWc
  have hWlocal : IsLocalSet (walkFill κ b jumps E k A') (WholeField.centredField h u₀) P :=
    (htfae.out 1 4).1 hWloc.isAvoidanceLocal
  obtain ⟨gW, hgW⟩ := isGermConditionalLaw_iff.1 ((htfae.out 1 3).1 hWloc.isAvoidanceLocal)
  refine ⟨hAmp.mono hpastle le_rfl, fun ω => Sec7.SideHeight.image_add_relClosed (-u)
    ⟨walkFill_subset_H A' ω, isOpen_H_sdiff_walkFill A' ω⟩, ?_, ?_, gW, hgW, ?_⟩
  · exact hAmp.comap_le.trans ((EntranceUnion.past_le_aeSigma h12p h13 HP u₀).trans
      (Supp8.Q3Chain.aeSigma_le_of_le (comap_centredField_le e2)))
  · rw [e1]
    exact Sec7.SideHeight.IsLocalSet.translate hWlocal (-u)
  · rw [e1]
    exact Shift.IsLocalSetMean.translate hgW (-u)

omit [StandardBorelSpace Ω] in
/-- **FIN's hull inputs**: a version of the coupling hull at a stopping time is relatively closed and local for the
coupling's centred field. -/
theorem hull_coupling {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hκ : 0 < κ) {h' : Ω → DistOn upperHalfPlaneOpens} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h') {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W VL VR ζ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) {K : Ω → Set ℂ}
    (hKm : Measurable[mΩ, hittingSigma] K)
    (hKe : ∀ᵐ ω ∂P, K ω = fwdHull (fun r : ℝ => W r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) :
    (∀ᵐ ω ∂P, K ω ⊆ H ∧ IsOpen (H \ K ω)) ∧ IsLocalSet K (WholeField.centredField h' u₀') P := by
  have hh0' := WholeField.isZeroBoundaryGFF_centredField hC hu₀'
  obtain ⟨hX', hlocC⟩ := hC.2.2.2
  have hKc : ∀ᵐ ω ∂P, K ω ⊆ H ∧ IsOpen (H \ K ω) := by
    filter_upwards [(hlocC τ hτ hτζ).1.2.1, hKe] with ω hω hKω
    rw [hKω]
    exact hω
  have htr0 : ∀ ω, IsTranslateAddConst 0 (0 * 0) (h' ω) (h' ω) := fun ω =>
    Sec7.StripSysField.isTranslateAddConst_zero_self (h' ω) 0
  have hloc := Sec7.SideHeight.isHistoryAvoidanceLocal_flowHull hC hκ htr0 hh0' hu₀'.1 hu₀'
    (fun z _ => by simp) hX hτ hτζ hKm (by
      filter_upwards [hKe] with ω hω
      rw [hω]
      simp)
  exact ⟨hKc, ((isLocalSet_tfae hh0' hKm hKc).out 1 4).1 hloc.isAvoidanceLocal⟩

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- The translated union is the union of the translated walk fill and the hull. -/
theorem image_neg_union_image (S K : Set ℂ) (u : ℝ) :
    (fun z : ℂ => z + (-u : ℝ)) '' (S ∪ (fun z : ℂ => z + u) '' K) = (fun z : ℂ => z + (-u : ℝ)) '' S ∪ K := by
  rw [image_union, image_image]
  congr 1
  have e : (fun x : ℂ => x + (u : ℂ) + ((-u : ℝ) : ℂ)) = id := funext fun x => by
    show x + (u : ℂ) + ((-u : ℝ) : ℂ) = x
    push_cast
    ring
  rw [e, image_id]

omit [StandardBorelSpace Ω] in
/-- **FIN's union inputs**: the translate of a mean of `walkFill ∪ (K + u)` is a mean of `A ∪ K`, which is local. -/
theorem union_coupling {u₀ u₀' : ℂ → ℝ} {h' : Ω → DistOn upperHalfPlaneOpens}
    (hh0' : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h' u₀') P)
    (e1 : WholeField.centredField h' u₀' = (fun ω => Exist.flowField (-(-u)) 0 (WholeField.centredField h u₀ ω)))
    {A' : Ω → Set ℂ} {K : Ω → Set ℂ}
    (hAm : Measurable[mΩ, hittingSigma] (fun ω => (fun z : ℂ => z + (-u : ℝ)) '' walkFill κ b jumps E k A' ω))
    (hAc : ∀ ω, (fun z : ℂ => z + (-u : ℝ)) '' walkFill κ b jumps E k A' ω ⊆ H ∧
      IsOpen (H \ (fun z : ℂ => z + (-u : ℝ)) '' walkFill κ b jumps E k A' ω))
    (hKm : Measurable[mΩ, hittingSigma] K) (hKc : ∀ᵐ ω ∂P, K ω ⊆ H ∧ IsOpen (H \ K ω))
    {gU : Ω → DistOn upperHalfPlaneOpens}
    (hgU : IsLocalSetMean (fun ω => walkFill κ b jumps E k A' ω ∪ (fun z : ℂ => z + u) '' K ω)
      (WholeField.centredField h u₀) P gU) :
    IsLocalSetMean (fun ω => (fun z : ℂ => z + (-u : ℝ)) '' walkFill κ b jumps E k A' ω ∪ K ω)
        (WholeField.centredField h' u₀') P (fun ω => Exist.flowField (-(-u)) 0 (gU ω)) ∧
      IsLocalSet (fun ω => (fun z : ℂ => z + (-u : ℝ)) '' walkFill κ b jumps E k A' ω ∪ K ω)
        (WholeField.centredField h' u₀') P ∧
      (∀ᵐ ω ∂P, (fun z : ℂ => z + (-u : ℝ)) '' walkFill κ b jumps E k A' ω ∪ K ω ⊆ H ∧
        IsOpen (H \ ((fun z : ℂ => z + (-u : ℝ)) '' walkFill κ b jumps E k A' ω ∪ K ω))) := by
  have hmean : IsLocalSetMean (fun ω => (fun z : ℂ => z + (-u : ℝ)) '' walkFill κ b jumps E k A' ω ∪ K ω)
      (WholeField.centredField h' u₀') P (fun ω => Exist.flowField (-(-u)) 0 (gU ω)) := by
    have ht := Shift.IsLocalSetMean.translate hgU (-u)
    have es : (fun ω => (fun z : ℂ => z + ((-u : ℝ) : ℂ)) ''
        (walkFill κ b jumps E k A' ω ∪ (fun z : ℂ => z + u) '' K ω)) =
        fun ω => (fun z : ℂ => z + (-u : ℝ)) '' walkFill κ b jumps E k A' ω ∪ K ω :=
      funext fun ω => image_neg_union_image _ _ u
    rw [es, ← e1] at ht
    exact ht
  have hUm := LocalSets.measurable_union_hitting hAm hKm
  have hUc : ∀ᵐ ω ∂P, (fun z : ℂ => z + (-u : ℝ)) '' walkFill κ b jumps E k A' ω ∪ K ω ⊆ H ∧
      IsOpen (H \ ((fun z : ℂ => z + (-u : ℝ)) '' walkFill κ b jumps E k A' ω ∪ K ω)) := by
    filter_upwards [hKc] with ω hω
    refine ⟨union_subset (hAc ω).1 hω.1, ?_⟩
    rw [← Set.sdiff_inter_sdiff]
    exact (hAc ω).2.inter hω.2
  refine ⟨hmean, ((isLocalSet_tfae hh0' hUm hUc).out 3 4).1 (isGermConditionalLaw_iff.2 ⟨_, hmean⟩), hUc⟩

end Tr

end InteractingSLE.Theorem14.SB.Lv
