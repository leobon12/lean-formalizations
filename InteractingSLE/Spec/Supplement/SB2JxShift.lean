/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JxMean
import InteractingSLE.Spec.Supplement.SB2DrvShift

/-!
# SB2(1)'s late (S) line mean, part 4: FIN's retained inputs in the coupling's coordinates

Packet PROVE-T14-SB2DRV (round 8), two inputs of FIN's union mean for `SB2JxFinStatement` (FIN is applied in the
coordinates of the upper flow's coupling, shifted by the seed `u`, with the coupling field `h' = h(· + u) + ψχ` and
the bounded harmonic extension `u₀'` of the flow-line word, `u₀' = u₀(· + u) + ψχ` on `ℍ`):

* **`eqOn_bhe_typed_word`**: on a type cell, every bounded harmonic extension of the typed force data is the mean of
  the sorted launch word plus `ψχ` (FIN's `G₀`);
* **`ae_walkFill_translate_rep`**: FIN's `hind₁` up to the chart identification — almost surely on the launch event,
  every harmonic representative `w₁` of the translated walk-fill mean `flowField u 0 (gW)` off the translated walk fill
  satisfies `w₁ + u₀' = mean ∘ c(· + u) + ψχ − χ ℓ(· + u)` (from `ae_walkFill_mean`, translation invariance of
  Lebesgue measure, and the uniqueness of harmonic representatives `Sec6.eqOn_of_integral_mul_eq`).

**R48.** Theorems 1.2–1.3 are hypotheses; this serves Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (chiC H fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Restart Exist Exist.Staged Exist.StagedLaw GW1W GW1Conn WalkInf Restart.DomainMarkov Restart.DomainMarkov.K2
  Supp8.Q3Stop Sec7.PocketTraversal LocalSets Sec6

/-- **The typed word identity**: on a type cell, a bounded harmonic extension of the typed force data is the mean of
the sorted word plus `ψχ`. -/
theorem eqOn_bhe_typed_word {κ ψ : ℝ} (hκ : 0 < κ) {w : WordType} {c : BoundaryWord}
    (hc : c ∈ FCDet.typeSet κ ψ w.1 w.2.1 (typedRhoL w) (typedRhoR w))
    (hcp : IsPiecewiseConstantBoundaryData c.fn c.jumps) {G₀ : ℂ → ℝ}
    (hG₀ : IsBoundedHarmonicExtension (forceBoundaryData κ (typedRhoL w) (typedRhoR w)
      (FCDet.typeXL κ ψ w.1 w.2.1 (typedRhoL w) (typedRhoR w) c)
      (FCDet.typeXR κ ψ w.1 w.2.1 (typedRhoL w) (typedRhoR w) c))
      (forceJumpSet (FCDet.typeXL κ ψ w.1 w.2.1 (typedRhoL w) (typedRhoR w) c)
        (FCDet.typeXR κ ψ w.1 w.2.1 (typedRhoL w) (typedRhoR w) c)) G₀) :
    ∀ z ∈ H, G₀ z = (sortedRep c).mean z + ψ * chiC κ := by
  have hft := FCDet.isFlowType_of_mem_typeSet hc
  have hsort := (sortedRep_spec hcp).1
  have hS : ({0} ∪ (c.jumps : Set ℝ)).Finite := (finite_singleton 0).union c.jumps.finite_toSet
  refine Restart.RetAux79.eqOn_mean_add_of_forceBoundaryData hG₀ hsort (ψ * chiC κ) hS fun y hy => ?_
  have h0 : y ≠ 0 := fun h' => hy (Or.inl h')
  have hJ : y ∉ c.jumps := fun h' => hy (Or.inr h')
  rw [Restart.RetAux79.forceBoundaryData_zero_of_isFlowType hft y,
    Exist.forceBoundaryData_flowLine_seed hκ hcp 0 ψ h0 (by simpa using hJ), add_zero,
    (sortedRep_spec hcp).2.2 y hJ]

section Translate

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **FIN's `hind₁` in the coupling's coordinates, up to the chart identification.** -/
theorem ae_walkFill_translate_rep (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (I : K2LaunchInputs κ b jumps P h E k u ψ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {A' : Ω → Set ℂ} (hA'H : ∀ ω, A' ω ⊆ H)
    (hA'm : ∀ U : TopologicalSpace.Opens ℂ, (U : Set ℂ) ⊆ H →
      MeasurableSet[pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)] {ω | Disjoint (A' ω) U})
    (hA'ae : ∀ᵐ ω ∂P, A' ω = WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω)
    {u₀' : ℂ → ℝ} (hrel : EqOn u₀' (fun z => u₀ (z + u) + ψ * chiC κ) H)
    {gW : Ω → DistOn upperHalfPlaneOpens}
    (hgW : IsLocalSetMean (walkFill κ b jumps E k A') (WholeField.centredField h u₀) P gW) :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → ∀ w₁ : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd w₁ (H \ (fun z : ℂ => z + ((-u : ℝ) : ℂ)) '' walkFill κ b jumps E k A' ω) →
      (∀ φ : TestOn upperHalfPlaneOpens,
        tsupport φ ⊆ H \ (fun z : ℂ => z + ((-u : ℝ) : ℂ)) '' walkFill κ b jumps E k A' ω →
        Exist.flowField (-(-u)) 0 (gW ω) φ = ∫ z, w₁ z * φ z) →
      EqOn (fun z => w₁ z + u₀' z)
        (fun z => (sortedRep (I.word ω)).mean ((I.chart ω).1 (z + u)) + ψ * chiC κ -
          chiC κ * (I.chart ω).2.2 (z + u))
        (H \ (fun z : ℂ => z + ((-u : ℝ) : ℂ)) '' walkFill κ b jumps E k A' ω) := by
  filter_upwards [ae_walkFill_mean h12p h13 HP I hu₀ hA'H hA'm hA'ae hgW, ae_dom_eq_H_sdiff_walkFill HP I hA'ae,
    I.field] with ω hmean hdomω hf hl w₁ hw₁ hrep
  obtain ⟨hpc, -⟩ := hf hl
  have hc := isConformal_chart I ω
  obtain ⟨-, hliftc, hliftH, -, -, -, -⟩ := I.chart_measurable
  set O : Set ℂ := H \ (fun z : ℂ => z + ((-u : ℝ) : ℂ)) '' walkFill κ b jumps E k A' ω with hOdef
  -- the shifted domain
  have hmemO : ∀ z, z ∈ O → z + (u : ℂ) ∈ ((I.chart ω).dom : Set ℂ) := by
    intro z hz
    rw [hdomω hl]
    refine ⟨?_, fun hW => hz.2 ⟨z + u, hW, by push_cast; ring⟩⟩
    have : 0 < z.im := hz.1
    show 0 < (z + (u : ℂ)).im
    simpa using this
  have hOopen : IsOpen O := by
    have e : O = (fun z : ℂ => z + (u : ℂ)) ⁻¹' (H \ walkFill κ b jumps E k A' ω) := by
      ext z
      simp only [hOdef, Set.mem_sdiff, mem_preimage]
      constructor
      · rintro ⟨hzH, hzW⟩
        refine ⟨?_, fun hW => hzW ⟨z + u, hW, by push_cast; ring⟩⟩
        have : 0 < z.im := hzH
        show 0 < (z + (u : ℂ)).im
        simpa using this
      · rintro ⟨hzH, hzW⟩
        refine ⟨?_, ?_⟩
        · have : 0 < (z + (u : ℂ)).im := hzH
          show 0 < z.im
          simpa using this
        · rintro ⟨y, hy, rfl⟩
          apply hzW
          have : y + ((-u : ℝ) : ℂ) + (u : ℂ) = y := by push_cast; ring
          rw [this]
          exact hy
    rw [e]
    exact (isOpen_H_sdiff_walkFill A' ω).preimage (continuous_id.add continuous_const)
  have hOH : O ⊆ H := sdiff_subset
  -- the candidate representative and its harmonicity
  set m : ℂ → ℝ := fun z => (sortedRep (I.word ω)).mean ((I.chart ω).1 z) - chiC κ * (I.chart ω).2.2 z - u₀ z
    with hmdef
  have hmh : InnerProductSpace.HarmonicOnNhd m (I.chart ω).dom :=
    WalkSide.harmonicOnNhd_chartMean hc (hliftH ω) (sortedRep_spec hpc).1 hu₀.1 (chiC κ)
  have hmsh : InnerProductSpace.HarmonicOnNhd (fun z => m (z + (u : ℂ))) O := fun z hz =>
    Exist.harmonicAt_comp_add_const (hmh _ (hmemO z hz))
  -- the translated mean is represented by `m(· + u)`
  have hrep' : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ O →
      ∫ z, w₁ z * φ z = ∫ z, m (z + (u : ℂ)) * φ z := by
    intro φ hφ
    rw [← hrep φ hφ, Sec7.SideHeight.flowField_neg_apply]
    have hsupp : tsupport (WholeField.shiftTest (-u) φ) ⊆ (I.chart ω).dom := by
      refine (Shift.tsupport_shiftTest_subset (-u) φ).trans ?_
      rintro _ ⟨z, hz, rfl⟩
      have := hmemO z (hφ hz)
      simpa using this
    rw [hmean hl _ hsupp]
    have e : (fun z => m z * WholeField.shiftTest (-u) φ z) = fun z => m z * φ (z + ((-u : ℝ) : ℂ)) := by
      funext z
      rw [WholeField.shiftTest_apply]
    simp only [hmdef] at e ⊢
    rw [e]
    have h1 := MeasureTheory.integral_add_right_eq_self
      (μ := (volume : Measure ℂ)) (fun z => ((sortedRep (I.word ω)).mean ((I.chart ω).1 z) -
        chiC κ * (I.chart ω).2.2 z - u₀ z) * φ (z + ((-u : ℝ) : ℂ))) (u : ℂ)
    rw [← h1]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only
    congr 2
    push_cast
    ring
  have hEq := Sec6.eqOn_of_integral_mul_eq hOopen hOH hw₁ hmsh hrep'
  intro z hz
  show w₁ z + u₀' z = _
  rw [hEq hz, hrel (hOH hz)]
  simp only [hmdef]
  ring

end Translate

end InteractingSLE.Theorem14.SB.Lv
