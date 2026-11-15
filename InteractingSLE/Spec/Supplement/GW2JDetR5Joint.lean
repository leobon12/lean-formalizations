/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR5Law
import InteractingSLE.Spec.Supplement.GW2JDetR5Past
import InteractingSLE.Spec.Supplement.GW2JDetR2Root
import InteractingSLE.Spec.Supplement.GW2KModR1

/-!
# Staged canonical SDE availability from the actual retained joint-chart law

Start the stopping-time induction with the proved R1 law conditioned on exactly
the counterflow record. No image-curve coupling or determination statement is
used. The conclusion supplies every canonical stage's full flow-line coupling.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open LQGMetric (DistOn)
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2JDetR5

open Restart Exist Exist.Staged Exist.StagedLaw GW2JointKernel GW2TipSystem GW2KM2

variable {κ : ℝ} (hκ : 0 < κ)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h)
    {b' : ℝ → ℝ} {J' : Finset ℝ} (hb' : IsPiecewiseConstantBoundaryData b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1)
      (-(Real.pi * QuantumZipper.chiC κ)) (QuantumZipper.chiC (16 / κ)) (h ω) (h' ω))
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) {γ : Ω → ℝ≥0 → ℂ}
    (hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω))
    (s : ℝ≥0) {Hc : Ω → DistOn upperHalfPlaneOpens} (hHcm : Measurable Hc)
    (hHc : ∀ᵐ ω ∂P, γ ω s ∈ H →
      IsChartTransport (jointChart (fun r : ℝ => W r.toNNReal ω) s)
        1 (specOffset κ) (QuantumZipper.chiC κ) (h ω) (Hc ω))
    (c' : BoundaryWord) (hc'b : ∀ y ∉ J', c'.fn y = b' y)

include hκ hhm hb' hT hcf hζ hγ hHcm hHc hc'b in
/-- The initial GFF kernel uses the literal joint word and exactly the
counterflow record. Its live event is a measurable event of that record. -/
theorem exists_joint_initial_kernel : ∃ A : Set RecData, MeasurableSet A ∧
    (∀ᵐ ω ∂P, γ ω s ∈ H ↔ cfRec s W ζ ω ∈ A) ∧
    ∀ᵐ ω₀ ∂P, cfRec s W ζ ω₀ ∈ A →
      IsGFFWithBoundaryData
        (condExpKernel P (MeasurableSpace.comap (cfRec s W ζ) inferInstance) ω₀)
        Hc (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω₀)).fn
        (jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω₀)).jumps := by
  obtain ⟨M, β, hM, -, -, hCF, hev⟩ :=
    exists_jointKernel_r1_rec hκ (specOffset κ) hhm hb' hT hcf hζ hγ s hHcm hHc hc'b
  have hr := measurable_cfRec
    (show IsCenteredCounterflowDriver κ P h W ζ from ⟨b', J', h', hb', hT, hcf⟩) s
  have hw := GW2JDetR2.ae_jointWord_cfRec (a₀ := specOffset κ) hcf hζ c' s
  have hG := ae_isGFFWithBoundaryData_condExpKernel (P := P) hr.comap_le
    (M := M) (β := fun ω => jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω))
    (Eventually.of_forall fun ω _ => isSorted_jointWordOfRec _ _ _ _) hHcm
    (fun φ => by
      filter_upwards [hCF φ, hev, hw] with ω hc he hw' hω
      rw [hw', ← he.2]
      exact hc hω)
  change MeasurableSet[MeasurableSpace.comap (cfRec s W ζ) inferInstance] M at hM
  obtain ⟨A, hA, hAM⟩ := hM
  refine ⟨A, hA, ?_, ?_⟩
  · filter_upwards [hev] with ω hω
    rw [hω.1, ← hAM]
    rfl
  · filter_upwards [hG] with ω hg hω
    exact hg (hAM ▸ hω)

include hκ hhm hb' hT hcf hζ hγ hHcm hHc hc'b in
/-- Every finite stopped canonical stage launched in the retained joint-chart
experiment has its full conditional flow-line law. The initial field law is
proved from R1; there is no conditional-kernel hypothesis in this theorem. -/
theorem exists_joint_stage_couplings
    (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (θ : ℕ → ℝ)
    (τ : (n : ℕ) → Past RecData n → (ℝ≥0 → ℝ) × ℝ≥0∞ → ℝ≥0∞)
    (hτm : ∀ n, Measurable fun x : Past RecData n × ((ℝ≥0 → ℝ) × ℝ≥0∞) =>
      τ n x.1 x.2)
    (hτ : ∀ n (x : Past RecData n) (t : ℝ≥0),
      MeasurableSet[pathKilledSigma t] {e | τ n x e ≤ (t : ℝ≥0∞)}) :
    ∃ A : Set RecData, MeasurableSet A ∧
      (∀ᵐ ω ∂P, γ ω s ∈ H ↔ cfRec s W ζ ω ∈ A) ∧
      ∀ n, ∀ᵐ ω₀ ∂P,
        (stageState hκ h12p (jointWordOfRec (specOffset κ) κ c') θ τ
          (cfRec s W ζ) Hc n ω₀).1 ∈ finitePast A n →
        IsFlowLineDriver κ
          (stageWord (κ := κ) (jointWordOfRec (specOffset κ) κ c') θ n
            (stageState hκ h12p (jointWordOfRec (specOffset κ) κ c') θ τ
              (cfRec s W ζ) Hc n ω₀).1).fn
          (stageWord (κ := κ) (jointWordOfRec (specOffset κ) κ c') θ n
            (stageState hκ h12p (jointWordOfRec (specOffset κ) κ c') θ τ
              (cfRec s W ζ) Hc n ω₀).1).jumps (θ n)
          (condExpKernel P (MeasurableSpace.comap
            (fun ω => (stageState hκ h12p (jointWordOfRec (specOffset κ) κ c') θ τ
              (cfRec s W ζ) Hc n ω).1) inferInstance) ω₀)
          (fun ω => (stageState hκ h12p (jointWordOfRec (specOffset κ) κ c') θ τ
            (cfRec s W ζ) Hc n ω).2)
          (fun t ω => (stagePiece hκ h12p (jointWordOfRec (specOffset κ) κ c') θ τ
            (cfRec s W ζ) Hc n ω).1 t)
          (fun ω => (stagePiece hκ h12p (jointWordOfRec (specOffset κ) κ c') θ τ
            (cfRec s W ζ) Hc n ω).2) := by
  obtain ⟨A, hA, hev, hker⟩ :=
    exists_joint_initial_kernel hκ hhm hb' hT hcf hζ hγ s hHcm hHc c' hc'b
  refine ⟨A, hA, hev, ?_⟩
  exact ae_isFlowLineDriver_stagePiece hκ h12p h13 _ θ τ (cfRec s W ζ) Hc
    (measurable_jointWordOfRec (specOffset κ) κ c')
    (measurable_cfRec
      (show IsCenteredCounterflowDriver κ P h W ζ from ⟨b', J', h', hb', hT, hcf⟩) s)
    hHcm hτm hτ hA hker

end InteractingSLE.Theorem14.GW2JDetR5
