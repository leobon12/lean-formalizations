/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR2Hull
import InteractingSLE.Spec.Supplement.GW2JointDetFix
import InteractingSLE.Spec.Supplement.GW2SchedRuleSigma

/-!
# GW2: the root determination statement from pre-contact stopped kernels

The general-boundary joint stopped-kernel construction of GB9 p. 525 remains a
named mathematical input, `GW2StoppedKernelStatement`. It specifies primitive
regular stopped couplings, their complete joint laws, and geometric buffer
coverage. It mentions no canonical driver code or determination conclusion.

From that input this file proves the original `GW2JointDetC2Statement`, including
its simultaneous physical hull identity, and hence `GW2JointKernelC2Statement`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2JDetR2

open Restart Exist Exist.Staged Exist.StagedLaw Sec2.Assembly Supp8.GB6
open GW2JointKernel GW2TipSystem

/-- The literal joint word read from the regularized counterflow record equals
the physical driver's joint word almost surely. -/
theorem ae_jointWord_cfRec {κ a₀ : ℝ} {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {b' : ℝ → ℝ} {J' : Finset ℝ}
    {h' : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (c' : BoundaryWord) (s : ℝ≥0) :
    ∀ᵐ ω ∂P, jointWordOfRec a₀ κ c' (cfRec s W ζ ω) =
      jointWord a₀ κ c' s (fun t => W t ω) := by
  filter_upwards [hζ, ae_driver_zero_continuousOn hcf] with ω hζω hWω
  have hcont : Continuous fun t => W t ω := by
    have hc := hWω.2
    rw [hζω] at hc
    simp only [ENNReal.coe_lt_top, ofPred_true] at hc
    exact continuousOn_univ.1 hc
  unfold cfRec jointWord
  rw [cfE_eq s hζω hWω.1 hcont]

/-- **Named mathematical input, GB9 p. 525.** On the interior-counterflow-tip
event, countably many actual relative stopped experiments have the regular
finite-word joint kernels and cover every available pre-contact physical time.
The retained datum is exactly the counterflow record. -/
def GW2StoppedKernelStatement : Prop :=
  ∀ (κ θ : ℝ), 0 < κ → κ < 4 → -(Real.pi / 2) ≤ θ → θ ≤ Real.pi / 2 →
  ∀ (Ω : Type u) (_mΩ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (h : Ω → DistOn upperHalfPlaneOpens) (b : ℝ → ℝ) (J : Finset ℝ)
    (W Wα : ℝ≥0 → Ω → ℝ) (ζ ζα : Ω → ℝ≥0∞) (γ α : Ω → ℝ≥0 → ℂ)
    (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
    IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J →
    IsPiecewiseConstantBoundaryData b' J' →
    (∀ ω, IsChartTransport infinitySourceChart (-1)
      (-(Real.pi * QuantumZipper.chiC κ)) (QuantumZipper.chiC (16 / κ)) (h ω) (h' ω)) →
    IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ →
    (∀ i : Fin (flowLineNL b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i),
        flowLineRhoL (16 / κ) b' J' 0 0 l) →
    (∀ i : Fin (flowLineNR b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i),
        flowLineRhoR (16 / κ) b' J' 0 0 l) →
    (∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop) →
    IsFlowLineDriver κ b J θ P h Wα ζα →
    (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) →
    ∀ (s : ℝ≥0) (Hc : Ω → DistOn upperHalfPlaneOpens), Measurable Hc →
    (∀ᵐ ω ∂P, γ ω s ∈ H →
      IsChartTransport (jointChart (fun r : ℝ => W r.toNNReal ω) s)
        1 (specOffset κ) (QuantumZipper.chiC κ) (h ω) (Hc ω)) →
    ∀ c' : BoundaryWord, c'.jumps = J' → (∀ y ∉ J', c'.fn y = b' y) →
    ∃ (M : Set Ω)
      (D : ℕ → StoppedKernelBuffer κ θ P (cfRec s W ζ) M
        (jointWordOfRec (specOffset κ) κ c') Hc),
      MeasurableSet[MeasurableSpace.comap (cfRec s W ζ) inferInstance] M ∧
      (∀ᵐ ω ∂P, γ ω s ∈ H ↔ ω ∈ M) ∧
      ∀ᵐ ω ∂P, ω ∈ M → ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζα ω →
        (t : ℝ≥0∞) < firstContactTime (fun a => (α ω a : OnePoint ℂ))
          ((fun r => sphereInv (γ ω r : OnePoint ℂ)) '' Icc 0 s) →
        ∃ (n : ℕ) (q : ℝ≥0),
          (q : ℝ) = relClock (fun r : ℝ => W r.toNNReal ω) s
            (fun r : ℝ => Wα r.toNNReal ω) t ∧
          (q : ℝ≥0∞) < (D n).stop ((D n).sample ω) ∧
          QuantumZipper.fwdHull
            (fun r : ℝ => (D n).driver r.toNNReal ((D n).sample ω)) (q : ℝ) =
            relMap (fun r : ℝ => W r.toNNReal ω) s ''
              QuantumZipper.fwdHull (fun r : ℝ => Wα r.toNNReal ω) t

/-- The original root determination statement follows from the primitive
pre-contact stopped-kernel construction. No extra boundary hypotheses are used. -/
theorem gw2JointDetC2Statement_of_stoppedKernels
    (h12p : Theorem12ParamStatement.{0}) (h13 : Theorem13Statement.{0})
    (hK : GW2StoppedKernelStatement.{u}) : GW2JointDetC2Statement.{u} := by
  intro κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h'
    hb hh hb' hT hcf hpL hpR hreg hfl hα s Hc hHcm hHc F hF c' hc'J hc'b
  obtain ⟨M, D, hM, hev, hcover⟩ :=
    hK κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h'
      hb hh hb' hT hcf hpL hpR hreg hfl hα s Hc hHcm hHc c' hc'J hc'b
  have hr : Measurable (cfRec s W ζ) :=
    measurable_cfRec (show IsCenteredCounterflowDriver κ P h W ζ from
      ⟨b', J', h', hb', hT, hcf⟩) s
  have hMm : MeasurableSet M := hr.comap_le _ hM
  have hword := ae_jointWord_cfRec (a₀ := specOffset κ) hcf
    (hreg.mono fun _ hω => hω.1) c' s
  have hdet := ae_hull_eq_of_buffers h12p h13 hκ hF hr hMm
    (measurable_jointWordOfRec (specOffset κ) κ c') D
    (fun ω t => relClock (fun r : ℝ => W r.toNNReal ω) s
      (fun r : ℝ => Wα r.toNNReal ω) t)
    (fun ω t => relMap (fun r : ℝ => W r.toNNReal ω) s ''
      QuantumZipper.fwdHull (fun r : ℝ => Wα r.toNNReal ω) t)
    (fun ω t => (t : ℝ≥0∞) < ζα ω ∧
      (t : ℝ≥0∞) < firstContactTime (fun a => (α ω a : OnePoint ℂ))
        ((fun r => sphereInv (γ ω r : OnePoint ℂ)) '' Icc 0 s))
    (hcover.mono fun ω hω hωM t ht => hω hωM t ht.1 ht.2)
  filter_upwards [hdet, hev, hword] with ω hd he hw hsH
  have hcore := hd (he.1 hsH)
  rw [hw] at hcore
  exact ⟨hcore.1, fun t ht₁ ht₂ => hcore.2 t ⟨ht₁, ht₂⟩⟩

/-- The complete joint-chart kernel, conditionally on the same stopped-kernel
input, follows by the landed R1/determination assembly. -/
theorem gw2JointKernelC2Statement_of_stoppedKernels
    (h12p : Theorem12ParamStatement.{0}) (h13 : Theorem13Statement.{0})
    (hK : GW2StoppedKernelStatement.{u}) : GW2JointKernelC2Statement.{u} :=
  gw2JointKernelC2Statement_of_detC2
    (gw2JointDetC2Statement_of_stoppedKernels h12p h13 hK)

end InteractingSLE.Theorem14.GW2JDetR2
