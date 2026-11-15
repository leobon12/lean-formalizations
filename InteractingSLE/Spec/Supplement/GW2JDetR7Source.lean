/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR7Kernel

/-! # The actual GW2 stopped-pair Gaussian kernel from the source couplings -/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open QuantumZipper (H chiC fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2JDetR7

open Restart Exist Exist.StagedLaw WholeField LocalSets
open Supp8.GB6 Supp8.GB6LineL Supp8.GB6LMean Supp8.Q3Chain GW2TipSystem

/-- The original physical flow and counterflow have their Gaussian union
kernel with both stopped histories and both own germs retained. The mean is
the actual local-set mean. No image-word or stopped-kernel premise is used. -/
theorem exists_actual_union_kernel
    (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    {κ θ : ℝ} (hκ : 0 < κ)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' : Ω → DistOn upperHalfPlaneOpens} {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (hh : IsGFFWithBoundaryData P h b J)
    {b' : ℝ → ℝ} {J' : Finset ℝ} (hb' : IsPiecewiseConstantBoundaryData b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1)
      (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω))
    {W Wα : ℝ≥0 → Ω → ℝ} {ζ ζα : Ω → ℝ≥0∞}
    (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    (hfl : IsFlowLineDriver κ b J θ P h Wα ζα) (s t : ℝ≥0) :
    ∃ (u₀ : ℂ → ℝ) (ℋ : {m : MeasurableSpace Ω // m ≤ mΩ})
      (K : Ω → Set ℂ) (g : Ω → DistOn upperHalfPlaneOpens),
      IsBoundedHarmonicExtension (cfData (16 / κ) b' J')
        (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀ ∧
      IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h' u₀) P ∧
      Measurable[ℋ.1] (gb6Rec t Wα ζα) ∧ Measurable[ℋ.1] (cfRec s W ζ) ∧
      Measurable[ℋ.1, hittingSigma] K ∧
      (∀ᵐ ω ∂P, K ω = fwdHull (Ito.rpath (W · ω)) s) ∧
      unionMarks ℋ.1 (retSet t Wα ζα) K (centredField h' u₀) ≤ mΩ ∧
      IsLocalSetMean (fun ω => retSet t Wα ζα ω ∪ K ω) (centredField h' u₀) P g ∧
      IsCondZeroBoundaryGFF P
        (unionMarks ℋ.1 (retSet t Wα ζα) K (centredField h' u₀))
        (fun ω => H \ (retSet t Wα ζα ω ∪ K ω))
        (fun ω => centredField h' u₀ ω - g ω) ∧
      ∀ φ : TestOn upperHalfPlaneOpens,
        P[fun ω => Complex.exp (Complex.I * (centredField h' u₀ ω φ : ℂ)) |
            unionMarks ℋ.1 (retSet t Wα ζα) K (centredField h' u₀)] =ᵐ[P]
          fun ω => rangeKerCF (g ω) (H \ (retSet t Wα ζα ω ∪ K ω)) φ := by
  obtain ⟨c, hcJ, hcb⟩ := BoundaryWord.exists_fn_eq hb
  have hGc : IsGFFWithBoundaryData P h c.fn c.jumps := by
    rw [hcJ]
    exact WangWu.isGFFWithBoundaryData_congr (fun y hy => (hcb y hy).symm) hh
  have hflc : IsFlowLineDriver κ c.fn c.jumps θ P h Wα ζα :=
    (isFlowLineDriver_congr_of_eqOn hb c.isPiecewiseConstantBoundaryData J hcb).2 hfl
  obtain ⟨u₀, ℋ, K, hu₀, hzero, hRF, hRC, hKm, hKe, hKc, hRm, -, -, -, hloc⟩ :=
    exists_actual_union_local h12 h13 hκ hGc hb' hT hcf hζ hflc s t
  have hRc : ∀ᵐ ω ∂P, retSet t Wα ζα ω ⊆ H ∧
      IsOpen (H \ retSet t Wα ζα ω) :=
    Eventually.of_forall fun ω =>
      ⟨retSet_subset_H t Wα ζα ω, isOpen_H_diff_retSet t Wα ζα ω⟩
  obtain ⟨hΓ, g, hg, hk, hchar⟩ :=
    exists_union_kernel_with_own_germs hzero ℋ.2 hRm hKm hRc hKc hloc
  exact ⟨u₀, ℋ, K, g, hu₀, hzero, hRF, hRC, hKm, hKe, hΓ, hg, hk, hchar⟩

end InteractingSLE.Theorem14.GW2JDetR7
