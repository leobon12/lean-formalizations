import QuantumZipper.Proofs.Thm18.G3Za3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZOOM-A, item (a), layer 4: circle data of the zoom of `ofFun f + W` through a G0 map

`exists_logSing_data`: for an admissible local map `ψ` of G0 and a profile
`f = γ(−log ‖·‖) + h` near `0` (`h` continuous, harmonic and conjugation-invariant near `0`,
`f` measurable), there are `ρ₂ > 0` and a deterministic `k` with `k ∘ foldH` harmonic on
`ball 0 ρ₂` such that for every free field `W`, almost surely at each folded circle
`fc(c, s)` with `‖c‖ + s ≤ ρ₂` (circles through `0` included)

  `coordChange (ofFun f + W) ψ Q fc = coordChange W ψ Q fc + ∫ γ(−log ‖·‖) dfc + ∫ k dfc`.

`k = remK γ Ψ h` for the reflected extension `Ψ` of `ψ` (`pullData_of_isG0Map`). Own assembly of
G3Za1–3 (Sheffield arXiv:1012.4797, p. 70: near a quantum-typical boundary point the field
looks like a free boundary GFF plus `γ(−log|·|)` plus a smooth function).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology ComplexConjugate
open scoped ENNReal NNReal

namespace QuantumZipper
namespace G3Za

open G3Cv InnerProductSpace

/-- `coordChange` only reads the map on a set carrying the measure. -/
theorem coordChange_congr_ball {ψ Ψ : ℂ → ℂ} {R : ℝ} (heq : EqOn Ψ ψ (ball (0 : ℂ) R))
    {μ : Measure ℂ} (hμ : ∀ᵐ z ∂μ, z ∈ ball (0 : ℂ) R) (x : FieldSample) (Q : ℝ) :
    coordChange x ψ Q μ = coordChange x Ψ Q μ := by
  have hmap : μ.map ψ = μ.map Ψ := Measure.map_congr (hμ.mono fun z hz => (heq hz).symm)
  have hder : (fun z => Real.log ‖deriv ψ z‖) =ᵐ[μ] fun z => Real.log ‖deriv Ψ z‖ :=
    hμ.mono fun z hz => by
      show Real.log ‖deriv ψ z‖ = Real.log ‖deriv Ψ z‖
      rw [(Filter.EventuallyEq.deriv_eq (eventually_of_mem (isOpen_ball.mem_nhds hz) heq))]
  simp only [coordChange, hmap, integral_congr_ae hder]

theorem continuousOn_of_harmonic_foldH {k : ℂ → ℝ} {R R' : ℝ}
    (hk : HarmonicOnNhd (fun z => k (foldH z)) (ball (0 : ℂ) R)) (hR : R' < R) :
    ContinuousOn k (closedBall ((0 : ℝ) : ℂ) R' ∩ Hbar) := by
  intro z hz
  have hz0 : z ∈ closedBall (0 : ℂ) R' := by simpa using hz.1
  have hzR : z ∈ ball (0 : ℂ) R := closedBall_subset_ball hR hz0
  have h1 := (hk z hzR).1.continuousAt.continuousWithinAt
    (s := closedBall ((0 : ℝ) : ℂ) R' ∩ Hbar)
  refine h1.congr (fun v hv => ?_) ?_
  · simp only [CircleFubini.foldH_of_mem' hv.2]
  · simp only [CircleFubini.foldH_of_mem' hz.2]

end G3Za
end QuantumZipper
