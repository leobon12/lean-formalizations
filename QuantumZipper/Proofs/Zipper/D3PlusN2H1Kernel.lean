import QuantumZipper.Proofs.Zipper.D3PlusN2TmZRad

/-!
# N2-H1, kernel part: the free-field lateral family is uncorrelated with the radial family

Task N2-H1. Source: Duplantier–Miller–Sheffield, arXiv:1409.7055, proof of Prop. 4.7(ii), p. 77
(independence of the projections onto `H₁(ℍ)` and `H₂(ℍ)`); the free-field analogue is
`WedgeTK.indepFun_radialProc_lateralPart` (`Proofs/LQG/WedgeToolkit.lean` §15), whose proof
computes the cross-covariance through `WedgeTK.kernelCov2_lat_rad` for the specific coordinate
pairs `latPairId`, `radPair`.

Here we generalise that computation to the *whole* lateral family: for every admissible measure
`μ`, the lateral generator `X μ − X (radSmear μ)` (which is `lateralPart X μ` for a regular
sample, `WedgeTK.ae_lateral_X`) is uncorrelated with every radial increment
`X (fc(0,a)) − X (fc(0,b))`. The proof is the rotation-invariance argument of DMS p. 77:

* `kernelCov neumannH ν (foldedCircle 0 c) = ∫ x, -2 log (max c ‖x‖) ∂ν`
  (`WedgeTK.kernelCov_fc0_right`), so the cross-covariance is the integral of the *radial*
  function `g(‖x‖) = -2 log(max a ‖x‖) + 2 log(max b ‖x‖)` against `μ − radSmear μ`;
* that integral vanishes because `radSmear μ = ∫ foldedCircle 0 ‖z‖ ∂μ(z)` averages over the
  circle of radius `‖z‖` about `0`, on which `g(‖·‖)` is constant
  (`WedgeTK.integral_phi_radSmear`).

The radial smearing is exactly the "mean-zero on circles" projection, so this is the statement
that the lateral (mean-zero on circles) and radial (circle-average) parts of the free field are
uncorrelated; joint Gaussianity then gives independence
(`ProbabilityTheory.IsGaussianProcess.indepFun_of_covariance_eq_zero`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

open WedgeTK

/-! ## The kernel identity -/

/-- **(H1, covariance)** The lateral generator `X μ − X (radSmear μ)` of the free field is
uncorrelated with the radial increment `X (fc(0,a)) − X (fc(0,b))`: the cross-covariance is
`∫ x, (2 log (max b ‖x‖) − 2 log (max a ‖x‖)) ∂(μ − radSmear μ)`, and the integrand is a radial
function, which `radSmear` leaves unchanged. -/
theorem kernelCov2_latFam_radPair {μ : Measure ℂ} (hμ : IsAdmissibleH μ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    kernelCov2 neumannH (μ, radSmear μ) (foldedCircle 0 a, foldedCircle 0 b) = 0 := by
  have hμ' := isAdmissibleH_radSmear hμ
  have hIa : Integrable (fun x : ℂ => -2 * Real.log (max a ‖x‖)) μ :=
    integrable_of_continuousOn_Hbar (continuous_phi ha).continuousOn hμ
  have hIb : Integrable (fun x : ℂ => -2 * Real.log (max b ‖x‖)) μ :=
    integrable_of_continuousOn_Hbar (continuous_phi hb).continuousOn hμ
  have hIa' : Integrable (fun x : ℂ => -2 * Real.log (max a ‖x‖)) (radSmear μ) :=
    integrable_of_continuousOn_Hbar (continuous_phi ha).continuousOn hμ'
  have hIb' : Integrable (fun x : ℂ => -2 * Real.log (max b ‖x‖)) (radSmear μ) :=
    integrable_of_continuousOn_Hbar (continuous_phi hb).continuousOn hμ'
  simp only [kernelCov2]
  rw [kernelCov_fc0_right _ ha, kernelCov_fc0_right _ hb, kernelCov_fc0_right _ ha,
    kernelCov_fc0_right _ hb, integral_phi_radSmear hμ ha, integral_phi_radSmear hμ hb]
  ring

/-! ## The Gaussian families and their independence -/

/-- The index set of the lateral family: all admissible measures. -/
abbrev AdmIdx : Type := {μ : Measure ℂ // IsAdmissibleH μ}

/-- The lateral family `μ ↦ X μ − X (radSmear μ)` of the free field. -/
def latFam {Ω : Type*} (X : Ω → FieldSample) : AdmIdx → Ω → ℝ :=
  fun μ ω => X ω μ.1 - X ω (radSmear μ.1)

theorem measurable_latFam {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) :
    Measurable fun ω (μ : AdmIdx) => latFam X μ ω :=
  measurable_pi_iff.2 fun μ => (hX.measurable_coord _).sub (hX.measurable_coord _)

/-- The lateral family together with the radial family `X (fc(0,e^{−t})) − X (fc(0,1))` is a
Gaussian process: both are differences of pairings of the free field. -/
theorem isGaussianProcess_latFam_radPair {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) :
    IsGaussianProcess (Sum.elim (latFam X) (fun t : ℝ => gaussFam X radPair t)) P := by
  refine (hX.gaussian.comp_right (Sum.elim (fun μ : AdmIdx => ⟨(μ.1, radSmear μ.1), μ.2,
    isAdmissibleH_radSmear μ.2, (radSmear_univ μ.1).symm⟩) radPair)).congr fun i => ?_
  rcases i with μ | t
  · exact ae_of_all _ fun ω => rfl
  · exact ae_of_all _ fun ω => rfl

/-- The cross-covariances of the lateral and radial families vanish. -/
theorem cov_latFam_radPair {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P)
    (μ : AdmIdx) (t : ℝ) : cov[latFam X μ, fun ω => gaussFam X radPair t ω; P] = 0 := by
  have h := hX.covariance_eq (μ.1, radSmear μ.1) (radPair t).1 μ.2
    (isAdmissibleH_radSmear μ.2) (radSmear_univ μ.1).symm (radPair t).2.1 (radPair t).2.2.1
    (radPair t).2.2.2
  rw [show latFam X μ = fun ω => X ω μ.1 - X ω (radSmear μ.1) from rfl,
    show (fun ω => gaussFam X radPair t ω) =
      fun ω => X ω (radPair t).1.1 - X ω (radPair t).1.2 from rfl, h]
  unfold radPair
  exact kernelCov2_latFam_radPair μ.2 (Real.exp_pos _) one_pos

/-- **(H1, free-field form)** The full lateral family of the free field is independent of the
radial family `t ↦ X (fc(0,e^{−t})) − X (fc(0,1))` (DMS arXiv:1409.7055 p. 77, rotation
invariance of the Green function; the general form of `WedgeTK.indepFun_radialProc_lateralPart`). -/
theorem indepFun_latFam_radPair {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) :
    IndepFun (fun ω (μ : AdmIdx) => latFam X μ ω)
      (fun ω (t : ℝ) => gaussFam X radPair t ω) P :=
  (isGaussianProcess_latFam_radPair hX).indepFun_of_covariance_eq_zero
    (fun μ => (hX.measurable_coord _).sub (hX.measurable_coord _) |>.aemeasurable)
    (fun t => (measurable_gaussFam hX radPair t).aemeasurable)
    fun μ t => cov_latFam_radPair hX μ t

end D3Plus
end QuantumZipper
