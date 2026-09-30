import QuantumZipper.Proofs.Zipper.D3PlusN2H1Indep

/-!
# N2-H1: the radial-average side of the representation node

Task N2-H1. This file proves the second of the two ingredients of `N2H1LatReprStmt`
(`D3PlusN2H1Indep.lean`): the radial average of the *local* field `Z = markovZ X 0 r` against a
local measure `ν` is the free field's radial smear at `ν` minus the constant `ν(univ)·X(fc(0,r))`.

Source: Duplantier–Miller–Sheffield, arXiv:1409.7055, proof of Prop. 4.7(ii), p. 77, and the
Markov decomposition of Sheffield, *Gaussian free fields for mathematicians*, PTRF 139 (2007),
Thm. 2.17 as formalized in `K3.markov_decomposition`.

Route: on the good event of the regular version `G` of `X`, for every `0 < ρ < r`
`radAvgReg (locZField X r ω) ρ = G ω (0,ρ) − G ω (0,r)` (`radAvgReg_locZField_eq`, whose inputs
`GoodRad (X ω) (G ω)`, the raw dyadic values of `locZField` and `X ω (fc(0,r)) = G ω (0,r)` all
hold simultaneously on one event). Since a local `ν` is carried by `closedBall 0 r'`, `r' < r`,
and has no atom at `0`, the two integrands agree `ν`-a.e.; the free field's radial stochastic
Fubini `WedgeTK.ae_integral_radial` gives `∫ z, G ω (0,‖z‖) ∂ν = X ω (radSmear ν)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

open WedgeTK GaussTK

/-- **(H1, radial-average side)** For a local measure `ν` of the half-disc of radius `r`, almost
surely the semicircle averages of the local field are the free field's radial values shifted by
its value at radius `r`:
`∫ z, radAvgReg (locZField X r) ‖z‖ ∂ν = X (radSmear ν) − ν(ℂ) · X (fc(0,r))`. -/
theorem ae_integral_radAvgReg_locZField {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} {r : ℝ} (hX : IsFreeGFFModConstH X P)
    (hr : 0 < r) {ν : Measure ℂ} (hν : K3.IsLocalH 0 r ν) :
    ∀ᵐ ω ∂P, ∫ z, radAvgReg (locZField X r ω) ‖z‖ ∂ν =
      X ω (radSmear ν) - (ν Set.univ).toReal * X ω (foldedCircle 0 r) := by
  obtain ⟨G, hG⟩ := exists_isRegVersion hX
  obtain ⟨hadm, r', hr'r, hνr⟩ := hν
  filter_upwards [hG.ae_good, hG.raw 0 zero_mem_Hbar r hr, ae_locZField_fc0 hX r,
    ae_integral_radial hX hG hadm] with ω hgood hXr hZ hInt
  have hae : (fun z => radAvgReg (locZField X r ω) ‖z‖) =ᵐ[ν]
      fun z => G ω (0, ‖z‖) - G ω (0, r) := by
    have h0 := noAtoms_of_isAdmissibleH hadm 0
    have h0' : ∀ᵐ z ∂ν, z ≠ 0 := by rw [ae_iff]; simpa using h0
    filter_upwards [h0', ae_iff.2 hνr] with z hz0 hz
    have hzn : ‖z‖ < r :=
      lt_of_le_of_lt (by simpa using mem_closedBall_iff_norm.1 hz) hr'r
    exact radAvgReg_locZField_eq hgood hZ hXr.symm (norm_pos_iff.2 hz0) hzn
  have hIntc : Integrable (fun _ : ℂ => G ω (0, r)) ν := by haveI := hadm.1; exact integrable_const _
  rw [integral_congr_ae hae, integral_sub hInt.1 hIntc, hInt.2, integral_const, ← hXr,
    smul_eq_mul, measureReal_def]

/-- The balayage onto the semicircle of radius `r` is already radial: its radial smearing is the
uniform folded circle of radius `r` with the total mass of `ν` (own elementary argument: the
balayage lives on `‖w‖ = r`, where the smearing kernel is constant). -/
theorem radSmear_bal_eq {r : ℝ} (hr : 0 < r) {ν : Measure ℂ} (hν : K3.IsLocalH 0 r ν) :
    radSmear (K3.bal 0 r ν) = ν Set.univ • foldedCircle 0 r := by
  have hsph : ∀ᵐ w ∂K3.bal 0 r ν, ‖w‖ = r := by
    rw [ae_iff]
    refine measure_mono_null (fun w hw => ?_)
      (K3.bal_null_of_forall (t := 0) (r := r) (μ := ν)
        (Metric.isClosed_sphere.measurableSet.inter isClosed_Hbar.measurableSet).compl
        fun z => K3.halfDiscPoisson_compl_eq_zero hr z)
    intro hw'
    apply hw
    simpa using hw'.1
  ext A hA
  rw [radSmear_apply _ hA, Measure.smul_apply, smul_eq_mul]
  have h1 : (fun w => foldedCircle 0 ‖w‖ A) =ᵐ[K3.bal 0 r ν] fun _ => foldedCircle 0 r A := by
    filter_upwards [hsph] with w hw
    rw [hw]
  obtain ⟨-, r', hr'r, hνr⟩ := hν
  rw [lintegral_congr_ae h1, lintegral_const, K3.bal_univ hr hr'r (by simpa using hνr),
    mul_comm]

/-- Almost surely the free field at the radial smearing of the balayage is `ν(ℂ)` times its
value at the folded circle of radius `r`. -/
theorem ae_X_radSmear_bal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) {r : ℝ} (hr : 0 < r)
    {ν : Measure ℂ} (hν : K3.IsLocalH 0 r ν) :
    ∀ᵐ ω ∂P, X ω (radSmear (K3.bal 0 r ν)) = (ν Set.univ).toReal * X ω (foldedCircle 0 r) := by
  have hfin : IsFiniteMeasure ν := hν.1.1
  set c := foldedCircle 0 r with hc
  set m : ℝ≥0 := (ν Set.univ).toNNReal with hm_def
  have hm : ν Set.univ = (m : ℝ≥0∞) := (ENNReal.coe_toNNReal (measure_ne_top ν _)).symm
  have hadm : IsAdmissibleH c := isAdmissibleH_foldedCircle zero_mem_Hbar hr
  have hsm : radSmear (K3.bal 0 r ν) = m • c + (0 : ℝ≥0) • c := by
    rw [radSmear_bal_eq hr hν, zero_smul, add_zero, hm]
    exact (ENNReal.smul_def m c).symm
  filter_upwards [hX.linear c c hadm hadm m 0] with ω h
  rw [hsm, h, hm]
  simp

end D3Plus
end QuantumZipper
