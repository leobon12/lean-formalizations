import QuantumZipper.Proofs.Thm18.G2DisintBase
import QuantumZipper.Proofs.Thm18.G3Fid2Main
import QuantumZipper.Proofs.LQG.LocalRule
import QuantumZipper.Proofs.LQG.LogSingularity
import QuantumZipper.Proofs.LQG.RegularClosure
import QuantumZipper.Proofs.Zipper.E1TransferM4Cert

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 disintegration: the local rule for the resampled field, almost surely in `ω`, for all `a`

Sheffield (arXiv:1012.4797, §5.1, rule (5.1), p. 61, used in the proof of Prop. 5.5, p. 66):
`ν_{h + ψ} = e^{γψ/2} ν_h` for continuous `ψ`. For the bump decomposition `h = h₀ + α φ` this gives,
almost surely and **simultaneously for every coefficient `a`**, that the (measurable) boundary
measure of the resampled field `𝔥₀ + h₀ + a φ` (`g2Field`) is `e^{γ(a − α)φ/2} ν_h`
(`g2_ae_bdryM_loc`).

Proof: a.s. `normField γ X ω` has the regularized averages of the regular sample
`Z = zField X 1 ω + ofFun (logPot (−2/γ) 0)` (`G3Fid.normField_fc`), whose approximations converge
vaguely to `ν_h` (`G3Fid.ae_normField_good`); `LocalRule.isVagueLimitR_add_ofFun` (the local rule
for vague limits of regular samples) gives the limit for `Z + ofFun ((a − α) φ)`, the certificate
`E1.M4.BCert` follows from finiteness on compacts (`LogSing.isFiniteMeasureOnCompacts_bdryApprox`),
so `bdryM` is that limit. Own bookkeeping around the cited local rule.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω

theorem g2Field_sub (γ : ℝ) (φ : ℂ → ℝ) (y : AdmIdx → ℝ) (a b : ℝ) (μ : Measure ℂ) :
    g2Field γ φ y a μ = g2Field γ φ y b μ + (a - b) * ∫ z, φ z ∂μ := by
  simp only [g2Field]; ring

/-- **The local rule for the resampled field** (a.s. in `ω`, for every `a`). -/
theorem g2_ae_bdryM_loc {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {φ : ℂ → ℝ} (hφc : Continuous φ)
    (α : Ω₀ → ℝ) :
    ∀ᵐ ω ∂gffBase.P, ∀ a : ℝ, bdryM γ (g2Field γ φ (g2Y φ α ω) a) =
      (g3Hν γ ω).withDensity
        (fun t => ENNReal.ofReal (Real.exp (γ / 2 * ((a - α ω) * φ (t : ℂ))))) := by
  filter_upwards [G3Fid.ae_normField_good gffBase.gff hγ hγ2,
    RegSample.ae_isRegularSample gffBase.gff] with ω hgood hreg
  intro a
  set Z : FieldSample := BdryExist.zField gffBase.X 1 ω + ofFun (LogSing.logPot (-(2 / γ)) 0)
    with hZdef
  have hY : IsRegularSample Z := (hreg.addConst' _).add_ofFun_log' _ 0
  set ψ : ℂ → ℝ := fun z => (a - α ω) * φ z with hψdef
  have hψc : Continuous ψ := continuous_const.mul hφc
  have hZψ : IsRegularSample (Z + ofFun ψ) := hY.add_ofFun' hψc.continuousOn
  have hcirc : ∀ (c : ℂ) (r : ℝ), 0 < r →
      g2Field γ φ (g2Y φ α ω) a (foldedCircle c r) = (Z + ofFun ψ) (foldedCircle c r) := by
    intro c r hr
    rw [hZdef, g2Field_sub γ φ _ a (α ω), g2Field_Y_prob γ φ α ω _
      (D3Plus.isAdmissibleH_foldedCircle' c hr), G3Fid.normField_fc hγ ω]
    simp only [Pi.add_apply, ofFun, hψdef, integral_const_mul]
  have havg : avgReg (g2Field γ φ (g2Y φ α ω) a) = avgReg (Z + ofFun ψ) := by
    funext k z
    unfold avgReg
    congr 1
    funext n
    exact hcirc _ _ (radius_pos k)
  have havgN : avgReg (normField γ gffBase.X ω) = avgReg Z := by
    funext k z
    unfold avgReg
    simp_rw [G3Fid.normField_fc hγ ω, hZdef]
  have hvZ : IsVagueLimitR (bdryApprox γ Z) (g3Hν γ ω) := by
    rw [← Factorization.bdryApprox_congr havgN]
    exact hgood.1
  have hv' := LocalRule.isVagueLimitR_add_ofFun hY hvZ isOpen_univ (fun _ => mem_univ _)
    hψc.continuousOn
  have hfin : ∀ k N : ℕ, bdryApprox γ (Z + ofFun ψ) k (Icc (-(N : ℝ)) N) < ⊤ := fun k N =>
    (LogSing.isFiniteMeasureOnCompacts_bdryApprox hZψ γ k).lt_top_of_isCompact isCompact_Icc
  have hcert := E1.M4.bCert_of_isVagueLimitR hfin hv'
  rw [bdryM_congr_avgReg havg, bdryM, if_pos hcert, qBoundaryMeasure_eq hv']

/-- **The local rule in `h₀`-form** (the coefficient `α` eliminated): a.s., for every `a`, the
boundary measure of `𝔥₀ + h₀ + a φ` is `e^{γ a φ/2}` times that of `𝔥₀ + h₀`. -/
theorem g2_ae_bdryM_loc_Y {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {φ : ℂ → ℝ} (hφc : Continuous φ)
    (hφm : Measurable fun t : ℝ => φ (t : ℂ)) (α : Ω₀ → ℝ) :
    ∀ᵐ ω ∂gffBase.P, ∀ a : ℝ, bdryM γ (g2Field γ φ (g2Y φ α ω) a) =
      (bdryM γ (g2Field γ φ (g2Y φ α ω) 0)).withDensity
        (fun t => ENNReal.ofReal (Real.exp (γ / 2 * (a * φ (t : ℂ))))) := by
  filter_upwards [g2_ae_bdryM_loc hγ hγ2 hφc α] with ω h
  intro a
  have hm : ∀ c : ℝ, Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (γ / 2 * (c * φ (t : ℂ)))) :=
    fun c => ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp ((hφm.const_mul c).const_mul (γ / 2)))
  rw [h a, h 0, ← withDensity_mul _ (hm _) (hm _)]
  congr 1
  funext t
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

end Thm18Asm
end QuantumZipper
