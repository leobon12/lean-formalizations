import QuantumZipper.Proofs.Thm18.G3AreaPalm
import QuantumZipper.Proofs.Thm18.R18G3TSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T: the area input of scheme `C` (`G3TProfAreaStmt`)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, proof of Theorem 1.8,
p. 71 (near the Palm point the field looks like a free field, so the zoomed quantum area of a
fixed half-ball is `≥ 1` with probability `→ 1`), and p. 28 (the Palm weighting adds `−γ log|·|`
to `𝔥₀`). This file is our own assembly on top of the cited lemmas, copying the proved chain of
the free scheme (`ae_isAreaGood_normField`, `ae_g3PalmLaw_of_ae_field`,
`eventually_measureReal_zoomPalm_lt`, `g3AreaStmt_of_palm`) for the profile-shifted field
`g3pField γ (g3wProf γ)`.

On folded circles `g3pField γ (g3wProf γ) = zField X 1 + Lf (γ − 2/γ)`
(`h0rev (γ²) = Lf (−2/γ)`, `g3wProf γ = Lf γ`, and `∫ a·f + ∫ b·f = ∫ (a+b)·f` with no
integrability needed), `γ − 2/γ < Q`, so `LogSingGood.logSingGoodAS_holds` applies; the area
measure is the free one weighted by the density `‖z‖^{−(γ−2/γ)γ}`, positive on `ℍ`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace R18

open Thm18Asm LQGMeas LocalRule Factorization CoordsFull GoodSample

set_option linter.unusedSectionVars false

/-! ## The shifted field as a free field plus a log potential -/

theorem g3wProf_eq_Lf (γ : ℝ) : g3wProf γ = LogSingGood.Lf γ := by
  funext v
  simp only [g3wProf, LogSingGood.Lf]
  ring

theorem ofFun_Lf_add (a b : ℝ) (μ : Measure ℂ) :
    ofFun (LogSingGood.Lf a) μ + ofFun (LogSingGood.Lf b) μ =
      ofFun (LogSingGood.Lf (a + b)) μ := by
  simp only [ofFun, LogSingGood.Lf, integral_const_mul]
  ring

theorem g3pField_fc_eq_Lf {γ : ℝ} (hγ : 0 < γ) (ω : gffBase.Ω) (c : ℂ) (ρ : ℝ) :
    g3pField γ (g3wProf γ) ω (foldedCircle c ρ) =
      (BdryExist.zField gffBase.X 1 ω + ofFun (LogSingGood.Lf (γ - 2 / γ)))
        (foldedCircle c ρ) := by
  have h := normField_fc_eq_Lf hγ gffBase.X ω c ρ
  simp only [g3pField, Pi.add_apply] at h ⊢
  rw [h, g3wProf_eq_Lf, add_assoc, ofFun_Lf_add, show -(2 / γ) + γ = γ - 2 / γ by ring]

theorem coords_g3pField_eq_Lf {γ : ℝ} (hγ : 0 < γ) (ω : gffBase.Ω) :
    coords (g3pField γ (g3wProf γ) ω) =
      coords (BdryExist.zField gffBase.X 1 ω + ofFun (LogSingGood.Lf (γ - 2 / γ))) :=
  funext fun _ => g3pField_fc_eq_Lf hγ ω _ _

/-! ## Almost sure area-goodness of the shifted field -/

/-- **Almost surely the profile-shifted field `h − γ log|·|` is area-good.** -/
theorem ae_isAreaGood_g3pField {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂gffBase.P, IsAreaGood γ (g3pField γ (g3wProf γ) ω) := by
  have hαQ : γ - 2 / γ < Qc γ := by
    unfold Qc
    have h : 1 < 2 / γ := (one_lt_div hγ).2 hγ2
    linarith
  filter_upwards [PositivityArea.ae_forall_pos_qAreaMeasure gffBase.gff hγ hγ2,
    LogSingGood.logSingGoodAS_holds (γ := γ) (α := γ - 2 / γ) hγ hγ2 hαQ gffBase.Ω _
      gffBase.P gffBase.X inferInstance gffBase.gff,
    AreaOffsets.ae_isLQGGood gffBase.gff hγ hγ2] with ω hpos hLf hXg
  have hLf' : IsLQGGood γ (gffBase.X ω + ofFun (LogSingGood.Lf (γ - 2 / γ))) := hLf
  have hgoodZ : IsLQGGood γ
      (BdryExist.zField gffBase.X 1 ω + ofFun (LogSingGood.Lf (γ - 2 / γ))) := by
    rw [zField_add_Lf_eq_addConst]
    exact hLf'.addConst _
  have hgood : IsLQGGood γ (g3pField γ (g3wProf γ) ω) :=
    (WedgeGood.isLQGGood_congr_coords (coords_g3pField_eq_Lf hγ ω)).2 hgoodZ
  refine ⟨hgood, fun V hV hVH hne => ?_⟩
  have hrep : qAreaMeasure γ
      (BdryExist.zField gffBase.X 1 ω + ofFun (LogSingGood.Lf (γ - 2 / γ))) =
      ENNReal.ofReal (Real.exp (γ * (-(gffBase.X ω (foldedCircle 0 1))))) •
        (qAreaMeasure γ (gffBase.X ω)).withDensity
          (fun z => ENNReal.ofReal (‖z‖ ^ (-((γ - 2 / γ) * γ)))) := by
    rw [zField_add_Lf_eq_addConst, qAreaMeasure_addConst hLf' _,
      qAreaMeasure_add_Lf_of_isLQGGood (x := gffBase.X ω) hXg]
  have hap : areaApprox γ (g3pField γ (g3wProf γ) ω) =
      areaApprox γ (BdryExist.zField gffBase.X 1 ω + ofFun (LogSingGood.Lf (γ - 2 / γ))) :=
    PositivityArea.areaApprox_congr_pcirc
      (fun i => congrFun (coords_g3pField_eq_Lf hγ ω) i.1) γ
  have hlim : IsVagueLimitOn H (areaApprox γ (g3pField γ (g3wProf γ) ω))
      (qAreaMeasure γ
        (BdryExist.zField gffBase.X 1 ω + ofFun (LogSingGood.Lf (γ - 2 / γ)))) := by
    rw [hap]
    exact Prop16Area.G.isVagueLimitOn_H_of_good hgoodZ
  rw [qAreaMeasure_eq hlim, hrep, Measure.smul_apply, smul_eq_mul]
  refine ENNReal.mul_pos (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' ?_
  have hmeas : Measurable fun z : ℂ => ENNReal.ofReal (‖z‖ ^ (-((γ - 2 / γ) * γ))) :=
    ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)
  rw [Ne, withDensity_apply_eq_zero hmeas]
  have hV' : {z : ℂ | ENNReal.ofReal (‖z‖ ^ (-((γ - 2 / γ) * γ))) ≠ 0} ∩ V = V := by
    refine inter_eq_right.2 fun z hz => ?_
    have him : 0 < z.im := hVH hz
    have hn : 0 < ‖z‖ := norm_pos_iff.2 fun h0 => by simp [h0] at him
    exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hn _)).ne'
  rw [hV']
  exact (hpos V hV hVH hne).ne'

/-! ## Transfer to the Palm law of scheme `C` -/

/-! ## The zoomed Palm-area bound for scheme `C` -/

/-! ## Scheme `C` depends on `C` only through the zoom -/

section Congr

variable {γ : ℝ} {g : ℂ → ℝ} {i i' : G3Idx}

theorem g3pν₁_congr (h₁ : i.1.1 = i'.1.1) (h₂ : i.1.2.1 = i'.1.2.1) :
    g3pν₁ γ g i = g3pν₁ γ g i' := by
  funext ω
  simp only [g3pν₁, G3Idx.t₁, G3Idx.r₁, G3Idx.δ, G3Idx.η, h₁, h₂]

theorem g3pν₀_congr (h₁ : i.1.1 = i'.1.1) (h₂ : i.1.2.1 = i'.1.2.1) :
    g3pν₀ γ g i = g3pν₀ γ g i' := by
  funext ω
  simp only [g3pν₀, G3Idx.t₁, G3Idx.r₁, G3Idx.t₂, G3Idx.r₂, G3Idx.δ, G3Idx.η, h₁, h₂]

end Congr

/-! ## The area input of scheme `C` -/

end R18
end QuantumZipper
