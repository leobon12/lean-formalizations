import QuantumZipper.Proofs.Zipper.E5Model1
import QuantumZipper.Proofs.Zipper.D3PlusN1Local
import QuantumZipper.Proofs.GFF.CoordRegLog

/-!
# E5-MODEL, part 2: the E4 collision field is the D3⁺ model field near `0` (E5-LOC core)

Blueprint `blueprint/E_BRANCH_BLUEPRINT.md` §4 E5, step (1); Sheffield, arXiv:1012.4797, §5.4
(pp. 66–72). By E4 the collided field is `targetColl κ V τ ϖ X'` with `X'` an independent free
field. Here we show, deterministically, that its level-`C` shift is the D3⁺ model field
`zoomModel √κ α₀ C ρ₀ X' g` with `α₀ = √κ − 2/√κ` and the explicit correction

  `g = locCorr … = −(√κ/2)·k_{ϖ_τ} + K₀`,  `K₀ = X'(ρ₀) − (ofFun s + X')(ϖ_τ) − q_τ`

(`k_ϖ` the Neumann potential, `s` the Palm shift function), in the sense of `AgreeNear` on
`ball 0 r` whenever `k_{ϖ_τ}` is integrable on the folded circles inside `ball 0 r` (e.g. if it
is continuous there, `agreeNear_targetColl_zoomModel_of_continuousOn`). The key pointwise identity
is `h0rev κ z + (√κ/2) G_N(0, z) = α₀ · (−log |z|)` (`h0rev_add_neumannH_zero`).

Junk values: `ofFun` is a Bochner integral, so the identity is proved only at probability
measures on which `log |·|` and `k_{ϖ_τ}` are integrable; `AgreeNear` (hence all local readouts,
`D3PlusLocal`, `D3PlusN1Local`) only uses such measures.

`locFieldFull_canonical_eq_canonicalOn` is the rich-data version of
`D3Plus.locField_canonical_eq_canonicalOn` (switch global `canonical` ↔ local `canonicalOn`).

Own elementary proofs (algebra of the definitions).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace E5

open D3Plus E1 B2

/-- The pointwise identity behind step (1): `h0rev κ z + (√κ/2) G_N(0, z) = α₀ (−log |z|)`. -/
theorem h0rev_add_neumannH_zero (κ : ℝ) (z : ℂ) :
    h0rev κ z + Real.sqrt κ / 2 * neumannH ((0 : ℝ) : ℂ) z =
      (Real.sqrt κ - 2 / Real.sqrt κ) * -Real.log ‖z‖ := by
  simp only [h0rev, neumannH, Complex.ofReal_zero, zero_sub, norm_neg, Complex.norm_conj]
  ring

/-- The explicit D3⁺ correction of the collision field at time `t` (for the free field sample
`x`, normalizing measure `ρ₀`). -/
def locCorr (κ : ℝ) (V : ℝ → ℝ) (t : ℝ) (ϖ ρ₀ : Measure ℂ) (x : FieldSample) : ℂ → ℝ :=
  fun z => -(Real.sqrt κ / 2) * PalmNorm.kPot (varpiT V t ϖ) z +
    (x ρ₀ - (ofFun (PalmNorm.shiftFun (Real.sqrt κ) (h0rev κ) (varpiT V t ϖ) 0) + x)
      (varpiT V t ϖ) - qt κ V t ϖ)

/-- **The shifted collision field equals the D3⁺ model field** at every probability measure on
which `log |·|` and `k_{ϖ_t}` are integrable. -/
theorem targetColl_addConst_apply_eq_zoomModel (κ : ℝ) (V : ℝ → ℝ) (t : ℝ) (ϖ ρ₀ : Measure ℂ)
    (x : FieldSample) (C : ℝ) (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hlog : Integrable (fun z => Real.log ‖z‖) μ)
    (hk : Integrable (PalmNorm.kPot (varpiT V t ϖ)) μ) :
    addConst (Thm13Asm.targetColl κ V t ϖ x) (C / Real.sqrt κ) μ =
      zoomModel (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) C ρ₀ x
        (locCorr κ V t ϖ ρ₀ x) μ := by
  set γ := Real.sqrt κ
  set ϖt := varpiT V t ϖ
  set f : ℂ → ℝ := fun z => (γ - 2 / γ) * -Real.log ‖z‖ + -(γ / 2) * PalmNorm.kPot ϖt z
    with hf_def
  have hf : Integrable f μ := (hlog.neg.const_mul _).add (hk.const_mul _)
  have hs : PalmNorm.shiftFun γ (h0rev κ) ϖt 0 = f := by
    funext z
    have h := h0rev_add_neumannH_zero κ z
    simp only [PalmNorm.shiftFun, hf_def]
    rw [← h]
    ring
  set K₀ := x ρ₀ - (ofFun (PalmNorm.shiftFun γ (h0rev κ) ϖt 0) + x) ϖt - qt κ V t ϖ
    with hK₀
  have hz : (fun z => (γ - 2 / γ) * -Real.log ‖z‖ + locCorr κ V t ϖ ρ₀ x z + (C / γ - x ρ₀)) =
      fun z => f z + (K₀ + (C / γ - x ρ₀)) := by
    funext z
    simp only [locCorr, hf_def, hK₀]
    ring
  have hμ : (μ Set.univ).toReal = 1 := by simp
  simp only [zoomModel, Thm13Asm.targetColl, addConst, PalmNorm.normAt, Pi.add_apply, ofFun, hμ]
  rw [hz, integral_add hf (integrable_const _), integral_const, hs]
  simp only [probReal_univ, smul_eq_mul, one_mul, mul_one]
  rw [hK₀]
  simp only [ofFun, Pi.add_apply, hs]
  ring

/-- **`AgreeNear` form** (E5-LOC core): the shifted collision field and the D3⁺ model field have
the same raw values at all dyadic folded circles inside `ball 0 r`, provided `k_{ϖ_t}` is
integrable on the folded circles inside `ball 0 r`. -/
theorem agreeNear_targetColl_zoomModel (κ : ℝ) (V : ℝ → ℝ) (t : ℝ) (ϖ ρ₀ : Measure ℂ)
    (x : FieldSample) (C r : ℝ)
    (hk : ∀ (c : ℂ) (ρ : ℝ), 0 < ρ → ‖c‖ + ρ < r →
      Integrable (PalmNorm.kPot (varpiT V t ϖ)) (foldedCircle c ρ)) :
    AgreeNear (addConst (Thm13Asm.targetColl κ V t ϖ x) (C / Real.sqrt κ))
      (zoomModel (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) C ρ₀ x (locCorr κ V t ϖ ρ₀ x))
      r := fun _ k _ hz =>
  targetColl_addConst_apply_eq_zoomModel κ V t ϖ ρ₀ x C _
    (CoordReg.integrable_log_norm_foldedCircle _ _) (hk _ _ (radius_pos k) hz)

/-- Continuity of `k_{ϖ_t}` on `ball 0 r` gives the integrability hypothesis. -/
theorem integrable_foldedCircle_of_continuousOn {φ : ℂ → ℝ} {r : ℝ}
    (hφ : ContinuousOn φ (Metric.ball (0 : ℂ) r)) (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hcρ : ‖c‖ + ρ < r) : Integrable φ (foldedCircle c ρ) := by
  have hsupp := CircleFubini.foldedCircle_support hρ.le (le_refl (‖c‖ + ρ))
  have hsub : CircleFubini.ballH (‖c‖ + ρ) ⊆ Metric.ball (0 : ℂ) r := fun w hw =>
    Metric.mem_ball.2 (lt_of_le_of_lt (Metric.mem_closedBall.1 hw.1) hcρ)
  have hint : IntegrableOn φ (CircleFubini.ballH (‖c‖ + ρ)) (foldedCircle c ρ) :=
    (hφ.mono hsub).integrableOn_compact (CircleFubini.isCompact_ballH _)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (ae_iff.2 (show (foldedCircle c ρ) {a | a ∉ CircleFubini.ballH (‖c‖ + ρ)} = 0 from hsupp))] at hint

theorem agreeNear_targetColl_zoomModel_of_continuousOn (κ : ℝ) (V : ℝ → ℝ) (t : ℝ)
    (ϖ ρ₀ : Measure ℂ) (x : FieldSample) (C r : ℝ)
    (hk : ContinuousOn (PalmNorm.kPot (varpiT V t ϖ)) (Metric.ball (0 : ℂ) r)) :
    AgreeNear (addConst (Thm13Asm.targetColl κ V t ϖ x) (C / Real.sqrt κ))
      (zoomModel (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) C ρ₀ x (locCorr κ V t ϖ ρ₀ x))
      r :=
  agreeNear_targetColl_zoomModel κ V t ϖ ρ₀ x C r fun c ρ hρ hcρ =>
    integrable_foldedCircle_of_continuousOn hk c ρ hρ hcρ

/-- **Global canonical rich data = local canonical rich data** (rich version of
`D3Plus.locField_canonical_eq_canonicalOn`, same proof). -/
theorem locFieldFull_canonical_eq_canonicalOn {γ r : ℝ} {R : ℕ} {y y' : FieldSample}
    (hag : AgreeNear y y' r) {μ : Measure ℂ} (hy : IsVagueLimitOn H (areaApprox γ y) μ)
    (hpos : 0 < scaleParamOn γ y' (halfDisc r))
    (hlt : scaleParamOn γ y' (halfDisc r) * ((R : ℝ) + 1) < r) :
    scaleParam γ y = scaleParamOn γ y' (halfDisc r) ∧
      locFieldFull R (canonical γ y) = locFieldFull R (canonicalOn γ y' (halfDisc r)) := by
  set s := scaleParamOn γ y' (halfDisc r) with hs
  have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hsR : s * R < r := lt_of_le_of_lt (by nlinarith) hlt
  have hsr : s < r := lt_of_le_of_lt (by nlinarith) hlt
  have hloc : ∀ b : ℝ, b ≤ r → qAreaMeasure γ y (Metric.ball 0 b ∩ H) =
      qAreaMeasureOn γ y' (halfDisc r) (Metric.ball 0 b ∩ H) := by
    intro b hb
    rw [qAreaMeasure_eq hy, qAreaMeasureOn_eq_restrict_of_agree hag hy,
      Measure.restrict_apply (Metric.isOpen_ball.inter isOpen_H).measurableSet]
    have hsub : Metric.ball (0 : ℂ) b ∩ H ⊆ halfDisc r :=
      fun z hz => ⟨Metric.ball_subset_ball hb hz.1, hz.2⟩
    rw [inter_eq_left.2 hsub]
  have hscale := scaleParam_eq_scaleParamOn_of_lt hloc hpos hsr
  refine ⟨hscale, ?_⟩
  rw [canonical, canonicalOn, hscale]
  exact locFieldFull_rescale_congr hag hpos hsR

/-- **E5-LOC, field part, on the good scale event**: if `k_{ϖ_t}` is continuous on `ball 0 r`,
the level-`C` collision field `y` has a quantum-area limit on `H`, and the model scale `a` is
positive with `a (R + 1) < r`, then the rich local data of the canonicalized collision
configuration is the zoom-model data `zLoc`, and its scale is the model scale `zScale`. -/
theorem locG_canonConfig_targetColl_eq_zLoc (κ : ℝ) (V : ℝ → ℝ) (t : ℝ) (ϖ ρ₀ : Measure ℂ)
    (x : FieldSample) (C r : ℝ) (R : ℕ) (d : ℝ → ℝ)
    (hk : ContinuousOn (PalmNorm.kPot (varpiT V t ϖ)) (Metric.ball (0 : ℂ) r))
    {μ : Measure ℂ} (hy : IsVagueLimitOn H (areaApprox (Real.sqrt κ)
      (addConst (Thm13Asm.targetColl κ V t ϖ x) (C / Real.sqrt κ))) μ)
    (hpos : 0 < zScale (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀ C x
      (locCorr κ V t ϖ ρ₀ x))
    (hlt : zScale (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀ C x
      (locCorr κ V t ϖ ρ₀ x) * ((R : ℝ) + 1) < r) :
    scaleParam (Real.sqrt κ) (addConst (Thm13Asm.targetColl κ V t ϖ x) (C / Real.sqrt κ)) =
        zScale (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀ C x (locCorr κ V t ϖ ρ₀ x) ∧
      (locG locFieldFull R (canonConfig (Real.sqrt κ)
        (addConst (Thm13Asm.targetColl κ V t ϖ x) (C / Real.sqrt κ), d))).1 =
        zLoc locFieldFull (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀ R C x
          (locCorr κ V t ϖ ρ₀ x) :=
  locFieldFull_canonical_eq_canonicalOn
    (agreeNear_targetColl_zoomModel_of_continuousOn κ V t ϖ ρ₀ x C r hk) hy hpos hlt

end E5
end QuantumZipper
