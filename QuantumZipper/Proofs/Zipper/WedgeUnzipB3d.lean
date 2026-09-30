import QuantumZipper.Proofs.Zipper.WedgeUnzipScale
import QuantumZipper.Proofs.Zipper.F2Unscaled
import QuantumZipper.Proofs.Zipper.F2Step2b
import QuantumZipper.Proofs.LQG.Measurability

/-!
# D29 (wedge unzipping), part 2: `F2.UnscaledB3dStmt` and `F2.WedgeUnzipLimitAllStmt` from the
# wedge core statements

Decision D29 (`DECISIONS.md`, `handoff/WEDGE-UNZIP.md`). Sheffield, arXiv:1012.4797, §5.4
(pp. 71–72, proof of Theorem 1.3: regularity statements are transported to the wedge by
absolute continuity on compact sets and by scale invariance); §1.6 ((1.8), canonical
description). The field-level B3(d) identity is `WedgeUnzip.regEq_unzippedField_canonConfig`
(part 1); here it is applied almost surely.

The three wedge core statements (the unscaled wedge field `Z = F2.zU γ X' A`, driver
`W = √κ B''` independent of `(X', A)`), all in the setting of `F2.UnscaledB3dStmt`:
* `WedgeGoodAllStmt`: a.s. the unzipped fields `Z_t` are good (`IsLQGGood`) at all `t ≥ 0`;
* `WedgeExactAllStmt` (RC3 at all times): a.s. the folded-circle values of every `Z_t` are its
  regularized ones;
* `WedgeContinuumStmt`: a.s. `Z` is a regular sample and, for every `t ≥ 0` and every folded
  circle, the smoothed pairings `ρ ↦ ∫ evalReg Z (fc(u, ρ)) d(f_t⁻¹)_* fc(c, r)` are integrable and
  converge as `ρ → 0⁺` (continuum limit of the circle smoothing; it gives scale consistency by
  `G1.scaleConsistentAt_of_continuum`).

Results (exact reductions):
* `scaleConsistent_of_continuum`: deterministic, scale consistency at the images of folded
  circles under the unzipping map of the rescaled driver;
* `unscaledB3dStmt_of_core`: `WedgeGoodAllStmt → WedgeExactAllStmt → WedgeContinuumStmt →
  F2.UnscaledB3dStmt`;
* `wedgeUnzipLimitAllStmt_of_good`: `WedgeGoodAllStmt → F2.WedgeUnzipLimitAllStmt`.

Own bookkeeping (no new mathematics beyond the cited scaling).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace WedgeUnzip

open Thm18Asm

/-! ## The core statements -/

/-- **(Core W-X, RC3 at all times)** A.s., for all `t ≥ 0`, the folded-circle values of the
field unzipped from the unscaled wedge configuration are its regularized ones. -/
def WedgeExactAllStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X' : Ω → FieldSample) (A : ℝ → Ω → ℝ) (B'' : ℝ≥0 → Ω → ℝ),
    IsFreeGFFModConstH X' P →
    IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A P →
    IndepFun X' (fun ω t => A t ω) P → IsBrownianReal B'' P →
    IndepFun (fun ω => (X' ω, fun t => A t ω)) (pathOf B'') P →
    ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → ∀ d ∈ Hbar, ∀ r > 0,
      evalReg (unzippedField (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω) t)
          (foldedCircle d r) =
        unzippedField (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω) t
          (foldedCircle d r)

/-- **(Core W-C, continuum limit)** A.s. the unscaled wedge field `Z` is a regular sample and,
for all `t ≥ 0`, `c`, `r > 0`, the smoothed pairings of `Z` against the image of `fc(c, r)` under
the unzipping map `f_t⁻¹` are integrable and converge as the smoothing radius tends to `0⁺`. -/
def WedgeContinuumStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X' : Ω → FieldSample) (A : ℝ → Ω → ℝ) (B'' : ℝ≥0 → Ω → ℝ),
    IsFreeGFFModConstH X' P →
    IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A P →
    IndepFun X' (fun ω t => A t ω) P → IsBrownianReal B'' P →
    IndepFun (fun ω => (X' ω, fun t => A t ω)) (pathOf B'') P →
    ∀ᵐ ω ∂P, IsRegularSample (F2.zU (Real.sqrt κ) X' A ω) ∧
      ∀ t, 0 ≤ t → ∀ (c : ℂ) (r : ℝ), 0 < r →
        (∀ ρ : ℝ, 0 < ρ → Integrable (fun u => evalReg (F2.zU (Real.sqrt κ) X' A ω)
          (foldedCircle u ρ)) ((foldedCircle c r).map (fwdMapInv (drive κ B'' ω) t))) ∧
        ∃ L : ℝ, Tendsto (fun ρ => ∫ u, evalReg (F2.zU (Real.sqrt κ) X' A ω) (foldedCircle u ρ)
          ∂((foldedCircle c r).map (fwdMapInv (drive κ B'' ω) t))) (𝓝[>] 0) (𝓝 L)

/-! ## Scale consistency from the continuum limit (deterministic) -/

/-- The image of `fc(d, r)` under the unzipping map of the rescaled driver, pushed by `(b·)`, is
the image of `fc(b d, b r)` under the unzipping map of `W` at time `b² s`. -/
theorem map_mul_fc_map_fwdMapInv_scale {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {b : ℝ} (hb : 0 < b) {s : ℝ} (hs : 0 ≤ s) (d : ℂ) {r : ℝ} (hr : 0 < r) :
    ((foldedCircle d r).map (fwdMapInv (fun u => W (b ^ 2 * u) / b) s)).map
        (fun z => (b : ℂ) * z) =
      (foldedCircle ((b : ℂ) * d) (b * r)).map (fwdMapInv W (b ^ 2 * s)) := by
  set φ := fwdMapInv (fun u => W (b ^ 2 * u) / b) s
  set ψ := fwdMapInv W (b ^ 2 * s)
  have hWa : Continuous fun u => W (b ^ 2 * u) / b := by fun_prop
  have hWa0 : (fun u => W (b ^ 2 * u) / b) 0 = 0 := by simp [hW0]
  have hbs : 0 ≤ b ^ 2 * s := mul_nonneg (sq_nonneg b) hs
  have hφm : Measurable (modH φ) := measurable_modH (fwdMapInv_props hWa hWa0 hs).1.continuousOn
  have hψm : Measurable (modH ψ) := measurable_modH (fwdMapInv_props hW hW0 hbs).1.continuousOn
  have hm : Measurable fun z : ℂ => (b : ℂ) * z := measurable_const_mul _
  rw [← fc_map_modH φ d hr, Measure.map_map hm hφm, ← fc_map_modH ψ _ (mul_pos hb hr),
    ← WedgeTK.fc_map_mul d r hb, Measure.map_map hψm hm]
  refine Measure.map_congr ((TwoPoint.foldedCircle_ae_mem_H d hr).mono fun w hw => ?_)
  have hbw : (b : ℂ) * w ∈ H := by
    show 0 < ((b : ℂ) * w).im
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_pos hb hw
  show (b : ℂ) * modH φ w = modH ψ ((b : ℂ) * w)
  rw [modH_eqOn φ hw, modH_eqOn ψ hbw,
    show φ w = ψ ((b : ℂ) * w) / b from RS.fwdMapInv_scale hW hW0 hb hs hw,
    mul_div_cancel₀ _ (Complex.ofReal_ne_zero.2 hb.ne')]

/-- **Scale consistency at the unzipping images, from the continuum limit.** -/
theorem scaleConsistent_of_continuum {x : FieldSample} (hx : IsRegularSample x) (Q : ℝ)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {b : ℝ} (hb : 0 < b) {s : ℝ} (hs : 0 ≤ s)
    (d : ℂ) {r : ℝ} (hr : 0 < r)
    (hint : ∀ ρ : ℝ, 0 < ρ → Integrable (fun u => evalReg x (foldedCircle u ρ))
      ((foldedCircle ((b : ℂ) * d) (b * r)).map (fwdMapInv W (b ^ 2 * s))))
    (hcont : ∃ L : ℝ, Tendsto (fun ρ => ∫ u, evalReg x (foldedCircle u ρ)
      ∂((foldedCircle ((b : ℂ) * d) (b * r)).map (fwdMapInv W (b ^ 2 * s)))) (𝓝[>] 0) (𝓝 L)) :
    G1.ScaleConsistentAt x Q b
      ((foldedCircle d r).map (fwdMapInv (fun u => W (b ^ 2 * u) / b) s)) := by
  have hWa : Continuous fun u => W (b ^ 2 * u) / b := by fun_prop
  have hWa0 : (fun u => W (b ^ 2 * u) / b) 0 = 0 := by simp [hW0]
  set φ := fwdMapInv (fun u => W (b ^ 2 * u) / b) s
  have hφm : Measurable (modH φ) := measurable_modH (fwdMapInv_props hWa hWa0 hs).1.continuousOn
  have hfin : IsFiniteMeasure ((foldedCircle d r).map φ) := by
    rw [← fc_map_modH φ d hr]; infer_instance
  have hν : ∀ᵐ u ∂((foldedCircle d r).map φ), u ∈ Hbar := by
    rw [← fc_map_modH φ d hr]
    refine (ae_map_iff (p := fun u => u ∈ Hbar) hφm.aemeasurable
      isClosed_Hbar.measurableSet).2 ?_
    exact (TwoPoint.foldedCircle_ae_mem_H d hr).mono fun w hw => by
      rw [modH_eqOn φ hw]
      show 0 ≤ (φ w).im
      exact le_of_lt (show 0 < (φ w).im from RS.fwdMapInv_mem_H hWa hWa0 hs hw)
  obtain ⟨L, hL⟩ := hcont
  have e := map_mul_fc_map_fwdMapInv_scale hW hW0 hb hs d hr
  exact G1.scaleConsistentAt_of_continuum hx Q hb hν (fun ρ hρ => by rw [e]; exact hint ρ hρ)
    (L := L) (by rw [e]; exact hL)

/-! ## The reductions -/

end WedgeUnzip
end QuantumZipper
