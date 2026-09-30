import QuantumZipper.Proofs.Thm18.G4BSideLen
import QuantumZipper.Proofs.Thm18.G4CoreDefs2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, G4 Core B (task G4C-2): positivity on `[0,∞)` and Core B

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 and §5.4
(pp. 69–72). Own elementary bookkeeping.

In the picture at time `τ > 0`, `[0, O⁺_τ]` is the image of the right side of `η[0,τ]`: with
`z(r) = 0₊^V(r)` (`V = vrev W τ`, continuous and strictly increasing from `0` to `O⁺_τ`, by
reflection of the `0₋` facts), the right half of the pair cocycle gives
`L⁺(τ) = L⁺(τ − r) + ν_{U_τ}[0, z(r)]`, and `L⁺ = L⁻` is strictly increasing
(`F1.LenStrictMonoStmt`, `LenEqStmt`). Hence `ν_{U_τ}` charges every nonempty open subinterval of
`[0, O⁺_τ]` (`pos_of_rightCurve`). The remaining part `[O⁺_τ, ∞)` (the image of the positive real
half-line of the original picture) is the new node `G4UnzipRealPosStmt`.

Main results: `g4UnzipSideAllStmt_of` (Core B) and the direct consumers
`g4UnzipBdryPosRightStmt_of_pair`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G4Core

/-! ## 1. Deterministic positivity on the right side of the curve -/

/-! ## 2. The right curve map at the Theorem 1.8 driver -/

/-- A.s., for all `τ > 0`, `r ↦ 0₊^{vrev W τ}(r)` is continuous and strictly increasing on
`[0, τ]`, vanishes at `0` and ends at `O⁺_τ`. -/
theorem ae_zeroPlus_facts {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) :
    ∀ᵐ ω ∂P, ∀ τ : ℝ, 0 < τ →
      ContinuousOn (zeroPlus (B2.vrev (drive (γ ^ 2) B ω) τ)) (Icc 0 τ) ∧
      StrictMonoOn (zeroPlus (B2.vrev (drive (γ ^ 2) B ω) τ)) (Icc 0 τ) ∧
      zeroPlus (B2.vrev (drive (γ ^ 2) B ω) τ) 0 = 0 ∧
      (sideImages (drive (γ ^ 2) B ω) τ).2 = zeroPlus (B2.vrev (drive (γ ^ 2) B ω) τ) τ := by
  obtain ⟨hγ, hγ2, hB, -, -⟩ := hS
  have hκ : 0 < γ ^ 2 := by positivity
  have hκ4 : γ ^ 2 ≤ 4 := by nlinarith
  have hB' : IsBrownianReal (RegUnif.negB B) P := hB.neg
  filter_upwards [RegUnif.ae_forall_isSimpleCurveHull_revHull_Vr RS.rohdeSchrammSimple hκ hκ4 P _
      hB', RS.ae_real_alive hB' hκ hκ4, hB.cont, hB.eval_zero_ae_eq_zero]
    with ω hK' hal' hc h0 τ hτ
  set W := drive (γ ^ 2) B ω with hWdef
  have hW : Continuous W := by
    rw [hWdef]; unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hW0 : W 0 = 0 := by simp [hWdef, drive, h0]
  have hneg : ∀ v ≤ 0, W v = 0 := fun v hv => by
    simp [hWdef, drive, Real.toNNReal_of_nonpos hv, h0]
  simp only [B2.Vr, RegUnif.drive_negB] at hK' hal'
  have hVc : Continuous (B2.vrev (-W) τ) := B2.continuous_vrev hW.neg τ
  have hV0 : B2.vrev (-W) τ 0 = 0 := B2.vrev_zero hτ.le
  have heq : EqOn (zeroPlus (B2.vrev W τ)) (fun r => -zeroMinus (B2.vrev (-W) τ) r) (Icc 0 τ) :=
    fun r hr => by
      simp only
      rw [zeroPlus_eq_neg_zeroMinus_neg (B2.continuous_vrev hW τ) hr.1, vrev_neg]
  refine ⟨ContinuousOn.congr (B5.continuousOn_zeroMinus_Icc hVc hV0 hτ (hK' τ hτ)).neg heq,
    fun r hr r' hr' hlt => ?_, ?_, ?_⟩
  · rw [heq hr, heq hr']
    exact neg_lt_neg (B5.strictAntiOn_zeroMinus hVc hV0 hτ (hK' τ hτ) hr hr' hlt)
  · rw [heq ⟨le_rfl, hτ.le⟩]
    simp [B5.zeroMinus_zero_time hVc hV0]
  · have e := lswPos_snd_eq_zeroPlus hW hW0 hneg hK' (fun x hx T hT => hal' x hx T hT) hτ
      ⟨le_rfl, hτ.le⟩
    rw [F1.lswPos_zero_of hW0 hneg, sub_zero] at e
    exact e

/-! ## 3. Positivity on `[0,∞)` at all times -/

/-! ## 4. Core B and its consumers -/

end G4Core
end Thm18Asm
end QuantumZipper
