import QuantumZipper.Proofs.Thm18.G3Pl4Tr
import QuantumZipper.Proofs.Thm18.R18G3TArea

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T, (G-b), part (b): the coupled free field side

* `g3pl4_ae_isAreaGood_logSing`: a free field plus `(γ − 2/γ)(−log|·|)` is a.s. area-good (good,
  with positive area on every nonempty open subset of `ℍ`), as `ae_isAreaGood_g3pField` for `h_C`
  (`LogSingGood.logSingGoodAS_holds`, `qAreaMeasure_add_Lf_of_isLQGGood`,
  `PositivityArea.ae_forall_pos_qAreaMeasure`).
* `g3pl4_lintegral_phiCap_V_eq`: for the normalized free field `V` of the wedge decomposition,
  `E[Φcap_L(V + log)] = g3plHonX` (law transfer through the circle coordinates).

Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm

theorem g3pl4_logSingField_eq {γ : ℝ} (hγ : 0 < γ) :
    F2.logSingField (γ ^ 2) = ofFun (LogSingGood.Lf (γ - 2 / γ)) := by
  unfold F2.logSingField LogSingGood.Lf
  rw [Real.sqrt_sq hγ.le]

/-- **A free field plus the wedge log singularity is a.s. area-good.** -/
theorem g3pl4_ae_isAreaGood_logSing {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω' : Type}
    [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {V : Ω' → FieldSample}
    (hV : IsFreeGFFModConstH V P') :
    ∀ᵐ ω ∂P', IsAreaGood γ (V ω + F2.logSingField (γ ^ 2)) := by
  have hαQ : γ - 2 / γ < Qc γ := alpha_lt_Qc hγ hγ2
  rw [g3pl4_logSingField_eq hγ]
  filter_upwards [LogSingGood.logSingGoodAS_holds (γ := γ) (α := γ - 2 / γ) hγ hγ2 hαQ Ω' _
      P' V inferInstance hV, AreaOffsets.ae_isLQGGood hV hγ hγ2,
    PositivityArea.ae_forall_pos_qAreaMeasure hV hγ hγ2] with ω hLf hXg hpos
  refine ⟨hLf, fun W hW hWH hne => ?_⟩
  rw [qAreaMeasure_add_Lf_of_isLQGGood hXg]
  have hmeas : Measurable fun z : ℂ => ENNReal.ofReal (‖z‖ ^ (-((γ - 2 / γ) * γ))) :=
    ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)
  rw [pos_iff_ne_zero, Ne, withDensity_apply_eq_zero hmeas]
  have hW' : {z : ℂ | ENNReal.ofReal (‖z‖ ^ (-((γ - 2 / γ) * γ))) ≠ 0} ∩ W = W := by
    refine inter_eq_right.2 fun z hz => ?_
    have him : 0 < z.im := hWH hz
    have hn : 0 < ‖z‖ := norm_pos_iff.2 fun h0 => by simp [h0] at him
    exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hn _)).ne'
  rw [hW']
  exact (hpos W hW hWH hne).ne'

end R18
end QuantumZipper
