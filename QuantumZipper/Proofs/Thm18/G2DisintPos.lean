import QuantumZipper.Proofs.Thm18.G2DisintLoc
import QuantumZipper.Proofs.Zipper.F2Step3DensCore
import QuantumZipper.Proofs.LQG.Positivity
import QuantumZipper.Proofs.LQG.BoundaryExistenceAS
import QuantumZipper.Proofs.Zipper.E1CoordChange2
import QuantumZipper.Proofs.Thm18.UnzipBdryPosAtBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 disintegration: the boundary measure of `h` charges every interval left of `0`

Needed so that the length is *strictly* increasing in the bump coefficient (Sheffield,
arXiv:1012.4797, proof of Prop. 5.5, p. 66). Almost surely, for all `a < b < 0`,
`ν_h(a, b) > 0` for `h = normField γ X₀` (`g2_ae_pos_g3Hν`).

Proof: `normField γ X ω = normX X ω + 𝔥₀` on folded circles, `normX X` is a free field
(`isFreeGFFModConstH_normX`) whose boundary measure charges every interval
(`Positivity.ae_forall_pos_qBoundaryMeasure_Ioo`, M4-P2), and on `(a, b)`, away from the
singularity of `𝔥₀ = (2/γ) log|·|`, rule (5.1) (`F2.restrict_eq_withDensity_add_ofFun`) gives
`ν_h = e^{γ𝔥₀/2} ν_{normX X}` with a density bounded below by `e^{γ𝔥₀(b)/2} > 0`.
Own bookkeeping around the cited results.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω

theorem g2_ae_pos_g3Hν {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂gffBase.P, ∀ a b : ℝ, a < b → b < 0 → 0 < g3Hν γ ω (Ioo a b) := by
  have hX' := isFreeGFFModConstH_normX gffBase.gff
  filter_upwards [G3Fid.ae_normField_good gffBase.gff hγ hγ2,
    BdryExist.ae_isVagueLimitR_qBoundaryMeasure hX' hγ hγ2, RegSample.ae_isRegularSample hX',
    Positivity.ae_forall_pos_qBoundaryMeasure_Ioo hX' hγ hγ2] with ω hgood hv hreg hpos
  intro a b hab hb
  have hU : IsOpen (Ioo a b) := isOpen_Ioo
  have key := F2.restrict_eq_withDensity_add_ofFun (x := normField γ gffBase.X ω)
    (y := normX gffBase.X ω) hU ⟨_, hgood.1⟩ ⟨_, hv⟩ hreg (φ := h0rev (γ ^ 2))
    (V := {z : ℂ | z ≠ 0}) isOpen_ne
    (fun t ht => by
      simp only [mem_setOf_eq, ne_eq, Complex.ofReal_eq_zero]
      exact (ht.2.trans hb).ne)
    ((E1.continuousOn_h0rev _).mono inter_subset_left)
    (Eventually.of_forall fun k t _ => by
      unfold avgReg
      congr 1
      funext n
      simp only [normField, Pi.add_apply, normX_of_prob]
      ring)
  have hb0 : 0 < |b| := abs_pos.2 hb.ne
  have hρ : ∀ t ∈ Ioo a b, ENNReal.ofReal (Real.exp (γ / 2 * h0rev (γ ^ 2) (b : ℂ))) ≤
      ENNReal.ofReal (Real.exp (γ / 2 * h0rev (γ ^ 2) (t : ℂ))) := by
    intro t ht
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    unfold h0rev
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    refine Real.log_le_log hb0 ?_
    rw [abs_of_neg hb, abs_of_neg (ht.2.trans hb)]
    linarith [ht.2]
  have h := pos_of_withDensity_ge' hU.measurableSet key
    (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' hρ
    (by rw [Measure.restrict_apply_self]; exact hpos a b hab)
  rwa [Measure.restrict_apply_self] at h

end Thm18Asm
end QuantumZipper
