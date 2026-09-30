import QuantumZipper.Proofs.Thm18.A1RS2Dec

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS2 (13): fixed-driver convergence of the dyadic pairings at rational parameters

**`ae_smear_conv_fixed`**: for a fixed good driver and a free field `X`, almost surely, at every
rational parameter `q ∈ smearU` and rational radius `r ∈ [0, 1]`, the dyadic pairings
`∫ avgReg X k dν_{q,r}` converge to `evalReg X ν_{q,r}` (Duplantier–Sheffield, Invent. Math. 185
(2011), Prop. 3.1 at one measure: `FrostmanReg.ae_tendsto_integral_avgReg_frostman`,
`FrostmanReg.ae_evalReg_eq_frostman`; the uniform Frostman bound `isFrostman_a1rfNu_unif`). This
is the convergence input `hA` of `evalReg_Z_split` at the countably many parameters of the
rational Cauchy estimate. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm

/-- Every parameter of `smearU` lies in a (degenerate in time) parameter box. -/
theorem exists_smearBox_mem {p : Fin 4 → ℝ} (hp : p ∈ smearU) :
    ∃ R : ℕ, p ∈ smearBox (p 0) (p 0) R := by
  obtain ⟨R, hR⟩ := exists_nat_ge (‖parD p‖ + |Real.log (p 3)| + p 3)
  refine ⟨R, ⟨le_rfl, le_rfl⟩, by linarith [abs_nonneg (Real.log (p 3)), hp.2.le], ?_, ?_⟩
  · have hle : -(R : ℝ) ≤ Real.log (p 3) := by
      linarith [neg_abs_le (Real.log (p 3)), norm_nonneg (parD p), hp.2.le]
    calc Real.exp (-(R : ℝ)) ≤ Real.exp (Real.log (p 3)) := Real.exp_le_exp.2 hle
      _ = p 3 := Real.exp_log hp.2
  · have := Real.add_one_le_exp (R : ℝ)
    linarith [norm_nonneg (parD p), abs_nonneg (Real.log (p 3))]

end A1RS
end R18
end QuantumZipper
