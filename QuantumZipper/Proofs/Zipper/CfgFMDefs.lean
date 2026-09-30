import QuantumZipper.Proofs.Zipper.CfgFMReg
import QuantumZipper.Proofs.Zipper.CfgFMBlock

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CFG-FIRSTMODE (3): the fixed-driver variance node

For a fixed good path `f` (continuous on `[0,T]`, `f 0 = 0`, `1/3`-Hölder: `RegUnif.GoodP`), the
continuous extension `ZE(f, X)` of the regularized values `X((ψ_t)_* fc(c, r))`,
`ψ_t = fwdMapInv (Wof κ T f) t` (`RegUnif.ZE`, `RegUnif.ae_fibre4`), is a Gaussian process in
`(c, r, t)`. `CfgFMVarStmt` asks for the Gaussian variance bounds of its first circle modes in the
rescaled block coordinates `2^n (Re w, Im w, τ, s)`, `2^{3n} t` (`CfgFM.FMHVarHyp`): the analogue
of `Thm18Asm.G1FMPushVarStmt` with the scale `S` replaced by the time `t`, whose increments are only
`1/3`-Hölder (the flow `t ↦ ψ_t` is as regular as the driver, `RegCont.norm_fwdMapInv_add_sub_le`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace QuantumZipper.E6
namespace CfgFM

open RegUnif RegCont

/-- The free-field part of the unzipped raw values along a path/field pair. -/
def fZE {T : ℝ} (hT : 0 ≤ T) (κ : ℝ) (px : C(Icc (0 : ℝ) T, ℝ) × FieldSample) (t : ℝ)
    (p : ℂ × ℝ) : ℝ :=
  ZE hT κ px (pr4 (t, p))

/-- **Node CFG-FM-VAR** (fixed good driver): Gaussian variance bounds for the first modes of the
free-field part, uniformly on `[0,T]` in time. -/
def CfgFMVarStmt (κ T : ℝ) (hT : 0 < T) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample), IsFreeGFFModConstH X P →
    ∀ f ∈ GoodP hT.le (1 / 3), FMHVarHyp P T fun ω => fZE hT.le κ (f, X ω)

end CfgFM
end QuantumZipper.E6
