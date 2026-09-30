import QuantumZipper.Proofs.Thm18.G3ZrMain
import QuantumZipper.Proofs.Thm18.G3ZrDil2
import QuantumZipper.Proofs.Thm18.G1Side3Red

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Z-REG (14): the inner integrals of the curve Fubini formulas at the representative

For a.e. good path, a.s. in `ω'`, the measurable inner functionals `g1PhiM` / `g3PhiM2` at the
canonical wedge `wedgeRep γ X A ω'` are the Palm-window integrals through the curve maps
(`ae_g1Inner_rep`, `ae_g3Inner_rep`; the latter up to the positivity of the length partner, a
statement about the wedge alone). From `g1Inner_eq_g1PhiMA`, `g3Inner_eq_g3PhiM2A` and
`ae_g1FacRegA_rep`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Zr

open G3Z2b2 D3Plus

theorem ae_good_wedgeRep {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω' : Type} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ}
    (hX : IsFreeGFFModConstH X P') (hA : IsWedgeProcess (γ - 2 / γ) (Qc γ) A P')
    (hXA : IndepFun X (fun ω t => A t ω) P') : ∀ᵐ ω' ∂P', IsLQGGood γ (wedgeRep γ X A ω') := by
  filter_upwards [LogSingGood.wedgeRefGoodAS_holds hγ hγ2 (alpha_lt_Qc hγ hγ2) Ω' _ P' X A
    inferInstance hX hA hXA, G1RC.ae_scale_pos hγ hγ2 hX hA hXA] with ω' hg hb
  have hgW : IsLQGGood γ (G1RC.wedge0 γ X A ω') := hg
  exact hgW.rescale hγ hb

end G3Zr
end Thm18Asm
end QuantumZipper
