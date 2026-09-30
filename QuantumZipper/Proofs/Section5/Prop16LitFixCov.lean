import QuantumZipper.Proofs.Section5.Prop16LitMain
import QuantumZipper.Proofs.Section5.Prop16NodeB2Rep

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: the chart clause at a fixed point and under the Palm law (D98)

`Prop16Lit.Prop16LitCovStmt` has two clauses at `prop16Q`-a.e. `p = (ω, x)`: (1) the coordinate
change of the local area measure under the chart `ψ_x` (Duplantier–Sheffield, Invent. Math. 185
(2011), Prop. 2.1), (2) the dilation rule for the canonical description. This file names clause
(1) under the weighted law (`Prop16LitCov1Stmt`) and its fixed-point form for the Palm-shifted
field `X + (γ/2) G_D(x, ·)` (`Prop16LitFixCov1Stmt`): the chart is then deterministic, and the
statement is the local coordinate-change theorem `CoordChangeArea.ae_map_qAreaMeasureOn_coordChange_mixed`
read through the zoom (translation by `x`, constant `C/γ`). The passage between them is the Palm
formula (`Prop16Asm.Prop16PalmGlobalStmt`, proved).
-/

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Lit

open Prop16Asm

/-- **Clause (1) at a fixed boundary point, for the Palm-shifted field.** -/
def Prop16LitFixCov1Stmt : Prop :=
  ∀ (γ : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → FieldSample), Prop16Data γ D c d a b h0 P X →
    ∀ (ψ : ℝ → ℂ → ℂ) (r₀ : ℝ → ℝ), LitFamily D a b ψ r₀ → ∀ x ∈ Ioo a b,
    ∀ᵐ ω ∂P, ∀ C : ℝ,
      (qAreaMeasureOn γ (zoomFieldLit γ C
          (ofFun h0 + palmMixedField γ D (realSet (Icc c d)) X x ω) x (ψ x))
          (ball 0 (r₀ x) ∩ H)).map (ψ x) =
        (qAreaMeasureOn γ (zoomField γ C
            (ofFun h0 + palmMixedField γ D (realSet (Icc c d)) X x ω) x)
          (zoomDomain D x)).restrict (ψ x '' (ball 0 (r₀ x) ∩ H))

end Prop16Lit

end QuantumZipper
