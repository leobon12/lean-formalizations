import QuantumZipper.Proofs.Section5.Prop16LitEach
import QuantumZipper.Proofs.Section5.Prop16LitPalmCov
import QuantumZipper.Proofs.Section5.Prop16LitMeasEx
import QuantumZipper.Proofs.Section5.Prop16LitFixCovProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: wiring of the remaining nodes (COORD-CHANGE, D98)

`Prop16Lit.theorem1_6_literal_of_open`: `theorem1_6_literal` from the three remaining open nodes
* `Prop16LitRepMeasAtStmt` (Borel measurability, one level at a time, of the set of local
  readings at which the chart identity holds; input of the Palm transfer);
* `Prop16LitDilEachStmt` (the dilation clause (2) of `Prop16LitCovStmt`, level by level);
* `Prop16LitExStmt` (a.e. existence of the two local vague limits of the chart field),
with the proved chart identity at fixed points (`prop16LitFixCov1Stmt_proved`), its Palm
transfer (`prop16LitCov1_each_of_fix`), the measurability reduction
(`prop16LitMeasStmt_of_exists`) and the level-by-level assembly
(`theorem1_6_literal_of_covEach_meas`). Own wiring.
-/

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Lit

open Prop16Asm

/-- **Node: the dilation clause (2) of `Prop16LitCovStmt`, level by level.** -/
def Prop16LitDilEachStmt : Prop :=
  ∀ (γ : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → FieldSample), Prop16Data γ D c d a b h0 P X →
    ∀ (ψ : ℝ → ℂ → ℂ) (r₀ : ℝ → ℝ), LitFamily D a b ψ r₀ → ∀ C : ℝ,
    ∀ᵐ p ∂(prop16Q γ h0 a b P X),
      0 < scaleParamOn γ (zoomFieldLit γ C (ofFun h0 + X p.1) p.2 (ψ p.2))
          (ball 0 (r₀ p.2) ∩ H) →
        qAreaMeasureOn γ (canonicalOn γ (zoomFieldLit γ C (ofFun h0 + X p.1) p.2 (ψ p.2))
            (ball 0 (r₀ p.2) ∩ H))
          (canonicalDomainOn γ (zoomFieldLit γ C (ofFun h0 + X p.1) p.2 (ψ p.2))
            (ball 0 (r₀ p.2) ∩ H)) =
        (qAreaMeasureOn γ (zoomFieldLit γ C (ofFun h0 + X p.1) p.2 (ψ p.2))
            (ball 0 (r₀ p.2) ∩ H)).map fun z => z /
          (scaleParamOn γ (zoomFieldLit γ C (ofFun h0 + X p.1) p.2 (ψ p.2))
            (ball 0 (r₀ p.2) ∩ H) : ℂ)

end Prop16Lit

end QuantumZipper
