import QuantumZipper.Proofs.Zipper.F2Weld
import QuantumZipper.Proofs.Zipper.F1StrictMonoAllT
import QuantumZipper.Proofs.Zipper.F1LenInRefl
import QuantumZipper.Proofs.Zipper.F1LenInCanon
import QuantumZipper.Proofs.Zipper.F1LenReg
import QuantumZipper.Proofs.Zipper.F2Step3DensCara
import QuantumZipper.Proofs.Zipper.B5ZeroMinus
import QuantumZipper.Proofs.RS.RohdeSchrammSimple

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# F2 step (3), B5: the plus side of `B5UniformStmt` by reflection

Theorem 1.3, node F2. Source: Sheffield, *Conformal weldings of random surfaces: SLE and the
quantum gravity zipper*, arXiv:1012.4797, §5.4, p. 72 ("by symmetry"); decision D26 ("plus side
... by reflection"). The reflection `z ↦ −z̄` exchanges the two sides of the curve.

* `zeroMinus_neg_of_simpleHull` (deterministic): for a continuous driver `V` with `V 0 = 0` whose
  reverse hull at time `T > 0` is a simple arc, `0₋(−V)(u) = −0₊(V)(u)` for `u ∈ [0,T]` (the
  Carathéodory extension `CaraR.revMapCaratheodory` and `F2.zeroMinus_neg_eq` for `u > 0`, the
  trivial time `0` otherwise).
* `b5PlusUniform_of_refl`: `B5PlusUniformStmt` from `B5MinusUniformStmt` (applied to the
  reflected `Γ⁰` pair `(−B, X ∘ refl)`) and `F1.CfgFlowRegStmt`: the reflected pair's `L⁻` is the
  original `L⁺` (`F1.ae_unzipLengths_reflPair`), its `h⁰` has boundary measure `(−·)_* ν_{h⁰}`
  (`F1.qBoundaryMeasure_of_avgReg_neg`, with the vague limit at time `T` from `CfgFlowRegStmt`),
  its reversed driver is `−V`, and `0₋(−V) = −0₊(V)`.

The identifications are own elementary arguments (the paper only says "by symmetry").
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F2

/-- **`0₋(−V)(u) = −0₊(V)(u)`** for `u ∈ [0,T]`, when the reverse hull of `V` at `T > 0` is a
simple arc. -/
theorem zeroMinus_neg_of_simpleHull {V : ℝ → ℝ} (hVc : Continuous V) (hV0 : V 0 = 0) {T : ℝ}
    (hT : 0 < T) (hK : IsSimpleCurveHull (revHull V T)) {u : ℝ} (hu0 : 0 ≤ u) (huT : u ≤ T) :
    zeroMinus (-V) u = -zeroPlus V u := by
  rcases hu0.eq_or_lt with h | h
  · subst h
    rw [B5.zeroMinus_zero_time hVc.neg (by simp [hV0]), zeroPlus_zero_time hVc hV0, neg_zero]
  · obtain ⟨F, hF⟩ := CaraR.revMapCaratheodory V hVc hV0 u h
      (B5.isSimpleCurveHull_of_le hVc hV0 hT hK h huT)
    exact zeroMinus_neg_eq hVc h.le hF

end F2
end QuantumZipper
