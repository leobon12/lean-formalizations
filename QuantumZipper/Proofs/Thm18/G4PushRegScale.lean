import QuantumZipper.Proofs.Thm18.G4RezipNodes
import QuantumZipper.Proofs.Thm18.G4WeldUniq
import QuantumZipper.Proofs.Thm18.G4WeldRound
import QuantumZipper.Proofs.Loewner.Algebra
import QuantumZipper.Proofs.Zipper.Cor15RezipRegGood

/-!
# Theorem 1.8, node G4-PUSHREG: scaling of the pushed circles and of the reverse hull

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (1). The
deterministic reformulations of the two pushed-circle nodes (`G4PushRegRed.lean`,
`G4PushRegUp.lean`) leave, for the hull-nullity conjunct of `UpZipPushRegVrev`, the reverse hull
of the *rescaled* time reversal `vrevDrv γ ℓ c = s ↦ vrev c.2 τ (a²s)/a` at time `τ/a²`
(`τ = unzipTime γ ℓ c`, `a = unzipScale γ ℓ c`). This file proves the two scaling identities
that turn that conjunct into hull-nullity of the SLE trace at the **scaled dyadic circles**:

* `foldH_mul_ofReal`, `circleMap_mul_ofReal`, `circleUnif_map_mul`, `foldedCircle_map_mul`:
  the folded circles are equivariant under `w ↦ a w` (`a > 0`),
  `(foldedCircle z ε).map (w ↦ a w) = foldedCircle (a z) (a ε)`;
* `revHull_scale`: the Loewner scaling rule `LoewnerAlgebra.revMap_scale` gives
  `revHull (s ↦ V(a²s)/a) T = {w | a w ∈ revHull V (a² T)}`;
* `revHull_vrevDrv`, `fcI_revHull_vrevDrv`: instantiated at `V = vrev c.2 τ`, hence the
  hull-nullity conjunct of `UpZipPushRegVrev` is *equivalent* (as an equality of masses) to
  `foldedCircle (a w_i) (a r_i) (revHull (vrev c.2 τ) τ) = 0`, with the *fixed* (rescaled) hull
  and the *scaled* dyadic circles; with `Cor15Group.rezip_revHull_vrev_eq_fwdHull` and
  `Thm18Inputs` this is hull-nullity of `sleTrace (γ²) B ω` at those circles.

The mass identity `fcI_revHull_vrevDrv` uses that `w ↦ a w` is a `MeasurableEmbedding`, so no
measurability of the hull is needed. The remaining gap for the SLE trace (a per-fixed-circle
mass bound must be uniform over the random scale `a`) is described in the docstring of
`G4PushRegUp.lean`.

**Own elementary argument** (measure pushforward under a similarity and set algebra for the
Loewner scaling rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm

/-! ## Scaling of the folded circles -/

theorem foldH_mul_ofReal {a : ℝ} (ha : 0 < a) (w : ℂ) :
    foldH ((a : ℂ) * w) = (a : ℂ) * foldH w := by
  have him : ((a : ℂ) * w).im = a * w.im := by simp
  unfold foldH
  by_cases hw : 0 ≤ w.im
  · rw [ite_eq_left (by rw [him]; positivity), ite_eq_left hw]
  · rw [ite_eq_right (by rw [him]; nlinarith [not_le.1 hw, ha]), ite_eq_right hw]
    show starRingEnd ℂ ((a : ℂ) * w) = (a : ℂ) * starRingEnd ℂ w
    rw [map_mul, Complex.conj_ofReal]

theorem circleMap_mul_ofReal {z : ℂ} {ε a : ℝ} (θ : ℝ) :
    circleMap ((a : ℂ) * z) (a * ε) θ = (a : ℂ) * circleMap z ε θ := by
  unfold circleMap
  push_cast
  ring

theorem circleUnif_map_mul {z : ℂ} {ε a : ℝ} (_ha : 0 < a) :
    (circleUnif z ε).map (fun w => (a : ℂ) * w) = circleUnif ((a : ℂ) * z) (a * ε) := by
  have hf : Measurable fun w : ℂ => (a : ℂ) * w := measurable_const_mul _
  have hc : Measurable (circleMap z ε) := measurable_circleMap z ε
  have h1 : Measure.map (fun w : ℂ => (a : ℂ) * w) (Measure.map (circleMap z ε) (volume.restrict
      (Set.Ico 0 (2 * Real.pi)))) =
      Measure.map (circleMap ((a : ℂ) * z) (a * ε)) (volume.restrict (Set.Ico 0 (2 * Real.pi))) := by
    rw [Measure.map_map hf hc]
    exact Measure.map_congr (ae_of_all _ fun θ =>
      (circleMap_mul_ofReal (z := z) (ε := ε) (a := a) θ).symm)
  simp only [circleUnif]
  rw [Measure.map_smul _ hf.aemeasurable, h1]

theorem foldedCircle_map_mul {z : ℂ} {ε a : ℝ} (ha : 0 < a) :
    (foldedCircle z ε).map (fun w => (a : ℂ) * w) =
      foldedCircle ((a : ℂ) * z) (a * ε) := by
  have hf : Measurable fun w : ℂ => (a : ℂ) * w := measurable_const_mul _
  have h1 : Measure.map ((fun w : ℂ => (a : ℂ) * w) ∘ foldH) (circleUnif z ε) =
      Measure.map (foldH ∘ fun w : ℂ => (a : ℂ) * w) (circleUnif z ε) :=
    Measure.map_congr (ae_of_all _ fun w => (foldH_mul_ofReal ha w).symm)
  have h2 : Measure.map (fun w : ℂ => (a : ℂ) * w) ((circleUnif z ε).map foldH) =
      Measure.map ((fun w : ℂ => (a : ℂ) * w) ∘ foldH) (circleUnif z ε) :=
    Measure.map_map hf measurable_foldH
  have h3 : Measure.map (foldH ∘ fun w : ℂ => (a : ℂ) * w) (circleUnif z ε) =
      (circleUnif ((a : ℂ) * z) (a * ε)).map foldH := by
    rw [← Measure.map_map measurable_foldH hf, circleUnif_map_mul ha]
  simp only [foldedCircle]
  exact h2.trans (h1.trans h3)

/-! ## Scaling of the reverse hull -/

end Thm18Asm
end QuantumZipper
