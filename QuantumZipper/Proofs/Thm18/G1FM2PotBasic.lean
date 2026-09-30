import QuantumZipper.Proofs.Thm18.G1FM2Loc
import QuantumZipper.Proofs.Thm18.G1FM2PotDef
import QuantumZipper.Proofs.Zipper.D3PlusN2FMVarPot
import QuantumZipper.Proofs.Zipper.D3PlusN2FMVarPsi
import QuantumZipper.Proofs.Zipper.D3PlusN2FMVarEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-FIRSTMODE round 2 (energy), part 2: the pushed potential in pre-image coordinates

For `f = S ψ` and a first-mode pair `A = fmMeas w v s`, `B = fmMeas w (−v) s` on a disc where
`f` is controlled, the pushed potential at `f x` is the free first-mode potential minus a
smooth correction (`G1FM2.pushPot_comp`):

  `pushPot ψ S w v s (f x) = fmPot w v s x − (∫ ek f x · dA − ∫ ek f x · dB)`,

because `neumannH (f x) (f y) = neumannH x y − ek f x y` (`G1FM2.neumannH_comp`). The first-mode
measures have no atoms (`G1FM2.fmMeas_singleton`), so the off-diagonal Lipschitz bound of `ek`
(`G1FM2.abs_ek_sub_le`) integrates to a Lipschitz bound of the correction.
Own elementary argument.
-/

noncomputable section

open MeasureTheory Filter Metric Set Function
open scoped Topology ComplexConjugate

namespace QuantumZipper
namespace Thm18Asm
namespace G1FM2

open G1RC

/-- First-mode measures have no atoms. -/
theorem fmMeas_singleton {w v : ℂ} {s : ℝ} (hs : 0 ≤ s) (hv : 0 < ‖v‖) (x : ℂ) :
    D3Plus.fmMeas w v s {x} = 0 := by
  have : IsFiniteMeasure (D3Plus.fmMeas w v s) :=
    CircleFubini.isFiniteMeasure_bind_circle (r := s) (D3Plus.fmArc w v)
  have hF := RegCont.isFrostman_bindFc (D3Plus.isFrostman_fmArc w v hv) hs
  set C := 24 * ((6 * Real.pi + (D3Plus.fmBase univ).toReal) / ‖v‖ ^ (1 / 3 : ℝ))
  have hle : ∀ t : ℝ, 0 < t → (D3Plus.fmMeas w v s {x}).toReal ≤ C * t ^ (1 / 3 : ℝ) :=
    fun t ht => (ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono (singleton_subset_iff.2 (mem_closedBall_self ht.le)))).trans (hF x t ht)
  have hlim : Tendsto (fun t : ℝ => C * t ^ (1 / 3 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have h := ((Real.continuousAt_rpow_const 0 (1 / 3 : ℝ) (Or.inr (by norm_num))).tendsto.const_mul
      C).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa [Real.zero_rpow (by norm_num : (1 / 3 : ℝ) ≠ 0)] using h
  have h0 : (D3Plus.fmMeas w v s {x}).toReal ≤ 0 :=
    ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun t ht => hle t ht)
  have h1 := le_antisymm h0 ENNReal.toReal_nonneg
  rcases (ENNReal.toReal_eq_zero_iff _).1 h1 with h | h
  · exact h
  · exact absurd h (measure_ne_top _ _)

variable {ψ : ℂ → ℂ} {S : ℝ}

/-- **The pushed potential in pre-image coordinates.** -/
theorem pushPot_comp (hψ : PsiGood ψ) (hS : 0 < S) {w v : ℂ} {s : ℝ} (hs : 0 ≤ s)
    (hv : 0 < ‖v‖) (hvw : ‖v‖ + s < w.im) (x : ℂ) :
    pushPot ψ S w v s ((S : ℂ) * ψ x) = D3Plus.fmPot w v s x -
      ((∫ y, ek (fun z => (S : ℂ) * ψ z) x y ∂D3Plus.fmMeas w v s) -
        ∫ y, ek (fun z => (S : ℂ) * ψ z) x y ∂D3Plus.fmMeas w (-v) s) := by
  have hv' : 0 < ‖-v‖ := by rwa [norm_neg]
  have hvw' : ‖-v‖ + s < w.im := by rwa [norm_neg]
  have hfm : Measurable fun z => (S : ℂ) * ψ z := measurable_const.mul hψ.1
  have key : ∀ v : ℂ, 0 < ‖v‖ → ‖v‖ + s < w.im →
      ∫ y, neumannH ((S : ℂ) * ψ x) y ∂pfmMeas ψ S w v s =
        (∫ y, neumannH x y ∂D3Plus.fmMeas w v s) -
          ∫ y, ek (fun z => (S : ℂ) * ψ z) x y ∂D3Plus.fmMeas w v s := by
    intro v hv hvw
    have aP := G1FM.isAdmissibleH_pushFm hψ hs hv hvw hS
    have aA := D3Plus.fmAdmStmt_holds w v s hs hv hvw
    have i1 := D3Plus.integrable_neumannH_right_adm aA x
    have hg : AEStronglyMeasurable (fun y => neumannH ((S : ℂ) * ψ x) y)
        ((D3Plus.fmMeas w v s).map fun z => (S : ℂ) * ψ z) :=
      (TwoPoint.measurable_neumannH_uncurry.comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    have i2 : Integrable (fun y => neumannH ((S : ℂ) * ψ x) ((S : ℂ) * ψ y))
        (D3Plus.fmMeas w v s) :=
      (integrable_map_measure hg hfm.aemeasurable).1 (D3Plus.integrable_neumannH_right_adm aP _)
    unfold pfmMeas
    rw [integral_map hfm.aemeasurable hg]
    have e : ∀ y, neumannH ((S : ℂ) * ψ x) ((S : ℂ) * ψ y) =
        neumannH x y - ek (fun z => (S : ℂ) * ψ z) x y := fun y =>
      neumannH_comp (fun z => (S : ℂ) * ψ z) x y
    have i3 : Integrable (fun y => ek (fun z => (S : ℂ) * ψ z) x y) (D3Plus.fmMeas w v s) :=
      (i1.sub i2).congr (ae_of_all _ fun y => by
        show neumannH x y - neumannH ((S : ℂ) * ψ x) ((S : ℂ) * ψ y) = _
        rw [e y]; ring)
    simp_rw [e]
    exact integral_sub i1 i3
  unfold pushPot
  rw [key v hv hvw, key (-v) hv' hvw']
  unfold D3Plus.fmPot
  ring

/-- The correction integrand is integrable. -/
theorem integrable_ek (hψ : PsiGood ψ) (hS : 0 < S) {w v : ℂ} {s : ℝ} (hs : 0 ≤ s)
    (hv : 0 < ‖v‖) (hvw : ‖v‖ + s < w.im) (x : ℂ) :
    Integrable (fun y => ek (fun z => (S : ℂ) * ψ z) x y) (D3Plus.fmMeas w v s) := by
  have hfm : Measurable fun z => (S : ℂ) * ψ z := measurable_const.mul hψ.1
  have aP := G1FM.isAdmissibleH_pushFm hψ hs hv hvw hS
  have aA := D3Plus.fmAdmStmt_holds w v s hs hv hvw
  have i1 := D3Plus.integrable_neumannH_right_adm aA x
  have hg : AEStronglyMeasurable (fun y => neumannH ((S : ℂ) * ψ x) y)
      ((D3Plus.fmMeas w v s).map fun z => (S : ℂ) * ψ z) :=
    (TwoPoint.measurable_neumannH_uncurry.comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have i2 : Integrable (fun y => neumannH ((S : ℂ) * ψ x) ((S : ℂ) * ψ y))
      (D3Plus.fmMeas w v s) :=
    (integrable_map_measure hg hfm.aemeasurable).1 (D3Plus.integrable_neumannH_right_adm aP _)
  exact (i1.sub i2).congr (ae_of_all _ fun y => rfl)

end G1FM2
end Thm18Asm
end QuantumZipper
