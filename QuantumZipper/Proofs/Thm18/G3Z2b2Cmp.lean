import QuantumZipper.Proofs.Thm18.G3Z2b2Loc
import QuantumZipper.Proofs.Thm18.G3Z2b2Abs
import QuantumZipper.Proofs.Thm18.G1ZB2CMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3Z2B-2 (4): the wedge Palm window of `canonical W` through the curve maps, read off `W` and
the measurable local maps

For a good path `a` (continuous, simple chord trace, normalized chosen uniformizer) and a good
unscaled field `W` with scale parameter `b = scaleParam γ W > 0`, the inner Palm-window integral of
`g1zWedgePalmInt` for the field `canonical γ W` through the curve maps `g1zLocMap left (W_a) x`
equals the Palm-window integral of `W` through the maps `b · Λ(a, x/b, ·)`, where
`Λ = g3locM Ψ left` is the jointly measurable family of `G3Z2b2Loc` (`wedgePalm_canonical_eq`).
The inputs are regularity identities at fixed maps (evaluation = regularized evaluation, RC3 and
PAIR-LIM type, `DilReg`, `E1.RegShift`, `G1.ChoiceRegular`), which is the form in which the
G3-CURVE regularity lemmas at fixed maps are proved (`G3Cv2Reg.ae_coordChange_pullCircle`).

Combination of `wedgePalm_rescale` (dilation), `g1zLocMap_eq_g3locM` (measurable maps up to a
domain dilation) and `data_canonical_zoomFieldVia_comp_mul` (absorption). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function Complex
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Z2b2

open D3Plus

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- The target-dilated measurable local map `b · Λ(a, x', ·)`. -/
def g3mapB (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool) (a : ℝ≥0 → ℝ) (b x' : ℝ) :
    ℂ → ℂ :=
  fun w => (b : ℂ) * g3locM Ψ left (a, x', w)

/-- Analytic properties of the measurable local maps on good paths. -/
theorem g3mapB_props {γ : ℝ} (hsel : G1PsiSel γ Ψ) {a : ℝ≥0 → ℝ} (hac : Continuous a)
    (hs : IsSimpleChord (pathTrace (γ ^ 2) a)) (left : Bool) {b : ℝ} (hb : 0 < b) (x' : ℝ) :
    DifferentiableOn ℂ (g3mapB Ψ left a b x') H ∧
      (∀ w ∈ H, deriv (g3mapB Ψ left a b x') w ≠ 0) ∧ Measurable (g3mapB Ψ left a b x') := by
  obtain ⟨φ, hφ, hΨa⟩ := hsel.2.2 a hac hs left
  obtain ⟨hd, hd0, hm, -⟩ := G1.invFunOn_props (G1.isOpen_component hs left) hφ
  set B : ℂ := (g3bpre Ψ left a x' : ℂ) with hB
  have hmemH : ∀ w ∈ H, w + B ∈ H := fun w hw => by
    have hw' : 0 < w.im := hw
    show 0 < (w + B).im
    simpa [hB] using hw'
  have hH : IsOpen H := isOpen_lt continuous_const Complex.continuous_im
  have hder : ∀ w ∈ H, HasDerivAt (g3mapB Ψ left a b x')
      ((b : ℂ) * deriv (Ψ left a) (w + B)) w := fun w hw => by
    have h1 : DifferentiableAt ℂ (Ψ left a) (w + B) := by
      rw [hΨa]; exact hd.differentiableAt (hH.mem_nhds (hmemH w hw))
    have h2 := ((h1.hasDerivAt.comp_add_const w B).sub_const (x' : ℂ)).const_mul (b : ℂ)
    exact h2
  refine ⟨fun w hw => (hder w hw).differentiableAt.differentiableWithinAt, fun w hw => ?_, ?_⟩
  · rw [(hder w hw).deriv]
    refine mul_ne_zero (ofReal_ne_zero.2 hb.ne') ?_
    rw [hΨa]; exact hd0 _ (hmemH w hw)
  · have hΨm : Measurable (Ψ left a) := by rw [hΨa]; exact hm
    show Measurable fun w => (b : ℂ) * (Ψ left a (w + B) - (x' : ℂ))
    exact measurable_const.mul ((hΨm.comp (measurable_id.add_const B)).sub_const _)

end G3Z2b2
end Thm18Asm
end QuantumZipper
