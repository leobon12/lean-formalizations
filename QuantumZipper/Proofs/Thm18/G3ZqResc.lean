import QuantumZipper.Proofs.Thm18.G1ZmUnsc

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH (3): the path average does not see the random dilation (rescaling route)

The canonical description `canonical γ W = rescale W Q b` of an unscaled wedge field `W` uses the
random, global scale `b = scaleParam γ W`. Along a fixed path the Palm-window functionals of the
canonical field and of the unscaled field differ by the Brownian scaling `S_b` of the path
(`G1Zm.g1PhiM_canonical_scalePath`, one point). Since the curve is independent of the field and
the law of Brownian motion is invariant under `S_b` for every fixed `b > 0`
(`G1Zm.lintegral_pathOf_scale`), **the path average of the canonical functional equals the path
average of the unscaled functional** (`lintegral_path_rescale`); no measurability of `b` is
needed, because `b` is frozen before the path integral is taken (Tonelli on both sides).

Sheffield, arXiv:1012.4797, p. 70 (the curve is independent of the wedge; scale invariance of
SLE). Own bookkeeping (AGENT_GUIDE cost rule); generic in the functional `Φ`, so it serves both the
one-point (`g1PhiM`) and the two-point (`g3PhiM2`) Palm-window functionals.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Zq

open G1Zm

/-- The Brownian scaling of paths is measurable. -/
theorem measurable_scalePath (b : ℝ) : Measurable (scalePath b) := by
  unfold scalePath
  exact measurable_pi_iff.2 fun s =>
    (measurable_pi_apply (a := ((b ^ 2).toNNReal * s)) (X := fun _ : ℝ≥0 => ℝ)).div_const b

/-- **Brownian scaling of the path law, image-measure form.** -/
theorem lintegral_map_pathOf_scale {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {b : ℝ} (hb : 0 < b)
    {F : (ℝ≥0 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ a, F a ∂(P.map (pathOf B)) = ∫⁻ a, F (scalePath b a) ∂(P.map (pathOf B)) := by
  have hgm : AEMeasurable (pathOf B) P := IsBrownianReal.aemeasurable_pathOf hB
  rw [lintegral_map' hF.aemeasurable hgm,
    lintegral_map' (f := fun a => F (scalePath b a))
      (hF.comp (measurable_scalePath b)).aemeasurable hgm]
  exact lintegral_pathOf_scale hB hb hF

/-- **The path average does not see the random dilation.** Let `Φ` be a measurable functional of
(field, path), `Wc, Wu` two random fields and `b > 0` a random scale such that, for a.e. `ω'` and
a.e. path `a`, `Φ (Wc ω', S_{b ω'} a) = Φ (Wu ω', a)`. Then the path averages of the `P'`-means
of `Φ (Wc, ·)` and `Φ (Wu, ·)` agree. -/
theorem lintegral_path_rescale {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    {Φ : FieldSample × (ℝ≥0 → ℝ) → ℝ≥0∞} (hΦ : Measurable Φ)
    {Wc Wu : Ω' → FieldSample} {b : Ω' → ℝ}
    (hc : AEMeasurable (uncurry fun (a : ℝ≥0 → ℝ) (ω' : Ω') => Φ (Wc ω', a))
      ((P.map (pathOf B)).prod P'))
    (hu : AEMeasurable (uncurry fun (a : ℝ≥0 → ℝ) (ω' : Ω') => Φ (Wu ω', a))
      ((P.map (pathOf B)).prod P'))
    (hid : ∀ᵐ ω' ∂P', 0 < b ω' ∧
      ∀ᵐ a ∂(P.map (pathOf B)), Φ (Wc ω', scalePath (b ω') a) = Φ (Wu ω', a)) :
    ∫⁻ a, ∫⁻ ω', Φ (Wc ω', a) ∂P' ∂(P.map (pathOf B)) =
      ∫⁻ a, ∫⁻ ω', Φ (Wu ω', a) ∂P' ∂(P.map (pathOf B)) := by
  rw [lintegral_lintegral_swap hc, lintegral_lintegral_swap hu]
  refine lintegral_congr_ae ?_
  filter_upwards [hid] with ω' ⟨hb, hω'⟩
  rw [lintegral_map_pathOf_scale hB hb (F := fun a => Φ (Wc ω', a))
    (hΦ.comp (measurable_const.prodMk measurable_id))]
  exact lintegral_congr_ae hω'

end G3Zq
end Thm18Asm
end QuantumZipper
