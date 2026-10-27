import MatedCRTHarmonic.GMS4.Prop48ThickLocal
import Mathlib.Probability.Independence.Basic

/-!
# Joint local-law transfer for Proposition 4.8

Equality in law of the restricted 0-cone and normalized whole-plane fields
extends to an independent IG coordinate. A measurable reconstruction then
transports any local configuration observable.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory

namespace MatedCRTHarmonic.GMS4

/-- Equal field and IG marginals, independent in each realization, give the
same joint law. This is the probability step in [18]'s local transfer. -/
theorem prop48_jointLocalLaw_of_indep
    {Ω₀ Ω₁ A B : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω₁]
    [MeasurableSpace A] [MeasurableSpace B]
    {P₀ : Measure Ω₀} {P₁ : Measure Ω₁}
    [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    {f₀ : Ω₀ → A} {f₁ : Ω₁ → A} {g₀ : Ω₀ → B} {g₁ : Ω₁ → B}
    (hf₀ : Measurable f₀) (hf₁ : Measurable f₁)
    (hg₀ : Measurable g₀) (hg₁ : Measurable g₁)
    (hfield : P₀.map f₀ = P₁.map f₁)
    (hIG : P₀.map g₀ = P₁.map g₁)
    (hind₀ : IndepFun f₀ g₀ P₀) (hind₁ : IndepFun f₁ g₁ P₁) :
    P₀.map (fun ω => (f₀ ω, g₀ ω)) =
      P₁.map (fun ω => (f₁ ω, g₁ ω)) := by
  rw [(indepFun_iff_map_prod_eq_prod_map_map hf₀.aemeasurable hg₀.aemeasurable).1 hind₀,
    (indepFun_iff_map_prod_eq_prod_map_map hf₁.aemeasurable hg₁.aemeasurable).1 hind₁,
    hfield, hIG]

/-- The same product-law argument when the frozen IG phase and cone field are
only almost-everywhere measurable. -/
theorem prop48_jointLocalLaw_of_indep_ae
    {Ω₀ Ω₁ A B : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω₁]
    [MeasurableSpace A] [MeasurableSpace B]
    {P₀ : Measure Ω₀} {P₁ : Measure Ω₁}
    [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    {f₀ : Ω₀ → A} {f₁ : Ω₁ → A} {g₀ : Ω₀ → B} {g₁ : Ω₁ → B}
    (hf₀ : AEMeasurable f₀ P₀) (hf₁ : AEMeasurable f₁ P₁)
    (hg₀ : AEMeasurable g₀ P₀) (hg₁ : AEMeasurable g₁ P₁)
    (hfield : P₀.map f₀ = P₁.map f₁)
    (hIG : P₀.map g₀ = P₁.map g₁)
    (hind₀ : IndepFun f₀ g₀ P₀) (hind₁ : IndepFun f₁ g₁ P₁) :
    P₀.map (fun ω => (f₀ ω, g₀ ω)) =
      P₁.map (fun ω => (f₁ ω, g₁ ω)) := by
  rw [(indepFun_iff_map_prod_eq_prod_map_map hf₀ hg₀).1 hind₀,
    (indepFun_iff_map_prod_eq_prod_map_map hf₁ hg₁).1 hind₁,
    hfield, hIG]

/-- The joint local-law identity transports every measurable function of the
restricted field and independent IG input, including the reconstructed local
configuration when the reconstruction supplies its measurable GMC map. -/
theorem prop48_localReconstruction_law_of_indep
    {Ω₀ Ω₁ A B C : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω₁]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    {P₀ : Measure Ω₀} {P₁ : Measure Ω₁}
    [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    {f₀ : Ω₀ → A} {f₁ : Ω₁ → A} {g₀ : Ω₀ → B} {g₁ : Ω₁ → B}
    (hf₀ : Measurable f₀) (hf₁ : Measurable f₁)
    (hg₀ : Measurable g₀) (hg₁ : Measurable g₁)
    (hfield : P₀.map f₀ = P₁.map f₁)
    (hIG : P₀.map g₀ = P₁.map g₁)
    (hind₀ : IndepFun f₀ g₀ P₀) (hind₁ : IndepFun f₁ g₁ P₁)
    (F : A × B → C) (hF : Measurable F) :
    P₀.map (fun ω => F (f₀ ω, g₀ ω)) =
      P₁.map (fun ω => F (f₁ ω, g₁ ω)) := by
  have hjoint := prop48_jointLocalLaw_of_indep hf₀ hf₁ hg₀ hg₁ hfield hIG hind₀ hind₁
  have hm₀ : Measurable fun ω => (f₀ ω, g₀ ω) := hf₀.prodMk hg₀
  have hm₁ : Measurable fun ω => (f₁ ω, g₁ ω) := hf₁.prodMk hg₁
  change P₀.map (F ∘ fun ω => (f₀ ω, g₀ ω)) =
    P₁.map (F ∘ fun ω => (f₁ ω, g₁ ω))
  rw [← Measure.map_map hF hm₀, ← Measure.map_map hF hm₁, hjoint]

end MatedCRTHarmonic.GMS4

