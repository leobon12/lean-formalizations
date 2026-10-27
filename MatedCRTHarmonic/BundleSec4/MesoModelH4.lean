import MatedCRTHarmonic.BundleSec4.MesoModelTriple
import MatedCRTHarmonic.GMS4cM.BundleSec4Link

/-!
# The mated-CRT map conclusion from the triple-centred H4 alone

`GMS4cM/BundleSec4Link.lean` proves the restricted Lemma 4.3 measurability on every frozen coupling,
`GMS4cM.lemma43MeasurableM_holds D hγ : BundleSec4.Lemma43MeasurableM D`. Plugged into the final two-input theorem
(`BundleSec4/MesoModelTriple.lean`, the triple bridge), the only remaining named fact is the triple-centred
good-event second moment:

* **`H4TripleForAllBundles`** — for every frozen coupling on a standard Borel space,
  `GMS4O.Prop48GoodEventSecondMomentInputTriple D hγ q ζ (bundle_H1 D hγ hζ)` at some admissible `q, ζ` (the second-moment input);
* `twoInputsTripleForAllBundles_of_H4Triple`;
* **the companion map conclusion**, `exists_cellModel_of_matingOfTrees_of_H4Triple`;
* `bundle_exists_admissible_qζ` — admissible parameters exist for every `γ ∈ (0, 2)` (for the final instantiation by a
  producer valid at every admissible `q, ζ`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.BundleSec4

open MatedCRTHarmonic

/-- Admissible Proposition 4.8 parameters exist for every `γ ∈ (0, 2)`:
`q = min (2/(2+γ)²) γ / 2`, `ζ = min (2/(2+γ)²) γ / 400`. -/
theorem bundle_exists_admissible_qζ {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∃ q ζ : ℝ, q ∈ Ioo (0 : ℝ) (min (2 / (2 + γ) ^ 2) γ) ∧ ζ ∈ Ioo (0 : ℝ) (q / 100) := by
  have h1 : 0 < 2 / (2 + γ) ^ 2 := by have := hγ.1; positivity
  have hm : 0 < min (2 / (2 + γ) ^ 2) γ := lt_min h1 hγ.1
  exact ⟨min (2 / (2 + γ) ^ 2) γ / 2, min (2 / (2 + γ) ^ 2) γ / 400, ⟨by positivity, by linarith⟩,
    ⟨by positivity, by linarith⟩⟩

/-- **The one remaining named fact**: the triple-centred H4 at the first-moment input, for every frozen coupling. -/
def H4TripleForAllBundles : Prop :=
  ∀ (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 2) (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω)
    (P : Measure Ω) (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
    (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2)
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm),
      ∃ (q ζ : ℝ) (_ : q ∈ Ioo (0 : ℝ) (min (2 / (2 + γ) ^ 2) γ)) (hζ : ζ ∈ Ioo (0 : ℝ) (q / 100)),
        GMS4O.Prop48GoodEventSecondMomentInputTriple D hγ q ζ (bundle_H1 D hγ hζ)

/-- the final two inputs from the triple H4 alone (the `lemma43MeasurableM_holds`). -/
theorem twoInputsTripleForAllBundles_of_H4Triple (h : H4TripleForAllBundles) :
    TwoInputsTripleForAllBundles :=
  fun γ hγ Ω mΩ hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D =>
    ⟨h γ hγ Ω mΩ hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D, GMS4cM.lemma43MeasurableM_holds D hγ⟩

/-- **`exists_cellModel_of_matingOfTrees` (frozen v3 type) from the triple H4 alone.** -/
theorem exists_cellModel_of_matingOfTrees_of_H4Triple (h : H4TripleForAllBundles) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → MatedCRT.MatingOfTreesInput γ → MatedCRT.CellModelExists γ :=
  exists_cellModel_of_matingOfTrees_of_twoInputsTriple (twoInputsTripleForAllBundles_of_H4Triple h)

end MatedCRTHarmonic.BundleSec4
