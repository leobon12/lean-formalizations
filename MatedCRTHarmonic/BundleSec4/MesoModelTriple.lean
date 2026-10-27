import MatedCRTHarmonic.BundleSec4.Lemma43M
import MatedCRTHarmonic.GMS4.Prop48CanonicalTripleConclusion

/-!
# The mated-CRT map conclusion from the (triple-mean) H4 and `Lemma43MeasurableM`

The restatement `GMS4.Canonical.prop48ZeroConeLintegral_of_tripleH4` takes only the triple-centred H4
`GMS4O.Prop48GoodEventSecondMomentInputTriple D hγ q ζ H1` at the H1 (H2, H3 and the triple mean premise are
discharged inside). With it:

* **`TwoInputsTripleForAllBundles`** — for every frozen coupling on a standard Borel space: the triple H4 at
  `bundle_H1 D hγ hζ` for some admissible `q, ζ`, and `BundleSec4.Lemma43MeasurableM D`;
* `inputsMForAllBundles_of_twoInputsTriple`; **the companion map conclusion**,
  `exists_cellModel_of_matingOfTrees_of_twoInputsTriple`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.BundleSec4

open MatedCRTHarmonic

/-- **The two remaining named facts, form**: (a) the triple-centred H4 at `bundle_H1 D hγ hζ` for some
admissible `q, ζ`, (b) `BundleSec4.Lemma43MeasurableM D`. -/
def TwoInputsTripleForAllBundles : Prop :=
  ∀ (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 2) (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω)
    (P : Measure Ω) (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
    (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2)
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm),
      (∃ (q ζ : ℝ) (_ : q ∈ Ioo (0 : ℝ) (min (2 / (2 + γ) ^ 2) γ)) (hζ : ζ ∈ Ioo (0 : ℝ) (q / 100)),
          GMS4O.Prop48GoodEventSecondMomentInputTriple D hγ q ζ (bundle_H1 D hγ hζ)) ∧
      Lemma43MeasurableM D

/-- the restricted inputs from the two facts (the triple bridge; `zeroConeCase0At_of_lintegral`). -/
theorem inputsMForAllBundles_of_twoInputsTriple (h : TwoInputsTripleForAllBundles) : InputsMForAllBundles := by
  intro γ hγ Ω mΩ hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D
  obtain ⟨⟨q, ζ, hq, hζ, H4⟩, hL⟩ := h γ hγ Ω mΩ hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D
  exact ⟨zeroConeCase0At_of_lintegral D hγ ⟨by norm_num, by norm_num⟩
    (GMS4.Canonical.prop48ZeroConeLintegral_of_tripleH4 D hγ q ζ hq hζ H4), hL⟩

/-- **`exists_cellModel_of_matingOfTrees` (frozen v3 type) from the two facts.** -/
theorem exists_cellModel_of_matingOfTrees_of_twoInputsTriple (h : TwoInputsTripleForAllBundles) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → MatedCRT.MatingOfTreesInput γ → MatedCRT.CellModelExists γ :=
  exists_cellModel_of_matingOfTrees_of_prop410AtForAllBundles
    (prop410AtForAllBundles_of_inputsM (inputsMForAllBundles_of_twoInputsTriple h))

end MatedCRTHarmonic.BundleSec4
