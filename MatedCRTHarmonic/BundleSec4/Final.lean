import MatedCRTHarmonic.BundleSec4.FixedInstance
import MatedCRTHarmonic.BundleSec4.Prop410

/-!
# The mated-CRT map conclusion from ONE instance of [18] Proposition 4.10 for the γ-cone (the smallest named input)

Combining `BundleSec4.FixedInstance` (one Proposition 2.10 instance at `(3/4, 100)` suffices for `hAnnulus38` and `hREC`) with
`BundleSec4.Prop410` (Proposition 2.10 from Proposition 4.10 and the concrete (4.20)):

* `Prop410At P η ρ C` — one fixed-parameter instance of [18] Proposition 4.10 for the area-parametrized curve `η`
  (`∃ β, A, α, Cfail`, every mesh `2^{-k}` and every pair admissible at `(ρ, C, β)`, failure of
  `∫⁻_D f u_*^ε ≤ A ∫⁻_D f + ε^α` has outer probability `≤ Cfail ε^α`);
* `prop210At_of_prop410At` — at MTC's family: `Prop410At P η ρ C ⇒ Prop210At F ρ C` (threshold `2A`, exponent
  `α/2`, rate `Cfail + 2`);
* `exists_cellModel_of_matingOfTrees_of_prop410At`, the companion map conclusion — both frozen v3
  conclusions with `Prop410At M.coupled.family.P C.curve (3/4) 100` (the cone realization's curve of every coupling)
  as the only remaining input.

`Prop410Source` (source quantifier order) gives every admissible instance (`prop410At_of_source`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Real
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.BundleSec4

open MatedCRTHarmonic

/-- **One fixed-parameter instance of [18] Proposition 4.10** for the area-parametrized curve `η` at ambient radius
`ρ` and test constant `C`. -/
def Prop410At {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (η : Ω → C(ℝ, ℂ)) (ρ C : ℝ) : Prop :=
  ∃ β A α Cfail : ℝ, 0 < β ∧ 0 < α ∧ 0 ≤ A ∧ 0 ≤ Cfail ∧
    ∀ (k : ℕ) (V : Set ℂ) (f : ℂ → ℝ), GMS4.Prop210Admissible (CellFamily.mesh k) ρ C β V f →
      P (Prop410Bad η (CellFamily.mesh k) V f A (CellFamily.mesh k ^ α)) ≤
        ENNReal.ofReal (Cfail * CellFamily.mesh k ^ α)

/-- `Prop410At` depends only on the a.e. class of the curve. -/
theorem prop410At_congr_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {η η' : Ω → C(ℝ, ℂ)}
    (hηη' : η =ᵐ[P] η') {ρ C : ℝ} (h : Prop410At P η ρ C) : Prop410At P η' ρ C := by
  obtain ⟨β, A, α, Cfail, hβ, hα, hA, hCfail, h⟩ := h
  refine ⟨β, A, α, Cfail, hβ, hα, hA, hCfail, fun k V f hadm => ?_⟩
  have hnull : P {ω | ¬ η ω = η' ω} = 0 := ae_iff.mp hηη'
  have hsub : Prop410Bad η' (CellFamily.mesh k) V f A (CellFamily.mesh k ^ α) ⊆
      Prop410Bad η (CellFamily.mesh k) V f A (CellFamily.mesh k ^ α) ∪ {ω | ¬ η ω = η' ω} := by
    intro ω hω
    by_cases he : η ω = η' ω
    · left
      change ¬ _ at hω ⊢
      rw [he]
      exact hω
    · exact Or.inr he
  calc
    P (Prop410Bad η' (CellFamily.mesh k) V f A (CellFamily.mesh k ^ α)) ≤
        P (Prop410Bad η (CellFamily.mesh k) V f A (CellFamily.mesh k ^ α)) + P {ω | ¬ η ω = η' ω} :=
      (measure_mono hsub).trans (measure_union_le _ _)
    _ = P (Prop410Bad η (CellFamily.mesh k) V f A (CellFamily.mesh k ^ α)) := by rw [hnull, add_zero]
    _ ≤ _ := h k V f hadm

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- **One instance of Proposition 2.10 from the same instance of Proposition 4.10 and (4.20)** at MTC's family. -/
theorem prop210At_of_prop410At
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2) {ρ C : ℝ} (h : Prop410At P η ρ C) :
    Prop210At (MoTInput.unitMesoModelOfCoupling D hstd hγ).coupled.family ρ C := by
  obtain ⟨β, A, α, Cfail, hβ, hα, hA, hCfail, h⟩ := h
  refine ⟨β, A, α / 2, Cfail + 2, hβ, by positivity, hA, by positivity, fun k V f hadm => ?_⟩
  exact prop210Bad_le_of_prop410Bad D hstd hγ hadm.2.2.2.2.2.2.1.measurableSet hα hCfail (h k V f hadm)

end Coupling

/-- One Proposition 4.10 instance at the cone realization's curve of every coupling gives one Proposition 2.10
instance at MTC's family. -/
theorem prop210At_forAllCouplings_of_prop410At {ρ C : ℝ}
    (h : MesoModel.FinalForAllCouplings fun _ M R => Prop410At M.coupled.family.P R.curve ρ C) :
    MesoModel.FinalForAllCouplings fun _ M _ => Prop210At M.coupled.family ρ C :=
  fun γ hγ Ω mΩ hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D =>
    prop210At_of_prop410At D hstd hγ
      (prop410At_congr_ae (MoTInput.ae_bundleCurve_eq D)
        (h γ hγ Ω mΩ hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D))

/-- **`exists_cellModel_of_matingOfTrees` (frozen v3 type) from ONE Proposition 4.10 instance** at `(3/4, 100)` for
The γ-cone curve of the cone realization of every coupling. -/
theorem exists_cellModel_of_matingOfTrees_of_prop410At
    (h : MesoModel.FinalForAllCouplings fun _ M R => Prop410At M.coupled.family.P R.curve (3 / 4) 100) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → MatedCRT.MatingOfTreesInput γ → MatedCRT.CellModelExists γ :=
  exists_cellModel_of_matingOfTrees_of_prop210At (prop210At_forAllCouplings_of_prop410At h)

/-! ### The same, with Proposition 4.10 stated for the bundle's own γ-cone curve `η` -/

/-- **Proposition 4.10 at `(3/4, 100)` for the bundle's γ-cone curve `η` of every coupling** (stated with the raw bundle variables). -/
def Prop410AtForAllBundles : Prop :=
  ∀ (γ : ℝ) (_ : γ ∈ Ioo (0 : ℝ) 2) (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω)
    (P : Measure Ω) (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
    (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2),
    MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm →
      Prop410At P η (3 / 4) 100

/-- The bundle-variable form gives the realization-curve form used by the final assembly. -/
theorem prop410At_forAllCouplings_of_bundles (h : Prop410AtForAllBundles) :
    MesoModel.FinalForAllCouplings fun _ M R => Prop410At M.coupled.family.P R.curve (3 / 4) 100 :=
  fun γ hγ Ω mΩ hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D =>
    prop410At_congr_ae (MoTInput.ae_bundleCurve_eq D).symm
      (h γ hγ Ω mΩ hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D)

/-- **`exists_cellModel_of_matingOfTrees` (frozen v3 type) from `Prop410AtForAllBundles`.** -/
theorem exists_cellModel_of_matingOfTrees_of_prop410AtForAllBundles (h : Prop410AtForAllBundles) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → MatedCRT.MatingOfTreesInput γ → MatedCRT.CellModelExists γ :=
  exists_cellModel_of_matingOfTrees_of_prop410At (prop410At_forAllCouplings_of_bundles h)

end MatedCRTHarmonic.BundleSec4
