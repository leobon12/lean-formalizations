import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.Topology.Bases

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-PSIEXT: a jointly measurable path functional depends on countably many coordinates

For the product σ-algebra on `(ι → ℝ) × Y` (`Y` a measurable space) and a measurable
`f : (ι → ℝ) × Y → Z` into a second-countable Hausdorff Borel space `Z`, there is a countable set
`S ⊆ ι` such that `f (x, y) = f (x', y)` for all `y` whenever `x` and `x'` agree on `S`
(`exists_countable_determined_fun`).

Use in G1-PSIEXT: the selected inverse uniformizers `Ψ left a` of `G1PsiSel` are jointly
measurable in `(a, z)`, so `Ψ left a` depends only on the values of the path `a` on a countable
set of times. This is what allows the a.e. statement over the path law `P.map (pathOf B)` (whose
null sets are only the measurable ones of the product σ-algebra, see G1PathNoGo.lean) to be
reduced to a statement about measurable sets of paths.

Standard fact of measure theory (every set of a product σ-algebra is determined by countably many
coordinates); no source consulted: **own elementary proof** (cost rule), by the good-sets principle.
-/

noncomputable section

open MeasureTheory Set

namespace QuantumZipper
namespace Thm18Asm
namespace G1RC

variable {ι : Type*} {Y : Type*} [MeasurableSpace Y]

/-- Every measurable subset of `(ι → ℝ) × Y` is determined by countably many path coordinates.
Own elementary proof: the sets with this property form a σ-algebra containing the generators. -/
theorem exists_countable_determined_prod {A : Set ((ι → ℝ) × Y)} (hA : MeasurableSet A) :
    ∃ S : Set ι, S.Countable ∧
      ∀ x x' : ι → ℝ, (∀ i ∈ S, x i = x' i) → ∀ y : Y, ((x, y) ∈ A ↔ (x', y) ∈ A) := by
  let Q : MeasurableSpace ((ι → ℝ) × Y) :=
    { MeasurableSet' := fun A => ∃ S : Set ι, S.Countable ∧
        ∀ x x' : ι → ℝ, (∀ i ∈ S, x i = x' i) → ∀ y : Y, ((x, y) ∈ A ↔ (x', y) ∈ A)
      measurableSet_empty := ⟨∅, Set.countable_empty, fun x x' _ y => by simp⟩
      measurableSet_compl := by
        rintro A ⟨S, hS, hdet⟩
        exact ⟨S, hS, fun x x' hxx y => by
          rw [mem_compl_iff, mem_compl_iff, hdet x x' hxx y]⟩
      measurableSet_iUnion := by
        intro f hf
        choose S hS hdet using hf
        refine ⟨⋃ n, S n, Set.countable_iUnion hS, fun x x' hxx y => ?_⟩
        rw [mem_iUnion, mem_iUnion]
        constructor
        · rintro ⟨n, hn⟩
          exact ⟨n, (hdet n x x' (fun j hj => hxx j (mem_iUnion.2 ⟨n, hj⟩)) y).1 hn⟩
        · rintro ⟨n, hn⟩
          exact ⟨n, (hdet n x x' (fun j hj => hxx j (mem_iUnion.2 ⟨n, hj⟩)) y).2 hn⟩ }
  have hle : (Prod.instMeasurableSpace : MeasurableSpace ((ι → ℝ) × Y)) ≤ Q := by
    change MeasurableSpace.comap Prod.fst (MeasurableSpace.pi : MeasurableSpace (ι → ℝ)) ⊔
      MeasurableSpace.comap Prod.snd ‹MeasurableSpace Y› ≤ Q
    refine sup_le ?_ ?_
    · rw [MeasurableSpace.comap_le_iff_le_map]
      change (⨆ i, (inferInstance : MeasurableSpace ℝ).comap (fun b : ι → ℝ => b i)) ≤ _
      refine iSup_le fun i => ?_
      rw [MeasurableSpace.comap_le_iff_le_map]
      intro s _
      exact ⟨{i}, Set.countable_singleton i, fun x x' hxx y => by
        simp only [mem_preimage, hxx i (mem_singleton i)]⟩
    · rw [MeasurableSpace.comap_le_iff_le_map]
      intro s _
      exact ⟨∅, Set.countable_empty, fun x x' _ y => Iff.rfl⟩
  exact hle A hA

/-- **A measurable functional of `(path, y)` depends on countably many path coordinates.**
Own elementary proof: apply `exists_countable_determined_prod` to the preimages of a countable
basis of `Z`, which separates points. -/
theorem exists_countable_determined_fun {Z : Type*} [TopologicalSpace Z]
    [SecondCountableTopology Z] [T2Space Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    {f : (ι → ℝ) × Y → Z} (hf : Measurable f) :
    ∃ S : Set ι, S.Countable ∧
      ∀ x x' : ι → ℝ, (∀ i ∈ S, x i = x' i) → ∀ y : Y, f (x, y) = f (x', y) := by
  obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis Z
  have hdet : ∀ u : b, ∃ S : Set ι, S.Countable ∧
      ∀ x x' : ι → ℝ, (∀ i ∈ S, x i = x' i) → ∀ y : Y,
        ((x, y) ∈ f ⁻¹' (u : Set Z) ↔ (x', y) ∈ f ⁻¹' (u : Set Z)) := fun u =>
    exists_countable_determined_prod (hf (hb.isOpen u.2).measurableSet)
  choose S hS hSdet using hdet
  have : Countable b := hbc.to_subtype
  refine ⟨⋃ u, S u, Set.countable_iUnion hS, fun x x' hxx y => ?_⟩
  by_contra hne
  obtain ⟨u, hub, hxu, hux⟩ := hb.mem_nhds_iff.1
    (isOpen_ne.mem_nhds (show f (x, y) ≠ f (x', y) from hne))
  have h := (hSdet ⟨u, hub⟩ x x' (fun i hi => hxx i (mem_iUnion.2 ⟨⟨u, hub⟩, hi⟩)) y).1 hxu
  exact hux h rfl

end G1RC
end Thm18Asm
end QuantumZipper
