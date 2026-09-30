import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Sets in a product σ-algebra depend on countably many coordinates

Standard fact (cf. Dudley, *Real Analysis and Probability*, on countably
determined sets). Own elementary proof: the sets depending on countably many coordinates
form a σ-algebra containing the generators of `pi ⊗ β`.
-/

namespace QuantumZipper.Thm18Asm

/-- The σ-algebra of sets depending on countably many `ι`-coordinates. -/
@[instance_reducible] def countDepMS (ι β : Type*) : MeasurableSpace ((ι → ℝ) × β) where
  MeasurableSet' A := ∃ J : Set ι, J.Countable ∧ ∀ f g : ι → ℝ, (∀ j ∈ J, f j = g j) →
    ∀ b : β, ((f, b) ∈ A ↔ (g, b) ∈ A)
  measurableSet_empty := ⟨∅, Set.countable_empty, fun _ _ _ _ => Iff.rfl⟩
  measurableSet_compl A := by
    rintro ⟨J, hJ, h⟩
    exact ⟨J, hJ, fun f g hfg b => not_congr (h f g hfg b)⟩
  measurableSet_iUnion A := by
    intro hA
    choose J hJ h using hA
    refine ⟨⋃ n, J n, Set.countable_iUnion hJ, fun f g hfg b => ?_⟩
    simp only [Set.mem_iUnion]
    exact exists_congr fun n =>
      h n f g (fun j hj => hfg j (Set.mem_iUnion.2 ⟨n, hj⟩)) b

theorem exists_countable_dep {ι β : Type*} [MeasurableSpace β] {G : Set ((ι → ℝ) × β)}
    (hG : MeasurableSet G) :
    ∃ J : Set ι, J.Countable ∧ ∀ f g : ι → ℝ, (∀ j ∈ J, f j = g j) → ∀ b : β,
      ((f, b) ∈ G ↔ (g, b) ∈ G) := by
  have hle : (Prod.instMeasurableSpace : MeasurableSpace ((ι → ℝ) × β)) ≤ countDepMS ι β := by
    refine sup_le ?_ ?_
    · rw [MeasurableSpace.comap_le_iff_le_map]
      refine iSup_le fun i => ?_
      rw [MeasurableSpace.comap_le_iff_le_map]
      intro B _
      refine ⟨{i}, Set.countable_singleton i, fun f g hfg b => ?_⟩
      show f i ∈ B ↔ g i ∈ B
      rw [hfg i rfl]
    · rw [MeasurableSpace.comap_le_iff_le_map]
      intro B _
      exact ⟨∅, Set.countable_empty, fun _ _ _ _ => Iff.rfl⟩
  exact hle G hG

end QuantumZipper.Thm18Asm
