import SupercriticalLQGUniqueness.B2.PfeWeyl.R68S1TCountable
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Data.Nat.Pairing

 








set_option autoImplicit false
noncomputable section

open Set Topology TopologicalSpace
open scoped Topology

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

private abbrev BoundedShift (N : ℕ) := {f : C(ℂ, ℝ) // ∀ z, |f z| ≤ (N : ℝ)}

private instance (N : ℕ) : Nonempty (BoundedShift N) :=
  ⟨⟨0, by intro z; simp⟩⟩

private instance (N : ℕ) : SecondCountableTopology (BoundedShift N) :=
  Subtype.secondCountableTopology _

private instance (N : ℕ) : SeparableSpace (BoundedShift N) :=
  TopologicalSpace.SecondCountableTopology.to_separableSpace

private def boundedShiftDenseSeq (N : ℕ) : ℕ → BoundedShift N :=
  Classical.choose (exists_dense_seq (BoundedShift N))

private theorem boundedShiftDenseSeq_dense (N : ℕ) :
    DenseRange (boundedShiftDenseSeq N) :=
  Classical.choose_spec (exists_dense_seq (BoundedShift N))

 

theorem exists_countable_boundedShift_family :
    ∃ (f : ℕ → C(ℂ, ℝ)) (M : ℕ → ℝ),
      (∀ j z, |f j z| ≤ M j) ∧
      ∀ (N : ℕ) (g : C(ℂ, ℝ)), (∀ z, |g z| ≤ (N : ℝ)) →
        ∀ U : Set C(ℂ, ℝ), IsOpen U → g ∈ U →
          ∃ j, M j = (N : ℝ) ∧ f j ∈ U := by
  let f : ℕ → C(ℂ, ℝ) := fun j =>
    (boundedShiftDenseSeq (Nat.unpair j).1 (Nat.unpair j).2).1
  let M : ℕ → ℝ := fun j => ((Nat.unpair j).1 : ℝ)
  refine ⟨f, M, ?_, ?_⟩
  · intro j z
    exact (boundedShiftDenseSeq (Nat.unpair j).1 (Nat.unpair j).2).2 z
  · intro N g hg U hU hgU
    let gN : BoundedShift N := ⟨g, hg⟩
    have hOpen : IsOpen ((Subtype.val : BoundedShift N → C(ℂ, ℝ)) ⁻¹' U) :=
      hU.preimage continuous_subtype_val
    obtain ⟨j, hj⟩ := (boundedShiftDenseSeq_dense N).exists_mem_open hOpen
      ⟨gN, hgU⟩
    refine ⟨Nat.pair N j, ?_, ?_⟩
    · simp only [M, Nat.unpair_pair]
    · change (boundedShiftDenseSeq (Nat.unpair (Nat.pair N j)).1
        (Nat.unpair (Nat.pair N j)).2).1 ∈ U
      rw [Nat.unpair_pair]
      exact hj

end SupercriticalLQGUniqueness.B2.PfeWeyl
