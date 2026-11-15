/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR5Stages

/-!
# The nested stopped past retains exactly the initial record and all pieces
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

universe v

namespace InteractingSLE.Theorem14.GW2JDetR5

open Exist.StagedLaw

variable {S : Type v}

/-- Flatten the recursive past into the usual finite vector of records. -/
def flattenPast : (n : ℕ) → Past S n → S × (Fin n → RecData)
  | 0 => fun x => (x, Fin.elim0)
  | n + 1 => fun x => ((flattenPast n x.1).1,
      Fin.snoc (α := fun _ => RecData) (flattenPast n x.1).2 x.2)

/-- Reconstruct the nested past from its initial record and stopped pieces. -/
def nestPast : (n : ℕ) → S × (Fin n → RecData) → Past S n
  | 0 => Prod.fst
  | n + 1 => fun x => (nestPast n (x.1, Fin.init x.2), x.2 (Fin.last n))

theorem nestPast_flattenPast : ∀ n (x : Past S n),
    nestPast n (flattenPast n x) = x
  | 0, _ => rfl
  | n + 1, x => by
    change (nestPast n ((flattenPast n x.1).1,
      Fin.init (Fin.snoc (α := fun _ => RecData) (flattenPast n x.1).2 x.2)),
      Fin.snoc (α := fun _ => RecData) (flattenPast n x.1).2 x.2 (Fin.last n)) = x
    rw [Fin.init_snoc, Fin.snoc_last, Prod.eta, nestPast_flattenPast n x.1]
    cases x
    rfl

theorem flattenPast_nestPast : ∀ n (x : S × (Fin n → RecData)),
    flattenPast n (nestPast n x) = x
  | 0, x => by
    change (x.1, Fin.elim0) = x
    refine Prod.ext ?_ ?_
    · rfl
    · exact funext fun i => i.elim0
  | n + 1, x => by
    change ((flattenPast n (nestPast n (x.1, Fin.init x.2))).1,
      Fin.snoc (α := fun _ => RecData) (flattenPast n (nestPast n (x.1, Fin.init x.2))).2
        (x.2 (Fin.last n))) = x
    rw [flattenPast_nestPast n, Fin.snoc_init_self]

variable [MeasurableSpace S]

theorem measurable_flattenPast : ∀ n, Measurable (flattenPast (S := S) n)
  | 0 => measurable_id.prodMk measurable_const
  | n + 1 => by
    have h := (measurable_flattenPast n).comp
      (measurable_fst : Measurable fun x : Past S n × RecData => x.1)
    change Measurable fun x : Past S n × RecData =>
      ((flattenPast n x.1).1, Fin.snoc (α := fun _ => RecData) (flattenPast n x.1).2 x.2)
    refine (measurable_fst.comp h).prodMk (measurable_pi_iff.mpr fun i => ?_)
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using
        (measurable_snd : Measurable fun x : Past S n × RecData => x.2)
    · simp only [Fin.snoc_castSucc]
      exact (measurable_pi_apply j).comp (measurable_snd.comp h)

theorem measurable_nestPast : ∀ n, Measurable (nestPast (S := S) n)
  | 0 => measurable_fst
  | n + 1 => by
    change Measurable fun x : S × (Fin (n + 1) → RecData) =>
      (nestPast n (x.1, Fin.init x.2), x.2 (Fin.last n))
    exact ((measurable_nestPast n).comp
      (measurable_fst.prodMk (measurable_pi_iff.mpr fun i =>
        (measurable_pi_apply i.castSucc).comp measurable_snd))).prodMk
      ((measurable_pi_apply (Fin.last n)).comp measurable_snd)

/-- Replacing the recursive past by its finite record vector leaves the
conditioning sigma-algebra unchanged. -/
theorem comap_flattenPast {Ω : Type*} (n : ℕ) (p : Ω → Past S n) :
    MeasurableSpace.comap (fun ω => flattenPast n (p ω)) inferInstance =
      MeasurableSpace.comap p inferInstance := by
  apply le_antisymm
  · change MeasurableSpace.comap (flattenPast n ∘ p) _ ≤ _
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_flattenPast n).comap_le
  · have h := MeasurableSpace.comap_mono
      (g := fun ω => flattenPast n (p ω)) (measurable_nestPast n).comap_le
    simpa only [MeasurableSpace.comap_comp, Function.comp_def,
      nestPast_flattenPast] using h

end InteractingSLE.Theorem14.GW2JDetR5
