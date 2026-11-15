/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GInstInverseMeas

/-! # Countable measurable localization of a free real collar -/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric Complex MeasureTheory

namespace InteractingSLE.Sec5.Aux61GInst

def collarRadius (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem collarRadius_pos (n : ℕ) : 0 < collarRadius n := by unfold collarRadius; positivity

/-- Both the collar radius and its distance from the old boundary are
bounded by fixed positive rational numbers on this history event. -/
def collarPiece {X : Type*} (E : Set X) (g : X → ℝ → ℝ) (n m : ℕ) : Set X :=
  E ∩ {x | ∀ a ∈ Icc (-collarRadius n) (collarRadius n), collarRadius m ≤ g x a}

/-- Uniform lower bounds on a compact interval are measurable for a
pointwise measurable family of continuous real functions. -/
theorem measurableSet_collarPiece {X : Type*} [MeasurableSpace X]
    {E : Set X} (hE : MeasurableSet E) {g : X → ℝ → ℝ}
    (hgm : ∀ a, Measurable (fun x => g x a)) (hgc : ∀ x ∈ E, Continuous (g x)) (n m : ℕ) :
    MeasurableSet (collarPiece E g n m) := by
  classical
  let J := Icc (-collarRadius n) (collarRadius n)
  haveI : CompactSpace J := isCompact_iff_compactSpace.1 isCompact_Icc
  let G : X → C(J, ℝ) := fun x => if hx : x ∈ E then
    ⟨fun a => g x a, (hgc x hx).comp continuous_subtype_val⟩ else 0
  have hG : Measurable G := ContinuousMap.measurable_iff_eval.2 fun a => by
    have hm : Measurable (fun x => if x ∈ E then g x a else 0) :=
      Measurable.ite hE (hgm a) measurable_const
    convert hm using 1
    funext x
    by_cases hx : x ∈ E <;> simp [G, hx]
  have hP : IsClosed {f : C(J, ℝ) | ∀ a : J, collarRadius m ≤ f a} := by
    have he : {f : C(J, ℝ) | ∀ a : J, collarRadius m ≤ f a} =
        ⋂ a : J, {f : C(J, ℝ) | collarRadius m ≤ f a} := by ext f; simp
    rw [he]
    exact isClosed_iInter fun a => isClosed_le continuous_const (continuous_eval_const a)
  have he : collarPiece E g n m = E ∩ G ⁻¹' {f : C(J, ℝ) | ∀ a : J, collarRadius m ≤ f a} := by
    ext x
    by_cases hx : x ∈ E
    · simp only [collarPiece, mem_inter_iff, mem_setOf_eq, mem_preimage, hx, true_and, G, dif_pos]
      exact ⟨fun h a => h a a.2, fun h a ha => h ⟨a, ha⟩⟩
    · simp [collarPiece, hx]
  rw [he]
  exact hE.inter (hP.measurableSet.preimage hG)

/-- Every history with a free collar belongs to one of the countably many
pieces; each piece carries a fixed radius and a uniform positive clearance. -/
theorem collarPieces_cover {X : Type*} {E : Set X} {g : X → ℝ → ℝ}
    (hgc : ∀ x ∈ E, Continuous (g x))
    (hgap : ∀ x ∈ E, ∃ δ > 0, ∀ a : ℝ, |a| < δ → 0 < g x a) :
    E = ⋃ p : ℕ × ℕ, collarPiece E g p.1 p.2 := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨δ, hδ, hfree⟩ := hgap x hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    have hnδ : collarRadius n < δ := hn
    have hn0 := collarRadius_pos n
    obtain ⟨a₀, ha₀, hmin⟩ := isCompact_Icc.exists_isMinOn
      (show (Icc (-collarRadius n) (collarRadius n)).Nonempty from
        ⟨0, neg_nonpos.2 hn0.le, hn0.le⟩) (hgc x hx).continuousOn
    have hapos : 0 < g x a₀ := hfree a₀ ((abs_le.2 ha₀).trans_lt hnδ)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hapos
    refine mem_iUnion.2 ⟨(n, m), hx, fun a ha => ?_⟩
    exact hm.le.trans (hmin ha)
  · intro x hx
    obtain ⟨p, hp⟩ := mem_iUnion.1 hx
    exact hp.1

theorem positive_on_collarPiece {X : Type*} {E : Set X} {g : X → ℝ → ℝ}
    {n m : ℕ} {x : X} (hx : x ∈ collarPiece E g n m) {a : ℝ}
    (ha : |a| ≤ collarRadius n) : 0 < g x a :=
  (collarRadius_pos m).trans_le (hx.2 a (abs_le.1 ha))

end InteractingSLE.Sec5.Aux61GInst
