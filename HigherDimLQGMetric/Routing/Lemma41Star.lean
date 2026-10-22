import HigherDimLQGMetric.Routing.Lemma41Components

/-! Compact connected unions of finitely many attachments at one vertex. -/

set_option autoImplicit false

open Set Topology

namespace HigherDimLQGMetric

theorem lemma41_star_union {X E : Type*} [TopologicalSpace X] [Fintype E]
    (p : X) (A : E → Set X) (hc : ∀ e, IsCompact (A e))
    (hn : ∀ e, IsConnected (A e)) (hp : ∀ e, p ∈ A e) :
    IsCompact ({p} ∪ ⋃ e, A e) ∧ IsConnected ({p} ∪ ⋃ e, A e) := by
  let D : Option E → Set X := fun e => match e with
    | none => {p}
    | some e => A e
  have hDc : ∀ e, IsCompact (D e) := by
    intro e
    cases e with
    | none => exact isCompact_singleton
    | some e => exact hc e
  have hDn : ∀ e, IsConnected (D e) := by
    intro e
    cases e with
    | none => exact isConnected_singleton
    | some e => exact hn e
  have hDp : ∀ e, p ∈ D e := by
    intro e
    cases e with
    | none => exact mem_singleton p
    | some e => exact hp e
  have hconn : IsConnected (⋃ e, D e) := by
    apply IsConnected.iUnion_of_reflTransGen hDn
    intro e f
    exact Relation.ReflTransGen.single ⟨p, hDp e, hDp f⟩
  have heq : (⋃ e, D e) = {p} ∪ ⋃ e, A e := by
    ext x
    simp [D, Option.exists]
  rw [← heq]
  exact ⟨isCompact_iUnion hDc, hconn⟩

end HigherDimLQGMetric
