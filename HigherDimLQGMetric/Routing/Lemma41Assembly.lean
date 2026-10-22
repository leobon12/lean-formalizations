import HigherDimLQGMetric.Routing.Lemma41Marked

/-! Finite assembly of edge attachments after deletion of marked interiors. -/

set_option autoImplicit false

noncomputable section

open Set Topology

namespace HigherDimLQGMetric

theorem lemma41_finite_attachment_partition {X V E : Type*}
    [MetricSpace X] [Fintype V] [Fintype E]
    (p : V → X) (K M : E → Set X) (S : E → V → Set X)
    (hSc : ∀ e v, IsCompact (S e v))
    (hSn : ∀ e v, (S e v).Nonempty → IsConnected (S e v))
    (hSp : ∀ e v, (S e v).Nonempty → p v ∈ S e v)
    (hvertex : ∀ v, ∃ e, p v ∈ S e v)
    (hK : ∀ e, K e \ M e = ⋃ v, S e v)
    (hcross : ∀ e f v w, v ≠ w → Disjoint (S e v) (S f w))
    (hMS : ∀ e f v, Disjoint (M e) (S f v)) :
    let C : V → Set X := fun v => ⋃ e, S e v
    (∀ v, IsCompact (C v) ∧ IsConnected (C v) ∧ p v ∈ C v) ∧
    (∀ v w, v ≠ w → Disjoint (C v) (C w)) ∧
    (⋃ e, K e) \ (⋃ e, M e) = ⋃ v, C v := by
  let C : V → Set X := fun v => ⋃ e, S e v
  have hC : ∀ v, IsCompact (C v) ∧ IsConnected (C v) ∧ p v ∈ C v := by
    intro v
    let A : E → Set X := fun e => {p v} ∪ S e v
    have hAc : ∀ e, IsCompact (A e) := fun e => isCompact_singleton.union (hSc e v)
    have hAn : ∀ e, IsConnected (A e) := by
      intro e
      by_cases he : (S e v).Nonempty
      · exact IsConnected.union ⟨p v, by simp, hSp e v he⟩ isConnected_singleton (hSn e v he)
      · have hempty : S e v = ∅ := by simpa only [Set.not_nonempty_iff_eq_empty] using he
        simpa only [A, hempty, union_empty] using (isConnected_singleton : IsConnected ({p v} : Set X))
    have hAp : ∀ e, p v ∈ A e := fun _ => Or.inl (by simp)
    have hstar := lemma41_star_union (p v) A hAc hAn hAp
    have heq : {p v} ∪ ⋃ e, A e = C v := by
      ext x
      simp only [A, C, mem_union, mem_singleton_iff, mem_iUnion]
      constructor
      · rintro (rfl | ⟨e, (rfl | hx)⟩)
        · obtain ⟨e, he⟩ := hvertex v
          exact ⟨e, he⟩
        · obtain ⟨e', he'⟩ := hvertex v
          exact ⟨e', he'⟩
        · exact ⟨e, hx⟩
      · rintro ⟨e, he⟩
        exact Or.inr ⟨e, Or.inr he⟩
    rw [← heq]
    refine ⟨hstar.1, hstar.2, ?_⟩
    exact Or.inl (by simp)
  have hCdisj : ∀ v w, v ≠ w → Disjoint (C v) (C w) := by
    intro v w hvw
    apply Set.disjoint_left.mpr
    intro x hx hy
    obtain ⟨e, he⟩ : ∃ e : E, x ∈ S e v := Set.mem_iUnion.mp hx
    obtain ⟨f, hf⟩ : ∃ f : E, x ∈ S f w := Set.mem_iUnion.mp hy
    exact Set.disjoint_left.mp (hcross e f v w hvw) he hf
  have hsep : (⋃ e, K e) \ (⋃ e, M e) = ⋃ v, C v := by
    ext x
    constructor
    · rintro ⟨hxK, hxM⟩
      obtain ⟨e, he⟩ : ∃ e : E, x ∈ K e := Set.mem_iUnion.mp hxK
      have hxe : x ∈ K e \ M e := ⟨he, fun hm => hxM (Set.mem_iUnion_of_mem e hm)⟩
      obtain ⟨v, hv⟩ : ∃ v : V, x ∈ S e v := Set.mem_iUnion.mp ((hK e) ▸ hxe)
      exact Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨e, hv⟩⟩
    · intro hx
      obtain ⟨v, hv⟩ : ∃ v : V, x ∈ C v := Set.mem_iUnion.mp hx
      obtain ⟨e, he⟩ : ∃ e : E, x ∈ S e v := Set.mem_iUnion.mp hv
      have hxe : x ∈ K e \ M e := (hK e).symm ▸ Set.mem_iUnion_of_mem v he
      have hxKe : x ∈ K e := hxe.1
      refine ⟨Set.mem_iUnion_of_mem e hxKe, ?_⟩
      intro hxM
      obtain ⟨f, hf⟩ : ∃ f : E, x ∈ M f := Set.mem_iUnion.mp hxM
      exact Set.disjoint_left.mp (hMS f e v) hf he
  exact ⟨hC, hCdisj, hsep⟩

end HigherDimLQGMetric
