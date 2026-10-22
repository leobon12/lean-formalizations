import HigherDimLQGMetric.Routing.Lemma41Bridge

/-! Splitting a finite family of marked arcs at one interior point per arc. -/

set_option autoImplicit false

noncomputable section

open Set Topology

namespace HigherDimLQGMetric

def lemma41_cutSide {X V E : Type*} [DecidableEq V]
    (left right : E → V) (σ : E → ℝ → X) (r : E → ℝ) (e : E) (v : V) : Set X :=
  if left e = v then σ e '' Icc 0 (r e)
  else if right e = v then σ e '' Icc (r e) 1 else ∅

def lemma41_cutPiece {X V E : Type*} [DecidableEq V] [Fintype E]
    (C : V → Set X) (left right : E → V) (σ : E → ℝ → X)
    (r : E → ℝ) (v : V) : Set X :=
  C v ∪ ⋃ e, lemma41_cutSide left right σ r e v

theorem lemma41_cutSide_compact {X V E : Type*} [MetricSpace X] [DecidableEq V]
    (left right : E → V) (σ : E → ℝ → X) (r : E → ℝ)
    (hr : ∀ e, r e ∈ Icc (0 : ℝ) 1)
    (hσc : ∀ e, ContinuousOn (σ e) (Icc 0 1)) (e : E) (v : V) :
    IsCompact (lemma41_cutSide left right σ r e v) := by
  by_cases hl : left e = v
  · have hsub : Icc (0 : ℝ) (r e) ⊆ Icc 0 1 := Icc_subset_Icc le_rfl (hr e).2
    simpa only [lemma41_cutSide, ite_eq_left hl] using
      (isCompact_Icc.image_of_continuousOn ((hσc e).mono hsub))
  · by_cases hright : right e = v
    · have hsub : Icc (r e) (1 : ℝ) ⊆ Icc 0 1 := Icc_subset_Icc (hr e).1 le_rfl
      simpa [lemma41_cutSide, hl, hright] using
        (isCompact_Icc.image_of_continuousOn ((hσc e).mono hsub))
    · simp [lemma41_cutSide, hl, hright]

theorem lemma41_cutPiece_closed {X V E : Type*} [MetricSpace X]
    [DecidableEq V] [Fintype E]
    (C : V → Set X) (left right : E → V) (σ : E → ℝ → X)
    (r : E → ℝ) (hC : ∀ v, IsCompact (C v))
    (hr : ∀ e, r e ∈ Icc (0 : ℝ) 1)
    (hσc : ∀ e, ContinuousOn (σ e) (Icc 0 1)) (v : V) :
    IsClosed (lemma41_cutPiece C left right σ r v) := by
  apply IsCompact.isClosed
  exact (hC v).union (isCompact_iUnion fun e =>
    lemma41_cutSide_compact left right σ r hr hσc e v)

theorem lemma41_cutPiece_cover {X V E : Type*} [DecidableEq V] [Fintype E]
    (C : V → Set X) (left right : E → V) (σ : E → ℝ → X)
    (r : E → ℝ)
    (hne : ∀ e, left e ≠ right e) :
    (⋃ v, C v) ∪ (⋃ e, σ e '' Icc (0 : ℝ) 1) ⊆
      ⋃ v, lemma41_cutPiece C left right σ r v := by
  intro x hx
  rcases hx with hxC | hxσ
  · obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hxC
    exact Set.mem_iUnion_of_mem v (Or.inl hv)
  · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hxσ
    obtain ⟨u, hu, rfl⟩ := he
    rcases le_total u (r e) with hle | hge
    · refine Set.mem_iUnion_of_mem (left e) (Or.inr (Set.mem_iUnion_of_mem e ?_))
      simp only [lemma41_cutSide]
      exact ⟨u, ⟨hu.1, hle⟩, rfl⟩
    · refine Set.mem_iUnion_of_mem (right e) (Or.inr (Set.mem_iUnion_of_mem e ?_))
      simp [lemma41_cutSide, hne e]
      exact ⟨u, ⟨hge, hu.2⟩, rfl⟩

theorem lemma41_cutPiece_subset_star {X V E : Type*}
    [DecidableEq V] [Fintype E]
    (C Star : V → Set X) (left right : E → V) (σ : E → ℝ → X)
    (r : E → ℝ) (hr : ∀ e, r e ∈ Icc (0 : ℝ) 1)
    (hC : ∀ v, C v ⊆ Star v)
    (hσ : ∀ e, σ e '' Icc (0 : ℝ) 1 ⊆ Star (left e) ∩ Star (right e))
    (v : V) : lemma41_cutPiece C left right σ r v ⊆ Star v := by
  rintro x (hxC | hxS)
  · exact hC v hxC
  · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hxS
    by_cases hl : left e = v
    · have hx : x ∈ σ e '' Icc (0 : ℝ) 1 := by
        obtain ⟨u, hu, rfl⟩ : x ∈ σ e '' Icc 0 (r e) := by
          simpa only [lemma41_cutSide, ite_eq_left hl] using he
        exact ⟨u, ⟨hu.1, hu.2.trans (hr e).2⟩, rfl⟩
      exact hl ▸ (hσ e hx).1
    · by_cases hright : right e = v
      · have hx : x ∈ σ e '' Icc (0 : ℝ) 1 := by
          obtain ⟨u, hu, rfl⟩ : x ∈ σ e '' Icc (r e) 1 := by
            simpa [lemma41_cutSide, hl, hright] using he
          exact ⟨u, ⟨(hr e).1.trans hu.1, hu.2⟩, rfl⟩
        exact hright ▸ (hσ e hx).2
      · simp [lemma41_cutSide, hl, hright] at he

theorem lemma41_cutSide_mem {X V E : Type*} [DecidableEq V]
    (left right : E → V) (σ : E → ℝ → X) (r : E → ℝ)
    (hr : ∀ e, r e ∈ Icc (0 : ℝ) 1)
    (e : E) (v : V) {x : X}
    (hx : x ∈ lemma41_cutSide left right σ r e v) :
    ∃ u ∈ Icc (0 : ℝ) 1, σ e u = x ∧
      ((v = left e ∧ u ≤ r e) ∨ (v = right e ∧ r e ≤ u)) := by
  by_cases hl : left e = v
  · obtain ⟨u, hu, heq⟩ : x ∈ σ e '' Icc 0 (r e) := by
      simpa only [lemma41_cutSide, ite_eq_left hl] using hx
    exact ⟨u, ⟨hu.1, hu.2.trans (hr e).2⟩, heq, Or.inl ⟨hl.symm, hu.2⟩⟩
  · by_cases hright : right e = v
    · obtain ⟨u, hu, heq⟩ : x ∈ σ e '' Icc (r e) 1 := by
        simpa [lemma41_cutSide, hl, hright] using hx
      exact ⟨u, ⟨(hr e).1.trans hu.1, hu.2⟩, heq, Or.inr ⟨hright.symm, hu.1⟩⟩
    · simp [lemma41_cutSide, hl, hright] at hx

theorem lemma41_cut_C_side_disjoint {X V E : Type*} [DecidableEq V]
    (C : V → Set X) (left right : E → V) (σ : E → ℝ → X) (r : E → ℝ)
    (hr : ∀ e, r e ∈ Ioo (0 : ℝ) 1)
    (hσC : ∀ e v u, u ∈ Icc (0 : ℝ) 1 → σ e u ∈ C v →
      (u = 0 ∧ v = left e) ∨ (u = 1 ∧ v = right e))
    (e : E) (v w : V) (hvw : v ≠ w) :
    Disjoint (C v) (lemma41_cutSide left right σ r e w) := by
  apply Set.disjoint_left.mpr
  intro x hxC hxS
  have hr' : ∀ e, r e ∈ Icc (0 : ℝ) 1 := fun e => ⟨(hr e).1.le, (hr e).2.le⟩
  obtain ⟨u, hu, heq, hside⟩ := lemma41_cutSide_mem left right σ r hr' e w hxS
  rcases hσC e v u hu (heq ▸ hxC) with ⟨hu0, hvleft⟩ | ⟨hu1, hvright⟩
  · rcases hside with ⟨hwleft, _⟩ | ⟨_, hru⟩
    · exact hvw (hvleft.trans hwleft.symm)
    · linarith [(hr e).1]
  · rcases hside with ⟨_, hur⟩ | ⟨hwright, _⟩
    · linarith [(hr e).2]
    · exact hvw (hvright.trans hwright.symm)

theorem lemma41_cut_side_inter_subset_cut {X V E : Type*} [DecidableEq V]
    (left right : E → V) (σ : E → ℝ → X) (r : E → ℝ)
    (hr : ∀ e, r e ∈ Icc (0 : ℝ) 1)
    (hσi : ∀ e, InjOn (σ e) (Icc (0 : ℝ) 1))
    (hσσ : ∀ e f, e ≠ f →
      Disjoint (σ e '' Icc (0 : ℝ) 1) (σ f '' Icc (0 : ℝ) 1))
    (e f : E) (v w : V) (hvw : v ≠ w) :
    lemma41_cutSide left right σ r e v ∩ lemma41_cutSide left right σ r f w ⊆
      ⋃ g, {σ g (r g)} := by
  intro x hx
  obtain ⟨u, hu, heq, huSide⟩ := lemma41_cutSide_mem left right σ r hr e v hx.1
  obtain ⟨t, ht, heq', htSide⟩ := lemma41_cutSide_mem left right σ r hr f w hx.2
  by_cases hef : e = f
  · subst f
    have hut : u = t := hσi e hu ht (heq.trans heq'.symm)
    have hcut : u = r e := by
      rcases huSide with ⟨hv, hur⟩ | ⟨hv, hru⟩ <;>
        rcases htSide with ⟨hw, htr⟩ | ⟨hw, hrt⟩
      · exact False.elim (hvw (hv.trans hw.symm))
      · exact le_antisymm hur (hut ▸ hrt)
      · exact le_antisymm (hut ▸ htr) hru
      · exact False.elim (hvw (hv.trans hw.symm))
    exact Set.mem_iUnion_of_mem e (by simpa only [mem_singleton_iff, ← hcut] using heq.symm)
  · have hxE : x ∈ σ e '' Icc (0 : ℝ) 1 := ⟨u, hu, heq⟩
    have hxF : x ∈ σ f '' Icc (0 : ℝ) 1 := ⟨t, ht, heq'⟩
    exact False.elim (Set.disjoint_left.mp (hσσ e f hef) hxE hxF)

theorem lemma41_cutPiece_inter_subset_cut {X V E : Type*}
    [DecidableEq V] [Fintype E]
    (C : V → Set X) (left right : E → V) (σ : E → ℝ → X) (r : E → ℝ)
    (hr : ∀ e, r e ∈ Ioo (0 : ℝ) 1)
    (hCC : ∀ v w, v ≠ w → Disjoint (C v) (C w))
    (hσC : ∀ e v u, u ∈ Icc (0 : ℝ) 1 → σ e u ∈ C v →
      (u = 0 ∧ v = left e) ∨ (u = 1 ∧ v = right e))
    (hσi : ∀ e, InjOn (σ e) (Icc (0 : ℝ) 1))
    (hσσ : ∀ e f, e ≠ f →
      Disjoint (σ e '' Icc (0 : ℝ) 1) (σ f '' Icc (0 : ℝ) 1))
    (v w : V) (hvw : v ≠ w) :
    lemma41_cutPiece C left right σ r v ∩
      lemma41_cutPiece C left right σ r w ⊆ ⋃ e, {σ e (r e)} := by
  intro x hx
  rcases hx.1 with hxC | hxS <;> rcases hx.2 with hyC | hyS
  · exact False.elim (Set.disjoint_left.mp (hCC v w hvw) hxC hyC)
  · obtain ⟨f, hf⟩ := Set.mem_iUnion.mp hyS
    exact False.elim (Set.disjoint_left.mp
      (lemma41_cut_C_side_disjoint C left right σ r hr hσC f v w hvw) hxC hf)
  · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hxS
    exact False.elim (Set.disjoint_left.mp
      (lemma41_cut_C_side_disjoint C left right σ r hr hσC e w v hvw.symm) hyC he)
  · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hxS
    obtain ⟨f, hf⟩ := Set.mem_iUnion.mp hyS
    exact lemma41_cut_side_inter_subset_cut left right σ r
      (fun e => ⟨(hr e).1.le, (hr e).2.le⟩) hσi hσσ e f v w hvw ⟨he, hf⟩

theorem lemma41_path_avoiding_cuts_in_star {X V E : Type*}
    [MetricSpace X] [Fintype V] [DecidableEq V] [Fintype E]
    {x y : X} (P : Path x y)
    (C Star : V → Set X) (left right : E → V) (σ : E → ℝ → X)
    (r : E → ℝ) (hr : ∀ e, r e ∈ Ioo (0 : ℝ) 1)
    (hne : ∀ e, left e ≠ right e)
    (hCcompact : ∀ v, IsCompact (C v))
    (hCC : ∀ v w, v ≠ w → Disjoint (C v) (C w))
    (hσc : ∀ e, ContinuousOn (σ e) (Icc 0 1))
    (hσi : ∀ e, InjOn (σ e) (Icc (0 : ℝ) 1))
    (hσC : ∀ e v u, u ∈ Icc (0 : ℝ) 1 → σ e u ∈ C v →
      (u = 0 ∧ v = left e) ∨ (u = 1 ∧ v = right e))
    (hσσ : ∀ e f, e ≠ f →
      Disjoint (σ e '' Icc (0 : ℝ) 1) (σ f '' Icc (0 : ℝ) 1))
    (hCStar : ∀ v, C v ⊆ Star v)
    (hσStar : ∀ e, σ e '' Icc (0 : ℝ) 1 ⊆ Star (left e) ∩ Star (right e))
    (hPK : Set.range P ⊆ (⋃ v, C v) ∪ (⋃ e, σ e '' Icc (0 : ℝ) 1))
    (havoid : ∀ e, σ e (r e) ∉ Set.range P) :
    ∃ v, Set.range P ⊆ Star v := by
  let D : V → Set X := lemma41_cutPiece C left right σ r
  have hr' : ∀ e, r e ∈ Icc (0 : ℝ) 1 := fun e => ⟨(hr e).1.le, (hr e).2.le⟩
  have hclosed : ∀ v, IsClosed (D v) :=
    lemma41_cutPiece_closed C left right σ r hCcompact hr' hσc
  have hcover : Set.range P ⊆ ⋃ v, D v :=
    hPK.trans (lemma41_cutPiece_cover C left right σ r hne)
  have hdisj : ∀ v w, v ≠ w → Disjoint (Set.range P ∩ D v) (D w) := by
    intro v w hvw
    apply Set.disjoint_left.mpr
    intro z hzP hzW
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp
      (lemma41_cutPiece_inter_subset_cut C left right σ r hr hCC hσC hσi hσσ
        v w hvw ⟨hzP.2, hzW⟩)
    exact havoid e (he ▸ hzP.1)
  obtain ⟨v, hv⟩ := lemma41_path_in_one_closed_piece P D hclosed hcover hdisj
  exact ⟨v, hv.trans (lemma41_cutPiece_subset_star C Star left right σ r hr'
    hCStar hσStar v)⟩

theorem lemma41_missing_interior_point {X : Type*} [MetricSpace X]
    {x y : X} (P : Path x y) (σ : ℝ → X)
    (hσc : ContinuousOn σ (Icc 0 1))
    (hnot : ¬ σ '' Icc (0 : ℝ) 1 ⊆ Set.range P) :
    ∃ r ∈ Ioo (0 : ℝ) 1, σ r ∉ Set.range P := by
  by_contra h
  have hinside : σ '' Ioo (0 : ℝ) 1 ⊆ Set.range P := by
    rintro z ⟨r, hr, rfl⟩
    by_contra hz
    exact h ⟨r, hr, hz⟩
  have hclosure : σ '' Icc (0 : ℝ) 1 ⊆ closure (σ '' Ioo (0 : ℝ) 1) := by
    have hc : ContinuousOn σ (closure (Ioo (0 : ℝ) 1)) := by
      simpa only [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] using hσc
    simpa only [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] using hc.image_closure
  exact hnot (hclosure.trans (closure_minimal hinside
    (isCompact_range P.continuous).isClosed))

/-- A simple path between points farther apart than every star must contain a whole marked arc. -/
theorem lemma41_distant_path_contains_marked {X V E : Type*}
    [MetricSpace X] [Fintype V] [DecidableEq V] [Fintype E]
    {x y : X} (P : Path x y)
    (C Star : V → Set X) (left right : E → V) (σ : E → ℝ → X)
    (hne : ∀ e, left e ≠ right e)
    (hCcompact : ∀ v, IsCompact (C v))
    (hCC : ∀ v w, v ≠ w → Disjoint (C v) (C w))
    (hσc : ∀ e, ContinuousOn (σ e) (Icc 0 1))
    (hσi : ∀ e, InjOn (σ e) (Icc (0 : ℝ) 1))
    (hσC : ∀ e v u, u ∈ Icc (0 : ℝ) 1 → σ e u ∈ C v →
      (u = 0 ∧ v = left e) ∨ (u = 1 ∧ v = right e))
    (hσσ : ∀ e f, e ≠ f →
      Disjoint (σ e '' Icc (0 : ℝ) 1) (σ f '' Icc (0 : ℝ) 1))
    (hCStar : ∀ v, C v ⊆ Star v)
    (hσStar : ∀ e, σ e '' Icc (0 : ℝ) 1 ⊆ Star (left e) ∩ Star (right e))
    (hPK : Set.range P ⊆ (⋃ v, C v) ∪ (⋃ e, σ e '' Icc (0 : ℝ) 1))
    {b : ℝ} (hb : 0 < b)
    (hdiam : ∀ v, ∀ a ∈ Star v, ∀ c ∈ Star v, dist a c < b / 8)
    (hsep : b / 4 ≤ dist x y) :
    ∃ e, σ e '' Icc (0 : ℝ) 1 ⊆ Set.range P := by
  classical
  by_contra h
  have hnot : ∀ e, ¬ σ e '' Icc (0 : ℝ) 1 ⊆ Set.range P := by
    simpa only [not_exists] using h
  have hmiss : ∀ e, ∃ r ∈ Ioo (0 : ℝ) 1, σ e r ∉ Set.range P :=
    fun e => lemma41_missing_interior_point P (σ e) (hσc e) (hnot e)
  choose r hr hrmiss using hmiss
  obtain ⟨v, hv⟩ := lemma41_path_avoiding_cuts_in_star P C Star left right σ r hr
    hne hCcompact hCC hσc hσi hσC hσσ hCStar hσStar hPK hrmiss
  have hx : x ∈ Star v := hv ⟨0, P.source⟩
  have hy : y ∈ Star v := hv ⟨1, P.target⟩
  linarith [hdiam v x hx y hy]

end HigherDimLQGMetric
