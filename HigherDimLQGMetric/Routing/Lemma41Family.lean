import HigherDimLQGMetric.Routing.Lemma41LocalMesh

/-! Assembly of finitely many routed edge pieces. -/

set_option autoImplicit false

noncomputable section

open Set Topology LQGMetric.MetricGeometry
open scoped ENNReal

namespace HigherDimLQGMetric

def lemma41_side {X V E : Type*} [DecidableEq V]
    (left right : E → V) (L R : E → Set X) (e : E) (v : V) : Set X :=
  if left e = v then L e else if right e = v then R e else ∅

theorem lemma41_side_left {X V E : Type*} [DecidableEq V]
    (left right : E → V) (L R : E → Set X) (e : E) :
    lemma41_side left right L R e (left e) = L e := by
  simp [lemma41_side]

theorem lemma41_side_right {X V E : Type*} [DecidableEq V]
    (left right : E → V) (L R : E → Set X)
    (hne : ∀ e, left e ≠ right e) (e : E) :
    lemma41_side left right L R e (right e) = R e := by
  simp [lemma41_side, hne e]

theorem lemma41_side_iUnion {X V E : Type*} [DecidableEq V]
    (left right : E → V) (L R : E → Set X)
    (hne : ∀ e, left e ≠ right e) (e : E) :
    (⋃ v, lemma41_side left right L R e v) = L e ∪ R e := by
  ext x
  constructor
  · intro hx
    obtain ⟨v, hv⟩ : ∃ v : V, x ∈ lemma41_side left right L R e v :=
      Set.mem_iUnion.mp hx
    by_cases hl : left e = v
    · exact Or.inl (by simpa [lemma41_side, hl] using hv)
    · by_cases hr : right e = v
      · exact Or.inr (by simpa [lemma41_side, hl, hr] using hv)
      · simp [lemma41_side, hl, hr] at hv
  · intro hx
    rcases hx with hxL | hxR
    · exact Set.mem_iUnion_of_mem (left e)
        (by simpa [lemma41_side] using hxL)
    · exact Set.mem_iUnion_of_mem (right e)
        (by simpa [lemma41_side, hne e] using hxR)

theorem lemma41_side_same_edge_disjoint {X V E : Type*} [DecidableEq V]
    (left right : E → V) (L R : E → Set X)
    (hLR : ∀ e, Disjoint (L e) (R e))
    (e : E) (v w : V) (hvw : v ≠ w) :
    Disjoint (lemma41_side left right L R e v)
      (lemma41_side left right L R e w) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  by_cases hvl : left e = v
  · have hxL : x ∈ L e := by simpa [lemma41_side, hvl] using hx
    by_cases hwl : left e = w
    · exact hvw (hvl.symm.trans hwl)
    · by_cases hwr : right e = w
      · have hyR : x ∈ R e := by simpa [lemma41_side, hwl, hwr] using hy
        exact Set.disjoint_left.mp (hLR e) hxL hyR
      · simp [lemma41_side, hwl, hwr] at hy
  · by_cases hvr : right e = v
    · have hxR : x ∈ R e := by simpa [lemma41_side, hvl, hvr] using hx
      by_cases hwl : left e = w
      · have hyL : x ∈ L e := by simpa [lemma41_side, hwl] using hy
        exact Set.disjoint_right.mp (hLR e) hxR hyL
      · by_cases hwr : right e = w
        · exact hvw (hvr.symm.trans hwr)
        · simp [lemma41_side, hwl, hwr] at hy
    · simp [lemma41_side, hvl, hvr] at hx

theorem lemma41_family_partition {X V E : Type*}
    [MetricSpace X] [Fintype V] [Fintype E] [DecidableEq V]
    (left right : E → V) (hne : ∀ e, left e ≠ right e)
    (p : V → X) (RegL RegR Box : E → Set X)
    (Cost : X → X → ℝ≥0∞) (a₁ c₃ : ℝ)
    (P : ∀ e, Lemma41LocalPiece (p (left e)) (p (right e))
      (RegL e) (RegR e) (Box e) Cost a₁ c₃)
    (hincident : ∀ v, ∃ e, v = left e ∨ v = right e)
    (hcross_diff : ∀ e f v w, e ≠ f → v ≠ w →
      Disjoint
        (lemma41_side left right (fun e => (P e).L) (fun e => (P e).R) e v)
        (lemma41_side left right (fun e => (P e).L) (fun e => (P e).R) f w))
    (hbox_side : ∀ e f v, e ≠ f →
      Disjoint (Box e)
        (lemma41_side left right (fun e => (P e).L) (fun e => (P e).R) f v)) :
    let S : E → V → Set X :=
      lemma41_side left right (fun e => (P e).L) (fun e => (P e).R)
    let C : V → Set X := fun v => ⋃ e, S e v
    (∀ v, IsCompact (C v) ∧ IsConnected (C v) ∧ p v ∈ C v) ∧
    (∀ v w, v ≠ w → Disjoint (C v) (C w)) ∧
    (⋃ e, (P e).K) \ (⋃ e, (P e).σ '' Ioo (0 : ℝ) 1) = ⋃ v, C v := by
  let S : E → V → Set X :=
    lemma41_side left right (fun e => (P e).L) (fun e => (P e).R)
  have hSc : ∀ e v, IsCompact (S e v) := by
    intro e v
    by_cases hl : left e = v
    · simpa [S, lemma41_side, hl] using (P e).Lcompact
    · by_cases hr : right e = v
      · simpa [S, lemma41_side, hl, hr] using (P e).Rcompact
      · simp [S, lemma41_side, hl, hr]
  have hSn : ∀ e v, (S e v).Nonempty → IsConnected (S e v) := by
    intro e v _
    by_cases hl : left e = v
    · simpa [S, lemma41_side, hl] using (P e).Lconnected
    · by_cases hr : right e = v
      · simpa [S, lemma41_side, hl, hr] using (P e).Rconnected
      · simp [S, lemma41_side, hl, hr] at *
  have hSp : ∀ e v, (S e v).Nonempty → p v ∈ S e v := by
    intro e v _
    by_cases hl : left e = v
    · simpa [S, lemma41_side, ← hl] using (P e).pLmem
    · by_cases hr : right e = v
      · subst v
        simpa [S, lemma41_side, hne e] using (P e).pRmem
      · simp [S, lemma41_side, hl, hr] at *
  have hvertex : ∀ v, ∃ e, p v ∈ S e v := by
    intro v
    obtain ⟨e, he⟩ := hincident v
    refine ⟨e, ?_⟩
    rcases he with he | he
    · subst v
      simpa [S, lemma41_side] using (P e).pLmem
    · subst v
      simpa [S, lemma41_side, hne e] using (P e).pRmem
  have hK : ∀ e, (P e).K \ ((P e).σ '' Ioo (0 : ℝ) 1) = ⋃ v, S e v := by
    intro e
    rw [(P e).cut_eq]
    exact (lemma41_side_iUnion left right (fun e => (P e).L)
      (fun e => (P e).R) hne e).symm
  have hcross : ∀ e f v w, v ≠ w → Disjoint (S e v) (S f w) := by
    intro e f v w hvw
    by_cases hef : e = f
    · subst f
      exact lemma41_side_same_edge_disjoint left right
        (fun e => (P e).L) (fun e => (P e).R)
        (fun e => (P e).LRdisjoint) e v w hvw
    · exact hcross_diff e f v w hef hvw
  have hMS : ∀ e f v, Disjoint ((P e).σ '' Ioo (0 : ℝ) 1) (S f v) := by
    intro e f v
    by_cases hef : e = f
    · subst f
      by_cases hl : left e = v
      · simpa [S, lemma41_side, hl] using (P e).mark_disjoint_left
      · by_cases hr : right e = v
        · simpa [S, lemma41_side, hl, hr] using (P e).mark_disjoint_right
        · simp [S, lemma41_side, hl, hr]
    · exact (hbox_side e f v hef).mono_left
        ((image_mono Ioo_subset_Icc_self).trans (P e).σbox)
  exact lemma41_finite_attachment_partition p (fun e => (P e).K)
    (fun e => (P e).σ '' Ioo (0 : ℝ) 1) S hSc hSn hSp hvertex hK hcross hMS

theorem lemma41_family_mark_contacts {X V E : Type*}
    [MetricSpace X] [Fintype E] [DecidableEq V]
    (left right : E → V) (p : V → X)
    (RegL RegR Box : E → Set X)
    (Cost : X → X → ℝ≥0∞) (a₁ c₃ : ℝ)
    (P : ∀ e, Lemma41LocalPiece (p (left e)) (p (right e))
      (RegL e) (RegR e) (Box e) Cost a₁ c₃)
    (hbox_side : ∀ e f v, e ≠ f →
      Disjoint (Box e)
        (lemma41_side left right (fun e => (P e).L) (fun e => (P e).R) f v)) :
    ∀ e v u, u ∈ Icc (0 : ℝ) 1 →
      (P e).σ u ∈ ⋃ f, lemma41_side left right
        (fun e => (P e).L) (fun e => (P e).R) f v →
      (u = 0 ∧ v = left e) ∨ (u = 1 ∧ v = right e) := by
  intro e v u hu hx
  obtain ⟨f, hf⟩ := Set.mem_iUnion.mp hx
  by_cases hef : e = f
  · subst f
    by_cases hl : left e = v
    · have hxL : (P e).σ u ∈ (P e).L := by
        simpa [lemma41_side, hl] using hf
      have hEq : (P e).σ u = (P e).σ 0 :=
        Set.mem_singleton_iff.mp
          ((P e).left_meets_mark_at_start ▸
            (show (P e).σ u ∈ (P e).L ∩ ((P e).σ '' Icc (0 : ℝ) 1) from
              ⟨hxL, ⟨u, hu, rfl⟩⟩))
      exact Or.inl ⟨(P e).σinjective hu (by norm_num) hEq, hl.symm⟩
    · by_cases hr : right e = v
      · have hxR : (P e).σ u ∈ (P e).R := by
          simpa [lemma41_side, hl, hr] using hf
        have hEq : (P e).σ u = (P e).σ 1 :=
          Set.mem_singleton_iff.mp
            ((P e).right_meets_mark_at_end ▸
              (show (P e).σ u ∈ (P e).R ∩ ((P e).σ '' Icc (0 : ℝ) 1) from
                ⟨hxR, ⟨u, hu, rfl⟩⟩))
        exact Or.inr ⟨(P e).σinjective hu (by norm_num) hEq, hr.symm⟩
      · simp [lemma41_side, hl, hr] at hf
  · have hxBox : (P e).σ u ∈ Box e :=
      (P e).σbox ⟨u, hu, rfl⟩
    exact False.elim (Set.disjoint_left.mp (hbox_side e f v hef) hxBox hf)

theorem lemma41_family_marks_disjoint {X V E : Type*}
    [MetricSpace X] [DecidableEq V]
    (left right : E → V) (p : V → X)
    (RegL RegR Box : E → Set X)
    (Cost : X → X → ℝ≥0∞) (a₁ c₃ : ℝ)
    (P : ∀ e, Lemma41LocalPiece (p (left e)) (p (right e))
      (RegL e) (RegR e) (Box e) Cost a₁ c₃)
    (hbox_box : ∀ e f, e ≠ f → Disjoint (Box e) (Box f))
    (e f : E) (hef : e ≠ f) :
    Disjoint ((P e).σ '' Icc (0 : ℝ) 1) ((P f).σ '' Icc (0 : ℝ) 1) :=
  (hbox_box e f hef).mono (P e).σbox (P f).σbox

theorem lemma41_family_graph_eq {X V E : Type*}
    [MetricSpace X] [Fintype V] [Fintype E] [DecidableEq V]
    (left right : E → V) (hne : ∀ e, left e ≠ right e)
    (p : V → X) (RegL RegR Box : E → Set X)
    (Cost : X → X → ℝ≥0∞) (a₁ c₃ : ℝ)
    (P : ∀ e, Lemma41LocalPiece (p (left e)) (p (right e))
      (RegL e) (RegR e) (Box e) Cost a₁ c₃) :
    (⋃ e, (P e).K) =
      (⋃ v, ⋃ e, lemma41_side left right
        (fun e => (P e).L) (fun e => (P e).R) e v) ∪
      (⋃ e, (P e).σ '' Icc (0 : ℝ) 1) := by
  let S : E → V → Set X :=
    lemma41_side left right (fun e => (P e).L) (fun e => (P e).R)
  ext x
  constructor
  · intro hx
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp hx
    rw [(P e).graph_eq] at he
    rcases he with (heL | heσ) | heR
    · exact Or.inl (Set.mem_iUnion_of_mem (left e)
        (Set.mem_iUnion_of_mem e (by simpa only [S, lemma41_side_left] using heL)))
    · exact Or.inr (Set.mem_iUnion_of_mem e heσ)
    · exact Or.inl (Set.mem_iUnion_of_mem (right e)
        (Set.mem_iUnion_of_mem e (by
          change x ∈ S e (right e)
          dsimp only [S]
          rw [lemma41_side_right left right (fun e => (P e).L)
            (fun e => (P e).R) hne e]
          exact heR)))
  · intro hx
    rcases hx with hxC | hxσ
    · obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hxC
      obtain ⟨e, he⟩ := Set.mem_iUnion.mp hv
      have hxside : x ∈ (P e).L ∪ (P e).R := by
        rw [← lemma41_side_iUnion left right (fun e => (P e).L)
          (fun e => (P e).R) hne e]
        exact Set.mem_iUnion_of_mem v he
      rcases hxside with heL | heR
      · exact Set.mem_iUnion_of_mem e (by rw [(P e).graph_eq]; exact Or.inl (Or.inl heL))
      · exact Set.mem_iUnion_of_mem e (by rw [(P e).graph_eq]; exact Or.inr heR)
    · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hxσ
      exact Set.mem_iUnion_of_mem e ((P e).σK he)

end HigherDimLQGMetric
