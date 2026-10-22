import HigherDimLQGContinuity.Network.Spec

/-! # Incidence combinatorics of the subdivided site tree -/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 400000

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

def networkAugStar {d : ℕ} (S : SiteData d) (v : S.Vertex) :
    Set (NetworkNode S)
  | Sum.inl w => w = v
  | Sum.inr (e, 0) => S.edgeLeft e = v
  | Sum.inr (e, 1) => S.edgeLeft e = v ∨ S.edgeRight e = v
  | Sum.inr (e, 2) => S.edgeRight e = v

def networkStrongStar {d : ℕ} (S : SiteData d)
    (T : Set (NetworkNode S)) (v : S.Vertex) :
    NetworkNode S → Prop
  | Sum.inl w => w = v
  | Sum.inr (e, 0) => S.edgeLeft e = v
  | Sum.inr (e, 1) =>
      (S.edgeLeft e = v ∧ Sum.inr (e, 0) ∈ T) ∨
        (S.edgeRight e = v ∧ Sum.inr (e, 2) ∈ T)
  | Sum.inr (e, 2) => S.edgeRight e = v

theorem networkStrongStar_subset_aug {d : ℕ} (S : SiteData d)
    (T : Set (NetworkNode S)) (v : S.Vertex) :
    {n | networkStrongStar S T v n} ⊆ networkAugStar S v := by
  intro n hn
  rcases n with w | ⟨e, i⟩
  · exact hn
  · fin_cases i <;> simp only [networkStrongStar] at hn ⊢
    · exact hn
    · exact hn.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
    · exact hn

theorem connected_forall_of_adj_closed {V : Type*} (G : SimpleGraph V)
    (T : Set V) (hT : (G.induce T).Connected)
    (P : V → Prop) (hstep : ∀ a b : V,
      a ∈ T → b ∈ T → G.Adj a b → P a → P b)
    {a : V} (ha : a ∈ T) (hPa : P a) :
    ∀ b ∈ T, P b := by
  intro b hb
  have walk_closed : ∀ {u w : T}, (G.induce T).Walk u w → P u.1 → P w.1 := by
    intro u w p
    induction p with
    | nil => intro h; exact h
    | @cons u z w hadj p ih =>
      intro hu
      exact ih (hstep u.1 z.1 u.2 z.2
        ((SimpleGraph.induce_adj).mp hadj) hu)
  obtain ⟨p⟩ := hT ⟨a, ha⟩ ⟨b, hb⟩
  exact walk_closed p hPa

theorem networkStrongStar_adj_closed {d : ℕ} (S : SiteData d)
    (T : Set (NetworkNode S))
    (hNo : ∀ e : S.Edge,
      ¬ (Sum.inr (e, (0 : Fin 3)) ∈ T ∧
        Sum.inr (e, (2 : Fin 3)) ∈ T))
    (v : S.Vertex) (a b : NetworkNode S)
    (ha : a ∈ T) (hb : b ∈ T)
    (hab : (SimpleGraph.fromRel (networkIncidence S)).Adj a b)
    (hstar : networkStrongStar S T v a) :
    networkStrongStar S T v b := by
  rw [SimpleGraph.fromRel_adj] at hab
  rcases a with u | ⟨e, i⟩
  · rcases b with w | ⟨f, j⟩
    · simp [networkIncidence] at hab
    · fin_cases j <;>
        simp_all [networkStrongStar, networkIncidence]
  · fin_cases i
    all_goals
      rcases b with w | ⟨f, j⟩
      · simp_all [networkStrongStar, networkIncidence]
      · fin_cases j <;>
          simp_all [networkStrongStar, networkIncidence]
        all_goals
          rcases hstar with hleft | hright
          · exact False.elim (hNo e.1 e.2 hleft.2 hb)
          · exact hright

/-- The incidence graph itself forces a connected set without opposite gates
to stay in one augmented vertex star. -/
theorem network_connected_subset_augStar {d : ℕ} (S : SiteData d)
    (T : Set (NetworkNode S))
    (hconn : ((SimpleGraph.fromRel (networkIncidence S)).induce T).Connected)
    (hNo : ∀ e : S.Edge,
      ¬ (Sum.inr (e, (0 : Fin 3)) ∈ T ∧
        Sum.inr (e, (2 : Fin 3)) ∈ T)) :
    ∃ v : S.Vertex, T ⊆ networkAugStar S v := by
  let G : SimpleGraph (NetworkNode S) := SimpleGraph.fromRel (networkIncidence S)
  have hstep (v : S.Vertex) :
      ∀ a b : NetworkNode S, a ∈ T → b ∈ T → G.Adj a b →
        networkStrongStar S T v a → networkStrongStar S T v b :=
    networkStrongStar_adj_closed S T hNo v
  have hfull (v : S.Vertex) (n : NetworkNode S)
      (hn : n ∈ T) (hstrong : networkStrongStar S T v n) :
      T ⊆ networkAugStar S v := by
    intro b hb
    have h := connected_forall_of_adj_closed G T hconn
      (networkStrongStar S T v) (hstep v) hn hstrong b hb
    exact networkStrongStar_subset_aug S T v h
  obtain ⟨n, hn⟩ := (Classical.choice hconn.nonempty : T)
  rcases n with w | ⟨e, i⟩
  · exact ⟨w, hfull w (Sum.inl w) hn rfl⟩
  · fin_cases i
    · exact ⟨S.edgeLeft e, hfull (S.edgeLeft e)
        (Sum.inr (e, 0)) hn rfl⟩
    · by_cases h0 : Sum.inr (e, (0 : Fin 3)) ∈ T
      · exact ⟨S.edgeLeft e, hfull (S.edgeLeft e)
          (Sum.inr (e, 1)) hn (Or.inl ⟨rfl, h0⟩)⟩
      by_cases h2 : Sum.inr (e, (2 : Fin 3)) ∈ T
      · exact ⟨S.edgeRight e, hfull (S.edgeRight e)
          (Sum.inr (e, 1)) hn (Or.inr ⟨rfl, h2⟩)⟩
      have hsingle : ∀ b ∈ T, b = Sum.inr (e, (1 : Fin 3)) := by
        apply connected_forall_of_adj_closed G T hconn
          (fun b => b = Sum.inr (e, (1 : Fin 3)))
          ?_ hn rfl
        intro a b ha hb hab haeq
        subst a
        rw [SimpleGraph.fromRel_adj] at hab
        rcases b with w | ⟨f, j⟩
        · simp [networkIncidence] at hab
        · fin_cases j <;> simp_all [networkIncidence]
      refine ⟨S.edgeLeft e, ?_⟩
      intro b hb
      rw [hsingle b hb]
      change S.edgeLeft e = S.edgeLeft e ∨ S.edgeRight e = S.edgeLeft e
      exact Or.inl rfl
    · exact ⟨S.edgeRight e, hfull (S.edgeRight e)
        (Sum.inr (e, 2)) hn rfl⟩

end HigherDimLQGContinuity
