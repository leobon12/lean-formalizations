import SLUMetricAPI2
import SupercriticalLQGUniqueness.Frozen.LSCMetricInternalSetDist
import SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions.Sep
import Mathlib.Topology.Connected.Basic

/-!
# Chain lemma J (SB2 D5) in reachability form

The joining argument of Lemma 4.1 (paper l. 446–461; SB2 Details D5) in a set-theoretic form.

*Nodes* are elements of an arbitrary type `ν`, each with a set `S u ⊆ ℂ`. A node is either *real* (its set is the
trace of a target curve, paid by its length) or *virtual* (its set is a bounded complementary component `U` of a
compact separator trace `K`, and costs nothing). Two nodes of a finite node set `N` are adjacent when their sets meet
(`L41Rel`); a *chain* from `B₀` to `B₁` inside `N` (`L41Chain`) is a pair of nodes, the first meeting `B₀`, the last
meeting `B₁`, joined by a path of adjacent nodes of `N`.

* `l41_surgery` removes one virtual node `v` (set `U`, separator node `j` with set `K`): every chain inside `N` gives
  a chain inside `N ∖ {v} ∪ {j}`. This is SB2 D5's step (cases A–D), phrased with reachable sets instead of first
  and last hitting times: a preconnected union of reachable node sets that contains a point outside `U` and meets
  `U` must meet `K` (`U` is a connected component of `Kᶜ`); a preconnected endpoint set `B` meeting `U` and not
  contained in `U` meets `K`.
* `l41_chain_remove_virtual` removes a finite set of virtual nodes, one at a time (D5's termination: the number of
  virtual labels decreases).
* `l41_reach_cost`: inside a node set of real nodes, the internal distance between points of two nodes joined by a
  path is at most the sum of the costs over the node set (each node is paid once; SB2 D5 "Conclusion").
* `l41_internalSetDist_le_of_chain`: the resulting bound on the internal set distance.

No length is ever assigned to a virtual node, as in the paper (l. 457–459).
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLFPPAS.Contraction

open SupercriticalLQGUniqueness

/-- Adjacency inside a finite node set `N`: both nodes belong to `N` and their sets meet. -/
def L41Rel {ν : Type*} (S : ν → Set ℂ) (N : Finset ν) (u v : ν) : Prop :=
  u ∈ N ∧ v ∈ N ∧ (S u ∩ S v).Nonempty

/-- A chain of adjacent nodes of `N` from a node meeting `B₀` to a node meeting `B₁`. -/
def L41Chain {ν : Type*} (S : ν → Set ℂ) (N : Finset ν) (B₀ B₁ : Set ℂ) : Prop :=
  ∃ a ∈ N, ∃ b ∈ N, (S a ∩ B₀).Nonempty ∧ (S b ∩ B₁).Nonempty ∧
    Relation.ReflTransGen (L41Rel S N) a b

theorem l41Rel_symm {ν : Type*} (S : ν → Set ℂ) (N : Finset ν) {u v : ν}
    (h : L41Rel S N u v) : L41Rel S N v u :=
  ⟨h.2.1, h.1, by rw [inter_comm]; exact h.2.2⟩

theorem l41_rtg_symm {ν : Type*} (S : ν → Set ℂ) (N : Finset ν) {a b : ν}
    (h : Relation.ReflTransGen (L41Rel S N) a b) : Relation.ReflTransGen (L41Rel S N) b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (l41Rel_symm S N hbc) ih

theorem l41_rtg_mono {ν : Type*} (S : ν → Set ℂ) {N N' : Finset ν} (hNN' : N ⊆ N') {a b : ν}
    (h : Relation.ReflTransGen (L41Rel S N) a b) : Relation.ReflTransGen (L41Rel S N') a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.tail ih ⟨hNN' hbc.1, hNN' hbc.2.1, hbc.2.2⟩

theorem l41_rtg_mem {ν : Type*} (S : ν → Set ℂ) (N : Finset ν) {a b : ν}
    (h : Relation.ReflTransGen (L41Rel S N) a b) (ha : a ∈ N) : b ∈ N := by
  induction h with
  | refl => exact ha
  | tail _ hbc _ => exact hbc.2.1

theorem l41_chain_mono {ν : Type*} (S : ν → Set ℂ) {N N' : Finset ν} {B₀ B₁ : Set ℂ}
    (hNN' : N ⊆ N') (hch : L41Chain S N B₀ B₁) : L41Chain S N' B₀ B₁ := by
  obtain ⟨a, ha, b, hb, haB, hbB, hab⟩ := hch
  exact ⟨a, hNN' ha, b, hNN' hb, haB, hbB, l41_rtg_mono S hNN' hab⟩

/-- A path from a node with property `P` to a node without it has a step leaving `P`. -/
theorem l41_rtg_escape {ν : Type*} {R : ν → ν → Prop} (P : ν → Prop) {a b : ν}
    (h : Relation.ReflTransGen R a b) (ha : P a) (hb : ¬ P b) : ∃ u v, P u ∧ ¬ P v ∧ R u v := by
  induction h with
  | refl => exact absurd ha hb
  | @tail c d _ hcd ih =>
      by_cases hc : P c
      · exact ⟨c, d, hc, hb, hcd⟩
      · exact ih hc

/-- After its last visit to its start, a path avoids the start: either the path is trivial, or it makes a first step
to some `p ≠ a` and continues inside `N ∖ {a}`. -/
theorem l41_rtg_split {ν : Type*} [DecidableEq ν] (S : ν → Set ℂ) (N : Finset ν) {a b : ν}
    (h : Relation.ReflTransGen (L41Rel S N) a b) :
    b = a ∨ ∃ p, p ≠ a ∧ L41Rel S N a p ∧ Relation.ReflTransGen (L41Rel S (N.erase a)) p b := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail c d _ hcd ih =>
      by_cases hda : d = a
      · exact Or.inl hda
      · by_cases hca : c = a
        · exact Or.inr ⟨d, hda, hca ▸ hcd, Relation.ReflTransGen.refl⟩
        · rcases ih with hca' | ⟨p, hpa, hap, hpc⟩
          · exact absurd hca' hca
          · refine Or.inr ⟨p, hpa, hap, Relation.ReflTransGen.tail hpc ?_⟩
            exact ⟨Finset.mem_erase.mpr ⟨hca, hcd.1⟩, Finset.mem_erase.mpr ⟨hda, hcd.2.1⟩, hcd.2.2⟩

/-- The sets of the nodes along a path lie in one preconnected set made of reachable node sets. -/
theorem l41_reach_hull {ν : Type*} (S : ν → Set ℂ) (N : Finset ν)
    (hS : ∀ u ∈ N, IsPreconnected (S u)) {a u : ν} (ha : a ∈ N)
    (h : Relation.ReflTransGen (L41Rel S N) a u) :
    ∃ Z : Set ℂ, IsPreconnected Z ∧ S a ⊆ Z ∧ S u ⊆ Z ∧
      ∀ z ∈ Z, ∃ v ∈ N, Relation.ReflTransGen (L41Rel S N) a v ∧ z ∈ S v := by
  induction h with
  | refl =>
      exact ⟨S a, hS a ha, subset_rfl, subset_rfl,
        fun z hz => ⟨a, ha, Relation.ReflTransGen.refl, hz⟩⟩
  | @tail b c hab hbc ih =>
      obtain ⟨Z, hZ, haZ, hbZ, hZr⟩ := ih
      obtain ⟨z₀, hz₀b, hz₀c⟩ := hbc.2.2
      refine ⟨Z ∪ S c, IsPreconnected.union' ⟨z₀, hbZ hz₀b, hz₀c⟩ hZ (hS c hbc.2.1),
        subset_union_of_subset_left haZ _, subset_union_right, ?_⟩
      intro z hz
      rcases hz with hz | hz
      · exact hZr z hz
      · exact ⟨c, hbc.2.1, Relation.ReflTransGen.tail hab hbc, hz⟩

/-- One half of the surgery (SB2 D5 cases A–D, start side). Let `v` be a virtual node with set `U = S v` and
separator node `j` with set `K = S j`, `U` a component of `Kᶜ` (hypothesis `hU`). For a path from `a` (meeting `B`)
to `b` inside `N`: either it can be rerouted inside `N ∖ {v}`, or some node of `N ∖ {v} ∪ {j}` meeting `B` reaches
`j` inside `N ∖ {v} ∪ {j}`. -/
theorem l41_left {ν : Type*} [DecidableEq ν] (S : ν → Set ℂ) (N : Finset ν) (v j : ν)
    (hS : ∀ u ∈ N, IsPreconnected (S u))
    (hU : ∀ Z : Set ℂ, IsPreconnected Z → Disjoint Z (S j) → (Z ∩ S v).Nonempty → Z ⊆ S v)
    {B : Set ℂ} (hB : IsPreconnected B) (hBU : ¬ B ⊆ S v)
    {a b : ν} (ha : a ∈ N) (hab : Relation.ReflTransGen (L41Rel S N) a b)
    (haB : (S a ∩ B).Nonempty) :
    (a ∈ N.erase v ∧ Relation.ReflTransGen (L41Rel S (N.erase v)) a b) ∨
      ∃ a' ∈ insert j (N.erase v), (S a' ∩ B).Nonempty ∧
        Relation.ReflTransGen (L41Rel S (insert j (N.erase v))) a' j := by
  obtain ⟨x₀, hx₀a, hx₀B⟩ := haB
  by_cases hx₀U : x₀ ∈ S v
  · -- the endpoint set meets `U` and is not contained in it, so it meets `K`
    right
    have hBK : ¬ Disjoint B (S j) := fun hdisj => hBU (hU B hB hdisj ⟨x₀, hx₀B, hx₀U⟩)
    obtain ⟨x, hxB, hxK⟩ := Set.not_disjoint_iff.mp hBK
    exact ⟨j, Finset.mem_insert_self _ _, ⟨x, hxK, hxB⟩, Relation.ReflTransGen.refl⟩
  · have hav : a ≠ v := by
      rintro rfl
      exact hx₀U hx₀a
    have haN' : a ∈ N.erase v := Finset.mem_erase.mpr ⟨hav, ha⟩
    by_cases hreach : Relation.ReflTransGen (L41Rel S (N.erase v)) a b
    · exact Or.inl ⟨haN', hreach⟩
    · right
      obtain ⟨u, w, hu, hw, huw⟩ :=
        l41_rtg_escape (fun x => Relation.ReflTransGen (L41Rel S (N.erase v)) a x) hab
          Relation.ReflTransGen.refl hreach
      have huN' : u ∈ N.erase v := l41_rtg_mem S _ hu haN'
      have hwv : w = v := by
        by_contra hne
        exact hw (Relation.ReflTransGen.tail hu
          ⟨huN', Finset.mem_erase.mpr ⟨hne, huw.2.1⟩, huw.2.2⟩)
      rw [hwv] at huw
      obtain ⟨Z, hZ, haZ, huZ, hZr⟩ := l41_reach_hull S (N.erase v)
        (fun x hx => hS x (Finset.mem_of_mem_erase hx)) haN' hu
      have hZK : ¬ Disjoint Z (S j) := by
        intro hdisj
        obtain ⟨y, hyu, hyv⟩ := huw.2.2
        exact hx₀U (hU Z hZ hdisj ⟨y, huZ hyu, hyv⟩ (haZ hx₀a))
      obtain ⟨z, hzZ, hzK⟩ := Set.not_disjoint_iff.mp hZK
      obtain ⟨y, hyN, hay, hzy⟩ := hZr z hzZ
      refine ⟨a, Finset.mem_insert_of_mem haN', ⟨x₀, hx₀a, hx₀B⟩, ?_⟩
      exact Relation.ReflTransGen.tail (l41_rtg_mono S (Finset.subset_insert j (N.erase v)) hay)
        ⟨Finset.mem_insert_of_mem hyN, Finset.mem_insert_self _ _, ⟨z, hzy, hzK⟩⟩

/-- **The surgery step of chain lemma J** (SB2 D5): a chain inside `N` gives a chain inside `N ∖ {v} ∪ {j}`, where
`v` is a virtual node whose set is a component of the complement of the set of the real node `j`. -/
theorem l41_surgery {ν : Type*} [DecidableEq ν] (S : ν → Set ℂ) (N : Finset ν) (v j : ν)
    (hS : ∀ u ∈ N, IsPreconnected (S u))
    (hU : ∀ Z : Set ℂ, IsPreconnected Z → Disjoint Z (S j) → (Z ∩ S v).Nonempty → Z ⊆ S v)
    {B₀ B₁ : Set ℂ} (hB₀ : IsPreconnected B₀) (hB₁ : IsPreconnected B₁)
    (hB₀U : ¬ B₀ ⊆ S v) (hB₁U : ¬ B₁ ⊆ S v) (hch : L41Chain S N B₀ B₁) :
    L41Chain S (insert j (N.erase v)) B₀ B₁ := by
  obtain ⟨a, ha, b, hb, haB, hbB, hab⟩ := hch
  have hsub : N.erase v ⊆ insert j (N.erase v) := Finset.subset_insert _ _
  rcases l41_left S N v j hS hU hB₀ hB₀U ha hab haB with ⟨haN', hab'⟩ | ⟨a', ha', ha'B, ha'j⟩
  · exact ⟨a, hsub haN', b, hsub (l41_rtg_mem S _ hab' haN'), haB, hbB, l41_rtg_mono S hsub hab'⟩
  · rcases l41_left S N v j hS hU hB₁ hB₁U hb (l41_rtg_symm S N hab) hbB with
      ⟨hbN', hba'⟩ | ⟨b', hb', hb'B, hb'j⟩
    · exact ⟨a, hsub (l41_rtg_mem S _ hba' hbN'), b, hsub hbN', haB, hbB,
        l41_rtg_mono S hsub (l41_rtg_symm S _ hba')⟩
    · exact ⟨a', ha', b', hb', ha'B, hb'B, ha'j.trans (l41_rtg_symm S _ hb'j)⟩

/-- **Chain lemma J, removal of all virtual nodes** (SB2 D5, termination): a chain inside `M ∪ V` gives a chain
inside `M ∪ jn(V)`, where every `v ∈ V` is a virtual node whose set is a component of the complement of the set of
its separator node `jn v`, not containing either endpoint set. -/
theorem l41_chain_remove_virtual {ν : Type*} [DecidableEq ν] (S : ν → Set ℂ) (jn : ν → ν)
    {B₀ B₁ : Set ℂ} (hB₀ : IsPreconnected B₀) (hB₁ : IsPreconnected B₁) (V : Finset ν) :
    (∀ v ∈ V, IsPreconnected (S v) ∧ IsPreconnected (S (jn v)) ∧
      (∀ Z : Set ℂ, IsPreconnected Z → Disjoint Z (S (jn v)) → (Z ∩ S v).Nonempty → Z ⊆ S v) ∧
      ¬ B₀ ⊆ S v ∧ ¬ B₁ ⊆ S v) →
    ∀ M : Finset ν, (∀ u ∈ M, IsPreconnected (S u)) → L41Chain S (M ∪ V) B₀ B₁ →
      L41Chain S (M ∪ V.image jn) B₀ B₁ := by
  induction V using Finset.induction_on with
  | empty =>
      intro _ M _ h
      simpa using h
  | insert v V hvV ih =>
      intro hV M hM hch
      have hv := hV v (Finset.mem_insert_self v V)
      have hV' : ∀ w ∈ V, IsPreconnected (S w) ∧ IsPreconnected (S (jn w)) ∧
          (∀ Z : Set ℂ, IsPreconnected Z → Disjoint Z (S (jn w)) → (Z ∩ S w).Nonempty →
            Z ⊆ S w) ∧ ¬ B₀ ⊆ S w ∧ ¬ B₁ ⊆ S w :=
        fun w hw => hV w (Finset.mem_insert_of_mem hw)
      have hS : ∀ u ∈ M ∪ insert v V, IsPreconnected (S u) := by
        intro u hu
        rcases Finset.mem_union.mp hu with hu | hu
        · exact hM u hu
        · rcases Finset.mem_insert.mp hu with rfl | hu
          · exact hv.1
          · exact (hV' u hu).1
      have h1 := l41_surgery S (M ∪ insert v V) v (jn v) hS hv.2.2.1 hB₀ hB₁ hv.2.2.2.1
        hv.2.2.2.2 hch
      have hsub : insert (jn v) ((M ∪ insert v V).erase v) ⊆ insert (jn v) M ∪ V := by
        intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu
        · exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
        · obtain ⟨huv, hu⟩ := Finset.mem_erase.mp hu
          rcases Finset.mem_union.mp hu with hu | hu
          · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hu)
          · rcases Finset.mem_insert.mp hu with rfl | hu
            · exact absurd rfl huv
            · exact Finset.mem_union_right _ hu
      have hM' : ∀ u ∈ insert (jn v) M, IsPreconnected (S u) := by
        intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu
        · exact hv.2.1
        · exact hM u hu
      have h3 := ih hV' (insert (jn v) M) hM' (l41_chain_mono S hsub h1)
      have hsub' : insert (jn v) M ∪ V.image jn ⊆ M ∪ (insert v V).image jn := by
        intro u hu
        rcases Finset.mem_union.mp hu with hu | hu
        · rcases Finset.mem_insert.mp hu with rfl | hu
          · exact Finset.mem_union_right _ (Finset.mem_image_of_mem jn (Finset.mem_insert_self _ _))
          · exact Finset.mem_union_left _ hu
        · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
          exact Finset.mem_union_right _ (Finset.mem_image_of_mem jn (Finset.mem_insert_of_mem hw))
      exact l41_chain_mono S hsub' h3

/-- **Payment along a path of real nodes** (SB2 D5, conclusion): if every node of `N` has its set in `W` and any two
of its points are within internal distance `c u`, then two points of nodes joined by a path inside `N` are within
`∑_{u ∈ N} c u`. Each node is paid once (strong induction on `N`, cutting the path after its last visit to the start
node). -/
theorem l41_reach_cost {ν : Type*} [DecidableEq ν] (D : LSCMetric) (W : Set ℂ) (S : ν → Set ℂ)
    (c : ν → ℝ≥0∞) (N : Finset ν) :
    (∀ u ∈ N, S u ⊆ W) →
    (∀ u ∈ N, ∀ x y : ℂ, ∀ (hx : x ∈ W) (hy : y ∈ W), x ∈ S u → y ∈ S u →
      D.internal W (⟨x, hx⟩, ⟨y, hy⟩) ≤ c u) →
    ∀ {a b : ν}, a ∈ N → Relation.ReflTransGen (L41Rel S N) a b →
    ∀ {x y : ℂ} (hx : x ∈ W) (hy : y ∈ W), x ∈ S a → y ∈ S b →
      D.internal W (⟨x, hx⟩, ⟨y, hy⟩) ≤ ∑ u ∈ N, c u := by
  induction N using Finset.strongInduction with
  | H N ih =>
    intro hSW hcost a b ha hab x y hx hy hxa hyb
    rcases l41_rtg_split S N hab with hba | ⟨p, hpa, hap, hpb⟩
    · rw [hba] at hyb
      exact (hcost a ha x y hx hy hxa hyb).trans
        (Finset.single_le_sum (fun _ _ => zero_le) ha)
    · obtain ⟨z, hza, hzp⟩ := hap.2.2
      have hzW : z ∈ W := hSW a ha hza
      have hpN' : p ∈ N.erase a := Finset.mem_erase.mpr ⟨hpa, hap.2.1⟩
      have h1 := hcost a ha x z hx hzW hxa hza
      have h2 := ih (N.erase a) (Finset.erase_ssubset ha)
        (fun u hu => hSW u (Finset.mem_of_mem_erase hu))
        (fun u hu => hcost u (Finset.mem_of_mem_erase hu)) hpN' hpb hzW hy hzp hyb
      calc D.internal W (⟨x, hx⟩, ⟨y, hy⟩)
          ≤ D.internal W (⟨x, hx⟩, ⟨z, hzW⟩) + D.internal W (⟨z, hzW⟩, ⟨y, hy⟩) :=
            (LSCMetric.isExtMetric_internal D W).2.2.2 _ _ _
        _ ≤ c a + ∑ u ∈ N.erase a, c u := add_le_add h1 h2
        _ = ∑ u ∈ N, c u := Finset.add_sum_erase N c ha

/-- A chain of real nodes bounds the internal set distance between its endpoint sets by the total cost. -/
theorem l41_internalSetDist_le_of_chain {ν : Type*} [DecidableEq ν] (D : LSCMetric) (W : Set ℂ)
    (S : ν → Set ℂ) (c : ν → ℝ≥0∞) (N : Finset ν) (hSW : ∀ u ∈ N, S u ⊆ W)
    (hcost : ∀ u ∈ N, ∀ x y : ℂ, ∀ (hx : x ∈ W) (hy : y ∈ W), x ∈ S u → y ∈ S u →
      D.internal W (⟨x, hx⟩, ⟨y, hy⟩) ≤ c u)
    {B₀ B₁ : Set ℂ} (hch : L41Chain S N B₀ B₁) :
    D.internalSetDist W {y | (y : ℂ) ∈ B₀} {y | (y : ℂ) ∈ B₁} ≤ ∑ u ∈ N, c u := by
  obtain ⟨a, ha, b, hb, ⟨x, hxa, hxB⟩, ⟨y, hyb, hyB⟩, hab⟩ := hch
  have hxW := hSW a ha hxa
  have hyW := hSW b hb hyb
  have h := l41_reach_cost D W S c N hSW hcost ha hab hxW hyW hxa hyb
  unfold LSCMetric.internalSetDist
  exact iInf₂_le_of_le ⟨x, hxW⟩ hxB (iInf₂_le_of_le ⟨y, hyW⟩ hyB h)

/-- Two points of the trace of a target curve inside `W` are within internal distance its length. -/
theorem l41_trace_internal_le (D : LSCMetric) {W : Set ℂ} {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : D.IsCurve γ a b) (hW : ∀ t ∈ Icc a b, γ t ∈ W) {x y : ℂ} (hx : x ∈ W) (hy : y ∈ W)
    (hxγ : x ∈ γ '' Icc a b) (hyγ : y ∈ γ '' Icc a b) :
    D.internal W (⟨x, hx⟩, ⟨y, hy⟩) ≤ D.len γ a b := by
  obtain ⟨s, hs, rfl⟩ := hxγ
  obtain ⟨t, ht, rfl⟩ := hyγ
  exact SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions.internal_le_len_of_mem D hγ hW hs ht
    hx hy

end SupercriticalLFPPAS.Contraction
