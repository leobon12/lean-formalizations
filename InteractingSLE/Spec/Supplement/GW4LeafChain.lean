/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4LeafOrder
import InteractingSLE.Spec.Supplement.GW1WalkChain

/-!
# GW1's reverse first visits along a chronological chain of arcs (deterministic)

Packet PROVE-T14-GW4REG. GW4's proof (p. 637) uses GW1's "strict reverse first-visit order" along each whole walk.
A walk is built chronologically (`GW1WalkChain.ArcHistory`): arcs appended at the current endpoint, then a proper
terminal ray. This file carries first-visit information through that construction, for one counterflow trace `γ`:

* `VHist γ x A q`: `ArcHistory` in which every appended arc is first visited in strict reverse order along itself
  (`ArcOrd`) and all its points after its start strictly before every point of the earlier history ("new before old",
  GW1 item 3: "Every point of `A_j \ {w_j}` has first counterflow visit strictly after `T_{w_j}`");
* `VHist.endpoint_min`: the current endpoint is first visited no later than any point of the history;
* `ChainRV`: the corresponding condition on a forward chain `(L, ρ)` (`GW1X.ChainOK`);
* **`exists_isProperCurve_of_chainRV`**: a chain with `ChainRV` has a proper parametrization with strict reverse first
  visits (`ReverseVisits`), the curve of `GW1X.exists_isProperCurve_of_chainOK`;
* **`VHist.complete`**: closing a history by a proper ray, new before old and in reverse order along itself, gives
  such a chain.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Theorem14

namespace GW4Leaf

open GW1X GW1WalkChain

/-- **Strict reverse first visits along an arc** `α` on `[0, 1]`, after its start. -/
def ArcOrd (γ α : ℝ≥0 → ℂ) : Prop :=
  ∀ s s' : ℝ≥0, 0 < s → s < s' → s' ≤ 1 → GB11.firstVisit γ (α s') < GB11.firstVisit γ (α s)

/-- **A chronological history with first-visit data**: `GW1WalkChain.ArcHistory` in which every appended arc is first
visited in strict reverse order along itself, and all its points after its start strictly before every point of the
earlier history. -/
inductive VHist (γ : ℝ≥0 → ℂ) (x : ℂ) : Set ℂ → ℂ → Prop
  | root : VHist γ x {x} x
  | append {A : Set ℂ} {q : ℂ} (past : VHist γ x A q) (α : ℝ≥0 → ℂ)
      (arc : IsArc α) (upper : ∀ t ∈ Iic (1 : ℝ≥0), 0 ≤ (α t).im)
      (start : α 0 = q) (meet : ∀ t ∈ Iic (1 : ℝ≥0), α t ∈ A → t = 0)
      (ord : ArcOrd γ α)
      (new : ∀ t : ℝ≥0, 0 < t → t ≤ 1 → ∀ p ∈ A, GB11.firstVisit γ (α t) < GB11.firstVisit γ p) :
      VHist γ x (A ∪ α '' Iic 1) (α 1)

theorem VHist.endpoint_mem {γ : ℝ≥0 → ℂ} {x q : ℂ} {A : Set ℂ} (h : VHist γ x A q) : q ∈ A := by
  cases h with
  | root => exact mem_singleton _
  | append _ α _ _ _ _ _ _ => exact Or.inr ⟨1, mem_Iic.2 le_rfl, rfl⟩

/-- **The current endpoint is first visited no later than any point of the history.** -/
theorem VHist.endpoint_min {γ : ℝ≥0 → ℂ} {x q : ℂ} {A : Set ℂ} (h : VHist γ x A q) :
    ∀ p ∈ A, GB11.firstVisit γ q ≤ GB11.firstVisit γ p := by
  induction h with
  | root => intro p hp; rw [mem_singleton_iff.1 hp]
  | @append A q past α hα hup hα0 hmeet hord hnew ih =>
    intro p hp
    rcases hp with hpA | ⟨t, ht, rfl⟩
    · exact (hnew 1 one_pos le_rfl p hpA).le
    · rcases eq_zero_or_pos t with rfl | htpos
      · rw [hα0]
        exact (hnew 1 one_pos le_rfl q past.endpoint_mem).le
      · rcases (mem_Iic.1 ht).lt_or_eq with ht1 | ht1
        · exact (hord t 1 htpos ht1 le_rfl).le
        · rw [ht1]

/-- **The forward condition on a chain**: each arc in strict reverse order along itself, and every later point of the
chain (other than its junction) first visited strictly before every point of the arc after its start. -/
def ChainRV (γ : ℝ≥0 → ℂ) : List (ℝ≥0 → ℂ) → (ℝ≥0 → ℂ) → Prop
  | [], ρ => ReverseVisits γ ρ
  | α :: L, ρ => ArcOrd γ α ∧
      (∀ s : ℝ≥0, 0 < s → s ≤ 1 → ∀ z ∈ chainSet L ρ, z ≠ chainStart L ρ →
        GB11.firstVisit γ z < GB11.firstVisit γ (α s)) ∧ ChainRV γ L ρ

/-- **Reverse first visits of an arc followed by a ray.** -/
theorem reverseVisits_concatArc {γ α ρ : ℝ≥0 → ℂ} (hord : ArcOrd γ α)
    (hcross : ∀ s : ℝ≥0, 0 < s → s ≤ 1 → ∀ t : ℝ≥0, 0 < t →
      GB11.firstVisit γ (ρ t) < GB11.firstVisit γ (α s))
    (hρ : ReverseVisits γ ρ) : ReverseVisits γ (concatArc α ρ) := by
  intro s s' hs hss
  unfold concatArc
  by_cases hs' : s' ≤ 1
  · have hs1 : s ≤ 1 := hss.le.trans hs'
    simp only [hs1, hs', ↓reduceIte]
    exact hord s s' hs hss hs'
  · by_cases hs1 : s ≤ 1
    · simp only [hs1, hs', ↓reduceIte]
      exact hcross s hs hs1 _ (tsub_pos_of_lt (not_le.1 hs'))
    · simp only [hs1, hs', ↓reduceIte]
      exact hρ _ _ (tsub_pos_of_lt (not_le.1 hs1)) (tsub_lt_tsub_right_of_le (not_le.1 hs1).le hss)

/-- **A chain with `ChainRV` has a proper parametrization with strict reverse first visits** (the curve of
`GW1X.exists_isProperCurve_of_chainOK`). -/
theorem exists_isProperCurve_of_chainRV {γ ρ : ℝ≥0 → ℂ} (hρ : Supp9B.IsProperCurve ρ) :
    ∀ {L : List (ℝ≥0 → ℂ)}, ChainOK L ρ → ChainRV γ L ρ →
      ∃ g : ℝ≥0 → ℂ, Supp9B.IsProperCurve g ∧ g 0 = chainStart L ρ ∧ range g = chainSet L ρ ∧
        ReverseVisits γ g
  | [], _, hR => ⟨ρ, hρ, rfl,
      by simp only [chainSet, List.not_mem_nil, iUnion_of_empty, iUnion_empty, empty_union], hR⟩
  | α :: L, ⟨hα, hαH, h1, hmeet, hL⟩, ⟨hord, hcross, hR⟩ => by
    obtain ⟨g, hg, hg0, hgR, hgV⟩ := exists_isProperCurve_of_chainRV hρ hL hR
    have h1' : α 1 = g 0 := h1.trans hg0.symm
    refine ⟨concatArc α g, isProperCurve_concatArc hα hαH hg h1' fun s hs t hst => hmeet s hs ?_,
      concatArc_zero α g, ?_, ?_⟩
    · rw [← hgR]; exact ⟨t, hst.symm⟩
    · rw [range_concatArc h1', hgR, chainSet_cons]
    · refine reverseVisits_concatArc hord (fun s hs hs1 t ht => ?_) hgV
      refine hcross s hs hs1 (g t) (hgR ▸ mem_range_self t) ?_
      rw [← hg0]
      exact fun he => (ne_of_gt ht) (hg.2.1 he)

/-- **Prepending a history to a chain** (`GW1WalkChain.ArcHistory.prepend` with first-visit data): a chain from the
current endpoint, meeting the history only there, all of whose other points are first visited before every point of
the history, gives a chain from the root with `ChainRV`. -/
theorem VHist.prepend {γ : ℝ≥0 → ℂ} {x q : ℂ} {A : Set ℂ} (h : VHist γ x A q)
    (L : List (ℝ≥0 → ℂ)) (ρ : ℝ≥0 → ℂ) (hL : ChainOK L ρ) (hR : ChainRV γ L ρ)
    (hstart : chainStart L ρ = q)
    (hmeet : ∀ z ∈ chainSet L ρ, z ∈ A → z = q)
    (hnew : ∀ z ∈ chainSet L ρ, z ≠ q → ∀ p ∈ A, GB11.firstVisit γ z < GB11.firstVisit γ p) :
    ∃ L' : List (ℝ≥0 → ℂ), ChainOK L' ρ ∧ ChainRV γ L' ρ ∧ chainStart L' ρ = x ∧
      chainSet L' ρ = A ∪ chainSet L ρ := by
  induction h generalizing L with
  | root =>
    refine ⟨L, hL, hR, hstart, ?_⟩
    symm
    apply union_eq_right.2
    intro z hz
    rw [mem_singleton_iff] at hz
    rw [hz, ← hstart]
    exact chainStart_mem L ρ
  | @append A q past α hα hupper hα0 hαmeet hord hαnew ih =>
    have hC : ChainOK (α :: L) ρ := by
      refine ⟨hα, hupper, hstart.symm, ?_, hL⟩
      intro t ht hmem
      apply hα.2 ht (mem_Iic.2 le_rfl)
      exact hmeet _ hmem (Or.inr ⟨t, ht, rfl⟩)
    have hRC : ChainRV γ (α :: L) ρ := by
      refine ⟨hord, fun s hs hs1 z hz hzs => ?_, hR⟩
      exact hnew z hz (hstart ▸ hzs) (α s) (Or.inr ⟨s, mem_Iic.2 hs1, rfl⟩)
    have hM : ∀ z ∈ chainSet (α :: L) ρ, z ∈ A → z = q := by
      intro z hz hA
      rw [chainSet_cons] at hz
      rcases hz with ⟨t, ht, rfl⟩ | hz
      · rw [hαmeet t ht hA, hα0]
      · have heq := hmeet z hz (Or.inl hA)
        have hbad : α 1 ∈ A := heq ▸ hA
        have := hαmeet 1 (mem_Iic.2 le_rfl) hbad
        exact False.elim (one_ne_zero this)
    have hN : ∀ z ∈ chainSet (α :: L) ρ, z ≠ q → ∀ p ∈ A,
        GB11.firstVisit γ z < GB11.firstVisit γ p := by
      intro z hz hzq p hp
      rw [chainSet_cons] at hz
      rcases hz with ⟨t, ht, rfl⟩ | hz
      · have ht0 : 0 < t := pos_iff_ne_zero.2 fun h0 => hzq (by rw [h0, hα0])
        exact hαnew t ht0 (mem_Iic.1 ht) p hp
      · by_cases hz1 : z = α 1
        · rw [hz1]
          exact hαnew 1 one_pos le_rfl p hp
        · exact hnew z hz hz1 p (Or.inl hp)
    obtain ⟨L', hL', hR', hs, hset⟩ := ih (α :: L) hC hRC hα0 hM hN
    refine ⟨L', hL', hR', hs, ?_⟩
    rw [hset, chainSet_cons, union_assoc]

/-- **Closing a history by a proper ray** with first-visit data gives a chain from the root with `ChainRV`. -/
theorem VHist.complete {γ : ℝ≥0 → ℂ} {x q : ℂ} {A : Set ℂ} (h : VHist γ x A q)
    {ρ : ℝ≥0 → ℂ} (hρ0 : ρ 0 = q)
    (hmeet : ∀ t, ρ t ∈ A → t = 0) (hρV : ReverseVisits γ ρ)
    (hρnew : ∀ t : ℝ≥0, 0 < t → ∀ p ∈ A, GB11.firstVisit γ (ρ t) < GB11.firstVisit γ p) :
    ∃ L : List (ℝ≥0 → ℂ), ChainOK L ρ ∧ ChainRV γ L ρ ∧ chainStart L ρ = x ∧
      chainSet L ρ = A ∪ range ρ := by
  have hset : chainSet [] ρ = range ρ := by
    simp only [chainSet, List.not_mem_nil, iUnion_of_empty, iUnion_empty, empty_union]
  obtain ⟨L, hL, hR, hs, hS⟩ := h.prepend [] ρ trivial hρV hρ0
    (by
      intro z hz hA
      rw [hset] at hz
      obtain ⟨t, rfl⟩ := hz
      rw [hmeet t hA, hρ0])
    (by
      intro z hz hzq p hp
      rw [hset] at hz
      obtain ⟨t, rfl⟩ := hz
      have ht : 0 < t := pos_iff_ne_zero.2 fun h0 => hzq (by rw [h0, hρ0])
      exact hρnew t ht p hp)
  exact ⟨L, hL, hR, hs, hS.trans (by rw [hset])⟩

/-- **A closed history has a proper parametrization with strict reverse first visits.** -/
theorem VHist.exists_reverseVisits {γ : ℝ≥0 → ℂ} {x q : ℂ} {A : Set ℂ} (h : VHist γ x A q)
    {ρ : ℝ≥0 → ℂ} (hρ : Supp9B.IsProperCurve ρ) (hρ0 : ρ 0 = q)
    (hmeet : ∀ t, ρ t ∈ A → t = 0) (hρV : ReverseVisits γ ρ)
    (hρnew : ∀ t : ℝ≥0, 0 < t → ∀ p ∈ A, GB11.firstVisit γ (ρ t) < GB11.firstVisit γ p) :
    ∃ g : ℝ≥0 → ℂ, Supp9B.IsProperCurve g ∧ g 0 = x ∧ range g = A ∪ range ρ ∧ ReverseVisits γ g := by
  obtain ⟨L, hL, hR, hs, hS⟩ := h.complete hρ0 hmeet hρV hρnew
  obtain ⟨g, hg, hg0, hgR, hgV⟩ := exists_isProperCurve_of_chainRV hρ hL hR
  exact ⟨g, hg, hg0.trans hs, hgR.trans hS, hgV⟩

end GW4Leaf

end Theorem14

end InteractingSLE
