/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.GFF.LocalSets.Prop38

/-!
# Proposition 3.8 per prime end: the random set of `A₁`-free components of a patch

Packet PROVE-T14-SB2FIN, ruling R84. The per-prime-end form of Proposition 3.8 compares `𝒞_{A₁ ∪ A₂}` with `𝒞_{A₂}`
on the components of `(ℍ ∖ A₂) ∩ B(c, 4R)` that `A₁` does not reach (a cusp of `A₂` at a point of `A₁ ∩ A₂`, seen
from the side where `A₁` is absent). This file provides the random domain of that argument,

  `compFree A₁ A₂ c R = {y ∈ U | the component of y in U misses rc(A₁)}`,  `U = (ℍ ∖ rc(A₂)) ∩ B(c, 4R)`,

(`rc` the relative closure in `ℍ`), its description by chains of closed rational balls (`disjoint_component_iff`: the
component of `y` in an open `U` misses `F` iff every chain of rational balls in `U` starting at `y` ends at a ball
missing `F`), and its joint measurability (`measurableSet_compFree`) — in particular, for fixed `y`, measurability with
respect to the hitting σ-algebras of `A₁` and `A₂` (`measurableSet_mem_compFree`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.FinRel

open LocalSets (ratBall relClosureH compDist)

/-! ### Chains of rational balls -/

/-- The open rational ball (the interior of `ratBall p`). -/
def ratOBall (p : ℕ × ℕ) : Set ℂ := ball (TopologicalSpace.denseSeq ℂ p.1) (1 / ((p.2 : ℝ) + 1))

theorem ratOBall_subset (p : ℕ × ℕ) : ratOBall p ⊆ ratBall p := ball_subset_closedBall

/-- Every point of an open set lies in an open rational ball whose closed ball is in the set. -/
theorem exists_ratBall_subset {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) :
    ∃ p : ℕ × ℕ, z ∈ ratOBall p ∧ ratBall p ⊆ U := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU z hz
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt (show 0 < ε / 2 by positivity)
  obtain ⟨k, hk⟩ := Metric.denseRange_iff.1 (TopologicalSpace.denseRange_denseSeq ℂ) z
    (1 / ((j : ℝ) + 1)) (by positivity)
  refine ⟨(k, j), ?_, fun w hw => hεU ?_⟩
  · show dist z (TopologicalSpace.denseSeq ℂ k) < _
    exact hk
  · rw [mem_ball]
    have h1 : dist w (TopologicalSpace.denseSeq ℂ k) ≤ 1 / ((j : ℝ) + 1) := hw
    have := dist_triangle w (TopologicalSpace.denseSeq ℂ k) z
    rw [dist_comm] at hk
    linarith

/-- The chain relation: consecutive closed rational balls meet. -/
def BallLink (p q : ℕ × ℕ) : Prop := (ratBall p ∩ ratBall q).Nonempty

/-- The union of a chain of closed rational balls is preconnected. -/
theorem isPreconnected_biUnion_chain : ∀ l : List (ℕ × ℕ), l.IsChain BallLink →
    IsPreconnected (⋃ p ∈ l, ratBall p)
  | [], _ => by simp only [List.not_mem_nil, iUnion_of_empty, iUnion_empty]; exact isPreconnected_empty
  | [p], _ => by
    have e : (⋃ r ∈ [p], ratBall r) = ratBall p := by ext; simp
    rw [e]
    exact isPreconnected_closedBall
  | p :: q :: t, h => by
    rw [List.isChain_cons_cons] at h
    have e : (⋃ r ∈ p :: q :: t, ratBall r) = ratBall p ∪ ⋃ r ∈ q :: t, ratBall r := by
      ext z; simp only [List.mem_cons, mem_iUnion, mem_union, exists_prop]
      constructor
      · rintro ⟨r, hr | hr | hr, hz⟩
        · exact Or.inl (hr ▸ hz)
        · exact Or.inr ⟨r, Or.inl hr, hz⟩
        · exact Or.inr ⟨r, Or.inr hr, hz⟩
      · rintro (hz | ⟨r, hr, hz⟩)
        · exact ⟨p, Or.inl rfl, hz⟩
        · exact ⟨r, Or.inr hr, hz⟩
    rw [e]
    obtain ⟨w, hwp, hwq⟩ := h.1
    refine IsPreconnected.union' ⟨w, hwp, mem_biUnion (List.mem_cons_self) hwq⟩ isPreconnected_closedBall
      (isPreconnected_biUnion_chain (q :: t) h.2)

/-- A chain of closed rational balls inside `U` starting at `y`. -/
def IsBallChain (U : Set ℂ) (y : ℂ) (l : List (ℕ × ℕ)) : Prop :=
  (∀ p ∈ l, ratBall p ⊆ U) ∧ l.IsChain BallLink ∧ ∀ p ∈ l.head?, y ∈ ratBall p

/-- **Components through chains of rational balls**: for `U` open and `y ∈ U`, the component of `y` in `U` misses
`F` iff the last ball of every chain of rational balls in `U` starting at `y` misses `F`. -/
theorem disjoint_component_iff {U F : Set ℂ} (hU : IsOpen U) {y : ℂ} (hy : y ∈ U) :
    Disjoint (connectedComponentIn U y) F ↔
      ∀ l : List (ℕ × ℕ), IsBallChain U y l → ∀ p ∈ l.getLast?, Disjoint (ratBall p) F := by
  constructor
  · intro hd l ⟨hlU, hlc, hly⟩ p hp
    have hpl : p ∈ l := List.mem_of_getLast? hp
    obtain ⟨p₀, hp₀⟩ : ∃ p₀, l.head? = some p₀ := by
      cases l with
      | nil => simp at hpl
      | cons a t => exact ⟨a, rfl⟩
    have hp₀l : p₀ ∈ l := List.mem_of_mem_head? hp₀
    have hS := isPreconnected_biUnion_chain l hlc
    have hSU : (⋃ q ∈ l, ratBall q) ⊆ U := iUnion₂_subset fun q hq => hlU q hq
    have hyS : y ∈ ⋃ q ∈ l, ratBall q := mem_biUnion hp₀l (hly p₀ hp₀)
    have hsub := hS.subset_connectedComponentIn hyS hSU
    exact hd.mono_left (((subset_biUnion_of_mem (u := fun q => ratBall q) hpl) :
      ratBall p ⊆ ⋃ q ∈ l, ratBall q).trans hsub)
  · intro h
    -- the points reachable by chains
    set Rch : Set ℂ := {z | ∃ l : List (ℕ × ℕ), IsBallChain U y l ∧ ∃ p ∈ l.getLast?, z ∈ ratOBall p} with hRdef
    have hRo : IsOpen Rch := by
      rw [Metric.isOpen_iff]
      rintro z ⟨l, hl, p, hp, hz⟩
      obtain ⟨ε, hε, hεb⟩ := Metric.isOpen_iff.1 isOpen_ball z hz
      exact ⟨ε, hε, fun w hw => ⟨l, hl, p, hp, hεb hw⟩⟩
    have hRU : Rch ⊆ U := by
      rintro z ⟨l, hl, p, hp, hz⟩
      exact hl.1 p (List.mem_of_getLast? hp) (ratOBall_subset p hz)
    have hVo : IsOpen (U \ Rch) := by
      rw [Metric.isOpen_iff]
      intro z hz
      obtain ⟨q, hzq, hqU⟩ := exists_ratBall_subset hU hz.1
      obtain ⟨ε, hε, hεb⟩ := Metric.isOpen_iff.1 isOpen_ball z hzq
      refine ⟨ε, hε, fun w hw => ⟨hqU (ratOBall_subset q (hεb hw)), fun hwR => ?_⟩⟩
      obtain ⟨l, ⟨hlU, hlc, hly⟩, p, hp, hwp⟩ := hwR
      apply hz.2
      have hlne : l ≠ [] := List.ne_nil_of_mem (List.mem_of_getLast? hp)
      refine ⟨l ++ [q], ⟨fun r hr => ?_, ?_, fun r hr => ?_⟩, q, by simp, hzq⟩
      · rcases List.mem_append.1 hr with hr | hr
        · exact hlU r hr
        · rw [List.mem_singleton.1 hr]; exact hqU
      · rw [List.isChain_append]
        refine ⟨hlc, List.isChain_singleton q, fun a ha b hb => ?_⟩
        rw [hp] at ha
        cases ha
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
        subst hb
        exact ⟨w, ratOBall_subset _ hwp, ratOBall_subset _ (hεb hw)⟩
      · rw [List.head?_append_of_ne_nil _ hlne] at hr
        exact hly r hr
    have hyR : y ∈ Rch := by
      obtain ⟨q, hyq, hqU⟩ := exists_ratBall_subset hU hy
      exact ⟨[q], ⟨fun r hr => by rw [List.mem_singleton.1 hr]; exact hqU, List.isChain_singleton q,
        fun r hr => by
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hr
          exact hr ▸ ratOBall_subset q hyq⟩, q, by simp, hyq⟩
    have hsub : connectedComponentIn U y ⊆ Rch :=
      isPreconnected_connectedComponentIn.subset_left_of_subset_union hRo hVo disjoint_sdiff_right
        (fun z hz => by
          by_cases hzR : z ∈ Rch
          · exact Or.inl hzR
          · exact Or.inr ⟨connectedComponentIn_subset _ _ hz, hzR⟩)
        ⟨y, mem_connectedComponentIn hy, hyR⟩
    rw [Set.disjoint_left]
    intro z hz hzF
    obtain ⟨l, hl, p, hp, hzp⟩ := hsub hz
    exact Set.disjoint_left.1 (h l hl p hp) (ratOBall_subset p hzp) hzF

/-! ### The random domain of `A₁`-free components -/

/-- The patch domain `U = (ℍ ∖ rc(A₂)) ∩ B(c, 4R)`. -/
def patchDom (A₂ : Set ℂ) (c : ℂ) (R : ℝ) : Set ℂ := (H \ relClosureH A₂) ∩ ball c (4 * R)

theorem isOpen_patchDom (A₂ : Set ℂ) (c : ℂ) (R : ℝ) : IsOpen (patchDom A₂ c R) :=
  (LocalSets.isOpen_H_diff_relClosureH A₂).inter isOpen_ball

/-- **The `A₁`-free part of the patch**: the points of `U` whose component in `U` misses `rc(A₁)`. -/
def compFree (A₁ A₂ : Set ℂ) (c : ℂ) (R : ℝ) : Set ℂ :=
  {y | y ∈ patchDom A₂ c R ∧ Disjoint (connectedComponentIn (patchDom A₂ c R) y) (relClosureH A₁)}

theorem compFree_subset (A₁ A₂ : Set ℂ) (c : ℂ) (R : ℝ) : compFree A₁ A₂ c R ⊆ patchDom A₂ c R :=
  fun _ hy => hy.1

/-- Membership in the patch domain through the distance to the complement of `ℍ ∖ rc(A₂)`. -/
theorem mem_H_diff_relClosureH_iff (S : Set ℂ) (y : ℂ) : y ∈ H \ relClosureH S ↔ 0 < compDist S y := by
  have hc : IsClosed (H \ relClosureH S)ᶜ := (LocalSets.isOpen_H_diff_relClosureH S).isClosed_compl
  have hne : (H \ relClosureH S)ᶜ.Nonempty := ⟨-Complex.I, fun h => by
    have : (0 : ℝ) < (-Complex.I).im := h.1
    rw [Complex.neg_im, Complex.I_im] at this
    linarith⟩
  rw [compDist, ← hc.notMem_iff_infDist_pos hne, Set.notMem_compl_iff]

/-- The chain description of `compFree`. -/
theorem mem_compFree_iff {A₁ A₂ : Set ℂ} {c : ℂ} {R : ℝ} {y : ℂ} :
    y ∈ compFree A₁ A₂ c R ↔ y ∈ patchDom A₂ c R ∧
      ∀ l : List (ℕ × ℕ), (∀ p ∈ l, ratBall p ⊆ H ∩ ball c (4 * R)) → l.IsChain BallLink →
        (∀ p ∈ l, Disjoint (ratBall p) (relClosureH A₂)) → (∀ p ∈ l.head?, y ∈ ratBall p) →
          ∀ p ∈ l.getLast?, Disjoint (ratBall p) (relClosureH A₁) := by
  have hball : ∀ p, ratBall p ⊆ patchDom A₂ c R ↔
      ratBall p ⊆ H ∩ ball c (4 * R) ∧ Disjoint (ratBall p) (relClosureH A₂) := fun p => by
    constructor
    · intro hp
      exact ⟨fun z hz => ⟨(hp hz).1.1, (hp hz).2⟩, Set.disjoint_left.2 fun z hz h => (hp hz).1.2 h⟩
    · rintro ⟨h1, h2⟩ z hz
      exact ⟨⟨(h1 hz).1, Set.disjoint_left.1 h2 hz⟩, (h1 hz).2⟩
  constructor
  · rintro ⟨hy, hd⟩
    refine ⟨hy, fun l hl hlc hl2 hly p hp => ?_⟩
    exact (disjoint_component_iff (isOpen_patchDom A₂ c R) hy).1 hd l
      ⟨fun q hq => (hball q).2 ⟨hl q hq, hl2 q hq⟩, hlc, hly⟩ p hp
  · rintro ⟨hy, h⟩
    refine ⟨hy, (disjoint_component_iff (isOpen_patchDom A₂ c R) hy).2 fun l ⟨hlU, hlc, hly⟩ p hp => ?_⟩
    exact h l (fun q hq => ((hball q).1 (hlU q hq)).1) hlc (fun q hq => ((hball q).1 (hlU q hq)).2) hly p hp

section Meas

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {A₁ A₂ : Ω → Set ℂ}

/-- The finite conjunction of avoidance events over a list of balls inside `ℍ` is measurable. -/
theorem measurableSet_forall_disjoint {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (l : List (ℕ × ℕ)) (hl : ∀ p ∈ l, ratBall p ⊆ H) :
    MeasurableSet {ω | ∀ p ∈ l, Disjoint (ratBall p) (relClosureH (A ω))} := by
  classical
  have e : {ω | ∀ p ∈ l, Disjoint (ratBall p) (relClosureH (A ω))} =
      ⋂ p : ℕ × ℕ, if p ∈ l then {ω | Disjoint (ratBall p) (relClosureH (A ω))} else univ := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter]
    constructor
    · intro h p
      split_ifs with hp
      · exact h p hp
      · exact mem_univ _
    · intro h p hp
      have := h p
      simp only [hp, ↓reduceIte] at this
      exact this
  rw [e]
  refine MeasurableSet.iInter fun p => ?_
  split_ifs with hp
  · exact hA (LocalSets.measurableSet_disjoint_relClosureH (isCompact_closedBall _ _) (hl p hp))
  · exact MeasurableSet.univ

/-- **Joint measurability of the `A₁`-free part of the patch.** -/
theorem measurableSet_compFree (hA₁ : Measurable[mΩ, hittingSigma] A₁)
    (hA₂ : Measurable[mΩ, hittingSigma] A₂) (c : ℂ) (R : ℝ) :
    MeasurableSet {p : Ω × ℂ | p.2 ∈ compFree (A₁ p.1) (A₂ p.1) c R} := by
  classical
  set T : List (ℕ × ℕ) → Set (Ω × ℂ) := fun l =>
    {q | (∀ p ∈ l, ratBall p ⊆ H ∩ ball c (4 * R)) → l.IsChain BallLink →
      (∀ p ∈ l, Disjoint (ratBall p) (relClosureH (A₂ q.1))) → (∀ p ∈ l.head?, q.2 ∈ ratBall p) →
        ∀ p ∈ l.getLast?, Disjoint (ratBall p) (relClosureH (A₁ q.1))} with hT
  have e : {p : Ω × ℂ | p.2 ∈ compFree (A₁ p.1) (A₂ p.1) c R} =
      ({q : Ω × ℂ | 0 < compDist (A₂ q.1) q.2} ∩ {q | q.2 ∈ ball c (4 * R)}) ∩ ⋂ l, T l := by
    ext q
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_compFree_iff, patchDom,
      ← mem_H_diff_relClosureH_iff, hT]
  rw [e]
  refine ((measurableSet_lt measurable_const (LocalSets.measurable_compDist hA₂)).inter
    (measurableSet_lt (measurable_snd.dist measurable_const) measurable_const)).inter
    (MeasurableSet.iInter fun l => ?_)
  by_cases hs : (∀ p ∈ l, ratBall p ⊆ H ∩ ball c (4 * R)) ∧ l.IsChain BallLink
  · have hlH : ∀ p ∈ l, ratBall p ⊆ H := fun p hp => (hs.1 p hp).trans inter_subset_left
    have eT : T l = (Prod.fst ⁻¹' {ω | ∀ p ∈ l, Disjoint (ratBall p) (relClosureH (A₂ ω))})ᶜ ∪
        (Prod.snd ⁻¹' {y | ∀ p ∈ l.head?, y ∈ ratBall p})ᶜ ∪
          Prod.fst ⁻¹' {ω | ∀ p ∈ l.getLast?, Disjoint (ratBall p) (relClosureH (A₁ ω))} := by
      ext q
      simp only [hT, mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage]
      constructor
      · intro h
        by_cases h2 : ∀ p ∈ l, Disjoint (ratBall p) (relClosureH (A₂ q.1))
        · by_cases h3 : ∀ p ∈ l.head?, q.2 ∈ ratBall p
          · exact Or.inr (h hs.1 hs.2 h2 h3)
          · exact Or.inl (Or.inr h3)
        · exact Or.inl (Or.inl h2)
      · rintro ((h | h) | h) _ _ h2 h3
        · exact absurd h2 h
        · exact absurd h3 h
        · exact h
    rw [eT]
    have hlast : MeasurableSet {ω | ∀ p ∈ l.getLast?, Disjoint (ratBall p) (relClosureH (A₁ ω))} := by
      cases hg : l.getLast? with
      | none => simp only [Option.not_mem_none, IsEmpty.forall_iff, implies_true, ofPred_true,
          MeasurableSet.univ]
      | some p =>
        have hpl : p ∈ l := List.mem_of_getLast? hg
        have e2 : {ω | ∀ q ∈ some p, Disjoint (ratBall q) (relClosureH (A₁ ω))} =
            {ω | Disjoint (ratBall p) (relClosureH (A₁ ω))} := by
          ext ω; simp only [Option.mem_def, Option.some.injEq, forall_eq', mem_ofPred_eq]
        rw [e2]
        exact hA₁ (LocalSets.measurableSet_disjoint_relClosureH (isCompact_closedBall _ _) (hlH p hpl))
    have hhead : MeasurableSet {y : ℂ | ∀ p ∈ l.head?, y ∈ ratBall p} := by
      cases l.head? with
      | none => simp only [Option.not_mem_none, IsEmpty.forall_iff, implies_true, ofPred_true,
          MeasurableSet.univ]
      | some p =>
        have e3 : {y : ℂ | ∀ q ∈ some p, y ∈ ratBall q} = ratBall p := by
          ext y; simp only [Option.mem_def, Option.some.injEq, forall_eq', mem_ofPred_eq]
        rw [e3]
        exact isClosed_closedBall.measurableSet
    exact (((measurableSet_forall_disjoint hA₂ l hlH).preimage measurable_fst).compl.union
      (hhead.preimage measurable_snd).compl).union (hlast.preimage measurable_fst)
  · have eT : T l = univ := by
      ext q
      simp only [hT, mem_ofPred_eq, mem_univ, iff_true]
      intro h1 h2
      exact absurd ⟨h1, h2⟩ hs
    rw [eT]
    exact MeasurableSet.univ

omit mΩ in
/-- **For a fixed point, membership in the `A₁`-free part is an event of the two hitting σ-algebras.** -/
theorem measurableSet_mem_compFree (A₁ A₂ : Ω → Set ℂ) (c : ℂ) (R : ℝ) (y : ℂ) :
    MeasurableSet[MeasurableSpace.comap A₁ hittingSigma ⊔ MeasurableSpace.comap A₂ hittingSigma]
      {ω | y ∈ compFree (A₁ ω) (A₂ ω) c R} := by
  have h1 : Measurable[MeasurableSpace.comap A₁ hittingSigma ⊔ MeasurableSpace.comap A₂ hittingSigma,
      hittingSigma] A₁ := (comap_measurable A₁).mono le_sup_left le_rfl
  have h2 : Measurable[MeasurableSpace.comap A₁ hittingSigma ⊔ MeasurableSpace.comap A₂ hittingSigma,
      hittingSigma] A₂ := (comap_measurable A₂).mono le_sup_right le_rfl
  have hS := @measurableSet_compFree Ω
    (MeasurableSpace.comap A₁ hittingSigma ⊔ MeasurableSpace.comap A₂ hittingSigma) A₁ A₂ h1 h2 c R
  exact (@measurable_prodMk_right Ω ℂ
    (MeasurableSpace.comap A₁ hittingSigma ⊔ MeasurableSpace.comap A₂ hittingSigma) _ y) hS

end Meas

end InteractingSLE.Theorem14.SB.FinRel
