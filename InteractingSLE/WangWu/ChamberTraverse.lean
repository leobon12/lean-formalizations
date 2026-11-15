/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ChamberPocket
import InteractingSLE.Spec.Sec6.DrivingSimple

/-!
# The middle curve traverses each pocket between the outer curves

Packet PROVE-WW-B4. Wang–Wu (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), Lemma 4.22: "In
each component `C` between the outer two lines, the middle line traverses `C` from its opening point `x` to its
closing point `y`. … A simple intermediate arc cannot bypass `C` except by following an entire nontrivial boundary
subarc … The common-arc alternative is excluded by Lemma 4.21. Simplicity also shows that the times spent in `C`
form a single interval, with endpoints `x, y`." The specification's proof of Lemma 7.1 (p. 224) gives the same
argument in detail; we follow it.

Setting (in the disc, `IsOrderedTriple`): crosscuts `α` (lower wall), `μ` (middle), `β` (upper wall), with `μ`
avoiding the lower side of `α` and `β` avoiding the lower side of `μ`. A pocket is the inside `U` of
`α[a, b] ∪ β[j a, j b]` for a gap `(a, b)` of the contacts of `α` and `β` (`ChamberPocket.lean`).

* `IsOrderedTriple.exists_corner_times`: the corners `x = α a`, `y = α b` lie on `μ` ("every common point of the two
  outer curves belongs to `γ`"), at times `σ < τ` (contact order, Aux. lemma 93);
* `IsOrderedTriple.eventually_mem_closure_pocket`: "at any nonendpoint point of either boundary arc of `D`, a
  sufficiently small neighborhood meets the closed between-flank region only on the `D̄` side" — local connectivity of
  the side of the wall (Schoenflies), separation from the other wall and from the rest of the same wall;
* `IsOrderedTriple.notMem_closure_pocket_of_lt`, `…_of_gt`: "the assertion `γ(t) ∈ D̄` is locally constant in `t`
  away from `σ_D, τ_D` … Before `σ_D` and after `τ_D` it must be false";
* `IsOrderedTriple.traverse`: **the traversal** — if the contact times of `μ` with each wall have empty interior
  (Wang–Wu Lemma 4.21 / the specification's Lemma 6.13), then `μ([σ, τ]) ⊆ D̄`, `μ` is outside `D̄` at all other
  times, and the times in `(σ, τ]` at which `μ` is not in the open pocket have empty interior ("Every nonempty pocket
  is in fact visited … Distinct outer contact gaps have disjoint ordered parameter intervals").
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Complex Bornology

namespace InteractingSLE.WangWu

/-- A predicate that is locally constant within a preconnected set is constant on it. -/
theorem IsPreconnected.iff_of_eventually {I : Set ℝ} (hI : IsPreconnected I) {P : ℝ → Prop}
    (h : ∀ t ∈ I, ∀ᶠ t' in 𝓝[I] t, (P t' ↔ P t)) {t t' : ℝ} (ht : t ∈ I) (ht' : t' ∈ I) : P t ↔ P t' := by
  classical
  have hc : ContinuousOn (fun u => decide (P u)) I := by
    intro u hu
    refine (continuousWithinAt_const (b := decide (P u))).congr_of_eventuallyEq ?_ rfl
    filter_upwards [h u hu] with v hv
    simp only [hv]
  have := hI.constant hc ht ht'
  simpa using this

/-- Three ordered crosscuts: `μ` avoids the lower side of `α`, and `β` avoids the lower side of `μ`. -/
structure IsOrderedTriple (α μ β : ℝ → ℂ) : Prop where
  lower : IsDiscCrosscut α
  middle : IsDiscCrosscut μ
  upper : IsDiscCrosscut β
  lower_middle : Disjoint (crossRange μ) (crossSide α (-1))
  middle_upper : Disjoint (crossRange β) (crossSide μ (-1))

namespace IsOrderedTriple

variable {α μ β : ℝ → ℂ}

theorem lower_upper (h : IsOrderedTriple α μ β) : Disjoint (crossRange β) (crossSide α (-1)) :=
  h.middle_upper.mono_right (h.lower.crossSide_neg_subset_of_disjoint h.middle h.lower_middle)

theorem middle_upper' (h : IsOrderedTriple α μ β) : Disjoint (crossRange μ) (crossSide β 1) :=
  h.middle.disjoint_crossRange_crossSide_swap h.upper h.middle_upper

/-- A point of `μ` in the open disc off `α` lies in the upper side of `α`. -/
theorem mem_crossSide_lower (h : IsOrderedTriple α μ β) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hb : μ t ∈ ball (0 : ℂ) 1) (hα : μ t ∉ crossRange α) : μ t ∈ crossSide α 1 :=
  h.lower.mem_crossSide_one_of hb hα fun h' => Set.disjoint_left.1 h.lower_middle ⟨t, ht, rfl⟩ h'

/-- A point of `μ` in the open disc off `β` lies in the lower side of `β`. -/
theorem mem_crossSide_upper (h : IsOrderedTriple α μ β) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hb : μ t ∈ ball (0 : ℂ) 1) (hβ : μ t ∉ crossRange β) : μ t ∈ crossSide β (-1) :=
  h.upper.mem_crossSide_neg_of hb hβ fun h' => Set.disjoint_left.1 h.middle_upper' ⟨t, ht, rfl⟩ h'

/-- The corners of a pocket lie on the middle curve, in order. -/
theorem exists_corner_times (h : IsOrderedTriple α μ β) {a b : ℝ} (hg : IsContactGap α β a b) :
    ∃ σ ∈ Icc (0 : ℝ) 1, ∃ τ ∈ Icc (0 : ℝ) 1, σ < τ ∧ μ σ = α a ∧ μ τ = α b := by
  obtain ⟨haS, hbS, hab, -⟩ := hg
  have hcorner : ∀ {s : ℝ}, s ∈ Sec7.pocketContactSet α β → ∃ σ ∈ Icc (0 : ℝ) 1, μ σ = α s := by
    intro s hs
    obtain ⟨hs01, r, hr, hrs⟩ := hs
    obtain ⟨σ, hσ, hσs⟩ := IsDiscCrosscut.crossRange_inter_subset_of_between h.lower h.middle
      h.lower_middle h.middle_upper ⟨⟨s, hs01, rfl⟩, ⟨r, hr, hrs⟩⟩
    exact ⟨σ, hσ, hσs⟩
  obtain ⟨σ, hσ, hσa⟩ := hcorner haS
  obtain ⟨τ, hτ, hτb⟩ := hcorner hbS
  exact ⟨σ, hσ, τ, hτ, h.lower.lt_of_contact h.middle h.lower_middle haS.1 hbS.1 hσ hτ hσa.symm hτb.symm hab,
    hσa, hτb⟩

theorem alpha_notMem_upper {a b : ℝ} (hg : IsContactGap α β a b) {s : ℝ} (hs : s ∈ Ioo a b)
    (hs01 : s ∈ Icc (0 : ℝ) 1) : α s ∉ crossRange β := fun hβ => by
  obtain ⟨r, hr, hrs⟩ := hβ
  exact hg.2.2.2 s hs ⟨hs01, r, hr, hrs⟩

theorem beta_notMem_lower (h : IsOrderedTriple α μ β) {a b : ℝ} (hg : IsContactGap α β a b) {r : ℝ}
    (hr : r ∈ Ioo (contactMap α β a) (contactMap α β b)) (hr01 : r ∈ Icc (0 : ℝ) 1) : β r ∉ crossRange α := by
  obtain ⟨haS, hbS, -, hgap⟩ := hg
  have hmono := strictMonoOn_contactMap h.lower h.upper h.lower_upper
  rintro ⟨v, hv, hvq⟩
  have hvS : v ∈ Sec7.pocketContactSet α β := ⟨hv, r, hr01, hvq.symm⟩
  have hjv : contactMap α β v = r := contactMap_eq h.upper hr01 hvq
  rcases lt_trichotomy v a with h₁ | h₁ | h₁
  · have := hmono hvS haS h₁; rw [hjv] at this; linarith [hr.1]
  · rw [h₁] at hjv; linarith [hr.1]
  rcases lt_trichotomy v b with h₂ | h₂ | h₂
  · exact hgap v ⟨h₁, h₂⟩ hvS
  · rw [h₂] at hjv; linarith [hr.2]
  · have := hmono hbS hvS h₂; rw [hjv] at this; linarith [hr.2]

/-- **Near a non-corner boundary point of a pocket, the middle curve stays in the closed pocket.** -/
theorem eventually_mem_closure_pocket (h : IsOrderedTriple α μ β) {a b : ℝ} (hg : IsContactGap α β a b)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hfr : μ t ∈ pocketCurve α β a b) (hx : μ t ≠ α a) (hy : μ t ≠ α b) :
    ∀ᶠ t' in 𝓝[Icc 0 1] t, μ t' ∈ closure (jordanIn (pocketCurve α β a b)) := by
  obtain ⟨hJ, hUD, hUαβ, hUfr, w, hwU, hwc⟩ := pocket_props h.lower h.upper h.lower_upper hg
  have hUbet := pocket_subset_between h.lower h.upper h.lower_upper hg
  set U := jordanIn (pocketCurve α β a b) with hUdef
  set O := ball (0 : ℂ) 1 \ (crossRange α ∪ crossRange β) with hOdef
  have hcl : ∀ q ∈ pocketCurve α β a b, q ∈ closure U := fun q hq => by
    rw [closure_eq_self_union_frontier, hUfr]; exact Or.inr hq
  have hμt : Tendsto μ (𝓝[Icc 0 1] t) (𝓝 (μ t)) := h.middle.cont t ht
  obtain ⟨haS, hbS, hab, hgap⟩ := hg
  have hg' : IsContactGap α β a b := ⟨haS, hbS, hab, hgap⟩
  obtain ⟨hja, hjaβ⟩ := contactMap_mem h.upper haS
  obtain ⟨hjb, hjbβ⟩ := contactMap_mem h.upper hbS
  -- the component property of `U`
  have hcomp : ∀ {V : Set ℂ}, IsPreconnected V → V ⊆ O → (V ∩ U).Nonempty → V ⊆ U := by
    intro V hV hVO ⟨v, hvV, hvU⟩
    rw [← hwc, connectedComponentIn_eq (hwc ▸ hvU : v ∈ connectedComponentIn O w)]
    exact hV.subset_connectedComponentIn hvV hVO
  rcases hfr with ⟨s₁, hs₁, hμs⟩ | ⟨r₁, hr₁, hμr⟩
  · -- a boundary point on the lower wall
    have hs₁' : s₁ ∈ Ioo a b := ⟨lt_of_le_of_ne hs₁.1 fun h' => hx (by rw [← hμs, h']),
      lt_of_le_of_ne hs₁.2 fun h' => hy (by rw [← hμs, h'])⟩
    have hs₁01 : s₁ ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_lt haS.1.1 hs₁'.1, lt_of_lt_of_le hs₁'.2 hbS.1.2⟩
    have hpβ := alpha_notMem_upper hg' hs₁' (Ioo_subset_Icc_self hs₁01)
    have hpD := h.lower.mem_disc s₁ hs₁01
    set F := α '' (Icc 0 a ∪ Icc b 1) with hF
    have hFc : IsClosed F := ((isCompact_Icc.union isCompact_Icc).image_of_continuousOn
      (h.lower.cont.mono (union_subset (Icc_subset_Icc le_rfl haS.1.2)
        (Icc_subset_Icc hbS.1.1 le_rfl)))).isClosed
    have hpF : α s₁ ∉ F := by
      rintro ⟨s, hs, hss⟩
      have hs01 : s ∈ Icc (0 : ℝ) 1 := by
        rcases hs with hs | hs
        · exact ⟨hs.1, hs.2.trans haS.1.2⟩
        · exact ⟨hbS.1.1.trans hs.1, hs.2⟩
      have := h.lower.inj hs01 (Ioo_subset_Icc_self hs₁01) hss
      rcases hs with hs | hs
      · linarith [hs.2, hs₁'.1]
      · linarith [hs.1, hs₁'.2]
    obtain ⟨ε₁, hε₁, hε₁β⟩ :=
      Metric.isOpen_iff.1 h.upper.isCompact_crossRange.isClosed.isOpen_compl (α s₁) hpβ
    obtain ⟨ε₂, hε₂, hε₂D⟩ := Metric.isOpen_iff.1 isOpen_ball (α s₁) hpD
    obtain ⟨ε₃, hε₃, hε₃F⟩ := Metric.isOpen_iff.1 hFc.isOpen_compl (α s₁) hpF
    set ε := min (min ε₁ ε₂) ε₃
    have hε : 0 < ε := lt_min (lt_min hε₁ hε₂) hε₃
    obtain ⟨N, hN, hNε, hNc⟩ :=
      exists_mem_nhds_isPreconnected_inter_jordanIn h.lower.isJordanCurve_upper (α s₁) hε
    have hNb : ∀ v ∈ N, v ∈ ball (0 : ℂ) 1 ∧ v ∉ crossRange β ∧ v ∉ F := fun v hv => by
      have hv' := hNε hv
      refine ⟨hε₂D (ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _)) hv'),
        hε₁β (ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) hv'),
        hε₃F (ball_subset_ball (min_le_right _ _) hv')⟩
    have hVO : N ∩ crossSide α 1 ⊆ O := fun v ⟨hvN, hv1⟩ =>
      ⟨(hNb v hvN).1, fun h' => h'.elim (h.lower.crossSide_subset (Or.inl rfl) hv1).2 (hNb v hvN).2.1⟩
    have hVU : N ∩ crossSide α 1 ⊆ U := by
      refine hcomp hNc hVO ?_
      obtain ⟨v, hvN, hvU⟩ := mem_closure_iff_nhds.1 (hcl _ (Or.inl ⟨s₁, hs₁, rfl⟩)) N hN
      exact ⟨v, ⟨hvN, (hUbet hvU).1⟩, hvU⟩
    rw [hμs] at hN
    filter_upwards [hμt hN, self_mem_nhdsWithin] with t' ht'N ht'
    obtain ⟨hb, hβ', hF'⟩ := hNb _ ht'N
    by_cases hα' : μ t' ∈ crossRange α
    · obtain ⟨s, hs, hss⟩ := hα'
      refine hcl _ (Or.inl ⟨s, ⟨?_, ?_⟩, hss⟩)
      · by_contra h'; push Not at h'; exact hF' ⟨s, Or.inl ⟨hs.1, h'.le⟩, hss⟩
      · by_contra h'; push Not at h'; exact hF' ⟨s, Or.inr ⟨h'.le, hs.2⟩, hss⟩
    · exact subset_closure (hVU ⟨ht'N, h.mem_crossSide_lower ht' hb hα'⟩)
  · -- a boundary point on the upper wall
    have hr₁' : r₁ ∈ Ioo (contactMap α β a) (contactMap α β b) :=
      ⟨lt_of_le_of_ne hr₁.1 fun h' => hx (by rw [← hμr, ← h', hjaβ]),
        lt_of_le_of_ne hr₁.2 fun h' => hy (by rw [← hμr, h', hjbβ])⟩
    have hr₁01 : r₁ ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_lt hja.1 hr₁'.1, lt_of_lt_of_le hr₁'.2 hjb.2⟩
    have hpα := h.beta_notMem_lower hg' hr₁' (Ioo_subset_Icc_self hr₁01)
    have hpD := h.upper.mem_disc r₁ hr₁01
    set F := β '' (Icc 0 (contactMap α β a) ∪ Icc (contactMap α β b) 1) with hF
    have hFc : IsClosed F := ((isCompact_Icc.union isCompact_Icc).image_of_continuousOn
      (h.upper.cont.mono (union_subset (Icc_subset_Icc le_rfl hja.2)
        (Icc_subset_Icc hjb.1 le_rfl)))).isClosed
    have hpF : β r₁ ∉ F := by
      rintro ⟨r, hr, hrr⟩
      have hr01 : r ∈ Icc (0 : ℝ) 1 := by
        rcases hr with hr | hr
        · exact ⟨hr.1, hr.2.trans hja.2⟩
        · exact ⟨hjb.1.trans hr.1, hr.2⟩
      have := h.upper.inj hr01 (Ioo_subset_Icc_self hr₁01) hrr
      rcases hr with hr | hr
      · linarith [hr.2, hr₁'.1]
      · linarith [hr.1, hr₁'.2]
    obtain ⟨ε₁, hε₁, hε₁α⟩ :=
      Metric.isOpen_iff.1 h.lower.isCompact_crossRange.isClosed.isOpen_compl (β r₁) hpα
    obtain ⟨ε₂, hε₂, hε₂D⟩ := Metric.isOpen_iff.1 isOpen_ball (β r₁) hpD
    obtain ⟨ε₃, hε₃, hε₃F⟩ := Metric.isOpen_iff.1 hFc.isOpen_compl (β r₁) hpF
    set ε := min (min ε₁ ε₂) ε₃
    have hε : 0 < ε := lt_min (lt_min hε₁ hε₂) hε₃
    obtain ⟨N, hN, hNε, hNc⟩ :=
      exists_mem_nhds_isPreconnected_inter_jordanIn h.upper.isJordanCurve_lower (β r₁) hε
    have hNb : ∀ v ∈ N, v ∈ ball (0 : ℂ) 1 ∧ v ∉ crossRange α ∧ v ∉ F := fun v hv => by
      have hv' := hNε hv
      refine ⟨hε₂D (ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _)) hv'),
        hε₁α (ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) hv'),
        hε₃F (ball_subset_ball (min_le_right _ _) hv')⟩
    have hVO : N ∩ crossSide β (-1) ⊆ O := fun v ⟨hvN, hv1⟩ =>
      ⟨(hNb v hvN).1, fun h' => h'.elim (hNb v hvN).2.1 (h.upper.crossSide_subset (Or.inr rfl) hv1).2⟩
    have hVU : N ∩ crossSide β (-1) ⊆ U := by
      refine hcomp hNc hVO ?_
      obtain ⟨v, hvN, hvU⟩ := mem_closure_iff_nhds.1 (hcl _ (Or.inr ⟨r₁, hr₁, rfl⟩)) N hN
      exact ⟨v, ⟨hvN, (hUbet hvU).2⟩, hvU⟩
    rw [hμr] at hN
    filter_upwards [hμt hN, self_mem_nhdsWithin] with t' ht'N ht'
    obtain ⟨hb, hα', hF'⟩ := hNb _ ht'N
    by_cases hβ' : μ t' ∈ crossRange β
    · obtain ⟨r, hr, hrr⟩ := hβ'
      refine hcl _ (Or.inr ⟨r, ⟨?_, ?_⟩, hrr⟩)
      · by_contra h'; push Not at h'; exact hF' ⟨r, Or.inl ⟨hr.1, h'.le⟩, hrr⟩
      · by_contra h'; push Not at h'; exact hF' ⟨r, Or.inr ⟨h'.le, hr.2⟩, hrr⟩
    · exact subset_closure (hVU ⟨ht'N, h.mem_crossSide_upper ht' hb hβ'⟩)


/-- Away from the corners, "`μ t` is in the closed pocket" is locally constant in `t`. -/
theorem eventually_iff_mem_closure_pocket (h : IsOrderedTriple α μ β) {a b : ℝ} (hg : IsContactGap α β a b)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hx : μ t ≠ α a) (hy : μ t ≠ α b) :
    ∀ᶠ t' in 𝓝[Icc 0 1] t, (μ t' ∈ closure (jordanIn (pocketCurve α β a b)) ↔
      μ t ∈ closure (jordanIn (pocketCurve α β a b))) := by
  obtain ⟨hJ, -, -, hUfr, -⟩ := pocket_props h.lower h.upper h.lower_upper hg
  set U := jordanIn (pocketCurve α β a b)
  have hμt : Tendsto μ (𝓝[Icc 0 1] t) (𝓝 (μ t)) := h.middle.cont t ht
  by_cases hU : μ t ∈ U
  · filter_upwards [hμt ((isOpen_jordanIn hJ).mem_nhds hU)] with t' ht'
    exact iff_of_true (subset_closure ht') (subset_closure hU)
  by_cases hcl : μ t ∈ closure U
  · have hfr : μ t ∈ pocketCurve α β a b := by
      rw [← hUfr]; exact ⟨hcl, by rwa [(isOpen_jordanIn hJ).interior_eq]⟩
    filter_upwards [h.eventually_mem_closure_pocket hg ht hfr hx hy] with t' ht'
    exact iff_of_true ht' hcl
  · filter_upwards [hμt (isClosed_closure.isOpen_compl.mem_nhds hcl)] with t' ht'
    exact iff_of_false ht' hcl

/-- The closed pocket meets the unit circle at most at its corners. -/
theorem mem_closure_pocket_of_norm (h : IsOrderedTriple α μ β) {a b : ℝ} (hg : IsContactGap α β a b) {q : ℂ}
    (hq : q ∈ closure (jordanIn (pocketCurve α β a b))) (hn : ‖q‖ = 1) : q = α a ∨ q = α b := by
  obtain ⟨hJ, hUD, -, -, -⟩ := pocket_props h.lower h.upper h.lower_upper hg
  obtain ⟨haS, hbS, -, -⟩ := hg
  obtain ⟨hja, hjaβ⟩ := contactMap_mem h.upper haS
  obtain ⟨hjb, hjbβ⟩ := contactMap_mem h.upper hbS
  rw [closure_jordanIn hJ] at hq
  rcases hq with hq | ⟨s, hs, rfl⟩ | ⟨r, hr, rfl⟩
  · have := hUD hq; rw [mem_ball, dist_zero_right, hn] at this; exact absurd this (lt_irrefl 1)
  · have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨haS.1.1.trans hs.1, hs.2.trans hbS.1.2⟩
    rcases h.lower.eq_of_mem_crossRange_of_norm ⟨s, hs01, rfl⟩ hn with h' | h'
    · have hs0 : s = 0 := h.lower.inj hs01 ⟨le_rfl, zero_le_one⟩ (h'.trans h.lower.zero.symm)
      left; rw [hs0, le_antisymm (hs0 ▸ hs.1) haS.1.1]
    · have hs1 : s = 1 := h.lower.inj hs01 ⟨zero_le_one, le_rfl⟩ (h'.trans h.lower.one.symm)
      right; rw [hs1, le_antisymm hbS.1.2 (hs1 ▸ hs.2)]
  · have hr01 : r ∈ Icc (0 : ℝ) 1 := ⟨hja.1.trans hr.1, hr.2.trans hjb.2⟩
    rcases h.upper.eq_of_mem_crossRange_of_norm ⟨r, hr01, rfl⟩ hn with h' | h'
    · have hr0 : r = 0 := h.upper.inj hr01 ⟨le_rfl, zero_le_one⟩ (h'.trans h.upper.zero.symm)
      left; rw [← hjaβ, hr0, le_antisymm (hr0 ▸ hr.1) hja.1]
    · have hr1 : r = 1 := h.upper.inj hr01 ⟨zero_le_one, le_rfl⟩ (h'.trans h.upper.one.symm)
      right; rw [← hjbβ, hr1, le_antisymm hjb.2 (hr1 ▸ hr.2)]

/-- **Before its first corner time the middle curve is outside the closed pocket.** -/
theorem notMem_closure_pocket_of_lt (h : IsOrderedTriple α μ β) {a b : ℝ} (hg : IsContactGap α β a b)
    {σ τ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) (hτ : τ ∈ Icc (0 : ℝ) 1) (hστ : σ < τ) (hσa : μ σ = α a)
    (hτb : μ τ = α b) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (htσ : t < σ) :
    μ t ∉ closure (jordanIn (pocketCurve α β a b)) := by
  have hI : IsPreconnected (Ico (0 : ℝ) σ) := (convex_Ico 0 σ).isPreconnected
  have hIsub : Ico (0 : ℝ) σ ⊆ Icc 0 1 := fun u hu => ⟨hu.1, hu.2.le.trans hσ.2⟩
  have hloc : ∀ u ∈ Ico (0 : ℝ) σ, ∀ᶠ u' in 𝓝[Ico 0 σ] u,
      (μ u' ∈ closure (jordanIn (pocketCurve α β a b)) ↔ μ u ∈ closure (jordanIn (pocketCurve α β a b))) := by
    intro u hu
    refine nhdsWithin_mono _ hIsub (h.eventually_iff_mem_closure_pocket hg (hIsub hu) ?_ ?_)
    · rw [← hσa]; exact fun h' => (hu.2).ne (h.middle.inj (hIsub hu) hσ h')
    · rw [← hτb]; exact fun h' => (hu.2.trans hστ).ne (h.middle.inj (hIsub hu) hτ h')
  have h0 : (0 : ℝ) ∈ Ico (0 : ℝ) σ := ⟨le_rfl, ht.1.trans_lt htσ⟩
  rw [IsPreconnected.iff_of_eventually hI hloc ⟨ht.1, htσ⟩ h0, h.middle.zero]
  intro hcl
  rcases h.mem_closure_pocket_of_norm hg hcl (by simp) with h' | h'
  · rw [← hσa, ← h.middle.zero] at h'
    exact h0.2.ne (h.middle.inj ⟨le_rfl, zero_le_one⟩ hσ h')
  · rw [← hτb, ← h.middle.zero] at h'
    exact (h0.2.trans hστ).ne (h.middle.inj ⟨le_rfl, zero_le_one⟩ hτ h')

/-- **After its last corner time the middle curve is outside the closed pocket.** -/
theorem notMem_closure_pocket_of_gt (h : IsOrderedTriple α μ β) {a b : ℝ} (hg : IsContactGap α β a b)
    {σ τ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) (hτ : τ ∈ Icc (0 : ℝ) 1) (hστ : σ < τ) (hσa : μ σ = α a)
    (hτb : μ τ = α b) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (htτ : τ < t) :
    μ t ∉ closure (jordanIn (pocketCurve α β a b)) := by
  have hI : IsPreconnected (Ioc τ (1 : ℝ)) := (convex_Ioc τ 1).isPreconnected
  have hIsub : Ioc τ (1 : ℝ) ⊆ Icc 0 1 := fun u hu => ⟨hτ.1.trans hu.1.le, hu.2⟩
  have hloc : ∀ u ∈ Ioc τ (1 : ℝ), ∀ᶠ u' in 𝓝[Ioc τ 1] u,
      (μ u' ∈ closure (jordanIn (pocketCurve α β a b)) ↔ μ u ∈ closure (jordanIn (pocketCurve α β a b))) := by
    intro u hu
    refine nhdsWithin_mono _ hIsub (h.eventually_iff_mem_closure_pocket hg (hIsub hu) ?_ ?_)
    · rw [← hσa]; exact fun h' => (hστ.trans hu.1).ne' (h.middle.inj (hIsub hu) hσ h')
    · rw [← hτb]; exact fun h' => (hu.1).ne' (h.middle.inj (hIsub hu) hτ h')
  have h1 : (1 : ℝ) ∈ Ioc τ (1 : ℝ) := ⟨htτ.trans_le ht.2, le_rfl⟩
  rw [IsPreconnected.iff_of_eventually hI hloc ⟨htτ, ht.2⟩ h1, h.middle.one]
  intro hcl
  rcases h.mem_closure_pocket_of_norm hg hcl (by simp) with h' | h'
  · rw [← hσa, ← h.middle.one] at h'
    exact (hστ.trans h1.1).ne' (h.middle.inj ⟨zero_le_one, le_rfl⟩ hσ h')
  · rw [← hτb, ← h.middle.one] at h'
    exact h1.1.ne' (h.middle.inj ⟨zero_le_one, le_rfl⟩ hτ h')

/-- **Every pocket is visited, between its corner times** (specification, proof of Lemma 7.1: "Between its two
endpoint-hit times, the middle curve cannot lie entirely on the outer curves … It belongs to some between-component
`D'` … these two open time intervals can overlap only when `D' = D`"). -/
theorem exists_mem_pocket (h : IsOrderedTriple α μ β)
    (hcα : interior {t ∈ Icc (0 : ℝ) 1 | μ t ∈ crossRange α} = ∅)
    (hcβ : interior {t ∈ Icc (0 : ℝ) 1 | μ t ∈ crossRange β} = ∅) {a b : ℝ} (hg : IsContactGap α β a b)
    {σ τ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) (hτ : τ ∈ Icc (0 : ℝ) 1) (hστ : σ < τ) (hσa : μ σ = α a)
    (hτb : μ τ = α b) : ∃ t₁ ∈ Ioo σ τ, μ t₁ ∈ jordanIn (pocketCurve α β a b) := by
  -- a time in `(σ, τ)` off both walls
  have hint := Sec6.interior_setOf_mem_union_eq_empty h.middle.cont h.lower.isCompact_crossRange.isClosed hcα hcβ
  obtain ⟨t₁, ht₁, ht₁w⟩ : ∃ t₁ ∈ Ioo σ τ, μ t₁ ∉ crossRange α ∪ crossRange β := by
    by_contra hnot
    push Not at hnot
    have hsub : Ioo σ τ ⊆ interior {t ∈ Icc (0 : ℝ) 1 | μ t ∈ crossRange α ∪ crossRange β} :=
      interior_maximal (fun t ht => ⟨⟨hσ.1.trans ht.1.le, ht.2.le.trans hτ.2⟩, hnot t ht⟩) isOpen_Ioo
    rw [hint] at hsub
    exact (nonempty_Ioo.2 hστ).ne_empty (subset_empty_iff.1 hsub)
  have ht₁01 : t₁ ∈ Ioo (0 : ℝ) 1 := ⟨hσ.1.trans_lt ht₁.1, ht₁.2.trans_le hτ.2⟩
  have hb := h.middle.mem_disc t₁ ht₁01
  have hα' : μ t₁ ∉ crossRange α := fun h' => ht₁w (Or.inl h')
  have hβ' : μ t₁ ∉ crossRange β := fun h' => ht₁w (Or.inr h')
  have hz₁ := h.mem_crossSide_lower (Ioo_subset_Icc_self ht₁01) hb hα'
  have hz₂ := h.mem_crossSide_upper (Ioo_subset_Icc_self ht₁01) hb hβ'
  obtain ⟨a', b', hg', hcomp⟩ := exists_contactGap_of_between h.lower h.upper h.lower_upper hz₁ hz₂ hβ'
  have hmem : μ t₁ ∈ jordanIn (pocketCurve α β a' b') := by
    rw [← hcomp]; exact mem_connectedComponentIn ⟨hb, ht₁w⟩
  obtain ⟨σ', hσ', τ', hτ', hσ'τ', hσ'a', hτ'b'⟩ := h.exists_corner_times hg'
  have hcl' : μ t₁ ∈ closure (jordanIn (pocketCurve α β a' b')) := subset_closure hmem
  have h1 : σ' ≤ t₁ := not_lt.1 fun h' =>
    h.notMem_closure_pocket_of_lt hg' hσ' hτ' hσ'τ' hσ'a' hτ'b' (Ioo_subset_Icc_self ht₁01) h' hcl'
  have h2 : t₁ ≤ τ' := not_lt.1 fun h' =>
    h.notMem_closure_pocket_of_gt hg' hσ' hτ' hσ'τ' hσ'a' hτ'b' (Ioo_subset_Icc_self ht₁01) h' hcl'
  have hcontact : ∀ {u v : ℝ}, u ∈ Sec7.pocketContactSet α β → v ∈ Sec7.pocketContactSet α β → u ≤ v →
      ∀ {p q : ℝ}, p ∈ Icc (0 : ℝ) 1 → q ∈ Icc (0 : ℝ) 1 → μ p = α u → μ q = α v → p ≤ q := by
    intro u v hu hv huv p q hp hq hpu hqv
    rcases eq_or_lt_of_le huv with he | hl
    · rw [he] at hpu; exact (h.middle.inj hp hq (hpu.trans hqv.symm)).le
    · exact (h.lower.lt_of_contact h.middle h.lower_middle hu.1 hv.1 hp hq hpu.symm hqv.symm hl).le
  obtain ⟨haS, hbS, hab, hgap⟩ := hg
  obtain ⟨ha'S, hb'S, ha'b', hgap'⟩ := hg'
  refine ⟨t₁, ht₁, ?_⟩
  rcases le_or_gt b a' with hba' | hab'
  · have := hcontact hbS ha'S hba' hτ hσ' hτb hσ'a'
    linarith [ht₁.2]
  rcases le_or_gt b' a with hb'a | hab''
  · have := hcontact hb'S haS hb'a hτ' hσ hτ'b' hσa
    linarith [ht₁.1]
  have haa : a = a' := by
    rcases lt_trichotomy a a' with h' | h' | h'
    · exact absurd ha'S (hgap a' ⟨h', hab'⟩)
    · exact h'
    · exact absurd haS (hgap' a ⟨h', hab''⟩)
  have hbb : b = b' := by
    rcases lt_trichotomy b b' with h' | h' | h'
    · exact absurd hbS (hgap' b ⟨haa ▸ hab, h'⟩)
    · exact h'
    · exact absurd hb'S (hgap b' ⟨haa ▸ hab'', h'⟩)
  rw [haa, hbb]
  exact hmem

/-- **The traversal of a pocket** (Wang–Wu Lemma 4.22, first part; specification, proof of Lemma 7.1). Let the
contact times of the middle curve with each wall have empty interior. For a pocket with corners `x = α a`,
`y = α b`, the middle curve meets `x` and `y` at times `σ < τ`, lies in the closed pocket exactly on `[σ, τ]`, and the
times in `(σ, τ]` at which it is not in the open pocket have empty interior. -/
theorem traverse (h : IsOrderedTriple α μ β)
    (hcα : interior {t ∈ Icc (0 : ℝ) 1 | μ t ∈ crossRange α} = ∅)
    (hcβ : interior {t ∈ Icc (0 : ℝ) 1 | μ t ∈ crossRange β} = ∅) {a b : ℝ} (hg : IsContactGap α β a b) :
    ∃ σ τ, 0 ≤ σ ∧ σ < τ ∧ τ ≤ 1 ∧ μ σ = α a ∧ μ τ = α b ∧
      (∀ t ∈ Icc σ τ, μ t ∈ closure (jordanIn (pocketCurve α β a b))) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, t ∉ Icc σ τ → μ t ∉ closure (jordanIn (pocketCurve α β a b))) ∧
      interior {t ∈ Icc σ τ | σ < t ∧ μ t ∉ jordanIn (pocketCurve α β a b)} = ∅ := by
  obtain ⟨σ, hσ, τ, hτ, hστ, hσa, hτb⟩ := h.exists_corner_times hg
  obtain ⟨hJ, -, -, hUfr, -⟩ := pocket_props h.lower h.upper h.lower_upper hg
  set U := jordanIn (pocketCurve α β a b)
  have hcorner : ∀ q, q = α a ∨ q = α b → q ∈ closure U := by
    rintro q (rfl | rfl)
    · rw [closure_eq_self_union_frontier, hUfr]
      exact Or.inr (Or.inl ⟨a, ⟨le_rfl, hg.2.2.1.le⟩, rfl⟩)
    · rw [closure_eq_self_union_frontier, hUfr]
      exact Or.inr (Or.inl ⟨b, ⟨hg.2.2.1.le, le_rfl⟩, rfl⟩)
  have hIsub : Icc σ τ ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hσ.1 hτ.2
  have hin : ∀ t ∈ Icc σ τ, μ t ∈ closure U := by
    obtain ⟨t₁, ht₁, ht₁U⟩ := h.exists_mem_pocket hcα hcβ hg hσ hτ hστ hσa hτb
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h' | h'
    · rw [← h', hσa]; exact hcorner _ (Or.inl rfl)
    rcases eq_or_lt_of_le ht.2 with h'' | h''
    · rw [h'', hτb]; exact hcorner _ (Or.inr rfl)
    have hloc : ∀ u ∈ Ioo σ τ, ∀ᶠ u' in 𝓝[Ioo σ τ] u, (μ u' ∈ closure U ↔ μ u ∈ closure U) := by
      intro u hu
      refine nhdsWithin_mono _ (Ioo_subset_Icc_self.trans hIsub)
        (h.eventually_iff_mem_closure_pocket hg (hIsub (Ioo_subset_Icc_self hu)) ?_ ?_)
      · rw [← hσa]; exact fun h₀ => hu.1.ne' (h.middle.inj (hIsub (Ioo_subset_Icc_self hu)) hσ h₀)
      · rw [← hτb]; exact fun h₀ => hu.2.ne (h.middle.inj (hIsub (Ioo_subset_Icc_self hu)) hτ h₀)
    exact (IsPreconnected.iff_of_eventually (convex_Ioo σ τ).isPreconnected hloc ht₁ ⟨h', h''⟩).1 (subset_closure ht₁U)
  refine ⟨σ, τ, hσ.1, hστ, hτ.2, hσa, hτb, hin, fun t ht hnot => ?_, ?_⟩
  · rcases not_and_or.1 hnot with h' | h'
    · exact h.notMem_closure_pocket_of_lt hg hσ hτ hστ hσa hτb ht (not_le.1 h')
    · exact h.notMem_closure_pocket_of_gt hg hσ hτ hστ hσa hτb ht (not_le.1 h')
  · have hsub : {t ∈ Icc σ τ | σ < t ∧ μ t ∉ U} ⊆ {t ∈ Icc (0 : ℝ) 1 | μ t ∈ crossRange α ∪ crossRange β} := by
      rintro t ⟨ht, -, htU⟩
      refine ⟨hIsub ht, ?_⟩
      have hfr : μ t ∈ pocketCurve α β a b := by
        rw [← hUfr]; exact ⟨hin t ht, by rwa [(isOpen_jordanIn hJ).interior_eq]⟩
      rcases hfr with ⟨s, hs, hss⟩ | ⟨r, hr, hrr⟩
      · exact Or.inl ⟨s, ⟨hg.1.1.1.trans hs.1, hs.2.trans hg.2.1.1.2⟩, hss⟩
      · obtain ⟨hja, -⟩ := contactMap_mem h.upper hg.1
        obtain ⟨hjb, -⟩ := contactMap_mem h.upper hg.2.1
        exact Or.inr ⟨r, ⟨hja.1.trans hr.1, hr.2.trans hjb.2⟩, hrr⟩
    exact subset_empty_iff.1 ((interior_mono hsub).trans
      (Sec6.interior_setOf_mem_union_eq_empty h.middle.cont h.lower.isCompact_crossRange.isClosed hcα hcβ).subset)

end IsOrderedTriple

end InteractingSLE.WangWu
