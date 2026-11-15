/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripCollar
import InteractingSLE.Spec.Sec4.Heights

/-!
# (RS13.3): exposure of a common terminal arc, and the contradiction for either side

Packet PROVE-STRIPSYS12. Specification §7.4, the proof of Aux. lemma 130, (RS13.3) (`source/spec/p385-432.md`
L440–L456, p. 411):

> If a terminal interval of `β` were in `α`, compact injectivity would identify each of its compact proper subarcs with
> a subarc of `α`. […] Their traversal directions agree by reverse first-visit order. A smaller proper subarc has a
> common right-side collar which meets no other portions of either path […] Expressing both germs in one chart
> therefore forces `θ₁ − π/2 = 2πn`. This is impossible because `−π < θ₁ − π/2 < 0`.

PROVE-STRIPSYS11 proved the chart comparison (`StripCollar.commonArcChart_of_approach`: along an approach from the
joint unbounded domain both own charts tend to real points and the derivative-argument lifts differ by `o(1)`, so the
integer of (RS13.3) is `0`) and left two geometric inputs: the **exposure** of the common arc to the joint unbounded
domain, and the identification of the **side** of the approach in each own chart. This file removes both.

* **Arcs are nowhere dense** (`mem_closure_compl_image_Icc`): every point is adherent to the complement of an arc
  `η([a, b])` (a circle about an interior point of the arc would split into its two closed halves).
* **Exposure of a same-direction terminal arc** (`mem_closure_H_diff_fillH_of_sameArc`): if two good paths share the
  terminal arc `β([σ₂, q₂]) = α([σ₁, q₁]) ⊆ ℍ` traversed in the same direction (`β(σ₂) = α(σ₁)`), and the tip `α(q₁)` is
  adherent to the joint unbounded domain (for instance because the paths continue to `∞`,
  `mem_closure_H_diff_fillH_of_continuation`), then every point `α(s)`, `σ₁ < s ≤ q₁`, of the common arc is adherent
  to the joint unbounded domain. Proof: the two legs `F = α([0, σ₁]) ∪ β([0, σ₂])` meet the arc `S = α([σ₁, q₁])` only
  at the merge point; the arc after the merge point is connected, misses `F` and contains the tip, which is free for
  `F`, so it lies in the unbounded domain of `F`; the slit lemma (`mem_H_diff_fillH_union_of_slit`) then adds `S`.
* **Local coincidence** (`exists_ball_inter_eq_of_sameArc`): near `α(s)`, `σ₁ < s`, the two stopped ranges coincide.
* **The side does not matter** (`false_of_sideHeights_of_signs`): for `0 < κ < 4` and `−π/2 < θ₁ < π/2`, the integer
  `0` of the common collar is incompatible with side heights `s₁λ − θ₁χ` and `s₂λ − (π/2)χ` for **all four** sign
  choices `s₁, s₂ ∈ {±1}` (the mixed choices would need `θ₁ − π/2 = ±4π/(4 − κ)`, of modulus `> π`). So the own-chart
  sides of the approach need not be identified.
* **(RS13.3), assembled from the paths** (`false_of_sameArc_sideHeights`): two good paths with a same-direction common
  terminal arc, exposed tip, the single-path side heights at a common arc point (in the form of
  `Aux70.SinglePathSideHeightStatement`'s conclusion) and boundary agreement of the two means along approaches from
  the joint unbounded domain: impossible.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Bornology Complex
open scoped NNReal ENNReal Real

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Sec7

open HalfPlaneSep Restart ReverseArc StripCollar

namespace StripGeom

/-! ### Arcs are nowhere dense -/

section Arc

variable {η : ℝ≥0 → ℂ} {a b : ℝ≥0}

/-- A circle about an interior point `η t` of an arc is not contained in the arc. -/
theorem not_sphere_subset_image_Icc (hc : ContinuousOn η (Icc a b)) (hi : InjOn η (Icc a b)) {t : ℝ≥0}
    (hat : a < t) (htb : t < b) : ∃ r > 0, ∀ r' ∈ Ioc 0 r, ¬ sphere (η t) r' ⊆ η '' Icc a b := by
  have htI : t ∈ Icc a b := ⟨hat.le, htb.le⟩
  have haI : a ∈ Icc a b := ⟨le_rfl, (hat.trans htb).le⟩
  have hbI : b ∈ Icc a b := ⟨(hat.trans htb).le, le_rfl⟩
  have hda : 0 < ‖η a - η t‖ := norm_pos_iff.2 (sub_ne_zero.2 fun h => hat.ne (hi haI htI h))
  have hdb : 0 < ‖η b - η t‖ := norm_pos_iff.2 (sub_ne_zero.2 fun h => htb.ne' (hi hbI htI h))
  refine ⟨min ‖η a - η t‖ ‖η b - η t‖, lt_min hda hdb, fun r' hr' hsub => ?_⟩
  set g : ℝ≥0 → ℝ := fun u => ‖η u - η t‖ with hgdef
  have hgc : ContinuousOn g (Icc a b) := (hc.sub continuousOn_const).norm
  -- a point of each half on the circle
  have h₁ : ∃ u ∈ Icc a t, g u = r' := by
    have hsub' := intermediate_value_Icc' hat.le (hgc.mono (Icc_subset_Icc_right htb.le))
    have hmem : r' ∈ Icc (g t) (g a) := ⟨by simp only [hgdef, sub_self, norm_zero]; exact hr'.1.le,
      hr'.2.trans (min_le_left _ _)⟩
    exact hsub' hmem
  have h₂ : ∃ u ∈ Icc t b, g u = r' := by
    have hsub' := intermediate_value_Icc htb.le (hgc.mono (Icc_subset_Icc_left hat.le))
    have hmem : r' ∈ Icc (g t) (g b) := ⟨by simp only [hgdef, sub_self, norm_zero]; exact hr'.1.le,
      hr'.2.trans (min_le_right _ _)⟩
    exact hsub' hmem
  obtain ⟨u₁, hu₁, hgu₁⟩ := h₁
  obtain ⟨u₂, hu₂, hgu₂⟩ := h₂
  -- the two closed halves split the circle
  have hconn : IsPreconnected (sphere (η t) r') :=
    isPreconnected_sphere (by rw [Complex.rank_real_complex]; norm_num) (η t) r'
  have hP : IsClosed (η '' Icc a t) :=
    (isCompact_Icc.image_of_continuousOn (hc.mono (Icc_subset_Icc_right htb.le))).isClosed
  have hQ : IsClosed (η '' Icc t b) :=
    (isCompact_Icc.image_of_continuousOn (hc.mono (Icc_subset_Icc_left hat.le))).isClosed
  have hcover : sphere (η t) r' ⊆ η '' Icc a t ∪ η '' Icc t b := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := hsub hw
    rcases le_total u t with h | h
    · exact Or.inl ⟨u, ⟨hu.1, h⟩, rfl⟩
    · exact Or.inr ⟨u, ⟨h, hu.2⟩, rfl⟩
  have hne₁ : (sphere (η t) r' ∩ η '' Icc a t).Nonempty :=
    ⟨η u₁, by rw [mem_sphere, dist_eq_norm]; exact hgu₁, ⟨u₁, hu₁, rfl⟩⟩
  have hne₂ : (sphere (η t) r' ∩ η '' Icc t b).Nonempty :=
    ⟨η u₂, by rw [mem_sphere, dist_eq_norm]; exact hgu₂, ⟨u₂, hu₂, rfl⟩⟩
  obtain ⟨w, hw, ⟨u, hu, rfl⟩, ⟨u', hu', he⟩⟩ :=
    isPreconnected_closed_iff.1 hconn _ _ hP hQ hcover hne₁ hne₂
  have huI : u ∈ Icc a b := ⟨hu.1, hu.2.trans htb.le⟩
  have hu'I : u' ∈ Icc a b := ⟨hat.le.trans hu'.1, hu'.2⟩
  have huu' : u' = u := hi hu'I huI he
  have hut : u = t := le_antisymm hu.2 (huu' ▸ hu'.1)
  rw [mem_sphere, hut, dist_self] at hw
  exact hr'.1.ne hw

/-- **An arc is nowhere dense**: every point is adherent to the complement of `η([a, b])`. -/
theorem mem_closure_compl_image_Icc (hc : ContinuousOn η (Icc a b)) (hi : InjOn η (Icc a b)) (z : ℂ) :
    z ∈ closure (η '' Icc a b)ᶜ := by
  rw [closure_compl, mem_compl_iff, mem_interior]
  rintro ⟨V, hVS, hVo, hzV⟩
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.1 hVo z hzV
  have hball : ball z ε ⊆ η '' Icc a b := hεV.trans hVS
  rcases lt_or_ge a b with hab | hba
  · -- a parameter strictly inside `(a, b)` whose point lies in the ball
    obtain ⟨t₀, ht₀, hzt₀⟩ := hball (mem_ball_self hε)
    have hpre : η ⁻¹' ball z ε ∈ 𝓝[Icc a b] t₀ := hc t₀ ht₀ (isOpen_ball.mem_nhds (hzt₀ ▸ mem_ball_self hε))
    have hcl : t₀ ∈ closure (Ioo a b) := by rw [closure_Ioo hab.ne]; exact ht₀
    obtain ⟨O, hOo, ht₀O, hOsub⟩ := mem_nhdsWithin.1 hpre
    obtain ⟨t, htO, htI⟩ := mem_closure_iff.1 hcl O hOo ht₀O
    have htb : η t ∈ ball z ε := hOsub ⟨htO, Ioo_subset_Icc_self htI⟩
    -- a small circle about `η t` inside the ball
    obtain ⟨δ, hδ, hδb⟩ := Metric.isOpen_iff.1 isOpen_ball (η t) htb
    obtain ⟨r, hr, hsph⟩ := not_sphere_subset_image_Icc hc hi htI.1 htI.2
    set r' := min r (δ / 2) with hr'def
    have hr'pos : 0 < r' := lt_min hr (half_pos hδ)
    refine hsph r' ⟨hr'pos, min_le_left _ _⟩ fun w hw => hball (hδb ?_)
    rw [mem_ball, mem_sphere.1 hw]
    exact (min_le_right _ _).trans_lt (half_lt_self hδ)
  · -- a degenerate arc is at most one point
    have hsub : η '' Icc a b ⊆ {η a} := by
      rintro _ ⟨t, ht, rfl⟩
      rw [mem_singleton_iff, le_antisymm ht.2 (hba.trans ht.1), le_antisymm (ht.1.trans ht.2) hba]
    have h1 : z ∈ ({η a} : Set ℂ) := hsub (hball (mem_ball_self hε))
    have h2 : z + ((ε / 2 : ℝ) : ℂ) ∈ ({η a} : Set ℂ) := by
      refine hsub (hball ?_)
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hε)]
      exact half_lt_self hε
    rw [mem_singleton_iff] at h1 h2
    rw [← h1, add_eq_left] at h2
    exact (half_pos hε).ne' (by exact_mod_cast h2)

end Arc

/-! ### Exposure of a same-direction common terminal arc -/

section Expose

variable {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ} {q₁ q₂ σ₁ σ₂ : ℝ≥0}

/-- A tip adherent to the unbounded domain through a continuation: a preconnected unbounded subset of `ℍ \ Γ`
adherent to `z` makes `z` adherent to the unbounded domain of `Γ`. -/
theorem mem_closure_H_diff_fillH_of_continuation {Γ C : Set ℂ} (hΓ : IsClosed Γ) (hC : IsPreconnected C)
    (hCu : ¬ IsBounded C) (hCΓ : C ⊆ H \ Γ) {z : ℂ} (hz : z ∈ closure C) : z ∈ closure (H \ fillH Γ) :=
  closure_mono (subset_H_diff_fillH_of_not_isBounded hΓ hC hCu hCΓ) hz

/-- **The tip is exposed when the path continues to `∞`**: if `α` is continuous on `[q, ∞)` and `α((q, ∞))` is an
unbounded subset of `ℍ \ Γ`, then `α(q)` is adherent to the unbounded domain of the closed set `Γ`. -/
theorem tip_mem_closure_H_diff_fillH_of_continuation {Γ : Set ℂ} (hΓ : IsClosed Γ) {q : ℝ≥0}
    (hc : ContinuousOn α (Ici q)) (hu : ¬ IsBounded (α '' Ioi q)) (hH : α '' Ioi q ⊆ H \ Γ) :
    α q ∈ closure (H \ fillH Γ) := by
  have hcl : α q ∈ closure (α '' Ioi q) := by
    refine ContinuousWithinAt.mem_closure_image ((hc q self_mem_Ici).mono Ioi_subset_Ici_self) ?_
    rw [closure_Ioi]
    exact self_mem_Ici
  exact mem_closure_H_diff_fillH_of_continuation hΓ (isPreconnected_Ioi.image _ (hc.mono Ioi_subset_Ici_self)) hu
    hH hcl

/-- The two stopped ranges are the legs `α([0, σ₁]) ∪ β([0, σ₂])` and the arc `α([σ₁, q₁])`, when the terminal piece of
the second prefix lies on that arc. -/
theorem union_eq_legs_union_arc {τ₁ : ℝ≥0} (hσ₁ : σ₁ ≤ τ₁) (hτ₁ : τ₁ ≤ q₁) (hσ₂ : σ₂ ≤ q₂)
    (hJ : β '' Icc σ₂ q₂ = α '' Icc σ₁ τ₁) :
    α '' Icc 0 q₁ ∪ β '' Icc 0 q₂ = (α '' Icc 0 σ₁ ∪ β '' Icc 0 σ₂) ∪ α '' Icc σ₁ q₁ := by
  have hA : α '' Icc 0 q₁ = α '' Icc 0 σ₁ ∪ α '' Icc σ₁ q₁ := by
    rw [← image_union, Icc_union_Icc_eq_Icc (zero_le : (0 : ℝ≥0) ≤ σ₁) (hσ₁.trans hτ₁)]
  have hB : β '' Icc 0 q₂ = β '' Icc 0 σ₂ ∪ α '' Icc σ₁ τ₁ := by
    rw [← hJ, ← image_union, Icc_union_Icc_eq_Icc (zero_le : (0 : ℝ≥0) ≤ σ₂) hσ₂]
  have hsub : α '' Icc σ₁ τ₁ ⊆ α '' Icc σ₁ q₁ := image_mono (Icc_subset_Icc_right hτ₁)
  rw [hA, hB]
  ext w
  simp only [mem_union]
  constructor
  · rintro ((h | h) | (h | h))
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr h)
    · exact Or.inr (hsub h)
  · rintro ((h | h) | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inr h)

/-- The legs meet the arc `α([σ₁, q₁])` only at the merge point `α(σ₁) = β(σ₂)`. -/
theorem legs_inter_arc_eq (hi₁ : InjOn α (Icc 0 q₁)) (hσ₁ : σ₁ ≤ q₁) (hm : β σ₂ = α σ₁)
    (hβJ : ∀ t < σ₂, β t ∉ α '' Icc σ₁ q₁) :
    (α '' Icc 0 σ₁ ∪ β '' Icc 0 σ₂) ∩ α '' Icc σ₁ q₁ = {α σ₁} := by
  refine Subset.antisymm ?_ ?_
  · rintro w ⟨⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩, hw⟩
    · obtain ⟨v, hv, hvu⟩ := hw
      have := hi₁ ⟨zero_le, hv.2⟩ ⟨zero_le, hu.2.trans hσ₁⟩ hvu
      rw [mem_singleton_iff, ← this, le_antisymm (this ▸ hu.2) hv.1]
    · rcases eq_or_lt_of_le hu.2 with h | h
      · rw [mem_singleton_iff, h, hm]
      · exact absurd hw (hβJ u h)
  · rintro _ rfl
    exact ⟨Or.inl ⟨σ₁, ⟨zero_le, le_rfl⟩, rfl⟩, ⟨σ₁, ⟨le_rfl, hσ₁⟩, rfl⟩⟩

/-- Points of the arc after the merge point are off the legs. -/
theorem notMem_legs (hi₁ : InjOn α (Icc 0 q₁)) (hσ₁ : σ₁ ≤ q₁) (hm : β σ₂ = α σ₁)
    (hβJ : ∀ t < σ₂, β t ∉ α '' Icc σ₁ q₁) {s : ℝ≥0} (hs : s ∈ Ioc σ₁ q₁) :
    α s ∉ α '' Icc 0 σ₁ ∪ β '' Icc 0 σ₂ := by
  intro h
  have hmem : α s ∈ (α '' Icc 0 σ₁ ∪ β '' Icc 0 σ₂) ∩ α '' Icc σ₁ q₁ := ⟨h, s, ⟨hs.1.le, hs.2⟩, rfl⟩
  rw [legs_inter_arc_eq hi₁ hσ₁ hm hβJ, mem_singleton_iff] at hmem
  exact hs.1.ne' (hi₁ ⟨zero_le, hs.2⟩ ⟨zero_le, hσ₁⟩ hmem)

/-- **Exposure of a same-direction common arc.** Let two good paths `α, β` merge at `α(σ₁) = β(σ₂)` and then run
along one arc in the same direction: `β([σ₂, q₂]) = α([σ₁, τ₁])` with `τ₁ ≤ q₁`, `β` meets `α([σ₁, q₁])` at no earlier
time, and `α([σ₁, q₁]) ⊆ ℍ`. If the tip `α(q₁)` is adherent to the joint unbounded domain, then every point `α(s)`,
`σ₁ < s ≤ q₁`, is adherent to the joint unbounded domain. -/
theorem mem_closure_H_diff_fillH_of_sameArc (hp₁ : IsPathGood α ζ₁ x₁) (hp₂ : IsPathGood β ζ₂ x₂)
    (hq₁ : (q₁ : ℝ≥0∞) ≤ ζ₁) (hq₂ : (q₂ : ℝ≥0∞) ≤ ζ₂) {τ₁ : ℝ≥0} (hσ₁ : σ₁ < q₁) (hσ₁τ : σ₁ ≤ τ₁)
    (hτ₁ : τ₁ ≤ q₁) (hσ₂ : σ₂ ≤ q₂) (hJ : β '' Icc σ₂ q₂ = α '' Icc σ₁ τ₁) (hm : β σ₂ = α σ₁)
    (hβJ : ∀ t < σ₂, β t ∉ α '' Icc σ₁ q₁) (hJH : α '' Icc σ₁ q₁ ⊆ H)
    (htip : α q₁ ∈ closure (H \ fillH (α '' Icc 0 q₁ ∪ β '' Icc 0 q₂))) {s : ℝ≥0} (hs : s ∈ Ioc σ₁ q₁) :
    α s ∈ closure (H \ fillH (α '' Icc 0 q₁ ∪ β '' Icc 0 q₂)) := by
  have hi₁ := IsPathGood.injOn_Icc hp₁ hq₁
  have hc₁ := IsPathGood.continuousOn_Icc hp₁ hq₁
  set F := α '' Icc 0 σ₁ ∪ β '' Icc 0 σ₂ with hFdef
  set S := α '' Icc σ₁ q₁ with hSdef
  have hσ₁ζ : (σ₁ : ℝ≥0∞) ≤ ζ₁ := (ENNReal.coe_le_coe.2 hσ₁.le).trans hq₁
  have hσ₂ζ : (σ₂ : ℝ≥0∞) ≤ ζ₂ := (ENNReal.coe_le_coe.2 hσ₂).trans hq₂
  have hFc : IsCompact F := (IsPathGood.isCompact_image hp₁ hσ₁ζ).union (IsPathGood.isCompact_image hp₂ hσ₂ζ)
  have hSc : IsCompact S := IsPathGood.isCompact_image_Icc hp₁ hq₁
  have hΓ := union_eq_legs_union_arc (α := α) hσ₁τ hτ₁ hσ₂ hJ
  have hFS := legs_inter_arc_eq hi₁ hσ₁.le hm hβJ
  have hFΓ : F ⊆ α '' Icc 0 q₁ ∪ β '' Icc 0 q₂ := by rw [hΓ]; exact subset_union_left
  -- the tip is in the unbounded domain of the legs
  have htipF : α q₁ ∈ H \ fillH F := by
    have h1 : α q₁ ∈ closure (H \ fillH F) :=
      closure_mono (sdiff_subset_sdiff_right (fillH_mono hFΓ)) htip
    have hnot := notMem_legs hi₁ hσ₁.le hm hβJ ⟨hσ₁, le_rfl⟩
    exact mem_H_diff_fillH_of_isFreeAt (isFreeAt_of_mem_closure hFc.isClosed hnot h1)
      (hJH ⟨q₁, ⟨hσ₁.le, le_rfl⟩, rfl⟩)
  -- the arc after `s` is connected, off the legs, and contains the tip
  have hsF : α s ∈ H \ fillH F := by
    have hX : IsPreconnected (α '' Icc s q₁) :=
      isPreconnected_Icc.image _ (hc₁.mono (Icc_subset_Icc_left zero_le))
    have hXF : α '' Icc s q₁ ⊆ H \ F := by
      rintro _ ⟨t, ht, rfl⟩
      exact ⟨hJH ⟨t, ⟨hs.1.le.trans ht.1, ht.2⟩, rfl⟩,
        notMem_legs hi₁ hσ₁.le hm hβJ ⟨hs.1.trans_le ht.1, ht.2⟩⟩
    have hsub := hX.subset_connectedComponentIn (x := α q₁) ⟨q₁, ⟨hs.2, le_rfl⟩, rfl⟩ hXF
    exact connectedComponentIn_subset_H_diff_fillH hFc.isClosed htipF (hsub ⟨s, ⟨le_rfl, hs.2⟩, rfl⟩)
  -- the slit lemma adds the arc
  have hopen : IsOpen (H \ fillH F) := isOpen_H_diff_fillH hFc.isBounded
  obtain ⟨ε, hε, hεF⟩ := Metric.isOpen_iff.1 hopen _ hsF
  have hcS : ContinuousOn α (Icc σ₁ q₁) :=
    hp₁.continuousOn.mono fun _ ht => (ENNReal.coe_le_coe.2 ht.2).trans hq₁
  have hiS : InjOn α (Icc σ₁ q₁) := hp₁.1.mono fun _ ht => (ENNReal.coe_le_coe.2 ht.2).trans hq₁
  have hSpc : IsPreconnected Sᶜ := isPreconnected_compl_image_Icc hσ₁ hcS hiS
  have hScl := mem_closure_compl_image_Icc hcS hiS (α s)
  rw [Metric.mem_closure_iff]
  intro δ hδ
  obtain ⟨z, hzS, hzd⟩ := Metric.mem_closure_iff.1 hScl (min δ ε) (lt_min hδ hε)
  refine ⟨z, ?_, hzd.trans_le (min_le_left _ _)⟩
  have hzF : z ∈ H \ fillH F := hεF (by rw [mem_ball, dist_comm]; exact hzd.trans_le (min_le_right _ _))
  rw [hΓ]
  exact mem_H_diff_fillH_union_of_slit hFc hSc hSpc hJH (by rw [hFS]; exact isPreconnected_singleton) hzF hzS

/-- **Local coincidence**: near a point `α(s)`, `σ₁ < s < τ₁`, of the common arc, the two stopped ranges coincide. -/
theorem exists_ball_inter_eq_of_sameArc (hp₁ : IsPathGood α ζ₁ x₁) (hp₂ : IsPathGood β ζ₂ x₂)
    (hq₁ : (q₁ : ℝ≥0∞) ≤ ζ₁) (hq₂ : (q₂ : ℝ≥0∞) ≤ ζ₂) {τ₁ : ℝ≥0} (hσ₁τ : σ₁ ≤ τ₁) (hτ₁ : τ₁ ≤ q₁)
    (hσ₂ : σ₂ ≤ q₂) (hJ : β '' Icc σ₂ q₂ = α '' Icc σ₁ τ₁) (hm : β σ₂ = α σ₁)
    (hβJ : ∀ t < σ₂, β t ∉ α '' Icc σ₁ q₁) {s : ℝ≥0} (hs : s ∈ Ioo σ₁ τ₁) :
    ∃ ρ > 0, α '' Icc 0 q₁ ∩ ball (α s) ρ = β '' Icc 0 q₂ ∩ ball (α s) ρ := by
  have hi₁ := IsPathGood.injOn_Icc hp₁ hq₁
  have hσ₁q : σ₁ ≤ q₁ := hσ₁τ.trans hτ₁
  have hσ₁ζ : (σ₁ : ℝ≥0∞) ≤ ζ₁ := (ENNReal.coe_le_coe.2 hσ₁q).trans hq₁
  have hσ₂ζ : (σ₂ : ℝ≥0∞) ≤ ζ₂ := (ENNReal.coe_le_coe.2 hσ₂).trans hq₂
  set G := (α '' Icc 0 σ₁ ∪ β '' Icc 0 σ₂) ∪ α '' Icc τ₁ q₁ with hGdef
  have hGc : IsCompact G := ((IsPathGood.isCompact_image hp₁ hσ₁ζ).union
    (IsPathGood.isCompact_image hp₂ hσ₂ζ)).union (IsPathGood.isCompact_image_Icc hp₁ hq₁)
  have hnot : α s ∉ G := by
    rintro (h | ⟨u, hu, hus⟩)
    · exact notMem_legs hi₁ hσ₁q hm hβJ ⟨hs.1, hs.2.le.trans hτ₁⟩ h
    · have := hi₁ ⟨zero_le, hu.2⟩ ⟨zero_le, hs.2.le.trans hτ₁⟩ hus
      exact absurd (this ▸ hu.1) (not_le.2 hs.2)
  obtain ⟨ρ, hρ, hρG⟩ := Metric.isOpen_iff.1 hGc.isClosed.isOpen_compl _ hnot
  refine ⟨ρ, hρ, ?_⟩
  have hA : α '' Icc 0 q₁ = α '' Icc 0 σ₁ ∪ α '' Icc σ₁ τ₁ ∪ α '' Icc τ₁ q₁ := by
    rw [← image_union, ← image_union, Icc_union_Icc_eq_Icc (zero_le : (0 : ℝ≥0) ≤ σ₁) hσ₁τ,
      Icc_union_Icc_eq_Icc (zero_le : (0 : ℝ≥0) ≤ τ₁) hτ₁]
  have hB : β '' Icc 0 q₂ = β '' Icc 0 σ₂ ∪ α '' Icc σ₁ τ₁ := by
    rw [← hJ, ← image_union, Icc_union_Icc_eq_Icc (zero_le : (0 : ℝ≥0) ≤ σ₂) hσ₂]
  rw [hA, hB]
  ext w
  constructor
  · rintro ⟨(hw | hw) | hw, hwb⟩
    · exact absurd (Or.inl (Or.inl hw)) (hρG hwb)
    · exact ⟨Or.inr hw, hwb⟩
    · exact absurd (Or.inr hw) (hρG hwb)
  · rintro ⟨hw | hw, hwb⟩
    · exact absurd (Or.inl (Or.inr hw)) (hρG hwb)
    · exact ⟨Or.inl (Or.inr hw), hwb⟩

/-- **Boundary agreement along the joint unbounded domain**, from the two-local-set comparison of
`SideHeightBox.ae_tendsto_sub_of_locals` at the point `α(s)` (whose local-agreement premises the same-direction arc
supplies): the difference of the two means tends to `0` along approaches from the joint unbounded domain. -/
theorem tendsto_sub_of_sameArc_of_locals {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ} {q₁ q₂ σ₁ σ₂ τ₁ : ℝ≥0}
    (hp₁ : IsPathGood α ζ₁ x₁) (hp₂ : IsPathGood β ζ₂ x₂) (hq₁ : (q₁ : ℝ≥0∞) ≤ ζ₁) (hq₂ : (q₂ : ℝ≥0∞) ≤ ζ₂)
    (hσ₁τ : σ₁ ≤ τ₁) (hτ₁ : τ₁ ≤ q₁) (hσ₂ : σ₂ ≤ q₂) (hJ : β '' Icc σ₂ q₂ = α '' Icc σ₁ τ₁)
    (hm : β σ₂ = α σ₁) (hβJ : ∀ t < σ₂, β t ∉ α '' Icc σ₁ q₁) {s : ℝ≥0} (hs : s ∈ Ioo σ₁ τ₁) {vA vB : ℂ → ℝ}
    (hloc : (∃ r > 0, β '' Icc 0 q₂ ∩ H ∩ ball (α s) r ⊆ α '' Icc 0 q₁ ∩ H) →
      (∃ r > 0, α '' Icc 0 q₁ ∩ H ∩ ball (α s) r ⊆ β '' Icc 0 q₂ ∩ H) →
      Tendsto (fun z => vA z - vB z) (𝓝[H \ (α '' Icc 0 q₁ ∩ H ∪ β '' Icc 0 q₂ ∩ H)] (α s)) (𝓝 0)) :
    Tendsto (fun z => vA z - vB z) (𝓝[H \ fillH (α '' Icc 0 q₁ ∪ β '' Icc 0 q₂)] (α s)) (𝓝 0) := by
  obtain ⟨ρ, hρ, hagree⟩ := exists_ball_inter_eq_of_sameArc hp₁ hp₂ hq₁ hq₂ hσ₁τ hτ₁ hσ₂ hJ hm hβJ hs
  have h₁ : ∃ r > 0, β '' Icc 0 q₂ ∩ H ∩ ball (α s) r ⊆ α '' Icc 0 q₁ ∩ H := by
    refine ⟨ρ, hρ, fun w hw => ?_⟩
    have : w ∈ α '' Icc 0 q₁ ∩ ball (α s) ρ := by rw [hagree]; exact ⟨hw.1.1, hw.2⟩
    exact ⟨this.1, hw.1.2⟩
  have h₂ : ∃ r > 0, α '' Icc 0 q₁ ∩ H ∩ ball (α s) r ⊆ β '' Icc 0 q₂ ∩ H := by
    refine ⟨ρ, hρ, fun w hw => ?_⟩
    have : w ∈ β '' Icc 0 q₂ ∩ ball (α s) ρ := by rw [← hagree]; exact ⟨hw.1.1, hw.2⟩
    exact ⟨this.1, hw.1.2⟩
  refine (hloc h₁ h₂).mono_left (nhdsWithin_mono _ fun z hz => ⟨hz.1, fun hzU => hz.2 ⟨hz.1, Or.inl ?_⟩⟩)
  rcases hzU with h | h
  · exact subset_closure (Or.inl h.1)
  · exact subset_closure (Or.inr h.1)

end Expose

/-! ### The side does not matter -/

section Signs

open QuantumZipper (chiC)

/-- For `0 < κ < 4` and `|d| ≤ π`: `2λ ≠ dχ` (`2λ/χ = 4π/(4 − κ) > π`). -/
theorem two_mul_sleLambda_ne {κ d : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hd : |d| ≤ π) :
    2 * sleLambda κ ≠ d * chiC κ := by
  intro h
  have hl := Sec4.sleLambda_pos hκ
  have hpc := Sec4.pi_mul_chiC hκ
  -- `2πλ = dπχ = d(2 − κ/2)λ`, so `4π = d(4 − κ)`
  have h1 : 2 * π * sleLambda κ = d * (2 - κ / 2) * sleLambda κ := by
    calc 2 * π * sleLambda κ = π * (2 * sleLambda κ) := by ring
      _ = d * (π * chiC κ) := by rw [h]; ring
      _ = d * (2 - κ / 2) * sleLambda κ := by rw [hpc]; ring
  have h2 : 2 * π = d * (2 - κ / 2) := mul_right_cancel₀ hl.ne' h1
  obtain ⟨hd₁, hd₂⟩ := abs_le.1 hd
  nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_right hd₂ (show (0 : ℝ) ≤ 2 - κ / 2 by linarith)]

/-- **(RS13.3) for either side.** For `0 < κ < 4` and two angles with `0 < |θ₁ − θ₂| ≤ π`, side heights `a₁ − θ₁χ` and
`a₂ − θ₂χ` with `aᵢ = ±λ`, together with boundary agreement of the two means and the integer `0` of the common collar,
are impossible, whatever the signs. -/
theorem false_of_sideHeights_of_signs {F : Filter ℂ} [F.NeBot] {v₁ v₂ u₀ : ℂ → ℝ} {L₁ L₂ : ℂ → ℂ}
    {κ θ₁ θ₂ a₁ a₂ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ ≠ θ₂) (hθπ : |θ₁ - θ₂| ≤ π)
    (ha₁ : a₁ = sleLambda κ ∨ a₁ = -sleLambda κ) (ha₂ : a₂ = sleLambda κ ∨ a₂ = -sleLambda κ)
    (hv : Tendsto (fun z => v₁ z - v₂ z) F (𝓝 0)) (hL : Tendsto (fun z => (L₁ z).im - (L₂ z).im) F (𝓝 0))
    (h₁ : Tendsto (fun z => v₁ z + u₀ z + chiC κ * (L₁ z).im) F (𝓝 (a₁ - θ₁ * chiC κ)))
    (h₂ : Tendsto (fun z => v₂ z + u₀ z + chiC κ * (L₂ z).im) F (𝓝 (a₂ - θ₂ * chiC κ))) : False := by
  have hsub := h₁.sub h₂
  have hsum := hv.add (hL.const_mul (chiC κ))
  have heq : (fun z => (v₁ z + u₀ z + chiC κ * (L₁ z).im) - (v₂ z + u₀ z + chiC κ * (L₂ z).im)) =
      fun z => (v₁ z - v₂ z) + chiC κ * ((L₁ z).im - (L₂ z).im) := by
    funext z
    ring
  rw [heq] at hsub
  have hlim := tendsto_nhds_unique hsub hsum
  simp only [mul_zero, add_zero] at hlim
  -- `a₁ − a₂ = (θ₁ − θ₂)χ`
  have hχ := Sec4.chiC_pos hκ hκ4
  have key : a₁ - a₂ = (θ₁ - θ₂) * chiC κ := by linarith
  rcases ha₁ with rfl | rfl <;> rcases ha₂ with rfl | rfl
  · exact hθ (by nlinarith [mul_right_cancel₀ hχ.ne' (show (θ₁ - θ₂) * chiC κ = 0 * chiC κ by linarith)])
  · exact two_mul_sleLambda_ne hκ hκ4 hθπ (by linarith)
  · exact two_mul_sleLambda_ne (d := -(θ₁ - θ₂)) hκ hκ4 (by rwa [abs_neg]) (by linarith)
  · exact hθ (by nlinarith [mul_right_cancel₀ hχ.ne' (show (θ₁ - θ₂) * chiC κ = 0 * chiC κ by linarith)])

end Signs

/-! ### (RS13.3), assembled from the paths -/

section Assembly

open QuantumZipper (chiC fwdMap logDerivFwd)

variable {α : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ} {W : ℝ≥0 → ℝ} {q : ℝ≥0}

/-- **The own chart tends to a nonzero real point** along any ultrafilter converging to a non-tip point of the stopped
prefix from outside its filled hull (the chart value `0` is the tip). -/
theorem exists_real_ne_zero_tendsto_of_mem (hg : IsGeneratingTrace W ζ (fun t => α t - x))
    (hWc : ContinuousOn W {s | (s : ℝ≥0∞) < ζ}) (hW0 : W 0 = 0) (hi : InjOn α {t | (t : ℝ≥0∞) ≤ ζ})
    (hq : (q : ℝ≥0∞) < ζ) (hq0 : 0 < q) {z₀ : ℂ} (hz₀ : z₀ ∈ α '' Icc 0 q) (hz₀q : z₀ ≠ α q)
    (U : Ultrafilter ℂ) (hU : (U : Filter ℂ) ≤ 𝓝[H \ fillH (α '' Icc 0 q)] z₀) :
    ∃ y : ℝ, y ≠ 0 ∧ Tendsto (fun z => fwdMap (fun r : ℝ => W r.toNNReal) q (z - x)) U (𝓝 (y : ℂ)) := by
  have hinj' : InjOn (fun t => α t - x) {t | (t : ℝ≥0∞) ≤ ζ} := fun a ha b hb hab =>
    hi ha hb (sub_left_injective hab)
  have hch := isChart hg hWc hW0 hinj' hq hq0
  set U' : Ultrafilter ℂ := U.map fun z => z - x with hU'def
  have htr : Tendsto (fun z : ℂ => z - x) (𝓝[H \ fillH (α '' Icc 0 q)] z₀)
      (𝓝[H \ fillH ((fun t => α t - x) '' Icc 0 q)] (z₀ - x)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact ((continuous_sub_right (x : ℂ)).tendsto z₀).mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall fun z hz => (mem_H_diff_fillH_phys_iff x q z).1 hz
  have hU' : (U' : Filter ℂ) ≤ 𝓝[H \ fillH ((fun t => α t - x) '' Icc 0 q)] (z₀ - x) := by
    rw [hU'def, Ultrafilter.coe_map]
    exact (Filter.map_mono hU).trans htr
  obtain ⟨y, hyH, hyt, hΦy⟩ := hch.cluster U' (z₀ - x) hU'
  have hyim : y.im = 0 := by
    refine le_antisymm (not_lt.1 fun hpos => ?_) hyH
    have hmem := hch.inv_mem (show y ∈ H from hpos)
    rw [hΦy] at hmem
    obtain ⟨t, ht, hte⟩ := hz₀
    refine hmem.2 ⟨hmem.1, Or.inl (subset_closure ⟨t, ht, ?_⟩)⟩
    show α t - x = z₀ - x
    rw [hte]
  have hyre : (y.re : ℂ) = y := Complex.ext (by simp) (by simp [hyim])
  refine ⟨y.re, fun h0 => hz₀q ?_, ?_⟩
  · have htip := hch.tip
    rw [← hyre, h0, ofReal_zero, htip] at hΦy
    exact (sub_left_injective hΦy).symm
  · rw [hyre]
    have := hyt
    rw [hU'def, Ultrafilter.coe_map, tendsto_map'_iff] at this
    exact this

/-- The side-height conclusion of `Aux70.SinglePathSideHeightStatement` for one path at one point `z₀`: along every
approach to `z₀` from the unbounded domain of the stopped prefix with a real own-chart limit `y`, the mean plus the
derivative correction tends to `λ − θχ` if `y > 0` and to `−λ − θχ` if `y < 0`. -/
def HasSideHeights (κ θ : ℝ) (α : ℝ≥0 → ℂ) (x : ℝ) (W : ℝ≥0 → ℝ) (q : ℝ≥0) (z₀ : ℂ) (v u₀ : ℂ → ℝ) : Prop :=
  ∀ F : Filter ℂ, F.NeBot → F ≤ 𝓝[H \ fillH (α '' Icc 0 q)] z₀ → ∀ y : ℝ,
    Tendsto (fun z => fwdMap (fun r : ℝ => W r.toNNReal) q (z - x)) F (𝓝 (y : ℂ)) →
      (0 < y → Tendsto (fun z => v z + u₀ z + chiC κ * (logDerivFwd (fun r : ℝ => W r.toNNReal) q (z - x)).im) F
        (𝓝 (sleLambda κ - θ * chiC κ))) ∧
      (y < 0 → Tendsto (fun z => v z + u₀ z + chiC κ * (logDerivFwd (fun r : ℝ => W r.toNNReal) q (z - x)).im) F
        (𝓝 (-sleLambda κ - θ * chiC κ)))

/-- Along an ultrafilter with a nonzero chart limit, the side heights give a limit `±λ − θχ`. -/
theorem HasSideHeights.exists_tendsto {κ θ : ℝ} {v u₀ : ℂ → ℝ} {z₀ : ℂ}
    (h : HasSideHeights κ θ α x W q z₀ v u₀) (U : Ultrafilter ℂ)
    (hU : (U : Filter ℂ) ≤ 𝓝[H \ fillH (α '' Icc 0 q)] z₀) {y : ℝ} (hy : y ≠ 0)
    (hfy : Tendsto (fun z => fwdMap (fun r : ℝ => W r.toNNReal) q (z - x)) U (𝓝 (y : ℂ))) :
    ∃ a : ℝ, (a = sleLambda κ ∨ a = -sleLambda κ) ∧
      Tendsto (fun z => v z + u₀ z + chiC κ * (logDerivFwd (fun r : ℝ => W r.toNNReal) q (z - x)).im) U
        (𝓝 (a - θ * chiC κ)) := by
  obtain ⟨hpos, hneg⟩ := h U inferInstance hU y hfy
  rcases lt_or_gt_of_ne hy with hlt | hgt
  · exact ⟨_, Or.inr rfl, hneg hlt⟩
  · exact ⟨_, Or.inl rfl, hpos hgt⟩

/-- **(RS13.3), assembled from the paths** (proof of Aux. lemma 130, p. 411). Two good paths `α` (angle `θ₁`) and `β`
(angle `θ₂`), `0 < |θ₁ − θ₂| ≤ π`, `0 < κ < 4`, merge at `α(σ₁) = β(σ₂)` and then run along one arc in the same
direction (`β([σ₂, q₂]) = α([σ₁, τ₁])`, `β(q₂) = α(τ₁)`, `τ₁ ≤ q₁`, `β` meets `α([σ₁, q₁]) ⊆ ℍ` at no earlier
time), with the tip `α(q₁)` adherent to the joint unbounded domain. At a point `α(s)`, `σ₁ < s < τ₁`, the two
single-path means cannot both have their side heights (`HasSideHeights`) and agree in boundary value along the
approaches from the joint unbounded domain. No side of the approach is identified: all four sign choices are
excluded. -/
theorem false_of_sameArc_sideHeights (α β : ℝ≥0 → ℂ) (x₁ x₂ : ℝ) (W₁ W₂ : ℝ≥0 → ℝ) (ζ₁ ζ₂ : ℝ≥0∞)
    (hg₁ : IsGeneratingTrace W₁ ζ₁ (fun t => α t - x₁)) (hW₁c : ContinuousOn W₁ {s | (s : ℝ≥0∞) < ζ₁})
    (hW₁0 : W₁ 0 = 0) (hg₂ : IsGeneratingTrace W₂ ζ₂ (fun t => β t - x₂))
    (hW₂c : ContinuousOn W₂ {s | (s : ℝ≥0∞) < ζ₂}) (hW₂0 : W₂ 0 = 0)
    (hi₁ : InjOn α {t | (t : ℝ≥0∞) ≤ ζ₁}) (hi₂ : InjOn β {t | (t : ℝ≥0∞) ≤ ζ₂})
    {q₁ q₂ σ₁ σ₂ τ₁ : ℝ≥0} (hq₁ : (q₁ : ℝ≥0∞) < ζ₁) (hq₂ : (q₂ : ℝ≥0∞) < ζ₂) (hσ₁τ : σ₁ < τ₁) (hτ₁ : τ₁ ≤ q₁)
    (hσ₂ : σ₂ ≤ q₂) (hJ : β '' Icc σ₂ q₂ = α '' Icc σ₁ τ₁) (hm : β σ₂ = α σ₁) (hβq : β q₂ = α τ₁)
    (hβJ : ∀ t < σ₂, β t ∉ α '' Icc σ₁ q₁) (hJH : α '' Icc σ₁ q₁ ⊆ H)
    (htip : α q₁ ∈ closure (H \ fillH (α '' Icc 0 q₁ ∪ β '' Icc 0 q₂))) {s : ℝ≥0} (hs : s ∈ Ioo σ₁ τ₁)
    {κ θ₁ θ₂ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ ≠ θ₂) (hθπ : |θ₁ - θ₂| ≤ π) {v₁ v₂ u₀ : ℂ → ℝ}
    (hside₁ : HasSideHeights κ θ₁ α x₁ W₁ q₁ (α s) v₁ u₀) (hside₂ : HasSideHeights κ θ₂ β x₂ W₂ q₂ (α s) v₂ u₀)
    (hv : Tendsto (fun z => v₁ z - v₂ z) (𝓝[H \ fillH (α '' Icc 0 q₁ ∪ β '' Icc 0 q₂)] (α s)) (𝓝 0)) :
    False := by
  have hp₁ : IsPathGood α ζ₁ x₁ := ⟨hi₁, W₁, hW₁c, hW₁0, hg₁⟩
  have hp₂ : IsPathGood β ζ₂ x₂ := ⟨hi₂, W₂, hW₂c, hW₂0, hg₂⟩
  have hi₁' := IsPathGood.injOn_Icc hp₁ hq₁.le
  have hi₂' := IsPathGood.injOn_Icc hp₂ hq₂.le
  have hσ₁ : σ₁ < q₁ := hσ₁τ.trans_le hτ₁
  have hsq : s < q₁ := hs.2.trans_le hτ₁
  -- the second prefix has positive length: its range contains the two distinct points `α(σ₁)`, `α(τ₁)`
  have hq₂0 : 0 < q₂ := by
    refine pos_iff_ne_zero.2 fun h0 => ?_
    have hσ₂0 : σ₂ = 0 := le_antisymm (h0 ▸ hσ₂) zero_le
    have : α σ₁ = α τ₁ := by rw [← hm, ← hβq, hσ₂0, h0]
    exact hσ₁τ.ne (hi₁' ⟨zero_le, hσ₁.le⟩ ⟨zero_le, hτ₁⟩ this)
  -- the approach from the joint unbounded domain
  set Γ := α '' Icc 0 q₁ ∪ β '' Icc 0 q₂ with hΓdef
  have hexp := mem_closure_H_diff_fillH_of_sameArc hp₁ hp₂ hq₁.le hq₂.le hσ₁ hσ₁τ.le hτ₁ hσ₂ hJ hm hβJ hJH htip
    ⟨hs.1, hsq.le⟩
  have : (𝓝[H \ fillH Γ] (α s)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hexp
  set U : Ultrafilter ℂ := Ultrafilter.of (𝓝[H \ fillH Γ] (α s)) with hUdef
  have hU : (U : Filter ℂ) ≤ 𝓝[H \ fillH Γ] (α s) := Ultrafilter.of_le _
  have hU₁ : (U : Filter ℂ) ≤ 𝓝[H \ fillH (α '' Icc 0 q₁)] (α s) :=
    hU.trans (nhdsWithin_mono _ (sdiff_subset_sdiff_right (fillH_mono subset_union_left)))
  have hU₂ : (U : Filter ℂ) ≤ 𝓝[H \ fillH (β '' Icc 0 q₂)] (α s) :=
    hU.trans (nhdsWithin_mono _ (sdiff_subset_sdiff_right (fillH_mono subset_union_right)))
  -- the common collar: the integer is `0`
  obtain ⟨ρ, hρ, hagree⟩ := exists_ball_inter_eq_of_sameArc hp₁ hp₂ hq₁.le hq₂.le hσ₁τ.le hτ₁ hσ₂ hJ hm hβJ hs
  have hz₁ : α s ∈ α '' Icc 0 q₁ := ⟨s, ⟨zero_le, hsq.le⟩, rfl⟩
  have hz₂ : α s ∈ β '' Icc 0 q₂ := by
    have : α s ∈ β '' Icc σ₂ q₂ := by rw [hJ]; exact ⟨s, ⟨hs.1.le, hs.2.le⟩, rfl⟩
    exact image_mono (Icc_subset_Icc_left zero_le) this
  obtain ⟨-, -, -, -, hL⟩ := commonArcChart_of_approach α β x₁ x₂ W₁ W₂ ζ₁ ζ₂ hg₁ hW₁c hW₁0 hg₂ hW₂c hW₂0 hi₁
    hi₂ q₁ q₂ hq₁ hq₂ (zero_le.trans_lt hσ₁) hq₂0 hz₁ hρ hagree U hU
  -- the two own-chart limits are nonzero
  have hne₁ : α s ≠ α q₁ := fun h => hsq.ne (hi₁' ⟨zero_le, hsq.le⟩ ⟨zero_le, le_rfl⟩ h)
  have hne₂ : α s ≠ β q₂ := by
    rw [hβq]
    exact fun h => hs.2.ne (hi₁' ⟨zero_le, hsq.le⟩ ⟨zero_le, hτ₁⟩ h)
  obtain ⟨y₁, hy₁, hf₁⟩ := exists_real_ne_zero_tendsto_of_mem hg₁ hW₁c hW₁0 hi₁ hq₁ (zero_le.trans_lt hσ₁) hz₁
    hne₁ U hU₁
  obtain ⟨y₂, hy₂, hf₂⟩ := exists_real_ne_zero_tendsto_of_mem hg₂ hW₂c hW₂0 hi₂ hq₂ hq₂0 hz₂ hne₂ U hU₂
  obtain ⟨a₁, ha₁, h₁⟩ := hside₁.exists_tendsto U hU₁ hy₁ hf₁
  obtain ⟨a₂, ha₂, h₂⟩ := hside₂.exists_tendsto U hU₂ hy₂ hf₂
  exact false_of_sideHeights_of_signs (F := (U : Filter ℂ)) hκ hκ4 hθ hθπ ha₁ ha₂ (hv.mono_left hU) hL h₁ h₂

/-- **(RS13.3) for Aux. lemma 130**: the angle-varying path (final angle `θ₁`, `−π/2 ≤ θ₁ < π/2`) against the extremal
path of angle `π/2`. -/
theorem false_of_sameArc_sideHeights_half_pi (α β : ℝ≥0 → ℂ) (x₁ x₂ : ℝ) (W₁ W₂ : ℝ≥0 → ℝ) (ζ₁ ζ₂ : ℝ≥0∞)
    (hg₁ : IsGeneratingTrace W₁ ζ₁ (fun t => α t - x₁)) (hW₁c : ContinuousOn W₁ {s | (s : ℝ≥0∞) < ζ₁})
    (hW₁0 : W₁ 0 = 0) (hg₂ : IsGeneratingTrace W₂ ζ₂ (fun t => β t - x₂))
    (hW₂c : ContinuousOn W₂ {s | (s : ℝ≥0∞) < ζ₂}) (hW₂0 : W₂ 0 = 0)
    (hi₁ : InjOn α {t | (t : ℝ≥0∞) ≤ ζ₁}) (hi₂ : InjOn β {t | (t : ℝ≥0∞) ≤ ζ₂})
    {q₁ q₂ σ₁ σ₂ τ₁ : ℝ≥0} (hq₁ : (q₁ : ℝ≥0∞) < ζ₁) (hq₂ : (q₂ : ℝ≥0∞) < ζ₂) (hσ₁τ : σ₁ < τ₁) (hτ₁ : τ₁ ≤ q₁)
    (hσ₂ : σ₂ ≤ q₂) (hJ : β '' Icc σ₂ q₂ = α '' Icc σ₁ τ₁) (hm : β σ₂ = α σ₁) (hβq : β q₂ = α τ₁)
    (hβJ : ∀ t < σ₂, β t ∉ α '' Icc σ₁ q₁) (hJH : α '' Icc σ₁ q₁ ⊆ H)
    (htip : α q₁ ∈ closure (H \ fillH (α '' Icc 0 q₁ ∪ β '' Icc 0 q₂))) {s : ℝ≥0} (hs : s ∈ Ioo σ₁ τ₁)
    {κ θ₁ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ₁ : -(π / 2) ≤ θ₁) (hθ₁' : θ₁ < π / 2) {v₁ v₂ u₀ : ℂ → ℝ}
    (hside₁ : HasSideHeights κ θ₁ α x₁ W₁ q₁ (α s) v₁ u₀) (hside₂ : HasSideHeights κ (π / 2) β x₂ W₂ q₂ (α s) v₂ u₀)
    (hv : Tendsto (fun z => v₁ z - v₂ z) (𝓝[H \ fillH (α '' Icc 0 q₁ ∪ β '' Icc 0 q₂)] (α s)) (𝓝 0)) :
    False :=
  false_of_sameArc_sideHeights α β x₁ x₂ W₁ W₂ ζ₁ ζ₂ hg₁ hW₁c hW₁0 hg₂ hW₂c hW₂0 hi₁ hi₂ hq₁ hq₂ hσ₁τ hτ₁ hσ₂ hJ
    hm hβq hβJ hJH htip hs hκ hκ4 hθ₁'.ne (by rw [abs_le]; constructor <;> linarith) hside₁ hside₂ hv

end Assembly

end StripGeom

end Sec7

end InteractingSLE
