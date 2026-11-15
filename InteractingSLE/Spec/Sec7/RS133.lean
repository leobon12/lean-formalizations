/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripGeom

/-!
# (RS13.3) in full, pathwise: no terminal arc of `β = η_{π/2}` lies in the angle-varying path `α`

Packet PROVE-STRIPSYS19. Specification §7.4, proof of Aux. lemma 130 (`source/spec/p385-432.md` L440–L456, p. 411):

> The path `β` has points outside the complete range of `α` at arbitrarily late finite times. Here is the needed
> no-common-arc argument with its lift accounted for. If a terminal interval of `β` were in `α`, compact injectivity
> would identify each of its compact proper subarcs with a subarc of `α`. Close enough to `y`, that subarc is after the
> first change of `α`: the compact first prefix `α([0, 1])` avoids `y`. Their traversal directions agree by reverse
> first-visit order. […] Expressing both germs in one chart therefore forces `θ₁ − π/2 = 2πn`.  (RS13.3)

This is the `late` field of `StripSys.IsSelectionConfig`. PROVE-STRIPSYS12 proved the final contradiction
(`StripGeom.false_of_sameArc_sideHeights_half_pi`) from a same-direction common arc `β([σ₂, q₂]) = α([σ₁, τ₁])` and its
side and boundary data. This file supplies the remaining geometry, for one realization:

* **`isClosedEmbedding_of_transient`**: a continuous injective path tending to `∞` is a closed embedding (it is a proper
  map), so its range is closed and its inverse is continuous on the range;
* **`exists_sameArc_of_terminal`** ("compact injectivity would identify each of its compact proper subarcs with a subarc
  of `α` […] Their traversal directions agree by reverse first-visit order"): if a terminal interval of `β` lies in
  the range of `α`, and the first-visit time `T` of the counterflow decreases strictly along both paths, then for every
  late time `N` and every later stop `q₂` there is a same-direction common arc `β([σ₂, q₂]) = α([σ₁, τ₁])` with
  `σ₁ > t₀` ("after the first change of `α`") satisfying all geometric hypotheses of
  `false_of_sameArc_sideHeights(_half_pi)` (the other portions of `β` before `σ₂` avoid `α([σ₁, q₁])`, and `α` after
  `q₁` avoids both stopped ranges, by reverse first-visit order);
* **`late_of_sideHeights`** ((RS13.3) pathwise): given the side heights of `α` (angle `θ₁ ∈ [−π/2, π/2)`, at stops in
  an unbounded set `Q₁`, at its points after `t₀`) and of `β` (angle `π/2`, at stops in an unbounded set `Q₂`), and the
  nested local-set boundary agreement of the two means wherever the two stopped ranges locally coincide, `β` has points
  outside the complete range of `α` at arbitrarily late times.

The probabilistic inputs are exactly what holds almost surely at countably many rational stops: (S) for `α`
(`StripMark.ae_hasSideHeights_stage_of_lemma62`), the single-path side heights of the flow line `β`
(`Aux70.SinglePathSideHeightStatement`), and Proposition 3.8 for the two stopped ranges
(`SideHeightBox.ae_tendsto_sub_of_locals`); `T` is the counterflow first-visit time (`Aux130.firstVisit`, strictly
decreasing along each incoming path by `Aux130.firstVisit_lt_of_lt`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Bornology Function
open scoped NNReal ENNReal Real

open QuantumZipper (H)

namespace InteractingSLE

namespace Sec7

namespace RS133

open StripGeom Restart

/-! ### Transient injective paths are closed embeddings -/

section Embedding

variable {α : ℝ≥0 → ℂ}

/-- **A continuous injective path tending to `∞` is a closed embedding** (it is proper: the preimage of a compact set
is closed and bounded). -/
theorem isClosedEmbedding_of_transient (hc : Continuous α) (hi : Injective α)
    (hu : Tendsto (fun t => ‖α t‖) atTop atTop) : Topology.IsClosedEmbedding α := by
  have hp : IsProperMap α := by
    refine isProperMap_iff_isCompact_preimage.2 ⟨hc, fun K hK => ?_⟩
    obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hu.eventually_gt_atTop R)
    refine (isCompact_Icc (a := (0 : ℝ≥0)) (b := N)).of_isClosed_subset (hK.isClosed.preimage hc) fun t ht => ?_
    refine ⟨zero_le, le_of_not_gt fun hNt => ?_⟩
    exact (hN t hNt.le).not_ge (hR _ ht)
  exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap hc hi hp.isClosedMap

end Embedding

/-! ### A terminal interval in the other path gives a same-direction common arc -/

theorem zero_notMem_H (h : (0 : ℂ) ∈ H) : False := by
  have : (0 : ℝ) < (0 : ℂ).im := h
  simp at this

section SameArc

variable {α β : ℝ≥0 → ℂ}

/-- **The same-direction common arc of a terminal interval** (compact injectivity and reverse first-visit order). Let
`α`, `β` be continuous injective paths from `0`, in `ℍ` at positive times, tending to `∞`, and let `T` decrease
strictly along both on `(0, ∞)`. If `β([N, ∞))` lies in the closure of the range of `α`, then for all `t₀` there are
`N' ≥ N` and, for every `q₂ > N'` and every `q₁ ≥ φ(q₂)`, a common arc `β([N', q₂]) = α([σ₁, τ₁])` traversed in the
same direction, with `t₀ < σ₁`, satisfying the geometric hypotheses of `false_of_sameArc_sideHeights`. -/
theorem exists_sameArc_of_terminal (T : ℂ → ℝ≥0∞) (hαc : Continuous α) (hβc : Continuous β)
    (hαi : Injective α) (hβ0 : β 0 = 0) (hαH : ∀ t, 0 < t → α t ∈ H)
    (hαu : Tendsto (fun t => ‖α t‖) atTop atTop)
    (hβu : Tendsto (fun t => ‖β t‖) atTop atTop)
    (hTα : StrictAntiOn (fun t => T (α t)) (Ioi 0)) (hTβ : StrictAntiOn (fun t => T (β t)) (Ioi 0))
    {N : ℝ≥0} (hN : ∀ t, N ≤ t → β t ∈ closure (range α)) (t₀ : ℝ≥0) :
    ∃ N' : ℝ≥0, N ≤ N' ∧ 0 < N' ∧ ∃ φ : ℝ≥0 → ℝ≥0, (∀ t, N' ≤ t → β t = α (φ t) ∧ t₀ < φ t) ∧
      StrictMonoOn φ (Ici N') ∧ ∀ q₂ q₁ : ℝ≥0, N' < q₂ → φ q₂ ≤ q₁ →
        β '' Icc N' q₂ = α '' Icc (φ N') (φ q₂) ∧ (∀ t < N', β t ∉ α '' Icc (φ N') q₁) ∧
        α '' Icc (φ N') q₁ ⊆ H ∧ α q₁ ∈ closure (H \ fillH (α '' Icc 0 q₁ ∪ β '' Icc 0 q₂)) := by
  classical
  have hemb := isClosedEmbedding_of_transient hαc hαi hαu
  have hcl : closure (range α) = range α := hemb.isClosed_range.closure_eq
  -- late times avoid the first prefix `α([0, t₀])`
  obtain ⟨R, hR⟩ := (isCompact_Icc.image hαc : IsCompact (α '' Icc 0 t₀)).isBounded.exists_norm_le
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hβu.eventually_gt_atTop R)
  set N' : ℝ≥0 := max (max N N₀) 1 with hN'def
  have hNN' : N ≤ N' := (le_max_left _ _).trans (le_max_left _ _)
  have hN₀N' : N₀ ≤ N' := (le_max_right _ _).trans (le_max_left _ _)
  have hN'pos : 0 < N' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set φ : ℝ≥0 → ℝ≥0 := fun t => invFun α (β t) with hφdef
  have hφ : ∀ t, N' ≤ t → β t = α (φ t) ∧ t₀ < φ t := by
    intro t ht
    have hmem : β t ∈ range α := hcl ▸ hN t (hNN'.trans ht)
    have he : α (φ t) = β t := invFun_eq hmem
    refine ⟨he.symm, lt_of_not_ge fun hle => ?_⟩
    have h1 := hR (α (φ t)) ⟨φ t, ⟨zero_le, hle⟩, rfl⟩
    rw [he] at h1
    exact (hN₀ t (hN₀N'.trans ht)).not_ge h1
  have hpos : ∀ t, N' ≤ t → 0 < φ t := fun t ht => lt_of_le_of_lt zero_le (hφ t ht).2
  -- `φ` increases: reverse first-visit order along both paths
  have hmono : StrictMonoOn φ (Ici N') := by
    intro t ht t' ht' htt'
    refine lt_of_not_ge fun hle => ?_
    have h1 : T (β t') < T (β t) :=
      hTβ (lt_of_lt_of_le hN'pos ht) (lt_of_lt_of_le hN'pos ht') htt'
    rw [(hφ t ht).1, (hφ t' ht').1] at h1
    exact h1.not_ge (hTα.antitoneOn (hpos t' ht') (hpos t ht) hle)
  -- `φ` is continuous: the inverse of a closed embedding
  have hφc : ContinuousOn φ (Ici N') := by
    rw [hemb.isInducing.continuousOn_iff]
    exact hβc.continuousOn.congr fun t ht => ((hφ t ht).1).symm
  refine ⟨N', hNN', hN'pos, φ, hφ, hmono, fun q₂ q₁ hq₂ hq₁ => ?_⟩
  have hσ₁pos : 0 < φ N' := hpos N' le_rfl
  have hσ₁τ : φ N' < φ q₂ := hmono (le_refl N') (show N' ≤ q₂ from le_of_lt hq₂) hq₂
  refine ⟨?_, fun t ht => ?_, ?_, ?_⟩
  · -- the common arc
    have himg : φ '' Icc N' q₂ = Icc (φ N') (φ q₂) := by
      refine Subset.antisymm ?_ (intermediate_value_Icc hq₂.le (hφc.mono fun t ht => ht.1))
      rintro _ ⟨t, ht, rfl⟩
      exact ⟨hmono.monotoneOn (le_refl N') (show N' ≤ t from ht.1) ht.1,
        hmono.monotoneOn (show N' ≤ t from ht.1) (show N' ≤ q₂ from hq₂.le) ht.2⟩
    rw [← himg, image_image]
    exact image_congr fun t ht => (hφ t ht.1).1
  · -- the earlier portions of `β` avoid the arc `α([σ₁, q₁])`
    rintro ⟨u, hu, he⟩
    have hupos : 0 < u := lt_of_lt_of_le hσ₁pos hu.1
    rcases eq_or_lt_of_le (zero_le : 0 ≤ t) with rfl | htpos
    · have h0H : (0 : ℂ) ∈ H := by rw [← hβ0, ← he]; exact hαH u hupos
      exact zero_notMem_H h0H
    · have h1 : T (β N') < T (β t) := hTβ htpos hN'pos ht
      rw [(hφ N' le_rfl).1, ← he] at h1
      exact h1.not_ge (hTα.antitoneOn hσ₁pos hupos hu.1)
  · rintro _ ⟨u, hu, rfl⟩
    exact hαH u (lt_of_lt_of_le hσ₁pos hu.1)
  · -- the tip is exposed: `α` continues to `∞` avoiding both stopped ranges
    have hτpos : 0 < φ q₂ := hpos q₂ hq₂.le
    have hΓ : IsClosed (α '' Icc 0 q₁ ∪ β '' Icc 0 q₂) :=
      ((isCompact_Icc.image hαc).union (isCompact_Icc.image hβc)).isClosed
    refine tip_mem_closure_H_diff_fillH_of_continuation hΓ hαc.continuousOn ?_ ?_
    · intro hb
      obtain ⟨R', hR'⟩ := hb.exists_norm_le
      obtain ⟨M, hM⟩ := eventually_atTop.1 (hαu.eventually_gt_atTop R')
      have := hR' (α (max M (q₁ + 1))) ⟨max M (q₁ + 1), lt_of_lt_of_le (lt_add_one q₁) (le_max_right _ _), rfl⟩
      exact (hM _ (le_max_left _ _)).not_ge this
    · rintro _ ⟨u, hu, rfl⟩
      have hupos : 0 < u := lt_of_le_of_lt zero_le hu
      refine ⟨hαH u hupos, ?_⟩
      rintro (⟨u', hu', he⟩ | ⟨t, ht, he⟩)
      · exact (hu.trans_le' hu'.2).ne' (hαi he).symm |>.elim
      · rcases eq_or_lt_of_le (zero_le : 0 ≤ t) with rfl | htpos
        · have h0H : (0 : ℂ) ∈ H := by rw [← hβ0, he]; exact hαH u hupos
          exact zero_notMem_H h0H
        · have h1 : T (α u) < T (α (φ q₂)) := hTα hτpos hupos (lt_of_le_of_lt hq₁ hu)
          rw [← (hφ q₂ hq₂.le).1, ← he] at h1
          exact h1.not_ge (hTβ.antitoneOn htpos (hN'pos.trans hq₂) ht.2)

/-- **(RS13.3), pathwise: `β` has points outside the complete range of `α` at arbitrarily late times** (the `late`
field of `StripSys.IsSelectionConfig`). For one realization: `α` (the angle-varying path, angle `θ₁ ∈ [−π/2, π/2)` after
own time `t₀`) and `β = η_{π/2}` are simple generating traces from `0` of continuous drivers `W₁`, `W₂`, in `ℍ` at
positive times, tending to `∞`; the counterflow first-visit time `T` decreases strictly along both; at the stops in the
unbounded sets `Q₁`, `Q₂` the stopped means `v₁ q₁`, `v₂ q₂` have the single-path side heights (`α` at its points after
`t₀`, `β` at all its points) and agree at the boundary at every common point where the two stopped ranges locally
coincide (nested local-set boundary comparison). Then a terminal interval of `β` in `α` would give a same-direction
common arc (`exists_sameArc_of_terminal`) on which `StripGeom.false_of_sameArc_sideHeights_half_pi` applies. -/
theorem late_of_sideHeights {W₁ W₂ : ℝ≥0 → ℝ} (T : ℂ → ℝ≥0∞)
    (hg₁ : IsGeneratingTrace W₁ ⊤ α) (hW₁c : Continuous W₁) (hW₁0 : W₁ 0 = 0)
    (hg₂ : IsGeneratingTrace W₂ ⊤ β) (hW₂c : Continuous W₂) (hW₂0 : W₂ 0 = 0)
    (hαi : Injective α) (hβi : Injective β) (hαH : ∀ t, 0 < t → α t ∈ H)
    (hαu : Tendsto (fun t => ‖α t‖) atTop atTop) (hβu : Tendsto (fun t => ‖β t‖) atTop atTop)
    (hTα : StrictAntiOn (fun t => T (α t)) (Ioi 0)) (hTβ : StrictAntiOn (fun t => T (β t)) (Ioi 0))
    {κ θ₁ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ₁ : -(π / 2) ≤ θ₁) (hθ₁' : θ₁ < π / 2) {u₀ : ℂ → ℝ}
    {t₀ : ℝ≥0} {Q₁ Q₂ : Set ℝ≥0} (hQ₁ : ∀ a, ∃ q ∈ Q₁, a ≤ q) (hQ₂ : ∀ a, ∃ q ∈ Q₂, a < q)
    {v₁ v₂ : ℝ≥0 → ℂ → ℝ}
    (hside₁ : ∀ q ∈ Q₁, ∀ s, t₀ < s → s < q → HasSideHeights κ θ₁ α 0 W₁ q (α s) (v₁ q) u₀)
    (hside₂ : ∀ q ∈ Q₂, ∀ s, 0 < s → s < q → HasSideHeights κ (π / 2) β 0 W₂ q (β s) (v₂ q) u₀)
    (hloc : ∀ q₁ ∈ Q₁, ∀ q₂ ∈ Q₂, ∀ z₀ ∈ α '' Icc 0 q₁ ∩ H, z₀ ∈ β '' Icc 0 q₂ ∩ H →
      (∃ r > 0, β '' Icc 0 q₂ ∩ H ∩ ball z₀ r ⊆ α '' Icc 0 q₁ ∩ H) →
      (∃ r > 0, α '' Icc 0 q₁ ∩ H ∩ ball z₀ r ⊆ β '' Icc 0 q₂ ∩ H) →
      Tendsto (fun z => v₁ q₁ z - v₂ q₂ z) (𝓝[H \ (α '' Icc 0 q₁ ∩ H ∪ β '' Icc 0 q₂ ∩ H)] z₀) (𝓝 0)) :
    ∀ N : ℝ≥0, ∃ t, N ≤ t ∧ β t ∉ closure (range α) := by
  intro N
  by_contra hcon
  push Not at hcon
  have hαc : Continuous α :=
    continuousOn_univ.1 (hg₁.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hβc : Continuous β :=
    continuousOn_univ.1 (hg₂.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  obtain ⟨N', -, hN'pos, φ, hφ, hmono, harc⟩ :=
    exists_sameArc_of_terminal T hαc hβc hαi hg₂.1 hαH hαu hβu hTα hTβ hcon t₀
  obtain ⟨q₂, hq₂Q, hq₂⟩ := hQ₂ N'
  obtain ⟨q₁, hq₁Q, hq₁⟩ := hQ₁ (φ q₂)
  obtain ⟨hJ, hβJ, hJH, htip⟩ := harc q₂ q₁ hq₂ hq₁
  have hσ₁τ : φ N' < φ q₂ := hmono (le_refl N') (show N' ≤ q₂ from hq₂.le) hq₂
  obtain ⟨s, hs1, hs2⟩ := exists_between hσ₁τ
  -- the point `α s` of the common arc as a point of `β`
  have hαs : α s ∈ β '' Icc N' q₂ := by rw [hJ]; exact ⟨s, ⟨hs1.le, hs2.le⟩, rfl⟩
  obtain ⟨t', ht', hβt'⟩ := hαs
  have ht'q : t' < q₂ := by
    refine lt_of_le_of_ne ht'.2 fun h => ?_
    rw [h, (hφ q₂ hq₂.le).1] at hβt'
    exact hs2.ne (hαi hβt').symm
  have hs₂ := hside₂ q₂ hq₂Q t' (lt_of_lt_of_le hN'pos ht'.1) ht'q
  rw [hβt'] at hs₂
  have hαsH : α s ∈ H := hαH s (lt_of_le_of_lt zero_le hs1)
  have hs₁ := hside₁ q₁ hq₁Q s (((hφ N' le_rfl).2).trans hs1) (hs2.trans_le hq₁)
  have hg₁' : IsGeneratingTrace W₁ ⊤ fun t => α t - ((0 : ℝ) : ℂ) := by simpa using hg₁
  have hg₂' : IsGeneratingTrace W₂ ⊤ fun t => β t - ((0 : ℝ) : ℂ) := by simpa using hg₂
  have hp₁ : IsPathGood α ⊤ 0 := ⟨hαi.injOn, W₁, hW₁c.continuousOn, hW₁0, hg₁'⟩
  have hp₂ : IsPathGood β ⊤ 0 := ⟨hβi.injOn, W₂, hW₂c.continuousOn, hW₂0, hg₂'⟩
  have hv := tendsto_sub_of_sameArc_of_locals hp₁ hp₂ le_top le_top hσ₁τ.le hq₁ hq₂.le hJ (hφ N' le_rfl).1 hβJ
    ⟨hs1, hs2⟩ (hloc q₁ hq₁Q q₂ hq₂Q (α s) ⟨⟨s, ⟨zero_le, (hs2.trans_le hq₁).le⟩, rfl⟩, hαsH⟩
      ⟨⟨t', ⟨zero_le, ht'.2⟩, hβt'⟩, hαsH⟩)
  exact false_of_sameArc_sideHeights_half_pi α β 0 0 W₁ W₂ ⊤ ⊤ hg₁' hW₁c.continuousOn hW₁0 hg₂'
    hW₂c.continuousOn hW₂0 hαi.injOn hβi.injOn ENNReal.coe_lt_top ENNReal.coe_lt_top hσ₁τ hq₁ hq₂.le hJ
    (hφ N' le_rfl).1 (hφ q₂ hq₂.le).1 hβJ hJH htip ⟨hs1, hs2⟩ hκ hκ4 hθ₁ hθ₁' hs₁ hs₂ hv

end SameArc

end RS133

end Sec7

end InteractingSLE
