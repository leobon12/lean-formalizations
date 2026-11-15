/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma76ExitChart
import InteractingSLE.Spec.Sec7.Lemma77Conf

/-!
# Lemma 7.6: moving a forbidden first exit to good rational stops

Packet PROVE-LEMMA76D, part (b). Specification §7.2, proof of Lemma 7.6 (pp. 267–270). The proof is "conditional on
the two retained histories" at the given stops; Lemma 7.6 is applied at stops `τ̃₁ ≤ T₁`, `τ̃₂ ≤ T₂` which may be the
lifetimes, and with a second tip that may be real. Here every forbidden first exit at the stops `(A, B)` (e.g.
`A = r ∧ ζ₁`, `B = t ∧ ζ₂`) is moved to rational stops `(a', b')` with `u < a' < A`, `B < b' < e` at which the
configuration is good (`IsDisjointPair`): both stops strictly before the lifetimes, the second tip interior, disjoint
prefixes, both tips accessible from the joint unbounded domain; and the exit is still forbidden there, with the first
tip `α(a')` itself as the witness inside the Jordan curve.

## Main results

* `IsDisjointPair`: the good configuration at deterministic stops;
* `mapsTo_jordanIn_of_isForbiddenExit`: the onward first path `α((u, A])` lies inside the Jordan curve;
* `tip_mem_closure`: the tip of a good path is accessible from its own unbounded domain;
* **`exists_rat_isDisjointPair_of_not_firstExitBarrier`**: a failed barrier at `(A, B)` gives rational stops with a
  good configuration and a forbidden exit whose witness is the first tip.

## Mathematical steps

* Moving the first stop down to `a' ∈ (u, A)` only shrinks the removed set, so the joint unbounded domain grows
  (`fillH_mono`); the witness `α(a')` is inside the curve since `α((u, A])` is a connected set off the curve meeting
  the inside.
* Moving the second stop up to `b' ∈ (B, e)` adds the slit `β([B, b'])`, which meets `α([0, A]) ∪ β([0, B])` and the
  closed lower half-plane only at `β(B)`; a point of the old unbounded domain off the slit stays in the unbounded
  domain (`mem_H_diff_fillH_union_of_mem_jordanOut`, the complement of an arc being connected).
* The new second tip `β(b')` is a limit of `β((b', e)) ⊆ D`.
* The new first tip `α(a')` is a limit of the unbounded domain of `α([0, a'])` (tip property of the generating
  trace); `β([0, b'])` is free along `α([0, A])` (the label is constant along a connected set, and `α(u) = β(e)` is a
  limit of `D`); Janiszewski's theorem in `ℍ` (`H_diff_fillH_inter_subset`, disjoint sets) puts the nearby points of
  both unbounded domains in `D`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Sec7

namespace Lemma76Exit

/-- **The good configuration at deterministic stops `(a, b)`** for the restart of Lemma 7.6: both stops strictly
before the lifetimes, the second tip interior, the prefixes disjoint, and both tips accessible from the joint
unbounded domain `activeDomain α a β b`. -/
def IsDisjointPair (α : ℝ≥0 → ℂ) (ζ₁ : ℝ≥0∞) (a : ℝ≥0) (β : ℝ≥0 → ℂ) (ζ₂ : ℝ≥0∞) (b : ℝ≥0) : Prop :=
  (a : ℝ≥0∞) < ζ₁ ∧ (b : ℝ≥0∞) < ζ₂ ∧ β b ∈ H ∧ Disjoint (α '' Icc 0 a) (β '' Icc 0 b) ∧
    β b ∈ closure (activeDomain α a β b) ∧ α a ∈ closure (activeDomain α a β b)

section GoodPath

variable {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ}

/-- **The tip of a good path is accessible from its own unbounded domain.** -/
theorem tip_mem_closure (hp : Restart.IsPathGood η ζ x) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    η t ∈ closure (H \ fillH (η '' Icc 0 t)) := by
  obtain ⟨-, w, hw, hw0, hg⟩ := hp
  have h := Restart.IsGeneratingTrace.mem_closure_self hg hw hw0 ht
  have he : Continuous fun z : ℂ => z + x := by fun_prop
  have h1 := image_closure_subset_closure_image he ⟨_, h, rfl⟩
  simp only [sub_add_cancel] at h1
  refine closure_mono ?_ h1
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨show (0 : ℝ) < (z + x).im by simpa using (show (0 : ℝ) < z.im from hz.1), ?_⟩
  rw [← Restart.image_add_real_eq η x, Restart.fillH_image_add_real]
  rintro ⟨z', hz', hzz'⟩
  exact hz.2 (by rwa [add_left_inj] at hzz' ▸ hz')

end GoodPath

/-- The complement of an arc lies outside it. -/
theorem compl_image_Icc_subset_jordanOut {η : ℝ≥0 → ℂ} {s r : ℝ≥0} (hsr : s < r)
    (hc : ContinuousOn η (Icc s r)) (hi : InjOn η (Icc s r)) :
    (η '' Icc s r)ᶜ ⊆ WangWu.jordanOut (η '' Icc s r) := by
  have hK : IsCompact (η '' Icc s r) := isCompact_Icc.image_of_continuousOn hc
  refine WangWu.subset_jordanOut_of_isPreconnected (isPreconnected_compl_image_Icc hsr hc hi) ?_
    disjoint_compl_left
  intro hb
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall 0).1 (hK.isBounded.union hb)
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z ∉ closedBall (0 : ℂ) R :=
    ⟨((|R| + 1 : ℝ) : ℂ), by
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith [le_abs_self R]⟩
  by_cases hzK : z ∈ η '' Icc s r
  · exact hz (hR (Or.inl hzK))
  · exact hz (hR (Or.inr hzK))

/-! ### Moving the stops -/

section Reduce

variable {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ}

/-- **A failed barrier gives good rational stops with a forbidden exit** (the reduction of Lemma 7.6 at arbitrary
stops `(A, B)`, `A ≤ ζ₁`, to the good configurations `IsDisjointPair` at rational stops, with the first tip as the
witness inside the Jordan curve). -/
theorem exists_rat_isDisjointPair_of_not_firstExitBarrier (hp₁ : Restart.IsPathGood α ζ₁ x₁)
    (hp₂ : Restart.IsPathGood β ζ₂ x₂) {A B : ℝ≥0} (hA : (A : ℝ≥0∞) ≤ ζ₁)
    (hbar : ¬ FirstExitBarrier α A β ζ₂ B (lowerArc x₂ x₁)) :
    ∃ q₁ q₂ : ℚ, IsDisjointPair α ζ₁ (q₁ : ℝ).toNNReal β ζ₂ (q₂ : ℝ).toNNReal ∧
      ∃ e u : ℝ≥0, (e : ℝ≥0∞) ≤ ζ₂ ∧
        IsForbiddenExit α (q₁ : ℝ).toNNReal β (q₂ : ℝ).toNNReal e u (q₁ : ℝ).toNNReal (lowerArc x₂ x₁) := by
  unfold FirstExitBarrier at hbar
  push Not at hbar
  obtain ⟨hdisj, -, e, u, v, he, hBe, huv, hvA, hpath, hβe, hjord⟩ := hbar
  have hBζ : (B : ℝ≥0∞) ≤ ζ₂ := (ENNReal.coe_le_coe.2 hBe.le).trans he
  have hα0 : α 0 = x₁ := IsPathGood.zero hp₁
  have hβ0 : β 0 = x₂ := IsPathGood.zero hp₂
  have hαc := IsPathGood.continuousOn_Icc hp₁ hA
  have hαi := IsPathGood.injOn_Icc hp₁ hA
  have hβc := IsPathGood.continuousOn_Icc hp₂ he
  have hβi := IsPathGood.injOn_Icc hp₂ he
  set K₀ := α '' Icc 0 A ∪ β '' Icc 0 B with hK₀
  have hK₀c : IsCompact K₀ :=
    (IsPathGood.isCompact_image_Icc hp₁ hA).union (IsPathGood.isCompact_image_Icc hp₂ hBζ)
  rw [unboundedPart_eq hK₀c.isClosed] at hpath
  have hD₀K : ∀ z ∈ H \ fillH K₀, z ∉ K₀ := fun z hz =>
    (HalfPlaneSep.H_diff_fillH_subset_H_diff hK₀c.isClosed hz).2
  have hβα : ∀ t ∈ Ioo B e, β t ∉ α '' Icc 0 A := fun t ht h => hD₀K _ (hpath t ht) (Or.inl h)
  have huA : u < A := huv.trans_le hvA
  -- the onward first path is inside the Jordan curve
  set J := α '' Icc 0 u ∪ β '' Icc 0 e ∪ lowerArc x₂ x₁ with hJ
  have hin : ∀ s ∈ Ioc u A, α s ∈ WangWu.jordanIn J := by
    have hpc : IsPreconnected (α '' Ioc u A) :=
      isPreconnected_Ioc.image _ (hαc.mono fun s hs => ⟨zero_le, hs.2⟩)
    have hoff : α '' Ioc u A ⊆ Jᶜ := by
      rintro _ ⟨s, hs, rfl⟩ hJs
      have hsA : s ∈ Icc 0 A := ⟨zero_le, hs.2⟩
      rcases hJs with (⟨s', hs', hss'⟩ | ⟨t, ht, hts⟩) | hL
      · have h := hαi ⟨zero_le, hs'.2.trans huA.le⟩ hsA hss'
        rw [h] at hs'
        exact absurd hs.1 (not_lt.2 hs'.2)
      · rcases le_or_gt t B with htB | htB
        · exact Set.disjoint_left.1 hdisj ⟨s, hsA, rfl⟩ ⟨t, ⟨zero_le, htB⟩, hts⟩
        rcases eq_or_lt_of_le ht.2 with hte | hte
        · rw [hte, hβe] at hts
          have h := hαi ⟨zero_le, huA.le⟩ hsA hts
          rw [h] at hs
          exact lt_irrefl s hs.1
        · exact hβα t ⟨htB, hte⟩ ⟨s, hsA, hts.symm⟩
      · obtain ⟨hle, hreal⟩ := im_le_zero_of_mem_lowerArc hL
        have him : (α s).im = 0 :=
          le_antisymm hle (IsPathGood.im_nonneg hp₁ ((ENNReal.coe_le_coe.2 hs.2).trans hA))
        rcases hreal him with h1 | h2
        · have h := hαi ⟨le_rfl, zero_le⟩ hsA (hα0.trans h1.symm)
          rw [← h] at hs
          exact absurd hs.1 (not_lt.2 zero_le)
        · exact Set.disjoint_left.1 hdisj ⟨s, hsA, rfl⟩ ⟨0, ⟨le_rfl, zero_le⟩, hβ0.trans h2.symm⟩
    intro s hs
    have hsv := hpc.subset_connectedComponentIn ⟨v, ⟨huv, hvA⟩, rfl⟩ hoff ⟨s, hs, rfl⟩
    refine ⟨hoff ⟨s, hs, rfl⟩, ?_⟩
    rw [← connectedComponentIn_eq hsv]
    exact hjord.2
  -- the rational stops
  obtain ⟨q₁, hq₁u, hq₁A⟩ := exists_rat_toNNReal_btwn huA
  obtain ⟨q₂, hq₂B, hq₂e⟩ := exists_rat_toNNReal_btwn hBe
  refine ⟨q₁, q₂, ?_⟩
  set a' := (q₁ : ℝ).toNNReal with ha'
  set b' := (q₂ : ℝ).toNNReal with hb'
  have ha'A : a' ≤ A := hq₁A.le
  have hb'ζ : (b' : ℝ≥0∞) ≤ ζ₂ := (ENNReal.coe_le_coe.2 hq₂e.le).trans he
  set K := α '' Icc 0 a' ∪ β '' Icc 0 b' with hKdef
  have hKc : IsCompact K :=
    (IsPathGood.isCompact_image_Icc hp₁ ((ENNReal.coe_le_coe.2 ha'A).trans hA)).union
      (IsPathGood.isCompact_image_Icc hp₂ hb'ζ)
  have hact : activeDomain α a' β b' = H \ fillH K := unboundedPart_eq hKc.isClosed
  -- the slit `β([B, b'])`
  set G := β '' Icc B b' with hG
  have hGc : IsCompact G := IsPathGood.isCompact_image_Icc hp₂ hb'ζ
  have hsplit : β '' Icc 0 b' = β '' Icc 0 B ∪ G := by
    rw [hG, ← image_union, Icc_union_Icc_eq_Icc zero_le hq₂B.le]
  have hKsub : K ⊆ K₀ ∪ G := by
    rintro z (hz | hz)
    · exact Or.inl (Or.inl (image_mono (Icc_subset_Icc_right ha'A) hz))
    · rw [hsplit] at hz
      rcases hz with hz | hz
      · exact Or.inl (Or.inr hz)
      · exact Or.inr hz
  have hGD : ∀ t ∈ Ioc B b', β t ∈ H \ fillH K₀ := fun t ht => hpath t ⟨ht.1, ht.2.trans_lt hq₂e⟩
  obtain ⟨R, hR0, hRb⟩ := (hK₀c.union hGc).isBounded.subset_ball_lt 0 0
  have hGint : (K₀ ∪ HalfPlaneSep.lowerDisc R) ∩ G = {β B} := by
    ext z
    constructor
    · rintro ⟨hz, ⟨t, ht, rfl⟩⟩
      rcases eq_or_lt_of_le ht.1 with h | h
      · rw [← h]; exact mem_singleton _
      · exfalso
        have hD := hGD t ⟨h, ht.2⟩
        rcases hz with hz | hz
        · exact hD₀K _ hD hz
        · exact HalfPlaneSep.notMem_lowerDisc_of_mem_H hD.1 hz
    · rintro rfl
      exact ⟨Or.inl (Or.inr ⟨B, ⟨zero_le, le_rfl⟩, rfl⟩), ⟨B, ⟨le_rfl, hq₂B.le⟩, rfl⟩⟩
  have hslit : ∀ z ∈ H \ fillH K₀, z ∉ G → z ∈ H \ fillH K := by
    intro z hz hzG
    have h1 := mem_H_diff_fillH_union_of_mem_jordanOut hK₀c hGc hR0 (subset_union_left.trans hRb)
      (subset_union_right.trans hRb) (by rw [hGint]; exact isPreconnected_singleton) hz
      (compl_image_Icc_subset_jordanOut hq₂B (hβc.mono (Icc_subset_Icc zero_le hq₂e.le))
        (hβi.mono (Icc_subset_Icc zero_le hq₂e.le)) hzG)
    exact ⟨h1.1, fun h => h1.2 (fillH_mono hKsub h)⟩
  -- the continuation stays in the new domain
  have hpath' : ∀ s ∈ Ioo b' e, β s ∈ H \ fillH K := by
    intro s hs
    refine hslit _ (hpath s ⟨hq₂B.trans hs.1, hs.2⟩) ?_
    rintro ⟨t, ht, hts⟩
    have h := hβi ⟨zero_le, ht.2.trans hq₂e.le⟩ ⟨zero_le, hs.2.le⟩ hts
    rw [h] at ht
    exact absurd hs.1 (not_lt.2 ht.2)
  -- disjointness of the new prefixes
  have hdisjA : Disjoint (α '' Icc 0 A) (β '' Icc 0 b') := by
    rw [hsplit, Set.disjoint_union_right]
    refine ⟨hdisj, Set.disjoint_left.2 ?_⟩
    rintro _ hα ⟨t, ht, rfl⟩
    rcases eq_or_lt_of_le ht.1 with h | h
    · exact Set.disjoint_left.1 hdisj hα ⟨B, ⟨zero_le, le_rfl⟩, by rw [h]⟩
    · exact hβα t ⟨h, ht.2.trans_lt hq₂e⟩ hα
  have hdisj' : Disjoint (α '' Icc 0 a') (β '' Icc 0 b') :=
    hdisjA.mono_left (image_mono (Icc_subset_Icc_right ha'A))
  -- the second tip and the exit point are limits of the continuation
  have hlim : ∀ s ∈ Icc b' e, β s ∈ closure (H \ fillH K) := by
    intro s hs
    have hcw : ContinuousWithinAt β (Ioo b' e) s :=
      (hβc s ⟨zero_le, hs.2⟩).mono fun t ht => ⟨zero_le, ht.2.le⟩
    have h1 : s ∈ closure (Ioo b' e) := by rw [closure_Ioo hq₂e.ne]; exact hs
    refine closure_mono ?_ (hcw.mem_closure_image h1)
    rintro _ ⟨t, ht, rfl⟩
    exact hpath' t ht
  have hb'D : β b' ∈ H \ fillH K₀ := hGD b' ⟨hq₂B, le_rfl⟩
  have hclu : α u ∈ closure (H \ fillH K) := hβe ▸ hlim e ⟨hq₂e.le, le_rfl⟩
  -- the first tip: free for the second prefix along the first path, then Janiszewski
  set Fβ := β '' Icc 0 b' with hFβ
  have hFβc : IsCompact Fβ := IsPathGood.isCompact_image_Icc hp₂ hb'ζ
  have hfree : ∀ s ∈ Icc 0 A, HalfPlaneSep.IsFreeAt Fβ (α s) := by
    have hX : IsPreconnected (α '' Icc 0 A) := isPreconnected_Icc.image _ hαc
    have hXF : α '' Icc 0 A ⊆ {w | 0 ≤ w.im} \ Fβ := by
      rintro _ ⟨s, hs, rfl⟩
      exact ⟨IsPathGood.im_nonneg hp₁ ((ENNReal.coe_le_coe.2 hs.2).trans hA),
        fun h => Set.disjoint_left.1 hdisjA ⟨s, hs, rfl⟩ h⟩
    rcases HalfPlaneSep.isFreeAt_or_isTrappedAt_of_isPreconnected hFβc.isClosed hX hXF with h | h
    · exact fun s hs => h _ ⟨s, hs, rfl⟩
    · exfalso
      obtain ⟨ε, hε, hdis⟩ := h (α u) ⟨u, ⟨zero_le, huA.le⟩, rfl⟩
      obtain ⟨z, hz, hzu⟩ := Metric.mem_closure_iff.1 hclu ε hε
      refine Set.disjoint_left.1 hdis (show z ∈ ball (α u) ε by rw [mem_ball, dist_comm]; exact hzu) ?_
      exact ⟨hz.1, fun h => hz.2 (fillH_mono subset_union_right h)⟩
  have hcla : α a' ∈ closure (H \ fillH K) := by
    have ha'ζ : (a' : ℝ≥0∞) < ζ₁ := (ENNReal.coe_lt_coe.2 hq₁A).trans_le hA
    have h2 := HalfPlaneSep.mem_closure_inter_of_isFreeAt (tip_mem_closure hp₁ ha'ζ) (fun _ h => h.1)
      (hfree a' ⟨zero_le, ha'A⟩)
    refine closure_mono ?_ h2
    rintro z ⟨hz1, hz2⟩
    exact HalfPlaneSep.H_diff_fillH_inter_subset
      (IsPathGood.isCompact_image_Icc hp₁ ((ENNReal.coe_le_coe.2 ha'A).trans hA)) hFβc
      (fun w hw => (Set.disjoint_left.1 hdisj' hw.1 hw.2).elim) ⟨hz1, hz2⟩
  refine ⟨⟨(ENNReal.coe_lt_coe.2 hq₁A).trans_le hA, (ENNReal.coe_lt_coe.2 hq₂e).trans_le he, hb'D.1,
    hdisj', by rw [hact]; exact hlim b' ⟨le_rfl, hq₂e.le⟩, by rw [hact]; exact hcla⟩,
    e, u, he, hq₂e, hq₁u, le_rfl, ?_, hβe, hin a' ⟨hq₁u, ha'A⟩⟩
  rw [unboundedPart_eq hKc.isClosed]
  exact hpath'

end Reduce

end Lemma76Exit

end Sec7

end InteractingSLE
