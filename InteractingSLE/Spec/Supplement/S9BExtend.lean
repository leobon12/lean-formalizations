/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S9BJoint

/-!
# Supplement §9, Lemma W4: extending the first path without a new contact

Packet PROVE-SUPP9-C. Lemma W4 (supplement p. 532) for the first (right) path: if `𝓔(α([0, a]), β([0, c]))` holds
and `α([a, a'])` avoids `β([0, c])`, then `𝓔(α([0, a']), β([0, c]))`, provided `α([0, a'])` has a slit completion
(a proper completion whose new points lie in `ℍ` off `α([0, a'])`: the Loewner slit) and one of the two tips lies in
the closure of the joint domain.

*Proof.*
* If the tip `α(a')` is in the closure of the joint domain, a tail from it inside the joint domain
  (`exists_tail_of_mem_closure_jointDomain`) completes `α([0, a'])` avoiding `β([0, c])`; the transfer lemma of
  PROVE-SUPP9-B (`hasOrderedProperCompletions_of_completion`) applies.
* Otherwise the tip `β(c)` is. A tail `T` from it inside the joint domain completes `β([0, c])` to `β^T`, whose tail
  avoids `α([0, a'])`; the reflected transfer lemma gives a completion `α°` of `α([0, a])` with `(α°, β^T)` ordered
  (`exists_completion_left_of_tail`). Follow the slit `S` of `α(a')` until it first meets `β^T`, at `β^T(v*)`, and then
  follow `β^T`. This is injective because every old contact `α(x) = β(y)` has `y < v*`
  (`lt_of_slit_hit`): otherwise, with the last old contact `q = α(s_q) = β(v_q)`, the curve `δ` following `α°` to `q`
  and then `β^T` is proper (contact order), lies in the closed left side of `α°`, so `α°` lies in its closed right side
  (duality); but `β^T(v*)` is on the left of `δ` (pieces lemma), hence so are the slit before `v*`, the tip `α(a')`
  and the whole suffix `α((s_q, a'])`, which contains `α(a)` — a point of `α°`.
  Ordering: `β^T` before `v*` avoids the new part of the completion, so the pieces lemma puts it on the closed left;
  after `v*` it lies on the completion itself.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex Bornology
open scoped NNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Supp9B

/-! ### Completions by tails -/

section Tails

/-- A tail started at a point of `ℍ̄` and lying in `ℍ` afterwards is a proper curve. -/
theorem isProperCurve_of_tail {T : ℝ≥0 → ℂ} (hc : Continuous T) (hi : Function.Injective T)
    (h0 : 0 ≤ (T 0).im) (hH : ∀ t, 0 < t → T t ∈ H) (hn : Tendsto (fun t => ‖T t‖) atTop atTop) :
    IsProperCurve T := by
  refine ⟨hc, hi, fun t => ?_, hn⟩
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with ht | ht
  · rw [← ht]; exact h0
  · exact (hH t ht).le

/-- Continuing a proper curve after time `b` by a tail from `γ'(b)` that avoids `γ'([0, b))`. -/
theorem isProperCompletion_junction_tail {γ γ' T : ℝ≥0 → ℂ} {b : ℝ≥0} (hγ' : IsProperCompletion γ b γ')
    (hT : IsProperCurve T) (hT0 : T 0 = γ' b) (hdisj : ∀ u < b, ∀ s, γ' u ≠ T s) :
    IsProperCompletion γ b (junction γ' T b 0) := by
  have hJ := isProperCurve_junction (isProperCurve_of_isProperCompletion hγ') hT hT0.symm
    fun u hu s _ => hdisj u hu s
  exact ⟨hJ.1, hJ.2.1, hJ.2.2.1, hJ.2.2.2, fun t ht => by rw [junction_of_le ht]; exact hγ'.2.2.2.2 t ht⟩

theorem junction_tail_of_lt {γ' T : ℝ≥0 → ℂ} {b t : ℝ≥0} (ht : b < t) :
    junction γ' T b 0 t = T (t - b) := by
  rw [junction_of_lt ht, zero_add]

end Tails

/-! ### The reflected transfer: a left completion for a given right completion -/

section Normalize

variable {α β β'' : ℝ≥0 → ℂ} {a c : ℝ≥0}

/-- **Reverse duality.** If `α'` lies in the closed right side of `β'` (seeds `β'(0) ≤ α'(0)` real), then `β'` lies
in the closed left side of `α'`. -/
theorem range_subset_closedLeftSide_of_closedRightSide {α' β' : ℝ≥0 → ℂ} (hα' : IsProperCurve α')
    (hβ' : IsProperCurve β') (h0 : (α' 0).im = 0) (hβ0 : (β' 0).im = 0) (hseed : (β' 0).re ≤ (α' 0).re)
    (hord : range α' ⊆ closedRightSide β') : range β' ⊆ closedLeftSide α' := by
  have hordr : range (reflectCurve α') ⊆ closedLeftSide (reflectCurve β') := by
    rintro _ ⟨u, rfl⟩
    rcases hord ⟨u, rfl⟩ with hR | hS
    · exact Or.inl (refl_image_rightSide_subset hβ'.2.2.1 hβ0 ⟨_, hR, rfl⟩)
    · exact Or.inr (refl_image_seedRayClosure_subset β' ⟨_, hS, rfl⟩)
  have hdual := range_subset_closedRightSide (isProperCurve_reflectCurve hβ') (isProperCurve_reflectCurve hα')
    (by simp [reflectCurve, hβ0]) (by simp [reflectCurve, h0]) (by simp [reflectCurve, hseed]) hordr
  rintro _ ⟨t, rfl⟩
  rcases hdual ⟨t, rfl⟩ with hR | hS
  · have := refl_image_rightSide_subset (isProperCurve_reflectCurve hα').2.2.1
      (by simp [reflectCurve, h0]) ⟨_, hR, rfl⟩
    rw [reflectCurve_reflectCurve] at this
    exact Or.inl (show β' t ∈ leftSide α' by simpa [reflectCurve] using this)
  · have := refl_image_seedRayClosure_subset (reflectCurve α') ⟨_, hS, rfl⟩
    rw [reflectCurve_reflectCurve] at this
    exact Or.inr (by simpa [reflectCurve] using this)

/-- **The reflected transfer lemma.** If `𝓔(α([0, a]), β([0, c]))` holds and `β''` is a proper completion of
`β([0, c])` whose part after `c` avoids `α([0, a])`, then some completion `α°` of `α([0, a])` has `β''` in its closed
left side. -/
theorem exists_completion_left_of_tail (h : HasOrderedProperCompletions α a β c) (h0 : (α 0).im = 0)
    (hβ0 : (β 0).im = 0) (hseed : (β 0).re ≤ (α 0).re) (hβ'' : IsProperCompletion β c β'')
    (htail : ∀ s, c ≤ s → ∀ x ≤ a, β'' s ≠ α x) :
    ∃ αn, IsProperCompletion α a αn ∧ range β'' ⊆ closedLeftSide αn := by
  obtain ⟨ρβ, ρα, hρβ, hρα, hordρ⟩ := hasOrderedProperCompletions_reflect h h0 hβ0 hseed
  obtain ⟨β₃, hβ₃, hord₃⟩ := exists_isProperCompletion_subset_closedLeftSide hρβ hρα hordρ
    (by simp [reflectCurve, hβ0]) (by simp [reflectCurve, h0]) (by simp [reflectCurve, hseed])
    (isProperCompletion_reflectCurve hβ'') fun s hs y hy h' => htail s hs y hy (refl_injective h')
  have hαn : IsProperCompletion α a (reflectCurve β₃) := by
    simpa using isProperCompletion_reflectCurve hβ₃
  refine ⟨reflectCurve β₃, hαn, ?_⟩
  have P₃ := isProperCurve_of_isProperCompletion hβ₃
  have P'' := isProperCurve_of_isProperCompletion (isProperCompletion_reflectCurve hβ'')
  have e₃ : β₃ 0 = reflectCurve α 0 := hβ₃.2.2.2.2 0 zero_le
  have e'' : reflectCurve β'' 0 = reflectCurve β 0 := (isProperCompletion_reflectCurve hβ'').2.2.2.2 0 zero_le
  have hdual := range_subset_closedRightSide P'' P₃ (by rw [e'']; simp [reflectCurve, hβ0])
    (by rw [e₃]; simp [reflectCurve, h0]) (by rw [e₃, e'']; simp [reflectCurve, hseed]) hord₃
  rintro _ ⟨t, rfl⟩
  rcases hdual ⟨t, rfl⟩ with hR | hS
  · have := refl_image_rightSide_subset P₃.2.2.1 (by rw [e₃]; simp [reflectCurve, h0]) ⟨_, hR, rfl⟩
    exact Or.inl (show β'' t ∈ leftSide (reflectCurve β₃) by simpa [reflectCurve] using this)
  · have := refl_image_seedRayClosure_subset β₃ ⟨_, hS, rfl⟩
    exact Or.inr (by simpa [reflectCurve] using this)

end Normalize

/-! ### The slit meets the left completion after the last old contact -/

section SlitHit

variable {α β αn βn S : ℝ≥0 → ℂ} {a a' c : ℝ≥0}

/-- **The first hit of the slit is after every old contact** (the injectivity step of Lemma W4). Let `(αn, βn)` be
ordered completions of `α([0, a])`, `β([0, c])` with the tail of `βn` off `α([0, a'])`, let `S` be a slit completion
of `α([0, a'])` (its new points are in `ℍ` and off `α([0, a'])`), and suppose `α([a, a'])` avoids `β([0, c])`. If
`S` first meets `βn` at `S(us) = βn(vs)`, then every old contact `α(x) = β(y)` has `y < vs`. -/
theorem lt_of_slit_hit (hαn : IsProperCompletion α a αn) (hβn : IsProperCompletion β c βn)
    (hord : range βn ⊆ closedLeftSide αn) (h0 : (α 0).im = 0) (hβ0 : (β 0).im = 0)
    (hseed : (β 0).re ≤ (α 0).re) (haa' : a < a') (hS : IsProperCompletion α a' S)
    (hSout : ∀ t, a' < t → 0 < (S t).im ∧ S t ∉ α '' Icc 0 a')
    (htailA : ∀ v, c < v → βn v ∉ α '' Icc 0 a')
    (hnew : ∀ x ∈ Icc a a', ∀ y ∈ Icc 0 c, α x ≠ β y)
    {us vs : ℝ≥0} (hus : a' < us) (hhit : S us = βn vs)
    (hfirst : ∀ t, a' ≤ t → t < us → S t ∉ range βn)
    {x₀ y₀ : ℝ≥0} (hx₀ : x₀ ≤ a) (hy₀ : y₀ ≤ c) (hc₀ : α x₀ = β y₀) : y₀ < vs := by
  by_contra hcon
  have hvy : vs ≤ y₀ := not_lt.1 hcon
  have Pα := isProperCurve_of_isProperCompletion hαn
  have Pβ := isProperCurve_of_isProperCompletion hβn
  have eα : ∀ t ≤ a, αn t = α t := hαn.2.2.2.2
  have eβ : ∀ t ≤ c, βn t = β t := hβn.2.2.2.2
  have eS : ∀ t ≤ a', S t = α t := hS.2.2.2.2
  have Pα0 : (αn 0).im = 0 := by rw [eα 0 zero_le]; exact h0
  have Pβ0 : (βn 0).im = 0 := by rw [eβ 0 zero_le]; exact hβ0
  have Pseed : (βn 0).re ≤ (αn 0).re := by rw [eα 0 zero_le, eβ 0 zero_le]; exact hseed
  have hinj : ∀ u v, u ≤ a' → v ≤ a' → α u = α v → u = v := fun u v hu hv huv =>
    hS.2.1 (by rw [eS u hu, eS v hv, huv])
  -- the last old contact
  set Cs := {p : ℝ≥0 × ℝ≥0 | p ∈ Icc 0 a ×ˢ Icc 0 c ∧ αn p.1 = βn p.2} with hCs
  have hCc : IsCompact Cs := (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_eq (Pα.1.comp continuous_fst) (Pβ.1.comp continuous_snd))
  have hCne : Cs.Nonempty :=
    ⟨(x₀, y₀), ⟨⟨zero_le, hx₀⟩, ⟨zero_le, hy₀⟩⟩, by rw [eα x₀ hx₀, eβ y₀ hy₀, hc₀]⟩
  obtain ⟨⟨sq, vq⟩, ⟨⟨⟨-, hsq⟩, ⟨-, hvq⟩⟩, hq⟩, hmax⟩ :=
    hCc.exists_isMaxOn hCne continuous_snd.continuousOn
  have hmax' : ∀ x ≤ a, ∀ y ≤ c, α x = β y → y ≤ vq := fun x hx y hy hxy =>
    hmax (show (x, y) ∈ Cs from ⟨⟨⟨zero_le, hx⟩, ⟨zero_le, hy⟩⟩, by rw [eα x hx, eβ y hy, hxy]⟩)
  have hq' : α sq = β vq := by rw [← eα sq hsq, ← eβ vq hvq]; exact hq
  have hy₀vq := hmax' x₀ hx₀ y₀ hy₀ hc₀
  have hSus := hSout us hus
  have hvsvq : vs < vq := by
    refine lt_of_le_of_ne (hvy.trans hy₀vq) fun h => hSus.2 ?_
    rw [hhit, h, eβ vq hvq, ← hq']
    exact ⟨sq, ⟨zero_le, hsq.trans haa'.le⟩, rfl⟩
  have hsqa : sq < a := lt_of_le_of_ne hsq fun h =>
    hnew a ⟨le_rfl, haa'.le⟩ vq ⟨zero_le, hvq⟩ (h ▸ hq')
  -- the curve `δ`: `αn` up to the last contact, then `βn`
  have hjq : αn sq = βn vq := hq
  have hdisjq : ∀ u < sq, ∀ v, vq ≤ v → αn u ≠ βn v := by
    intro u hu v hv huv
    exact absurd hv (not_le.2 (contact_order Pα Pβ Pα0 Pβ0 Pseed hord huv hjq hu))
  set δ := junction αn βn sq vq with hδdef
  have Pδ : IsProperCurve δ := isProperCurve_junction Pα Pβ hjq hdisjq
  have hδle : ∀ u ≤ sq, δ u = αn u := fun u hu => junction_of_le hu
  have hδlt : ∀ u, sq < u → δ u = βn (vq + (u - sq)) := fun u hu => junction_of_lt hu
  have hδ0' : δ 0 = αn 0 := hδle 0 zero_le
  have hδ0 : (δ 0).im = 0 := by rw [hδ0']; exact Pα0
  have hrδ : ∀ z, z ∈ range δ → (∃ u ≤ sq, αn u = z) ∨ ∃ v, vq ≤ v ∧ βn v = z := by
    rintro z ⟨u, rfl⟩
    by_cases hu : u ≤ sq
    · exact Or.inl ⟨u, hu, (hδle u hu).symm⟩
    · exact Or.inr ⟨vq + (u - sq), le_self_add, (hδlt u (not_le.1 hu)).symm⟩
  have hδL : range δ ⊆ closedLeftSide αn := by
    intro z hz
    rcases hrδ z hz with ⟨u, -, rfl⟩ | ⟨v, -, rfl⟩
    · exact Or.inr (Or.inl ⟨u, rfl⟩)
    · exact hord ⟨v, rfl⟩
  have hαR : range αn ⊆ closedRightSide δ :=
    range_subset_closedRightSide Pα Pδ Pα0 hδ0 (by rw [hδ0']) hδL
  have hoffδ : ∀ z : ℂ, 0 ≤ z.im → (∀ u ≤ sq, αn u ≠ z) → (∀ v, vq ≤ v → βn v ≠ z) →
      z ∉ seedRayClosure δ := by
    intro z hz h1 h2 hzS
    rw [seedRayClosure_eq_range_union hδ0] at hzS
    rcases hzS with hzS | hzS
    · rcases hrδ z hzS with ⟨u, hu, hue⟩ | ⟨v, hv, hve⟩
      · exact h1 u hu hue
      · exact h2 v hv hve
    · exact h1 0 zero_le (by rw [← hδ0']; exact (eq_seed_of_mem_lowerRay hδ0 hz hzS).symm)
  have hcδ := compl_seedRayClosure_eq Pδ hδ0
  have hdδ := disjoint_leftSide_rightSide Pδ hδ0
  have hclL : ∀ z, z ∈ closure (leftSide δ) → z ∉ seedRayClosure δ → z ∈ leftSide δ := by
    intro z hz hzS
    rcases (hcδ ▸ hzS : z ∈ leftSide δ ∪ rightSide δ) with h' | h'
    · exact h'
    · obtain ⟨w, hwL, hwR⟩ := ((mem_closure_iff_frequently.1 hz).and_eventually
        ((isOpen_rightSide Pδ).mem_nhds h')).exists
      exact absurd hwR (Set.disjoint_left.1 hdδ hwL)
  -- the hit point is on the left of `δ`
  have hβvs : βn vs ∈ leftSide δ := by
    have hmem := mem_closedLeftSide_of_avoid Pα Pδ Pα0 hδle Pβ Pβ0 Pseed hord (t := vs) (by
      intro u hu s hs h'
      rcases hs.lt_or_eq with hs' | hs'
      · rw [hδlt s hs'] at h'
        have h1 := Pβ.2.1 h'
        have h2 : vq < u := by rw [h1]; exact lt_add_of_pos_right _ (tsub_pos_of_lt hs')
        exact absurd (hu.trans hvsvq.le) (not_le.2 h2)
      · rw [← hs', hδle sq le_rfl, hjq] at h'
        exact absurd (Pβ.2.1 h' ▸ hu) (not_le.2 hvsvq))
    refine hmem.resolve_right (hoffδ _ (hhit ▸ hSus.1.le) (fun u hu h' => hSus.2 ?_) fun v hv h' =>
      absurd (Pβ.2.1 h' ▸ hv) (not_le.2 hvsvq))
    exact ⟨u, ⟨zero_le, hu.trans (hsqa.le.trans haa'.le)⟩, by rw [← eα u (hu.trans hsqa.le), h', hhit]⟩
  -- the slit before the hit is on the left of `δ`
  have hSL : S '' Ioc a' us ⊆ leftSide δ := by
    have hpc : IsPreconnected (S '' Ioc a' us) := isPreconnected_Ioc.image _ hS.1.continuousOn
    have hsub : S '' Ioc a' us ⊆ (seedRayClosure δ)ᶜ := by
      rintro _ ⟨t, ht, rfl⟩
      have hSt := hSout t ht.1
      refine hoffδ (S t) hSt.1.le (fun u hu h' => hSt.2 ⟨u, ⟨zero_le, hu.trans (hsqa.le.trans haa'.le)⟩,
        by rw [← eα u (hu.trans hsqa.le)]; exact h'⟩) fun v hv h' => ?_
      rcases ht.2.lt_or_eq with htu | htu
      · exact hfirst t ht.1.le htu ⟨v, h'⟩
      · rw [htu, hhit] at h'
        exact absurd (Pβ.2.1 h' ▸ hv) (not_le.2 hvsvq)
    have := hpc.subset_connectedComponentIn ⟨us, ⟨hus, le_rfl⟩, rfl⟩ hsub
    rwa [← connectedComponentIn_eq (show S us ∈ leftSide δ by rw [hhit]; exact hβvs)] at this
  -- hence the tip `α(a')`
  have hαa'L : α a' ∈ leftSide δ := by
    have hlim : Tendsto S (𝓝[>] a') (𝓝 (S a')) := hS.1.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hcl : α a' ∈ closure (leftSide δ) := by
      rw [← eS a' le_rfl]
      refine mem_closure_of_tendsto hlim ?_
      filter_upwards [Ioc_mem_nhdsGT hus] with t ht using hSL ⟨t, ht, rfl⟩
    refine hclL _ hcl (hoffδ _ (by rw [← eS a' le_rfl]; exact hS.2.2.1 a') (fun u hu h' => ?_) fun v hv h' => ?_)
    · rw [eα u (hu.trans hsqa.le)] at h'
      have := hinj u a' (hu.trans (hsqa.le.trans haa'.le)) le_rfl h'
      exact absurd (this ▸ hu) (not_le.2 (hsqa.trans haa'))
    · by_cases hvc : v ≤ c
      · rw [eβ v hvc] at h'
        exact hnew a' ⟨haa'.le, le_rfl⟩ v ⟨zero_le, hvc⟩ h'.symm
      · exact htailA v (not_le.1 hvc) ⟨a', ⟨zero_le, le_rfl⟩, h'.symm⟩
  -- hence the whole suffix after the last contact
  have hsufL : α '' Ioc sq a' ⊆ leftSide δ := by
    have hpc : IsPreconnected (α '' Ioc sq a') := by
      have : α '' Ioc sq a' = S '' Ioc sq a' := image_congr fun t ht => (eS t ht.2).symm
      rw [this]; exact isPreconnected_Ioc.image _ hS.1.continuousOn
    have hsub : α '' Ioc sq a' ⊆ (seedRayClosure δ)ᶜ := by
      rintro _ ⟨t, ht, rfl⟩
      refine hoffδ (α t) (by rw [← eS t ht.2]; exact hS.2.2.1 t) (fun u hu h' => ?_) fun v hv h' => ?_
      · rw [eα u (hu.trans hsqa.le)] at h'
        have := hinj u t (hu.trans (hsqa.le.trans haa'.le)) ht.2 h'
        exact absurd (this ▸ hu) (not_le.2 ht.1)
      · by_cases hvc : v ≤ c
        · rw [eβ v hvc] at h'
          by_cases hta : t ≤ a
          · have hv' := hmax' t hta v hvc h'.symm
            have hvv : v = vq := le_antisymm hv' hv
            rw [hvv, ← hq'] at h'
            exact absurd (hinj sq t (hsq.trans haa'.le) ht.2 h' ▸ ht.1) (lt_irrefl _)
          · exact hnew t ⟨(not_le.1 hta).le, ht.2⟩ v ⟨zero_le, hvc⟩ h'.symm
        · exact htailA v (not_le.1 hvc) ⟨t, ⟨zero_le, ht.2⟩, h'.symm⟩
    have := hpc.subset_connectedComponentIn ⟨a', ⟨hsqa.trans haa', le_rfl⟩, rfl⟩ hsub
    rwa [← connectedComponentIn_eq hαa'L] at this
  -- but `α(a)` is a point of `αn`, on the closed right of `δ`
  have haL : α a ∈ leftSide δ := hsufL ⟨a, ⟨hsqa, haa'.le⟩, rfl⟩
  rcases hαR ⟨a, eα a le_rfl⟩ with h' | h'
  · exact Set.disjoint_left.1 hdδ haL h'
  · exact leftSide_subset_compl δ haL h'

end SlitHit

/-! ### Extending the first path -/

section ExtendLeft

variable {α β S : ℝ≥0 → ℂ} {a a' c : ℝ≥0}

/-- **Lemma W4 for the first path, from an accessible tip.** Let `𝓔(α([0, a]), β([0, c]))` hold (real seeds
`β(0) ≤ α(0)`), let `S` be a slit completion of `α([0, a'])`, `a < a'`, and let `α([a, a'])` avoid `β([0, c])`. If
the tip `α(a')` lies in the closure of the joint domain, or the tip `β(c)` does and is not an old contact, then
`𝓔(α([0, a']), β([0, c]))`. -/
theorem hasOrderedProperCompletions_extend_left (h : HasOrderedProperCompletions α a β c)
    (h0 : (α 0).im = 0) (hβ0 : (β 0).im = 0) (hseed : (β 0).re ≤ (α 0).re) (haa' : a < a')
    (hS : IsProperCompletion α a' S) (hSout : ∀ t, a' < t → 0 < (S t).im ∧ S t ∉ α '' Icc 0 a')
    (hnew : ∀ x ∈ Icc a a', ∀ y ∈ Icc 0 c, α x ≠ β y)
    (hacc : α a' ∈ closure (jointDomain α a' β c) ∨
      (β c ∈ closure (jointDomain α a' β c) ∧ ∀ x ≤ a, β c ≠ α x)) :
    HasOrderedProperCompletions α a' β c := by
  obtain ⟨α', β', hα', hβ', hord⟩ := id h
  have eS : ∀ t ≤ a', S t = α t := hS.2.2.2.2
  have eβ' : ∀ t ≤ c, β' t = β t := hβ'.2.2.2.2
  have hαc : ContinuousOn α (Icc 0 a') := hS.1.continuousOn.congr fun t ht => (eS t ht.2).symm
  have hβc : ContinuousOn β (Icc 0 c) := hβ'.1.continuousOn.congr fun t ht => (eβ' t ht.2).symm
  have hαH : MapsTo α (Icc 0 a') Hbar := fun t ht => by rw [← eS t ht.2]; exact hS.2.2.1 t
  have hβH : MapsTo β (Icc 0 c) Hbar := fun t ht => by rw [← eβ' t ht.2]; exact hβ'.2.2.1 t
  have hinj : ∀ u v, u ≤ a' → v ≤ a' → α u = α v → u = v := fun u v hu hv huv =>
    hS.2.1 (by rw [eS u hu, eS v hv, huv])
  set J := jointDomain α a' β c with hJ
  rcases hacc with hacc | ⟨hacc, hcβ⟩
  · -- the first tip is accessible: the transfer lemma
    obtain ⟨T, hTc, hTi, hT0, hTJ, hTn⟩ :=
      exists_tail_of_mem_closure_jointDomain hαc hβc hαH hβH h0 hβ0 hacc
    have PT : IsProperCurve T := isProperCurve_of_tail hTc hTi
      (by rw [hT0]; exact hαH ⟨zero_le, le_rfl⟩) (fun t ht => jointDomain_subset_H (hTJ t ht)) hTn
    have hdisj : ∀ u < a', ∀ s, S u ≠ T s := by
      intro u hu s h'
      rw [eS u hu.le] at h'
      rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with hs | hs
      · rw [← hs, hT0] at h'
        exact hu.ne (hinj u a' hu.le le_rfl h')
      · exact notMem_jointDomain_left hu.le (h' ▸ hTJ s hs)
    have hα'' := isProperCompletion_junction_tail hS PT (by rw [hT0, eS a' le_rfl]) hdisj
    refine hasOrderedProperCompletions_of_completion h h0 hβ0 hseed haa'.le hα'' ?_
    intro s hs y hy h'
    by_cases hsa' : s ≤ a'
    · rw [junction_of_le hsa', eS s hsa'] at h'
      exact hnew s ⟨hs, hsa'⟩ y ⟨zero_le, hy⟩ h'
    · rw [junction_tail_of_lt (not_le.1 hsa')] at h'
      exact notMem_jointDomain_right hy (h' ▸ hTJ _ (tsub_pos_of_lt (not_le.1 hsa')))
  · -- the second tip is accessible: normalize its completion, then follow the slit
    obtain ⟨T, hTc, hTi, hT0, hTJ, hTn⟩ :=
      exists_tail_of_mem_closure_jointDomain hαc hβc hαH hβH h0 hβ0 hacc
    have PT : IsProperCurve T := isProperCurve_of_tail hTc hTi
      (by rw [hT0]; exact hβH ⟨zero_le, le_rfl⟩) (fun t ht => jointDomain_subset_H (hTJ t ht)) hTn
    have hβinj : ∀ u v, u ≤ c → v ≤ c → β u = β v → u = v := fun u v hu hv huv =>
      hβ'.2.1 (by rw [eβ' u hu, eβ' v hv, huv])
    have hdisjβ : ∀ u < c, ∀ s, β' u ≠ T s := by
      intro u hu s h'
      rw [eβ' u hu.le] at h'
      rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with hs | hs
      · rw [← hs, hT0] at h'
        exact hu.ne (hβinj u c hu.le le_rfl h')
      · exact notMem_jointDomain_right hu.le (h' ▸ hTJ s hs)
    have hβT := isProperCompletion_junction_tail hβ' PT (by rw [hT0, eβ' c le_rfl]) hdisjβ
    set βT := junction β' T c 0 with hβTdef
    have PβT := isProperCurve_of_isProperCompletion hβT
    have eβT : ∀ t ≤ c, βT t = β t := hβT.2.2.2.2
    have hβTeq : ∀ v, c < v → βT v = T (v - c) := fun v hv => junction_tail_of_lt hv
    have hβTlt : ∀ v, c < v → βT v ∈ J := fun v hv => by
      rw [hβTeq v hv]; exact hTJ _ (tsub_pos_of_lt hv)
    have htailA : ∀ v, c < v → βT v ∉ α '' Icc 0 a' := by
      rintro v hv ⟨x, hx, hxv⟩
      exact notMem_jointDomain_left hx.2 (hxv ▸ hβTlt v hv)
    obtain ⟨αn, hαn, hordn⟩ := exists_completion_left_of_tail h h0 hβ0 hseed hβT fun s hs x hx h' => by
      rcases hs.lt_or_eq with hs' | hs'
      · exact notMem_jointDomain_left (hx.trans haa'.le) (h' ▸ hβTlt s hs')
      · rw [← hs', eβT c le_rfl] at h'
        exact hcβ x hx h'
    have Pαn := isProperCurve_of_isProperCompletion hαn
    have hαn0 : (αn 0).im = 0 := by rw [hαn.2.2.2.2 0 zero_le]; exact h0
    have hβT0 : (βT 0).im = 0 := by rw [eβT 0 zero_le]; exact hβ0
    have hseedn : (βT 0).re ≤ (αn 0).re := by rw [eβT 0 zero_le, hαn.2.2.2.2 0 zero_le]; exact hseed
    have hpieces : ∀ αx : ℝ≥0 → ℂ, IsProperCompletion α a' αx → ∀ t,
        (∀ u ≤ t, ∀ s, a ≤ s → βT u ≠ αx s) → βT t ∈ closedLeftSide αx := fun αx hαx t hav =>
      mem_closedLeftSide_of_avoid Pαn (isProperCurve_of_isProperCompletion hαx) hαn0
        (fun t ht => (hαx.2.2.2.2 t (ht.trans haa'.le)).trans (hαn.2.2.2.2 t ht).symm) PβT hβT0 hseedn
        hordn hav
    -- an old point of `βT` and a point of `α([a, a'])` are distinct
    have hold : ∀ u, ∀ s, a ≤ s → s ≤ a' → βT u ≠ α s := by
      intro u s hs hsa' h'
      by_cases huc : u ≤ c
      · rw [eβT u huc] at h'; exact hnew s ⟨hs, hsa'⟩ u ⟨zero_le, huc⟩ h'.symm
      · exact notMem_jointDomain_left hsa' (h' ▸ hβTlt u (not_le.1 huc))
    -- the hits of the slit on `βT`
    set Hs := {t : ℝ≥0 | a' ≤ t ∧ S t ∈ range βT} with hHs
    have hrc : IsClosed (range βT) := by rw [← image_univ]; exact isClosed_image PβT isClosed_univ
    have hHsc : IsClosed Hs := isClosed_Ici.inter (hrc.preimage hS.1)
    rcases Hs.eq_empty_or_nonempty with hHe | hHne
    · refine ⟨S, βT, hS, hβT, ?_⟩
      rintro _ ⟨t, rfl⟩
      refine hpieces S hS t fun u _ s hs h' => ?_
      by_cases hsa' : s ≤ a'
      · rw [eS s hsa'] at h'; exact hold u s hs hsa' h'
      · have : s ∈ Hs := ⟨(not_le.1 hsa').le, ⟨u, h'⟩⟩
        rw [hHe] at this; exact this
    · set us := sInf Hs with hus_def
      have husH : us ∈ Hs := hHsc.csInf_mem hHne (OrderBot.bddBelow Hs)
      obtain ⟨vs, hvs⟩ := husH.2
      have hSa' : S a' ∉ range βT := by
        rintro ⟨v, hv⟩
        rw [eS a' le_rfl] at hv
        exact hold v a' haa'.le le_rfl hv
      have hus : a' < us := lt_of_le_of_ne husH.1 fun h' => hSa' (h' ▸ husH.2)
      have hfirst : ∀ t, a' ≤ t → t < us → S t ∉ range βT := fun t ht htu hS' =>
        absurd (csInf_le (OrderBot.bddBelow Hs) ⟨ht, hS'⟩) (not_le.2 htu)
      have hT1 : ∀ x ≤ a, ∀ y ≤ c, α x = β y → y < vs := fun x hx y hy hxy =>
        lt_of_slit_hit hαn hβT hordn h0 hβ0 hseed haa' hS hSout htailA hnew hus hvs.symm hfirst hx hy hxy
      have hdisj : ∀ u < us, ∀ v, vs ≤ v → S u ≠ βT v := by
        intro u hu v hv h'
        by_cases hua' : u ≤ a'
        · rw [eS u hua'] at h'
          by_cases hua : u ≤ a
          · by_cases hvc : v ≤ c
            · rw [eβT v hvc] at h'
              exact absurd hv (not_le.2 (hT1 u hua v hvc h'))
            · exact notMem_jointDomain_left hua' (h' ▸ hβTlt v (not_le.1 hvc))
          · exact hold v u (not_le.1 hua).le hua' h'.symm
        · exact hfirst u (not_le.1 hua').le hu ⟨v, h'.symm⟩
      have PS := isProperCurve_of_isProperCompletion hS
      have hJc := isProperCurve_junction PS PβT hvs.symm hdisj
      set α'' := junction S βT us vs with hα''def
      have hα''le : ∀ t ≤ us, α'' t = S t := fun t ht => junction_of_le ht
      have hα''lt : ∀ t, us < t → α'' t = βT (vs + (t - us)) := fun t ht => junction_of_lt ht
      have hα'' : IsProperCompletion α a' α'' := ⟨hJc.1, hJc.2.1, hJc.2.2.1, hJc.2.2.2, fun t ht => by
        rw [hα''le t (ht.trans hus.le)]; exact eS t ht⟩
      refine ⟨α'', βT, hα'', hβT, ?_⟩
      rintro _ ⟨t, rfl⟩
      by_cases htv : t < vs
      · refine hpieces α'' hα'' t fun u hu s hs h' => ?_
        by_cases hsu : s ≤ us
        · rw [hα''le s hsu] at h'
          by_cases hsa' : s ≤ a'
          · rw [eS s hsa'] at h'; exact hold u s hs hsa' h'
          · rcases hsu.lt_or_eq with hsu' | hsu'
            · exact hfirst s (not_le.1 hsa').le hsu' ⟨u, h'⟩
            · rw [hsu', ← hvs] at h'
              exact absurd (PβT.2.1 h' ▸ hu) (not_le.2 htv)
        · rw [hα''lt s (not_le.1 hsu)] at h'
          have h1 := PβT.2.1 h'
          have h2 : vs < u := by
            rw [h1]; exact lt_add_of_pos_right _ (tsub_pos_of_lt (not_le.1 hsu))
          exact absurd (hu.trans htv.le) (not_le.2 h2)
      · refine Or.inr (Or.inl ⟨us + (t - vs), ?_⟩)
        have hvt : vs ≤ t := not_lt.1 htv
        rcases hvt.lt_or_eq with hvt' | hvt'
        · have hlt : us < us + (t - vs) := lt_add_of_pos_right _ (tsub_pos_of_lt hvt')
          rw [hα''lt _ hlt, add_tsub_cancel_left, add_tsub_cancel_of_le hvt]
        · rw [← hvt', tsub_self, add_zero, hα''le us le_rfl, hvs]

end ExtendLeft

end Supp9B

end InteractingSLE
