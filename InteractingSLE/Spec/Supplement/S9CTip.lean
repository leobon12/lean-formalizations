/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S9BSlit
import InteractingSLE.Foundations.Topology.JaniszewskiHalfPlane

/-!
# Supplement §9, Lemma W4: the tip-access input, proved

Packet PROVE-W4TIP. `w4TipAccessStatement` proves the named input `Supp9B.W4TipAccessStatement` of PROVE-SUPP9-C:

> if `𝓔(α([0, a]), β([0, c]))` holds for curves from real seeds `β(0) ≤ α(0)`, the prefixes `α([0, a'])` (`a < a'`)
> and `β([0, c])` have slit completions, and `α([a, a'])` avoids `β([0, c])`, then the tip `α(a')` lies in the closure
> of the joint domain, or the tip `β(c)` does and is not a point of `α([0, a])`.

Hence Lemma W4 holds on the frozen carriers from the Aux. 25 interface alone (`w4Statement_of_aux25`).

## The proof (Lemma G13's trapping classification after the last old contact, supplement pp. 506–507, 532)

Write `A = α([0, a'])`, `B = β([0, c])`, and `Ω(F) = ℍ \ fillH F` (the unbounded domain). Each tip is accessible from
the unbounded domain of its own prefix (its slit, `mem_closure_H_diff_fillH_of_isSlitCompletion`).

* **No old contact.** Then `A ∩ B = ∅`, so `Ω(A) ∩ Ω(B) ⊆ Ω(A ∪ B)` (Janiszewski in `ℍ`,
  `HalfPlaneSep.H_diff_fillH_inter_subset`). If `B` is free at `α(a')` (near the tip all points of `ℍ` lie in `Ω(B)`),
  the tip is in the closure of `Ω(A) ∩ Ω(B)`. Otherwise `B` traps the tip, hence (constancy of the label along the
  connected `A ⊆ ℍ̄ \ B`) all of `A`; so `A` misses `Ω(B)`, `Ω(B) ⊆ Ω(A ∪ B)`, and `β(c) ∈ closure Ω(B)`.
* **Old contacts.** Let `q = α(s_q) = β(v_q)` be the last one (contact order of the old completions, Lemma G5:
  every contact `α(x) = β(y)` of the prefixes has `x ≤ s_q`, `y ≤ v_q`; `s_q < a` since `α(a)` is not a contact).
  Put `K_q = α([0, s_q]) ∪ β([0, v_q])`, `X = A ∪ β([0, v_q])`, `Y = α([0, s_q]) ∪ B`; then `X ∩ Y = K_q`,
  `A ∩ K_q = α([0, s_q])`, `B ∩ K_q = β([0, v_q])`, and Janiszewski gives `Ω(X) ∩ Ω(Y) ⊆ Ω(A ∪ B)`,
  `Ω(A) ∩ Ω(K_q) ⊆ Ω(X)`, `Ω(B) ∩ Ω(K_q) ⊆ Ω(Y)`. The old completion of `α` after `s_q`, together with the suffix
  `α((s_q, a'])`, is an unbounded connected set off `K_q`, so `K_q` is free at `α(a')`; likewise at `β(c)` if
  `v_q < c`. Hence `α(a') ∈ closure Ω(X)`. If `Y` is free at `α(a')`, the tip is in the closure of
  `Ω(X) ∩ Ω(Y)`. Otherwise `Y` traps the whole suffix `α((s_q, a'])`, `A` misses `Ω(Y)`, `Ω(Y) ⊆ Ω(A ∪ B)`; if
  `v_q < c` then `β(c) ∈ closure Ω(Y)` and `β(c)` is not an old contact, and if `v_q = c` then `Y = K_q` is both free
  and trapping at `α(a')`, which is absurd.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex Bornology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace Supp9B

open HalfPlaneSep

section Tip

theorem not_isBounded_image_Ioi {γ : ℝ≥0 → ℂ} (hγ : Tendsto (fun t => ‖γ t‖) atTop atTop) (s : ℝ≥0) :
    ¬ IsBounded (γ '' Ioi s) := by
  intro hb
  obtain ⟨M, hM⟩ := hb.exists_norm_le
  obtain ⟨t, ht1, ht2⟩ := ((hγ.eventually_gt_atTop M).and (eventually_gt_atTop s)).exists
  exact absurd (hM _ ⟨t, ht2, rfl⟩) (not_le.2 ht1)

/-- **The tip of a slit completion is accessible** from the unbounded domain of its prefix. -/
theorem mem_closure_H_diff_fillH_of_isSlitCompletion {γ S : ℝ≥0 → ℂ} {b : ℝ≥0}
    (hS : IsSlitCompletion γ b S) : γ b ∈ closure (H \ fillH (γ '' Icc 0 b)) := by
  have eS : ∀ t ≤ b, S t = γ t := hS.1.2.2.2.2
  have him : γ '' Icc 0 b = S '' Icc 0 b := image_congr fun t ht => (eS t ht.2).symm
  have hcl : IsClosed (γ '' Icc 0 b) := by rw [him]; exact (isCompact_Icc.image hS.1.1).isClosed
  have hT : S '' Ioi b ⊆ H \ fillH (γ '' Icc 0 b) :=
    subset_H_diff_fillH_of_not_isBounded hcl (isPreconnected_Ioi.image _ hS.1.1.continuousOn)
      (not_isBounded_image_Ioi hS.1.2.2.2.1 b) (by
        rintro _ ⟨t, ht, rfl⟩
        exact ⟨(hS.2 t ht).1, (hS.2 t ht).2⟩)
  refine closure_mono hT ?_
  rw [← eS b le_rfl]
  have hlim : Tendsto S (𝓝[>] b) (𝓝 (S b)) := hS.1.1.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact mem_closure_of_tendsto hlim (eventually_mem_nhdsWithin.mono fun t ht => ⟨t, ht, rfl⟩)

/-- **The trapping classification, abstract form.** Let `Ω(X) ∩ Ω(Y) ⊆ Ω(A ∪ B)`, let the tip `p` be accessible from
`Ω(X)`, and let `p` lie on a preconnected `As ⊆ ℍ̄ \ Y` with `A ⊆ Y ∪ As` and `B ⊆ Y ⊆ A ∪ B`. Then `p` is
accessible from `Ω(A ∪ B)`, or `Y` traps `p` and `Ω(Y) ⊆ Ω(A ∪ B)`. -/
theorem mem_closure_or_isTrappedAt {A B X Y As : Set ℂ} {p : ℂ} (hA : IsCompact A) (hY : IsCompact Y)
    (hJ : (H \ fillH X) ∩ (H \ fillH Y) ⊆ H \ fillH (A ∪ B)) (hpX : p ∈ closure (H \ fillH X))
    (hAs : IsPreconnected As) (hpAs : p ∈ As) (hAsY : As ⊆ {w | 0 ≤ w.im} \ Y) (hAY : A ⊆ Y ∪ As)
    (hYAB : Y ⊆ A ∪ B) (hBY : B ⊆ Y) :
    p ∈ closure (H \ fillH (A ∪ B)) ∨ (H \ fillH Y ⊆ H \ fillH (A ∪ B) ∧ IsTrappedAt Y p) := by
  rcases isFreeAt_or_isTrappedAt hY.isClosed (hAsY hpAs).2 with hf | ht
  · exact Or.inl (closure_mono hJ (mem_closure_inter_of_isFreeAt hpX sdiff_subset hf))
  · refine Or.inr ⟨?_, ht⟩
    have hall := (isFreeAt_or_isTrappedAt_of_isPreconnected hY.isClosed hAs hAsY).resolve_left
      fun hf' => (hf' p hpAs).not_isTrappedAt (hAsY hpAs).1 ht
    have hd : Disjoint A (H \ fillH Y) := Set.disjoint_left.2 fun w hwA hwU => by
      rcases hAY hwA with hwY | hwAs
      · exact (H_diff_fillH_subset_H_diff hY.isClosed hwU).2 hwY
      · exact (hall w hwAs).notMem hwU
    have hsub := H_diff_fillH_subset_union_of_disjoint hY.isClosed hY.isBounded hA.isClosed hd
    have heq : Y ∪ A = A ∪ B := by
      ext w
      constructor
      · rintro (hw | hw)
        · exact hYAB hw
        · exact Or.inl hw
      · rintro (hw | hw)
        · exact Or.inr hw
        · exact Or.inl (hBY hw)
    rwa [heq] at hsub

end Tip

/-! ### The tip-access input -/

section Main

/-- **The tip-access input of Lemma W4** (`W4TipAccessStatement`; Lemma G13's trapping classification after the last
old contact, supplement pp. 506–507, used in W4's proof, p. 532). -/
theorem w4TipAccessStatement : W4TipAccessStatement := by
  intro α β S Sβ a a' c h h0 hβ0 hseed haa' hS hSβ hnew
  obtain ⟨αn, βn, hαn, hβn, hord⟩ := h
  have eS : ∀ t ≤ a', S t = α t := hS.1.2.2.2.2
  have eSβ : ∀ t ≤ c, Sβ t = β t := hSβ.1.2.2.2.2
  have eα : ∀ t ≤ a, αn t = α t := hαn.2.2.2.2
  have eβ : ∀ t ≤ c, βn t = β t := hβn.2.2.2.2
  have Pα := isProperCurve_of_isProperCompletion hαn
  have Pβ := isProperCurve_of_isProperCompletion hβn
  have Pα0 : (αn 0).im = 0 := by rw [eα 0 zero_le]; exact h0
  have Pβ0 : (βn 0).im = 0 := by rw [eβ 0 zero_le]; exact hβ0
  have Pseed : (βn 0).re ≤ (αn 0).re := by rw [eα 0 zero_le, eβ 0 zero_le]; exact hseed
  have hαinj : ∀ u v, u ≤ a' → v ≤ a' → α u = α v → u = v := fun u v hu hv huv =>
    hS.1.2.1 (by rw [eS u hu, eS v hv, huv])
  have hαH : ∀ t ≤ a', 0 ≤ (α t).im := fun t ht => by rw [← eS t ht]; exact hS.1.2.2.1 t
  have himα : ∀ {I : Set ℝ≥0}, I ⊆ Iic a' → α '' I = S '' I := fun hI =>
    image_congr fun t ht => (eS t (hI ht)).symm
  have himβ : ∀ {I : Set ℝ≥0}, I ⊆ Iic c → β '' I = Sβ '' I := fun hI =>
    image_congr fun t ht => (eSβ t (hI ht)).symm
  have hcα : ∀ s ≤ a', IsCompact (α '' Icc 0 s) := fun s hs => by
    rw [himα (fun t ht => ht.2.trans hs)]; exact isCompact_Icc.image hS.1.1
  have hcβ : ∀ s ≤ c, IsCompact (β '' Icc 0 s) := fun s hs => by
    rw [himβ (fun t ht => ht.2.trans hs)]; exact isCompact_Icc.image hSβ.1.1
  have hpα : ∀ s ≤ a', IsPreconnected (α '' Icc 0 s) := fun s hs => by
    rw [himα (fun t ht => ht.2.trans hs)]; exact isPreconnected_Icc.image _ hS.1.1.continuousOn
  have hpβ : ∀ s ≤ c, IsPreconnected (β '' Icc 0 s) := fun s hs => by
    rw [himβ (fun t ht => ht.2.trans hs)]; exact isPreconnected_Icc.image _ hSβ.1.1.continuousOn
  have hpA := mem_closure_H_diff_fillH_of_isSlitCompletion hS
  have hrB := mem_closure_H_diff_fillH_of_isSlitCompletion hSβ
  have hcA := hcα a' le_rfl
  have hcB := hcβ c le_rfl
  show α a' ∈ closure (H \ fillH (α '' Icc 0 a' ∪ β '' Icc 0 c)) ∨
    (β c ∈ closure (H \ fillH (α '' Icc 0 a' ∪ β '' Icc 0 c)) ∧ ∀ x ≤ a, β c ≠ α x)
  set A := α '' Icc 0 a' with hAdef
  set B := β '' Icc 0 c with hBdef
  -- the old contacts
  set Cs := {p : ℝ≥0 × ℝ≥0 | p ∈ Icc 0 a ×ˢ Icc 0 c ∧ αn p.1 = βn p.2} with hCs
  rcases Cs.eq_empty_or_nonempty with hCe | hCne
  · -- no old contact: Lemma G13a's classification
    have hno : ∀ x ≤ a', ∀ y ≤ c, α x ≠ β y := by
      intro x hx y hy hxy
      by_cases hxa : x ≤ a
      · have hmem : (x, y) ∈ Cs := ⟨⟨⟨zero_le, hxa⟩, ⟨zero_le, hy⟩⟩, by rw [eα x hxa, eβ y hy, hxy]⟩
        rw [hCe] at hmem
        exact hmem
      · exact hnew x ⟨(not_le.1 hxa).le, hx⟩ y ⟨zero_le, hy⟩ hxy
    have hJ := H_diff_fillH_inter_subset hcA hcB (by
      rintro w ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
      exact absurd hxy.symm (hno x hx.2 y hy.2))
    rcases mem_closure_or_isTrappedAt (B := B) hcA hcB hJ hpA (hpα a' le_rfl)
        (mem_image_of_mem α ⟨zero_le, le_rfl⟩) (by
          rintro _ ⟨x, hx, rfl⟩
          exact ⟨hαH x hx.2, fun ⟨y, hy, hxy⟩ => hno x hx.2 y hy.2 hxy.symm⟩)
        subset_union_right subset_union_right subset_rfl with h | ⟨hsub, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨closure_mono hsub hrB, fun x hx hxy => hno x (hx.trans haa'.le) c le_rfl hxy.symm⟩
  -- the last old contact `q = α(sq) = β(vq)`
  have hCc : IsCompact Cs := (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_eq (Pα.1.comp continuous_fst) (Pβ.1.comp continuous_snd))
  obtain ⟨⟨sq, vq⟩, ⟨⟨⟨-, hsq⟩, ⟨-, hvq⟩⟩, hq⟩, hmax⟩ :=
    hCc.exists_isMaxOn hCne continuous_snd.continuousOn
  change sq ≤ a at hsq
  change vq ≤ c at hvq
  change αn sq = βn vq at hq
  have hmax' : ∀ x ≤ a, ∀ y ≤ c, α x = β y → y ≤ vq := fun x hx y hy hxy =>
    hmax (show (x, y) ∈ Cs from ⟨⟨⟨zero_le, hx⟩, ⟨zero_le, hy⟩⟩, by rw [eα x hx, eβ y hy, hxy]⟩)
  have hq' : α sq = β vq := by rw [← eα sq hsq, ← eβ vq hvq]; exact hq
  have hsqa : sq < a := lt_of_le_of_ne hsq fun he =>
    hnew a ⟨le_rfl, haa'.le⟩ vq ⟨zero_le, hvq⟩ (he ▸ hq')
  have hsqa' : sq < a' := hsqa.trans haa'
  -- every contact of the prefixes is at or before the last one (contact order, Lemma G5)
  have hcon : ∀ x ≤ a', ∀ y ≤ c, α x = β y → x ≤ sq ∧ y ≤ vq := by
    intro x hx y hy hxy
    have hxa : x ≤ a := by
      by_contra hxa
      exact hnew x ⟨(not_le.1 hxa).le, hx⟩ y ⟨zero_le, hy⟩ hxy
    have hyv := hmax' x hxa y hy hxy
    refine ⟨not_lt.1 fun hxs => ?_, hyv⟩
    have := contact_order Pα Pβ Pα0 Pβ0 Pseed hord hq
      (show αn x = βn y by rw [eα x hxa, eβ y hy, hxy]) hxs
    exact absurd hyv (not_le.2 this)
  set Kα := α '' Icc 0 sq with hKαdef
  set Kβ := β '' Icc 0 vq with hKβdef
  have hKαA : Kα ⊆ A := image_mono (Icc_subset_Icc_right hsqa'.le)
  have hKβB : Kβ ⊆ B := image_mono (Icc_subset_Icc_right hvq)
  have hcKα : IsCompact Kα := hcα sq hsqa'.le
  have hcKβ : IsCompact Kβ := hcβ vq hvq
  have hKq : IsCompact (Kα ∪ Kβ) := hcKα.union hcKβ
  have hα0Kα : α 0 ∈ Kα := ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩
  have hβ0Kβ : β 0 ∈ Kβ := ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩
  -- Janiszewski: `Ω(X) ∩ Ω(Y) ⊆ Ω(A ∪ B)` for `X = A ∪ Kβ`, `Y = Kα ∪ B`
  have hJ1 : (H \ fillH (A ∪ Kβ)) ∩ (H \ fillH (Kα ∪ B)) ⊆ H \ fillH (A ∪ B) := by
    have hXY : (A ∪ Kβ) ∪ (Kα ∪ B) = A ∪ B := by
      ext w
      constructor
      · rintro ((hw | hw) | (hw | hw))
        exacts [Or.inl hw, Or.inr (hKβB hw), Or.inl (hKαA hw), Or.inr hw]
      · rintro (hw | hw)
        exacts [Or.inl (Or.inl hw), Or.inr (Or.inr hw)]
    rw [← hXY]
    refine H_diff_fillH_inter_subset (hcA.union hcKβ) (hcKα.union hcB) fun w hw => ?_
    have hw' : w ∈ Kα ∨ w ∈ Kβ := by
      rcases hw with ⟨hwA | hwKβ, hwKα | hwB⟩
      · exact Or.inl hwKα
      · obtain ⟨x, hx, rfl⟩ := hwA
        obtain ⟨y, hy, hxy⟩ := hwB
        exact Or.inl ⟨x, ⟨zero_le, (hcon x hx.2 y hy.2 hxy.symm).1⟩, rfl⟩
      · exact Or.inr hwKβ
      · exact Or.inr hwKβ
    rcases hw' with hw' | hw'
    · exact ⟨Kα, fun u hu => ⟨Or.inl (hKαA hu), Or.inl hu⟩, hpα sq hsqa'.le, hw', α 0, hα0Kα, h0⟩
    · exact ⟨Kβ, fun u hu => ⟨Or.inr hu, Or.inr (hKβB hu)⟩, hpβ vq hvq, hw', β 0, hβ0Kβ, hβ0⟩
  -- Janiszewski: `Ω(A) ∩ Ω(K_q) ⊆ Ω(X)`
  have hJ2 : (H \ fillH A) ∩ (H \ fillH (Kα ∪ Kβ)) ⊆ H \ fillH (A ∪ Kβ) := by
    have he : A ∪ (Kα ∪ Kβ) = A ∪ Kβ := by
      rw [← union_assoc, union_eq_self_of_subset_right hKαA]
    rw [← he]
    refine H_diff_fillH_inter_subset hcA hKq fun w hw => ?_
    have hw' : w ∈ Kα := by
      rcases hw with ⟨hwA, hwKα | hwKβ⟩
      · exact hwKα
      · obtain ⟨x, hx, rfl⟩ := hwA
        obtain ⟨y, hy, hxy⟩ := hwKβ
        exact ⟨x, ⟨zero_le, (hcon x hx.2 y (hy.2.trans hvq) hxy.symm).1⟩, rfl⟩
    exact ⟨Kα, fun u hu => ⟨hKαA hu, Or.inl hu⟩, hpα sq hsqa'.le, hw', α 0, hα0Kα, h0⟩
  -- Janiszewski: `Ω(B) ∩ Ω(K_q) ⊆ Ω(Y)`
  have hJ3 : (H \ fillH B) ∩ (H \ fillH (Kα ∪ Kβ)) ⊆ H \ fillH (Kα ∪ B) := by
    have he : B ∪ (Kα ∪ Kβ) = Kα ∪ B := by
      rw [union_comm Kα Kβ, ← union_assoc, union_eq_self_of_subset_right hKβB, union_comm B Kα]
    rw [← he]
    refine H_diff_fillH_inter_subset hcB hKq fun w hw => ?_
    have hw' : w ∈ Kβ := by
      rcases hw with ⟨hwB, hwKα | hwKβ⟩
      · obtain ⟨y, hy, rfl⟩ := hwB
        obtain ⟨x, hx, hxy⟩ := hwKα
        exact ⟨y, ⟨zero_le, (hcon x (hx.2.trans hsqa'.le) y hy.2 hxy).2⟩, rfl⟩
      · exact hwKβ
    exact ⟨Kβ, fun u hu => ⟨hKβB hu, Or.inr hu⟩, hpβ vq hvq, hw', β 0, hβ0Kβ, hβ0⟩
  -- the suffix after the last contact misses `Y` (hence `K_q`)
  have hsufY : ∀ t, sq < t → t ≤ a' → α t ∉ Kα ∪ B := by
    rintro t hst hta (⟨x, hx, hxt⟩ | ⟨y, hy, hyt⟩)
    · exact absurd (hαinj x t (hx.2.trans hsqa'.le) hta hxt ▸ hx.2) (not_le.2 hst)
    · exact absurd (hcon t hta y hy.2 hyt.symm).1 (not_le.2 hst)
  have hsufK : ∀ t, sq < t → t ≤ a' → α t ∉ Kα ∪ Kβ := by
    rintro t hst hta (h | h)
    · exact hsufY t hst hta (Or.inl h)
    · exact hsufY t hst hta (Or.inr (hKβB h))
  -- the old completions after the last contact miss `K_q`
  have htailK : ∀ t, sq < t → αn t ∉ Kα ∪ Kβ := by
    rintro t hst (⟨x, hx, hxt⟩ | ⟨y, hy, hyt⟩)
    · rw [← eα x (hx.2.trans hsqa.le)] at hxt
      exact absurd (Pα.2.1 hxt ▸ hx.2) (not_le.2 hst)
    · rw [← eβ y (hy.2.trans hvq)] at hyt
      exact absurd (contact_order Pα Pβ Pα0 Pβ0 Pseed hord hq hyt.symm hst) (not_lt.2 hy.2)
  have htailKβ : ∀ t, vq < t → βn t ∉ Kα ∪ Kβ := by
    rintro t hvt (⟨x, hx, hxt⟩ | ⟨y, hy, hyt⟩)
    · rw [← eα x (hx.2.trans hsqa.le)] at hxt
      rcases hx.2.lt_or_eq with hxs | hxs
      · exact absurd (contact_order Pα Pβ Pα0 Pβ0 Pseed hord hxt hq hxs) (not_lt.2 hvt.le)
      · rw [hxs, hq] at hxt
        exact absurd (Pβ.2.1 hxt) hvt.ne
    · rw [← eβ y (hy.2.trans hvq)] at hyt
      exact absurd (Pβ.2.1 hyt ▸ hy.2) (not_le.2 hvt)
  -- `K_q` is free at both tips (unbounded connected sets off `K_q`)
  have hpfree : IsFreeAt (Kα ∪ Kβ) (α a') := by
    refine isFreeAt_of_not_isBounded hKq.isClosed hKq.isBounded (X := αn '' Ioi sq ∪ α '' Ioc sq a')
      ?_ ?_ ?_ _ (Or.inr ⟨a', ⟨hsqa', le_rfl⟩, rfl⟩)
    · refine (isPreconnected_Ioi.image _ Pα.1.continuousOn).union (α a) ⟨a, hsqa, eα a le_rfl⟩
        ⟨a, ⟨hsqa, haa'.le⟩, rfl⟩ ?_
      rw [himα (fun t ht => ht.2)]
      exact isPreconnected_Ioc.image _ hS.1.1.continuousOn
    · exact fun hb => not_isBounded_image_Ioi Pα.2.2.2 sq (hb.subset subset_union_left)
    · rintro _ (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
      · exact ⟨Pα.2.2.1 t, htailK t ht⟩
      · exact ⟨hαH t ht.2, hsufK t ht.1 ht.2⟩
  have hrfree : vq < c → IsFreeAt (Kα ∪ Kβ) (β c) := fun hvc =>
    isFreeAt_of_not_isBounded hKq.isClosed hKq.isBounded (isPreconnected_Ioi.image _ Pβ.1.continuousOn)
      (not_isBounded_image_Ioi Pβ.2.2.2 vq) (by
        rintro _ ⟨t, ht, rfl⟩
        exact ⟨Pβ.2.2.1 t, htailKβ t ht⟩) _ ⟨c, hvc, eβ c le_rfl⟩
  -- the classification
  have hpX : α a' ∈ closure (H \ fillH (A ∪ Kβ)) :=
    closure_mono hJ2 (mem_closure_inter_of_isFreeAt hpA sdiff_subset hpfree)
  rcases mem_closure_or_isTrappedAt (As := α '' Ioc sq a') hcA (hcKα.union hcB) hJ1 hpX
      (by rw [himα (fun t ht => ht.2)]; exact isPreconnected_Ioc.image _ hS.1.1.continuousOn)
      ⟨a', ⟨hsqa', le_rfl⟩, rfl⟩
      (by rintro _ ⟨t, ht, rfl⟩; exact ⟨hαH t ht.2, hsufY t ht.1 ht.2⟩)
      (by
        rintro _ ⟨t, ht, rfl⟩
        by_cases hts : t ≤ sq
        · exact Or.inl (Or.inl ⟨t, ⟨zero_le, hts⟩, rfl⟩)
        · exact Or.inr ⟨t, ⟨not_le.1 hts, ht.2⟩, rfl⟩)
      (union_subset (hKαA.trans subset_union_left) subset_union_right) subset_union_right
      with h | ⟨hsub, htrap⟩
  · exact Or.inl h
  · rcases hvq.lt_or_eq with hvc | hvc
    · refine Or.inr ⟨closure_mono (hJ3.trans hsub)
        (mem_closure_inter_of_isFreeAt hrB sdiff_subset (hrfree hvc)), fun x hx hxy => ?_⟩
      exact absurd (hcon x (hx.trans haa'.le) c le_rfl hxy.symm).2 (not_le.2 hvc)
    · exfalso
      have hKB : Kβ = B := by rw [hKβdef, hBdef, hvc]
      exact hpfree.not_isTrappedAt (hαH a' le_rfl) (by rw [hKB]; exact htrap)

end Main

/-! ### Lemma W4, unconditionally in the deterministic input -/

section W4

/-- **Lemma W4 for the first path**: `𝓔(α([0, a]), β([0, c]))`, slit completions of `α([0, a'])` and `β([0, c])`, and
no new contact give `𝓔(α([0, a']), β([0, c]))`. -/
theorem hasOrderedProperCompletions_extend_left_of_isSlitCompletion {α β : ℝ≥0 → ℂ} {a a' c : ℝ≥0}
    (h : HasOrderedProperCompletions α a β c) (h0 : (α 0).im = 0) (hβ0 : (β 0).im = 0)
    (hseed : (β 0).re ≤ (α 0).re) (haa' : a < a') {S Sβ : ℝ≥0 → ℂ} (hS : IsSlitCompletion α a' S)
    (hSβ : IsSlitCompletion β c Sβ) (hnew : ∀ x ∈ Icc a a', ∀ y ∈ Icc 0 c, α x ≠ β y) :
    HasOrderedProperCompletions α a' β c :=
  hasOrderedProperCompletions_extend_left_of_access w4TipAccessStatement h h0 hβ0 hseed haa' hS hSβ hnew

/-- **Lemma W4 for the second path**, by reflection. -/
theorem hasOrderedProperCompletions_extend_right_of_isSlitCompletion {α β : ℝ≥0 → ℂ} {a c c' : ℝ≥0}
    (h : HasOrderedProperCompletions α a β c) (h0 : (α 0).im = 0) (hβ0 : (β 0).im = 0)
    (hseed : (β 0).re ≤ (α 0).re) (hcc' : c < c') {Sα Sβ : ℝ≥0 → ℂ} (hSα : IsSlitCompletion α a Sα)
    (hSβ : IsSlitCompletion β c' Sβ) (hnew : ∀ y ∈ Icc c c', ∀ x ∈ Icc 0 a, β y ≠ α x) :
    HasOrderedProperCompletions α a β c' :=
  hasOrderedProperCompletions_extend_right_of_access w4TipAccessStatement h h0 hβ0 hseed hcc' hSα hSβ hnew

/-- **Lemma W4, pathwise** (supplement p. 532): two curves from real seeds `β(0) ≤ α(0)` whose available prefixes all
have slit completions satisfy `ExtendsWithoutNewContact`. -/
theorem extendsWithoutNewContact_of_isSlitCompletion {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} (h0 : (α 0).im = 0)
    (hβ0 : (β 0).im = 0) (hseed : (β 0).re ≤ (α 0).re)
    (hslα : ∀ a : ℝ≥0, (a : ℝ≥0∞) < ζ₁ → ∃ S, IsSlitCompletion α a S)
    (hslβ : ∀ c : ℝ≥0, (c : ℝ≥0∞) < ζ₂ → ∃ S, IsSlitCompletion β c S) :
    Supp9.ExtendsWithoutNewContact α ζ₁ β ζ₂ :=
  extendsWithoutNewContact_of_slits w4TipAccessStatement h0 hβ0 hseed hslα hslβ

/-- **Lemma W4 on the frozen carriers** (`Supp9.W4Statement`, supplement p. 532), from the Aux. 25 interface alone
(`Theorem15.Aux25Statement`, packet PROVE-AUX25). -/
theorem w4Statement_of_aux25 (hA : Theorem15.Aux25Statement.{u}) : Supp9.W4Statement.{u} :=
  w4Statement_of_inputs hA w4TipAccessStatement

/-- **Theorem W5** (`Theorem15.W5Statement`, pp. 533–536) from `Supp9.w5Statement_of_inputs` with its W4 input
discharged by `w4Statement_of_aux25`: the remaining inputs are Aux. 25, W0a, W0b, W2 and the two local comparisons of
W5's proof. -/
theorem w5Statement_of_inputs_of_aux25 (h25 : Theorem15.Aux25Statement.{u}) (hW0a : Supp9.W0aStatement.{u})
    (hW0b : Supp9.W0bStatement.{u}) (hW2 : Supp9.W2Statement.{u}) (hCS : Supp9.W5CommonSeedStatement.{u})
    (hLF : Supp9.W5LocalFrameStatement.{u}) : Theorem15.W5Statement.{u} :=
  Supp9.w5Statement_of_inputs h25 hW0a hW0b hW2 (w4Statement_of_aux25 h25) hCS hLF

end W4

end Supp9B

end InteractingSLE
