/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S9CTip
import InteractingSLE.Foundations.Topology.PathComplement
import InteractingSLE.Foundations.Loewner.CapacityEstimates

/-!
# Supplement §9: joint activity of interior tips (Aux. lemma 90) and the opposite-hull exclusion of W1

Packet PROVE-W5-REST. Sources: Aux. lemma 90 (`source/spec/p289-336.md` L257–L262, pp. 306–307: "Let
`A = α([0, a])` and `B = β([0, b])` be finite simple Loewner prefixes admitting the actual closed-side ordered proper
completions in (OF1). Let `K_B` be the individual filled hull of the second prefix. If `p = α(a) ∈ ℍ \ K_B`, then
`p` is active for the joint unbounded component of `ℍ \ (A ∪ B)`. The reflected statement holds for the second
current tip outside the first individual hull"), and the proof of Lemma W1 (`source/spec/p529-576.md` L54–L56,
p. 530: "The point `p` is a future unvisited point of `β` after `s` […] Such a point is outside the older individual
filled hull. […] The connected fresh arc from `α(r)` to `p` avoids the second old range. […] Since its terminal point
is outside that hull, `α(r)` is outside as well. […] Aux. lemma 90 therefore gives joint activity of both interior
tips.").

The proof of Aux. 90 given here is planar topology only, without the conformal maps of the source proof: it uses
Janiszewski's theorem in `ℍ` (`HalfPlaneSep.H_diff_fillH_inter_subset`) at the last old contact, exactly as in the
proof of `Supp9B.w4TipAccessStatement`, together with the contact-order theorem `Supp9B.contact_order`.

Notation: `Ω(F) = ℍ \ fillH F` (the unbounded domain of `ℍ \ F`, for closed bounded `F`).

## Main results

* `mem_closure_of_isProperCompletion`: the tip of a prefix with a proper completion is accessible from `Ω(prefix)`.
* `aux90`: for prefixes with ordered proper completions, a tip that lies in the other prefix's unbounded domain
  (outside its individual filled hull) is accessible from the joint unbounded domain (both tips).
* `mem_H_diff_fillH_of_arc`: the opposite-hull exclusion of W1 — an arc which avoids a closed set `F` and ends at a
  point accessible from `Ω(F)` (off `F`) starts in `Ω(F)` when it starts in `ℍ`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex Bornology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Supp9D

open HalfPlaneSep Supp9B

/-! ### Free points are accessible -/

/-- A point of `ℍ̄` at which `F` is free is in the closure of `Ω(F)`. -/
theorem mem_closure_of_isFreeAt {F : Set ℂ} {z : ℂ} (hf : IsFreeAt F z) (hz : 0 ≤ z.im) :
    z ∈ closure (H \ fillH F) := by
  have hzH : z ∈ closure H := by rw [closure_H]; exact hz
  have h := mem_closure_inter_of_isFreeAt hzH subset_rfl hf
  exact closure_mono inter_subset_right h

/-- **The tip of a prefix with a proper completion is accessible** from the unbounded domain of the prefix: the
completion after the tip is an unbounded preconnected subset of `ℍ̄` off the prefix, so every one of its points is
free, and the tip is their limit. -/
theorem mem_closure_of_isProperCompletion {γ γ' : ℝ≥0 → ℂ} {a : ℝ≥0} (h : IsProperCompletion γ a γ') :
    γ a ∈ closure (H \ fillH (γ '' Icc 0 a)) := by
  have e : ∀ t ≤ a, γ' t = γ t := h.2.2.2.2
  have him : γ '' Icc 0 a = γ' '' Icc 0 a := image_congr fun t ht => (e t ht.2).symm
  rw [him, ← e a le_rfl]
  have hc : IsCompact (γ' '' Icc 0 a) := isCompact_Icc.image h.1
  have hfree : ∀ w ∈ γ' '' Ioi a, IsFreeAt (γ' '' Icc 0 a) w :=
    isFreeAt_of_not_isBounded hc.isClosed hc.isBounded (isPreconnected_Ioi.image _ h.1.continuousOn)
      (not_isBounded_image_Ioi h.2.2.2.1 a) (by
        rintro _ ⟨t, ht, rfl⟩
        refine ⟨h.2.2.1 t, ?_⟩
        rintro ⟨x, hx, hxt⟩
        exact absurd (h.2.1 hxt ▸ hx.2) (not_le.2 ht))
  have hsub : γ' '' Ioi a ⊆ closure (H \ fillH (γ' '' Icc 0 a)) := by
    rintro _ ⟨t, ht, rfl⟩
    exact mem_closure_of_isFreeAt (hfree _ ⟨t, ht, rfl⟩) (h.2.2.1 t)
  refine closure_minimal hsub isClosed_closure ?_
  have hlim : Tendsto γ' (𝓝[>] a) (𝓝 (γ' a)) := h.1.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact mem_closure_of_tendsto hlim (eventually_mem_nhdsWithin.mono fun t ht => ⟨t, ht, rfl⟩)

/-- A point of `Ω(F)` (closed bounded `F`) is free for `F`. -/
theorem isFreeAt_of_mem {F : Set ℂ} {z : ℂ} (hFb : IsBounded F) (hz : z ∈ H \ fillH F) : IsFreeAt F z := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isOpen_H_diff_fillH hFb) z hz
  exact ⟨ε, hε, fun w hw => hball hw.1⟩

/-- A point of `ℍ` at which a closed `F` is free lies in `Ω(F)`. -/
theorem mem_of_isFreeAt {F : Set ℂ} {z : ℂ} (hf : IsFreeAt F z) (hz : z ∈ H) : z ∈ H \ fillH F := by
  obtain ⟨ε, hε, h⟩ := hf
  exact h ⟨mem_ball_self hε, hz⟩

/-- The unbounded domain is antitone in the removed set. -/
theorem H_diff_fillH_anti {F G : Set ℂ} (hFG : F ⊆ G) : H \ fillH G ⊆ H \ fillH F :=
  fun _ hz => ⟨hz.1, fun h => hz.2 (fillH_mono hFG h)⟩

/-! ### The label of a closed set along an arc -/

/-- **The opposite-hull exclusion** (proof of Lemma W1, p. 530): along a preconnected set `X ⊆ ℍ̄ \ F` the label of
the closed set `F` is constant, so if one point `p ∈ X` is accessible from `Ω(F)`, every point of `X` in `ℍ` lies in
`Ω(F)` ("The connected fresh arc from `α(r)` to `p` avoids the second old range. […] Since its terminal point is
outside that hull, `α(r)` is outside as well"). -/
theorem mem_H_diff_fillH_of_arc {F X : Set ℂ} {p z : ℂ} (hF : IsClosed F) (hX : IsPreconnected X)
    (hXF : X ⊆ {w | 0 ≤ w.im} \ F) (hp : p ∈ X) (hpacc : p ∈ closure (H \ fillH F)) (hz : z ∈ X)
    (hzH : z ∈ H) : z ∈ H \ fillH F := by
  have hpfree : IsFreeAt F p := by
    rcases isFreeAt_or_isTrappedAt hF (hXF hp).2 with hf | ⟨ε, hε, hd⟩
    · exact hf
    · exfalso
      obtain ⟨w, hw, hwp⟩ := Metric.mem_closure_iff.1 hpacc ε hε
      exact Set.disjoint_left.1 hd (show w ∈ ball p ε by rw [mem_ball, dist_comm]; exact hwp) hw
  rcases isFreeAt_or_isTrappedAt_of_isPreconnected hF hX hXF with h | h
  · exact mem_of_isFreeAt (h z hz) hzH
  · exact absurd (h p hp) (hpfree.not_isTrappedAt (hXF hp).1)

/-- **A later point of a prefix is outside the earlier filled hull** (proof of Lemma W1, p. 530: "The point `p` is a
future unvisited point of `β` after `s` […] Such a point is outside the older individual filled hull"): if every
prefix `γ([0, v])`, `s < v < t`, has a proper completion and `γ` is continuous from the left at `t`, then `γ(t)` is
accessible from `Ω(γ([0, s]))`. -/
theorem mem_closure_of_later {γ : ℝ≥0 → ℂ} {s t : ℝ≥0} (hst : s < t)
    (hc : ContinuousWithinAt γ (Ioo s t) t)
    (hcomp : ∀ v, s < v → v < t → ∃ γ', IsProperCompletion γ v γ') :
    γ t ∈ closure (H \ fillH (γ '' Icc 0 s)) := by
  have hsub : γ '' Ioo s t ⊆ closure (H \ fillH (γ '' Icc 0 s)) := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨γ', hγ'⟩ := hcomp v hv.1 hv.2
    exact closure_mono (H_diff_fillH_anti (image_mono (Icc_subset_Icc_right hv.1.le)))
      (mem_closure_of_isProperCompletion hγ')
  refine closure_minimal hsub isClosed_closure ?_
  have : (𝓝[Ioo s t] t).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo hst.ne]
    exact ⟨hst.le, le_rfl⟩
  exact mem_closure_of_tendsto hc (eventually_mem_nhdsWithin.mono fun v hv => ⟨v, hv, rfl⟩)

/-! ### Aux. lemma 90 -/

/-- **Aux. lemma 90** (an ordered interior tip outside the other individual hull is active, pp. 306–307), for both
tips. Let `α([0, a])`, `β([0, c])` have ordered proper completions (`αn`, `βn` with `βn` in the closed left side of
`αn`) from real seeds `β(0) ≤ α(0)`. If the first tip lies in the unbounded domain of the second prefix, it is
accessible from the joint unbounded domain; and symmetrically for the second tip. The proof: Janiszewski's theorem
in `ℍ` at the last old contact `q = α(s_q) = β(v_q)`, with `K_q = α([0, s_q]) ∪ β([0, v_q])`; the completion tails
after `q` avoid `K_q` (contact order), so `K_q` is free at both tips. -/
theorem aux90 {α β αn βn : ℝ≥0 → ℂ} {a c : ℝ≥0} (hαn : IsProperCompletion α a αn)
    (hβn : IsProperCompletion β c βn) (hord : range βn ⊆ closedLeftSide αn) (h0 : (α 0).im = 0)
    (hβ0 : (β 0).im = 0) (hseed : (β 0).re ≤ (α 0).re) :
    (α a ∈ H \ fillH (β '' Icc 0 c) → α a ∈ closure (H \ fillH (α '' Icc 0 a ∪ β '' Icc 0 c))) ∧
    (β c ∈ H \ fillH (α '' Icc 0 a) → β c ∈ closure (H \ fillH (α '' Icc 0 a ∪ β '' Icc 0 c))) := by
  have eα : ∀ t ≤ a, αn t = α t := hαn.2.2.2.2
  have eβ : ∀ t ≤ c, βn t = β t := hβn.2.2.2.2
  have Pα := isProperCurve_of_isProperCompletion hαn
  have Pβ := isProperCurve_of_isProperCompletion hβn
  have Pα0 : (αn 0).im = 0 := by rw [eα 0 zero_le]; exact h0
  have Pβ0 : (βn 0).im = 0 := by rw [eβ 0 zero_le]; exact hβ0
  have Pseed : (βn 0).re ≤ (αn 0).re := by rw [eα 0 zero_le, eβ 0 zero_le]; exact hseed
  have himα : ∀ s ≤ a, α '' Icc 0 s = αn '' Icc 0 s := fun s hs =>
    image_congr fun t ht => (eα t (ht.2.trans hs)).symm
  have himβ : ∀ s ≤ c, β '' Icc 0 s = βn '' Icc 0 s := fun s hs =>
    image_congr fun t ht => (eβ t (ht.2.trans hs)).symm
  have hcα : ∀ s ≤ a, IsCompact (α '' Icc 0 s) := fun s hs => by
    rw [himα s hs]; exact isCompact_Icc.image Pα.1
  have hcβ : ∀ s ≤ c, IsCompact (β '' Icc 0 s) := fun s hs => by
    rw [himβ s hs]; exact isCompact_Icc.image Pβ.1
  have hpα : ∀ s ≤ a, IsPreconnected (α '' Icc 0 s) := fun s hs => by
    rw [himα s hs]; exact isPreconnected_Icc.image _ Pα.1.continuousOn
  have hpβ : ∀ s ≤ c, IsPreconnected (β '' Icc 0 s) := fun s hs => by
    rw [himβ s hs]; exact isPreconnected_Icc.image _ Pβ.1.continuousOn
  have hαacc := mem_closure_of_isProperCompletion hαn
  have hβacc := mem_closure_of_isProperCompletion hβn
  set A := α '' Icc 0 a with hAdef
  set B := β '' Icc 0 c with hBdef
  have hcA := hcα a le_rfl
  have hcB := hcβ c le_rfl
  have key : ∀ {p : ℂ} {X Y : Set ℂ} (V : Set ℂ), IsOpen V → p ∈ V → V ∩ H ⊆ H \ fillH Y →
      p ∈ closure (H \ fillH X) → (H \ fillH X) ∩ (H \ fillH Y) ⊆ H \ fillH (A ∪ B) →
      p ∈ closure (H \ fillH (A ∪ B)) := by
    intro p X Y V hV hpV hVY hpX hJ
    refine closure_mono ?_ (hV.inter_closure ⟨hpV, hpX⟩)
    rintro w ⟨hwV, hwX⟩
    exact hJ ⟨hwX, hVY ⟨hwV, hwX.1⟩⟩
  have hoA : IsOpen (H \ fillH A) := isOpen_H_diff_fillH hcA.isBounded
  have hoB : IsOpen (H \ fillH B) := isOpen_H_diff_fillH hcB.isBounded
  set Cs := {p : ℝ≥0 × ℝ≥0 | p ∈ Icc 0 a ×ˢ Icc 0 c ∧ αn p.1 = βn p.2} with hCs
  rcases Cs.eq_empty_or_nonempty with hCe | hCne
  · have hno : ∀ x ≤ a, ∀ y ≤ c, α x ≠ β y := by
      intro x hx y hy hxy
      have hmem : (x, y) ∈ Cs := ⟨⟨⟨zero_le, hx⟩, ⟨zero_le, hy⟩⟩, by rw [eα x hx, eβ y hy, hxy]⟩
      rw [hCe] at hmem
      exact hmem
    have hJ := H_diff_fillH_inter_subset hcA hcB (by
      rintro w ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
      exact absurd hxy.symm (hno x hx.2 y hy.2))
    refine ⟨fun hp => key (H \ fillH B) hoB hp inter_subset_left hαacc hJ,
      fun hp => key (H \ fillH A) hoA hp inter_subset_left hβacc (by rw [inter_comm]; exact hJ)⟩
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
  have hcon : ∀ x ≤ a, ∀ y ≤ c, α x = β y → x ≤ sq ∧ y ≤ vq := by
    intro x hx y hy hxy
    have hyv := hmax' x hx y hy hxy
    refine ⟨not_lt.1 fun hxs => ?_, hyv⟩
    have := contact_order Pα Pβ Pα0 Pβ0 Pseed hord hq
      (show αn x = βn y by rw [eα x hx, eβ y hy, hxy]) hxs
    exact absurd hyv (not_le.2 this)
  set Kα := α '' Icc 0 sq with hKαdef
  set Kβ := β '' Icc 0 vq with hKβdef
  have hKαA : Kα ⊆ A := image_mono (Icc_subset_Icc_right hsq)
  have hKβB : Kβ ⊆ B := image_mono (Icc_subset_Icc_right hvq)
  have hcKα : IsCompact Kα := hcα sq hsq
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
    · exact ⟨Kα, fun u hu => ⟨Or.inl (hKαA hu), Or.inl hu⟩, hpα sq hsq, hw', α 0, hα0Kα, h0⟩
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
    exact ⟨Kα, fun u hu => ⟨hKαA hu, Or.inl hu⟩, hpα sq hsq, hw', α 0, hα0Kα, h0⟩
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
        exact ⟨y, ⟨zero_le, (hcon x (hx.2.trans hsq) y hy.2 hxy).2⟩, rfl⟩
      · exact hwKβ
    exact ⟨Kβ, fun u hu => ⟨hKβB hu, Or.inr hu⟩, hpβ vq hvq, hw', β 0, hβ0Kβ, hβ0⟩
  -- the completion tails after the last contact miss `K_q`
  have htailK : ∀ t, sq < t → αn t ∉ Kα ∪ Kβ := by
    rintro t hst (⟨x, hx, hxt⟩ | ⟨y, hy, hyt⟩)
    · rw [← eα x (hx.2.trans hsq)] at hxt
      exact absurd (Pα.2.1 hxt ▸ hx.2) (not_le.2 hst)
    · rw [← eβ y (hy.2.trans hvq)] at hyt
      exact absurd (contact_order Pα Pβ Pα0 Pβ0 Pseed hord hq hyt.symm hst) (not_lt.2 hy.2)
  have htailKβ : ∀ t, vq < t → βn t ∉ Kα ∪ Kβ := by
    rintro t hvt (⟨x, hx, hxt⟩ | ⟨y, hy, hyt⟩)
    · rw [← eα x (hx.2.trans hsq)] at hxt
      rcases hx.2.lt_or_eq with hxs | hxs
      · exact absurd (contact_order Pα Pβ Pα0 Pβ0 Pseed hord hxt hq hxs) (not_lt.2 hvt.le)
      · rw [hxs, hq] at hxt
        exact absurd (Pβ.2.1 hxt) hvt.ne
    · rw [← eβ y (hy.2.trans hvq)] at hyt
      exact absurd (Pβ.2.1 hyt ▸ hy.2) (not_le.2 hvt)
  have hpfree : sq < a → IsFreeAt (Kα ∪ Kβ) (α a) := fun hsa =>
    isFreeAt_of_not_isBounded hKq.isClosed hKq.isBounded (isPreconnected_Ioi.image _ Pα.1.continuousOn)
      (not_isBounded_image_Ioi Pα.2.2.2 sq) (by
        rintro _ ⟨t, ht, rfl⟩
        exact ⟨Pα.2.2.1 t, htailK t ht⟩) _ ⟨a, hsa, eα a le_rfl⟩
  have hrfree : vq < c → IsFreeAt (Kα ∪ Kβ) (β c) := fun hvc =>
    isFreeAt_of_not_isBounded hKq.isClosed hKq.isBounded (isPreconnected_Ioi.image _ Pβ.1.continuousOn)
      (not_isBounded_image_Ioi Pβ.2.2.2 vq) (by
        rintro _ ⟨t, ht, rfl⟩
        exact ⟨Pβ.2.2.1 t, htailKβ t ht⟩) _ ⟨c, hvc, eβ c le_rfl⟩
  constructor
  · intro hp
    have hnB : α a ∉ B := (H_diff_fillH_subset_H_diff hcB.isClosed hp).2
    have hsa : sq < a := lt_of_le_of_ne hsq fun he =>
      hnB ⟨vq, ⟨zero_le, hvq⟩, by rw [← hq', he]⟩
    obtain ⟨ε, hε, hball⟩ := hpfree hsa
    have hpX : α a ∈ closure (H \ fillH (A ∪ Kβ)) :=
      closure_mono hJ2 (mem_closure_inter_of_isFreeAt hαacc sdiff_subset (hpfree hsa))
    refine key (Y := Kα ∪ B) ((H \ fillH B) ∩ ball (α a) ε) (hoB.inter isOpen_ball)
      ⟨hp, mem_ball_self hε⟩ ?_ hpX hJ1
    rintro w ⟨⟨hwB, hwb⟩, hwH⟩
    exact hJ3 ⟨hwB, hball ⟨hwb, hwH⟩⟩
  · intro hp
    have hnA : β c ∉ A := (H_diff_fillH_subset_H_diff hcA.isClosed hp).2
    have hvc : vq < c := lt_of_le_of_ne hvq fun he =>
      hnA ⟨sq, ⟨zero_le, hsq⟩, by rw [hq', he]⟩
    obtain ⟨ε, hε, hball⟩ := hrfree hvc
    have hpY : β c ∈ closure (H \ fillH (Kα ∪ B)) :=
      closure_mono hJ3 (mem_closure_inter_of_isFreeAt hβacc sdiff_subset (hrfree hvc))
    refine key (Y := A ∪ Kβ) ((H \ fillH A) ∩ ball (β c) ε) (hoA.inter isOpen_ball)
      ⟨hp, mem_ball_self hε⟩ ?_ hpY (by rw [inter_comm]; exact hJ1)
    rintro w ⟨⟨hwA, hwb⟩, hwH⟩
    exact hJ2 ⟨hwA, hball ⟨hwb, hwH⟩⟩

end Supp9D

end InteractingSLE
