/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Aux85Straddle
import InteractingSLE.Spec.Sec7.Lemma76GZone
import InteractingSLE.Spec.Supplement.RLCCGlue
import InteractingSLE.Spec.Supplement.S9BOrder

/-!
# Aux. lemma 85 in the retained chart: the setting, tail completions and the side split

Packet PROVE-T15-AUX85 (Aux. lemma 85, supplement pp. 299–300, read in the retained chart of Lemma G7, p. 497). Two
good paths `α` (from `x₁`, stop `a`) and `β` (from `x₂ ≤ x₁`, stop `b`) at a **touching** ordinary retained pair, with
the retained chart `(φ, ψ)` of `D = ℍ \ fill(α[0, a] ∪ β[0, b])` based at the second tip (`IsTSetting`).

* **Tail completions** (`exists_tail₁`, `exists_tail₂`): W0's ordered completions (part of the ordinary pair) can be
  chosen with the new part of the first (resp. second) curve inside the joint domain `D`, from its active tip
  (`Supp9B.exists_tail_of_mem_closure_jointDomain`); the other prefix then has a completion in the closed left side
  of the first (resp. the first prefix one in the closed right side of the second) — W0's transfer lemmas.
* **The side split** (`side_split`): for a proper curve `γ` that runs along the retained union up to `c` and then in
  `D`, with chart point `m` of `γ(c)`, every real chart point left of `m` is mapped into the closure of the left side
  of `γ`, and every one right of `m` into the closure of its right side. The chart image of the tail stays away from
  the real line except at `m`, so small half-discs at other real points are mapped into one side; the side is
  locally constant along `(−∞, m)` and `(m, ∞)` and is the expected one far away.
* **Consequences** (OF1 read in the chart): `0 < M₁` (the second tip precedes the first, `zero_lt_M₁`); a real chart
  point right of `M₁` on the union is on the first prefix (`mem₁_of_gt`), one left of `0` is on the second
  (`mem₂_of_lt`); the real points of the union lie in `[baseL β, baseR α]` (`re_le_baseR`, `baseL_le_re`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace RLC

namespace Aux85

open HalfPlaneSep Restart Supp7 Supp9B Sec7.Lemma76G

/-! ### The setting -/

/-- **The pathwise setting of Aux. lemma 85 at a touching pair**: two good paths at a touching ordinary retained
pair (`x₂ ≤ x₁`) and the retained chart based at the second tip. -/
structure IsTSetting (α : ℝ≥0 → ℂ) (ζ₁ : ℝ≥0∞) (x₁ : ℝ) (a : ℝ≥0) (β : ℝ≥0 → ℂ) (ζ₂ : ℝ≥0∞) (x₂ : ℝ)
    (b : ℝ≥0) (φ ψ : ℂ → ℂ) (lift : ℂ → ℝ) : Prop where
  hp₁ : IsPathGood α ζ₁ x₁
  hp₂ : IsPathGood β ζ₂ x₂
  hx : x₂ ≤ x₁
  hpair : IsOrdinaryRetainedPair α ζ₁ a β ζ₂ b
  htouch : ¬ Disjoint (α '' Icc 0 a) (β '' Icc 0 b)
  hC : IsRetChart α a β b φ ψ lift

namespace IsTSetting

variable {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ} {a b : ℝ≥0} {φ ψ : ℂ → ℂ} {lift : ℂ → ℝ}
  (hs : IsTSetting α ζ₁ x₁ a β ζ₂ x₂ b φ ψ lift)
include hs

theorem ha : (a : ℝ≥0∞) ≤ ζ₁ := hs.hpair.1.le

theorem hb : (b : ℝ≥0∞) ≤ ζ₂ := hs.hpair.2.1.le

theorem h0₁ : (α 0).im = 0 := by rw [Sec7.IsPathGood.zero hs.hp₁]; simp

theorem h0₂ : (β 0).im = 0 := by rw [Sec7.IsPathGood.zero hs.hp₂]; simp

theorem hc₁ : ContinuousOn α (Icc 0 a) := Sec7.IsPathGood.continuousOn_Icc hs.hp₁ hs.ha

theorem hc₂ : ContinuousOn β (Icc 0 b) := Sec7.IsPathGood.continuousOn_Icc hs.hp₂ hs.hb

theorem hi₁ : InjOn α (Icc 0 a) := Sec7.IsPathGood.injOn_Icc hs.hp₁ hs.ha

theorem hi₂ : InjOn β (Icc 0 b) := Sec7.IsPathGood.injOn_Icc hs.hp₂ hs.hb

theorem isCompact₁ : IsCompact (α '' Icc 0 a) := Sec7.IsPathGood.isCompact_image hs.hp₁ hs.ha

theorem isCompact₂ : IsCompact (β '' Icc 0 b) := Sec7.IsPathGood.isCompact_image hs.hp₂ hs.hb

theorem isCompact_K : IsCompact (prefixSet α a β b) := hs.isCompact₁.union hs.isCompact₂

theorem D_eq : activeDomain α a β b = H \ fillH (prefixSet α a β b) := activeDomain_eq hs.isCompact_K.isClosed

theorem ψc : ContinuousOn ψ Hbar := hs.hC.continuousOn_inv

theorem bijD : BijOn ψ H (activeDomain α a β b) := hs.hC.bijOn hs.h0₂

theorem bij : BijOn ψ H (H \ fillH (prefixSet α a β b)) := by rw [← hs.D_eq]; exact hs.bijD

theorem real : ∀ w ∉ H, ψ w ∉ H \ fillH (prefixSet α a β b) := by
  rw [← hs.D_eq]; exact hs.hC.inv_notMem hs.h0₂

theorem disp : ∃ M : ℝ, ∀ w ∈ Hbar, ‖ψ w - w‖ ≤ M := hs.hC.2.2.2.2.2.2.2.2.2.1

theorem ψ0 : ψ 0 = β b := hs.hC.inv_zero hs.h0₂

theorem im_nonneg {w : ℂ} (hw : w ∈ Hbar) : 0 ≤ (ψ w).im :=
  Sec7.Lemma76E.im_nonneg_of_mapsTo hs.ψc (fun _ hv => (hs.bij.mapsTo hv).1) hw

theorem D_subset_H : activeDomain α a β b ⊆ H := fun _ hz => (hs.D_eq ▸ hz).1

omit hs in
theorem notMem_D_of_mem_K {z : ℂ} (hz : z ∈ prefixSet α a β b) : z ∉ H \ fillH (prefixSet α a β b) :=
  fun h => h.2 ⟨h.1, Or.inl (subset_closure hz)⟩

theorem notMem_activeDomain_of_mem_K {z : ℂ} (hz : z ∈ prefixSet α a β b) : z ∉ activeDomain α a β b := by
  rw [hs.D_eq]; exact notMem_D_of_mem_K hz

theorem im₁ : ∀ z ∈ α '' Icc 0 a, 0 ≤ z.im := by
  rintro _ ⟨s, hs', rfl⟩
  exact Sec7.IsPathGood.im_nonneg hs.hp₁ ((ENNReal.coe_le_coe.2 hs'.2).trans hs.ha)

theorem im₂ : ∀ z ∈ β '' Icc 0 b, 0 ≤ z.im := by
  rintro _ ⟨t, ht, rfl⟩
  exact Sec7.IsPathGood.im_nonneg hs.hp₂ ((ENNReal.coe_le_coe.2 ht.2).trans hs.hb)

theorem imK : ∀ z ∈ prefixSet α a β b, 0 ≤ z.im := by
  rintro z (h | h)
  · exact hs.im₁ z h
  · exact hs.im₂ z h

theorem pc₁ : IsPreconnected (α '' Icc 0 a) := isPreconnected_Icc.image _ hs.hc₁

theorem pc₂ : IsPreconnected (β '' Icc 0 b) := isPreconnected_Icc.image _ hs.hc₂

/-- **The union of touching prefixes is connected.** -/
theorem pcK : IsPreconnected (prefixSet α a β b) := by
  obtain ⟨z, hz₁, hz₂⟩ := not_disjoint_iff.1 hs.htouch
  exact IsPreconnected.union z hz₁ hz₂ hs.pc₁ hs.pc₂

theorem seed₁ : ((x₁ : ℝ) : ℂ) ∈ α '' Icc 0 a := ⟨0, ⟨le_rfl, zero_le⟩, Sec7.IsPathGood.zero hs.hp₁⟩

theorem seed₂ : ((x₂ : ℝ) : ℂ) ∈ β '' Icc 0 b := ⟨0, ⟨le_rfl, zero_le⟩, Sec7.IsPathGood.zero hs.hp₂⟩

omit hs in
theorem tip₁_mem : α a ∈ α '' Icc 0 a := ⟨a, ⟨zero_le, le_rfl⟩, rfl⟩

omit hs in
theorem tip₂_mem : β b ∈ β '' Icc 0 b := ⟨b, ⟨zero_le, le_rfl⟩, rfl⟩

theorem tip₁_H : α a ∈ H := hs.hpair.2.2.1

theorem tip₂_H : β b ∈ H := hs.hpair.2.2.2.1

theorem tip₂_notMem : β b ∉ α '' Icc 0 a := hs.hpair.2.2.2.2.1

theorem tip₁_notMem : α a ∉ β '' Icc 0 b := hs.hpair.2.2.2.2.2.1

theorem tip₁_cl : α a ∈ closure (activeDomain α a β b) := hs.hpair.2.2.2.2.2.2.1

theorem tip₂_cl : β b ∈ closure (activeDomain α a β b) := hs.hpair.2.2.2.2.2.2.2.1

theorem hord : HasOrderedProperCompletions α a β b := hs.hpair.2.2.2.2.2.2.2.2

theorem hseed : (β 0).re ≤ (α 0).re := by
  rw [Sec7.IsPathGood.zero hs.hp₁, Sec7.IsPathGood.zero hs.hp₂]; simpa using hs.hx

/-- **Every real chart point is on a prefix or an untouched real point.** -/
theorem inv_cases (w : ℝ) : ψ w ∈ α '' Icc 0 a ∨ ψ w ∈ β '' Icc 0 b ∨
    ((ψ w).im = 0 ∧ ψ w ∉ prefixSet α a β b) := by
  by_cases hK : ψ w ∈ prefixSet α a β b
  · rcases hK with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨?_, hK⟩)
    by_contra hne
    have hH : ψ w ∈ H := lt_of_le_of_ne (hs.im_nonneg (ofReal_mem_Hbar w)) (Ne.symm hne)
    exact hK (inv_mem_prefixSet_of_real hs.hC hs.h0₂ hs.hc₁ hs.hc₂ hH)

theorem inv_mem_closure (w : ℝ) : ψ w ∈ closure (activeDomain α a β b) :=
  Supp7.inv_mem_closure hs.hC hs.h0₂ (ofReal_mem_Hbar w)

/-! ### Chart points of regular points -/

/-- **The chart point of a regular point off the domain**: the forward limit is a real point mapped back to it, and
it is its only chart preimage in `ℍ̄`. -/
theorem chartPt_spec {z : ℂ} (hz : z ∈ closure (activeDomain α a β b)) (hzD : z ∉ activeDomain α a β b)
    (hreg : IsChartRegularPoint α a β b z) :
    Tendsto φ (𝓝[activeDomain α a β b] z) (𝓝 ((chartPt φ (activeDomain α a β b) z : ℝ) : ℂ)) ∧
      ψ (chartPt φ (activeDomain α a β b) z) = z ∧
      ∀ w ∈ Hbar, ψ w = z → w = ((chartPt φ (activeDomain α a β b) z : ℝ) : ℂ) := by
  obtain ⟨w₀, hw₀, hlim, hψ, huniq⟩ := hs.hC.exists_tendsto_of_regular hs.h0₂ hz hreg
  have hw₀r : w₀.im = 0 := by
    by_contra hne
    have hH : w₀ ∈ H := lt_of_le_of_ne hw₀ (Ne.symm hne)
    exact hzD (hψ ▸ hs.bijD.mapsTo hH)
  have := mem_closure_iff_nhdsWithin_neBot.1 hz
  have hlu : limUnder (𝓝[activeDomain α a β b] z) φ = w₀ := hlim.limUnder_eq
  have hcp : ((chartPt φ (activeDomain α a β b) z : ℝ) : ℂ) = w₀ := by
    rw [chartPt, hlu]; exact Restart.ofReal_re_eq hw₀r
  rw [hcp]
  exact ⟨hlim, hψ, huniq⟩

/-- The chart point of the first tip. -/
theorem chartPt_tip₁ :
    Tendsto φ (𝓝[activeDomain α a β b] (α a)) (𝓝 ((chartPt φ (activeDomain α a β b) (α a) : ℝ) : ℂ)) ∧
      ψ (chartPt φ (activeDomain α a β b) (α a)) = α a ∧
      ∀ w ∈ Hbar, ψ w = α a → w = ((chartPt φ (activeDomain α a β b) (α a) : ℝ) : ℂ) :=
  hs.chartPt_spec hs.tip₁_cl (hs.notMem_activeDomain_of_mem_K (Or.inl (tip₁_mem (α := α) (a := a))))
    (RLC.isChartRegularPoint_tip₁ hs.hc₁ hs.hc₂ hs.h0₁ hs.h0₂ hs.tip₁_notMem hs.hi₁)

/-- `0` is the only chart preimage of the second tip. -/
theorem eq_zero_of_inv_eq_tip₂ {w : ℂ} (hw : w ∈ Hbar) (he : ψ w = β b) : w = 0 :=
  RLC.eq_of_inv_eq_of_regular hs.hC hs.h0₂ (RLC.isChartRegularPoint_tip₂ hs.hc₁ hs.hc₂ hs.h0₁ hs.h0₂
    hs.tip₂_notMem (fun t ht he' => (ne_of_lt ht) (hs.hi₂ ⟨zero_le, ht.le⟩ ⟨zero_le, le_rfl⟩ he')))
    (show (0 : ℂ) ∈ Hbar by simp [Hbar]) hs.ψ0 hw he

/-- The forward chart tends to `0` at the second tip. -/
theorem tendsto_tip₂ : Tendsto φ (𝓝[activeDomain α a β b] (β b)) (𝓝 ((0 : ℝ) : ℂ)) := by
  rw [ofReal_zero]; exact (hs.hC.isActiveChart hs.h0₂).2.2.1

theorem φ_mapsTo : MapsTo φ (activeDomain α a β b) H := (hs.hC.isActiveChart hs.h0₂).1.mapsTo

theorem φ_cont : ContinuousOn φ (activeDomain α a β b) := (hs.hC.isActiveChart hs.h0₂).2.1.continuousOn

theorem ψφ {z : ℂ} (hz : z ∈ activeDomain α a β b) : ψ (φ z) = z := by
  obtain ⟨v, hv, rfl⟩ := hs.bijD.surjOn hz
  rw [hs.hC.fwd_inv v hv]

/-! ### The side split -/

/-- **The chart image of a tail in the domain avoids every real point but its start**: if `γ` is a proper curve
whose points after `c` lie in `D` and `φ → m` at `γ(c)`, then every real `w ≠ m` has a ball missing `φ(γ((c, ∞)))`. -/
theorem exists_ball_tail {γ : ℝ≥0 → ℂ} {c : ℝ≥0} {m : ℝ} (hγ : IsProperCurve γ)
    (hγD : ∀ t, c < t → γ t ∈ activeDomain α a β b)
    (hlim : Tendsto φ (𝓝[activeDomain α a β b] (γ c)) (𝓝 ((m : ℝ) : ℂ))) {w : ℝ} (hw : w ≠ m) :
    ∃ ε > 0, ∀ t, c < t → φ (γ t) ∉ ball ((w : ℝ) : ℂ) ε := by
  obtain ⟨Md, hMd⟩ := hs.disp
  have hnear : Tendsto (fun t => φ (γ t)) (𝓝[>] c) (𝓝 ((m : ℝ) : ℂ)) := by
    have h1 : Tendsto γ (𝓝[>] c) (𝓝[activeDomain α a β b] (γ c)) :=
      tendsto_nhdsWithin_iff.2 ⟨(hγ.1.tendsto c).mono_left nhdsWithin_le_nhds,
        eventually_nhdsWithin_of_forall fun t ht => hγD t ht⟩
    exact hlim.comp h1
  set d : ℝ := |w - m| / 2 with hd
  have hd0 : 0 < d := half_pos (abs_pos.2 (sub_ne_zero.2 hw))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hnear (ball_mem_nhds _ hd0))
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 (tendsto_atTop.1 hγ.2.2.2 (|w| + 1 + Md))
  set T : ℝ≥0 := max T₀ u with hT
  obtain ⟨u', hcu', hu'u⟩ := exists_between (show c < u from hu)
  have hmaps : MapsTo γ (Icc u' T) (activeDomain α a β b) := fun t ht => hγD t (hcu'.trans_le ht.1)
  have hcomp : IsCompact ((fun t => φ (γ t)) '' Icc u' T) :=
    isCompact_Icc.image_of_continuousOn (hs.φ_cont.comp hγ.1.continuousOn hmaps)
  have hwnot : ((w : ℝ) : ℂ) ∉ (fun t => φ (γ t)) '' Icc u' T := by
    rintro ⟨t, ht, he⟩
    have h1 : (0 : ℝ) < (φ (γ t)).im := hs.φ_mapsTo (hmaps ht)
    have he' : φ (γ t) = ((w : ℝ) : ℂ) := he
    rw [he'] at h1
    simp at h1
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.isOpen_iff.1 hcomp.isClosed.isOpen_compl _ hwnot
  refine ⟨min d (min 1 ε₁), lt_min hd0 (lt_min one_pos hε₁), fun t ht hmem => ?_⟩
  rw [mem_ball] at hmem
  have hm1 := min_le_left d (min 1 ε₁)
  have hm2 := (min_le_right d (min 1 ε₁)).trans (min_le_left 1 ε₁)
  have hm3 := (min_le_right d (min 1 ε₁)).trans (min_le_right 1 ε₁)
  rcases lt_or_ge t u with htu | htu
  · have h1 : φ (γ t) ∈ ball ((m : ℝ) : ℂ) d := hsub ⟨ht, htu⟩
    rw [mem_ball] at h1
    have h2 : dist ((w : ℝ) : ℂ) ((m : ℝ) : ℂ) = 2 * d := by
      rw [dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs, hd]; ring
    have h3 := dist_triangle ((w : ℝ) : ℂ) (φ (γ t)) ((m : ℝ) : ℂ)
    rw [dist_comm] at hmem
    linarith
  · rcases le_or_gt t T with htT | htT
    · exact hball (mem_ball.2 (lt_of_lt_of_le hmem hm3)) ⟨t, ⟨hu'u.le.trans htu, htT⟩, rfl⟩
    · have h1 := hT₀ t ((le_max_left T₀ u).trans htT.le)
      have hD := hγD t ht
      have h2 := hMd (φ (γ t)) (Sec7.Lemma76Exit.H_subset_Hbar (hs.φ_mapsTo hD))
      rw [hs.ψφ hD] at h2
      have h3 := norm_sub_norm_le (γ t) (φ (γ t))
      have h4 := norm_sub_norm_le (φ (γ t)) ((w : ℝ) : ℂ)
      rw [← dist_eq_norm, norm_real, Real.norm_eq_abs] at h4
      linarith

/-- **The side split.** Let `γ` be a proper curve from a real seed, on the retained union up to `c` and in `D` after
`c`, whose start `γ(c)` has chart point `m` (`φ → m` along `D`). Then real chart points left of `m` are mapped into
the closure of the left side of `γ`, and real chart points right of `m` into the closure of its right side. -/
theorem side_split {γ : ℝ≥0 → ℂ} {c : ℝ≥0} {m : ℝ} (hγ : IsProperCurve γ) (hγ0 : (γ 0).im = 0)
    (hγK : ∀ t ≤ c, γ t ∈ prefixSet α a β b) (hγD : ∀ t, c < t → γ t ∈ activeDomain α a β b)
    (hlim : Tendsto φ (𝓝[activeDomain α a β b] (γ c)) (𝓝 ((m : ℝ) : ℂ))) :
    (∀ w : ℝ, w < m → ψ w ∈ closure (leftSide γ)) ∧ (∀ w : ℝ, m < w → ψ w ∈ closure (rightSide γ)) := by
  obtain ⟨Md, hMd⟩ := hs.disp
  have hMd0 : 0 ≤ Md := (norm_nonneg _).trans (hMd 0 (by simp [Hbar]))
  -- half-discs at real points other than `m` are mapped into one side
  have hHB : ∀ (w : ℝ) (ε : ℝ), IsPreconnected (ψ '' (ball ((w : ℝ) : ℂ) ε ∩ H)) := fun w ε =>
    (isPreconnected_ball_inter_H _ _).image _ (hs.ψc.mono fun z hz => Sec7.Lemma76Exit.H_subset_Hbar hz.2)
  have hsides : ∀ w : ℝ, w ≠ m → ∃ ε > 0, ψ '' (ball ((w : ℝ) : ℂ) ε ∩ H) ⊆ leftSide γ ∨
      ψ '' (ball ((w : ℝ) : ℂ) ε ∩ H) ⊆ rightSide γ := by
    intro w hw
    obtain ⟨ε, hε, hcl⟩ := hs.exists_ball_tail hγ hγD hlim hw
    refine ⟨ε, hε, (hHB w ε).subset_or_subset (isOpen_leftSide hγ) (isOpen_rightSide hγ)
      (disjoint_leftSide_rightSide hγ hγ0) ?_⟩
    rw [← compl_seedRayClosure_eq hγ hγ0]
    rintro _ ⟨v, hv, rfl⟩ hS
    have hvD := hs.bijD.mapsTo hv.2
    rcases hS with ⟨t, ht⟩ | ⟨-, him⟩
    · rcases le_or_gt t c with htc | htc
      · exact hs.notMem_activeDomain_of_mem_K (hγK t htc) (by rw [ht]; exact hvD)
      · refine hcl t htc ?_
        rw [ht, hs.hC.fwd_inv v hv.2]
        exact hv.1
    · rw [hγ0] at him
      exact absurd (hs.D_subset_H hvD) (not_lt.2 him)
  -- the two side labels
  have hopen : ∀ S : Set ℂ, IsOpen {w : ℝ | ∃ ε > 0, ψ '' (ball ((w : ℝ) : ℂ) ε ∩ H) ⊆ S} := by
    intro S
    refine Metric.isOpen_iff.2 fun w ⟨ε, hε, hsub⟩ => ⟨ε / 2, half_pos hε, fun w' hw' => ⟨ε / 2, half_pos hε, ?_⟩⟩
    refine (image_mono (inter_subset_inter_left _ (ball_subset_ball' ?_))).trans hsub
    rw [mem_ball, Real.dist_eq] at hw'
    rw [dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs]
    linarith
  have hdisj : ∀ w : ℝ, (∃ ε > 0, ψ '' (ball ((w : ℝ) : ℂ) ε ∩ H) ⊆ rightSide γ) →
      (∃ ε > 0, ψ '' (ball ((w : ℝ) : ℂ) ε ∩ H) ⊆ leftSide γ) → False := by
    rintro w ⟨ε, hε, hR⟩ ⟨ε', hε', hL⟩
    set δ : ℝ := min ε ε' / 2 with hδdef
    have hδ : 0 < δ := half_pos (lt_min hε hε')
    set q : ℂ := (w : ℂ) + (δ : ℂ) * I with hq
    have hqH : q ∈ H := show 0 < q.im by simp [hq, hδ]
    have hqd : dist q (w : ℂ) = δ := by
      rw [dist_eq_norm, hq, add_sub_cancel_left, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs,
        abs_of_pos hδ]
    have h1 : q ∈ ball ((w : ℝ) : ℂ) ε ∩ H := ⟨mem_ball.2 (by rw [hqd]; linarith [min_le_left ε ε']), hqH⟩
    have h2 : q ∈ ball ((w : ℝ) : ℂ) ε' ∩ H := ⟨mem_ball.2 (by rw [hqd]; linarith [min_le_right ε ε']), hqH⟩
    exact Set.disjoint_left.1 (disjoint_leftSide_rightSide hγ hγ0) (hL ⟨q, h2, rfl⟩) (hR ⟨q, h1, rfl⟩)
  have hcl : ∀ (w : ℝ) (S : Set ℂ), (∃ ε > 0, ψ '' (ball ((w : ℝ) : ℂ) ε ∩ H) ⊆ S) → ψ w ∈ closure S := by
    rintro w S ⟨ε, hε, hsub⟩
    have hwcl : ((w : ℝ) : ℂ) ∈ closure (ball ((w : ℝ) : ℂ) ε ∩ H) := by
      refine Metric.mem_closure_iff.2 fun δ hδ => ?_
      set η : ℝ := min ε δ / 2 with hηdef
      have hη : 0 < η := half_pos (lt_min hε hδ)
      have hd : dist ((w : ℂ) + (η : ℂ) * I) (w : ℂ) = η := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs,
          abs_of_pos hη]
      refine ⟨(w : ℂ) + (η : ℂ) * I, ⟨mem_ball.2 ?_, show 0 < ((w : ℂ) + (η : ℂ) * I).im by simp [hη]⟩, ?_⟩
      · rw [hd]; linarith [min_le_left ε δ]
      · rw [dist_comm, hd]; linarith [min_le_right ε δ]
    have hcw : ContinuousWithinAt ψ (ball ((w : ℝ) : ℂ) ε ∩ H) (w : ℂ) :=
      (hs.ψc _ (ofReal_mem_Hbar w)).mono fun z hz => Sec7.Lemma76Exit.H_subset_Hbar hz.2
    exact closure_mono hsub (hcw.mem_closure_image hwcl)
  -- far away the side is the expected one
  obtain ⟨R₀, hR₀⟩ := hs.isCompact_K.isBounded.subset_ball 0
  have hγ0n : ‖γ 0‖ < R₀ := by have := hR₀ (hγK 0 zero_le); rwa [mem_ball_zero_iff] at this
  have hR₀pos : 0 < R₀ := lt_of_le_of_lt (norm_nonneg _) hγ0n
  have hfar : ∀ w : ℝ, R₀ + Md < |w| → (ψ w).im = 0 ∧ |(ψ w).re - w| ≤ Md := by
    intro w hw
    have h1 := hMd w (ofReal_mem_Hbar w)
    refine ⟨?_, ?_⟩
    · by_contra hne
      have hH : ψ w ∈ H := lt_of_le_of_ne (hs.im_nonneg (ofReal_mem_Hbar w)) (Ne.symm hne)
      have hK := inv_mem_prefixSet_of_real hs.hC hs.h0₂ hs.hc₁ hs.hc₂ hH
      have h2 := hR₀ hK
      rw [mem_ball_zero_iff] at h2
      have h3 := norm_sub_norm_le ((w : ℝ) : ℂ) (ψ w)
      rw [norm_sub_rev, norm_real, Real.norm_eq_abs] at h3
      linarith
    · have h2 := Complex.abs_re_le_norm (ψ w - w)
      rw [sub_re, ofReal_re] at h2
      linarith
  have hnotγ : ∀ y : ℝ, R₀ < |y| → ((y : ℝ) : ℂ) ∉ range γ := by
    rintro y hy ⟨t, ht⟩
    rcases le_or_gt t c with htc | htc
    · have := hR₀ (hγK t htc)
      rw [mem_ball_zero_iff, ht, norm_real, Real.norm_eq_abs] at this
      linarith
    · have := hs.D_subset_H (hγD t htc)
      rw [ht] at this
      exact absurd this (by simp [H])
  have hside : ∀ (w : ℝ) (S : Set ℂ), IsOpen S → ψ w ∈ S →
      ∃ ε > 0, ψ '' (ball ((w : ℝ) : ℂ) ε ∩ H) ⊆ S := by
    intro w S hS hwS
    obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.1 hS _ hwS
    obtain ⟨δ, hδ, hcont⟩ := Metric.continuousWithinAt_iff.1 (hs.ψc _ (ofReal_mem_Hbar w)) ε₀ hε₀
    refine ⟨δ, hδ, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    exact hball (mem_ball.2 (hcont (Sec7.Lemma76Exit.H_subset_Hbar hv.2) (mem_ball.1 hv.1)))
  have hfarR : ∀ w : ℝ, R₀ + Md < w → ∃ ε > 0, ψ '' (ball ((w : ℝ) : ℂ) ε ∩ H) ⊆ rightSide γ := by
    intro w hw
    have hw' : R₀ + Md < |w| := lt_of_lt_of_le hw (le_abs_self w)
    obtain ⟨him, hre⟩ := hfar w hw'
    have hψy : ψ w = (((ψ w).re : ℝ) : ℂ) := (Restart.ofReal_re_eq him).symm
    have hy : R₀ < (ψ w).re := by linarith [(abs_le.1 hre).1]
    have hy0 : (γ 0).re < (ψ w).re := by linarith [Complex.re_le_norm (γ 0)]
    have hyR := RLC.ofReal_mem_rightSide_of_notMem hγ hγ0 hy0
      (hnotγ _ (lt_of_lt_of_le hy (le_abs_self _)))
    rw [← hψy] at hyR
    exact hside w _ (isOpen_rightSide hγ) hyR
  have hfarL : ∀ w : ℝ, w < -(R₀ + Md) → ∃ ε > 0, ψ '' (ball ((w : ℝ) : ℂ) ε ∩ H) ⊆ leftSide γ := by
    intro w hw
    have hw' : R₀ + Md < |w| := by rw [abs_of_neg (by linarith)]; linarith
    obtain ⟨him, hre⟩ := hfar w hw'
    have hψy : ψ w = (((ψ w).re : ℝ) : ℂ) := (Restart.ofReal_re_eq him).symm
    have hy : (ψ w).re < -R₀ := by linarith [(abs_le.1 hre).2]
    have hy0 : (ψ w).re < (γ 0).re := by
      have := Complex.abs_re_le_norm (γ 0)
      linarith [neg_abs_le (γ 0).re]
    have hyL := RLC.ofReal_mem_leftSide_of_notMem hγ hγ0 hy0
      (hnotγ _ (by rw [abs_of_neg (by linarith)]; linarith))
    rw [← hψy] at hyL
    exact hside w _ (isOpen_leftSide hγ) hyL
  have hcover : ∀ w : ℝ, w ≠ m → w ∈ {w : ℝ | ∃ ε > 0, ψ '' (ball ((w : ℝ) : ℂ) ε ∩ H) ⊆ rightSide γ} ∪
      {w : ℝ | ∃ ε > 0, ψ '' (ball ((w : ℝ) : ℂ) ε ∩ H) ⊆ leftSide γ} := fun w hw => by
    obtain ⟨ε, hε, h | h⟩ := hsides w hw
    · exact Or.inr ⟨ε, hε, h⟩
    · exact Or.inl ⟨ε, hε, h⟩
  have hdisjRL : Disjoint {w : ℝ | ∃ ε > 0, ψ '' (ball ((w : ℝ) : ℂ) ε ∩ H) ⊆ rightSide γ}
      {w : ℝ | ∃ ε > 0, ψ '' (ball ((w : ℝ) : ℂ) ε ∩ H) ⊆ leftSide γ} :=
    Set.disjoint_left.2 fun w h1 h2 => hdisj w h1 h2
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · rcases isPreconnected_Iio.subset_or_subset (hopen _) (hopen _) hdisjRL
      (fun w' hw' => hcover w' (ne_of_lt hw')) with h | h
    · exfalso
      set w₀ : ℝ := min (m - 1) (-(R₀ + Md) - 1) with hw₀
      have h1 : w₀ < m := (min_le_left _ _).trans_lt (by linarith)
      exact hdisj w₀ (h h1) (hfarL w₀ ((min_le_right _ _).trans_lt (by linarith)))
    · exact hcl w _ (h hw)
  · rcases isPreconnected_Ioi.subset_or_subset (hopen _) (hopen _) hdisjRL
      (fun w' hw' => hcover w' (ne_of_gt hw')) with h | h
    · exact hcl w _ (h hw)
    · exfalso
      set w₀ : ℝ := max (m + 1) (R₀ + Md + 1) with hw₀
      have h1 : m < w₀ := by have := le_max_left (m + 1) (R₀ + Md + 1); linarith
      exact hdisj w₀ (hfarR w₀ (by have := le_max_right (m + 1) (R₀ + Md + 1); linarith)) (h h1)

/-! ### Tail completions through the joint domain -/

theorem inv_notMem_D (w : ℝ) : ψ w ∉ activeDomain α a β b :=
  hs.hC.inv_notMem hs.h0₂ _ fun h => (lt_irrefl (0 : ℝ)) (by simpa using (show (0 : ℝ) < ((w : ℝ) : ℂ).im from h))

theorem jointDomain_eq : jointDomain α a β b = activeDomain α a β b := by
  rw [jointDomain, hs.D_eq]; rfl

theorem hH₁ : MapsTo α (Icc 0 a) Hbar := fun s hs' => show (0 : ℝ) ≤ (α s).im from hs.im₁ _ ⟨s, hs', rfl⟩

theorem hH₂ : MapsTo β (Icc 0 b) Hbar := fun t ht => show (0 : ℝ) ≤ (β t).im from hs.im₂ _ ⟨t, ht, rfl⟩

/-- **A completion of the first prefix through the joint domain** (W0 with the first curve continued from its active
tip inside `D`), together with a completion of the second prefix in its closed left side. -/
theorem exists_tail₁ : ∃ α'' : ℝ≥0 → ℂ, IsProperCompletion α a α'' ∧
    (∀ t, a < t → α'' t ∈ activeDomain α a β b) ∧
    ∃ β₃ : ℝ≥0 → ℂ, IsProperCompletion β b β₃ ∧ range β₃ ⊆ closedLeftSide α'' := by
  obtain ⟨α', β', hα', hβ', hordc⟩ := hs.hord
  obtain ⟨T, hTc, hTi, hT0, hTD, hTn⟩ := exists_tail_of_mem_closure_jointDomain hs.hc₁ hs.hc₂ hs.hH₁ hs.hH₂
    hs.h0₁ hs.h0₂ (p := α a) (by rw [hs.jointDomain_eq]; exact hs.tip₁_cl)
  rw [hs.jointDomain_eq] at hTD
  have hTP : IsProperCurve T := isProperCurve_of_tail hTc hTi
    (by rw [hT0]; exact (show (0 : ℝ) < (α a).im from hs.tip₁_H).le) (fun t ht => hs.D_subset_H (hTD t ht)) hTn
  have hα'a : α' a = α a := hα'.2.2.2.2 a le_rfl
  have hdisj : ∀ u < a, ∀ s, α' u ≠ T s := by
    intro u hu s he
    rw [hα'.2.2.2.2 u hu.le] at he
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with hs0 | hs0
    · rw [← hs0, hT0] at he
      exact (ne_of_lt hu) (hs.hi₁ ⟨zero_le, hu.le⟩ ⟨zero_le, le_rfl⟩ he)
    · have := hTD s hs0
      rw [← he] at this
      exact hs.notMem_activeDomain_of_mem_K (Or.inl ⟨u, ⟨zero_le, hu.le⟩, rfl⟩) this
  have hα'' := isProperCompletion_junction_tail hα' hTP (by rw [hT0, hα'a]) hdisj
  have htailD : ∀ t, a < t → junction α' T a 0 t ∈ activeDomain α a β b := fun t ht => by
    rw [junction_tail_of_lt ht]; exact hTD _ (tsub_pos_of_lt ht)
  refine ⟨_, hα'', htailD,
    exists_isProperCompletion_subset_closedLeftSide hα' hβ' hordc hs.h0₁ hs.h0₂ hs.hseed hα'' ?_⟩
  intro s hsa y hy he
  rcases eq_or_lt_of_le hsa with rfl | hlt
  · rw [hα''.2.2.2.2 _ le_rfl] at he
    exact hs.tip₁_notMem ⟨y, ⟨zero_le, hy⟩, he.symm⟩
  · have := htailD s hlt
    rw [he] at this
    exact hs.notMem_activeDomain_of_mem_K (Or.inr ⟨y, ⟨zero_le, hy⟩, rfl⟩) this

/-- **A completion of the second prefix through the joint domain**, with a completion of the first prefix in its
closed right side. -/
theorem exists_tail₂ : ∃ β'' : ℝ≥0 → ℂ, IsProperCompletion β b β'' ∧
    (∀ t, b < t → β'' t ∈ activeDomain α a β b) ∧
    ∃ α₃ : ℝ≥0 → ℂ, IsProperCompletion α a α₃ ∧ range α₃ ⊆ closedRightSide β'' := by
  obtain ⟨-, β', -, hβ', -⟩ := hs.hord
  obtain ⟨T, hTc, hTi, hT0, hTD, hTn⟩ := exists_tail_of_mem_closure_jointDomain hs.hc₁ hs.hc₂ hs.hH₁ hs.hH₂
    hs.h0₁ hs.h0₂ (p := β b) (by rw [hs.jointDomain_eq]; exact hs.tip₂_cl)
  rw [hs.jointDomain_eq] at hTD
  have hTP : IsProperCurve T := isProperCurve_of_tail hTc hTi
    (by rw [hT0]; exact (show (0 : ℝ) < (β b).im from hs.tip₂_H).le) (fun t ht => hs.D_subset_H (hTD t ht)) hTn
  have hβ'b : β' b = β b := hβ'.2.2.2.2 b le_rfl
  have hdisj : ∀ u < b, ∀ s, β' u ≠ T s := by
    intro u hu s he
    rw [hβ'.2.2.2.2 u hu.le] at he
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with hs0 | hs0
    · rw [← hs0, hT0] at he
      exact (ne_of_lt hu) (hs.hi₂ ⟨zero_le, hu.le⟩ ⟨zero_le, le_rfl⟩ he)
    · have := hTD s hs0
      rw [← he] at this
      exact hs.notMem_activeDomain_of_mem_K (Or.inr ⟨u, ⟨zero_le, hu.le⟩, rfl⟩) this
  have hβ'' := isProperCompletion_junction_tail hβ' hTP (by rw [hT0, hβ'b]) hdisj
  have htailD : ∀ t, b < t → junction β' T b 0 t ∈ activeDomain α a β b := fun t ht => by
    rw [junction_tail_of_lt ht]; exact hTD _ (tsub_pos_of_lt ht)
  have htail' : ∀ s, b ≤ s → ∀ x ≤ a, junction β' T b 0 s ≠ α x := by
    intro s hsb x hx he
    rcases eq_or_lt_of_le hsb with rfl | hlt
    · rw [hβ''.2.2.2.2 _ le_rfl] at he
      exact hs.tip₂_notMem ⟨x, ⟨zero_le, hx⟩, he.symm⟩
    · have := htailD s hlt
      rw [he] at this
      exact hs.notMem_activeDomain_of_mem_K (Or.inl ⟨x, ⟨zero_le, hx⟩, rfl⟩) this
  obtain ⟨αn, hαn, hordn⟩ := exists_completion_left_of_tail hs.hord hs.h0₁ hs.h0₂ hs.hseed hβ'' htail'
  refine ⟨_, hβ'', htailD, αn, hαn, ?_⟩
  have e₁ : αn 0 = α 0 := hαn.2.2.2.2 0 zero_le
  have e₂ : junction β' T b 0 0 = β 0 := hβ''.2.2.2.2 0 zero_le
  exact range_subset_closedRightSide (isProperCurve_of_isProperCompletion hαn)
    (isProperCurve_of_isProperCompletion hβ'') (by rw [e₁]; exact hs.h0₁) (by rw [e₂]; exact hs.h0₂)
    (by rw [e₁, e₂]; exact hs.hseed) hordn

omit hs in
theorem mem_seedRay_of_closure_right {γ : ℝ≥0 → ℂ} (hγ : IsProperCurve γ) (hγ0 : (γ 0).im = 0) {z : ℂ}
    (h1 : z ∈ closure (rightSide γ)) (h2 : z ∈ closedLeftSide γ) : z ∈ seedRayClosure γ := by
  rcases h2 with h | h
  · exfalso
    obtain ⟨y, hyL, hyR⟩ := mem_closure_iff.1 h1 _ (isOpen_leftSide hγ) h
    exact Set.disjoint_left.1 (disjoint_leftSide_rightSide hγ hγ0) hyL hyR
  · exact h

omit hs in
theorem mem_seedRay_of_closure_left {γ : ℝ≥0 → ℂ} (hγ : IsProperCurve γ) (hγ0 : (γ 0).im = 0) {z : ℂ}
    (h1 : z ∈ closure (leftSide γ)) (h2 : z ∈ closedRightSide γ) : z ∈ seedRayClosure γ := by
  rcases h2 with h | h
  · exfalso
    obtain ⟨y, hyR, hyL⟩ := mem_closure_iff.1 h1 _ (isOpen_rightSide hγ) h
    exact Set.disjoint_left.1 (disjoint_leftSide_rightSide hγ hγ0) hyL hyR
  · exact h

omit hs in
/-- A point off the domain on a completion through the domain (or its seed ray) is on the prefix. -/
theorem mem_image_of_mem_seedRay {γ γ' : ℝ≥0 → ℂ} {c : ℝ≥0} (hγ' : IsProperCompletion γ c γ')
    (hγ0 : (γ 0).im = 0) (htail : ∀ t, c < t → γ' t ∈ activeDomain α a β b) {z : ℂ}
    (hz : z ∈ seedRayClosure γ') (hzD : z ∉ activeDomain α a β b) (hzim : 0 ≤ z.im) : z ∈ γ '' Icc 0 c := by
  have e0 : γ' 0 = γ 0 := hγ'.2.2.2.2 0 zero_le
  rcases hz with ⟨t, rfl⟩ | ⟨hre, him⟩
  · rcases le_or_gt t c with htc | htc
    · exact ⟨t, ⟨zero_le, htc⟩, (hγ'.2.2.2.2 t htc).symm⟩
    · exact absurd (htail t htc) hzD
  · rw [e0, hγ0] at him
    have hz0 : z.im = 0 := le_antisymm him hzim
    rw [e0] at hre
    exact ⟨0, ⟨le_rfl, zero_le⟩, Complex.ext hre.symm (by rw [hγ0, hz0])⟩

/-! ### Consequences in the chart -/

/-- **The second tip precedes the first in the chart** (`0 < M₁`). -/
theorem zero_lt_M₁ : 0 < chartPt φ (activeDomain α a β b) (α a) := by
  obtain ⟨α'', hα'', htail, β₃, hβ₃, hord₃⟩ := hs.exists_tail₁
  have hP := isProperCurve_of_isProperCompletion hα''
  have h0'' : (α'' 0).im = 0 := by rw [hα''.2.2.2.2 0 zero_le]; exact hs.h0₁
  have hsplit := hs.side_split hP h0'' (fun t ht => Or.inl ⟨t, ⟨zero_le, ht⟩, (hα''.2.2.2.2 t ht).symm⟩) htail
    (by rw [hα''.2.2.2.2 a le_rfl]; exact hs.chartPt_tip₁.1)
  by_contra hle
  push Not at hle
  have hne : chartPt φ (activeDomain α a β b) (α a) ≠ 0 := by
    intro h0
    have := hs.chartPt_tip₁.2.1
    rw [h0, ofReal_zero, hs.ψ0] at this
    exact hs.tip₂_notMem (this ▸ (tip₁_mem (α := α) (a := a)))
  have h1 := hsplit.2 0 (lt_of_le_of_ne hle hne)
  rw [ofReal_zero, hs.ψ0] at h1
  have h2 : β b ∈ closedLeftSide α'' := hord₃ ⟨b, hβ₃.2.2.2.2 b le_rfl⟩
  have h3 := mem_seedRay_of_closure_right hP h0'' h1 h2
  exact hs.tip₂_notMem (mem_image_of_mem_seedRay hα'' hs.h0₁ htail h3
    (hs.notMem_activeDomain_of_mem_K (Or.inr (tip₂_mem (β := β) (b := b)))) (show (0 : ℝ) < (β b).im from hs.tip₂_H).le)

/-- **Right of the first tip, the union is the first prefix** (its right side; OF1 in the chart). -/
theorem mem₁_of_gt {w : ℝ} (hw : chartPt φ (activeDomain α a β b) (α a) < w)
    (hK : ψ w ∈ prefixSet α a β b) : ψ w ∈ α '' Icc 0 a := by
  obtain ⟨α'', hα'', htail, β₃, hβ₃, hord₃⟩ := hs.exists_tail₁
  have hP := isProperCurve_of_isProperCompletion hα''
  have h0'' : (α'' 0).im = 0 := by rw [hα''.2.2.2.2 0 zero_le]; exact hs.h0₁
  have hsplit := hs.side_split hP h0'' (fun t ht => Or.inl ⟨t, ⟨zero_le, ht⟩, (hα''.2.2.2.2 t ht).symm⟩) htail
    (by rw [hα''.2.2.2.2 a le_rfl]; exact hs.chartPt_tip₁.1)
  rcases hK with h | ⟨t, ht, he⟩
  · exact h
  · have h2 : ψ w ∈ closedLeftSide α'' := hord₃ ⟨t, by rw [hβ₃.2.2.2.2 t ht.2, he]⟩
    have h3 := mem_seedRay_of_closure_right hP h0'' (hsplit.2 w hw) h2
    exact mem_image_of_mem_seedRay hα'' hs.h0₁ htail h3 (hs.inv_notMem_D w) (hs.im_nonneg (ofReal_mem_Hbar w))

/-- **Left of the second tip, the union is the second prefix** (its left side; OF1 in the chart). -/
theorem mem₂_of_lt {w : ℝ} (hw : w < 0) (hK : ψ w ∈ prefixSet α a β b) : ψ w ∈ β '' Icc 0 b := by
  obtain ⟨β'', hβ'', htail, α₃, hα₃, hord₃⟩ := hs.exists_tail₂
  have hP := isProperCurve_of_isProperCompletion hβ''
  have h0'' : (β'' 0).im = 0 := by rw [hβ''.2.2.2.2 0 zero_le]; exact hs.h0₂
  have hsplit := hs.side_split hP h0'' (fun t ht => Or.inr ⟨t, ⟨zero_le, ht⟩, (hβ''.2.2.2.2 t ht).symm⟩) htail
    (by rw [hβ''.2.2.2.2 b le_rfl]; exact hs.tendsto_tip₂)
  rcases hK with ⟨s, hs', he⟩ | h
  · have h2 : ψ w ∈ closedRightSide β'' := hord₃ ⟨s, by rw [hα₃.2.2.2.2 s hs'.2, he]⟩
    have h3 := mem_seedRay_of_closure_left hP h0'' (hsplit.1 w hw) h2
    exact mem_image_of_mem_seedRay hβ'' hs.h0₂ htail h3 (hs.inv_notMem_D w) (hs.im_nonneg (ofReal_mem_Hbar w))
  · exact h

/-- **The real points of the second prefix are left of the first base's right end.** -/
theorem re_le_baseR {z : ℂ} (hz : z ∈ β '' Icc 0 b) (hz0 : z.im = 0) : z.re ≤ baseR α a := by
  by_contra hlt
  push Not at hlt
  obtain ⟨α'', hα'', htail, β₃, hβ₃, hord₃⟩ := hs.exists_tail₁
  have hP := isProperCurve_of_isProperCompletion hα''
  have e0 : α'' 0 = α 0 := hα''.2.2.2.2 0 zero_le
  have h0'' : (α'' 0).im = 0 := by rw [e0]; exact hs.h0₁
  have hx₁ : (α'' 0).re < z.re := by
    rw [e0, Sec7.IsPathGood.zero hs.hp₁, ofReal_re]
    exact (seed_le_baseR hs.hp₁ hs.ha).trans_lt hlt
  have hz' : z = ((z.re : ℝ) : ℂ) := (Restart.ofReal_re_eq hz0).symm
  have h2 : z ∈ closedLeftSide α'' := by
    obtain ⟨t, ht, he⟩ := hz
    exact hord₃ ⟨t, by rw [hβ₃.2.2.2.2 t ht.2, he]⟩
  by_cases hS : z ∈ seedRayClosure α''
  · have hzD : z ∉ activeDomain α a β b := fun h => by
      have h' : (0 : ℝ) < z.im := hs.D_subset_H h
      rw [hz0] at h'
      exact lt_irrefl _ h'
    have := mem_image_of_mem_seedRay hα'' hs.h0₁ htail hS hzD (by rw [hz0])
    exact absurd (re_mem_Icc_base hs.hp₁ hs.ha this hz0).2 (not_le.2 hlt)
  · rw [hz'] at hS h2
    have hR := RLC.ofReal_mem_rightSide hP.2.2.1 h0'' hx₁ hS
    rcases h2 with hL | hS'
    · exact Set.disjoint_left.1 (disjoint_leftSide_rightSide hP h0'') hL hR
    · exact hS hS'

/-- **The real points of the first prefix are right of the second base's left end.** -/
theorem baseL_le_re {z : ℂ} (hz : z ∈ α '' Icc 0 a) (hz0 : z.im = 0) : baseL β b ≤ z.re := by
  by_contra hlt
  push Not at hlt
  obtain ⟨β'', hβ'', htail, α₃, hα₃, hord₃⟩ := hs.exists_tail₂
  have hP := isProperCurve_of_isProperCompletion hβ''
  have e0 : β'' 0 = β 0 := hβ''.2.2.2.2 0 zero_le
  have h0'' : (β'' 0).im = 0 := by rw [e0]; exact hs.h0₂
  have hx₂ : z.re < (β'' 0).re := by
    rw [e0, Sec7.IsPathGood.zero hs.hp₂, ofReal_re]
    exact hlt.trans_le (baseL_le_seed hs.hp₂ hs.hb)
  have hz' : z = ((z.re : ℝ) : ℂ) := (Restart.ofReal_re_eq hz0).symm
  have h2 : z ∈ closedRightSide β'' := by
    obtain ⟨s, hs', he⟩ := hz
    exact hord₃ ⟨s, by rw [hα₃.2.2.2.2 s hs'.2, he]⟩
  by_cases hS : z ∈ seedRayClosure β''
  · have hzD : z ∉ activeDomain α a β b := fun h => by
      have h' : (0 : ℝ) < z.im := hs.D_subset_H h
      rw [hz0] at h'
      exact lt_irrefl _ h'
    have := mem_image_of_mem_seedRay hβ'' hs.h0₂ htail hS hzD (by rw [hz0])
    exact absurd (re_mem_Icc_base hs.hp₂ hs.hb this hz0).1 (not_le.2 hlt)
  · rw [hz'] at hS h2
    have hL := Supp9B.ofReal_mem_leftSide hP.2.2.1 h0'' hx₂ hS
    rcases h2 with hR | hS'
    · exact Set.disjoint_left.1 (disjoint_leftSide_rightSide hP h0'') hL hR
    · exact hS hS'

end IsTSetting

end Aux85

end RLC

end InteractingSLE
