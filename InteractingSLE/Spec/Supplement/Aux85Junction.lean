/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Aux85Zones

/-!
# Aux. lemma 85 in the retained chart: the junction, and `RetTouchZonesStatement`

Packet PROVE-T15-AUX85 (Aux. lemma 85, supplement pp. 299–300). In the setting `Aux85.IsTSetting` (two good paths
`α`, `β` at a touching ordinary retained pair, retained chart `ψ` with the second tip at `0` and the first at `M₁`):

* **The last common point** (`exists_isLastContact`): by W0's contact order (Aux. lemma 84,
  `Supp9B.contact_order`) the last common point `w* = α(s₀) = β(t₀)` is last in both orders, so the suffixes
  `α((s₀, a])` and `β((t₀, b])` miss the other prefix.
* **The fork** `α([s₀, a]) ∪ β([t₀, b])` carries every real chart point of `(0, M₁)` (`mem_fork`): a point of an older
  part would be straddled by the two tips (no straddling, `Aux85.false_of_straddle`).
* **The junction** `J₀ = inf {w ∈ [0, M₁] : ψ(w) ∈ α([0, a])}` (`IsJunction`): `(0, J₀)` is mapped onto the second
  suffix (its right side), `ψ(J₀) = w*`, and `(J₀, M₁)` onto the first suffix (its left side); a second visit of the
  second suffix after `J₀`, or a visit of the first suffix before a later visit of `w*`, would straddle; `ψ` is not
  constant on an interval (`exists_ne_of_injOn`).
* `junction ψ β b M₁ = J₀` (`junction_eq`), and the touching zone data satisfy (OF2) (`IsTSetting.isTouchZones`):
  **`retTouchZonesStatement`** proves `RLC.RetTouchZonesStatement`.

Deterministic; no named input.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace RLC

namespace Aux85

open HalfPlaneSep Restart Supp7 Supp9B Sec7.Lemma76G RetChart RetTouch

/-- **The last common point** of two prefixes, last in both orders: `α(s₀) = β(t₀)` and the two suffixes after it miss
the other prefix. -/
structure IsLastContact (α : ℝ≥0 → ℂ) (a : ℝ≥0) (β : ℝ≥0 → ℂ) (b : ℝ≥0) (s₀ t₀ : ℝ≥0) : Prop where
  s₀_lt : s₀ < a
  t₀_lt : t₀ < b
  eq : α s₀ = β t₀
  sufβ : ∀ t, t₀ < t → t ≤ b → β t ∉ α '' Icc 0 a
  sufα : ∀ s, s₀ < s → s ≤ a → α s ∉ β '' Icc 0 b

namespace IsTSetting

variable {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ} {a b : ℝ≥0} {φ ψ : ℂ → ℂ} {lift : ℂ → ℝ}
  (hs : IsTSetting α ζ₁ x₁ a β ζ₂ x₂ b φ ψ lift)
include hs

/-! ### The last common point -/

/-- **Contact order** (Aux. lemma 84) for the two prefixes. -/
theorem contact {s s' t t' : ℝ≥0} (hs₁ : s ≤ a) (hs₂ : s' ≤ a) (ht₁ : t ≤ b) (ht₂ : t' ≤ b) (h1 : α s = β t)
    (h2 : α s' = β t') (hss : s < s') : t < t' := by
  obtain ⟨α', β', hα', hβ', hordc⟩ := hs.hord
  have e₁ : α' 0 = α 0 := hα'.2.2.2.2 0 zero_le
  have e₂ : β' 0 = β 0 := hβ'.2.2.2.2 0 zero_le
  exact contact_order (isProperCurve_of_isProperCompletion hα') (isProperCurve_of_isProperCompletion hβ')
    (by rw [e₁]; exact hs.h0₁) (by rw [e₂]; exact hs.h0₂) (by rw [e₁, e₂]; exact hs.hseed) hordc
    (by rw [hα'.2.2.2.2 s hs₁, hβ'.2.2.2.2 t ht₁, h1]) (by rw [hα'.2.2.2.2 s' hs₂, hβ'.2.2.2.2 t' ht₂, h2]) hss

/-- **The last common point exists.** -/
theorem exists_isLastContact : ∃ s₀ t₀ : ℝ≥0, IsLastContact α a β b s₀ t₀ := by
  set Tc : Set ℝ≥0 := Icc 0 b ∩ β ⁻¹' (α '' Icc 0 a) with hTc
  have hTcc : IsClosed Tc := hs.hc₂.preimage_isClosed_of_isClosed isClosed_Icc hs.isCompact₁.isClosed
  obtain ⟨z, hzA, ⟨t, ht, rfl⟩⟩ := not_disjoint_iff.1 hs.htouch
  have hne : Tc.Nonempty := ⟨t, ht, hzA⟩
  have hbdd : BddAbove Tc := ⟨b, fun t' ht' => ht'.1.2⟩
  set t₀ := sSup Tc with ht₀
  have ht₀m : t₀ ∈ Tc := hTcc.csSup_mem hne hbdd
  obtain ⟨s₀, hs₀, he⟩ := ht₀m.2
  have hsufβ : ∀ t', t₀ < t' → t' ≤ b → β t' ∉ α '' Icc 0 a := fun t' h1 h2 h3 =>
    absurd (le_csSup hbdd ⟨⟨zero_le, h2⟩, h3⟩) (not_le.2 h1)
  have ht₀b : t₀ < b := lt_of_le_of_ne ht₀m.1.2 fun h => hs.tip₂_notMem (h ▸ ht₀m.2)
  have hs₀a : s₀ < a := lt_of_le_of_ne hs₀.2 fun h => hs.tip₁_notMem (by rw [← h, he]; exact ⟨t₀, ht₀m.1, rfl⟩)
  refine ⟨s₀, t₀, hs₀a, ht₀b, he, hsufβ, fun s h1 h2 ⟨t', ht', he'⟩ => ?_⟩
  have := hs.contact hs₀.2 h2 ht₀m.1.2 ht'.2 he he'.symm h1
  exact hsufβ t' this ht'.2 ⟨s, ⟨zero_le, h2⟩, he'.symm⟩

/-! ### No straddling in the setting -/

/-- `Aux85.false_of_straddle` for subsets of the retained union. -/
theorem false_of_straddle_K {X Y : Set ℂ} (hXc : IsCompact X) (hXpc : IsPreconnected X)
    (hXK : X ⊆ prefixSet α a β b) (hYpc : IsPreconnected Y) (hYK : Y ⊆ prefixSet α a β b) (hXY : Disjoint X Y)
    {x₀ : ℝ} (hx₀ : ((x₀ : ℝ) : ℂ) ∈ X) {wX wY wY' : ℝ} (hwX : ψ wX ∈ X) (hwY : ψ wY ∈ Y) (hwY' : ψ wY' ∈ Y)
    (h1 : wY < wX) (h2 : wX < wY') : False := by
  obtain ⟨M, hM⟩ := hs.disp
  exact false_of_straddle hs.isCompact_K hs.ψc hs.bij hs.real hM hXc hXpc (fun z hz => hs.imK z (hXK hz))
    (fun z hz => notMem_D_of_mem_K (hXK hz)) (hs.isCompact_K.isBounded.subset hYK) hYpc
    (fun z hz => hs.imK z (hYK hz)) (fun z hz => notMem_D_of_mem_K (hYK hz)) hXY hx₀ hwX hwY hwY' h1 h2

/-! ### The fork and the two suffixes -/

variable {s₀ t₀ : ℝ≥0} (hl : IsLastContact α a β b s₀ t₀)
include hl

theorem fork_pc : IsPreconnected (α '' Icc s₀ a ∪ β '' Icc t₀ b) :=
  IsPreconnected.union (α s₀) ⟨s₀, ⟨le_rfl, hl.s₀_lt.le⟩, rfl⟩ ⟨t₀, ⟨le_rfl, hl.t₀_lt.le⟩, hl.eq.symm⟩
    (isPreconnected_Icc.image _ (hs.hc₁.mono (Icc_subset_Icc_left zero_le)))
    (isPreconnected_Icc.image _ (hs.hc₂.mono (Icc_subset_Icc_left zero_le)))

omit hs hl in
theorem fork_K : α '' Icc s₀ a ∪ β '' Icc t₀ b ⊆ prefixSet α a β b := by
  rintro _ (⟨s, hs', rfl⟩ | ⟨t, ht, rfl⟩)
  · exact Or.inl ⟨s, ⟨zero_le, hs'.2⟩, rfl⟩
  · exact Or.inr ⟨t, ⟨zero_le, ht.2⟩, rfl⟩

omit hs in
theorem tip₁_fork : α a ∈ α '' Icc s₀ a ∪ β '' Icc t₀ b := Or.inl ⟨a, ⟨hl.s₀_lt.le, le_rfl⟩, rfl⟩

omit hs in
theorem tip₂_fork : β b ∈ α '' Icc s₀ a ∪ β '' Icc t₀ b := Or.inr ⟨b, ⟨hl.t₀_lt.le, le_rfl⟩, rfl⟩

/-- An earlier piece of the first prefix misses the fork. -/
theorem disjoint_fork₁ {σ : ℝ≥0} (hσ : σ < s₀) : Disjoint (α '' Icc 0 σ) (α '' Icc s₀ a ∪ β '' Icc t₀ b) := by
  rw [Set.disjoint_left]
  rintro _ ⟨s, hs', rfl⟩ (⟨s', hs'', he⟩ | ⟨t, ht, he⟩)
  · have := hs.hi₁ ⟨zero_le, hs''.2⟩ ⟨zero_le, hs'.2.trans (hσ.le.trans hl.s₀_lt.le)⟩ he
    exact absurd (this ▸ hs''.1) (not_le.2 (lt_of_le_of_lt hs'.2 hσ))
  · rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h, ← hl.eq] at he
      have := hs.hi₁ ⟨zero_le, hl.s₀_lt.le⟩ ⟨zero_le, hs'.2.trans (hσ.le.trans hl.s₀_lt.le)⟩ he
      exact absurd (this ▸ hs'.2) (not_le.2 hσ)
    · exact hl.sufβ t h ht.2 ⟨s, ⟨zero_le, hs'.2.trans (hσ.le.trans hl.s₀_lt.le)⟩, he.symm⟩

/-- An earlier piece of the second prefix misses the fork. -/
theorem disjoint_fork₂ {τ : ℝ≥0} (hτ : τ < t₀) : Disjoint (β '' Icc 0 τ) (α '' Icc s₀ a ∪ β '' Icc t₀ b) := by
  rw [Set.disjoint_left]
  rintro _ ⟨t, ht, rfl⟩ (⟨s, hs', he⟩ | ⟨t', ht', he⟩)
  · rcases eq_or_lt_of_le hs'.1 with h | h
    · rw [← h, hl.eq] at he
      have := hs.hi₂ ⟨zero_le, hl.t₀_lt.le⟩ ⟨zero_le, ht.2.trans (hτ.le.trans hl.t₀_lt.le)⟩ he
      exact absurd (this ▸ ht.2) (not_le.2 hτ)
    · exact hl.sufα s h hs'.2 ⟨t, ⟨zero_le, ht.2.trans (hτ.le.trans hl.t₀_lt.le)⟩, he.symm⟩
  · have := hs.hi₂ ⟨zero_le, ht'.2⟩ ⟨zero_le, ht.2.trans (hτ.le.trans hl.t₀_lt.le)⟩ he
    exact absurd (this ▸ ht'.1) (not_le.2 (lt_of_le_of_lt ht.2 hτ))

/-- **Every real chart point of `(0, M₁)` is on the fork.** -/
theorem mem_fork {w : ℝ} (h0 : 0 < w) (hM : w < chartPt φ (activeDomain α a β b) (α a)) :
    ψ w ∈ α '' Icc s₀ a ∪ β '' Icc t₀ b := by
  have hK := hs.mem_K_of_mem_Icc (hs.L₂_le_zero.trans h0.le) (hM.le.trans hs.M₁_le_R₁)
  have hw0 : ψ ((0 : ℝ) : ℂ) ∈ α '' Icc s₀ a ∪ β '' Icc t₀ b := by
    rw [ofReal_zero, hs.ψ0]; exact tip₂_fork hl
  have hwM : ψ (chartPt φ (activeDomain α a β b) (α a)) ∈ α '' Icc s₀ a ∪ β '' Icc t₀ b := by
    rw [hs.chartPt_tip₁.2.1]; exact tip₁_fork hl
  rcases hK with ⟨σ, hσ, he⟩ | ⟨τ, hτ, he⟩
  · by_cases hσs : s₀ ≤ σ
    · exact Or.inl ⟨σ, ⟨hσs, hσ.2⟩, he⟩
    · push Not at hσs
      exact (hs.false_of_straddle_K (isCompact_Icc.image_of_continuousOn
        (hs.hc₁.mono (Icc_subset_Icc_right (hσs.le.trans hl.s₀_lt.le))))
        (isPreconnected_Icc.image _ (hs.hc₁.mono (Icc_subset_Icc_right (hσs.le.trans hl.s₀_lt.le))))
        (fun z ⟨s, hs', hz⟩ => Or.inl ⟨s, ⟨zero_le, hs'.2.trans (hσs.le.trans hl.s₀_lt.le)⟩, hz⟩)
        (hs.fork_pc hl) fork_K (hs.disjoint_fork₁ hl hσs)
        (⟨0, ⟨le_rfl, zero_le⟩, Sec7.IsPathGood.zero hs.hp₁⟩ : ((x₁ : ℝ) : ℂ) ∈ α '' Icc 0 σ)
        ⟨σ, ⟨zero_le, le_rfl⟩, he⟩ hw0 hwM h0 hM).elim
  · by_cases hτt : t₀ ≤ τ
    · exact Or.inr ⟨τ, ⟨hτt, hτ.2⟩, he⟩
    · push Not at hτt
      exact (hs.false_of_straddle_K (isCompact_Icc.image_of_continuousOn
        (hs.hc₂.mono (Icc_subset_Icc_right (hτt.le.trans hl.t₀_lt.le))))
        (isPreconnected_Icc.image _ (hs.hc₂.mono (Icc_subset_Icc_right (hτt.le.trans hl.t₀_lt.le))))
        (fun z ⟨t, ht, hz⟩ => Or.inr ⟨t, ⟨zero_le, ht.2.trans (hτt.le.trans hl.t₀_lt.le)⟩, hz⟩)
        (hs.fork_pc hl) fork_K (hs.disjoint_fork₂ hl hτt)
        (⟨0, ⟨le_rfl, zero_le⟩, Sec7.IsPathGood.zero hs.hp₂⟩ : ((x₂ : ℝ) : ℂ) ∈ β '' Icc 0 τ)
        ⟨τ, ⟨zero_le, le_rfl⟩, he⟩ hw0 hwM h0 hM).elim

/-! ### The junction -/

theorem X₁_isCompact : IsCompact (α '' Icc 0 a ∪ β '' Icc 0 t₀) :=
  hs.isCompact₁.union (isCompact_Icc.image_of_continuousOn (hs.hc₂.mono (Icc_subset_Icc_right hl.t₀_lt.le)))

theorem X₁_pc : IsPreconnected (α '' Icc 0 a ∪ β '' Icc 0 t₀) :=
  IsPreconnected.union (α s₀) ⟨s₀, ⟨zero_le, hl.s₀_lt.le⟩, rfl⟩ ⟨t₀, ⟨zero_le, le_rfl⟩, hl.eq.symm⟩ hs.pc₁
    (isPreconnected_Icc.image _ (hs.hc₂.mono (Icc_subset_Icc_right hl.t₀_lt.le)))

omit hs in
theorem X₁_K : α '' Icc 0 a ∪ β '' Icc 0 t₀ ⊆ prefixSet α a β b := by
  rintro _ (h | ⟨t, ht, rfl⟩)
  · exact Or.inl h
  · exact Or.inr ⟨t, ⟨zero_le, ht.2.trans hl.t₀_lt.le⟩, rfl⟩

theorem X₂_isCompact : IsCompact (β '' Icc 0 b ∪ α '' Icc 0 s₀) :=
  hs.isCompact₂.union (isCompact_Icc.image_of_continuousOn (hs.hc₁.mono (Icc_subset_Icc_right hl.s₀_lt.le)))

theorem X₂_pc : IsPreconnected (β '' Icc 0 b ∪ α '' Icc 0 s₀) :=
  IsPreconnected.union (β t₀) ⟨t₀, ⟨zero_le, hl.t₀_lt.le⟩, rfl⟩ ⟨s₀, ⟨zero_le, le_rfl⟩, hl.eq⟩ hs.pc₂
    (isPreconnected_Icc.image _ (hs.hc₁.mono (Icc_subset_Icc_right hl.s₀_lt.le)))

omit hs in
theorem X₂_K : β '' Icc 0 b ∪ α '' Icc 0 s₀ ⊆ prefixSet α a β b := by
  rintro _ (h | ⟨s, hs', rfl⟩)
  · exact Or.inr h
  · exact Or.inl ⟨s, ⟨zero_le, hs'.2.trans hl.s₀_lt.le⟩, rfl⟩

omit hl in
theorem Y₂_pc : IsPreconnected (β '' Ioc t₀ b) :=
  isPreconnected_Ioc.image _ (hs.hc₂.mono fun _ ht => ⟨zero_le, ht.2⟩)

omit hl in
theorem Y₁_pc : IsPreconnected (α '' Ioc s₀ a) :=
  isPreconnected_Ioc.image _ (hs.hc₁.mono fun _ hs' => ⟨zero_le, hs'.2⟩)

theorem disjoint_X₁_Y₂ : Disjoint (α '' Icc 0 a ∪ β '' Icc 0 t₀) (β '' Ioc t₀ b) := by
  rw [Set.disjoint_left]
  rintro _ (h | ⟨t', ht', rfl⟩) ⟨t, ht, he⟩
  · exact hl.sufβ t ht.1 ht.2 (by rw [he]; exact h)
  · have := hs.hi₂ ⟨zero_le, ht.2⟩ ⟨zero_le, ht'.2.trans hl.t₀_lt.le⟩ he
    exact absurd (this ▸ ht.1) (not_lt.2 ht'.2)

theorem disjoint_X₂_Y₁ : Disjoint (β '' Icc 0 b ∪ α '' Icc 0 s₀) (α '' Ioc s₀ a) := by
  rw [Set.disjoint_left]
  rintro _ (h | ⟨s', hs', rfl⟩) ⟨s, hs'', he⟩
  · exact hl.sufα s hs''.1 hs''.2 (by rw [he]; exact h)
  · have := hs.hi₁ ⟨zero_le, hs''.2⟩ ⟨zero_le, hs'.2.trans hl.s₀_lt.le⟩ he
    exact absurd (this ▸ hs''.1) (not_lt.2 hs'.2)

/-- **The junction chart point.** There is `J₀ ∈ (0, M₁)` such that `(0, J₀)` is mapped into the second suffix,
`ψ(J₀)` is the last common point and `(J₀, M₁)` is mapped into the first suffix. -/
theorem exists_junction : ∃ J₀ : ℝ, 0 < J₀ ∧ J₀ < chartPt φ (activeDomain α a β b) (α a) ∧ ψ J₀ = α s₀ ∧
    (∀ w : ℝ, 0 < w → w < J₀ → ψ w ∈ β '' Ioc t₀ b) ∧
    (∀ w : ℝ, J₀ < w → w < chartPt φ (activeDomain α a β b) (α a) → ψ w ∈ α '' Ioc s₀ a) := by
  set M₁ := chartPt φ (activeDomain α a β b) (α a) with hM₁
  have hM₁0 : 0 < M₁ := hs.zero_lt_M₁
  have eM : ψ (M₁ : ℂ) = α a := hs.chartPt_tip₁.2.1
  have hcont : Continuous fun w : ℝ => ψ (w : ℂ) :=
    hs.ψc.comp_continuous continuous_ofReal fun w => ofReal_mem_Hbar w
  set Z : Set ℝ := Icc 0 M₁ ∩ {w : ℝ | ψ (w : ℂ) ∈ α '' Icc 0 a} with hZ
  have hZc : IsClosed Z := isClosed_Icc.inter (hs.isCompact₁.isClosed.preimage hcont)
  have hMZ : M₁ ∈ Z := ⟨⟨hM₁0.le, le_rfl⟩, show ψ (M₁ : ℂ) ∈ _ by rw [eM]; exact (tip₁_mem (α := α) (a := a))⟩
  have hbdd : BddBelow Z := ⟨0, fun w hw => hw.1.1⟩
  set J₀ := sInf Z with hJ₀
  have hJZ : J₀ ∈ Z := hZc.csInf_mem ⟨M₁, hMZ⟩ hbdd
  have hJle : ∀ w ∈ Z, J₀ ≤ w := fun w hw => csInf_le hbdd hw
  have hJ0 : 0 < J₀ := by
    refine lt_of_le_of_ne hJZ.1.1 fun h => hs.tip₂_notMem ?_
    have h1 : ψ ((J₀ : ℝ) : ℂ) ∈ α '' Icc 0 a := hJZ.2
    rw [← h, ofReal_zero, hs.ψ0] at h1
    exact h1
  have hJM : J₀ < M₁ := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hs.isCompact₂.isClosed.isOpen_compl _ hs.tip₁_notMem
    obtain ⟨δ, hδ, hδb⟩ := Metric.continuous_iff.1 hcont M₁ ε hε
    set w : ℝ := max (M₁ / 2) (M₁ - δ / 2) with hw
    have hw1 : w < M₁ := max_lt (by linarith) (by linarith)
    have hw0 : 0 < w := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hdist : dist w M₁ < δ := by
      rw [Real.dist_eq, abs_of_neg (by linarith)]
      have := le_max_right (M₁ / 2) (M₁ - δ / 2)
      linarith
    have hψw : ψ (w : ℂ) ∉ β '' Icc 0 b := fun h => by
      have h2 := hδb w hdist
      rw [eM] at h2
      exact hball (mem_ball.2 h2) h
    have hK := hs.mem_K_of_mem_Icc (hs.L₂_le_zero.trans hw0.le) (hw1.le.trans hs.M₁_le_R₁)
    have hwZ : w ∈ Z := ⟨⟨hw0.le, hw1.le⟩, hK.resolve_right hψw⟩
    exact lt_of_le_of_lt (hJle w hwZ) hw1
  -- left of `J₀`: the second suffix
  have hleft : ∀ w : ℝ, 0 < w → w < J₀ → ψ w ∈ β '' Ioc t₀ b := by
    intro w h0 hw
    have hnA : ψ (w : ℂ) ∉ α '' Icc 0 a := fun h => absurd (hJle w ⟨⟨h0.le, (hw.trans hJM).le⟩, h⟩) (not_le.2 hw)
    rcases hs.mem_fork hl h0 (hw.trans hJM) with ⟨s, hs', he⟩ | ⟨t, ht, he⟩
    · exact absurd ⟨s, ⟨zero_le, hs'.2⟩, he⟩ hnA
    · refine ⟨t, ⟨lt_of_le_of_ne ht.1 fun h => hnA ?_, ht.2⟩, he⟩
      rw [← he, ← h, ← hl.eq]
      exact ⟨s₀, ⟨zero_le, hl.s₀_lt.le⟩, rfl⟩
  -- `ψ(J₀)` is the last common point
  have hJw : ψ (J₀ : ℂ) = α s₀ := by
    have hcl : ψ (J₀ : ℂ) ∈ closure (β '' Icc t₀ b) := by
      have h1 : J₀ ∈ closure (Ioo 0 J₀) := by rw [closure_Ioo hJ0.ne]; exact ⟨hJ0.le, le_rfl⟩
      have h2 := (hcont.continuousWithinAt (s := Ioo 0 J₀) (x := J₀)).mem_closure_image h1
      refine closure_mono ?_ h2
      rintro _ ⟨w, hw, rfl⟩
      exact image_mono Ioc_subset_Icc_self (hleft w hw.1 hw.2)
    rw [(isCompact_Icc.image_of_continuousOn (hs.hc₂.mono (Icc_subset_Icc_left zero_le))).isClosed.closure_eq]
      at hcl
    obtain ⟨t, ht, he⟩ := hcl
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← he, ← h, hl.eq]
    · exact absurd (by rw [he]; exact hJZ.2) (hl.sufβ t h ht.2)
  -- after `J₀` the second suffix is not visited again
  have hwX₁ : ψ (J₀ : ℂ) ∈ α '' Icc 0 a ∪ β '' Icc 0 t₀ := Or.inl (by rw [hJw]; exact ⟨s₀, ⟨zero_le, hl.s₀_lt.le⟩, rfl⟩)
  have h0Y₂ : ψ ((0 : ℝ) : ℂ) ∈ β '' Ioc t₀ b := by
    rw [ofReal_zero, hs.ψ0]; exact ⟨b, ⟨hl.t₀_lt, le_rfl⟩, rfl⟩
  have hnoβ : ∀ v : ℝ, J₀ < v → ψ (v : ℂ) ∉ β '' Ioc t₀ b := fun v hv hvβ =>
    hs.false_of_straddle_K (hs.X₁_isCompact hl) (hs.X₁_pc hl) (X₁_K hl) hs.Y₂_pc
      (fun z ⟨t, ht, hz⟩ => Or.inr ⟨t, ⟨zero_le, ht.2⟩, hz⟩) (hs.disjoint_X₁_Y₂ hl) (Or.inl hs.seed₁) hwX₁ h0Y₂ hvβ
      hJ0 hv
  have hcase : ∀ v : ℝ, J₀ < v → v < M₁ → ψ (v : ℂ) ∈ α '' Ioc s₀ a ∨ ψ (v : ℂ) = α s₀ := by
    intro v h1 h2
    rcases hs.mem_fork hl (hJ0.trans h1) h2 with ⟨s, hs', he⟩ | ⟨t, ht, he⟩
    · rcases eq_or_lt_of_le hs'.1 with h | h
      · right; rw [← he, h]
      · left; exact ⟨s, ⟨h, hs'.2⟩, he⟩
    · rcases eq_or_lt_of_le ht.1 with h | h
      · right; rw [← he, ← h, hl.eq]
      · exact absurd ⟨t, ⟨h, ht.2⟩, he⟩ (hnoβ v h1)
  have hMY₁ : ψ (M₁ : ℂ) ∈ α '' Ioc s₀ a := ⟨a, ⟨hl.s₀_lt, le_rfl⟩, eM.symm⟩
  refine ⟨J₀, hJ0, hJM, hJw, hleft, fun w h1 h2 => ?_⟩
  rcases hcase w h1 h2 with h | h
  · exact h
  · exfalso
    obtain ⟨m, hm, hmne⟩ := exists_ne_of_injOn hs.hC.differentiableOn_inv hs.ψc hs.bijD.injOn h1 (α s₀)
    rcases hcase m hm.1 (hm.2.trans h2) with hmα | hmeq
    · have hwX₂ : ψ (w : ℂ) ∈ β '' Icc 0 b ∪ α '' Icc 0 s₀ :=
        Or.inl ⟨t₀, ⟨zero_le, hl.t₀_lt.le⟩, by rw [h, hl.eq]⟩
      exact hs.false_of_straddle_K (hs.X₂_isCompact hl) (hs.X₂_pc hl) (X₂_K hl) hs.Y₁_pc
        (fun z ⟨s, hs', hz⟩ => Or.inl ⟨s, ⟨zero_le, hs'.2⟩, hz⟩) (hs.disjoint_X₂_Y₁ hl) (Or.inl hs.seed₂) hwX₂ hmα
        hMY₁ hm.2 h2
    · exact hmne hmeq

omit hs in
open scoped Classical in
/-- **The junction of the zone data is `J₀`.** -/
theorem junction_eq {J₀ : ℝ} (hJ0 : 0 < J₀) (hJM : J₀ < chartPt φ (activeDomain α a β b) (α a))
    (hleft : ∀ w : ℝ, 0 < w → w < J₀ → ψ w ∈ β '' Ioc t₀ b)
    (hright : ∀ w : ℝ, J₀ < w → w < chartPt φ (activeDomain α a β b) (α a) → ψ w ∈ α '' Ioc s₀ a) :
    RetChart.junction ψ β b (chartPt φ (activeDomain α a β b) (α a)) = J₀ := by
  set M₁ := chartPt φ (activeDomain α a β b) (α a) with hM₁
  have hbdd : BddAbove (range fun q : ℚ =>
      if 0 < (q : ℝ) ∧ (q : ℝ) < M₁ ∧ ψ ((q : ℝ) : ℂ) ∈ β '' Icc 0 b then (q : ℝ) else 0) := by
    refine ⟨M₁, ?_⟩
    rintro _ ⟨q, rfl⟩
    dsimp only
    split_ifs with h
    · exact h.2.1.le
    · exact (hJ0.trans hJM).le
  unfold RetChart.junction
  refine le_antisymm (ciSup_le fun q => ?_) (le_of_forall_lt fun c hc => ?_)
  · split_ifs with h
    · by_contra hlt
      push Not at hlt
      obtain ⟨s, hs', he⟩ := hright q hlt h.2.1
      exact hl.sufα s hs'.1 hs'.2 (by rw [he]; exact h.2.2)
    · exact hJ0.le
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt hc hJ0)
    have hq0 : 0 < (q : ℝ) := lt_of_le_of_lt (le_max_right _ _) hq1
    have hqc : c < (q : ℝ) := lt_of_le_of_lt (le_max_left _ _) hq1
    have hB : ψ ((q : ℝ) : ℂ) ∈ β '' Icc 0 b :=
      image_mono (show Ioc t₀ b ⊆ Icc 0 b from fun _ ht => ⟨zero_le, ht.2⟩) (hleft q hq0 hq2)
    refine lt_of_lt_of_le hqc (le_ciSup_of_le hbdd q ?_)
    split_ifs with h
    · exact le_rfl
    · exact absurd ⟨hq0, hq2.trans hJM, hB⟩ h

omit hl in
/-- **(OF2) for the touching zone data** (Aux. lemma 85 in the retained chart). -/
theorem isTouchZones : IsTouchZones α a β b ψ (zoneDataT φ (activeDomain α a β b) ψ α a β b) := by
  obtain ⟨s₀, t₀, hl⟩ := hs.exists_isLastContact
  obtain ⟨J₀, hJ0, hJM, hJw, hleft, hright⟩ := hs.exists_junction hl
  have hJ : (zoneDataT φ (activeDomain α a β b) ψ α a β b).R₂ = J₀ := junction_eq hl hJ0 hJM hleft hright
  have hJ' : (zoneDataT φ (activeDomain α a β b) ψ α a β b).L₁ = J₀ := hJ
  have hM₁R₁ := hs.M₁_le_R₁
  have hM₁0 := hs.zero_lt_M₁
  refine
    { good :=
        { a₂_le_b₁ := hs.baseL_le_baseR
          a₁_le_b₂ := hs.baseL_le_baseR
          mono₀ := fun x hx x' hx' h => hs.T_lt_T (Or.inl hx) (Or.inl hx') h
          mono₂ := fun x hx x' hx' h => hs.T_lt_T (Or.inr hx) (Or.inr hx') h
          T₀_lt := fun x hx => hs.T_lt_L₂ hx
          L₂_le := hs.L₂_le_zero
          M₂_le := by rw [hJ]; exact hJ0.le
          R₂_le := le_rfl
          L₁_le := by rw [hJ']; exact hJM.le
          M₁_le := hM₁R₁
          lt_T₂ := fun x hx => hs.lt_R₁_T hx }
      M₂_eq := rfl
      junction := rfl
      zero_lt_R₂ := by rw [hJ]; exact hJ0
      R₂_lt_M₁ := by rw [hJ]; exact hJM
      T_spec := fun x hx => (hs.chartPt_zone hx).2.1
      notMem_zone := fun x hx => hs.notMem_K_of_zone hx
      zone₀ := fun w hw => hs.zone₀_of_lt hw
      zone₂ := fun w hw => hs.zone₂_of_gt hw
      side₂ := fun w h1 h2 => ?_
      side₂' := fun w h0 h2 hA => ?_
      side₃ := fun w h1 h2 => ?_
      side₄ := fun w h1 h2 =>
        hs.mem₁_of_gt h1 (hs.mem_K_of_mem_Icc (hs.L₂_le_zero.trans (hM₁0.le.trans h1.le)) h2.le)
      L₂_real := by rw [hs.ψ_L₂]; simp
      L₂_mem := by rw [hs.ψ_L₂]; exact baseL_mem hs.hp₂ hs.hb
      R₁_real := by rw [hs.ψ_R₁]; simp
      R₁_mem := by rw [hs.ψ_R₁]; exact baseR_mem hs.hp₁ hs.ha
      J_mem := by
        rw [hJ, hJw]
        exact ⟨⟨s₀, ⟨zero_le, hl.s₀_lt.le⟩, rfl⟩, ⟨t₀, ⟨zero_le, hl.t₀_lt.le⟩, hl.eq.symm⟩⟩
      tip₂ := hs.ψ0
      tip₁ := hs.chartPt_tip₁.2.1 }
  · rw [hJ] at h2
    rcases lt_trichotomy w 0 with h | h | h
    · exact hs.mem₂_of_lt h (hs.mem_K_of_mem_Icc h1.le (h.le.trans (hM₁0.le.trans hM₁R₁)))
    · rw [h, ofReal_zero, hs.ψ0]; exact (tip₂_mem (β := β) (b := b))
    · exact image_mono (show Ioc t₀ b ⊆ Icc 0 b from fun t ht => ⟨zero_le, ht.2⟩) (hleft w h h2)
  · rw [hJ] at h2
    obtain ⟨t, ht, he⟩ := hleft w h0 h2
    exact hl.sufβ t ht.1 ht.2 (by rw [he]; exact hA)
  · rw [hJ'] at h1
    obtain ⟨s, hs', he⟩ := hright w h1 h2
    exact ⟨⟨s, ⟨zero_le, hs'.2⟩, he⟩, fun hB => hl.sufα s hs'.1 hs'.2 (by rw [he]; exact hB)⟩

end IsTSetting

/-- **Aux. lemma 85 in the retained chart, proved** (`RLC.RetTouchZonesStatement`): at a touching ordinary retained
pair of two good paths with the retained chart, the touching zone data have the outer boundary (OF2). -/
theorem retTouchZonesStatement : RetTouchZonesStatement := by
  intro α β ζ₁ ζ₂ x₁ x₂ a b φ ψ lift hp₁ hp₂ hx hpair htouch hC
  exact (IsTSetting.mk hp₁ hp₂ hx hpair htouch hC).isTouchZones

end Aux85

end RLC

end InteractingSLE
