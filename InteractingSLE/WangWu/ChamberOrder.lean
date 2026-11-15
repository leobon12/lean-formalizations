/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ChamberCross
import InteractingSLE.WangWu.ChamberSides

/-!
# Contact order of ordered curves (specification Aux. lemma 93)

Packet PROVE-WW-B4. Specification Aux. lemma 93 (`source/spec/p289-336.md#aux-93`, p. 314), used in the proof of
Lemma 7.1 ("**Aux.** lemma 93 orders the common contacts of every pair. This is a deterministic Jordan-domain
result", p. 223) and in the chamber geometry of Wang–Wu §4.5 (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`,
ruling R31; the pockets of Aux. lemma 33 need increasing contacts):

> *Let `γ₁, γ₂` be continuous simple proper curves from `0` to `∞` whose noninitial finite points belong to `ℍ`.
> Suppose that `γ₂` is contained in the closed left side of `γ₁` … Their common points occur in the same traversal
> order.*

## Proof (in the disc)

Let the crosscut `β` avoid the lower side of the crosscut `α`, and suppose `α s = β r`, `α s' = β r'` with `s < s'`
but `r' < r`. Then `β` lies in the closure of the upper side `D` of `α`, a Jordan domain with boundary
`α[0, 1] ∪ (upper semicircle)`. The prefix `β[0, r']` joins `−1` to `α s'`, the suffix `β[r, 1]` joins `α s` to `1`,
and on the boundary the pair `{α s, 1}` is separated by `{−1, α s'}` (the two closed pieces `α[0, s']` and
`α[s', 1] ∪ (upper semicircle)` of the boundary meet only at `−1` and `α s'`). The crossing lemma in a Jordan domain
(`jordan_crossing`) makes the two disjoint pieces of `β` meet — a contradiction.

## Main results

* `IsDiscCrosscut.lt_of_contact`: contact order for crosscuts;
* `IsProperArc.lt_of_contact`: **Aux. lemma 93** for simple proper arcs of `ℍ` (with "`γ₂` in the closed left side of
  `γ₁`" read as `γ₂` avoiding the right side of `γ₁`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Complex Bornology
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)

namespace InteractingSLE.WangWu

namespace IsDiscCrosscut

variable {α β : ℝ → ℂ}

/-- A crosscut above `α` lies in the closure of the upper side of `α`. -/
theorem mapsTo_closure_upper (hα : IsDiscCrosscut α) (hβ : IsDiscCrosscut β)
    (hord : Disjoint (crossRange β) (crossSide α (-1))) :
    MapsTo β (Icc 0 1) (jordanIn (crossRange α ∪ semiArc 1) ∪ (crossRange α ∪ semiArc 1)) := by
  intro u hu
  have hbu : β u ∈ crossRange β := ⟨u, hu, rfl⟩
  have hD := hβ.crossRange_subset_closedBall hbu
  rw [mem_closedBall, dist_zero_right] at hD
  by_cases hα' : β u ∈ crossRange α
  · exact Or.inr (Or.inl hα')
  rcases eq_or_lt_of_le hD with hn | hn
  · rcases hβ.eq_of_mem_crossRange_of_norm hbu hn with h | h
    · exact Or.inr (Or.inr ⟨hn, by rw [h]; simp⟩)
    · exact Or.inr (Or.inr ⟨hn, by rw [h]; simp⟩)
  · refine Or.inl (hα.mem_crossSide_one_of (by rw [mem_ball, dist_zero_right]; exact hn) hα' ?_)
    exact fun h => Set.disjoint_left.1 hord hbu h

/-- **Contact order for crosscuts** (Aux. lemma 93 in the disc). If `β` avoids the lower side of `α`, the common
points of `α` and `β` occur in the same order along both. -/
theorem lt_of_contact (hα : IsDiscCrosscut α) (hβ : IsDiscCrosscut β)
    (hord : Disjoint (crossRange β) (crossSide α (-1))) {s s' r r' : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hs' : s' ∈ Icc (0 : ℝ) 1) (hr : r ∈ Icc (0 : ℝ) 1) (hr' : r' ∈ Icc (0 : ℝ) 1) (h₁ : α s = β r)
    (h₂ : α s' = β r') (hss : s < s') : r < r' := by
  have hne : r ≠ r' := by
    rintro rfl
    exact hss.ne (hα.inj hs hs' (h₁.trans h₂.symm))
  by_contra hle
  have hlt : r' < r := lt_of_le_of_ne (not_lt.1 hle) (Ne.symm hne)
  set Γ := crossRange α ∪ semiArc 1 with hΓdef
  have hΓ : LQGMetric.JordanMap.IsJordanCurve Γ := hα.isJordanCurve_upper
  have hmaps := hα.mapsTo_closure_upper hβ hord
  -- the two pieces of `β`
  set P : ℝ → ℂ := fun u => β (u * r') with hP
  set Q : ℝ → ℂ := fun u => β (r + u * (1 - r)) with hQ
  have hPt : MapsTo (fun u : ℝ => u * r') (Icc 0 1) (Icc 0 1) := fun u hu =>
    ⟨mul_nonneg hu.1 hr'.1, by nlinarith [hu.1, hu.2, hr'.1, hr'.2]⟩
  have hQt : MapsTo (fun u : ℝ => r + u * (1 - r)) (Icc 0 1) (Icc 0 1) := fun u hu =>
    ⟨by nlinarith [hu.1, hu.2, hr.1, hr.2], by nlinarith [hu.1, hu.2, hr.1, hr.2]⟩
  have hPc : ContinuousOn P (Icc 0 1) := hβ.cont.comp (by fun_prop) hPt
  have hQc : ContinuousOn Q (Icc 0 1) := hβ.cont.comp (by fun_prop) hQt
  have hs'0 : 0 < s' := lt_of_le_of_lt hs.1 hss
  -- endpoints
  have hP0 : P 0 = -1 := by simp only [hP, zero_mul, hβ.zero]
  have hP1 : P 1 = α s' := by simp only [hP, one_mul, h₂]
  have hQ0 : Q 0 = α s := by simp only [hQ, zero_mul, add_zero, h₁]
  have hQ1 : Q 1 = 1 := by simp only [hQ, one_mul, add_sub_cancel, hβ.one]
  have hm1 : (-1 : ℂ) ∈ Γ := Or.inr ⟨by simp, by simp⟩
  have hp1 : (1 : ℂ) ∈ Γ := Or.inr ⟨by simp, by simp⟩
  have hab : (-1 : ℂ) ≠ α s' := by
    intro h
    rw [← hα.zero] at h
    exact hs'0.ne (hα.inj ⟨le_rfl, zero_le_one⟩ hs' h)
  -- the separation on the boundary
  have hsep : ∀ K ⊆ Γ, IsPreconnected K → α s ∈ K → (1 : ℂ) ∈ K → (-1 : ℂ) ∈ K ∨ α s' ∈ K := by
    intro K hK hKc hcK hdK
    by_contra hnot
    push Not at hnot
    obtain ⟨haK, hbK⟩ := hnot
    set F₁ := α '' Icc 0 s'
    set F₂ := α '' Icc s' 1 ∪ semiArc 1
    have hF₁ : IsClosed F₁ := (isCompact_Icc.image_of_continuousOn
      (hα.cont.mono (Icc_subset_Icc le_rfl hs'.2))).isClosed
    have hF₂ : IsClosed F₂ := by
      refine (isCompact_Icc.image_of_continuousOn
        (hα.cont.mono (Icc_subset_Icc hs'.1 le_rfl))).isClosed.union ?_
      have : semiArc 1 = sphere (0 : ℂ) 1 ∩ {w | 0 ≤ 1 * w.im} := by
        ext w; simp [semiArc]
      rw [this]
      exact isClosed_sphere.inter (isClosed_le continuous_const (by fun_prop))
    have hcover : K ⊆ F₁ ∪ F₂ := by
      intro w hw
      rcases hK hw with ⟨u, hu, rfl⟩ | h
      · rcases le_total u s' with h' | h'
        · exact Or.inl ⟨u, ⟨hu.1, h'⟩, rfl⟩
        · exact Or.inr (Or.inl ⟨u, ⟨h', hu.2⟩, rfl⟩)
      · exact Or.inr (Or.inr h)
    have hdisj : K ∩ (F₁ ∩ F₂) = ∅ := by
      refine eq_empty_iff_forall_notMem.2 fun w ⟨hwK, ⟨u, hu, hwu⟩, hw2⟩ => ?_
      subst hwu
      have hu01 : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1, hu.2.trans hs'.2⟩
      rcases hw2 with ⟨v, hv, hvu⟩ | hS
      · have hv01 : v ∈ Icc (0 : ℝ) 1 := ⟨hs'.1.trans hv.1, hv.2⟩
        have := hα.inj hv01 hu01 hvu
        have hus : u = s' := le_antisymm hu.2 (this ▸ hv.1)
        rw [hus] at hwK
        exact hbK hwK
      · rcases hα.eq_of_mem_crossRange_of_norm ⟨u, hu01, rfl⟩ hS.1 with h | h
        · exact haK (h ▸ hwK)
        · have hu1 : u = 1 := hα.inj hu01 ⟨zero_le_one, le_rfl⟩ (h.trans hα.one.symm)
          have hs1 : s' = 1 := le_antisymm hs'.2 (hu1 ▸ hu.2)
          rw [hu1, hα.one] at hwK
          rw [hs1, hα.one] at hbK
          exact hbK hwK
    rcases (isPreconnected_iff_subset_of_disjoint_closed.1 hKc) F₁ F₂ hF₁ hF₂ hcover hdisj with h | h
    · obtain ⟨u, hu, hu1⟩ := h hdK
      have hu01 : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1, hu.2.trans hs'.2⟩
      have : u = 1 := hα.inj hu01 ⟨zero_le_one, le_rfl⟩ (hu1.trans hα.one.symm)
      have hs1 : s' = 1 := le_antisymm hs'.2 (this ▸ hu.2)
      rw [hs1, hα.one] at hbK
      exact hbK hdK
    · rcases h hcK with ⟨v, hv, hvs⟩ | hS
      · have := hα.inj ⟨hs'.1.trans hv.1, hv.2⟩ hs hvs
        linarith [hv.1]
      · rcases hα.eq_of_mem_crossRange_of_norm ⟨s, hs, rfl⟩ hS.1 with h' | h'
        · exact haK (h' ▸ hcK)
        · have : s = 1 := hα.inj hs ⟨zero_le_one, le_rfl⟩ (h'.trans hα.one.symm)
          linarith [hs'.2]
  obtain ⟨u, hu, v, hv, huv⟩ := jordan_crossing hΓ hm1 (Or.inl ⟨s', hs', rfl⟩) hab
    (Or.inl ⟨s, hs, rfl⟩) hp1 hsep hPc hQc (hmaps.comp hPt) (hmaps.comp hQt) hP0 hP1 hQ0 hQ1
  have h3 : u * r' = r + v * (1 - r) := hβ.inj (hPt hu) (hQt hv) huv
  nlinarith [mul_nonneg hv.1 (sub_nonneg.2 hr.2), mul_le_of_le_one_left hr'.1 hu.2]

end IsDiscCrosscut

/-- **Aux. lemma 93 (contact order).** Let `R` and `L` be simple proper arcs of `ℍ` from `0` to `∞`, with `L` avoiding
the right side of `R`. If `R t₁ = L u₁`, `R t₂ = L u₂` and `t₁ < t₂`, then `u₁ < u₂`. -/
theorem IsProperArc.lt_of_contact {R L : ℝ → ℂ} (hR : IsProperArc R) (hL : IsProperArc L)
    (hord : Disjoint (arcRange L) (rightSideOf (arcRange R))) {t₁ t₂ u₁ u₂ : ℝ} (ht₁ : 0 ≤ t₁)
    (hu₁ : 0 ≤ u₁) (hu₂ : 0 ≤ u₂) (h₁ : R t₁ = L u₁) (h₂ : R t₂ = L u₂) (ht : t₁ < t₂) : u₁ < u₂ := by
  have ht₂ : 0 ≤ t₂ := ht₁.trans ht.le
  have hmono : ∀ {t t' : ℝ}, 0 ≤ t → 0 ≤ t' → t < t' → discTime t < discTime t' := by
    intro t t' h h' hlt
    rw [discTime, discTime, div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hc₁ : toDisc R (discTime t₁) = toDisc L (discTime u₁) := by
    rw [toDisc_discTime R ht₁, toDisc_discTime L hu₁, h₁]
  have hc₂ : toDisc R (discTime t₂) = toDisc L (discTime u₂) := by
    rw [toDisc_discTime R ht₂, toDisc_discTime L hu₂, h₂]
  have hlt := hR.isDiscCrosscut_toDisc.lt_of_contact hL.isDiscCrosscut_toDisc
    ((disjoint_rightSideOf_iff hR hL).1 hord) (Ico_subset_Icc_self (discTime_mem_Ico ht₁))
    (Ico_subset_Icc_self (discTime_mem_Ico ht₂)) (Ico_subset_Icc_self (discTime_mem_Ico hu₁))
    (Ico_subset_Icc_self (discTime_mem_Ico hu₂)) hc₁ hc₂ (hmono ht₁ ht₂ ht)
  by_contra hle
  push Not at hle
  rcases eq_or_lt_of_le hle with h | h
  · rw [h] at hlt; exact lt_irrefl _ hlt
  · exact lt_asymm hlt (hmono hu₂ hu₁ h)

end InteractingSLE.WangWu
