/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLemmaS
import InteractingSLE.Foundations.Topology.JaniszewskiHalfPlane

/-!
# Lemma S5's inside clause, repaired, from Lemma S2's hull restriction

Packet PROVE-T14-SB3. `SB.S5InsideStatement` is false as stated (`SBLemmaSProof.not_s5InsideStatement`): it allows a
second prefix which runs through `L = min(A ∩ ℝ)` and then along `∂K_A`. The source's proof (supplement p. 583: "If the
actual second prefix stops before the exit at `L`, retain the original witness only through that exit and replace its
remaining tail by the negative-real ray from `L` to infinity") covers prefixes which do **not visit `L` before their
end**; this is also how SB3 uses the clause ("If that upper prefix is wholly in `K_A`, including a terminal prefix that
never reaches `L`"; SB2(1) gives `η([0, T ∧ T_L]) ⊆ K_A` with `T_L` the first visit to `L`).

* `S5InsideNoVisitStatement` — the inside clause with the added hypothesis `∀ s < a₂, β s ≠ L`;
* `s5InsideNoVisitStatement_of_s2Hull` — **its proof from `S2HullStatement`**: S2 applied to the S1 witness `β'`
  gives the visit `t_L ≥ a₂`, `β'([0, t_L]) ⊆ K_A` and `β'((t_L, ∞)) ⊆ closure D_A`. The new witness `β''` is `β'` on
  `[0, t_L]` followed by the ray `(−∞, L]`. Then `D_A` misses the closed curve of `β''` and contains far points of its
  right side, so `closure D_A` is on the closed right of `β''`; and the left side of `β''` misses the closed curve of
  `β'` (its tail is in `closure D_A`), so it lies in the left side of `β'`, which keeps `A` on the closed right of
  `β''`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex Bornology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE

namespace Theorem14

namespace SB

open Supp9B

/-- **Lemma S5's inside clause, repaired** (supplement p. 582–583): as `S5InsideStatement`, for a second prefix which
does not visit `L = min(A ∩ ℝ)` before its end ("If the actual second prefix stops before the exit at `L`"). -/
def S5InsideNoVisitStatement : Prop :=
  ∀ (p : ℝ → ℂ) (β : ℝ≥0 → ℂ) (a₂ : ℝ≥0), ContinuousOn p (Icc 0 1) → p 0 = 0 →
    (∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) → β 0 = 0 → IsOneSided (p '' Icc 0 1) β a₂ →
    β '' Icc 0 a₂ ⊆ hullK (p '' Icc 0 1) → (∀ s : ℝ≥0, s < a₂ → β s ≠ realMin (p '' Icc 0 1)) →
    ∀ A' : Set ℂ, A' ⊆ closure (H \ fillH (p '' Icc 0 1)) → IsOneSided (p '' Icc 0 1 ∪ A') β a₂

/-- A curve followed, after the time `tL`, by the leftward real ray from `L`. -/
def rayTail (β' : ℝ≥0 → ℂ) (tL : ℝ≥0) (L : ℝ) (t : ℝ≥0) : ℂ :=
  if t ≤ tL then β' t else ((L - ((t : ℝ) - tL) : ℝ) : ℂ)

theorem rayTail_of_le {β' : ℝ≥0 → ℂ} {tL : ℝ≥0} {L : ℝ} {t : ℝ≥0} (ht : t ≤ tL) :
    rayTail β' tL L t = β' t := by simp only [rayTail, ht, ↓reduceIte]

theorem rayTail_of_lt {β' : ℝ≥0 → ℂ} {tL : ℝ≥0} {L : ℝ} {t : ℝ≥0} (ht : tL < t) :
    rayTail β' tL L t = ((L - ((t : ℝ) - tL) : ℝ) : ℂ) := by
  simp only [rayTail, not_le.2 ht, ↓reduceIte]

/-- The ray completion is a proper curve when the first part has no real point to the left of `L`. -/
theorem isProperCurve_rayTail {β' : ℝ≥0 → ℂ} {tL : ℝ≥0} {L : ℝ} (hβ' : IsProperCurve β')
    (hL : β' tL = L) (hleft : ∀ t ≤ tL, ∀ x : ℝ, β' t = x → L ≤ x) : IsProperCurve (rayTail β' tL L) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Continuous.if_le hβ'.1 (by fun_prop : Continuous fun t : ℝ≥0 =>
      ((L - ((t : ℝ) - tL) : ℝ) : ℂ)) continuous_id continuous_const ?_
    intro t ht
    rw [ht, hL]; simp
  · intro s t hst
    rcases le_or_gt s tL with hs | hs <;> rcases le_or_gt t tL with ht | ht
    · rw [rayTail_of_le hs, rayTail_of_le ht] at hst; exact hβ'.2.1 hst
    · rw [rayTail_of_le hs, rayTail_of_lt ht] at hst
      have := hleft s hs _ hst
      have ht' : (tL : ℝ) < t := ht
      linarith
    · rw [rayTail_of_lt hs, rayTail_of_le ht] at hst
      have := hleft t ht _ hst.symm
      have hs' : (tL : ℝ) < s := hs
      linarith
    · rw [rayTail_of_lt hs, rayTail_of_lt ht] at hst
      have := Complex.ofReal_injective hst
      exact NNReal.coe_injective (by linarith)
  · intro t
    rcases le_or_gt t tL with ht | ht
    · rw [rayTail_of_le ht]; exact hβ'.2.2.1 t
    · rw [rayTail_of_lt ht]; simp
  · have hlin : Tendsto (fun t : ℝ≥0 => (t : ℝ) + (-(tL : ℝ) - |L|)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (NNReal.tendsto_coe_atTop.2 tendsto_id)
    refine tendsto_atTop_mono' _ ?_ hlin
    filter_upwards [eventually_gt_atTop tL] with t ht
    rw [rayTail_of_lt ht, Complex.norm_real, Real.norm_eq_abs]
    have h1 := neg_le_abs (L - ((t : ℝ) - tL))
    linarith [le_abs_self L]

/-- **Lemma S5's inside clause, repaired, from Lemma S2's hull restriction.** -/
theorem s5InsideNoVisitStatement_of_s2Hull (hS2 : S2HullStatement) : S5InsideNoVisitStatement := by
  intro p β a₂ hpc hp0 hpim hβ0 hS1 _ hvisit A' hA'
  obtain ⟨β', hβ', hA⟩ := hS1
  set A := p '' Icc 0 1 with hAdef
  set L := realMin A with hLdef
  have P' := isProperCurve_of_isProperCompletion hβ'
  have hβ'0 : β' 0 = 0 := (hβ'.2.2.2.2 0 zero_le).trans hβ0
  obtain ⟨-, tL, htL, -, hhull, htail, -⟩ := hS2 p β' hpc hp0 hpim P' hβ'0 hA
  -- the prefix ends before the visit to `L`
  have ha₂ : a₂ ≤ tL := by
    by_contra h
    exact hvisit tL (not_le.1 h) ((hβ'.2.2.2.2 tL (not_le.1 h).le).symm.trans htL)
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn hpc
  -- real points of the hull are to the right of `L`
  have hleft : ∀ t ≤ tL, ∀ x : ℝ, β' t = x → L ≤ x := by
    intro t ht x hx
    rcases hhull ⟨t, ⟨zero_le, ht⟩, rfl⟩ with hF | ⟨y, hy, hyx⟩
    · have : (0 : ℝ) < (β' t).im := hF.1
      rw [hx, Complex.ofReal_im] at this
      exact absurd this (lt_irrefl 0)
    · rw [hx] at hyx
      rw [← Complex.ofReal_injective hyx]; exact hy.1
  set β'' := rayTail β' tL L with hβ''def
  have P'' : IsProperCurve β'' := isProperCurve_rayTail P' htL hleft
  have h0'' : β'' 0 = 0 := by rw [hβ''def, rayTail_of_le zero_le, hβ'0]
  have him0'' : (β'' 0).im = 0 := by rw [h0'']; rfl
  have hcompl : IsProperCompletion β a₂ β'' :=
    ⟨P''.1, P''.2.1, P''.2.2.1, P''.2.2.2, fun t ht => by
      rw [hβ''def, rayTail_of_le (ht.trans ha₂)]; exact hβ'.2.2.2.2 t ht⟩
  have hJ'' := isClosed_seedRayClosure P''
  -- `D_A` misses the closed curve of `β''`
  have hDJ : H \ fillH A ⊆ (seedRayClosure β'')ᶜ := by
    rintro w ⟨hwH, hwF⟩ (⟨t, rfl⟩ | ⟨-, him⟩)
    · rcases le_or_gt t tL with ht | ht
      · rw [hβ''def, rayTail_of_le ht] at hwH hwF
        rcases hhull ⟨t, ⟨zero_le, ht⟩, rfl⟩ with h' | ⟨y, -, hy⟩
        · exact hwF h'
        · have : (0 : ℝ) < (β' t).im := hwH
          rw [← hy, Complex.ofReal_im] at this
          exact lt_irrefl _ this
      · rw [hβ''def, rayTail_of_lt ht] at hwH
        have : (0 : ℝ) < (((L - ((t : ℝ) - tL) : ℝ) : ℂ)).im := hwH
        rw [Complex.ofReal_im] at this
        exact lt_irrefl _ this
    · rw [him0''] at him
      exact absurd hwH (not_lt.2 him)
  -- far points of `D_A` are on the right of `β''`
  obtain ⟨R₁, hR₁⟩ := (hAc.isBounded).subset_ball 0
  have hKc : IsCompact (β' '' Icc 0 tL) := isCompact_Icc.image P'.1
  obtain ⟨R₂, hR₂⟩ := (hKc.isBounded).subset_ball 0
  set M : ℝ := max (max R₁ R₂) 1 + 1 with hM
  have hM1 : R₁ + 1 ≤ M := by rw [hM]; linarith [le_max_left R₁ R₂, le_max_left (max R₁ R₂) 1]
  have hM2 : R₂ + 1 ≤ M := by rw [hM]; linarith [le_max_right R₁ R₂, le_max_left (max R₁ R₂) 1]
  have hM3 : 2 ≤ M := by rw [hM]; linarith [le_max_right (max R₁ R₂) 1]
  set Q : Set ℂ := {w | M - 1 / 2 < w.re} with hQ
  have hQJ : Q ⊆ (seedRayClosure β'')ᶜ := by
    rintro w hw (⟨t, rfl⟩ | ⟨hre, -⟩)
    · rcases le_or_gt t tL with ht | ht
      · have hw' : M - 1 / 2 < (β' t).re := by simpa [hQ, hβ''def, rayTail_of_le ht] using hw
        have hb := hR₂ ⟨t, ⟨zero_le, ht⟩, rfl⟩
        rw [mem_ball, dist_zero_right] at hb
        linarith [Complex.re_le_norm (β' t)]
      · have hw : M - 1 / 2 < L - ((t : ℝ) - tL) := by simpa [hQ, hβ''def, rayTail_of_lt ht] using hw
        have h1 : L ≤ 0 := by
          have := hleft tL le_rfl L htL
          have hm0 : (0 : ℝ) ∈ {x : ℝ | (x : ℂ) ∈ A} := ⟨0, ⟨le_rfl, zero_le_one⟩, by rw [hp0]; simp⟩
          have hbdd : BddBelow {x : ℝ | (x : ℂ) ∈ A} := by
            refine ⟨-R₁, fun x hx => ?_⟩
            have hb := hR₁ hx
            rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] at hb
            linarith [neg_abs_le x]
          exact csInf_le hbdd hm0
        have h2 : (tL : ℝ) < t := ht
        linarith
    · rw [h0'', Complex.zero_re] at hre
      have hw' : M - 1 / 2 < w.re := hw
      rw [hre] at hw'
      linarith
  have hQR : Q ⊆ rightSide β'' := by
    have hpt : (M : ℂ) - I ∈ Q ∩ lowerRight (β'' 0).re := by
      refine ⟨?_, ?_, ?_⟩
      · simp [hQ]
      · rw [h0'']; simp; linarith
      · simp
    have hpR := lowerRight_subset_rightSide P''.2.2.1 him0'' hpt.2
    have := (convex_halfSpace_re_gt (M - 1 / 2)).isPreconnected.subset_connectedComponentIn hpt.1 hQJ
    rwa [← connectedComponentIn_eq hpR] at this
  have hDR : H \ fillH A ⊆ rightSide β'' := by
    have hz : (M : ℂ) + I ∈ H \ fillH A := by
      refine HalfPlaneSep.mem_H_diff_fillH_of_le_norm hAc.isClosed (R := M) (by linarith) ?_
        (show (0 : ℝ) < ((M : ℂ) + I).im by simp) ?_
      · exact hR₁.trans (ball_subset_ball (by linarith))
      · have := Complex.re_le_norm ((M : ℂ) + I)
        simp only [Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero] at this
        exact this
    have hzR : (M : ℂ) + I ∈ rightSide β'' := hQR (by simp [hQ])
    have := (HalfPlaneSep.isPreconnected_H_diff_fillH hAc.isClosed hAc.isBounded).subset_connectedComponentIn
      hz hDJ
    rwa [← connectedComponentIn_eq hzR] at this
  have hclR : closure (H \ fillH A) ⊆ closedRightSide β'' := by
    intro x hx
    by_cases hxJ : x ∈ seedRayClosure β''
    · exact Or.inr hxJ
    refine Or.inl ?_
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hJ''.isOpen_compl _ hxJ
    obtain ⟨y, hyD, hyx⟩ := Metric.mem_closure_iff.1 hx ε hε
    have hyB : y ∈ ball x ε := by rw [mem_ball, dist_comm]; exact hyx
    have := (convex_ball x ε).isPreconnected.subset_connectedComponentIn hyB hball
    rw [← connectedComponentIn_eq (hDR hyD)] at this
    exact this (mem_ball_self hε)
  -- the left side of `β''` lies in the left side of `β'`
  have hdisj'' := disjoint_leftSide_rightSide P'' him0''
  have hLJ' : leftSide β'' ⊆ (seedRayClosure β')ᶜ := by
    intro w hwL hwJ
    have hwJ'' : w ∉ seedRayClosure β'' := connectedComponentIn_subset _ _ hwL
    rcases hwJ with ⟨t, rfl⟩ | ⟨hre, him⟩
    · rcases le_or_gt t tL with ht | ht
      · exact hwJ'' (Or.inl ⟨t, by rw [hβ''def, rayTail_of_le ht]⟩)
      · rcases hclR (htail ⟨t, ht, rfl⟩) with h' | h'
        · exact Set.disjoint_left.1 hdisj'' hwL h'
        · exact hwJ'' h'
    · exact hwJ'' (Or.inr ⟨by rw [h0'', ← hβ'0]; exact hre, by rw [h0'', ← hβ'0]; exact him⟩)
  have hLL : leftSide β'' ⊆ leftSide β' := by
    have href : β'' 0 - 1 - I ∈ leftSide β' := by
      rw [h0'', ← hβ'0]; exact leftRef_mem_leftSide P'.2.2.1 (by rw [hβ'0]; rfl)
    have := (isPreconnected_connectedComponentIn (F := (seedRayClosure β'')ᶜ)
      (x := β'' 0 - 1 - I)).subset_connectedComponentIn (leftRef_mem_leftSide P''.2.2.1 him0'') hLJ'
    rwa [← connectedComponentIn_eq href] at this
  -- the closed right side of `β''` is the complement of its left side
  have hcR : ∀ z, z ∉ leftSide β'' → z ∈ closedRightSide β'' := by
    intro z hz
    by_cases hzJ : z ∈ seedRayClosure β''
    · exact Or.inr hzJ
    · rcases (compl_seedRayClosure_eq P'' him0'').subset hzJ with h' | h'
      · exact absurd h' hz
      · exact Or.inl h'
  refine ⟨β'', hcompl, union_subset ?_ (hA'.trans hclR)⟩
  intro z hzA
  refine hcR z fun hzL => ?_
  rcases hA hzA with hR' | hS'
  · exact Set.disjoint_left.1 (disjoint_leftSide_rightSide P' (by rw [hβ'0]; rfl)) (hLL hzL) hR'
  · exact hLJ' hzL hS'

end SB

end Theorem14

end InteractingSLE
