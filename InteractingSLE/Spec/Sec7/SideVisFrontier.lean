/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB10
import InteractingSLE.Spec.Sec5.Prop55HalfSide
import InteractingSLE.WangWu.UnboundedComponent

/-!
# No exhaustion of an open visit set by two certified frontiers

PROVE-SIDE-VISITS. Supplement p. 476–477 (R.6, "For the probability-one
quantifiers"): the set of original times at which the counterflow tip lies in
the pocket but off the certified frontiers is open, and Aux. 42 (Lemma GB10's
pathwise conclusion) with the finite closed-cover argument shows that it is
nonempty in every nonempty open visit set; hence it contains a rational time.

The frontiers are seed-proper curves `β₁, β₂` in the original coordinate; the
trace `η` is read in the inversion chart `m(z) = −1/z`, so the tip is off the
frontiers when `m(η t) ∉ range β₁ ∪ range β₂`. Every positive-time piece
`m ∘ β([p, q])`, `0 < p < q`, is a compact simple arc, and the positive part of
`m(range β)` is a countable union of such arcs.

Deterministic statements; no probability and no source theorem are involved.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.SideVis

open Sec5.Prop55Half (IsSeedProper)
open Theorem14.GB10 (IsSimpleArc NoSimpleArcInterval)

theorem negInv_negInv (z : ℂ) : negInv (negInv z) = z := by
  simp only [negInv, inv_neg, inv_inv, neg_neg]

theorem negInv_injective : Function.Injective negInv := fun z w h => by
  rw [← negInv_negInv z, h, negInv_negInv]

theorem negInv_eq_zero_iff {z : ℂ} : negInv z = 0 ↔ z = 0 := by
  simp only [negInv, neg_eq_zero, inv_eq_zero]

/-- A positive-time compact piece of an inverted seed-proper curve is a simple arc. -/
theorem isSimpleArc_negInv_comp {β : ℝ≥0 → ℂ} (hβ : IsSeedProper β) {p q : ℝ} (hp : 0 < p)
    (hpq : p < q) :
    IsSimpleArc ((fun s : ℝ => negInv (β s.toNNReal)) '' Icc p q) := by
  apply Theorem14.GB10.isSimpleArc_image_Icc hpq
  · intro s hs
    have hs0 : 0 < s := hp.trans_le hs.1
    have hne : β s.toNNReal ≠ 0 := fun h0 => by
      have hH := hβ.2.2.2.1 s.toNNReal (Real.toNNReal_pos.2 hs0)
      rw [h0] at hH
      simp [QuantumZipper.H] at hH
    have hc : ContinuousAt (fun s : ℝ => β s.toNNReal) s :=
      (hβ.1.comp continuous_real_toNNReal).continuousAt
    exact (ContinuousAt.comp (g := fun z : ℂ => -z⁻¹) (f := fun s : ℝ => β s.toNNReal)
      ((continuousAt_inv₀ hne).neg) hc).continuousWithinAt
  · intro s hs s' hs' he
    have h1 : β s.toNNReal = β s'.toNNReal := negInv_injective he
    have h2 := hβ.2.1 h1
    have hs0 : 0 ≤ s := hp.le.trans hs.1
    have hs0' : 0 ≤ s' := hp.le.trans hs'.1
    rw [← Real.coe_toNNReal s hs0, ← Real.coe_toNNReal s' hs0', h2]

/-- A nonzero point whose inversion lies on a seed-proper curve lies on one of
the countably many positive-time arcs `m ∘ β([1/(n+2), n+2])`. -/
theorem exists_mem_negInv_arc {β : ℝ≥0 → ℂ} (hβ : IsSeedProper β) {z : ℂ} (hz : z ≠ 0)
    (hzβ : negInv z ∈ range β) :
    ∃ n : ℕ, z ∈ (fun s : ℝ => negInv (β s.toNNReal)) '' Icc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) := by
  obtain ⟨t, ht⟩ := hzβ
  have ht0 : (0 : ℝ) < t := by
    rcases eq_zero_or_pos t with h | h
    · exfalso
      rw [h, hβ.2.2.1] at ht
      exact hz (negInv_eq_zero_iff.1 ht.symm)
    · exact_mod_cast h
  obtain ⟨n, hn⟩ := exists_nat_ge (max (t : ℝ) (1 / (t : ℝ)))
  have hn2 : (n : ℝ) < (n : ℝ) + 2 := by linarith
  refine ⟨n, (t : ℝ), ⟨?_, ?_⟩, ?_⟩
  · have h1 : 1 / (t : ℝ) < (n : ℝ) + 2 := (le_max_right _ _).trans_lt (hn.trans_lt hn2)
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ ht0] at h1
    linarith
  · exact ((le_max_left _ _).trans hn).trans hn2.le
  · show negInv (β (t : ℝ).toNNReal) = z
    rw [Real.toNNReal_coe, ht, negInv_negInv]

/-- **No positive trace interval lies on two inverted seed-proper frontiers**
(Aux. 42 with the closed-cover step): if the trace is nonzero on `[a, b]`, some
time of `[a, b]` has its tip off both frontiers. -/
theorem exists_mem_Icc_offFrontier {η : ℝ → ℂ} (hηc : ContinuousOn η (Ici 0))
    (h42 : NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤) {β₁ β₂ : ℝ≥0 → ℂ}
    (hβ₁ : IsSeedProper β₁) (hβ₂ : IsSeedProper β₂) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (h0 : ∀ t ∈ Icc a b, η t ≠ 0) :
    ∃ t ∈ Icc a b, negInv (η t) ∉ range β₁ ∪ range β₂ := by
  by_contra hcon
  push Not at hcon
  set A : ℕ → Set ℂ := fun m => (fun s : ℝ => negInv ((if Even m then β₁ else β₂) s.toNNReal)) ''
    Icc (1 / (((m / 2 : ℕ) : ℝ) + 2)) (((m / 2 : ℕ) : ℝ) + 2) with hA
  have hlt : ∀ n : ℕ, 1 / ((n : ℝ) + 2) < (n : ℝ) + 2 := by
    intro n
    have h2 : (1 : ℝ) < (n : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    exact (div_lt_one (by positivity)).2 h2 |>.trans h2
  have hAs : ∀ m, IsSimpleArc (A m) := fun m => by
    simp only [hA]
    split_ifs
    · exact isSimpleArc_negInv_comp hβ₁ (by positivity) (hlt _)
    · exact isSimpleArc_negInv_comp hβ₂ (by positivity) (hlt _)
  have hab' : a.toNNReal < b.toNNReal := (Real.toNNReal_lt_toNNReal_iff (ha.trans_lt hab)).2 hab
  refine h42.not_image_subset_iUnion hab' ENNReal.coe_lt_top
    (hηc.comp continuous_subtype_val.continuousOn fun s _ => s.2) (A := A) hAs ?_
  rintro _ ⟨s, hs, rfl⟩
  have hs' : (s : ℝ) ∈ Icc a b := by
    constructor
    · have := NNReal.coe_le_coe.2 hs.1
      rwa [Real.coe_toNNReal _ ha] at this
    · have := NNReal.coe_le_coe.2 hs.2
      rwa [Real.coe_toNNReal _ (ha.trans hab.le)] at this
  rcases hcon (s : ℝ) hs' with h | h
  · obtain ⟨n, hn⟩ := exists_mem_negInv_arc hβ₁ (h0 _ hs') h
    refine mem_iUnion.2 ⟨2 * n, ?_⟩
    have h2 : 2 * n / 2 = n := by omega
    simp only [hA, even_two_mul, ↓reduceIte, h2]
    exact hn
  · obtain ⟨n, hn⟩ := exists_mem_negInv_arc hβ₂ (h0 _ hs') h
    refine mem_iUnion.2 ⟨2 * n + 1, ?_⟩
    have h2 : (2 * n + 1) / 2 = n := by omega
    have hodd : ¬ Even (2 * n + 1) := Nat.not_even_iff_odd.2 (odd_two_mul_add_one _)
    simp only [hA, hodd, ↓reduceIte, h2]
    exact hn

/-- **A rational visit off the certified frontiers** (R.6, supplement p. 476–477):
in a nonempty open set `V` of positive times on which the trace is nonzero, some
rational time has its tip off both inverted frontiers. The set of such times in
`V` is open because the frontiers are closed. -/
theorem exists_rat_mem_offFrontier {η : ℝ → ℂ} (hηc : ContinuousOn η (Ici 0))
    (h42 : NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤) {β₁ β₂ : ℝ≥0 → ℂ}
    (hβ₁ : IsSeedProper β₁) (hβ₂ : IsSeedProper β₂) {V : Set ℝ} (hV : IsOpen V)
    (hVpos : V ⊆ Ioi 0) (h0 : ∀ t ∈ V, η t ≠ 0) (hne : V.Nonempty) :
    ∃ r : ℚ, (r : ℝ) ∈ V ∧ negInv (η r) ∉ range β₁ ∪ range β₂ := by
  obtain ⟨t, ht⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV t ht
  have hsub : Icc t (t + ε / 2) ⊆ V := fun s hs => hball (by
    rw [mem_ball, Real.dist_eq, abs_of_nonneg (by linarith [hs.1])]
    linarith [hs.2])
  have ht0 : 0 ≤ t := (hVpos ht).le
  obtain ⟨s, hs, hsoff⟩ := exists_mem_Icc_offFrontier hηc h42 hβ₁ hβ₂ ht0
    (by linarith) fun u hu => h0 u (hsub hu)
  have hcl : IsClosed (range β₁ ∪ range β₂) := hβ₁.isClosed_range.union hβ₂.isClosed_range
  have hcont : ContinuousOn (fun u => negInv (η u)) V := by
    intro u hu
    have hcu : ContinuousWithinAt η V u :=
      (hηc u (mem_Ici.2 (le_of_lt (hVpos hu)))).mono fun v hv => mem_Ici.2 (le_of_lt (hVpos hv))
    exact ((continuousAt_inv₀ (h0 u hu)).neg).comp_continuousWithinAt hcu
  have hU : IsOpen (V ∩ (fun u => negInv (η u)) ⁻¹' (range β₁ ∪ range β₂)ᶜ) :=
    hcont.isOpen_inter_preimage hV hcl.isOpen_compl
  obtain ⟨r, hr⟩ := Rat.denseRange_cast.exists_mem_open hU ⟨s, hsub hs, hsoff⟩
  exact ⟨r, hr.1, hr.2⟩

end InteractingSLE.Sec7.SideVis
