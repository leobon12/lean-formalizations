/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCKLift
import InteractingSLE.Spec.Supplement.RLCFAvgSide
import InteractingSLE.Spec.Supplement.G7Restart

/-!
# Lemma G9 at a retained pair of a complete ordered reference: the proof

Packet PROVE-RLC-K, item (f). Proof of `RLC.G9LiftStatement` (`RLCKLift.lean`), following the proof of Lemma G9
(supplement pp. 501–502):

* `le_sigma_of_adm`: an admissible chart prefix (points in `ℍ` or real beyond `v`) ends before the first new contact
  of the continuation with the retained union (that contact is over the retained union, hence neither in `ℍ` nor
  beyond `v`);
* `exists_tail_completion`: if the continuation never returns to the retained union, G7's chart path of the whole
  continuation (`contPath`, through `IsRetCont`) glued to the chart prefix is a proper completion; its points lie over
  the continuation and every point of `ℍ̄` over the continuation is on it;
* **`g9LiftStatement`**: at the fresh common point the contact order of the complete ordered pair
  (`Supp9B.contact_order`) and injectivity keep both complete tails off the retained union; their completions are
  ordered because a point of the chart right side of the first completion is sent by `ψ` into the physical right side
  of the first curve (RLC-C's `image_side_subset`, with the untouched real points beyond the first tip as the real
  boundary data and one rational untouched point as the reference point), which the second curve avoids; the seeds are
  not revisited since their inverse images are the tips, in the retained union.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace RLC

open Supp7 Restart Supp9B

/-! ### An admissible chart prefix ends before the first new contact -/

/-- **An admissible chart prefix stays within the clock's range.** If the chart path, read through `ψ`, is the
continuation of `η` up to its first new contact with the closed set `A` (`σ > 0`), and its points at times in
`(0, s]` are in `ℍ` (sent by `ψ` into a domain `D` off `A`) or real beyond `v` (sent off `A`), then `s ≤ σ`. -/
theorem le_sigma_of_adm {η : ℝ≥0 → ℂ} {a : ℝ≥0} {A D : Set ℂ} {ψ : ℂ → ℂ} {Γ : ℝ≥0 → ℂ} {v : ℝ}
    (hA : IsClosed A) (hηc : Continuous η) (hDA : ∀ z ∈ D, z ∉ A) (hψD : MapsTo ψ H D)
    (hgeo : ∀ y : ℝ, v < y → ψ y ∉ A) {cl : ℝ≥0 → ℝ≥0} {σ : ℝ≥0∞} (hσ0 : 0 < σ)
    (hmono : StrictMonoOn cl {t | (t : ℝ≥0∞) ≤ σ})
    (himg : cl '' {t | (t : ℝ≥0∞) ≤ σ} = {t | a ≤ t ∧ (t : ℝ≥0∞) ≤ ⊤ ∧ ∀ t' : ℝ≥0, a < t' → t' < t → η t' ∉ A})
    (hpth : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ σ → η (cl t) = ψ (Γ t)) {s : ℝ≥0}
    (hadm : ∀ t : ℝ≥0, 0 < t → t ≤ s → Γ t ∈ H ∨ ((Γ t).im = 0 ∧ (Γ t).re ∈ Ioi v)) : (s : ℝ≥0∞) ≤ σ := by
  by_contra hlt
  push Not at hlt
  have hσtop : σ ≠ ⊤ := ne_top_of_lt hlt
  set σ' : ℝ≥0 := σ.toNNReal with hσ'
  have hσe : (σ' : ℝ≥0∞) = σ := ENNReal.coe_toNNReal hσtop
  have hσ'0 : 0 < σ' := by
    rw [← ENNReal.coe_lt_coe, hσe]; simpa using hσ0
  have hσ's : σ' < s := by rw [← ENNReal.coe_lt_coe, hσe]; exact hlt
  have hmem : (σ' : ℝ≥0∞) ≤ σ := hσe.le
  have hcσ : cl σ' ∈ cl '' {t | (t : ℝ≥0∞) ≤ σ} := ⟨σ', hmem, rfl⟩
  rw [himg] at hcσ
  -- the end of the clock is a contact
  have hcA : η (cl σ') ∈ A := by
    by_contra hn
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (hA.isOpen_compl.preimage hηc) (cl σ') hn
    set T : ℝ≥0 := cl σ' + ⟨δ / 2, by positivity⟩ with hT
    have hlt' : cl σ' < T := lt_add_of_pos_right _ (by
      show (0 : ℝ≥0) < ⟨δ / 2, by positivity⟩
      exact_mod_cast half_pos hδ)
    have hTmem : T ∈ {t | a ≤ t ∧ (t : ℝ≥0∞) ≤ ⊤ ∧ ∀ t' : ℝ≥0, a < t' → t' < t → η t' ∉ A} := by
      refine ⟨hcσ.1.trans hlt'.le, le_top, fun t' ht'a ht'T => ?_⟩
      rcases lt_or_ge t' (cl σ') with h | h
      · exact hcσ.2.2 t' ht'a h
      · refine hball ?_
        rw [mem_ball, NNReal.dist_eq, abs_lt]
        have e : ((T : ℝ≥0) : ℝ) = (cl σ' : ℝ) + δ / 2 := rfl
        have h1 : ((t' : ℝ≥0) : ℝ) < T := ht'T
        have h2 : ((cl σ' : ℝ≥0) : ℝ) ≤ t' := h
        rw [e] at h1
        constructor <;> linarith
    rw [← himg] at hTmem
    obtain ⟨x, hx, hxT⟩ := hTmem
    have := hmono.monotoneOn hx hmem (show x ≤ σ' from by
      by_contra hxσ
      push Not at hxσ
      have : (σ' : ℝ≥0∞) < x := ENNReal.coe_lt_coe.2 hxσ
      exact absurd hx (not_le.2 (hσe ▸ this)))
    rw [hxT] at this
    exact absurd this (not_le.2 hlt')
  rw [hpth σ' hmem] at hcA
  rcases hadm σ' hσ'0 hσ's.le with hH | ⟨h0, hv⟩
  · exact hDA _ (hψD hH) hcA
  · have e : Γ σ' = ((Γ σ').re : ℂ) := Complex.ext (by simp) (by simp [h0])
    rw [e] at hcA
    exact hgeo _ hv hcA

/-! ### The completion of a chart prefix by the whole continuation -/

/-- **The tail completion of a chart prefix** (G9's lift: "the relative lift is continuous […] The complete lifts are
therefore continuous and proper. They are injective"). If the continuation of `η` after `a` never returns to the
retained union `A`, the chart path `Λ` of the whole continuation (G7's `contPath`, read in the chart translated by the
real `c`) exists for all times; the chart prefix `Γ|[0, s]` (read through `ψ` by a clock `cl` with `s ≤ σ`) followed
by `Λ` is a proper completion of `Γ|[0, s]`. Every point of it lies over the continuation, at a positive continuation
time after time `0`, and every point of `ℍ̄` over the continuation is on it. -/
theorem exists_tail_completion {η : ℝ≥0 → ℂ} {x : ℝ} {a : ℝ≥0} {O A : Set ℂ} {φ ψ : ℂ → ℂ} {c : ℝ}
    (hR : IsRetCont η ⊤ x a O (fun z => φ z - c) (fun w => ψ (w + c))) (hOA : O ∪ η '' Icc 0 a = A)
    (hno : ∀ t : ℝ≥0, a < t → η t ∉ A) (hprop : Tendsto (fun t => ‖η t‖) atTop atTop)
    {Γ : ℝ≥0 → ℂ} {s : ℝ≥0} {cl : ℝ≥0 → ℝ≥0} {σ : ℝ≥0∞} (hsσ : (s : ℝ≥0∞) ≤ σ)
    (hmono : StrictMonoOn cl {t | (t : ℝ≥0∞) ≤ σ})
    (himg : cl '' {t | (t : ℝ≥0∞) ≤ σ} = {t | a ≤ t ∧ (t : ℝ≥0∞) ≤ ⊤ ∧ ∀ t' : ℝ≥0, a < t' → t' < t → η t' ∉ A})
    (hpth : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ σ → η (cl t) = ψ (Γ t)) (hH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ σ → Γ t ∈ Hbar)
    (hΓc : ContinuousOn Γ (Iic s)) :
    ∃ γ : ℝ≥0 → ℂ, IsProperCompletion Γ s γ ∧ (∀ t, γ t ∈ Hbar) ∧
      (∀ t, ∃ ρ : ℝ≥0, ψ (γ t) = η (a + ρ) ∧ (0 < t → 0 < ρ)) ∧
      ∀ z ∈ Hbar, ∀ ρ : ℝ≥0, ψ z = η (a + ρ) → z ∈ range γ := by
  set K := O ∪ η '' Icc 0 a with hK
  have hstop : contStop η ⊤ a K = ⊤ := by
    refine ENNReal.eq_top_of_forall_nnreal_le fun t => ?_
    have hmem : a + t ∈ contSet η ⊤ a K :=
      ⟨le_self_add, le_top, fun t' h1 _ => by rw [hOA]; exact hno t' h1⟩
    exact (ENNReal.coe_le_coe.2 le_add_self).trans (le_contStop hmem)
  have hlife : contLife η ⊤ a K = ⊤ := by
    rw [contLife, hstop]; exact ENNReal.top_sub_coe
  set Λ' := contPath (H \ fillH K) (fun z => φ z - c) η a (contLife η ⊤ a K) with hΛ'
  have hspec : ∀ r : ℝ≥0, Λ' r ∈ Hbar ∧ ψ (Λ' r + c) = η (a + r) ∧
      ∀ w' ∈ Hbar, ψ (w' + c) = η (a + r) → w' = Λ' r := by
    intro r
    have hr : (r : ℝ≥0∞) < contLife η ⊤ a K := by rw [hlife]; exact ENNReal.coe_lt_top
    obtain ⟨h1, -, h3, h4⟩ := hR.contPath_spec_lt hr
    exact ⟨h1, h3, h4⟩
  have hΛc : Continuous Λ' := hR.continuous_contPath
  obtain ⟨M, hM⟩ := hR.chart.bdd
  have hcl0 : cl 0 = a := clock_zero le_top hmono himg
  have hcla : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ σ → a ≤ cl t := fun t ht => by
    have : cl t ∈ cl '' {t | (t : ℝ≥0∞) ≤ σ} := ⟨t, ht, rfl⟩
    rw [himg] at this; exact this.1
  have hsub : ∀ z : ℂ, z ∈ Hbar → z - c ∈ Hbar := fun z hz => by
    show (0 : ℝ) ≤ (z - c).im; simpa using (show (0 : ℝ) ≤ z.im from hz)
  have hΓΛ : ∀ t ≤ s, Γ t = Λ' (cl t - a) + c := by
    intro t ht
    have htσ : (t : ℝ≥0∞) ≤ σ := (ENNReal.coe_le_coe.2 ht).trans hsσ
    have e : a + (cl t - a) = cl t := add_tsub_cancel_of_le (hcla t htσ)
    have := (hspec (cl t - a)).2.2 (Γ t - c) (hsub _ (hH t htσ)) (by rw [sub_add_cancel, e, hpth t htσ])
    rw [← this]; ring
  set τ : ℝ≥0 → ℝ≥0 := fun t => if t ≤ s then cl t - a else cl s - a + (t - s) with hτ
  have hsσ' : ∀ t ≤ s, (t : ℝ≥0∞) ≤ σ := fun t ht => (ENNReal.coe_le_coe.2 ht).trans hsσ
  have hτmono : StrictMono τ := by
    intro t t' htt'
    simp only [hτ]
    by_cases h' : t' ≤ s
    · have h : t ≤ s := htt'.le.trans h'
      simp only [h, h', ↓reduceIte]
      have := hmono (hsσ' t h) (hsσ' t' h') htt'
      exact tsub_lt_tsub_right_of_le (hcla t (hsσ' t h)) this
    · simp only [h', ↓reduceIte]
      push Not at h'
      by_cases h : t ≤ s
      · simp only [h, ↓reduceIte]
        have h1 : cl t ≤ cl s := hmono.monotoneOn (hsσ' t h) (hsσ' s le_rfl) h
        have h2 : 0 < t' - s := tsub_pos_of_lt h'
        calc cl t - a ≤ cl s - a := tsub_le_tsub_right h1 a
          _ < cl s - a + (t' - s) := lt_add_of_pos_right _ h2
      · simp only [h, ↓reduceIte]
        push Not at h
        exact (add_lt_add_iff_left (cl s - a)).2 (tsub_lt_tsub_right_of_le h.le htt')
  set γ : ℝ≥0 → ℂ := fun t => if t ≤ s then Γ t else Λ' (cl s - a + (t - s)) + c with hγ
  have hγτ : ∀ t, γ t = Λ' (τ t) + c := by
    intro t
    simp only [hγ, hτ]
    split_ifs with h
    · exact hΓΛ t h
    · rfl
  have hγc : Continuous γ := by
    refine continuous_if_le continuous_id continuous_const (hΓc.mono fun t ht => ht)
      ((hΛc.comp (continuous_const.add (continuous_id.sub continuous_const))).add continuous_const).continuousOn ?_
    intro t ht
    have ht' : t = s := ht
    rw [ht', tsub_self, add_zero, hΓΛ s le_rfl]
  have hψγ : ∀ t, ψ (γ t) = η (a + τ t) := fun t => by rw [hγτ]; exact (hspec _).2.1
  have hγH : ∀ t, γ t ∈ Hbar := fun t => by
    rw [hγτ]; show (0 : ℝ) ≤ (Λ' (τ t) + c).im; simpa using (show (0 : ℝ) ≤ (Λ' (τ t)).im from (hspec _).1)
  refine ⟨γ, ⟨hγc, fun t t' he => ?_, fun t => hγH t, ?_, fun t ht => ?_⟩, hγH, fun t => ⟨τ t, hψγ t, fun ht => ?_⟩,
    fun z hz ρ hzρ => ?_⟩
  · -- injective
    have h1 := hψγ t
    rw [he, hψγ t'] at h1
    have h2 := hR.path.1 (show ((a + τ t' : ℝ≥0) : ℝ≥0∞) ≤ ⊤ from le_top)
      (show ((a + τ t : ℝ≥0) : ℝ≥0∞) ≤ ⊤ from le_top) h1
    exact hτmono.injective (add_left_cancel h2).symm
  · -- proper
    have hτt : Tendsto (fun t => a + τ t) atTop atTop := by
      refine tendsto_atTop.2 fun b => (eventually_ge_atTop (b + s + 1)).mono fun t ht => ?_
      have hts : ¬ t ≤ s := not_le.2 (lt_of_lt_of_le (lt_of_le_of_lt le_add_self (lt_add_one _)) ht)
      simp only [hτ, hts, ↓reduceIte]
      have : b ≤ t - s := by
        rw [le_tsub_iff_right (le_of_lt (not_le.1 hts))]
        exact (le_add_right le_rfl).trans ht
      exact this.trans (le_add_self.trans (le_add_self))
    have hlow : ∀ t, ‖η (a + τ t)‖ - (M + |c|) ≤ ‖γ t‖ := by
      intro t
      have h1 := hM (Λ' (τ t)) (hspec _).1
      have h2 : ψ (Λ' (τ t) + c) = η (a + τ t) := (hspec _).2.1
      rw [h2] at h1
      have h3 := norm_sub_norm_le (η (a + τ t)) (Λ' (τ t))
      have h4 : ‖Λ' (τ t)‖ ≤ ‖γ t‖ + |c| := by
        rw [hγτ]
        have := norm_sub_le (Λ' (τ t) + c) (c : ℂ)
        simp only [add_sub_cancel_right, Complex.norm_real, Real.norm_eq_abs] at this
        linarith
      linarith
    exact tendsto_atTop_mono hlow (tendsto_atTop_add_const_right _ _ (hprop.comp hτt))
  · -- agreement
    exact (hγτ t).trans (by simp only [hτ, ht, ↓reduceIte]; exact (hΓΛ t ht).symm)
  · -- positive continuation time
    simp only [hτ]
    split_ifs with h
    · have := hmono (show ((0 : ℝ≥0) : ℝ≥0∞) ≤ σ by simp) (hsσ' t h) ht
      rw [hcl0] at this
      exact tsub_pos_of_lt this
    · push Not at h
      exact lt_of_lt_of_le (tsub_pos_of_lt h) le_add_self
  · -- every point over the continuation is on the completion
    have hzΛ : z - c = Λ' ρ := (hspec ρ).2.2 (z - c) (hsub z hz) (by rw [sub_add_cancel]; exact hzρ)
    have hz' : z = Λ' ρ + c := by rw [← hzΛ]; ring
    rw [hz']
    by_cases hρ : cl s - a ≤ ρ
    · refine ⟨s + (ρ - (cl s - a)), ?_⟩
      rw [hγτ]
      congr 2
      simp only [hτ]
      split_ifs with h
      · have h0 : ρ - (cl s - a) = 0 := by
          have : s + (ρ - (cl s - a)) ≤ s + 0 := by rwa [add_zero]
          exact le_antisymm (le_of_add_le_add_left this) zero_le
        rw [h0, add_zero]
        exact le_antisymm hρ (tsub_eq_zero_iff_le.1 h0)
      · rw [add_tsub_cancel_left, add_tsub_cancel_of_le hρ]
    · push Not at hρ
      have hmem : a + ρ ∈ cl '' {t | (t : ℝ≥0∞) ≤ σ} := by
        have hs : cl s ∈ cl '' {t | (t : ℝ≥0∞) ≤ σ} := ⟨s, hsσ, rfl⟩
        rw [himg] at hs ⊢
        refine ⟨le_self_add, le_top, fun t' h1 h2 => hs.2.2 t' h1 ?_⟩
        have : a + ρ < cl s := by
          have := add_lt_add_left hρ a
          rwa [tsub_add_cancel_of_le (hcla s hsσ), add_comm] at this
        exact h2.trans this
      obtain ⟨t, ht, hte⟩ := hmem
      have hts : t ≤ s := by
        by_contra h
        push Not at h
        have h1 := hmono hsσ ht h
        have : a + ρ < cl s := by
          have := add_lt_add_left hρ a
          rwa [tsub_add_cancel_of_le (hcla s hsσ), add_comm] at this
        rw [hte] at h1
        exact absurd (h1.trans this) (lt_irrefl _)
      refine ⟨t, ?_⟩
      rw [hγτ]
      congr 2
      simp only [hτ, hts, ↓reduceIte, hte, add_tsub_cancel_left]

/-! ### Lemma G9 -/

/-- **Lemma G9 for the complete ordered reference of G8, at one retained pair** (`G9LiftStatement`). -/
theorem g9LiftStatement : G9LiftStatement := by
  intro α β u r φ ψ lift w v Γ₁ Γ₂ U₁ U₂ hcomp hα0 hβ0 pg₁ pg₂ hrat hO hC hφ hψw hw0 hGeo hk₁ hk₂ hΓ₁0 hΓ₂0
    hc₁ hc₂ hH₁ hH₂ s₁ s₂ hs₁ hs₂ hp₁ hp₂ hcom
  obtain ⟨cα, iα, mα, pα, cβ, iβ, mβ, pβ, hordαβ⟩ := hcomp
  have hαP : Supp9B.IsProperCurve α := ⟨cα, iα, mα, pα⟩
  have hβP : Supp9B.IsProperCurve β := ⟨cβ, iβ, mβ, pβ⟩
  have hα0' : (α 0).im = 0 := by rw [hα0]; simp
  have hβ0' : (β 0).im = 0 := by rw [hβ0]; simp
  have hα0r : (α 0).re = 0 := by rw [hα0]; simp
  set A := α '' Icc 0 u ∪ β '' Icc 0 r with hAdef
  set D := activeDomain α u β r with hDdef
  have hAc : IsClosed A := ((isCompact_Icc.image cα).union (isCompact_Icc.image cβ)).isClosed
  have hg : IsRetGood α u β r := ⟨cα.continuousOn, cβ.continuousOn, fun t _ => mα t, fun t _ => mβ t, hα0', hβ0',
    fun t ht he => (ne_of_lt ht) (iβ he)⟩
  obtain ⟨hR₂, -, hR₁⟩ := isRetCont_of_ordinary hg hC hφ pg₁ pg₂ (fun _ _ => rfl) (fun _ _ => rfl) hO
  -- the translation of the first chart is the first tip's coordinate
  have hww : (w : ℂ) - ((limUnder (𝓝[activeDomain α u β r] (α u)) φ).re : ℂ) = 0 :=
    hR₁.tipUniq _ (show (0 : ℝ) ≤ ((w : ℂ) - ((limUnder (𝓝[activeDomain α u β r] (α u)) φ).re : ℂ)).im by simp)
      (show ψ ((w : ℂ) - ((limUnder (𝓝[activeDomain α u β r] (α u)) φ).re : ℂ) +
        ((limUnder (𝓝[activeDomain α u β r] (α u)) φ).re : ℂ)) = α u by rw [sub_add_cancel]; exact hψw)
  have hDA : ∀ z ∈ D, z ∉ A := fun z hz => hz.1.2
  have hDH : D ⊆ H := fun z hz => hz.1.1
  have hbij : BijOn ψ H D := hC.bijOn hβ0'
  have hoff : ∀ z ∉ H, ψ z ∉ D := hC.inv_notMem hβ0'
  have hψc : ContinuousOn ψ Hbar := hC.continuousOn_inv
  obtain ⟨M, hM⟩ := hC.2.2.2.2.2.2.2.2.2.1
  have hψ0 : ψ 0 = β r := hC.inv_zero hβ0'
  obtain ⟨c₁, σ₁, -, hmono₁, himg₁, hpth₁, hHb₁⟩ := hk₁
  obtain ⟨c₂, σ₂, -, hmono₂, himg₂, hpth₂, hHb₂⟩ := hk₂
  have hσ₁0 : 0 < σ₁ := pos_of_isClock hO.1 cα.continuousOn iα.injOn (isCompact_Icc.image cβ).isClosed
    hO.2.2.2.2.2.1 hmono₁ himg₁
  have himg₂' : c₂ '' {s | (s : ℝ≥0∞) ≤ σ₂} = {t | r ≤ t ∧ (t : ℝ≥0∞) ≤ ⊤ ∧
      ∀ t' : ℝ≥0, r < t' → t' < t → β t' ∉ β '' Icc 0 r ∪ α '' Icc 0 u} := by
    rw [himg₂, hAdef, union_comm]
  have hσ₂0 : 0 < σ₂ := pos_of_isClock hO.2.1 cβ.continuousOn iβ.injOn (isCompact_Icc.image cα).isClosed
    hO.2.2.2.2.1 hmono₂ himg₂'
  have hgeoA : ∀ y : ℝ, v < y → ψ y ∉ A := fun y hy => (hGeo y hy).2.2
  have hs₁σ := le_sigma_of_adm hAc cα hDA hbij.mapsTo hgeoA hσ₁0 hmono₁ himg₁ hpth₁ hp₁
  have hs₂σ := le_sigma_of_adm hAc cβ hDA hbij.mapsTo hgeoA hσ₂0 hmono₂ himg₂ hpth₂ hp₂
  have hc₁0 : c₁ 0 = u := clock_zero le_top hmono₁ himg₁
  have hc₂0 : c₂ 0 = r := clock_zero le_top hmono₂ himg₂
  -- the fresh common point
  obtain ⟨t₁, t₂, ht₁0, ht₁s, ht₂0, ht₂s, heq⟩ := hcom
  have ht₁σ : (t₁ : ℝ≥0∞) ≤ σ₁ := (ENNReal.coe_le_coe.2 ht₁s).trans hs₁σ
  have ht₂σ : (t₂ : ℝ≥0∞) ≤ σ₂ := (ENNReal.coe_le_coe.2 ht₂s).trans hs₂σ
  have hq : α (c₁ t₁) = β (c₂ t₂) := by rw [hpth₁ t₁ ht₁σ, hpth₂ t₂ ht₂σ, heq]
  have hqA : α (c₁ t₁) ∉ A := by
    rw [hpth₁ t₁ ht₁σ]
    rcases hp₁ t₁ ht₁0 ht₁s with hH | ⟨h0, hv⟩
    · exact hDA _ (hbij.mapsTo hH)
    · have e : Γ₁ t₁ = ((Γ₁ t₁).re : ℂ) := Complex.ext (by simp) (by simp [h0])
      rw [e]; exact hgeoA _ hv
  have h0σ₁ : ((0 : ℝ≥0) : ℝ≥0∞) ≤ σ₁ := by simp
  have h0σ₂ : ((0 : ℝ≥0) : ℝ≥0∞) ≤ σ₂ := by simp
  have ha : u < c₁ t₁ := by have := hmono₁ h0σ₁ ht₁σ ht₁0; rwa [hc₁0] at this
  have hb : r < c₂ t₂ := by have := hmono₂ h0σ₂ ht₂σ ht₂0; rwa [hc₂0] at this
  have himgt₁ : c₁ t₁ ∈ c₁ '' {t | (t : ℝ≥0∞) ≤ σ₁} := ⟨t₁, ht₁σ, rfl⟩
  have himgt₂ : c₂ t₂ ∈ c₂ '' {t | (t : ℝ≥0∞) ≤ σ₂} := ⟨t₂, ht₂σ, rfl⟩
  rw [himg₁] at himgt₁
  rw [himg₂] at himgt₂
  have hseed : (β 0).re ≤ (α 0).re := by rw [hα0, hβ0]
  -- the complete tails never return to the retained union
  have hno₁ : ∀ t : ℝ≥0, u < t → α t ∉ A := by
    intro t ht hA
    rcases lt_trichotomy t (c₁ t₁) with h | h | h
    · exact himgt₁.2.2 t ht h hA
    · exact hqA (h ▸ hA)
    · rcases hA with ⟨s', hs', hs'e⟩ | ⟨t'', ht'', ht''e⟩
      · exact (ne_of_lt (lt_of_le_of_lt hs'.2 ht)) (iα hs'e)
      · have := Supp9B.contact_order hαP hβP hα0' hβ0' hseed hordαβ hq ht''e.symm h
        exact absurd (this.trans_le ht''.2) (not_lt.2 hb.le)
  have hno₂ : ∀ t : ℝ≥0, r < t → β t ∉ A := by
    intro t ht hA
    rcases lt_trichotomy t (c₂ t₂) with h | h | h
    · exact himgt₂.2.2 t ht h hA
    · exact hqA (by rw [hq, ← h]; exact hA)
    · rcases hA with ⟨s', hs', hs'e⟩ | ⟨t'', ht'', ht''e⟩
      · have := Supp9B.contact_order hαP hβP hα0' hβ0' hseed hordαβ hs'e hq (lt_of_le_of_lt hs'.2 ha)
        exact absurd this (not_lt.2 h.le)
      · exact (ne_of_lt (lt_of_le_of_lt ht''.2 ht)) (iβ ht''e)
  -- the completions
  obtain ⟨γ₁, hγ₁, hγ₁H, hP1₁, hP2₁⟩ := exists_tail_completion hR₁ (union_comm _ _) hno₁ pα hs₁σ hmono₁ himg₁ hpth₁
    hHb₁ (continuousOn_Iic_of_lt hc₁ hs₁)
  obtain ⟨γ₂, hγ₂, hγ₂H, hP1₂, hP2₂⟩ := exists_tail_completion hR₂.shift_zero rfl hno₂ pβ hs₂σ hmono₂ himg₂
    hpth₂ hHb₂ (continuousOn_Iic_of_lt hc₂ hs₂)
  have hγ₁P : Supp9B.IsProperCurve γ₁ := Supp9B.isProperCurve_of_isProperCompletion hγ₁
  have hγ₁0 : γ₁ 0 = w := by rw [hγ₁.2.2.2.2 0 zero_le, hΓ₁0]
  have hγ₁0im : (γ₁ 0).im = 0 := by rw [hγ₁0]; simp
  have hγ₂0 : γ₂ 0 = 0 := by rw [hγ₂.2.2.2.2 0 zero_le, hΓ₂0]
  -- real chart points over untouched real points
  have hψreal : Continuous fun y : ℝ => ψ (y : ℂ) :=
    hψc.comp_continuous continuous_ofReal fun y => show (0 : ℝ) ≤ (y : ℂ).im by simp
  have hcl : ∀ y : ℝ, ψ y ∈ closure D := by
    intro y
    have hxcl : (y : ℂ) ∈ closure H := by
      refine Metric.mem_closure_iff.2 fun ε hε => ⟨(y : ℂ) + ((ε / 2 : ℝ) : ℂ) * I, ?_, ?_⟩
      · show (0 : ℝ) < ((y : ℂ) + ((ε / 2 : ℝ) : ℂ) * I).im
        simp; linarith
      · rw [Complex.dist_eq, sub_add_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (half_pos hε)]
        exact half_lt_self hε
    have := ((hψc _ (show (0 : ℝ) ≤ (y : ℂ).im by simp)).mono fun z (hz : z ∈ H) =>
      show (0 : ℝ) ≤ z.im from le_of_lt hz).mem_closure_image hxcl
    rwa [hbij.image_eq] at this
  have hreal : ∀ y : ℝ, ψ y ∉ A → (ψ y).im = 0 := by
    intro y hy
    have hHbarC : IsClosed Hbar := isClosed_le continuous_const Complex.continuous_im
    have him0 : 0 ≤ (ψ y).im :=
      (closure_minimal (fun z hz => show (0 : ℝ) ≤ z.im from le_of_lt (hDH hz)) hHbarC) (hcl y)
    refine le_antisymm (not_lt.1 fun hpos => ?_) him0
    exact hoff y (fun h => by have : (0 : ℝ) < (y : ℂ).im := h; simp at this)
      (mem_activeDomain_of_mem_closure hAc (hcl y) hpos hy)
  have huniq : ∀ y₁ y₂ : ℝ, ψ y₁ ∉ A → ψ y₁ = ψ y₂ → y₁ = y₂ := by
    intro y₁ y₂ hy he
    have hDe : D = H \ fillH (α '' Icc 0 u ∪ β '' Icc 0 r) := activeDomain_eq hAc
    obtain ⟨w₀, -, -, -, hu⟩ := hR₂.reg (ψ y₁) (by rw [← hDe]; exact hcl y₁) hy
    have h1 := hu y₁ (show (0 : ℝ) ≤ (y₁ : ℂ).im by simp) rfl
    have h2 := hu y₂ (show (0 : ℝ) ≤ (y₂ : ℂ).im by simp) he.symm
    exact ofReal_injective (h1.trans h2.symm)
  have hnotα : ∀ z : ℂ, z ∈ Hbar → ψ z ∉ A → z ∉ range γ₁ → ψ z ∉ range α := by
    rintro z hz hzA hzγ ⟨t, ht⟩
    by_cases htu : t ≤ u
    · exact hzA (ht ▸ Or.inl ⟨t, ⟨zero_le, htu⟩, rfl⟩)
    · push Not at htu
      exact hzγ (hP2₁ z hz (t - u) (by rw [add_tsub_cancel_of_le htu.le]; exact ht.symm))
  have hES : ∀ y : ℝ, ψ y ∉ A → y ∈ Ioi w → (y : ℂ) ∉ range γ₁ → ψ y ∈ rightSide α := by
    intro y hy hyw hyγ
    have him := hreal y hy
    have hnr := hnotα y (show (0 : ℝ) ≤ (y : ℂ).im by simp) hy hyγ
    have hyA' : ψ y ∉ α '' Icc 0 u := fun h => hy (Or.inl h)
    have hside := chart_side_of_real cα.continuousOn iα.injOn (fun t _ => mα t) hα0' hDH
      (fun z hz h => hDA z hz (Or.inl h)) hbij.mapsTo hbij.injOn hψc hM hψw hyA' him
    have hre : 0 < (ψ y).re := by
      rcases lt_trichotomy (ψ y).re 0 with h | h | h
      · exact absurd (hside.2 (by rw [hα0r]; exact h)) (not_lt.2 (le_of_lt hyw))
      · exfalso
        exact hnr ⟨0, by rw [hα0]; exact Complex.ext (by simp [h]) (by simp [him])⟩
      · exact h
    have e : ψ y = ((ψ y).re : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [e] at hnr ⊢
    exact ofReal_mem_rightSide_of_notMem hαP hα0' (by rw [hα0r]; exact hre) hnr
  -- one untouched real point right of the first tip, off the first curve
  have hwv : w ≤ v := by
    by_contra h
    push Not at h
    have := (hGeo w h).2.2
    rw [hψw] at this
    exact this (Or.inl ⟨u, ⟨zero_le, le_rfl⟩, rfl⟩)
  obtain ⟨y₀, hy₀v, hy₀S⟩ : ∃ y₀ : ℝ, v < y₀ ∧ ψ y₀ ∈ rightSide α := by
    set f : ℝ → ℝ := fun y => (ψ (y : ℂ)).re with hf
    have hfc : Continuous f := Complex.continuous_re.comp hψreal
    have hne : f (v + 1) ≠ f (v + 2) := by
      intro he
      have e1 := (hGeo (v + 1) (by linarith)).1
      have e2 := (hGeo (v + 2) (by linarith)).1
      have : ψ ((v + 1 : ℝ) : ℂ) = ψ ((v + 2 : ℝ) : ℂ) := Complex.ext he (by rw [e1, e2])
      have := huniq _ _ (hGeo (v + 1) (by linarith)).2.2 this
      linarith
    have hivt : ∀ q : ℝ, q ∈ uIcc (f (v + 1)) (f (v + 2)) → ∃ y ∈ uIcc (v + 1) (v + 2), f y = q := fun q hq =>
      intermediate_value_uIcc hfc.continuousOn hq
    obtain ⟨q, hq⟩ : ∃ q : ℚ, (q : ℝ) ∈ uIcc (f (v + 1)) (f (v + 2)) := by
      rcases lt_or_gt_of_ne hne with h | h
      · obtain ⟨q, h1, h2⟩ := exists_rat_btwn h
        exact ⟨q, by rw [uIcc_of_le h.le]; exact ⟨h1.le, h2.le⟩⟩
      · obtain ⟨q, h1, h2⟩ := exists_rat_btwn h
        exact ⟨q, by rw [uIcc_of_ge h.le]; exact ⟨h1.le, h2.le⟩⟩
    obtain ⟨y₀, hy₀, hfy₀⟩ := hivt q hq
    have hy₀v : v < y₀ := by
      rw [uIcc_of_le (by linarith)] at hy₀; linarith [hy₀.1]
    obtain ⟨h0, hpos, hA⟩ := hGeo y₀ hy₀v
    have e : ψ y₀ = ((q : ℝ) : ℂ) := Complex.ext (by rw [ofReal_re]; exact hfy₀) (by rw [h0]; simp)
    have hq0 : 0 < (q : ℝ) := by rw [← hfy₀]; exact hpos
    refine ⟨y₀, hy₀v, ?_⟩
    rw [e]
    exact ofReal_mem_rightSide_of_notMem hαP hα0' (by rw [hα0r]; exact hq0) (hrat q hq0)
  -- the image of the chart right side of the first completion
  have hSI : ∀ y : ℝ, (y : ℂ) ∈ rightSide γ₁ → y ∈ Ioi w := by
    intro y hy
    have hyγ := notMem_range_of_mem_rightSide hy
    rcases lt_trichotomy y w with h | h | h
    · exfalso
      have hL := ofReal_mem_leftSide_of_notMem hγ₁P hγ₁0im (by rw [hγ₁0]; simpa using h) hyγ
      exact Set.disjoint_left.1 (disjoint_leftSide_rightSide hγ₁P hγ₁0im) hL hy
    · exact absurd ⟨0, by rw [hγ₁0, h]⟩ hyγ
    · exact h
  have hIS : ∀ y ∈ Ioi w, (y : ℂ) ∉ range γ₁ → (y : ℂ) ∈ rightSide γ₁ := fun y hy hyγ =>
    ofReal_mem_rightSide_of_notMem hγ₁P hγ₁0im (by rw [hγ₁0]; simpa using hy) hyγ
  have hψS : ∀ z ∈ rightSide γ₁, z ∈ H → ψ z ∈ rightSide α ∪ leftSide α := by
    intro z hz hzH
    have hzD := hbij.mapsTo hzH
    have hzS : ψ z ∉ seedRayClosure α := by
      rintro (⟨t, ht⟩ | ⟨-, him⟩)
      · exact hnotα z (show (0 : ℝ) ≤ z.im from le_of_lt (show (0 : ℝ) < z.im from hzH)) (hDA _ hzD)
          (notMem_range_of_mem_rightSide hz) ⟨t, ht⟩
      · have : (0 : ℝ) < (ψ z).im := hDH hzD
        rw [hα0'] at him
        linarith
    rcases (Supp9B.compl_seedRayClosure_eq hαP hα0').subset hzS with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hEo : IsOpen {y : ℝ | ψ y ∉ A} := hAc.isOpen_compl.preimage hψreal
  have hγE : ∀ t, 0 < t → (γ₁ t).im = 0 → (γ₁ t).re ∈ {y : ℝ | ψ y ∉ A} := by
    intro t ht him
    obtain ⟨ρ, hρ, hρpos⟩ := hP1₁ t
    have e : ((γ₁ t).re : ℂ) = γ₁ t := Complex.ext (by simp) (by simp [him])
    show ψ ((γ₁ t).re : ℂ) ∉ A
    rw [e, hρ]
    exact hno₁ _ (lt_add_of_pos_right _ (hρpos ht))
  have hside := image_side_subset hγ₁P (isOpen_rightSide hγ₁P) isPreconnected_connectedComponentIn
    ⟨Supp9B.rightRef γ₁, Supp9B.rightRef_mem_rightSide hγ₁P.2.2.1 hγ₁0im, by
      simp [Supp9B.rightRef, hγ₁0im]⟩
    (fun z hz => notMem_range_of_mem_rightSide hz) ordConnected_Ioi (by rw [hγ₁0]; simp) hSI hIS
    (isOpen_rightSide hαP) (isOpen_leftSide hαP) (disjoint_leftSide_rightSide hαP hα0').symm hψc hψS
    (show y₀ ∈ Ioi w from lt_of_le_of_lt hwv hy₀v) hy₀S hEo hγE (fun y hy hyI hyγ => hES y hy hyI hyγ)
  -- the order
  have hβnotR : ∀ t, β t ∉ rightSide α := by
    intro t hR
    rcases hordαβ ⟨t, rfl⟩ with hL | hS
    · exact Set.disjoint_left.1 (disjoint_leftSide_rightSide hαP hα0') hL hR
    · exact rightSide_subset_compl α hR hS
  have hord : range γ₂ ⊆ closedLeftSide γ₁ := by
    rintro _ ⟨t, rfl⟩
    by_cases hS : γ₂ t ∈ seedRayClosure γ₁
    · exact Or.inr hS
    rcases (Supp9B.compl_seedRayClosure_eq hγ₁P hγ₁0im).subset hS with hL | hR
    · exact Or.inl hL
    exfalso
    obtain ⟨ρ, hρ, hρpos⟩ := hP1₂ t
    rcases (show (0 : ℝ) ≤ (γ₂ t).im from hγ₂H t).lt_or_eq with hpos | h0
    · have := hside (γ₂ t) hR hpos
      rw [hρ] at this
      exact hβnotR _ this
    · have e : ((γ₂ t).re : ℂ) = γ₂ t := Complex.ext (by simp) (by simp [h0.symm])
      have hyI := hSI (γ₂ t).re (by rw [e]; exact hR)
      rcases eq_zero_or_pos t with ht0 | ht0
      · rw [ht0, hγ₂0] at hyI
        simp only [zero_re, mem_Ioi] at hyI
        linarith
      · have hyA : ψ ((γ₂ t).re : ℂ) ∉ A := by
          rw [e, hρ]; exact hno₂ _ (lt_add_of_pos_right _ (hρpos ht0))
        have := hES _ hyA hyI (by rw [e]; exact notMem_range_of_mem_rightSide hR)
        rw [e, hρ] at this
        exact hβnotR _ this
  -- the seeds are not visited again
  have hs₁' : Γ₁ 0 ∉ range γ₂ := by
    rintro ⟨t, ht⟩
    obtain ⟨ρ, hρ, -⟩ := hP1₂ t
    rw [ht, hΓ₁0, hψw] at hρ
    rcases eq_zero_or_pos ρ with h | h
    · rw [h, add_zero] at hρ
      exact hO.2.2.2.2.2.1 ⟨r, ⟨zero_le, le_rfl⟩, hρ.symm⟩
    · exact hno₂ _ (lt_add_of_pos_right _ h) (hρ ▸ Or.inl ⟨u, ⟨zero_le, le_rfl⟩, rfl⟩)
  have hs₂' : Γ₂ 0 ∉ range γ₁ := by
    rintro ⟨t, ht⟩
    obtain ⟨ρ, hρ, -⟩ := hP1₁ t
    rw [ht, hΓ₂0, hψ0] at hρ
    rcases eq_zero_or_pos ρ with h | h
    · rw [h, add_zero] at hρ
      exact hO.2.2.2.2.1 ⟨u, ⟨zero_le, le_rfl⟩, hρ.symm⟩
    · exact hno₁ _ (lt_add_of_pos_right _ h) (hρ ▸ Or.inr ⟨r, ⟨zero_le, le_rfl⟩, rfl⟩)
  exact ⟨γ₁, γ₂, hγ₁, hγ₂, hord, hs₁', hs₂'⟩

end RLC

end InteractingSLE
