/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JaZero
import InteractingSLE.Spec.Supplement.SB2JvRoot
import InteractingSLE.Spec.Supplement.SB2JvCap
import InteractingSLE.Spec.Supplement.SB2JiClock

/-!
# SB2(2)'s joint stage induction: the stage curve's start, end and values through the relative run chart

Packet PROVE-SB2-LIFTSET (round 20). At a lockstep stage the piece runs on the tail of the actual walk, `q t =
β₀ (t_L + σ t)` with a continuous tail time `σ` (`exists_tailTime`), and at good times the lifted point is the lift
curve's point `γ (σ t)` (`lift_mem_H_iff`). Hence:

* **`tendsto_relValp_of_tail`**: the run-chart values along the good times tend to the relative chart's value at the
  lift curve's point (where the relative chart is continuous from `ℍ`);
* **`phys_facts_of_fill`**: the physical domain identity in the form `stageRelFinP_of_canon` reads it (the relative
  chart in physical coordinates is a hull chart of `fill (A ∪ B)` and maps `ℍ` onto its complement);
* `exists_good_between`, **`mem_closure_clock_good`**, **`mem_closure_good_top`**: good times accumulate from the
  right, read through the clock;
* **`tendsto_stCurvep_fin`**: a continuous finite stage curve whose values along the good times converge at the
  end converges at `∞`;
* **`stCurvep_mem_Hbar`**: a continuous stage curve with values in `ℍ̄` at the good times stays in `ℍ̄`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep Sec7.PocketTraversal

variable {c : Chart} {R m : ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}

/-- **At a good time the lifted point is the lift curve's point**, in `ℍ`. -/
theorem liftPt_eq_of_good (hγ : IsTailLiftCurve c R m β₀ tL γ) (hcH : ContinuousOn c.2.1 H)
    (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hoff : BdryOff c) {q : ℝ≥0 → ℂ} {L : ℝ≥0∞} {σ : ℝ≥0 → ℝ≥0}
    (hσ : ∀ t ∈ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ L}, β₀ (tL + σ t) = q t) {t : ℝ≥0} (ht : t ∈ goodTp c q L) :
    liftPt c m (q t) = γ (σ t) ∧ γ (σ t) ∈ H := by
  have hl := lift_mem_H_iff hγ hcH hc1 hoff (σ t)
  have hD : β₀ (tL + σ t) ∈ c.2.1 '' H := by rw [hσ t ht.1]; exact ht.2
  have hH := hl.1.1 hD
  refine ⟨by rw [← hσ t ht.1]; exact (hl.2 hH).symm, ?_⟩
  show 0 < (γ (σ t)).im
  simpa using (show (0 : ℝ) < (γ (σ t) - (m : ℂ)).im from hH)

/-- **The run-chart values along the good times tend to the relative chart's value at the lift curve's point.** -/
theorem tendsto_relValp_of_tail (hγ : IsTailLiftCurve c R m β₀ tL γ) (hcH : ContinuousOn c.2.1 H)
    (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hoff : BdryOff c) {q : ℝ≥0 → ℂ} {L : ℝ≥0∞} {s₂ : ExplState}
    {σ : ℝ≥0 → ℝ≥0} (hσc : ContinuousOn σ {t | (t : ℝ≥0∞) ≤ L})
    (hσ : ∀ t ∈ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ L}, β₀ (tL + σ t) = q t) {G : Set ℝ≥0} (hG : G ⊆ goodTp c q L)
    {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) ≤ L) {w : ℂ} (hw : γ (σ t₀) = w)
    (hcw : ContinuousWithinAt (stChart s₂).1 H w) :
    Tendsto (relValp c m q s₂) (𝓝[G] t₀) (𝓝 ((stChart s₂).1 w)) := by
  have hGS : G ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ L} := fun t ht => (hG ht).1
  have hζ : Tendsto (fun t => γ (σ t)) (𝓝[G] t₀) (𝓝 w) := by
    rw [← hw]
    exact (hγ.2.1.1.continuousAt.comp_continuousWithinAt (hσc t₀ ht₀)).tendsto.mono_left
      (nhdsWithin_mono _ hGS)
  have hlift : Tendsto (fun t => liftPt c m (q t)) (𝓝[G] t₀) (𝓝 w) :=
    hζ.congr' (eventually_nhdsWithin_of_forall fun t ht =>
      (liftPt_eq_of_good hγ hcH hc1 hoff hσ (hG ht)).1.symm)
  exact tendsto_relValp_of_continuousWithinAt hcw hlift fun t ht => by
    rw [(liftPt_eq_of_good hγ hcH hc1 hoff hσ (hG ht)).1]
    exact (liftPt_eq_of_good hγ hcH hc1 hoff hσ (hG ht)).2

/-- **The physical domain identity at a lockstep stage, as `stageRelFinP_of_canon` reads it**: the relative chart in
physical coordinates agrees on `ℍ ∖ fill (A ∪ B)` with a hull chart of `fill (A ∪ B)` and maps `ℍ` onto it. -/
theorem phys_facts_of_fill {c₁ : Chart} {A B P₂ : Set ℂ} {ĝ : ℂ → ℂ}
    (hc : IsDomainChart (H \ fillH A) c) (hcN : WalkIntCanon.IsNormalized c)
    (h₁ : IsDomainChart (H \ fillH P₂) c₁) (hc₁N : WalkIntCanon.IsNormalized c₁) (hA : IsCompact A)
    (hĝ : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (ĝ p))) {C : ℝ} (hC : ∀ p ∈ Hbar, ‖ĝ p - p‖ ≤ C)
    (hγ : IsTailLiftCurve c R m β₀ tL γ) (hβ : Supp9B.IsProperCurve β₀)
    (hfill : fillH P₂ = fillH (liftImage β₀ tL γ B)) (hB : IsCompact B) (hBr : B ⊆ range β₀)
    (hhead : β₀ '' Icc 0 tL ⊆ hullK A) (hX : IsHPHull (fillH (A ∪ B))) :
    ∃ x₁ : ℝ, (∀ z ∈ H \ fillH (A ∪ B), c₁.1 (c.1 z + (m : ℂ)) = (Mo.hullChart (fillH (A ∪ B)) x₁).1 z) ∧
      (Mo.physRelChart c c₁ m).2.1 '' H = H \ fillH (A ∪ B) := by
  have hD := isDomainChart_phys_of_fill hc h₁ hA hĝ hC hγ hβ hfill hB hBr hhead
  obtain ⟨x₁, hf, -⟩ := Mt.physRelChart_eq_hullChart hX hcN hc₁N m hD
  exact ⟨x₁, fun z hz => hf hz, hD.image_eq⟩

/-! ### Good times from the right, through the clock -/

/-- **Good times accumulate from the right**: below `L`, every time has good times just after it. -/
theorem exists_good_between {G : Set ℝ≥0} {L : ℝ≥0∞} (hgd : {t : ℝ≥0 | (t : ℝ≥0∞) < L} ⊆ closure G)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < L) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ t' ∈ G, t < t' ∧ t' < t + ε ∧ (t' : ℝ≥0∞) < L := by
  obtain ⟨r, htr, hrL⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have htr' : t < r := by exact_mod_cast htr
  set r' := min r (t + ε) with hr'
  have htr'' : t < r' := lt_min htr' (lt_add_of_pos_right t hε)
  obtain ⟨t₁, h1, h2⟩ := exists_between htr''
  have hr'L : (r' : ℝ≥0∞) < L := lt_of_le_of_lt (by exact_mod_cast min_le_left r (t + ε)) hrL
  have ht₁L : (t₁ : ℝ≥0∞) < L := lt_trans (by exact_mod_cast h2) hr'L
  obtain ⟨t', ⟨h3, h4⟩, ht'G⟩ := mem_closure_iff.1 (hgd ht₁L) (Ioo t r') isOpen_Ioo ⟨h1, h2⟩
  refine ⟨t', ht'G, h3, lt_of_lt_of_le h4 (min_le_right _ _), lt_trans (by exact_mod_cast h4) hr'L⟩

/-- **Good times through the clock accumulate from the right** (finite piece): every `u ≥ 0` is a limit of
parameters `u' ≥ u` whose clock time is good. -/
theorem mem_closure_clock_good {G : Set ℝ≥0} {L₁ : ℝ≥0} (hL₁ : 0 < L₁)
    (hgd : {t : ℝ≥0 | (t : ℝ≥0∞) < L₁} ⊆ closure G) {u : ℝ} (hu : 0 ≤ u) :
    u ∈ closure ({u' : ℝ | 0 ≤ u' ∧ (clockOf L₁ u').toNNReal ∈ G} ∩ Ici u) := by
  have hL : (0 : ℝ) < L₁ := NNReal.coe_pos.2 hL₁
  rw [Metric.mem_closure_iff]
  intro ε hε
  set t₀ : ℝ := clockOf L₁ u with ht₀
  have hm := clockOf_mem_Ico hL hu
  -- continuity of `t ↦ t / (L₁ - t)` at `t₀`
  have hφc : ContinuousAt (fun t : ℝ => t / ((L₁ : ℝ) - t)) t₀ :=
    continuousAt_id.div (continuousAt_const.sub continuousAt_id) (by linarith [hm.2])
  have hφu : t₀ / ((L₁ : ℝ) - t₀) = u := div_sub_clockOf hL hu
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.1 hφc ε hε
  have hδ' : (0 : ℝ≥0) < (min δ ((L₁ : ℝ) - t₀)).toNNReal :=
    Real.toNNReal_pos.2 (lt_min hδ (by linarith [hm.2]))
  have ht₀L : ((t₀.toNNReal : ℝ≥0) : ℝ≥0∞) < (L₁ : ℝ≥0∞) := by
    rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hm.1]; exact hm.2
  obtain ⟨t', ht'G, h1, h2, h3⟩ := exists_good_between hgd ht₀L hδ'
  have h1' : t₀ < (t' : ℝ) := by
    have := NNReal.coe_lt_coe.2 h1; rwa [Real.coe_toNNReal _ hm.1] at this
  have h2' : (t' : ℝ) < t₀ + min δ ((L₁ : ℝ) - t₀) := by
    have := NNReal.coe_lt_coe.2 h2
    rwa [NNReal.coe_add, Real.coe_toNNReal _ hm.1,
      Real.coe_toNNReal _ (le_min hδ.le (by linarith [hm.2]))] at this
  have hmin1 := min_le_left δ ((L₁ : ℝ) - t₀)
  have hmin2 := min_le_right δ ((L₁ : ℝ) - t₀)
  have ht'L : (t' : ℝ) < L₁ := by linarith
  have ht'I : (t' : ℝ) ∈ Ico 0 (L₁ : ℝ) := ⟨t'.2, ht'L⟩
  refine ⟨(t' : ℝ) / ((L₁ : ℝ) - t'), ⟨⟨div_nonneg t'.2 (by linarith), ?_⟩, ?_⟩, ?_⟩
  · rw [clockOf_div_sub ht'I, Real.toNNReal_coe]; exact ht'G
  · rw [mem_Ici, ← hφu]
    exact div_le_div₀ (by linarith) h1'.le (by linarith) (by linarith)
  · have hdist : dist (t' : ℝ) t₀ < δ := by
      rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith
    have := hδε hdist
    rw [hφu, dist_comm] at this
    exact this

/-- **Good times accumulate from the right** (infinite piece, the clock is the identity). -/
theorem mem_closure_good_top {G : Set ℝ≥0} (hgd : ∀ t : ℝ≥0, t ∈ closure G) {u : ℝ} (hu : 0 ≤ u) :
    u ∈ closure ({u' : ℝ | 0 ≤ u' ∧ u'.toNNReal ∈ G} ∩ Ici u) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hgd' : {t : ℝ≥0 | (t : ℝ≥0∞) < ⊤} ⊆ closure G := fun t _ => hgd t
  obtain ⟨t', ht'G, h1, h2, -⟩ := exists_good_between hgd' (show ((u.toNNReal : ℝ≥0) : ℝ≥0∞) < ⊤ from
    ENNReal.coe_lt_top) (Real.toNNReal_pos.2 hε)
  have h1' : u < (t' : ℝ) := by
    have := NNReal.coe_lt_coe.2 h1; rwa [Real.coe_toNNReal _ hu] at this
  have h2' : (t' : ℝ) < u + ε := by
    have := NNReal.coe_lt_coe.2 h2; rwa [NNReal.coe_add, Real.coe_toNNReal _ hu, Real.coe_toNNReal _ hε.le] at this
  refine ⟨t', ⟨⟨t'.2, by rw [Real.toNNReal_coe]; exact ht'G⟩, h1'.le⟩, ?_⟩
  rw [Real.dist_eq, abs_of_neg (by linarith)]
  linarith

variable {q : ℝ≥0 → ℂ} {s₂ : ExplState}

/-- **The end of a finite stage curve**: a stage curve continuous on `[0, ∞)` whose run-chart values along the good
times converge at the end converges at `∞`. -/
theorem tendsto_stCurvep_fin {L₁ : ℝ≥0} (hL₁ : 0 < L₁) (hc : ContinuousOn (stCurvep c m q L₁ s₂) (Ici 0))
    (hgd : {t : ℝ≥0 | (t : ℝ≥0∞) < L₁} ⊆ closure (goodTp c q L₁)) {v : ℂ}
    (hv : Tendsto (relValp c m q s₂) (𝓝[goodTp c q L₁ ∩ {t | (t : ℝ≥0∞) < L₁}] L₁) (𝓝 v)) :
    Tendsto (stCurvep c m q L₁ s₂) atTop (𝓝 v) := by
  have hL : (0 : ℝ) < L₁ := NNReal.coe_pos.2 hL₁
  set G := {u' : ℝ | 0 ≤ u' ∧ (clockOf L₁ u').toNNReal ∈ goodTp c q L₁} with hGdef
  have heq : ∀ u ∈ G, stCurvep c m q L₁ s₂ u = relValp c m q s₂ (clockOf L₁ u).toNNReal := fun u hu => by
    rw [stCurvep_of_fin ENNReal.coe_ne_top, ENNReal.coe_toReal, stValp_of_good hu.2]
  refine tendsto_of_dense_eq hc (fun u hu => mem_closure_clock_good hL₁ hgd hu) heq ?_
  -- the clock times along `G` tend to `L₁` from below, through good times
  have hcl : Tendsto (fun u => (clockOf L₁ u).toNNReal) (atTop ⊓ 𝓟 G)
      (𝓝[goodTp c q L₁ ∩ {t | (t : ℝ≥0∞) < L₁}] L₁) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h1 : Tendsto (clockOf L₁) atTop (𝓝 (L₁ : ℝ)) :=
        (Sec7.R7Aux131.tendsto_clockOf hL).mono_right nhdsWithin_le_nhds
      have h2 : Tendsto (fun u => (clockOf L₁ u).toNNReal) atTop (𝓝 (L₁ : ℝ).toNNReal) :=
        (continuous_real_toNNReal.tendsto _).comp h1
      rw [Real.toNNReal_coe] at h2
      exact h2.mono_left inf_le_left
    · refine eventually_inf_principal.2 (Eventually.of_forall fun u hu => ⟨hu.2, ?_⟩)
      have hm := clockOf_mem_Ico hL hu.1
      show (((clockOf L₁ u).toNNReal : ℝ≥0) : ℝ≥0∞) < (L₁ : ℝ≥0∞)
      rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hm.1]
      exact hm.2
  exact hv.comp hcl

/-- **A continuous stage curve with values in `ℍ̄` at the good times stays in `ℍ̄`.** -/
theorem stCurvep_mem_Hbar {L : ℝ≥0∞} (hL : L ≠ 0) (hc : ContinuousOn (stCurvep c m q L s₂) (Ici 0))
    (hgd : {t : ℝ≥0 | (t : ℝ≥0∞) < L} ⊆ closure (goodTp c q L))
    (hgH : ∀ t ∈ goodTp c q L, relValp c m q s₂ t ∈ Hbar) {u : ℝ} (hu : 0 ≤ u) :
    stCurvep c m q L s₂ u ∈ Hbar := by
  have hHc : IsClosed Hbar := isClosed_le continuous_const Complex.continuous_im
  rcases eq_or_ne L ⊤ with htop | hfin
  · set G := {u' : ℝ | 0 ≤ u' ∧ u'.toNNReal ∈ goodTp c q L} with hGdef
    have hgd' : ∀ t : ℝ≥0, t ∈ closure (goodTp c q L) := fun t =>
      hgd (show (t : ℝ≥0∞) < L by rw [htop]; exact ENNReal.coe_lt_top)
    have hmem := mem_closure_good_top hgd' hu
    have hcw : ContinuousWithinAt (stCurvep c m q L s₂) (G ∩ Ici u) u :=
      (hc u (mem_Ici.2 hu)).mono fun x hx => mem_Ici.2 (hu.trans hx.2)
    refine hHc.closure_subset_iff.2 ?_ (hcw.mem_closure_image hmem)
    rintro _ ⟨x, ⟨hxG, -⟩, rfl⟩
    rw [stCurvep_of_top htop, stValp_of_good hxG.2]
    exact hgH _ hxG.2
  · lift L to ℝ≥0 using hfin
    have hL₁ : 0 < L := pos_iff_ne_zero.2 (by exact_mod_cast hL)
    set G := {u' : ℝ | 0 ≤ u' ∧ (clockOf L u').toNNReal ∈ goodTp c q L} with hGdef
    have hmem := mem_closure_clock_good hL₁ hgd hu
    have hcw : ContinuousWithinAt (stCurvep c m q L s₂) (G ∩ Ici u) u :=
      (hc u (mem_Ici.2 hu)).mono fun x hx => mem_Ici.2 (hu.trans hx.2)
    refine hHc.closure_subset_iff.2 ?_ (hcw.mem_closure_image hmem)
    rintro _ ⟨x, ⟨hxG, -⟩, rfl⟩
    rw [stCurvep_of_fin ENNReal.coe_ne_top, ENNReal.coe_toReal, stValp_of_good hxG.2]
    exact hgH _ hxG.2

end InteractingSLE.Theorem14.SB.Lk
