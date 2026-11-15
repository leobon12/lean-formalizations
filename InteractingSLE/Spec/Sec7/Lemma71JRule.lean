/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71ICap
import InteractingSLE.Spec.Sec7.Lemma71EPrefix
import InteractingSLE.Spec.Sec5.CrossRestartLawPath

/-!
# Lemma 7.1's pocket: the capacity stopping rule is the capacity time along the middle curve

Packet PROVE-LEMMA71J, item R1 of `planning/handoffs/PROVE-LEMMA71I.md` (specification §7.1, proof of Lemma 7.1,
p. 224, `source/spec/p193-240.md` L600: "For each bounded stopping time of this mapped path, the history-locality
statement of Lemma 6.2 applies to the revealed outer curves and the middle prefix"; the stopping times of the mapped
path are the original times at which the mapped prefix reaches a given capacity).

`Lemma71I.exists_capacityRule` gives, for an outer-measurable pocket chart `F` on `C`, a measurable Galmarino rule
`levelRule (capFamily G M) a`: the first rational-coordinate time at which the grid capacity `WholeField.hcapHit` of the
chart values of the middle coordinates reaches the level `a`. Here it is identified, deterministically, with the
original time at which the mapped segment reaches capacity `s`:

* `hcapHit_mono`; `hcapHit_image_eq_capClock`: the grid capacity of a prefix of a segment curve is twice its capacity
  clock;
* `capSet_subset`, `image_Icc_subset_closure_capSet`: the chart values of the rational middle coordinates up to `q`
  lie in the mapped prefix up to original time `q`, and are dense in it;
* **`levelRule_capFamily_eq`**: if the middle curve `γ` traverses the pocket along a continuous strictly increasing
  clock `κ` (every visit to `C` is a time `κ u`, visits are dense in mapped time), and its chart image `Γ(u) = lim F` at
  `γ(κ u)` is a segment curve, then for every capacity `0 < s` below the terminal one
  `levelRule (capFamily G M) (2s) x (pathCoord γ) = κ(capInv Γ s)`.

With `X = Hist × Hist`, `x = (histOf β ⊤, histOf α ⊤)` this is the identification `hτ` of
`Lemma71G.ae_condExp_exp_eq_three_of_le` for the original time `τ_s = κ(capInv Γ s)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.Lemma71Pin

open Lemma71I Lemma71C Sec6

/-! ### Grid capacities of prefixes -/

/-- `hcapHit` is monotone. -/
theorem hcapHit_mono {K K' : Set ℂ} (h : K ⊆ K') : WholeField.hcapHit K ≤ WholeField.hcapHit K' := by
  classical
  unfold WholeField.hcapHit
  refine iInf₂_mono fun n s => ?_
  by_cases h' : Disjoint K' (QuantumZipper.H \ WholeField.gridUnion n s)
  · simp only [h', h'.mono_left h, ↓reduceIte, le_refl]
  · simp only [h', ↓reduceIte]
    exact le_top

/-- **The grid capacity of a prefix of a segment curve is twice its capacity clock.** -/
theorem hcapHit_image_eq_capClock {Γ : ℝ → ℂ} (hΓ : IsSegCurve Γ) {u : ℝ} (hu : 0 ≤ u) :
    WholeField.hcapHit (Γ '' Icc 0 u) = ENNReal.ofReal (2 * capClock Γ u) := by
  set Γ' : ℝ≥0 → ℂ := fun s => Γ s with hΓ'
  have hc : Continuous Γ' := hΓ.1.comp_continuous NNReal.continuous_coe fun s => s.2
  have h0 : (Γ' 0).im ≤ 0 := by
    show (Γ ((0 : ℝ≥0) : ℝ)).im ≤ 0
    rw [NNReal.coe_zero, hΓ.2.2.2.1, Complex.zero_im]
  rw [Lemma71E.image_Icc_real_eq hu, Restart.hcapHit_image_eq hc.continuousOn h0, capClock,
    Lemma71E.image_Icc_real_eq hu]
  congr 1
  ring

/-! ### The chart values of the middle coordinates -/

section Traversal

variable {X : Type*} {G : X × ℂ → ℂ} {M : Set (X × ℂ)} {x : X} {C : Set ℂ} {F : ℂ → ℂ} {γ : ℝ≥0 → ℂ}
  {Γ : ℝ → ℂ} {κ : ℝ → ℝ}

/-- At a point of the open pocket, a limit of the chart within the pocket is its value. -/
theorem eq_of_tendsto_of_mem (hFc : ContinuousOn F C) {p : ℂ} (hp : p ∈ C) {w : ℂ}
    (hw : Tendsto F (𝓝[C] p) (𝓝 w)) : F p = w :=
  have : (𝓝[C] p).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (subset_closure hp)
  tendsto_nhds_unique (hFc p hp).tendsto hw

/-- **The chart values of the rational middle coordinates up to `q` lie on the mapped prefix up to original time
`q`**: every visit `γ(r)` to the pocket is at a clock time `r = κ(u)`, where the chart value is `Γ(u)`. -/
theorem capSet_subset (hM : ∀ z, (x, z) ∈ M ↔ z ∈ C) (hG : ∀ z ∈ C, G (x, z) = F z) (hFc : ContinuousOn F C)
    (hlim : ∀ u, 0 ≤ u → Tendsto F (𝓝[C] (γ (κ u).toNNReal)) (𝓝 (Γ u)))
    (hcov : ∀ t : ℝ≥0, γ t ∈ C → ∃ u, 0 ≤ u ∧ κ u = t) (q : ℚ≥0) :
    capSet G M q x (pathCoord γ) ⊆ Γ '' {u | 0 ≤ u ∧ κ u ≤ ((q : ℝ≥0) : ℝ)} := by
  rintro w ⟨r, hr, hrM, rfl⟩
  have hrC : γ r ∈ C := (hM _).1 hrM
  obtain ⟨u, hu, hκu⟩ := hcov r hrC
  refine ⟨u, ⟨hu, ?_⟩, ?_⟩
  · rw [hκu]
    exact_mod_cast hr
  · have hp : γ (κ u).toNNReal = γ r := by rw [hκu, Real.toNNReal_coe]
    rw [show pathCoord γ r = γ r from rfl, hG _ hrC]
    exact (eq_of_tendsto_of_mem hFc hrC (hp ▸ hlim u hu)).symm

/-- **The chart values of the rational middle coordinates are dense in the mapped prefix**: if visits to the open
pocket are dense in the mapped time, every mapped point `Γ(u)`, `u ≤ U`, `κ(U) ≤ q`, is a limit of chart values
`F(γ(r))` at rational times `r ≤ q` in the pocket. -/
theorem image_Icc_subset_closure_capSet (hM : ∀ z, (x, z) ∈ M ↔ z ∈ C) (hG : ∀ z ∈ C, G (x, z) = F z)
    (hCo : IsOpen C) (hFc : ContinuousOn F C) (hγ : Continuous γ) (hΓc : ContinuousOn Γ (Ici 0))
    (hκm : StrictMonoOn κ (Ici 0)) (hκ0 : 0 ≤ κ 0)
    (hlim : ∀ u, 0 ≤ u → Tendsto F (𝓝[C] (γ (κ u).toNNReal)) (𝓝 (Γ u)))
    (hcov : ∀ t : ℝ≥0, γ t ∈ C → ∃ u, 0 ≤ u ∧ κ u = t)
    (hdense : ∀ u₁ u₂, 0 ≤ u₁ → u₁ < u₂ → ∃ u ∈ Ioo u₁ u₂, γ (κ u).toNNReal ∈ C)
    {q : ℚ≥0} {U : ℝ} (hU : 0 < U) (hUq : κ U ≤ ((q : ℝ≥0) : ℝ)) :
    Γ '' Icc 0 U ⊆ closure (capSet G M q x (pathCoord γ)) := by
  rintro _ ⟨u, hu, rfl⟩
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδΓ⟩ := Metric.continuousWithinAt_iff.1 (hΓc u hu.1) ε hε
  -- an interval about `u` inside `[0, U]` of radius `< δ`
  set a₁ := max 0 (u - δ / 2) with ha₁
  set b₁ := min U (u + δ / 2) with hb₁
  have hab : a₁ < b₁ := by
    rw [ha₁, hb₁, max_lt_iff, lt_min_iff, lt_min_iff]
    exact ⟨⟨hU, by linarith [hu.1]⟩, by linarith [hu.2], by linarith⟩
  have ha₁0 : 0 ≤ a₁ := le_max_left _ _
  have hb₁0 : 0 ≤ b₁ := ha₁0.trans hab.le
  have hb₁U : b₁ ≤ U := min_le_left _ _
  obtain ⟨u', hu'I, hu'C⟩ := hdense a₁ b₁ ha₁0 hab
  have hu'0 : 0 ≤ u' := ha₁0.trans hu'I.1.le
  have hκa : κ a₁ < κ u' := hκm ha₁0 hu'0 hu'I.1
  have hκb : κ u' < κ b₁ := hκm hu'0 hb₁0 hu'I.2
  have hκu'0 : 0 ≤ κ u' := hκ0.trans (hκm.monotoneOn self_mem_Ici hu'0 hu'0)
  -- a rational visit time near `κ u'`
  set O : Set ℝ≥0 := {t | γ t ∈ C ∧ κ a₁ < (t : ℝ) ∧ (t : ℝ) < κ b₁} with hO
  have hOo : IsOpen O :=
    (hCo.preimage hγ).inter ((isOpen_lt continuous_const NNReal.continuous_coe).inter
      (isOpen_lt NNReal.continuous_coe continuous_const))
  have ht'O : (κ u').toNNReal ∈ O := by
    refine ⟨hu'C, ?_, ?_⟩ <;> rw [Real.coe_toNNReal _ hκu'0]
    · exact hκa
    · exact hκb
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 hOo _ ht'O
  obtain ⟨r, -, hr2⟩ := exists_nnrat_le_dist_lt (κ u').toNNReal hη
  have hrO : ((r : ℝ≥0)) ∈ O := hball (mem_ball.2 hr2)
  obtain ⟨u'', hu''0, hκu''⟩ := hcov r hrO.1
  have h1 : a₁ < u'' := (hκm.lt_iff_lt ha₁0 hu''0).1 (by rw [hκu'']; exact hrO.2.1)
  have h2 : u'' < b₁ := (hκm.lt_iff_lt hu''0 hb₁0).1 (by rw [hκu'']; exact hrO.2.2)
  have hrq : r ≤ q := by
    have h3 : ((r : ℝ≥0) : ℝ) ≤ ((q : ℝ≥0) : ℝ) :=
      (hrO.2.2.le.trans (hκm.monotoneOn hb₁0 hU.le hb₁U)).trans hUq
    exact_mod_cast h3
  refine ⟨Γ u'', ⟨r, hrq, (hM _).2 hrO.1, ?_⟩, ?_⟩
  · have hp : γ (κ u'').toNNReal = γ r := by rw [hκu'', Real.toNNReal_coe]
    rw [show pathCoord γ r = γ r from rfl, hG _ hrO.1]
    exact eq_of_tendsto_of_mem hFc hrO.1 (hp ▸ hlim u'' hu''0)
  · rw [dist_comm]
    refine hδΓ hu''0 ?_
    rw [Real.dist_eq, abs_lt]
    have ha : u - δ / 2 ≤ a₁ := le_max_right _ _
    have hb : b₁ ≤ u + δ / 2 := min_le_right _ _
    constructor <;> linarith

/-- **The capacity stopping rule is the capacity time of the mapped segment** (R1 of PROVE-LEMMA71I). Let the chart
`F` (continuous on the open pocket `C`) be represented at `x` by `G` on the domain `M`, let the continuous middle curve
`γ` traverse the pocket along the continuous strictly increasing clock `κ` (`κ 0 ≥ 0`; every visit to `C` is a time
`κ u`; visits are dense in the mapped time), and let its mapped segment `Γ(u) = lim_{z → γ(κ u), z ∈ C} F(z)` be a
segment curve. Then for every capacity time `0 < s` below the terminal one, the level rule of the grid capacity at the
level `2s` (`hcap = 2 × capacity time`) on the rational coordinates of `γ` is the original time `κ(capInv Γ s)` at
which the mapped prefix reaches capacity time `s`. -/
theorem levelRule_capFamily_eq (hM : ∀ z, (x, z) ∈ M ↔ z ∈ C) (hG : ∀ z ∈ C, G (x, z) = F z)
    (hCo : IsOpen C) (hFc : ContinuousOn F C) (hγ : Continuous γ) (hΓ : IsSegCurve Γ)
    (hκc : ContinuousOn κ (Ici 0)) (hκm : StrictMonoOn κ (Ici 0)) (hκ0 : 0 ≤ κ 0)
    (hlim : ∀ u, 0 ≤ u → Tendsto F (𝓝[C] (γ (κ u).toNNReal)) (𝓝 (Γ u)))
    (hcov : ∀ t : ℝ≥0, γ t ∈ C → ∃ u, 0 ≤ u ∧ κ u = t)
    (hdense : ∀ u₁ u₂, 0 ≤ u₁ → u₁ < u₂ → ∃ u ∈ Ioo u₁ u₂, γ (κ u).toNNReal ∈ C)
    {s : ℝ} (hs : 0 < s) (hsl : ENNReal.ofReal s < capLife Γ) :
    levelRule (capFamily G M) (ENNReal.ofReal (2 * s)) x (pathCoord γ) = ENNReal.ofReal (κ (capInv Γ s)) := by
  classical
  obtain ⟨hU0, hUs⟩ := hΓ.capInv_spec hs.le hsl
  set U := capInv Γ s with hUdef
  have hUpos : 0 < U := by
    rcases hU0.eq_or_lt with h | h
    · rw [← h, hΓ.capClock_zero] at hUs
      linarith
    · exact h
  set T : ℝ≥0∞ := ENNReal.ofReal (κ U) with hT
  set a := ENNReal.ofReal (2 * s) with ha
  have ha0 : 0 < 2 * s := by linarith
  set f := capFamily G M with hf
  -- below `T` the running capacity stays below the level
  have hbelow : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ) < κ U → runSup f x (pathCoord γ) ((q : ℝ≥0) : ℝ≥0∞) < a := by
    intro q hq
    obtain ⟨u', hu'0, hu'U, hsub⟩ : ∃ u', 0 ≤ u' ∧ u' < U ∧ ∀ u, 0 ≤ u → κ u ≤ ((q : ℝ≥0) : ℝ) → u ≤ u' := by
      by_cases hq0 : ((q : ℝ≥0) : ℝ) < κ 0
      · refine ⟨0, le_rfl, hUpos, fun u hu hκu => ?_⟩
        have := hκm.monotoneOn self_mem_Ici hu hu
        linarith
      · obtain ⟨u', hu'I, hκu'⟩ := intermediate_value_Icc hU0 (hκc.mono Icc_subset_Ici_self)
          ⟨not_lt.1 hq0, hq.le⟩
        refine ⟨u', hu'I.1, lt_of_le_of_ne hu'I.2 fun h => by rw [h] at hκu'; linarith, fun u hu hκu => ?_⟩
        by_contra hlt
        have := hκm hu'I.1 hu (not_le.1 hlt)
        linarith
    have hbound : ∀ q' : ℚ≥0, q' ≤ q → f q' x (pathCoord γ) ≤ ENNReal.ofReal (2 * capClock Γ u') := by
      intro q' hq'
      calc f q' x (pathCoord γ) ≤ WholeField.hcapHit (Γ '' Icc 0 u') := by
            refine hcapHit_mono ((capSet_subset hM hG hFc hlim hcov q').trans ?_)
            rintro _ ⟨u, ⟨hu, hκu⟩, rfl⟩
            have hq'q : ((q' : ℝ≥0) : ℝ) ≤ ((q : ℝ≥0) : ℝ) := by exact_mod_cast hq'
            exact ⟨u, ⟨hu, hsub u hu (hκu.trans hq'q)⟩, rfl⟩
        _ = _ := hcapHit_image_eq_capClock hΓ hu'0
    have hlt : ENNReal.ofReal (2 * capClock Γ u') < a := by
      rw [ha, ENNReal.ofReal_lt_ofReal_iff ha0]
      have := hΓ.strictMonoOn_capClock hu'0 hU0 hu'U
      linarith
    refine lt_of_le_of_lt (iSup_le fun q' => ?_) hlt
    split_ifs with h
    · exact hbound q' (by exact_mod_cast h)
    · exact zero_le
  -- at `T` the level is reached
  have hat : a ≤ runSup f x (pathCoord γ) T := by
    refine le_of_forall_lt fun b hb => ?_
    have hbtop : b ≠ ⊤ := ne_top_of_lt (hb.trans ENNReal.ofReal_lt_top)
    have hbr : b.toReal < 2 * s := ENNReal.toReal_lt_of_lt_ofReal hb
    have hcont := hΓ.continuousOn_capClock U hU0
    have hev : ∀ᶠ u in 𝓝[Ici 0] U, b.toReal / 2 < capClock Γ u :=
      hcont.eventually (lt_mem_nhds (by rw [hUs]; linarith))
    obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhdsWithin_iff.1 hev
    set u₁ := max 0 (U - η / 2) with hu₁
    have hu₁0 : 0 ≤ u₁ := le_max_left _ _
    have hu₁U : u₁ < U := max_lt hUpos (by linarith)
    have hu₁b : b.toReal < 2 * capClock Γ u₁ := by
      have hmem : u₁ ∈ ball U η ∩ Ici 0 := by
        refine ⟨?_, hu₁0⟩
        rw [mem_ball, Real.dist_eq, abs_lt]
        constructor <;> [linarith [le_max_right 0 (U - η / 2)]; linarith]
      have := hηsub hmem
      simp only [mem_ofPred_eq] at this
      linarith
    have hκu₁U : κ u₁ < κ U := hκm hu₁0 hU0 hu₁U
    have hκU0 : 0 ≤ κ U := hκ0.trans (hκm.monotoneOn self_mem_Ici hU0 hU0)
    obtain ⟨q', hq'1, hq'2⟩ := exists_nnrat_le_dist_lt (κ U).toNNReal (show 0 < κ U - κ u₁ by linarith)
    have hq'T : ((q' : ℝ≥0) : ℝ) ≤ κ U := by
      have := NNReal.coe_le_coe.2 hq'1
      rwa [Real.coe_toNNReal _ hκU0] at this
    have hq'u₁ : κ u₁ < ((q' : ℝ≥0) : ℝ) := by
      rw [NNReal.dist_eq, Real.coe_toNNReal _ hκU0, abs_lt] at hq'2
      linarith [hq'2.1]
    obtain ⟨u₂, hu₂I, hκu₂⟩ := intermediate_value_Icc hu₁U.le (hκc.mono fun u hu => hu₁0.trans hu.1)
      ⟨hq'u₁.le, hq'T⟩
    have hu₂pos : 0 < u₂ := by
      refine lt_of_le_of_lt hu₁0 (lt_of_le_of_ne hu₂I.1 fun h => ?_)
      rw [← h] at hκu₂
      linarith
    have hfq : ENNReal.ofReal (2 * capClock Γ u₂) ≤ f q' x (pathCoord γ) := by
      rw [← hcapHit_image_eq_capClock hΓ hu₂pos.le, hf, capFamily]
      exact (hcapHit_mono (image_Icc_subset_closure_capSet hM hG hCo hFc hγ hΓ.1 hκm hκ0 hlim hcov hdense
        hu₂pos hκu₂.le)).trans (Sec5.CrossRestart.hcapHit_closure _).le
    have hq'le : ((q' : ℝ≥0) : ℝ≥0∞) ≤ T := by
      rw [hT, ← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal hq'T
    have hcl : capClock Γ u₁ ≤ capClock Γ u₂ :=
      hΓ.strictMonoOn_capClock.monotoneOn hu₁0 (hu₁0.trans hu₂I.1) hu₂I.1
    calc b = ENNReal.ofReal b.toReal := (ENNReal.ofReal_toReal hbtop).symm
      _ < ENNReal.ofReal (2 * capClock Γ u₂) :=
          (ENNReal.ofReal_lt_ofReal_iff (by linarith [ENNReal.toReal_nonneg (a := b)])).2 (by linarith)
      _ ≤ f q' x (pathCoord γ) := hfq
      _ ≤ runSup f x (pathCoord γ) T := le_runSup hq'le
  -- the rational test of the level infimum
  have hiff : ∀ q : ℚ≥0, a ≤ runSup f x (pathCoord γ) ((q : ℝ≥0) : ℝ≥0∞) ↔ T ≤ ((q : ℝ≥0) : ℝ≥0∞) := by
    intro q
    constructor
    · intro h
      by_contra hlt
      have hlt' : ((q : ℝ≥0) : ℝ) < κ U := by
        have h1 := not_le.1 hlt
        rw [hT, ← ENNReal.ofReal_coe_nnreal] at h1
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (q : ℝ≥0).2).1 h1
      exact absurd h (not_le.2 (hbelow q hlt'))
    · intro h
      exact hat.trans (runSup_mono h)
  have hinf : levelInf f a x (pathCoord γ) = T := by
    unfold levelInf
    simp_rw [hiff]
    exact iInf_ite_le_eq ENNReal.ofReal_ne_top
  simp only [levelRule, hinf, hat, ↓reduceIte]

end Traversal

end InteractingSLE.Sec7.Lemma71Pin
