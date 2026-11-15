/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.Assembly2Entr

/-!
# Theorem 2.2, uniqueness for the admissible entrances: pathwise lemmas

Packet PROVE-SEC2-PATCH4. Deterministic facts used by the uniqueness proof for the words with a
left and a right mark at `0` (`Assembly3Entr`):

* `IsSLEPathUpTo.vL_eq_of_xL_eq`, `vR_eq_of_xR_eq`: marks with the same initial position coincide;
* `IsSLEPathUpTo.mergeSeeds`: a local path of the word in which only the seeds (marks at `0`) carry
  weight is, after merging each seed group into one mark, a local path of the two-seed word whose
  weights are the group sums (the reverse of `IsSLEPathUpTo.splitL/R`);
* `IsSLEPathUpTo.isIntegratedSLEPath_concat_closed`: a local path up to `σ` that is continuous at
  `σ`, followed by a solution of Definition 2.1 from its state at `σ`, is a solution of
  Definition 2.1 (the variant of `Assembly2.isIntegratedSLEPath_concat` with the first piece
  ending exactly at `σ`);
* `Assembly3.eq_of_markEq`, `eq_leftMark`, `eq_rightMark`: uniqueness for the Lipschitz mark
  equation, so a mark at distance `≥ δ` from the driver is the cut mark flow `leftMark`/`rightMark`;
* hitting times of processes killed at a random time (`killedFam`): attained, measurable, positive,
  at most the killing time; `min_hitTime_one_eq` (the hitting time capped at `1` only depends on the
  processes up to it).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

/-! ### Seed weights -/

/-- The weights of the seeds (the marks at `0`), `0` for the other marks. -/
def seedW {n : ℕ} (x ρ : Fin n → ℝ) : Fin n → ℝ := fun i => if x i = 0 then ρ i else 0

/-- The total weight of the seed group (the marks at `0`). -/
def seedSum {n : ℕ} (x ρ : Fin n → ℝ) : ℝ := ∑ i ∈ Finset.univ.filter (fun i => x i = 0), ρ i

theorem seedW_of_eq {n : ℕ} {x ρ : Fin n → ℝ} {i : Fin n} (hi : x i = 0) : seedW x ρ i = ρ i := by
  simp [seedW, hi]

theorem seedW_of_ne {n : ℕ} {x ρ : Fin n → ℝ} {i : Fin n} (hi : x i ≠ 0) : seedW x ρ i = 0 := by
  simp [seedW, hi]

/-- The seed condition: a seed `(0, xL, xR)` is not a threshold state iff both seed groups have
total weight `> −2`. -/
theorem not_thr_iff_seedSum {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) :
    ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR ↔ -2 < seedSum xL ρL ∧ -2 < seedSum xR ρR := by
  unfold ForceWord.ThresholdCondition seedSum
  rw [not_or, not_le, not_le]

/-- A weighted sum of drift integrals over a seed group, all seeds integrating the same function. -/
theorem sum_seedW_div_integral {n : ℕ} (x ρ : Fin n → ℝ) (g : Fin n → ℝ → ℝ) (g₀ : ℝ → ℝ) (t : ℝ)
    (hg : ∀ i, x i = 0 → ∫ s in (0 : ℝ)..t, (g i s)⁻¹ = ∫ s in (0 : ℝ)..t, (g₀ s)⁻¹) :
    ∑ i, ∫ s in (0 : ℝ)..t, seedW x ρ i / g i s =
      ∑ _i : Fin 1, ∫ s in (0 : ℝ)..t, seedSum x ρ / g₀ s := by
  rw [sum_integral_div_eq, Fin.sum_univ_one, integral_div_eq_mul_integral_inv, seedSum,
    Finset.sum_filter, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : x i = 0
  · simp only [seedW_of_eq hi, hg i hi, hi, ↓reduceIte]
  · simp only [seedW_of_ne hi, hi, ↓reduceIte, zero_mul]

namespace IsSLEPathUpTo

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {τ : ℝ≥0∞}

/-! ### Coincident marks -/

/-- Right marks with the same initial position coincide before the horizon. -/
theorem vR_eq_of_xR_eq (h : IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ) {j k : Fin nR}
    (hjk : xR j = xR k) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < τ) : vR j t = vR k t :=
  UpTo.vR_eq_of_eq h ht (by rw [h.vR_zero, h.vR_zero, hjk]) ⟨zero_le, le_rfl⟩

/-- Left marks with the same initial position coincide before the horizon. -/
theorem vL_eq_of_xL_eq (h : IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ) {j k : Fin nL}
    (hjk : xL j = xL k) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < τ) : vL j t = vL k t := by
  have := UpTo.vR_eq_of_eq h.reflect ht (j := j) (k := k)
    (by show -vL j 0 = -vL k 0; rw [h.vL_zero, h.vL_zero, hjk]) ⟨zero_le, le_rfl⟩
  simpa using this

/-- Real times in `[0, t]` with `t < τ` are before the horizon. -/
theorem toNNReal_lt_of_mem {t : ℝ≥0} (ht : (t : ℝ≥0∞) < τ) {s : ℝ} (hs : s ∈ uIcc (0 : ℝ) t) :
    ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < τ := by
  rw [uIcc_of_le t.coe_nonneg] at hs
  exact lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hs.2) ht

/-! ### Merging the seed groups -/

/-- **Merging the seed groups.** A local path of a word in which only the marks at `0` carry
weight (`seedW`) is, with each seed group replaced by one of its marks, a local path of the
two-seed word whose weights are the group sums (both `> −2`). -/
theorem mergeSeeds (h : IsSLEPathUpTo a xL xR (seedW xL ρL) (seedW xR ρR) w vL vR b τ)
    {pL : Fin nL} {pR : Fin nR} (hpL : xL pL = 0) (hpR : xR pR = 0)
    (hL : -2 < seedSum xL ρL) (hR : -2 < seedSum xR ρR) :
    IsSLEPathUpTo a (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0) (fun _ => seedSum xL ρL)
      (fun _ => seedSum xR ρR) w (fun _ => vL pL) (fun _ => vR pR) b τ where
  w_zero := h.w_zero
  vL_zero _ := by rw [h.vL_zero, hpL]
  vR_zero _ := by rw [h.vR_zero, hpR]
  continuousOn_w := h.continuousOn_w
  continuousOn_vL _ := h.continuousOn_vL pL
  continuousOn_vR _ := h.continuousOn_vR pR
  antitone_vL _ _ _ _ := le_rfl
  vL_le_w ht _ := h.vL_le_w ht pL
  w_le_vR ht _ := h.w_le_vR ht pR
  monotone_vR _ _ _ _ := le_rfl
  integrable_gapL ht _ := h.integrable_gapL ht pL
  integrable_gapR ht _ := h.integrable_gapR ht pR
  w_eq {t} ht := by
    rw [h.w_eq ht]
    congr 1
    · congr 1
      refine sum_seedW_div_integral xL ρL _ _ _ fun i hi => ?_
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [h.vL_eq_of_xL_eq (hi.trans hpL.symm) (toNNReal_lt_of_mem ht hs)]
    · refine sum_seedW_div_integral xR ρR _ _ _ fun i hi => ?_
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [h.vR_eq_of_xR_eq (hi.trans hpR.symm) (toNNReal_lt_of_mem ht hs)]
  vL_eq ht _ := by rw [h.vL_eq ht pL, hpL]
  vR_eq ht _ := by rw [h.vR_eq ht pR, hpR]
  volume_collisionL _ := h.volume_collisionL pL
  volume_collisionR _ := h.volume_collisionR pR
  not_threshold _ := Assembly2.not_thr_twoSeed hL hR _ _ _

/-! ### Concatenation at the horizon -/

/-- **A local path up to `σ`, continuous at `σ`, followed by a solution of Definition 2.1 from its
state at `σ`** (driven by the increments after `σ`) **is a solution of Definition 2.1** with
lifetime `σ + ζ₂`. -/
theorem isIntegratedSLEPath_concat_closed {w' : ℝ≥0 → ℝ} {vL' : Fin nL → ℝ≥0 → ℝ}
    {vR' : Fin nR → ℝ≥0 → ℝ} {b' : ℝ≥0 → ℝ} {ζ₂ : ℝ≥0∞} {σ : ℝ≥0}
    (h₁ : IsSLEPathUpTo a xL xR ρL ρR w vL vR b σ) (hσ0 : 0 < σ)
    (hc : ContinuousAt (fun t => (w t, fun i => vL i t, fun j => vR j t)) σ)
    (hb : ContinuousAt b σ)
    (h₂ : IsIntegratedSLEPath a (fun i => vL i σ - w σ) (fun j => vR j σ - w σ) ρL ρR w' vL' vR'
      b' ζ₂) (hb' : ∀ t, b' t = b (σ + t) - b σ) :
    IsIntegratedSLEPath a xL xR ρL ρR (concatAt σ w (w σ) w')
      (fun i => concatAt σ (vL i) (w σ) (vL' i)) (fun j => concatAt σ (vR j) (w σ) (vR' j)) b
      ((σ : ℝ≥0∞) + ζ₂) := by
  have hU := h₁.concat_of_tendsto (w₀ := w σ) (vL₀ := fun i => vL i σ) (vR₀ := fun j => vR j σ)
    hσ0 hb (hc.tendsto.mono_left nhdsWithin_le_nhds) (h₂.isSLEPathUpTo le_rfl) hb'
  have hp₂ := h₂.isForcePath
  refine ⟨hU.w_zero, hU.vL_zero, hU.vR_zero, hU.continuousOn_w, hU.continuousOn_vL,
    hU.continuousOn_vR, fun t ht => hU.antitone_vL ht, fun t ht => hU.vL_le_w ht,
    fun t ht => hU.w_le_vR ht, fun t ht => hU.monotone_vR ht, fun t ht => hU.integrable_gapL ht,
    fun t ht => hU.integrable_gapR ht, fun t ht => hU.w_eq ht, fun t ht => hU.vL_eq ht,
    fun t ht => hU.vR_eq ht, hU.volume_collisionL, hU.volume_collisionR,
    fun t ht => hU.not_threshold ht, fun h0 => ?_, fun T hT0 hT w₀ vL₀ vR₀ hlim => ?_⟩
  · have : (σ : ℝ≥0∞) = 0 := le_antisymm (h0 ▸ le_self_add) bot_le
    exact absurd (show σ = 0 by exact_mod_cast this) hσ0.ne'
  · have hσT : σ ≤ T := by
      have : (σ : ℝ≥0∞) ≤ T := by rw [hT]; exact le_self_add
      exact_mod_cast this
    have hζ₂ : ζ₂ = ((T - σ : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.coe_sub, hT, ENNReal.add_sub_cancel_left ENNReal.coe_ne_top]
    rcases eq_or_lt_of_le hσT with hTσ | hTσ
    · -- the second piece has lifetime `0`: the limit is the state at `σ`
      subst hTσ
      have hz : ζ₂ = 0 := by rw [hζ₂, tsub_self]; rfl
      have hthr := hp₂.threshold_of_eq_zero hz
      have : NeBot (𝓝[<] σ) := nhdsLT_neBot_of_exists_lt ⟨0, hσ0⟩
      have hlim' : Tendsto (fun t => (w t, fun i => vL i t, fun j => vR j t)) (𝓝[<] σ)
          (𝓝 (w₀, vL₀, vR₀)) := by
        refine hlim.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        have ht' : t < σ := ht
        simp only [concatAt_of_lt ht']
      have e := tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds) hlim'
      simp only [Prod.mk.injEq] at e
      obtain ⟨e1, e2, e3⟩ := e
      rw [← e1, ← e2, ← e3]
      have := (Assembly2.thr_sub_iff (ρL := ρL) (ρR := ρR) (w σ) (w σ) (fun i => vL i σ)
        (fun j => vR j σ)).1
      rw [sub_self] at this
      exact this hthr
    · -- the limit at the end of the second piece
      set T₂ := T - σ with hT₂
      have hT₂0 : 0 < T₂ := tsub_pos_of_lt hTσ
      have hshift : Tendsto (fun s : ℝ≥0 => σ + s) (𝓝[<] T₂) (𝓝[<] T) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
        · have : T = σ + T₂ := by rw [hT₂, add_tsub_cancel_of_le hσT]
          rw [this]
          exact (((continuous_const (y := σ)).add continuous_id).tendsto T₂).mono_left
            nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with s hs
          have hs' : s < T₂ := hs
          show σ + s < T
          calc σ + s < σ + T₂ := add_lt_add_right hs' σ
            _ = T := by rw [hT₂, add_tsub_cancel_of_le hσT]
      set c : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) := (w σ, fun _ => w σ, fun _ => w σ) with hcdef
      have hc' := ((continuous_id.sub (continuous_const (y := c))).tendsto
        ((w₀, vL₀, vR₀) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))).comp (hlim.comp hshift)
      have h1 : ∀ (f g : ℝ≥0 → ℝ) (s : ℝ≥0), concatAt σ f (w σ) g (σ + s) = w σ + g s :=
        fun f g s => by rw [concatAt_of_le le_self_add, add_tsub_cancel_left]
      have hlim₂ : Tendsto (fun s => (w' s, fun i => vL' i s, fun j => vR' j s)) (𝓝[<] T₂)
          (𝓝 ((w₀, vL₀, vR₀) - c)) := by
        refine hc'.congr fun s => ?_
        simp only [Function.comp_apply, id, Pi.sub_apply, h1, hcdef, Prod.mk_sub_mk]
        refine Prod.ext (by ring) (Prod.ext (funext fun i => by simp) (funext fun j => by simp))
      have := hp₂.threshold_of_tendsto hT₂0 hζ₂.symm hlim₂
      exact (Assembly2.thr_sub_iff (ρL := ρL) (ρR := ρR) w₀ (w σ) vL₀ vR₀).1 this

end IsSLEPathUpTo

namespace Assembly3

open Assembly Assembly2

/-! ### Uniqueness for the mark equation -/

/-- **Uniqueness for a Lipschitz mark equation** `u = y + ∫₀ᵗ F(u − w)` on `[0, t₁]`. -/
theorem eq_of_markEq {F : ℝ → ℝ} {K : ℝ≥0} (hF : LipschitzWith K F) {w u₁ u₂ : ℝ≥0 → ℝ} {y : ℝ}
    {t₁ : ℝ≥0} (hw : ContinuousOn w (Iic t₁)) (hu₁ : ContinuousOn u₁ (Iic t₁))
    (hu₂ : ContinuousOn u₂ (Iic t₁))
    (h₁ : ∀ t ≤ t₁, u₁ t = y + ∫ s in (0 : ℝ)..t, F (u₁ s.toNNReal - w s.toNNReal))
    (h₂ : ∀ t ≤ t₁, u₂ t = y + ∫ s in (0 : ℝ)..t, F (u₂ s.toNNReal - w s.toNNReal))
    {t : ℝ≥0} (ht : t ≤ t₁) : u₁ t = u₂ t := by
  have hmaps : MapsTo (fun s : ℝ => s.toNNReal) (Icc (0 : ℝ) t₁) (Iic t₁) := fun s hs =>
    Real.toNNReal_le_iff_le_coe.2 hs.2
  have hc : ∀ {u : ℝ≥0 → ℝ}, ContinuousOn u (Iic t₁) →
      ContinuousOn (fun s : ℝ => u s.toNNReal) (Icc 0 t₁) := fun hu =>
    hu.comp continuous_real_toNNReal.continuousOn hmaps
  have hφ : ∀ {u : ℝ≥0 → ℝ}, ContinuousOn u (Iic t₁) →
      ContinuousOn (fun s : ℝ => F (u s.toNNReal - w s.toNNReal)) (Icc 0 t₁) := fun hu =>
    hF.continuous.comp_continuousOn ((hc hu).sub (hc hw))
  have hii : ∀ {u : ℝ≥0 → ℝ}, ContinuousOn u (Iic t₁) → ∀ s ∈ Icc (0 : ℝ) t₁,
      IntervalIntegrable (fun r : ℝ => F (u r.toNNReal - w r.toNNReal)) volume 0 s :=
    fun hu s hs => ((hφ hu).mono (by rw [uIcc_of_le hs.1]; exact Icc_subset_Icc le_rfl hs.2)
      ).intervalIntegrable
  set g : ℝ → ℝ := fun s => |u₁ s.toNNReal - u₂ s.toNNReal| with hgdef
  have hgc : ContinuousOn g (Icc 0 t₁) := ((hc hu₁).sub (hc hu₂)).abs
  have key := Assembly.eq_zero_of_le_mul_integral (g := g) (K := K) (t₀ := 0) (t₁ := t₁)
    (fun s _ => abs_nonneg _) hgc fun s hs => ?_
  · have := key t ⟨t.coe_nonneg, by exact_mod_cast ht⟩
    simp only [hgdef, Real.toNNReal_coe, abs_eq_zero, sub_eq_zero] at this
    exact this
  · have hs' : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal s hs.1
    have hst : s.toNNReal ≤ t₁ := hmaps hs
    have e : u₁ s.toNNReal - u₂ s.toNNReal = ∫ r in (0 : ℝ)..s,
        (F (u₁ r.toNNReal - w r.toNNReal) - F (u₂ r.toNNReal - w r.toNNReal)) := by
      rw [intervalIntegral.integral_sub (hii hu₁ s hs) (hii hu₂ s hs), h₁ _ hst, h₂ _ hst, hs']
      ring
    show |u₁ s.toNNReal - u₂ s.toNNReal| ≤ K * ∫ r in (0 : ℝ)..s, g r
    rw [e, ← intervalIntegral.integral_const_mul]
    refine (intervalIntegral.abs_integral_le_integral_abs hs.1).trans ?_
    refine intervalIntegral.integral_mono_on hs.1 ((hii hu₁ s hs).sub (hii hu₂ s hs)).abs ?_ ?_
    · exact ((hgc.mono (Icc_subset_Icc le_rfl hs.2)).const_smul (K : ℝ)).intervalIntegrable_of_Icc
        hs.1
    · intro r _
      have := hF.dist_le_mul (u₁ r.toNNReal - w r.toNNReal) (u₂ r.toNNReal - w r.toNNReal)
      rw [Real.dist_eq, Real.dist_eq] at this
      simpa only [hgdef, sub_sub_sub_cancel_right] using this

/-- **A mark at distance `≥ δ` left of a continuous driver is the cut mark flow** `leftMark δ`. -/
theorem eq_leftMark {Ω : Type*} {Wg : ℝ≥0 → Ω → ℝ} {ω : Ω} (hWg : Continuous (Wg · ω)) {δ y : ℝ}
    (hδ : 0 < δ) {v : ℝ≥0 → ℝ} {t₁ : ℝ≥0} (hv : ContinuousOn v (Iic t₁))
    (hveq : ∀ t ≤ t₁, v t = y + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - Wg s.toNNReal ω))
    (hgap : ∀ t ≤ t₁, δ ≤ Wg t ω - v t) {t : ℝ≥0} (ht : t ≤ t₁) :
    v t = leftMark δ y (fun _ => ⊤) Wg t ω := by
  obtain ⟨hmc, hmeq⟩ := markFlow_eq_of_continuousOn (ζ := fun _ => ⊤) (y := y) (ω := ω)
    (lipschitzWith_leftMarkDrift hδ) (abs_leftMarkDrift_le hδ) hWg.continuousOn
  refine eq_of_markEq (lipschitzWith_leftMarkDrift hδ) (w := fun s => Wg s ω)
    hWg.continuousOn hv (hmc.mono fun s _ => ENNReal.coe_lt_top) (fun s hs => ?_)
    (fun s _ => hmeq s ENNReal.coe_lt_top) ht
  rw [hveq s hs]
  congr 1
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le s.coe_nonneg] at hr
  have hrs : r.toNNReal ≤ t₁ := (Real.toNNReal_le_iff_le_coe.2 hr.2).trans hs
  exact (leftMarkDrift_of_le (by linarith [hgap _ hrs])).symm

/-- **A mark at distance `≥ δ` right of a continuous driver is the cut mark flow** `rightMark δ`. -/
theorem eq_rightMark {Ω : Type*} {Wg : ℝ≥0 → Ω → ℝ} {ω : Ω} (hWg : Continuous (Wg · ω)) {δ y : ℝ}
    (hδ : 0 < δ) {v : ℝ≥0 → ℝ} {t₁ : ℝ≥0} (hv : ContinuousOn v (Iic t₁))
    (hveq : ∀ t ≤ t₁, v t = y + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - Wg s.toNNReal ω))
    (hgap : ∀ t ≤ t₁, δ ≤ v t - Wg t ω) {t : ℝ≥0} (ht : t ≤ t₁) :
    v t = rightMark δ y (fun _ => ⊤) Wg t ω := by
  obtain ⟨hmc, hmeq⟩ := markFlow_eq_of_continuousOn (ζ := fun _ => ⊤) (y := y) (ω := ω)
    (lipschitzWith_rightMarkDrift hδ) (abs_rightMarkDrift_le hδ) hWg.continuousOn
  refine eq_of_markEq (lipschitzWith_rightMarkDrift hδ) (w := fun s => Wg s ω)
    hWg.continuousOn hv (hmc.mono fun s _ => ENNReal.coe_lt_top) (fun s hs => ?_)
    (fun s _ => hmeq s ENNReal.coe_lt_top) ht
  rw [hveq s hs]
  congr 1
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le s.coe_nonneg] at hr
  have hrs : r.toNNReal ≤ t₁ := (Real.toNNReal_le_iff_le_coe.2 hr.2).trans hs
  exact (rightMarkDrift_of_le (hgap _ hrs)).symm

/-! ### Hitting times of killed processes -/

section Hit

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {K : Type*} {Y : K → ℝ≥0 → Ω → ℝ} {δ : ℝ}

/-- The hitting time is attained when the hitting set is closed. -/
theorem hitTime_le_iff_of_isClosed {ω : Ω} (hcl : IsClosed {t : ℝ≥0 | ∃ k, Y k t ω ≤ δ})
    {s : ℝ≥0} : hitTime Y δ ω ≤ s ↔ ∃ t ≤ s, ∃ k, Y k t ω ≤ δ := by
  set S := {t : ℝ≥0 | ∃ k, Y k t ω ≤ δ} with hS
  constructor
  · intro h
    have hne : S.Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      have htop : hitTime Y δ ω = ⊤ := by
        refine le_antisymm le_top (le_iInf₂ fun t ht => ?_)
        exact absurd (show t ∈ S from ht) (by rw [hne]; exact notMem_empty t)
      rw [htop] at h
      exact absurd h (not_le.2 ENNReal.coe_lt_top)
    have hmem := hcl.csInf_mem hne (OrderBot.bddBelow S)
    have hle : ((sInf S : ℝ≥0) : ℝ≥0∞) ≤ hitTime Y δ ω :=
      le_iInf₂ fun t ht => ENNReal.coe_le_coe.2 (csInf_le (OrderBot.bddBelow S) ht)
    exact ⟨sInf S, by exact_mod_cast hle.trans h, hmem⟩
  · rintro ⟨t, hts, k, hk⟩
    exact (iInf₂_le (f := fun (t : ℝ≥0) (_ : ∃ k, Y k t ω ≤ δ) => (t : ℝ≥0∞)) t ⟨k, hk⟩).trans
      (by exact_mod_cast hts)

/-- The family `Y` killed at `ζ`. -/
def killedFam (ζ : Ω → ℝ≥0∞) (Y : K → ℝ≥0 → Ω → ℝ) : K → ℝ≥0 → Ω → ℝ :=
  fun k => Girsanov.killed ζ (Y k)

variable {ζ : Ω → ℝ≥0∞}

/-- The hitting set of a killed family is closed (the processes being continuous before `ζ`). -/
theorem isClosed_killedFam [Finite K] [Nonempty K] (hδ : 0 ≤ δ) {ω : Ω}
    (hc : ∀ k, ContinuousOn (Y k · ω) {t | (t : ℝ≥0∞) < ζ ω}) :
    IsClosed {t : ℝ≥0 | ∃ k, killedFam ζ Y k t ω ≤ δ} := by
  have hU : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := isOpen_lt ENNReal.continuous_coe continuous_const
  have e : {t : ℝ≥0 | ∃ k, killedFam ζ Y k t ω ≤ δ}ᶜ =
      ⋂ k, ({t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} ∩ (Y k · ω) ⁻¹' Ioi δ) := by
    ext t
    simp only [mem_compl_iff, mem_ofPred_eq, not_exists, not_le, mem_iInter, mem_inter_iff,
      mem_preimage, mem_Ioi]
    constructor
    · intro h k
      by_cases ht : (t : ℝ≥0∞) < ζ ω
      · refine ⟨ht, ?_⟩
        have := h k
        rwa [killedFam, Girsanov.killed_of_lt ht] at this
      · have := h k
        simp only [killedFam, Girsanov.killed, ht, ↓reduceIte] at this
        exact absurd this (not_lt.2 hδ)
    · intro h k
      rw [killedFam, Girsanov.killed_of_lt (h k).1]
      exact (h k).2
  rw [← isOpen_compl_iff, e]
  exact isOpen_iInter_of_finite fun k => (hc k).isOpen_inter_preimage hU isOpen_Ioi

/-- The hitting time of a killed family is at most the killing time. -/
theorem hitTime_killedFam_le [Nonempty K] (hδ : 0 ≤ δ) (ω : Ω) :
    hitTime (killedFam ζ Y) δ ω ≤ ζ ω := by
  rcases eq_or_ne (ζ ω) ⊤ with h | h
  · rw [h]; exact le_top
  · have k : K := Classical.arbitrary K
    have ht : ¬ (((ζ ω).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω := by
      rw [ENNReal.coe_toNNReal h]; exact lt_irrefl _
    refine (iInf₂_le (f := fun (t : ℝ≥0) (_ : ∃ k, killedFam ζ Y k t ω ≤ δ) => (t : ℝ≥0∞))
      (ζ ω).toNNReal ⟨k, ?_⟩).trans (ENNReal.coe_toNNReal h).le
    simp only [killedFam, Girsanov.killed, ht, ↓reduceIte]
    exact hδ

/-- Positivity of the hitting time of a killed family. -/
theorem hitTime_killedFam_pos [Finite K] [Nonempty K] (hδ : 0 ≤ δ) {ω : Ω}
    (hc : ∀ k, ContinuousOn (Y k · ω) {t | (t : ℝ≥0∞) < ζ ω}) (hζ : 0 < ζ ω)
    (h0 : ∀ k, δ < Y k 0 ω) : 0 < hitTime (killedFam ζ Y) δ ω := by
  rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0∞) ≤ hitTime (killedFam ζ Y) δ ω) with h | h
  · obtain ⟨t, ht, k, hk⟩ := (hitTime_le_iff_of_isClosed (s := 0) (isClosed_killedFam hδ hc)).1
      (by rw [← h]; rfl)
    rw [nonpos_iff_eq_zero.1 ht, killedFam, Girsanov.killed_of_lt (by simpa using hζ)] at hk
    exact absurd hk (not_le.2 (h0 k))
  · exact h

/-- Before the hitting time of a killed family, the processes are alive and above `δ`. -/
theorem lt_of_lt_hitTime_killedFam [Nonempty K] (hδ : 0 ≤ δ) {ω : Ω} {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < hitTime (killedFam ζ Y) δ ω) : (t : ℝ≥0∞) < ζ ω ∧ ∀ k, δ < Y k t ω := by
  have hk := lt_of_lt_hitTime ht
  have hζ : (t : ℝ≥0∞) < ζ ω := by
    by_contra hn
    have := hk (Classical.arbitrary K)
    simp only [killedFam, Girsanov.killed, hn, ↓reduceIte] at this
    exact absurd hδ (not_le.2 this)
  refine ⟨hζ, fun k => ?_⟩
  have := hk k
  rwa [killedFam, Girsanov.killed_of_lt hζ] at this

/-- **The hitting time of a killed family is a stopping time.** -/
theorem measurableSet_hitTime_killedFam_le [Finite K] [Nonempty K] {𝓕 : Filtration ℝ≥0 mΩ}
    (hδ : 0 ≤ δ) (hY : ∀ k, AdaptedBefore 𝓕 ζ (Y k))
    (hc : ∀ k ω, ContinuousOn (Y k · ω) {t | (t : ℝ≥0∞) < ζ ω}) (s : ℝ≥0) :
    MeasurableSet[𝓕 s] {ω | hitTime (killedFam ζ Y) δ ω ≤ s} := by
  classical
  set Z : K → ℝ → Ω → ℝ := fun k r ω =>
    if (s : ℝ≥0∞) < ζ ω then killedFam ζ Y k r.toNNReal ω else δ + 1 with hZ
  have hζs : MeasurableSet[𝓕 s] {ω | (s : ℝ≥0∞) < ζ ω} := by
    simpa using hY (Classical.arbitrary K) s univ MeasurableSet.univ
  have e : {ω | hitTime (killedFam ζ Y) δ ω ≤ s} =
      ({ω | (s : ℝ≥0∞) < ζ ω} ∩ ⋂ k, {ω | ∀ r ∈ Icc (0 : ℝ) s, δ < Z k r ω})ᶜ := by
    ext ω
    rw [mem_ofPred_eq, hitTime_le_iff_of_isClosed (isClosed_killedFam hδ (hc · ω))]
    simp only [mem_compl_iff, mem_inter_iff, mem_ofPred_eq, mem_iInter]
    constructor
    · rintro ⟨t, hts, k, hk⟩ ⟨hs, h⟩
      have := h k t ⟨t.coe_nonneg, by exact_mod_cast hts⟩
      simp only [hZ, hs, ↓reduceIte, Real.toNNReal_coe] at this
      exact absurd hk (not_le.2 this)
    · intro h
      by_cases hs : (s : ℝ≥0∞) < ζ ω
      · have : ¬ ∀ k, ∀ r ∈ Icc (0 : ℝ) s, δ < Z k r ω := fun h' => h ⟨hs, h'⟩
        simp only [not_forall, not_lt] at this
        obtain ⟨k, r, hr, hk⟩ := this
        simp only [hZ, hs, ↓reduceIte] at hk
        exact ⟨r.toNNReal, Real.toNNReal_le_iff_le_coe.2 hr.2, k, hk⟩
      · have hfin : ζ ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top (not_lt.1 hs)
        have hn : ¬ (((ζ ω).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω := by
          rw [ENNReal.coe_toNNReal hfin]; exact lt_irrefl _
        refine ⟨(ζ ω).toNNReal, ?_, Classical.arbitrary K, ?_⟩
        · have : (((ζ ω).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ s := by
            rw [ENNReal.coe_toNNReal hfin]; exact not_lt.1 hs
          exact_mod_cast this
        · simp only [killedFam, Girsanov.killed, hn, ↓reduceIte]
          exact hδ
  rw [e]
  refine (hζs.inter (MeasurableSet.iInter fun k => ?_)).compl
  refine OneForce.measurableSet_forall_Icc_lt (mα := 𝓕 s) s.coe_nonneg (fun r hr => ?_)
    (fun ω => ?_) δ
  · refine Measurable.ite hζs ?_ measurable_const
    refine (Girsanov.measurable_killed (hY k) r.toNNReal).mono (𝓕.mono ?_) le_rfl
    exact Real.toNNReal_le_iff_le_coe.2 hr.2
  · by_cases hs : (s : ℝ≥0∞) < ζ ω
    · have hmaps : MapsTo (fun r : ℝ => r.toNNReal) (Icc (0 : ℝ) s)
          {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun r hr =>
        lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hr.2) hs
      refine ((hc k ω).comp continuous_real_toNNReal.continuousOn hmaps).congr fun r hr => ?_
      simp only [hZ, hs, ↓reduceIte, Function.comp_apply, killedFam]
      exact Girsanov.killed_of_lt (hmaps hr)
    · simp only [hZ, hs, ↓reduceIte]
      exact continuousOn_const

/-- **The hitting time capped at `1` only depends on the processes up to it.** If `Y` and `Y'`
agree up to `min (hitTime Y δ) 1` and the hitting set of `Y` is closed, the
capped hitting times agree. -/
theorem min_hitTime_one_eq {Ω' : Type*} {Y' : K → ℝ≥0 → Ω' → ℝ} {ω : Ω} {ω' : Ω'}
    (hcl : IsClosed {t : ℝ≥0 | ∃ k, Y k t ω ≤ δ})
    (heq : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ min (hitTime Y δ ω) 1 → ∀ k, Y' k t ω' = Y k t ω) :
    min (hitTime Y' δ ω') 1 = min (hitTime Y δ ω) 1 := by
  refine le_antisymm ?_ ?_
  · rcases lt_or_ge (hitTime Y δ ω) 1 with h | h
    · have hfin : hitTime Y δ ω ≠ ⊤ := (lt_of_lt_of_le h le_top).ne
      obtain ⟨t, ht, k, hk⟩ := (hitTime_le_iff_of_isClosed hcl).1
        (ENNReal.coe_toNNReal hfin).ge
      have ht' : (t : ℝ≥0∞) ≤ hitTime Y δ ω := by
        rw [← ENNReal.coe_toNNReal hfin]; exact_mod_cast ht
      have hY' : Y' k t ω' ≤ δ := by
        rw [heq t (le_min ht' (ht'.trans h.le)) k]; exact hk
      refine min_le_of_left_le ((iInf₂_le (f := fun (t : ℝ≥0) (_ : ∃ k, Y' k t ω' ≤ δ) =>
        (t : ℝ≥0∞)) t ⟨k, hY'⟩).trans ?_)
      exact ht'.trans (le_min le_rfl h.le)
    · exact (min_le_right _ _).trans (le_min h le_rfl)
  · refine le_min ?_ (min_le_right _ _)
    refine le_iInf₂ fun t ⟨k, hk⟩ => ?_
    by_contra hlt
    rw [not_le] at hlt
    have h1 : (t : ℝ≥0∞) < hitTime Y δ ω := lt_of_lt_of_le hlt (min_le_left _ _)
    have := lt_of_lt_hitTime h1 k
    rw [← heq t hlt.le k] at this
    exact absurd hk (not_le.2 this)

end Hit

end Assembly3

end Sec2

end InteractingSLE
