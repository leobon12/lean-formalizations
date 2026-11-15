/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.TrialsHi4Osc
import InteractingSLE.Spec.Sec7.TrialsHi3Assembly

/-!
# The reference success event at critical or singleton weights

Packet PROVE-TRIALS-HI4. Specification §7.3, Aux. lemma 111 ("Both totals are at least `c` … Aux. lemma 7 supplies a
continuous transient trace whose two marks are never swallowed … Choose deterministic `δ > 0` such that this distance
exceeds `4δ` with positive probability"; "A sole right mark is allowed to continue … The left mark never collides").
For the four-mark reference word `(−1, −M; 1, M)` with weights `(s_L, 0; s_R, 0)`, `s_L ≥ κ/2 − 2`, `s_R > −2`:

* the lifetime is infinite (`ae_lifetime_eq_top_ref`; both weights exceed `−2`);
* a side with weight `≥ κ/2 − 2` never collides (`ae_w_lt_vR_ref`, `ae_vL_lt_w_ref`, the one-sided Aux. lemma 6,
  which allows every admissible collision of the other side);
* the trace is quantitatively transient with probability close to one (`exists_qTrans_codeLaw_le'`, from the
  completeness of the two-mark word);
* **the reference success event has positive probability** (`refPos`): steer the driver along a slow line
  (`TrialsHi3.exists_steer_bound`, `steer_det`) until the left and right spreads are small against the nearest
  gaps, then apply the critical-oscillation bound `measure_critBad_le` on each side with weight `≥ κ/2 − 2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace TrialsHi4

open ZhanGT4 Zhan Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart TrialsHi TrialsHi2 TrialsHi3 Clock

variable {κ M sL sR : ℝ}

/-! ### The reference word -/

theorem neg_refXR (M : ℝ) : -refXR M = refXL M := by
  funext i; rcases fin_two_cases i with rfl | rfl <;> simp [refXL, refXR]

theorem neg_refXL (M : ℝ) : -refXL M = refXR M := by
  funext i; rcases fin_two_cases i with rfl | rfl <;> simp [refXL, refXR]

theorem refXL_le (hM : 1 ≤ M) : ∀ i, refXL M i ≤ -1 := fun i => by
  rcases fin_two_cases i with rfl | rfl
  · simp [refXL]
  · simp only [refXL, Matrix.cons_val_one, Matrix.cons_val_fin_one]; linarith

theorem refXR_mem (hM : 1 ≤ M) : ∀ j, 1 ≤ refXR M j ∧ refXR M j ≤ M := fun j => by
  rcases fin_two_cases j with rfl | rfl
  · simp only [refXR, Matrix.cons_val_zero]; exact ⟨le_rfl, hM⟩
  · simp only [refXR, Matrix.cons_val_one, Matrix.cons_val_fin_one]; exact ⟨hM, le_rfl⟩

theorem hasGroupEndSums_ref {c s : ℝ} (h : c ≤ s) (x : Fin 2 → ℝ) : Sec4.HasGroupEndSums c ![s, 0] x := by
  intro j _
  rcases fin_two_cases j with rfl | rfl
  · have e : (Finset.univ.filter fun i : Fin 2 => i ≤ 0) = {0} := by decide
    rw [e, Finset.sum_singleton]; simpa using h
  · have e : (Finset.univ.filter fun i : Fin 2 => i ≤ 1) = Finset.univ := by decide
    rw [e, Fin.sum_univ_two]; simpa using h

section Ev

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL VR : Fin 2 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The lifetime of the reference word is infinite** when both nearest weights exceed `−2` (no group of marks
can reach a continuation threshold). -/
theorem ae_lifetime_eq_top_ref (hsL : -2 < sL) (hsR : -2 < sR) (hM : 1 ≤ M)
    (hE : IsIntegratedSLEEvolution κ (refXL M) (refXR M) ![sL, 0] ![sR, 0] P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ := by
  set c := min sL sR with hcdef
  have hc : (-2 : ℝ) < c := lt_min hsL hsR
  have hL : Sec4.HasGroupEndSums c ![sL, 0] (-refXL M) := hasGroupEndSums_ref (min_le_left _ _) _
  have hR : Sec4.HasGroupEndSums c ![sR, 0] (refXR M) := hasGroupEndSums_ref (min_le_right _ _) _
  obtain ⟨hxL, hxL0, hxR, hxR0⟩ := isOrderedForceWord_ref hM
  have hsL' := (Sec4.neg_two_lt_sum_of_hasGroupEndSums hc hL).ne'
  have hsR' := (Sec4.neg_two_lt_sum_of_hasGroupEndSums hc hR).ne'
  filter_upwards [hE.ae_tendsto_threshold_of_ne hsL' hsR', hE.ae_isIntegratedSLEPath] with ω hlim hp
  by_contra hne
  obtain ⟨T, hT⟩ : ∃ T : ℝ≥0, (T : ℝ≥0∞) = ζ ω := ⟨(ζ ω).toNNReal, ENNReal.coe_toNNReal hne⟩
  have hfp := hp.isForcePath
  rcases eq_zero_or_pos T with hT0 | hT0
  · have h0 : ζ ω = 0 := by rw [← hT, hT0, ENNReal.coe_zero]
    exact Sec4.not_thresholdCondition_of_hasGroupEndSums hc hxL hxR hL hR hxL hxR hxL0 hxR0
      (fun _ _ h => h) (fun _ _ h => h) (hfp.threshold_of_eq_zero h0)
  · obtain ⟨w₀, vL₀, vR₀, hlim', hth⟩ := hlim T hT0 hT
    have : NeBot (𝓝[<] T) := nhdsLT_neBot_of_exists_lt ⟨0, hT0⟩
    have hev : ∀ᶠ t : ℝ≥0 in 𝓝[<] T, (t : ℝ≥0∞) < ζ ω := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [← hT]; exact_mod_cast ht
    have hw : Tendsto (fun t => W t ω) (𝓝[<] T) (𝓝 w₀) := hlim'.fst_nhds
    have hvL : ∀ i, Tendsto (fun t => VL i t ω) (𝓝[<] T) (𝓝 (vL₀ i)) := fun i =>
      tendsto_pi_nhds.1 hlim'.snd_nhds.fst_nhds i
    have hvR : ∀ i, Tendsto (fun t => VR i t ω) (𝓝[<] T) (𝓝 (vR₀ i)) := fun i =>
      tendsto_pi_nhds.1 hlim'.snd_nhds.snd_nhds i
    refine Sec4.not_thresholdCondition_of_hasGroupEndSums hc hxL hxR hL hR ?_ ?_ ?_ ?_ ?_ ?_ hth
    · intro i j hij
      exact le_of_tendsto_of_tendsto (hvL j) (hvL i) (hev.mono fun t ht => hfp.antitone_vL ht hij)
    · intro i j hij
      exact le_of_tendsto_of_tendsto (hvR i) (hvR j) (hev.mono fun t ht => hfp.monotone_vR ht hij)
    · intro i
      exact le_of_tendsto_of_tendsto (hvL i) hw (hev.mono fun t ht => hfp.vL_le_w ht i)
    · intro i
      exact le_of_tendsto_of_tendsto hw (hvR i) (hev.mono fun t ht => hfp.w_le_vR ht i)
    · intro i j hij
      exact tendsto_nhds_unique (hvL i)
        ((hvL j).congr' (hev.mono fun t ht => (hp.vL_eq_of_xL_eq ht hij).symm))
    · intro i j hij
      exact tendsto_nhds_unique (hvR i)
        ((hvR j).congr' (hev.mono fun t ht => (hp.vR_eq_of_xR_eq ht hij).symm))

/-- **The nearest right mark of weight `≥ κ/2 − 2` is never hit** (one-sided Aux. lemma 6; the left side may
collide). -/
theorem ae_w_lt_vR_ref (hκ : 0 < κ) (hsR : κ / 2 - 2 ≤ sR) (hM : 1 ≤ M)
    (hE : IsIntegratedSLEEvolution κ (refXL M) (refXR M) ![sL, 0] ![sR, 0] P 𝓕 W VL VR B ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) : ∀ᵐ ω ∂P, ∀ t, W t ω < VR 0 t ω := by
  have h := hE.ae_w_lt_vR hκ (isOrderedForceWord_ref hM) (hasGroupEndSums_ref hsR _) hζ (by norm_num)
  filter_upwards [h, hE.ae_isIntegratedSLEPath] with ω hω hp t
  rcases (zero_le (a := t)).eq_or_lt with ht | ht
  · subst ht
    have hF := hp.isForcePath
    rw [hF.w_zero, hF.vR_zero]
    simp [refXR]
  · exact hω t ht

/-- The reflected evolution of the reference word is an evolution of the reference word. -/
theorem reflect_ref (hE : IsIntegratedSLEEvolution κ (refXL M) (refXR M) ![sL, 0] ![sR, 0] P 𝓕 W VL VR B ζ) :
    IsIntegratedSLEEvolution κ (refXL M) (refXR M) ![sR, 0] ![sL, 0] P 𝓕 (-W) (fun i => -VR i) (fun i => -VL i)
      (-B) ζ := by
  have h := hE.reflect
  rwa [neg_refXR, neg_refXL] at h

/-- **The nearest left mark of weight `≥ κ/2 − 2` is never hit.** -/
theorem ae_vL_lt_w_ref (hκ : 0 < κ) (hsL : κ / 2 - 2 ≤ sL) (hM : 1 ≤ M)
    (hE : IsIntegratedSLEEvolution κ (refXL M) (refXR M) ![sL, 0] ![sR, 0] P 𝓕 W VL VR B ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) : ∀ᵐ ω ∂P, ∀ t, VL 0 t ω < W t ω := by
  filter_upwards [ae_w_lt_vR_ref hκ hsL hM (reflect_ref hE) hζ] with ω h t
  have := h t
  simp only [Pi.neg_apply, neg_lt_neg_iff] at this
  exact this

end Ev

/-! ### Quantitative transience -/

/-- **Quantitative transience of the reference word in law**: under the smaller-count hypothesis at `N = 3`, for
every `ε > 0` there is `K` with `codeLaw(not QTrans K) ≤ ε` (both nearest weights exceed `−2`). -/
theorem exists_qTrans_codeLaw_le' (hκ : 0 < κ) (hD3 : LP.DistinctCompleteBelow.{u} κ 3) (hsL : -2 < sL)
    (hsR : -2 < sR) (hM : 1 ≤ M) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ → ℕ, codeLaw κ ![sL, 0] ![sR, 0] {x | QTrans K (cw x) (cζ x)}ᶜ (refXL M, refXR M) ≤
      ENNReal.ofReal ε := by
  obtain ⟨Ω', mΩ', P', hP', 𝓕', W', VL', VR', B', ζ', hE'⟩ :=
    LP.exists_isIntegratedSLEEvolution_ulift.{u} hκ (isOrderedForceWord_ref hM) (ρL := ![sL, 0])
      (ρR := ![sR, 0])
  -- the two-mark subword is complete
  have hrange : ∀ i : Fin 2, i ∉ Set.range (Fin.castSuccOrderEmb (n := 1)) → i ≠ 0 := fun i hi h0 =>
    hi ⟨0, by rw [h0]; rfl⟩
  have hsub := hE'.compEmb (Fin.castSuccOrderEmb (n := 1)) (Fin.castSuccOrderEmb (n := 1))
    (fun i hi => weights_ref sL i (hrange i hi)) (fun i hi => weights_ref sR i (hrange i hi))
  have hdist : LP.IsDistinctForceWord (fun j => refXL M (Fin.castSuccOrderEmb (n := 1) j))
      (fun j => refXR M (Fin.castSuccOrderEmb (n := 1) j)) := by
    refine ⟨⟨fun i j _ => ?_, fun i => ?_, fun i j _ => ?_, fun i => ?_⟩, fun i j hij => ?_, fun i j hij => ?_⟩
    · rw [Subsingleton.elim i j]
    · rw [Fin.fin_one_eq_zero i]; show refXL M 0 ≤ 0; simp [refXL]
    · rw [Subsingleton.elim i j]
    · rw [Fin.fin_one_eq_zero i]; show 0 ≤ refXR M 0; simp [refXR]
    · exact absurd hij (by rw [Subsingleton.elim i j]; exact lt_irrefl _)
    · exact absurd hij (by rw [Subsingleton.elim i j]; exact lt_irrefl _)
  have htr := hD3 _ _ (fun j => (![sL, 0] : Fin 2 → ℝ) (Fin.castSuccOrderEmb (n := 1) j))
    (fun j => (![sR, 0] : Fin 2 → ℝ) (Fin.castSuccOrderEmb (n := 1) j)) hdist (by norm_num) P' 𝓕' W' _ _ B' ζ'
    hsub
  have hζ := ae_lifetime_eq_top_ref hsL hsR hM hE'
  -- for each radius, the late-return probability tends to `0`
  have hlim : ∀ R : ℕ, Tendsto (fun k => codeLaw κ ![sL, 0] ![sR, 0] (lateSetR R k)ᶜ (refXL M, refXR M)) atTop
      (𝓝 0) := by
    intro R
    have h := tendsto_codeLaw_of_antitone (a := κ) (ρL := ![sL, 0]) (ρR := ![sR, 0])
      (fun k => (measurableSet_lateSetR R k).compl)
      (fun k k' hkk' => compl_subset_compl.2 (monotone_lateSetR R hkk')) (refXL M, refXR M)
    convert h using 2
    symm
    rw [← measure_eventOf_eq_codeLaw hκ (sep_ref hM) hE'
      (Φ := fun w τ => ∀ k : ℕ, ¬ (τ = ⊤ ∧ ∀ p : ℚ≥0, (k : ℚ≥0) ≤ p → (R : ℝ) < ‖LP.traceAt (p : ℝ≥0) w‖))
      (MeasurableSet.iInter fun k => (measurableSet_lateSetR R k).compl)
      (fun x _ _ => by simp only [mem_iInter, mem_compl_iff, lateSetR, mem_ofPred_eq])
      (fun w w' τ hww hΦ k ⟨hτ, hk⟩ => hΦ k ⟨hτ, fun p hp => by
        have e : w = w' := funext fun t => hww t (by rw [hτ]; exact ENNReal.coe_lt_top)
        rw [e]; exact hk p hp⟩)]
    refine measure_eq_zero_iff_ae_notMem.2 ?_
    filter_upwards [htr, hζ, hE'.2.2.2.2] with ω htrω hζω hp hΦ
    obtain ⟨η, hη, htend⟩ := htrω
    have hwc : ContinuousOn (fun t => W' t ω) {s : ℝ≥0 | (s : ℝ≥0∞) < ζ' ω} := hp.isForcePath.continuousOn_w
    obtain ⟨t₀, ht₀⟩ := eventually_atTop.1 ((tendsto_atTop.1 (htend hζω)) ((R : ℝ) + 1))
    obtain ⟨k, hk⟩ := exists_nat_ge (t₀ : ℝ)
    refine hΦ k ⟨hζω, fun p hp' => ?_⟩
    have hpt : t₀ ≤ (p : ℝ≥0) := by
      have h1 : (k : ℝ≥0) ≤ (p : ℝ≥0) := by exact_mod_cast hp'
      have h2 : t₀ ≤ (k : ℝ≥0) := by exact_mod_cast hk
      exact h2.trans h1
    rw [LP.traceAt_eq_of_isGeneratingTrace hη hwc hp.1 (by rw [hζω]; exact ENNReal.coe_lt_top)]
    linarith [ht₀ _ hpt]
  -- choose the cutoffs
  set ε' : ℝ≥0∞ := ENNReal.ofReal ε / 2 with hε'
  have hε'0 : 0 < ε' := ENNReal.div_pos (ENNReal.ofReal_pos.2 hε).ne' (by norm_num)
  have hK : ∀ R : ℕ, ∃ k, codeLaw κ ![sL, 0] ![sR, 0] (lateSetR R k)ᶜ (refXL M, refXR M) <
      (2⁻¹ : ℝ≥0∞) ^ R * ε' := fun R =>
    ((hlim R).eventually (gt_mem_nhds (ENNReal.mul_pos (pow_ne_zero _ (by norm_num)) hε'0.ne'))).exists
  choose K hK using hK
  refine ⟨K, ?_⟩
  calc codeLaw κ ![sL, 0] ![sR, 0] {x | QTrans K (cw x) (cζ x)}ᶜ (refXL M, refXR M)
      ≤ codeLaw κ ![sL, 0] ![sR, 0] (⋃ R, (lateSetR R (K R))ᶜ) (refXL M, refXR M) :=
        codeLaw_mono' (qTrans_compl_subset K) _
    _ ≤ ∑' R, codeLaw κ ![sL, 0] ![sR, 0] (lateSetR R (K R))ᶜ (refXL M, refXR M) := codeLaw_iUnion_le' _ _
    _ ≤ ∑' R : ℕ, (2⁻¹ : ℝ≥0∞) ^ R * ε' := ENNReal.tsum_le_tsum fun R => (hK R).le
    _ = ENNReal.ofReal ε := by
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv, hε',
          ENNReal.mul_div_cancel (by norm_num) (by norm_num)]

/-! ### Two estimates -/

/-- **An oscillation bound from a tube bound on `[0, T]` and a bound after `T`.** -/
theorem sideOsc_le_of_after {near far : ℝ≥0 → ℝ} {T : ℝ≥0} {C₁ : ℝ} (hn : Continuous near) (hf : Continuous far)
    (hpos : ∀ t, 0 < near t) (hle : ∀ t, near t ≤ far t) (htube : ∀ t ≤ T, 7 / 8 ≤ near t)
    (hafter : ∀ t, T ≤ t → ∫ s in (T : ℝ)..t, (1 / near s.toNNReal ^ 2 - 1 / far s.toNNReal ^ 2) ≤ C₁)
    (T' : ℝ≥0) : TrialsHi.sideOsc near far T' ≤ 64 / 49 * T + C₁ := by
  set f : ℝ → ℝ := fun s => 1 / near s.toNNReal ^ 2 - 1 / far s.toNNReal ^ 2 with hfdef
  have hfc : Continuous f := by
    have h1 : Continuous fun s : ℝ => near s.toNNReal := hn.comp continuous_real_toNNReal
    have h2 : Continuous fun s : ℝ => far s.toNNReal := hf.comp continuous_real_toNNReal
    refine (continuous_const.div (h1.pow 2) fun s => (pow_pos (hpos _) 2).ne').sub
      (continuous_const.div (h2.pow 2) fun s => (pow_pos ((hpos _).trans_le (hle _)) 2).ne')
  have hfi : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b => hfc.intervalIntegrable a b
  have hf0 : ∀ s, 0 ≤ f s := fun s => by
    simp only [hfdef, sub_nonneg]
    exact one_div_le_one_div_of_le (pow_pos (hpos _) 2) (pow_le_pow_left₀ (hpos _).le (hle _) 2)
  have hC₁ : 0 ≤ C₁ := by simpa using hafter T le_rfl
  have hT0 : ∫ s in (0 : ℝ)..(T : ℝ), f s ≤ 64 / 49 * T := by
    have h := intervalIntegral.integral_mono_on T.coe_nonneg (hfi 0 T) (intervalIntegrable_const (c := 64 / 49))
      fun s hs => by
        have hs' : s.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hs.2
        have h78 := htube _ hs'
        have hp := hpos s.toNNReal
        have h1 : f s ≤ 1 / near s.toNNReal ^ 2 := by
          simp only [hfdef]; have : 0 ≤ 1 / far s.toNNReal ^ 2 := by positivity
          linarith
        have h2 : 1 / near s.toNNReal ^ 2 ≤ 64 / 49 := by
          rw [div_le_iff₀ (by positivity)]; nlinarith
        exact h1.trans h2
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
    linarith
  show ∫ s in (0 : ℝ)..(T' : ℝ), f s ≤ 64 / 49 * T + C₁
  rcases le_total T' T with h | h
  · have hmono : ∫ s in (0 : ℝ)..(T' : ℝ), f s ≤ ∫ s in (0 : ℝ)..(T : ℝ), f s :=
      intervalIntegral.integral_mono_interval le_rfl T'.coe_nonneg (by exact_mod_cast h)
        (Eventually.of_forall fun s => hf0 s) (hfi 0 T)
    linarith
  · rw [← intervalIntegral.integral_add_adjacent_intervals (hfi 0 T) (hfi T T')]
    linarith [hafter T' h]

/-- **The Lyapunov value is small when the spread is small against the nearest gap.** -/
theorem critVal_le {κ r w l r₀ r₁ y₀ : ℝ} (hκ : 0 < κ) (hR : 0 < r₀ - w) (hlw : l ≤ w) (hΔ : 0 ≤ r₁ - r₀)
    (hy : (r₁ - r₀) / (r₀ - w) ≤ y₀) : critVal κ r w l r₀ r₁ ≤ (1 + critK r) * y₀ ^ critMu κ := by
  have hμ := (critMu_pos hκ).le
  have hD : r₀ - w ≤ r₀ - l := by linarith
  have h1 : (r₁ - r₀) / (r₀ - l) ≤ (r₁ - r₀) / (r₀ - w) := div_le_div_of_nonneg_left hΔ hR hD
  have hy0 : 0 ≤ (r₁ - r₀) / (r₀ - w) := div_nonneg hΔ hR.le
  have hA : ((r₁ - r₀) / (r₀ - w)) ^ critMu κ ≤ y₀ ^ critMu κ := Real.rpow_le_rpow hy0 hy hμ
  have hB : ((r₁ - r₀) / (r₀ - l)) ^ critMu κ ≤ y₀ ^ critMu κ :=
    Real.rpow_le_rpow (div_nonneg hΔ (hR.trans_le hD).le) (h1.trans hy) hμ
  have hK := critK_nonneg r
  unfold critVal
  nlinarith [mul_le_mul_of_nonneg_left hB hK]


/-! ### The reference success event -/

/-- **The (one- or two-sided) reference success event** of a path of the four-mark word: infinite lifetime, the
nearest left mark never hit, the left side oscillation at most `C`, quantitative transience, and — under the
proposition `rt` — the same on the right. -/
def RefGoodLR (rt : Prop) (C : ℝ) (K : ℕ → ℕ) (w : ℝ≥0 → ℝ) (vL vR : Fin 2 → ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : Prop :=
  ζ = ⊤ ∧ (∀ t, vL 0 t < w t) ∧ (∀ T, sideOsc (fun s => w s - vL 0 s) (fun s => w s - vL 1 s) T ≤ C) ∧
    (∀ (R : ℕ) (p : ℚ≥0), (K R : ℚ≥0) ≤ p → (R : ℝ) < ‖LP.traceAt (p : ℝ≥0) w‖) ∧
    (rt → (∀ t, w t < vR 0 t) ∧ ∀ T, sideOsc (fun s => vR 0 s - w s) (fun s => vR 1 s - w s) T ≤ C)

/-- **The positivity of the reference success event, separated barriers** (`M > 1`). -/
theorem refPos_of_one_lt (hκ : 0 < κ) (hD3 : LP.DistinctCompleteBelow.{u} κ 3) (hsL : κ / 2 - 2 ≤ sL)
    (hsR : -2 < sR) (hM : 1 < M) :
    ∃ (C : ℝ) (K : ℕ → ℕ) (p₀ : ℝ), 0 < p₀ ∧
      ∀ {Ω : Type} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
        (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 2 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
        IsIntegratedSLEEvolution κ (refXL M) (refXR M) ![sL, 0] ![sR, 0] P 𝓕 W VL VR B ζ →
        (∀ᵐ ω ∂P, ζ ω = ⊤) ∧ ENNReal.ofReal p₀ ≤ P {ω | RefGoodLR (κ / 2 - 2 ≤ sR) C K (fun t => W t ω)
          (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω)} := by
  have hsL2 : -2 < sL := by linarith
  -- the constants
  set μ := critMu κ with hμdef
  have hμ0 : 0 < μ := critMu_pos hκ
  set KK : ℝ := 1 + critK sL + critK sR with hKKdef
  have hKK : 1 ≤ KK := by have := critK_nonneg sL; have := critK_nonneg sR; linarith
  set y₀ : ℝ := (1 / (4 * KK)) ^ (1 / μ) with hy₀def
  have hb0 : 0 < 1 / (4 * KK) := by positivity
  have hb1 : 1 / (4 * KK) < 1 := by rw [div_lt_one (by positivity)]; linarith
  have hy₀ : 0 < y₀ := Real.rpow_pos_of_pos hb0 _
  have hy₀1 : y₀ < 1 := Real.rpow_lt_one hb0.le hb1 (by positivity)
  have hy₀μ : y₀ ^ μ = 1 / (4 * KK) := by
    rw [hy₀def, ← Real.rpow_mul hb0.le, one_div_mul_cancel hμ0.ne', Real.rpow_one]
  set ℓ₂ : ℝ := (M - 1) / y₀ + 1 with hℓ₂def
  have hM1 : 0 < M - 1 := by linarith
  have hℓ₂ : 1 ≤ ℓ₂ := by have : 0 ≤ (M - 1) / y₀ := by positivity
                          linarith
  set c : ℝ := 1 / (ℓ₂ + 1 / 8) with hcdef
  have hc : 0 < c := by positivity
  have hTn : 0 ≤ ℓ₂ / c := by positivity
  set T : ℝ≥0 := ⟨ℓ₂ / c, hTn⟩ with hTdef
  have hTv : (T : ℝ) = ℓ₂ / c := rfl
  have hT : ℓ₂ ≤ c * T := by rw [hTv, mul_div_cancel₀ _ hc.ne']
  have hTpos : (0 : ℝ) < T := by rw [hTv]; positivity
  set C : ℝ := 64 / 49 * T + 4 / μ with hCdef
  obtain ⟨ps, hps, hsteer⟩ := exists_steer_bound hκ ![sL, 0] ![sR, 0] (M := M) hc hℓ₂ le_rfl hT
  obtain ⟨K, hK⟩ := exists_qTrans_codeLaw_le' hκ hD3 hsL2 hsR hM.le (ε := ps / 4) (by positivity)
  -- the spread against the nearest gap at the steering time
  have hyle : ∀ {Δ R : ℝ}, 0 ≤ Δ → Δ ≤ M - 1 → ℓ₂ - 1 / 8 ≤ R → Δ < R ∧ Δ / R ≤ y₀ := by
    intro Δ R hΔ0 hΔ hR
    have hRpos : 0 < ℓ₂ - 1 / 8 := by linarith
    have hMy : M - 1 ≤ y₀ * (ℓ₂ - 1 / 8) := by
      have : y₀ * (ℓ₂ - 1 / 8) = M - 1 + y₀ * (7 / 8) := by
        simp only [hℓ₂def]; field_simp; ring
      rw [this]; have := hy₀.le; nlinarith
    refine ⟨?_, ?_⟩
    · have : M - 1 < ℓ₂ - 1 / 8 := by
        have h1 : M - 1 ≤ (M - 1) / y₀ := by rw [le_div_iff₀ hy₀]; nlinarith
        simp only [hℓ₂def]; linarith
      linarith
    · rw [div_le_iff₀ (hRpos.trans_le hR)]
      nlinarith
  refine ⟨C, K, ps / 4, by positivity, fun {Ω} {mΩ} P _ 𝓕 W VL VR B ζ hE => ?_⟩
  have hζ := ae_lifetime_eq_top_ref hsL2 hsR hM.le hE
  refine ⟨hζ, ?_⟩
  have hEa := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  -- the good set at time `0`
  set Good : Ω → Prop := fun ω => ζ ω = ⊤ ∧ IsIntegratedSLEPath κ (refXL M) (refXR M) ![sL, 0] ![sR, 0]
    (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (fun t => B t ω) (ζ ω) with hGooddef
  have hgood : ∀ᵐ ω ∂P, Good ω := by
    filter_upwards [hζ, hE.2.2.2.2] with ω h1 h2 using ⟨h1, h2⟩
  set N := {ω | ¬ Good ω} with hNdef
  have hN : P N = 0 := ae_iff.1 hgood
  set G₀ := (toMeasurable P N)ᶜ with hG₀def
  have hG₀m : MeasurableSet[usualAugmentation 𝓕 P 0] G₀ :=
    (Ito.measurableSet_usualAugmentation_of_null (measurableSet_toMeasurable P N)
      (by rw [measure_toMeasurable]; exact hN) 0).compl
  have hG₀ : ∀ ω ∈ G₀, Good ω := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable P N h)
  have hG₀c : P G₀ᶜ = 0 := by rw [hG₀def, compl_compl, measure_toMeasurable]; exact hN
  -- the tube event
  set A : Set Ω := G₀ ∩ ⋂ r : ℚ≥0, {ω | (r : ℝ≥0) < T → ((r : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
    W r ω ∈ Icc (c * r - 1 / 8) (c * r + 1 / 8)} with hAdef
  have hAm : MeasurableSet[usualAugmentation 𝓕 P T] A := by
    refine ((usualAugmentation 𝓕 P).mono (zero_le (a := T)) _ hG₀m).inter (MeasurableSet.iInter fun r => ?_)
    by_cases hr : (r : ℝ≥0) < T
    · simp only [hr, true_implies]
      exact (usualAugmentation 𝓕 P).mono hr.le _ (hEa.2.1 r _ measurableSet_Icc)
    · simp only [hr, false_implies, ofPred_true]
      exact MeasurableSet.univ
  -- the probability of the tube event
  have hPA : ENNReal.ofReal ps ≤ P A := by
    have hst := hsteer (refXL M) (refXR M) (isOrderedForceWord_ref hM.le) (refXL_le hM.le) (refXR_mem hM.le)
    rw [← measure_eventOf_eq_codeLaw hκ (sep_ref hM.le) hE
      (Φ := fun w τ => (T : ℝ≥0∞) ≤ τ ∧ ∀ r : ℚ≥0, (r : ℝ≥0) < T → |w r - c * r| ≤ 1 / 8)
      (measurableSet_steerSet c T) (fun x _ _ => Iff.rfl)
      (fun w w' τ hww ⟨h1, h2⟩ => ⟨h1, fun r hr => by
        rw [← hww r (lt_of_lt_of_le (by exact_mod_cast hr) h1)]; exact h2 r hr⟩)] at hst
    refine hst.trans ?_
    rw [← measure_inter_conull hG₀c]
    refine measure_mono fun ω ⟨⟨h1, h2⟩, hω⟩ => ⟨hω, mem_iInter.2 fun r hr => ?_⟩
    have hζω := (hG₀ ω hω).1
    refine ⟨by rw [hζω]; exact ENNReal.coe_lt_top, ?_⟩
    have := h2 r hr
    rw [abs_le] at this
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  -- the steering facts on the tube event
  have hfacts : ∀ ω ∈ A, Good ω ∧ (∀ t ≤ T, ∀ j, 7 / 8 ≤ VR j t ω - W t ω) ∧
      (∀ t ≤ T, ∀ i, 7 / 8 ≤ W t ω - VL i t ω) ∧ ℓ₂ - 1 / 8 ≤ VR 0 T ω - W T ω ∧
      c * T + 7 / 8 ≤ W T ω - VL 0 T ω := by
    intro ω hωA
    have hg := hG₀ ω hωA.1
    refine ⟨hg, ?_⟩
    have hp := hg.2
    have hf := hp.isForcePath
    have hTζ : (T : ℝ≥0∞) < ζ ω := by rw [hg.1]; exact ENNReal.coe_lt_top
    have htr : ∀ r : ℚ≥0, (r : ℝ≥0) < T → |W r ω - c * r| ≤ 1 / 8 := fun r hr => by
      have h := (mem_iInter.1 hωA.2 r) hr
      rw [abs_le]; exact ⟨by linarith [h.2.1], by linarith [h.2.2]⟩
    have hwc : ContinuousOn (fun s : ℝ => |W s.toNNReal ω - c * s|) (Icc 0 T) :=
      ((hf.continuousOn_w.comp continuous_real_toNNReal.continuousOn (Clock.mapsTo_toNNReal hTζ)).sub
        (continuousOn_const.mul continuousOn_id)).abs
    have htube : ∀ s ∈ Icc (0 : ℝ) T, |W s.toNNReal ω - c * s| ≤ 1 / 8 :=
      le_of_forall_rat_lt hTpos hwc fun r hr => by
        rw [Real.toNNReal_coe]
        exact htr r (by exact_mod_cast hr)
    obtain ⟨hR, hL, hR0, -, hL0⟩ := steer_det hp hTζ (refXL_le hM.le) (refXR_mem hM.le) htube hc hℓ₂ le_rfl hT
    exact ⟨hR, hL, hR0, hL0⟩
  -- the critical bound on the right
  set SR : Set Ω := {ω | κ / 2 - 2 ≤ sR ∧ ω ∈ A ∩ critBad (4 / μ) T W VR ζ} with hSRdef
  have hSR : P SR ≤ ENNReal.ofReal (1 / 4) * P A := by
    by_cases hsRc : κ / 2 - 2 ≤ sR
    · refine (measure_mono fun ω h => h.2).trans ?_
      refine measure_critBad_le hκ hE (by simp [refXL, refXR]) (by simp [refXR]; linarith)
        (weights_ref sL) (weights_ref sR) (by simpa using hsRc) hAm (by norm_num) fun ω hωA _ => ?_
      obtain ⟨hg, hR, -, hR0, -⟩ := hfacts ω hωA
      have hf := hg.2.isForcePath
      have hTζ : (T : ℝ≥0∞) < ζ ω := by rw [hg.1]; exact ENNReal.coe_lt_top
      have hΔ := hf.vR_sub_vR_le hTζ (Fin.zero_le (Fin.last 1))
      have hΔ0 := sub_nonneg.2 (hf.monotone_vR hTζ (Fin.zero_le (Fin.last 1)))
      have hxx : refXR M (Fin.last 1) - refXR M 0 = M - 1 := by simp [refXR]
      rw [hxx] at hΔ
      obtain ⟨hlt, hy⟩ := hyle hΔ0 hΔ hR0
      refine ⟨hlt, (critVal_le hκ (y₀ := y₀) (by linarith) (hf.vL_le_w hTζ 0) hΔ0 hy).trans ?_⟩
      rw [hy₀μ]
      have : 1 + critK (![sL, 0] 0) ≤ KK := by
        simp only [Matrix.cons_val_zero, hKKdef]; have := critK_nonneg sR; linarith
      calc (1 + critK (![sL, 0] 0)) * (1 / (4 * KK)) ≤ KK * (1 / (4 * KK)) :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = 1 / 4 := by field_simp
    · have : SR = ∅ := by
        ext ω; simp only [hSRdef, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        exact fun h => absurd h hsRc
      rw [this, measure_empty]; exact bot_le
  -- the critical bound on the left, by reflection
  set SL : Set Ω := A ∩ critBad (4 / μ) T (-W) (fun i => -VL i) ζ with hSLdef
  have hSL : P SL ≤ ENNReal.ofReal (1 / 4) * P A := by
    refine measure_critBad_le hκ (reflect_ref hE) (by simp [refXL, refXR])
      (by simp [refXR]; linarith) (weights_ref sR) (weights_ref sL) (by simpa using hsL) hAm (by norm_num)
      fun ω hωA _ => ?_
    obtain ⟨hg, -, hL, -, hL0⟩ := hfacts ω hωA
    have hf := hg.2.isForcePath
    have hTζ : (T : ℝ≥0∞) < ζ ω := by rw [hg.1]; exact ENNReal.coe_lt_top
    have hΔ := hf.vL_sub_vL_le hTζ (Fin.zero_le (Fin.last 1))
    have hΔ0 := sub_nonneg.2 (hf.antitone_vL hTζ (Fin.zero_le (Fin.last 1)))
    have hxx : refXL M 0 - refXL M (Fin.last 1) = M - 1 := by simp [refXL]; ring
    rw [hxx] at hΔ
    have hcT : ℓ₂ - 1 / 8 ≤ W T ω - VL 0 T ω := by linarith
    simp only [Pi.neg_apply]
    have e1 : -VL (Fin.last 1) T ω - -VL 0 T ω = VL 0 T ω - VL (Fin.last 1) T ω := by ring
    have e2 : -VL 0 T ω - -W T ω = W T ω - VL 0 T ω := by ring
    rw [e1, e2]
    obtain ⟨hlt, hy⟩ := hyle hΔ0 hΔ hcT
    refine ⟨hlt, ?_⟩
    have hlw : -VR 0 T ω ≤ -W T ω := neg_le_neg (hf.w_le_vR hTζ 0)
    have h := critVal_le hκ (r := ![sR, 0] 0) (y₀ := y₀) (by rw [e2]; linarith) hlw (by rw [e1]; exact hΔ0)
      (by rw [e1, e2]; exact hy)
    refine h.trans ?_
    rw [hy₀μ]
    have : 1 + critK (![sR, 0] 0) ≤ KK := by
      simp only [Matrix.cons_val_zero, hKKdef]; have := critK_nonneg sL; linarith
    calc (1 + critK (![sR, 0] 0)) * (1 / (4 * KK)) ≤ KK * (1 / (4 * KK)) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = 1 / 4 := by field_simp
  -- the quantitative transience
  have hQm : MeasurableSet {x : XCode 2 2 | QTrans K (cw x) (cζ x)} := by
    rw [← iInter_qSet]; exact MeasurableSet.iInter fun T => measurableSet_qSet K T
  set SQ := {ω | ¬ QTrans K (fun t => W t ω) (ζ ω)} with hSQdef
  have hSQ : P SQ ≤ ENNReal.ofReal (ps / 4) := by
    rw [measure_eventOf_eq_codeLaw hκ (sep_ref hM.le) hE (S := {x | QTrans K (cw x) (cζ x)}ᶜ)
      (Φ := fun w τ => ¬ QTrans K w τ) hQm.compl (fun x _ _ => Iff.rfl)
      (fun w w' τ h hn hq => hn (qTrans_congr K w' w τ (fun t ht => (h t ht).symm) hq))]
    exact hK
  -- the null event
  have hncL := ae_vL_lt_w_ref hκ hsL hM.le hE hζ
  set N₁ := {ω | ¬ (ζ ω = ⊤ ∧ (∀ t, VL 0 t ω < W t ω) ∧ (κ / 2 - 2 ≤ sR → ∀ t, W t ω < VR 0 t ω))} with hN₁def
  have hN₁ : P N₁ = 0 := by
    rw [hN₁def, ← ae_iff]
    by_cases hsRc : κ / 2 - 2 ≤ sR
    · filter_upwards [hζ, hncL, ae_w_lt_vR_ref hκ hsRc hM.le hE hζ] with ω h1 h2 h3 using ⟨h1, h2, fun _ => h3⟩
    · filter_upwards [hζ, hncL] with ω h1 h2 using ⟨h1, h2, fun h => absurd h hsRc⟩
  -- the success event contains the tube event minus the bad events
  set E := {ω | RefGoodLR (κ / 2 - 2 ≤ sR) C K (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
    (ζ ω)} with hEdef
  have hsub : A ⊆ E ∪ SL ∪ SR ∪ SQ ∪ N₁ := by
    intro ω hωA
    by_contra hcon
    simp only [mem_union, not_or] at hcon
    obtain ⟨⟨⟨⟨hE', hSL'⟩, hSR'⟩, hSQ'⟩, hN₁'⟩ := hcon
    obtain ⟨hζω, hncLω, hncRω⟩ := not_not.1 hN₁'
    have hq := not_not.1 hSQ'
    obtain ⟨hg, hRt, hLt, -, -⟩ := hfacts ω hωA
    have hp := hg.2
    have hf := hp.isForcePath
    have hlt : ∀ t : ℝ≥0, t ∈ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun t => by
      show (t : ℝ≥0∞) < ζ ω; rw [hζω]; exact ENNReal.coe_lt_top
    have hWc : Continuous fun t => W t ω := continuousOn_univ.1 (hf.continuousOn_w.mono fun t _ => hlt t)
    have hLc : ∀ i, Continuous fun t => VL i t ω := fun i =>
      continuousOn_univ.1 ((hf.continuousOn_vL i).mono fun t _ => hlt t)
    have hRc : ∀ j, Continuous fun t => VR j t ω := fun j =>
      continuousOn_univ.1 ((hf.continuousOn_vR j).mono fun t _ => hlt t)
    refine hE' ⟨hζω, hncLω, ?_, hq.2, fun hsRc => ⟨hncRω hsRc, ?_⟩⟩
    · -- the left oscillation
      have hafter : ∀ t, T ≤ t → ∫ s in (T : ℝ)..t, (1 / (W s.toNNReal ω - VL 0 s.toNNReal ω) ^ 2 -
          1 / (W s.toNNReal ω - VL 1 s.toNNReal ω) ^ 2) ≤ 4 / μ := by
        intro t hTt
        by_contra hgt
        push Not at hgt
        refine hSL' ⟨hωA, hζω, fun s => by simp only [Pi.neg_apply, neg_lt_neg_iff]; exact hncLω s,
          Or.inr ⟨t, hTt, ?_⟩⟩
        have e : ∫ s in (T : ℝ)..(t : ℝ), (1 / ((fun i => -VL i) 0 s.toNNReal ω - (-W) s.toNNReal ω) ^ 2 -
            1 / ((fun i => -VL i) (Fin.last 1) s.toNNReal ω - (-W) s.toNNReal ω) ^ 2) =
            ∫ s in (T : ℝ)..(t : ℝ), (1 / (W s.toNNReal ω - VL 0 s.toNNReal ω) ^ 2 -
            1 / (W s.toNNReal ω - VL 1 s.toNNReal ω) ^ 2) :=
          intervalIntegral.integral_congr fun s _ => by
            simp only [Pi.neg_apply, show (Fin.last 1 : Fin 2) = 1 from rfl]; ring_nf
        rw [e]; exact hgt
      exact sideOsc_le_of_after (hWc.sub (hLc 0)) (hWc.sub (hLc 1)) (fun t => sub_pos.2 (hncLω t))
        (fun t => by have := hf.antitone_vL (hlt t) (Fin.zero_le (1 : Fin 2)); simp only at this; linarith)
        (fun t ht => hLt t ht 0) hafter
    · -- the right oscillation
      have hafter : ∀ t, T ≤ t → ∫ s in (T : ℝ)..t, (1 / (VR 0 s.toNNReal ω - W s.toNNReal ω) ^ 2 -
          1 / (VR 1 s.toNNReal ω - W s.toNNReal ω) ^ 2) ≤ 4 / μ := by
        intro t hTt
        by_contra hgt
        push Not at hgt
        exact hSR' ⟨hsRc, hωA, hζω, hncRω hsRc, Or.inr ⟨t, hTt, hgt⟩⟩
      exact sideOsc_le_of_after ((hRc 0).sub hWc) ((hRc 1).sub hWc) (fun t => sub_pos.2 (hncRω hsRc t))
        (fun t => by have := hf.monotone_vR (hlt t) (Fin.zero_le (1 : Fin 2)); simp only at this; linarith)
        (fun t ht => hRt t ht 0) hafter
  -- the measure estimate
  have hPAfin : P A ≠ ⊤ := measure_ne_top P A
  have hmain : P A ≤ P E + ENNReal.ofReal (1 / 4) * P A + ENNReal.ofReal (1 / 4) * P A +
      ENNReal.ofReal (ps / 4) := by
    calc P A ≤ P (E ∪ SL ∪ SR ∪ SQ ∪ N₁) := measure_mono hsub
      _ ≤ P E + P SL + P SR + P SQ + P N₁ := by
          refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
          refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
          refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
          exact measure_union_le _ _
      _ ≤ P E + ENNReal.ofReal (1 / 4) * P A + ENNReal.ofReal (1 / 4) * P A + ENNReal.ofReal (ps / 4) + 0 := by
          rw [hN₁]; gcongr
      _ = _ := add_zero _
  have hEfin : P E ≠ ⊤ := measure_ne_top P E
  have hreal := ENNReal.toReal_mono (by finiteness) hmain
  rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add hEfin (by finiteness), ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num),
    ENNReal.toReal_ofReal (by positivity)] at hreal
  have hpsA : ps ≤ (P A).toReal := (ENNReal.ofReal_le_iff_le_toReal hPAfin).1 hPA
  rw [← ENNReal.ofReal_toReal hEfin]
  exact ENNReal.ofReal_le_ofReal (by linarith)


/-- **The positivity of the reference success event, coincident barriers** (`M = 1`: the side oscillations vanish). -/
theorem refPos_one (hκ : 0 < κ) (hD3 : LP.DistinctCompleteBelow.{u} κ 3) (hsL : κ / 2 - 2 ≤ sL)
    (hsR : -2 < sR) :
    ∃ (C : ℝ) (K : ℕ → ℕ) (p₀ : ℝ), 0 < p₀ ∧
      ∀ {Ω : Type} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
        (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 2 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
        IsIntegratedSLEEvolution κ (refXL 1) (refXR 1) ![sL, 0] ![sR, 0] P 𝓕 W VL VR B ζ →
        (∀ᵐ ω ∂P, ζ ω = ⊤) ∧ ENNReal.ofReal p₀ ≤ P {ω | RefGoodLR (κ / 2 - 2 ≤ sR) C K (fun t => W t ω)
          (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω)} := by
  have hsL2 : -2 < sL := by linarith
  obtain ⟨K, hK⟩ := exists_qTrans_codeLaw_le' hκ hD3 hsL2 hsR le_rfl (M := 1) (ε := 1 / 2) (by norm_num)
  refine ⟨0, K, 1 / 2, by norm_num, fun {Ω} {mΩ} P _ 𝓕 W VL VR B ζ hE => ?_⟩
  have hζ := ae_lifetime_eq_top_ref hsL2 hsR le_rfl hE
  refine ⟨hζ, ?_⟩
  have hQm : MeasurableSet {x : XCode 2 2 | QTrans K (cw x) (cζ x)} := by
    rw [← iInter_qSet]; exact MeasurableSet.iInter fun T => measurableSet_qSet K T
  set SQ := {ω | ¬ QTrans K (fun t => W t ω) (ζ ω)} with hSQdef
  have hSQ : P SQ ≤ ENNReal.ofReal (1 / 2) := by
    rw [measure_eventOf_eq_codeLaw hκ (sep_ref le_rfl) hE (S := {x | QTrans K (cw x) (cζ x)}ᶜ)
      (Φ := fun w τ => ¬ QTrans K w τ) hQm.compl (fun x _ _ => Iff.rfl)
      (fun w w' τ h hn hq => hn (qTrans_congr K w' w τ (fun t ht => (h t ht).symm) hq))]
    exact hK
  have hncL := ae_vL_lt_w_ref hκ hsL le_rfl hE hζ
  set N₁ := {ω | ¬ (ζ ω = ⊤ ∧ IsIntegratedSLEPath κ (refXL 1) (refXR 1) ![sL, 0] ![sR, 0] (fun t => W t ω)
    (fun i t => VL i t ω) (fun j t => VR j t ω) (fun t => B t ω) (ζ ω) ∧ (∀ t, VL 0 t ω < W t ω) ∧
    (κ / 2 - 2 ≤ sR → ∀ t, W t ω < VR 0 t ω))} with hN₁def
  have hN₁ : P N₁ = 0 := by
    rw [hN₁def, ← ae_iff]
    by_cases hsRc : κ / 2 - 2 ≤ sR
    · filter_upwards [hζ, hE.2.2.2.2, hncL, ae_w_lt_vR_ref hκ hsRc le_rfl hE hζ] with ω h1 h2 h3 h4
        using ⟨h1, h2, h3, fun _ => h4⟩
    · filter_upwards [hζ, hE.2.2.2.2, hncL] with ω h1 h2 h3 using ⟨h1, h2, h3, fun h => absurd h hsRc⟩
  set E := {ω | RefGoodLR (κ / 2 - 2 ≤ sR) 0 K (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
    (ζ ω)} with hEdef
  have hsub : (univ : Set Ω) ⊆ E ∪ SQ ∪ N₁ := by
    intro ω _
    by_contra hcon
    simp only [mem_union, not_or] at hcon
    obtain ⟨⟨hE', hSQ'⟩, hN₁'⟩ := hcon
    obtain ⟨hζω, hp, hncLω, hncRω⟩ := not_not.1 hN₁'
    have hq := not_not.1 hSQ'
    have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω := fun t => by rw [hζω]; exact ENNReal.coe_lt_top
    have hzero : ∀ (f g : ℝ≥0 → ℝ), (∀ t, f t = g t) → ∀ T, TrialsHi.sideOsc f g T = 0 := fun f g h T => by
      simp only [TrialsHi.sideOsc, h, sub_self, intervalIntegral.integral_zero]
    refine hE' ⟨hζω, hncLω, fun T => (hzero _ _ (fun t => by
        show W t ω - VL 0 t ω = W t ω - VL 1 t ω
        rw [hp.vL_eq_of_xL_eq (hlt t) (show refXL 1 0 = refXL 1 1 by simp [refXL])]) T).le, hq.2,
      fun hsRc => ⟨hncRω hsRc, fun T => (hzero _ _ (fun t => by
        show VR 0 t ω - W t ω = VR 1 t ω - W t ω
        rw [hp.vR_eq_of_xR_eq (hlt t) (show refXR 1 0 = refXR 1 1 by simp [refXR])]) T).le⟩⟩
  have hmain : 1 ≤ P E + ENNReal.ofReal (1 / 2) := by
    calc (1 : ℝ≥0∞) = P univ := measure_univ.symm
      _ ≤ P (E ∪ SQ ∪ N₁) := measure_mono hsub
      _ ≤ P E + P SQ + P N₁ := (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ P E + ENNReal.ofReal (1 / 2) + 0 := by rw [hN₁]; gcongr
      _ = _ := add_zero _
  have e : ENNReal.ofReal (1 / 2) = 1 - ENNReal.ofReal (1 / 2) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]; norm_num
  rw [e]
  exact tsub_le_iff_right.2 hmain

/-- **The positivity of the reference success event** (Aux. lemma 111, "Both totals are at least `c`" and "A sole
right mark is allowed to continue"), every `M ≥ 1`. -/
theorem refPos (hκ : 0 < κ) (hD3 : LP.DistinctCompleteBelow.{u} κ 3) (hsL : κ / 2 - 2 ≤ sL) (hsR : -2 < sR)
    (hM : 1 ≤ M) :
    ∃ (C : ℝ) (K : ℕ → ℕ) (p₀ : ℝ), 0 < p₀ ∧
      ∀ {Ω : Type} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
        (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 2 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
        IsIntegratedSLEEvolution κ (refXL M) (refXR M) ![sL, 0] ![sR, 0] P 𝓕 W VL VR B ζ →
        (∀ᵐ ω ∂P, ζ ω = ⊤) ∧ ENNReal.ofReal p₀ ≤ P {ω | RefGoodLR (κ / 2 - 2 ≤ sR) C K (fun t => W t ω)
          (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω)} := by
  rcases hM.lt_or_eq with h | h
  · exact refPos_of_one_lt hκ hD3 hsL hsR h
  · subst h; exact refPos_one hκ hD3 hsL hsR

/-- **`RefTrialPositivity` for nearest weights at least `κ/2 − 2`** (the inner references of Aux. lemma 111, critical
totals included): the extension of PROVE-TRIALS-HI2's `innerRefPositivityStatement` to `s_L, s_R ≥ κ/2 − 2`. -/
theorem refTrialPositivity_of_ge (hκ : 0 < κ) (hD3 : LP.DistinctCompleteBelow.{u} κ 3) (hsL : κ / 2 - 2 ≤ sL)
    (hsR : κ / 2 - 2 ≤ sR) (hM : 1 ≤ M) : RefTrialPositivity κ M ![sL, 0] ![sR, 0] := by
  obtain ⟨C, K, p₀, hp₀, h⟩ := refPos (sR := sR) hκ hD3 hsL (by linarith) hM
  refine ⟨C, K, p₀, hp₀, fun {Ω} {mΩ} P _ 𝓕 W VL VR B ζ hE => ?_⟩
  obtain ⟨hζ, hP⟩ := h P 𝓕 W VL VR B ζ hE
  refine ⟨hζ, hP.trans (measure_mono fun ω hω => ?_)⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hω
  obtain ⟨h6, h7⟩ := h5 hsR
  exact ⟨h1, fun t => ⟨h2 t, h6 t⟩, h3, h7, h4⟩


end TrialsHi4

end Sec7

end InteractingSLE
