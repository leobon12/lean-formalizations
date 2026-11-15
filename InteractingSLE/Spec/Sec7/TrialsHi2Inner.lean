/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.TrialsHi2OscBound
import InteractingSLE.Spec.Sec7.TrialsHiSector
import InteractingSLE.Spec.Sec4.RepulsionNoncollision

/-!
# The inner reference of Aux. lemma 111 has a positive-probability success event

Packet PROVE-TRIALS-HI2. Proof of PROVE-TRIALS-HI's named input `TrialsHi.InnerRefPositivityStatement κ` for every
`κ > 0` (Specification p. 364: "Both totals are at least `c`. Take the reference weights to be `s_L, s_R` … Choose
deterministic `δ > 0` such that this distance exceeds `4δ` with positive probability"), in driver form. For the
four-mark word `(−1, −M; 1, M)` with weights `(s_L, 0; s_R, 0)`, `s_L, s_R > κ/2 − 2`, every evolution has:

* an infinite lifetime and strictly noncolliding nearest marks (Aux. lemma 6, `Sec4.aux6Statement`;
  `ae_noncollision_ref`);
* both side oscillations bounded by `C` with probability `≥ 3/4` each, `C` independent of the evolution (the
  Lyapunov tail bound `measure_sideOsc_gt_le`, and the reflection for the left side);
* quantitative transience `QTrans K` with probability `≥ 3/4`, `K` independent of the evolution: the smaller-count
  hypothesis at `N = 3` makes the two-mark word `(−1; 1)` complete, deleting the zero-weight marks gives a transient
  trace on one evolution in the universe of the hypothesis, and the canonical code law transports the probability to
  every evolution (`exists_qTrans_codeLaw_le`).

Hence `P(RefGood C K) ≥ 1/4` (`innerRefPositivityStatement`).

## Main results

* `codeLaw_mono'`, `codeLaw_iUnion_le'`;
* `ae_noncollision_ref`, `exists_qTrans_codeLaw_le`;
* **`innerRefPositivityStatement`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u v

namespace InteractingSLE

namespace Sec7

namespace TrialsHi2

open ZhanGT4 Zhan Sec7.RandRestart Sec2 Sec2.Assembly Sec2.Restart TrialsHi

/-! ### Monotonicity and subadditivity of the canonical code law -/

section CodeLaw

variable {nL nR : ℕ} {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

theorem codeLaw_mono' {S S' : Set (XCode nL nR)} (h : S ⊆ S') (s : (Fin nL → ℝ) × (Fin nR → ℝ)) :
    codeLaw a ρL ρR S s ≤ codeLaw a ρL ρR S' s := by
  refine measure_mono fun f hf => ?_
  simp only [mem_preimage, restartSetS, lawSetS, mem_ofPred_eq, mem_image] at hf ⊢
  obtain ⟨x, hx, hxe⟩ := hf
  exact ⟨x, ⟨hx.1, h hx.2⟩, hxe⟩

theorem codeLaw_iUnion_le' (S : ℕ → Set (XCode nL nR)) (s : (Fin nL → ℝ) × (Fin nR → ℝ)) :
    codeLaw a ρL ρR (⋃ n, S n) s ≤ ∑' n, codeLaw a ρL ρR (S n) s := by
  unfold codeLaw
  refine (measure_mono fun f hf => ?_).trans (measure_iUnion_le (fun n => Prod.mk s ⁻¹' restartSetS a ρL ρR (S n)))
  obtain ⟨x, ⟨hx1, hx2⟩, hxe⟩ := hf
  obtain ⟨n, hn⟩ := mem_iUnion.1 hx2
  exact mem_iUnion.2 ⟨n, ⟨x, ⟨hx1, hn⟩, hxe⟩⟩

end CodeLaw

/-! ### The reference word -/

section Word

variable {M : ℝ}

@[simp] theorem refXL_zero (M : ℝ) : refXL M 0 = -1 := rfl
@[simp] theorem refXL_one (M : ℝ) : refXL M 1 = -M := rfl
@[simp] theorem refXR_zero (M : ℝ) : refXR M 0 = 1 := rfl
@[simp] theorem refXR_one (M : ℝ) : refXR M 1 = M := rfl

theorem fin_two_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  rcases i with ⟨_ | _ | n, hn⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
  · omega

theorem isOrderedForceWord_ref (hM : 1 ≤ M) : IsOrderedForceWord (refXL M) (refXR M) := by
  refine ⟨fun i j hij => ?_, fun i => ?_, fun i j hij => ?_, fun i => ?_⟩
  · rcases fin_two_cases i with rfl | rfl <;> rcases fin_two_cases j with rfl | rfl <;> simp_all
  · rcases fin_two_cases i with rfl | rfl
    · simp
    · simp; linarith
  · rcases fin_two_cases i with rfl | rfl <;> rcases fin_two_cases j with rfl | rfl <;> simp_all
  · rcases fin_two_cases i with rfl | rfl
    · simp
    · simp; linarith

theorem sep_ref (hM : 1 ≤ M) : ∀ i j, refXL M i < refXR M j := fun i j => by
  rcases fin_two_cases i with rfl | rfl <;> rcases fin_two_cases j with rfl | rfl <;> simp <;> linarith

theorem sep_ref_reflect (hM : 1 ≤ M) : ∀ i j, (-refXR M) i < (-refXL M) j := fun i j => by
  simp only [Pi.neg_apply, neg_lt_neg_iff]; exact sep_ref hM j i

theorem weights_ref (s : ℝ) : ∀ i : Fin 2, i ≠ 0 → (![s, 0] : Fin 2 → ℝ) i = 0 := fun i hi => by
  rcases fin_two_cases i with rfl | rfl
  · exact absurd rfl hi
  · rfl

theorem sum_weights_ref (s : ℝ) : ∑ i, (![s, 0] : Fin 2 → ℝ) i = s := by simp [Fin.sum_univ_two]

/-- **The partial sums of the inner reference are admissible** (both nearest weights `≥ κ/2 − 2`). -/
theorem hasAdmissiblePartialSums_ref {κ sL sR : ℝ} (hsL : κ / 2 - 2 < sL) (hsR : κ / 2 - 2 < sR) (hM : 1 ≤ M) :
    Sec4.HasAdmissiblePartialSums κ ![sL, 0] ![sR, 0] (refXL M) (refXR M) := by
  refine ⟨fun x _ hx => ?_, fun x _ hx => ?_⟩
  · obtain ⟨i, hi⟩ := hx
    have h0 : x < refXL M 0 := by
      rcases fin_two_cases i with rfl | rfl
      · exact hi
      · simp only [refXL_one, refXL_zero] at hi ⊢; linarith
    rw [Finset.sum_filter, Fin.sum_univ_two]
    simp only [refXL_zero] at h0
    simp only [refXL_zero, refXL_one, h0, ↓reduceIte, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    split_ifs <;> linarith
  · obtain ⟨j, hj⟩ := hx
    have h0 : refXR M 0 ≤ x := by
      rcases fin_two_cases j with rfl | rfl
      · exact hj
      · simp only [refXR_one, refXR_zero] at hj ⊢; linarith
    rw [Finset.sum_filter, Fin.sum_univ_two]
    simp only [refXR_zero] at h0
    simp only [refXR_zero, refXR_one, h0, ↓reduceIte, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    split_ifs <;> linarith

variable {κ sL sR : ℝ} {Ω : Type v} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 2 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Noncollision of the inner reference** (Aux. lemma 6): infinite lifetime and the nearest marks strictly
separated from the driver at every time. -/
theorem ae_noncollision_ref (hκ : 0 < κ) (hsL : κ / 2 - 2 < sL) (hsR : κ / 2 - 2 < sR) (hM : 1 ≤ M)
    (hE : IsIntegratedSLEEvolution κ (refXL M) (refXR M) ![sL, 0] ![sR, 0] P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ t, VL 0 t ω < W t ω ∧ W t ω < VR 0 t ω := by
  have h6 := Sec4.aux6Statement.{v} hκ (refXL M) (refXR M) ![sL, 0] ![sR, 0] P 𝓕 W VL VR B ζ
    (isOrderedForceWord_ref hM) (hasAdmissiblePartialSums_ref hsL hsR hM) hE
  filter_upwards [h6, hE.2.2.2.2] with ω h hp
  refine ⟨h.1, fun t => ?_⟩
  rcases (zero_le (a := t)).eq_or_lt with ht | ht
  · subst ht
    have hF := hp.isForcePath
    have e1 := hF.vL_zero 0
    have e2 := hF.vR_zero 0
    have e3 := hp.1
    simp only at e1 e2 e3
    rw [e1, e2, e3]
    simp
  · exact ⟨(h.2 t ht).1 0, (h.2 t ht).2 0⟩

end Word

/-! ### Quantitative transience of the inner reference, through the code law -/

section Trans

variable {nL nR : ℕ}

/-- The code event "infinite lifetime, and from time `k` on the trace at rational times lies outside the closed disc
of radius `R`". -/
def lateSetR (R k : ℕ) : Set (XCode nL nR) :=
  {x | cζ x = ⊤ ∧ ∀ p : ℚ≥0, (k : ℚ≥0) ≤ p → (R : ℝ) < ‖LP.traceAt (p : ℝ≥0) (cw x)‖}

theorem measurableSet_lateSetR (R k : ℕ) : MeasurableSet (lateSetR (nL := nL) (nR := nR) R k) := by
  have h1 : MeasurableSet {x : XCode nL nR | cζ x = ⊤} := measurable_cζ (measurableSet_singleton ⊤)
  have h2 : ∀ p : ℚ≥0, MeasurableSet {x : XCode nL nR | (k : ℚ≥0) ≤ p →
      (R : ℝ) < ‖LP.traceAt (p : ℝ≥0) (cw x)‖} := fun p => by
    by_cases hk : (k : ℚ≥0) ≤ p
    · simp only [hk, true_implies]
      exact measurableSet_lt measurable_const ((LP.measurable_traceAt _).comp measurable_cw).norm
    · simp [hk]
  have e : lateSetR (nL := nL) (nR := nR) R k = {x | cζ x = ⊤} ∩ ⋂ p : ℚ≥0, {x | (k : ℚ≥0) ≤ p →
      (R : ℝ) < ‖LP.traceAt (p : ℝ≥0) (cw x)‖} := by
    ext x; simp [lateSetR]
  rw [e]
  exact h1.inter (MeasurableSet.iInter h2)

theorem monotone_lateSetR (R : ℕ) : Monotone fun k => lateSetR (nL := nL) (nR := nR) R k := by
  intro k k' hk x ⟨h1, h2⟩
  exact ⟨h1, fun p hp => h2 p ((by exact_mod_cast hk : (k : ℚ≥0) ≤ k').trans hp)⟩

theorem qTrans_compl_subset (K : ℕ → ℕ) :
    {x : XCode nL nR | QTrans K (cw x) (cζ x)}ᶜ ⊆ ⋃ R, (lateSetR R (K R))ᶜ := by
  intro x hx
  by_contra h
  simp only [mem_iUnion, mem_compl_iff, not_exists, not_not] at h
  exact hx ⟨(h 0).1, fun R p hp => (h R).2 p hp⟩

variable {κ sL sR M : ℝ}

/-- **Quantitative transience of the inner reference in law**: under the smaller-count hypothesis at `N = 3`, there
is `K` with `codeLaw(not QTrans K) ≤ 1/4` at the reference word. -/
theorem exists_qTrans_codeLaw_le (hκ : 0 < κ) (hD3 : LP.DistinctCompleteBelow.{u} κ 3)
    (hsL : κ / 2 - 2 < sL) (hsR : κ / 2 - 2 < sR) (hM : 1 ≤ M) :
    ∃ K : ℕ → ℕ, codeLaw κ ![sL, 0] ![sR, 0] {x | QTrans K (cw x) (cζ x)}ᶜ (refXL M, refXR M) ≤
      ENNReal.ofReal (1 / 4) := by
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
    · rw [Fin.fin_one_eq_zero i]; show refXL M 0 ≤ 0; simp
    · rw [Subsingleton.elim i j]
    · rw [Fin.fin_one_eq_zero i]; show 0 ≤ refXR M 0; simp
    · exact absurd hij (by rw [Subsingleton.elim i j]; exact lt_irrefl _)
    · exact absurd hij (by rw [Subsingleton.elim i j]; exact lt_irrefl _)
  have htr := hD3 _ _ (fun j => (![sL, 0] : Fin 2 → ℝ) (Fin.castSuccOrderEmb (n := 1) j))
    (fun j => (![sR, 0] : Fin 2 → ℝ) (Fin.castSuccOrderEmb (n := 1) j)) hdist (by norm_num) P' 𝓕' W' _ _ B' ζ'
    hsub
  have hnc := ae_noncollision_ref hκ hsL hsR hM hE'
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
    filter_upwards [htr, hnc, hE'.2.2.2.2] with ω htrω hncω hp hΦ
    obtain ⟨η, hη, htend⟩ := htrω
    have hζ := hncω.1
    have hwc : ContinuousOn (fun t => W' t ω) {s : ℝ≥0 | (s : ℝ≥0∞) < ζ' ω} := hp.isForcePath.continuousOn_w
    obtain ⟨t₀, ht₀⟩ := eventually_atTop.1 ((tendsto_atTop.1 (htend hζ)) ((R : ℝ) + 1))
    obtain ⟨k, hk⟩ := exists_nat_ge (t₀ : ℝ)
    refine hΦ k ⟨hζ, fun p hp' => ?_⟩
    have hpt : t₀ ≤ (p : ℝ≥0) := by
      have h1 : (k : ℝ≥0) ≤ (p : ℝ≥0) := by exact_mod_cast hp'
      have h2 : t₀ ≤ (k : ℝ≥0) := by exact_mod_cast hk
      exact h2.trans h1
    rw [LP.traceAt_eq_of_isGeneratingTrace hη hwc hp.1 (by rw [hζ]; exact ENNReal.coe_lt_top)]
    linarith [ht₀ _ hpt]
  -- choose the cutoffs
  have hK : ∀ R : ℕ, ∃ k, codeLaw κ ![sL, 0] ![sR, 0] (lateSetR R k)ᶜ (refXL M, refXR M) <
      (2⁻¹ : ℝ≥0∞) ^ R * 8⁻¹ := fun R =>
    ((hlim R).eventually (gt_mem_nhds (ENNReal.mul_pos (pow_ne_zero _ (by norm_num)) (by norm_num)))).exists
  choose K hK using hK
  refine ⟨K, ?_⟩
  calc codeLaw κ ![sL, 0] ![sR, 0] {x | QTrans K (cw x) (cζ x)}ᶜ (refXL M, refXR M)
      ≤ codeLaw κ ![sL, 0] ![sR, 0] (⋃ R, (lateSetR R (K R))ᶜ) (refXL M, refXR M) :=
        codeLaw_mono' (qTrans_compl_subset K) _
    _ ≤ ∑' R, codeLaw κ ![sL, 0] ![sR, 0] (lateSetR R (K R))ᶜ (refXL M, refXR M) := codeLaw_iUnion_le' _ _
    _ ≤ ∑' R : ℕ, (2⁻¹ : ℝ≥0∞) ^ R * 8⁻¹ := ENNReal.tsum_le_tsum fun R => (hK R).le
    _ = ENNReal.ofReal (1 / 4) := by
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
        rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]
        rw [show (ENNReal.ofReal 4) = 4 by norm_num]
        rw [show (8 : ℝ≥0∞) = 2 * 4 by norm_num, ENNReal.mul_inv (by norm_num) (by norm_num), ← mul_assoc,
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul, one_div]

end Trans

/-! ### The inner-reference positivity -/

section Main

/-- **`TrialsHi.InnerRefPositivityStatement κ` for every `κ > 0`** (Specification p. 364, Aux. lemma 111's inner
references): the reference success event of the four-mark word `(−1, −M; 1, M)` with weights `(s_L, 0; s_R, 0)`,
`s_L, s_R > κ/2 − 2`, has probability at least `1/4` for every evolution, with constants `C`, `K` independent of the
evolution. -/
theorem innerRefPositivityStatement {κ : ℝ} (hκ : 0 < κ) : InnerRefPositivityStatement.{u} κ := by
  intro hD3 sL sR hsL hsR M hM
  have ha : 0 < 2 + ∑ i, (![sL, 0] : Fin 2 → ℝ) i := by rw [sum_weights_ref]; linarith
  have hb : κ / 2 < 2 + ∑ j, (![sR, 0] : Fin 2 → ℝ) j := by rw [sum_weights_ref]; linarith
  have ha' : 0 < 2 + ∑ i, (![sR, 0] : Fin 2 → ℝ) i := by rw [sum_weights_ref]; linarith
  have hb' : κ / 2 < 2 + ∑ j, (![sL, 0] : Fin 2 → ℝ) j := by rw [sum_weights_ref]; linarith
  obtain ⟨θ, lam, c₀, hθ0, hθ1, hlam, hc₀, hJ⟩ := exists_oscJ_le hκ ha hb
  obtain ⟨θ', lam', c₀', hθ0', hθ1', hlam', hc₀', hJ'⟩ := exists_oscJ_le hκ ha' hb'
  obtain ⟨K, hKq⟩ := exists_qTrans_codeLaw_le hκ hD3 hsL hsR hM
  set KR := oscK (refXL M) (refXR M) 1 θ lam c₀ with hKRdef
  set KL := oscK (-refXR M) (-refXL M) 1 θ' lam' c₀' with hKLdef
  set C := 4 * (|KR| + |KL|) + 1 with hCdef
  have hC : 0 < C := by positivity
  have hKR : ENNReal.ofReal (KR / C) ≤ ENNReal.ofReal (1 / 4) := ENNReal.ofReal_le_ofReal (by
    rw [div_le_iff₀ hC]; linarith [le_abs_self KR, abs_nonneg KL])
  have hKL : ENNReal.ofReal (KL / C) ≤ ENNReal.ofReal (1 / 4) := ENNReal.ofReal_le_ofReal (by
    rw [div_le_iff₀ hC]; linarith [le_abs_self KL, abs_nonneg KR])
  have hQm : MeasurableSet {x : XCode 2 2 | QTrans K (cw x) (cζ x)} := by
    rw [← iInter_qSet]; exact MeasurableSet.iInter fun T => measurableSet_qSet K T
  refine ⟨C, K, 1 / 4, by norm_num, fun {Ω} {mΩ} P _ 𝓕 W VL VR B ζ hE => ?_⟩
  have hnc := ae_noncollision_ref hκ hsL hsR hM hE
  refine ⟨hnc.mono fun ω h => h.1, ?_⟩
  -- the right oscillation
  have hRo := measure_sideOsc_gt_le hκ hE (sep_ref hM) (by simp) (weights_ref sL) (weights_ref sR) hnc hθ0 hθ1
    hlam hc₀ hJ 1 hC
  -- the left oscillation, by reflection
  have hEr := hE.reflect
  have hncr : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ t, (fun i => -VR i) 0 t ω < (-W) t ω ∧ (-W) t ω < (fun i => -VL i) 0 t ω := by
    filter_upwards [hnc] with ω h
    refine ⟨h.1, fun t => ⟨?_, ?_⟩⟩
    · simp only [Pi.neg_apply, neg_lt_neg_iff]; exact (h.2 t).2
    · simp only [Pi.neg_apply, neg_lt_neg_iff]; exact (h.2 t).1
  have hLo := measure_sideOsc_gt_le hκ hEr (sep_ref_reflect hM) (by simp) (weights_ref sR) (weights_ref sL) hncr
    hθ0' hθ1' hlam' hc₀' hJ' 1 hC
  -- the quantitative transience
  have hQ : P {ω | ¬ QTrans K (fun t => W t ω) (ζ ω)} ≤ ENNReal.ofReal (1 / 4) := by
    rw [measure_eventOf_eq_codeLaw hκ (sep_ref hM) hE (S := {x | QTrans K (cw x) (cζ x)}ᶜ)
      (Φ := fun w τ => ¬ QTrans K w τ) hQm.compl (fun x _ _ => Iff.rfl)
      (fun w w' τ h hn hq => hn (qTrans_congr K w' w τ (fun t ht => (h t ht).symm) hq))]
    exact hKq
  -- the success event contains the complement of the four bad events
  set N₀ := {ω | ¬ (ζ ω = ⊤ ∧ ∀ t, VL 0 t ω < W t ω ∧ W t ω < VR 0 t ω)} with hN₀
  have hN₀0 : P N₀ = 0 := by rw [hN₀, ← ae_iff]; exact hnc
  set SR := {ω | ∃ T₀ : ℝ≥0, C < sideOsc (fun s => VR 0 s ω - W s ω) (fun s => VR 1 s ω - W s ω) T₀}
  set SL := {ω | ∃ T₀ : ℝ≥0, C < sideOsc (fun s => (fun i => -VL i) 0 s ω - (-W) s ω)
    (fun s => (fun i => -VL i) 1 s ω - (-W) s ω) T₀}
  set SQ := {ω | ¬ QTrans K (fun t => W t ω) (ζ ω)}
  set Gd := {ω | RefGood C K (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω)}
  have hsub : Gdᶜ ⊆ N₀ ∪ SL ∪ SR ∪ SQ := by
    intro ω hω
    by_contra h
    simp only [mem_union, not_or] at h
    obtain ⟨⟨⟨h0, hl⟩, hr⟩, hq⟩ := h
    have h0' : ζ ω = ⊤ ∧ ∀ t, VL 0 t ω < W t ω ∧ W t ω < VR 0 t ω := not_not.1 h0
    have hq' : QTrans K (fun t => W t ω) (ζ ω) := not_not.1 hq
    refine hω ⟨h0'.1, h0'.2, fun T₀ => ?_, fun T₀ => ?_, hq'.2⟩
    · have e1 : (fun s => (fun i => -VL i) 0 s ω - (-W) s ω) = fun s => W s ω - VL 0 s ω := by
        funext s; simp only [Pi.neg_apply]; ring
      have e2 : (fun s => (fun i => -VL i) 1 s ω - (-W) s ω) = fun s => W s ω - VL 1 s ω := by
        funext s; simp only [Pi.neg_apply]; ring
      have := fun T => not_lt.1 (fun hT => hl ⟨T, hT⟩)
      simp only [e1, e2] at this
      exact this T₀
    · exact not_lt.1 fun hT => hr ⟨T₀, hT⟩
  have hbad : P Gdᶜ ≤ ENNReal.ofReal (3 / 4) := by
    calc P Gdᶜ ≤ P (N₀ ∪ SL ∪ SR ∪ SQ) := measure_mono hsub
      _ ≤ P N₀ + P SL + P SR + P SQ := by
          refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
          refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
          exact measure_union_le _ _
      _ ≤ 0 + ENNReal.ofReal (1 / 4) + ENNReal.ofReal (1 / 4) + ENNReal.ofReal (1 / 4) := by
          rw [hN₀0]
          gcongr
          · exact hLo.trans hKL
          · exact hRo.trans hKR
      _ = ENNReal.ofReal (3 / 4) := by
          rw [zero_add, ← ENNReal.ofReal_add (by norm_num) (by norm_num),
            ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
          norm_num
  have h1 : (1 : ℝ≥0∞) ≤ P Gd + P Gdᶜ := by
    rw [← measure_univ (μ := P), ← union_compl_self Gd]; exact measure_union_le _ _
  have h2 : (1 : ℝ≥0∞) ≤ P Gd + ENNReal.ofReal (3 / 4) := h1.trans (add_le_add le_rfl hbad)
  have e : ENNReal.ofReal (1 / 4) = 1 - ENNReal.ofReal (3 / 4) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]; norm_num
  rw [e]
  exact tsub_le_iff_right.2 h2

end Main

end TrialsHi2

end Sec7

end InteractingSLE
