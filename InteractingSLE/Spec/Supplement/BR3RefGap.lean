/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BR3RefPath

/-!
# BR3's bounded reference: gaps up to a threshold on the right

Packet PROVE-T14-BR3. For an integrated path of a word whose left partial sums all exceed `−2` and whose right partial
sums exceed `−2` before a right index `k`, a finite positive lifetime is reached with the driver at the right mark `k`
(Aux. lemma 3's limit is a threshold, and only the right group through `k` can be one). A left mark that never meets
the driver before the lifetime then keeps a gap bounded above and below by positive constants: at the lifetime the gap
is `V^R_k − V^L_ℓ ≥ x^R_k − x^L_ℓ > 0` (right marks only move right, left marks only move left). This is BR3's
"All changed groups lie beyond the crosscut and remain separated" in driver form, for the marks on the side opposite
to the threshold.

* `neg_two_lt_sum_filter_of_down`: a down-closed colliding set whose partial sums exceed `−2` has weight `> −2`;
* `vR_eq_of_thresholdCondition`: at a threshold state the driver sits at the right mark `k`;
* `exists_bounds_of_tendsto`: a positive continuous function on `[0, T)` with a positive limit at `T` is bounded above
  and below by positive constants;
* **`gapBdd_of_path`**: the gap `w − v^{L,ℓ}` is bounded above and below at the rational times before a finite
  lifetime (`BR3Ref.GapBdd`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Theorem14

namespace BR3Ref

/-! ### Colliding sums -/

/-- A down-closed set of indices on which every partial sum exceeds `−2` has weight `> −2`. -/
theorem neg_two_lt_sum_filter_of_down {n : ℕ} {ρ : Fin n → ℝ} (p : Fin n → Prop) [DecidablePred p]
    (hdown : ∀ i i', i' ≤ i → p i → p i') (hpart : ∀ i, p i → -2 < ∑ l ∈ univ.filter (· ≤ i), ρ l) :
    -2 < ∑ l ∈ univ.filter p, ρ l := by
  by_cases hne : (univ.filter p).Nonempty
  · set m := (univ.filter p).max' hne
    have hm : p m := (mem_filter.1 ((univ.filter p).max'_mem hne)).2
    have e : univ.filter p = univ.filter (· ≤ m) := by
      ext i
      simp only [mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun hi => (univ.filter p).le_max' i (by simp [hi]), fun hi => hdown m i hi hm⟩
    rw [e]
    exact hpart m hm
  · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sum_empty]
    norm_num

/-- **At a threshold state the driver sits at the right mark `k`**, when every left partial sum and every right
partial sum before `k` exceeds `−2` (positions ordered around the driver). -/
theorem vR_eq_of_thresholdCondition {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w₀ : ℝ} {vL₀ : Fin nL → ℝ}
    {vR₀ : Fin nR → ℝ} (hvL : Antitone vL₀) (hvR : Monotone vR₀) (hLw : ∀ i, vL₀ i ≤ w₀) (hwR : ∀ i, w₀ ≤ vR₀ i)
    (hL : ∀ i, -2 < ∑ l ∈ univ.filter (· ≤ i), ρL l) (k : Fin nR)
    (hR : ∀ i, i < k → -2 < ∑ l ∈ univ.filter (· ≤ i), ρR l)
    (hth : ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀) : vR₀ k = w₀ := by
  by_contra hk
  have hk' : w₀ < vR₀ k := lt_of_le_of_ne (hwR k) (Ne.symm hk)
  rcases hth with h | h
  · refine absurd h (not_le.2 (neg_two_lt_sum_filter_of_down (fun i => vL₀ i = w₀) (fun i i' hii' hi => ?_)
      fun i _ => hL i))
    exact le_antisymm (hLw i') (hi ▸ hvL hii')
  · refine absurd h (not_le.2 (neg_two_lt_sum_filter_of_down (fun i => vR₀ i = w₀) (fun i i' hii' hi => ?_)
      fun i hi => hR i ?_))
    · exact le_antisymm (hi ▸ hvR hii') (hwR i')
    · by_contra hki
      rw [not_lt] at hki
      exact absurd hi (ne_of_gt (lt_of_lt_of_le hk' (hvR hki)))

/-! ### Bounds up to a limit -/

/-- **A positive continuous function on `[0, T)` with a positive limit at `T`** is bounded above and below by
positive constants on `[0, T)`. -/
theorem exists_bounds_of_tendsto {g : ℝ≥0 → ℝ} {T : ℝ≥0} (hg : ContinuousOn g (Iio T))
    (hpos : ∀ t, t < T → 0 < g t) {g₀ : ℝ} (hg₀ : 0 < g₀) (hlim : Tendsto g (𝓝[<] T) (𝓝 g₀)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∀ t, t < T → δ ≤ g t ∧ g t ≤ M := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ T) with hT | hT
  · exact ⟨1, one_pos, 0, fun t ht => absurd ht (by rw [← hT]; exact not_lt_zero)⟩
  have hev : ∀ᶠ t in 𝓝[<] T, g t ∈ Ioo (g₀ / 2) (2 * g₀) :=
    hlim (Ioo_mem_nhds (by linarith) (by linarith))
  obtain ⟨l, hlT, hl⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hT).1 hev
  have hcK : ContinuousOn g (Icc 0 l) := hg.mono fun t ht => lt_of_le_of_lt ht.2 hlT
  obtain ⟨t₁, ht₁, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, le_rfl, zero_le⟩ hcK
  obtain ⟨t₂, ht₂, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, le_rfl, zero_le⟩ hcK
  have hpos₁ : 0 < g t₁ := hpos t₁ (lt_of_le_of_lt ht₁.2 hlT)
  refine ⟨min (g t₁) (g₀ / 2), lt_min hpos₁ (by linarith), max (g t₂) (2 * g₀), fun t ht => ?_⟩
  rcases le_or_gt t l with htl | htl
  · exact ⟨(min_le_left _ _).trans (hmin ⟨zero_le, htl⟩), (hmax ⟨zero_le, htl⟩).trans (le_max_left _ _)⟩
  · have := hl ⟨htl, ht⟩
    exact ⟨(min_le_right _ _).trans this.1.le, this.2.le.trans (le_max_right _ _)⟩

/-! ### The gap code event along one path -/

/-- **The gap to a protected left mark is bounded above and below before a finite lifetime** reached at a threshold of
the right group through `k`: with every left partial sum and the right partial sums before `k` exceeding `−2`, a
separated start, a left mark `ℓ` that stays strictly left of the driver before the lifetime, and Aux. lemma 3's limit at
a positive finite lifetime. -/
theorem gapBdd_of_path {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) (hsep : ∀ i i', xL i < xR i')
    (hL : ∀ i, -2 < ∑ l ∈ univ.filter (· ≤ i), ρL l) (k : Fin nR)
    (hR : ∀ i, i < k → -2 < ∑ l ∈ univ.filter (· ≤ i), ρR l) (ℓ : Fin nL)
    (hℓ : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → vL ℓ t < w t) (hζ : ζ < ⊤)
    (hlim : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ → ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
      Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) ∧
        ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀) :
    GapBdd ℓ w vL ζ := by
  refine ⟨hζ, ?_⟩
  set T := ζ.toNNReal with hTdef
  have hT : (T : ℝ≥0∞) = ζ := ENNReal.coe_toNNReal hζ.ne
  have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ↔ t < T := fun t => by rw [← hT, ENNReal.coe_lt_coe]
  -- the real-time bounds
  obtain ⟨δ, hδ, M, hb⟩ : ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∀ t, t < T → δ ≤ w t - vL ℓ t ∧ w t - vL ℓ t ≤ M := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ T) with hT0 | hT0
    · exact ⟨1, one_pos, 0, fun t ht => absurd ht (by rw [← hT0]; exact not_lt_zero)⟩
    obtain ⟨w₀, vL₀, vR₀, htend, hth⟩ := hlim T hT0 hT
    have hfp := hp.isForcePath
    have hev : ∀ᶠ t : ℝ≥0 in 𝓝[<] T, (t : ℝ≥0∞) < ζ := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (hlt t).2 ht
    have hw := (continuous_fst.tendsto _).comp htend
    have hvL : ∀ i, Tendsto (fun t => vL i t) (𝓝[<] T) (𝓝 (vL₀ i)) := fun i =>
      ((continuous_apply i).tendsto _).comp ((continuous_fst.tendsto _).comp ((continuous_snd.tendsto _).comp htend))
    have hvR : ∀ i, Tendsto (fun t => vR i t) (𝓝[<] T) (𝓝 (vR₀ i)) := fun i =>
      ((continuous_apply i).tendsto _).comp ((continuous_snd.tendsto _).comp ((continuous_snd.tendsto _).comp htend))
    have hne : (𝓝[<] T).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hT0⟩
    have hantiL : Antitone vL₀ := fun i i' h =>
      le_of_tendsto_of_tendsto (hvL i') (hvL i) (hev.mono fun t ht => hfp.antitone_vL ht h)
    have hmonoR : Monotone vR₀ := fun i i' h =>
      le_of_tendsto_of_tendsto (hvR i) (hvR i') (hev.mono fun t ht => hfp.monotone_vR ht h)
    have hLw : ∀ i, vL₀ i ≤ w₀ := fun i =>
      le_of_tendsto_of_tendsto (hvL i) hw (hev.mono fun t ht => hfp.vL_le_w ht i)
    have hwR : ∀ i, w₀ ≤ vR₀ i := fun i =>
      le_of_tendsto_of_tendsto hw (hvR i) (hev.mono fun t ht => hfp.w_le_vR ht i)
    have hk := vR_eq_of_thresholdCondition hantiL hmonoR hLw hwR hL k hR hth
    have hxR : xR k ≤ vR₀ k := ge_of_tendsto (hvR k) (hev.mono fun t ht => hfp.xR_le_vR ht k)
    have hxL : vL₀ ℓ ≤ xL ℓ := le_of_tendsto (hvL ℓ) (hev.mono fun t ht => hfp.vL_le_xL ht ℓ)
    have hg₀ : 0 < w₀ - vL₀ ℓ := by have := hsep ℓ k; linarith
    have hset : Iio T = {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} := by ext t; exact (hlt t).symm
    refine exists_bounds_of_tendsto (g := fun t => w t - vL ℓ t)
      (by rw [hset]; exact hfp.continuousOn_w.sub (hfp.continuousOn_vL ℓ))
      (fun t ht => sub_pos.2 (hℓ t ((hlt t).2 ht))) hg₀ (hw.sub (hvL ℓ))
  obtain ⟨n₁, hn₁⟩ := exists_nat_one_div_lt hδ
  obtain ⟨n₂, hn₂⟩ := exists_nat_ge M
  refine ⟨max n₁ n₂, fun q hq => ?_⟩
  have hqT := (hlt (q : ℝ≥0)).1 hq
  obtain ⟨h1, h2⟩ := hb _ hqT
  have hm1 : (n₁ : ℝ) ≤ (max n₁ n₂ : ℕ) := by exact_mod_cast le_max_left _ _
  have hm2 : (n₂ : ℝ) ≤ (max n₁ n₂ : ℕ) := by exact_mod_cast le_max_right _ _
  refine ⟨le_trans ?_ h1, by linarith⟩
  refine le_trans ?_ hn₁.le
  gcongr

end BR3Ref

end Theorem14

end InteractingSLE
