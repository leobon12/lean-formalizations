/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G12RemSwallow

/-!
# Lemma G12's remainder: farther marks of any weight

Packet PROVE-G12B. `G12Core.ae_trace_ne_right` (PROVE-G12) proves Lemma G12 (supplement §7.9, p. 504) for a right
mark `y = x_{j₀}` beyond an inner right mark when `S' > −2`, `S_y > d_*` and every right weight beyond `y` is `≥ 0`.
The sign condition entered only through the bound on the far terms `(ρ_k/2) log(V^k − V^{j₀})` of `F` on the life
of the mark. The source's proof (p. 504) needs no sign: "At `τ`, every farther right mark remains separated from the
driver". Here:

* `exists_farAt_le_of_visit`: **if `η` visits `y` at all**, then at its first visit `t₀` the life of the mark is
  exactly `[0, t₀)` (a mark swallowed off the prefix is never visited, `trace_ne_of_gap_eq_zero`), the gap of `y`
  tends to `0` (`tendsto_gap_eq_zero_of_visit`), every farther mark keeps a positive gap
  (`tendsto_gap_pos_of_visit`), and hence `F` is bounded above on the life whatever the far weights;
* `ae_trace_ne_right_of_near`, `ae_trace_ne_left_of_near`: **Lemma G12 for a mark with `S' > −2`**, any weights
  beyond it (left weights arbitrary), almost surely.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp7

namespace G12

open G11 (IsMarkLife)
open Supp8.GB5 (IsGBGood abs_le_norm_state)

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {η : ℝ≥0 → ℂ} {i₀ j₀ : Fin nR}

/-- A function continuous and positive on `[0, T)` with a positive limit at `T⁻` has a positive lower bound. -/
theorem exists_pos_le_of_tendsto {f : ℝ≥0 → ℝ} {T : ℝ≥0} (hT : 0 < T) (hf : ContinuousOn f (Iio T))
    (hpos : ∀ s < T, 0 < f s) {L : ℝ} (hL0 : 0 < L) (hL : Tendsto f (𝓝[<] T) (𝓝 L)) :
    ∃ m > 0, ∀ s < T, m ≤ f s := by
  have hev : ∀ᶠ s in 𝓝[<] T, L / 2 < f s := hL (lt_mem_nhds (by linarith))
  obtain ⟨a, ha, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hT).1 hev
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_le_of_isCompact (isCompact_Icc (a := (0 : ℝ≥0)) (b := a))
    ⟨0, zero_le, zero_le⟩ (hf.mono fun s hs => lt_of_le_of_lt hs.2 ha) fun s hs => hpos s (lt_of_le_of_lt hs.2 ha)
  refine ⟨min δ (L / 2), lt_min hδ (by linarith), fun s hs => ?_⟩
  rcases le_or_gt s a with hsa | hsa
  · exact (min_le_left _ _).trans (hδle s ⟨zero_le, hsa⟩)
  · exact (min_le_right _ _).trans (hsub ⟨hsa, hs⟩).le

/-- **At a first visit, the far terms are bounded on the life of the mark, for any far weights.** Let `y = x_{j₀}`
be a right mark beyond an inner mark `x_{i₀} ≥ 0` (`i₀ ≤ j₀`), and let the state converge at a finite lifetime
(Aux. lemma 3). If `η` visits `y` on `[0, ζ]`, then `F = Σᵢ (ρ_{i,L}/2) log(V^{j₀} − V^{i,L}) +
Σ_{x_k > y} (ρ_k/2) log(V^{j₀} − V^k)` is bounded above on the life of the mark. -/
theorem exists_farAt_le_of_visit (hF : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) (hord : IsOrderedForceWord xL xR)
    (hη : IsGeneratingTrace w ζ η) (hij : i₀ ≤ j₀) (hx0 : 0 ≤ xR i₀) (hx : xR i₀ < xR j₀)
    (hconv : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ → ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
      Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)))
    (hvis : ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ∧ η t = xR j₀) :
    ∃ Fb, ∀ s, IsMarkLife w (vR j₀) ζ s → farAt xR ρL ρR j₀ vL vR s ≤ Fb := by
  have hy : 0 < xR j₀ := lt_of_le_of_lt hx0 hx
  -- the first visit `t₀`
  set S : Set ℝ≥0 := {t | (t : ℝ≥0∞) ≤ ζ} ∩ η ⁻¹' {(xR j₀ : ℂ)} with hS
  have hζc : IsClosed {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ} := isClosed_le ENNReal.continuous_coe continuous_const
  have hSc : IsClosed S := hη.2.1.preimage_isClosed_of_isClosed hζc isClosed_singleton
  obtain ⟨t₁, ht₁, he₁⟩ := hvis
  have hSne : S.Nonempty := ⟨t₁, ht₁, he₁⟩
  set t₀ := sInf S with ht₀def
  have ht₀S : t₀ ∈ S := hSc.csInf_mem hSne (OrderBot.bddBelow S)
  have ht₀ζ : (t₀ : ℝ≥0∞) ≤ ζ := ht₀S.1
  have hvis₀ : η t₀ = xR j₀ := ht₀S.2
  have hfirst : ∀ s < t₀, η s ≠ xR j₀ := fun s hs he =>
    absurd (csInf_le (OrderBot.bddBelow S)
      ⟨(ENNReal.coe_le_coe.2 hs.le).trans ht₀ζ, he⟩) (not_le.2 hs)
  have ht₀0 : 0 < t₀ := by
    refine pos_iff_ne_zero.2 fun h0 => ?_
    rw [h0, hη.1] at hvis₀
    have := congrArg Complex.re hvis₀
    simp only [Complex.zero_re, Complex.ofReal_re] at this
    linarith
  have hltζ : ∀ s : ℝ≥0, s < t₀ → (s : ℝ≥0∞) < ζ := fun s hs =>
    (ENNReal.coe_lt_coe.2 hs).trans_le ht₀ζ
  -- the mark is alive before `t₀`
  have hlife₀ : ∀ s : ℝ≥0, s < t₀ → w s < vR j₀ s := by
    intro s hs
    refine lt_of_le_of_ne (hF.w_le_vR (hltζ s hs) j₀) fun he => ?_
    exact trace_ne_of_gap_eq_zero hF hη hy (hltζ s hs) he.symm
      (fun s' hs' => hfirst s' (lt_of_le_of_lt hs' hs)) t₀ ht₀ζ hvis₀
  have hlifeLT : ∀ s, IsMarkLife w (vR j₀) ζ s → s < t₀ := by
    intro s hs
    by_contra hts; rw [not_lt] at hts
    exact trace_ne_of_isMarkLife hF hij hx0 hx hη (isMarkLife_mono hs hts) hvis₀
  have hLife : ∀ s, s < t₀ → IsMarkLife w (vR j₀) ζ s := fun s hs =>
    ⟨hltζ s hs, fun u hu => hlife₀ u (lt_of_le_of_lt hu hs)⟩
  -- the driver and the limits of the gaps at `t₀⁻`
  obtain ⟨U, hU, hU0, hUw, hlimV⟩ := GB7a.exists_driver hF ht₀ζ ht₀0 hconv
  obtain ⟨Ly, hLy⟩ := hlimV j₀
  have hLy0 : Ly = 0 :=
    tendsto_gap_eq_zero_of_visit hF hη hy ht₀0 ht₀ζ hvis₀ hlife₀ hU hU0 hUw hLy
  -- every far mark keeps a positive distance from `V^{j₀}` on the life
  have hm : ∀ k ∈ farR xR j₀, ∃ m > 0, ∀ s, IsMarkLife w (vR j₀) ζ s → m ≤ vR k s - vR j₀ s := by
    intro k hk
    have hk' : xR j₀ < xR k := (Finset.mem_filter.1 hk).2
    obtain ⟨Lk, hLk⟩ := hlimV k
    have hLk0 := tendsto_gap_pos_of_visit hF hord hη hk' ht₀0 ht₀ζ hvis₀ hlife₀ hU hU0 hUw hLk
    have hlim : Tendsto (fun s => vR k s - vR j₀ s) (𝓝[<] t₀) (𝓝 Lk) := by
      have := hLk.sub hLy
      rw [hLy0, sub_zero] at this
      refine this.congr fun s => ?_
      ring
    have hcont : ContinuousOn (fun s => vR k s - vR j₀ s) (Iio t₀) :=
      ((hF.continuousOn_vR k).sub (hF.continuousOn_vR j₀)).mono fun s hs => hltζ s hs
    obtain ⟨m, hm0, hmle⟩ := exists_pos_le_of_tendsto ht₀0 hcont
      (fun s hs => (far_bounds hF hord hk' (hLife s hs)).1) hLk0 hlim
    exact ⟨m, hm0, fun s hs => hmle s (hlifeLT s hs)⟩
  choose! m hm0 hmle using hm
  -- a bound on the state before `t₀`
  set st : ℝ≥0 → ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) := fun r => (w r, fun i => vL i r, fun i => vR i r) with hst
  have hcont : ContinuousOn st {r : ℝ≥0 | (r : ℝ≥0∞) < ζ} :=
    hF.continuousOn_w.prodMk ((continuousOn_pi.2 hF.continuousOn_vL).prodMk
      (continuousOn_pi.2 hF.continuousOn_vR))
  obtain ⟨M, hM⟩ : ∃ M, ∀ s < t₀, ‖st s‖ ≤ M := by
    rcases ht₀ζ.lt_or_eq with htζ | htζ
    · obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t₀)).exists_bound_of_continuousOn
        (hcont.mono fun r hr => lt_of_le_of_lt (by exact_mod_cast hr.2) htζ)
      exact ⟨M, fun s hs => hM s ⟨zero_le, hs.le⟩⟩
    · obtain ⟨w₀, vL₀, vR₀, hL⟩ := hconv t₀ ht₀0 htζ
      obtain ⟨M, hM⟩ := exists_bound_of_tendsto ht₀0 (hcont.mono fun r (hr : r < t₀) => by
        rw [Set.mem_ofPred_eq, ← htζ]; exact_mod_cast hr) hL
      exact ⟨M, fun s hs => hM s hs⟩
  set M' := max (2 * M) (xR j₀ - ∑ i, xL i + 1) with hM'
  refine ⟨∑ i, (if 0 ≤ ρL i then ρL i / 2 * Real.log M' else ρL i / 2 * Real.log (xR j₀ - xL i)) +
    ∑ k ∈ farR xR j₀, (if 0 ≤ ρR k then ρR k / 2 * Real.log (xR k - xR j₀) else ρR k / 2 * Real.log (m k)),
    fun s hs => ?_⟩
  refine add_le_add (Finset.sum_le_sum fun i _ => ?_) (Finset.sum_le_sum fun k hk => ?_)
  · have hge := left_gap_ge (j₀ := j₀) hF i hs.1
    have hpos : 0 < xR j₀ - xL i := by linarith [hord.2.1 i]
    split_ifs with hρ
    · have hb : vR j₀ s - vL i s ≤ M' := by
        obtain ⟨-, hvL, hvR⟩ := abs_le_norm_state (st s)
        have hn := hM s (hlifeLT s hs)
        have h1 := (hvR j₀).trans hn
        have h2 := (hvL i).trans hn
        simp only [hst] at h1 h2
        have : vR j₀ s - vL i s ≤ 2 * M := by
          linarith [le_abs_self (vR j₀ s), neg_abs_le (vL i s)]
        exact this.trans (le_max_left _ _)
      exact mul_le_mul_of_nonneg_left (Real.log_le_log (hpos.trans_le hge) hb) (by linarith)
    · exact mul_le_mul_of_nonpos_left (Real.log_le_log hpos hge) (by linarith)
  · have hk' : xR j₀ < xR k := (Finset.mem_filter.1 hk).2
    obtain ⟨hpos, hle⟩ := far_bounds hF hord hk' hs
    have e : Real.log (vR j₀ s - vR k s) = Real.log (vR k s - vR j₀ s) := by
      rw [← Real.log_neg_eq_log, neg_sub]
    rw [e]
    split_ifs with hρ
    · exact mul_le_mul_of_nonneg_left (Real.log_le_log hpos hle) (by linarith)
    · exact mul_le_mul_of_nonpos_left (Real.log_le_log (hm0 k hk) (hmle k hk s hs)) (by linarith)

section Evolution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **Lemma G12 (right mark, nearer weight above `−2`, any farther weights).** For an integrated `SLE_κ(ρ)`
evolution of an ordered force word (`κ > 0`) and a generating trace `η`, a right mark `j₀` at `y = x_{j₀}` beyond
the first right mark `i₀`, with `S' = Σ_{x_k < y} ρ_k > −2` and `S_y = Σ_{x_k ≤ y} ρ_k > κ/2 − 4`: almost surely `η`
does not visit `y` on `[0, ζ]` (the terminal value included). The weights beyond `y` and on the left are
arbitrary. -/
theorem ae_trace_ne_right_of_near [IsProbabilityMeasure P] (hκ : 0 < κ) (hord : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) (hi₀ : ∀ k, i₀ ≤ k)
    (hx : xR i₀ < xR j₀) (hS' : -2 < ∑ k ∈ univ.filter (fun k => xR k < xR j₀), ρR k)
    (hS : κ / 2 - 4 < ∑ k ∈ univ.filter (fun k => xR k ≤ xR j₀), ρR k) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ xR j₀ := by
  have hx0 : 0 ≤ xR i₀ := hord.2.2.2 i₀
  have hy : 0 < xR j₀ := lt_of_le_of_lt hx0 hx
  have hxL : ∀ i, xL i ≤ 0 := hord.2.1
  by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · -- the lifetime vanishes: only `t = 0`, where `η 0 = 0`
    filter_upwards [hE.2.2.2.2, hη] with ω hp hηω t ht
    have hζ : ζ ω = 0 := by
      by_contra hne
      have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [ENNReal.coe_zero]; exact pos_iff_ne_zero.2 hne
      have := hp.isForcePath.not_threshold h0
      have hw : W 0 ω = 0 := hp.isForcePath.w_zero
      have hL : (fun i => VL i 0 ω) = xL := funext hp.isForcePath.vL_zero
      have hR : (fun i => VR i 0 ω) = xR := funext hp.isForcePath.vR_zero
      simp only [hw, hL, hR] at this
      exact this hseed
    rw [hζ, nonpos_iff_eq_zero, ENNReal.coe_eq_zero] at ht
    rw [ht, hηω.1]
    exact_mod_cast hy.ne
  obtain ⟨T, hTann, hTn⟩ := Coupling.exists_isAnnouncingSeq_le hE hκ hseed
  obtain ⟨hT, hTm, hTζ, hTcov⟩ := hTann
  have hae : ∀ᵐ ω ∂P, IsGBGood κ xL xR ρL ρR W VL VR B ζ T ω := by
    filter_upwards [hE.2.2.2.2, hE.1.1.cont, hE.1.1.eval_zero_ae_eq_zero, ae_all_iff.2 hTζ, hTcov]
      with ω h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨G, hGm, hGc, hgood⟩ : ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧
      ∀ ω ∈ G, IsGBGood κ xL xR ρL ρR W VL VR B ζ T ω := by
    refine ⟨(toMeasurable P {ω | ¬ IsGBGood κ xL xR ρL ρR W VL VR B ζ T ω})ᶜ,
      (measurableSet_toMeasurable _ _).compl, ?_, fun ω hω => ?_⟩
    · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
    · by_contra h; exact hω (subset_toMeasurable _ _ h)
  have hα : 0 < escRate κ xR ρR j₀ := by
    rw [escRate, ← sum_le_eq_nearW_add]; linarith
  have hbound := ae_abs_phi_lt (j₀ := j₀) hE hGm hGc hgood hT hTm hTn hy hxL hκ hα
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  filter_upwards [hbound, hη, hGae, hE.ae_tendsto_threshold hκ] with ω hb hηω hωG hconv
  obtain ⟨a, ha⟩ := hb hωG
  have hω := hgood ω hωG
  have hS2 : κ / 2 - 4 < nearW xR ρR j₀ + rhoY xR ρR j₀ := by rw [← sum_le_eq_nearW_add]; exact hS
  have hconv' : ∀ T' : ℝ≥0, 0 < T' → (T' : ℝ≥0∞) = ζ ω → ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
      Tendsto (fun t => (W t ω, fun i => VL i t ω, fun i => VR i t ω)) (𝓝[<] T') (𝓝 (w₀, vL₀, vR₀)) := by
    intro T' hT' hTζ'
    obtain ⟨w₀, vL₀, vR₀, h1, -⟩ := hconv T' hT' hTζ'
    exact ⟨w₀, vL₀, vR₀, h1⟩
  intro t ht hvis
  obtain ⟨Fb, hFb⟩ := exists_farAt_le_of_visit hω.1.isForcePath hord hηω (hi₀ j₀) hx0 hx hconv' ⟨t, ht, hvis⟩
  refine trace_ne_of_phi_bound (b := fun t => B t ω) hω.1 hord hi₀ hx (by simpa [nearW, nearR] using hS') hS2
    (fun _ _ _ => ⟨Fb, hFb⟩) hηω (Φ₀ := phi0 κ xL xR ρL ρR j₀) (a := a) (fun s hs => ?_) t ht hvis
  obtain ⟨n, hn⟩ := exists_le_locG hord hi₀ hx hTm hgood hωG hs
  have h := ha n s hn
  simp only [coordG, Sec2.TwoSeed.brownG, hωG, ↓reduceIte] at h
  exact h

/-- **Lemma G12 (left mark, nearer weight above `−2`, any farther weights)**, the reflection of
`ae_trace_ne_right_of_near`: a left mark `j₀` at `y = x_{j₀,L} < x_{i₀,L}` (`i₀` the first left index) with
`Σ_{y < x_k} ρ_{k,L} > −2` and `Σ_{y ≤ x_k} ρ_{k,L} > κ/2 − 4` is almost surely never visited. -/
theorem ae_trace_ne_left_of_near [IsProbabilityMeasure P] (hκ : 0 < κ) (hord : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) {i₀ j₀ : Fin nL} (hi₀ : ∀ k, i₀ ≤ k)
    (hx : xL j₀ < xL i₀) (hS' : -2 < ∑ k ∈ univ.filter (fun k => xL j₀ < xL k), ρL k)
    (hS : κ / 2 - 4 < ∑ k ∈ univ.filter (fun k => xL j₀ ≤ xL k), ρL k) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ xL j₀ := by
  have hE' := hE.reflect
  have hη' : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => (-W) t ω) (ζ ω) (fun t => LP.reflectC (η ω t)) := by
    filter_upwards [hη] with ω h
    exact LP.isGeneratingTrace_reflect h
  have h := ae_trace_ne_right_of_near (i₀ := i₀) (j₀ := j₀) hκ (isOrderedForceWord_reflect hord) hE' hη' hi₀
    (by simpa using hx) (by simpa using hS') (by simpa using hS)
  filter_upwards [h] with ω hω t ht heq
  apply hω t ht
  rw [heq]
  simp [LP.reflectC]

end Evolution

end G12

end Supp7

end InteractingSLE
