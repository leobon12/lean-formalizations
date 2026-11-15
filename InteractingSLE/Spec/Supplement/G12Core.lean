/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G12Escape
import InteractingSLE.Spec.Coupling.AnnounceLifetime
import InteractingSLE.Spec.Supplement.LPProbReflect
import InteractingSLE.Spec.Sec4.RepulsionNoncollision

/-!
# Lemma G12 for marks with nearer weight above `−2` (almost sure)

Packet PROVE-G12. Supplement §7.9, Lemma G12 (p. 504). For an integrated `SLE_κ(ρ)` evolution of an ordered force
word, a right mark `j₀` at `y = x_{j₀}` with an inner right mark `i₀` (`x_{i₀} < y`, `i₀` the first index):

  if `S' = Σ_{x_k < y} ρ_k > −2` and `S_y = Σ_{x_k ≤ y} ρ_k > d_* = κ/2 − 4` and the right weights beyond `y` are
  `≥ 0` (left weights arbitrary), then almost surely the trace never visits `y` on `[0, ζ]` (`ae_trace_ne_right`;
  `ae_trace_ne_left` is the reflection).

The proof is the G11 method of PROVE-G11-G4 for the general word, with the strip clock and strip Brownian motion
replaced by the exponential maximal inequality of `G12Max.lean` (no time change, no unbounded-clock lemma):

* `exists_le_locG`: the localizing times `σ_n` exhaust the life of the mark on every good path;
* `ae_trace_ne_right`: the almost sure bound `|Φ − Φ_0| < a + αT` (`ae_abs_phi_lt`) on the life of the mark, and the
  pathwise `trace_ne_of_phi_bound` (`G12Escape.lean`).

The hypotheses `−2 < S'`, far weights `≥ 0` and `y` a mark beyond another right mark are where this falls short of
`Supp7.G12EvolStatement` (see the handoff `planning/handoffs/PROVE-G12.md`).
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

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {i₀ j₀ : Fin nR}
  {G : Set Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {T : ℕ → Ω → ℝ≥0}

/-- A continuous positive function on a compact set has a positive lower bound. -/
theorem exists_pos_le_of_isCompact {K : Set ℝ≥0} (hK : IsCompact K) (hne : K.Nonempty) {f : ℝ≥0 → ℝ}
    (hf : ContinuousOn f K) (hpos : ∀ r ∈ K, 0 < f r) : ∃ δ > 0, ∀ r ∈ K, δ ≤ f r := by
  obtain ⟨r₀, hr₀, hmin⟩ := hK.exists_isMinOn hne hf
  exact ⟨f r₀, hpos r₀ hr₀, fun r hr => isMinOn_iff.1 hmin r hr⟩

/-- **The localizing times exhaust the life of the mark** on every good path. -/
theorem exists_le_locG (hord : IsOrderedForceWord xL xR) (hi₀ : ∀ k, i₀ ≤ k) (hx : xR i₀ < xR j₀)
    (hTm : ∀ ω, Monotone fun n => T n ω) (hgood : ∀ ω ∈ G, IsGBGood κ xL xR ρL ρR W VL VR B ζ T ω)
    {ω : Ω} (hωG : ω ∈ G) {s : ℝ≥0}
    (hs : IsMarkLife (W · ω) (VR j₀ · ω) (ζ ω) s) : ∃ n, s ≤ locG xR j₀ G W VL VR B ζ T n ω := by
  have hω := hgood ω hωG
  have hF := hω.1.isForcePath
  set K : Set ℝ≥0 := Icc 0 s with hK
  have hKc : IsCompact K := isCompact_Icc
  have hKne : K.Nonempty := ⟨0, zero_le, zero_le⟩
  have hKζ : K ⊆ {r : ℝ≥0 | (r : ℝ≥0∞) < ζ ω} := fun r hr => (isMarkLife_mono hs hr.2).1
  have hlifeK : ∀ r ∈ K, IsMarkLife (W · ω) (VR j₀ · ω) (ζ ω) r := fun r hr => isMarkLife_mono hs hr.2
  -- the gap to the driver
  obtain ⟨δu, hδu, hδuK⟩ := exists_pos_le_of_isCompact hKc hKne
    (((hF.continuousOn_vR j₀).sub hF.continuousOn_w).mono hKζ) fun r hr => sub_pos.2 ((hlifeK r hr).2 r le_rfl)
  -- the gaps to the other marks
  have hgap : ∀ k ∈ offY xR j₀, ∃ δ > 0, ∀ r ∈ K, δ ≤ |VR j₀ r ω - VR k r ω| := by
    intro k hk
    refine exists_pos_le_of_isCompact hKc hKne
      (continuous_abs.comp_continuousOn (((hF.continuousOn_vR j₀).sub (hF.continuousOn_vR k)).mono hKζ))
      fun r hr => abs_pos.2 ?_
    have hk' : xR k ≠ xR j₀ := by simpa [offY] using hk
    rcases lt_or_gt_of_ne hk' with hlt | hgt
    · exact (near_bounds hF hord hi₀ hx hlt (hlifeK r hr)).1.ne'
    · exact sub_ne_zero.2 (ne_of_lt (sub_pos.1 (far_bounds hF hord hgt (hlifeK r hr)).1))
  choose! δk hδk hδkK using hgap
  obtain ⟨d, hd, hdle⟩ : ∃ d > 0, ∀ k ∈ offY xR j₀, d ≤ δk k := by
    rcases (offY xR j₀).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun k hk => absurd hk (by rw [he]; exact Finset.notMem_empty k)⟩
    · obtain ⟨k₀, hk₀, hmin⟩ := (offY xR j₀).exists_min_image δk hne
      exact ⟨δk k₀, hδk k₀ hk₀, hmin⟩
  set δ : ℝ := min δu d with hδ
  have hδpos : 0 < δ := lt_min hδu hd
  -- bounds on the state and on the Brownian path
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn
    ((Supp8.GB5.continuousOn_stateAt_gb hgood hωG).mono hKζ)
  obtain ⟨MB, hMB⟩ := hKc.exists_bound_of_continuousOn hω.2.1.continuousOn
  obtain ⟨n₀, hn₀⟩ := hω.2.2.2.2 s hs.1
  set n : ℕ := max n₀ (⌈M⌉₊ + ⌈MB⌉₊ + ⌈1 / δ⌉₊ + 1) with hn
  have hn₀n : n₀ ≤ n := le_max_left _ _
  have hnbig : (⌈M⌉₊ + ⌈MB⌉₊ + ⌈1 / δ⌉₊ + 1 : ℝ) ≤ n := by exact_mod_cast le_max_right n₀ _
  have hM0 : M ≤ n := by
    have := Nat.le_ceil M
    have : (0 : ℝ) ≤ ⌈MB⌉₊ := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ ⌈1 / δ⌉₊ := Nat.cast_nonneg _
    linarith
  have hMB0 : MB < n := by
    have := Nat.le_ceil MB
    have : (0 : ℝ) ≤ ⌈M⌉₊ := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ ⌈1 / δ⌉₊ := Nat.cast_nonneg _
    linarith
  have hdlt : dlt n ≤ δ := by
    have h1 := Nat.le_ceil (1 / δ)
    have : (0 : ℝ) ≤ ⌈M⌉₊ := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ ⌈MB⌉₊ := Nat.cast_nonneg _
    have h2 : 1 / δ ≤ (n : ℝ) + 1 := by linarith
    rw [dlt, div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hδpos] at h2
    linarith
  -- the level function is nonnegative on `[0, s]`
  have hlev : ∀ r ∈ K, 0 ≤ levG xR j₀ n (Coupling.stateAt W VL VR r ω) := by
    intro r hr
    refine levG_nonneg_iff.2 ⟨?_, ?_, fun i => ?_, fun k hk => ?_⟩
    · simp only [Coupling.stateAt]
      exact hdlt.trans ((min_le_left _ _).trans (hδuK r hr))
    · have := hM r hr
      exact this.trans hM0
    · simp only [Coupling.stateAt]
      have hrζ := hKζ hr
      have h1 : VR j₀ r ω - W r ω ≤ VR j₀ r ω - VL i r ω := by linarith [hF.vL_le_w hrζ i]
      have h2 : 0 < VR j₀ r ω - W r ω := sub_pos.2 ((hlifeK r hr).2 r le_rfl)
      rw [abs_of_pos (h2.trans_le h1)]
      exact hdlt.trans ((min_le_left _ _).trans ((hδuK r hr).trans h1))
    · simp only [Coupling.stateAt]
      exact hdlt.trans ((min_le_right _ _).trans ((hdle k hk).trans (hδkK k hk r hr)))
  -- `s ≤ σ_n`
  refine ⟨n, ?_⟩
  have e : (locG xR j₀ G W VL VR B ζ T n ω : WithTop ℝ≥0) = min (T n ω : WithTop ℝ≥0)
      (min (hitG xR j₀ G W VL VR ζ n ω) (MathFin.exitTime (Sec2.TwoSeed.brownG G B) n ω)) :=
    Sec2.TwoSeed.coe_capTime _ _ ω
  have hc : (s : WithTop ℝ≥0) ≤ locG xR j₀ G W VL VR B ζ T n ω := by
    rw [e]
    refine le_min (by exact_mod_cast hn₀.trans (hTm ω hn₀n)) (le_min ?_ ?_)
    · simp only [hitG, hωG, ↓reduceIte]
      refine Coupling.le_hitBelow fun r _ hneg => ?_
      by_contra hrs; rw [not_le] at hrs
      exact absurd (hlev r ⟨zero_le, hrs.le⟩) (not_le.2 hneg)
    · by_contra hlt; rw [not_le] at hlt
      have hne : MathFin.exitTime (Sec2.TwoSeed.brownG G B) n ω ≠ ⊤ := ne_top_of_lt hlt
      obtain ⟨i, hi⟩ := WithTop.ne_top_iff_exists.1 hne
      have his : i < s := by rw [← hi] at hlt; exact_mod_cast hlt
      obtain ⟨r, hr, hrB⟩ := (MathFin.exitTime_le_iff (Supp8.GB5.continuous_brownG_gb hgood) n i ω).1 (le_of_eq hi.symm)
      have hrK : r ∈ K := ⟨zero_le, hr.2.trans his.le⟩
      have hB := hMB r hrK
      simp only [Sec2.TwoSeed.brownG, hωG, ↓reduceIte] at hrB
      rw [Real.norm_eq_abs] at hB
      linarith
  exact_mod_cast hc

/-- A path continuous on `[0, T)` with a limit at `T⁻` is bounded there. -/
theorem exists_bound_of_tendsto {f : ℝ≥0 → ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)} {T : ℝ≥0} (hT : 0 < T)
    (hf : ContinuousOn f (Iio T)) {L : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)} (hL : Tendsto f (𝓝[<] T) (𝓝 L)) :
    ∃ M, ∀ s < T, ‖f s‖ ≤ M := by
  have hev : ∀ᶠ s in 𝓝[<] T, f s ∈ Metric.ball L 1 := hL (Metric.ball_mem_nhds L one_pos)
  obtain ⟨a, ha, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hT).1 hev
  obtain ⟨M₁, hM₁⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := a)).exists_bound_of_continuousOn
    (hf.mono fun s hs => lt_of_le_of_lt hs.2 ha)
  refine ⟨max M₁ (‖L‖ + 1), fun s hs => ?_⟩
  rcases le_or_gt s a with hsa | hsa
  · exact (hM₁ s ⟨zero_le, hsa⟩).trans (le_max_left _ _)
  · have h := hsub ⟨hsa, hs⟩
    rw [Set.mem_ofPred_eq, Metric.mem_ball, dist_eq_norm] at h
    have := norm_le_insert' (f s) L
    exact (by linarith : ‖f s‖ ≤ ‖L‖ + 1).trans (le_max_right _ _)

/-- **On a bounded life the left and far terms are bounded above** when the weights beyond `y` are `≥ 0` and the
state converges at a finite lifetime (Aux. lemma 3). -/
theorem exists_farAt_le {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hF : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) (hord : IsOrderedForceWord xL xR) (hy : 0 < xR j₀)
    (hfar : ∀ k ∈ farR xR j₀, 0 ≤ ρR k)
    (hconv : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ → ∃ L : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ),
      Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 L))
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ ζ) (htl : ¬ IsMarkLife w (vR j₀) ζ t) :
    ∃ Fb, ∀ s, IsMarkLife w (vR j₀) ζ s → farAt xR ρL ρR j₀ vL vR s ≤ Fb := by
  have hlt : ∀ s, IsMarkLife w (vR j₀) ζ s → s < t := by
    intro s hs
    by_contra hts; rw [not_lt] at hts
    exact htl (isMarkLife_mono hs hts)
  set st : ℝ≥0 → ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) := fun r => (w r, fun i => vL i r, fun i => vR i r) with hst
  have hcont : ContinuousOn st {r : ℝ≥0 | (r : ℝ≥0∞) < ζ} :=
    hF.continuousOn_w.prodMk ((continuousOn_pi.2 hF.continuousOn_vL).prodMk (continuousOn_pi.2 hF.continuousOn_vR))
  -- a bound on the state before `t`
  obtain ⟨M, hM⟩ : ∃ M, ∀ s < t, (s : ℝ≥0∞) < ζ → ‖st s‖ ≤ M := by
    rcases ht.lt_or_eq with htζ | htζ
    · obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).exists_bound_of_continuousOn
        (hcont.mono fun r hr => lt_of_le_of_lt (by exact_mod_cast hr.2) htζ)
      exact ⟨M, fun s hs _ => hM s ⟨zero_le, hs.le⟩⟩
    · rcases (zero_le (a := t)).eq_or_lt with h0 | h0
      · exact ⟨0, fun s hs => absurd hs (by rw [← h0]; exact not_lt_zero)⟩
      obtain ⟨L, hL⟩ := hconv t h0 htζ
      obtain ⟨M, hM⟩ := exists_bound_of_tendsto h0 (hcont.mono fun r (hr : r < t) => by
        rw [Set.mem_ofPred_eq, ← htζ]; exact_mod_cast hr) hL
      exact ⟨M, fun s hs _ => hM s hs⟩
  set M' := max (2 * M) (xR j₀ - ∑ i, xL i + 1) with hM'
  refine ⟨∑ i, (if 0 ≤ ρL i then ρL i / 2 * Real.log M' else ρL i / 2 * Real.log (xR j₀ - xL i)) +
    ∑ k ∈ farR xR j₀, ρR k / 2 * Real.log (xR k - xR j₀), fun s hs => ?_⟩
  refine add_le_add (Finset.sum_le_sum fun i _ => ?_) (Finset.sum_le_sum fun k hk => ?_)
  · have hge := left_gap_ge (j₀ := j₀) hF i hs.1
    have hpos : 0 < xR j₀ - xL i := by linarith [hord.2.1 i]
    split_ifs with hρ
    · have hb : vR j₀ s - vL i s ≤ M' := by
        obtain ⟨-, hvL, hvR⟩ := abs_le_norm_state (st s)
        have hn := hM s (hlt s hs) hs.1
        have h1 := (hvR j₀).trans hn
        have h2 := (hvL i).trans hn
        simp only [hst] at h1 h2
        have : vR j₀ s - vL i s ≤ 2 * M := by
          linarith [le_abs_self (vR j₀ s), neg_abs_le (vL i s)]
        exact this.trans (le_max_left _ _)
      exact mul_le_mul_of_nonneg_left (Real.log_le_log (hpos.trans_le hge) hb) (by linarith)
    · exact mul_le_mul_of_nonpos_left (Real.log_le_log hpos hge) (by linarith)
  · obtain ⟨hpos, hle⟩ := far_bounds hF hord (by simpa [farR] using hk) hs
    have e : Real.log (vR j₀ s - vR k s) = Real.log (vR k s - vR j₀ s) := by
      rw [← Real.log_neg_eq_log, neg_sub]
    rw [e]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hpos hle) (by linarith [hfar k hk])

/-- **Lemma G12 (right mark, nearer weight above `−2`).** For an integrated `SLE_κ(ρ)` evolution of an ordered force
word (`κ > 0`) and a generating trace `η`, a right mark `j₀` at `y = x_{j₀}` beyond the first right mark `i₀`, with
`S' = Σ_{x_k < y} ρ_k > −2`, `S_y = Σ_{x_k ≤ y} ρ_k > κ/2 − 4` and right weights beyond `y` that are `≥ 0` (left
weights arbitrary): almost surely `η` does not visit `y` on `[0, ζ]` (the terminal value included). -/
theorem ae_trace_ne_right [IsProbabilityMeasure P] (hκ : 0 < κ) (hord : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) (hi₀ : ∀ k, i₀ ≤ k)
    (hx : xR i₀ < xR j₀) (hS' : -2 < ∑ k ∈ univ.filter (fun k => xR k < xR j₀), ρR k)
    (hS : κ / 2 - 4 < ∑ k ∈ univ.filter (fun k => xR k ≤ xR j₀), ρR k)
    (hfar : ∀ k, xR j₀ < xR k → 0 ≤ ρR k) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ xR j₀ := by
  have hy : 0 < xR j₀ := lt_of_le_of_lt (hord.2.2.2 i₀) hx
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
  have hFb : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → ¬ IsMarkLife (W · ω) (VR j₀ · ω) (ζ ω) t →
      ∃ Fb, ∀ s, IsMarkLife (W · ω) (VR j₀ · ω) (ζ ω) s →
        farAt xR ρL ρR j₀ (fun i t => VL i t ω) (fun j t => VR j t ω) s ≤ Fb := by
    intro t ht htl
    refine exists_farAt_le (j₀ := j₀) hω.1.isForcePath hord hy ?_ ?_ ht htl
    · intro k hk; exact hfar k (by simpa [farR] using hk)
    · intro T' hT' hTζ
      obtain ⟨w₀, vL₀, vR₀, h1, -⟩ := hconv T' hT' hTζ
      exact ⟨(w₀, vL₀, vR₀), h1⟩
  refine trace_ne_of_phi_bound (b := fun t => B t ω) hω.1 hord hi₀ hx (by simpa [nearW, nearR] using hS') hS2
    hFb hηω (Φ₀ := phi0 κ xL xR ρL ρR j₀) (a := a) fun s hs => ?_
  obtain ⟨n, hn⟩ := exists_le_locG hord hi₀ hx hTm hgood hωG hs
  have h := ha n s hn
  simp only [coordG, Sec2.TwoSeed.brownG, hωG, ↓reduceIte] at h
  exact h

theorem isOrderedForceWord_reflect (h : IsOrderedForceWord xL xR) : IsOrderedForceWord (-xR) (-xL) :=
  ⟨fun _ _ hij => neg_le_neg (h.2.2.1 hij), fun i => neg_nonpos.2 (h.2.2.2 i),
    fun _ _ hij => neg_le_neg (h.1 hij), fun i => neg_nonneg.2 (h.2.1 i)⟩

/-- **Lemma G12 (left mark, nearer weight above `−2`)**, the reflection of `ae_trace_ne_right`: a left mark `j₀` at
`y = x_{j₀,L} < x_{i₀,L}` (`i₀` the first left index) with `Σ_{y < x_k} ρ_{k,L} > −2`, `Σ_{y ≤ x_k} ρ_{k,L} > κ/2 − 4`,
and left weights beyond `y` that are `≥ 0` (right weights arbitrary) is almost surely never visited. -/
theorem ae_trace_ne_left [IsProbabilityMeasure P] (hκ : 0 < κ) (hord : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) {i₀ j₀ : Fin nL} (hi₀ : ∀ k, i₀ ≤ k)
    (hx : xL j₀ < xL i₀) (hS' : -2 < ∑ k ∈ univ.filter (fun k => xL j₀ < xL k), ρL k)
    (hS : κ / 2 - 4 < ∑ k ∈ univ.filter (fun k => xL j₀ ≤ xL k), ρL k)
    (hfar : ∀ k, xL k < xL j₀ → 0 ≤ ρL k) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ xL j₀ := by
  have hE' := hE.reflect
  have hη' : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => (-W) t ω) (ζ ω) (fun t => LP.reflectC (η ω t)) := by
    filter_upwards [hη] with ω h
    exact LP.isGeneratingTrace_reflect h
  have h := ae_trace_ne_right (i₀ := i₀) (j₀ := j₀) hκ (isOrderedForceWord_reflect hord) hE' hη' hi₀
    (by simpa using hx) (by simpa using hS') (by simpa using hS) (fun k hk => hfar k (by simpa using hk))
  filter_upwards [h] with ω hω t ht heq
  apply hω t ht
  rw [heq]
  simp [LP.reflectC]

end G12

end Supp7

end InteractingSLE
