/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.TrialsHi3Phase1
import InteractingSLE.Spec.Sec7.TrialsHi2Assembly
import InteractingSLE.Spec.Supplement.LPProbReflect

/-!
# The low-sector trial bound when a side with at least two marks has total in `(κ/2 − 4, κ/2 − 2)`

Packet PROVE-TRIALS-HI3. Specification §7.3, Aux. lemmas 110–111 (the finite whole-side swallow) and Aux. lemma 113
(p. 370: after a merge "at most `N − 1` active groups remain"). For weights whose right side has at least two marks
and total `s ∈ (κ/2 − 4, κ/2 − 2)` the uniform trial bound holds (`uniformTrialBound_swallowR`), and by reflection
the same for the left side (`uniformTrialBound_swallowL`). The proof combines

* the steering stage (`exists_steer_bound`): with probability at least `p > 0` (uniform over the normalized family)
  the driver follows `c t` up to a time `T`, at which the realized word is tight (`steer_det`);
* the restart at `T` (`measure_restart_codeEvent`) with the tight bound: from a tight word the canonical
  non-transience probability is at most `1/2` (`codeLaw_nt_le_half_of_tight`: the cluster is swallowed or the
  evolution dies with probability `≥ 1/2`, `measure_noMeet_le_half`, and a merge excludes non-transience,
  `ae_noMeet_of_nonTransient`);

so that `codeLaw ρ ntCodeSet (y) ≤ 1 − p/2`.

## Main results

* `codeLaw_nt_le_half_of_tight`, `codeLaw_nt_le_of_restart`;
* **`uniformTrialBound_swallowR`**, `codeLaw_nt_reflect`, `uniformTrialBound_reflect`,
  **`uniformTrialBound_swallowL`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace TrialsHi3

open ZhanGT4 Zhan Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart

variable {nL nR : ℕ}

/-! ### From a tight start -/

/-- **From a tight start the canonical non-transience probability is at most `1/2`** (right cluster with at least
two marks and total in `(κ/2 − 4, κ/2 − 2)`, under the smaller-count hypothesis). -/
theorem codeLaw_nt_le_half_of_tight {κ : ℝ} (hκ : 0 < κ) {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    (hnR : 0 < nR) (hs1 : κ / 2 - 4 < ∑ j, ρR j) (hs2 : ∑ j, ρR j < κ / 2 - 2) {N : ℕ}
    (hD : LP.DistinctCompleteBelow.{u} κ N) (hN : nL + 1 + (nR + 1) ≤ N) :
    ∃ ε₀ K₀ : ℝ, 0 < ε₀ ∧ 0 < K₀ ∧ ∀ (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ),
      IsOrderedForceWord xL xR → (∀ i j, xL i < xR j) → 0 < xR 0 →
      xR (Fin.last nR) - xR 0 ≤ ε₀ * xR (Fin.last nR) → K₀ * xR (Fin.last nR) ≤ xR 0 - xL 0 →
      codeLaw κ ρL ρR ntCodeSet (xL, xR) ≤ ENNReal.ofReal (1 / 2) := by
  obtain ⟨ε₀, K₀, hε₀, hK₀, h⟩ := measure_noMeet_le_half.{u} (ρL := ρL) hκ hnR hs1 hs2
  refine ⟨ε₀, K₀, hε₀, hK₀, fun xL xR hF hsep hx0 hΔ hK => ?_⟩
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ :=
    LP.exists_isIntegratedSLEEvolution_ulift.{u} hκ hF (ρL := ρL) (ρR := ρR)
  rw [← measure_nonTransient_eq_codeLaw hκ hsep hE]
  have hmerge := ae_noMeet_of_nonTransient hκ hD hN hE
  calc P {ω | NonTransientEvent (fun t => W t ω) (ζ ω)}
      ≤ P {ω | ζ ω = ⊤ ∧ ∀ t, ¬ SameSideMeet (fun i t => VL i t ω) (fun j t => VR j t ω) t} := by
        refine measure_mono_ae (hmerge.mono fun ω hω hnt => ?_)
        exact ⟨hnt.1, hω hnt⟩
    _ ≤ _ := h xL xR hF hsep hx0 hΔ hK hE

/-! ### The restart at the end of the steering stage -/

/-- **The restart at a deterministic time `T`.** If every path that survives `T` with its driver in the tube has a
realized word at `T` with canonical non-transience probability at most `1/2`, then
`codeLaw nt ≤ 1 − codeLaw(steerSet)/2`. -/
theorem codeLaw_nt_le_of_restart {κ : ℝ} (hκ : 0 < κ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) (hsep : ∀ i j, xL i < xR j) {c : ℝ} {T : ℝ≥0}
    (hgood : ∀ {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞},
      IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ → (T : ℝ≥0∞) < ζ →
      (∀ r : ℚ≥0, (r : ℝ≥0) < T → |w r - c * r| ≤ 1 / 8) →
      codeLaw κ ρL ρR ntCodeSet ((fun i => vL i T - w T), fun j => vR j T - w T) ≤ ENNReal.ofReal (1 / 2)) :
    (codeLaw κ ρL ρR ntCodeSet (xL, xR)).toReal ≤
      1 - (codeLaw κ ρL ρR (steerSet c T) (xL, xR)).toReal / 2 := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ :=
    exists_isIntegratedSLEEvolution_assembled hκ hF (ρL := ρL) (ρR := ρR)
  have hEa := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  set Φ : (ℝ≥0 → ℝ) → Prop := fun w => ∀ r : ℚ≥0, (r : ℝ≥0) < T → |w r - c * r| ≤ 1 / 8 with hΦdef
  -- the two canonical laws
  have hNT := measure_nonTransient_eq_codeLaw hκ hsep hE
  have hA' : P {ω | (T : ℝ≥0∞) ≤ ζ ω ∧ Φ (fun t => W t ω)} = codeLaw κ ρL ρR (steerSet c T) (xL, xR) :=
    measure_eventOf_eq_codeLaw hκ hsep hE (Φ := fun w τ => (T : ℝ≥0∞) ≤ τ ∧ Φ w)
      (measurableSet_steerSet c T) (fun _ _ _ => Iff.rfl) fun w w' τ h ⟨hT, hw⟩ =>
        ⟨hT, fun r hr => by
          rw [← h r (lt_of_lt_of_le (by exact_mod_cast hr) hT)]; exact hw r hr⟩
  -- measurability
  have hζst : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (ζ ω : WithTop ℝ≥0) :=
    Ito.isStoppingTime_lifetime hEa.2.1
  have hKm : ∀ r : ℝ≥0, Measurable[usualAugmentation 𝓕 P r] (Girsanov.killed ζ W r) := fun r =>
    Girsanov.measurable_killed hEa.2.1 r
  have hTζm : MeasurableSet[usualAugmentation 𝓕 P T] {ω | (T : ℝ≥0∞) < ζ ω} := by
    have h := (hζst T).compl
    convert h using 1
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff]
    exact not_le.symm
  have hΦm : MeasurableSet[usualAugmentation 𝓕 P T]
      {ω | ∀ r : ℚ≥0, (r : ℝ≥0) < T → |Girsanov.killed ζ W r ω - c * r| ≤ 1 / 8} := by
    have e : {ω | ∀ r : ℚ≥0, (r : ℝ≥0) < T → |Girsanov.killed ζ W r ω - c * r| ≤ 1 / 8} =
        ⋂ r : ℚ≥0, {ω | (r : ℝ≥0) < T → |Girsanov.killed ζ W r ω - c * r| ≤ 1 / 8} := by
      ext ω; simp
    rw [e]
    refine MeasurableSet.iInter fun r => ?_
    by_cases hr : (r : ℝ≥0) < T
    · simp only [hr, true_implies]
      have hm : Measurable[usualAugmentation 𝓕 P T] fun ω => Girsanov.killed ζ W r ω - c * r :=
        ((hKm r).mono ((usualAugmentation 𝓕 P).mono hr.le) le_rfl).sub_const _
      have e2 : {ω | |Girsanov.killed ζ W r ω - c * r| ≤ 1 / 8} =
          (fun ω => Girsanov.killed ζ W r ω - c * r) ⁻¹' Icc (-(1 / 8)) (1 / 8) := by
        ext ω; simp only [mem_ofPred_eq, mem_preimage, mem_Icc, abs_le]
      rw [e2]
      exact hm measurableSet_Icc
    · simp [hr]
  -- the bad paths
  have hae : ∀ᵐ ω ∂P, IsIntegratedSLEPath κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
      (B · ω) (ζ ω) := hE.2.2.2.2
  obtain ⟨Nn, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hae)
  have hN𝓖 : MeasurableSet[usualAugmentation 𝓕 P T] Nn := Ito.measurableSet_usualAugmentation_of_null hNm hN0 T
  have hpath : ∀ ω ∉ Nn, IsIntegratedSLEPath κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (B · ω) (ζ ω) := fun ω hω => by
    by_contra hc
    exact hω (hNsub hc)
  -- the restart event
  set A := {ω | ω ∉ Nn ∧ (T : ℝ≥0∞) < ζ ω ∧ Φ (fun t => W t ω)} with hAdef
  have hAe : A = Nnᶜ ∩ ({ω | (T : ℝ≥0∞) < ζ ω} ∩
      {ω | ∀ r : ℚ≥0, (r : ℝ≥0) < T → |Girsanov.killed ζ W r ω - c * r| ≤ 1 / 8}) := by
    ext ω
    simp only [hAdef, hΦdef, mem_ofPred_eq, mem_inter_iff, mem_compl_iff]
    refine and_congr_right fun _ => ⟨fun ⟨h1, h2⟩ => ⟨h1, fun r hr => ?_⟩, fun ⟨h1, h2⟩ => ⟨h1, fun r hr => ?_⟩⟩
    · rw [Girsanov.killed_of_lt (lt_trans (by exact_mod_cast hr) h1)]; exact h2 r hr
    · have := h2 r hr
      rwa [Girsanov.killed_of_lt (lt_trans (by exact_mod_cast hr) h1)] at this
  have hst := isStoppingTime_const (usualAugmentation 𝓕 P) T
  have hAm : MeasurableSet[hst.measurableSpace] A := by
    rw [IsStoppingTime.measurableSpace_const, hAe]
    exact hN𝓖.compl.inter (hTζm.inter hΦm)
  have hAT : ∀ ω ∈ A, (T : ℝ≥0∞) < ζ ω ∧ (0 < T ∨ ∀ i j, xL i < xR j) := fun ω hω => ⟨hω.2.1, Or.inr hsep⟩
  have hlaw := measure_restart_codeEvent hκ hEa (T := fun _ => T) hst hAm hAT (Φ := NonTransientEvent)
    measurableSet_ntCodeSet (fun _ _ _ => Iff.rfl) nonTransientEvent_congr
  have hsub : A ∩ {ω | NonTransientEvent (fun t => W t ω) (ζ ω)} ⊆
      A ∩ {ω | NonTransientEvent (fun t => W (T + t) ω - W T ω) (ζ ω - T)} := by
    rintro ω ⟨hωA, hnt⟩
    refine ⟨hωA, ?_⟩
    have hζ : ζ ω = ⊤ := hnt.1
    have hp := hpath ω hωA.1
    have hwc : Continuous fun t => W t ω :=
      continuousOn_univ.1 (hp.isForcePath.continuousOn_w.mono fun t _ => by
        rw [hζ]; exact ENNReal.coe_lt_top)
    have hnt' : NonTransientEvent (fun t => W t ω) ⊤ := hζ ▸ hnt
    have h2 := TrialsHi.nonTransientEvent_shiftNN hwc hp.1 hnt' T
    show NonTransientEvent (fun t => W (T + t) ω - W T ω) (ζ ω - T)
    rw [hζ, ENNReal.top_sub_coe]
    exact h2
  have hint : ∫⁻ ω in A, codeLaw κ ρL ρR ntCodeSet (wordAt W VL VR (fun _ => T) ω) ∂P ≤
      ENNReal.ofReal (1 / 2) * P A := by
    rw [← setLIntegral_const]
    refine setLIntegral_mono measurable_const fun ω hω => ?_
    exact hgood (hpath ω hω.1) hω.2.1 hω.2.2
  have hfail : P (A ∩ {ω | NonTransientEvent (fun t => W t ω) (ζ ω)}) ≤ ENNReal.ofReal (1 / 2) * P A :=
    (measure_mono hsub).trans (hlaw.le.trans hint)
  -- the non-transience event is covered
  set A' := {ω | (T : ℝ≥0∞) ≤ ζ ω ∧ Φ (fun t => W t ω)} with hA'def
  have hA'm : MeasurableSet A' := by
    have hζm : Measurable fun ω => (ζ ω : WithTop ℝ≥0) := hζst.measurable_iSup.mono (iSup_le fun t =>
      (usualAugmentation 𝓕 P).le t) le_rfl
    have h1 : MeasurableSet {ω | (T : ℝ≥0∞) ≤ ζ ω} := measurableSet_le measurable_const hζm
    have e : A' = {ω | (T : ℝ≥0∞) ≤ ζ ω} ∩
        ⋂ r : ℚ≥0, {ω | (r : ℝ≥0) < T → |Girsanov.killed ζ W r ω - c * r| ≤ 1 / 8} := by
      ext ω
      simp only [hA'def, hΦdef, mem_ofPred_eq, mem_inter_iff, mem_iInter]
      refine and_congr_right fun h1 => forall_congr' fun r => imp_congr_right fun hr => ?_
      rw [Girsanov.killed_of_lt (lt_of_lt_of_le (by exact_mod_cast hr) h1)]
    rw [e]
    refine h1.inter (MeasurableSet.iInter fun r => ?_)
    by_cases hr : (r : ℝ≥0) < T
    · simp only [hr, true_implies]
      have hm : Measurable fun ω => Girsanov.killed ζ W r ω - c * r :=
        ((hKm r).mono ((usualAugmentation 𝓕 P).le r) le_rfl).sub_const _
      exact measurableSet_le hm.abs measurable_const
    · simp [hr]
  have hcover : {ω | NonTransientEvent (fun t => W t ω) (ζ ω)} ⊆
      (A ∩ {ω | NonTransientEvent (fun t => W t ω) (ζ ω)}) ∪ A'ᶜ ∪ Nn := by
    intro ω hnt
    by_cases hN : ω ∈ Nn
    · exact Or.inr hN
    by_cases hA'ω : ω ∈ A'
    · refine Or.inl (Or.inl ⟨⟨hN, ?_, hA'ω.2⟩, hnt⟩)
      rw [hnt.1]; exact ENNReal.coe_lt_top
    · exact Or.inl (Or.inr hA'ω)
  have hAA' : A ⊆ A' := fun ω hω => ⟨hω.2.1.le, hω.2.2⟩
  have hbound : P {ω | NonTransientEvent (fun t => W t ω) (ζ ω)} ≤
      ENNReal.ofReal (1 / 2) * P A' + (1 - P A') := by
    calc _ ≤ P ((A ∩ {ω | NonTransientEvent (fun t => W t ω) (ζ ω)}) ∪ A'ᶜ ∪ Nn) := measure_mono hcover
      _ ≤ P (A ∩ {ω | NonTransientEvent (fun t => W t ω) (ζ ω)}) + P A'ᶜ + P Nn :=
          (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ ENNReal.ofReal (1 / 2) * P A' + (1 - P A') := by
          rw [hN0, add_zero, prob_compl_eq_one_sub hA'm]
          exact add_le_add (hfail.trans (mul_le_mul_of_nonneg_left (measure_mono hAA') bot_le)) le_rfl
  rw [← hNT, ← hA']
  have ha1 : P A' ≤ 1 := prob_le_one
  have hfin : P A' ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ha1
  have hr := ENNReal.toReal_mono (by finiteness) hbound
  rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num),
    ENNReal.toReal_sub_of_le ha1 ENNReal.one_ne_top, ENNReal.toReal_one] at hr
  linarith

/-! ### The tube on all of `[0, T]` from the rational times -/

/-- A continuous function bounded at the rational times of `[0, T)` (`T > 0`) is bounded on `[0, T]`. -/
theorem le_of_forall_rat_lt {g : ℝ → ℝ} {T a : ℝ} (hT : 0 < T) (hg : ContinuousOn g (Icc 0 T))
    (h : ∀ r : ℚ≥0, ((r : ℝ≥0) : ℝ) < T → g ((r : ℝ≥0) : ℝ) ≤ a) : ∀ s ∈ Icc (0 : ℝ) T, g s ≤ a := by
  intro s hs
  by_contra hgt
  rw [not_le] at hgt
  have hev : ∀ᶠ s' in 𝓝[Icc 0 T] s, a < g s' := (hg s hs).eventually (lt_mem_nhds hgt)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hev)
  rcases eq_or_lt_of_le hs.1 with h0 | h0
  · have := h 0 (by simpa using hT)
    simp only [NNRat.cast_zero, NNReal.coe_zero] at this
    rw [← h0] at hgt
    linarith
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max 0 (s - δ) < s from max_lt h0 (by linarith))
    have hq0 : (0 : ℝ) ≤ q := (le_max_left _ _).trans hq1.le
    set r : ℚ≥0 := q.toNNRat with hrdef
    have hr : ((r : ℝ≥0) : ℝ) = q := by
      have e1 : ((r : ℝ≥0) : ℝ) = ((r : ℚ) : ℝ) := by norm_cast
      rw [e1, hrdef, Rat.coe_toNNRat q (by exact_mod_cast hq0)]
    have hqT : (q : ℝ) < T := hq2.trans_le hs.2
    have h1 := h r (by rw [hr]; exact hqT)
    rw [hr] at h1
    have h2 := hball (show dist (q : ℝ) s < δ by
      rw [Real.dist_eq, abs_sub_lt_iff]; constructor <;> linarith [le_max_right 0 (s - δ)])
      ⟨hq0, hqT.le⟩
    linarith

/-! ### The uniform trial bound -/

/-- **The uniform trial bound when the right side has at least two marks and total in `(κ/2 − 4, κ/2 − 2)`**
(every `κ > 0`, under the smaller-count hypothesis). -/
theorem uniformTrialBound_swallowR {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hD : LP.DistinctCompleteBelow.{u} κ N)
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} (hN : nL + 1 + (nR + 1) ≤ N) (hnR : 0 < nR)
    (hs1 : κ / 2 - 4 < ∑ j, ρR j) (hs2 : ∑ j, ρR j < κ / 2 - 2) : TrialsHi.UniformTrialBound κ ρL ρR := by
  intro M
  obtain ⟨ε₀, K₀, hε₀, hK₀, htight⟩ := codeLaw_nt_le_half_of_tight hκ hnR hs1 hs2 hD hN (ρL := ρL)
  set M' := max M 1 with hM'
  set ℓ₂ := max 1 ((M' - 1) / ε₀ + 1 / 8) with hℓ₂def
  have hℓ₂ : 1 ≤ ℓ₂ := le_max_left _ _
  set c := 1 / (ℓ₂ + 1 / 8) with hcdef
  have hc : 0 < c := by positivity
  set Xb := max (2 / c + 1 / 8) M' + 1 / 8 with hXb
  have hTpos : 0 < max (ℓ₂ / c) (K₀ * Xb / c) := lt_max_of_lt_left (by positivity)
  set T : ℝ≥0 := ⟨max (ℓ₂ / c) (K₀ * Xb / c), hTpos.le⟩ with hTdef
  have hTv : (T : ℝ) = max (ℓ₂ / c) (K₀ * Xb / c) := rfl
  have hT : ℓ₂ ≤ c * T := by
    rw [hTv]
    have := mul_le_mul_of_nonneg_left (le_max_left (ℓ₂ / c) (K₀ * Xb / c)) hc.le
    rwa [mul_div_cancel₀ _ hc.ne'] at this
  have hTK : K₀ * Xb ≤ c * T := by
    rw [hTv]
    have := mul_le_mul_of_nonneg_left (le_max_right (ℓ₂ / c) (K₀ * Xb / c)) hc.le
    rwa [mul_div_cancel₀ _ hc.ne'] at this
  obtain ⟨p, hp, hsteer⟩ := exists_steer_bound hκ ρL ρR (M := M') hc hℓ₂ le_rfl hT
  refine ⟨p / 2, by positivity, fun yL yR hF hyL0 hyR0 hML hMR => ?_⟩
  have hyL : ∀ i, yL i ≤ -1 := fun i => (hF.1 (Fin.zero_le i)).trans_eq hyL0
  have hyR : ∀ j, 1 ≤ yR j ∧ yR j ≤ M' := fun j =>
    ⟨hyR0 ▸ hF.2.2.1 (Fin.zero_le j), (hMR j).trans (le_max_left _ _)⟩
  have hsep : ∀ i j, yL i < yR j := fun i j => by linarith [hyL i, (hyR j).1]
  have hst := hsteer yL yR hF hyL hyR
  -- the realized word at `T` is tight
  have hgood : ∀ {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ} {vR : Fin (nR + 1) → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
      {ζ : ℝ≥0∞}, IsIntegratedSLEPath κ yL yR ρL ρR w vL vR b ζ → (T : ℝ≥0∞) < ζ →
      (∀ r : ℚ≥0, (r : ℝ≥0) < T → |w r - c * r| ≤ 1 / 8) →
      codeLaw κ ρL ρR ntCodeSet ((fun i => vL i T - w T), fun j => vR j T - w T) ≤ ENNReal.ofReal (1 / 2) := by
    intro w vL vR b ζ hp hTζ htr
    have hf := hp.isForcePath
    have hwc : ContinuousOn (fun s : ℝ => |w s.toNNReal - c * s|) (Icc 0 T) :=
      ((hf.continuousOn_w.comp continuous_real_toNNReal.continuousOn (Clock.mapsTo_toNNReal hTζ)).sub
        (continuousOn_const.mul continuousOn_id)).abs
    have htube : ∀ s ∈ Icc (0 : ℝ) T, |w s.toNNReal - c * s| ≤ 1 / 8 :=
      le_of_forall_rat_lt (by exact_mod_cast hTpos) hwc fun r hr => by
        rw [Real.toNNReal_coe]
        exact htr r (by exact_mod_cast hr)
    obtain ⟨hR, hL, hR0, hXT, hL0⟩ := steer_det hp hTζ hyL hyR htube hc hℓ₂ le_rfl hT
    have hord := isOrderedForceWord_at hp hTζ
    have hR0' := hR T le_rfl 0
    have hRl := hf.monotone_vR hTζ (Fin.zero_le (Fin.last nR))
    have hspread := hf.vR_sub_vR_le hTζ (Fin.zero_le (Fin.last nR))
    simp only at hRl
    refine htight _ _ hord (fun i j => ?_) (by linarith) ?_ ?_
    · have := hL T le_rfl i
      have := hR T le_rfl j
      linarith
    · have h1 : yR (Fin.last nR) - yR 0 ≤ M' - 1 := by linarith [(hyR (Fin.last nR)).2, (hyR 0).1]
      have h2 : M' - 1 ≤ ε₀ * (ℓ₂ - 1 / 8) := by
        have : (M' - 1) / ε₀ + 1 / 8 ≤ ℓ₂ := le_max_right _ _
        have h3 : (M' - 1) / ε₀ ≤ ℓ₂ - 1 / 8 := by linarith
        rwa [div_le_iff₀ hε₀, mul_comm] at h3
      have h4 : ε₀ * (ℓ₂ - 1 / 8) ≤ ε₀ * (vR (Fin.last nR) T - w T) :=
        mul_le_mul_of_nonneg_left (by linarith) hε₀.le
      linarith
    · have h1 : K₀ * (vR (Fin.last nR) T - w T) ≤ K₀ * Xb := mul_le_mul_of_nonneg_left hXT hK₀.le
      linarith
  have hres := codeLaw_nt_le_of_restart hκ hF hsep (c := c) (T := T) hgood
  have hfin : codeLaw κ ρL ρR (steerSet c T) (yL, yR) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (codeLaw_le_one _ _ _ _ _)
  have hpr : p ≤ (codeLaw κ ρL ρR (steerSet c T) (yL, yR)).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hfin).1 hst
  have hfin' : codeLaw κ ρL ρR ntCodeSet (yL, yR) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (codeLaw_le_one _ _ _ _ _)
  rw [← ENNReal.ofReal_toReal hfin']
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-! ### Reflection -/

/-- Non-transience is invariant under the reflection `w ↦ −w` of a continuous driver. -/
theorem nonTransientEvent_neg_iff {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {τ : ℝ≥0∞} :
    NonTransientEvent (-w) τ ↔ NonTransientEvent w τ := by
  rcases eq_or_ne τ ⊤ with rfl | hτ
  · have hnw : Continuous (-w) := hw.neg
    have hnw0 : (-w) 0 = 0 := by simp [hw0]
    rw [nonTransientEvent_iff hnw hnw0, nonTransientEvent_iff hw hw0]
    have htr : ∀ {v : ℝ≥0 → ℝ}, HasTrace v → HasTrace (-v) := fun ⟨η, hη⟩ =>
      ⟨_, LP.isGeneratingTrace_reflect hη⟩
    have htt : ∀ {v : ℝ≥0 → ℝ}, HasTransTrace v → HasTransTrace (-v) := fun ⟨η, hη, ht⟩ =>
      ⟨_, LP.isGeneratingTrace_reflect hη, by simpa using ht⟩
    have hnn : -(-w) = w := neg_neg w
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨hnn ▸ htr h1, fun h => h2 (htt h)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨htr h1, fun h => h2 (hnn ▸ htt h)⟩
  · exact iff_of_false (TrialsHi.not_nonTransientEvent_of_ne_top hτ)
      (TrialsHi.not_nonTransientEvent_of_ne_top hτ)

/-- **Reflection of the canonical non-transience probability.** -/
theorem codeLaw_nt_reflect {κ : ℝ} (hκ : 0 < κ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) (hsep : ∀ i j, xL i < xR j) :
    codeLaw κ ρR ρL ntCodeSet (-xR, -xL) = codeLaw κ ρL ρR ntCodeSet (xL, xR) := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ :=
    exists_isIntegratedSLEEvolution_assembled hκ hF (ρL := ρL) (ρR := ρR)
  have hsep' : ∀ i j, (-xR) i < (-xL) j := fun i j => by simp only [Pi.neg_apply]; linarith [hsep j i]
  rw [← measure_nonTransient_eq_codeLaw hκ hsep hE, ← measure_nonTransient_eq_codeLaw hκ hsep' hE.reflect]
  refine measure_congr (eventuallyEqSet_iff.2 ?_)
  filter_upwards [hE.2.2.2.2] with ω hp
  show NonTransientEvent (fun t => -W t ω) (ζ ω) ↔ NonTransientEvent (fun t => W t ω) (ζ ω)
  rcases eq_or_ne (ζ ω) ⊤ with hζ | hζ
  · have hwc : Continuous fun t => W t ω :=
      continuousOn_univ.1 (hp.isForcePath.continuousOn_w.mono fun t _ => by rw [hζ]; exact ENNReal.coe_lt_top)
    exact nonTransientEvent_neg_iff (w := fun t => W t ω) hwc hp.1
  · exact iff_of_false (TrialsHi.not_nonTransientEvent_of_ne_top hζ)
      (TrialsHi.not_nonTransientEvent_of_ne_top hζ)

/-- **Reflection of the uniform trial bound.** -/
theorem uniformTrialBound_reflect {κ : ℝ} (hκ : 0 < κ) {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    (h : TrialsHi.UniformTrialBound κ ρR ρL) : TrialsHi.UniformTrialBound κ ρL ρR := by
  intro M
  obtain ⟨p, hp, hb⟩ := h M
  refine ⟨p, hp, fun yL yR hF hyL0 hyR0 hML hMR => ?_⟩
  have hyL : ∀ i, yL i ≤ -1 := fun i => (hF.1 (Fin.zero_le i)).trans_eq hyL0
  have hyR : ∀ j, 1 ≤ yR j := fun j => hyR0 ▸ hF.2.2.1 (Fin.zero_le j)
  have hsep : ∀ i j, yL i < yR j := fun i j => by linarith [hyL i, hyR j]
  have hF' : IsOrderedForceWord (-yR) (-yL) :=
    ⟨fun i j hij => by simp only [Pi.neg_apply]; linarith [hF.2.2.1 hij],
      fun i => by simp only [Pi.neg_apply]; linarith [hF.2.2.2 i],
      fun i j hij => by simp only [Pi.neg_apply]; linarith [hF.1 hij],
      fun i => by simp only [Pi.neg_apply]; linarith [hF.2.1 i]⟩
  rw [← codeLaw_nt_reflect hκ hF hsep]
  exact hb (-yR) (-yL) hF' (by simp [hyR0]) (by simp [hyL0]) (fun j => by simp only [Pi.neg_apply]; linarith [hMR j])
    (fun i => by simp only [Pi.neg_apply]; linarith [hML i])

/-- **The uniform trial bound when the left side has at least two marks and total in `(κ/2 − 4, κ/2 − 2)`.** -/
theorem uniformTrialBound_swallowL {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hD : LP.DistinctCompleteBelow.{u} κ N)
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} (hN : nL + 1 + (nR + 1) ≤ N) (hnL : 0 < nL)
    (hs1 : κ / 2 - 4 < ∑ i, ρL i) (hs2 : ∑ i, ρL i < κ / 2 - 2) : TrialsHi.UniformTrialBound κ ρL ρR :=
  uniformTrialBound_reflect hκ (uniformTrialBound_swallowR hκ hD (ρL := ρR) (by omega) hnL hs1 hs2)

end TrialsHi3

end Sec7

end InteractingSLE
