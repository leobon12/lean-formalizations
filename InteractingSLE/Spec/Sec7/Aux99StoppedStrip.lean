/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux99StoppedReduce
import InteractingSLE.Spec.Zhan.ConstDriftAlive
import InteractingSLE.Spec.Sec5.CrossRestartLawTopo

/-!
# Aux. lemma 99 stopped: the non-continuing weights `κ/2 − 4 < ρ ≤ −2` from the strip endpoint theorem (`κ ≤ 4`)

Packet PROVE-ZHAN-A8. Specification Aux. lemma 99 (p. 340–343): after the reflection `x ↦ −x̄` and the dilation that
puts the mark at `−1`, an evolution with one mark of weight `ρ` is the R36 strip evolution without lower marks and end
weight `τ₋ = ρ` (`Strip.IsStripSLEEvolution`), with strip drift `σ = ρ + 3 − κ/2`; `|σ| < 1` is
`κ/2 − 4 < ρ < κ/2 − 2`. For `ρ ≤ −2` the mark meeting the driver is the continuation threshold, so the strip life is
the whole life `[0, ζ)`. The strip endpoint theorem (`Zhan.stripEndpointStatement_of_le_four`, PROVE-ZHAN-A8) gives a
generating trace on the strip life converging to a point `x₀ < −1`. Then:

* the lifetime is finite: a trace that is bounded on `[0, ∞)` contradicts `hcap(K_t) = 2t ≤ diam(K_t)²`
  (`false_of_bounded_isGeneratingTrace`);
* the trace extended by `x₀` at `ζ` is a generating trace on `[0, ζ]` (`isGeneratingTrace_extend_of_tendsto`).

So the end-mark word is complete (`isCompleteForceWord_endMark`), and by reflection and dilation every word with one
right mark `x > 0` of such a weight (`isCompleteForceWord_oneRight_of_strip`). With
`Sec7.aux99StoppedStatement_of_seed_of_nonAdmissible` this leaves, for every `κ > 0`, only the weights
`ρ ≤ min(−2, κ/2 − 4)` (strip drift `σ ≤ −1`) in `Aux99StoppedStatement κ` besides the seed theorem
(`aux99StoppedStatement_of_seed_of_low`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

open Sec7.RandRestart

/-! ### A bounded trace has a bounded horizon -/

/-- **A generating trace of a continuous driver on every finite horizon is unbounded** (`hcap(K_s) = 2s` and
`hcap ≤ diam²`). -/
theorem false_of_bounded_isGeneratingTrace {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : ∀ s : ℝ≥0, IsGeneratingTrace w s η) {R : ℝ} (hR : ∀ t, ‖η t‖ ≤ R) : False := by
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR 0)
  set W : ℝ → ℝ := fun r => w r.toNNReal with hW
  have hWc : Continuous W := hw.comp continuous_real_toNNReal
  have hW0 : W 0 = 0 := by simp [hW, hw0]
  set s : ℝ≥0 := ⟨2 * R ^ 2 + 1, by positivity⟩ with hs
  have hfill := (hη (s + 1)).2.2 s (by exact_mod_cast lt_add_one s)
  have hcont : ContinuousOn η (Icc 0 s) := (hη (s + 1)).2.1.mono fun t ht =>
    (show (t : ℝ≥0∞) ≤ ((s + 1 : ℝ≥0) : ℝ≥0∞) by exact_mod_cast ht.2.trans (le_add_of_nonneg_right zero_le))
  have hcpt : IsCompact (η '' Icc 0 s) := isCompact_Icc.image_of_continuousOn hcont
  have hK : QuantumZipper.fwdHull W s = fillH (η '' Icc 0 s) :=
    Sec5.CrossRestart.fwdHull_eq_fillH_of_isFilling hcpt hfill
  have hball : QuantumZipper.fwdHull W s ⊆ closedBall 0 R := by
    rw [hK]
    refine fillH_subset_closedBall_zero ?_
    rw [hcpt.isClosed.closure_eq]
    rintro _ ⟨t, -, rfl⟩
    exact mem_closedBall_zero_iff.2 (hR t)
  have hcap := hcap_fwdHull hWc hW0 s.coe_nonneg
  have hle := HPHull.hcap_le_diam_sq ⟨QuantumZipper.fwdHull W s, isHPHull_fwdHull hWc s.coe_nonneg⟩
  rw [hcap] at hle
  have hdiam : diam (QuantumZipper.fwdHull W s) ≤ 2 * R :=
    (diam_mono hball isBounded_closedBall).trans (diam_closedBall hR0)
  have hd0 : 0 ≤ diam (QuantumZipper.fwdHull W s) := diam_nonneg
  have hsq : diam (QuantumZipper.fwdHull W s) ^ 2 ≤ (2 * R) ^ 2 := pow_le_pow_left₀ hd0 hdiam 2
  have : ((s : ℝ)) = 2 * R ^ 2 + 1 := rfl
  change 2 * (s : ℝ) ≤ diam (QuantumZipper.fwdHull W s) ^ 2 at hle
  nlinarith

/-! ### Extending a converging trace to its finite horizon -/

/-- **A trace generating on every `[0, s]`, `s < ζ`, and converging at the finite horizon `ζ > 0` extends to a
generating trace on `[0, ζ]`.** -/
theorem isGeneratingTrace_extend_of_tendsto {w : ℝ≥0 → ℝ} {Z : ℝ≥0} (hZ : 0 < Z) {η : ℝ≥0 → ℂ}
    (hη : ∀ s : ℝ≥0, s < Z → IsGeneratingTrace w s η) {x₀ : ℂ}
    (hlim : ∀ ε > 0, ∃ s₀ : ℝ≥0, s₀ < Z ∧ ∀ s : ℝ≥0, s₀ ≤ s → s < Z → ‖η s - x₀‖ < ε) :
    IsGeneratingTrace w Z (fun t => if t < Z then η t else x₀) := by
  set η' : ℝ≥0 → ℂ := fun t => if t < Z then η t else x₀ with hη'
  refine ⟨?_, ?_, fun t ht => ?_⟩
  · simp only [hη', hZ, ↓reduceIte]
    exact (hη 0 hZ).1
  · intro t ht
    have ht' : t ≤ Z := by exact_mod_cast ht
    rcases ht'.lt_or_eq with htZ | rfl
    · -- an interior point: `η' = η` near `t`, and `η` is continuous at `t`
      obtain ⟨s, hts, hsZ⟩ := exists_between htZ
      have hc : ContinuousWithinAt η {t' : ℝ≥0 | (t' : ℝ≥0∞) ≤ s} t :=
        (hη s hsZ).2.1 t (by exact_mod_cast hts.le)
      have hnhds : {t' : ℝ≥0 | (t' : ℝ≥0∞) ≤ s} ∈ 𝓝 t := by
        have : {t' : ℝ≥0 | (t' : ℝ≥0∞) ≤ s} = Iic s := by ext; simp
        rw [this]; exact Iic_mem_nhds hts
      have hca : ContinuousAt η t := hc.continuousAt hnhds
      have heq : η' =ᶠ[𝓝 t] η := by
        filter_upwards [Iio_mem_nhds htZ] with t' ht'
        have ht'' : t' < Z := ht'
        simp only [hη', ht'', ↓reduceIte]
      exact (hca.congr heq.symm).continuousWithinAt
    · -- the horizon
      rw [Metric.continuousWithinAt_iff]
      intro ε hε
      obtain ⟨s₀, hs₀Z, hs₀⟩ := hlim ε hε
      refine ⟨(t : ℝ) - s₀, sub_pos.2 (by exact_mod_cast hs₀Z), fun {t'} ht'Z hd => ?_⟩
      have ht'Z' : t' ≤ t := by exact_mod_cast ht'Z
      have htt : ¬ t < t := lt_irrefl t
      simp only [hη', htt, ↓reduceIte]
      rcases ht'Z'.lt_or_eq with hlt | heq
      · simp only [hlt, ↓reduceIte]
        rw [dist_eq_norm]
        have h1 : (t' : ℝ) ≤ t := by exact_mod_cast ht'Z'
        have h2 : dist t' t = (t : ℝ) - t' := by
          rw [NNReal.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]
        rw [h2] at hd
        have h3 : (s₀ : ℝ) ≤ t' := by linarith
        exact hs₀ t' (by exact_mod_cast h3) hlt
      · subst heq
        simp only [htt, ↓reduceIte, dist_self]
        exact hε
  · have htZ : t < Z := by exact_mod_cast ht
    obtain ⟨s, hts, hsZ⟩ := exists_between htZ
    have h := (hη s hsZ).2.2 t (by exact_mod_cast hts)
    have himg : η' '' Icc 0 t = η '' Icc 0 t :=
      image_congr fun t' ht' => by
        have h' : t' < Z := ht'.2.trans_lt htZ
        simp only [hη', h', ↓reduceIte]
    rw [himg]
    exact h

/-! ### The end-mark word -/

section EndMark

variable {κ : ℝ}

theorem abs_charge_sub_lt_two {ρL ρR : Fin 0 → ℝ} {ρ : ℝ} (h1 : κ / 2 - 4 < ρ) (h2 : ρ < κ / 2 - 2) :
    |Strip.chargePlus κ ρL ρR ρ - Strip.chargeMinus ρL ρ| < 2 := by
  have e : Strip.chargePlus κ ρL ρR ρ - Strip.chargeMinus ρL ρ = κ - 6 - 2 * ρ := by
    simp only [Strip.chargePlus, Strip.chargeMinus, Strip.tauPlus, Finset.univ_eq_empty, Finset.sum_empty]
    ring
  rw [e, abs_lt]
  constructor <;> linarith

/-- **The end-mark word is complete** for `0 < κ ≤ 4` and `κ/2 − 4 < ρ ≤ −2`: the strip evolution without lower
marks and end weight `ρ` has a continuous generating trace on `[0, ζ]`, and `ζ < ∞`. -/
theorem isCompleteForceWord_endMark (hκ : 0 < κ) (hκ4 : κ ≤ 4) {ρ : ℝ} (hρ : ρ ≤ -2) (hρ' : κ / 2 - 4 < ρ)
    (pL pR ρL ρR : Fin 0 → ℝ) :
    LP.IsCompleteForceWord.{u} κ (Strip.wordXL pL) (Strip.wordXR pR) (Strip.wordRhoL ρL ρ) ρR := by
  intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
  have hq := abs_charge_sub_lt_two (κ := κ) (ρL := ρL) (ρR := ρR) hρ' (by linarith)
  have hS := Zhan.stripEndpointStatement_of_le_four.{u} hκ hκ4 pL pR ρL ρR ρ P 𝓕 W VL VR B ζ
    Zhan.isSeparatedStripWord_elim0 Zhan.hasStripPrefixSums_elim0 hq hE
  filter_upwards [hS, hE.2.2.2.2] with ω hend hp
  have hF := hp.isForcePath
  -- before the lifetime the end mark is strictly left of the driver (a collision is the threshold)
  have hlife : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ ω →
      Strip.IsStripLife (fun t => W t ω) (fun t => VL (Fin.last 0) t ω) (ζ ω) s := by
    intro s hs
    refine ⟨hs, fun r hr => ?_⟩
    have hr' : (r : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) hs
    rcases lt_or_eq_of_le (hF.vL_le_w hr' (Fin.last 0)) with h | h
    · exact h
    · exfalso
      refine hF.not_threshold hr' (Or.inl ?_)
      have hall : ∀ i : Fin (0 + 1), VL i r ω = W r ω := fun i => by
        rw [Fin.fin_one_eq_zero i]; exact h
      rw [Finset.filter_true_of_mem fun i _ => hall i, Fin.sum_univ_one]
      have : Strip.wordRhoL ρL ρ 0 = ρ := Strip.wordRhoL_last ρL ρ
      rw [this]
      exact hρ
  obtain ⟨-, ⟨η, hη⟩, hconv⟩ := hend
  obtain ⟨x₀, -, hlim⟩ := hconv η hη
  rcases eq_or_ne (ζ ω) ⊤ with htop | hne
  · -- an infinite lifetime is impossible: the trace would be bounded
    exfalso
    have hwc : Continuous fun t => W t ω := by
      rw [← continuousOn_univ]
      exact hF.continuousOn_w.mono fun t _ => by rw [htop]; exact ENNReal.coe_lt_top
    have hη' : ∀ s : ℝ≥0, IsGeneratingTrace (fun t => W t ω) s η := fun s =>
      hη s (hlife s (by rw [htop]; exact ENNReal.coe_lt_top))
    obtain ⟨s₀, -, hs₀⟩ := hlim 1 one_pos
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := s₀)).exists_bound_of_continuousOn
      ((hη' s₀).2.1.mono fun t ht => (show (t : ℝ≥0∞) ≤ s₀ by exact_mod_cast ht.2))
    refine false_of_bounded_isGeneratingTrace hwc hF.w_zero hη' (R := max M (‖(x₀ : ℂ)‖ + 1)) fun t => ?_
    rcases le_total t s₀ with hts | hts
    · exact (hM t ⟨zero_le, hts⟩).trans (le_max_left _ _)
    · have h1 := hs₀ t hts (hlife t (by rw [htop]; exact ENNReal.coe_lt_top))
      have h2 : ‖η t‖ ≤ ‖η t - x₀‖ + ‖(x₀ : ℂ)‖ := by
        calc ‖η t‖ = ‖(η t - x₀) + x₀‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      exact (by linarith : ‖η t‖ ≤ ‖(x₀ : ℂ)‖ + 1).trans (le_max_right _ _)
  · lift ζ ω to ℝ≥0 using hne with Z hZ
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ Z) with h0 | hpos
    · -- zero lifetime: the constant trace
      refine ⟨fun _ => 0, ⟨rfl, continuousOn_const, fun t ht => ?_⟩, fun h => absurd h ENNReal.coe_ne_top⟩
      rw [← h0] at ht
      exact absurd ht (not_lt.2 bot_le)
    · refine ⟨_, isGeneratingTrace_extend_of_tendsto hpos (fun s hs => hη s (hlife s (by exact_mod_cast hs)))
        (x₀ := (x₀ : ℂ)) fun ε hε => ?_, fun h => absurd h ENNReal.coe_ne_top⟩
      obtain ⟨s₀, hs₀l, hs₀⟩ := hlim ε hε
      exact ⟨s₀, by exact_mod_cast hs₀l.1, fun s hs hsZ => hs₀ s hs (hlife s (by exact_mod_cast hsZ))⟩

end EndMark

/-! ### One right mark -/

section OneRight

variable {κ : ℝ}

/-- **One right mark at `x > 0` with weight `κ/2 − 4 < ρ ≤ −2` gives a complete word** (`0 < κ ≤ 4`), by reflection and
dilation of the end-mark word. -/
theorem isCompleteForceWord_oneRight_of_strip (hκ : 0 < κ) (hκ4 : κ ≤ 4) {xL ρL : Fin 0 → ℝ}
    {xR ρR : Fin 1 → ℝ} (hx : 0 < xR 0) (hρ : ρR 0 ≤ -2) (hρ' : κ / 2 - 4 < ρR 0) :
    LP.IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  have h1 : LP.IsCompleteForceWord.{u} κ (Strip.wordXL xL) (Strip.wordXR xL) (Strip.wordRhoL ρL (ρR 0)) ρL :=
    isCompleteForceWord_endMark hκ hκ4 hρ hρ' xL xL ρL ρL
  have h1' : LP.IsCompleteForceWord.{u} κ (-Strip.wordXR xL) (-Strip.wordXL xL) ρL (Strip.wordRhoL ρL (ρR 0)) :=
    LP.IsCompleteForceWord.reflect h1
  have h2 : LP.IsCompleteForceWord.{u} κ (fun i => xR 0 * (-Strip.wordXR xL) i)
      (fun j => xR 0 * (-Strip.wordXL xL) j) ρL (Strip.wordRhoL ρL (ρR 0)) :=
    LP.IsCompleteForceWord.dilate h1' hx
  have e1 : (fun i => xR 0 * (-Strip.wordXR xL) i) = xL := funext fun i => i.elim0
  have e2 : (fun j => xR 0 * (-Strip.wordXL xL) j) = xR := by
    funext j
    rw [Fin.fin_one_eq_zero j]
    show xR 0 * -(Strip.wordXL xL (Fin.last 0)) = xR 0
    rw [Strip.wordXL_last]
    ring
  have e3 : Strip.wordRhoL ρL (ρR 0) = ρR := by
    funext j
    rw [Fin.fin_one_eq_zero j]
    exact Strip.wordRhoL_last ρL (ρR 0)
  rwa [e1, e2, e3] at h2

/-- **`Aux99StoppedStatement κ` from the seed theorem and the low weights** `ρ ≤ min(−2, κ/2 − 4)` (strip drift
`σ ≤ −1`), for every `κ > 0`; the weights `κ/2 − 4 < ρ ≤ −2` (only present for `κ < 4`) are
`isCompleteForceWord_oneRight_of_strip`. -/
theorem aux99StoppedStatement_of_seed_of_low (hκ : 0 < κ)
    (hseed : ∀ (xL ρL : Fin 0 → ℝ) (ρR : Fin 1 → ℝ), -2 < ρR 0 →
      LP.IsCompleteForceWord.{u} κ xL (fun _ => 0) ρL ρR)
    (hlow : ∀ (xL ρL : Fin 0 → ℝ) (xR ρR : Fin 1 → ℝ), 0 < xR 0 → ρR 0 ≤ -2 → ρR 0 ≤ κ / 2 - 4 →
      LP.IsCompleteForceWord.{u} κ xL xR ρL ρR) :
    Aux99StoppedStatement.{u} κ := by
  refine aux99StoppedStatement_of_seed_of_nonAdmissible hκ hseed fun xL ρL xR ρR hx hρ => ?_
  rcases le_or_gt (ρR 0) (κ / 2 - 4) with h | h
  · exact hlow xL ρL xR ρR hx hρ h
  · exact isCompleteForceWord_oneRight_of_strip hκ (by linarith) hx hρ h

end OneRight

end Sec7

end InteractingSLE
