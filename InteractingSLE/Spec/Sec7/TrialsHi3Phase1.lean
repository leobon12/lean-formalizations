/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.TrialsHi3Steer
import InteractingSLE.Spec.Sec7.TrialsHiCompare
import InteractingSLE.Stochastic.BrownianSupport
import InteractingSLE.Spec.Sec7.ContinuityProbBase

/-!
# The low-sector trial bound: the steering stage has uniformly positive probability

Packet PROVE-TRIALS-HI3. For any weights `ρ`, from every word with left marks `≤ −1` and right marks in `[1, M]`, the
canonical probability that the lifetime is at least `T` and the driver stays within `1/8` of `c t` at the rational
times before `T` (`steerSet`) is at least a constant `p > 0` independent of the word (`exists_steer_bound`).

Proof: run the zero-weight evolution (ordinary `SLE_κ`, driver `√κ B`, infinite lifetime) from the word. On the
Brownian tube `{|√κ B_t − c t| < 1/8 at rational t ≤ T}` the deterministic stage `steer_det` keeps every gap at least
`7/8` on `[0, T]`, so the energy of the change of weights `0 → ρ` is at most `m = κ⁻¹ T (8/7 Σ|ρ|)²`. The driver-form
comparison of Aux. lemma 108 (`TrialsHi.measure_horizonEvent_le`) gives `q² ≤ e^m codeLaw ρ (steerSet)`, where
`q = wienerPath(tube) > 0` (the support theorem for Brownian motion, `BrownianSupport.measure_forall_abs_sub_lt_pos`)
does not depend on the word.

## Main results

* `steerSet`, `tubeSet` and their measurability; `changeEnergy_le_of_gap`;
* **`exists_steer_bound`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace TrialsHi3

open Zhan Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart

variable {nL nR : ℕ}

/-! ### The code set and the tube -/

/-- **The steering code set**: lifetime at least `T` and the driver within `1/8` of `c t` at the rational times
before `T`. -/
def steerSet (c : ℝ) (T : ℝ≥0) : Set (XCode nL nR) :=
  {x | (T : ℝ≥0∞) ≤ cζ x ∧ ∀ r : ℚ≥0, (r : ℝ≥0) < T → |cw x r - c * r| ≤ 1 / 8}

theorem measurableSet_steerSet (c : ℝ) (T : ℝ≥0) : MeasurableSet (steerSet (nL := nL) (nR := nR) c T) := by
  have h1 : MeasurableSet {x : XCode nL nR | (T : ℝ≥0∞) ≤ cζ x} := measurableSet_le measurable_const measurable_cζ
  have h2 : ∀ r : ℚ≥0, MeasurableSet {x : XCode nL nR | (r : ℝ≥0) < T → |cw x r - c * r| ≤ 1 / 8} := fun r => by
    by_cases hr : (r : ℝ≥0) < T
    · simp only [hr, true_implies]
      exact measurableSet_le ((((measurable_pi_apply _).comp measurable_cw).sub measurable_const).abs)
        measurable_const
    · simp [hr]
  have e : steerSet (nL := nL) (nR := nR) c T =
      {x | (T : ℝ≥0∞) ≤ cζ x} ∩ ⋂ r : ℚ≥0, {x | (r : ℝ≥0) < T → |cw x r - c * r| ≤ 1 / 8} := by
    ext x; simp [steerSet]
  rw [e]
  exact h1.inter (MeasurableSet.iInter h2)

/-- **The Brownian tube**: `|√κ f(r) − c r| < 1/8` at the rational times `r ≤ T`. -/
def tubeSet (κ c : ℝ) (T : ℝ≥0) : Set (ℝ≥0 → ℝ) :=
  {f | ∀ r : ℚ≥0, (r : ℝ≥0) ≤ T → |Real.sqrt κ * f r - c * r| < 1 / 8}

theorem measurableSet_tubeSet (κ c : ℝ) (T : ℝ≥0) : MeasurableSet (tubeSet κ c T) := by
  have e : tubeSet κ c T = ⋂ r : ℚ≥0, {f : ℝ≥0 → ℝ | (r : ℝ≥0) ≤ T → |Real.sqrt κ * f r - c * r| < 1 / 8} := by
    ext f; simp [tubeSet]
  rw [e]
  refine MeasurableSet.iInter fun r => ?_
  by_cases hr : (r : ℝ≥0) ≤ T
  · simp only [hr, true_implies]
    exact measurableSet_lt ((((measurable_pi_apply _).const_mul _).sub measurable_const).abs) measurable_const
  · simp [hr]

/-- On the tube, a continuous path stays within `1/8` of the line on all of `[0, T]`. -/
theorem abs_le_of_mem_tubeSet {κ c : ℝ} {T : ℝ≥0} {f : ℝ≥0 → ℝ} (hf : Continuous f) (h : f ∈ tubeSet κ c T) :
    ∀ t ≤ T, |Real.sqrt κ * f t - c * t| ≤ 1 / 8 :=
  BrownianSupport.le_of_forall_nnrat_lt (φ := fun t => |Real.sqrt κ * f t - c * t|)
    ((continuous_const.mul hf).sub (continuous_const.mul NNReal.continuous_coe)).abs h

/-! ### The energy with gaps bounded below -/

/-- **The energy of a change of weights** with all gaps at least `δ` on `[0, T]` is at most
`κ⁻¹ T ((Σ|ρ' − ρ|)/δ)²`. -/
theorem changeEnergy_le_of_gap {κ : ℝ} (hκ : 0 < κ) {ρL ρL' : Fin nL → ℝ} {ρR ρR' : Fin nR → ℝ} {Ω : Type*}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {ω : Ω} {δ : ℝ}
    (hδ : 0 < δ) (hgap : ∀ s : ℝ≥0, s ≤ T → ∀ j, δ ≤ |W s ω - Girsanov.allMarks VL VR j s ω|) :
    Zhan.changeEnergy κ ρL ρL' ρR ρR' W VL VR T ω ≤
      1 / κ * (T * ((∑ j, |Sec2.weightDiff ρL ρL' ρR ρR' j|) / δ) ^ 2) := by
  set A := ∑ j, |Sec2.weightDiff ρL ρL' ρR ρR' j| with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hpt : ∀ s ∈ Icc (0 : ℝ) T, (∑ j, Sec2.weightDiff ρL ρL' ρR ρR' j /
      (W s.toNNReal ω - Girsanov.allMarks VL VR j s.toNNReal ω)) ^ 2 ≤ (A / δ) ^ 2 := by
    intro s hs
    have hsT : s.toNNReal ≤ T := by
      rw [← Real.toNNReal_coe (r := T)]; exact Real.toNNReal_le_toNNReal hs.2
    have hb : |∑ j, Sec2.weightDiff ρL ρL' ρR ρR' j / (W s.toNNReal ω - Girsanov.allMarks VL VR j s.toNNReal ω)| ≤
        A / δ := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [hA, Finset.sum_div]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [abs_div]
      have hg := hgap _ hsT j
      exact div_le_div_of_nonneg_left (abs_nonneg _) hδ hg
    have := sq_le_sq' (abs_le.1 hb).1 (abs_le.1 hb).2
    exact this
  unfold Zhan.changeEnergy
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  by_cases hi : IntervalIntegrable (fun s : ℝ => (∑ j, Sec2.weightDiff ρL ρL' ρR ρR' j /
      (W s.toNNReal ω - Girsanov.allMarks VL VR j s.toNNReal ω)) ^ 2) volume 0 T
  · calc ∫ s in (0 : ℝ)..(T : ℝ), (∑ j, Sec2.weightDiff ρL ρL' ρR ρR' j /
          (W s.toNNReal ω - Girsanov.allMarks VL VR j s.toNNReal ω)) ^ 2
        ≤ ∫ _s in (0 : ℝ)..(T : ℝ), (A / δ) ^ 2 :=
          intervalIntegral.integral_mono_on T.coe_nonneg hi intervalIntegrable_const hpt
      _ = T * (A / δ) ^ 2 := by simp
  · rw [intervalIntegral.integral_undef hi]
    positivity

/-! ### The uniform bound -/

/-- **The steering stage has a uniformly positive canonical probability.** -/
theorem exists_steer_bound {κ : ℝ} (hκ : 0 < κ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) {M ℓ₂ c : ℝ}
    {T : ℝ≥0} (hc : 0 < c) (hℓ₂ : 1 ≤ ℓ₂) (hcℓ : c ≤ 1 / (ℓ₂ + 1 / 8)) (hT : ℓ₂ ≤ c * T) :
    ∃ p : ℝ, 0 < p ∧ ∀ (yL : Fin (nL + 1) → ℝ) (yR : Fin (nR + 1) → ℝ), IsOrderedForceWord yL yR →
      (∀ i, yL i ≤ -1) → (∀ j, 1 ≤ yR j ∧ yR j ≤ M) →
      ENNReal.ofReal p ≤ codeLaw κ ρL ρR (steerSet c T) (yL, yR) := by
  set A := ∑ j, |Sec2.weightDiff (0 : Fin (nL + 1) → ℝ) ρL (0 : Fin (nR + 1) → ℝ) ρR j| with hAdef
  set m : ℝ := 1 / κ * (T * (A / (7 / 8)) ^ 2) with hmdef
  set q := wienerPath (tubeSet κ c T) with hqdef
  have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  -- the Brownian tube probability is the Wiener measure of the tube
  have htubeP : ∀ {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
      {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}, IsFilteredBrownianReal 𝓕 B P →
      P {ω | (fun s => B s ω) ∈ tubeSet κ c T} = q := fun {Ω mΩ P _ 𝓕 B} hB => by
    have hBm : ∀ t, Measurable (B t) := fun t => (hB.2.1 t).mono (𝓕.le t) le_rfl
    have hpath : Measurable fun ω (s : ℝ≥0) => B s ω := measurable_pi_iff.2 hBm
    have hmap := map_path_eq_wienerPath hB.1.toIsPreBrownianReal hpath
    rw [hqdef, ← hmap, Measure.map_apply hpath (measurableSet_tubeSet κ c T)]
    rfl
  -- `q > 0`
  have hq : 0 < q := by
    have hF0 : IsOrderedForceWord (fun _ : Fin (nL + 1) => (-1 : ℝ)) (fun _ : Fin (nR + 1) => (1 : ℝ)) :=
      ⟨antitone_const, fun _ => by norm_num, monotone_const, fun _ => by norm_num⟩
    obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ :=
      exists_isIntegratedSLEEvolution_assembled hκ hF0 (ρL := (0 : Fin (nL + 1) → ℝ)) (ρR := 0)
    have hBm : ∀ t, Measurable (B t) := fun t => (hE.1.2.1 t).mono (𝓕.le t) le_rfl
    have hpos := BrownianSupport.measure_forall_abs_sub_lt_pos hE.1.1 hBm (f := fun t => c / Real.sqrt κ * t)
      (by fun_prop) (by simp) T (ε := 1 / (8 * Real.sqrt κ)) (by positivity)
    rw [← htubeP hE.1]
    refine hpos.trans_le (measure_mono fun ω hω r hr => ?_)
    have h := hω r hr
    have e : Real.sqrt κ * B r ω - c * r = Real.sqrt κ * (B r ω - c / Real.sqrt κ * r) := by
      field_simp
    rw [e, abs_mul, abs_of_pos hsk]
    have : Real.sqrt κ * (1 / (8 * Real.sqrt κ)) = 1 / 8 := by field_simp
    calc Real.sqrt κ * |B r ω - c / Real.sqrt κ * r| < Real.sqrt κ * (1 / (8 * Real.sqrt κ)) :=
          mul_lt_mul_of_pos_left h hsk
      _ = 1 / 8 := this
  have hq1 : q ≤ 1 := prob_le_one
  have hqt : q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hq1
  have hqr : 0 < q.toReal := ENNReal.toReal_pos hq.ne' hqt
  refine ⟨q.toReal ^ 2 / Real.exp m, by positivity, fun yL yR hF hyL hyR => ?_⟩
  have hsep : ∀ i j, yL i < yR j := fun i j => by linarith [hyL i, (hyR j).1]
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ :=
    exists_isIntegratedSLEEvolution_assembled hκ hF (ρL := (0 : Fin (nL + 1) → ℝ)) (ρR := 0)
  have hE𝓖 := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  set Good : Ω → Prop := fun ω => ζ ω = ⊤ ∧ Continuous (fun s => Coupling.stateAt W VL VR s ω) ∧
    IsIntegratedSLEPath κ yL yR 0 0 (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
      (fun t => B t ω) (ζ ω) ∧ Continuous (fun t => B t ω) with hGood
  have hgood : ∀ᵐ ω ∂P, Good ω := by
    filter_upwards [hE.2.2.2.2, hE.1.1.cont] with ω hp hBc
    have hζω : ζ ω = ⊤ := hp.lifetime_eq_top_of_zero hBc
    refine ⟨hζω, ?_, hp, hBc⟩
    have hf := hp.isForcePath
    have hlt : ∀ t : ℝ≥0, t ∈ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun t => by
      show (t : ℝ≥0∞) < ζ ω; rw [hζω]; exact ENNReal.coe_lt_top
    have hw : Continuous fun t => W t ω := continuousOn_univ.1 (hf.continuousOn_w.mono fun t _ => hlt t)
    have hl : ∀ i, Continuous fun t => VL i t ω := fun i =>
      continuousOn_univ.1 ((hf.continuousOn_vL i).mono fun t _ => hlt t)
    have hr : ∀ j, Continuous fun t => VR j t ω := fun j =>
      continuousOn_univ.1 ((hf.continuousOn_vR j).mono fun t _ => hlt t)
    exact hw.prodMk ((continuous_pi hl).prodMk (continuous_pi hr))
  set N := {ω | ¬ Good ω} with hNdef
  have hN : P N = 0 := ae_iff.1 hgood
  set G := (toMeasurable P N)ᶜ with hGdef
  have hGm : MeasurableSet[usualAugmentation 𝓕 P 0] G :=
    (Ito.measurableSet_usualAugmentation_of_null (measurableSet_toMeasurable P N)
      (by rw [measure_toMeasurable]; exact hN) 0).compl
  have hGgood : ∀ ω ∈ G, Good ω := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable P N h)
  have hGc : P Gᶜ = 0 := by rw [hGdef, compl_compl, measure_toMeasurable]; exact hN
  set Φ : (ℝ≥0 → ℝ) → Prop := fun w => ∀ r : ℚ≥0, (r : ℝ≥0) < T → |w r - c * r| ≤ 1 / 8 with hΦdef
  have hΦ : ∀ w w' : ℝ≥0 → ℝ, (∀ r : ℝ≥0, r < T → w r = w' r) → Φ w → Φ w' := fun w w' h hw r hr => by
    rw [← h r hr]; exact hw r hr
  have hbound := TrialsHi.measure_horizonEvent_le hκ hF hsep hE𝓖 hGm (fun ω hω => (hGgood ω hω).1)
    (fun ω hω => (hGgood ω hω).2.1) (by norm_num : (0 : ℝ) < 7 / 8) T m hΦ
    (measurableSet_steerSet (nL := nL + 1) (nR := nR + 1) c T) (fun x _ hT hx => ⟨hT, hx⟩)
    (ρL' := ρL) (ρR' := ρR)
  -- the tube lies in the horizon event
  have hsub : G ∩ {ω | (fun s => B s ω) ∈ tubeSet κ c T} ⊆
      TrialsHi.horizonEvent κ 0 ρL 0 ρR G W VL VR (7 / 8) T m Φ := by
    rintro ω ⟨hωG, htube⟩
    obtain ⟨hζω, -, hp, hBc⟩ := hGgood ω hωG
    have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω := fun t => by rw [hζω]; exact ENNReal.coe_lt_top
    have hW : ∀ t, W t ω = Real.sqrt κ * B t ω := fun t => hp.w_eq_of_zero (hlt t)
    have htb := abs_le_of_mem_tubeSet hBc htube
    have htr : ∀ s ∈ Icc (0 : ℝ) T, |W s.toNNReal ω - c * s| ≤ 1 / 8 := fun s hs => by
      have hsT : s.toNNReal ≤ T := by
        rw [← Real.toNNReal_coe (r := T)]; exact Real.toNNReal_le_toNNReal hs.2
      have := htb _ hsT
      rwa [Real.coe_toNNReal _ hs.1, ← hW] at this
    obtain ⟨hR, hL, -, -, -⟩ := steer_det hp (hlt T) hyL hyR htr hc hℓ₂ hcℓ hT
    have hgapL : ∀ t : ℝ≥0, t ≤ T → ∀ i, 7 / 8 ≤ |W t ω - VL i t ω| := fun t ht i => by
      have := hL t ht i
      rw [abs_of_pos (by linarith)]; exact this
    have hgapR : ∀ t : ℝ≥0, t ≤ T → ∀ j, 7 / 8 ≤ |W t ω - VR j t ω| := fun t ht j => by
      have := hR t ht j
      rw [abs_sub_comm, abs_of_pos (by linarith)]; exact this
    refine ⟨hωG, fun s hs => ?_, ?_, fun r hr => ?_⟩
    · exact le_minGap_iff.2 ⟨by norm_num, hgapL s hs, hgapR s hs⟩
    · refine changeEnergy_le_of_gap hκ (by norm_num) fun s hs j => ?_
      refine Fin.addCases (motive := fun j => 7 / 8 ≤ |W s ω - Girsanov.allMarks VL VR j s ω|)
        (fun i => ?_) (fun j => ?_) j
      · simp only [Girsanov.allMarks, Fin.addCases_left]; exact hgapL s hs i
      · simp only [Girsanov.allMarks, Fin.addCases_right]; exact hgapR s hs j
    · have := htr (((r : ℝ≥0) : ℝ)) ⟨NNReal.coe_nonneg _, by exact_mod_cast hr.le⟩
      rw [Real.toNNReal_coe] at this
      exact_mod_cast this
  have hqle : q ≤ ENNReal.ofReal (Real.exp m) ^ (1 / 2 : ℝ) *
      codeLaw κ ρL ρR (steerSet c T) (yL, yR) ^ (1 / 2 : ℝ) := by
    rw [← htubeP hE.1, ← measure_inter_conull hGc, inter_comm]
    exact (measure_mono hsub).trans hbound
  have hsq : ∀ a : ℝ≥0∞, (a ^ (1 / 2 : ℝ)) ^ 2 = a := fun a => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hq2 : q ^ 2 ≤ ENNReal.ofReal (Real.exp m) * codeLaw κ ρL ρR (steerSet c T) (yL, yR) := by
    have := pow_le_pow_left₀ zero_le hqle 2
    rwa [mul_pow, hsq, hsq] at this
  have hem : 0 < Real.exp m := Real.exp_pos m
  have hkey : ENNReal.ofReal (Real.exp m) * ENNReal.ofReal (q.toReal ^ 2 / Real.exp m) = q ^ 2 := by
    rw [← ENNReal.ofReal_mul hem.le, mul_div_cancel₀ _ hem.ne', ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hqt]
  have hne0 : ENNReal.ofReal (Real.exp m) ≠ 0 := ENNReal.ofReal_ne_zero_iff.2 hem
  exact (ENNReal.mul_le_mul_iff_right hne0 ENNReal.ofReal_ne_top).1 (hkey ▸ hq2)

end TrialsHi3

end Sec7

end InteractingSLE
