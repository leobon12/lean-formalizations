/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.Prefix
import InteractingSLE.Spec.Zhan.TwoForceSeed

/-!
# Seed transience from the absence of a terminal cluster point at the seed, every `κ > 0`

Packet PROVE-ZHAN-GT4-B. Source: Astra, *Follow-up proofs and dependency audit*, §B.2 L1189–L1198 and §B.3 L1262–L1264
(ruling R38): "Let `Q_c` be the chordal terminal cluster set and `Z = inf{|z| : z ∈ Q_c ∖ {∞}}` … Compactness and
exclusion of zero give `Z > 0`. Scaling of the seed law gives `Z =d rZ` for every `r > 0`. For every finite `x > 0`,
`P[Z ≤ x] = P[Z ≤ x/r] → 0`. Thus `Z = ∞` almost surely." — "For the two-seed chordal law … The inverse-fibre argument
excludes zero from the original cluster set. The same scaling argument as for one force proves seed transience."
Also the additional note, Lemma 1.6 (`ig1_additional_proofs.txt` L419–L425, ruling R39).

For `κ ≤ 4`, PROVE-ZHAN-B2 proved seed transience from the stronger input `inf_{t ≥ 1} |η(t)| > 0`
(`Zhan.IsIntegratedSLEEvolution.ae_tendsto_norm_trace_twoSeed`). For `κ > 4` the trace is not simple, and the input the
source supplies is only that `0` is not a **terminal** cluster point: `∃ d > 0, |η(t)| ≥ d` for all large `t`
(`liminf_{t → ∞} |η(t)| > 0`). This file runs the scaling argument with that input, for every `κ > 0`, using the
liminf event `farSet r = ⋂_N nearSet r N` ("`|η(q)| < r` at arbitrarily large rational times") in place of
`nearSet r 1`. The seed trace for `κ > 4` is B.1 (`Prefix.lean`).

## Main results

* `farSet`, `measurableSet_farSet`, `mem_farSet_iff`.
* `IsIntegratedSLEEvolution.ae_tendsto_norm_trace_twoSeed_of_noCluster`: **two-seed transience from the absence of a
  terminal cluster point at the seed**, every `κ > 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4

open Zhan Sec7.Dilation

/-! ### The liminf event -/

/-- `|η(q)| < r` at arbitrarily large rational times (the trace read from the rational driver values). -/
def farSet (r : ℝ) : Set (ℚ≥0 → ℝ) := ⋂ N : ℕ, nearSet r (N : ℝ≥0)

theorem measurableSet_farSet (r : ℝ) : MeasurableSet (farSet r) :=
  MeasurableSet.iInter fun _ => measurableSet_nearSet r _

theorem farSet_mono {r r' : ℝ} (h : r ≤ r') : farSet r ⊆ farSet r' :=
  iInter_mono fun _ => nearSet_mono h _

theorem mem_farSet_iff {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ⊤ η) {r : ℝ} :
    (fun q : ℚ≥0 => w q) ∈ farSet r ↔ ∀ N : ℕ, ∃ q : ℚ≥0, (N : ℝ≥0) ≤ (q : ℝ≥0) ∧ ‖η q‖ < r := by
  simp only [farSet, mem_iInter, mem_nearSet_iff hw hw0 hη]

/-! ### Transience -/

section Transience

variable {κ : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {ρL ρR : Fin 1 → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin 1 → ℝ≥0 → Ω → ℝ} {VR : Fin 1 → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Two-seed transience from the absence of a terminal cluster point at the seed** (every `κ > 0`; B.2 L1189–L1198,
B.3 L1262–L1264, additional note Lemma 1.6). For an integrated `SLE_κ(ρ_L; ρ_R)` evolution with seed forces at `0⁻`,
`0⁺` and admissible weights, if almost surely `0` is not a terminal cluster point of the trace (`|η(t)| ≥ d > 0` for
all large `t`), then almost surely every continuous generating trace on `[0, ∞)` tends to `∞`. -/
theorem IsIntegratedSLEEvolution.ae_tendsto_norm_trace_twoSeed_of_noCluster (hκ : 0 < κ)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR (fun _ => 0) (fun _ => 0))
    (hE : IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P 𝓕 W VL VR B ζ)
    (hno : ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      ∃ d > (0 : ℝ), ∀ᶠ t in atTop, d ≤ ‖η t‖) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      Tendsto (fun t => ‖η t‖) atTop atTop := by
  have : IsProbabilityMeasure P := hE.1.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hF := isOrderedForceWord_zero
  have hρL : -2 < ρL 0 := by
    have h := hadm.1 (-1) (by norm_num) ⟨0, by norm_num⟩
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.filter_true_of_mem,
      Finset.mem_singleton, forall_eq, Finset.sum_singleton, show (-1 : ℝ) < 0 by norm_num] at h
    linarith
  have hρR : -2 < ρR 0 := by
    have h := hadm.2 0 le_rfl ⟨0, le_rfl⟩
    simp only [Finset.univ_unique, Fin.default_eq_zero, le_refl, Finset.filter_true_of_mem,
      Finset.mem_singleton, forall_eq, Finset.sum_singleton] at h
    linarith
  have h6 := Sec4.aux6Statement hκ _ _ ρL ρR P 𝓕 W VL VR B ζ hF hadm hE
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := h6.mono fun _ h => h.1
  set X := ratProc ζ W with hX
  have hXm : Measurable X := measurable_ratProc hE.2.1
  -- the dilated evolutions have the same law of rational-time values
  have hlaw : ∀ c : ℝ≥0, c ≠ 0 → P.map (ratProc (fun ω => ζ ω / c) (dilProc c W)) = P.map X :=
    fun c hc => map_ratProc_eq_twoSeed hκ hρL hρR (hE.dilate_zero hc) hE
      (hζ.mono fun ω h => by simp only [h]; exact ENNReal.top_div_of_ne_top ENNReal.coe_ne_top) hζ
  -- the good event
  have hgood : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧
      ∃ ηs : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ ηs ∧
        ∃ d > (0 : ℝ), ∀ᶠ t in atTop, d ≤ ‖ηs t‖ := by
    filter_upwards [IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_top_of_admissible hκ hF hadm hE,
      hno, hE.2.2.2.2] with ω ⟨hζω, _, ηs, hηs⟩ hnoω hp
    have hwc : Continuous fun t => W t ω := by
      have h := hp.2.2.2.1
      rw [hζω] at h
      exact continuousOn_univ.1 (h.mono fun t _ => ENNReal.coe_lt_top)
    exact ⟨hζω, hwc, hp.1, ηs, hηs, hnoω ηs hηs⟩
  -- `μ(farSet r) → 0` as `r → 0`
  have hsmall : Tendsto (fun n : ℕ => P (X ⁻¹' farSet (1 / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
    have hanti : Antitone fun n : ℕ => X ⁻¹' farSet (1 / ((n : ℝ) + 1)) := fun n m hnm =>
      preimage_mono (farSet_mono (one_div_le_one_div_of_le (by positivity)
        (by exact_mod_cast Nat.add_le_add_right hnm 1)))
    have hlim := tendsto_measure_iInter_atTop (μ := P)
      (fun n => (hXm (measurableSet_farSet _)).nullMeasurableSet) hanti
      ⟨0, measure_ne_top _ _⟩
    have h0 : P (⋂ n : ℕ, X ⁻¹' farSet (1 / ((n : ℝ) + 1))) = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hgood] with ω ⟨hζω, hwc, hw0, ηs, hηs, d, hd, hbd⟩ hmem
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hd
      obtain ⟨T, hT⟩ := eventually_atTop.1 hbd
      obtain ⟨N, hN⟩ := exists_nat_ge (T : ℝ)
      have h1 := mem_iInter.1 hmem n
      rw [mem_preimage, hX, ratProc_of_eq_top hζω, mem_farSet_iff hwc hw0 hηs] at h1
      obtain ⟨q, hqN, hqn⟩ := h1 N
      have hTq : T ≤ (q : ℝ≥0) := by
        rw [← NNReal.coe_le_coe]; exact hN.trans (by exact_mod_cast hqN)
      linarith [hT _ hTq]
    rwa [h0] at hlim
  -- for each level `m`, the trace eventually stays outside the disk of radius `m`
  have hm : ∀ m : ℕ, ∀ᵐ ω ∂P, ∃ T : ℝ≥0, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      ∀ t : ℝ≥0, T ≤ t → (m : ℝ) ≤ ‖η t‖ := by
    intro m
    rw [ae_iff]
    refine le_antisymm (ge_of_tendsto' hsmall fun n => ?_) bot_le
    set k : ℕ := (n + 1) * (m + 1) with hk
    set c : ℝ≥0 := ((k : ℝ≥0) + 1) ^ 2 with hc
    have hc0 : c ≠ 0 := by positivity
    have hsc : √(c : ℝ) = (k : ℝ) + 1 := by
      rw [hc]
      push_cast
      exact Real.sqrt_sq (by positivity)
    set Xc := ratProc (fun ω => ζ ω / c) (dilProc c W) with hXc
    have hXcm : Measurable Xc := measurable_ratProc (hE.dilate_zero hc0).2.1
    have hr : (m : ℝ) / ((k : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity), hk]
      push_cast
      nlinarith
    refine (measure_mono_ae (t := Xc ⁻¹' farSet ((m : ℝ) / ((k : ℝ) + 1))) ?_).trans ?_
    · filter_upwards [hgood] with ω ⟨hζω, hwc, hw0, ηs, hηs, _⟩ hbad
      have hb : ¬∃ T : ℝ≥0, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
          ∀ t : ℝ≥0, T ≤ t → (m : ℝ) ≤ ‖η t‖ := hbad
      push Not at hb
      have hdil := hηs.dilate hc0
      rw [ENNReal.top_div_of_ne_top ENNReal.coe_ne_top] at hdil
      have hdc : Continuous (dilPath c fun t => W t ω) :=
        continuous_const.mul (hwc.comp (continuous_const.mul continuous_id))
      have hd0 : dilPath c (fun t => W t ω) 0 = 0 := by simp [dilPath, hw0]
      have hXcω : Xc ω = fun q : ℚ≥0 => dilPath c (fun t => W t ω) q := by
        rw [hXc, ratProc_of_eq_top (ζ := fun ω => ζ ω / c) (W := dilProc c W) (ω := ω) (show ζ ω / c = ⊤ by
          rw [hζω]; exact ENNReal.top_div_of_ne_top ENNReal.coe_ne_top)]
        rfl
      rw [mem_preimage, hXcω, mem_farSet_iff hdc hd0 hdil]
      intro N
      obtain ⟨η, hη, t, ht, hlt⟩ := hb (c * N)
      rw [hη.eq_of_le hηs hwc.continuousOn hw0 le_top] at hlt
      have hηc : Continuous fun s : ℝ≥0 => (((√(c : ℝ))⁻¹ : ℝ) : ℂ) * ηs (c * s) :=
        continuousOn_univ.1 (hdil.2.1.mono fun s _ => show (s : ℝ≥0∞) ≤ ⊤ from le_top)
      refine exists_rat_of_norm_lt hηc (t := t / c) ?_ ?_
      · rw [le_div_iff₀ (pos_iff_ne_zero.2 hc0), mul_comm]
        exact ht
      · have hct : c * (t / c) = t := by rw [mul_comm, div_mul_cancel₀ t hc0]
        show ‖(((√(c : ℝ))⁻¹ : ℝ) : ℂ) * ηs (c * (t / c))‖ < (m : ℝ) / ((k : ℝ) + 1)
        rw [hct, norm_mul, Complex.norm_of_nonneg (by positivity), hsc, inv_mul_eq_div]
        exact div_lt_div_of_pos_right hlt (by positivity)
    · rw [← Measure.map_apply hXcm (measurableSet_farSet _), hlaw c hc0,
        Measure.map_apply hXm (measurableSet_farSet _)]
      exact measure_mono (preimage_mono (farSet_mono hr))
  filter_upwards [ae_all_iff.2 hm] with ω hω η hη
  refine tendsto_atTop.2 fun b => ?_
  obtain ⟨T, hT⟩ := hω ⌈b⌉₊
  exact eventually_atTop.2 ⟨T, fun t ht => (Nat.le_ceil b).trans (hT η hη t ht)⟩

end Transience

end InteractingSLE.ZhanGT4
