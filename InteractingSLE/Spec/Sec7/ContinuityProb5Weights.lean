/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProb5Girsanov

/-!
# Whole-tail changes of weights of separated marks

Packet PROVE-SEC7-C5. The whole-tail versions of the Girsanov steps of `Spec/Sec2/GirsanovCut`,
`Spec/Sec2/GirsanovSLE` and `Spec/Sec2/AddMarksGirsanov`: the stopping time `τ` before which the changed marks stay
`δ`-far from the driver need not be bounded; instead the energy of the change of drift is bounded,
`∫₀^τ θ² ≤ K` almost surely (Specification §7.3, Aux. lemma 101, p. 348: "Stop additionally when the angular clock
reaches `m` […] the two entire stopped driving laws are equivalent, also at an infinite terminal physical time";
Aux. lemma 106, p. 354: "On the final infinite band, deleting the opposite mark has finite energy"). The measure is
the whole-tail Girsanov measure `girsanovMeasureTail` of `ContinuityProb5Girsanov.lean`.

* `quadInt_cutDrift_le`: the energy of the cut drift is that of the uncut one before `τ`;
* `girsanov_cutDrift_tail`, `girsanov_shift_drift_tail`;
* **`Sec2.IsSLEEvolutionUpTo.girsanov_changeWeights_tail`**: under `Q_∞`, the processes with the Brownian motion
  `B̃ = B + ∫ θ` are a local evolution of the force word with the new weights before `τ`.

The proofs of the last two are those of `girsanov_shift_drift` and `girsanov_changeWeights`, with
`girsanov_cutDrift_tail` in place of `girsanov_cutDrift`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {m : ℕ}
  {τ ζ : Ω → ℝ≥0∞} {W B : ℝ≥0 → Ω → ℝ} {U : Fin m → ℝ≥0 → Ω → ℝ} {F : ℝ → (Fin m → ℝ) → ℝ}

/-- **The energy of the cut drift** is the energy of the uncut drift up to `τ`. -/
theorem quadInt_cutDrift_le (hF : Continuous fun p : ℝ × (Fin m → ℝ) => F p.1 p.2) {M : ℝ}
    (hFb : ∀ w u, |F w u| ≤ M) (hθ : IsStronglyProgressive 𝓕 (cutDrift τ ζ F W U)) {ω : Ω}
    (hτζ : τ ω ≤ ζ ω) (hWc : ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hUc : ∀ j, ContinuousOn (fun s => U j s ω) {s | (s : ℝ≥0∞) < ζ ω}) {K : ℝ}
    (hK : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ τ ω →
      ∫ s in (0 : ℝ)..(t : ℝ), F (W s.toNNReal ω) (fun j => U j s.toNNReal ω) ^ 2 ≤ K)
    (t : ℝ≥0) : quadInt (cutDrift τ ζ F W U) t ω ≤ K := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun u : ℝ => cutDrift τ ζ F W U u.toNNReal ω ^ 2)
      volume a b := fun a b =>
    (intervalIntegrable_const (c := M ^ 2)).mono_fun'
      ((measurable_time_of_progressive hθ ω).pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun u => by
        show ‖cutDrift τ ζ F W U u.toNNReal ω ^ 2‖ ≤ M ^ 2
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_cutDrift_le hFb _ _) 2)
  by_cases ht : (t : ℝ≥0∞) ≤ τ ω
  · rw [quadInt, integral_comp_cutDrift_eq hF (fun x => x ^ 2) hτζ hWc hUc ht]
    exact hK t ht
  · rw [not_le] at ht
    obtain ⟨τ', hτ'⟩ : ∃ τ' : ℝ≥0, τ ω = τ' :=
      ⟨(τ ω).toNNReal, (ENNReal.coe_toNNReal (ht.trans ENNReal.coe_lt_top).ne).symm⟩
    have hτ't : τ' ≤ t := by rw [hτ'] at ht; exact_mod_cast ht.le
    rw [quadInt, ← intervalIntegral.integral_add_adjacent_intervals (hint 0 τ') (hint τ' t)]
    have h0 : ∫ u in (τ' : ℝ)..(t : ℝ), cutDrift τ ζ F W U u.toNNReal ω ^ 2 = 0 := by
      refine (intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ)) ?_).trans
        intervalIntegral.integral_zero
      filter_upwards [ae_ne_real (τ' : ℝ)] with u _ hmem
      rw [uIoc_of_le (by exact_mod_cast hτ't)] at hmem
      have hlt : τ ω < (u.toNNReal : ℝ≥0∞) := by
        rw [hτ', ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal _
          ((NNReal.coe_nonneg τ').trans hmem.1.le)]
        exact hmem.1
      rw [cutDrift_eq_zero hlt]
      ring
    rw [h0, add_zero]
    have h := hK τ' (le_of_eq hτ'.symm)
    rw [← integral_comp_cutDrift_eq hF (fun x => x ^ 2) hτζ hWc hUc (le_of_eq hτ'.symm)] at h
    exact h

/-- **Girsanov for a cut drift on the whole time line** (bounded energy before `τ`). -/
theorem girsanov_cutDrift_tail [IsProbabilityMeasure P] (hBF : IsFilteredBrownianReal 𝓕 B P)
    (hF : Continuous fun p : ℝ × (Fin m → ℝ) => F p.1 p.2) {M : ℝ} (hFb : ∀ w u, |F w u| ≤ M)
    (hW : AdaptedBefore 𝓕 ζ W) (hU : ∀ j, AdaptedBefore 𝓕 ζ (U j))
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ ω ≤ s}) (hτζ : ∀ ω, τ ω ≤ ζ ω)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω} ∧
      ∀ j, ContinuousOn (fun s => U j s ω) {s | (s : ℝ≥0∞) < ζ ω}) {K : ℝ}
    (hK : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ τ ω →
      ∫ s in (0 : ℝ)..(t : ℝ), F (W s.toNNReal ω) (fun j => U j s.toNNReal ω) ^ 2 ≤ K) :
    MathFin.IsEquivProbMeasure P (girsanovMeasureTail P 𝓕 B (cutDrift τ ζ F W U)) ∧
    IsFilteredBrownianReal 𝓕 (girsanovProcess B (cutDrift τ ζ F W U))
      (girsanovMeasureTail P 𝓕 B (cutDrift τ ζ F W U)) ∧
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ τ ω →
      girsanovProcess B (cutDrift τ ζ F W U) t ω
        = B t ω + ∫ s in (0 : ℝ)..(t : ℝ), F (W s.toNNReal ω) (fun j => U j s.toNNReal ω) := by
  have hθ := isStronglyProgressive_cutDrift hF hW hU hτ
  have hθb := abs_cutDrift_le (τ := τ) (ζ := ζ) (W := W) (U := U) hFb
  have hθreg := isRiemannRegular_cutDrift (P := P) hF hτζ hcont
  have hK' : ∀ᵐ ω ∂P, ∀ t, quadInt (cutDrift τ ζ F W U) t ω ≤ K := by
    filter_upwards [hcont, hK] with ω ⟨hWc, hUc⟩ hKω t
    exact quadInt_cutDrift_le hF hFb hθ (hτζ ω) hWc hUc hKω t
  obtain ⟨h1, h2⟩ := isFilteredBrownianReal_girsanovTail hBF hθ hθb hθreg hK'
  refine ⟨h1, h2, ?_⟩
  filter_upwards [hcont] with ω ⟨hWc, hUc⟩ t ht
  rw [girsanovProcess, drift_cutDrift_eq hF (hτζ ω) hWc hUc ht]

/-- **The change of drift on the whole time line** (`girsanov_shift_drift` without a bound on `τ`, with a bounded
energy of the cut integrand before `τ`). -/
theorem girsanov_shift_drift_tail [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ) (ε : ℝ) {δ : ℝ}
    (hδ : 0 < δ) (σ : Fin m → ℝ) (hBF : IsFilteredBrownianReal 𝓕 B P)
    (hW : AdaptedBefore 𝓕 ζ W) (hU : ∀ j, AdaptedBefore 𝓕 ζ (U j))
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ ω ≤ s}) (hτζ : ∀ ω, τ ω ≤ ζ ω)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω} ∧
      ∀ j, ContinuousOn (fun s => U j s ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hgap : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω → ∀ j, σ j ≠ 0 → δ ≤ |W t ω - U j t ω|) {K : ℝ}
    (hK : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ τ ω →
      ∫ s in (0 : ℝ)..(t : ℝ), shiftIntegrand κ ε δ σ (W s.toNNReal ω) (fun j => U j s.toNNReal ω) ^ 2
        ≤ K) :
    MathFin.IsEquivProbMeasure P (girsanovMeasureTail P 𝓕 B (shiftDrift κ ε δ σ τ ζ W U)) ∧
    IsFilteredBrownianReal 𝓕 (girsanovProcess B (shiftDrift κ ε δ σ τ ζ W U))
      (girsanovMeasureTail P 𝓕 B (shiftDrift κ ε δ σ τ ζ W U)) ∧
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ τ ω →
      (∀ j, IntervalIntegrable (fun s : ℝ => σ j / (W s.toNNReal ω - U j s.toNNReal ω)) volume 0 t) ∧
      Real.sqrt κ * girsanovProcess B (shiftDrift κ ε δ σ τ ζ W U) t ω
        = Real.sqrt κ * B t ω
          - ε * ∑ j, ∫ s in (0 : ℝ)..(t : ℝ), σ j / (W s.toNNReal ω - U j s.toNNReal ω) := by
  have hF : Continuous fun p : ℝ × (Fin m → ℝ) => shiftIntegrand κ ε δ σ p.1 p.2 :=
    continuous_const.mul (continuous_addedDriftCut σ hδ)
  have hFb : ∀ w u, |shiftIntegrand κ ε δ σ w u| ≤ |ε / Real.sqrt κ| * ((∑ j, |σ j|) * δ⁻¹) :=
    fun w u => by
      rw [shiftIntegrand, abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left (abs_addedDriftCut_le σ hδ w u) (abs_nonneg _)
  obtain ⟨h1, h2, h3⟩ := girsanov_cutDrift_tail (P := P) hBF hF hFb hW hU hτ hτζ hcont hK
  refine ⟨h1, h2, ?_⟩
  filter_upwards [h3, hcont, hgap] with ω h3ω ⟨hWc, hUc⟩ hgω t ht
  -- each cut term is integrable and equals the uncut term a.e. on `[0, t]`
  have hterm : ∀ j, IntervalIntegrable
      (fun s : ℝ => σ j * recipCut δ (W s.toNNReal ω - U j s.toNNReal ω)) volume 0 t := fun j =>
    intervalIntegrable_comp_of_le (G := fun w u => σ j * recipCut δ (w - u j))
      (M := |σ j| * δ⁻¹)
      (continuous_const.mul ((continuous_recipCut hδ).comp
        (continuous_fst.sub ((continuous_apply j).comp continuous_snd))))
      (fun w u => by
        show |σ j * recipCut δ (w - u j)| ≤ |σ j| * δ⁻¹
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_recipCut_le hδ _) (abs_nonneg _))
      hW hU hτ (hτζ ω) hWc hUc ht
  have hae : ∀ j, ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.uIoc 0 (t : ℝ) →
      σ j * recipCut δ (W s.toNNReal ω - U j s.toNNReal ω)
        = σ j / (W s.toNNReal ω - U j s.toNNReal ω) := fun j => by
    filter_upwards [ae_ne_real (t : ℝ)] with s hst hs
    rw [Set.uIoc_of_le (NNReal.coe_nonneg t)] at hs
    have hlt : (s.toNNReal : ℝ≥0∞) < τ ω := by
      refine lt_of_lt_of_le ?_ ht
      rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs.1.le]
      exact lt_of_le_of_ne hs.2 hst
    by_cases hσ : σ j = 0
    · simp [hσ]
    · rw [recipCut_of_le hδ (hgω _ hlt j hσ), div_eq_mul_inv]
  have hint : ∀ j, IntervalIntegrable (fun s : ℝ => σ j / (W s.toNNReal ω - U j s.toNNReal ω))
      volume 0 t := fun j => by
    have := hterm j
    rw [intervalIntegrable_iff] at this ⊢
    refine this.congr_fun_ae ?_
    rw [EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    exact hae j
  refine ⟨hint, ?_⟩
  rw [show shiftDrift κ ε δ σ τ ζ W U = cutDrift τ ζ (shiftIntegrand κ ε δ σ) W U from rfl,
    h3ω t ht]
  have hsum : ∫ s in (0 : ℝ)..(t : ℝ), shiftIntegrand κ ε δ σ (W s.toNNReal ω)
      (fun j => U j s.toNNReal ω)
      = -(ε / Real.sqrt κ) * ∑ j, ∫ s in (0 : ℝ)..(t : ℝ), σ j / (W s.toNNReal ω - U j s.toNNReal ω) := by
    simp only [shiftIntegrand, addedDriftCut]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum
      fun j _ => hterm j]
    congr 1
    refine Finset.sum_congr rfl fun j _ => intervalIntegral.integral_congr_ae (hae j)
  rw [hsum]
  have hk : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  field_simp
  ring

end Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {τ ζ : Ω → ℝ≥0∞}
  {W B : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}

open Sec2 Girsanov in
/-- **The whole-tail change of weights of separated marks** (`girsanov_changeWeights` without a bound on `τ`).
Let `(W, V, B)` be a local evolution of `(xL; xR)`, `(ρL; ρR)` before `ζ`, `(ρL'; ρR')` new weights, and `τ ≤ ζ` a
stopping time before which every mark whose weight changes stays at distance `≥ δ > 0` from `W`. If the energy of the
change of drift before `τ` is at most `K` almost surely, then under the whole-tail Girsanov measure `Q_∞` (equivalent
to `P`), `(W, V, B̃)` is a local evolution of the force word with the new weights before `τ`. -/
theorem Sec2.IsSLEEvolutionUpTo.girsanov_changeWeights_tail [IsProbabilityMeasure P] {κ : ℝ}
    (hκ : 0 < κ) (hE : IsSLEEvolutionUpTo κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (ρL' : Fin nL → ℝ)
    (ρR' : Fin nR → ℝ) (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ ω ≤ s})
    (hτζ : ∀ ω, τ ω ≤ ζ ω) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω →
      (∀ i, ρL' i ≠ ρL i → δ ≤ |W t ω - VL i t ω|) ∧
        ∀ i, ρR' i ≠ ρR i → δ ≤ |W t ω - VR i t ω|) {K : ℝ}
    (hK : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ τ ω →
      ∫ s in (0 : ℝ)..(t : ℝ), shiftIntegrand κ 1 δ (weightDiff ρL ρL' ρR ρR') (W s.toNNReal ω)
        (fun k => allMarks VL VR k s.toNNReal ω) ^ 2 ≤ K) :
    MathFin.IsEquivProbMeasure P
      (girsanovMeasureTail P 𝓕 B (weightDrift κ δ ρL ρL' ρR ρR' τ ζ W VL VR)) ∧
    IsSLEEvolutionUpTo κ xL xR ρL' ρR'
      (girsanovMeasureTail P 𝓕 B (weightDrift κ δ ρL ρL' ρR ρR' τ ζ W VL VR)) 𝓕 W VL VR
      (girsanovProcess B (weightDrift κ δ ρL ρL' ρR ρR' τ ζ W VL VR)) τ := by
  have hU := allMarks_adaptedBefore hE.adapted_VL hE.adapted_VR
  have hcont : ∀ᵐ ω ∂P, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω} ∧
      ∀ k, ContinuousOn (fun s => allMarks VL VR k s ω) {s | (s : ℝ≥0∞) < ζ ω} := by
    filter_upwards [hE.ae_path] with ω hp
    refine ⟨hp.continuousOn_w, fun k => ?_⟩
    cases k using Fin.addCases with
    | left i => simpa [allMarks] using hp.continuousOn_vL i
    | right i => simpa [allMarks] using hp.continuousOn_vR i
  have hgap' : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω → ∀ k,
      weightDiff ρL ρL' ρR ρR' k ≠ 0 → δ ≤ |W t ω - allMarks VL VR k t ω| := by
    filter_upwards [hgap] with ω hg t ht k hk
    cases k using Fin.addCases with
    | left i =>
      simp only [weightDiff, allMarks, Fin.addCases_left] at hk ⊢
      exact (hg t ht).1 i (sub_ne_zero.1 hk)
    | right i =>
      simp only [weightDiff, allMarks, Fin.addCases_right] at hk ⊢
      exact (hg t ht).2 i (sub_ne_zero.1 hk)
  obtain ⟨h1, h2, h3⟩ := girsanov_shift_drift_tail (P := P) hκ 1 hδ (weightDiff ρL ρL' ρR ρR')
    hE.brownian hE.adapted_W hU hτ hτζ hcont hgap' hK
  refine ⟨h1, ⟨h2, hE.adapted_W.of_le hτ hτζ, fun i => (hE.adapted_VL i).of_le hτ hτζ,
    fun i => (hE.adapted_VR i).of_le hτ hτζ, h1.ac.ae_le ?_⟩⟩
  filter_upwards [h3, hE.ae_path, hgap] with ω h3ω hp hg
  refine (hp.mono (hτζ ω)).changeWeights ρL' ρR' ?_ ?_ ?_
  · intro t ht i hi he
    have := (hg t ht).1 i hi
    rw [he, sub_self, abs_zero] at this
    exact absurd this (not_le.2 hδ)
  · intro t ht i hi he
    have := (hg t ht).2 i hi
    rw [he, sub_self, abs_zero] at this
    exact absurd this (not_le.2 hδ)
  · intro t ht
    obtain ⟨-, hB⟩ := h3ω t ht.le
    rw [sum_weightDiff_integral] at hB
    simp only [sum_integral_div_eq] at hB ⊢
    have eL : ∑ i, (ρL i - ρL' i) * ∫ s in (0 : ℝ)..(t : ℝ), (W s.toNNReal ω - VL i s.toNNReal ω)⁻¹
        = -∑ i, (ρL' i - ρL i) * ∫ s in (0 : ℝ)..(t : ℝ), (W s.toNNReal ω - VL i s.toNNReal ω)⁻¹ := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have eR : ∑ i, (ρR i - ρR' i) * ∫ s in (0 : ℝ)..(t : ℝ), (W s.toNNReal ω - VR i s.toNNReal ω)⁻¹
        = -∑ i, (ρR' i - ρR i) * ∫ s in (0 : ℝ)..(t : ℝ), (W s.toNNReal ω - VR i s.toNNReal ω)⁻¹ := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [eL, eR]
    unfold weightDrift
    linarith

end InteractingSLE
