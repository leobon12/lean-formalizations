/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedInstBrownian
import InteractingSLE.Spec.ZhanGT4.DualSeedInstMart

/-!
# Measurable boundary source versions on the protected prefix

Packet PROVE-ZHAN-GT4-A22. Evaluate the existing adapted interior Loewner
map and take its holomorphic boundary limit on the alive event. The force
coordinate can be set to zero after the stop without making a global flow claim.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace InteractingSLE.ZhanGT4
open QuantumZipper (IsForwardSol fwdMap)
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The adapted interior-map API also applies to an arbitrary continuous
adapted driver, with its specified nonnegative-time extension. -/
theorem measurable_fwdMap_of_adapted {𝓕 : Filtration ℝ≥0 mΩ}
    {X : ℝ≥0 → Ω → ℝ} (hXm : Adapted 𝓕 X) (hXc : ∀ ω, Continuous (X · ω))
    (t : ℝ≥0) {z : ℂ} (hz : 0 < z.im) :
    Measurable[𝓕 t] fun ω => fwdMap (fun u => X u.toNNReal ω) t z := by
  classical
  have hAd : AdaptedBefore 𝓕 (fun _ => (⊤ : ℝ≥0∞)) X := by
    intro u A hA
    have he : {ω | (u : ℝ≥0∞) < ⊤ ∧ X u ω ∈ A} = X u ⁻¹' A := by
      ext ω; simp only [mem_ofPred_eq, ENNReal.coe_lt_top, true_and, mem_preimage]
    rw [he]
    exact hXm u hA
  have hm := Ito.measurable_fwdMap_alive hAd
    (fun ω _ => (hXc ω).continuousOn) MeasurableSet.univ hz t
  convert hm using 1
  funext ω
  split_ifs with hh
  · rfl
  · have ha : ¬ ∃ q, IsForwardSol (fun u => X u.toNNReal ω) z t q := by
      intro hq
      exact hh ⟨mem_univ ω, ENNReal.coe_lt_top, hq⟩
    simp only [QuantumZipper.fwdMap, ha, ↓reduceDIte]

/-- An alive real access is a measurable boundary limit on any measurable
event. Interior approximants may be dead away from that event. -/
theorem measurable_indicator_fwdMap_real_of_alive {W : Ω → ℝ → ℝ} {t p : ℝ} {G : Set Ω}
    (ht : 0 ≤ t) (hG : MeasurableSet G) (hW : ∀ ω ∈ G, Continuous (W ω))
    (hq : ∀ ω ∈ G, ∃ q, IsForwardSol (W ω) (p : ℂ) t q)
    (hm : ∀ z : ℂ, 0 < z.im → Measurable fun ω => fwdMap (W ω) t z) :
    Measurable (G.indicator fun ω => fwdMap (W ω) t p) := by
  refine measurable_of_tendsto_metrizable (f := fun n =>
    G.indicator fun ω => fwdMap (W ω) t ((p : ℂ) + stepC n * I)) (fun n => ?_) ?_
  · apply (hm _ ?_).indicator hG
    simp only [add_im, ofReal_im, mul_im, stepC, ofReal_re, I_im, mul_one,
      ofReal_im, I_re, mul_zero, add_zero, zero_add]
    positivity
  · rw [tendsto_pi_nhds]
    intro ω
    by_cases hω : ω ∈ G
    · obtain ⟨q, hq'⟩ := hq ω hω
      obtain ⟨δ, hδ, hl, hp⟩ := exists_aliveDisc_self hq' ht
      have hc := (hasDerivAt_fwdMap_aliveDisc (hW ω hω) hq' hδ hl hp ⟨ht, le_rfl⟩).continuousAt
      have hlim : Tendsto (fun n => (p : ℂ) + stepC n * I) atTop (𝓝 (p : ℂ)) := by
        simpa only [zero_mul, add_zero] using tendsto_const_nhds.add (tendsto_stepC.mul_const I)
      simp only [indicator_of_mem hω]
      exact hc.tendsto.comp hlim
    · simpa only [indicator_of_notMem hω] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))

/-- A real source coordinate with an explicit zero version after the stop. -/
def seedPrefixSource (W : Ω → ℝ → ℝ) (p : ℝ) (T : Ω → ℝ≥0) (ω : Ω) (u : ℝ) : ℝ :=
  if u ≤ T ω then (frzChart (W ω) u 0).re - p else 0

/-- Only the alive protected prefix is needed for measurability of the
source version; no boundary flow after the stop is assumed. -/
theorem measurable_seedPrefixSource {𝓕 : Filtration ℝ≥0 mΩ}
    {X : ℝ≥0 → Ω → ℝ} (hXm : Adapted 𝓕 X) (hXc : ∀ ω, Continuous (X · ω))
    {T : Ω → ℝ≥0} (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0))
    (hq : ∀ ω, ∃ q, IsForwardSol (fun u => X u.toNNReal ω) (0 : ℂ) (T ω) q)
    (p : ℝ) (u : ℝ≥0) :
    Measurable[𝓕 u] fun ω => seedPrefixSource (fun ω t => X t.toNNReal ω) p T ω u := by
  let G := {ω | (u : ℝ) ≤ T ω}
  have hG : MeasurableSet[𝓕 u] G := by
    have hh := measurableSet_ge_of_isStoppingTime hT u
    simpa only [G, WithTop.coe_le_coe, NNReal.coe_le_coe] using hh
  have hm := @measurable_indicator_fwdMap_real_of_alive Ω (𝓕 u)
    (fun ω t => X t.toNNReal ω) (u : ℝ) 0 G u.coe_nonneg hG
    (fun ω _ => (hXc ω).comp continuous_real_toNNReal)
    (fun ω hω => by
      obtain ⟨q, hh⟩ := hq ω
      exact ⟨q, isForwardSol_restrict hh hω⟩)
    (fun z hz => measurable_fwdMap_of_adapted hXm hXc u hz)
  have hmr := Complex.measurable_re.comp hm
  have hdrv : Measurable[𝓕 u] (G.indicator (X u)) := (hXm u).indicator hG
  convert hmr.add hdrv |>.sub ((measurable_const (a := p)).indicator hG) using 1
  funext ω
  change (if (u : ℝ) ≤ T ω then (frzChart (fun t => X t.toNNReal ω) u 0).re - p else 0) =
    (G.indicator (fun ω => fwdMap (fun t => X t.toNNReal ω) u 0) ω).re +
      G.indicator (X u) ω - G.indicator (fun _ => p) ω
  by_cases hω : ω ∈ G
  · have hω' : (u : ℝ) ≤ T ω := hω
    simp only [hω', ↓reduceIte, indicator_of_mem hω, frzChart,
      add_re, ofReal_re, Real.toNNReal_coe]
  · have hω' : ¬ (u : ℝ) ≤ T ω := hω
    simp only [hω', ↓reduceIte, indicator_of_notMem hω, zero_re,
      add_zero, sub_zero]

end InteractingSLE.ZhanGT4
