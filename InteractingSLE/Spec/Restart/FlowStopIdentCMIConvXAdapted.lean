/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvXTrace

/-! # A globally continuous adapted trace on the original space -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Restart.FlowStopIdentCMI
namespace CMIVSetting
variable {S : Type u} [MeasurableSpace S] (D : CMIVSetting S)

/-- The available trace has an everywhere continuous, adapted extension,
including agreement at its finite lifetime. -/
theorem exists_continuous_adapted_trace :
    ∃ Z : ℝ≥0 → S → ℂ, (∀ ω, Z 0 ω = D.y) ∧ (∀ ω, Continuous (Z · ω)) ∧
      (∀ t, Measurable[D.driving t] (Z t)) ∧
      ∀ᵐ ω ∂D.Q₀, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ D.U ω → Z t ω = D.Γ ω t := by
  classical
  obtain ⟨η, hm, hc, hag⟩ := D.exists_continuous_measurable_trace
  let G : Set S := {ω | η ω 0 = (D.y : ℂ)}
  have hGm : MeasurableSet G := measurableSet_eq_fun (hm 0) measurable_const
  have hGae : ∀ᵐ ω ∂D.Q₀, ω ∈ G := by
    filter_upwards [hag, D.trace] with ω hη hg
    exact (hη 0 bot_le).trans (sub_eq_zero.1 hg.1)
  let Y : S → ℝ≥0 → ℂ := fun ω t => if ω ∈ G then η ω t else D.y
  have hYm : ∀ t, Measurable fun ω => Y ω t := fun t => (hm t).ite hGm measurable_const
  have hYc : ∀ ω, Continuous (Y ω) := by
    intro ω
    by_cases hω : ω ∈ G
    · simpa only [Y, hω, ↓reduceIte] using hc ω
    · simp only [Y, hω, ↓reduceIte]; exact continuous_const
  have hY0 : ∀ ω, Y ω 0 = D.y := by
    intro ω
    by_cases hω : ω ∈ G
    · exact (ite_eq_left hω).trans hω
    · exact ite_eq_right hω
  have hYag : ∀ᵐ ω ∂D.Q₀, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ D.U ω → Y ω t = D.Γ ω t := by
    filter_upwards [hGae, hag] with ω hG hη t ht
    exact (ite_eq_left hG).trans (hη t ht)
  have haR : AdaptedBefore D.driving D.U (fun t ω => (Y ω t).re - D.y) := by
    intro t A hA
    exact D.measurableSet_trace_before hYm hYag t
      ((Complex.continuous_re.sub continuous_const).measurable hA)
  have haI : AdaptedBefore D.driving D.U (fun t ω => (Y ω t).im) := by
    intro t A hA
    exact D.measurableSet_trace_before hYm hYag t (Complex.continuous_im.measurable hA)
  obtain ⟨R, hR0, hRc, hRa, hRag⟩ := RetAux79.exists_continuous_adapted_stopped
    (X := fun t ω => (Y ω t).re - D.y)
    (fun ω => (Complex.continuous_re.comp (hYc ω)).sub continuous_const)
    (fun ω => by rw [hY0]; simp only [Complex.ofReal_re, sub_self]) haR
  obtain ⟨I, hI0, hIc, hIa, hIag⟩ := RetAux79.exists_continuous_adapted_stopped
    (X := fun t ω => (Y ω t).im)
    (fun ω => Complex.continuous_im.comp (hYc ω))
    (fun ω => by rw [hY0]; exact Complex.ofReal_im _) haI
  let Z : ℝ≥0 → S → ℂ := fun t ω => ((D.y + R t ω : ℝ) : ℂ) + (I t ω : ℂ) * Complex.I
  have hZc : ∀ ω, Continuous (Z · ω) := fun ω =>
    (Complex.continuous_ofReal.comp (continuous_const.add (hRc ω))).add
      ((Complex.continuous_ofReal.comp (hIc ω)).mul continuous_const)
  have hZ0 : ∀ ω, Z 0 ω = D.y := fun ω => by
    simp only [Z, hR0, hI0, add_zero, Complex.ofReal_zero, zero_mul]
  have hZY : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < D.U ω → Z t ω = Y ω t := by
    intro ω t ht
    apply Complex.ext
    · simp only [Z, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, hRag ω t ht]
      ring
    · simp only [Z, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add, hIag ω t ht]
  refine ⟨Z, hZ0, hZc, fun t =>
    (Complex.measurable_ofReal.comp (measurable_const.add (hRa t).measurable)).add
      ((Complex.measurable_ofReal.comp (hIa t).measurable).mul measurable_const), ?_⟩
  filter_upwards [hYag] with ω hω t ht
  refine Eq.trans ?_ (hω t ht)
  by_cases ht0 : t = 0
  · subst t
    exact (hZ0 ω).trans (hY0 ω).symm
  · have htpos : 0 < t := pos_iff_ne_zero.2 ht0
    have : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, htpos⟩
    have hz : Tendsto (Z · ω) (𝓝[<] t) (𝓝 (Z t ω)) :=
      (hZc ω).tendsto t |>.mono_left nhdsWithin_le_nhds
    have hy : Tendsto (Y ω) (𝓝[<] t) (𝓝 (Y ω t)) :=
      (hYc ω).tendsto t |>.mono_left nhdsWithin_le_nhds
    have heq : (Y ω) =ᶠ[𝓝[<] t] (Z · ω) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (hZY ω s ((ENNReal.coe_lt_coe.2 hs).trans_le ht)).symm
    exact tendsto_nhds_unique hz (hy.congr' heq)

end CMIVSetting
end InteractingSLE.Restart.FlowStopIdentCMI
