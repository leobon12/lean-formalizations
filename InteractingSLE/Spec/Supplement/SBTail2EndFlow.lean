/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBTail2EndSlit
import InteractingSLE.Spec.Supplement.SBTail2Induction
import InteractingSLE.Spec.Sec4.Aux25Term

/-!
# Available flow prefixes have slit completions, including their terminal stop

Auxiliary lemma 25 gives injectivity through the lifetime. The integrated
evolution has a finite left limit there; correcting its terminal driver value
preserves the generating trace and permits the closed-horizon slit theorem.
This also proves SB3's purely real initial-prefix case without an S6 input.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.End

open Supp9B

/-- Every available finite prefix of a flow line has a slit completion, also
when it ends exactly at a finite lifetime. No endpoint-driver convention is
added to the frozen flow-line hypotheses. -/
theorem ae_forall_exists_slitCompletion_of_isFlowLine
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    {x θ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hη : IsFlowLine κ b jumps x θ P h η ζ) :
    ∀ᵐ ω ∂P, ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω → ∃ S, IsSlitCompletion (η ω) a S := by
  have hstrict := Supp9B.ae_forall_exists_isSlitCompletion_of_isFlowLine
    InteractingSLE.Theorem15.aux25Statement hκ hκ4 hη
  have hinj := InteractingSLE.Theorem15.ae_injOn_of_isFlowLine
    InteractingSLE.Theorem15.aux25Statement hκ hκ4 hη
  obtain ⟨h', 𝓕, W, VL, VR, B, _, hcoup, htr⟩ := hη
  filter_upwards [hstrict, hinj, htr, hcoup.1.2.2.2.2, hcoup.1.ae_tendsto_threshold hκ]
    with ω hs hi ht hp hthr a ha
  rcases ha.lt_or_eq with hlt | heq
  · exact hs a hlt
  have hgen : IsGeneratingTrace (fun t => W t ω) (a : ℝ≥0∞)
      (fun t => η ω t - (x : ℂ)) := heq ▸ ht
  have hw : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < (a : ℝ≥0∞)} := by
    rw [heq]
    exact hp.2.2.2.1
  have hi' : InjOn (fun t => η ω t - (x : ℂ)) (Icc 0 a) := by
    intro s hs t ht he
    exact hi ((ENNReal.coe_le_coe.2 hs.2).trans ha)
      ((ENNReal.coe_le_coe.2 ht.2).trans ha) (sub_left_inj.1 he)
  have hlim : 0 < a → ∃ L : ℝ, Tendsto (fun t => W t ω) (𝓝[<] a) (𝓝 L) := by
    intro hapos
    obtain ⟨w₀, vL₀, vR₀, hL, _⟩ := hthr a hapos heq
    exact ⟨w₀, (continuous_fst.tendsto _).comp hL⟩
  obtain ⟨S, hS⟩ := exists_slitCompletion_of_leftLimit hgen hw hp.1 hi' hlim
  have hadd := isSlitCompletion_add_real hS x
  have he : (fun t => (x : ℂ) + (η ω t - (x : ℂ))) = η ω := by
    funext t
    ring
  rw [he] at hadd
  exact ⟨_, hadd⟩

/-- SB3's initial unavailable lower seed contributes only real points to the
right of the upper seed. Any available upper prefix, including its finite
terminal prefix, has S1 against all such points on one common event. -/
theorem ae_isOneSided_right_real_of_isFlowLine
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    {x θ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hη : IsFlowLine κ b jumps x θ P h η ζ) :
    ∀ᵐ ω ∂P, ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω →
      ∀ T : Set ℝ, (∀ y ∈ T, x ≤ y) →
        IsOneSided (((↑) : ℝ → ℂ) '' T) (η ω) a := by
  filter_upwards [ae_forall_exists_slitCompletion_of_isFlowLine hκ hκ4 hη,
    IsFlowLine.ae_seed_continuousOn hη] with ω hcomp hseed a ha T hT
  obtain ⟨S, hS, _⟩ := hcomp a ha
  have hS0 : S 0 = (x : ℂ) := (hS.2.2.2.2 0 zero_le).trans hseed.1
  refine ⟨S, hS, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact ofReal_mem_closedRightSide_of_seed_le (isProperCurve_of_isProperCompletion hS)
    (by rw [hS0]; rfl) (by rw [hS0, Complex.ofReal_re]; exact hT y hy)

end InteractingSLE.Theorem14.SB.End
