/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G15LandMain
import InteractingSLE.Spec.Sec5.Aux22ChartEFlow

/-!
# The middle exclusions for S6 and SB1

Finite positive lifetimes end at bad incident heights. Admissibility of the
middle word excludes such endpoints for S6. For SB1 the lower word is
admissible; an upper threshold on a protected middle interval cannot be
visited by the lower flow. All conclusions retain finite terminal values.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.SB.W5Middle

open PiecewiseConstantBoundaryData (leftLim rightLim)
open Restart.FCPlumb

universe u

/-- Left admissibility on an open middle interval also bounds the incident
left height at every point of that interval, including its jump marks. -/
theorem leftLim_lt_of_middle_admissible {κ θ u v y : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (hL : ∀ z ∈ Ioo u v, z ∉ J → -2 < Sec4.cumWeightLeft κ (b z + θ * chiC κ))
    (hy : y ∈ Ioo u v) : leftLim b y + θ * chiC κ < sleLambda κ := by
  obtain ⟨z, huz, hzy, hzJ, he⟩ := Sec5.Aux22ChartE.exists_leftLim_eq hb hy.1
  rw [he]
  exact (cumWeightLeft_gt_iff hκ).1 (hL z ⟨huz, hzy.trans hy.2⟩ hzJ)

/-- The right incident analogue, with jump marks included. -/
theorem neg_lt_rightLim_of_middle_admissible {κ θ u v y : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (hR : ∀ z ∈ Ioo u v, z ∉ J → -2 < Sec4.cumWeightRight κ (b z + θ * chiC κ))
    (hy : y ∈ Ioo u v) : -sleLambda κ < rightLim b y + θ * chiC κ := by
  obtain ⟨z, hyz, hzv, hzJ, he⟩ := Sec5.Aux22ChartE.exists_rightLim_eq hb hy.2
  rw [he]
  exact (cumWeightRight_gt_iff hκ).1 (hR z ⟨hy.1.trans hyz, hzv⟩ hzJ)

/-- A flow whose whole left middle word is admissible cannot terminate in
that open interval. This includes a terminal visit to an original jump. -/
theorem ae_terminal_notMem_left_middle {κ θ u v : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (hL : ∀ z ∈ Ioo u v, z ∉ J → -2 < Sec4.cumWeightLeft κ (b z + θ * chiC κ))
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hη : IsFlowLine κ b J v θ P h η ζ) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω →
      (η ω T).re ∉ Ioo u v := by
  filter_upwards [ae_original_terminal_bad_incident hκ hb hη] with ω hω T hT hζ hy
  obtain ⟨-, hbad | hbad⟩ := hω T hT hζ
  · exact (not_lt_of_ge hbad.2) (leftLim_lt_of_middle_admissible hκ hb hL hy)
  · exact (not_le_of_gt hy.2) hbad.1

/-- The corresponding exclusion on the right of the original seed. -/
theorem ae_terminal_notMem_right_middle {κ θ u v : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (hR : ∀ z ∈ Ioo u v, z ∉ J → -2 < Sec4.cumWeightRight κ (b z + θ * chiC κ))
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hη : IsFlowLine κ b J u θ P h η ζ) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω →
      (η ω T).re ∉ Ioo u v := by
  filter_upwards [ae_original_terminal_bad_incident hκ hb hη] with ω hω T hT hζ hy
  obtain ⟨-, hbad | hbad⟩ := hω T hT hζ
  · exact (not_le_of_gt hy.1) hbad.1
  · exact (not_lt_of_ge hbad.2) (neg_lt_rightLim_of_middle_admissible hκ hb hR hy)

/-- A positive terminal time of a good path cannot return to its own seed. -/
theorem terminal_ne_seed {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ}
    (hp : Restart.IsPathGood η ζ x) {T : ℝ≥0} (hT : 0 < T)
    (hζ : (T : ℝ≥0∞) = ζ) : η T ≠ x := by
  intro he
  have hzero := hp.1 hζ.le (show (0 : ℝ≥0∞) ≤ ζ from zero_le)
    (he.trans (Sec7.IsPathGood.zero hp).symm)
  exact hT.ne' hzero

/-- S6's middle exclusion, from the original hypotheses alone. -/
theorem s6MiddleStatement : S6MiddleStatement.{u} := by
  intro κ hκ hκ4 b J hb x₁ x₂ θ₁ θ₂ hx hθ hL hR Ω _ P _ h hh
    η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ hζ₁ hζ₂
  have hseeds : ∀ᵐ ω ∂P, x₂ < x₁ → 0 < ζ₁ ω → 0 < ζ₂ ω →
      (∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → η₂ ω t ≠ x₁) ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₁ ω → η₁ ω t ≠ x₂) := by
    by_cases hsep : x₂ < x₁
    · filter_upwards [Supp7.w0aStatement κ hκ hκ4 b J hb x₁ x₂ θ₁ θ₂ hsep hθ
        P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂] with ω hω _ using hω
    · exact Filter.Eventually.of_forall fun _ hlt => (hsep hlt).elim
  filter_upwards [ae_terminal_notMem_left_middle hκ hb hL hη₁,
    ae_terminal_notMem_right_middle hκ hb hR hη₂,
    ae_original_terminal_bad_incident hκ hb hη₁,
    ae_original_terminal_bad_incident hκ hb hη₂,
    Restart.ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁,
    Restart.ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂,
    hseeds, hζ₁, hζ₂] with ω hmid₁ hmid₂ hreal₁ hreal₂ hp₁ hp₂ hs hz₁ hz₂
  intro a c ha hc hterm he
  rcases hterm with hterm | hterm
  · have ha0 : 0 < a := ENNReal.coe_pos.1 (hterm.symm ▸ hz₁)
    have hr := (hreal₁ a ha0 hterm).1
    have heα : η₁ ω a = ((η₁ ω a).re : ℂ) :=
      Complex.ext rfl (by simpa only [Complex.ofReal_im] using hr)
    refine ⟨(η₁ ω a).re, heα, ?_⟩
    by_cases hleft : (η₁ ω a).re < x₂
    · exact Or.inl hleft
    by_cases hright : x₁ < (η₁ ω a).re
    · exact Or.inr hright
    have hlow : x₂ ≤ (η₁ ω a).re := le_of_not_gt hleft
    have hhigh : (η₁ ω a).re ≤ x₁ := le_of_not_gt hright
    have hne₁ : (η₁ ω a).re ≠ x₁ := fun hy =>
      terminal_ne_seed hp₁ ha0 hterm (heα.trans (congrArg Complex.ofReal hy))
    have hne₂ : (η₁ ω a).re ≠ x₂ := by
      intro hy
      have hsep : x₂ < x₁ := lt_of_le_of_ne hx (by
        intro hx'; exact hne₁ (hy.trans hx'))
      exact (hs hsep hz₁ hz₂).2 a ha (heα.trans (congrArg Complex.ofReal hy))
    exact (hmid₁ a ha0 hterm ⟨lt_of_le_of_ne hlow hne₂.symm,
      lt_of_le_of_ne hhigh hne₁⟩).elim
  · have hc0 : 0 < c := ENNReal.coe_pos.1 (hterm.symm ▸ hz₂)
    have hr := (hreal₂ c hc0 hterm).1
    have heβ : η₂ ω c = ((η₂ ω c).re : ℂ) :=
      Complex.ext rfl (by simpa only [Complex.ofReal_im] using hr)
    refine ⟨(η₂ ω c).re, he.trans heβ, ?_⟩
    by_cases hleft : (η₂ ω c).re < x₂
    · exact Or.inl hleft
    by_cases hright : x₁ < (η₂ ω c).re
    · exact Or.inr hright
    have hlow : x₂ ≤ (η₂ ω c).re := le_of_not_gt hleft
    have hhigh : (η₂ ω c).re ≤ x₁ := le_of_not_gt hright
    have hne₂ : (η₂ ω c).re ≠ x₂ := fun hy =>
      terminal_ne_seed hp₂ hc0 hterm (heβ.trans (congrArg Complex.ofReal hy))
    have hne₁ : (η₂ ω c).re ≠ x₁ := by
      intro hy
      have hsep : x₂ < x₁ := lt_of_le_of_ne hx (by
        intro hx'; exact hne₂ (hy.trans hx'.symm))
      exact (hs hsep hz₁ hz₂).1 c hc (heβ.trans (congrArg Complex.ofReal hy))
    exact (hmid₂ c hc0 hterm ⟨lt_of_le_of_ne hlow hne₂.symm,
      lt_of_le_of_ne hhigh hne₁⟩).elim

/-- SB1's hybrid middle exclusion, from the original hypotheses alone. -/
theorem sb1MiddleStatement : SB1MiddleStatement.{u} := by
  intro κ hκ hκ4 b J hb Ω _ P _ h hh u v ψ huv hψ hL hH
    ηL ηU ζL ζU hηL hηU hζL hζU
  filter_upwards [ae_terminal_notMem_left_middle hκ hb hL hηL,
    ae_original_terminal_bad_incident hκ hb hηL,
    ae_original_terminal_bad_incident hκ hb hηU,
    Restart.ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hηL,
    Restart.ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hηU,
    Supp7.w0aStatement κ hκ hκ4 b J hb v u (-(Real.pi / 2)) ψ huv hψ
      P h hh ηL ηU ζL ζU hηL hηU,
    Supp8.GB7aFlowStatement.ae_forall Supp8.gb7aFlowStatement hκ hκ4 hb hh hηL,
    RLC.jumpVisitStatement κ hκ hκ4 b J hb v (-(Real.pi / 2)) P h hh ηL ζL hηL,
    hζL, hζU] with ω hmid hrealL hrealU hpL hpU hs hprot hjump hzL hzU
  have hs' := hs hzL hzU
  intro a c ha hc hterm he
  rcases hterm with hterm | hterm
  · have ha0 : 0 < a := ENNReal.coe_pos.1 (hterm.symm ▸ hzL)
    have hr := (hrealL a ha0 hterm).1
    have heL : ηL ω a = ((ηL ω a).re : ℂ) :=
      Complex.ext rfl (by simpa only [Complex.ofReal_im] using hr)
    refine ⟨(ηL ω a).re, heL, ?_⟩
    by_cases hleft : (ηL ω a).re < u
    · exact Or.inl hleft
    by_cases hright : v < (ηL ω a).re
    · exact Or.inr hright
    have hneV : (ηL ω a).re ≠ v := fun hy =>
      terminal_ne_seed hpL ha0 hterm (heL.trans (congrArg Complex.ofReal hy))
    have hneU : (ηL ω a).re ≠ u := fun hy =>
      hs'.2 a ha (heL.trans (congrArg Complex.ofReal hy))
    exact (hmid a ha0 hterm ⟨lt_of_le_of_ne (le_of_not_gt hleft) hneU.symm,
      lt_of_le_of_ne (le_of_not_gt hright) hneV⟩).elim
  · have hc0 : 0 < c := ENNReal.coe_pos.1 (hterm.symm ▸ hzU)
    obtain ⟨hr, hbad⟩ := hrealU c hc0 hterm
    let y := (ηU ω c).re
    have heU : ηU ω c = (y : ℂ) :=
      Complex.ext rfl (by simpa only [Complex.ofReal_im] using hr)
    have heL : ηL ω a = (y : ℂ) := he.trans heU
    refine ⟨y, heL, ?_⟩
    by_cases hleft : y < u
    · exact Or.inl hleft
    by_cases hright : v < y
    · exact Or.inr hright
    have hneU : y ≠ u := fun hy =>
      terminal_ne_seed hpU hc0 hterm (heU.trans (congrArg Complex.ofReal hy))
    have hneV : y ≠ v := fun hy => hs'.1 c hc (heU.trans (congrArg Complex.ofReal hy))
    have hymid : y ∈ Ioo u v :=
      ⟨lt_of_le_of_ne (le_of_not_gt hleft) hneU.symm,
        lt_of_le_of_ne (le_of_not_gt hright) hneV⟩
    have hya : (ηL ω a).re = y := by rw [heL, Complex.ofReal_re]
    have ha0 : 0 < a := by
      apply pos_iff_ne_zero.2
      intro haz
      exact hneV (Complex.ofReal_injective
        (heL.symm.trans (haz ▸ Sec7.IsPathGood.zero hpL)))
    have halive : (a : ℝ≥0∞) < ζL ω := by
      apply lt_of_le_of_ne ha
      intro haζ
      exact hmid a ha0 haζ (hya.symm ▸ hymid)
    have hyJ : y ∉ J := fun hyJ => hjump a ha0 halive y hyJ hneV heL
    have hbadR : rightLim b y + ψ * chiC κ ≤ -sleLambda κ := by
      rcases hbad with hbad | hbad
      · exact ((not_le_of_gt hymid.1) hbad.1).elim
      · exact hbad.2
    rw [Exist.StagedLaw.rightLim_eq_of_notMem hb hyJ] at hbadR
    rcases hH y hymid hyJ with hgood | hprotected
    · exact ((not_lt_of_ge hbadR) ((cumWeightRight_gt_iff hκ).1 hgood)).elim
    · exact ((hprot a ha y hyJ).2 hymid.2 hprotected heL).elim

/-- With its middle exclusion discharged, SB1 needs only strict-prefix W5. -/
theorem sb1Statement_of_w5 (hW5 : Theorem15.W5Statement.{u}) : SB1Statement.{u} :=
  G15Land.sb1Statement_of_middle hW5 sb1MiddleStatement

/-- With its middle exclusion discharged, S6 needs only strict-prefix W5. -/
theorem s6Statement_of_w5 (hW5 : Theorem15.W5Statement.{u}) : S6Statement.{u} :=
  G15Land.s6Statement_of_middle hW5 s6MiddleStatement

end InteractingSLE.Theorem14.SB.W5Middle
