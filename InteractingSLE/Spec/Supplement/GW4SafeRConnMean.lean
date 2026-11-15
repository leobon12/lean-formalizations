/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRConnWord
import InteractingSLE.Spec.Supplement.GW4SafeRAdvanceBefore

/-!
# GW4: the zero-phase mean after discharging the actual upper seed bounds

The remaining analytic input has no incoming-height, upper-weight, cap or
mean-continuity premise. It still requires the full boundary representation
and the phase martingales, with the explicit through-cutoff constancy of
`ComponentPhaseBefore`. This sufficient input is not claimed here as a theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW4Fix

open Exist Exist.Staged Exist.StagedLaw Supp8.Q3Stop

/-- **Open analytic input.** The actual full boundary-collar representation
and phase martingales for every choice of the shared locality witnesses.
The phase is controlled through the cutoff, including a finite endpoint;
constancy merely strictly before the lifetime does not supply this condition. -/
def GW4ComponentBeforeInputsStatement : Prop :=
  GW4ComponentProperty.{u} fun {Ω} _ k c₀ F ν X Wd GT R V hWm =>
    ∀ (u₀ : ℂ → ℝ) (ℋ : ℝ≥0 → MeasurableSpace Ω) (B : ℝ≥0 → Ω → Set ℂ),
      ComponentLineLocality c₀ F ν X Wd GT R V hWm u₀ ℋ B →
      ∃ h : ComponentPhaseBefore k c₀ ν X R V,
        ComponentPhaseRepresentation k c₀ F ν X Wd GT R V u₀ B h.phase

/-- Construct the original cap-based analytic input: the source's upper seed
bounds now follow from the actual walks, and the finite caps are constructed. -/
theorem gw4ComponentPhaseInputsStatement_of_before
    (h13₀ : Theorem13Statement.{0}) (hI : GW4ComponentBeforeInputsStatement.{u}) :
    GW4ComponentPhaseInputsStatement.{u} := by
  intro κ hκ hκ4 b J hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  filter_upwards [hI κ hκ hκ4 b J hb P h hh W' ζ' hcf hζ' E hE hreg,
    gw4ComponentSeedUpper_of_theorem13 h13₀
      κ hκ hκ4 b J hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hi hu
  intro R L ν C hCm c hC bC JC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀
    F Wd GT hF hFC hFc hGT hWm hGTm hGTae hVW Rv V hver u₀ ℋ B hloc
  obtain ⟨hbefore, hrep⟩ := hi C hCm c hC bC JC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀
    F Wd GT hF hFC hFc hGT hWm hGTm hGTae hVW Rv V hver u₀ ℋ B hloc
  obtain ⟨huL, huR⟩ := hu C hCm c hC bC JC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀
    F Wd GT hF hFC hFc hGT hWm hGTm hGTae hVW Rv V hver
  exact ⟨hbefore.toCaps hver.1.1.2.2.1 hver.1.1.2.1 huL huR, hrep⟩

/-- The unchanged shared mean conclusion, conditional only on the remaining
analytic input and the existing lower-word-bound theorem. -/
theorem gw4ComponentMeanStatement_of_before
    (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h13₀ : Theorem13Statement.{0}) (hWB : GW4R51.GW3WordBoundRegStatement.{u})
    (hI : GW4ComponentBeforeInputsStatement.{u}) : GW4ComponentMeanStatement.{u} :=
  gw4ComponentMeanStatement_of_phaseInputs h12 h13 hWB
    (gw4ComponentPhaseInputsStatement_of_before h13₀ hI)

end InteractingSLE.Theorem14.GW4Fix
