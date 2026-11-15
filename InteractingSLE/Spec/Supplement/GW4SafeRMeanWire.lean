/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRMeanIdentify

/-!
# GW4: the mean half from its phase-word analytic inputs

`GW4ComponentPhaseInputsStatement` is the precise named remaining hypothesis.
Theorems below prove the zero-phase selection and mean assembly from it. CLOC's
locality half plugs into the shared interface without a choice of clipped set.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW4Fix

open Restart Sec7.StripSysField GW4Rel Supp8.Q3Stop Exist.StagedLaw

/-- **Open analytic input:** the actual component mean has the finite-word
phase description, the source's seed bounds, and the protected martingale and
continuity inputs. No zero phase or relative SLE law is assumed here. -/
def GW4ComponentPhaseInputsStatement : Prop :=
  GW4ComponentProperty.{u} fun {Ω} _ k c₀ F ν X Wd GT R V hWm =>
    ∀ (u₀ : ℂ → ℝ) (ℋ : ℝ≥0 → MeasurableSpace Ω) (B : ℝ≥0 → Ω → Set ℂ),
      ComponentLineLocality c₀ F ν X Wd GT R V hWm u₀ ℋ B →
      ∃ hcap : ComponentPhaseCaps k c₀ ν X R V,
        ComponentPhaseRepresentation k c₀ F ν X Wd GT R V u₀ B hcap.phase

/-- The remaining analytic input implies the shared mean target, with the
phase eliminated by Aux. 122 and time zero covered by the empty seed interval. -/
theorem gw4ComponentMeanStatement_of_phaseInputs
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hWB : GW4R51.GW3WordBoundRegStatement.{u})
    (hI : GW4ComponentPhaseInputsStatement.{u}) : GW4ComponentMeanStatement.{u} := by
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  filter_upwards [hI κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hWB κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hi hBound
  intro R L ν C hCm c hC bC jumpsC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀
    F Wd GT hF hFC hFc hGT hWm hGTm hGTae hVW Rv V hver u₀ ℋ B hloc
  obtain ⟨hcap, hrep⟩ := hi C hCm c hC bC jumpsC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀
    F Wd GT hF hFC hFc hGT hWm hGTm hGTae hVW Rv V hver u₀ ℋ B hloc
  have hk : 4 < 16 / κ := (lt_div_iff₀ hκ).2 (by linarith only [hκ4])
  have hν : IsProbabilityMeasure ν := by
    show IsProbabilityMeasure (condExpKernel P _ ω₀)
    infer_instance
  let X := fun ω => invField κ (hC ω)
  have hX : IsGFFWithBoundaryData ν X c₀.fn c₀.jumps :=
    isGFFWithBoundaryData_invField_word hκ hpc hgff hc₀J hc₀
  have hk0 : 0 < 16 / κ := by positivity
  have hcan := isFlowLineDriver_cfDrv_word h12p h13 hk0 c₀ hX
  obtain ⟨hsL, hsR⟩ := hBound C hCm c hC bC jumpsC hch htr hpc hbd hgff
    c₀.fn c₀.jumps X (fun t ω => (BRLeaf.cfDrv h12p hk0 c₀ (X ω)).1 t)
    (fun ω => (BRLeaf.cfDrv h12p hk0 c₀ (X ω)).2) c₀.isPiecewiseConstantBoundaryData
    (fun ω => isChartTransport_invField hκ (hC ω)) hcan
  have htL : ∀ i, typedRhoL (wordType (16 / κ) c₀) i =
      flowLineRhoL (16 / κ) c₀.fn c₀.jumps 0 0 i := fun i => padFL_snd_fst_fin _ _ _ _ i
  have htR : ∀ i, typedRhoR (wordType (16 / κ) c₀) i =
      flowLineRhoR (16 / κ) c₀.fn c₀.jumps 0 0 i := fun i => padFL_snd_snd_fin _ _ _ _ i
  refine componentLineMean_of_phaseInputs hk hloc ?_ ?_
    hver.1.1.2.2.1 hver.1.1.2.1 hcap hrep
  · rw [htL]
    exact seed_lower_of_partialSums hsL
  · rw [htR]
    exact seed_lower_of_partialSums hsR

/-- CLOC's locality half and the explicit remaining analytic input imply the
unchanged component-lines assertion. -/
theorem gw4ComponentLinesStatement_of_locality_phaseInputs
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hWB : GW4R51.GW3WordBoundRegStatement.{u})
    (hL : GW4ComponentLocalityStatement.{u}) (hI : GW4ComponentPhaseInputsStatement.{u}) :
    GW4ComponentLinesStatement.{u} :=
  gw4ComponentLinesStatement_of_locality_mean hL
    (gw4ComponentMeanStatement_of_phaseInputs h12 h13 hWB hI)

/-- The same two halves feed the already checked safe relative kernel. -/
theorem gw4RelSafeRStatement_of_locality_phaseInputs
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hB : GW4Reg.GW4BarrierPocketRegStatement.{u})
    (hWB : GW4R51.GW3WordBoundRegStatement.{u})
    (hL : GW4ComponentLocalityStatement.{u}) (hI : GW4ComponentPhaseInputsStatement.{u}) :
    GW4RelSafeRStatement.{u} :=
  gw4RelSafeRStatement_of_componentLines h12 h13 hB hWB
    (gw4ComponentLinesStatement_of_locality_phaseInputs h12 h13 hWB hL hI)

end InteractingSLE.Theorem14.GW4Fix
