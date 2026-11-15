/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRConnLaw

/-!
# GW4: the actual component words satisfy the upper seed bounds

This applies the proved connector heights to the component's actual boundary
data and the compatible inversion. The hypotheses are precisely the common
GW4 component context; an incoming-height premise is no longer needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW4Fix

open Exist Exist.Staged Exist.StagedLaw Supp8.Q3Stop

/-- The exact typed seed weights of every actual GW4 component satisfy the
upper bounds used by Aux. 122. Theorem 1.3 supplies the connector exit law. -/
theorem gw4ComponentSeedUpper_of_theorem13 (h13₀ : Theorem13Statement.{0}) :
    GW4ComponentProperty.{u} fun {_Ω} _ k c₀ _ _ _ _ _ _ _ _ =>
      typedRhoL (wordType k c₀) (componentSeedL k c₀) ≤ k / 2 - 4 ∧
        typedRhoR (wordType k c₀) (componentSeedR k c₀) ≤ k / 2 - 4 := by
  intro κ hκ hκ4 b J hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  filter_upwards [ae_walkConnectorHeightBounds h13₀ hκ hκ4 hb hh hcf hζ' hE hreg true,
    ae_walkConnectorHeightBounds h13₀ hκ hκ4 hb hh hcf hζ' hE hreg false]
    with ω₀ hR hL
  intro R L ν C _ c hC bC JC hch _ hpc hbd _ c₀ _ hc₀J hc₀
    F Wd GT hF hFC _ hGT hWm _ hGTae _ Rv V _
  have hν : IsProbabilityMeasure ν := by
    show IsProbabilityMeasure (condExpKernel P _ ω₀)
    infer_instance
  have := hν
  obtain ⟨ω, hω⟩ := hGTae.exists
  have hCo : IsOpen C := hFC ▸ Frame.isOpen_C hF (hGT ω hω)
  have hi := incomingHeightBounds_of_connectorHeights hκ rfl rfl hR hL hch hCo hpc hbd
  exact typed_seed_upper_of_incoming hκ hi hc₀J hc₀

end InteractingSLE.Theorem14.GW4Fix
