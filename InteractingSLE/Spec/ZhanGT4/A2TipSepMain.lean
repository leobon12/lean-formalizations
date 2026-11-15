/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A2TipSepHit

/-!
# A.2, part 2: the conditional separation at first hits, from the image endpoint theorem

Packet PROVE-ZHAN-A2TIPSEP. Source: Astra, *Follow-up proofs*, §A.2 L537–L561 (R38, R53, R70).

* `a2TipSepG3AugStatement_of_imageEndpoint : ImageEndpointG3Statement κ → A2TipSepG3AugStatement κ` and the (Eight)
  analogue: the conditional separation (L548–L553) at the first hits of the countable argument (L555–L561), for the
  dual pairs whose conditional image law holds at usual-augmentation stopping times (R70);
* `a2HullInsideG3AugStatement_of_imageEndpoint`, `a2HullInsideEightAugStatement_of_imageEndpoint`: **A.2 part 2** for
  these pairs (A2P2's countable argument on top).

The only input is the image endpoint theorem `ImageEndpoint…Statement` (probability only, about local evolutions of
the image word).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4.A2TipSep

open QuantumZipper A2X A2Part2

/-- **A.2, part 2, step 1, (G3), augmented**, from the image endpoint theorem. -/
theorem a2TipSepG3AugStatement_of_imageEndpoint {κ : ℝ} (hI : ImageEndpointG3Statement.{u} κ) :
    A2TipSepG3AugStatement.{u} κ := by
  intro hκ4 hκ8 y x hyx hx Ω mΩ P hP 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair L hL hLH
  have hpath := hpair.1.1.2.2.2.2
  refine ae_of_firstHit_of_stop (W := W₂) (V := VL₂ 0) (ζ := ζ₂) hpair.1.1.2.1 (hpair.1.1.2.2.1 0) ?_
    (fun τ hτ => ae_tipSeparated_at_stop_G3_of_law hκ4 hκ8 hI hyx hx hpair.1.1 hpair.2 hτ) hL hLH
  filter_upwards [hpath] with ω hp
  exact ⟨hp.isForcePath.continuousOn_w, hp.isForcePath.continuousOn_vL 0⟩

/-- **A.2, part 2, step 1, (Eight), augmented**, from the image endpoint theorem. -/
theorem a2TipSepEightAugStatement_of_imageEndpoint {κ : ℝ} (hI : ImageEndpointEightStatement.{u} κ) :
    A2TipSepEightAugStatement.{u} κ := by
  intro hκ8 x hx Ω mΩ P hP 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair L hL hLH
  have hpath := hpair.1.1.2.2.2.2
  refine ae_of_firstHit_of_stop (W := W₂) (V := VL₂ 0) (ζ := ζ₂) hpair.1.1.2.1 (hpair.1.1.2.2.1 0) ?_
    (fun τ hτ => ae_tipSeparated_at_stop_eight_of_law hκ8 hI hx hpair.1.1 hpair.2 hτ) hL hLH
  filter_upwards [hpath] with ω hp
  exact ⟨hp.isForcePath.continuousOn_w, hp.isForcePath.continuousOn_vL 0⟩

/-- **A.2, part 2, (G3), augmented** (`A2X.A2HullInsideG3Statement` for the pairs of R70), from the image endpoint
theorem. -/
theorem a2HullInsideG3AugStatement_of_imageEndpoint {κ : ℝ} (hI : ImageEndpointG3Statement.{u} κ) :
    A2HullInsideG3AugStatement.{u} κ :=
  a2HullInsideG3AugStatement_of_tipSepAug (a2TipSepG3AugStatement_of_imageEndpoint hI)

/-- **A.2, part 2, (Eight), augmented**, from the image endpoint theorem. -/
theorem a2HullInsideEightAugStatement_of_imageEndpoint {κ : ℝ} (hI : ImageEndpointEightStatement.{u} κ) :
    A2HullInsideEightAugStatement.{u} κ :=
  a2HullInsideEightAugStatement_of_tipSepAug (a2TipSepEightAugStatement_of_imageEndpoint hI)

end InteractingSLE.ZhanGT4.A2TipSep
