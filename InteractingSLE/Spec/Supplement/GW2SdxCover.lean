/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdxSched

/-!
# The lossy binders on COVER's scaled cover (rulings R118, R119)

Packet PROVE-GW2-SDE (round 10). Ruling R118 moves GW2's J32 pair and the Theorem 1.4 top to COVER's scaled cover
`RootCv.withScaledCover D gap`: the same experiment with the smaller initial event `scaledCoverEvent ⊆ coverEvent`.
The alive histories are monotone in the initial event, and the binders read the experiment only through
`∀ᵐ ω, ω ∈ alive l → …`, so both lossy binders pass from J32 to the scaled cover:

* `aliveTests_mono`;
* **`retainedNearModelsLossy_withScaledCover`**, **`retainedSlowComparisonsLossy_withScaledCover`** (any `D` whose
  initial event contains the scaled cover event), and `retainedSlowComparisons_withScaledCover` (the exact slow
  binder);
* **`retainedComparisonsLossyX_vpkg_scaled`**: the successor pair for J32 on the scaled cover.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Sdx

open GW2JDetR11 GW2Sdh GW2Sdi GW2TipSystem GW2TipSystem.RootC24

/-- The alive histories are monotone in the initial event. -/
theorem aliveTests_mono {Ω Θ Q : Type*} {G G' : Set Ω} (h : G' ⊆ G) (ang : ℕ → Θ)
    (T : List (Θ × Q) → ℕ → Q → Set Ω) (l : List (Θ × Q)) :
    (TestEvents.aliveTests G' ang T l : Set Ω) ⊆ TestEvents.aliveTests G ang T l := by
  induction l with
  | nil => exact h
  | cons x l ih => exact inter_subset_inter_left _ ih

/-- **The lossy near binder passes to the scaled cover.** -/
theorem retainedNearModelsLossy_withScaledCover {D : ConstructionFamily.{u}} (gap : RootCv.GapFamily.{u})
    (hG : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q),
      RootCv.scaledCoverEvent c (gap Ω c) r ⊆ (D Ω c).G r)
    (h : RetainedNearModelsLossyStatement D) : RetainedNearModelsLossyStatement (RootCv.withScaledCover D gap) := by
  intro Ω _ _ c r l k
  filter_upwards [h Ω c r l k] with ω hω hωA
  exact hω (aliveTests_mono (hG Ω c r) _ _ l hωA)

/-- **The lossy slow binder passes to the scaled cover.** -/
theorem retainedSlowComparisonsLossy_withScaledCover {D : ConstructionFamily.{u}} (gap : RootCv.GapFamily.{u})
    (hG : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q),
      RootCv.scaledCoverEvent c (gap Ω c) r ⊆ (D Ω c).G r)
    (h : RetainedSlowComparisonsLossyStatement D) :
    RetainedSlowComparisonsLossyStatement (RootCv.withScaledCover D gap) := by
  intro Ω _ _ c r k l hl a
  filter_upwards [h Ω c r k l hl a] with ω hω hωA
  exact hω (aliveTests_mono (hG Ω c r) _ _ l hωA)

/-- The exact slow binder passes to the scaled cover. -/
theorem retainedSlowComparisons_withScaledCover {D : ConstructionFamily.{u}} (gap : RootCv.GapFamily.{u})
    (hG : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q),
      RootCv.scaledCoverEvent c (gap Ω c) r ⊆ (D Ω c).G r)
    (h : RetainedSlowComparisonsStatement D) : RetainedSlowComparisonsStatement (RootCv.withScaledCover D gap) := by
  intro Ω _ _ c r
  dsimp only
  intro k l hl a
  filter_upwards [h Ω c r k l hl a] with ω hω hωA
  exact hω (aliveTests_mono (hG Ω c r) _ _ l hωA)

/-- J32's initial event is COVER's event, which contains the scaled cover event. -/
theorem scaledCoverEvent_subset_rootJ32 (gap : RootCv.GapFamily.{u}) (Ω : Type u) [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) :
    RootCv.scaledCoverEvent c (gap Ω c) r ⊆ (RootJ32.constructionFamily.{u} Ω c).G r :=
  RootCv.scaledCoverEvent_subset c (gap Ω c) r

/-- **The successor pair for J32 on the scaled cover** (decisions D1, D3; rulings R114, R118): the lossy near binder
and the lossy slow binder for `RootCv.withScaledCover RootJ32.constructionFamily gap`. -/
theorem retainedComparisonsLossyX_vpkg_scaled (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) (V : ℕ → VPkgXFamily.{u})
    (lam : NearDil.{u}) (hV : VPairInputsX V lam) (gap : RootCv.GapFamily.{u}) :
    RetainedNearModelsLossyStatement (RootCv.withScaledCover RootJ32.constructionFamily.{u} gap) ∧
      RetainedSlowComparisonsLossyStatement (RootCv.withScaledCover RootJ32.constructionFamily.{u} gap) :=
  have h := retainedComparisonsLossyX_vpkg h12p₀ h13₀ h13 V lam hV
  ⟨retainedNearModelsLossy_withScaledCover gap (scaledCoverEvent_subset_rootJ32 gap) h.1,
    retainedSlowComparisonsLossy_withScaledCover gap (scaledCoverEvent_subset_rootJ32 gap) h.2⟩

end InteractingSLE.Theorem14.GW2Sdx
