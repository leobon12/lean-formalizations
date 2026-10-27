import MatedCRTHarmonic.GMS4.Prop48
import MatedCRTHarmonic.GMS4c.LocalAreaLimit
import MatedCRTHarmonic.MesoModel.FrozenIdentities
import MatedCRTHarmonic.MoTPort.IG.GFF.AbsContCore

/-!
# Thickened local-field reconstruction for Proposition 4.8

The selected area on `V` is read from a field on `thickening δ V`, matching
The dyadic GMC locality interface. The frozen S7 clause then reconstructs
The remaining local configuration from the independent IG data.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped NNReal

namespace MatedCRTHarmonic.GMS4

open MatedCRTHarmonic.MatedCRT
open MatedCRTHarmonic.MoTPort.IG.GFFAbsCont

/-- The one remaining reconstruction input in its thickened-field shape: a Borel map from
The field on `thickening δ V` to the canonical GMC area restricted to `V`. -/
structure Prop48ThickLocalGMCFromFieldInput
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (γ : ℝ) (h : Ω → MatedCRT.Field)
    (V : TopologicalSpace.Opens ℂ) (δ : ℝ) where
  reconstruct : LQGMetric.DistOn (GMS4c.thickOpen V δ) → Measure ℂ
  measurable_reconstruct : Measurable reconstruct
  ae_reconstruct : (fun ω => reconstruct
    (LQGMetric.restrictTo (GMS4c.thickOpen V δ) (h ω))) =ᵐ[P]
      fun ω => (MatedCRTHarmonic.CellScaling.lqgArea γ (h ω)).restrict V

/-- Assemble the excursion map with the single pending thickened-GMC map.
This produces the actual local configuration from the two local field inputs. -/
theorem prop48_zeroCone_localConfiguration_from_thickFields
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ))
    (δ : ℝ) (hδ : 0 < δ)
    (A : Prop48ThickLocalGMCFromFieldInput P γ
      (fun ω => coneField (X₀ ω)
        (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω))) V δ) :
    ∃ F : (LQGMetric.DistOn (GMS4c.thickOpen V δ) ×
        (LQGMetric.DistOn (GMS4c.thickOpen V δ) × ℝ)) →
          GMS4c.LocalConfiguration V,
      Measurable F ∧ ∀ᵐ ω ∂P,
        F (LQGMetric.restrictTo (GMS4c.thickOpen V δ)
            (coneField (X₀ ω)
              (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω))),
          (LQGMetric.restrictTo (GMS4c.thickOpen V δ) (hIG₀ ω), U ω)) =
          GMS4c.localConfiguration V
            (MatedCRTHarmonic.CellScaling.lqgArea γ
              (coneField (X₀ ω)
                (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω))))
            (coneField (X₀ ω)
              (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω))) (ηL ω) := by
  let W := GMS4c.thickOpen V δ
  have hVW : V ≤ W := by
    intro z hz
    change z ∈ thickening δ (V : Set ℂ)
    exact self_subset_thickening hδ (V : Set ℂ) hz
  let h₀ : Ω → MatedCRT.Field := fun ω => coneField (X₀ ω)
    (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω))
  let μ : Ω → Measure ℂ := fun ω => MatedCRTHarmonic.CellScaling.lqgArea γ (h₀ ω)
  obtain ⟨G, hG, hGeq⟩ :=
    GMS4c.ae_bundle_localConfiguration_from_localAreaIG D V hVb δ hδ μ h₀
  let F : (LQGMetric.DistOn W × (LQGMetric.DistOn W × ℝ)) →
      GMS4c.LocalConfiguration V := fun x =>
    G ((A.reconstruct x.1, resOn V W x.1), x.2)
  have hF : Measurable F :=
    hG.comp (((A.measurable_reconstruct.comp measurable_fst).prodMk
      ((measurable_resOn V W).comp measurable_fst)).prodMk measurable_snd)
  refine ⟨F, hF, ?_⟩
  filter_upwards [hGeq, A.ae_reconstruct] with ω hω hA
  change G ((A.reconstruct (LQGMetric.restrictTo W (h₀ ω)),
      resOn V W (LQGMetric.restrictTo W (h₀ ω))), _) =
        GMS4c.localConfiguration V (μ ω) (h₀ ω) (ηL ω)
  rw [hA, resOn_restrictTo hVW]
  exact hω

end MatedCRTHarmonic.GMS4

