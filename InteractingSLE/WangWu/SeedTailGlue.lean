/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.SeedTailHistory
import InteractingSLE.WangWu.ImgChartConstMarks

/-!
# The tail bookkeeping on the reverse glued space

Packet PROVE-WW-B27. Apply Proposition 4.18 to the lower-height seed line.
The reversed history is a proper arc by a Borel certificate, so equality of
hitting codes gives the reverse parametrization, the exact slit tails, and dense heights.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WangWu.SeedTail

open LawUnique
open LQGMetric (DistOn)

/-- The reverse slits of the glue are the tails of the original seed line, with
the correct tips and a continuous decreasing onto height parametrization. -/
theorem ae_tailReversal_glue {rL rR : ℝ} (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR)
      P 𝓕 W VL VR B ζ h)
    {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 mΩ₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ}
    {B₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞} {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}
    (hC₂ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR) (fun _ => rL)
      P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂)
    (hlaw : P.map h = P₂.map (fun ω => reflectField (h₂ ω)))
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k) :
    ∀ᵐ p ∂(glueMeasure P k h hC.2.1), ∃ a : ℝ → ℝ,
      IsTailReversal (seedLine ζ W p.1) (histLine p.2) a ∧
      ∀ s : ℚ, 0 < s → negInv '' histHull s p.2 = seedLine ζ W p.1 '' Ici (a s) ∧
        revLine p.2 s = seedLine ζ W p.1 (a s) := by
  have hβ := ae_glue_fst (μ := P) k hC.2.1 (ae_good_twoSeed hL hR hC.1)
  have hγ := ae_glue_snd hC.2.1 (measurable_reflectField.comp hC₂.2.1)
    (measurable_killedHistory hC₂.2.2.2.1) hlaw k hk measurableSet_properHistory
    (ae_killedHistory_mem_properHistory hR hL hC₂.1)
  have hcode := ae_hitCode_seedLine_eq_revLine reverseTipContactStatement hL hR hC hC₂ hlaw k hk
  filter_upwards [hβ, hγ, hcode] with p hpβ hpγ hpcode
  have hγp := isProperArc_of_mem_properHistory hpγ
  obtain ⟨a, ha⟩ := exists_isTailReversal hpβ.1 hγp (image_Ioi_eq_of_hitCode hpβ.1 hγp hpcode)
  refine ⟨a, ha, fun s hs => ⟨?_, (ha.eq s (by exact_mod_cast hs)).symm⟩⟩
  rw [histHull_eq_image_Ioc hγp]
  exact ha.image_Ioc (by exact_mod_cast hs)

end InteractingSLE.WangWu.SeedTail
