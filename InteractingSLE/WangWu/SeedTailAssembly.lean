/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.SeedTailGlue
import InteractingSLE.WangWu.SeedTailBarrier

/-!
# Proposition 4.19 from the shifted law and two explicit remaining inputs

Packet PROVE-WW-B27. The probabilistic terminal right barrier and the deterministic
chart translation remain named hypotheses. All construction of the reverse glue,
its tail bookkeeping, the killed-word equations, and descent to the original space
are proved in the imported modules. These conditional results replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WangWu.SeedTail

open LawUnique ImgWord
open LQGMetric (DistOn)

/-- Named remaining geometric input: in the reverse-slit chart, a first contact
away from the reverse tip from the right, or escape in the original right component,
forces a right force gap to vanish at a finite positive killing time. -/
def TailChartStatement : Prop :=
  ∀ {Ω : Type u} {s : ℚ} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}
    {E : Set (Ω × HistorySpace 1 1)} {p : Ω × HistorySpace 1 1} {β : ℝ → ℂ} {a : ℝ},
    0 < s → IsProperArc β → IsGlueGood s ζ W p → p ∈ E → 0 < a →
    negInv '' histHull s p.2 = β '' Ici a → revLine p.2 s = β a →
    RightSafe (imgW s ζ W E) (imgVR s ζ W E) (imgT s ζ W E) p →
    Descent.NoRightFirstContact (seedLine ζ W p.1) β a ∧
      Descent.NoRightEscape (seedLine ζ W p.1) β a

/-- The shifted glue supplies the tail conditions on the original probability
space, conditional on the terminal barrier and the chart translation. -/
theorem ae_tail_conditions_of_shift
    (hI : ImageWordFiltShiftStatement.{u}) (hBarrier : KilledRightBarrierStatement.{u})
    (hChart : TailChartStatement.{u}) {rL rR δ : ℝ}
    (hL : 0 ≤ rL) (hR : 0 ≤ rR) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hbL : 0 ≤ rL + δ) (hbR : 0 ≤ rR - δ)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h X : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR)
      P 𝓕 W VL VR B ζ h)
    {𝓕β : Filtration ℝ≥0 mΩ} {Wβ : ℝ≥0 → Ω → ℝ} {VLβ VRβ : Fin 1 → ℝ≥0 → Ω → ℝ}
    {Bβ : ℝ≥0 → Ω → ℝ} {ζβ : Ω → ℝ≥0∞}
    (hCβ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL + δ) (fun _ => rR - δ)
      P 𝓕β Wβ VLβ VRβ Bβ ζβ X)
    (hX : ∀ ω, h ω = Exist.flowField 0 (δ * wwLambda) (X ω))
    {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 mΩ₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ}
    {B₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞} {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}
    (hC₂ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR - δ) (fun _ => rL + δ)
      P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂)
    (hlaw : P.map X = P₂.map (fun ω => reflectField (h₂ ω)))
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k) :
    ∀ᵐ ω ∂P, ∃ D : Set ℝ, Descent.IsDenseAbove D ∧ ∀ a ∈ D,
      Descent.NoRightFirstContact (seedLine ζ W ω) (seedLine ζβ Wβ ω) a ∧
        Descent.NoRightEscape (seedLine ζ W ω) (seedLine ζβ Wβ ω) a := by
  let μ := glueMeasure P k X hCβ.2.1
  have hgood : ∀ s : ℚ, 0 < s → ∀ᵐ p ∂μ, IsGlueGood s ζ W p := fun s hs =>
    ae_isGlueGood_of_marginals hL hR hbR hbL hC hC₂ hCβ.2.1 hlaw k hk hs
  have hgoodAll : ∀ᵐ p ∂μ, ∀ s : ℚ, 0 < s → IsGlueGood s ζ W p ∧ p ∈ glueGood μ s ζ W := by
    rw [ae_all_iff]
    intro s
    by_cases hs : 0 < s
    · filter_upwards [hgood s hs, ae_mem_glueGood (hgood s hs)] with p hp hE _
      exact ⟨hp, hE⟩
    · exact Eventually.of_forall fun _ hs' => absurd hs' hs
  have hsafe : ∀ᵐ p ∂μ, ∀ s : ℚ, 0 < s →
      RightSafe (imgW s ζ W (glueGood μ s ζ W)) (imgVR s ζ W (glueGood μ s ζ W))
        (imgT s ζ W (glueGood μ s ζ W)) p := by
    rw [ae_all_iff]
    intro s
    by_cases hs : 0 < s
    · filter_upwards [ae_rightSafe_img_of_mart hBarrier hL hR hδ hδ1 hs hC.1.2.1 (hgood s hs)
        (hI rL rR δ hL hR hbL hbR P 𝓕 W VL VR B ζ h hC X hCβ.2.1 hX
          P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ hC₂ hlaw k hk s hs)] with p hp _
      exact hp
    · exact Eventually.of_forall fun _ hs' => absurd hs' hs
  have hbook := ae_tailReversal_glue hbL hbR hCβ hC₂ hlaw k hk
  have hβ := ae_glue_fst (μ := P) k hCβ.2.1 (ae_good_twoSeed hbL hbR hCβ.1)
  apply ae_tail_conditions_of_glue k hCβ.2.1 (γ := histLine)
  filter_upwards [hbook, hgoodAll, hsafe, hβ] with p hp hg hs hβp
  obtain ⟨a, ha, hat⟩ := hp
  refine ⟨a, ha, fun s hspos => ?_⟩
  exact hChart hspos hβp.1 (hg s hspos).1 (hg s hspos).2
    (ha.positive s (by exact_mod_cast hspos)) (hat s hspos).1 (hat s hspos).2 (hs s hspos)

/-- The small-gap tail statement from the shifted two-slit law and the two
remaining local inputs. The reflected coupling is constructed from Theorem 1.1. -/
theorem seedTailSmallStatement_of_shift
    (hI : ImageWordFiltShiftStatement.{u}) (hBarrier : KilledRightBarrierStatement.{u})
    (hChart : TailChartStatement.{u}) : SeedField.SeedTailSmallStatement.{u} := by
  intro rL rR u₁ u₂ h12 hgap hL hR Ω mΩ P _ h
    𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ hC₁ hC₂
  let aL := rL - u₂ / wwLambda
  let aR := rR + u₂ / wwLambda
  let δ := (u₂ - u₁) / wwLambda
  have hLam := wwLambda_pos
  have hδ : 0 < δ := div_pos (sub_pos.2 h12) hLam
  have hδ1 : δ < 1 := (div_lt_one hLam).2 hgap
  have eL : rL - u₁ / wwLambda = aL + δ := by dsimp [aL, δ]; rw [sub_div]; ring
  have eR : rR + u₁ / wwLambda = aR - δ := by dsimp [aR, δ]; rw [sub_div]; ring
  have haR : 0 ≤ aR := by
    have hdiv := div_lt_div_of_pos_right h12 hLam
    dsimp [aR]
    linarith only [hR, hdiv]
  have hbL : 0 ≤ aL + δ := add_nonneg hL hδ.le
  have hbR : 0 ≤ aR - δ := by rw [← eR]; exact hR
  rw [eL, eR] at hC₁
  let X := fun ω => Exist.flowField 0 u₁ (h ω)
  let F := fun ω => Exist.flowField 0 u₂ (h ω)
  have hX : ∀ ω, F ω = Exist.flowField 0 (δ * wwLambda) (X ω) := by
    intro ω
    have heδ : δ * wwLambda = u₂ - u₁ := div_mul_cancel₀ _ hLam.ne'
    dsimp [F, X]
    rw [heδ, Sec5.GlueCond.flowField_zero_flowField_zero, sub_add_cancel]
  obtain ⟨Ω₃, mΩ₃, P₃, hP₃, 𝓕₃, W₃, VL₃, VR₃, B₃, ζ₃, h₃, hC₃⟩ :=
    Spec.Provider.exists_isOptionalHullCoupling.{u} (κ := 4) (xL := LP.twoSeedXL) (xR := LP.twoSeedXR)
      (ρL := fun _ : Fin 1 => aR - δ) (ρR := fun _ : Fin 1 => aL + δ)
      (by norm_num) LP.isOrderedForceWord_twoSeed
  have hlaw : P.map X = P₃.map (fun ω => reflectField (h₃ ω)) :=
    map_reflectField_eq_twoSeed ⟨hC₁.2.1, hC₁.2.2.1⟩ ⟨hC₃.2.1, hC₃.2.2.1⟩
  have hRh₃ := measurable_reflectField.comp hC₃.2.1
  have hk := (compProd_map_condDistrib (μ := P₃) hRh₃.aemeasurable
    (measurable_killedHistory hC₃.2.2.2.1).aemeasurable).symm
  exact ae_tail_conditions_of_shift hI hBarrier hChart hL haR hδ hδ1 hbL hbR hC₂ hC₁ hX hC₃ hlaw _ hk

/-- Proposition 4.19 follows once the shifted law and both remaining local inputs
are supplied. The reduction from small height gaps is the proved result of B25. -/
theorem prop419Statement_of_shift
    (hI : ImageWordFiltShiftStatement.{u}) (hBarrier : KilledRightBarrierStatement.{u})
    (hChart : TailChartStatement.{u}) : SeedField.Prop419Statement.{u} :=
  SeedField.prop419Statement_of_seedTailSmall (seedTailSmallStatement_of_shift hI hBarrier hChart)

end InteractingSLE.WangWu.SeedTail
