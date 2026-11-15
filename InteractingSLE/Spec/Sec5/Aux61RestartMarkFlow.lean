import InteractingSLE.Spec.Sec5.Aux61RestartGeoProtect
import InteractingSLE.Spec.Sec5.GlueCondHit
import InteractingSLE.Spec.Sec4.Prob41Trace

/-!
# The original target mark for the actual counterflow

Packet PROVE-AUX61-R1. The admissible counterflow word has a seed at zero,
whose noncollision protects every negative real mark. In particular, the
original right target in Q is protected by the mark -1 before inversion.
Only driver agreement through the retained stop is used.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory
open QuantumZipper (IsForwardSol)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.Aux61Restart

open WangWu LawUnique GlueCond CrossCond.Word49 Cond44Ref

/-- A separated seed force at zero protects every negative real point.
No force at the protected point is required. -/
theorem exists_real_forwardSol_of_left_seed
    {a : ℝ} {nL nR : ℕ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ}
    {w b : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ⊤)
    {i : Fin nL} (hi : xL i = 0)
    (hsep : ∀ t : ℝ≥0, 0 < t → vL i t < w t)
    {x : ℝ} (hx : x < 0) (s : ℝ≥0) :
    ∃ v, IsForwardSol (Ito.rpath w) (x : ℂ) s v := by
  have hf := hp.isForcePath
  have hv : Continuous (vL i) := continuousOn_univ.1
    ((hf.continuousOn_vL i).mono fun t _ => ENNReal.coe_lt_top)
  exact Sec4.exists_isForwardSol_of_forceEq_left
    (Sec4.continuous_toNNReal_of_isIntegratedSLEPath hp) hf.w_zero hv
    (fun _ => hf.vL_eq ENNReal.coe_lt_top i)
    (fun _ => hf.intervalIntegrable_forceL ENNReal.coe_lt_top i) hsep hx
    (by rw [hi]; exact hx.le) s.coe_nonneg

/-- The recentered stopped driver equals the actual driver through its stop. -/
theorem cfDrv0_cfHistory_eq_on
    {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω}
    (hζ : ζ ω = ⊤) (hw0 : W 0 ω = 0) (hw : Continuous fun t => W t ω)
    (s : ℝ≥0) :
    EqOn (cfDrv0 s (cfHistory W ζ ω)) (Ito.rpath (W · ω)) (Icc 0 (s : ℝ)) := by
  have heq := eqOn_rpath_cfStop_cfHistory hζ hw0 hw s
  have hzero := heq (show (0 : ℝ) ∈ Icc 0 (s : ℝ) from ⟨le_rfl, s.coe_nonneg⟩)
  simp only [Real.toNNReal_zero, hw0] at hzero
  intro t ht
  change Ito.rpath (Sec4.regPath (cfStop s (cfHistory W ζ ω))) t -
    Ito.rpath (Sec4.regPath (cfStop s (cfHistory W ζ ω))) 0 = _
  rw [heq ht, hzero, sub_zero]
  rfl

/-- The live real mark for the actual stopped counterflow history follows
from the existing seed-force construction and Aux. lemma 6. The conclusion
holds simultaneously at every finite retained time. -/
theorem ae_actual_history_original_mark_alive
    {κ : ℝ} {nL nR : ℕ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ}
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {W B : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    {Ω₂ : Type u} [MeasurableSpace Ω₂] {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ}
    {ζ₂ : Ω₂ → ℝ≥0∞}
    (hκ : 0 < κ) (hκ4 : κ < 4) (hF : IsOrderedForceWord xL xR)
    (h44 : Sec4.Cond44 κ ρL ρR)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂) :
    ∀ᵐ ω ∂P₂, ∀ s : ℝ≥0, ∃ v : ℝ → ℂ,
      IsForwardSol (cfDrv0 s (cfHistory W₂ ζ₂ ω)) (-1 : ℂ) s v := by
  obtain ⟨mL, mR, yL, yR, σL, σR, 𝓕₂, VL₂, VR₂, B₂,
    hF', hadm, hE, ⟨i, hi⟩, -⟩ :=
    exists_seed_admissible_of_isCenteredCounterflowDriver hκ hκ4 hF h44 hC hcf hlaw
  have hk' : 0 < 16 / κ := by positivity
  filter_upwards [Sec4.aux6Statement hk' yL yR σL σR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂
    hF' hadm hE, hE.2.2.2.2]
    with ω ⟨hζ, hsep⟩ hp s
  rw [hζ] at hp
  obtain ⟨v, hv⟩ := exists_real_forwardSol_of_left_seed hp hi
    (fun t ht => (hsep t ht).1 i) (by norm_num : (-1 : ℝ) < 0) s
  have hw : Continuous fun t => W₂ t ω := continuousOn_univ.1
    (hp.isForcePath.continuousOn_w.mono fun t _ => ENNReal.coe_lt_top)
  refine ⟨v, ?_⟩
  have heq := cfDrv0_cfHistory_eq_on hζ hp.1 hw s
  simpa only [ofReal_neg, ofReal_one] using
    QuantumZipper.isForwardSol_congr_drive (fun t ht => (heq ht).symm) hv

end InteractingSLE.Sec5.Aux61Restart
