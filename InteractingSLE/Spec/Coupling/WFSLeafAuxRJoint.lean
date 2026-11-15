/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafAuxRHistory
import InteractingSLE.Spec.Restart.Aux54Loc

/-!
# Joint field--history identification at a regular Galmarino stop

R79's unconditional Aux. 54 extension preserves the original whole field.
Its optional coupling has the common full joint law from Theorems 1.2--1.3.
Reading the original rule on that extension identifies the stopped joint law,
without constructing a retained mean graph or assuming a field-kernel input.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WFS

open LawUnique Restart.StoppedExtendWF Restart.StoppedExtend LQGMetric

/-- The full joint-law comparison is proved for the regular stopped couplings
of R79. The regularity and closed-stop coupling premises remain explicit. -/
theorem map_field_ruleHistory_eq_of_regularStopped
    {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR)
    (hdet : LP.HasFieldDeterminedHistories.{u} κ xL xR ρL ρR)
    {R : HistorySpace nL nR → ℝ≥0∞} (hRm : Measurable R) (hRg : IsHistGalmarino R)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hSC : IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h)
    (hV : ∀ᵐ ω ∂P, V ω = R (killedHistory W VL VR V ω))
    (hreg : Restart.Aux54.IsRegularStop ρL ρR P W VL VR V)
    {Ω₀ : Type u} {mΩ₀ : MeasurableSpace Ω₀} {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]
    {𝓕₀ : Filtration ℝ≥0 mΩ₀} {W₀ : ℝ≥0 → Ω₀ → ℝ}
    {VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ} {VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ}
    {B₀ : ℝ≥0 → Ω₀ → ℝ} {ζ₀ : Ω₀ → ℝ≥0∞} {h₀ : Ω₀ → DistOn upperHalfPlaneOpens}
    (hC₀ : IsOptionalHullCoupling κ xL xR ρL ρR P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀) :
    P.map (fun ω => (h ω, killedHistory W VL VR V ω)) =
      P₀.map (fun ω => (h₀ ω, killedHistory W₀ VL₀ VR₀
        (fun ω => min (R (killedHistory W₀ VL₀ VR₀ ζ₀ ω)) (ζ₀ ω)) ω)) := by
  obtain ⟨C, mC, K, hK, 𝓕', W', VL', VR', B', ζ', hC', hag⟩ :=
    Restart.Aux54.stoppedHullExtendRStatement hκ xL xR ρL ρR hF R hRm hRg
      P 𝓕 W VL VR B V h hSC hV hreg
  let : MeasurableSpace C := mC
  let : IsMarkovKernel K := hK
  have hπP : (P ⊗ₘ K).map Prod.fst = P := Measure.fst_compProd P K
  have hq : Measure.QuasiMeasurePreserving Prod.fst (P ⊗ₘ K) P :=
    ⟨measurable_fst, hπP.le.absolutelyContinuous⟩
  have hY : Measurable (killedHistory W VL VR V) := measurable_killedHistory hSC.2.2.2.2.choose
  have he : ∀ᵐ p ∂(P ⊗ₘ K),
      ruleKill R (killedHistory W' VL' VR' ζ' p) = killedHistory W VL VR V p.1 := by
    filter_upwards [hq.ae hV, hq.ae hSC.1.ae_path,
      hC'.1.isSLEEvolutionUpTo.ae_path, hag] with p hVp hp hp' hagp
    refine ruleKill_eq_of_prefix hRg
      (isKilledContHist_killedHistory (continuousOn_state_of_isSLEPathUpTo hp))
      (isKilledContHist_killedHistory (continuousOn_state_of_isSLEPathUpTo hp'))
      (historyNormalize_killedHistory _ _ _ _ _) hVp.symm hagp.1 ?_
    intro q hqt
    change (dyadicTime q : ℝ≥0∞) < V p.1 at hqt
    have ha := hagp.2 (dyadicTime q) hqt.le (hqt.trans_le hagp.1)
    simp only [killedHistory, hqt, hqt.trans_le hagp.1, ↓reduceIte]
    exact Prod.ext ha.1.symm (Prod.ext (funext fun i => (ha.2.1 i).symm)
      (funext fun j => (ha.2.2 j).symm))
  have hlaw := map_field_ruleHistory_eq hdet hRm hC' hC₀
  rw [← ruleKill_killedHistory] at hlaw
  have hleft : (P ⊗ₘ K).map
      (fun p => (h p.1, (ruleKill R ∘ killedHistory W' VL' VR' ζ') p)) =
      P.map (fun ω => (h ω, killedHistory W VL VR V ω)) := by
    calc
      (P ⊗ₘ K).map (fun p => (h p.1, (ruleKill R ∘ killedHistory W' VL' VR' ζ') p)) =
          (P ⊗ₘ K).map (fun p => (h p.1, killedHistory W VL VR V p.1)) := by
        apply Measure.map_congr
        filter_upwards [he] with p hp using Prod.ext rfl hp
      _ = ((P ⊗ₘ K).map Prod.fst).map (fun ω => (h ω, killedHistory W VL VR V ω)) :=
        (Measure.map_map (hSC.2.2.1.prodMk hY) measurable_fst).symm
      _ = _ := by rw [hπP]
  exact hleft.symm.trans hlaw

end InteractingSLE.WFS
