/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.Aux54Loc
import InteractingSLE.Spec.Restart.StoppedK2Wire

/-!
# Stopped trace determination at a regular history rule

The R79 extension theorem gives the stopped trace match, including the finite
endpoint. The rule and its almost sure identity with the stop are explicit;
the obsolete arbitrary-stop extension is not assumed.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

namespace InteractingSLE.Wire.RetMatch

open Restart Restart.StoppedExtend Restart.StoppedExtendWF Restart.FCDet
open LawUnique Sec2.Assembly Sec7.PocketTraversal

/-- A typed stopped coupling at a regular history rule has the canonical trace
through its closed lifetime. This uses R79 and Theorem 1.3. -/
theorem ae_codeMatch_of_regular_coupling
    {κ θ : ℝ} (h13 : Exist.Theorem13Statement.{0}) (hκ : 0 < κ)
    {Fc : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hFc : IsCanonicalFlowCode κ θ Fc) {c : BoundaryWord}
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hord : IsOrderedForceWord xL xR) (htype : IsFlowType κ θ c xL xR ρL ρR)
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    {Hc X : Ω → DistOn upperHalfPlaneOpens}
    (hXH : ∀ ω, IsTranslateAddConst 0 (θ * QuantumZipper.chiC κ) (Hc ω) (X ω))
    (hSC : IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V X)
    {R : HistorySpace nL nR → ℝ≥0∞} (hRm : Measurable R) (hRg : IsHistGalmarino R)
    (hR : ∀ᵐ ω ∂P, V ω = R (killedHistory W VL VR V ω))
    (hreg : Aux54.IsRegularStop ρL ρR P W VL VR V)
    {γ : Ω → ℝ≥0 → ℂ}
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (V ω) (γ ω)) :
    ∀ᵐ ω ∂P, V ω ≤ (Fc ((c, 0), Hc ω)).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V ω →
        γ ω t = decPath (Fc ((c, 0), Hc ω)) t := by
  obtain ⟨C, mC, K, hK, 𝓕', W', VL', VR', B', ζ', hC, hag⟩ :=
    Aux54.stoppedHullExtendRStatement hκ xL xR ρL ρR hord R hRm hRg
      P 𝓕 W VL VR B V X hSC hR hreg
  obtain ⟨eL, eR, hxL, hxR, hρL, hρR⟩ := htype
  have hSC' := StoppedK2.isStoppedHullCoupling_cast eL eR hSC
  have hC' := isOptionalHullCoupling_cast eL eR hC
  rw [hxL, hxR, hρL, hρR] at hSC' hC'
  have hag' : ∀ᵐ p ∂(P ⊗ₘ K), V p.1 ≤ ζ' p ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V p.1 → (t : ℝ≥0∞) < ζ' p →
        W' t p = W t p.1 ∧
          (∀ i, VL' (Fin.cast eL i) t p = VL (Fin.cast eL i) t p.1) ∧
          ∀ j, VR' (Fin.cast eR j) t p = VR (Fin.cast eR j) t p.1 := by
    filter_upwards [hag] with p hp
    exact ⟨hp.1, fun t ht ht' =>
      ⟨(hp.2 t ht ht').1, fun i => (hp.2 t ht ht').2.1 _,
        fun j => (hp.2 t ht ht').2.2 _⟩⟩
  have htr' : ∀ᵐ ω ∂P,
      IsGeneratingTrace (fun t => W t ω) (V ω) (fun t => γ ω t - (0 : ℝ)) := by
    simpa only [Complex.ofReal_zero, sub_zero] using htr
  exact ae_of_ae_compProd_fst (K := K)
    (ae_stopMatch_on_extension (G := fun f => Fc ((c, 0), f))
      h13 hκ (IsCanonicalFlowCode.isFlowDet hFc c 0) hXH
      hSC'.1.ae_path htr' (Measure.fst_compProd P K) hC' hag')

end InteractingSLE.Wire.RetMatch
