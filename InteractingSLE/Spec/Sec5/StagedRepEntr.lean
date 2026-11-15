/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedKCandFreeze
import InteractingSLE.Spec.Sec7.Aux117

/-!
# Prop 5.9's per-candidate representation from a word entrance

Packet PROVE-STAGED-REP (rulings R71, R75, R78). PROVE-STAGEDK-CAND reduced the per-candidate killed law
`IsStageLawFarK` to a stopped representation of the piece (`IsKilledStageRep`, `IsStoppedRep`). The cross-conditioning
law (the θ-template `exists_isWordEntrance_of_filtW` / `…_of_filtTheta`, and its staged port) produces the piece's
law in the form of **Aux. lemma 117's word entrance** (`Sec7.Aux117.IsWordEntrance`: the integrated driving and force
equations before the killing time, driven by a Brownian motion of a filtration containing the past at time `0`). This
file is the generic bridge between the two forms, and the transfer of the killed law along a product extension (the
Brownian motion of a word entrance lives on `Ω × Ω₀`):

* `not_threshold_of_sep`, `not_threshold_of_zero_of_sep`: marks strictly separated from the driver at positive times
  never trigger the continuation threshold, so the threshold clause reduces to time `0`;
* `isSLEPathUpTo_of_isWordEntrance`: a word entrance below the threshold is a local integrated path
  (`Sec2.IsSLEPathUpTo`);
* **`isKilledStageRep_of_entrance`**: the representation `IsKilledStageRep` from a word entrance with the Brownian
  motion as the piece's noise, the threshold at time `0`, strict separation at positive times, the killing at a far
  contact with left limits, and a trace up to the killing time;
* **`IsStageLawFarK.of_prod_fst`**: the killed law on `(Ω × Ω₀, P ⊗ P₀)` of processes read on the first factor, with a
  past pulled back from `Ω`, is the killed law on `(Ω, P)`.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.StagedRep

open Prop59Stage Prop59Nodes StagedKill StagedKCand

/-! ### The threshold clause -/

section Threshold

variable {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **Separated marks never trigger the continuation threshold**: if every mark differs from the driver, both
collision sums are empty. -/
theorem not_threshold_of_sep {w : ℝ} {vL : Fin nL → ℝ} {vR : Fin nR → ℝ} (hL : ∀ i, vL i < w)
    (hR : ∀ j, w < vR j) : ¬ ForceWord.ThresholdCondition ρL ρR w vL vR := by
  have eL : (Finset.univ.filter fun i => vL i = w) = ∅ :=
    Finset.filter_eq_empty_iff.2 fun i _ h => (hL i).ne h
  have eR : (Finset.univ.filter fun j => vR j = w) = ∅ :=
    Finset.filter_eq_empty_iff.2 fun j _ h => (hR j).ne' h
  simp only [ForceWord.ThresholdCondition, eL, eR, Finset.sum_empty, not_or, not_le]
  norm_num

/-- **The threshold clause before `τ` from time `0`**: below the threshold at `0` and strictly separated at positive
times before `τ`. -/
theorem not_threshold_of_zero_of_sep {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {τ : ℝ≥0∞} (h0 : ¬ ForceWord.ThresholdCondition ρL ρR (w 0) (fun i => vL i 0) (fun j => vR j 0))
    (hL : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < τ → ∀ i, vL i t < w t)
    (hR : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < τ → ∀ j, w t < vR j t) :
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ →
      ¬ ForceWord.ThresholdCondition ρL ρR (w t) (fun i => vL i t) (fun j => vR j t) := by
  intro t ht
  rcases eq_zero_or_pos t with rfl | ht0
  · exact h0
  · exact not_threshold_of_sep (hL t ht0 ht) (hR t ht0 ht)

/-- **A word entrance below the threshold is a local integrated path** before its killing time. -/
theorem isSLEPathUpTo_of_isWordEntrance {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {w b : ℝ≥0 → ℝ}
    {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {τ : ℝ≥0∞}
    (hE : Sec7.Aux117.IsWordEntrance a xL xR ρL ρR w vL vR b τ)
    (hthr : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ →
      ¬ ForceWord.ThresholdCondition ρL ρR (w t) (fun i => vL i t) (fun j => vR j t)) :
    Sec2.IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ :=
  ⟨hE.w_zero, hE.vL_zero, hE.vR_zero, hE.continuousOn_w, hE.continuousOn_vL, hE.continuousOn_vR,
    fun ht => hE.antitone_vL _ ht, fun ht => hE.vL_le_w _ ht, fun ht => hE.w_le_vR _ ht,
    fun ht => hE.monotone_vR _ ht, fun ht => hE.integrable_gapL _ ht, fun ht => hE.integrable_gapR _ ht,
    fun ht => hE.w_eq _ ht, fun ht => hE.vL_eq _ ht, fun ht => hE.vR_eq _ ht, hE.volume_collisionL,
    hE.volume_collisionR, fun ht => hthr _ ht⟩

end Threshold

/-! ### The representation from a word entrance -/

section Entrance

variable {Ω : Type*} {𝓠 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL nR : ℕ} {κ : ℝ}
  {R : Set Ω} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {iL : Fin nL} {iR : Fin nR} {y : Ω → Start nL nR}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {𝓕 : Filtration ℝ≥0 mΩ}

/-- **The stopped representation from a word entrance.** A filtration `𝓕` containing the past `𝓠` at time `0` with
a Brownian motion `B`, the piece adapted before its lifetime `ζ`, and almost surely on the stage event: an ordered
strict start whose word is the piece's initial state, the word entrance of the piece driven by `B` before `ζ`, below
the threshold at time `0`, the marks strictly separated from the driver at positive times, the killing at a far
contact with left limits, and a trace up to `ζ`. The piece's own noise is `B`. -/
theorem isKilledStageRep_of_entrance (hle : 𝓠 ≤ 𝓕 0) (hB : IsFilteredBrownianReal 𝓕 B P)
    (hW : AdaptedBefore 𝓕 ζ W) (hVL : ∀ i, AdaptedBefore 𝓕 ζ (VL i)) (hVR : ∀ j, AdaptedBefore 𝓕 ζ (VR j))
    (hpath : ∀ᵐ ω ∂P, ω ∈ R → IsOrderedForceWord (y ω).2.1 (y ω).2.2 ∧ StrictAnti (y ω).2.1 ∧
      StrictMono (y ω).2.2 ∧
      Sec7.Aux117.IsWordEntrance κ (y ω).2.1 (y ω).2.2 ρL ρR (W · ω) (fun i t => VL i t ω)
        (fun j t => VR j t ω) (B · ω) (ζ ω) ∧
      ¬ ForceWord.ThresholdCondition ρL ρR (W 0 ω) (fun i => VL i 0 ω) (fun j => VR j 0 ω) ∧
      (∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < ζ ω → ∀ i, VL i t ω < W t ω) ∧
      (∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < ζ ω → ∀ j, W t ω < VR j t ω) ∧
      IsKilledAtFarLim iL iR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (W · ω) (ζ ω) η) :
    IsKilledStageRep κ P 𝓠 R ρL ρR iL iR y W VL VR B ζ 𝓕 B := by
  refine ⟨hle, hB, hW, hVL, hVR, ?_⟩
  filter_upwards [hpath] with ω hω hR
  obtain ⟨hF, hA, hM, hE, h0, hsL, hsR, hK, htr⟩ := hω hR
  exact ⟨hF, hA, hM, isSLEPathUpTo_of_isWordEntrance hE (not_threshold_of_zero_of_sep h0 hsL hsR), hK, htr,
    fun _ _ => rfl⟩

end Entrance

/-! ### Transfer along a product extension -/

section Prod

variable {Ω : Type*} {𝓠 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {Ω₀ : Type*} [m₀ : MeasurableSpace Ω₀]
  {P : Measure Ω} {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀] {nL nR : ℕ} {κ : ℝ} {R : Set Ω}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {iL : Fin nL} {iR : Fin nR} {y : Ω → Start nL nR}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **The killed law descends from a product extension.** If the processes read on the first factor satisfy the
killed law on `(Ω × Ω₀, P ⊗ P₀)` for the past `𝓠` pulled back by the first projection (which is contained in the
product σ-algebra), then they satisfy it on `(Ω, P)`. -/
theorem IsStageLawFarK.of_prod_fst [SFinite P] (h𝓠 : 𝓠 ≤ mΩ)
    (h : IsStageLawFarK κ (P.prod P₀) (𝓠.comap Prod.fst) (Prod.fst ⁻¹' R) ρL ρR iL iR (fun p => y p.1)
      (fun t p => W t p.1) (fun i t p => VL i t p.1) (fun j t p => VR j t p.1) (fun t p => B t p.1)
      (fun p => ζ p.1)) :
    IsStageLawFarK κ P 𝓠 R ρL ρR iL iR y W VL VR B ζ := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun S hS p hp A hA hAR => ?_⟩
  · have h1' := Measure.ae_ae_of_ae_prod h1
    filter_upwards [h1'] with ω hω hR
    obtain ⟨_, hω'⟩ := hω.exists
    exact hω' hR
  · have hA' : MeasurableSet[𝓠.comap Prod.fst] (Prod.fst ⁻¹' A : Set (Ω × Ω₀)) := ⟨A, hA, rfl⟩
    have hle := h2 S hS p hp _ hA' (preimage_mono hAR)
    have hAm : MeasurableSet A := h𝓠 _ hA
    have e1 : (P.prod P₀) (Prod.fst ⁻¹' A) = P A := by
      rw [← Measure.map_apply measurable_fst hAm, Measure.map_fst_prod, measure_univ, one_smul]
    have e2 : (Prod.fst ⁻¹' A ∩ {p : Ω × Ω₀ | ((fun p => y p.1) p, samp ((fun t p => W t p.1) · p)
        (fun i t => (fun i t p => VL i t p.1) i t p) (fun k t => (fun j t p => VR j t p.1) k t p)
        ((fun p => ζ p.1) p)) ∈ S}) =
        Prod.fst ⁻¹' (A ∩ {ω | (y ω, samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω)) ∈ S}) := by
      ext p
      simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
    rw [e1, e2] at hle
    refine hle.trans ?_
    calc (P.prod P₀) (Prod.fst ⁻¹' (A ∩ {ω | (y ω, samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω)
          (ζ ω)) ∈ S}))
        ≤ ((P.prod P₀).map Prod.fst) (A ∩ {ω | (y ω, samp (W · ω) (fun i t => VL i t ω)
          (fun k t => VR k t ω) (ζ ω)) ∈ S}) := Measure.le_map_apply measurable_fst.aemeasurable _
      _ = P (A ∩ {ω | (y ω, samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω)) ∈ S}) := by
        rw [Measure.map_fst_prod, measure_univ, one_smul]

end Prod

end InteractingSLE.Sec5.CrossCond.StagedRep
