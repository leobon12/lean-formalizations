/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma725RefDetErase
import InteractingSLE.Spec.Sec7.Lemma725RefChartStrip

/-!
# The determination input of the strip pocket from the ambient recovery and Proposition 5.13

Packet PROVE-LEMMA725REF4, items 1 and 3. Specification §7.4, Aux. lemma 125's proof (`source/spec/p385-432.md`
L197–L250, p. 398) and Lemma 7.25's proof (pp. 413–414).

`PocketDetInput`/`…Inf` (the determination companion of `PocketStopWallsInput`, `Lemma725RefChartWord`) follow from:

* the **ambient recovery** on every word-shape event (`PocketRecoveryInput`/`…Inf`, named input: the ambient field is a
  Borel function of a walls' record and the pocket field in the canonical pocket chart);
* **Proposition 5.13** for the counterflow (named hypothesis, PROVE-PROP513C's form);
* the **measurable pocket erasure**, proved (`Lemma725RefDetErase`) when the walls' σ-algebra is generated up to null
  sets by a standard Borel record `E₀` and the counterflow is continuous on `[0, ∞)`.

**`pocketChartFieldStatement_of_stripPocket_recovery`** is then PROVE-LEMMA725REF3's named input
`PocketChartFieldStatement κ′ r_L r_R` from the strip pocket with the inputs of PROVE-STRIPSYS35's
`pocketWordEvolution_of_stripPocket_walls`, the ambient recovery, Proposition 5.13 and the record `E₀`.

Conditional helpers; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H Hbar)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open InteractingSLE.WangWu (negInv)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.Lemma725RefChart

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketWordAssembly PocketSeedOpen PocketLeftFrontier
  PocketCoupling Lemma725RefSafe

universe u

section Defs

variable {Ω : Type u}

/-- **Named input: the ambient recovery on every word-shape event** (bounded change pocket; Aux. lemma 125's proof,
p. 398). -/
def PocketRecoveryInput (κ : ℝ) (𝓦 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (G : Set Ω) (h : Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) → @IsPointMeasurable Ω 𝓦 R L r G ψ →
    PocketAmbientRecovery (16 / κ) 𝓦 P A (fun ω => cfPocket (R ω) (L ω) r) ψ h

/-- **Named input: the ambient recovery on every word-shape event** (change pocket opening at the flow seed). -/
def PocketRecoveryInputInf (κ : ℝ) (𝓦 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (G : Set Ω) (h : Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) → @IsPointMeasurableInf Ω 𝓦 R L r G ψ →
    PocketAmbientRecovery (16 / κ) 𝓦 P A (fun ω => cfPocket (R ω) (L ω) r) ψ h

end Defs

section Input

variable {Ω : Type u} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **`PocketDetInput` from the ambient recovery, Proposition 5.13 and the measurable pocket erasure** (bounded change
pocket). -/
theorem pocketDetInput_of_recovery [IsProbabilityMeasure P] {κ : ℝ} (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ}
    {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω}
    (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω)) (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {h : Ω → DistOn upperHalfPlaneOpens}
    (h513 : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap h inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t)
    {ε₀ : Type u} [MeasurableSpace ε₀] [StandardBorelSpace ε₀] {E₀ : Ω → ε₀} (hE₀ : Measurable[𝓦] E₀)
    (hgen : 𝓦 ≤ MeasurableSpace.comap E₀ inferInstance ⊔ Ito.nullSets P)
    (hrec : PocketRecoveryInput κ 𝓦 P R L r G h) : PocketDetInput κ 𝓦 P R L r η G h := by
  intro A hA hAG hPA ψ hψ hψm
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hG0 : ∀ ω ∈ G, 0 < rightLo (R ω) (L ω) r := fun ω hω => (hcfg ω hω).bounded
  have hmk := measurable_marks (m := 𝓦) hRm hLm hG hG0 hψm hA hAG
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H
  have hrecA := hrec A hA hAG hPA ψ hψ hψm
  refine ⟨fun hs => ?_, fun _ => ?_⟩
  · exact pocketHistDet_of_recovery hCo hCH (fun ω hω => (hψ ω hω).2.2.2.1) hrecA h513
      (pocketErasure_cfPocket h𝓦 hRm hLm hGm hcfg hηc hηm hA hAG hψ hψm (hmk.2 hs) hmk.1 hE₀ hgen)
  · exact pocketHistDet_of_recovery hCo hCH (fun ω hω => (hψ ω hω).2.2.2.1) hrecA h513
      (pocketErasure_cfPocket h𝓦 hRm hLm hGm hcfg hηc hηm hA hAG hψ hψm measurable_const hmk.1 hE₀ hgen)

/-- **`PocketDetInputInf` from the ambient recovery, Proposition 5.13 and the measurable pocket erasure** (change
pocket opening at the flow seed). -/
theorem pocketDetInputInf_of_recovery [IsProbabilityMeasure P] {κ : ℝ} (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ}
    {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω}
    (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω)) (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {h : Ω → DistOn upperHalfPlaneOpens}
    (h513 : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap h inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t)
    {ε₀ : Type u} [MeasurableSpace ε₀] [StandardBorelSpace ε₀] {E₀ : Ω → ε₀} (hE₀ : Measurable[𝓦] E₀)
    (hgen : 𝓦 ≤ MeasurableSpace.comap E₀ inferInstance ⊔ Ito.nullSets P)
    (hrec : PocketRecoveryInputInf κ 𝓦 P R L r G h) : PocketDetInputInf κ 𝓦 P R L r η G h := by
  intro A hA hAG hPA ψ hψ hψm
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hG0 : ∀ ω ∈ G, rightLo (R ω) (L ω) r = 0 := fun ω hω => (hcfg ω hω).seed
  have hmk := PocketCoupling.measurable_marksInf (m := 𝓦) hRm hLm hG hG0 hψm hA hAG
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H
  have hrecA := hrec A hA hAG hPA ψ hψ hψm
  refine ⟨fun hs => ?_, fun _ => ?_⟩
  · exact pocketHistDet_of_recovery hCo hCH (fun ω hω => (hψ ω hω).2.2.2.1) hrecA h513
      (pocketErasure_cfPocketInf h𝓦 hRm hLm hGm hcfg hηc hηm hA hAG hψ hψm (hmk.2 hs) hmk.1 hE₀ hgen)
  · exact pocketHistDet_of_recovery hCo hCH (fun ω hω => (hψ ω hω).2.2.2.1) hrecA h513
      (pocketErasure_cfPocketInf h𝓦 hRm hLm hGm hcfg hηc hηm hA hAG hψ hψm measurable_const hmk.1 hE₀ hgen)

end Input

/-- **`PocketChartFieldStatement κ′ r_L r_R` from the strip pocket, the ambient recovery and Proposition 5.13**: the
hypotheses of `pocketChartFieldStatement_of_stripPocket_walls` with the determination input replaced by its three
ingredients — the ambient recovery on every configuration event (`hrec`, named input), Proposition 5.13 for the
counterflow (`h513`, named hypothesis), and a standard Borel record `E₀` generating the walls' σ-algebra up to null sets
(the measurable pocket erasure is proved, `Lemma725RefDetErase`). -/
theorem pocketChartFieldStatement_of_stripPocket_recovery {κ' rL rR : ℝ} (hκ' : 4 < κ') (hL : -2 < rL)
    (hLd : rL < κ' / 2 - 4) (hRr : -2 < rR) (hRd : rR < κ' / 2 - 4)
    {Ω : Type u} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (h𝓦 : 𝓦 ≤ mΩ)
    {R β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ q t, Measurable[𝓦] fun ω => Lr q ω t)
    (hβm : ∀ t, Measurable fun ω => β ω t) (hηm : ∀ t : ℝ, 0 ≤ t → Measurable fun ω => η ω t)
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0)) (hηH : ∀ ω, ∀ t : ℝ, 0 ≤ t → η ω t ∈ Hbar)
    (hη0 : ∀ ω, η ω 0 = 0)
    (hR : ∀ᵐ ω ∂P, IsSimpleProper (R ω) ∧ IsWallReverseVisit (R ω) (η ω) ∧ IsWallVisited (R ω) (η ω))
    (hβ : ∀ᵐ ω ∂P, IsSimpleProper (β ω) ∧ IsWallReverseVisit (β ω) (η ω) ∧ IsWallVisited (β ω) (η ω))
    (hLw : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsSimpleProper (Lr q ω) ∧ IsWallReverseVisit (Lr q ω) (η ω) ∧
      Lr q ω (StripSys.rt q) = β ω (StripSys.rt q))
    (hnohit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → η ω t ≠ 0)
    (hlate : ∀ᵐ ω ∂P, ∀ N : ℝ≥0, ∃ t, N ≤ t ∧ β ω t ∉ range (R ω))
    (htrace : ∀ᵐ ω ∂P, IsLoewnerTrace (W ω) (η ω) ∧ Continuous (W ω) ∧ W ω 0 = 0)
    (hav : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (η ω q) ∉ leftSideOf (range (β ω)))
    (hattach : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (Lr q ω) (StripSys.rt q) →
      0 < rightLo (R ω) (Lr q ω) (StripSys.rt q) →
      Sec6.AttachmentConstancy (η ω) (cfPocket (R ω) (Lr q ω) (StripSys.rt q))
        (cfArcR (R ω) (Lr q ω) (StripSys.rt q)) (cfArcL (R ω) (Lr q ω) (StripSys.rt q))
        (firstHit (η ω) (cfArcR (R ω) (Lr q ω) (StripSys.rt q) 1))
        (firstHit (η ω) (cfArcR (R ω) (Lr q ω) (StripSys.rt q) 0)))
    (hattachI : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (Lr q ω) (StripSys.rt q) →
      rightLo (R ω) (Lr q ω) (StripSys.rt q) = 0 →
      Tendsto (fun t => ‖η ω t‖) atTop atTop ∧ IsWallVisited (Lr q ω) (η ω) ∧
        Sec6.AttachmentConstancyInf (η ω) (cfPocket (R ω) (Lr q ω) (StripSys.rt q))
          (cfArcRInf (R ω) (Lr q ω) (StripSys.rt q)) (cfArcLInf (R ω) (Lr q ω) (StripSys.rt q))
          (firstHit (η ω) (cfArcRInf (R ω) (Lr q ω) (StripSys.rt q) 0)))
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    (hin : ∀ q : ℚ, 0 < q → ∀ G : Set Ω, MeasurableSet[𝓦 ⊔ Ito.nullSets P] G → 0 < P G →
      (∀ ω ∈ G, IsChangeConfigInc (R ω) (Lr q ω) (StripSys.rt q) ∧
        discTime 1 < rightHi (R ω) (Lr q ω) (StripSys.rt q)) →
      PocketStopField.PocketStopWallsInput (16 / κ') rL rR (𝓦 ⊔ Ito.nullSets P) P R (Lr q) (StripSys.rt q) W η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (Lr q ω) (StripSys.rt q)} h₀ u ∧
        PocketStopField.PocketStopWallsInputInf (16 / κ') rL rR (𝓦 ⊔ Ito.nullSets P) P R (Lr q) (StripSys.rt q) W η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (Lr q ω) (StripSys.rt q)} h₀ u)
    (h513 : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t)
    {ε₀ : Type u} [MeasurableSpace ε₀] [StandardBorelSpace ε₀] {E₀ : Ω → ε₀} (hE₀ : Measurable[𝓦] E₀)
    (hgen : 𝓦 ≤ MeasurableSpace.comap E₀ inferInstance ⊔ Ito.nullSets P)
    (hrec : ∀ q : ℚ, 0 < q → ∀ G : Set Ω, MeasurableSet[𝓦 ⊔ Ito.nullSets P] G → 0 < P G →
      (∀ ω ∈ G, IsChangeConfigInc (R ω) (Lr q ω) (StripSys.rt q) ∧
        discTime 1 < rightHi (R ω) (Lr q ω) (StripSys.rt q)) →
      PocketRecoveryInput (16 / κ') (𝓦 ⊔ Ito.nullSets P) P R (Lr q) (StripSys.rt q)
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (Lr q ω) (StripSys.rt q)}
          (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) ∧
        PocketRecoveryInputInf (16 / κ') (𝓦 ⊔ Ito.nullSets P) P R (Lr q) (StripSys.rt q)
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (Lr q ω) (StripSys.rt q)}
          (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u)) :
    PocketChartFieldStatement.{u} κ' rL rR := by
  have h𝓦' : 𝓦 ⊔ Ito.nullSets P ≤ mΩ := sup_le h𝓦 (Ito.nullSets_le P)
  have hgen' : 𝓦 ⊔ Ito.nullSets P ≤ MeasurableSpace.comap E₀ inferInstance ⊔ Ito.nullSets P :=
    sup_le hgen le_sup_right
  have hE₀' : Measurable[𝓦 ⊔ Ito.nullSets P] E₀ := hE₀.mono le_sup_left le_rfl
  refine pocketChartFieldStatement_of_stripPocket_walls hκ' hL hLd hRr hRd h𝓦 hRm hLm hβm hηm hηc hηH hη0 hR hβ
    hLw hnohit hlate htrace hav hattach hattachI hh₀ hu hub hin fun q hq G hGm hPG hG hcfg hcfgI => ?_
  have hRm' : ∀ t, Measurable[𝓦 ⊔ Ito.nullSets P] fun ω => R ω t := fun t => (hRm t).mono le_sup_left le_rfl
  have hLm' : ∀ t, Measurable[𝓦 ⊔ Ito.nullSets P] fun ω => Lr q ω t := fun t =>
    (hLm q t).mono le_sup_left le_rfl
  have hconf : ∀ ω ∈ G, IsChangeConfigInc (R ω) (Lr q ω) (StripSys.rt q) := fun ω hω => (hG ω hω).1
  have hGp : MeasurableSet[𝓦 ⊔ Ito.nullSets P] {ω | ω ∈ G ∧ 0 < rightLo (R ω) (Lr q ω) (StripSys.rt q)} :=
    (measurableSet_rightLo_pos_and (mΩ := 𝓦 ⊔ Ito.nullSets P) hRm' hLm' hGm hconf).1
  have hG0 : MeasurableSet[𝓦 ⊔ Ito.nullSets P]
      {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (Lr q ω) (StripSys.rt q)} := by
    have e : {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (Lr q ω) (StripSys.rt q)} =
        G \ {ω | ω ∈ G ∧ 0 < rightLo (R ω) (Lr q ω) (StripSys.rt q)} := by
      ext ω
      exact ⟨fun h => ⟨h.1, fun h' => h.2 h'.2⟩, fun h => ⟨h.1, fun h' => h.2 ⟨h.1, h'⟩⟩⟩
    rw [e]
    exact hGm.diff hGp
  obtain ⟨hrec1, hrec2⟩ := hrec q hq G hGm hPG hG
  exact ⟨pocketDetInput_of_recovery h𝓦' hRm' hLm' hGp (fun ω hω => hcfg ω hω.1 hω.2) hηc hηm h513 hE₀' hgen'
      hrec1,
    pocketDetInputInf_of_recovery h𝓦' hRm' hLm' hG0
      (fun ω hω => hcfgI ω hω.1 (le_antisymm (not_lt.1 hω.2) (hconf ω hω.1).changeCorner_props.1.1)) hηc hηm h513
      hE₀' hgen' hrec2⟩

end InteractingSLE.Sec7.Lemma725RefChart
