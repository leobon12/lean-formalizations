/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripPocketConfigEvent
import InteractingSLE.Spec.Sec7.PocketCouplingMean
import InteractingSLE.Spec.Sec7.PocketLeftFrontier

/-!
# Theorem 1.3's pocket word from the strip pocket: hPW with the configuration constructed

Packet PROVE-STRIPSYS30. Specification §7.4.1, Aux. lemma 130 and Lemma 7.25's proof (`source/spec/p385-432.md`
L401–L515, pp. 408–414).

PROVE-STRIPSYS26's `PocketCoupling.pocketWordEvolution_of_unionPtInput'` gives `Lemma725Ref.PocketWordEvolution`
(hPW) from a random change pocket on a walls-measurable event of positive probability with its configuration
(`hconf`, `hcfg`, `hcfgI`) and the field-level inputs `PocketUnionPtInput`/`…Inf` on that event. Here the event, its
measurability, its positive probability and the configuration `IsChangeConfigInc` with (RS13.5) are constructed
(`StripPocketConfig.exists_stripPocketEvent_ae`), the orientation comes from the counterflow's avoidance of the left
side of `β = η_{π/2}` (`PocketLeftFrontier.isCfPocketConfig(Inf)_of_cfAvoid`), and the remaining inputs are the
source's facts about the given random objects, all stated almost surely:

* the walls' and counterflow's pathwise facts of `exists_stripPocketEvent` (Lemma 5.7's reverse visit order, the
  counterflow's non-return to its seed, (RS13.3)'s late points, the common prefix of `β` and `β^{(q)}`);
* the counterflow's Loewner trace in the chart `m` with continuous driver from `0`;
* the counterflow's avoidance of the open left side of `β` (non-boundary duality: `β` is the complete left
  counterflow frontier);
* Aux. lemma 37's attachment constancy of the pocket traversal (and, when the pocket opens at the flow seed, the
  counterflow's transience and its visits of the left wall);
* the field-level inputs `PocketUnionPtInput`/`…Inf` for every walls-measurable configuration event (the source's
  "all-stop component mean theorem", stated for the selected configurations; walls' σ-algebra with null sets).

## Main result

* **`pocketWordEvolution_of_stripPocket`**: hPW from these inputs.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open QuantumZipper (H Hbar)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.StripPocketConfig

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketWordAssembly PocketSeedOpen PocketLeftFrontier
  PocketCoupling

/-- **hPW from the strip pocket** (Aux. lemma 130 and Lemma 7.25's proof, pp. 408–414): for `κ′ > 4` and seed weights
`r_L, r_R ∈ (−2, κ′/2 − 4)`, `Lemma725Ref.PocketWordEvolution κ′ r_L r_R` follows from random walls `R = α`,
`β = η_{π/2}`, `Lr q = β^{(q)}` (`q ∈ ℚ_{>0}`, measurable at fixed times for the walls' σ-algebra `𝓦`) and a random
counterflow `η` in the chart `m(z) = −1/z` with driver `W`, through the almost sure pathwise inputs listed in the
module docstring and the field-level pocket inputs for every walls-measurable configuration event. The rational
change time, the event, its positive probability and the configuration are constructed here. -/
theorem pocketWordEvolution_of_stripPocket.{v} {κ' rL rR : ℝ} (hκ' : 4 < κ') (hL : -2 < rL)
    (hLd : rL < κ' / 2 - 4) (hRr : -2 < rR) (hRd : rR < κ' / 2 - 4)
    {Ω : Type v} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
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
    (𝔥 : DistOn upperHalfPlaneOpens)
    (hin : ∀ q : ℚ, 0 < q → ∀ G : Set Ω, MeasurableSet[𝓦 ⊔ Ito.nullSets P] G → 0 < P G →
      (∀ ω ∈ G, IsChangeConfigInc (R ω) (Lr q ω) (StripSys.rt q) ∧
        discTime 1 < rightHi (R ω) (Lr q ω) (StripSys.rt q)) →
      PocketUnionPtInput (16 / κ') rL rR (𝓦 ⊔ Ito.nullSets P) P R (Lr q) (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (Lr q ω) (StripSys.rt q)} h₀ 𝔥 ∧
        PocketUnionPtInputInf (16 / κ') rL rR (𝓦 ⊔ Ito.nullSets P) P R (Lr q) (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (Lr q ω) (StripSys.rt q)} h₀ 𝔥) :
    Lemma725Ref.PocketWordEvolution.{v} κ' rL rR := by
  obtain ⟨q, hq, G, hGm, hPG, hG⟩ := exists_stripPocketEvent_ae (P := P) h𝓦 hRm hLm hβm hηm hηc hηH hη0 hR hβ
    hLw hnohit hlate (Q := fun q ω => (IsLoewnerTrace (W ω) (η ω) ∧ Continuous (W ω) ∧ W ω 0 = 0) ∧
      (∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (η ω q) ∉ leftSideOf (range (β ω))) ∧
      (IsChangeConfigInc (R ω) (Lr q ω) (StripSys.rt q) → 0 < rightLo (R ω) (Lr q ω) (StripSys.rt q) →
        Sec6.AttachmentConstancy (η ω) (cfPocket (R ω) (Lr q ω) (StripSys.rt q))
          (cfArcR (R ω) (Lr q ω) (StripSys.rt q)) (cfArcL (R ω) (Lr q ω) (StripSys.rt q))
          (firstHit (η ω) (cfArcR (R ω) (Lr q ω) (StripSys.rt q) 1))
          (firstHit (η ω) (cfArcR (R ω) (Lr q ω) (StripSys.rt q) 0))) ∧
      (IsChangeConfigInc (R ω) (Lr q ω) (StripSys.rt q) → rightLo (R ω) (Lr q ω) (StripSys.rt q) = 0 →
        Tendsto (fun t => ‖η ω t‖) atTop atTop ∧ IsWallVisited (Lr q ω) (η ω) ∧
          Sec6.AttachmentConstancyInf (η ω) (cfPocket (R ω) (Lr q ω) (StripSys.rt q))
            (cfArcRInf (R ω) (Lr q ω) (StripSys.rt q)) (cfArcLInf (R ω) (Lr q ω) (StripSys.rt q))
            (firstHit (η ω) (cfArcRInf (R ω) (Lr q ω) (StripSys.rt q) 0))) ∧
      IsSimpleProper (β ω) ∧ Lr q ω (StripSys.rt q) = β ω (StripSys.rt q))
    (fun q hq => by
      filter_upwards [htrace, hav, hattach q hq, hattachI q hq, hβ, hLw q hq] with ω h1 h2 h3 h4 h5 h6
      exact ⟨h1, h2, h3, h4, h5.1, h6.2.2⟩)
  obtain ⟨hin1, hin2⟩ := hin q hq G hGm hPG fun ω hω => ⟨(hG ω hω).1, (hG ω hω).2.1⟩
  refine pocketWordEvolution_of_unionPtInput' (W := W) hκ' hL hLd hRr hRd (sup_le h𝓦 (Ito.nullSets_le P))
    (fun t => (hRm t).mono le_sup_left le_rfl) (fun t => (hLm q t).mono le_sup_left le_rfl) hGm hPG
    (fun ω hω => (hG ω hω).1) (fun ω hω hpos => ?_) (fun ω hω h0 => ?_) hηm hh₀ 𝔥 hin1 hin2
  · obtain ⟨hconf, -, hrevR, hrevL, hvisR, ⟨htr, hWc, hW0⟩, havω, hatt, -, hβsp, hLβ⟩ := hG ω hω
    exact isCfPocketConfig_of_cfAvoid hconf hpos htr hWc hW0 hrevR hrevL hvisR (hatt hconf hpos) hβsp hLβ havω
  · obtain ⟨hconf, -, hrevR, hrevL, hvisR, ⟨htr, hWc, hW0⟩, havω, -, hattI, hβsp, hLβ⟩ := hG ω hω
    obtain ⟨htrans, hvisL, hatt⟩ := hattI hconf h0
    exact isCfPocketConfigInf_of_cfAvoid hconf h0 htr hWc hW0 htrans hrevR hrevL hvisR hvisL hatt hβsp hLβ havω

end InteractingSLE.Sec7.StripPocketConfig
