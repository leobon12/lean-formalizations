/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma725RefReglue
import InteractingSLE.Spec.Sec7.PocketStopWallsFinField

/-!
# Lemma 7.25's determination reference `href725` from the strip pockets, with the enlarged record

Packet PROVE-LEMMA725REF6 (the strip-level re-glue and the wiring of `href725`). Specification §7.4.1, Aux. lemma 130
and Lemma 7.25's proof (`source/spec/p385-432.md` L401–L515, pp. 408–414); rulings R48, R67–R69.

* **`pocketChartFieldStatement_of_stripPocket_marks0`**: STRIPSYS41's `pocketWordEvolution_of_stripPocket_walls0`
  rerun with the pocket chart explicit, concluding `PocketChartFieldStatement κ′ r_L r_R` (the input of `href725`).
  Its inputs are those of STRIPSYS41's theorem (the pathwise strip inputs and the walls law at `T⁰(q)` for the walls'
  σ-algebra `𝓦 ∨ 𝒩`), a standard Borel record `E₀` generating `𝓦` up to null sets, and Proposition 5.13 (`h513`). The
  pocket is selected at one strip level `q` (`exists_stripPocketEvent_ae`), and the record σ-algebra
  `(𝓦 ∨ 𝒩) ∨ σ(h₁^{C_q})` is built for that pocket only (`Lemma725RefMarksWord`): PROVE-LEMMA725REF5 §5 (b).
* **`pocketChartFieldStatement_of_stripPocket_comap`**: the same when the walls' σ-algebra is the σ-algebra of a
  standard Borel walls record `E_w` (e.g. the walls at rational times; the walls are continuous curves), where the
  record hypotheses `hE₀`, `hgen` hold trivially.
* `StripPocketMarksInput κ′ r_L r_R` (**named input**: the strip pocket of Lemma 7.25 for `κ′` with exactly the
  hypotheses of `pocketChartFieldStatement_of_stripPocket_comap`) and
  **`lemma725DetReferenceStatement_of_stripPocketMarks`**: `href725` (`Aux50Hit.Lemma725DetReferenceStatement`) from
  `StripPocketMarksInput` for every `κ′ > 4` and every both-low pair (through
  `Lemma725RefSafe.lemma725DetReferenceStatement_of_pocketChartField`).

Conditional helpers; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses; no `h44`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open QuantumZipper (H Hbar)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open InteractingSLE.WangWu (negInv)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.Lemma725RefMarks

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketWordAssembly PocketSeedOpen PocketLeftFrontier
  PocketCoupling StripPocketConfig Lemma725RefSafe

universe u

/-! ### The strip level -/

section Strip

/-- **`PocketChartFieldStatement κ′ r_L r_R` from the strip pocket, with the enlarged record** (Aux. lemmas 35–36,
119, 124–125 and 130, Lemma 7.25's proof): the hypotheses of STRIPSYS41's
`StripPocketConfig.pocketWordEvolution_of_stripPocket_walls0` (the bounded harmonic mean `u` read as `smoothDist u`),
a standard Borel record `E₀` generating the walls' σ-algebra `𝓦` up to null sets, and Proposition 5.13 for the
counterflow and the field `h₀ + u`. -/
theorem pocketChartFieldStatement_of_stripPocket_marks0 {κ' rL rR : ℝ} (hκ' : 4 < κ') (hL : -2 < rL)
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
      PocketStopField.PocketStopWallsInput0 (16 / κ') rL rR (𝓦 ⊔ Ito.nullSets P) P R (Lr q) (StripSys.rt q) W η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (Lr q ω) (StripSys.rt q)} h₀ u ∧
        PocketStopField.PocketStopWallsInputInf0 (16 / κ') rL rR (𝓦 ⊔ Ito.nullSets P) P R (Lr q) (StripSys.rt q) W η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (Lr q ω) (StripSys.rt q)} h₀ u)
    (h513 : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t)
    {ε₀ : Type u} [MeasurableSpace ε₀] [StandardBorelSpace ε₀] {E₀ : Ω → ε₀} (hE₀ : Measurable[𝓦] E₀)
    (hgen : 𝓦 ≤ MeasurableSpace.comap E₀ inferInstance ⊔ Ito.nullSets P) :
    PocketChartFieldStatement.{u} κ' rL rR := by
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
  have hcfg : ∀ ω ∈ G, 0 < rightLo (R ω) (Lr q ω) (StripSys.rt q) →
      IsCfPocketConfig (R ω) (Lr q ω) (StripSys.rt q) (W ω) (η ω) := fun ω hω hpos => by
    obtain ⟨hconf, -, hrevR, hrevL, hvisR, ⟨htr, hWc, hW0⟩, havω, hatt, -, hβsp, hLβ⟩ := hG ω hω
    exact isCfPocketConfig_of_cfAvoid hconf hpos htr hWc hW0 hrevR hrevL hvisR (hatt hconf hpos) hβsp hLβ havω
  have hcfgI : ∀ ω ∈ G, rightLo (R ω) (Lr q ω) (StripSys.rt q) = 0 →
      IsCfPocketConfigInf (R ω) (Lr q ω) (StripSys.rt q) (W ω) (η ω) := fun ω hω h0 => by
    obtain ⟨hconf, -, hrevR, hrevL, hvisR, ⟨htr, hWc, hW0⟩, havω, -, hattI, hβsp, hLβ⟩ := hG ω hω
    obtain ⟨htrans, hvisL, hatt⟩ := hattI hconf h0
    exact isCfPocketConfigInf_of_cfAvoid hconf h0 htr hWc hW0 htrans hrevR hrevL hvisR hvisL hatt hβsp hLβ havω
  obtain ⟨hin1, hin2⟩ := hin q hq G hGm hPG fun ω hω => ⟨(hG ω hω).1, (hG ω hω).2.1⟩
  exact pocketChartField_of_changeConfig'_marks0 (W := W) hκ' hL hLd hRr hRd (sup_le h𝓦 (Ito.nullSets_le P))
    (fun t => (hRm t).mono le_sup_left le_rfl) (fun t => (hLm q t).mono le_sup_left le_rfl) hGm hPG
    (fun ω hω => (hG ω hω).1) hcfg hcfgI hηm hh₀ hu hub hin1 hin2 (hE₀.mono le_sup_left le_rfl)
    (sup_le_sup_right hgen _ |>.trans (by rw [sup_assoc, sup_idem])) hηc h513

/-- **The strip level with the walls' σ-algebra generated by a standard Borel walls record** `E_w` (the record
hypotheses of `pocketChartFieldStatement_of_stripPocket_marks0` then hold trivially). -/
theorem pocketChartFieldStatement_of_stripPocket_comap {κ' rL rR : ℝ} (hκ' : 4 < κ') (hL : -2 < rL)
    (hLd : rL < κ' / 2 - 4) (hRr : -2 < rR) (hRd : rR < κ' / 2 - 4)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ε₀ : Type u} [MeasurableSpace ε₀] [StandardBorelSpace ε₀] {Ew : Ω → ε₀} (hEw : Measurable Ew)
    {R β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hRm : ∀ t, Measurable[(MeasurableSpace.comap Ew inferInstance)] fun ω => R ω t)
    (hLm : ∀ q t, Measurable[(MeasurableSpace.comap Ew inferInstance)] fun ω => Lr q ω t)
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
    (hin : ∀ q : ℚ, 0 < q → ∀ G : Set Ω,
      MeasurableSet[(MeasurableSpace.comap Ew inferInstance) ⊔ Ito.nullSets P] G → 0 < P G →
      (∀ ω ∈ G, IsChangeConfigInc (R ω) (Lr q ω) (StripSys.rt q) ∧
        discTime 1 < rightHi (R ω) (Lr q ω) (StripSys.rt q)) →
      PocketStopField.PocketStopWallsInput0 (16 / κ') rL rR
        ((MeasurableSpace.comap Ew inferInstance) ⊔ Ito.nullSets P) P R (Lr q) (StripSys.rt q) W η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (Lr q ω) (StripSys.rt q)} h₀ u ∧
        PocketStopField.PocketStopWallsInputInf0 (16 / κ') rL rR
        ((MeasurableSpace.comap Ew inferInstance) ⊔ Ito.nullSets P) P R (Lr q) (StripSys.rt q) W η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (Lr q ω) (StripSys.rt q)} h₀ u)
    (h513 : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t)
    :
    PocketChartFieldStatement.{u} κ' rL rR :=
  pocketChartFieldStatement_of_stripPocket_marks0 (𝓦 := MeasurableSpace.comap Ew inferInstance) hκ' hL hLd hRr hRd
    hEw.comap_le hRm hLm hβm hηm hηc hηH hη0 hR hβ hLw hnohit hlate htrace hav hattach hattachI hh₀ hu hub hin h513
    (comap_measurable Ew) le_sup_left

end Strip

/-! ### The walls' record at rational times -/

section Record

variable {Ω : Type*}

/-- **The walls at rational times**, a standard Borel record of the strip walls. -/
def wallsRec (R : Ω → ℝ≥0 → ℂ) (Lr : ℚ → Ω → ℝ≥0 → ℂ) (ω : Ω) : (ℚ≥0 → ℂ) × (ℚ → ℚ≥0 → ℂ) :=
  (fun t => R ω t, fun q t => Lr q ω t)

/-- A random path continuous at every sample is measurable at every time once it is measurable at rational times. -/
theorem measurable_apply_of_continuous_rat {m : MeasurableSpace Ω} {S : Ω → ℝ≥0 → ℂ} (hc : ∀ ω, Continuous (S ω))
    (hq : ∀ t : ℚ≥0, Measurable[m] fun ω => S ω t) (t : ℝ≥0) : Measurable[m] fun ω => S ω t := by
  obtain ⟨q, hqt⟩ := Lemma725RefChart.exists_seq_rat_tendsto t.coe_nonneg
  have hq' : Tendsto (fun n => ((q n : ℚ≥0) : ℝ≥0)) atTop (𝓝 t) := by
    rw [← NNReal.tendsto_coe]
    exact hqt
  exact measurable_of_tendsto_metrizable (fun n => hq (q n)) (tendsto_pi_nhds.2 fun ω => ((hc ω).tendsto t).comp hq')

theorem measurable_wallsRec_fst {R : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (t : ℝ≥0) :
    Measurable[MeasurableSpace.comap (wallsRec R Lr) inferInstance] fun ω => R ω t := by
  have h : Measurable[MeasurableSpace.comap (wallsRec R Lr) inferInstance] (wallsRec R Lr) := comap_measurable _
  exact measurable_apply_of_continuous_rat hRc (fun s => (measurable_pi_apply s).comp (measurable_fst.comp h)) t

theorem measurable_wallsRec_snd {R : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} (hLc : ∀ q ω, Continuous (Lr q ω))
    (q : ℚ) (t : ℝ≥0) : Measurable[MeasurableSpace.comap (wallsRec R Lr) inferInstance] fun ω => Lr q ω t := by
  have h : Measurable[MeasurableSpace.comap (wallsRec R Lr) inferInstance] (wallsRec R Lr) := comap_measurable _
  exact measurable_apply_of_continuous_rat (hLc q)
    (fun s => (measurable_pi_apply s).comp ((measurable_pi_apply q).comp (measurable_snd.comp h))) t

theorem measurable_wallsRec [MeasurableSpace Ω] {R : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ}
    (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ q t, Measurable fun ω => Lr q ω t) :
    Measurable (wallsRec R Lr) := by
  unfold wallsRec
  exact (measurable_pi_iff.2 fun s : ℚ≥0 => hRm s).prodMk
    (measurable_pi_iff.2 fun q => measurable_pi_iff.2 fun s : ℚ≥0 => hLm q s)

end Record

/-- **The strip level with the walls' σ-algebra of the walls at rational times** (`E₀ = wallsRec R Lr`, for walls
continuous at every sample): `pocketChartFieldStatement_of_stripPocket_comap` with this record. -/
theorem pocketChartFieldStatement_of_stripPocket_rat {κ' rL rR : ℝ} (hκ' : 4 < κ') (hL : -2 < rL)
    (hLd : rL < κ' / 2 - 4) (hRr : -2 < rR) (hRd : rR < κ' / 2 - 4)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {R β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ q ω, Continuous (Lr q ω))
    (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ q t, Measurable fun ω => Lr q ω t)
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
    (hin : ∀ q : ℚ, 0 < q → ∀ G : Set Ω,
      MeasurableSet[(MeasurableSpace.comap (wallsRec R Lr) inferInstance) ⊔ Ito.nullSets P] G → 0 < P G →
      (∀ ω ∈ G, IsChangeConfigInc (R ω) (Lr q ω) (StripSys.rt q) ∧
        discTime 1 < rightHi (R ω) (Lr q ω) (StripSys.rt q)) →
      PocketStopField.PocketStopWallsInput0 (16 / κ') rL rR
        ((MeasurableSpace.comap (wallsRec R Lr) inferInstance) ⊔ Ito.nullSets P) P R (Lr q) (StripSys.rt q) W η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (Lr q ω) (StripSys.rt q)} h₀ u ∧
        PocketStopField.PocketStopWallsInputInf0 (16 / κ') rL rR
        ((MeasurableSpace.comap (wallsRec R Lr) inferInstance) ⊔ Ito.nullSets P) P R (Lr q) (StripSys.rt q) W η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (Lr q ω) (StripSys.rt q)} h₀ u)
    (h513 : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t)
    :
    PocketChartFieldStatement.{u} κ' rL rR := by
  have : StandardBorelSpace (ULift.{u} ((ℚ≥0 → ℂ) × (ℚ → ℚ≥0 → ℂ))) :=
    LQGMetric.standardBorelSpace_of_measurableEquiv MeasurableEquiv.ulift
  exact pocketChartFieldStatement_of_stripPocket_marks0 (𝓦 := MeasurableSpace.comap (wallsRec R Lr) inferInstance)
    hκ' hL hLd hRr hRd (measurable_wallsRec hRm hLm).comap_le (measurable_wallsRec_fst hRc)
    (measurable_wallsRec_snd hLc) hβm hηm hηc hηH hη0 hR hβ hLw hnohit hlate htrace hav hattach hattachI hh₀ hu hub
    hin h513 (E₀ := fun ω => ULift.up.{u} (wallsRec R Lr ω)) (measurable_up.comp (comap_measurable _))
    ((show Measurable[MeasurableSpace.comap (fun ω => ULift.up.{u} (wallsRec R Lr ω)) inferInstance]
      (wallsRec R Lr) from measurable_down.comp (comap_measurable _)).comap_le.trans le_sup_left)

/-! ### The wiring of `href725` -/

section Wire

/-- **Named input: Lemma 7.25's strip pocket for `κ′` with the walls' record** (Aux. lemmas 35–36, 119, 124–125 and
130): a standard Borel probability space, a standard Borel walls record `E_w` whose σ-algebra is the walls'
σ-algebra, the strip walls `R`, `β`, `L_q` and the counterflow `η` with STRIPSYS41's pathwise inputs, the zero-boundary
GFF `h₀` and the bounded harmonic mean `u`, the walls union law at `T⁰(q)` (`PocketStopWallsInput0`/`…Inf0`), and
Proposition 5.13 for `η` and `h₀ + u` — exactly the hypotheses of `pocketChartFieldStatement_of_stripPocket_comap`.
**Not proved in Lean.** -/
def StripPocketMarksInput (κ' rL rR : ℝ) : Prop :=
  ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
    (ε₀ : Type u) (_ : MeasurableSpace ε₀) (_ : StandardBorelSpace ε₀) (Ew : Ω → ε₀)
    (R β : Ω → ℝ≥0 → ℂ) (Lr : ℚ → Ω → ℝ≥0 → ℂ) (W : Ω → ℝ → ℝ) (η : Ω → ℝ → ℂ)
    (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ),
    Measurable Ew ∧
      (∀ t, Measurable[(MeasurableSpace.comap Ew inferInstance)] fun ω => R ω t) ∧
      (∀ q t, Measurable[(MeasurableSpace.comap Ew inferInstance)] fun ω => Lr q ω t) ∧
      (∀ t, Measurable fun ω => β ω t) ∧
      (∀ t : ℝ, 0 ≤ t → Measurable fun ω => η ω t) ∧
      (∀ ω, ContinuousOn (η ω) (Ici 0)) ∧
      (∀ ω, ∀ t : ℝ, 0 ≤ t → η ω t ∈ Hbar) ∧
      (∀ ω, η ω 0 = 0) ∧
      (∀ᵐ ω ∂P, IsSimpleProper (R ω) ∧ IsWallReverseVisit (R ω) (η ω) ∧ IsWallVisited (R ω) (η ω)) ∧
      (∀ᵐ ω ∂P, IsSimpleProper (β ω) ∧ IsWallReverseVisit (β ω) (η ω) ∧ IsWallVisited (β ω) (η ω)) ∧
      (∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsSimpleProper (Lr q ω) ∧ IsWallReverseVisit (Lr q ω) (η ω) ∧
      Lr q ω (StripSys.rt q) = β ω (StripSys.rt q)) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → η ω t ≠ 0) ∧
      (∀ᵐ ω ∂P, ∀ N : ℝ≥0, ∃ t, N ≤ t ∧ β ω t ∉ range (R ω)) ∧
      (∀ᵐ ω ∂P, IsLoewnerTrace (W ω) (η ω) ∧ Continuous (W ω) ∧ W ω 0 = 0) ∧
      (∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (η ω q) ∉ leftSideOf (range (β ω))) ∧
      (∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (Lr q ω) (StripSys.rt q) →
      0 < rightLo (R ω) (Lr q ω) (StripSys.rt q) →
      Sec6.AttachmentConstancy (η ω) (cfPocket (R ω) (Lr q ω) (StripSys.rt q))
      (cfArcR (R ω) (Lr q ω) (StripSys.rt q)) (cfArcL (R ω) (Lr q ω) (StripSys.rt q))
      (firstHit (η ω) (cfArcR (R ω) (Lr q ω) (StripSys.rt q) 1))
      (firstHit (η ω) (cfArcR (R ω) (Lr q ω) (StripSys.rt q) 0))) ∧
      (∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (Lr q ω) (StripSys.rt q) →
      rightLo (R ω) (Lr q ω) (StripSys.rt q) = 0 →
      Tendsto (fun t => ‖η ω t‖) atTop atTop ∧ IsWallVisited (Lr q ω) (η ω) ∧
      Sec6.AttachmentConstancyInf (η ω) (cfPocket (R ω) (Lr q ω) (StripSys.rt q))
      (cfArcRInf (R ω) (Lr q ω) (StripSys.rt q)) (cfArcLInf (R ω) (Lr q ω) (StripSys.rt q))
      (firstHit (η ω) (cfArcRInf (R ω) (Lr q ω) (StripSys.rt q) 0))) ∧
      (IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P) ∧
      (InnerProductSpace.HarmonicOnNhd u H) ∧
      (∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M) ∧
      (∀ q : ℚ, 0 < q → ∀ G : Set Ω,
      MeasurableSet[(MeasurableSpace.comap Ew inferInstance) ⊔ Ito.nullSets P] G → 0 < P G →
      (∀ ω ∈ G, IsChangeConfigInc (R ω) (Lr q ω) (StripSys.rt q) ∧
      discTime 1 < rightHi (R ω) (Lr q ω) (StripSys.rt q)) →
      PocketStopField.PocketStopWallsInput0 (16 / κ') rL rR
        ((MeasurableSpace.comap Ew inferInstance) ⊔ Ito.nullSets P) P R (Lr q) (StripSys.rt q) W η
      {ω | ω ∈ G ∧ 0 < rightLo (R ω) (Lr q ω) (StripSys.rt q)} h₀ u ∧
      PocketStopField.PocketStopWallsInputInf0 (16 / κ') rL rR
        ((MeasurableSpace.comap Ew inferInstance) ⊔ Ito.nullSets P) P R (Lr q) (StripSys.rt q) W η
      {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (Lr q ω) (StripSys.rt q)} h₀ u) ∧
      (∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t)

/-- **`PocketChartFieldStatement κ′ r_L r_R` from the named strip input.** -/
theorem pocketChartFieldStatement_of_stripPocketMarksInput {κ' rL rR : ℝ} (hκ' : 4 < κ') (hL : -2 < rL)
    (hLd : rL < κ' / 2 - 4) (hRr : -2 < rR) (hRd : rR < κ' / 2 - 4) (h : StripPocketMarksInput.{u} κ' rL rR) :
    PocketChartFieldStatement.{u} κ' rL rR := by
  obtain ⟨Ω, mΩ, hSB, P, hP, ε₀, mε, hSBε, Ew, R, β, Lr, W, η, h₀, u, hEw, hRm, hLm, hβm, hηm, hηc, hηH, hη0, hR,
    hβ, hLw, hnohit, hlate, htrace, hav, hattach, hattachI, hh₀, hu, hub, hin, h513⟩ := h
  exact pocketChartFieldStatement_of_stripPocket_comap hκ' hL hLd hRr hRd hEw hRm hLm hβm hηm hηc hηH hη0 hR hβ hLw
    hnohit hlate htrace hav hattach hattachI hh₀ hu hub hin h513

/-- **Lemma 7.25's determination reference `href725`** (`Aux50Hit.Lemma725DetReferenceStatement`) from Lemma 7.25's
strip pockets with the walls' record, for every `κ′ > 4` and every both-low pair
(`Lemma725RefSafe.lemma725DetReferenceStatement_of_pocketChartField`). -/
theorem lemma725DetReferenceStatement_of_stripPocketMarks
    (h : ∀ κ' : ℝ, 4 < κ' → ∀ rL rR : ℝ, -2 < rL → rL < κ' / 2 - 4 → -2 < rR → rR < κ' / 2 - 4 →
      StripPocketMarksInput.{u} κ' rL rR) :
    Aux50Hit.Lemma725DetReferenceStatement.{u} :=
  lemma725DetReferenceStatement_of_pocketChartField fun κ' hκ' rL rR hL hLd hR hRd =>
    pocketChartFieldStatement_of_stripPocketMarksInput hκ' hL hLd hR hRd (h κ' hκ' rL rR hL hLd hR hRd)

end Wire

end InteractingSLE.Sec7.Lemma725RefMarks
