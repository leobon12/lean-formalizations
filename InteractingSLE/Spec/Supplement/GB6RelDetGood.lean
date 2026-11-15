/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6RestartProof
import InteractingSLE.Spec.Restart.ChartGauss
import InteractingSLE.Spec.Restart.Kernel
import InteractingSLE.Spec.Sec5.MarkovOther
import InteractingSLE.Spec.Sec7.StripSysBorel
import InteractingSLE.Spec.Exist.FlowField
import InteractingSLE.Spec.Theorem15Inputs

/-!
# GB6's (Det): the good-code clause

Packet PROVE-GB6-RELDET. `GB6RelDetStatement` (PROVE-GB6-RESTART) has two clauses, almost surely on
`{s < ζα, α(s) ∈ ℍ}`: the canonical driver code `F (β, Hc)` of the conditional field is good, and the hull identity
before the first contact. This file proves the first clause unconditionally and isolates the second as
`GB6HullDetStatement`.

* `isGoodDrvCode_of_driverCodeMatch`: a code matched by a driver continuous before its lifetime is good;
* **`ae_isGoodDrvCode_gffLaw`**: for every sorted word `c` and every canonical driver code `F` at angle `0`, `F (c, ·)`
  is good for almost every sample of the GFF of `c` (Theorem 1.1's coupling of the flow-line word of `c` on a standard
  Borel space, the determination clause of `F`, and uniqueness of the GFF law);
* `ae_isGoodDrvCode_of_isGFF`: the same for any GFF with the data of `c`;
* **`ae_isGoodDrvCode_gb6`**: the good-code clause of `GB6RelDetStatement` (GB6's (R1), `gb6_condDet_r1`, makes the
  chart field, given the record of the flow prefix, the GFF of the conditional word; a disintegrating kernel carries
  the good event back);
* **`GB6HullDetStatement`** (the hull-identity clause alone) and **`gb6RelDetStatement_of_hullDet`**.

Nothing here uses Theorem 1.2/1.3 or any `*_of_param` result.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE

namespace Supp8

namespace GB6

open Restart Sec2.Assembly Exist.Staged Exist.StagedLaw Sec7.StripSysField

/-! ### Good codes from continuous drivers -/

/-- **A code matched by a driver continuous before its lifetime is good.** -/
theorem isGoodDrvCode_of_driverCodeMatch {p : PCode × ℝ≥0∞} {W : ℝ≥0 → ℝ} {L : ℝ≥0∞}
    (hm : IsDriverCodeMatch p W L) (hW : ContinuousOn W {t | (t : ℝ≥0∞) < L}) : IsGoodDrvCode p := by
  intro n k hd
  have hdL : ((dyad n k : ℝ≥0) : ℝ≥0∞) < L := by rw [hm.1]; exact hd
  have hWI : ContinuousOn W (Iic (dyad n k)) := hW.mono fun t ht =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (mem_Iic.1 ht)) hdL
  have he := uc_enc hWI
  intro m
  obtain ⟨N, hN⟩ := he m
  refine ⟨N, fun n₁ k₁ n₂ k₂ h₁ h₂ hclose => ?_⟩
  have e₁ : p.1 n₁ k₁ = W (dyad n₁ k₁) :=
    (hm.2.2 n₁ k₁ (lt_of_le_of_lt (ENNReal.coe_le_coe.2 h₁) hdL)).symm
  have e₂ : p.1 n₂ k₂ = W (dyad n₂ k₂) :=
    (hm.2.2 n₂ k₂ (lt_of_le_of_lt (ENNReal.coe_le_coe.2 h₂) hdL)).symm
  rw [e₁, e₂]
  exact hN n₁ k₁ n₂ k₂ h₁ h₂ hclose

/-! ### Canonical codes are good under the GFF of a word -/

/-- **A canonical driver code is good under the GFF of a sorted word.** For every sorted word `c` and every canonical
driver code `F` at angle `0` (any `κ > 0`), `F (c, g)` is good for almost every sample `g` of the GFF of `c`. Proof:
Theorem 1.1's coupling of the flow-line word of `c` (on a standard Borel space in `Type`) is an angle-`0` flow-line
driver of its field, which is a GFF with the data of `c`; the determination clause of `F` matches the coupling's driver,
continuous before its lifetime, so the code is good almost surely; the two GFFs have one law. -/
theorem ae_isGoodDrvCode_gffLaw {κ : ℝ} (hκ : 0 < κ) {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hF : IsCanonicalDriverCode κ 0 F) {c : BoundaryWord} (hc : c.IsSorted) :
    ∀ᵐ g ∂c.gffLaw, IsGoodDrvCode (F (c, g)) := by
  obtain ⟨Ω₀, mΩ₀, -, P₀, hP₀, 𝓕, W, VL, VR, B, ζ, X, hC⟩ :=
    Sec7.StripSysBorel.exists_isOptionalHullCoupling_standardBorel.{0} hκ
      (ρL := flowLineRhoL κ c.fn c.jumps 0 0) (ρR := flowLineRhoR κ c.fn c.jumps 0 0)
      (Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0)
  have hfld : IsFlowLineDriver κ c.fn c.jumps 0 P₀ X W ζ :=
    ⟨X, 𝓕, VL, VR, B, fun ω => isTranslateAddConst_zero_self (X ω) (chiC κ), hC⟩
  have hX : IsGFFWithBoundaryData P₀ X c.fn c.jumps :=
    isGFFWithBoundaryData_of_flowLineGFF hκ c.isPiecewiseConstantBoundaryData ⟨hC.2.1, hC.2.2.1⟩
  have hgood : ∀ᵐ ω ∂P₀, IsGoodDrvCode (F (c, X ω)) := by
    filter_upwards [hF.2.2 c P₀ X W ζ hfld, ae_driver_zero_continuousOn hfld] with ω hm hW
    exact isGoodDrvCode_of_driverCodeMatch hm hW.2
  obtain ⟨u, hu, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension c.isPiecewiseConstantBoundaryData
  have hmap : P₀.map X = c.gffLaw := by
    have h1 := Exist.map_eq_of_isGFFWithBoundaryData hX (c.isGFFWithBoundaryData_gffLaw hc) hu
    rwa [Measure.map_id] at h1
  have hFc : Measurable fun g : DistOn upperHalfPlaneOpens => F (c, g) :=
    hF.1.comp (measurable_const.prodMk measurable_id)
  have hmeas : MeasurableSet {g : DistOn upperHalfPlaneOpens | IsGoodDrvCode (F (c, g))} :=
    hFc measurableSet_isGoodDrvCode
  rw [← hmap, ae_map_iff hX.1.aemeasurable hmeas]
  exact hgood

/-- **A canonical driver code is good under any GFF with the data of a sorted word.** -/
theorem ae_isGoodDrvCode_of_isGFF {κ : ℝ} (hκ : 0 < κ)
    {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞} (hF : IsCanonicalDriverCode κ 0 F)
    {c : BoundaryWord} (hc : c.IsSorted) {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {X : Ω → DistOn upperHalfPlaneOpens} (hX : IsGFFWithBoundaryData Q X c.fn c.jumps) :
    ∀ᵐ ω ∂Q, IsGoodDrvCode (F (c, X ω)) := by
  obtain ⟨u, hu, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension c.isPiecewiseConstantBoundaryData
  have hmap : Q.map X = c.gffLaw := by
    have h1 := Exist.map_eq_of_isGFFWithBoundaryData hX (c.isGFFWithBoundaryData_gffLaw hc) hu
    rwa [Measure.map_id] at h1
  have hFc : Measurable fun g : DistOn upperHalfPlaneOpens => F (c, g) :=
    hF.1.comp (measurable_const.prodMk measurable_id)
  have hmeas : MeasurableSet {g : DistOn upperHalfPlaneOpens | IsGoodDrvCode (F (c, g))} :=
    hFc measurableSet_isGoodDrvCode
  have h := ae_isGoodDrvCode_gffLaw hκ hF hc
  rw [← hmap, ae_map_iff hX.1.aemeasurable hmeas] at h
  exact h

/-! ### The good-code clause of GB6's (Det) -/

/-- **The good-code clause of `GB6RelDetStatement`.** Almost surely on `{s < ζα, α(s) ∈ ℍ}`, the canonical driver code
`F (β, Hc)` of the conditional field, `β = gb6Word κ θ c s Wα`, is good. By GB6's (R1) (`gb6_condDet_r1`), on the
record event the chart field has, given the record of the flow prefix, the Gaussian characteristic functional of the
conditional word; so under a disintegrating kernel it is the GFF of that word, under which the code is good
(`ae_isGoodDrvCode_of_isGFF`); the record event is almost surely `{s < ζα, α(s) ∈ ℍ}` (`mem_gb6TS_iff`). -/
theorem ae_isGoodDrvCode_gb6 {κ θ : ℝ} (hκ : 0 < κ) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (hG : IsGFFWithBoundaryData P h b J)
    {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {α : Ω → ℝ≥0 → ℂ}
    (hfl : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) (s : ℝ≥0)
    {Hc : Ω → DistOn upperHalfPlaneOpens} (hHcm : Measurable Hc)
    (hHc : ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      IsChartTransport (ownComponentChart (fun r : ℝ => Wα r.toNNReal ω) s) (-1)
        (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (Hc ω))
    {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞} (hF : IsCanonicalDriverCode (16 / κ) 0 F)
    {c : BoundaryWord} (hcb : ∀ y ∉ J, c.fn y = b y) :
    ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      IsGoodDrvCode (F (gb6Word κ θ c s (fun t => Wα t ω), Hc ω)) := by
  have hflc : IsFlowLineDriver κ c.fn c.jumps θ P h Wα ζα :=
    (isFlowLineDriver_congr_of_eqOn hb c.isPiecewiseConstantBoundaryData J hcb).2 hfl
  have hrecm : Measurable (gb6Rec s Wα ζα) := (measurable_recOf_cfE hfl s).2
  have hM𝒢 : MeasurableSet[MeasurableSpace.comap (gb6Rec s Wα ζα) inferInstance] (gb6Rec s Wα ζα ⁻¹' gb6TS s) :=
    ⟨gb6TS s, measurableSet_gb6TS s, rfl⟩
  have hMm : MeasurableSet (gb6Rec s Wα ζα ⁻¹' gb6TS s) := hrecm (measurableSet_gb6TS s)
  obtain ⟨K, hK, hlaw⟩ := exists_isMarkovKernel_map_eq_compProd P (gb6Rec s Wα ζα ⁻¹' gb6TS s) hrecm hHcm
  have hGK := ae_isGFFWithBoundaryData_of_condExp_word hrecm.comap_le hM𝒢 (comap_measurable _)
    (measurable_gb6WordOfRec κ θ c) (ae_of_all _ fun ω _ => isSorted_gb6WordOfRec κ θ c _) hHcm measurable_id
    hlaw (fun φ => gb6_condDet_r1 hκ hG hflc hα s hHcm hHc φ)
  have hE : MeasurableSet
      {p : RecData × DistOn upperHalfPlaneOpens | IsGoodDrvCode (F (gb6WordOfRec κ θ c p.1, p.2))} :=
    (hF.1.comp (((measurable_gb6WordOfRec κ θ c).comp measurable_fst).prodMk measurable_snd))
      measurableSet_isGoodDrvCode
  have hκ' : 0 < 16 / κ := div_pos (by norm_num) hκ
  have hgood := Sec5.MarkovOther.ae_mem_of_compProd_eq_prod hMm hrecm hHcm hlaw hE (by
    filter_upwards [hGK] with r hr
    exact ae_isGoodDrvCode_of_isGFF hκ' hF hr.1 hr.2)
  filter_upwards [hgood, ae_gb6RecGood hfl hα s] with ω hω hg hs hsH
  have hωM : gb6Rec s Wα ζα ω ∈ gb6TS s := (mem_gb6TS_iff hg).1 ⟨hs, hsH⟩
  have hβ : gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω) = gb6Word κ θ c s (fun t => Wα t ω) := by
    rw [gb6Word, (hg hs).2.1]
  have h1 : IsGoodDrvCode (F (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω), Hc ω)) := hω hωM
  rwa [hβ] at h1

end GB6

end Supp8

end InteractingSLE
