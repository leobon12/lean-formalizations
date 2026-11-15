/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4RelSpace
import InteractingSLE.Spec.Supplement.BRLeafGB6

/-!
# Theorem GW4's component (Det): the field-determined driver through a stop

Packet PROVE-GW4-RELLAW. Under an arbitrary probability measure `ν` on a space in `Type u` (in the application: the
regular conditional law given the two boundary walks), let `X` be a GFF with the data of a sorted word `c₀`, and let
`(R, V)` be a measurable continuous driver from `0` with a measurable stop such that, on GB6's canonical space
`RelSpace × Ω₀` under `(ν.map (X, R, V)) ⊗ P₀`, the driver is a coupling through the stop `V` of the field with the
flow-line word of `c₀` (`StoppedExtend.IsStoppedHullCoupling`). Then `ν`-almost surely the field-determined driver of
Theorem 1.2 (`BRLeaf.cfDrv`, read off `X`) lives at least until `V` and equals `R` before `V`:

* **`ae_isStopDrvMatch_of_relCoupling`**: Aux. lemma 54 and the determination clause of a canonical driver code give
  the stopped driver match on the canonical space (`RelDrv.ae_isStopDrvMatch_of_isStoppedHullCoupling`); it is a
  property of the first factor and of the law of `(X, R, V)`, so it holds `ν`-almost surely;
* **`ae_cfDrv_eq_of_match`**: the code is good under the GFF law (`GB6.ae_isGoodDrvCode_gffLaw`), so its decoded
  driver is `R` before `V`; Theorem 1.2 at universe `u` identifies the decoded code with `cfDrv`
  (`BRLeaf.ae_drvOf_eq_drvDec`).
* `cfField_eq_invField`, `isGFFWithBoundaryData_invField_word`: the inverted component field of `GW4Traverse` is
  `invField`, and it is a GFF with the data of every word of the counterflow data.

**R48.** Theorems 1.2–1.3 are used (through `cfDrv` and the canonical driver code); GW4 serves Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW4Rel

open Supp8.GB6.RelDrv Restart Restart.StoppedExtend Sec2.Assembly Sec7.StripSysField

/-! ### The inverted component field -/

/-- `GW4Traverse.cfField κ f` (the frozen infinity-source transport of the centred counterflow) is `invField κ f`. -/
theorem cfField_eq_invField {κ : ℝ} (hκ : 0 < κ) (f : DistOn upperHalfPlaneOpens) :
    GW4Traverse.cfField κ f = invField κ f := by
  have e1 : cfOffset κ - 2 * Real.pi * cfCoeff κ = Real.pi * chiC κ := by
    simp only [cfOffset, cfCoeff, Supp8.GB6.chiC_sixteen_div hκ]
    ring
  have e2 : -cfCoeff κ = chiC κ := by
    simp only [cfCoeff, Supp8.GB6.chiC_sixteen_div hκ, neg_neg]
  simp only [GW4Traverse.cfField, invField, e1, e2]

/-- **The inverted component field is a GFF with the data of every word of the counterflow data.** -/
theorem isGFFWithBoundaryData_invField_word {κ : ℝ} (hκ : 0 < κ) {bC : ℝ → ℝ} {jumpsC : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData bC jumpsC) {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {hC : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData ν hC bC jumpsC) {c₀ : BoundaryWord}
    (hc₀J : c₀.jumps = counterflowJumps jumpsC) (hc₀ : ∀ y ∉ c₀.jumps, c₀.fn y = counterflowData κ bC y) :
    IsGFFWithBoundaryData ν (fun ω => invField κ (hC ω)) c₀.fn c₀.jumps := by
  have hcf := GW4Traverse.isGFFWithBoundaryData_cfField κ hb hh
  have e : (fun ω => GW4Traverse.cfField κ (hC ω)) = fun ω => invField κ (hC ω) :=
    funext fun ω => cfField_eq_invField hκ (hC ω)
  rw [e] at hcf
  rw [hc₀J] at hc₀ ⊢
  exact (Restart.isGFFWithBoundaryData_congr ν _ (S := ((counterflowJumps jumpsC : Finset ℝ) : Set ℝ))
    fun y hy => hc₀ y hy).2 hcf

/-! ### The field-determined driver through a stop -/

/-- **The stopped driver match of a relative coupling through a stop.** Under a probability measure `ν` on a space in
`Type u`, let `X` be a measurable field, `R` a measurable continuous driver from `0` and `V` a measurable stop, such
that on `RelSpace × Ω₀` under `(ν.map (X, R, V)) ⊗ P₀` the driver is a coupling through the stop of the field with the
flow-line word of `c₀` at `k` (angle `0`). Then `ν`-almost surely `V` is at most the lifetime of the canonical driver
code of `(c₀, X)` and `R` is that code at the dyadic times before `V` (Aux. lemma 54 and the code's determination
clause on the canonical space, `RelDrv.ae_isStopDrvMatch_of_isStoppedHullCoupling`, then the first factor). -/
theorem ae_isStopDrvMatch_of_relCoupling {k : ℝ} (hext : StoppedHullExtendStatement.{0} k)
    {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞} (hF : IsCanonicalDriverCode k 0 F)
    (c₀ : BoundaryWord) {Ω : Type u} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {X : Ω → DistOn upperHalfPlaneOpens} (hXm : Measurable X) {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hRm : ∀ t, Measurable (R t)) (hRc : ∀ ω, Continuous fun t => R t ω) (hR0 : ∀ ω, R 0 ω = 0)
    (hVm : Measurable V) {Ω₀ : Type} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]
    {𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (RelSpace × Ω₀))}
    {VL : Fin (flowLineNL c₀.fn c₀.jumps 0) → ℝ≥0 → RelSpace × Ω₀ → ℝ}
    {VR : Fin (flowLineNR c₀.fn c₀.jumps 0) → ℝ≥0 → RelSpace × Ω₀ → ℝ} {B : ℝ≥0 → RelSpace × Ω₀ → ℝ}
    (hSC : IsStoppedHullCoupling k (flowLineXL c₀.fn c₀.jumps 0) (flowLineXR c₀.fn c₀.jumps 0)
      (flowLineRhoL k c₀.fn c₀.jumps 0 0) (flowLineRhoR k c₀.fn c₀.jumps 0 0)
      ((ν.map (relVar X R V)).prod P₀) 𝓕 (fun t p => relDrv t p.1) VL VR B (fun p => relStp p.1)
      (fun p => relFld p.1)) :
    ∀ᵐ ω ∂ν, IsStopDrvMatch (F (c₀, X ω)) (fun t => R t ω) (V ω) := by
  have hYm : Measurable (relVar X R V) := measurable_relVar hXm hRm hVm
  have : IsProbabilityMeasure (ν.map (relVar X R V)) :=
    (Measure.isProbabilityMeasure_map_iff hYm.aemeasurable).2 inferInstance
  -- the stopped driver match on the canonical space, then on its first factor
  have hd := ae_isStopDrvMatch_of_isStoppedHullCoupling hext hF c₀ (Ω := RelSpace × Ω₀)
    (Q := (ν.map (relVar X R V)).prod P₀) (Hc := fun p => relFld p.1) (X := fun p => relFld p.1)
    (fun p => isTranslateAddConst_zero_self _ _) hSC (Wb := fun t p => relDrv t p.1)
    (fun t => (measurable_relDrv t).comp measurable_fst) (measurable_relFld.comp measurable_fst)
    (measurable_relStp.comp measurable_fst) (ae_of_all _ fun _ _ _ => rfl)
  have hd' := ConverseBefore.ae_of_ae_fst (P₀ := P₀)
    (q := fun q => IsStopDrvMatch (F (c₀, relFld q)) (fun t => relDrv t q) (relStp q)) hd
  have hE : MeasurableSet {q : RelSpace | IsStopDrvMatch (F (c₀, relFld q)) (fun t => relDrv t q) (relStp q)} :=
    measurableSet_isStopDrvMatch (hF.1.comp (measurable_const.prodMk measurable_relFld)) measurable_relDrv
      measurable_relStp
  filter_upwards [(ae_map_iff hYm.aemeasurable hE).1 hd'] with ω hm
  have he : (fun t => relDrv t (relVar X R V ω)) = fun t => R t ω :=
    funext fun t => relDrv_relVar (hRc ω) (hR0 ω) t
  have h1 : IsStopDrvMatch (F (c₀, relFld (relVar X R V ω))) (fun t => relDrv t (relVar X R V ω))
      (relStp (relVar X R V ω)) := hm
  rw [he] at h1
  exact h1

/-- **The field-determined driver is the stopped relative driver.** Under a probability measure `ν` on a space in
`Type u`, let `X` be a GFF with the data of a sorted word `c₀` and `R` a continuous driver which, `ν`-almost surely,
is the canonical driver code of `(c₀, X)` before a stop `V` (`IsStopDrvMatch`). Then `ν`-almost surely `V` is at
most the lifetime of the field-determined driver `cfDrv` of Theorem 1.2 read off `X`, and the two drivers agree before
`V` (the code is good under the GFF law, `GB6.ae_isGoodDrvCode_gffLaw`; Theorem 1.2 at universe `u` identifies its
decoded driver with `cfDrv`, `BRLeaf.ae_drvOf_eq_drvDec`). -/
theorem ae_cfDrv_eq_of_match (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) {k : ℝ} (hk : 0 < k)
    {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞} (hF : IsCanonicalDriverCode k 0 F)
    {c₀ : BoundaryWord} (hc₀ : c₀.IsSorted) {Ω : Type u} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] {X : Ω → DistOn upperHalfPlaneOpens} (hX : IsGFFWithBoundaryData ν X c₀.fn c₀.jumps)
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} (hRc : ∀ ω, Continuous fun t => R t ω)
    (hmatch : ∀ᵐ ω ∂ν, IsStopDrvMatch (F (c₀, X ω)) (fun t => R t ω) (V ω)) :
    ∀ᵐ ω ∂ν, V ω ≤ (BRLeaf.cfDrv h12p hk c₀ (X ω)).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < V ω → (BRLeaf.cfDrv h12p hk c₀ (X ω)).1 t = R t ω := by
  -- the law of `X` is the GFF law of the word
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension
    c₀.isPiecewiseConstantBoundaryData
  have hmap : ν.map X = c₀.gffLaw := by
    have h1 := Exist.map_eq_of_isGFFWithBoundaryData hX (c₀.isGFFWithBoundaryData_gffLaw hc₀) hu₀
    rwa [Measure.map_id] at h1
  have hgood0 := Supp8.GB6.ae_isGoodDrvCode_gffLaw hk hF hc₀
  have hcmp0 := BRLeaf.ae_drvOf_eq_drvDec h12p h13 hk hF hc₀
  rw [← hmap] at hgood0 hcmp0
  have hgood := ae_of_ae_map hX.1.aemeasurable hgood0
  have hcmp := ae_of_ae_map hX.1.aemeasurable hcmp0
  filter_upwards [hmatch, hgood, hcmp] with ω hm' hg hc
  have hdec := eqOn_drvDec_of_isStopDrvMatch hg (hRc ω).continuousOn hm'
  obtain ⟨hlife, hpath⟩ := hc
  refine ⟨?_, fun t ht => ?_⟩
  · show V ω ≤ (BRLeaf.cfDrv h12p hk c₀ (X ω)).2
    have h2 : (BRLeaf.cfDrv h12p hk c₀ (X ω)).2 = (F (c₀, X ω)).2 := hlife
    rw [h2]
    exact hm'.1
  · have htF : (t : ℝ≥0∞) < (F (c₀, X ω)).2 := lt_of_lt_of_le ht hm'.1
    show (BRLeaf.cfDrv h12p hk c₀ (X ω)).1 t = R t ω
    rw [← hdec t ht]
    exact hpath t htF

end GW4Rel

end Theorem14

end InteractingSLE
