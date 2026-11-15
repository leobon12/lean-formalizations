/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.HullDetGen
import InteractingSLE.Spec.Supplement.GW2ScheduleCanon

/-!
# GW2: determination of a flow driver at an arbitrary angle and universe

The canonical driver code quantifies over probability spaces in `Type`. GW2 also
uses spaces in `Type u`. We compare the canonical code with the parametrized
determination map on a lifted canonical GFF, then transfer this comparison by the
law of the field. This extends the angle-zero adapter in `HullDetGen`.

These results serve Theorem 1.4; Theorems 1.2 and 1.3 are explicit inputs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2JDet

open Restart Exist Exist.Staged Exist.StagedLaw Sec2.Assembly
open Supp8.GB6 GW2Schedule

/-- The word-driver wrapper is the existing parametrized determination map. -/
theorem wordDrv_eq_drvOf (h12p : Theorem12ParamStatement.{u}) {κ : ℝ}
    (hκ : 0 < κ) (θ : ℝ) (c : BoundaryWord) (g : DistOn upperHalfPlaneOpens) :
    wordDrv hκ h12p θ c g =
      drvOf (detCode (paramΦ h12p hκ (flowLineNL c.fn c.jumps 0)
        (flowLineNR c.fn c.jumps 0))
        (((flowLineXL c.fn c.jumps 0, flowLineXR c.fn c.jumps 0),
          (flowLineRhoL κ c.fn c.jumps 0 θ, flowLineRhoR κ c.fn c.jumps 0 θ)),
          flowField 0 (θ * QuantumZipper.chiC κ) g)) := by
  simp only [wordDrv, stagedDrv, wNL, wNR, wPad, truncWord_padFL]

/-- The existing field-determined word driver realizes the angle-`θ` flow line
on every probability space carrying the word's GFF. -/
theorem isFlowLineDriver_wordDrv (h12p : Theorem12ParamStatement.{u})
    (h13 : Theorem13Statement.{u}) {κ θ : ℝ} (hκ : 0 < κ)
    {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {g : Ω → DistOn upperHalfPlaneOpens} {c : BoundaryWord}
    (hg : IsGFFWithBoundaryData Q g c.fn c.jumps) :
    IsFlowLineDriver κ c.fn c.jumps θ Q g
      (fun t ω => (wordDrv hκ h12p θ c (g ω)).1 t)
      (fun ω => (wordDrv hκ h12p θ c (g ω)).2) := by
  let E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞ :=
    (fun q : BoundaryWord × DistOn upperHalfPlaneOpens => wordDrv hκ h12p θ q.1 q.2) ∘
      fun ω => (c, g ω)
  have hpair : Measurable fun ω : Ω => (c, g ω) := measurable_const.prodMk hg.1
  have hEm := (measurable_wordDrv hκ h12p θ).comp hpair
  obtain ⟨𝓕, VL, VR, B, hC⟩ := isOptionalHullCoupling_drv h12p h13 hκ
    (Q := Q) (h₀ := fun ω => flowField 0 (θ * QuantumZipper.chiC κ) (g ω))
    (xL := flowLineXL c.fn c.jumps 0) (xR := flowLineXR c.fn c.jumps 0)
    (ρL := flowLineRhoL κ c.fn c.jumps 0 θ)
    (ρR := flowLineRhoR κ c.fn c.jumps 0 θ) (E := E)
    (Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0)
    (isGFFWithBoundaryData_flowField hκ c.isPiecewiseConstantBoundaryData 0 θ hg)
    hEm (Eventually.of_forall fun ω => wordDrv_eq_drvOf h12p hκ θ c (g ω))
  exact ⟨(fun ω => flowField 0 (θ * QuantumZipper.chiC κ) (g ω)),
    𝓕, VL, VR, B, fun ω => isTranslateAddConst_flowField 0 _ (g ω), hC⟩

/-- Canonical codes at every angle are good under the GFF law of a sorted word.
No admissibility of the seed is needed. -/
theorem ae_isGoodDrvCode_gffLaw_theta (h12p : Theorem12ParamStatement.{0})
    (h13 : Theorem13Statement.{0}) {κ θ : ℝ} (hκ : 0 < κ)
    {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hF : IsCanonicalDriverCode κ θ F) {c : BoundaryWord} (hc : c.IsSorted) :
    ∀ᵐ g ∂c.gffLaw, IsGoodDrvCode (F (c, g)) := by
  have hfl := isFlowLineDriver_wordDrv h12p h13 (θ := θ) hκ
    (c.isGFFWithBoundaryData_gffLaw hc)
  filter_upwards [hF.2.2 c c.gffLaw id _ _ hfl] with g hg
  exact isGoodDrvCode_of_driverCodeMatch hg (isRegularDriver_wordDrv hκ h12p θ c g).1

/-- The parametrized determined driver in universe `u` agrees with the canonical
driver code at angle `θ`, under the GFF law of the word. -/
theorem ae_wordDrv_eq_drvDec (h12p : Theorem12ParamStatement.{u})
    (h13 : Theorem13Statement.{u}) (h12p₀ : Theorem12ParamStatement.{0})
    (h13₀ : Theorem13Statement.{0}) {κ θ : ℝ} (hκ : 0 < κ)
    {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hF : IsCanonicalDriverCode κ θ F) {c : BoundaryWord} (hc : c.IsSorted) :
    ∀ᵐ g ∂c.gffLaw,
      (wordDrv hκ h12p θ c g).2 = (F (c, g)).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < (F (c, g)).2 →
        (wordDrv hκ h12p θ c g).1 t = drvDec (F (c, g)) t := by
  have hgood := ae_isGoodDrvCode_gffLaw_theta h12p₀ h13₀ hκ hF hc
  obtain ⟨h', 𝓕, VL, VR, B, htr, hC⟩ :=
    GW2JointKernel.isFlowLineDriver_gffLaw hF hc hgood
  let ι : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens × ULift.{u} PUnit :=
    fun g => (g, ULift.up PUnit.unit)
  have hι : Measurable ι := measurable_id.prodMk measurable_const
  let μ := c.gffLaw.map ι
  have : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff hι.aemeasurable).2 inferInstance
  have hμ : μ.map Prod.fst = c.gffLaw := by
    rw [Measure.map_map measurable_fst hι]
    exact Measure.map_id
  have hC' := BRLeaf.isOptionalHullCoupling_fstU (C := ULift.{u} PUnit) hμ hC
  have hF' := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have hΦ := (h12p κ hκ (flowLineNL c.fn c.jumps 0)
    (flowLineNR c.fn c.jumps 0)).choose_spec.2 _ _ _ _ hF' hC'
  have hdet := ae_detCode_eq hκ hF' h13 hC' hΦ
  have hback := ae_of_ae_map hι.aemeasurable hdet
  filter_upwards [hback] with g ⟨x₀, hx₀, hζ, hpath, hdc⟩
  have he : h' g = flowField 0 (θ * QuantumZipper.chiC κ) g := by
    ext φ
    exact (htr g φ φ (fun z => by rw [Complex.ofReal_zero, add_zero])).trans
      (isTranslateAddConst_flowField 0 _ g φ φ
        (fun z => by rw [Complex.ofReal_zero, add_zero])).symm
  have hdc' : detCode (paramΦ h12p hκ (flowLineNL c.fn c.jumps 0)
      (flowLineNR c.fn c.jumps 0))
      (((flowLineXL c.fn c.jumps 0, flowLineXR c.fn c.jumps 0),
        (flowLineRhoL κ c.fn c.jumps 0 θ, flowLineRhoR κ c.fn c.jumps 0 θ)),
        flowField 0 (θ * QuantumZipper.chiC κ) g) = dOf x₀ := by
    rw [← he]
    exact hdc
  rw [wordDrv_eq_drvOf h12p hκ θ c g]
  rw [hdc', drvOf_of_mem (dOf_mem_DSet hx₀)]
  refine ⟨hζ, fun t ht => ?_⟩
  show drvPath (dOf x₀) t = _
  rw [(drvPath_dOf_agree x₀).2 t (hζ ▸ ht)]
  exact (hpath t ht).1

/-- Goodness transfers to every realization of the same GFF, in any universe. -/
theorem ae_isGoodDrvCode_of_isGFF_theta (h12p : Theorem12ParamStatement.{0})
    (h13 : Theorem13Statement.{0}) {κ θ : ℝ} (hκ : 0 < κ)
    {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hF : IsCanonicalDriverCode κ θ F) {c : BoundaryWord} (hc : c.IsSorted)
    {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {X : Ω → DistOn upperHalfPlaneOpens}
    (hX : IsGFFWithBoundaryData Q X c.fn c.jumps) :
    ∀ᵐ ω ∂Q, IsGoodDrvCode (F (c, X ω)) := by
  have hg := ae_isGoodDrvCode_gffLaw_theta h12p h13 hκ hF hc
  rw [← Supp8.HullDetGen.map_eq_gffLaw hc hX] at hg
  exact ae_of_ae_map hX.1.aemeasurable hg

/-- A flow driver on a space in `Type u` is the decoded canonical driver, at
any angle. This supplies the universe transfer needed by GW2. -/
theorem ae_flowLineDriver_eq_drvDec_theta (h12p : Theorem12ParamStatement.{u})
    (h13 : Theorem13Statement.{u}) (h12p₀ : Theorem12ParamStatement.{0})
    (h13₀ : Theorem13Statement.{0}) {κ θ : ℝ} (hκ : 0 < κ)
    {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hF : IsCanonicalDriverCode κ θ F) {c : BoundaryWord} (hc : c.IsSorted)
    {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {X : Ω → DistOn upperHalfPlaneOpens}
    (hX : IsGFFWithBoundaryData Q X c.fn c.jumps)
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hW : IsFlowLineDriver κ c.fn c.jumps θ Q X W ζ) :
    ∀ᵐ ω ∂Q, ζ ω = (F (c, X ω)).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → W t ω = drvDec (F (c, X ω)) t := by
  obtain ⟨h', 𝓕, VL, VR, B, htr, hC⟩ := hW
  have hF' := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have hΦ := (h12p κ hκ (flowLineNL c.fn c.jumps 0)
    (flowLineNR c.fn c.jumps 0)).choose_spec.2 _ _ _ _ hF' hC
  have hdet := ae_detCode_eq hκ hF' h13 hC hΦ
  have hcmp := ae_wordDrv_eq_drvDec h12p h13 h12p₀ h13₀ hκ hF hc
  rw [← Supp8.HullDetGen.map_eq_gffLaw hc hX] at hcmp
  have hcmp' := ae_of_ae_map hX.1.aemeasurable hcmp
  filter_upwards [hdet, hcmp'] with ω ⟨x₀, hx₀, hζx, hpath, hdc⟩ hcmpω
  have he : h' ω = flowField 0 (θ * QuantumZipper.chiC κ) (X ω) := by
    ext φ
    exact (htr ω φ φ (fun z => by rw [Complex.ofReal_zero, add_zero])).trans
      (isTranslateAddConst_flowField 0 _ (X ω) φ φ
        (fun z => by rw [Complex.ofReal_zero, add_zero])).symm
  have hword : wordDrv hκ h12p θ c (X ω) =
      (drvPath (dOf x₀), (dOf x₀).1) := by
    have hdc' : detCode (paramΦ h12p hκ (flowLineNL c.fn c.jumps 0)
        (flowLineNR c.fn c.jumps 0))
        (((flowLineXL c.fn c.jumps 0, flowLineXR c.fn c.jumps 0),
          (flowLineRhoL κ c.fn c.jumps 0 θ, flowLineRhoR κ c.fn c.jumps 0 θ)),
          h' ω) = dOf x₀ := hdc
    rw [wordDrv_eq_drvOf, ← he, hdc', drvOf_of_mem (dOf_mem_DSet hx₀)]
  rw [hword] at hcmpω
  have hζ : ζ ω = (F (c, X ω)).2 := hζx.symm.trans hcmpω.1
  refine ⟨hζ, fun t ht => ?_⟩
  calc
    W t ω = cw x₀ t := ((hpath t ht).1).symm
    _ = drvPath (dOf x₀) t := ((drvPath_dOf_agree x₀).2 t (hζx ▸ ht)).symm
    _ = drvDec (F (c, X ω)) t := hcmpω.2 t (hζ ▸ ht)

end InteractingSLE.Theorem14.GW2JDet
