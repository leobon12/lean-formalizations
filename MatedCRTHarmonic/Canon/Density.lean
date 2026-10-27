import MatedCRTHarmonic.Canon.Local
import MatedCRTHarmonic.CellScaling.MeshMeasurableWalk
import MatedCRTHarmonic.GMS3.Cells
import MatedCRTHarmonic.GMS4F.Prop210DensityComparison

/-!
# The nonlocalized density `u^ε` of [18] (2.12)

The countable Brownian dart code supplies a Borel degree on every path. On the
locally finite event it equals the degree of the actual mated-CRT multigraph.
This gives the source density without a graph-witness choice on null samples.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.Canon

open MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
  {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- `diam(H_x)^2 deg(x)/area(H_x)` with the countable Brownian degree. -/
def rawCellCoef (ε : ℝ) (c : C(ℝ, ℂ)) (w : Path2) (x : ℤ) : ℝ≥0∞ :=
  GMS4b.segRatio c (ε * ((x : ℝ) - 1)) (ε * x) *
    CellScaling.meshGridRawDegree ε w x

/-- The selection-free `u^ε(z)`: sum over every cell containing `z`. -/
def uDensity (ε : ℝ) (c : C(ℝ, ℂ)) (w : Path2) (z : ℂ) : ℝ≥0∞ :=
  ∑' x : ℤ, (cell ε c x).indicator (fun _ => rawCellCoef ε c w x) z

def coneUDensity
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε : ℝ) (ω : Ω) (z : ℂ) : ℝ≥0∞ :=
  uDensity ε (coneSample D hγ ω).curve (coneSample D hγ ω).boundary z

/-- On the locally finite event, the Brownian degree is the multigraph degree. -/
theorem rawCellCoef_eq_graph
    (ε : ℝ) (c : C(ℝ, ℂ)) (w : Path2)
    (hlf : IsLocallyFinite ε w) (x : ℤ) :
    rawCellCoef ε c w x =
      GMS4b.segRatio c (ε * ((x : ℝ) - 1)) (ε * x) *
        (((structureGraph ε w hlf).deg x : ℕ) : ℝ≥0∞) := by
  rw [rawCellCoef, CellScaling.meshGridRawDegree_eq_graph_deg]
  rfl

/-- The raw coefficient is the GMS3 coefficient of the actual cellular
embedding whenever its cells are the SLE interval images. -/
theorem rawCellCoef_eq_uCoef
    (ε : ℝ) (c : C(ℝ, ℂ)) (w : Path2)
    (hlf : IsLocallyFinite ε w)
    (H : CellularEmbedding (structureGraph ε w hlf) 0)
    (x : ℤ) (hcell : H.cell x = cell ε c x) :
    rawCellCoef ε c w x = GMS3.uCoef H x := by
  rw [rawCellCoef_eq_graph ε c w hlf x,
    GMS4F.uCoef_eq_cellRatio_mul_degree]
  simp only [GMS4b.segRatio, GMS3.cellDiam, hcell, cell, GMS4b.cellOf]

/-- The selection-free density is exactly GMS3's density on a cellular
embedding of the Brownian graph. -/
theorem uDensity_eq_gms3
    (ε : ℝ) (c : C(ℝ, ℂ)) (w : Path2)
    (hlf : IsLocallyFinite ε w)
    (H : CellularEmbedding (structureGraph ε w hlf) 0)
    (hcell : ∀ x : ℤ, H.cell x = cell ε c x) :
    uDensity ε c w = GMS3.uDens H := by
  funext z
  simp only [uDensity, GMS3.uDens]
  congr 1
  funext x
  rw [← hcell x, rawCellCoef_eq_uCoef ε c w hlf H x (hcell x)]

/-- On MTC's all-sample dyadic realization, the density is exactly GMS3's
cellular-embedding density. -/
theorem bundle_uDensity_eq_gms3
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (k : ℕ) (ω : Ω) :
    uDensity (CellFamily.mesh k) (MoTInput.bundleCurve (D := D) ω)
      (MoTInput.bundleBM (D := D) ω) =
        GMS3.uDens ((MoTInput.bundleGeometry (D := D) ω k).2) := by
  let H := (MoTInput.bundleGeometry (D := D) ω k).2
  have hc : ∀ x : ℤ, H.cell x =
      cell (CellFamily.mesh k) (MoTInput.bundleCurve (D := D) ω) x := by
    intro x
    have h := congrArg (fun f : ℤ → Set ℂ => f x) (MoTInput.bundleGeometry_cell D ω k)
    simpa only [H, cell, GMS4b.cellOf] using h
  exact uDensity_eq_gms3 (CellFamily.mesh k) (MoTInput.bundleCurve (D := D) ω)
    (MoTInput.bundleBM (D := D) ω) (MoTInput.bundleGeometry (D := D) ω k).1 H hc

/-- The raw Brownian/curve density of the coupling agrees almost surely with
the density of MTC's dyadic cellular embedding. -/
theorem ae_coneUDensity_eq_gms3
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (k : ℕ) :
    ∀ᵐ ω ∂P, coneUDensity D hγ (CellFamily.mesh k) ω =
      GMS3.uDens ((MoTInput.bundleGeometry (D := D) ω k).2) := by
  filter_upwards [MoTInput.ae_bundleBM_eq D, MoTInput.ae_bundleCurve_eq D]
    with ω hB hC
  change uDensity (CellFamily.mesh k) (η ω) (bm ω) = _
  simpa only [hB, hC] using bundle_uDensity_eq_gms3 D k ω

/-- The selected cell is one of the segments in `DA^ε(z)`; this is the
area-ratio half of [18] (4.3). -/
theorem selectedCell_ratio_le_DA
    {ε : ℝ} (hε : 0 < ε) (c : C(ℝ, ℂ)) (z : ℂ) :
    GMS4b.segRatio c
      (ε * ((selectedIndex ε c z : ℝ) - 1))
      (ε * (selectedIndex ε c z : ℝ)) ≤
        GMS4b.areaRatio ε c z := by
  have ht := firstHit_mem_selectedCellTime hε c z
  have hlo : ε * (selectedIndex ε c z : ℝ) - ε ≤ GMS4b.hitTime c z := by
    calc
      ε * (selectedIndex ε c z : ℝ) - ε =
          ε * ((selectedIndex ε c z : ℝ) - 1) := by ring
      _ ≤ GMS4b.hitTime c z := ht.1.le
  have h := GMS4b.segRatio_le_locDA (ε := ε) (c := c)
    (t₀ := GMS4b.hitTime c z) (s := ε * (selectedIndex ε c z : ℝ)) hlo ht.2
  simpa only [GMS4b.areaRatio, show
    ε * (selectedIndex ε c z : ℝ) - ε =
      ε * ((selectedIndex ε c z : ℝ) - 1) by ring] using h

/-- The selected coefficient is bounded by twice the canonical localized
density when the graph-degree half of (4.3) holds. -/
theorem selectedCell_rawCoef_le_two_uStar
    {ε : ℝ} (hε : 0 < ε) (c : C(ℝ, ℂ)) (w : Path2)
    (hlf : IsLocallyFinite ε w) (z : ℂ)
    (hdegree : ((structureGraph ε w hlf).deg (selectedIndex ε c z) : ℕ∞) ≤
      2 * (GMS4b.degreeIn ε c z + GMS4b.degreeOut ε c z)) :
    rawCellCoef ε c w (selectedIndex ε c z) ≤ 2 * GMS4b.uStar ε c z := by
  have hratio := selectedCell_ratio_le_DA hε c z
  have hdegE : (((structureGraph ε w hlf).deg (selectedIndex ε c z) : ℕ) : ℝ≥0∞) ≤
      2 * (((GMS4b.degreeIn ε c z + GMS4b.degreeOut ε c z : ℕ∞)) : ℝ≥0∞) := by
    exact_mod_cast hdegree
  rw [rawCellCoef_eq_graph ε c w hlf (selectedIndex ε c z)]
  calc
    _ ≤ GMS4b.areaRatio ε c z *
        (2 * (((GMS4b.degreeIn ε c z + GMS4b.degreeOut ε c z : ℕ∞)) : ℝ≥0∞)) :=
      mul_le_mul' hratio hdegE
    _ = 2 * GMS4b.uStar ε c z := by simp only [GMS4b.uStar, GMS4b.locUStar,
      GMS4b.areaRatio, GMS4b.degreeIn, GMS4b.degreeOut]; ac_rfl

/-- The coefficient bound holds at every dyadic mesh and every spatial point
on the same full-measure event as G4FS's (4.7). -/
theorem ae_cone_selectedCell_rawCoef_le_two_uStar
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (k : ℕ) (z : ℂ),
      rawCellCoef (CellFamily.mesh k) (η ω) (bm ω)
        (selectedIndex (CellFamily.mesh k) (η ω) z) ≤
          2 * GMS4b.uStar (CellFamily.mesh k) (η ω) z := by
  filter_upwards [GMS4F.ae_matedCRT_degree_le_two_local_degrees D] with ω hω k z
  obtain ⟨hlf, hdeg⟩ := hω k (GMS4b.hitTime (η ω) z)
  have hε : 0 < CellFamily.mesh k := by dsimp [CellFamily.mesh]; positivity
  exact selectedCell_rawCoef_le_two_uStar hε (η ω) (bm ω) hlf z hdeg

/-- Borel measurability of the source density in `(curve, Brownian path, z)`.
The cell membership set is closed in the curve/point pair. -/
theorem measurable_uDensity (ε : ℝ) :
    Measurable fun p : (C(ℝ, ℂ) × Path2) × ℂ => uDensity ε p.1.1 p.1.2 p.2 := by
  unfold uDensity
  apply Measurable.tsum
  intro x
  have hc : Measurable fun p : (C(ℝ, ℂ) × Path2) × ℂ => p.1.1 :=
    measurable_fst.comp measurable_fst
  have hw : Measurable fun p : (C(ℝ, ℂ) × Path2) × ℂ => p.1.2 :=
    measurable_snd.comp measurable_fst
  have hr : Measurable fun p : (C(ℝ, ℂ) × Path2) × ℂ =>
      GMS4b.segRatio p.1.1 (ε * ((x : ℝ) - 1)) (ε * x) :=
    (GMS4b.lowerSemicontinuous_segRatio _ _).measurable.comp hc
  have hd : Measurable fun p : (C(ℝ, ℂ) × Path2) × ℂ =>
      CellScaling.meshGridRawDegree ε p.1.2 x :=
    (CellScaling.measurable_meshGridRawDegree ε x).comp hw
  have hm : MeasurableSet {p : (C(ℝ, ℂ) × Path2) × ℂ |
      p.2 ∈ cell ε p.1.1 x} := by
    have hpair : Measurable fun p : (C(ℝ, ℂ) × Path2) × ℂ =>
        ((p.1.1, p.2) : C(ℝ, ℂ) × ℂ) := hc.prodMk measurable_snd
    change MeasurableSet {p : (C(ℝ, ℂ) × Path2) × ℂ |
      ∃ t ∈ Icc (ε * ((x : ℝ) - 1)) (ε * x), p.1.1 t = p.2}
    exact (GMS4b.isClosed_hitIn isCompact_Icc).measurableSet.preimage hpair
  have hf : Measurable fun p : (C(ℝ, ℂ) × Path2) × ℂ =>
      rawCellCoef ε p.1.1 p.1.2 x := hr.mul hd
  exact hf.indicator hm

/-- Joint measurability of the actual cone density in sample and point. -/
theorem measurable_coneUDensity
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε : ℝ) :
    Measurable fun p : Ω × ℂ => coneUDensity D hγ ε p.1 p.2 := by
  have hpair : Measurable fun p : Ω × ℂ =>
      (((η p.1, bm p.1), p.2) : (C(ℝ, ℂ) × Path2) × ℂ) :=
    ((D.measurable_curves.2.1.comp measurable_fst).prodMk
      (D.measurable_curves.2.2.2.comp measurable_fst)).prodMk measurable_snd
  simpa only [Function.comp_def, coneUDensity, coneSample] using
    (measurable_uDensity ε).comp hpair

end MatedCRTHarmonic.Canon
