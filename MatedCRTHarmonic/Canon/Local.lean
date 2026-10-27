import MatedCRTHarmonic.Canon.Data
import MatedCRTHarmonic.GMS4b.JointMeasurable
import MatedCRTHarmonic.GMS4b.Lemma46
import MatedCRTHarmonic.GMS4F.Prop210Degree47
import MatedCRTHarmonic.MoTInput.CurveAdapters

/-!
# Canonical localized objects of [18] §4.2

All local objects are defined from the actual area-parametrized curve. Degrees
retain their extended natural values; this is essential before finiteness is
proved. The graph is the Brownian multigraph where it is locally finite.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.Canon

open MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
  {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The selected mesh cell contains the first visit time of `z`. -/
def selectedIndex (ε : ℝ) (c : C(ℝ, ℂ)) (z : ℂ) : ℤ :=
  ⌈GMS4b.hitTime c z / ε⌉

/-- A quantum-time cell, exactly [18]'s `H^ε_x`. -/
def cell (ε : ℝ) (c : C(ℝ, ℂ)) (x : ℤ) : Set ℂ :=
  GMS4b.cellOf ε c x

/-- All six point observables are direct views of `GMS4b`'s §4.2 definitions. -/
structure LocalPoint where
  firstHit : ℝ
  selected : ℤ
  DA : ℝ≥0∞
  degreeIn : ℕ∞
  degreeOut : ℕ∞
  uStar : ℝ≥0∞

def localPoint (ε : ℝ) (c : C(ℝ, ℂ)) (z : ℂ) : LocalPoint :=
  { firstHit := GMS4b.hitTime c z
    selected := selectedIndex ε c z
    DA := GMS4b.areaRatio ε c z
    degreeIn := GMS4b.degreeIn ε c z
    degreeOut := GMS4b.degreeOut ε c z
    uStar := GMS4b.uStar ε c z }

def coneLocalPoint
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε : ℝ) (ω : Ω) (z : ℂ) : LocalPoint :=
  localPoint ε (coneSample D hγ ω).curve z

def referenceLocalPoint
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε : ℝ) (ω : Ω) (z : ℂ) : LocalPoint :=
  localPoint ε (referenceSample D hγ ω).areaCurve z

/-- The Brownian structure graph at a mesh where it is locally finite. -/
def structureGraph (ε : ℝ) (w : Path2) (hlf : IsLocallyFinite ε w) :
    LFMultigraph ℤ (MatedCRT.Edge ε w) :=
  MatedCRT.graph ε w hlf

theorem localPoint_uStar (ε : ℝ) (c : C(ℝ, ℂ)) (z : ℂ) :
    (localPoint ε c z).uStar = (localPoint ε c z).DA *
      (((((localPoint ε c z).degreeIn + (localPoint ε c z).degreeOut : ℕ∞)) : ℝ≥0∞)) :=
  rfl

/-- The first-hit time lies in the half-open interval of the selected cell. -/
theorem firstHit_mem_selectedCellTime {ε : ℝ} (hε : 0 < ε)
    (c : C(ℝ, ℂ)) (z : ℂ) :
    GMS4b.hitTime c z ∈ Ioc
      (ε * ((selectedIndex ε c z : ℝ) - 1))
      (ε * (selectedIndex ε c z : ℝ)) := by
  have hlt := Int.ceil_lt_add_one (GMS4b.hitTime c z / ε)
  have hle := Int.le_ceil (GMS4b.hitTime c z / ε)
  have hlt' : ((selectedIndex ε c z : ℝ) - 1) < GMS4b.hitTime c z / ε := by
    dsimp [selectedIndex]
    linarith
  have hle' : GMS4b.hitTime c z / ε ≤ (selectedIndex ε c z : ℝ) := by
    simpa only [selectedIndex] using hle
  constructor
  · calc
      ε * ((selectedIndex ε c z : ℝ) - 1) < ε * (GMS4b.hitTime c z / ε) :=
        mul_lt_mul_of_pos_left hlt' hε
      _ = GMS4b.hitTime c z := mul_div_cancel₀ _ hε.ne'
  · calc
      GMS4b.hitTime c z = ε * (GMS4b.hitTime c z / ε) := (mul_div_cancel₀ _ hε.ne').symm
      _ ≤ ε * (selectedIndex ε c z : ℝ) := mul_le_mul_of_nonneg_left hle' hε.le

theorem coneLocalPoint_eq_gms4b
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε : ℝ) (ω : Ω) (z : ℂ) :
    (coneLocalPoint D hγ ε ω z).DA = GMS4b.areaRatio ε (η ω) z ∧
    (coneLocalPoint D hγ ε ω z).degreeIn = GMS4b.degreeIn ε (η ω) z ∧
    (coneLocalPoint D hγ ε ω z).degreeOut = GMS4b.degreeOut ε (η ω) z ∧
    (coneLocalPoint D hγ ε ω z).uStar = GMS4b.uStar ε (η ω) z :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem referenceLocalPoint_eq_gms4b
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε : ℝ) (ω : Ω) (z : ℂ) :
    (referenceLocalPoint D hγ ε ω z).DA = GMS4b.areaRatio ε (η₀ ω) z ∧
    (referenceLocalPoint D hγ ε ω z).degreeIn = GMS4b.degreeIn ε (η₀ ω) z ∧
    (referenceLocalPoint D hγ ε ω z).degreeOut = GMS4b.degreeOut ε (η₀ ω) z ∧
    (referenceLocalPoint D hγ ε ω z).uStar = GMS4b.uStar ε (η₀ ω) z :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Equation (4.7) on the canonical Brownian graph. Its geometric event is
the one in the checked G4FS theorem; the source uses this only on the local
regularity event, where the window diameter is positive. -/
theorem graph_degree_le_two_local_degrees
    {ε : ℝ} {w : Path2} {c : C(ℝ, ℂ)}
    (hε : 0 < ε) (Peno : RouteM.Peanosphere w c)
    (hside : RouteM.SideStrict ε w) (hlf : IsLocallyFinite ε w)
    (z : ℂ) (hD : 0 < diam (GMS4b.locWindow ε c (GMS4b.hitTime c z))) :
    ((structureGraph ε w hlf).deg (selectedIndex ε c z) : ℕ∞) ≤
      2 * ((localPoint ε c z).degreeIn + (localPoint ε c z).degreeOut) := by
  exact GMS4F.matedCRT_degree_le_two_local_degrees hε Peno hside hlf c.continuous
    (GMS4b.hitTime c z) hD

/-- The canonical (4.7) holds at every dyadic mesh and every point on a
single full-measure event. The locally finite graph witness is supplied by
the frozen cellular embedding, and G4FS derives the bound from `merge`. -/
theorem ae_cone_graph_degree_le_two_local_degrees
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ (k : ℕ) (z : ℂ),
      ∃ hlf : IsLocallyFinite (CellFamily.mesh k) (bm ω),
        ((structureGraph (CellFamily.mesh k) (bm ω) hlf).deg
          (selectedIndex (CellFamily.mesh k) (η ω) z) : ℕ∞) ≤
          2 * ((GMS4b.degreeIn (CellFamily.mesh k) (η ω) z) +
            GMS4b.degreeOut (CellFamily.mesh k) (η ω) z) := by
  filter_upwards [GMS4F.ae_matedCRT_degree_le_two_local_degrees D] with ω hω k z
  obtain ⟨hlf, hdeg⟩ := hω k (GMS4b.hitTime (η ω) z)
  exact ⟨hlf, hdeg⟩

-- The imported Borel proof expands the lower-semicontinuity construction.
set_option maxHeartbeats 800000 in
/-- Joint Borel measurability of the localized area ratio. -/
theorem measurable_cone_DA
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε : ℝ) :
    Measurable fun p : Ω × ℂ => (coneLocalPoint D hγ ε p.1 p.2).DA := by
  have h : Measurable fun p : Ω × ℂ => GMS4b.areaRatio ε (η p.1) p.2 :=
    by
      let g : Ω × ℂ → C(ℝ, ℂ) × ℂ := fun p => (η p.1, p.2)
      have hg : Measurable g :=
        (D.measurable_curves.2.1.comp measurable_fst).prodMk measurable_snd
      have hf : Measurable (fun p : C(ℝ, ℂ) × ℂ => GMS4b.areaRatio ε p.1 p.2) :=
        GMS4b.measurable_areaRatio ε
      simpa only [Function.comp_def, g] using (hf.comp hg)
  simpa only [coneLocalPoint, localPoint, coneSample] using h

theorem measurable_cone_uStar
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 ≤ ε) :
    Measurable fun p : Ω × ℂ => (coneLocalPoint D hγ ε p.1 p.2).uStar := by
  change Measurable fun p : Ω × ℂ => GMS4b.uStar ε (η p.1) p.2
  exact GMS4b.measurable_uStar_comp D.measurable_curves.2.1 hε

theorem measurable_reference_uStar
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε : ℝ} (hε : 0 ≤ ε) :
    Measurable fun p : Ω × ℂ => (referenceLocalPoint D hγ ε p.1 p.2).uStar := by
  change Measurable fun p : Ω × ℂ => GMS4b.uStar ε (η₀ p.1) p.2
  exact GMS4b.measurable_uStar_comp D.measurable_curves.2.2.1 hε

end MatedCRTHarmonic.Canon
