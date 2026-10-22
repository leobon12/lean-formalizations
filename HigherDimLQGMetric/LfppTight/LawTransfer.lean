import HigherDimLQGMetric.LfppTight.CenteredWN
import HigherDimLQGMetric.Weak.DetLFPPMetric
import HigherDimLFPP.Paths.Measurable

/-!
# Transfer of continuous-field functionals from product laws

The Borel σ-algebra of `C(Rd d, ℝ)` is pulled back from the coordinate
σ-algebra of `Rd d → ℝ`. This permits measurable functionals of a continuous
field to be transferred through `L1e_law`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_measurableSpace_fieldC_eq_comap {d : ℕ} :
    (ContinuousMap.measurableSpace : MeasurableSpace C(Rd d, ℝ)) =
      MeasurableSpace.comap (fun f : C(Rd d, ℝ) => (f : Rd d → ℝ)) MeasurableSpace.pi := by
  rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval, MeasurableSpace.pi,
    MeasurableSpace.comap_iSup]
  simp_rw [MeasurableSpace.comap_comp]
  rfl

/-- Every measurable event of a continuous field is the restriction of a
product-measurable event on all functions. -/
theorem l6a_exists_pi_event {d : ℕ} {E : Type*} [MeasurableSpace E]
    (F : C(Rd d, ℝ) → E) (hF : Measurable F)
    {S : Set E} (hS : MeasurableSet S) :
    ∃ T : Set (Rd d → ℝ), MeasurableSet T ∧
      ∀ g : Rd d → ℝ, ∀ hg : Continuous g,
        (F ⟨g, hg⟩ ∈ S ↔ g ∈ T) := by
  have hE : MeasurableSet[MeasurableSpace.comap
      (fun f : C(Rd d, ℝ) => (f : Rd d → ℝ)) MeasurableSpace.pi]
      {f : C(Rd d, ℝ) | F f ∈ S} := by
    rw [← l6a_measurableSpace_fieldC_eq_comap]
    exact hF hS
  obtain ⟨T, hT, heq⟩ := hE
  refine ⟨T, hT, fun g hg => ?_⟩
  have h := congrArg (fun A : Set C(Rd d, ℝ) => (⟨g, hg⟩ : C(Rd d, ℝ)) ∈ A) heq
  simpa only [mem_preimage, ContinuousMap.coe_mk, mem_ofPred_eq, eq_iff_iff] using h.symm

/-- Equality of process laws on all product-measurable sets transfers every
measurable functional on continuous sample paths. -/
theorem l6a_continuousFunctional_law {d : ℕ} {E : Type*} [MeasurableSpace E]
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω')
    (X : Rd d → Ω → ℝ) (Y : Rd d → Ω' → ℝ)
    (hXc : ∀ ω, Continuous fun z => X z ω)
    (hYc : ∀ ω', Continuous fun z => Y z ω')
    (hlaw : ∀ T : Set (Rd d → ℝ), MeasurableSet T →
      P {ω | (fun z => X z ω) ∈ T} = P' {ω' | (fun z => Y z ω') ∈ T})
    (F : C(Rd d, ℝ) → E) (hF : Measurable F)
    {S : Set E} (hS : MeasurableSet S) :
    P {ω | F ⟨fun z => X z ω, hXc ω⟩ ∈ S} =
      P' {ω' | F ⟨fun z => Y z ω', hYc ω'⟩ ∈ S} := by
  obtain ⟨T, hT, hTE⟩ := l6a_exists_pi_event F hF hS
  have h1 : {ω | F ⟨fun z => X z ω, hXc ω⟩ ∈ S} =
      {ω | (fun z => X z ω) ∈ T} := by
    ext ω
    exact hTE _ (hXc ω)
  have h2 : {ω' | F ⟨fun z => Y z ω', hYc ω'⟩ ∈ S} =
      {ω' | (fun z => Y z ω') ∈ T} := by
    ext ω'
    exact hTE _ (hYc ω')
  rw [h1, h2]
  exact hlaw T hT

open Classical in
/-- Totalize a possibly discontinuous field sample to a continuous map. -/
def l6a_toFieldCMap {d : ℕ} (f : Rd d → ℝ) : C(Rd d, ℝ) :=
  if hf : Continuous f then ⟨f, hf⟩ else 0

/-- The functional law transfer remains valid when the first process is
continuous only almost surely. -/
theorem l6a_aeContinuousFunctional_law {d : ℕ} {E : Type*} [MeasurableSpace E]
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω')
    (X : Rd d → Ω → ℝ) (Y : Rd d → Ω' → ℝ)
    (hXc : ∀ᵐ ω ∂P, Continuous fun z => X z ω)
    (hYc : ∀ ω', Continuous fun z => Y z ω')
    (hlaw : ∀ T : Set (Rd d → ℝ), MeasurableSet T →
      P {ω | (fun z => X z ω) ∈ T} = P' {ω' | (fun z => Y z ω') ∈ T})
    (F : C(Rd d, ℝ) → E) (hF : Measurable F)
    {S : Set E} (hS : MeasurableSet S) :
    P {ω | F (l6a_toFieldCMap (fun z => X z ω)) ∈ S} =
      P' {ω' | F ⟨fun z => Y z ω', hYc ω'⟩ ∈ S} := by
  classical
  let Xg : Rd d → Ω → ℝ := fun z ω =>
    if hc : Continuous (fun z => X z ω) then X z ω else 0
  have hXgc : ∀ ω, Continuous fun z => Xg z ω := by
    intro ω
    by_cases hc : Continuous (fun z => X z ω)
    · have heq : (fun z => Xg z ω) = fun z => X z ω := by
        funext z
        exact dite_eq_left hc
      rwa [heq]
    · have heq : (fun z => Xg z ω) = fun _ => 0 := by
        funext z
        exact dite_eq_right hc
      rw [heq]
      exact continuous_const
  have hlawg : ∀ T : Set (Rd d → ℝ), MeasurableSet T →
      P {ω | (fun z => Xg z ω) ∈ T} = P' {ω' | (fun z => Y z ω') ∈ T} := by
    intro T hT
    calc
      P {ω | (fun z => Xg z ω) ∈ T} = P {ω | (fun z => X z ω) ∈ T} := by
        apply measure_congr
        filter_upwards [hXc] with ω hω
        congr 1
        funext z
        exact dite_eq_left hω
      _ = _ := hlaw T hT
  have htrans := l6a_continuousFunctional_law P P' Xg Y hXgc hYc hlawg F hF hS
  calc
    P {ω | F (l6a_toFieldCMap (fun z => X z ω)) ∈ S} =
        P {ω | F ⟨fun z => Xg z ω, hXgc ω⟩ ∈ S} := by
      apply measure_congr
      filter_upwards [hXc] with ω hω
      have heq : l6a_toFieldCMap (fun z => X z ω) =
          (⟨fun z => Xg z ω, hXgc ω⟩ : C(Rd d, ℝ)) := by
        apply ContinuousMap.ext
        intro z
        simp only [l6a_toFieldCMap, dite_eq_left hω, ContinuousMap.coe_mk,
          Xg]
      rw [heq]
    _ = _ := htrans

/-- The continuous metric produced by a continuous field, with a fixed scalar
normalization. -/
def l6a_metricOfFieldC {d : ℕ} (ξ a : ℝ)
    (φ : C(Rd d, ℝ)) : C(Rd d × Rd d, ℝ) :=
  toCMapRd (a • fieldLfpp ξ φ)

theorem l6a_measurable_metricOfFieldC {d : ℕ} (ξ a : ℝ) :
    Measurable (l6a_metricOfFieldC (d := d) ξ a) := by
  apply ContinuousMap.measurable_iff_eval.2
  intro p
  have hF : Measurable (fun φ : C(Rd d, ℝ) =>
      a * HigherDimLFPP.lfppDistOn ξ φ Set.univ p.1 p.2) :=
    (HigherDimLFPP.measurable_lfppDistOn_continuousMap
      (V := Set.univ) isOpen_univ ξ p.1 p.2).const_mul a
  convert hF using 1
  funext φ
  rw [l6a_metricOfFieldC, toCMapRd_apply_of_continuous
    ((continuous_fieldLfpp φ.continuous).const_smul a)]
  simp only [Pi.smul_apply, smul_eq_mul, fieldLfpp_eq_lfppDistOn φ.continuous]

/-- `L1e_law` transfers the entire centered LFPP metric law once the
continuous infinite-band version is supplied. -/
theorem l6a_centered_metric_law (hL1e : L1e_law) {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : 0 < ε)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (W : HigherDimLFPP.WN d → Ω' → ℝ) (hW : HigherDimLFPP.IsWhiteNoise P' W)
    (ξ a : ℝ) :
    ∃ (Φ : Rd d → Ω' → ℝ) (hΦc : ∀ ω', Continuous fun x => Φ x ω'),
      ∀ S : Set C(Rd d × Rd d, ℝ), MeasurableSet S →
        P {ω | l6a_metricOfFieldC ξ a
          (l6a_toFieldCMap (convMollifyNorm κ ε (h ω))) ∈ S} =
        P' {ω' | l6a_metricOfFieldC ξ a
          ⟨fun x => Φ x ω', hΦc ω'⟩ ∈ S} := by
  obtain ⟨Φ, hΦc, _, hCc, hlaw⟩ := l6a_centered_law hL1e hd hκ hε P h hh P' W hW
  refine ⟨Φ, hΦc, ?_⟩
  intro S hS
  exact l6a_aeContinuousFunctional_law P P'
    (fun x ω => convMollifyNorm κ ε (h ω) x) Φ hCc hΦc hlaw
    (l6a_metricOfFieldC ξ a) (l6a_measurable_metricOfFieldC ξ a) hS

end HigherDimLQGMetric
