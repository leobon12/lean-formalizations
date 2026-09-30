import QuantumZipper.Proofs.Thm18.G3ZqG3Top
import QuantumZipper.Proofs.Thm18.G3Pl4Node

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3 above G2 with abstract zooms: the capped wedge functional, measurability, law transfer

Generalized copy (D92) of the zoom-dependent parts of `G3Pl4Win.lean` (`g3pl4PhiCap`,
`g3pl4_phiCap_le_phi`, `g3pl4_phi_le_phiCap`), `G3Pl4Asm.lean` (`g3pl4_phiCap_le_U`),
`G3Pl2Meas.lean` (`measurable_g3plZoom2`), `G3Pl4Meas.lean` (the measurable version `g3pl4CapM`
on the boundary-measure certificate), `G3Pl4Tr.lean` (`lintegral_phiCap_eq_of_coordsLaw`) and
`G3Pl4Z.lean` (`g3pl4_aemeasurable_phiCap_Z`), with the plain zooms replaced by abstract zooms `Z`
(at the root) and `Z'` (at the partner). The zooms are used through joint measurability (`hZm`)
and invariance under equal regularized averages (`hZa`), exactly where the originals use
`measurable_zoomLaw` and `zoomLaw_congr`.

Sheffield, arXiv:1012.4797, proof of Thm. 1.8, pp. 71–72. Own bookkeeping copied from the
originals.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm

variable {Z Z' : ℝ → FieldSample → ℝ → LawD}

/-- The capped Palm-window functional with abstract zooms (window of `g3plXWin`). -/
def g3pl4PhiCapZ (Z Z' : ℝ → FieldSample → ℝ → LawD) (γ δ U L : ℝ) (s t : Set LawD)
    (y : FieldSample) : ℝ≥0∞ :=
  ∫⁻ b in {b | b < 0 ∧ qBoundaryMeasure γ y (Icc b 0) ≤ ENNReal.ofReal U ∧
      qBoundaryMeasure γ y (Icc b 0) ≤ qBoundaryMeasure γ y (Icc (-δ) 0)},
    s.indicator 1 (Z L y b) * t.indicator 1 (Z' L y (g3zPartner γ y b))
    ∂(qBoundaryMeasure γ y)

/-- `g3plHonXZ` is the expectation of the capped functional of `h_C`. -/
theorem g3plHonXZ_eq_phiCapZ (γ δ U L : ℝ) (s t : Set LawD) :
    g3plHonXZ Z Z' γ δ U L s t = ∫⁻ ω, g3pl4PhiCapZ Z Z' γ δ U L s t (g3plF γ ω) ∂gffBase.P :=
  rfl

theorem g3pl4_phiCapZ_le_U (γ δ U L : ℝ) (s t : Set LawD) (y : FieldSample) :
    g3pl4PhiCapZ Z Z' γ δ U L s t y ≤ ENNReal.ofReal U := by
  unfold g3pl4PhiCapZ
  refine (setLIntegral_mono measurable_const fun x _ => g3pl4_ind_mul_le_one _ _ _ _).trans ?_
  rw [setLIntegral_one]
  exact (measure_mono (μ := qBoundaryMeasure γ y)
    (t := {x : ℝ | x < 0 ∧ qBoundaryMeasure γ y (Icc x 0) ≤ ENNReal.ofReal U})
    fun x hx => ⟨hx.1, hx.2.1⟩).trans
    (g3pl4_measure_win_le (qBoundaryMeasure γ y) (ENNReal.ofReal U))

/-- **Capped ≤ uncapped.** -/
theorem g3pl4_phiCapZ_le_phiZ (γ δ U L : ℝ) (s t : Set LawD) (y : FieldSample) :
    g3pl4PhiCapZ Z Z' γ δ U L s t y ≤ g3plPhiZ Z Z' γ L U s t y := by
  unfold g3pl4PhiCapZ g3plPhiZ
  rw [← g3pl4_restrict_Iio (ν := qBoundaryMeasure γ y) (W := {b : ℝ | b < 0 ∧
      qBoundaryMeasure γ y (Icc b 0) ≤ ENNReal.ofReal U ∧
        qBoundaryMeasure γ y (Icc b 0) ≤ qBoundaryMeasure γ y (Icc (-δ) 0)})
    (fun b hb => hb.1)]
  refine lintegral_mono_set fun b hb => ?_
  refine ⟨?_, hb.2.1⟩
  simp [g1SideHalf, hb.1]

/-- **Uncapped ≤ capped + `U · 1{ν[−δ, 0] < U}`.** -/
theorem g3pl4_phiZ_le_phiCapZ (γ δ U L : ℝ) (s t : Set LawD) (y : FieldSample) :
    g3plPhiZ Z Z' γ L U s t y ≤ g3pl4PhiCapZ Z Z' γ δ U L s t y +
      {y : FieldSample | qBoundaryMeasure γ y (Icc (-δ) 0) < ENNReal.ofReal U}.indicator
        (fun _ => ENNReal.ofReal U) y := by
  set ν := qBoundaryMeasure γ y
  by_cases hc : ν (Icc (-δ) 0) < ENNReal.ofReal U
  · rw [indicator_of_mem (show y ∈ {y : FieldSample | qBoundaryMeasure γ y (Icc (-δ) 0) <
      ENNReal.ofReal U} from hc)]
    refine le_add_left ?_
    unfold g3plPhiZ
    refine (setLIntegral_mono measurable_const fun x _ => g3pl4_ind_mul_le_one _ _ _ _).trans ?_
    rw [setLIntegral_one]
    refine (Measure.restrict_apply_le _ _).trans ((measure_mono fun x hx => ?_).trans
      (g3pl4_measure_win_le ν (ENNReal.ofReal U)))
    have h1 : x ∈ g1SideHalf true := hx.1
    simp only [g1SideHalf, ite_true, mem_Iio] at h1
    exact ⟨h1, by simpa [g1SideSeg] using hx.2⟩
  · rw [indicator_of_notMem (show y ∉ {y : FieldSample | qBoundaryMeasure γ y (Icc (-δ) 0) <
      ENNReal.ofReal U} from hc), add_zero]
    push Not at hc
    unfold g3plPhiZ g3pl4PhiCapZ
    rw [← g3pl4_restrict_Iio (ν := qBoundaryMeasure γ y) (W := {b : ℝ | b < 0 ∧
        qBoundaryMeasure γ y (Icc b 0) ≤ ENNReal.ofReal U ∧
        qBoundaryMeasure γ y (Icc b 0) ≤ qBoundaryMeasure γ y (Icc (-δ) 0)})
      (fun b hb => hb.1)]
    refine lintegral_mono_set fun x hx => ?_
    have h1 : x ∈ g1SideHalf true := hx.1
    simp only [g1SideHalf, ite_true, mem_Iio] at h1
    have h2 : ν (Icc x 0) ≤ ENNReal.ofReal U := by simpa [g1SideSeg] using hx.2
    exact ⟨h1, h2, h2.trans hc⟩

/-! ## The measurable version on the certificate -/

open Classical in
/-- The integrand of the capped functional, read on the certificate (abstract zooms). -/
def g3pl4IntCapMZ (Z Z' : ℝ → FieldSample → ℝ → LawD) (γ δ L U : ℝ) (s t : Set LawD)
    (p : FieldSample × ℝ) : ℝ≥0∞ :=
  if p.2 < 0 ∧ bdryM γ p.1 (Icc p.2 0) ≤ ENNReal.ofReal U ∧
      bdryM γ p.1 (Icc p.2 0) ≤ bdryM γ p.1 (Icc (-δ) 0) then
    s.indicator 1 (Z L p.1 p.2) *
      t.indicator 1 (Z' L p.1 (lenRight (bdryM γ p.1) (bdryM γ p.1 (Icc p.2 0)).toReal))
  else 0

/-- The measurable capped functional (abstract zooms). -/
def g3pl4CapMZ (Z Z' : ℝ → FieldSample → ℝ → LawD) (γ δ L U : ℝ) (s t : Set LawD)
    (y : FieldSample) : ℝ≥0∞ :=
  ∫⁻ x, g3pl4IntCapMZ Z Z' γ δ L U s t (y, x) ∂(bdryM γ y)

theorem measurable_g3pl4IntCapMZ (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (hZm' : ∀ C, Measurable fun q : FieldSample × ℝ => Z' C q.1 q.2)
    (γ δ L U : ℝ) {s t : Set LawD} (hs : MeasurableSet s)
    (ht : MeasurableSet t) : Measurable (g3pl4IntCapMZ Z Z' γ δ L U s t) := by
  classical
  have hA : Measurable fun p : FieldSample × ℝ => s.indicator (1 : LawD → ℝ≥0∞)
      (Z L p.1 p.2) := (measurable_one.indicator hs).comp (hZm L)
  have hz2 : Measurable fun p : FieldSample × ℝ =>
      Z' L p.1 (lenRight (bdryM γ p.1) (bdryM γ p.1 (Icc p.2 0)).toReal) :=
    (hZm' L).comp (f := fun p : FieldSample × ℝ =>
      ((p.1, lenRight (bdryM γ p.1) (bdryM γ p.1 (Icc p.2 0)).toReal) : FieldSample × ℝ))
      (Measurable.prodMk measurable_fst (measurable_g3plPartner γ))
  have hB : Measurable fun p : FieldSample × ℝ => t.indicator (1 : LawD → ℝ≥0∞)
      (Z' L p.1 (lenRight (bdryM γ p.1) (bdryM γ p.1 (Icc p.2 0)).toReal)) :=
    (measurable_one.indicator ht).comp hz2
  have hδm : Measurable fun p : FieldSample × ℝ => bdryM γ p.1 (Icc (-δ) 0) :=
    (measurable_bdryM_Icc γ).comp (f := fun p : FieldSample × ℝ => (p.1, -δ))
      (measurable_fst.prodMk measurable_const)
  have hS : MeasurableSet {p : FieldSample × ℝ | p.2 < 0 ∧
      bdryM γ p.1 (Icc p.2 0) ≤ ENNReal.ofReal U ∧
      bdryM γ p.1 (Icc p.2 0) ≤ bdryM γ p.1 (Icc (-δ) 0)} :=
    (measurableSet_lt measurable_snd measurable_const).inter
      ((measurableSet_le (measurable_bdryM_Icc γ) measurable_const).inter
        (measurableSet_le (measurable_bdryM_Icc γ) hδm))
  exact Measurable.ite hS (hA.mul hB) measurable_const

theorem measurable_g3pl4CapMZ (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (hZm' : ∀ C, Measurable fun q : FieldSample × ℝ => Z' C q.1 q.2)
    (γ δ L U : ℝ) {s t : Set LawD} (hs : MeasurableSet s)
    (ht : MeasurableSet t) : Measurable (g3pl4CapMZ Z Z' γ δ L U s t) :=
  measurable_lintegral_family (measurable_bdryM γ)
    (fun y N => bdryM_Icc_ne_top γ y _ _) (measurable_g3pl4IntCapMZ hZm hZm' γ δ L U hs ht)

theorem g3pl4CapMZ_congr
    (hZa : ∀ (C : ℝ) (y y' : FieldSample) (x : ℝ), avgReg y = avgReg y' → Z C y x = Z C y' x)
    (hZa' : ∀ (C : ℝ) (y y' : FieldSample) (x : ℝ), avgReg y = avgReg y' → Z' C y x = Z' C y' x)
    {γ δ L U : ℝ} {s t : Set LawD} {y y' : FieldSample}
    (h : avgReg y = avgReg y') : g3pl4CapMZ Z Z' γ δ L U s t y = g3pl4CapMZ Z Z' γ δ L U s t y' := by
  have e1 : Z L y = Z L y' := funext fun x => hZa L y y' x h
  have e2 : Z' L y = Z' L y' := funext fun x => hZa' L y y' x h
  simp only [g3pl4CapMZ, g3pl4IntCapMZ, bdryM_congr (γ := γ) h, e1, e2]

theorem g3pl4CapMZ_eq {γ δ L U : ℝ} {s t : Set LawD} {y : FieldSample} (hc : E1.M4.BCert γ y) :
    g3pl4CapMZ Z Z' γ δ L U s t y = g3pl4PhiCapZ Z Z' γ δ U L s t y := by
  classical
  have hb : bdryM γ y = qBoundaryMeasure γ y := by unfold bdryM; rw [if_pos hc]
  set ν := qBoundaryMeasure γ y with hν
  have hanti : Measurable fun x : ℝ => ν (Icc x 0) :=
    Antitone.measurable fun a b hab => measure_mono (Icc_subset_Icc_left hab)
  set W := {b : ℝ | b < 0 ∧ ν (Icc b 0) ≤ ENNReal.ofReal U ∧ ν (Icc b 0) ≤ ν (Icc (-δ) 0)}
    with hWdef
  have hW : MeasurableSet W :=
    measurableSet_Iio.inter ((measurableSet_le hanti measurable_const).inter
      (measurableSet_le hanti measurable_const))
  unfold g3pl4CapMZ g3pl4PhiCapZ
  rw [hb, ← hν, ← hWdef, ← lintegral_indicator hW]
  refine lintegral_congr fun x => ?_
  simp only [g3pl4IntCapMZ, g3zPartner, hb, ← hν]
  by_cases hc : x < 0 ∧ ν (Icc x 0) ≤ ENNReal.ofReal U ∧ ν (Icc x 0) ≤ ν (Icc (-δ) 0)
  · rw [if_pos hc, indicator_of_mem (show x ∈ W from hc)]
  · rw [if_neg hc, indicator_of_notMem (show x ∉ W from hc)]

theorem g3pl4PhiCapZ_eq_data
    (hZa : ∀ (C : ℝ) (y y' : FieldSample) (x : ℝ), avgReg y = avgReg y' → Z C y x = Z C y' x)
    (hZa' : ∀ (C : ℝ) (y y' : FieldSample) (x : ℝ), avgReg y = avgReg y' → Z' C y x = Z' C y' x)
    {γ δ L U : ℝ} {s t : Set LawD} {y : FieldSample} (hy : IsLQGGood γ y) :
    g3pl4PhiCapZ Z Z' γ δ U L s t y =
      g3pl4CapMZ Z Z' γ δ L U s t (E1.fromC (WedgeMeas.dataFull H y).1) := by
  rw [← g3pl4CapMZ_eq (G4Core.bCert_of_isLQGGood hy)]
  exact g3pl4CapMZ_congr hZa hZa' (CoordsFull.avgReg_congr_full (E1.coordsFull_fromC y).symm)

/-- **Law transfer through the circle coordinates** (abstract zooms). -/
theorem lintegral_phiCapZ_eq_of_coordsLaw
    (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (hZa : ∀ (C : ℝ) (y y' : FieldSample) (x : ℝ), avgReg y = avgReg y' → Z C y x = Z C y' x)
    (hZm' : ∀ C, Measurable fun q : FieldSample × ℝ => Z' C q.1 q.2)
    (hZa' : ∀ (C : ℝ) (y y' : FieldSample) (x : ℝ), avgReg y = avgReg y' → Z' C y x = Z' C y' x)
    {γ δ L U : ℝ} {s t : Set LawD} (hs : MeasurableSet s)
    (ht : MeasurableSet t) {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {Y : Ω → FieldSample} {Y' : Ω' → FieldSample}
    (hg : ∀ᵐ ω ∂P, IsLQGGood γ (Y ω)) (hg' : ∀ᵐ ω ∂P', IsLQGGood γ (Y' ω))
    (hm : AEMeasurable (fun ω => CoordsFull.coordsFull (Y ω)) P)
    (hm' : AEMeasurable (fun ω => CoordsFull.coordsFull (Y' ω)) P')
    (hlaw : P.map (fun ω => CoordsFull.coordsFull (Y ω)) =
      P'.map (fun ω => CoordsFull.coordsFull (Y' ω))) :
    ∫⁻ ω, g3pl4PhiCapZ Z Z' γ δ U L s t (Y ω) ∂P =
      ∫⁻ ω, g3pl4PhiCapZ Z Z' γ δ U L s t (Y' ω) ∂P' := by
  have hF : Measurable fun c : ℕ → ℝ => g3pl4CapMZ Z Z' γ δ L U s t (E1.fromC c) :=
    (measurable_g3pl4CapMZ hZm hZm' γ δ L U hs ht).comp Cor15Group.measurable_fromC
  have e1 : ∫⁻ ω, g3pl4PhiCapZ Z Z' γ δ U L s t (Y ω) ∂P =
      ∫⁻ c, g3pl4CapMZ Z Z' γ δ L U s t (E1.fromC c)
        ∂(P.map fun ω => CoordsFull.coordsFull (Y ω)) := by
    rw [lintegral_map' hF.aemeasurable hm]
    exact lintegral_congr_ae (hg.mono fun ω h => g3pl4PhiCapZ_eq_data hZa hZa' h)
  have e2 : ∫⁻ ω, g3pl4PhiCapZ Z Z' γ δ U L s t (Y' ω) ∂P' =
      ∫⁻ c, g3pl4CapMZ Z Z' γ δ L U s t (E1.fromC c)
        ∂(P'.map fun ω => CoordsFull.coordsFull (Y' ω)) := by
    rw [lintegral_map' hF.aemeasurable hm']
    exact lintegral_congr_ae (hg'.mono fun ω h => g3pl4PhiCapZ_eq_data hZa hZa' h)
  rw [e1, e2, hlaw]

/-- A.e.-measurability of the capped functional of the unscaled wedge (abstract zooms). -/
theorem g3pl4_aemeasurable_phiCapZ_UW
    (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (hZa : ∀ (C : ℝ) (y y' : FieldSample) (x : ℝ), avgReg y = avgReg y' → Z C y x = Z C y' x)
    (hZm' : ∀ C, Measurable fun q : FieldSample × ℝ => Z' C q.1 q.2)
    (hZa' : ∀ (C : ℝ) (y y' : FieldSample) (x : ℝ), avgReg y = avgReg y' → Z' C y x = Z' C y' x)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω' : Type}
    [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {X : Ω' → FieldSample}
    {A : ℝ → Ω' → ℝ} (hX : IsFreeGFFModConstH X P') (hA : IsWedgeProcess (γ - 2 / γ) (Qc γ) A P')
    (hXA : IndepFun X (fun ω t => A t ω) P') {s t : Set LawD} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (δ U L : ℝ) :
    AEMeasurable (fun ω => g3pl4PhiCapZ Z Z' γ δ U L s t (g3plUW γ X A ω)) P' := by
  have hαQ : γ - 2 / γ < Qc γ := alpha_lt_Qc hγ hγ2
  have hgood : ∀ᵐ ω ∂P', IsLQGGood γ (g3plUW γ X A ω) :=
    LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hαQ Ω' _ P' X A inferInstance hX hA hXA
  have hc := WedgeMeas.aemeasurable_coords_wedgeField (P := P') hX.measurable_coord hA
  have hF : Measurable fun c : ℕ → ℝ =>
      g3pl4CapMZ Z Z' γ δ L U s t (Factorization.reconstruct c) :=
    (measurable_g3pl4CapMZ hZm hZm' γ δ L U hs ht).comp Factorization.measurable_reconstruct
  refine (hF.comp_aemeasurable hc).congr (hgood.mono fun ω h => ?_)
  simp only [Function.comp]
  rw [g3pl4CapMZ_congr hZa hZa' (Factorization.avgReg_reconstruct_coords _),
    g3pl4CapMZ_eq (G4Core.bCert_of_isLQGGood h)]

end R18
end QuantumZipper
