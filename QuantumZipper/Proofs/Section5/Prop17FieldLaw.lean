import QuantumZipper.Proofs.Section5.Prop17Field
import QuantumZipper.Proofs.LQG.LogSingGood

/-!
# Proposition 1.7: reduction of the shift statement to the reference wedge (S5-PLAN node D5-d)

Sheffield, arXiv:1012.4797, Proposition 1.7 (§1.6, p. 25): "`(ℍ, h*)` is a `γ`-quantum wedge" is a
statement about the *law* of `h*`, where `h* = h(· + y)` and `y` is the length-`L` point of `h`.
So the law of the shifted surface must be a function of the law of `h`. This file proves that
(for the law `fieldLawFull H` used by `IsQuantumWedge`), and so reduces `Prop17ShiftStmt γ L` to
the stationarity of the reference wedge law (`Prop17RefShiftStmt`, the D4⁺ + A6 + D5-c argument).

* `shiftL γ L x = canonical γ (translate x (wedgeLengthPoint γ L x))`: the shift map;
* `measurable_translate_apply_joint`: `(x, t) ↦ translate x t μ` is jointly measurable;
* `measurable_lengthPoint`: `a ↦ inf {y > 0 : L ≤ m a [0,y]}` is measurable for a measurable
  family of measures `m` (rational approximation; own elementary proof);
* `dataFull_shiftL`: on good samples, `dataFull H (shiftL γ L x) = shiftData γ L (dataFull H x)`
  with `shiftData` measurable (blueprint A4 factorization through `coords`);
* `fieldLawFull_shiftL_eq`: two quantum wedges with the same law have shifted fields with the same
  law, given a.s. goodness (R23 (c));
* `prop17ShiftStmt_of_ref`: `Prop17ShiftStmt γ L` from `WedgeGoodStmt γ γ` (R23 (c), goodness
  half) and `Prop17RefShiftStmt γ L`.

Own elementary proofs (measurability plumbing; AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace QuantumZipper
namespace S5
namespace FieldLaw

open Factorization CoordsFull WedgeMeas

/-- The shift map of Proposition 1.7: recentre at the length-`L` point, then canonicalize. -/
def shiftL (γ L : ℝ) (x : FieldSample) : FieldSample :=
  canonical γ (translate x (wedgeLengthPoint γ L x : ℂ))

/-! ## Joint measurability of translation -/

theorem measurable_translate_apply_joint (μ : Measure ℂ) [SFinite μ] :
    Measurable fun p : FieldSample × ℝ => translate p.1 (p.2 : ℂ) μ := by
  have e : (fun p : FieldSample × ℝ => translate p.1 (p.2 : ℂ) μ) =
      fun p => limUnder atTop fun k : ℕ => ∫ w, avgReg p.1 k (w + p.2) ∂μ := by
    funext p
    simp only [translate, evalReg]
    congr 1; funext k
    rw [integral_map (by fun_prop) (RegClosure.measurable_avgReg_slice p.1 k).aestronglyMeasurable]
  rw [e]
  have hf : ∀ k : ℕ, StronglyMeasurable
      fun p : FieldSample × ℝ => ∫ w, avgReg p.1 k (w + p.2) ∂μ := fun k =>
    StronglyMeasurable.integral_prod_right'
      (f := fun q : (FieldSample × ℝ) × ℂ => avgReg q.1.1 k (q.2 + q.1.2))
      ((measurable_avgReg k).comp (by fun_prop :
        Measurable fun q : (FieldSample × ℝ) × ℂ => (q.1.1, q.2 + (q.1.2 : ℂ)))).stronglyMeasurable
  exact (StronglyMeasurable.limUnder hf).measurable

/-! ## Measurability of the length point -/

theorem measurable_lengthPoint {α : Type*} [MeasurableSpace α] {m : α → Measure ℝ}
    (hm : Measurable m) (L : ℝ) :
    Measurable fun a => sInf {y : ℝ | 0 < y ∧ ENNReal.ofReal L ≤ m a (Icc 0 y)} := by
  refine measurable_of_Iio fun c => ?_
  set S := fun a => {y : ℝ | 0 < y ∧ ENNReal.ofReal L ≤ m a (Icc 0 y)} with hS
  have hup : ∀ a y y', y ∈ S a → y ≤ y' → y' ∈ S a := fun a y y' hy hyy' =>
    ⟨hy.1.trans_le hyy', hy.2.trans (measure_mono (Icc_subset_Icc_right hyy'))⟩
  have hbdd : ∀ a, BddBelow (S a) := fun a => ⟨0, fun y hy => hy.1.le⟩
  have e : (fun a => sInf (S a)) ⁻¹' Iio c =
      (⋃ q : ℚ, {_a : α | (0 : ℝ) < q ∧ (q : ℝ) < c} ∩
          {a | ENNReal.ofReal L ≤ m a (Icc 0 (q : ℝ))}) ∪
        ((⋂ q : ℚ, {_a : α | ¬ (0 : ℝ) < q} ∪ {a | m a (Icc 0 (q : ℝ)) < ENNReal.ofReal L}) ∩
          {_a : α | 0 < c}) := by
    ext a
    simp only [mem_preimage, mem_Iio, mem_union, mem_iUnion, mem_iInter, mem_inter_iff,
      mem_ofPred_eq]
    by_cases hne : (S a).Nonempty
    · constructor
      · intro hlt
        obtain ⟨y, hy, hyc⟩ := exists_lt_of_csInf_lt hne hlt
        obtain ⟨q, hyq, hqc⟩ := exists_rat_btwn hyc
        exact Or.inl ⟨q, ⟨hy.1.trans hyq, hqc⟩, (hup a y q hy hyq.le).2⟩
      · rintro (⟨q, ⟨hq0, hqc⟩, hq⟩ | ⟨hall, -⟩)
        · exact (csInf_le (hbdd a) ⟨hq0, hq⟩).trans_lt hqc
        · exfalso
          obtain ⟨y, hy⟩ := hne
          obtain ⟨q, hyq, -⟩ := exists_rat_btwn (lt_add_one y)
          rcases hall q with h | h
          · exact h (hy.1.trans hyq)
          · exact (not_le.2 h) (hup a y q hy hyq.le).2
    · rw [not_nonempty_iff_eq_empty] at hne
      have hnot : ∀ y : ℝ, y ∉ S a := fun y hy => by rw [hne] at hy; exact hy
      rw [hne, Real.sInf_empty]
      constructor
      · intro hc
        refine Or.inr ⟨fun q => ?_, hc⟩
        by_cases hq : (0 : ℝ) < q
        · exact Or.inr (not_le.1 fun h => hnot q ⟨hq, h⟩)
        · exact Or.inl hq
      · rintro (⟨q, ⟨hq0, -⟩, hq⟩ | ⟨-, hc⟩)
        · exact absurd ⟨hq0, hq⟩ (hnot q)
        · exact hc
  rw [e]
  have hmeas : ∀ q : ℚ, Measurable fun a => m a (Icc 0 (q : ℝ)) := fun q =>
    (Measure.measurable_coe measurableSet_Icc).comp hm
  refine MeasurableSet.union (MeasurableSet.iUnion fun q => ?_) (MeasurableSet.inter
    (MeasurableSet.iInter fun q => ?_) (MeasurableSet.const _))
  · exact (MeasurableSet.const _).inter (measurableSet_le measurable_const (hmeas q))
  · exact (MeasurableSet.const _).union (measurableSet_lt (hmeas q) measurable_const)

open Classical in
/-- The boundary measure on the good set (junk `0` elsewhere). -/
def bdryG (γ : ℝ) (x : FieldSample) : Measure ℝ :=
  if IsLQGGood γ x then qBoundaryMeasure γ x else 0

/-- The length point computed from `bdryG`. -/
def lenG (γ L : ℝ) (x : FieldSample) : ℝ :=
  sInf {y : ℝ | 0 < y ∧ ENNReal.ofReal L ≤ bdryG γ x (Icc 0 y)}

theorem measurable_lenG (γ L : ℝ) : Measurable (lenG γ L) :=
  measurable_lengthPoint (GoodMeas.measurable_qBoundaryMeasure_global γ) L

theorem lenG_eq {γ L : ℝ} {x : FieldSample} (hx : IsLQGGood γ x) :
    lenG γ L x = wedgeLengthPoint γ L x := by
  simp [lenG, bdryG, hx, wedgeLengthPoint]

/-! ## The shift map through the coordinates -/

/-- `coords` read off `coordsFull`. -/
def proj (c : ℕ → ℝ) : ℕ → ℝ := fun i => c (Classical.choose (WedgeGood.exists_fullIndex i))

theorem measurable_proj : Measurable proj :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

theorem coords_eq_proj (x : FieldSample) : coords x = proj (coordsFull x) := by
  funext i
  simp only [proj, coordsFull, coords, Classical.choose_spec (WedgeGood.exists_fullIndex i)]

/-- Coordinates of the translated reconstruction. -/
def tcoords (γ L : ℝ) (c : ℕ → ℝ) : ℕ → ℝ :=
  coords (translate (reconstruct c) (lenG γ L (reconstruct c) : ℂ))

theorem measurable_tcoords (γ L : ℝ) : Measurable (tcoords γ L) := by
  refine measurable_pi_iff.2 fun i => ?_
  change Measurable fun c : ℕ → ℝ => translate (reconstruct c) ((lenG γ L (reconstruct c) : ℝ) : ℂ)
    (foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2))
  have hp : Measurable fun c : ℕ → ℝ => (reconstruct c, lenG γ L (reconstruct c)) :=
    measurable_reconstruct.prodMk ((measurable_lenG γ L).comp measurable_reconstruct)
  exact (measurable_translate_apply_joint
    (foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2))).comp (f := fun c : ℕ → ℝ =>
      (reconstruct c, lenG γ L (reconstruct c))) hp

/-- The shift map on the data space of `fieldLawFull H`. -/
def shiftData (γ L : ℝ) (d : (ℕ → ℝ) × (TestFun H → ℝ)) : (ℕ → ℝ) × (TestFun H → ℝ) :=
  dataFull H (resc (Qc γ) (tcoords γ L (proj d.1), scaleG γ (tcoords γ L (proj d.1))))

theorem measurable_shiftData (γ L : ℝ) : Measurable (shiftData γ L) := by
  have h : Measurable fun d : (ℕ → ℝ) × (TestFun H → ℝ) => tcoords γ L (proj d.1) :=
    (measurable_tcoords γ L).comp (measurable_proj.comp measurable_fst)
  exact (measurable_dataFull_resc H (Qc γ)).comp (h.prodMk ((measurable_scaleG γ).comp h))

/-- On good samples the data of the shifted field is a measurable function of the data. -/
theorem dataFull_shiftL {γ L : ℝ} {x : FieldSample} (hx : IsLQGGood γ x) :
    dataFull H (shiftL γ L x) = shiftData γ L (dataFull H x) := by
  have hav := avgReg_reconstruct_coords x
  have hx' : IsLQGGood γ (reconstruct (coords x)) := (GoodSample.isLQGGood_iff_reconstruct γ x).2 hx
  have hy : lenG γ L (reconstruct (coords x)) = wedgeLengthPoint γ L x := by
    rw [lenG_eq hx']
    unfold wedgeLengthPoint
    rw [Factorization.qBoundaryMeasure_congr hav]
  have ht : tcoords γ L (coords x) = coords (translate x (wedgeLengthPoint γ L x : ℂ)) := by
    rw [tcoords, hy, Factorization.translate_congr hav]
  have hW : IsLQGGood γ (translate x (wedgeLengthPoint γ L x : ℂ)) := hx.translate _
  simp only [shiftData, dataFull, ← coords_eq_proj, ht, scaleG_coords hW, ← canonical_eq_resc]
  rfl

/-! ## Law transfer -/

theorem fieldLawFull_shiftL_eq_map {γ L : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → FieldSample} (hm : AEMeasurable (fun ω => dataFull H (Y ω)) P)
    (hg : ∀ᵐ ω ∂P, IsLQGGood γ (Y ω)) :
    fieldLawFull H (fun ω => shiftL γ L (Y ω)) P = (fieldLawFull H Y P).map (shiftData γ L) := by
  show P.map (fun ω => dataFull H (shiftL γ L (Y ω))) =
    (P.map fun ω => dataFull H (Y ω)).map (shiftData γ L)
  rw [AEMeasurable.map_map_of_aemeasurable (measurable_shiftData γ L).aemeasurable
    hm]
  refine Measure.map_congr ?_
  filter_upwards [hg] with ω hω
  exact dataFull_shiftL hω

/-- **Law transfer.** Two random fields with the same law (`fieldLawFull H`), a.e.-measurable
data and a.s. good samples have shifted fields with the same law. -/
theorem fieldLawFull_shiftL_eq {γ L : ℝ}
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    {Y : Ω → FieldSample} {Y' : Ω' → FieldSample}
    (hm : AEMeasurable (fun ω => dataFull H (Y ω)) P)
    (hm' : AEMeasurable (fun ω => dataFull H (Y' ω)) P') (hg : ∀ᵐ ω ∂P, IsLQGGood γ (Y ω))
    (hg' : ∀ᵐ ω ∂P', IsLQGGood γ (Y' ω)) (hlaw : fieldLawFull H Y P = fieldLawFull H Y' P') :
    fieldLawFull H (fun ω => shiftL γ L (Y ω)) P = fieldLawFull H (fun ω => shiftL γ L (Y' ω)) P' := by
  rw [fieldLawFull_shiftL_eq_map hm hg, fieldLawFull_shiftL_eq_map hm' hg', hlaw]

/-! ## The reduction of `Prop17ShiftStmt` -/

/-- **R23 (c), goodness half** (TASKS R23, AUDIT8 §3.1 (c), `IsQuantumWedge.ae_unitArea`): the
samples of every `α`-quantum wedge are a.s. good. Hypothesis only. -/
def WedgeGoodStmt (γ α : ℝ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → FieldSample),
    IsQuantumWedge γ α Y P → ∀ᵐ ω ∂P, IsLQGGood γ (Y ω)

/-- **Measurability of wedge data (flagged gap).** The data of every `α`-quantum wedge is
a.e.-measurable. `IsQuantumWedge` does not ask for it, and at the pinned mathlib the push-forward
under a non-a.e.-measurable map is a Dirac mass (`Measure.map_of_not_aemeasurable_of_ne_zero`),
so this follows from (and is equivalent to) the reference wedge law not being that Dirac mass.
Hypothesis only. -/
def WedgeDataAEMeasStmt (γ α : ℝ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → FieldSample),
    IsQuantumWedge γ α Y P → AEMeasurable (fun ω => dataFull H (Y ω)) P

/-- **D5-e (remaining heart of D5).** The reference `γ`-wedge law is invariant under the shift
map `shiftL γ L` (to be proved from D4⁺, A6 `palm_shift_right_bound` and D5-c). -/
def Prop17RefShiftStmt (γ L : ℝ) : Prop :=
  ∀ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (X : Ω' → FieldSample)
    (A : ℝ → Ω' → ℝ), IsProbabilityMeasure P' → IsFreeGFFModConstH X P' →
    IsWedgeProcess γ (Qc γ) A P' → IndepFun X (fun ω t => A t ω) P' →
    fieldLawFull H
        (fun ω => shiftL γ L (canonical γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))))
        P' =
      fieldLawFull H
        (fun ω => canonical γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))) P'

/-- **D5-d.** `Prop17ShiftStmt γ L` from R23 (c) (goodness) and the stationarity of the reference
wedge law. -/
theorem prop17ShiftStmt_of_ref {γ L : ℝ} (hmeas : WedgeDataAEMeasStmt γ γ)
    (hgood : WedgeGoodStmt γ γ) (href : Prop17RefShiftStmt γ L) : Prop17ShiftStmt γ L := by
  intro Ω _ P _ Y hY
  obtain ⟨hα, Ω', _, P', X, A, hP', hX, hA, hI, hlaw⟩ := hY
  have hY : IsQuantumWedge γ γ Y P := ⟨hα, Ω', _, P', X, A, hP', hX, hA, hI, hlaw⟩
  refine ⟨hα, Ω', _, P', X, A, hP', hX, hA, hI, ?_⟩
  have hR : IsQuantumWedge γ γ
      (fun ω => canonical γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))) P' :=
    ⟨hα, Ω', _, P', X, A, hP', hX, hA, hI, rfl⟩
  rw [← href Ω' _ P' X A hP' hX hA hI]
  exact fieldLawFull_shiftL_eq (hmeas P Y hY) (hmeas P' _ hR) (hgood P Y hY) (hgood P' _ hR) hlaw

/-- **Proposition 1.7, conditional assembly.** `theorem1_7` from the wedge boundary regularity
(D5-a), R23 (c) goodness, a.e.-measurability of wedge data, and the reference stationarity D5-e. -/
theorem theorem1_7_of_ref
    (hreg : ∀ γ : ℝ, 0 < γ → γ < 2 → WedgeBoundaryRegularStmt γ γ)
    (hmeas : ∀ γ : ℝ, 0 < γ → γ < 2 → WedgeDataAEMeasStmt γ γ)
    (hgood : ∀ γ : ℝ, 0 < γ → γ < 2 → WedgeGoodStmt γ γ)
    (href : ∀ γ L : ℝ, 0 < γ → γ < 2 → 0 < L → Prop17RefShiftStmt γ L) : theorem1_7 :=
  theorem1_7_of hreg fun γ L hγ hγ2 hL =>
    prop17ShiftStmt_of_ref (hmeas γ hγ hγ2) (hgood γ hγ hγ2) (href γ L hγ hγ2 hL)

end FieldLaw
end S5
end QuantumZipper
