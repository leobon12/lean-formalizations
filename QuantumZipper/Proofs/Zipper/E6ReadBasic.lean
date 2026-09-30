import QuantumZipper.Proofs.Zipper.E6Up
import QuantumZipper.Proofs.Zipper.ESMComplF1
import QuantumZipper.Proofs.Wire2b
import QuantumZipper.Proofs.Section5.Prop17RawLaw

/-!
# E6-READ, part 1: the regularized reconstruction `regG` and the transfer of readability

Task E6-READ (readability node `E6.E6ReadStmt` behind `E6.e6Up_of_read`).

* `regG`: the fixed measurable reconstruction of `configLawFull`'s field data from the small
  circle coordinates `Factorization.coords`: the **regularized** values `evalReg` at all
  `coordsFull` circles and the regularized pairings `pairTest` (both only read `avgReg`, i.e.
  small dyadic circles, `Factorization.avgReg_reconstruct_coords`).
* `RegReadable Y P`: a.s. the raw values of `Y` at all `coordsFull` circles equal the regularized
  ones, and for each test function a.s. `pairRaw = pairTest`. `readableBy_regG` shows
  `RegReadable Y P → ReadableBy regG Y P`.
* `readableBy_of_fieldLawFull_eq`: readability by a measurable `G` depends only on
  `fieldLawFull H` (given a.e.-measurable data maps); it transfers from the reference wedge to
  any `IsQuantumWedge` field.

Own elementary arguments (definitions and measurable-set bookkeeping; the analytic content is the
regularity of the fields, which is an input). The idea that a GFF-type field is determined by its
small circle averages is Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math.
185 (2011), §3.1 (circle-average regularization).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace E6

/-- The `i`-th folded circle of the `coordsFull` enumeration. -/
def fcFull (i : ℕ) : Measure ℂ :=
  foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2

/-- **The regularized reconstruction.** From the small circle coordinates `y`, the regularized
values at all `coordsFull` circles and the regularized test pairings of `reconstruct y`. -/
def regG (y : ℕ → ℝ) : (ℕ → ℝ) × (TestFun H → ℝ) :=
  (fun i => evalReg (Factorization.reconstruct y) (fcFull i),
    fun ρ => pairTest (Factorization.reconstruct y) ρ.1)

theorem measurable_regG : Measurable regG := by
  refine Measurable.prodMk (measurable_pi_iff.2 fun i => ?_) (measurable_pi_iff.2 fun ρ => ?_)
  · have : SFinite (fcFull i) := by unfold fcFull; infer_instance
    exact (measurable_evalReg (fcFull i)).comp Factorization.measurable_reconstruct
  · exact (measurable_pairTest ρ.1).comp Factorization.measurable_reconstruct

theorem regG_coords (x : FieldSample) :
    regG (Factorization.coords x) = (fun i => evalReg x (fcFull i), fun ρ => pairTest x ρ.1) := by
  simp only [regG, Factorization.evalReg_congr (Factorization.avgReg_reconstruct_coords x),
    Factorization.pairTest_congr (Factorization.avgReg_reconstruct_coords x)]

/-- **Regular readability**: raw values at the `coordsFull` circles and raw test pairings agree
with the regularized ones (the circles jointly a.s., the pairings a.s. per test function). -/
def RegReadable {Ω : Type*} [MeasurableSpace Ω] (Y : Ω → FieldSample) (P : Measure Ω) : Prop :=
  (∀ᵐ ω ∂P, ∀ i, Y ω (fcFull i) = evalReg (Y ω) (fcFull i)) ∧
    ∀ ρ : TestFun H, ∀ᵐ ω ∂P, pairRaw (Y ω) ρ.1 = pairTest (Y ω) ρ.1

theorem readableBy_regG {Ω : Type*} [MeasurableSpace Ω] {Y : Ω → FieldSample} {P : Measure Ω}
    (h : RegReadable Y P) : ReadableBy regG Y P := by
  refine ⟨?_, fun ρ => ?_⟩
  · filter_upwards [h.1] with ω hω
    rw [regG_coords]
    funext i
    exact hω i
  · filter_upwards [h.2 ρ] with ω hω
    rw [regG_coords]
    exact hω

/-! ## Transfer of readability along equality of `fieldLawFull` -/

theorem measurableSet_circleEvent {G : (ℕ → ℝ) → (ℕ → ℝ) × (TestFun H → ℝ)} (hG : Measurable G) :
    MeasurableSet {d : (ℕ → ℝ) × (TestFun H → ℝ) | d.1 = (G (coordsOfFull d.1)).1} := by
  have e : {d : (ℕ → ℝ) × (TestFun H → ℝ) | d.1 = (G (coordsOfFull d.1)).1} =
      ⋂ i, {d | d.1 i = (G (coordsOfFull d.1)).1 i} := by
    ext d; simp only [mem_ofPred_eq, mem_iInter]; exact funext_iff
  rw [e]
  refine MeasurableSet.iInter fun i => measurableSet_eq_fun ?_ ?_
  · exact (measurable_pi_apply i).comp measurable_fst
  · exact (measurable_pi_apply i).comp
      (measurable_fst.comp (hG.comp (measurable_coordsOfFull.comp measurable_fst)))

theorem measurableSet_pairEvent {G : (ℕ → ℝ) → (ℕ → ℝ) × (TestFun H → ℝ)} (hG : Measurable G)
    (ρ : TestFun H) :
    MeasurableSet {d : (ℕ → ℝ) × (TestFun H → ℝ) | d.2 ρ = (G (coordsOfFull d.1)).2 ρ} :=
  measurableSet_eq_fun ((measurable_pi_apply ρ).comp measurable_snd)
    ((measurable_pi_apply ρ).comp
      (measurable_snd.comp (hG.comp (measurable_coordsOfFull.comp measurable_fst))))

/-- **Readability is a property of `fieldLawFull H`.** -/
theorem readableBy_of_fieldLawFull_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {Y : Ω → FieldSample} {Z : Ω' → FieldSample}
    {G : (ℕ → ℝ) → (ℕ → ℝ) × (TestFun H → ℝ)} (hG : Measurable G)
    (hY : AEMeasurable (fun ω => WedgeMeas.dataFull H (Y ω)) P)
    (hZ : AEMeasurable (fun ω => WedgeMeas.dataFull H (Z ω)) P')
    (hlaw : fieldLawFull H Y P = fieldLawFull H Z P') (hr : ReadableBy G Z P') :
    ReadableBy G Y P := by
  have hl : P.map (fun ω => WedgeMeas.dataFull H (Y ω)) =
      P'.map (fun ω => WedgeMeas.dataFull H (Z ω)) := hlaw
  refine ⟨?_, fun ρ => ?_⟩
  · have hZ' : ∀ᵐ d ∂P'.map (fun ω => WedgeMeas.dataFull H (Z ω)),
        d.1 = (G (coordsOfFull d.1)).1 := by
      rw [ae_map_iff hZ (measurableSet_circleEvent hG)]
      filter_upwards [hr.1] with ω hω
      simpa [WedgeMeas.dataFull, coordsOfFull_coordsFull] using hω
    rw [← hl, ae_map_iff hY (measurableSet_circleEvent hG)] at hZ'
    filter_upwards [hZ'] with ω hω
    simpa [WedgeMeas.dataFull, coordsOfFull_coordsFull] using hω
  · have hZ' : ∀ᵐ d ∂P'.map (fun ω => WedgeMeas.dataFull H (Z ω)),
        d.2 ρ = (G (coordsOfFull d.1)).2 ρ := by
      rw [ae_map_iff hZ (measurableSet_pairEvent hG ρ)]
      filter_upwards [hr.2 ρ] with ω hω
      simpa [WedgeMeas.dataFull, coordsOfFull_coordsFull] using hω
    rw [← hl, ae_map_iff hY (measurableSet_pairEvent hG ρ)] at hZ'
    filter_upwards [hZ'] with ω hω
    simpa [WedgeMeas.dataFull, coordsOfFull_coordsFull] using hω

end E6
end QuantumZipper
