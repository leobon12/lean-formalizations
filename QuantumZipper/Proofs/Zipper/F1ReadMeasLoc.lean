import QuantumZipper.Proofs.Zipper.F1ReadMeas
import QuantumZipper.Proofs.Zipper.F1ReadMeasVague
import QuantumZipper.Proofs.Zipper.B5LocF1Assembly

/-!
# READLEN, B5 input (R4): the local lengths are a measurable functional (`LocLengthsMeasStmt`)

Theorem 1.3, node B5 (locality) as consumed by F1 (`B5LocF1Assembly.lean`, input (R4)).
**`locLengthsMeasStmt_holds`**: `B5.LocLengthsMeasStmt γ κ` for all `γ, κ`.

The functional `locRd`: for `q = (x, path on [0,u])`,
* the path is extended to `ℝ≥0` (`extIic`), read through its dyadic values and turned into a
  continuous path on `[0,t]` on the measurable certificate `DyUC` (`pathT`);
* the side images are read by `ESM.sideReader` (complex approximants), which computes
  `sideImages` when all real points are alive (`ESM.sideImages_Wof_eq_sideReader`);
* the unzipped field is replaced by its coordinate-rebuilt path surrogate `surQC` (the reverse
  flow of the time-reversed path, any `Q`; same circle coordinates by
  `UnzipInvariance.fwdMapInv_eq_revMap_timeRev`), which is measurable in `q`
  (`measurable_evalReg_push_gen`, `measurable_integral_log_deriv_gen`);
* the masses of `[O⁻, 0]` and `[0, O⁺]` are read by the certificate-free reader `vagueRd`
  (`F1ReadMeasVague`), which computes `qBoundaryMeasureOn γ _ (-a, a)` whenever a local vague
  limit exists and the interval lies in `(-a, a)`.

Own bookkeeping (Sheffield, arXiv:1012.4797, §5.4 pp. 70–72 states locality without proof).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F1

open ESM CharFun CoordsFull

/-- The path surrogate of a field unzipped at time `t` (any `Q`): the field pushed by the reverse
flow of the time-reversed path. -/
def surQ (κ t : ℝ) (ht : 0 ≤ t) (Q : ℝ) (p : FieldSample × C(Icc (0 : ℝ) t, ℝ)) :
    FieldSample :=
  coordChange p.1 (revMap (Wof κ t ht (revPath t ht p.2)) t) Q

theorem measurable_surQ_apply (κ t : ℝ) (ht : 0 ≤ t) (Q : ℝ) (i : ℕ) :
    Measurable fun p : FieldSample × C(Icc (0 : ℝ) t, ℝ) =>
      surQ κ t ht Q p (foldedCircle (fullIndex i).1 (fullIndex i).2) := by
  have hμ : foldedCircle (fullIndex i).1 (fullIndex i).2 Hᶜ = 0 :=
    foldedCircle_compl_H_eq_zero _ (UnzipFull.fullIndex_radius_pos i)
  have hr : Measurable fun p : FieldSample × C(Icc (0 : ℝ) t, ℝ) => revPath t ht p.2 :=
    (measurable_revPath t ht).comp measurable_snd
  exact ((UnzipFull.measurable_evalReg_push_gen κ t ht _).comp (hr.prodMk measurable_fst)).add
    (((B1Full.measurable_integral_log_deriv_gen κ t ht _ hμ).comp hr).const_mul Q)

/-- The coordinate reconstruction of `surQ` (a measurable `FieldSample`-valued map). -/
def surQC (κ t : ℝ) (ht : 0 ≤ t) (Q : ℝ) (p : FieldSample × C(Icc (0 : ℝ) t, ℝ)) :
    FieldSample :=
  fromCoords (coordsFull (surQ κ t ht Q p))

theorem measurable_surQC (κ t : ℝ) (ht : 0 ≤ t) (Q : ℝ) : Measurable (surQC κ t ht Q) :=
  measurable_fromCoords (measurable_pi_iff.2 fun i => measurable_surQ_apply κ t ht Q i)

theorem coordsFull_fromCoords_coordsFull (x : FieldSample) :
    coordsFull (fromCoords (coordsFull x)) = coordsFull x := by
  classical
  funext i
  have h : ∃ j, foldedCircle (fullIndex j).1 (fullIndex j).2 =
      foldedCircle (fullIndex i).1 (fullIndex i).2 := ⟨i, rfl⟩
  simp only [coordsFull, fromCoords, h, ↓reduceDIte]
  exact congrArg x (Nat.find_spec h)

/-- A path on `[0,u]` extended to `ℝ≥0` (frozen after `u`). -/
def extIic (u : ℝ≥0) (q : Set.Iic u → ℝ) : ℝ≥0 → ℝ :=
  fun r => q ⟨min r u, Set.mem_Iic.2 (min_le_right _ _)⟩

theorem measurable_extIic (u : ℝ≥0) : Measurable (extIic u) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

theorem continuous_extIic (u : ℝ≥0) {q : Set.Iic u → ℝ} (hq : Continuous q) :
    Continuous (extIic u q) :=
  hq.comp (Continuous.subtype_mk (continuous_id.min continuous_const) _)

open Classical in
/-- The continuous path on `[0,t]` read from the dyadic values (on the certificate `DyUC`). -/
def pathT (t : ℝ) (p : ℝ≥0 → ℝ) : C(Icc (0 : ℝ) t, ℝ) :=
  if h : DyUC p then ⟨fun s => readDrv p s, (continuous_readDrv_of_dyUC h).comp
    continuous_subtype_val⟩ else 0

theorem measurable_pathT (t : ℝ) : Measurable (pathT t) := by
  classical
  refine ContinuousMap.measurable_iff_eval.2 fun s => ?_
  have e : (fun p => pathT t p s) = fun p => if DyUC p then readDrv p s else 0 := by
    funext p
    unfold pathT
    split_ifs <;> rfl
  rw [e]
  exact Measurable.ite measurableSet_dyUC (measurable_readDrv_apply s) measurable_const

theorem measurable_pathT_ext (t : ℝ) (u : ℝ≥0) :
    Measurable fun q : FieldSample × (Set.Iic u → ℝ) => pathT t (extIic u q.2) :=
  (measurable_pathT t).comp ((measurable_extIic u).comp measurable_snd)

theorem measurable_locX (γ κ : ℝ) (u : ℝ≥0) (t : ℝ) (ht : 0 ≤ t) :
    Measurable fun q : FieldSample × (Set.Iic u → ℝ) =>
      surQC κ t ht (Qc γ) (q.1, pathT t (extIic u q.2)) :=
  (measurable_surQC κ t ht _).comp (measurable_fst.prodMk (measurable_pathT_ext t u))

theorem measurable_locS (κ : ℝ) (u : ℝ≥0) (t : ℝ) (ht : 0 ≤ t) :
    Measurable fun q : FieldSample × (Set.Iic u → ℝ) =>
      sideReader κ t ht (pathT t (extIic u q.2)) :=
  (measurable_sideReader κ t ht).comp (measurable_pathT_ext t u)

theorem vagueRd_congr {γ : ℝ} {x x' : FieldSample} (h : bdryApprox γ x = bdryApprox γ x')
    (b c : ℝ) : vagueRd γ x b c = vagueRd γ x' b c := by
  unfold vagueRd; rw [h]

end F1
end QuantumZipper
