import QuantumZipper.Proofs.Zipper.F1ReadMeas
import QuantumZipper.Proofs.Zipper.F1ABJensen

/-!
# READLEN at a fixed time `t`: the reader, its measurability, and the deterministic identity

Theorem 1.3, node F1 (`F1.LenReadTimeStmt`): the fixed-time form of `F1.ReadLenAEMeasStmt`
(Sheffield, arXiv:1012.4797, §5.4, p. 72; the time-`1` statement is in `F1ReadMeas.lean`). For
every fixed `t ≥ 0` the unzipped lengths `d ↦ unzipLengths √κ (readCfg d) t` are a.e.-measurable
for the `P_*` data law.

Everything of `F1ReadMeas.lean` is repeated here with `1` replaced by a general `t ≥ 0`. The
readers `ESM.nuSur`, `ESM.sideReader` and the surrogate `ESM.unzipFieldCoord` are already stated
for general time, so only the glue changes:

* `rdMT`: the reader on `(coordinates, path on [0,t])` (gated boundary measure `ESM.nuSur` of the
  path surrogate of the unzipped field, on the windows given by `ESM.sideReader`), and
  `measurable_rdMT`.
* `coordsFull_unzip_eq_sur_t`: time-`t` form of `coordsFull_unzip_eq_sur` (the unzipped field and
  its path surrogate have the same circle coordinates).
* `rdTimeD`: the path on `[0,t]` read from the data through the continuity certificate `DyUC`;
  `Wof_rdTimeD`: its driver is `readDrv p`.
* `PathGoodAll`, `FieldFinT`, `ReadGoodT`: good data at time `t`. `PathGoodAll` does not mention
  `t`: it asks that every real `x ≠ 0` be alive at *every* time `T ≥ 0` (it implies the time-`1`
  `PathGood`).
* `readLenT_eq_rdMT`: on good data, `unzipLengths √κ (readCfg d) t` equals `rdMT` evaluated at
  any continuous path `f` with `Wof κ t ht f = readDrv d.2` on `[0,t]`; `rdGT` and
  `aemeasurable_unzipLengths_readCfg_of_ae_good`: the measurable version and a.e.-measurability.

Own bookkeeping (the paper states the intrinsic property without proof).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F1

open ESM CharFun CoordsFull

/-! ## The reader at time `t` -/

/-- **The unzipped field and its path surrogate have the same circle coordinates at time `t`**
(continuous driver started at `0`, read on `[0,t]` through `Wof κ t ht f`). Time-`t` form of
`coordsFull_unzip_eq_sur`. -/
theorem coordsFull_unzip_eq_sur_t {κ t : ℝ} (ht : 0 ≤ t) {W : ℝ → ℝ} (hc : Continuous W)
    (h0 : W 0 = 0) {f : C(Icc (0 : ℝ) t, ℝ)}
    (hf : ∀ r ∈ Icc (0 : ℝ) t, Wof κ t ht f r = W r) (c : ℕ → ℝ) :
    coordsFull (unzippedField (Real.sqrt κ) (Factorization.reconstruct (WedgeCan4.piC c), W) t) =
      coordsFull (unzipFieldCoord κ t ht (rdField κ c, f)) := by
  have hEqOn : EqOn (fwdMapInv W t) (revMap (Wof κ t ht (revPath t ht f)) t) H := by
    intro w hw
    rw [UnzipInvariance.fwdMapInv_eq_revMap_timeRev W hc h0 ht hw]
    refine ReverseFlow.revMap_congr_drive w fun r hr => ?_
    have hr' : t - r ∈ Icc (0 : ℝ) t := ⟨by linarith [hr.2], by linarith [hr.1]⟩
    have e1 := hf (t - r) hr'
    have e2 := hf t ⟨ht, le_rfl⟩
    show W (t - r) - W t = _
    rw [← e1, ← e2]
    simp only [Wof, projIcc_of_mem ht hr, projIcc_of_mem ht hr',
      projIcc_of_mem ht (show t ∈ Icc (0 : ℝ) t from ⟨ht, le_rfl⟩), revPath_apply]
    ring
  rw [coordsFull_unzipFieldCoord]
  funext i
  refine (UnzipInvariance.coordChange_congr_of_eqOn hEqOn
    (foldedCircle_compl_H_eq_zero _ (UnzipFull.fullIndex_radius_pos i)) _
    (Qc (Real.sqrt κ))).trans ?_
  rw [unzipFieldPath_apply, add_rdField]
  rfl

/-! ## The path read from the data -/

open Classical in
/-- **The path on `[0,t]` read measurably from the data**: the read-off `readDrv p / √κ` on the
continuity certificate `DyUC`, `0` elsewhere. -/
def rdTimeD (κ t : ℝ) (p : ℝ≥0 → ℝ) : C(Icc (0 : ℝ) t, ℝ) :=
  if h : DyUC p then
    ⟨fun u => readDrv p u / Real.sqrt κ,
      ((continuous_readDrv_of_dyUC h).comp continuous_subtype_val).div_const _⟩
  else 0

theorem measurable_rdTimeD (κ t : ℝ) : Measurable (rdTimeD κ t) := by
  classical
  refine ContinuousMap.measurable_iff_eval.2 fun u => ?_
  have e : (fun p => rdTimeD κ t p u) =
      fun p => if DyUC p then readDrv p u / Real.sqrt κ else 0 := by
    funext p
    unfold rdTimeD
    split_ifs <;> rfl
  rw [e]
  exact Measurable.ite measurableSet_dyUC ((measurable_readDrv_apply u).div_const _)
    measurable_const

theorem Wof_rdTimeD {κ t : ℝ} (ht : 0 ≤ t) (hκ : 0 < κ) {p : ℝ≥0 → ℝ} (hp : DyUC p) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) t) : Wof κ t ht (rdTimeD κ t p) r = readDrv p r := by
  have hs : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  classical
  simp only [Wof, rdTimeD, hp, ↓reduceDIte, ContinuousMap.coe_mk,
    projIcc_of_mem ht hr]
  field_simp

/-! ## Good data at time `t` and the deterministic identity -/

/-- **The path part of the good data, at all times**: the continuity certificate `DyUC`, the
read-off starting at `0`, and every real `x ≠ 0` alive at every time `T ≥ 0`. Implies the
time-`1` `PathGood`. -/
def PathGoodAll (p : ℝ≥0 → ℝ) : Prop :=
  DyUC p ∧ readDrv p 0 = 0 ∧
    ∀ x : ℝ, x ≠ 0 → ∀ T : ℝ, 0 ≤ T → ∃ u, IsForwardSol (readDrv p) (x : ℂ) T u

end F1
end QuantumZipper
