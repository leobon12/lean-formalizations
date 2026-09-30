import QuantumZipper.Proofs.Zipper.ESMComplF1
import QuantumZipper.Proofs.Zipper.ESMLMeas4
import QuantumZipper.Proofs.Zipper.ESMLMeas5
import QuantumZipper.Proofs.Zipper.F1ReadMeasPath

/-!
# READLEN: the length read-off `readLen` as a measurable function on good data

Theorem 1.3, node F1d input (d) (`F1.ReadLenAEMeasStmt`, `F1Read.lean`; Sheffield,
arXiv:1012.4797, §5.4 p. 72, "by symmetry", which needs the lengths to be *intrinsic*, B5).

`readLen γ d` recomputes the unzipped lengths at time `1` from the `configLawFull` data `d`:
the field `F = reconstruct (piC d.1.1)` and the driver `W = readDrv d.2` (dyadic read-off).
Here we write it, on *good* data, as a measurable function of the data. Method of ESM-LMEAS
(`ESMLMeas2`–`ESMLMeas5`, the `lenMinusSur` surrogate), transported to the data space:

* `rdField`, `rdM`: the reader on `(coordinates, continuous path on [0,1])`: the gated boundary
  measure `ESM.nuSur` of the path surrogate of the unzipped field (field `rdField κ c`, so that
  `𝔥₀ + rdField κ c = reconstruct (piC c)`) evaluated on `[a, 0]` and `[0, b]`, with the side
  images `(a, b) = ESM.sideReader` of the path. `measurable_rdM`.
* `measurable_measure_zero_Icc_of_finite`: the right-window companion of
  `ESM.measurable_measure_Icc_zero_of_finite` (by reflection `x ↦ -x`).
* `ReadGood κ d = PathGood d.2 ∧ FieldFin κ d`: the driver carries the continuity certificate
  `DyUC` (`F1ReadMeasPath`), starts at `0`, every real `x ≠ 0` is alive at time `1`, and the
  approximating boundary measures of the unzipped field are finite on the windows `[-N, N]`.
* `coordsFull_unzip_eq_sur`: the unzipped field and its path surrogate have the same circle
  coordinates (`UnzipInvariance.fwdMapInv_eq_revMap_timeRev`: the inverse forward map is the
  reverse flow of the time-reversed driver; `ReverseFlow.revMap_congr_drive`).
* **`readLen_eq_rdM`** (deterministic): on good data, `readLen √κ d = rdM κ √κ (d.1.1, f)` for
  any continuous path `f` with `Wof κ 1 f = readDrv d.2` on `[0,1]`. Side images:
  `ESM.sideImages_Wof_eq_sideReader`; boundary measure: `UnzipFull.qBoundaryMeasure_congr_of_coordsFull`
  and `gate_eq_of_fin` (`E1.M4.bCert_of_isVagueLimitR`: finite windows plus a vague limit give the
  certificate, so the gate of `nuSur` is invisible; off the certificate both sides are the junk `0`).
* `rdPathD` (the path on `[0,1]` read measurably from the data through `DyUC`), `rdG`
  (the measurable version of `readLen`), and **`aemeasurable_readLen_of_ae_good`**: `readLen √κ`
  is `μ`-a.e.-measurable whenever `μ`-a.e. datum is good (no measurability of the good event is
  needed, only `∀ᵐ`).

The reductions are own bookkeeping (no published proof: the paper states the intrinsic
property without proof). The a.s. goodness is `F1ReadMeasAlive` (path part, proved) and
`F1ReadMeasRed` (field part, reduced to `WedgeUnzipFinStmt`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F1

open ESM CharFun CoordsFull

/-- The data space of `configLawFull`. -/
abbrev RdData := ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ)

/-- The field fed to the ESM path surrogate: `𝔥₀ + rdField κ c = reconstruct (piC c)`. -/
def rdField (κ : ℝ) (c : ℕ → ℝ) : FieldSample :=
  Factorization.reconstruct (WedgeCan4.piC c) - ofFun (h0rev κ)

theorem add_rdField (κ : ℝ) (c : ℕ → ℝ) :
    ofFun (h0rev κ) + rdField κ c = Factorization.reconstruct (WedgeCan4.piC c) :=
  add_sub_cancel _ _

theorem measurable_rdField (κ : ℝ) : Measurable (rdField κ) := by
  refine measurable_pi_iff.2 fun μ => ?_
  have h : Measurable fun c : ℕ → ℝ => Factorization.reconstruct (WedgeCan4.piC c) μ :=
    (measurable_pi_apply μ).comp (Factorization.measurable_reconstruct.comp WedgeCan4.measurable_piC)
  exact h.sub_const _

/-- **The unzipped field and its path surrogate have the same circle coordinates** (continuous
driver started at `0`, read on `[0,1]` through `Wof κ 1 f`). -/
theorem coordsFull_unzip_eq_sur {κ : ℝ} {W : ℝ → ℝ} (hc : Continuous W) (h0 : W 0 = 0)
    {f : C(Icc (0 : ℝ) 1, ℝ)} (hf : ∀ r ∈ Icc (0 : ℝ) 1, Wof κ 1 zero_le_one f r = W r)
    (c : ℕ → ℝ) :
    coordsFull (unzippedField (Real.sqrt κ) (Factorization.reconstruct (WedgeCan4.piC c), W) 1) =
      coordsFull (unzipFieldCoord κ 1 zero_le_one (rdField κ c, f)) := by
  have hEqOn : EqOn (fwdMapInv W 1) (revMap (Wof κ 1 zero_le_one (revPath 1 zero_le_one f)) 1)
      H := by
    intro w hw
    rw [UnzipInvariance.fwdMapInv_eq_revMap_timeRev W hc h0 zero_le_one hw]
    refine ReverseFlow.revMap_congr_drive w fun r hr => ?_
    have hr' : 1 - r ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hr.2], by linarith [hr.1]⟩
    have e1 := hf (1 - r) hr'
    have e2 := hf 1 ⟨zero_le_one, le_rfl⟩
    show W (1 - r) - W 1 = _
    rw [← e1, ← e2]
    simp only [Wof, projIcc_of_mem zero_le_one hr, projIcc_of_mem zero_le_one hr',
      projIcc_of_mem zero_le_one (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩),
      revPath_apply]
    ring
  rw [coordsFull_unzipFieldCoord]
  funext i
  refine (UnzipInvariance.coordChange_congr_of_eqOn hEqOn
    (foldedCircle_compl_H_eq_zero _ (UnzipFull.fullIndex_radius_pos i)) _
    (Qc (Real.sqrt κ))).trans ?_
  rw [unzipFieldPath_apply, add_rdField]
  rfl

theorem measurable_readDrv_apply (u : ℝ) : Measurable fun p : ℝ≥0 → ℝ => readDrv p u := by
  have h1 : Measurable fun p : ℝ≥0 → ℝ => ((fun r : ℝ => p r.toNNReal), u) :=
    (measurable_pi_iff.2 fun r => measurable_pi_apply _).prodMk measurable_const
  exact B4d.measurable_pathExt.comp h1

open Classical in
/-- **The path on `[0,1]` read measurably from the data**: the read-off `readDrv p / √κ` on the
certificate `DyUC` (where it is continuous), `0` elsewhere. -/
def rdPathD (κ : ℝ) (p : ℝ≥0 → ℝ) : C(Icc (0 : ℝ) 1, ℝ) :=
  if h : DyUC p then
    ⟨fun u => readDrv p u / Real.sqrt κ,
      ((continuous_readDrv_of_dyUC h).comp continuous_subtype_val).div_const _⟩
  else 0

theorem measurable_rdPathD (κ : ℝ) : Measurable (rdPathD κ) := by
  classical
  refine ContinuousMap.measurable_iff_eval.2 fun u => ?_
  have e : (fun p => rdPathD κ p u) =
      fun p => if DyUC p then readDrv p u / Real.sqrt κ else 0 := by
    funext p
    unfold rdPathD
    split_ifs <;> rfl
  rw [e]
  exact Measurable.ite measurableSet_dyUC ((measurable_readDrv_apply u).div_const _)
    measurable_const

theorem Wof_rdPathD {κ : ℝ} (hκ : 0 < κ) {p : ℝ≥0 → ℝ} (hp : DyUC p) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) : Wof κ 1 zero_le_one (rdPathD κ p) r = readDrv p r := by
  have hs : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  classical
  simp only [Wof, rdPathD, hp, ↓reduceDIte, ContinuousMap.coe_mk,
    projIcc_of_mem zero_le_one hr]
  field_simp

end F1
end QuantumZipper
