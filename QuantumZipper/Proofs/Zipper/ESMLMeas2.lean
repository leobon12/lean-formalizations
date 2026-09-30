import QuantumZipper.Proofs.Zipper.ESMLMeas
import QuantumZipper.Proofs.Zipper.B1Full
import QuantumZipper.Proofs.Thm12.CharFun
import QuantumZipper.Proofs.Zipper.E1TransferM4Cert

/-!
# ESM-LMEAS-2: the path surrogate of `L⁻_s` and the a.e. identity

Continuation of `ESMLMeas.lean` (node **E-SM**, obligation `hLad` of
`ESM.lintegral_levelTime_strongMarkov_lenA`, decision D21). `ESMLMeas` proves that
`L⁻_s = lenMinus κ B X s` is computed from `(X ω, clampB s B ω)` only
(`ae_lenMinus_eq_clamp`). Here the same value is written as a deterministic functional of the
pair `(x, f)` — a field and a *continuous* path `f : C(I[0,s], ℝ)` — evaluated at
`(X ω, pathC s B ω)`, which is the mathematical content of "unzipping by time `s` uses only the
data up to time `s`" (Sheffield, arXiv:1012.4797, §5.2 and the proof of Lemma 5.6).

* `revPath`, `unzipFieldPath`: the field part `coordChange (𝔥₀ + x) (fwdMapInv W s) Q` written
  through the path as `coordChange (𝔥₀ + x) (revMap (Wof κ s hs (revPath f)) s) Q`.
* `ae_coordsFull_unzipFieldPath`: **the circle coordinates of the two fields agree a.s.** — a
  pointwise consequence of `UnzipInvariance.fwdMapInv_eq_revMap_timeRev` (the inverse forward map
  at time `s` is the reverse flow of the time-reversed driver) and `revMap_congr_drive` (the
  reverse flow reads the driver only on `[0,s]`).
* `fromCoords`, `unzipFieldCoord`, `nuSur`, `lenMinusSur`: the coordinate reconstruction of the
  surrogate field (a `FieldSample`), the `BCert`-gated boundary measure of the unzipped field,
  and the resulting functional for `L⁻_s`.
* `ae_lenMinus_eq_surrogate`: `L⁻_s = lenMinusSur (X, pathC s B)` a.s., from the field identity
  (proved here), the side images `hside` and the boundary certificate `hgood`.
* `measurable_lenMinus_of_surrogate`: `hLad` for any σ-algebra making `(X, pathC s B)`
  measurable and containing the `P`-null sets, from measurability of `lenMinusSur`.

The *measurability* of `lenMinusSur` (the analytic part of `hLad`) is not proved here: it
combines `B1Full.measurable_unzip_apply` (measurability of the path surrogate field at measures
vanishing off `ℍ`), `E1.M4.measurable_qBoundaryMeasure_bCert` (Giry measurability of the gated
boundary measure of a coordinate-rebuilt field) and the measurability of
`(ν, a) ↦ ν (Icc a 0)` for a measurable measure family `ν` (a general measure-theoretic fact,
provable from `Measure.measurable_coe` on the fixed sets `Ici q`, `q ∈ ℚ`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace ESM

open F1 CoordsFull CharFun

/-- The time-reversed path `u ↦ f (s − u) − f s` on `[0,s]`: the driver whose reverse flow
inverts the forward flow driven by `f` at time `s`
(`UnzipInvariance.fwdMapInv_eq_revMap_timeRev`). -/
def revPath (s : ℝ) (hs : 0 ≤ s) (f : C(Icc (0 : ℝ) s, ℝ)) : C(Icc (0 : ℝ) s, ℝ) where
  toFun u := f ⟨s - u.1, ⟨sub_nonneg.2 u.2.2, sub_le_self s u.2.1⟩⟩ - f ⟨s, ⟨hs, le_rfl⟩⟩
  continuous_toFun := by fun_prop

@[simp] theorem revPath_apply (s : ℝ) (hs : 0 ≤ s) (f : C(Icc (0 : ℝ) s, ℝ))
    (u : Icc (0 : ℝ) s) :
    revPath s hs f u = f ⟨s - u.1, ⟨sub_nonneg.2 u.2.2, sub_le_self s u.2.1⟩⟩ -
      f ⟨s, ⟨hs, le_rfl⟩⟩ := rfl

/-- **The unzipped field at time `s` through a continuous path.** -/
def unzipFieldPath (κ s : ℝ) (hs : 0 ≤ s) (p : FieldSample × C(Icc (0 : ℝ) s, ℝ)) :
    FieldSample :=
  coordChange (ofFun (h0rev κ) + p.1) (revMap (Wof κ s hs (revPath s hs p.2)) s)
    (Qc (Real.sqrt κ))

theorem unzipFieldPath_apply (κ s : ℝ) (hs : 0 ≤ s) (x : FieldSample)
    (f : C(Icc (0 : ℝ) s, ℝ)) :
    unzipFieldPath κ s hs (x, f) =
      coordChange (ofFun (h0rev κ) + x) (revMap (Wof κ s hs (revPath s hs f)) s)
        (Qc (Real.sqrt κ)) := rfl

variable {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-! ## The field part of the a.e. identity

The remaining statements (`ae_lenMinus_eq_surrogate`, `measurable_lenMinus_of_surrogate`,
`revPath_drive_eqOn`) are recorded in the ESM-LMEAS report; only fully proved material is kept
here. -/

/-- **The circle coordinates of the unzipped field and of its path–surrogate agree a.s.** The
inverse forward map at time `s` is the reverse flow of the time-reversed driver
(`UnzipInvariance.fwdMapInv_eq_revMap_timeRev`), the reverse flow reads the driver only through
its values on `[0,s]` (`ReverseFlow.revMap_congr_drive`), and the time-reversed driver of
`drive κ (clampB s B) ω` is `Wof κ s hs (revPath s hs (pathC s B ω))` on `[0,s]`. -/
theorem ae_coordsFull_unzipFieldPath {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous fun u : ℝ≥0 => B u ω) {κ : ℝ}
    {s : ℝ} (hs : 0 ≤ s) :
    ∀ᵐ ω ∂P, coordsFull (coordChange (ofFun (h0rev κ) + X ω)
        (fwdMapInv (drive κ (clampB s.toNNReal B) ω) s) (Qc (Real.sqrt κ))) =
      coordsFull (unzipFieldPath κ s hs (X ω, pathC s B hBc ω)) := by
  filter_upwards [hB.eval_zero_ae_eq_zero] with ω h0
  have hc : Continuous (drive κ (clampB s.toNNReal B) ω) :=
    drive_continuous (continuous_clampB hBc s.toNNReal ω)
  have hdrive : ∀ u : ℝ, u ≤ s → drive κ (clampB s.toNNReal B) ω u = drive κ B ω u := by
    intro u hu
    have hle : u.toNNReal ≤ s.toNNReal := Real.toNNReal_mono hu
    simp only [drive, clampB_apply, min_eq_left hle]
  have hEqOn : EqOn (fwdMapInv (drive κ (clampB s.toNNReal B) ω) s)
      (revMap (Wof κ s hs (revPath s hs (pathC s B hBc ω))) s) H := by
    intro w hw
    rw [UnzipInvariance.fwdMapInv_eq_revMap_timeRev _ hc (by rw [hdrive 0 hs, drive_zero h0])
      hs hw]
    refine ReverseFlow.revMap_congr_drive w fun r hr => ?_
    have h4 : projIcc (0 : ℝ) s hs r = ⟨r, hr⟩ := projIcc_of_mem hs hr
    simp only [Wof, h4, revPath_apply, pathC]
    rw [hdrive (s - r) (sub_le_self s hr.1), hdrive s le_rfl]
    simp only [drive, ContinuousMap.coe_mk]
    ring
  funext i
  refine (UnzipInvariance.coordChange_congr_of_eqOn hEqOn
    (foldedCircle_compl_H_eq_zero _ (UnzipFull.fullIndex_radius_pos i))
    (ofFun (h0rev κ) + X ω) (Qc (Real.sqrt κ))).trans ?_
  rw [unzipFieldPath_apply]
  rfl

end ESM
end QuantumZipper
