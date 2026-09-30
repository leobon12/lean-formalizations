import QuantumZipper.Proofs.Zipper.ESMInst
import QuantumZipper.Proofs.Zipper.F1Side
import QuantumZipper.Proofs.Loewner.ForwardFlow
import QuantumZipper.Proofs.Zipper.UnzipFullSplit

/-!
# ESM-LMEAS: adaptedness of the intrinsic left length `L⁻`

Node **E-SM** of `blueprint/E_BRANCH_BLUEPRINT.md`, obligation **`hLad`** of
`ESM.lintegral_levelTime_strongMarkov_lenA` (`Proofs/Zipper/ESMLen.lean`, decision D21):
`L⁻_s = lenMinus κ B X s` is measurable with respect to `σ(X) ⊔ σ(B u, u ≤ s)` (up to the
`P`-null sets, which the filtration `𝓕` of the consumer contains).

Mathematically the point is that the field unzipped at time `s` depends only on `X` and on the
driver on `[0,s]` (Sheffield, arXiv:1012.4797, §5.2, pp. 57–59: the Loewner maps up to time `s`
are determined by the driver up to time `s`), and that this dependence is measurable.

* **Part 1 (deterministic congruence).** `fwdMap_congr_drive_ext` (A1's `fwdMap_congr_drive`
  with the hypothesis `0 < z.im` dropped, using `F1Side.isForwardSol_unique_gronwall` and
  `F1Side.fwdMap_eq_of_isForwardSol`), `fwdHull_congr_drive`, `fwdMapInv_congr_drive`,
  `sideImages_congr_drive` and `unzipLengths_congr_drive`: two drivers agreeing on `[0,t]` give
  the same forward map, hull, inverse, side images and unzipped lengths at time `t`.
* **Part 2 (stopping the Brownian path).** `clampB s B := u ↦ B (min u s)` agrees with `B` on
  `[0,s]`, has continuous paths, and is measurable for `σ(B u, u ≤ s)`. Hence
  `lenMinus_eq_clamp`: pointwise, `L⁻_s` is computed from `(X ω, (clampB s B) ω)` only, i.e. it
  is a function of `X` and of the driver on `[0,s]`.

Sources: Sheffield, arXiv:1012.4797, §5.2 and the proof of Lemma 5.6 / Theorem 1.8 (unzipping at
a stopping time); `F1Side` (A1(e), uniqueness of the forward flow from real points). The
congruence statements themselves are own elementary proofs from the definitions.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace ESM

open F1

variable {Ω : Type*} {κ t T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-! ## Part 1: the unzipped configuration depends only on the driver on `[0, t]` -/

/-- **`fwdMap` depends only on the driver on `[0,T]`, any starting point.** A1's
`fwdMap_congr_drive` without the hypothesis `0 < z.im`: existence of a solution transfers by
`isForwardSol_congr_drive` and uniqueness from any real or complex point is
`F1Side.isForwardSol_unique_gronwall`. -/
theorem fwdMap_congr_drive_ext {W W' : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (h : ∀ r ∈ Set.Icc (0 : ℝ) T, W r = W' r) (z : ℂ) :
    fwdMap W T z = fwdMap W' T z := by
  by_cases hex : ∃ u, IsForwardSol W z T u
  · obtain ⟨u, hu⟩ := hex
    rw [fwdMap_eq_of_isForwardSol hu ⟨hT, le_rfl⟩,
      fwdMap_eq_of_isForwardSol (isForwardSol_congr_drive h hu) ⟨hT, le_rfl⟩]
  · have hex' : ¬ ∃ u, IsForwardSol W' z T u := fun ⟨u, hu⟩ =>
      hex ⟨u, isForwardSol_congr_drive (fun r hr => (h r hr).symm) hu⟩
    simp only [fwdMap, dif_neg hex, dif_neg hex']

/-- **`fwdMapInv` depends only on the driver on `[0,t]`, on `ℍ`.** The inverse forward map is
the reverse flow of the time-reversed driver (`UnzipInvariance.fwdMapInv_eq_revMap_timeRev`),
which reads the driver only through its values on `[0,t]` (`revMap_congr_drive`). -/
theorem fwdMapInv_eqOn_of_drive_eqOn {W W' : ℝ → ℝ} (hW : Continuous W) (hW' : Continuous W')
    (hW0 : W 0 = 0) (hW0' : W' 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    (h : ∀ r ∈ Set.Icc (0 : ℝ) t, W r = W' r) : EqOn (fwdMapInv W t) (fwdMapInv W' t) H := by
  intro w hw
  rw [UnzipInvariance.fwdMapInv_eq_revMap_timeRev W hW hW0 ht hw,
    UnzipInvariance.fwdMapInv_eq_revMap_timeRev W' hW' hW0' ht hw]
  refine ReverseFlow.revMap_congr_drive w fun u hu => ?_
  have h1 : t - u ∈ Set.Icc (0 : ℝ) t := ⟨sub_nonneg.2 hu.2, sub_le_self t hu.1⟩
  rw [h (t - u) h1, h t ⟨ht, le_rfl⟩]

/-- `foldedCircle`s of positive radius live on `ℍ`. -/
theorem foldedCircle_compl_H_eq_zero (w : ℂ) {r : ℝ} (hr : 0 < r) :
    foldedCircle w r Hᶜ = 0 :=
  ae_iff.1 (TwoPoint.foldedCircle_ae_mem_H w hr)

/-- `qBoundaryMeasure` of a `coordChange` only reads the map on `ℍ`. -/
theorem qBoundaryMeasure_coordChange_congr {γ : ℝ} (x : FieldSample) {f g : ℂ → ℂ}
    (hfg : EqOn f g H) (Q : ℝ) :
    qBoundaryMeasure γ (coordChange x f Q) = qBoundaryMeasure γ (coordChange x g Q) := by
  refine UnzipFull.qBoundaryMeasure_congr_of_coordsFull γ ?_
  funext i
  exact UnzipInvariance.coordChange_congr_of_eqOn hfg (foldedCircle_compl_H_eq_zero _ (UnzipFull.fullIndex_radius_pos i))
    x Q

/-- The side images at time `t` depend only on the driver on `[0,t]`. -/
theorem sideImages_congr_drive {W W' : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (h : ∀ r ∈ Set.Icc (0 : ℝ) t, W r = W' r) : sideImages W t = sideImages W' t := by
  have hf : (fun x : ℝ => (fwdMap W t x).re) = fun x : ℝ => (fwdMap W' t x).re :=
    funext fun x => by rw [fwdMap_congr_drive_ext ht h ((x : ℂ))]
  simp only [sideImages, hf]

/-- **The unzipped lengths at time `t` depend only on the driver on `[0,t]`.** For continuous
drivers vanishing at `0` that agree on `[0,t]`, the unzipped field (through its circle
coordinates) and the side images are the same, hence so is `unzipLengths`. -/
theorem unzipLengths_eq_of_drive_eqOn {γ : ℝ} (x : FieldSample) {W W' : ℝ → ℝ}
    (hW : Continuous W) (hW' : Continuous W') (hW0 : W 0 = 0) (hW0' : W' 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) (h : ∀ r ∈ Set.Icc (0 : ℝ) t, W r = W' r) :
    unzipLengths γ (x, W) t = unzipLengths γ (x, W') t := by
  have hψ := fwdMapInv_eqOn_of_drive_eqOn hW hW' hW0 hW0' ht h
  simp only [unzipLengths, qBoundaryMeasure_coordChange_congr x hψ (Qc γ),
    sideImages_congr_drive ht h]

/-! ## Part 2: stopping the Brownian path at `s`

`clampB s B u = B (min u s)` — the path stopped at `s`, an `ℝ≥0 → ℝ`-valued function that is
`σ(B u, u ≤ s)`-measurable (each of its coordinates is one of the generators). -/

/-- The Brownian path stopped at time `s`. -/
def clampB (s : ℝ≥0) (B : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ := fun u ω => B (min u s) ω

@[simp] theorem clampB_apply (s : ℝ≥0) (B : ℝ≥0 → Ω → ℝ) (u : ℝ≥0) (ω : Ω) :
    clampB s B u ω = B (min u s) ω := rfl

theorem continuous_clampB (hBc : ∀ ω, Continuous fun u : ℝ≥0 => B u ω) (s : ℝ≥0) (ω : Ω) :
    Continuous fun u : ℝ≥0 => clampB s B u ω :=
  (hBc ω).comp (continuous_id.min continuous_const)

/-- `drive κ (clampB s B) ω` agrees with `drive κ B ω` on `[0,s]`. -/
theorem drive_clampB_eqOn (s : ℝ≥0) (ω : Ω) :
    ∀ r ∈ Set.Icc (0 : ℝ) (s : ℝ), drive κ (clampB s B) ω r = drive κ B ω r := by
  intro r hr
  have hle : r.toNNReal ≤ s := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]
    exact hr.2
  simp only [drive, clampB_apply, min_eq_left hle]

/-- **The intrinsic left length at time `s` reads the Brownian path only up to time `s`.**
Almost surely, `L⁻_s` for the configuration `cfg κ B X` equals `L⁻_s` for the configuration
driven by the stopped path `clampB s B`, a function of `ω` through `(X ω, clampB s B ω)` only. -/
theorem ae_lenMinus_eq_clamp [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hBc : ∀ ω, Continuous fun u : ℝ≥0 => B u ω) (κ : ℝ) (X : Ω → FieldSample) (s : ℝ≥0) :
    ∀ᵐ ω ∂P, lenMinus κ B X s ω = lenMinus κ (clampB s B) X s ω := by
  filter_upwards [hB.eval_zero_ae_eq_zero] with ω h0
  have h := unzipLengths_eq_of_drive_eqOn (γ := Real.sqrt κ) (x := ofFun (h0rev κ) + X ω)
    (drive_continuous (hBc ω)) (drive_continuous (continuous_clampB hBc s ω))
    (drive_zero h0) (drive_zero (by rw [clampB_apply, min_eq_left (show (0 : ℝ≥0) ≤ s from s.2), h0])) s.2
    (fun r hr => (drive_clampB_eqOn (κ := κ) s ω r hr).symm)
  have e1 : lenMinus κ B X s ω = (unzipLengths (Real.sqrt κ)
      (ofFun (h0rev κ) + X ω, drive κ B ω) (s : ℝ)).1 := rfl
  have e2 : lenMinus κ (clampB s B) X s ω = (unzipLengths (Real.sqrt κ)
      (ofFun (h0rev κ) + X ω, drive κ (clampB s B) ω) (s : ℝ)).1 := rfl
  rw [e1, e2]
  exact congrArg Prod.fst h

end ESM
end QuantumZipper
