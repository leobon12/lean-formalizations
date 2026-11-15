import InteractingSLE.Foundations.Loewner.YuanCorollary13Finite
import InteractingSLE.SLE8.SpaceFilling.ZeroAreaDet
import InteractingSLE.WangWu.CouplingBridge
import QuantumZipper.Proofs.GFF.K3.C5Cov
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Wang–Wu at `κ = 4`: the residual covariance on `ℍ \ η[0,t]` is the retained Green form

Packet PROVE-WW-BRIDGE (ruling R40). The whole-field identification (WF2) of the follow-up note
(`source/external/AstraIG1/ig1_followup_proofs.txt` L1405–1420) states the conditional law of the field as
`M_τ + h⁰_{Ω_τ}`, with `h⁰_{Ω_τ}` a zero-boundary GFF on the possibly disconnected open set `Ω_τ = ℍ \ η[0,τ]`,
extended by zero. Its variance at a test function `φ` is QuantumZipper's `zeroGFFTestCov (ℍ \ η[0,τ]) φ φ` (the dual
Dirichlet norm, which for a disconnected set is the sum over the components). The Wang–Wu document's Definition 1.5
uses instead the retained Green form `Q_{U_τ}(φ, φ) = ∬ φ(a) G_{U_τ}(a,b) φ(b)`, with the kernel frozen at the first
swallowing of either argument (`retainedGreen`, QuantumZipper's `V_T`).

This file proves that the two agree for every continuous generating trace whose range has zero area
(`zeroGFFTestCov_compl_image_eq_retainedGreenEnergy`): this is QuantumZipper's deterministic node C5
(`K3.zeroGFFTestCov_compl_image_eq`, Sheffield arXiv:1012.4797, Theorem 1.1 addendum) applied to the driver frozen
after a time `T' ∈ (t, T)` and the trace continued by the image of a vertical slit (`YuanCorollary13.extDrive`,
`extTrace`, packet PROVE-YUAN-M1). The only new step is that a continuous Loewner trace on `[0, ∞)` satisfies
QuantumZipper's hull interface `K3.GenTrace` (`IsLoewnerTrace.genTrace`).

## Main results

* `IsLoewnerTrace.genTrace`: a continuous Loewner trace of a continuous driver is a `K3.GenTrace`.
* `IsGeneratingTrace.exists_genTrace`: the frozen generating trace before `T`, continued after `T' ∈ (t, T)`, is a
  `K3.GenTrace` of a continuous driver agreeing with `w` on `[0, T']`, with the same range on `[0, t]`.
* `zeroGFFTestCov_compl_image_eq_retainedGreenEnergy`: `zeroGFFTestCov (ℍ \ η[0,t]) φ φ = Q_{U_t}(φ, φ)` when
  `η[0,t] ∩ ℍ` has zero area.
* `volume_eq_zero_of_dimH_lt_two`: a subset of `ℂ` of Hausdorff dimension `< 2` has zero area.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric Complex QuantumZipper
open scoped NNReal ENNReal

namespace InteractingSLE

/-! ### Continuous Loewner traces satisfy QuantumZipper's hull interface -/

/-- `0` is in the closure of `ℍ`. -/
theorem zero_mem_closure_H : (0 : ℂ) ∈ closure H := by
  rw [closure_H]
  exact mem_Hbar_of_im_eq_zero (by simp)

/-- **A continuous Loewner trace of a continuous driver is a `K3.GenTrace`**: the complement of `K_t` in `ℍ` is the
component of `M i` in `ℍ \ η[0,t]` as soon as `|η| < M` on `[0, t]` (`H_diff_fillH`), and the tip `η(s)` is the limit
of `F_s(w) ∈ ℍ \ K_s` as `w → 0` (`IsLoewnerTrace.tendsto_fwdMapInv_tip`). -/
theorem IsLoewnerTrace.genTrace {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) : K3.GenTrace W η where
  contW := hW
  zeroW := hW0
  zero := hη.1
  cont := hη.2.1
  gen := fun t ht M hM => by
    have hA : IsCompact (η '' Icc 0 t) :=
      isCompact_Icc.image_of_continuousOn (hη.2.1.mono Icc_subset_Ici_self)
    have hM0 : 0 < M := by
      have := hM 0 ⟨le_rfl, ht⟩
      rwa [hη.1, norm_zero] at this
    have hAR : η '' Icc 0 t ⊆ ball 0 M := by
      rintro _ ⟨s, hs, rfl⟩
      exact mem_ball_zero_iff.2 (hM s hs)
    have hAR' : closure (η '' Icc 0 t) ⊆ ball 0 M := by rwa [hA.isClosed.closure_eq]
    rw [hη.2.2 t ht, H_diff_fillH hM0 hAR', hA.isClosed.closure_eq]
    have hmem : (M : ℂ) * I ∈ connectedComponentIn (H \ η '' Icc 0 t) (((M + 1 : ℝ) : ℂ) * I) := by
      refine mem_connectedComponentIn_of_le_norm hM0 hAR ?_ ?_
      · show 0 < ((M : ℂ) * I).im
        simpa using hM0
      · rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM0]
    exact connectedComponentIn_eq hmem
  tip := fun s hs => by
    have hlim := hη.tendsto_fwdMapInv_tip hW hW0 hs
    have : (𝓝[H] (0 : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 zero_mem_closure_H
    refine mem_closure_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 hs hw

/-! ### The frozen generating trace, continued -/

section Frozen

variable {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- **The frozen generating trace before `T`, continued, is a `K3.GenTrace`.** For `t < T` there are `T' > t` and a
continuous driver `W'` agreeing with `w` on `[0, T']` (the driver frozen after a time in `(T', T)`, then frozen again
after `T'`), with a `K3.GenTrace` `η'` (the trace continued after `T'` by the image of the vertical slit) having the
same range as `η` on `[0, t]`. -/
theorem IsGeneratingTrace.exists_genTrace (hη : IsGeneratingTrace w T η)
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) :
    ∃ (W' : ℝ → ℝ) (η' : ℝ → ℂ) (T' : ℝ), (t : ℝ) < T' ∧ K3.GenTrace W' η' ∧
      EqOn (Ito.rpath w) W' (Icc 0 T') ∧ η' '' Icc 0 (t : ℝ) = η '' Icc 0 t := by
  obtain ⟨t₂, htt₂, ht₂T⟩ := exists_real_btwn_of_lt ht
  have ht₂ : 0 ≤ t₂ := (NNReal.coe_nonneg t).trans htt₂.le
  set T' : ℝ := ((t : ℝ) + t₂) / 2 with hT'def
  have htT' : (t : ℝ) < T' := by rw [hT'def]; linarith
  have hT't₂ : T' < t₂ := by rw [hT'def]; linarith
  have hT'0 : 0 ≤ T' := (NNReal.coe_nonneg t).trans htT'.le
  have hW₀c : Continuous (frozenDrive w t₂) := continuous_frozenDrive_of_lt hw ht₂T
  have hW₀0 : frozenDrive w t₂ 0 = 0 := by rw [frozenDrive_zero ht₂, hw0]
  have hL := (hη.isLoewnerTraceLT ht₂T).isLoewnerTrace_ext hW₀c hW₀0 hT'0 hT't₂
  refine ⟨YuanCorollary13.extDrive (frozenDrive w t₂) T',
    YuanCorollary13.extTrace (frozenDrive w t₂) (fun s : ℝ => η s.toNNReal) T', T', htT',
    hL.genTrace (YuanCorollary13.continuous_extDrive hW₀c)
      (YuanCorollary13.extDrive_zero hW₀0 hT'0), ?_, ?_⟩
  · intro r hr
    rw [YuanCorollary13.extDrive_eq hr.2, frozenDrive_eq ⟨hr.1, hr.2.trans hT't₂.le⟩]
    rfl
  · have himg : YuanCorollary13.extTrace (frozenDrive w t₂) (fun s : ℝ => η s.toNNReal) T' '' Icc 0 (t : ℝ) =
        (fun s : ℝ => η s.toNNReal) '' Icc 0 (t : ℝ) :=
      image_congr fun s hs => YuanCorollary13.extTrace_eq (hs.2.trans htT'.le)
    rw [himg, image_toNNReal_Icc η (NNReal.coe_nonneg t), Real.toNNReal_coe]

/-- **The residual covariance on `ℍ \ η[0,t]` is the retained Green form.** For a continuous generating trace `η`
before `T` of a driver continuous before `T` with `w 0 = 0`, a time `t < T` with `η[0,t] ∩ ℍ` of zero area, and a test
function `φ` on `ℍ`: `zeroGFFTestCov (ℍ \ η[0,t]) φ φ = Q_{U_t}(φ, φ)`. -/
theorem zeroGFFTestCov_compl_image_eq_retainedGreenEnergy (hη : IsGeneratingTrace w T η)
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T)
    (harea : volume (η '' Icc 0 t ∩ H) = 0) (φ : LQGMetric.TestOn upperHalfPlaneOpens) :
    zeroGFFTestCov (H \ η '' Icc 0 t) φ φ = WangWu.retainedGreenEnergy w t φ := by
  obtain ⟨W', η', T', htT', hg, heq, himg⟩ := hη.exists_genTrace hw hw0 ht
  let ρ : TestFun H := ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset⟩
  have harea' : volume (η' '' Icc 0 (t : ℝ) ∩ H) = 0 := by rwa [himg]
  have hC5 := K3.zeroGFFTestCov_compl_image_eq hg (NNReal.coe_nonneg t) harea' ρ ρ
  rw [himg] at hC5
  rw [hC5, WangWu.retainedGreenEnergy]
  have hcont : ContinuousOn (Ito.rpath w) (Icc 0 T') := hg.contW.continuousOn.congr heq
  have hφH : ∀ z, φ z ≠ 0 → 0 < z.im := fun z hz =>
    φ.tsupport_subset (subset_tsupport φ (Function.mem_support.2 hz))
  refine congrArg _ (funext fun a => congrArg _ (funext fun b => ?_))
  show φ a * φ b * K3.VT W' t a b = φ a * WangWu.retainedGreen w t a b * φ b
  by_cases ha : φ a = 0
  · simp [ha]
  by_cases hb : φ b = 0
  · simp [hb]
  have hV : K3.VTe (Ito.rpath w) t a b = K3.VTe W' t a b :=
    WangWu.VTe_eq_of_eqOn htT' hcont hg.contW.continuousOn heq (hφH a ha) (hφH b hb)
  rw [WangWu.retainedGreen, K3.VT, K3.VT, hV]
  ring

end Frozen

/-! ### Zero area from Hausdorff dimension -/

/-- A subset of `ℂ` of Hausdorff dimension `< 2` has zero area. -/
theorem volume_eq_zero_of_dimH_lt_two {s : Set ℂ} (hs : dimH s < 2) : volume s = 0 := by
  have h2 : dimH s < ((2 : ℝ≥0) : ℝ≥0∞) := by simpa using hs
  exact SLE8.SpaceFilling.volume_eq_zero_of_hausdorffMeasure_eq_zero (d := 2) le_rfl
    (by simpa using hausdorffMeasure_of_dimH_lt h2)

end InteractingSLE
