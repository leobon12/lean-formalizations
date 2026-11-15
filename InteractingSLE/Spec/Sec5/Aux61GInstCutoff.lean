/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61CovCut

/-! # One even bump for every harmonic correction in a fixed window -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal ComplexConjugate Laplacian
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Aux61GInst
open Aux61Cov
open Restart.FlowStopIdentCMI (CMCut exists_smooth_cutoff mem_thickening_conj)
open Aux61Win (IsCutoffOn)

/-- A deterministic even bump, chosen from the buffer and boundary window. -/
structure ReflectionCutoff (O : Set ℝ) (K : Set ℂ) where
  bump : ℂ → ℝ
  neighbourhood : Set ℂ
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) bump
  compact : HasCompactSupport bump
  even : ∀ z, bump (conj z) = bump z
  support : tsupport bump ⊆ reflDom O
  open_neighbourhood : IsOpen neighbourhood
  buffer_sub : K ⊆ neighbourhood
  neighbourhood_sub : neighbourhood ⊆ reflDom O
  one : ∀ z ∈ neighbourhood, bump z = 1

/-- The geometric part of `exists_cmCut_of_harmonic`, before choosing `q`. -/
theorem exists_reflectionCutoff {O : Set ℝ} (hO : IsOpen O)
    {K : Set ℂ} (hK : IsCompact K) (hKO : ∀ z ∈ K, z.im = 0 → z.re ∈ O) :
    Nonempty (ReflectionCutoff O K) := by
  classical
  set K' : Set ℂ := K ∪ (fun z => conj z) '' K with hK'
  have hK'c : IsCompact K' := hK.union (hK.image Complex.continuous_conj)
  have hK'conj : ∀ z ∈ K', conj z ∈ K' := by
    rintro z (hz | ⟨w, hw, rfl⟩)
    · exact Or.inr ⟨z, hz, rfl⟩
    · rw [Complex.conj_conj]; exact Or.inl hw
  have hK'O : ∀ z ∈ K', z.im = 0 → z.re ∈ O := by
    rintro z (hz | ⟨w, hw, rfl⟩) h0
    · exact hKO z hz h0
    · rw [Complex.conj_re]
      rw [Complex.conj_im, neg_eq_zero] at h0
      exact hKO w hw h0
  set U' : Set ℂ := reflDom O with hU'def
  have hU'o : IsOpen U' := isOpen_reflDom hO
  have hK'U' : K' ⊆ U' := fun z hz hz' => hz'.2 (hK'O z hz hz'.1)
  obtain ⟨δ, hδ, hδU'⟩ := hK'c.exists_cthickening_subset_open hU'o hK'U'
  have hδ2 : 0 < δ / 2 := half_pos hδ
  obtain ⟨χ, hχs, hχc, hχU, hχ1⟩ := exists_smooth_cutoff (hK'c.cthickening (r := δ / 2)) hU'o
    ((cthickening_mono (half_le_self hδ.le) K').trans hδU')
  have hχ1' : ∀ z ∈ cthickening (δ / 2) K', χ z = 1 := fun z hz =>
    (eventually_nhdsSet_iff_forall.1 hχ1 z hz).self_of_nhds
  set N : Set ℂ := thickening (δ / 2) K' with hNdef
  have hNo : IsOpen N := isOpen_thickening
  have hKN : K ⊆ N := fun z hz => self_subset_thickening hδ2 K' (Or.inl hz)
  have hNU : N ⊆ U' := fun z hz => hδU' (thickening_subset_cthickening_of_le (half_le_self hδ.le) K' hz)
  have hNO : ∀ z ∈ N, z.im = 0 → z.re ∈ O := by
    intro z hz hz0
    by_contra h
    exact hNU hz ⟨hz0, h⟩
  -- the even cutoff
  set χe : ℂ → ℝ := fun z => (χ z + χ (conj z)) / 2 with hχe
  have hconj_s : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun z : ℂ => conj z :=
    Complex.conjCLE.toContinuousLinearMap.contDiff
  have hχes : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χe := (hχs.add (hχs.comp hconj_s)).div_const 2
  have hχec : HasCompactSupport χe := by
    have h2 : HasCompactSupport fun z => χ (conj z) :=
      hχc.comp_homeomorph Complex.conjLIE.toHomeomorph
    have h3 : HasCompactSupport fun z => χ z + χ (conj z) := hχc.add h2
    have e : χe = fun z => (1 / 2 : ℝ) * (χ z + χ (conj z)) := funext fun z => by simp only [hχe]; ring
    rw [e]
    exact h3.mul_left
  have hχe_conj : ∀ z, χe (conj z) = χe z := fun z => by
    simp only [hχe, Complex.conj_conj]; ring
  have hχeN : ∀ z ∈ N, χe z = 1 := fun z hz => by
    have h1 := hχ1' z (thickening_subset_cthickening _ _ hz)
    have h2 := hχ1' (conj z) (thickening_subset_cthickening _ _ (mem_thickening_conj hK'conj hz))
    simp only [hχe, h1, h2]; norm_num
  -- the support of the even cutoff lies in the reflected domain
  have hconjU : ∀ z, z ∈ U' → conj z ∈ U' := fun z hz h => hz ⟨by
    have := h.1; rwa [Complex.conj_im, neg_eq_zero] at this, by simpa using h.2⟩
  have hχe0 : ∀ z, z ∉ U' → χe =ᶠ[𝓝 z] 0 := by
    intro z hz
    have hzU : z ∉ tsupport χ := fun h => hz (hχU h)
    have h1 : χ =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.1 hzU
    have hzU' : conj z ∉ tsupport χ := fun h => hz (by
      have := hconjU _ (hχU h); rwa [Complex.conj_conj] at this)
    have h1' : χ =ᶠ[𝓝 (conj z)] 0 := notMem_tsupport_iff_eventuallyEq.1 hzU'
    have h2 : (fun w => χ (conj w)) =ᶠ[𝓝 z] 0 :=
      (Complex.continuous_conj.tendsto z).eventually h1'
    filter_upwards [h1, h2] with w hw1 hw2
    simp only [hχe, Pi.zero_apply] at hw1 hw2 ⊢
    rw [hw1, hw2]; norm_num
  have hsuppU : tsupport χe ⊆ U' := fun z hz => by
    by_contra hzU
    exact (notMem_tsupport_iff_eventuallyEq.2 (hχe0 z hzU)) hz
  exact ⟨χe, N, hχes, hχec, hχe_conj, hsuppU, hNo, hKN, hNU, hχeN⟩

namespace ReflectionCutoff
variable {O : Set ℝ} {K : Set ℂ} (C : ReflectionCutoff O K)

/-- Multiplying the reflected correction by the fixed bump is globally smooth. -/
theorem smooth_mul {q : ℂ → ℝ}
    (hR : InnerProductSpace.HarmonicOnNhd (oddRefl q) (reflDom O)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => C.bump z * oddRefl q z) := by
  refine contDiff_iff_contDiffAt.2 fun z => ?_
  by_cases hz : z ∈ reflDom O
  · exact C.smooth.contDiffAt.mul (_root_.HarmonicAt.analyticAt (hR z hz)).contDiffAt
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    have he : C.bump =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.1
      (fun hs => hz (C.support hs))
    filter_upwards [he] with w hw
    simp [hw]

/-- Explicit cutoff; its function depends on `q` by a fixed formula. -/
def cut (q : ℂ → ℝ) (hR : InnerProductSpace.HarmonicOnNhd (oddRefl q) (reflDom O)) : CMCut where
  f := fun z => C.bump z * oddRefl q z
  smooth := C.smooth_mul hR
  compact := C.compact.mul_right
  odd := fun z => by rw [C.even, oddRefl_conj, mul_neg]

/-- This fixed bump supplies every condition in `IsCutoffOn`. -/
theorem isCutoffOn {q : ℂ → ℝ}
    (hR : InnerProductSpace.HarmonicOnNhd (oddRefl q) (reflDom O)) :
    IsCutoffOn (C.cut q hR) q C.neighbourhood O := by
  classical
  refine ⟨C.open_neighbourhood, fun z hz hz0 => by
    by_contra hnot
    exact C.neighbourhood_sub hz ⟨hz0, hnot⟩,
    fun z hz hzH => ?_, fun z hz => ?_⟩
  · change C.bump z * oddRefl q z = q z
    rw [C.one z hz, one_mul, oddRefl_of_pos hzH]
  · have he : (C.cut q hR).f =ᶠ[𝓝 z] oddRefl q := by
      filter_upwards [C.open_neighbourhood.mem_nhds hz] with w hw
      change C.bump w * oddRefl q w = _
      rw [C.one w hw, one_mul]
    rw [QuantumZipper.K3.greenDensity, (InnerProductSpace.laplacian_congr_nhds he).eq_of_nhds,
      (hR z (C.neighbourhood_sub hz)).2.eq_of_nhds, Pi.zero_apply, mul_zero]

/-- The correction is bounded on the support of this cutoff's source. -/
theorem exists_abs_le_on_src {q : ℂ → ℝ}
    (hR : InnerProductSpace.HarmonicOnNhd (oddRefl q) (reflDom O)) :
    ∃ M : ℝ, ∀ z, (C.cut q hR).src z ≠ 0 → |q z| ≤ M := by
  have hcont : ContinuousOn (oddRefl q) (reflDom O) :=
    fun z hz => (hR z hz).1.continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := C.compact.isCompact.exists_bound_of_continuousOn (hcont.mono C.support)
  refine ⟨M, fun z hz => ?_⟩
  obtain ⟨hzH, hzs⟩ := (C.cut q hR).mem_of_src_ne_zero hz
  have hzC : z ∈ tsupport C.bump := by
    by_contra hnot
    have h0 : (C.cut q hR).f =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hnot] with w hw
      change C.bump w * oddRefl q w = 0
      rw [hw, Pi.zero_apply, zero_mul]
    have hg : QuantumZipper.K3.greenDensity (C.cut q hR).f =ᶠ[𝓝 z] 0 := by
      filter_upwards [InnerProductSpace.laplacian_congr_nhds h0] with w hw
      rw [QuantumZipper.K3.greenDensity, hw, InnerProductSpace.laplacian_const]
      simp
    exact (notMem_tsupport_iff_eventuallyEq.2 hg) hzs
  have hb := hM z hzC
  rwa [Real.norm_eq_abs, oddRefl_of_pos hzH] at hb

end ReflectionCutoff
end InteractingSLE.Sec5.Aux61GInst
