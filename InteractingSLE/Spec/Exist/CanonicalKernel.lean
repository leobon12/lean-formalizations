/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.CanonicalAtom
import InteractingSLE.Spec.Exist.CanonicalHist
import InteractingSLE.Spec.Coupling.WholeField4Birth
import InteractingSLE.GFF.LocalSets.MarkovNesting
import InteractingSLE.Spec.Coupling.MartMeans2Chart

/-!
# The field off the hull is not determined by the history: a Gaussian lower bound at the lifetime

Packet PROVE-FLOWEXIST3 (AUD-3c N1), the crux of `Exist.CanonicalBrownianStatement`. For the frozen optional hull
coupling, the bump `φₙ` at the high point `i(2√n + 3)` (`highBump n`) lies above height `2√n + 1`, which no hull `K_t`,
`t < ζ ≤ n`, reaches (`4t < (Im z)²`). Given the history announced at the lifetime, `⋁ₖ 𝓓_{σₖ}` (`σₖ ↑ ζ`), the
pairing `(h, φₙ)` is Gaussian with variance `⨅ₖ G_{ℍ∖K_{σₖ}}(φₙ, φₙ)` (`WholeField.exists_announced_kernel_history`), and
the variance is at least `cₙ = (∫ φₙ²)² / E(φₙ) > 0` (the dual Dirichlet norm is a supremum, tested at `φₙ` itself).
Hence (**`exists_announce_norm_condExp_le`**) on `{ζ ≤ n}`:

`‖E[e^{i s (h, φₙ)} | ⋁ₖ 𝓓_{σₖ}]‖ ≤ e^{−s² cₙ / 2}`.

* `highRegion`, `highBump`, `highConst`; `highConst_pos`; `le_zeroGFFTestCov_highBump`;
* `notMem_fwdHull_rpath_of_four_mul_lt`: a point above height `2√t` is outside `K_t` for a driver continuous before
  `ζ > t`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Complex Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Exist

open QuantumZipper (H zeroGFFTestCov zeroSpace)
open QuantumZipper (fwdHull IsForwardSol)
open LQGMetric WholeField Coupling LocalSets Ito

/-! ### The high bump and its variance lower bound -/

section Bump

/-- The region above height `2√n + 1`. -/
def highRegion (n : ℕ) : Set ℂ := {z | 2 * Real.sqrt n + 1 < z.im}

theorem isOpen_highRegion (n : ℕ) : IsOpen (highRegion n) :=
  isOpen_lt continuous_const Complex.continuous_im

theorem highRegion_subset_H (n : ℕ) : highRegion n ⊆ H := fun z hz => by
  change 0 < z.im
  have : 2 * Real.sqrt n + 1 < z.im := hz
  linarith [Real.sqrt_nonneg (n : ℝ)]

theorem closedBall_highPt_subset_highRegion (n : ℕ) : closedBall (highPt n) 1 ⊆ highRegion n :=
  fun y hy => by
    have := im_ge_of_mem_closedBall_highPt hy
    change 2 * Real.sqrt n + 1 < y.im
    linarith

/-- The bump test function at the high point of level `n`. -/
def highBump (n : ℕ) : TestOn upperHalfPlaneOpens :=
  GFF.bumpTest (D := upperHalfPlaneOpens) (highPt n) one_pos (closedBall_highPt_subset n)

theorem coe_highBump (n : ℕ) : ⇑(highBump n) = GFF.bumpFun (highPt n) 1 := rfl

theorem tsupport_highBump_subset (n : ℕ) : tsupport (highBump n) ⊆ highRegion n :=
  (GFF.tsupport_bumpFun_subset one_pos).trans (closedBall_highPt_subset_highRegion n)

theorem highBump_center_pos (n : ℕ) : 0 < highBump n (highPt n) := by
  rw [coe_highBump]
  simp only [GFF.bumpFun, sub_self, zero_div, LQGMetric.GM.radProf, norm_zero]
  exact expNegInvGlue.pos_of_pos (by norm_num)

theorem highBump_mem_zeroSpace (n : ℕ) {V : Set ℂ} (hV : highRegion n ⊆ V) :
    ⇑(highBump n) ∈ zeroSpace V :=
  ⟨GFF.contDiff_bumpFun _ _, GFF.hasCompactSupport_bumpFun one_pos,
    (tsupport_highBump_subset n).trans hV⟩

theorem integral_highBump_sq_pos (n : ℕ) : 0 < ∫ z, highBump n z * highBump n z := by
  have hc : Continuous fun z => highBump n z * highBump n z := by
    have := (GFF.contDiff_bumpFun (highPt n) 1).continuous
    rw [coe_highBump]; exact this.mul this
  refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := highPt n) ?_ ?_ ?_
  · rw [coe_highBump]; exact (GFF.hasCompactSupport_bumpFun one_pos).mul_left
  · exact fun z => mul_self_nonneg _
  · exact (mul_pos (highBump_center_pos n) (highBump_center_pos n)).ne'

theorem energyC_highBump_pos (n : ℕ) : 0 < energyC (highBump n) := by
  have hsm := GFF.contDiff_bumpFun (highPt n) 1
  rw [energyC, coe_highBump]
  refine mul_pos (by positivity) ?_
  have hdc : Continuous fun z => ‖fderiv ℝ (GFF.bumpFun (highPt n) 1) z‖ ^ 2 :=
    ((hsm.continuous_fderiv (by simp)).norm).pow 2
  -- the derivative does not vanish identically
  have hne : ∃ z, fderiv ℝ (GFF.bumpFun (highPt n) 1) z ≠ 0 := by
    by_contra hall
    push Not at hall
    have hconst := is_const_of_fderiv_eq_zero (hsm.differentiable (by simp)) hall (highPt n)
      (highPt n + 2)
    have h0 : GFF.bumpFun (highPt n) 1 (highPt n + 2) = 0 :=
      GFF.bumpFun_eq_zero one_pos (by simp [dist_eq_norm])
    have hpos := highBump_center_pos n
    rw [coe_highBump] at hpos
    rw [hconst, h0] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨z, hz⟩ := hne
  refine hdc.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := z) ?_ (fun _ => by positivity) ?_
  · exact ((GFF.hasCompactSupport_bumpFun one_pos).fderiv (𝕜 := ℝ)).norm.comp_left (g := fun x : ℝ => x ^ 2)
      (by norm_num)
  · exact pow_ne_zero 2 (norm_ne_zero_iff.2 hz)

/-- The variance lower bound `cₙ = (∫ φₙ²)² / E(φₙ)`. -/
def highConst (n : ℕ) : ℝ := (∫ z, highBump n z * highBump n z) ^ 2 / energyC (highBump n)

theorem highConst_pos (n : ℕ) : 0 < highConst n :=
  div_pos (pow_pos (integral_highBump_sq_pos n) 2) (energyC_highBump_pos n)

/-- **The variance lower bound.** For every open `V ⊆ ℍ` containing the high region,
`G_V(s φₙ, s φₙ) ≥ s² cₙ`. -/
theorem le_zeroGFFTestCov_highBump (n : ℕ) (s : ℝ) {V : Set ℂ} (hV : IsOpen V) (hVH : V ⊆ H)
    (hRV : highRegion n ⊆ V) :
    s ^ 2 * highConst n ≤ zeroGFFTestCov V ⇑(s • highBump n : TestOn upperHalfPlaneOpens)
      ⇑(s • highBump n : TestOn upperHalfPlaneOpens) := by
  have hiSup := ofReal_zeroGFFTestCov_eq_iSup hV hVH (s • highBump n)
  have hmem : ⇑(highBump n) ∈ {f | f ∈ zeroSpace V ∧ 0 < energyC f} :=
    ⟨highBump_mem_zeroSpace n hRV, energyC_highBump_pos n⟩
  have hle : ENNReal.ofReal ((∫ z, (s • highBump n) z * highBump n z) ^ 2 / energyC (highBump n)) ≤
      ENNReal.ofReal (zeroGFFTestCov V ⇑(s • highBump n : TestOn upperHalfPlaneOpens)
        ⇑(s • highBump n : TestOn upperHalfPlaneOpens)) := by
    rw [hiSup]
    exact le_iSup₂ (f := fun f (_ : f ∈ {f | f ∈ zeroSpace V ∧ 0 < energyC f}) =>
      ENNReal.ofReal ((∫ z, (s • highBump n) z * f z) ^ 2 / energyC f)) (⇑(highBump n)) hmem
  have e : (∫ z, (s • highBump n) z * highBump n z) ^ 2 / energyC (highBump n) =
      s ^ 2 * highConst n := by
    have : (fun z => (s • highBump n) z * highBump n z) = fun z => s * (highBump n z * highBump n z) := by
      funext z
      rw [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [this, integral_const_mul, highConst, mul_pow, mul_div_assoc]
  rw [e] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (zeroGFFTestCov_self_nonneg hV hVH _)).1 hle

end Bump

/-! ### Points above the hulls -/

/-- A point above height `2√t` is outside `K_t`, for a driver continuous before `ζ > t`. -/
theorem notMem_fwdHull_rpath_of_four_mul_lt {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) {r : ℝ≥0} (hr : (r : ℝ≥0∞) < ζ) {y : ℂ} (hy0 : 0 < y.im)
    (h4 : 4 * (r : ℝ) < y.im ^ 2) : y ∉ fwdHull (rpath w) r := by
  set T : ℝ := (r : ℝ) with hT
  have hT0 : 0 ≤ T := r.coe_nonneg
  have hwc : ContinuousOn (rpath w) (Icc 0 T) := continuousOn_rpath hw hr
  have hW' : Continuous (clampDrv (rpath w) T) := continuous_clampDrv hT0 hwc
  have hnot : y ∉ fwdHull (clampDrv (rpath w) T) T :=
    Sec7.notMem_fwdHull_of_four_mul_lt_im_sq hW' hy0 h4
  obtain ⟨u, hu⟩ := exists_isForwardSol_of_mem hT0 (show y ∈ H \ fwdHull (clampDrv (rpath w) T) T from
    ⟨hy0, hnot⟩)
  have hu' : IsForwardSol (rpath w) y T u := (isForwardSol_iff_of_eqOn clampDrv_eqOn u).1 hu
  exact notMem_fwdHull_of_alive hw hr hy0 ⟨u, hu'⟩

/-- Above height `2√n + 1` there is no point of `K_r`, `r < ζ ≤ n`. -/
theorem highRegion_subset_H_diff {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    {n : ℕ} (hζn : ζ ≤ n) {r : ℝ≥0} (hr : (r : ℝ≥0∞) < ζ) :
    highRegion n ⊆ H \ fwdHull (rpath w) r := by
  intro y hy
  have hyH := highRegion_subset_H n hy
  refine ⟨hyH, notMem_fwdHull_rpath_of_four_mul_lt hw hr hyH ?_⟩
  have hy' : 2 * Real.sqrt n + 1 < y.im := hy
  have hrn : (r : ℝ) < n := by
    have : (r : ℝ≥0∞) < (n : ℝ≥0∞) := lt_of_lt_of_le hr hζn
    exact_mod_cast this
  have hs := Real.sqrt_nonneg (n : ℝ)
  have hss := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  nlinarith

/-! ### The Gaussian bound given the history announced at the lifetime -/

section Announce

universe u

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The Gaussian bound at the lifetime.** For the frozen coupling with an admissible seed there is an announcing
sequence `σₖ ↑ ζ` of the driving filtration such that, for every `n` and `s`, almost surely on `{ζ ≤ n}`:
`‖E[e^{i s (h, φₙ)} | ⋁ₖ 𝓓_{σₖ}]‖ ≤ e^{−s² cₙ / 2}`. -/
theorem exists_announce_norm_condExp_le (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) :
    ∃ (σ : ℕ → Ω → ℝ≥0) (hσ : ∀ k, IsStoppingTime (drivingFiltration P hX) fun ω => (σ k ω : WithTop ℝ≥0)),
      IsAnnouncingSeq (drivingFiltration P hX) P ζ σ ∧
      ∀ (n : ℕ) (s : ℝ), ∀ᵐ ω ∂P, ζ ω ≤ n →
        ‖P[fun ω' => cexp (s * h ω' (highBump n) * I) | ⨆ k, (hσ k).measurableSpace] ω‖ ≤
          Real.exp (-(s ^ 2 * highConst n / 2)) := by
  have hE := hC.1
  have : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  obtain ⟨σ₀, hσ₀, -⟩ := exists_isAnnouncingSeq_of_adapted (𝓖 := drivingFiltration P hX) (B := B)
    (κ := κ) (xL := xL) (xR := xR) (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0)
    (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_W hX))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_VL hX i))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_VR hX i))
    hE.2.2.2.2 (hE.ae_tendsto_threshold hκ) hseed
  obtain ⟨u₀, hu₀⟩ := WholeField.exists_bhe κ ρL ρR xL xR
  obtain ⟨A, 𝒢, -, hAK, -, hker⟩ := exists_announced_kernel_history hC hκ hu₀ hX hσ₀.1 hσ₀.2.1 hσ₀.2.2.1
  refine ⟨σ₀, hσ₀.1, hσ₀, fun n s => ?_⟩
  set ψ : TestOn upperHalfPlaneOpens := s • highBump n with hψ
  filter_upwards [hker ψ, ae_all_iff.2 hAK, ae_all_iff.2 hσ₀.2.2.1, hE.2.2.2.2] with ω hk hAω hσω hp hζn
  have hw : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := hp.2.2.2.1
  have hsub : ∀ k, highRegion n ⊆ H \ A k ω := fun k => by
    rw [hAω k]
    exact highRegion_subset_H_diff hw hζn (hσω k)
  have hdisj : ∀ k, Disjoint (tsupport ψ) (A k ω) := fun k => by
    refine Set.disjoint_left.2 fun y hyψ hyK => ?_
    have hyφ : y ∈ tsupport (highBump n) := by
      rw [hψ, FunLike.coe_smul] at hyψ
      exact tsupport_smul_subset_right (fun _ => s) _ hyψ
    exact ((hsub k) (tsupport_highBump_subset n hyφ)).2 hyK
  obtain ⟨-, -, -, h4⟩ := hk hdisj
  have hlow : ∀ k, s ^ 2 * highConst n ≤ zeroGFFTestCov (H \ A k ω) ψ ψ := fun k => by
    have hopen : IsOpen (H \ A k ω) := by
      rw [hAω k]; exact MartMeans2.isOpen_H_diff_fwdHull_rpath hw (hσω k)
    exact le_zeroGFFTestCov_highBump n s hopen sdiff_subset (hsub k)
  have hinf : s ^ 2 * highConst n ≤ ⨅ k, zeroGFFTestCov (H \ A k ω) ψ ψ := le_ciInf hlow
  have e : (fun ω' => cexp (s * h ω' (highBump n) * I)) = fun ω' => cexp (I * (h ω' ψ : ℂ)) := by
    funext ω'
    rw [hψ, map_smul, smul_eq_mul, Complex.ofReal_mul]
    ring_nf
  rw [e, h4, Complex.norm_exp]
  refine Real.exp_le_exp.2 ?_
  simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, zero_sub]
  linarith

end Announce

end Exist

end InteractingSLE
