import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Complex.Harmonic.Analytic
import InteractingSLE.Foundations.Brownian.Dynkin

/-!
# Harmonic functions of planar Brownian motion at exit times

Packet GEO-BM of the geometry foundation (`planning/INFRA-GEO.md` §3, §4). Infrastructure
([KS] Karatzas–Shreve, §4.2.A–B, pp. 240–247; [Law05] Lawler, §2.3, pp. 33–40), not a frozen
source-facing file.

* `integral_untopA_eq_of_le`: optional stopping at a bounded stopping time for a martingale with
  continuous paths that is bounded on the time horizon (from QuantumZipper's
  `ItoLite.integral_mul_stoppedValue_eq_of_le`, applied to the martingale frozen at the horizon).
* `IsPlanarBrownian.integral_dynkin_stopped`: Dynkin's identity at `τ ∧ T` for a stopping time `τ`.
* `exists_cutoff`: smooth compactly supported cutoffs, `1` near a compact set.
* `IsPlanarBrownian.ae_exitTime_lt_top`: from a point of a bounded open set, planar Brownian
  motion exits almost surely (with `E[τ] < ∞`).
* `IsPlanarBrownian.integral_exitPoint_eq`: for `u` harmonic on a neighbourhood of the closure of
  a bounded open `D ∋ z`, `E[u(Z_τ)] = u(z)` (the Brownian representation of the solution of the
  Dirichlet problem, [KS] §4.2.B, Prop. 2.7, p. 244, in the case of a function harmonic near the
  closure; the proof here uses Dynkin's formula instead of Itô's rule).
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory ProbabilityTheory InnerProductSpace
open scoped NNReal ENNReal Laplacian Manifold

namespace InteractingSLE

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω}

/-! ### Optional stopping at bounded stopping times -/

/-- A martingale frozen at time `T` is a martingale. -/
lemma martingale_min_const [IsFiniteMeasure P] {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M 𝓕 P) (T : ℝ≥0) :
    Martingale (fun t => M (min t T)) 𝓕 P := by
  refine ⟨fun t => (hM.stronglyAdapted (min t T)).mono (𝓕.mono (min_le_left _ _)),
    fun s t hst => ?_⟩
  by_cases hsT : s ≤ T
  · have h1 : min s T = s := min_eq_left hsT
    simp only [h1]
    exact hM.condExp_ae_eq (le_min hst hsT)
  · have hTs : T ≤ s := le_of_not_ge hsT
    have h1 : min s T = T := min_eq_right hTs
    have h2 : min t T = T := min_eq_right (hTs.trans hst)
    simp only [h1, h2]
    exact (condExp_of_stronglyMeasurable (𝓕.le s) ((hM.stronglyAdapted T).mono (𝓕.mono hTs))
      (hM.integrable T)).eventuallyEq

lemma untopA_eq_toNNReal {x : ℝ≥0∞} (hx : x ≠ ⊤) : WithTop.untopA x = x.toNNReal := by
  lift x to ℝ≥0 using hx
  rfl

/-- **Optional stopping at a bounded stopping time.** For a martingale with continuous paths that
is bounded on `[0, T]`, and a stopping time `σ ≤ T`, `E[M_σ] = E[M_0]`. -/
theorem integral_untopA_eq_of_le [IsFiniteMeasure P] {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M 𝓕 P)
    (hc : ∀ ω, Continuous (M · ω)) {T : ℝ≥0} {B : ℝ} (hb : ∀ t ≤ T, ∀ ω, |M t ω| ≤ B)
    {σ : Ω → ℝ≥0∞} (hσ : IsStoppingTime 𝓕 σ) (hle : ∀ ω, σ ω ≤ T) :
    ∫ ω, M (σ ω).toNNReal ω ∂P = ∫ ω, M 0 ω ∂P := by
  have hN := martingale_min_const hM T
  have hNc : ∀ ω, Continuous (fun t => M (min t T) ω) := fun ω =>
    (hc ω).comp (continuous_id.min continuous_const)
  have hNb : ∀ t ω, |M (min t T) ω| ≤ B := fun t ω => hb _ (min_le_right _ _) ω
  have hos := QuantumZipper.ItoLite.integral_mul_stoppedValue_eq_of_le hN hNc hNb
    (σ := σ) hσ (t := T) hle (Y := fun _ => (1 : ℝ)) measurable_const (CY := 1)
    (fun _ => by simp)
  simp only [one_mul, stoppedValue] at hos
  have hσT : ∀ ω, (σ ω).toNNReal ≤ T := fun ω => by
    have := hle ω
    exact (ENNReal.toNNReal_le_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top this)
      ENNReal.coe_ne_top).2 this
  have e1 : ∀ ω, M (min (WithTop.untopA (σ ω)) T) ω = M (σ ω).toNNReal ω := fun ω => by
    rw [untopA_eq_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (hle ω)),
      min_eq_left (hσT ω)]
  simp only [e1, min_self] at hos
  rw [hos, ← integral_condExp (𝓕.le 0)]
  exact integral_congr_ae (hM.condExp_ae_eq bot_le)

/-! ### Smooth cutoffs -/

/-- A smooth compactly supported cutoff: for `K` compact inside an open `U`, a `C³` function `χ`
with compact support in `U` that equals `1` on a neighbourhood of `K`. -/
theorem exists_cutoff {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ 3 χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      (∀ᶠ x in 𝓝ˢ K, χ x = 1) := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨f, hf1, hf0, -⟩ := exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ, ℂ)
    (n := 3) hK.isClosed hKL
  have hfc : ContDiff ℝ 3 (f : ℂ → ℝ) := contMDiff_iff_contDiff.1 f.contMDiff
  have hsupp : tsupport (f : ℂ → ℝ) ⊆ L := by
    refine closure_minimal (fun x hx => ?_) hL.isClosed
    by_contra hxL
    exact hx (hf0 x hxL)
  exact ⟨f, hfc, HasCompactSupport.intro hL (fun x hx => hf0 x hx), hsupp.trans hLU, hf1⟩

/-- A cutoff times a function that is `C³` on an open set containing the cutoff's support is
`C³`. -/
lemma contDiff_cutoff_mul {χ u : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U) (hχ : ContDiff ℝ 3 χ)
    (hsupp : tsupport χ ⊆ U) (hu : ContDiffOn ℝ 3 u U) : ContDiff ℝ 3 (fun x => χ x * u x) := by
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  by_cases hx : x ∈ U
  · exact hχ.contDiffAt.mul (hu.contDiffAt (hU.mem_nhds hx))
  · have hx' : x ∉ tsupport χ := fun h => hx (hsupp h)
    have hev : χ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hx'
    have hev' : (fun x => χ x * u x) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [hev] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq hev'

/-- A `C³` function with compact support has bounded first, second and third derivatives and is
bounded. -/
lemma exists_bounds_of_hasCompactSupport {F : ℂ → ℝ} (hF : ContDiff ℝ 3 F)
    (hc : HasCompactSupport F) :
    ∃ C B : ℝ, (∀ x, ‖fderiv ℝ F x‖ ≤ C ∧ ‖iteratedFDeriv ℝ 2 F x‖ ≤ C ∧
      ‖iteratedFDeriv ℝ 3 F x‖ ≤ C) ∧ ∀ x, |F x| ≤ B := by
  obtain ⟨C1, h1⟩ := (hF.continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    (hc.fderiv (𝕜 := ℝ))
  obtain ⟨C2, h2⟩ := (hF.continuous_iteratedFDeriv (m := 2) (by norm_num)).bounded_above_of_compact_support
    (hc.iteratedFDeriv 2)
  obtain ⟨C3, h3⟩ := (hF.continuous_iteratedFDeriv (m := 3) (by norm_num)).bounded_above_of_compact_support
    (hc.iteratedFDeriv 3)
  obtain ⟨B, hB⟩ := hF.continuous.bounded_above_of_compact_support hc
  refine ⟨max C1 (max C2 C3), B, fun x => ⟨(h1 x).trans (le_max_left _ _),
    (h2 x).trans ((le_max_left _ _).trans (le_max_right _ _)),
    (h3 x).trans ((le_max_right _ _).trans (le_max_right _ _))⟩, fun x => ?_⟩
  rw [← Real.norm_eq_abs]; exact hB x

/-- A function harmonic on a neighbourhood of a compact set agrees there with a compactly
supported `C³` function whose generator vanishes on the set. -/
theorem exists_cutoff_harmonic {K : Set ℂ} (hK : IsCompact K) {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u K) :
    ∃ F : ℂ → ℝ, ContDiff ℝ 3 F ∧ HasCompactSupport F ∧ (∀ x ∈ K, F x = u x) ∧
      ∀ x ∈ K, planarGen F x = 0 := by
  set U := {x | HarmonicAt u x} with hUdef
  have hU : IsOpen U := isOpen_setOfPred_harmonicAt u
  have hKU : K ⊆ U := fun x hx => hu x hx
  obtain ⟨χ, hχ, hχc, hχU, hχ1⟩ := exists_cutoff hK hU hKU
  have hu3 : ContDiffOn ℝ 3 u U := fun x hx =>
    ((HarmonicAt.analyticAt hx).contDiffAt).contDiffWithinAt
  refine ⟨fun x => χ x * u x, contDiff_cutoff_mul hU hχ hχU hu3, hχc.mul_right, fun x hx => ?_,
    fun x hx => ?_⟩
  · have : χ x = 1 := (hχ1.filter_mono (nhds_le_nhdsSet hx)).self_of_nhds
    simp [this]
  · have hev : (fun x => χ x * u x) =ᶠ[𝓝 x] u := by
      filter_upwards [hχ1.filter_mono (nhds_le_nhdsSet hx)] with y hy
      simp [hy]
    rw [planarGen, (laplacian_congr_nhds hev).self_of_nhds, (hu x hx).2.self_of_nhds]
    simp

/-! ### Dynkin's identity at stopping times -/

namespace IsPlanarBrownian

variable {Z : ℝ≥0 → Ω → ℂ}

/-- The position at a measurable random time is measurable. -/
lemma measurable_comp_time (hZ : IsPlanarBrownian 𝓕 Z P) {σ : Ω → ℝ≥0} (hσ : Measurable σ) :
    Measurable (fun ω => Z (σ ω) ω) := by
  have hj : Measurable (Function.uncurry fun (t : ℝ≥0) (ω : Ω) => Z t ω) :=
    measurable_uncurry_of_continuous_of_measurable hZ.continuous hZ.measurable'
  exact hj.comp (hσ.prodMk measurable_id)

/-- The time integral up to a measurable random time is measurable. -/
lemma measurable_integral_time (hZ : IsPlanarBrownian 𝓕 Z P) {g : ℂ → ℝ} (hg : Continuous g)
    {σ : Ω → ℝ≥0} (hσ : Measurable σ) :
    Measurable (fun ω => ∫ r in (0 : ℝ)..(σ ω : ℝ), g (Z r.toNNReal ω)) := by
  have hYc : ∀ ω, Continuous fun r : ℝ => g (Z r.toNNReal ω) := fun ω =>
    hg.comp ((hZ.continuous ω).comp continuous_real_toNNReal)
  have hYm : ∀ r : ℝ, Measurable fun ω => g (Z r.toNNReal ω) := fun r =>
    hg.measurable.comp (hZ.measurable' _)
  set G : ℝ → Ω → ℝ := fun s ω => ∫ r in (0 : ℝ)..s, g (Z r.toNNReal ω) with hG
  have hGc : ∀ ω, Continuous fun s => G s ω := fun ω =>
    intervalIntegral.continuous_primitive (fun _ _ => (hYc ω).intervalIntegrable _ _) 0
  have hGm : ∀ s, Measurable (G s) := fun s =>
    QuantumZipper.Dynkin.measurable_intervalIntegral_of_continuous hYm hYc 0 s
  have hj : Measurable (Function.uncurry G) := measurable_uncurry_of_continuous_of_measurable hGc hGm
  exact hj.comp ((measurable_coe_nnreal_real.comp hσ).prodMk measurable_id)

/-- **Dynkin's identity at a stopping time**, truncated at a deterministic horizon `T`. -/
theorem integral_dynkin_stopped (hZ : IsPlanarBrownian 𝓕 Z P) {F : ℂ → ℝ} {C B : ℝ}
    (hF : ContDiff ℝ 3 F)
    (hD : ∀ x, ‖fderiv ℝ F x‖ ≤ C ∧ ‖iteratedFDeriv ℝ 2 F x‖ ≤ C ∧
      ‖iteratedFDeriv ℝ 3 F x‖ ≤ C)
    (hFb : ∀ x, |F x| ≤ B) {τ : Ω → ℝ≥0∞} (hτ : IsStoppingTime 𝓕 τ) (T : ℝ≥0) :
    ∫ ω, F (Z (min (τ ω) T).toNNReal ω) ∂P = ∫ ω, F (Z 0 ω) ∂P
      + ∫ ω, (∫ r in (0 : ℝ)..((min (τ ω) T).toNNReal : ℝ), planarGen F (Z r.toNNReal ω)) ∂P := by
  have hP := hZ.isProbabilityMeasure
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hD 0).1
  have hFm : Measurable F := hF.continuous.measurable
  have hF0 : Integrable (fun ω => F (Z 0 ω)) P :=
    Integrable.of_bound (hFm.comp (hZ.measurable' 0)).aestronglyMeasurable B
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hFb _)
  have hM := hZ.martingale_dynkin hF hD hF0
  set σ : Ω → ℝ≥0∞ := fun ω => min (τ ω) (T : ℝ≥0∞) with hσdef
  have hσ : IsStoppingTime 𝓕 σ := hτ.min_const T
  have hσle : ∀ ω, σ ω ≤ T := fun ω => min_le_right _ _
  have hgc := PlanarBM.continuous_planarGen hF
  have hgb : ∀ y, |planarGen F y| ≤ C := fun y => (PlanarBM.abs_planarGen_le F y).trans (hD y).2.1
  have hint_le : ∀ (t : ℝ≥0) ω, |∫ r in (0 : ℝ)..(t : ℝ), planarGen F (Z r.toNNReal ω)| ≤ C * t :=
    fun t ω => by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := (t : ℝ)) (C := C)
        (f := fun r => planarGen F (Z r.toNNReal ω)) (fun r _ => by
          rw [Real.norm_eq_abs]; exact hgb _)
      rw [sub_zero, abs_of_nonneg t.coe_nonneg, Real.norm_eq_abs] at this
      linarith
  have hMc : ∀ ω, Continuous fun t : ℝ≥0 =>
      F (Z t ω) - ∫ r in (0 : ℝ)..(t : ℝ), planarGen F (Z r.toNNReal ω) := fun ω =>
    (hF.continuous.comp (hZ.continuous ω)).sub
      ((intervalIntegral.continuous_primitive (fun _ _ => (hgc.comp ((hZ.continuous ω).comp
        continuous_real_toNNReal)).intervalIntegrable _ _) 0).comp NNReal.continuous_coe)
  have hMb : ∀ t ≤ T, ∀ ω, |F (Z t ω) - ∫ r in (0 : ℝ)..(t : ℝ), planarGen F (Z r.toNNReal ω)|
      ≤ B + C * T := fun t ht ω => by
    have h1 := hint_le t ω
    have h2 : C * t ≤ C * T := mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 ht) hC0
    calc _ ≤ |F (Z t ω)| + |∫ r in (0 : ℝ)..(t : ℝ), planarGen F (Z r.toNNReal ω)| := abs_sub _ _
      _ ≤ B + C * T := by linarith [hFb (Z t ω)]
  have hos := integral_untopA_eq_of_le hM hMc hMb hσ hσle
  simp only [NNReal.coe_zero, intervalIntegral.integral_same, sub_zero] at hos
  have hσm : Measurable fun ω => (σ ω).toNNReal :=
    (hσ.measurable' ).ennreal_toNNReal
  have i1 : Integrable (fun ω => F (Z (σ ω).toNNReal ω)) P :=
    Integrable.of_bound (hFm.comp (hZ.measurable_comp_time hσm)).aestronglyMeasurable B
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hFb _)
  have i2 : Integrable (fun ω => ∫ r in (0 : ℝ)..((σ ω).toNNReal : ℝ),
      planarGen F (Z r.toNNReal ω)) P :=
    Integrable.of_bound (hZ.measurable_integral_time hgc hσm).aestronglyMeasurable (C * T)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]
        refine (hint_le _ ω).trans (mul_le_mul_of_nonneg_left ?_ hC0)
        exact NNReal.coe_le_coe.2 ((ENNReal.toNNReal_le_toNNReal
          (ne_top_of_le_ne_top ENNReal.coe_ne_top (hσle ω)) ENNReal.coe_ne_top).2 (hσle ω)))
  rw [integral_sub i1 i2] at hos
  linarith

lemma integrable_integral_time (hZ : IsPlanarBrownian 𝓕 Z P) {g : ℂ → ℝ} (hg : Continuous g)
    {C : ℝ} (hgb : ∀ y, |g y| ≤ C) {σ : Ω → ℝ≥0} (hσ : Measurable σ) {T : ℝ≥0}
    (hσT : ∀ ω, σ ω ≤ T) :
    Integrable (fun ω => ∫ r in (0 : ℝ)..(σ ω : ℝ), g (Z r.toNNReal ω)) P := by
  have hP := hZ.isProbabilityMeasure
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hgb 0)
  refine Integrable.of_bound (hZ.measurable_integral_time hg hσ).aestronglyMeasurable (C * T)
    (Eventually.of_forall fun ω => ?_)
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := (σ ω : ℝ)) (C := C)
    (f := fun r => g (Z r.toNNReal ω)) (fun r _ => by rw [Real.norm_eq_abs]; exact hgb _)
  rw [sub_zero, abs_of_nonneg (σ ω).coe_nonneg] at this
  calc _ ≤ C * (σ ω : ℝ) := by linarith
    _ ≤ C * T := mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 (hσT ω)) hC0

end IsPlanarBrownian

lemma planarGen_re_sq (y : ℂ) : planarGen (fun w : ℂ => w.re ^ 2) y = 1 := by
  have hf : ContDiff ℝ 2 (fun x : ℝ => x ^ 2) := contDiff_id.pow 2
  have hcomp : (fun w : ℂ => w.re ^ 2) = (fun x : ℝ => x ^ 2) ∘ Complex.reCLM := rfl
  have h2 : ∀ v : ℂ, iteratedFDeriv ℝ 2 (fun w : ℂ => w.re ^ 2) y ![v, v] = 2 * v.re * v.re := by
    intro v
    rw [hcomp, Complex.reCLM.iteratedFDeriv_comp_right hf y le_rfl]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
    have hd : iteratedDeriv 2 (fun x : ℝ => x ^ 2) (Complex.reCLM y) = 2 := by simp
    rw [hd]
    simp [Fin.prod_univ_two]
    ring
  rw [planarGen, laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [h2]
  simp

lemma toNNReal_lt_of_lt_min {x : ℝ≥0∞} {n : ℝ≥0} {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < ((min x (n : ℝ≥0∞)).toNNReal : ℝ)) : (r.toNNReal : ℝ≥0∞) < x := by
  have hne : min x (n : ℝ≥0∞) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
  have h1 : r.toNNReal < (min x (n : ℝ≥0∞)).toNNReal := (Real.toNNReal_lt_iff_lt_coe hr0).2 hr
  calc (r.toNNReal : ℝ≥0∞) < (((min x (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ≥0∞) :=
        ENNReal.coe_lt_coe.2 h1
    _ = min x n := ENNReal.coe_toNNReal hne
    _ ≤ x := min_le_left _ _

lemma toNNReal_min_le (x : ℝ≥0∞) (n : ℝ≥0) : (min x (n : ℝ≥0∞)).toNNReal ≤ n :=
  (ENNReal.toNNReal_le_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))
    ENNReal.coe_ne_top).2 (min_le_right _ _)

/-- Before and at its exit time from an open set, a continuous path started inside stays in the
closure of the set. -/
lemma mem_closure_of_le_exitTime {D : Set ℂ} (hD : IsOpen D) {γ : ℝ≥0 → ℂ} (hγ : Continuous γ)
    (h0 : γ 0 ∈ D) {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ exitTime D γ) : γ t ∈ closure D := by
  rcases ht.lt_or_eq with h | h
  · exact subset_closure (mem_of_lt_exitTime h)
  · have hne : exitTime D γ ≠ ⊤ := h ▸ ENNReal.coe_ne_top
    have := exitPoint_mem_closure hD hγ h0 hne
    rwa [exitPoint, ← h, ENNReal.toNNReal_coe] at this

namespace IsPlanarBrownian

variable {Z : ℝ≥0 → Ω → ℂ}

/-- From a point of a bounded open set, planar Brownian motion exits almost surely. -/
theorem ae_exitTime_lt_top (hZ : IsPlanarBrownian 𝓕 Z P) {z : ℂ} (hz : ∀ ω, Z 0 ω = z)
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D) :
    ∀ᵐ ω ∂P, exitTime D (Z · ω) < ⊤ := by
  have hP := hZ.isProbabilityMeasure
  by_cases hzD : z ∉ D
  · refine ae_of_all _ fun ω => ?_
    rw [exitTime_eq_zero_of_not_mem (γ := (Z · ω)) (by simpa [hz ω] using hzD)]
    exact ENNReal.zero_lt_top
  push Not at hzD
  set K := closure D with hKdef
  have hK : IsCompact K := hDb.isCompact_closure
  obtain ⟨χ, hχ, hχc, -, hχ1⟩ := exists_cutoff hK isOpen_univ (subset_univ K)
  set F : ℂ → ℝ := fun x => χ x * x.re ^ 2 with hFdef
  have hF : ContDiff ℝ 3 F := contDiff_cutoff_mul isOpen_univ hχ (subset_univ _)
    ((Complex.reCLM.contDiff.pow 2 : ContDiff ℝ 3 fun x : ℂ => x.re ^ 2)).contDiffOn
  obtain ⟨C, B, hD3, hFb⟩ := exists_bounds_of_hasCompactSupport hF hχc.mul_right
  have hgen : ∀ x ∈ K, planarGen F x = 1 := fun x hx => by
    have hev : F =ᶠ[𝓝 x] fun w => w.re ^ 2 := by
      filter_upwards [hχ1.filter_mono (nhds_le_nhdsSet hx)] with y hy
      simp [hFdef, hy]
    rw [planarGen, (laplacian_congr_nhds hev).self_of_nhds, ← planarGen, planarGen_re_sq]
  set τ : Ω → ℝ≥0∞ := fun ω => exitTime D (Z · ω) with hτdef
  have hτ : IsStoppingTime 𝓕 τ := isStoppingTime_exitTime hZ.measurable hZ.continuous hD
  have hτm : Measurable τ := measurable_exitTime hZ.measurable' hZ.continuous hD
  have hgc := PlanarBM.continuous_planarGen hF
  have hgb : ∀ y, |planarGen F y| ≤ C := fun y => (PlanarBM.abs_planarGen_le F y).trans (hD3 y).2.1
  have hsm : ∀ n : ℝ≥0, Measurable fun ω => (min (τ ω) (n : ℝ≥0∞)).toNNReal := fun n =>
    (hτm.min measurable_const).ennreal_toNNReal
  have hi1 : ∀ n : ℝ≥0, Integrable (fun ω => ((min (τ ω) (n : ℝ≥0∞)).toNNReal : ℝ)) P := fun n =>
    Integrable.of_bound (measurable_coe_nnreal_real.comp (hsm n)).aestronglyMeasurable n
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
        exact NNReal.coe_le_coe.2 (toNNReal_min_le _ _))
  have hkey : ∀ n : ℝ≥0, ∫ ω, ((min (τ ω) (n : ℝ≥0∞)).toNNReal : ℝ) ∂P ≤ 2 * B := by
    intro n
    have hd := hZ.integral_dynkin_stopped hF hD3 hFb hτ n
    have hi2 := hZ.integrable_integral_time hgc hgb (hsm n) (fun ω => toNNReal_min_le (τ ω) n)
    have hge : ∀ ω, ((min (τ ω) (n : ℝ≥0∞)).toNNReal : ℝ) ≤
        ∫ r in (0 : ℝ)..((min (τ ω) (n : ℝ≥0∞)).toNNReal : ℝ), planarGen F (Z r.toNNReal ω) := by
      intro ω
      have h1 : ∫ r in (0 : ℝ)..((min (τ ω) (n : ℝ≥0∞)).toNNReal : ℝ), (1 : ℝ)
          = ((min (τ ω) (n : ℝ≥0∞)).toNNReal : ℝ) := by simp
      refine le_trans (le_of_eq h1.symm) ?_
      refine intervalIntegral.integral_mono_on_of_le_Ioo (NNReal.coe_nonneg _)
        intervalIntegrable_const ((hgc.comp ((hZ.continuous ω).comp
          continuous_real_toNNReal)).intervalIntegrable _ _) (fun r hr => ?_)
      have hlt := toNNReal_lt_of_lt_min hr.1.le hr.2
      rw [hgen _ (subset_closure (mem_of_lt_exitTime hlt))]
    have hint : ∫ ω, ((min (τ ω) (n : ℝ≥0∞)).toNNReal : ℝ) ∂P ≤
        ∫ ω, (∫ r in (0 : ℝ)..((min (τ ω) (n : ℝ≥0∞)).toNNReal : ℝ),
          planarGen F (Z r.toNNReal ω)) ∂P := integral_mono (hi1 n) hi2 hge
    have hb1 : ∫ ω, F (Z (min (τ ω) (n : ℝ≥0∞)).toNNReal ω) ∂P ≤ B := by
      have hm : Measurable fun ω => F (Z (min (τ ω) (n : ℝ≥0∞)).toNNReal ω) :=
        hF.continuous.measurable.comp (hZ.measurable_comp_time (hsm n))
      have hi : Integrable (fun ω => F (Z (min (τ ω) (n : ℝ≥0∞)).toNNReal ω)) P :=
        Integrable.of_bound hm.aestronglyMeasurable B
          (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hFb _)
      calc _ ≤ ∫ _ω, B ∂P :=
            integral_mono hi (integrable_const B) (fun ω => (le_abs_self _).trans (hFb _))
        _ = B := by simp
    have hb2 : -B ≤ ∫ ω, F (Z 0 ω) ∂P := by
      simp only [hz, integral_const, probReal_univ, one_smul]
      exact neg_le_of_abs_le (hFb z)
    linarith
  -- Markov's inequality: `P(τ = ∞) ≤ 2B/n` for every `n ≥ 1`
  have hbd : ∀ n : ℕ, 1 ≤ n → P.real {ω | τ ω = ⊤} ≤ 2 * B / n := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hm := mul_meas_ge_le_integral_of_nonneg (μ := P)
      (Eventually.of_forall fun ω => NNReal.coe_nonneg _) (hi1 (n : ℝ≥0)) (n : ℝ)
    have hsub : {ω | τ ω = ⊤} ⊆
        {ω | (n : ℝ) ≤ ((min (τ ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal : ℝ)} := by
      intro ω hω
      simp only [mem_ofPred_eq] at hω ⊢
      rw [hω]
      simp
    have h2 := measureReal_mono hsub (μ := P)
    rw [le_div_iff₀ hn0]
    nlinarith [hkey (n : ℝ≥0)]
  have hle0 : P.real {ω | τ ω = ⊤} ≤ 0 :=
    ge_of_tendsto (tendsto_const_div_atTop_nhds_zero_nat (2 * B))
      (eventually_atTop.2 ⟨1, hbd⟩)
  have hnull : P {ω | τ ω = ⊤} = 0 :=
    (measureReal_eq_zero_iff (measure_ne_top _ _)).1 (le_antisymm hle0 measureReal_nonneg)
  refine ae_iff.2 ?_
  simpa only [not_lt, top_le_iff] using hnull

/-- **Brownian mean value at the exit point** ([KS] §4.2.B, Prop. 4.2.7, p. 244; [Law05] §2.3):
for `u` harmonic on a neighbourhood of the closure of a bounded open set `D ∋ z`, planar Brownian
motion started at `z` satisfies `E[u(Z_τ)] = u(z)`, `τ` the exit time from `D`. -/
theorem integral_exitPoint_eq (hZ : IsPlanarBrownian 𝓕 Z P) {z : ℂ} (hz : ∀ ω, Z 0 ω = z)
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D) (hzD : z ∈ D) {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u (closure D)) :
    ∫ ω, u (exitPoint D (Z · ω)) ∂P = u z := by
  have hP := hZ.isProbabilityMeasure
  have hK : IsCompact (closure D) := hDb.isCompact_closure
  obtain ⟨F, hF, hFc, hFu, hgen⟩ := exists_cutoff_harmonic hK hu
  obtain ⟨C, B, hD3, hFb⟩ := exists_bounds_of_hasCompactSupport hF hFc
  set τ : Ω → ℝ≥0∞ := fun ω => exitTime D (Z · ω) with hτdef
  have hτ : IsStoppingTime 𝓕 τ := isStoppingTime_exitTime hZ.measurable hZ.continuous hD
  have hτm : Measurable τ := measurable_exitTime hZ.measurable' hZ.continuous hD
  have hfin := hZ.ae_exitTime_lt_top hz hD hDb
  have h0 : ∀ ω, (fun t => Z t ω) 0 ∈ D := fun ω => by simpa [hz ω] using hzD
  have hgc := PlanarBM.continuous_planarGen hF
  have hsm : ∀ n : ℝ≥0, Measurable fun ω => (min (τ ω) (n : ℝ≥0∞)).toNNReal := fun n =>
    (hτm.min measurable_const).ennreal_toNNReal
  have hn : ∀ n : ℕ, ∫ ω, F (Z (min (τ ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal ω) ∂P = u z := by
    intro n
    have hd := hZ.integral_dynkin_stopped hF hD3 hFb hτ n
    have hzero : ∀ ω, ∫ r in (0 : ℝ)..((min (τ ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal : ℝ),
        planarGen F (Z r.toNNReal ω) = 0 := by
      intro ω
      have hii := (hgc.comp ((hZ.continuous ω).comp continuous_real_toNNReal)).intervalIntegrable
        (μ := volume) 0 ((min (τ ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal : ℝ)
      have hz' : ∀ r ∈ Ioo (0 : ℝ) ((min (τ ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal : ℝ),
          planarGen F (Z r.toNNReal ω) = 0 := fun r hr =>
        hgen _ (subset_closure (mem_of_lt_exitTime (toNNReal_lt_of_lt_min hr.1.le hr.2)))
      apply le_antisymm
      · have := intervalIntegral.integral_mono_on_of_le_Ioo (NNReal.coe_nonneg _) hii
          (intervalIntegrable_const (c := (0 : ℝ))) (fun r hr => (hz' r hr).le)
        simpa using this
      · have := intervalIntegral.integral_mono_on_of_le_Ioo (NNReal.coe_nonneg _)
          (intervalIntegrable_const (c := (0 : ℝ))) hii (fun r hr => (hz' r hr).ge)
        simpa using this
    simp only [hzero, integral_zero, add_zero, hz, integral_const, probReal_univ, one_smul] at hd
    rw [hd, hFu z (subset_closure hzD)]
  have hlim : Tendsto (fun n : ℕ => ∫ ω, F (Z (min (τ ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal ω) ∂P)
      atTop (𝓝 (∫ ω, F (exitPoint D (Z · ω)) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => B) (fun n => ?_)
      (integrable_const B) (fun n => ae_of_all _ fun ω => ?_) ?_
    · exact (hF.continuous.measurable.comp (hZ.measurable_comp_time (hsm n))).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact hFb _
    · filter_upwards [hfin] with ω hω
      obtain ⟨N, hN⟩ := exists_nat_ge (τ ω).toNNReal
      refine (tendsto_const_nhds (x := F (exitPoint D (Z · ω)))).congr' ?_
      filter_upwards [eventually_ge_atTop N] with n hnN
      have hle : τ ω ≤ ((n : ℝ≥0) : ℝ≥0∞) := by
        change exitTime D (Z · ω) ≤ _
        rw [← ENNReal.coe_toNNReal hω.ne]
        exact ENNReal.coe_le_coe.2 (hN.trans (by exact_mod_cast hnN))
      have hle' : exitTime D (Z · ω) ≤ ((n : ℝ≥0) : ℝ≥0∞) := hle
      simp only [exitPoint, hτdef, min_eq_left hle']
  have heq : ∫ ω, F (exitPoint D (Z · ω)) ∂P = ∫ ω, u (exitPoint D (Z · ω)) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hfin] with ω hω
    exact hFu _ (exitPoint_mem_closure hD (hZ.continuous ω) (h0 ω) hω.ne)
  rw [← heq]
  refine tendsto_nhds_unique hlim ?_
  simp only [hn]
  exact tendsto_const_nhds

end IsPlanarBrownian

end InteractingSLE
