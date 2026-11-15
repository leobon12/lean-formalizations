import InteractingSLE.Spec.Coupling.Assembly11Safe
import InteractingSLE.Spec.Coupling.TestMean
import InteractingSLE.Spec.Ito.Mean
import InteractingSLE.Foundations.Complex.DerivLog

/-!
# The tested mean and energy along one safe path

Packet PROVE-T11-ASM (obligation 5 of `planning/handoffs/PROVE-T11-L312.md` §4). Along a driving path `w` with marks
`vL`, `vR`, continuous on `[0, ζ)`, and a compact `K ⊆ ℍ` that is safe at time `r` (`IsSafeAt K δ N σ₀ ζ w r`: alive
with `Im f_r ≥ δ` on `K`), this file records the path facts used to show that the frozen mean `(𝔥_τ, φ)` and energy
`E_τ(φ)` of Theorem 1.1 are measurable for the stopped σ-algebra of the driving filtration:

* `meanCan`: the explicit mean `𝔥_s(z) = Im H_s(z)` (`meanHarmonic` of the centred marks at `f_s(z)`, minus
  `χ arg f_s'(z)`), which equals the frozen `couplingMean` for every bounded harmonic extension
  (`couplingMean_eq_meanCan`) and only involves the driver and the marks;
* continuity in space (`continuousOn_meanCan_space`) and in time (`continuousOn_meanCan_time`), a uniform bound
  (`abs_meanCan_le`), and continuity in time of the tested mean (`continuousOn_meanInt`);
* the energy is Lipschitz in time up to `r` (`abs_loewnerGreenEnergy_sub_le`), hence continuous
  (`continuousOn_loewnerGreenEnergy`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace Coupling

open Ito

variable {nL nR : ℕ}

/-! ### The explicit harmonic function -/

theorem mem_slitPlane_of_im_pos {w : ℂ} (hw : 0 < w.im) : w ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.2 (Or.inr hw.ne')

/-- `meanHarmonic` is jointly continuous in the centred marks and the point, on `ℍ`. -/
theorem continuousOn_meanHarmonic_prod (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) :
    ContinuousOn (fun p : (Fin nL → ℝ) × (Fin nR → ℝ) × ℂ => meanHarmonic κ ρL ρR p.1 p.2.1 p.2.2)
      {p | 0 < p.2.2.im} := by
  intro p hp
  apply ContinuousAt.continuousWithinAt
  have h0 : ContinuousAt (fun p : (Fin nL → ℝ) × (Fin nR → ℝ) × ℂ => Complex.arg p.2.2) p :=
    ContinuousAt.comp (g := Complex.arg) (Complex.continuousAt_arg (mem_slitPlane_of_im_pos hp))
      continuous_snd.snd.continuousAt
  have hL : ∀ i, ContinuousAt
      (fun p : (Fin nL → ℝ) × (Fin nR → ℝ) × ℂ => Complex.arg (p.2.2 - (p.1 i : ℂ))) p := fun i =>
    (Complex.continuousAt_arg (mem_slitPlane_of_im_pos (by simpa using hp))).comp
      (continuous_snd.snd.sub
        (Complex.continuous_ofReal.comp ((continuous_apply i).comp continuous_fst))).continuousAt
  have hR : ∀ i, ContinuousAt
      (fun p : (Fin nL → ℝ) × (Fin nR → ℝ) × ℂ => Complex.arg (p.2.2 - (p.2.1 i : ℂ))) p := fun i =>
    (Complex.continuousAt_arg (mem_slitPlane_of_im_pos (by simpa using hp))).comp
      (continuous_snd.snd.sub
        (Complex.continuous_ofReal.comp ((continuous_apply i).comp continuous_snd.fst))).continuousAt
  unfold meanHarmonic
  refine continuousAt_const.mul (((continuousAt_const.sub (continuousAt_const.mul h0)).sub
    ?_).sub ?_)
  · exact tendsto_finsetSum _ fun i _ => continuousAt_const.mul (hL i)
  · exact tendsto_finsetSum _ fun i _ => continuousAt_const.mul (hR i)

/-- A uniform bound for `meanHarmonic` (every argument lies in `[−π, π]`). -/
def meanHarmonicBound (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : ℝ :=
  |1 / Real.sqrt κ| * (Real.pi * |1 + ∑ i, ρR i| + 2 * Real.pi + (∑ i, |ρL i|) * Real.pi +
    (∑ i, |ρR i|) * Real.pi)

theorem abs_meanHarmonic_le (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (vL : Fin nL → ℝ)
    (vR : Fin nR → ℝ) (w : ℂ) : |meanHarmonic κ ρL ρR vL vR w| ≤ meanHarmonicBound κ ρL ρR := by
  have hπ := Real.pi_pos.le
  have hA : ∀ x : ℂ, |Complex.arg x| ≤ Real.pi := Complex.abs_arg_le_pi
  have hsL : |∑ i, ρL i * Complex.arg (w - vL i)| ≤ (∑ i, |ρL i|) * Real.pi := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hA _) (abs_nonneg _)
  have hsR : |∑ i, ρR i * Complex.arg (w - vR i)| ≤ (∑ i, |ρR i|) * Real.pi := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hA _) (abs_nonneg _)
  unfold meanHarmonic meanHarmonicBound
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h1 : |Real.pi * (1 + ∑ i, ρR i)| = Real.pi * |1 + ∑ i, ρR i| := by
    rw [abs_mul, abs_of_nonneg hπ]
  have h2 : |2 * Complex.arg w| ≤ 2 * Real.pi := by
    rw [abs_mul, abs_two]; linarith [hA w]
  have e1 := abs_sub (Real.pi * (1 + ∑ i, ρR i) - 2 * Complex.arg w -
    ∑ i, ρL i * Complex.arg (w - vL i)) (∑ i, ρR i * Complex.arg (w - vR i))
  have e2 := abs_sub (Real.pi * (1 + ∑ i, ρR i) - 2 * Complex.arg w)
    (∑ i, ρL i * Complex.arg (w - vL i))
  have e3 := abs_sub (Real.pi * (1 + ∑ i, ρR i)) (2 * Complex.arg w)
  rw [h1] at e3
  linarith

/-! ### The explicit mean along a path -/

/-- **The explicit mean** `𝔥_s(z) = meanHarmonic(V̂_s)(f_s z) − χ arg f_s'(z)` along the path `w` with marks
`vL`, `vR` (centred at `w s`). -/
def meanCan (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (s : ℝ≥0) (z : ℂ) : ℝ :=
  meanHarmonic κ ρL ρR (fun i => vL i s - w s) (fun i => vR i s - w s) (fwdMap (rpath w) s z) -
    chiC κ * (logDerivFwd (rpath w) s z).im

section Path

variable {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ}
  {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {K : Set ℂ} {δ N : ℝ} {σ₀ r s : ℝ≥0} {z : ℂ}

theorem IsSafeAt.continuous_clampDrv (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (h : IsSafeAt K δ N σ₀ ζ w r) : Continuous (clampDrv (rpath w) r) :=
  Ito.continuous_clampDrv r.coe_nonneg (continuousOn_rpath hw h.1)

/-- A set safe at `r` is protected up to `r` for the clamped driver. -/
theorem IsSafeAt.isProtected (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hKH : K ⊆ H)
    (h : IsSafeAt K δ N σ₀ ζ w r) : IsProtected (clampDrv (rpath w) r) r δ K := fun z hz =>
  ⟨mem_diff_fwdHull_clampDrv r.coe_nonneg (continuousOn_rpath hw h.1) (hKH hz) (h.2.2.2 z hz).1,
    by rw [fwdMap_clampDrv_of_le le_rfl]; exact (h.2.2.2 z hz).2⟩

theorem IsSafeAt.le_im_fwdMap (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hKH : K ⊆ H)
    (h : IsSafeAt K δ N σ₀ ζ w r) (hs : s ≤ r) (hz : z ∈ K) : δ ≤ (fwdMap (rpath w) s z).im := by
  have hsI : (s : ℝ) ∈ Icc 0 (r : ℝ) := ⟨s.coe_nonneg, by exact_mod_cast hs⟩
  rw [← fwdMap_clampDrv_of_le hsI.2]
  exact (h.isProtected hw hKH).le_im (h.continuous_clampDrv hw) r.coe_nonneg hsI hz

theorem IsSafeAt.continuousOn_fwdMap (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hKH : K ⊆ H)
    (h : IsSafeAt K δ N σ₀ ζ w r) (hs : s ≤ r) : ContinuousOn (fwdMap (rpath w) s) K := by
  have hsI : (s : ℝ) ∈ Icc 0 (r : ℝ) := ⟨s.coe_nonneg, by exact_mod_cast hs⟩
  exact ((h.isProtected hw hKH).continuousOn_fwdMap (h.continuous_clampDrv hw) hsI).congr
    fun z _ => (fwdMap_clampDrv_of_le hsI.2).symm

theorem IsSafeAt.continuousOn_logDerivFwd (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hKH : K ⊆ H)
    (h : IsSafeAt K δ N σ₀ ζ w r) (hs : s ≤ r) : ContinuousOn (logDerivFwd (rpath w) s) K := by
  have hsI : (s : ℝ) ∈ Icc 0 (r : ℝ) := ⟨s.coe_nonneg, by exact_mod_cast hs⟩
  have hc : ContinuousOn (logDerivFwd (clampDrv (rpath w) r) s) K := fun z hz =>
    (continuousAt_logDerivFwd (h.continuous_clampDrv hw) hsI.1
      ((h.isProtected hw hKH).mem_of_le hsI hz)).continuousWithinAt
  exact hc.congr fun z _ => (logDerivFwd_clampDrv_of_le hsI.1 hsI.2).symm

theorem IsSafeAt.alive (hKH : K ⊆ H) (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (h : IsSafeAt K δ N σ₀ ζ w r) (hs : s ≤ r) (hz : z ∈ K) :
    ∃ u, IsForwardSol (rpath w) z s u :=
  ((h.anti hw hKH hs).2.2.2 z hz).1

/-- The explicit mean equals the frozen `couplingMean` at a point of a safe set. -/
theorem couplingMean_eq_meanCan (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hKH : K ⊆ H)
    (h : IsSafeAt K δ N σ₀ ζ w r) (hδ : 0 < δ) (hs : s ≤ r) (hz : z ∈ K)
    (hvL : ∀ i, vL i s ≤ w s) (hvR : ∀ i, w s ≤ vR i s) {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => vL i s - w s) (fun i => vR i s - w s))
      (forceJumpSet (fun i => vL i s - w s) (fun i => vR i s - w s)) u) :
    couplingMean κ (rpath w) s u z = meanCan κ ρL ρR w vL vR s z := by
  have hH : fwdMap (rpath w) s z ∈ H := by
    show 0 < (fwdMap (rpath w) s z).im
    exact hδ.trans_le (h.le_im_fwdMap hw hKH hs hz)
  exact couplingMean_eq_meanHarmonic (fun i => sub_nonpos.2 (hvL i)) (fun i => sub_nonneg.2 (hvR i))
    hu hH

theorem IsSafeAt.continuousOn_meanCan_space (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hKH : K ⊆ H) (h : IsSafeAt K δ N σ₀ ζ w r) (hδ : 0 < δ) (hs : s ≤ r) :
    ContinuousOn (meanCan κ ρL ρR w vL vR s) K := by
  have hf := h.continuousOn_fwdMap hw hKH hs
  have hL := h.continuousOn_logDerivFwd hw hKH hs
  set a : Fin nL → ℝ := fun i => vL i s - w s
  set b : Fin nR → ℝ := fun i => vR i s - w s
  have hp : ContinuousOn (fun z : ℂ => ((a, b, fwdMap (rpath w) s z) :
      (Fin nL → ℝ) × (Fin nR → ℝ) × ℂ)) K :=
    continuousOn_const.prodMk (continuousOn_const.prodMk hf)
  have hmaps : MapsTo (fun z : ℂ => ((a, b, fwdMap (rpath w) s z) :
      (Fin nL → ℝ) × (Fin nR → ℝ) × ℂ)) K {p | 0 < p.2.2.im} := fun z hz =>
    hδ.trans_le (h.le_im_fwdMap hw hKH hs hz)
  have hmh := (continuousOn_meanHarmonic_prod κ ρL ρR).comp hp hmaps
  have hL' : ContinuousOn (fun z => chiC κ * (logDerivFwd (rpath w) s z).im) K :=
    continuousOn_const.mul (Complex.continuous_im.comp_continuousOn hL)
  exact hmh.sub hL'

theorem IsSafeAt.continuousOn_meanCan_time (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hvLc : ∀ i, ContinuousOn (vL i) {t | (t : ℝ≥0∞) < ζ})
    (hvRc : ∀ i, ContinuousOn (vR i) {t | (t : ℝ≥0∞) < ζ}) (hKH : K ⊆ H)
    (h : IsSafeAt K δ N σ₀ ζ w r) (hδ : 0 < δ) (hz : z ∈ K) :
    ContinuousOn (fun s => meanCan κ ρL ρR w vL vR s z) (Iic r) := by
  have hIic : Iic r ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} := fun t ht =>
    lt_of_le_of_lt (by exact_mod_cast (mem_Iic.1 ht)) h.1
  have hcoe : MapsTo (fun s : ℝ≥0 => (s : ℝ)) (Iic r) (Icc 0 (r : ℝ)) := fun s hs =>
    ⟨s.coe_nonneg, by exact_mod_cast (mem_Iic.1 hs)⟩
  have hsol := (h.2.2.2 z hz).1
  have hrw := continuousOn_rpath hw h.1
  have hf : ContinuousOn (fun s : ℝ≥0 => fwdMap (rpath w) s z) (Iic r) :=
    (continuousOn_fwdMap_of_continuousOn r.coe_nonneg hrw (hKH hz) hsol).comp
      NNReal.continuous_coe.continuousOn hcoe
  have hL : ContinuousOn (fun s : ℝ≥0 => logDerivFwd (rpath w) s z) (Iic r) :=
    (continuousOn_logDerivFwd_of_continuousOn r.coe_nonneg hrw (hKH hz) hsol).comp
      NNReal.continuous_coe.continuousOn hcoe
  have hwI := hw.mono hIic
  have hvL : ContinuousOn (fun s => fun i => vL i s - w s) (Iic r) :=
    continuousOn_pi.2 fun i => ((hvLc i).mono hIic).sub hwI
  have hvR : ContinuousOn (fun s => fun i => vR i s - w s) (Iic r) :=
    continuousOn_pi.2 fun i => ((hvRc i).mono hIic).sub hwI
  have hmh := (continuousOn_meanHarmonic_prod κ ρL ρR).comp (hvL.prodMk (hvR.prodMk hf))
    fun s hs => hδ.trans_le (h.le_im_fwdMap hw hKH (mem_Iic.1 hs) hz)
  exact hmh.sub (continuousOn_const.mul (Complex.continuous_im.comp_continuousOn hL))

/-- `|arg f_s'(z)| ≤ 2 s / δ²` while `Im f ≥ δ`. -/
theorem IsSafeAt.norm_logDerivFwd_le (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hKH : K ⊆ H)
    (h : IsSafeAt K δ N σ₀ ζ w r) (hδ : 0 < δ) (hs : s ≤ r) (hz : z ∈ K) :
    ‖logDerivFwd (rpath w) s z‖ ≤ 2 / δ ^ 2 * s := by
  rw [logDerivFwd, norm_neg]
  have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (s : ℝ))
    (C := 2 / δ ^ 2) (f := fun u => 2 / fwdMap (rpath w) u z ^ 2) fun u hu => by
      rw [uIoc_of_le s.coe_nonneg] at hu
      have hu' : u.toNNReal ≤ r := by
        rw [Real.toNNReal_le_iff_le_coe]; exact hu.2.trans (by exact_mod_cast hs)
      have := h.le_im_fwdMap hw hKH hu' hz
      rw [Real.coe_toNNReal _ hu.1.le] at this
      exact norm_two_div_sq_le hδ this
  rw [sub_zero, abs_of_nonneg s.coe_nonneg] at h1
  linarith

theorem IsSafeAt.abs_meanCan_le (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hKH : K ⊆ H)
    (h : IsSafeAt K δ N σ₀ ζ w r) (hδ : 0 < δ) (hs : s ≤ r) (hz : z ∈ K) :
    |meanCan κ ρL ρR w vL vR s z| ≤
      meanHarmonicBound κ ρL ρR + |chiC κ| * (2 / δ ^ 2 * r) := by
  have hL := h.norm_logDerivFwd_le hw hKH hδ hs hz
  have hsr : (s : ℝ) ≤ r := by exact_mod_cast hs
  unfold meanCan
  refine (abs_sub _ _).trans (add_le_add (abs_meanHarmonic_le _ _ _ _ _ _) ?_)
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  refine (Complex.abs_im_le_norm _).trans (hL.trans ?_)
  exact mul_le_mul_of_nonneg_left hsr (by positivity)

/-- The integrand `𝔥_s φ` is measurable in space (continuous on `supp φ`, zero off it). -/
theorem IsSafeAt.aestronglyMeasurable_meanCan_mul {φ : ℂ → ℝ} (hφc : Continuous φ)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hKH : tsupport φ ⊆ H)
    (h : IsSafeAt (tsupport φ) δ N σ₀ ζ w r) (hδ : 0 < δ) (hs : s ≤ r) :
    AEStronglyMeasurable (fun z => meanCan κ ρL ρR w vL vR s z * φ z) volume := by
  have hc : ContinuousOn (fun z => meanCan κ ρL ρR w vL vR s z * φ z) (tsupport φ) :=
    (h.continuousOn_meanCan_space hw hKH hδ hs).mul hφc.continuousOn
  have e : (fun z => meanCan κ ρL ρR w vL vR s z * φ z) =
      (tsupport φ).piecewise (fun z => meanCan κ ρL ρR w vL vR s z * φ z) fun _ => 0 := by
    funext z
    by_cases hz : z ∈ tsupport φ
    · simp [Set.piecewise, hz]
    · simp [Set.piecewise, hz, image_eq_zero_of_notMem_tsupport hz]
  rw [e]
  exact (hc.measurable_piecewise continuousOn_const (isClosed_tsupport φ).measurableSet).aestronglyMeasurable

/-- **The tested mean is continuous in time** up to a safe time. -/
theorem IsSafeAt.continuousOn_meanInt {φ : ℂ → ℝ} (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hvLc : ∀ i, ContinuousOn (vL i) {t | (t : ℝ≥0∞) < ζ})
    (hvRc : ∀ i, ContinuousOn (vR i) {t | (t : ℝ≥0∞) < ζ}) (hKH : tsupport φ ⊆ H)
    (h : IsSafeAt (tsupport φ) δ N σ₀ ζ w r) (hδ : 0 < δ) :
    ContinuousOn (fun s => ∫ z, meanCan κ ρL ρR w vL vR s z * φ z) (Iic r) := by
  set C := meanHarmonicBound κ ρL ρR + |chiC κ| * (2 / δ ^ 2 * r)
  refine continuousOn_of_dominated (bound := fun z => C * |φ z|)
    (fun s hs => h.aestronglyMeasurable_meanCan_mul hφc hw hKH hδ (mem_Iic.1 hs))
    (fun s hs => ae_of_all _ fun z => ?_)
    ((hφc.integrable_of_hasCompactSupport hφs).abs.const_mul C) (ae_of_all _ fun z => ?_)
  · rw [Real.norm_eq_abs, abs_mul]
    by_cases hz : z ∈ tsupport φ
    · exact mul_le_mul_of_nonneg_right (h.abs_meanCan_le hw hKH hδ (mem_Iic.1 hs) hz) (abs_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport hz]
  · by_cases hz : z ∈ tsupport φ
    · exact (h.continuousOn_meanCan_time hw hvLc hvRc hKH hδ hz).mul continuousOn_const
    · simp only [image_eq_zero_of_notMem_tsupport hz, mul_zero]
      exact continuousOn_const

/-! ### The energy is Lipschitz in time -/

theorem loewnerGreenEnergy_clampDrv_of_le {W : ℝ → ℝ} {T t : ℝ} (ht : t ≤ T) (φ : ℂ → ℝ) :
    loewnerGreenEnergy (clampDrv W T) t φ = loewnerGreenEnergy W t φ := by
  unfold loewnerGreenEnergy
  simp only [fwdMap_clampDrv_of_le ht]

/-- `|E_p(φ) − E_q(φ)| ≤ (q − p) ((2/δ) ∫|φ|)²` for `p ≤ q ≤ r` up to a safe time `r`. -/
theorem IsSafeAt.abs_loewnerGreenEnergy_sub_le {φ : ℂ → ℝ} (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hKH : tsupport φ ⊆ H)
    (h : IsSafeAt (tsupport φ) δ N σ₀ ζ w r) (hδ : 0 < δ) {p q : ℝ≥0} (hpq : p ≤ q) (hqr : q ≤ r) :
    |loewnerGreenEnergy (rpath w) p φ - loewnerGreenEnergy (rpath w) q φ| ≤
      (q - p : ℝ) * (2 / δ * ∫ z, |φ z|) ^ 2 := by
  have hc := h.continuous_clampDrv hw
  have hprot := h.isProtected hw hKH
  have hpq' : (p : ℝ) ≤ q := by exact_mod_cast hpq
  have hqr' : (q : ℝ) ≤ r := by exact_mod_cast hqr
  have e := loewnerGreenEnergy_sub_eq_integral hφc hφs hprot hc r.coe_nonneg hδ p.coe_nonneg hpq' hqr'
  rw [loewnerGreenEnergy_clampDrv_of_le (hpq'.trans hqr'), loewnerGreenEnergy_clampDrv_of_le hqr']
    at e
  rw [e]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (p : ℝ)) (b := (q : ℝ))
    (C := (2 / δ * ∫ z, |φ z|) ^ 2)
    (f := fun u => (∫ z, φ z * kCoef (clampDrv (rpath w) r) u z) ^ 2) fun u hu => by
      rw [uIoc_of_le hpq'] at hu
      have huI : u ∈ Icc 0 (r : ℝ) := ⟨p.coe_nonneg.trans hu.1.le, hu.2.trans hqr'⟩
      have h1 := abs_integral_mul_kCoef_le hφc hφs hprot hc r.coe_nonneg hδ huI
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hpq')] at hb
  linarith

/-- **The energy is continuous in time** up to a safe time. -/
theorem IsSafeAt.continuousOn_loewnerGreenEnergy {φ : ℂ → ℝ} (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hKH : tsupport φ ⊆ H)
    (h : IsSafeAt (tsupport φ) δ N σ₀ ζ w r) (hδ : 0 < δ) :
    ContinuousOn (fun s : ℝ≥0 => loewnerGreenEnergy (rpath w) s φ) (Iic r) := by
  set M := (2 / δ * ∫ z, |φ z|) ^ 2
  refine (LipschitzOnWith.of_dist_le_mul (K := M.toNNReal) fun x hx y hy => ?_).continuousOn
  rw [Real.dist_eq, NNReal.dist_eq, Real.coe_toNNReal _ (sq_nonneg _)]
  rcases le_total x y with hxy | hyx
  · have := h.abs_loewnerGreenEnergy_sub_le hφc hφs hw hKH hδ hxy (mem_Iic.1 hy)
    rw [abs_of_nonpos (sub_nonpos.2 (by exact_mod_cast hxy : (x : ℝ) ≤ y))]
    nlinarith [this]
  · have := h.abs_loewnerGreenEnergy_sub_le hφc hφs hw hKH hδ hyx (mem_Iic.1 hx)
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast hyx : (y : ℝ) ≤ x))]
    nlinarith [this]

end Path

end Coupling

end InteractingSLE
