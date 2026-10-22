import HigherDimLQGMetric.LogEnergy.CM
import Mathlib.Analysis.Distribution.FourierMultiplier

/-!
# A quantitative Fourier energy bound

Plancherel and the Fourier multiplier formula for the Laplacian bound the
positive homogeneous Sobolev energy by two ordinary squared integrals.
-/

set_option autoImplicit false
noncomputable section
open FourierTransform MeasureTheory
open scoped SchwartzMap FourierTransform Laplacian
open scoped LineDeriv
open scoped ENNReal
open HigherDimLFPP (Rd)
namespace HigherDimLQGMetric
variable {d : ℕ}

private theorem fourier_laplacian (f : 𝓢(Rd d, ℂ)) (ζ : Rd d) :
    𝓕 (Δ f) ζ = -((2 * Real.pi) ^ 2 * ‖ζ‖ ^ 2 : ℝ) • 𝓕 f ζ := by
  rw [SchwartzMap.laplacian_eq_fourierMultiplierCLM]
  rw [SchwartzMap.fourierMultiplierCLM_apply, fourier_smul, fourier_fourierInv_eq]
  have hg : (fun x : Rd d => ‖x‖ ^ 2).HasTemperateGrowth := by fun_prop
  change (-(2 * Real.pi) ^ 2 : ℝ) •
    ((SchwartzMap.smulLeftCLM ℂ (fun x : Rd d => ‖x‖ ^ 2)) (𝓕 f) ζ) =
    -((2 * Real.pi) ^ 2 * ‖ζ‖ ^ 2 : ℝ) • 𝓕 f ζ
  rw [SchwartzMap.smulLeftCLM_apply_apply hg]
  simp [mul_smul]

/-- The iterated Laplacian on complex Schwartz functions. -/
def iterLap {d : ℕ} : ℕ → 𝓢(Rd d, ℂ) → 𝓢(Rd d, ℂ)
  | 0, f => f
  | m + 1, f => Δ (iterLap m f)

private theorem fourier_iterLap (m : ℕ) (f : 𝓢(Rd d, ℂ)) (ζ : Rd d) :
    𝓕 (iterLap m f) ζ =
      (-(2 * Real.pi) ^ 2 * ‖ζ‖ ^ 2 : ℝ) ^ m • 𝓕 f ζ := by
  induction m with
  | zero => simp [iterLap]
  | succ m ih =>
    let a : ℝ := -(2 * Real.pi) ^ 2 * ‖ζ‖ ^ 2
    change 𝓕 (Δ (iterLap m f)) ζ = a ^ (m + 1) • 𝓕 f ζ
    rw [fourier_laplacian, ih]
    have ha : -((2 * Real.pi) ^ 2 * ‖ζ‖ ^ 2) =
        (-(2 * Real.pi) ^ 2 * ‖ζ‖ ^ 2 : ℝ) := by ring
    rw [ha]
    change a • (a ^ m • 𝓕 f ζ) = a ^ (m + 1) • 𝓕 f ζ
    rw [smul_smul, pow_succ']

private theorem pow_le_one_add_pow {t : ℝ} (ht : 0 ≤ t) {d m : ℕ} (hdm : d ≤ 4 * m) :
    t ^ d ≤ 1 + t ^ (4 * m) := by
  by_cases h : t ≤ 1
  · exact (pow_le_one₀ ht h).trans (le_add_of_nonneg_right (pow_nonneg ht _))
  · have h1 : 1 ≤ t := le_of_not_ge h
    exact (pow_le_pow_right₀ h1 hdm).trans (le_add_of_nonneg_left zero_le_one)

private theorem fourier_energy_pointwise (f : 𝓢(Rd d, ℂ)) (m : ℕ)
    (hdm : d ≤ 4 * m) (ζ : Rd d) :
    ‖ζ‖ ^ d * ‖𝓕 f ζ‖ ^ 2 ≤
      ‖𝓕 f ζ‖ ^ 2 + ‖𝓕 (iterLap m f) ζ‖ ^ 2 := by
  have hpow := pow_le_one_add_pow (norm_nonneg ζ) hdm
  have hπ : 1 ≤ (2 * Real.pi) ^ 2 := by
    nlinarith [Real.one_le_pi_div_two, Real.pi_pos]
  have hA : 1 ≤ ((2 * Real.pi) ^ 2) ^ (2 * m) := one_le_pow₀ hπ
  have hn : ‖𝓕 (iterLap m f) ζ‖ ^ 2 =
      ((2 * Real.pi) ^ 2) ^ (2 * m) *
        (‖ζ‖ ^ (4 * m) * ‖𝓕 f ζ‖ ^ 2) := by
    rw [fourier_iterLap, norm_smul, Real.norm_eq_abs]
    have hcoeff : |(-(2 * Real.pi) ^ 2 * ‖ζ‖ ^ 2) ^ m| =
        ((2 * Real.pi) ^ 2 * ‖ζ‖ ^ 2) ^ m := by
      rw [abs_pow, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg _),
        abs_of_nonneg (sq_nonneg _)]
    rw [hcoeff, mul_pow, mul_pow]
    ring
  calc
    ‖ζ‖ ^ d * ‖𝓕 f ζ‖ ^ 2 ≤
        (1 + ‖ζ‖ ^ (4 * m)) * ‖𝓕 f ζ‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hpow (sq_nonneg _)
    _ = ‖𝓕 f ζ‖ ^ 2 +
        ‖ζ‖ ^ (4 * m) * ‖𝓕 f ζ‖ ^ 2 := by ring
    _ ≤ ‖𝓕 f ζ‖ ^ 2 + ‖𝓕 (iterLap m f) ζ‖ ^ 2 := by
      rw [hn]
      have hpos : 0 ≤ ‖ζ‖ ^ (4 * m) * ‖𝓕 f ζ‖ ^ 2 := by positivity
      nlinarith

/-- The Fourier energy of order `d` is bounded by the ordinary energies of
`f` and `Δ^m f` whenever `4m ≥ d`. -/
theorem fourier_energy_le_iterLap (f : 𝓢(Rd d, ℂ)) (m : ℕ)
    (hdm : d ≤ 4 * m) :
    (∫ ζ : Rd d, ‖ζ‖ ^ d * ‖𝓕 f ζ‖ ^ 2) ≤
      (∫ x : Rd d, ‖f x‖ ^ 2) +
        (∫ x : Rd d, ‖iterLap m f x‖ ^ 2) := by
  have hf : Integrable (fun ζ : Rd d => ‖𝓕 f ζ‖ ^ 2) :=
    ((𝓕 f).memLp 2 volume).integrable_norm_pow (by norm_num)
  have hl : Integrable (fun ζ : Rd d => ‖𝓕 (iterLap m f) ζ‖ ^ 2) :=
    ((𝓕 (iterLap m f)).memLp 2 volume).integrable_norm_pow (by norm_num)
  have hdom : Integrable (fun ζ : Rd d =>
      ‖𝓕 f ζ‖ ^ 2 + ‖𝓕 (iterLap m f) ζ‖ ^ 2) := hf.add hl
  have hw : Integrable (fun ζ : Rd d => ‖ζ‖ ^ d * ‖𝓕 f ζ‖ ^ 2) :=
    Integrable.mono' hdom (by fun_prop) (ae_of_all _ fun ζ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact fourier_energy_pointwise f m hdm ζ)
  calc
    _ ≤ ∫ ζ : Rd d, (‖𝓕 f ζ‖ ^ 2 + ‖𝓕 (iterLap m f) ζ‖ ^ 2) :=
      integral_mono hw hdom (fourier_energy_pointwise f m hdm)
    _ = (∫ ζ : Rd d, ‖𝓕 f ζ‖ ^ 2) +
        (∫ ζ : Rd d, ‖𝓕 (iterLap m f) ζ‖ ^ 2) :=
      integral_add hf hl
    _ = _ := by
      rw [SchwartzMap.integral_norm_sq_fourier f,
        SchwartzMap.integral_norm_sq_fourier (iterLap m f)]

private theorem tsupport_finsetSum_subset {ι X : Type*} [TopologicalSpace X]
    [DecidableEq ι] (s : Finset ι) (f : ι → X → ℂ) (S : Set X)
    (hf : ∀ i ∈ s, tsupport (f i) ⊆ S) :
    tsupport (fun x => ∑ i ∈ s, f i x) ⊆ S := by
  induction s using Finset.induction_on with
  | empty =>
    change tsupport (0 : X → ℂ) ⊆ S
    simp only [tsupport_zero, Set.empty_subset]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (tsupport_add (f i) (fun x => ∑ j ∈ s, f j x)).trans
      (Set.union_subset (hf i (Finset.mem_insert_self i s))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))))

private theorem tsupport_laplacian_subset (f : 𝓢(Rd d, ℂ)) :
    tsupport ((Δ f : 𝓢(Rd d, ℂ)) : Rd d → ℂ) ⊆ tsupport (f : Rd d → ℂ) := by
  let b := stdOrthonormalBasis ℝ (Rd d)
  have heq : ((Δ f : 𝓢(Rd d, ℂ)) : Rd d → ℂ) =
      fun x => ∑ i : Fin (Module.finrank ℝ (Rd d)), (∂_{b i} (∂_{b i} f)) x := by
    funext x
    rw [SchwartzMap.laplacian_eq_sum b f, sum_apply]
  rw [heq]
  apply tsupport_finsetSum_subset
  intro i hi
  exact (SchwartzMap.tsupport_lineDerivOp_subset (b i) (∂_{b i} f)).trans
    (SchwartzMap.tsupport_lineDerivOp_subset (b i) f)

/-- Iterating the Laplacian does not enlarge the support. -/
theorem tsupport_iterLap_subset (m : ℕ) (f : 𝓢(Rd d, ℂ)) :
    tsupport (iterLap m f : Rd d → ℂ) ⊆ tsupport (f : Rd d → ℂ) := by
  induction m with
  | zero => simp [iterLap]
  | succ m ih =>
    change tsupport ((Δ (iterLap m f) : 𝓢(Rd d, ℂ)) : Rd d → ℂ) ⊆
      tsupport (f : Rd d → ℂ)
    exact (tsupport_laplacian_subset (iterLap m f)).trans ih

/-- A pointwise bound on a Schwartz function with support in a finite-volume
set bounds its squared integral. -/
theorem integral_norm_sq_le_of_support (f : 𝓢(Rd d, ℂ))
    (S : Set (Rd d)) (hS : MeasurableSet S) (hfin : volume S ≠ ∞)
    (hs : tsupport (f : Rd d → ℂ) ⊆ S)
    {M : ℝ} (hb : ∀ x, ‖f x‖ ≤ M) :
    (∫ x : Rd d, ‖f x‖ ^ 2) ≤ (volume S).toReal * M ^ 2 := by
  have hf : Integrable (fun x : Rd d => ‖f x‖ ^ 2) :=
    (f.memLp 2 volume).integrable_norm_pow (by norm_num)
  have hg : Integrable (S.indicator fun _ : Rd d => M ^ 2) :=
    (integrable_indicator_iff hS).2 (integrableOn_const hfin)
  have hbound (x : Rd d) :
      ‖f x‖ ^ 2 ≤ S.indicator (fun _ : Rd d => M ^ 2) x := by
    by_cases hx : x ∈ S
    · simp only [Set.indicator_of_mem hx]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb x) 2
    · have hz : f x = 0 := by
        by_contra hne
        have hmem : x ∈ tsupport (f : Rd d → ℂ) :=
          subset_closure (by simpa [Function.mem_support] using hne)
        exact hx (hs hmem)
      simp [Set.indicator, hx, hz]
  calc
    _ ≤ ∫ x : Rd d, S.indicator (fun _ : Rd d => M ^ 2) x :=
      integral_mono hf hg hbound
    _ = (volume S).toReal * M ^ 2 := by
      rw [integral_indicator_const (M ^ 2) hS]
      simp only [Measure.real]
      rw [smul_eq_mul]

end HigherDimLQGMetric
