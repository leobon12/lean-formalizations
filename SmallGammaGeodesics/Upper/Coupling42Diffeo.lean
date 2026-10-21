import SmallGammaGeodesics.Upper.Interfaces
import SmallGammaGeodesics.Probes.Bounds
import SmallGammaGeodesics.NIC.Transport
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Lemma 4.2′, Steps 1–2: the global extension of the probe map (blueprint `lem:coupling`)

For `|θ| ≤ ε₁ ℓ_j` the probe map `ϕ = z + iθH_{j,a}` is extended to a global near-identity
diffeomorphism
`Φ(z) = z + c_j(z) · iθH_{j,a}(z)`, `c_j(z) = χ(Re z − 1/2) χ(2 Im z/ℓ_j)`,
with `‖DΦ − I‖ ≤ C₃|θ|/ℓ_j` everywhere (`norm_fderiv_pert_le`), `Φ = id` off a compact set, and
`Φ = ϕ` on the open rectangle `R_j = {|Re z − 1/2| < 1, |Im z| < ℓ_j/2}`, where `c_j = 1`.
The inverse `Ψ = Φ⁻¹` exists because `Φ − id` is a contraction (`ApproximatesLinearOn.toHomeomorph`),
is `C^∞` by the inverse function theorem (`Homeomorph.contDiff_symm`), maps `U_j` into `R_j`, and is
holomorphic on `U_j` (`HasDerivAt.of_local_left_inverse`). Hence `CC.IsNearIdDiffeo Φ Ψ U_j (C₃|θ|/ℓ_j)`
(`isNearIdDiffeo_extMap`).

The cutoff here is `χ(Re z − 1/2) χ(2 Im z/ℓ)` with P-B1's `χ` (`= 1` on `[-1, 1]`, `= 0` off
`(-2, 2)`), instead of the blueprint's `χ₁(Re z) χ₂(Im z/ℓ)`; only `c = 1` on a neighbourhood of
`Ψ(U_j)` and `c = 0` off the closed strip `|Im z| ≤ ℓ_j` are used.

Consequences for Lemma 4.2′:
* `transport_eq_of_probe` : the pullback of (b3) (`|ϕ'|² f ∘ ϕ` on the strip, `0` off it) is the NIC
  transport `|det DΦ| · f ∘ Φ`, for every `f` supported in `U_j`;
* `probeInv_eq_extInv` : `probeInv = Ψ` on `U_j`;
* `extInv_lipschitz`, `extInv_antilipschitz` : `Ψ` is bi-Lipschitz with constants `2`, `1/2`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal NNReal

namespace SmallGammaGeodesics

namespace Coupling42

open LQGMetric

/-! ## Definitions -/

/-- the cutoff `c_j(z) = χ(Re z − 1/2) χ(2 Im z/ℓ_j)` -/
def cut (j : ℕ) (z : ℂ) : ℝ := chi (z.re - 1 / 2) * chi (2 * z.im / ell j)

/-- the perturbation `g(z) = c_j(z) · iθH_{j,a}(z)` -/
def pert (j : ℕ) (a θ : ℝ) (z : ℂ) : ℂ := cut j z • (Complex.I * θ * probeH j a z)

/-- the global extension `Φ = id + g` of the probe map -/
def extMap (j : ℕ) (a θ : ℝ) (z : ℂ) : ℂ := z + pert j a θ z

/-- its inverse (the classical inverse; `extInv_extMap`, `extMap_extInv` under the smallness
condition) -/
def extInv (j : ℕ) (a θ : ℝ) : ℂ → ℂ := Function.invFun (extMap j a θ)

/-- the rectangle `R_j = {|Re z − 1/2| < 1, |Im z| < ℓ_j/2}` on which `Φ = ϕ` -/
def rectR (j : ℕ) : Set ℂ := {z | |z.re - 1 / 2| < 1 ∧ |z.im| < ell j / 2}

/-! ## The cutoff -/

theorem cut_nonneg (j : ℕ) (z : ℂ) : 0 ≤ cut j z :=
  mul_nonneg (chi_nonneg _) (chi_nonneg _)

theorem cut_le_one (j : ℕ) (z : ℂ) : cut j z ≤ 1 :=
  calc cut j z ≤ 1 * 1 :=
        mul_le_mul (chi_le_one _) (chi_le_one _) (chi_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem abs_cut_le_one (j : ℕ) (z : ℂ) : |cut j z| ≤ 1 := by
  rw [abs_of_nonneg (cut_nonneg j z)]; exact cut_le_one j z

theorem cut_eq_one {j : ℕ} {z : ℂ} (h1 : |z.re - 1 / 2| ≤ 1) (h2 : |z.im| ≤ ell j / 2) :
    cut j z = 1 := by
  have hℓ := ell_pos j
  have h2' : |2 * z.im / ell j| ≤ 1 := by
    rw [abs_div, abs_mul, abs_two, abs_of_pos hℓ, div_le_one hℓ]
    linarith
  rw [cut, chi_eq_one h1, chi_eq_one h2', mul_one]

theorem two_le_abs_of_le_abs_im {j : ℕ} {z : ℂ} (h : ell j ≤ |z.im|) :
    2 ≤ |2 * z.im / ell j| := by
  have hℓ := ell_pos j
  rw [abs_div, abs_mul, abs_two, abs_of_pos hℓ, le_div_iff₀ hℓ]
  linarith

theorem cut_eq_zero_of_le_abs_im {j : ℕ} {z : ℂ} (h : ell j ≤ |z.im|) : cut j z = 0 := by
  rw [cut, chi_eq_zero (two_le_abs_of_le_abs_im h), mul_zero]

theorem cut_eq_zero_of_le_abs_re {j : ℕ} {z : ℂ} (h : 2 ≤ |z.re - 1 / 2|) : cut j z = 0 := by
  rw [cut, chi_eq_zero h, zero_mul]

theorem isOpen_rectR (j : ℕ) : IsOpen (rectR j) := by
  have h1 : IsOpen {z : ℂ | |z.re - 1 / 2| < 1} :=
    isOpen_lt ((Complex.continuous_re.sub continuous_const).abs) continuous_const
  have h2 : IsOpen {z : ℂ | |z.im| < ell j / 2} :=
    isOpen_lt Complex.continuous_im.abs continuous_const
  exact h1.inter h2

theorem cut_eq_one_of_mem_rectR {j : ℕ} {z : ℂ} (hz : z ∈ rectR j) : cut j z = 1 :=
  cut_eq_one hz.1.le hz.2.le

theorem rectR_subset_probeStrip (j : ℕ) : rectR j ⊆ probeStrip j := fun z hz => by
  have hℓ := ell_pos j
  show |z.im| < ell j
  linarith [hz.2]

theorem extMap_eq_probeMap_of_cut {j : ℕ} {a θ : ℝ} {z : ℂ} (h : cut j z = 1) :
    extMap j a θ z = probeMap j a θ z := by
  rw [extMap, pert, h, one_smul, probeMap]

theorem extMap_eq_probeMap {j : ℕ} {a θ : ℝ} {z : ℂ} (hz : z ∈ rectR j) :
    extMap j a θ z = probeMap j a θ z :=
  extMap_eq_probeMap_of_cut (cut_eq_one_of_mem_rectR hz)

theorem extMap_eventuallyEq_probeMap {j : ℕ} {a θ : ℝ} {z : ℂ} (hz : z ∈ rectR j) :
    extMap j a θ =ᶠ[𝓝 z] probeMap j a θ :=
  Filter.eventually_of_mem ((isOpen_rectR j).mem_nhds hz) fun _ hw => extMap_eq_probeMap hw

/-! ## Bounds on the probe and on `χ'` -/

/-- `‖H‖ ≤ C₀` and `‖H'‖ ≤ C₀/ℓ_j` on the closed strip `|Im z| ≤ ℓ_j`, for every real `a`. -/
theorem probeH_strip_bounds : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (j : ℕ) (a : ℝ) (z : ℂ), |z.im| ≤ ell j →
    ‖probeH j a z‖ ≤ C₀ ∧ ‖deriv (probeH j a) z‖ ≤ C₀ / ell j := by
  obtain ⟨C, hC0, hC⟩ := norm_iteratedDeriv_probeH_le 1 one_pos
  refine ⟨2 * C, by positivity, fun j a z hz => ⟨?_, ?_⟩⟩
  · have h := hC j a 0 (by norm_num) z (by rw [one_mul]; exact hz)
    rw [iteratedDeriv_zero, pow_zero, mul_one] at h
    calc ‖probeH j a z‖ ≤ C * envelope j a z.re := h
      _ ≤ C * 2 := mul_le_mul_of_nonneg_left (envelope_le_two j a z.re) hC0
      _ = 2 * C := by ring
  · have h := hC j a 1 (by norm_num) z (by rw [one_mul]; exact hz)
    rw [iteratedDeriv_one, pow_one] at h
    have hℓ := ell_pos j
    calc ‖deriv (probeH j a) z‖ ≤ C * (ell j)⁻¹ * envelope j a z.re := h
      _ ≤ C * (ell j)⁻¹ * 2 :=
          mul_le_mul_of_nonneg_left (envelope_le_two j a z.re)
            (mul_nonneg hC0 (inv_nonneg.mpr hℓ.le))
      _ = 2 * C / ell j := by field_simp

/-- the probe constant `C₀` -/
def C0 : ℝ := Classical.choose probeH_strip_bounds

theorem C0_nonneg : 0 ≤ C0 := (Classical.choose_spec probeH_strip_bounds).1

theorem norm_probeH_le {j : ℕ} (a : ℝ) {z : ℂ} (hz : |z.im| ≤ ell j) : ‖probeH j a z‖ ≤ C0 :=
  ((Classical.choose_spec probeH_strip_bounds).2 j a z hz).1

theorem norm_deriv_probeH_le {j : ℕ} (a : ℝ) {z : ℂ} (hz : |z.im| ≤ ell j) :
    ‖deriv (probeH j a) z‖ ≤ C0 / ell j :=
  ((Classical.choose_spec probeH_strip_bounds).2 j a z hz).2

theorem hasCompactSupport_chi : HasCompactSupport chi := chiBump.hasCompactSupport

theorem exists_bound_deriv_chi : ∃ M : ℝ, 0 ≤ M ∧ ∀ s, |deriv chi s| ≤ M := by
  have hc : Continuous (deriv chi) :=
    (contDiff_chi (n := 1)).continuous_deriv le_rfl
  obtain ⟨C, hC⟩ := hasCompactSupport_chi.deriv.exists_bound_of_continuous hc
  exact ⟨max C 0, le_max_right _ _, fun s => (hC s).trans (le_max_left _ _)⟩

/-- the bound `M₁` on `|χ'|` -/
def M1 : ℝ := Classical.choose exists_bound_deriv_chi

theorem M1_nonneg : 0 ≤ M1 := (Classical.choose_spec exists_bound_deriv_chi).1

theorem abs_deriv_chi_le (s : ℝ) : |deriv chi s| ≤ M1 :=
  (Classical.choose_spec exists_bound_deriv_chi).2 s

theorem deriv_chi_eq_zero {s : ℝ} (hs : 2 < |s|) : deriv chi s = 0 := by
  have hev : chi =ᶠ[𝓝 s] fun _ => 0 := by
    have hopen : IsOpen {t : ℝ | 2 < |t|} := isOpen_lt continuous_const continuous_abs
    exact Filter.eventually_of_mem (hopen.mem_nhds hs) fun t ht => chi_eq_zero (le_of_lt ht)
  rw [hev.deriv_eq, deriv_const]

/-! ## The derivative of the perturbation -/

/-- the derivative of the cutoff -/
def cutDeriv (j : ℕ) (z : ℂ) : ℂ →L[ℝ] ℝ :=
  chi (z.re - 1 / 2) • (deriv chi (2 * z.im / ell j) • ((2 / ell j) • Complex.imCLM)) +
    chi (2 * z.im / ell j) • (deriv chi (z.re - 1 / 2) • Complex.reCLM)

theorem differentiable_chi : Differentiable ℝ chi :=
  (contDiff_chi (n := 1)).differentiable (by norm_num)

theorem hasFDerivAt_cut (j : ℕ) (z : ℂ) : HasFDerivAt (cut j) (cutDeriv j z) z := by
  have h1 : HasFDerivAt (fun w : ℂ => chi (w.re - 1 / 2))
      (deriv chi (z.re - 1 / 2) • Complex.reCLM) z := by
    have hre : HasFDerivAt (fun w : ℂ => w.re - 1 / 2) Complex.reCLM z :=
      Complex.reCLM.hasFDerivAt.sub_const _
    exact (differentiable_chi _).hasDerivAt.comp_hasFDerivAt z hre
  have h2 : HasFDerivAt (fun w : ℂ => chi (2 * w.im / ell j))
      (deriv chi (2 * z.im / ell j) • ((2 / ell j) • Complex.imCLM)) z := by
    have him : HasFDerivAt (fun w : ℂ => 2 * w.im / ell j) ((2 / ell j) • Complex.imCLM) z := by
      refine ((2 / ell j) • Complex.imCLM).hasFDerivAt.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun w => ?_)
      change 2 * w.im / ell j = (2 / ell j) • w.im
      rw [smul_eq_mul]
      ring
    exact (differentiable_chi _).hasDerivAt.comp_hasFDerivAt z him
  exact h1.mul h2

theorem abs_chi_le_one (s : ℝ) : |chi s| ≤ 1 := by
  rw [abs_of_nonneg (chi_nonneg s)]; exact chi_le_one s

theorem norm_cutDeriv_le (j : ℕ) (z : ℂ) : ‖cutDeriv j z‖ ≤ 3 * M1 / ell j := by
  have hℓ := ell_pos j
  have hℓ1 := ell_le_one j
  have hM := M1_nonneg
  unfold cutDeriv
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, norm_smul, norm_smul, norm_smul, Complex.reCLM_norm,
    Complex.imCLM_norm]
  simp only [Real.norm_eq_abs]
  have a1 := abs_deriv_chi_le (2 * z.im / ell j)
  have a2 := abs_deriv_chi_le (z.re - 1 / 2)
  have b1 := abs_chi_le_one (z.re - 1 / 2)
  have b2 := abs_chi_le_one (2 * z.im / ell j)
  have e2 : |2 / ell j| = 2 / ell j := abs_of_pos (by positivity)
  rw [e2]
  have hM' : M1 ≤ M1 / ell j := le_div_self hM hℓ hℓ1
  have t1 : |chi (z.re - 1 / 2)| * (|deriv chi (2 * z.im / ell j)| * (2 / ell j * 1)) ≤
      1 * (M1 * (2 / ell j * 1)) :=
    mul_le_mul b1 (mul_le_mul_of_nonneg_right a1 (by positivity)) (by positivity) zero_le_one
  have t2 : |chi (2 * z.im / ell j)| * (|deriv chi (z.re - 1 / 2)| * 1) ≤ 1 * (M1 * 1) :=
    mul_le_mul b2 (mul_le_mul_of_nonneg_right a2 zero_le_one) (by positivity) zero_le_one
  have e3 : 3 * M1 / ell j = 2 * (M1 / ell j) + M1 / ell j := by ring
  have e4 : 1 * (M1 * (2 / ell j * 1)) = 2 * (M1 / ell j) := by ring
  linarith

theorem cutDeriv_eq_zero {j : ℕ} {z : ℂ} (h : ell j < |z.im|) : cutDeriv j z = 0 := by
  have h2 : 2 < |2 * z.im / ell j| := by
    have hℓ := ell_pos j
    rw [abs_div, abs_mul, abs_two, abs_of_pos hℓ, lt_div_iff₀ hℓ]
    linarith
  rw [cutDeriv, chi_eq_zero h2.le, deriv_chi_eq_zero h2]
  simp only [zero_smul, smul_zero, add_zero]

/-- the derivative of the perturbation `g = c · iθH` -/
def pertDeriv (j : ℕ) (a θ : ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  cut j z • (ContinuousLinearMap.toSpanSingleton ℂ
      (Complex.I * θ * deriv (probeH j a) z)).restrictScalars ℝ +
    (cutDeriv j z).smulRight (Complex.I * θ * probeH j a z)

theorem hasFDerivAt_pert (j : ℕ) (a θ : ℝ) (z : ℂ) :
    HasFDerivAt (pert j a θ) (pertDeriv j a θ z) z := by
  have hH : HasDerivAt (fun w => Complex.I * θ * probeH j a w)
      (Complex.I * θ * deriv (probeH j a) z) z :=
    ((differentiable_probeH j a z).hasDerivAt).const_mul _
  exact (hasFDerivAt_cut j z).smul (hH.hasFDerivAt.restrictScalars ℝ)

theorem differentiable_pert (j : ℕ) (a θ : ℝ) : Differentiable ℝ (pert j a θ) :=
  fun z => (hasFDerivAt_pert j a θ z).differentiableAt

/-- the constant `C₃ = C₀ (1 + 3M₁)` of `‖Dg‖ ≤ C₃ |θ|/ℓ_j` -/
def C3 : ℝ := C0 * (1 + 3 * M1)

theorem C3_nonneg : 0 ≤ C3 := mul_nonneg C0_nonneg (by linarith [M1_nonneg])

theorem norm_pertDeriv_le (j : ℕ) (a θ : ℝ) (z : ℂ) :
    ‖pertDeriv j a θ z‖ ≤ C3 * |θ| / ell j := by
  have hℓ := ell_pos j
  have hbound : 0 ≤ C3 * |θ| / ell j := div_nonneg (mul_nonneg C3_nonneg (abs_nonneg θ)) hℓ.le
  rcases le_or_gt |z.im| (ell j) with hz | hz
  · unfold pertDeriv
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, ContinuousLinearMap.norm_restrictScalars,
      ContinuousLinearMap.norm_toSpanSingleton, ContinuousLinearMap.norm_smulRight_apply]
    simp only [Real.norm_eq_abs, norm_mul, Complex.norm_I, one_mul, Complex.norm_real]
    have hH := norm_probeH_le a hz
    have hH' := norm_deriv_probeH_le (j := j) a hz
    have hc := abs_cut_le_one j z
    have hD := norm_cutDeriv_le j z
    have hθ := abs_nonneg θ
    have hC0 := C0_nonneg
    have hM := M1_nonneg
    calc |cut j z| * (|θ| * ‖deriv (probeH j a) z‖) + ‖cutDeriv j z‖ * (|θ| * ‖probeH j a z‖)
        ≤ 1 * (|θ| * (C0 / ell j)) + 3 * M1 / ell j * (|θ| * C0) := by
          refine add_le_add (mul_le_mul hc (mul_le_mul_of_nonneg_left hH' hθ)
            (by positivity) zero_le_one) (mul_le_mul hD (mul_le_mul_of_nonneg_left hH hθ)
            (by positivity) (by positivity))
      _ = C3 * |θ| / ell j := by unfold C3; field_simp
  · unfold pertDeriv
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply, cutDeriv_eq_zero hz,
      cut_eq_zero_of_le_abs_im hz.le, norm_zero, norm_zero, zero_mul, zero_mul, add_zero]
    exact hbound

theorem fderiv_pert (j : ℕ) (a θ : ℝ) (z : ℂ) :
    fderiv ℝ (pert j a θ) z = pertDeriv j a θ z :=
  (hasFDerivAt_pert j a θ z).fderiv

theorem norm_fderiv_pert_le (j : ℕ) (a θ : ℝ) (z : ℂ) :
    ‖fderiv ℝ (pert j a θ) z‖ ≤ C3 * |θ| / ell j := by
  rw [fderiv_pert]; exact norm_pertDeriv_le j a θ z

/-- `g` is `C₃|θ|/ℓ_j`-Lipschitz -/
theorem norm_pert_sub_le (j : ℕ) (a θ : ℝ) (x y : ℂ) :
    ‖pert j a θ x - pert j a θ y‖ ≤ C3 * |θ| / ell j * ‖x - y‖ :=
  convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun z _ => differentiable_pert j a θ z)
    (fun z _ => norm_fderiv_pert_le j a θ z) (mem_univ y) (mem_univ x)

/-- `‖g‖ ≤ C₀|θ|` -/
theorem norm_pert_le (j : ℕ) (a θ : ℝ) (z : ℂ) : ‖pert j a θ z‖ ≤ C0 * |θ| := by
  rcases le_or_gt |z.im| (ell j) with hz | hz
  · rw [pert, norm_smul]
    simp only [Real.norm_eq_abs, norm_mul, Complex.norm_I, one_mul, Complex.norm_real]
    calc |cut j z| * (|θ| * ‖probeH j a z‖) ≤ 1 * (|θ| * C0) :=
          mul_le_mul (abs_cut_le_one j z)
            (mul_le_mul_of_nonneg_left (norm_probeH_le a hz) (abs_nonneg θ))
            (by positivity) zero_le_one
      _ = C0 * |θ| := by ring
  · rw [pert, cut_eq_zero_of_le_abs_im hz.le]
    simp only [zero_smul, norm_zero]
    exact mul_nonneg C0_nonneg (abs_nonneg θ)

/-! ## The smallness threshold -/

/-- P-B1's threshold for the probe map (`probeMap_geometry`) -/
def epsB : ℝ := Classical.choose probeMap_geometry

theorem epsB_pos : 0 < epsB := (Classical.choose_spec probeMap_geometry).1

theorem probeMap_injOn {j : ℕ} {a θ : ℝ} (hθ : |θ| ≤ epsB * ell j) :
    InjOn (probeMap j a θ) (probeStrip j) :=
  ((Classical.choose_spec probeMap_geometry).2 j a θ hθ).2.1

/-- the threshold `ε₁ = min(ε_B, 1/(48(C₃ + 1)))` of the geometry -/
def eps1 : ℝ := min epsB (1 / (48 * (C3 + 1)))

theorem eps1_pos : 0 < eps1 := lt_min epsB_pos (by have := C3_nonneg; positivity)

theorem eps1_le_epsB : eps1 ≤ epsB := min_le_left _ _

theorem C3_mul_eps1_le : C3 * eps1 ≤ 1 / 48 := by
  have h3 := C3_nonneg
  have h : eps1 ≤ 1 / (48 * (C3 + 1)) := min_le_right _ _
  calc C3 * eps1 ≤ (C3 + 1) * (1 / (48 * (C3 + 1))) :=
        mul_le_mul (by linarith) h eps1_pos.le (by linarith)
    _ = 1 / 48 := by field_simp

theorem C0_le_C3 : C0 ≤ C3 := by
  unfold C3
  have := C0_nonneg
  have := M1_nonneg
  nlinarith

section small

variable {j : ℕ} {a θ : ℝ}

/-- `η = C₃|θ|/ℓ_j ≤ 1/48` -/
theorem eta_le (hθ : |θ| ≤ eps1 * ell j) : C3 * |θ| / ell j ≤ 1 / 48 := by
  have hℓ := ell_pos j
  rw [div_le_iff₀ hℓ]
  calc C3 * |θ| ≤ C3 * (eps1 * ell j) := mul_le_mul_of_nonneg_left hθ C3_nonneg
    _ = C3 * eps1 * ell j := by ring
    _ ≤ 1 / 48 * ell j := mul_le_mul_of_nonneg_right C3_mul_eps1_le hℓ.le

theorem eta_nonneg : 0 ≤ C3 * |θ| / ell j :=
  div_nonneg (mul_nonneg C3_nonneg (abs_nonneg θ)) (ell_pos j).le

/-- `C₀|θ| ≤ ℓ_j/48` -/
theorem C0_mul_abs_le (hθ : |θ| ≤ eps1 * ell j) : C0 * |θ| ≤ ell j / 48 := by
  have hℓ := ell_pos j
  have h := eta_le hθ
  rw [div_le_iff₀ hℓ] at h
  have : C0 * |θ| ≤ C3 * |θ| := mul_le_mul_of_nonneg_right C0_le_C3 (abs_nonneg θ)
  linarith

/-! ## The homeomorphism and its smooth inverse -/

/-- `η` as a nonnegative real -/
def etaNN (j : ℕ) (θ : ℝ) : ℝ≥0 := ⟨C3 * |θ| / ell j, eta_nonneg⟩

theorem approximatesLinearOn_extMap (j : ℕ) (a θ : ℝ) :
    ApproximatesLinearOn (extMap j a θ)
      ((ContinuousLinearEquiv.refl ℝ ℂ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) univ (etaNN j θ) := by
  intro x _ y _
  rw [ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.id_apply]
  have e : extMap j a θ x - extMap j a θ y - (x - y) = pert j a θ x - pert j a θ y := by
    unfold extMap; ring
  rw [e]
  exact norm_pert_sub_le j a θ x y

theorem etaNN_lt (hθ : |θ| ≤ eps1 * ell j) :
    etaNN j θ < ‖((ContinuousLinearEquiv.refl ℝ ℂ : ℂ ≃L[ℝ] ℂ).symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ := by
  rw [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl,
    ContinuousLinearMap.nnnorm_id, inv_one]
  rw [← NNReal.coe_lt_coe]
  show C3 * |θ| / ell j < 1
  have := eta_le hθ
  linarith

/-- the homeomorphism `Φ` -/
def extHomeo (j : ℕ) (a θ : ℝ) (hθ : |θ| ≤ eps1 * ell j) : ℂ ≃ₜ ℂ :=
  (approximatesLinearOn_extMap j a θ).toHomeomorph (extMap j a θ) (Or.inr (etaNN_lt hθ))

theorem coe_extHomeo (hθ : |θ| ≤ eps1 * ell j) : (extHomeo j a θ hθ : ℂ → ℂ) = extMap j a θ :=
  rfl

theorem extMap_injective (hθ : |θ| ≤ eps1 * ell j) : Function.Injective (extMap j a θ) := by
  rw [← coe_extHomeo hθ]; exact (extHomeo j a θ hθ).injective

theorem extInv_eq_symm (hθ : |θ| ≤ eps1 * ell j) :
    extInv j a θ = (extHomeo j a θ hθ).symm := by
  funext w
  have h := (extHomeo j a θ hθ).apply_symm_apply w
  rw [coe_extHomeo hθ] at h
  conv_lhs => rw [← h]
  exact Function.leftInverse_invFun (extMap_injective hθ) _

theorem extInv_extMap (hθ : |θ| ≤ eps1 * ell j) (z : ℂ) : extInv j a θ (extMap j a θ z) = z :=
  Function.leftInverse_invFun (extMap_injective hθ) z

theorem extMap_extInv (hθ : |θ| ≤ eps1 * ell j) (w : ℂ) : extMap j a θ (extInv j a θ w) = w := by
  rw [extInv_eq_symm hθ, ← coe_extHomeo hθ]
  exact (extHomeo j a θ hθ).apply_symm_apply w

theorem continuous_extInv (hθ : |θ| ≤ eps1 * ell j) : Continuous (extInv j a θ) := by
  rw [extInv_eq_symm hθ]; exact (extHomeo j a θ hθ).symm.continuous

theorem hasFDerivAt_extMap (j : ℕ) (a θ : ℝ) (z : ℂ) :
    HasFDerivAt (extMap j a θ) (ContinuousLinearMap.id ℝ ℂ + pertDeriv j a θ z) z :=
  (hasFDerivAt_id z).add (hasFDerivAt_pert j a θ z)

theorem contDiff_cut (j : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cut j) := by
  unfold cut
  refine ContDiff.mul ?_ ?_
  · exact contDiff_chi.comp (Complex.reCLM.contDiff.sub contDiff_const)
  · exact contDiff_chi.comp ((contDiff_const.mul Complex.imCLM.contDiff).div_const _)

theorem contDiff_extMap (j : ℕ) (a θ : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (extMap j a θ) := by
  have hH : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => Complex.I * θ * probeH j a z) :=
    ((differentiable_probeH j a).const_mul (Complex.I * θ)).contDiff.restrict_scalars ℝ
  exact contDiff_id.add ((contDiff_cut j).smul hH)

/-- `DΦ(z) = I + Dg(z)` as a continuous linear equivalence (`‖Dg‖ < 1`) -/
def derivEquiv (a : ℝ) (hθ : |θ| ≤ eps1 * ell j) (z : ℂ) : ℂ ≃L[ℝ] ℂ :=
  ContinuousLinearEquiv.unitsEquiv ℝ ℂ (Units.oneSub (-pertDeriv j a θ z) (by
    rw [norm_neg]
    have := norm_pertDeriv_le j a θ z
    have := eta_le hθ
    linarith))

theorem coe_derivEquiv (hθ : |θ| ≤ eps1 * ell j) (z : ℂ) :
    (derivEquiv a hθ z : ℂ →L[ℝ] ℂ) = ContinuousLinearMap.id ℝ ℂ + pertDeriv j a θ z := by
  ext1 v
  rw [ContinuousLinearEquiv.coe_coe, derivEquiv, ContinuousLinearEquiv.unitsEquiv_apply,
    Units.val_oneSub, sub_neg_eq_add]
  rfl

theorem contDiff_extInv (hθ : |θ| ≤ eps1 * ell j) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (extInv j a θ) := by
  rw [extInv_eq_symm hθ]
  refine (extHomeo j a θ hθ).contDiff_symm (f₀' := derivEquiv a hθ) (fun z => ?_) ?_
  · rw [coe_derivEquiv hθ z, coe_extHomeo hθ]
    exact hasFDerivAt_extMap j a θ z
  · rw [coe_extHomeo hθ]; exact contDiff_extMap j a θ

/-! ## Localization: `Ψ(U_j) ⊆ R_j` and holomorphy of `Ψ` -/

theorem norm_extInv_sub_le (hθ : |θ| ≤ eps1 * ell j) (w : ℂ) :
    ‖extInv j a θ w - w‖ ≤ ell j / 48 := by
  have key : ∀ z, extMap j a θ z = w → z - w = -pert j a θ z := fun z hz => by
    rw [← hz]; unfold extMap; ring
  rw [key _ (extMap_extInv hθ w), norm_neg]
  exact (norm_pert_le j a θ _).trans (C0_mul_abs_le hθ)

theorem extInv_mem_rectR (hθ : |θ| ≤ eps1 * ell j) {w : ℂ} (hw : w ∈ probeRectU j) :
    extInv j a θ w ∈ rectR j := by
  have hℓ := ell_pos j
  have hℓ1 := ell_le_one j
  have hd := norm_extInv_sub_le (a := a) hθ w
  have hre : |(extInv j a θ w - w).re| ≤ ell j / 48 := (Complex.abs_re_le_norm _).trans hd
  have him : |(extInv j a θ w - w).im| ≤ ell j / 48 := (Complex.abs_im_le_norm _).trans hd
  rw [Complex.sub_re] at hre
  rw [Complex.sub_im] at him
  obtain ⟨⟨hw1, hw2⟩, hw3⟩ := hw
  constructor
  · rw [abs_le] at hre
    rw [abs_lt]
    constructor <;> linarith
  · have := abs_sub_abs_le_abs_sub (extInv j a θ w).im w.im
    linarith

theorem deriv_probeMap_ne_zero (hθ : |θ| ≤ eps1 * ell j) {z : ℂ} (hz : |z.im| ≤ ell j) :
    deriv (probeMap j a θ) z ≠ 0 := by
  have hℓ := ell_pos j
  rw [(hasDerivAt_probeMap j a θ z).deriv]
  intro h0
  have h1 : Complex.I * θ * deriv (probeH j a) z = -1 := by linear_combination h0
  have h2 : ‖Complex.I * θ * deriv (probeH j a) z‖ ≤ 1 / 48 := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |θ| * ‖deriv (probeH j a) z‖ ≤ |θ| * (C0 / ell j) :=
          mul_le_mul_of_nonneg_left (norm_deriv_probeH_le a hz) (abs_nonneg θ)
      _ = C0 * |θ| / ell j := by ring
      _ ≤ C3 * |θ| / ell j :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right C0_le_C3 (abs_nonneg θ))
            hℓ.le
      _ ≤ 1 / 48 := eta_le hθ
  rw [h1, norm_neg, norm_one] at h2
  norm_num at h2

theorem hasDerivAt_extMap_of_mem_rectR {z : ℂ} (hz : z ∈ rectR j) :
    HasDerivAt (extMap j a θ) (deriv (probeMap j a θ) z) z :=
  ((hasDerivAt_probeMap j a θ z).congr_of_eventuallyEq (extMap_eventuallyEq_probeMap hz)).congr_deriv
    (hasDerivAt_probeMap j a θ z).deriv.symm

theorem differentiableOn_extInv (hθ : |θ| ≤ eps1 * ell j) :
    DifferentiableOn ℂ (extInv j a θ) (probeRectU j) := by
  intro w hw
  have hz := extInv_mem_rectR (a := a) hθ hw
  have hd := hasDerivAt_extMap_of_mem_rectR (a := a) (θ := θ) hz
  have hne := deriv_probeMap_ne_zero (a := a) hθ (z := extInv j a θ w)
    (by have := hz.2; have := ell_pos j; linarith)
  exact (HasDerivAt.of_local_left_inverse (continuous_extInv hθ).continuousAt hd hne
    (Filter.Eventually.of_forall fun y => extMap_extInv hθ y)).differentiableAt.differentiableWithinAt

/-- **Step 2**: `Φ` is a near-identity diffeomorphism with holomorphic inverse on `U_j`. -/
theorem isNearIdDiffeo_extMap (hθ : |θ| ≤ eps1 * ell j) :
    CC.IsNearIdDiffeo (extMap j a θ) (extInv j a θ) (probeRectU j) (C3 * |θ| / ell j) where
  contDiff := contDiff_extMap j a θ
  contDiff_inv := contDiff_extInv hθ
  left_inv := extInv_extMap hθ
  right_inv := extMap_extInv hθ
  eq_id_off := by
    refine ⟨4, fun z hz => ?_⟩
    have hℓ1 := ell_le_one j
    have hn := Complex.norm_le_abs_re_add_abs_im z
    have hcut : cut j z = 0 := by
      by_cases h1 : 2 ≤ |z.re - 1 / 2|
      · exact cut_eq_zero_of_le_abs_re h1
      · by_cases h2 : ell j ≤ |z.im|
        · exact cut_eq_zero_of_le_abs_im h2
        · exfalso
          push Not at h1 h2
          have h3 : |z.re| ≤ |z.re - 1 / 2| + 1 / 2 := by
            have := abs_sub_abs_le_abs_sub z.re (1 / 2)
            rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
            linarith
          linarith
    rw [extMap, pert, hcut, zero_smul, add_zero]
  deriv_close z := by
    rw [(hasFDerivAt_extMap j a θ z).fderiv, add_sub_cancel_left]
    exact norm_pertDeriv_le j a θ z
  holo_inv := differentiableOn_extInv hθ

/-! ## The pullback of (b3) is the NIC transport -/

theorem probeMap_injOn_of_eps1 (hθ : |θ| ≤ eps1 * ell j) :
    InjOn (probeMap j a θ) (probeStrip j) :=
  probeMap_injOn (hθ.trans (mul_le_mul_of_nonneg_right eps1_le_epsB (ell_pos j).le))

theorem det_fderiv_extMap_of_mem_rectR {x : ℂ} (hx : x ∈ rectR j) :
    |LinearMap.det (fderiv ℝ (extMap j a θ) x : ℂ →ₗ[ℝ] ℂ)| =
      ‖deriv (probeMap j a θ) x‖ ^ 2 := by
  have hd := hasDerivAt_extMap_of_mem_rectR (a := a) (θ := θ) hx
  rw [(hd.hasFDerivAt.restrictScalars ℝ).fderiv]
  have h2 : LinearMap.det (((ContinuousLinearMap.toSpanSingleton ℂ
      (deriv (probeMap j a θ) x)).restrictScalars ℝ : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) =
      ‖deriv (probeMap j a θ) x‖ ^ 2 :=
    NIC.NearIdPair.det_restrictScalars_toSpanSingleton _
  rw [h2, abs_of_nonneg (sq_nonneg _)]

/-- **Step 3, the pullback**: the test function `τf = |ϕ'|² f ∘ ϕ` on the strip, `0` off it, of
clause (b3) is the NIC transport `|det DΦ| f ∘ Φ`, for every `f` supported in `U_j`. -/
theorem transport_eq_of_probe (hθ : |θ| ≤ eps1 * ell j) {f g : TestC}
    (hf : tsupport (f : ℂ → ℝ) ⊆ probeRectU j)
    (hg : ∀ z ∈ probeStrip j, g z = ‖deriv (probeMap j a θ) z‖ ^ 2 * f (probeMap j a θ z))
    (hg' : ∀ z ∉ probeStrip j, g z = 0) (x : ℂ) :
    g x = |LinearMap.det (fderiv ℝ (extMap j a θ) x : ℂ →ₗ[ℝ] ℂ)| * f (extMap j a θ x) := by
  have hinj := probeMap_injOn_of_eps1 (a := a) hθ
  by_cases hΦ : extMap j a θ x ∈ probeRectU j
  · have hx : x ∈ rectR j := by
      have := extInv_mem_rectR (a := a) hθ hΦ
      rwa [extInv_extMap hθ] at this
    rw [det_fderiv_extMap_of_mem_rectR hx, extMap_eq_probeMap hx]
    exact hg x (rectR_subset_probeStrip j hx)
  · have hf0 : f (extMap j a θ x) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hΦ (hf h))
    rw [hf0, mul_zero]
    by_cases hS : x ∈ probeStrip j
    · rw [hg x hS]
      have hfφ : f (probeMap j a θ x) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        have hU := hf hmem
        have hyR : extInv j a θ (probeMap j a θ x) ∈ rectR j := extInv_mem_rectR hθ hU
        have h1 : probeMap j a θ (extInv j a θ (probeMap j a θ x)) = probeMap j a θ x := by
          rw [← extMap_eq_probeMap hyR, extMap_extInv hθ]
        have h2 := hinj (rectR_subset_probeStrip j hyR) hS h1
        rw [h2] at hyR
        exact hΦ (by rw [extMap_eq_probeMap hyR]; exact hU)
      rw [hfφ, mul_zero]
    · exact hg' x hS

/-- `ψ = (ϕ|_S)⁻¹ = Ψ` on `U_j` -/
theorem probeInv_eq_extInv (hθ : |θ| ≤ eps1 * ell j) {w : ℂ} (hw : w ∈ probeRectU j) :
    probeInv j a θ w = extInv j a θ w := by
  have hinj := probeMap_injOn_of_eps1 (a := a) hθ
  have hR := extInv_mem_rectR (a := a) hθ hw
  have hS := rectR_subset_probeStrip j hR
  have hφ : probeMap j a θ (extInv j a θ w) = w := by
    rw [← extMap_eq_probeMap hR, extMap_extInv hθ]
  have hex : ∃ z ∈ probeStrip j, probeMap j a θ z = w := ⟨_, hS, hφ⟩
  obtain ⟨h1, h2⟩ := Function.invFunOn_pos hex
  exact hinj h1 hS (h2.trans hφ.symm)

theorem ofReal_mem_probeRectU (j : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (t : ℂ) ∈ probeRectU j := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Complex.ofReal_re]; linarith [ht.1]
  · rw [Complex.ofReal_re]; linarith [ht.2]
  · rw [Complex.ofReal_im, abs_zero]; have := ell_pos j; positivity

/-! ## Bi-Lipschitz bounds -/

theorem norm_pert_sub_le' (hθ : |θ| ≤ eps1 * ell j) (x y : ℂ) :
    ‖pert j a θ x - pert j a θ y‖ ≤ 1 / 48 * ‖x - y‖ :=
  (norm_pert_sub_le j a θ x y).trans (mul_le_mul_of_nonneg_right (eta_le hθ) (norm_nonneg _))

theorem norm_sub_le_extMap_sub (hθ : |θ| ≤ eps1 * ell j) (x y : ℂ) :
    47 / 48 * ‖x - y‖ ≤ ‖extMap j a θ x - extMap j a θ y‖ := by
  have h := norm_pert_sub_le' (a := a) hθ x y
  have e : extMap j a θ x - extMap j a θ y = (x - y) + (pert j a θ x - pert j a θ y) := by
    unfold extMap; ring
  have := norm_sub_norm_le (x - y) (-(pert j a θ x - pert j a θ y))
  rw [sub_neg_eq_add, ← e, norm_neg] at this
  linarith

theorem norm_extMap_sub_le (hθ : |θ| ≤ eps1 * ell j) (x y : ℂ) :
    ‖extMap j a θ x - extMap j a θ y‖ ≤ 49 / 48 * ‖x - y‖ := by
  have h := norm_pert_sub_le' (a := a) hθ x y
  have e : extMap j a θ x - extMap j a θ y = (x - y) + (pert j a θ x - pert j a θ y) := by
    unfold extMap; ring
  rw [e]
  have := norm_add_le (x - y) (pert j a θ x - pert j a θ y)
  linarith

/-- `Ψ` is `2`-Lipschitz -/
theorem norm_extInv_sub_le_two (hθ : |θ| ≤ eps1 * ell j) (w w' : ℂ) :
    ‖extInv j a θ w - extInv j a θ w'‖ ≤ 2 * ‖w - w'‖ := by
  have h := norm_sub_le_extMap_sub (a := a) hθ (extInv j a θ w) (extInv j a θ w')
  rw [extMap_extInv hθ, extMap_extInv hθ] at h
  have := norm_nonneg (extInv j a θ w - extInv j a θ w')
  linarith

/-- `Ψ` expands by at least `1/2` -/
theorem norm_sub_le_two_extInv (hθ : |θ| ≤ eps1 * ell j) (w w' : ℂ) :
    ‖w - w'‖ ≤ 2 * ‖extInv j a θ w - extInv j a θ w'‖ := by
  have h := norm_extMap_sub_le (a := a) hθ (extInv j a θ w) (extInv j a θ w')
  rw [extMap_extInv hθ, extMap_extInv hθ] at h
  have := norm_nonneg (extInv j a θ w - extInv j a θ w')
  linarith

/-- the sharp co-Lipschitz bound `‖w − w'‖ ≤ (49/48) ‖Ψ w − Ψ w'‖` -/
theorem norm_sub_le_extInv (hθ : |θ| ≤ eps1 * ell j) (w w' : ℂ) :
    ‖w - w'‖ ≤ 49 / 48 * ‖extInv j a θ w - extInv j a θ w'‖ := by
  have h := norm_extMap_sub_le (a := a) hθ (extInv j a θ w) (extInv j a θ w')
  rwa [extMap_extInv hθ, extMap_extInv hθ] at h

/-- the co-Lipschitz bound of `ψ = probeInv` on `[0,1]`: `|t − t'| ≤ (3/2) ‖ψ t − ψ t'‖` -/
theorem abs_sub_le_probeInv (hθ : |θ| ≤ eps1 * ell j) {t t' : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (ht' : t' ∈ Icc (0 : ℝ) 1) :
    |t - t'| ≤ 3 / 2 * ‖probeInv j a θ t - probeInv j a θ t'‖ := by
  rw [probeInv_eq_extInv hθ (ofReal_mem_probeRectU j ht),
    probeInv_eq_extInv hθ (ofReal_mem_probeRectU j ht')]
  have h := norm_sub_le_extInv (a := a) hθ (t : ℂ) (t' : ℂ)
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  have h0 := norm_nonneg (extInv j a θ t - extInv j a θ t')
  linarith

end small

end Coupling42

end SmallGammaGeodesics
