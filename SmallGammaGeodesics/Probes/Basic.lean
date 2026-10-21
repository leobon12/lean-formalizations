import SmallGammaGeodesics.Probes.Defs
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Elementary facts about the cutoffs `χ`, `ρ`, the scales `ℓ_j` and the probe kernel `q`

* `chi` is even, `= 1` on `[-1, 1]`, `= 0` off `(-2, 2)`, with values in `[0, 1]`, and smooth.
* `rho` vanishes on `[-1/2, 1/2]` and off `(-2, 2)`, is even, nonnegative and smooth; `ρ(1) = 1`.
* `ell j = 2⁻ʲ`, `2 ℓ_{j+1} = ℓ_j`.
* `probeQ s = ρ(s)/(πs)²` (GA2 D4.2's `q`) is smooth, even, and vanishes off `1/2 < |s| < 2`.
* `exists_bound_iteratedDeriv`: every derivative of a smooth compactly supported function is
  bounded, and it vanishes off the topological support.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Function
open scoped Real

namespace SmallGammaGeodesics

/-! ### The cutoff `χ` -/

theorem chi_eq_one {s : ℝ} (hs : |s| ≤ 1) : chi s = 1 := by
  unfold chi
  refine chiBump.one_of_mem_closedBall ?_
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
  exact hs

theorem chi_eq_zero {s : ℝ} (hs : 2 ≤ |s|) : chi s = 0 := by
  unfold chi
  refine chiBump.zero_of_le_dist ?_
  rw [Real.dist_eq, sub_zero]
  exact hs

theorem chi_nonneg (s : ℝ) : 0 ≤ chi s := chiBump.nonneg

theorem chi_le_one (s : ℝ) : chi s ≤ 1 := chiBump.le_one

theorem chi_neg (s : ℝ) : chi (-s) = chi s := chiBump.neg s

theorem chi_zero : chi 0 = 1 := chi_eq_one (by simp)

theorem contDiff_chi {n : ℕ∞} : ContDiff ℝ n chi := chiBump.contDiff

theorem continuous_chi : Continuous chi := chiBump.continuous

theorem chi_of_two_le {s : ℝ} (hs : 2 ≤ s) : chi s = 0 :=
  chi_eq_zero (by rw [abs_of_nonneg (by linarith)]; exact hs)

/-! ### The annular multiplier `ρ` -/

theorem rho_eq_zero_of_abs_le {s : ℝ} (hs : |s| ≤ 1 / 2) : rho s = 0 := by
  unfold rho
  rw [chi_eq_one (by linarith), chi_eq_one (by rw [abs_mul]; norm_num; linarith)]
  ring

theorem rho_eq_zero_of_le_abs {s : ℝ} (hs : 2 ≤ |s|) : rho s = 0 := by
  unfold rho
  rw [chi_eq_zero hs, chi_eq_zero (by rw [abs_mul]; norm_num; linarith)]
  ring

theorem rho_of_two_le {s : ℝ} (hs : 2 ≤ s) : rho s = 0 :=
  rho_eq_zero_of_le_abs (by rw [abs_of_nonneg (by linarith)]; exact hs)

theorem rho_neg (s : ℝ) : rho (-s) = rho s := by
  unfold rho
  rw [chi_neg, show 2 * -s = -(2 * s) by ring, chi_neg]

theorem rho_nonneg (s : ℝ) : 0 ≤ rho s := by
  unfold rho
  rcases le_or_gt |s| 1 with h | h
  · rw [chi_eq_one h]
    linarith [chi_le_one (2 * s)]
  · rw [chi_eq_zero (show 2 ≤ |2 * s| by rw [abs_mul]; norm_num; linarith)]
    linarith [chi_nonneg s]

theorem rho_one : rho 1 = 1 := by
  unfold rho
  rw [chi_eq_one (by norm_num), chi_eq_zero (by norm_num)]
  ring

theorem contDiff_rho {n : ℕ∞} : ContDiff ℝ n rho := by
  unfold rho
  exact contDiff_chi.sub (contDiff_chi.comp (contDiff_const.mul contDiff_id))

theorem continuous_rho : Continuous rho := contDiff_rho (n := 0).continuous

/-! ### The scales `ℓ_j` -/

theorem ell_pos (j : ℕ) : 0 < ell j := by unfold ell; positivity

theorem ell_le_one (j : ℕ) : ell j ≤ 1 := by
  unfold ell
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

theorem inv_ell (j : ℕ) : (ell j)⁻¹ = 2 ^ j := by unfold ell; rw [inv_inv]

theorem ell_mul_pow (j : ℕ) : ell j * 2 ^ j = 1 := by
  unfold ell
  exact inv_mul_cancel₀ (by positivity)

theorem two_mul_ell_succ (j : ℕ) : 2 * ell (j + 1) = ell j := by
  unfold ell
  rw [pow_succ]
  field_simp

theorem ell_zero : ell 0 = 1 := by simp [ell]

theorem natCast_mul_ell (k j : ℕ) : (k : ℝ) * ell j = k / (2 ^ j : ℕ) := by
  unfold ell
  push_cast
  ring

/-- For `k ≥ 2^{j+1}`, `k ℓ_j ≥ 2`. -/
theorem two_le_natCast_mul_ell {k j : ℕ} (hk : 2 ^ (j + 1) ≤ k) : 2 ≤ (k : ℝ) * ell j := by
  rw [natCast_mul_ell, le_div_iff₀ (by positivity)]
  have : ((2 ^ (j + 1) : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
  push_cast at this ⊢
  rw [pow_succ] at this
  linarith

/-! ### The probe kernel `q(s) = ρ(s)/(πs)²` -/

/-- GA2 D4.2's kernel `q(s) = ρ(s)/(πs)²` (`q(0) = 0`). -/
def probeQ (s : ℝ) : ℝ := rho s / (π * s) ^ 2

theorem probeQ_eq_zero_of_abs_le {s : ℝ} (hs : |s| ≤ 1 / 2) : probeQ s = 0 := by
  unfold probeQ
  rw [rho_eq_zero_of_abs_le hs, zero_div]

theorem probeQ_eq_zero_of_le_abs {s : ℝ} (hs : 2 ≤ |s|) : probeQ s = 0 := by
  unfold probeQ
  rw [rho_eq_zero_of_le_abs hs, zero_div]

theorem probeQ_neg (s : ℝ) : probeQ (-s) = probeQ s := by
  unfold probeQ
  rw [rho_neg]
  ring

theorem probeQ_nonneg (s : ℝ) : 0 ≤ probeQ s := by
  unfold probeQ
  exact div_nonneg (rho_nonneg s) (sq_nonneg _)

theorem contDiff_probeQ {n : ℕ∞} : ContDiff ℝ n probeQ := by
  rw [contDiff_iff_contDiffAt]
  intro s
  rcases lt_or_ge |s| (1 / 2) with hs | hs
  · have hev : probeQ =ᶠ[nhds s] fun _ => (0 : ℝ) := by
      have hopen : IsOpen {t : ℝ | |t| < 1 / 2} := isOpen_lt continuous_abs continuous_const
      filter_upwards [hopen.mem_nhds hs] with t ht
      exact probeQ_eq_zero_of_abs_le (le_of_lt ht)
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hs0 : s ≠ 0 := by
      intro h
      rw [h, abs_zero] at hs
      norm_num at hs
    unfold probeQ
    refine contDiff_rho.contDiffAt.div ?_ ?_
    · exact ((contDiff_const.mul contDiff_id).pow 2).contDiffAt
    · exact pow_ne_zero 2 (mul_ne_zero Real.pi_ne_zero hs0)

/-- The kernel `q` as a complex-valued function. -/
theorem contDiff_probeQ_complex {n : ℕ∞} : ContDiff ℝ n fun s : ℝ => (probeQ s : ℂ) :=
  Complex.ofRealCLM.contDiff.comp contDiff_probeQ

/-! ### Derivative bounds for smooth compactly supported functions -/

/-- Every derivative of a smooth compactly supported function is bounded. -/
theorem exists_bound_iteratedDeriv {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (i : ℕ) : ∃ C, ∀ x, ‖iteratedDeriv i f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (hc.iteratedFDeriv (𝕜 := ℝ) i).exists_bound_of_continuous
    (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top))
  exact ⟨C, fun x => by rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]; exact hC x⟩

/-- The derivatives of a function vanish off its topological support. -/
theorem iteratedDeriv_eq_zero_of_notMem_tsupport {f : ℝ → ℂ} (i : ℕ) {x : ℝ}
    (hx : x ∉ tsupport f) : iteratedDeriv i f x = 0 := by
  have h : iteratedFDeriv ℝ i f x = 0 := by
    by_contra hne
    exact hx (support_iteratedFDeriv_subset i (mem_support.mpr hne))
  rw [iteratedDeriv_eq_iteratedFDeriv, h]
  rfl

/-- A function vanishing for `|x| ≥ A` has compact support inside `[-A, A]`. -/
theorem tsupport_subset_of_abs {f : ℝ → ℂ} {A : ℝ} (hf : ∀ x, A ≤ |x| → f x = 0) :
    tsupport f ⊆ Icc (-A) A := by
  refine closure_minimal ?_ isClosed_Icc
  intro x hx
  rw [mem_support] at hx
  by_contra h
  rw [mem_Icc, not_and_or, not_le, not_le] at h
  refine hx (hf x ?_)
  rcases h with h | h
  · linarith [neg_le_abs x]
  · exact le_trans h.le (le_abs_self x)

theorem hasCompactSupport_of_abs {f : ℝ → ℂ} {A : ℝ} (hf : ∀ x, A ≤ |x| → f x = 0) :
    HasCompactSupport f :=
  isCompact_Icc.of_isClosed_subset isClosed_closure (tsupport_subset_of_abs hf)

end SmallGammaGeodesics
