import HigherDimLQGMetric.Trap.Stable
import HigherDimLQGMetric.Core.Defs
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# The smooth trap functions ([S] l. 664–669, MA1 A17 "Construction")

Packet S3. In `ℝ^d`, for an open collector `V`, a closed set `K` (the graph) and open tubes
`T n` with `K ⊆ T n ⊆ V`, and levels `λ_n ∈ (0, e^{-ξ}]`, the functions
`f_n := f₀ + (M_n - f₀) φ_n` with `M_n = ξ⁻¹ log λ_n⁻¹ ≥ 1`, `f₀` smooth with values in `[0, 1]`
and support `V`, and `φ_n` smooth with values in `[0, 1]`, support `T n` and `φ_n = 1` exactly on
`K` (Mathlib `IsOpen.exists_contDiff_support_eq`, `exists_contDiff_support_eq_eq_one_iff`) satisfy
(`trap_smooth_family`):

* `f_n` is smooth, `0 ≤ f_n ≤ M_n`, `f_n > 0` exactly on `V`;
* `e^{-ξ f_n} = λ_n` on `K`, `e^{-ξ f_n} ≥ e^{-ξ}` off `T n`, `e^{-ξ f_n} = 1` off `V`,
  `λ_n ≤ e^{-ξ f_n} ≤ 1`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open HigherDimLFPP (Rd)
open scoped ENNReal

namespace HigherDimLQGMetric

/-- **The trap functions** `f_n = f₀ + (M_n - f₀) φ_n` of [S] l. 664–669. -/
theorem trap_smooth_family {d : ℕ} {ξ : ℝ} (hξ : 0 < ξ) {V K : Set (Rd d)} (hV : IsOpen V)
    (hK : IsClosed K) (T : ℕ → Set (Rd d)) (hT : ∀ n, IsOpen (T n)) (hKT : ∀ n, K ⊆ T n)
    (hTV : ∀ n, T n ⊆ V) (lam : ℕ → ℝ) (hlam0 : ∀ n, 0 < lam n)
    (hlamξ : ∀ n, lam n ≤ Real.exp (-ξ)) :
    ∃ f : ℕ → Rd d → ℝ, ∀ n,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f n) ∧ (∀ x, 0 ≤ f n x) ∧
      (∀ x, 0 < f n x ↔ x ∈ V) ∧ (∀ x, x ∉ V → f n x = 0) ∧
      (∀ x, lam n ≤ Real.exp (-(ξ * f n x)) ∧ Real.exp (-(ξ * f n x)) ≤ 1) ∧
      (∀ x ∈ K, Real.exp (-(ξ * f n x)) = lam n) ∧
      (∀ x, x ∉ T n → Real.exp (-ξ) ≤ Real.exp (-(ξ * f n x))) := by
  obtain ⟨f₀, hf₀supp, hf₀c, hf₀r⟩ := hV.exists_contDiff_support_eq (n := (⊤ : ℕ∞))
  have hφ := fun n => exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) (hT n) hK (hKT n)
  choose φ hφc hφr hφsupp hφone using hφ
  have hf₀01 : ∀ x, 0 ≤ f₀ x ∧ f₀ x ≤ 1 := fun x => hf₀r (mem_range_self x)
  have hφ01 : ∀ n x, 0 ≤ φ n x ∧ φ n x ≤ 1 := fun n x => hφr n (mem_range_self x)
  set M : ℕ → ℝ := fun n => -Real.log (lam n) / ξ with hM_def
  have hM1 : ∀ n, 1 ≤ M n := by
    intro n
    have hlog : Real.log (lam n) ≤ -ξ := by
      have := Real.log_le_log (hlam0 n) (hlamξ n)
      rwa [Real.log_exp] at this
    rw [hM_def, le_div_iff₀ hξ]
    linarith
  have hexpM : ∀ n, Real.exp (-(ξ * M n)) = lam n := by
    intro n
    rw [hM_def]
    have : -(ξ * (-Real.log (lam n) / ξ)) = Real.log (lam n) := by field_simp
    rw [this, Real.exp_log (hlam0 n)]
  refine ⟨fun n x => f₀ x + (M n - f₀ x) * φ n x, fun n => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact hf₀c.add ((contDiff_const.sub hf₀c).mul (hφc n))
  · intro x
    have h0 := hf₀01 x
    have h1 := hφ01 n x
    have := hM1 n
    nlinarith
  · intro x
    constructor
    · intro hpos
      by_contra hxV
      have hf0 : f₀ x = 0 := by
        rw [← Function.notMem_support, hf₀supp]
        exact hxV
      have hφ0 : φ n x = 0 := by
        rw [← Function.notMem_support, hφsupp n]
        exact fun h => hxV (hTV n h)
      simp [hf0, hφ0] at hpos
    · intro hxV
      have hf0 : 0 < f₀ x := by
        have hne : f₀ x ≠ 0 := by
          rw [← Function.mem_support, hf₀supp]
          exact hxV
        exact lt_of_le_of_ne (hf₀01 x).1 (Ne.symm hne)
      have h1 := hφ01 n x
      have := hM1 n
      rcases h1.2.lt_or_eq with hlt | heq
      · nlinarith
      · show 0 < f₀ x + (M n - f₀ x) * φ n x
        rw [heq]
        linarith
  · intro x hxV
    have hf0 : f₀ x = 0 := by
      rw [← Function.notMem_support, hf₀supp]
      exact hxV
    have hφ0 : φ n x = 0 := by
      rw [← Function.notMem_support, hφsupp n]
      exact fun h => hxV (hTV n h)
    simp [hf0, hφ0]
  · intro x
    have h0 := hf₀01 x
    have h1 := hφ01 n x
    have := hM1 n
    have hle : f₀ x + (M n - f₀ x) * φ n x ≤ M n := by nlinarith
    have hge : 0 ≤ f₀ x + (M n - f₀ x) * φ n x := by nlinarith
    constructor
    · rw [← hexpM n]
      exact Real.exp_le_exp.2 (by nlinarith)
    · rw [← Real.exp_zero]
      exact Real.exp_le_exp.2 (by nlinarith)
  · intro x hx
    have h1 : φ n x = 1 := (hφone n x).1 hx
    show Real.exp (-(ξ * (f₀ x + (M n - f₀ x) * φ n x))) = lam n
    rw [h1]
    simp only [mul_one, add_sub_cancel]
    exact hexpM n
  · intro x hx
    have hφ0 : φ n x = 0 := by
      rw [← Function.notMem_support, hφsupp n]
      exact hx
    show Real.exp (-ξ) ≤ Real.exp (-(ξ * (f₀ x + (M n - f₀ x) * φ n x)))
    rw [hφ0, mul_zero, add_zero]
    exact Real.exp_le_exp.2 (by nlinarith [(hf₀01 x).2])

end HigherDimLQGMetric
