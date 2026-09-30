import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Order.Filter.AtTopBot.Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B7 (part): uniformity over a totally bounded family of test functions

Task SWC-B7. The uniform boundary transport `SWCore.BdryTransportUnifGood` is uniform over the
maps of a class but holds for **one** test function at a time. In AC-fam the test function in the
coordinates of the time-`s` field is `f ∘ F_s⁻¹`, which moves with `s`. This file proves the
deterministic upgrade: convergence that is uniform in an index `i` for each fixed test function of
a family `F` is uniform over `F` as well, provided `F` is totally bounded in the sup norm, all its
members vanish off a set `K`, the masses of `K` are controlled through one fixed dominating test
function `φ ≥ 1_K`, and the limit functionals are Lipschitz in the sup norm.

Own elementary proof (an `ε/3` argument with a finite net; cost rule of AGENT_GUIDE).
-/

noncomputable section

open MeasureTheory Filter Set

namespace QuantumZipper
namespace SWCore

/-- **Uniformity over a totally bounded test family.** -/
theorem unif_testFamily {ι : Type*} {μ : ι → ℕ → Measure ℝ} {L : ι → (ℝ → ℝ) → ℝ}
    {K : Set ℝ} {φ : ℝ → ℝ} {Mφ D : ℝ} {F : Set (ℝ → ℝ)}
    (hφ0 : ∀ x, 0 ≤ φ x) (hφK : ∀ x ∈ K, 1 ≤ φ x)
    (hφint : ∀ᶠ k in atTop, ∀ i, Integrable φ (μ i k))
    (hφconv : ∀ η > 0, ∀ᶠ k in atTop, ∀ i, |∫ x, φ x ∂μ i k - L i φ| ≤ η)
    (hLφ : ∀ i, L i φ ≤ Mφ)
    (hFK : ∀ f ∈ F, ∀ x ∉ K, f x = 0)
    (hFs : ∀ f ∈ F, StronglyMeasurable f)
    (hFb : ∀ f ∈ F, ∃ C, ∀ x, |f x| ≤ C)
    (hLlip : ∀ i, ∀ f ∈ F, ∀ g ∈ F, ∀ ε : ℝ, 0 ≤ ε → (∀ x, |f x - g x| ≤ ε) →
      |L i f - L i g| ≤ D * ε)
    (hnet : ∀ ε > 0, ∃ S : Finset (ℝ → ℝ), (∀ g ∈ S, g ∈ F) ∧
      ∀ f ∈ F, ∃ g ∈ S, ∀ x, |f x - g x| ≤ ε)
    (hconv : ∀ f ∈ F, ∀ η > 0, ∀ᶠ k in atTop, ∀ i, |∫ x, f x ∂μ i k - L i f| ≤ η) :
    ∀ η > 0, ∀ᶠ k in atTop, ∀ i, ∀ f ∈ F, |∫ x, f x ∂μ i k - L i f| ≤ η := by
  intro η hη
  set E : ℝ := |Mφ| + 1 + |D| + 1 with hE
  have hEpos : 0 < E := by positivity
  set ε : ℝ := η / (3 * E) with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨S, hSF, hSnet⟩ := hnet ε hε
  have hS : ∀ᶠ k in atTop, ∀ g ∈ S, ∀ i, |∫ x, g x ∂μ i k - L i g| ≤ η / 3 :=
    (Filter.eventually_all_finset S).2 fun g hg => hconv g (hSF g hg) (η / 3) (by positivity)
  filter_upwards [hφint, hφconv 1 one_pos, hS] with k hint hφk hSk i f hf
  obtain ⟨g, hgS, hfg⟩ := hSnet f hf
  have hgF := hSF g hgS
  -- integrability of members of `F` (dominated by a multiple of `φ`)
  have hdom : ∀ h ∈ F, Integrable h (μ i k) := by
    intro h hh
    obtain ⟨C, hC⟩ := hFb h hh
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
    refine Integrable.mono' ((hint i).const_mul C) (hFs h hh).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs]
    by_cases hx : x ∈ K
    · calc |h x| ≤ C := hC x
        _ = C * 1 := (mul_one C).symm
        _ ≤ C * φ x := mul_le_mul_of_nonneg_left (hφK x hx) hC0
    · rw [hFK h hh x hx, abs_zero]
      exact mul_nonneg hC0 (hφ0 x)
  have hfi := hdom f hf
  have hgi := hdom g hgF
  -- `|∫ f − ∫ g| ≤ ε ∫ φ`
  have h1 : |∫ x, f x ∂μ i k - ∫ x, g x ∂μ i k| ≤ ε * ∫ x, φ x ∂μ i k := by
    rw [← integral_sub hfi hgi, ← integral_const_mul]
    have := norm_integral_le_of_norm_le ((hint i).const_mul ε)
      (ae_of_all (μ i k) fun x => show ‖f x - g x‖ ≤ ε * φ x by
        rw [Real.norm_eq_abs]
        by_cases hx : x ∈ K
        · calc |f x - g x| ≤ ε := hfg x
            _ = ε * 1 := (mul_one ε).symm
            _ ≤ ε * φ x := mul_le_mul_of_nonneg_left (hφK x hx) hε.le
        · rw [hFK f hf x hx, hFK g hgF x hx, sub_zero, abs_zero]
          exact mul_nonneg hε.le (hφ0 x))
    rwa [Real.norm_eq_abs] at this
  have hφle : ∫ x, φ x ∂μ i k ≤ |Mφ| + 1 := by
    have := (abs_le.1 (hφk i)).2
    linarith [hLφ i, le_abs_self Mφ]
  have h2 := hSk g hgS i
  have h3 : |L i f - L i g| ≤ |D| * ε :=
    (hLlip i f hf g hgF ε hε.le hfg).trans
      (mul_le_mul_of_nonneg_right (le_abs_self D) hε.le)
  have hεE : ε * E = η / 3 := by
    rw [hεdef]; field_simp
  have h1' : ε * ∫ x, φ x ∂μ i k ≤ ε * (|Mφ| + 1) :=
    mul_le_mul_of_nonneg_left hφle hε.le
  have hsum : ε * (|Mφ| + 1) + |D| * ε ≤ η / 3 * 2 := by
    have : ε * (|Mφ| + 1) + |D| * ε ≤ ε * E := by
      rw [hE]; nlinarith [abs_nonneg D, abs_nonneg Mφ]
    linarith
  calc |∫ x, f x ∂μ i k - L i f|
      = |(∫ x, f x ∂μ i k - ∫ x, g x ∂μ i k) + (∫ x, g x ∂μ i k - L i g) +
          (L i g - L i f)| := by ring_nf
    _ ≤ |∫ x, f x ∂μ i k - ∫ x, g x ∂μ i k| + |∫ x, g x ∂μ i k - L i g| +
          |L i g - L i f| := abs_add_three _ _ _
    _ ≤ ε * (|Mφ| + 1) + η / 3 + |D| * ε := by
        rw [abs_sub_comm (L i g)]
        linarith
    _ ≤ η := by linarith

end SWCore
end QuantumZipper
