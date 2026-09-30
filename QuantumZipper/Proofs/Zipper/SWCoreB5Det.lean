import QuantumZipper.Proofs.Zipper.SWCoreB5Win

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B5 (4): the target integral and the deterministic partition estimates

Task SWC-B5 (`handoff/SW-CORE.md`).

* `target_eq_of_iso` — the target of `BdryTransportUnifGood`, `∫_{[ψa,ψb]} f(ψ⁻¹ u) dν`, equals
  `∫ f ∘ Φ⁻¹ dν` for any order isomorphism `Φ` of `ℝ` extending `Re ψ` on `[a,b]`
  (e.g. `CoordChange.extIso`), when `tsupport f ⊆ (a,b)`;
* `det_upper`, `det_lower` — replacing a nonnegative integrand `g` by piecewise constants
  `F_n` on a partition of unity costs at most `2ω ν(K')` in the integral.

Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace SWCore

/-- The target integral through an order isomorphism extending `Re ψ` on `[a,b]`. -/
theorem target_eq_of_iso {ψ : ℂ → ℂ} {a b : ℝ} (Φ : ℝ ≃o ℝ)
    (hΦ : ∀ t ∈ Icc a b, Φ t = (ψ t).re) {f : ℝ → ℝ} (hfs : tsupport f ⊆ Ioo a b)
    (ν : Measure ℝ) (hab : a ≤ b) :
    ∫ u in Icc (ψ (a : ℂ)).re (ψ (b : ℂ)).re,
        f (Function.invFunOn (fun t : ℝ => (ψ t).re) (Icc a b) u) ∂ν =
      ∫ u, f (Φ.symm u) ∂ν := by
  have ha : (ψ (a : ℂ)).re = Φ a := (hΦ a ⟨le_rfl, hab⟩).symm
  have hb : (ψ (b : ℂ)).re = Φ b := (hΦ b ⟨hab, le_rfl⟩).symm
  have hinj : InjOn (fun t : ℝ => (ψ t).re) (Icc a b) := by
    intro s hs t ht hst
    have : Φ s = Φ t := by rw [hΦ s hs, hΦ t ht]; exact hst
    exact Φ.injective this
  have hmem : ∀ u ∈ Icc (Φ a) (Φ b), Φ.symm u ∈ Icc a b := fun u hu =>
    ⟨Φ.le_symm_apply.2 hu.1, Φ.symm_apply_le.2 hu.2⟩
  rw [ha, hb]
  rw [setIntegral_congr_fun measurableSet_Icc (g := fun u => f (Φ.symm u)) ?_]
  · refine setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => ?_
    refine image_eq_zero_of_notMem_tsupport fun h => hu ?_
    have h' := hfs h
    exact ⟨by simpa using Φ.monotone h'.1.le, by simpa using Φ.monotone h'.2.le⟩
  · intro u hu
    have hex : ∃ t ∈ Icc a b, (fun t : ℝ => (ψ t).re) t = u :=
      ⟨Φ.symm u, hmem u hu, by
        show (ψ _).re = u
        rw [← hΦ _ (hmem u hu)]; simp⟩
    have h1 := Function.invFunOn_mem hex
    have h2 := Function.invFunOn_eq hex
    have : Function.invFunOn (fun t : ℝ => (ψ t).re) (Icc a b) u = Φ.symm u :=
      hinj h1 (hmem u hu) (by
        show (ψ _).re = (ψ _).re
        rw [h2, ← hΦ _ (hmem u hu)]; simp)
    simp only [this]

variable {ν : Measure ℝ} [IsLocallyFiniteMeasure ν] {T : Finset ℤ} {φ : T → ℝ → ℝ}
  {g : ℝ → ℝ} {F : T → ℝ} {ω : ℝ} {K : Set ℝ}

theorem integral_sum_F (hφc : ∀ n, Continuous (φ n)) (hφs : ∀ n, HasCompactSupport (φ n)) :
    ∫ u, ∑ n, F n * φ n u ∂ν = ∑ n, F n * ∫ u, φ n u ∂ν := by
  rw [integral_finsetSum _ fun n _ =>
    ((hφc n).integrable_of_hasCompactSupport (hφs n)).const_mul (F n)]
  exact Finset.sum_congr rfl fun n _ => integral_const_mul _ _

/-- **Upper deterministic estimate.** -/
theorem det_upper (hφc : ∀ n, Continuous (φ n)) (hφs : ∀ n, HasCompactSupport (φ n))
    (hφ0 : ∀ n u, 0 ≤ φ n u) (hsum : ∀ u, ∑ n, φ n u ≤ 1) (hF0 : ∀ n, 0 ≤ F n)
    (hg : Continuous g) (hgs : HasCompactSupport g) (hg0 : ∀ u, 0 ≤ g u) (hω : 0 ≤ ω)
    (hK : IsCompact K)
    (hpt : ∀ n u, φ n u ≠ 0 → 0 < F n → F n ≤ g u + 2 * ω ∧ u ∈ K) :
    ∑ n, F n * ∫ u, φ n u ∂ν ≤ ∫ u, g u ∂ν + 2 * ω * ν.real K := by
  rw [← integral_sum_F hφc hφs]
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hpw : ∀ u, ∑ n, F n * φ n u ≤ g u + 2 * ω * K.indicator 1 u := by
    intro u
    have hR0 : 0 ≤ g u + 2 * ω * K.indicator 1 u := by
      have : 0 ≤ K.indicator (1 : ℝ → ℝ) u := indicator_nonneg (fun _ _ => zero_le_one) u
      have := hg0 u; positivity
    calc ∑ n, F n * φ n u ≤ ∑ n, (g u + 2 * ω * K.indicator 1 u) * φ n u := by
          refine Finset.sum_le_sum fun n _ => ?_
          by_cases h0 : φ n u = 0
          · simp [h0]
          rcases (hF0 n).eq_or_lt with hF | hF
          · rw [← hF, zero_mul]; exact mul_nonneg hR0 (hφ0 n u)
          obtain ⟨h1, h2⟩ := hpt n u h0 hF
          rw [indicator_of_mem h2, Pi.one_apply, mul_one]
          exact mul_le_mul_of_nonneg_right h1 (hφ0 n u)
      _ = (g u + 2 * ω * K.indicator 1 u) * ∑ n, φ n u := by rw [Finset.mul_sum]
      _ ≤ (g u + 2 * ω * K.indicator 1 u) * 1 := by gcongr; exact hsum u
      _ = _ := mul_one _
  have hgi : Integrable g ν := hg.integrable_of_hasCompactSupport hgs
  have hKi : Integrable (fun u => 2 * ω * K.indicator (1 : ℝ → ℝ) u) ν :=
    ((integrable_indicator_iff hKm).2 (integrableOn_const hK.measure_lt_top.ne)).const_mul _
  calc ∫ u, ∑ n, F n * φ n u ∂ν ≤ ∫ u, (g u + 2 * ω * K.indicator 1 u) ∂ν :=
        integral_mono (integrable_finsetSum _ fun n _ =>
          ((hφc n).integrable_of_hasCompactSupport (hφs n)).const_mul (F n))
          (hgi.add hKi) hpw
    _ = ∫ u, g u ∂ν + 2 * ω * ν.real K := by
        rw [integral_add hgi hKi, integral_const_mul, integral_indicator_one hKm]

/-- **Lower deterministic estimate.** -/
theorem det_lower (hφc : ∀ n, Continuous (φ n)) (hφs : ∀ n, HasCompactSupport (φ n))
    (hφ0 : ∀ n u, 0 ≤ φ n u) (hF0 : ∀ n, 0 ≤ F n)
    (hg : Continuous g) (hgs : HasCompactSupport g) (hω : 0 ≤ ω)
    (hK : IsCompact K)
    (hpt : ∀ u, g u ≠ 0 → (∑ n, φ n u = 1 ∧ u ∈ K ∧ ∀ n, φ n u ≠ 0 → g u - 2 * ω ≤ F n)) :
    ∫ u, g u ∂ν ≤ ∑ n, F n * ∫ u, φ n u ∂ν + 2 * ω * ν.real K := by
  rw [← integral_sum_F hφc hφs]
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hpw : ∀ u, g u ≤ ∑ n, F n * φ n u + 2 * ω * K.indicator 1 u := by
    intro u
    by_cases h0 : g u = 0
    · rw [h0]
      have : 0 ≤ K.indicator (1 : ℝ → ℝ) u := indicator_nonneg (fun _ _ => zero_le_one) u
      have := Finset.sum_nonneg fun n (_ : n ∈ Finset.univ) => mul_nonneg (hF0 n) (hφ0 n u)
      positivity
    obtain ⟨h1, h2, h3⟩ := hpt u h0
    rw [indicator_of_mem h2, Pi.one_apply, mul_one]
    calc g u = ∑ n, (g u - 2 * ω) * φ n u + 2 * ω := by
          rw [← Finset.mul_sum, h1]; ring
      _ ≤ ∑ n, F n * φ n u + 2 * ω := by
          refine add_le_add_left (α := ℝ) (Finset.sum_le_sum fun n _ => ?_) _
          by_cases hn : φ n u = 0
          · simp [hn]
          exact mul_le_mul_of_nonneg_right (h3 n hn) (hφ0 n u)
  have hgi : Integrable g ν := hg.integrable_of_hasCompactSupport hgs
  have hKi : Integrable (fun u => 2 * ω * K.indicator (1 : ℝ → ℝ) u) ν :=
    ((integrable_indicator_iff hKm).2 (integrableOn_const hK.measure_lt_top.ne)).const_mul _
  have hSi : Integrable (fun u => ∑ n, F n * φ n u) ν := integrable_finsetSum _ fun n _ =>
    ((hφc n).integrable_of_hasCompactSupport (hφs n)).const_mul (F n)
  calc ∫ u, g u ∂ν ≤ ∫ u, (∑ n, F n * φ n u + 2 * ω * K.indicator 1 u) ∂ν :=
        integral_mono hgi (hSi.add hKi) hpw
    _ = _ := by rw [integral_add hSi hKi, integral_const_mul, integral_indicator_one hKm]

end SWCore
end QuantumZipper
