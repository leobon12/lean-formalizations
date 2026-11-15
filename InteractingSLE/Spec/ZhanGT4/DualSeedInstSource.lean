/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedInstRectangle

/-!
# Alive original sources and their uniform gap bounds

Packet PROVE-ZHAN-GT4-A22. Clearance from a fixed hull enclosure gives a
uniform positive original source gap and a finite upper bound, before the
paths and times are chosen. The image of the full opposite enclosure is a hull.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric
namespace InteractingSLE.ZhanGT4
open QuantumZipper (H IsForwardSol fwdMap fwdHull)

/-- Separation extends to a boundary source, giving a clear source disc. -/
theorem disjoint_ball_of_enclosure_source {F G : Set ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ a ∈ F, ∀ z ∈ G, 2 * δ ≤ ‖a - z‖) {p : ℝ} (hp : (p : ℂ) ∈ closure F) :
    Disjoint (ball (p : ℂ) δ) G := by
  refine Set.disjoint_left.2 fun z hz hzG => ?_
  have hb := le_norm_of_mem_closure hsep hp hzG
  rw [mem_ball, dist_eq_norm, norm_sub_rev] at hz
  linarith

/-- A protected original real source is alive, and its centered real
coordinate has uniform two-sided bounds over all paths inside the enclosure. -/
theorem exists_source_gap_bounds_of_enclosure {E : Set ℂ} (hE : IsHPHull E) {p ρ : ℝ}
    (hρ : 0 < ρ) (hc : Disjoint (ball (p : ℂ) ρ) E) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ (W : ℝ → ℝ) (T : ℝ),
      Continuous W → 0 ≤ T → ((W 0 : ℝ) : ℂ) ∈ closure E → fwdHull W T ⊆ E →
      (∃ q, IsForwardSol W (p : ℂ) T q) ∧
      ∀ t ∈ Icc (0 : ℝ) T, c ≤ |(fwdMap W t p).re| ∧ |(fwdMap W t p).re| ≤ C := by
  obtain ⟨μ, hμ, hd⟩ := exists_deriv_fwdMap_real_bounds hE hρ hc
  obtain ⟨R, hb⟩ := hE.2.1.closure.exists_norm_le
  let R₀ := max R 1
  have hR₀ : 0 < R₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hball : E ⊆ closedBall (0 : ℂ) R₀ := by
    intro z hz
    rw [mem_closedBall_zero_iff]
    exact (hb z (subset_closure hz)).trans (le_max_left _ _)
  refine ⟨ρ / 96 * μ, |p| + 12 * R₀, by positivity, by positivity, ?_⟩
  intro W T hW hT hsrc hK
  have hn : ∀ y : ℝ, (y : ℂ) ∈ ball (p : ℂ) (ρ / 2) → y ≠ W 0 := by
    intro y hy he
    apply notMem_ball_of_mem_closure hc hsrc
    rw [← he]
    exact ball_subset_ball (by linarith) hy
  obtain ⟨q, hq⟩ := exists_isForwardSol_of_disjoint_ball_gen hW
    (hn p (mem_ball_self (by positivity))) hT hρ (hc.mono_right hK)
  refine ⟨⟨q, hq⟩, fun t ht => ?_⟩
  have hKt := ((QuantumZipper.fwdHull_mono).1 ht.2).trans hK
  have hder := (hd W hW t ht.1 hKt hn).2.1
  have hlow := le_norm_fwdMap_real hW ht.1 hρ (hc.mono_right hKt) hn
  have hnorm : ‖fwdMap W t p‖ = |(fwdMap W t p).re| := by
    have hi := fwdMap_real_im hW hq ht
    have he : fwdMap W t p = (((fwdMap W t p).re : ℝ) : ℂ) :=
      Complex.ext rfl (by simpa only [ofReal_im] using hi)
    rw [he, Complex.norm_real, Real.norm_eq_abs]
    rfl
  have hstart : |W 0 - 0| ≤ R₀ := by
    have hm := (hb _ hsrc).trans (le_max_left R 1)
    simpa only [sub_zero, Complex.norm_real, Real.norm_eq_abs] using hm
  have hu := norm_sol_le hW ht.1 hR₀ (hKt.trans hball) hstart (isForwardSol_restrict hq ht.2)
  rw [← fwdMap_eq_of_isForwardSol hW hq ht, hnorm, sub_zero] at hu
  exact ⟨(mul_le_mul_of_nonneg_left (hder.trans (Complex.re_le_norm _))
    (by positivity : 0 ≤ ρ / 96)).trans (hlow.trans_eq hnorm), hu⟩

/-- The full frozen enclosure has an actual hull image in the first chart.
It can be used to bound every opposite image chain at a fixed first prefix. -/
theorem isHPHull_frzChart_enclosure {W : ℝ → ℝ} {S s δ : ℝ} {H₁ H₂ : Set ℂ}
    (hW : Continuous W) (h0 : W 0 = 0) (hS : 0 < S) (hs : s ∈ Icc (0 : ℝ) S)
    (hH₂ : IsHPHull H₂) (hδ : 0 < δ)
    (hsep : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖) (hK : fwdHull W S ⊆ H₁) :
    IsHPHull (frzChart W s '' H₂) := by
  obtain ⟨φ, hφ⟩ := hH₂.exists_isMapOut
  obtain ⟨a, U, ho⟩ := exists_ownData hW h0 hS hH₂ hφ
    ((disjoint_closure_of_le_norm_sub hδ hsep).symm.mono_right (closure_mono hK))
  exact ho.isHPHull_E hs

end InteractingSLE.ZhanGT4
