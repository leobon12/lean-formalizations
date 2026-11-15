/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFin3Integral

/-!
# The actual reflected map on a protected seed band

Packet PROVE-ZHAN-GT4-A22. The enclosure bounds give regularity of the
map itself, including its Loewner time derivative. No generator identity
is assumed, and no ordinary-mark separation is imposed on a seed.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4

namespace SeedData

variable {n : ℕ} (d : SeedData n) {A : Set ℂ} {ε T r a₀ γ Γ lam ρm L M : ℝ}

/-- The actual Loewner time derivative of the reflected map. -/
def mapTime (t x : ℝ) : ℝ := (dHat (ownExt d.W d.W' d.a d.φ t) (d.W t) x).re

/-- On each protected box the reflected map is a regular field. The bound
on the mapped tip is separate from the seed gaps and allows arbitrary seeds. -/
theorem isLogField_map_of_const (h : OwnData d.W A d.φ T d.a d.W')
    (hc : d.SeedConst A ε T r a₀ γ Γ lam ρm) (hL : SeedScaleOK r a₀ γ Γ lam T L)
    (hε : 0 ≤ ε) (hΓ : 0 ≤ Γ) (hM : 0 ≤ M)
    (hA0 : ∀ t ∈ Icc ε T, |d.A 0 t| ≤ M)
    {b c y : ℝ} (hJ : Icc b c ⊆ Icc ε T)
    (hWy : ∀ t ∈ Icc b c, |d.W t - y| < cutRad r a₀ γ) :
    IsLogField (d.F 0) (d.F 1) (d.F 2) (d.F 3) d.mapTime b c y
      (cutRad r a₀ γ) (Real.exp L + Γ + M) := by
  have hJ0 : Icc b c ⊆ Icc 0 T := fun t ht => ⟨hε.trans (hJ ht).1, (hJ ht).2⟩
  obtain ⟨hdisj, hWm, hq0, h3, hsp⟩ := d.piece_space h hc hL hε hJ hWy
  let f : FrzData n := ⟨d.W, d.W', d.a, d.φ, d.κ, d.r, d.ζ₀, fun _ => 0⟩
  have hF : ∀ t ∈ Icc b c, ∀ x : ℝ, |x - y| < 3 * cutRad r a₀ γ → ∀ k,
      HasDerivAt (d.F k t) (d.F (k + 1) t x) x :=
    fun t ht x hx k => h.hasDerivAt_re_iterDeriv_box hJ0 hdisj ht (FrzData.mem_ball_of_near h3 hx) k
  have cF (k : ℕ) : ContinuousOn (fun p : ℝ × ℝ => d.F k p.1 p.2)
      (Icc b c ×ˢ {x | |x - y| < 3 * cutRad r a₀ γ}) :=
    f.continuousOn_F h hJ0 hdisj h3 k
  have hK : Real.exp L ≤ Real.exp L + Γ + M := by linarith
  refine ⟨cutRad_pos hc.r0 hc.a0 hc.g0, by positivity,
    fun t ht x hx => hF t ht x hx 0, fun t ht x hx => hF t ht x hx 1,
    fun t ht x hx => hF t ht x hx 2, ?_, cF 0, cF 1, cF 2, ?_, ?_⟩
  · intro t ht x hx
    exact h.hasDerivWithinAt_re_ownExt_box hJ0 hdisj hWm hq0 ht (FrzData.mem_ball_of_near h3 hx)
  · have hdf0 := (h.continuousOn_dHat_box hJ0 hdisj hWm hq0).comp
      FrzData.continuous_region.continuousOn (FrzData.mapsTo_region (b := b) (c := c) (y := y) h3)
    have hdf := Complex.continuous_re.comp_continuousOn hdf0
    simp only [Function.comp_def] at hdf
    exact hdf
  · intro t ht x hx
    obtain ⟨s1, s0, -, s2, s3, -, sD, -⟩ := hsp t ht x hx
    refine ⟨?_, s1.2.trans hK, s2.trans hK, s3.trans hK, sD.trans hK⟩
    calc |d.F 0 t x| = |(d.F 0 t x - d.A20 t) + (d.A20 t - d.A 0 t) + d.A 0 t| := by ring_nf
         _ ≤ |d.F 0 t x - d.A20 t| + |d.A20 t - d.A 0 t| + |d.A 0 t| :=
           (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
         _ ≤ Real.exp L + Γ + M := add_le_add (add_le_add s0.2 (hc.E0 t (hJ ht)).2) (hA0 t (hJ ht))

/-- Local protected boxes give the actual map field on the whole driver tube. -/
theorem map_tube_facts (h : OwnData d.W A d.φ T d.a d.W')
    (hc : d.SeedConst A ε T r a₀ γ Γ lam ρm) (hL : SeedScaleOK r a₀ γ Γ lam T L)
    (hε : 0 ≤ ε) (hΓ : 0 ≤ Γ) (hM : 0 ≤ M)
    (hA0 : ∀ t ∈ Icc ε T, |d.A 0 t| ≤ M) :
    (∀ p ∈ {p : ℝ × ℝ | p.1 ∈ Icc ε T ∧ |p.2 - d.W p.1| < 3 * cutRad r a₀ γ},
      HasDerivAt (d.F 0 p.1) (d.F 1 p.1 p.2) p.2 ∧
      HasDerivAt (d.F 1 p.1) (d.F 2 p.1 p.2) p.2 ∧
      HasDerivAt (d.F 2 p.1) (d.F 3 p.1 p.2) p.2 ∧
      HasDerivWithinAt (fun s => d.F 0 s p.2) (d.mapTime p.1 p.2) (Icc ε T) p.1 ∧
      (|d.F 0 p.1 p.2| ≤ Real.exp L + Γ + M ∧ |d.F 1 p.1 p.2| ≤ Real.exp L + Γ + M ∧
        |d.F 2 p.1 p.2| ≤ Real.exp L + Γ + M ∧ |d.F 3 p.1 p.2| ≤ Real.exp L + Γ + M ∧
        |d.mapTime p.1 p.2| ≤ Real.exp L + Γ + M)) ∧
    ContinuousOn (fun p : ℝ × ℝ => d.F 0 p.1 p.2)
      {p : ℝ × ℝ | p.1 ∈ Icc ε T ∧ |p.2 - d.W p.1| < 3 * cutRad r a₀ γ} ∧
    ContinuousOn (fun p : ℝ × ℝ => d.F 1 p.1 p.2)
      {p : ℝ × ℝ | p.1 ∈ Icc ε T ∧ |p.2 - d.W p.1| < 3 * cutRad r a₀ γ} ∧
    ContinuousOn (fun p : ℝ × ℝ => d.F 2 p.1 p.2)
      {p : ℝ × ℝ | p.1 ∈ Icc ε T ∧ |p.2 - d.W p.1| < 3 * cutRad r a₀ γ} ∧
    ContinuousOn (fun p : ℝ × ℝ => d.mapTime p.1 p.2)
      {p : ℝ × ℝ | p.1 ∈ Icc ε T ∧ |p.2 - d.W p.1| < 3 * cutRad r a₀ γ} := by
  have hρ := cutRad_pos hc.r0 hc.a0 hc.g0
  refine tube_of_isLogField le_rfl fun t ht => ?_
  obtain ⟨δ, hδ, hδW⟩ := Metric.continuous_iff.1 h.cont t (cutRad r a₀ γ) hρ
  refine ⟨max ε (t - δ / 2), min T (t + δ / 2), box_mem_nhdsWithin_Icc (by positivity),
    ⟨max_le ht.1 (by linarith), le_min ht.2 (by linarith)⟩, ?_⟩
  have hJ : Icc (max ε (t - δ / 2)) (min T (t + δ / 2)) ⊆ Icc ε T := fun s hs =>
    ⟨(le_max_left _ _).trans hs.1, hs.2.trans (min_le_left _ _)⟩
  refine d.isLogField_map_of_const h hc hL hε hΓ hM hA0 hJ fun s hs => ?_
  have h1 : t - δ / 2 ≤ s := (le_max_right _ _).trans hs.1
  have h2 : s ≤ t + δ / 2 := hs.2.trans (min_le_right _ _)
  have := hδW s (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  rwa [Real.dist_eq] at this

end SeedData

end InteractingSLE.ZhanGT4
