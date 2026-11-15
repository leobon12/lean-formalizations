/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFusedScale

/-!
# The fused field's regular boxes from D9

Packet PROVE-ZHAN-GT4-A22. Choose the radius and bound uniformly before
the growing driver, image chain, time horizon and box. The raw log-field
regularity is proved by the landed D9 theorem, rather than assumed.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric
namespace InteractingSLE.ZhanGT4
open QuantumZipper (IsForwardSol fwdMap)

/-- D9 and the separated-source gap give uniform regular boxes for the
actual fused field. Constants may depend on the fixed frozen configuration
and reduced charges, but not on the growing path, horizon or center. -/
theorem exists_seedAccess_piece_constants {n : ℕ} (κ : ℝ) (rr : Fin n → ℝ)
    {r a₀ γ Γ lam L Tm c₀ C₀ : ℝ} (hr : 0 < r) (ha : 0 < a₀) (hg : 0 < γ)
    (hc : 0 < c₀) (hC : 0 ≤ C₀) (hL : ScaleOK r a₀ γ Γ lam Tm L) :
    ∃ ρ K : ℝ, 0 < ρ ∧ 0 ≤ K ∧
      ∀ (d : FrzData n) {A : Set ℂ} {T p : ℝ},
        d.κ = κ → d.r = rr → T ≤ Tm →
        OwnData d.W A d.φ T d.a d.W' →
        d.D9Const A T r a₀ γ Γ lam →
        (∃ q₀, IsForwardSol d.W' d.ζ₀ (d.a T) q₀) →
        (∀ m, ∃ q, IsForwardSol d.W' (d.ζ m) (d.a T) q) →
        (∀ m, d.ζ m ≠ d.ζ₀) → Function.Injective d.ζ →
        (∃ qS, IsForwardSol d.W (p : ℂ) T qS) →
        (∀ t ∈ Icc (0 : ℝ) T, c₀ ≤ |(fwdMap d.W t p).re| ∧ |(fwdMap d.W t p).re| ≤ C₀) →
        ∀ {b c y : ℝ}, Icc b c ⊆ Icc 0 T →
          (∀ t ∈ Icc b c, |d.W t - y| < ρ) →
          IsLogField (d.seedAccessEll p) (d.seedAccessX p) (d.seedAccessXX p)
            (d.seedAccessXXX p) (d.seedAccessT p) b c y ρ K := by
  obtain ⟨Ls, hLs, hGs, hxs⟩ := exists_seedAccessScale (C := C₀) hc (by linarith only [hC, hc]) Tm
  let ρ := min (cutRad r a₀ γ) (c₀ / 8)
  have hρ : 0 < ρ := lt_min (cutRad_pos hr ha hg) (by positivity)
  have hρr : ρ ≤ cutRad r a₀ γ := min_le_left _ _
  have hρs : ρ ≤ c₀ / 8 := min_le_right _ _
  let K₀ := 2 * coefTot κ rr * scaleBound L
  have hK₀ : 0 ≤ K₀ := mul_nonneg (mul_nonneg (by norm_num) (coefTot_ge (κ := κ) (r := rr)).2.2.2)
    (hL.L0.trans (le_scaleBound hL.L0).1)
  refine ⟨ρ, seedAccessBound κ (-1 / 2 + ∑ m, rr m) K₀ Ls (c₀ / 2), hρ,
    seedAccessBound_nonneg hK₀ hLs (half_pos hc), ?_⟩
  intro d A T p hdκ hdr hTm h hd9 hq₀ hq hζ₀ hζ hqS hgap b c y hJ hWy
  obtain ⟨q₀, hq₀⟩ := hq₀
  choose q hq using hq
  obtain ⟨qS, hqS⟩ := hqS
  have hLT : ScaleOK r a₀ γ Γ lam T L := { hL with
    logF := (mul_le_mul_of_nonneg_right hTm (by unfold rateBound; positivity)).trans hL.logF }
  have hWy' : ∀ t ∈ Icc b c, |d.W t - y| < cutRad r a₀ γ :=
    fun t ht => (hWy t ht).trans_le hρr
  have hraw := (d.isLogField_of_D9 h hq₀ hq hζ₀ hζ hJ hd9 hLT hWy').mono_radius hρ hρr
  obtain ⟨hdisj, hWm, hn, h3, hsp⟩ := d.piece_facts h hJ hd9 hLT hWy'
  have hnear : ∀ x : ℝ, |x - y| < 3 * ρ → |x - y| < 3 * cutRad r a₀ γ :=
    fun _ hx => lt_of_lt_of_le hx (mul_le_mul_of_nonneg_left hρr (by norm_num))
  have hnd : ∀ t ∈ Icc b c, ∀ x : ℝ, |x - y| < 3 * ρ →
      d.F 1 t x ≠ 0 ∧ d.F 0 t x - d.A20 t ≠ 0 ∧ ∀ m, d.F 0 t x - d.B0 t m ≠ 0 := by
    intro t ht x hx
    obtain ⟨s1, s0, sm, -⟩ := hsp t ht x (hnear x hx)
    exact ⟨SeedData.ne_zero_of_inScale s1, SeedData.ne_zero_of_inScale s0,
      fun m => SeedData.ne_zero_of_inScale (sm m)⟩
  have hspatial : ∀ t ∈ Icc b c, ∀ x : ℝ, |x - y| < 3 * ρ →
      c₀ / 2 ≤ |x - d.seedAccessSource p t| ∧ InScale Ls (x - d.seedAccessSource p t) := by
    intro t ht x hx
    have he : d.seedAccessSource p t - d.W t = (fwdMap d.W t p).re := by
      simp only [FrzData.seedAccessSource, add_sub_cancel_right]
    exact hxs hρs (hWy t ht) hx (he ▸ (hgap t (hJ ht)).1) (he ▸ (hgap t (hJ ht)).2)
  have htbound : 2 * T / (c₀ / 2) ^ 2 ≤ Ls :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hTm (by norm_num)) (by positivity)).trans hGs
  have hh := d.isLogField_seedAccess h hq₀ hq hζ₀ hζ hqS hJ hdisj hWm hn
    ((mul_le_mul_of_nonneg_left hρr (by norm_num)).trans h3) hnd hraw hLs (half_pos hc) htbound
    (fun t ht => (half_le_self hc.le).trans (hgap t ht).1) hspatial
  simpa only [hdκ, hdr, FrzData.seedAccessExponent, K₀] using hh

end InteractingSLE.ZhanGT4
