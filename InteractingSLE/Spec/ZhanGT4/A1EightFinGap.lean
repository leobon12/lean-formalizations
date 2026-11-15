/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1EightFinD9

/-!
# Zhan's A.1 (Eight): two-sided gap bounds at a protected real point

Packet PROVE-A1-EIGHTFIN. Source: Astra, *Follow-up proofs*, §A.1.3 (`ig1_followup_proofs.txt` L300–L330, (D9)).

A22's fused martingale (`seedAccess_density_facts`) asks for the original source gap of the growing curve,
`c₀ ≤ |Re g_t(x₀) − W_t| ≤ C₀`, uniformly in the curve. For a real point `x₀` whose disc misses the enclosure of the
hull:

* `exists_real_gap_lower`: the lower bound is A6's uniform clearance (`exists_le_norm_fwdMap_uniform`) at points of
  the upper half of the disc, passed to the boundary value (`tendsto_fwdMap_of_isForwardSol`);
* `re_forwardSol_lt_zero`, `abs_driver_le_of_sides`, `abs_re_forwardSol_le`: with protected points on both sides of the
  start, the force points stay on their sides, so they confine the driver, which bounds the gap from above;
* **`exists_real_gap_bounds`**: both bounds, uniform in the driver.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4.A1EightFin

open QuantumZipper (H IsForwardSol fwdMap fwdHull)

/-- **A6's clearance at a protected real point**: a uniform `c > 0` bounds the centered force point of every
continuous driver whose hull stays in the enclosure `G` from below. -/
theorem exists_real_gap_lower {G : Set ℂ} (hG : IsHPHull G) {x ρ : ℝ} (hρ : 0 < ρ)
    (hx : Disjoint (ball (x : ℂ) ρ) G) :
    ∃ c > (0 : ℝ), ∀ W : ℝ → ℝ, Continuous W → ((W 0 : ℝ) : ℂ) ∈ closure G → ∀ T : ℝ, fwdHull W T ⊆ G →
      ∀ u : ℝ → ℂ, IsForwardSol W (x : ℂ) T u → ∀ t ∈ Icc (0 : ℝ) T, c ≤ ‖u t‖ := by
  set S₂ : Set ℂ := ball (x : ℂ) (ρ / 2) ∩ H with hS₂
  have hb : Bornology.IsBounded S₂ := isBounded_ball.subset inter_subset_left
  have hsep : ∀ a ∈ S₂, ∀ z ∈ G, 2 * (ρ / 4) ≤ ‖a - z‖ := by
    intro a ha z hz
    have hzx : ρ ≤ ‖z - x‖ := by
      by_contra hlt
      exact Set.disjoint_left.1 hx (by rw [mem_ball, dist_eq_norm]; linarith) hz
    have hax : ‖a - x‖ < ρ / 2 := by have := ha.1; rwa [mem_ball, dist_eq_norm] at this
    have htri : ‖z - x‖ ≤ ‖a - z‖ + ‖a - x‖ := by
      calc ‖z - x‖ = ‖(a - x) - (a - z)‖ := by ring_nf
        _ ≤ ‖a - x‖ + ‖a - z‖ := norm_sub_le _ _
        _ = ‖a - z‖ + ‖a - x‖ := add_comm _ _
    linarith
  obtain ⟨r, hr, hcl⟩ := exists_le_norm_fwdMap_uniform hG hb inter_subset_right (by positivity) hsep
  refine ⟨r, hr, fun W hW hW0 T hK u hu t ht => ?_⟩
  have hu' : IsForwardSol W (x : ℂ) t u := Ito.isForwardSol_of_le hu ht.1 ht.2
  have htend := tendsto_fwdMap_of_isForwardSol hW ht.1 hu'
  have hne : (𝓝[H] (x : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (by simp)
  have hev : ∀ᶠ z in 𝓝[H] (x : ℂ), r ≤ ‖fwdMap W t z‖ := by
    filter_upwards [inter_mem_nhdsWithin H (ball_mem_nhds (x : ℂ) (by positivity : 0 < ρ / 2))] with z hz
    exact hcl W hW hW0 T hK t ht z ⟨hz.2, hz.1⟩
  exact ge_of_tendsto ((continuous_norm.tendsto _).comp htend) hev

/-- **A force point stays on its side of the driver**: a forward solution from a real point left of the start has
negative real part on its whole interval. -/
theorem re_forwardSol_lt_zero {W : ℝ → ℝ} (hW : Continuous W) {x T : ℝ} {u : ℝ → ℂ} (hu : IsForwardSol W (x : ℂ) T u)
    (hx : x < W 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : (u t).re < 0 := by
  have him : ∀ s ∈ Icc (0 : ℝ) T, (u s).im = 0 := fun s hs => im_eq_zero_of_isForwardSol_real hW hu hs
  have h0 : (u 0).re = x - W 0 := by
    have := (hu.2 0 ⟨le_rfl, ht.1.trans ht.2⟩).2
    rw [intervalIntegral.integral_same, add_zero] at this
    rw [this]
    simp
  by_contra hge
  rw [not_lt] at hge
  have hc : ContinuousOn (fun s => (u s).re) (Icc 0 t) :=
    continuous_re.comp_continuousOn (hu.1.mono (Icc_subset_Icc_right ht.2))
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc ht.1 hc ⟨by rw [h0]; linarith, hge⟩
  have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans ht.2⟩
  apply (hu.2 s hsT).1
  apply Complex.ext
  · simpa using hs0
  · simpa using him s hsT

/-- The mirror statement: right of the start the real part is positive. -/
theorem re_forwardSol_pos {W : ℝ → ℝ} (hW : Continuous W) {x T : ℝ} {u : ℝ → ℂ} (hu : IsForwardSol W (x : ℂ) T u)
    (hx : W 0 < x) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : 0 < (u t).re := by
  have him : ∀ s ∈ Icc (0 : ℝ) T, (u s).im = 0 := fun s hs => im_eq_zero_of_isForwardSol_real hW hu hs
  have h0 : (u 0).re = x - W 0 := by
    have := (hu.2 0 ⟨le_rfl, ht.1.trans ht.2⟩).2
    rw [intervalIntegral.integral_same, add_zero] at this
    rw [this]
    simp
  by_contra hge
  rw [not_lt] at hge
  have hc : ContinuousOn (fun s => (u s).re) (Icc 0 t) :=
    continuous_re.comp_continuousOn (hu.1.mono (Icc_subset_Icc_right ht.2))
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' ht.1 hc ⟨hge, by rw [h0]; linarith⟩
  have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans ht.2⟩
  apply (hu.2 s hsT).1
  apply Complex.ext
  · simpa using hs0
  · simpa using him s hsT

/-- The real part of a forward solution from a real point, as the start minus the driver plus a drift bounded by
`2t/c` when the solution stays at distance `c` from zero. -/
theorem re_forwardSol_eq {W : ℝ → ℝ} {x T c : ℝ} (hc : 0 < c) {u : ℝ → ℂ} (hu : IsForwardSol W (x : ℂ) T u)
    (hcl : ∀ s ∈ Icc (0 : ℝ) T, c ≤ ‖u s‖) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ∃ I : ℝ, (u t).re = x - W t + I ∧ |I| ≤ 2 * T / c := by
  refine ⟨(∫ s in (0 : ℝ)..t, 2 / u s).re, ?_, ?_⟩
  · have := (hu.2 t ht).2
    rw [this]
    simp
  · have hb : ∀ s ∈ uIoc (0 : ℝ) t, ‖2 / u s‖ ≤ 2 / c := by
      intro s hs
      rw [uIoc_of_le ht.1] at hs
      have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.trans ht.2⟩
      have hpos : 0 < ‖u s‖ := hc.trans_le (hcl s hsT)
      rw [norm_div, Complex.norm_two]
      exact div_le_div_of_nonneg_left (by norm_num) hc (hcl s hsT)
    have hI := intervalIntegral.norm_integral_le_of_norm_le_const hb
    calc |(∫ s in (0 : ℝ)..t, 2 / u s).re| ≤ ‖∫ s in (0 : ℝ)..t, 2 / u s‖ := abs_re_le_norm _
      _ ≤ 2 / c * |t - 0| := hI
      _ ≤ 2 * T / c := by
        rw [sub_zero, abs_of_nonneg ht.1, div_mul_eq_mul_div, mul_comm]
        exact div_le_div_of_nonneg_right (by nlinarith [ht.2]) hc.le

/-- **Two protected sides confine the driver**: with forward solutions from real points on both sides of the start,
staying at distance `c` from zero, the driver is bounded by `|xl| + |xr| + 2T/c`. -/
theorem abs_driver_le_of_sides {W : ℝ → ℝ} (hW : Continuous W) {xl xr T c : ℝ} (hc : 0 < c)
    {ul ur : ℝ → ℂ} (hl : IsForwardSol W (xl : ℂ) T ul) (hr : IsForwardSol W (xr : ℂ) T ur) (hxl : xl < W 0)
    (hxr : W 0 < xr) (hcl : ∀ s ∈ Icc (0 : ℝ) T, c ≤ ‖ul s‖) (hcr : ∀ s ∈ Icc (0 : ℝ) T, c ≤ ‖ur s‖) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) : |W t| ≤ |xl| + |xr| + 2 * T / c := by
  obtain ⟨Il, hl1, hl2⟩ := re_forwardSol_eq hc hl hcl ht
  obtain ⟨Ir, hr1, hr2⟩ := re_forwardSol_eq hc hr hcr ht
  have h1 := re_forwardSol_lt_zero hW hl hxl ht
  have h2 := re_forwardSol_pos hW hr hxr ht
  rw [abs_le] at hl2 hr2 ⊢
  have := le_abs_self xl
  have := neg_abs_le xl
  have := le_abs_self xr
  have := neg_abs_le xr
  constructor <;> linarith

/-- **Two-sided gap bounds at a protected real point**: for an enclosure `G` and real points `xl`, `xr` whose discs
miss `G`, there are `0 < c` and `C` such that for every continuous driver starting in `closure G` strictly between
`xl` and `xr`, with hull in `G` up to `T ≤ Tm`, `c ≤ |Re g_t(xl) − W_t| ≤ C` on `[0, T]`. -/
theorem exists_real_gap_bounds {G : Set ℂ} (hG : IsHPHull G) {xl xr ρ : ℝ} (hρ : 0 < ρ)
    (hl : Disjoint (ball (xl : ℂ) ρ) G) (hr : Disjoint (ball (xr : ℂ) ρ) G) (Tm : ℝ) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ W : ℝ → ℝ, Continuous W → ((W 0 : ℝ) : ℂ) ∈ closure G → xl < W 0 →
      W 0 < xr → ∀ T : ℝ, 0 ≤ T → T ≤ Tm → fwdHull W T ⊆ G → ∀ t ∈ Icc (0 : ℝ) T,
        c ≤ |(fwdMap W t xl).re| ∧ |(fwdMap W t xl).re| ≤ C := by
  obtain ⟨cl, hcl, hlow⟩ := exists_real_gap_lower hG hρ hl
  obtain ⟨cr, hcr, hrow⟩ := exists_real_gap_lower hG hρ hr
  set c := min cl cr with hcdef
  have hc : 0 < c := lt_min hcl hcr
  refine ⟨c, 2 * |xl| + |xr| + 4 * |Tm| / c, hc, by positivity, ?_⟩
  intro W hW hW0 hxl hxr T hT hTm hK t ht
  obtain ⟨ul, hul⟩ := exists_isForwardSol_of_disjoint_ball_gen hW hxl.ne hT hρ (hl.mono_right hK)
  obtain ⟨ur, hur⟩ := exists_isForwardSol_of_disjoint_ball_gen hW hxr.ne' hT hρ (hr.mono_right hK)
  have hcl' : ∀ s ∈ Icc (0 : ℝ) T, c ≤ ‖ul s‖ := fun s hs => (min_le_left _ _).trans (hlow W hW hW0 T hK ul hul s hs)
  have hcr' : ∀ s ∈ Icc (0 : ℝ) T, c ≤ ‖ur s‖ := fun s hs => (min_le_right _ _).trans (hrow W hW hW0 T hK ur hur s hs)
  rw [fwdMap_eq_of_isForwardSol hW hul ht]
  have him := im_eq_zero_of_isForwardSol_real hW hul ht
  have hre : |(ul t).re| = ‖ul t‖ := by
    have e : ul t = ((ul t).re : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [e, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
  refine ⟨hre ▸ hcl' t ht, ?_⟩
  obtain ⟨Il, hl1, hl2⟩ := re_forwardSol_eq hc hul hcl' ht
  have hWt := abs_driver_le_of_sides hW hc hul hur hxl hxr hcl' hcr' ht
  have hT' : 2 * T / c ≤ 2 * |Tm| / c := div_le_div_of_nonneg_right (by linarith [le_abs_self Tm]) hc.le
  rw [hl1]
  calc |xl - W t + Il| ≤ |xl| + |W t| + |Il| := by
        have := abs_add_le (xl - W t) Il
        have := abs_sub xl (W t)
        linarith
    _ ≤ 2 * |xl| + |xr| + 4 * |Tm| / c := by
        have e : 4 * |Tm| / c = 2 * |Tm| / c + 2 * |Tm| / c := by ring
        linarith

end InteractingSLE.ZhanGT4.A1EightFin
