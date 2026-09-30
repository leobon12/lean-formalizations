import QuantumZipper.Proofs.Thm18.ASepHopf

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP (b): the geometric hypothesis `hgeo` of `det_unif_gen` for the `τ' = 0` family

The deterministic node `G4Core.det_unif_gen` (G4SepUC2Det.lean) needs maps `g_p` with
`g_p(w) ∈ ℍ`, `Im g_p(w) ≥ c · Im w` and `‖g_p(w)‖ ≤ R_b` for **all** `w ∈ ℍ` in a ball. For the
A-sep family at `τ' = 0` (D84) the map is `g_p(w) = f_τ(a w)` (`= a ψ_p(w)` on the image of the
re-zipping map, `mul_revMapInv_revDrv0_eq`), and these bounds hold, uniformly over a parameter
box, on the points whose forward trajectory stays at distance `≥ m` from the singularity:

* `norm_fwdMap_le_of_lower`: `‖f_t(z)‖ ≤ ‖z‖ + |W t| + 2t/m` (integral equation);
* `geo_fwdMap_scaled`: the three bounds for `w ↦ f_τ(a w)`, with `c = a₀ exp(−2T/m²)`;
* `geo_piecewise`: off a set carrying the source measure the map can be replaced by the identity,
  which keeps the pushforward and gives the bounds everywhere.

Own elementary argument (Loewner integral equation, Lawler, *Conformally invariant processes in
the plane*, §4.1).
-/

noncomputable section

open MeasureTheory Set

namespace QuantumZipper
namespace ASep

/-- Size of the forward map along a trajectory bounded away from the singularity. -/
theorem norm_fwdMap_le_of_lower {W : ℝ → ℝ} (hW : Continuous W) {z : ℂ} (hz : 0 < z.im)
    {T m : ℝ} (hm : 0 < m) {u : ℝ → ℂ} (hu : IsForwardSol W z T u)
    (hlow : ∀ s ∈ Icc (0 : ℝ) T, m ≤ ‖u s‖) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖fwdMap W t z‖ ≤ ‖z‖ + |W t| + 2 * t / m := by
  rw [fwdMap_eq hW hz hu ht, (hu.2 t ht).2]
  have hI : ‖∫ s in (0 : ℝ)..t, 2 / u s‖ ≤ 2 / m * |t - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
    rw [uIoc_of_le ht.1] at hs
    have h1 : m ≤ ‖u s‖ := hlow s ⟨hs.1.le, hs.2.trans ht.2⟩
    rw [norm_div, Complex.norm_ofNat]
    exact div_le_div_of_nonneg_left (by norm_num) hm h1
  rw [sub_zero, abs_of_nonneg ht.1] at hI
  have hW' : ‖((W t : ℝ) : ℂ)‖ = |W t| := Complex.norm_real _
  calc ‖z - ((W t : ℝ) : ℂ) + ∫ s in (0 : ℝ)..t, 2 / u s‖
      ≤ ‖z - ((W t : ℝ) : ℂ)‖ + ‖∫ s in (0 : ℝ)..t, 2 / u s‖ := norm_add_le _ _
    _ ≤ ‖z‖ + ‖((W t : ℝ) : ℂ)‖ + 2 / m * t := by
        gcongr; exact norm_sub_le _ _
    _ = ‖z‖ + |W t| + 2 * t / m := by rw [hW']; ring

/-- **The three geometric bounds for `w ↦ f_τ(a w)`.** -/
theorem geo_fwdMap_scaled {W : ℝ → ℝ} (hW : Continuous W) {T m a₀ a τ : ℝ} (hm : 0 < m)
    (ha₀ : 0 < a₀) (ha : a₀ ≤ a) (hτ : τ ∈ Icc (0 : ℝ) T) {w : ℂ} (hw : 0 < w.im)
    (hsol : ∃ u, IsForwardSol W ((a : ℂ) * w) T u)
    (hlow : ∀ s ∈ Icc (0 : ℝ) T, m ≤ ‖fwdMap W s ((a : ℂ) * w)‖) :
    fwdMap W τ ((a : ℂ) * w) ∈ H ∧
      a₀ * Real.exp (-2 * T / m ^ 2) * w.im ≤ (fwdMap W τ ((a : ℂ) * w)).im ∧
      ‖fwdMap W τ ((a : ℂ) * w)‖ ≤ a * ‖w‖ + |W τ| + 2 * T / m := by
  have ha0 : 0 < a := ha₀.trans_le ha
  have haw : 0 < ((a : ℂ) * w).im := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    positivity
  have him := im_fwdMap_ge_of_lower hW haw hm hsol hlow hτ
  have hawim : ((a : ℂ) * w).im = a * w.im := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rw [hawim] at him
  have hE : 0 < Real.exp (-2 * T / m ^ 2) := Real.exp_pos _
  have hlow1 : a₀ * Real.exp (-2 * T / m ^ 2) * w.im ≤ a * w.im * Real.exp (-2 * T / m ^ 2) := by
    have := mul_le_mul_of_nonneg_right ha (mul_nonneg hw.le hE.le)
    nlinarith
  refine ⟨?_, hlow1.trans him, ?_⟩
  · show 0 < (fwdMap W τ ((a : ℂ) * w)).im
    exact lt_of_lt_of_le (by positivity) him
  · obtain ⟨u, hu⟩ := hsol
    have hl : ∀ s ∈ Icc (0 : ℝ) T, m ≤ ‖u s‖ := fun s hs => by
      rw [← fwdMap_eq hW haw hu hs]; exact hlow s hs
    have h := norm_fwdMap_le_of_lower hW haw hm hu hl hτ
    have e : ‖(a : ℂ) * w‖ = a * ‖w‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha0.le]
    have hτT : 2 * τ / m ≤ 2 * T / m := by
      have := hτ.2; gcongr
    rw [e] at h
    linarith

/-- **Modification off the support.** Replacing `g` by the identity off a measurable set `N`
carrying `μ` keeps `μ.map g` and makes the geometric bounds hold on all of `ℍ ∩ {‖w‖ ≤ R_a}`. -/
theorem geo_piecewise {N : Set ℂ} (hN : MeasurableSet N) [DecidablePred (· ∈ N)] {g : ℂ → ℂ}
    (hg : Measurable g) {c Ra Rb : ℝ} (hc1 : c ≤ 1) (hRab : Ra ≤ Rb)
    (hgeo : ∀ w ∈ N, w ∈ H → ‖w‖ ≤ Ra → g w ∈ H ∧ c * w.im ≤ (g w).im ∧ ‖g w‖ ≤ Rb) :
    Measurable (N.piecewise g id) ∧
      (∀ w ∈ H, ‖w‖ ≤ Ra →
        N.piecewise g id w ∈ H ∧ c * w.im ≤ (N.piecewise g id w).im ∧
          ‖N.piecewise g id w‖ ≤ Rb) ∧
      ∀ μ : Measure ℂ, μ Nᶜ = 0 → μ.map (N.piecewise g id) = μ.map g := by
  refine ⟨hg.piecewise hN measurable_id, fun w hw hwR => ?_, fun μ hμ => ?_⟩
  · by_cases hwN : w ∈ N
    · rw [piecewise_eq_of_mem _ _ _ hwN]; exact hgeo w hwN hw hwR
    · rw [piecewise_eq_of_notMem _ _ _ hwN]
      have hwpos : 0 < w.im := hw
      refine ⟨hw, ?_, hwR.trans hRab⟩
      show c * w.im ≤ w.im
      nlinarith
  · refine Measure.map_congr ?_
    filter_upwards [(mem_ae_iff.2 hμ : N ∈ ae μ)] with w hw
    exact piecewise_eq_of_mem _ _ _ hw

end ASep
end QuantumZipper
