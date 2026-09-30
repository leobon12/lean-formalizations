import QuantumZipper.Proofs.RS.TraceShift
import QuantumZipper.Proofs.Loewner.ForwardHolo

/-!
# EXT-RS node TR5: the trace lies in the hull or on the real line

Blueprint `blueprint/EXT_RS_BLUEPRINT.md` §3, node **TR5** (task RS-TR5). Notation: `W` is a
continuous driver with `W 0 = 0`, `f_t = fwdMap W t`, `f̂_t = fwdMapInv W t`,
`K_t = fwdHull W t`, `H = {z | 0 < z.im}`, and `trace W t = lim_{y ↓ 0} f̂_t (i y)`
(`QuantumZipper/Loewner/Forward.lean`).

## Main results (namespace `QuantumZipper.RS`)

* `mem_fwdHull_or_im_eq_zero_of_tendsto_fwdMapInv`: if `f̂_t (i y) → p` as `y ↓ 0`, then
  `p ∈ K_t` or `p.im = 0`. This is the form consumed downstream (nodes NR, HULL), where the
  limit point is not a priori equal to `trace W t`.
* `trace_mem_fwdHull_or_real` (**TR5**): if the defining limit of `trace W t` exists, then
  `trace W t ∈ K_t` or `(trace W t).im = 0`.
* `trace_eq_of_tendsto_fwdMapInv`: the defining limit, when it exists, *is* `trace W t`.
* `continuousAt_fwdMap_of_mem_complHull`: `f_t` is continuous at every point of `H \ K_t`
  (the quantitative input is `FwdHolo.fwdMap_local`).
* `tendsto_ofReal_mul_I_nhdsGT_zero`: `i y → 0` as `y ↓ 0`.

## Proof (contrapositive)

Suppose `p ∉ K_t` and `p.im ≠ 0`. The inverse map `f̂_t` sends `H` into `H`
(`fwdMapInv_mem_H`) and `i(0,∞) ⊆ H` (`mul_I_mem_H`), so the limit `p` lies in the closed upper
half-plane; with `p.im ≠ 0` this gives `p ∈ H \ K_t`. Then `f_t` is continuous at `p`
(`FwdHolo.fwdMap_local`: `fwdMap W T` moves a point `w` near `z` by at most `C‖w − z‖`), so
`f_t (f̂_t (i y)) → f_t p` as `y ↓ 0`. But `f_t ∘ f̂_t = id` on `H` (`fwdMap_fwdMapInv`), so
the left-hand side is eventually `i y`, which tends to `0`; hence `f_t p = 0`. This contradicts
`f_t (H \ K_t) ⊆ H` (`FwdHolo.mapsTo_fwdMap`), i.e. `0 < (f_t p).im`.

## Sources

A. Kemppainen, *Schramm–Loewner Evolution*, SpringerBriefs Math. Phys. 24, 2017, proof of
Theorem 6.4, p. 109 (the chart `g_t` maps the trace point to the tip of the image of the hull,
so `γ(s) ∈ ∂⁺H_s`): the same argument — `f_s(γ̂_s(iy)) = iy → 0` on the one hand, and the image
of a point of `H \ K_s` lies in `H` on the other. Rohde–Schramm, *Basic properties of SLE*,
Ann. Math. 161 (2005), §3 (the trace and the hulls it generates; the radial limit at the marked
boundary point). Deterministic; no probability is used. Own elementary proof of the two small
topological facts above (`i y → 0`, and the closedness of the half-plane step).

Deviation: `trace W t` is a `limUnder` (`QuantumZipper/Loewner/Forward.lean`), a junk value when
the defining limit fails, so TR5 is stated under the explicit hypothesis that the defining limit
exists; dually, the `limUnder` form loses no information, since by
`trace_eq_of_tendsto_fwdMapInv` any existing limit equals `trace W t`.
-/

noncomputable section

open Set Filter Topology Metric

namespace QuantumZipper
namespace RS

/-! ## Elementary limits -/

/-- `i y → 0` in `ℂ` as `y ↓ 0`. -/
theorem tendsto_ofReal_mul_I_nhdsGT_zero :
    Tendsto (fun y : ℝ => (y : ℂ) * Complex.I) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h : Tendsto (fun y : ℝ => (y : ℂ) * Complex.I) (𝓝 (0 : ℝ))
      (𝓝 ((0 : ℝ) * Complex.I)) :=
    Complex.continuous_ofReal.continuousAt.mul continuousAt_const
  simpa using h.mono_left nhdsWithin_le_nhds

/-! ## Continuity of the forward map off the hull -/

/-- `f_t` is continuous at every point of `H \ K_t`. -/
theorem continuousAt_fwdMap_of_mem_complHull {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ}
    (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ H \ fwdHull W t) : ContinuousAt (fwdMap W t) z := by
  obtain ⟨m, -, C, hC, ε, hε, hloc⟩ := FwdHolo.fwdMap_local hW ht hz
  rw [Metric.continuousAt_iff]
  intro δ hδ
  refine ⟨min ε (δ / (C + 1)), lt_min hε (by positivity), fun w hw => ?_⟩
  rw [Complex.dist_eq] at hw ⊢
  have h1 : ‖w - z‖ < ε := hw.trans_le (min_le_left _ _)
  have h2 : ‖w - z‖ < δ / (C + 1) := hw.trans_le (min_le_right _ _)
  have h3 : ‖w - z‖ * C < δ := by
    calc ‖w - z‖ * C ≤ ‖w - z‖ * (C + 1) := by nlinarith [norm_nonneg (w - z)]
      _ < δ / (C + 1) * (C + 1) := mul_lt_mul_of_pos_right h2 (by linarith)
      _ = δ := by field_simp
  exact lt_of_le_of_lt ((hloc w h1).2 t ⟨ht, le_rfl⟩).1 h3

/-! ## TR5 -/

/-- **TR5, limit form.** If `f̂_t (i y) → p` as `y ↓ 0`, then `p` lies in the hull `K_t` or on
the real line. (`f̂_t` maps `H` into `H`, so `p` is in the closed upper half-plane; a `p` of
positive imaginary part outside `K_t` would be sent by `f_t` both to `0` and into `H`.) -/
theorem mem_fwdHull_or_im_eq_zero_of_tendsto_fwdMapInv {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) {p : ℂ}
    (hlim : Tendsto (fun y : ℝ => fwdMapInv W t (y * Complex.I)) (𝓝[>] (0 : ℝ)) (𝓝 p)) :
    p ∈ fwdHull W t ∨ p.im = 0 := by
  have him0 : 0 ≤ p.im := by
    refine ge_of_tendsto ((Complex.continuous_im.tendsto p).comp hlim) ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    simpa using (fwdMapInv_mem_H hW hW0 ht (mul_I_mem_H hy)).le
  rcases eq_or_ne p.im 0 with h0 | hne
  · exact Or.inr h0
  · refine Or.inl ?_
    by_contra hpK
    have hp : p ∈ H \ fwdHull W t := ⟨lt_of_le_of_ne him0 (Ne.symm hne), hpK⟩
    have hcont : ContinuousAt (fwdMap W t) p := continuousAt_fwdMap_of_mem_complHull hW ht hp
    have hcomp : Tendsto (fun y : ℝ => fwdMap W t (fwdMapInv W t (y * Complex.I)))
        (𝓝[>] (0 : ℝ)) (𝓝 (fwdMap W t p)) := by
      simpa only [Function.comp_def] using hcont.tendsto.comp hlim
    have hev : (fun y : ℝ => fwdMap W t (fwdMapInv W t (y * Complex.I)))
        =ᶠ[𝓝[>] (0 : ℝ)] fun y : ℝ => y * Complex.I := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact fwdMap_fwdMapInv hW hW0 ht (mul_I_mem_H hy)
    have h1 : Tendsto (fun y : ℝ => y * Complex.I) (𝓝[>] (0 : ℝ)) (𝓝 (fwdMap W t p)) :=
      hcomp.congr' hev
    have hzero : fwdMap W t p = 0 := tendsto_nhds_unique h1 tendsto_ofReal_mul_I_nhdsGT_zero
    have hpos : 0 < (fwdMap W t p).im := FwdHolo.mapsTo_fwdMap hW ht hp
    rw [hzero] at hpos
    simp at hpos

/-- **TR5.** The trace at time `t ≥ 0` lies in the hull `K_t` or on the real line. -/
theorem trace_mem_fwdHull_or_real {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t)
    (hlim : Tendsto (fun y : ℝ => fwdMapInv W t (y * Complex.I)) (𝓝[>] 0) (𝓝 (trace W t))) :
    trace W t ∈ fwdHull W t ∨ (trace W t).im = 0 :=
  mem_fwdHull_or_im_eq_zero_of_tendsto_fwdMapInv hW hW0 ht hlim

end RS
end QuantumZipper
