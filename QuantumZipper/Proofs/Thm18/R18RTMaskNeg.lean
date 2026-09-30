import QuantumZipper.Proofs.Thm18.R18RTMaskAsm
import QuantumZipper.Proofs.Thm18.R18T6Curve
import QuantumZipper.Proofs.Thm18.R18RoundRaw
import QuantumZipper.Proofs.Zipper.B5LocDet
import QuantumZipper.Proofs.Zipper.PStarAreaCoord
import QuantumZipper.Proofs.RS.GenerationBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT2 (D82), geometric input: the unzipped remaining curve avoids the negative half-line

For a driver `W` whose trace `η` is a transient simple curve in `ℍ` with hulls `η(0,t]` (the
Rohde–Schramm facts carried by `Thm18Inputs`), for every `s ≥ 0` the curve of the unzipped driver
`W(s+·) − W(s)` is `f_s(η[s,∞))` (Rohde–Schramm, *Basic properties of SLE*, Ann. Math. 161
(2005), the identity `γ̂_s(t) = g_s ∘ g_{s+t}⁻¹` in the proof of Thm 6.1, p. 23; here
`R18.tendsto_fwdMapInv_shift`) and does not meet `(−∞, 0)`:

* near `u = 0` the trace of the shifted driver is small (`‖f_u⁻¹(z) − z‖ ≤ 6M + 6√u`,
  `B5.norm_fwdMapInv_sub_le`);
* for large `u`, `‖f_s(η(s+u))‖ ≥ ‖η(s+u)‖ − C_s → ∞` (transience, and the same bound for
  `f_s⁻¹`);
* on a compact range of `u > 0`, `f_s(η(s+u))` stays in a compact subset of `ℍ`.

Own elementary argument (compactness), on top of the cited Rohde–Schramm facts.
-/

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

/-- A uniform displacement bound for `f_s⁻¹` on `ℍ`. -/
theorem exists_norm_fwdMapInv_sub_le {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {s : ℝ}
    (hs : 0 ≤ s) : ∃ C : ℝ, ∀ u ∈ H, ‖fwdMapInv W s u - u‖ ≤ C := by
  rcases hs.lt_or_eq with hs | rfl
  · obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := s)).exists_bound_of_continuousOn
      hW.continuousOn
    refine ⟨6 * M + 6 * Real.sqrt s, fun u hu => ?_⟩
    exact B5.norm_fwdMapInv_sub_le hW hW0 hs (fun r hr => by
      have := hM r hr; rwa [Real.norm_eq_abs] at this) hu
  · refine ⟨0, fun u hu => ?_⟩
    rw [E6.fwdMapInv_zero_eq_self hW hW0 hu, sub_self, norm_zero]

/-- The trace of a continuous driver with `V 0 = 0` at a small time is small. -/
theorem norm_trace_le_of_small {V : ℝ → ℝ} (hV : Continuous V) (hV0 : V 0 = 0) {q M : ℝ}
    (hq : 0 < q) (hM : ∀ r ∈ Icc (0 : ℝ) q, |V r| ≤ M) {p : ℂ}
    (hp : Tendsto (fun y : ℝ => fwdMapInv V q (y * Complex.I)) (𝓝[>] 0) (𝓝 p)) :
    ‖p‖ ≤ 6 * M + 6 * Real.sqrt q := by
  have hg : Tendsto (fun y : ℝ => 6 * M + 6 * Real.sqrt q + y) (𝓝[>] 0)
      (𝓝 (6 * M + 6 * Real.sqrt q + 0)) :=
    (tendsto_const_nhds.add tendsto_id).mono_left nhdsWithin_le_nhds
  rw [add_zero] at hg
  refine le_of_tendsto_of_tendsto hp.norm hg ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hyH : (y : ℂ) * Complex.I ∈ H := RS.mul_I_mem_H hy
  have h1 := B5.norm_fwdMapInv_sub_le hV hV0 hq hM hyH
  have h2 : ‖(y : ℂ) * Complex.I‖ = y := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hy]
  calc ‖fwdMapInv V q (y * Complex.I)‖
      ≤ ‖fwdMapInv V q (y * Complex.I) - y * Complex.I‖ + ‖(y : ℂ) * Complex.I‖ := by
        have := norm_add_le (fwdMapInv V q (y * Complex.I) - y * Complex.I) (y * Complex.I)
        simpa using this
    _ ≤ 6 * M + 6 * Real.sqrt q + y := by rw [h2]; linarith

/-- **The unzipped remaining curve avoids the negative half-line** (deterministic). -/
theorem neg_real_not_mem_curveOf_outDrv {W : ℝ → ℝ} (hW : RS.RadialGood W)
    (hinj : InjOn (trace W) (Ici 0)) (hH : ∀ t > (0 : ℝ), trace W t ∈ H)
    (htr : Tendsto (fun t => ‖trace W t‖) atTop atTop) {s : ℝ} (hs : 0 ≤ s)
    (hhull : fwdHull W s = trace W '' Ioc 0 s) {x : ℝ} (hx : x < 0) :
    (x : ℂ) ∉ curveOf (outDrv W s 1) := by
  have hWc := hW.1
  have hW0 := hW.2.1
  set V := RS.shiftDrive W s with hVdef
  have hcong : curveOf (outDrv W s 1) = curveOf V :=
    curveOf_congr fun u hu => by
      simp only [outDrv, hVdef, RS.shiftDrive, one_pow, one_mul, max_eq_left hu, div_one]
  have hVc : Continuous V := (hWc.comp (continuous_const.add continuous_id)).sub continuous_const
  have hV0 : V 0 = 0 := by simp [hVdef, RS.shiftDrive]
  have htend := fun (q : ℝ) (hq : 0 ≤ q) =>
    tendsto_fwdMapInv_shift hW hinj hH hhull hs hq
  -- the value of the shifted trace
  have hval : ∀ q : ℝ, 0 ≤ q →
      trace V q = if q = 0 then 0 else fwdMap W s (trace W (s + q)) :=
    fun q hq => (htend q hq).limUnder_eq
  set a : ℝ := -x with hadef
  have ha : 0 < a := by linarith
  -- small times
  obtain ⟨δ, hδ, hδV⟩ := Metric.continuous_iff.1 hVc 0 (a / 24) (by positivity)
  set q₀ : ℝ := min (δ / 2) ((a / 24) ^ 2) with hq₀
  have hq₀pos : 0 < q₀ := lt_min (by positivity) (by positivity)
  have hsmall : ∀ q : ℝ, 0 ≤ q → q ≤ q₀ → ‖trace V q‖ ≤ a / 2 := by
    intro q hq0 hq
    rcases hq0.lt_or_eq with hq0 | rfl
    · have hM : ∀ r ∈ Icc (0 : ℝ) q, |V r| ≤ a / 24 := by
        intro r hr
        have hr' : dist r 0 < δ := by
          rw [Real.dist_eq, sub_zero, abs_of_nonneg hr.1]
          linarith [hr.2, min_le_left (δ / 2) ((a / 24) ^ 2)]
        have := hδV r hr'
        rw [Real.dist_eq, hV0, sub_zero] at this
        exact this.le
      have hb := norm_trace_le_of_small hVc hV0 hq0 hM (p := trace V q)
        (by rw [hval q hq0.le]; exact htend q hq0.le)
      have hsq : Real.sqrt q ≤ a / 24 := by
        rw [Real.sqrt_le_left (by positivity)]
        linarith [min_le_right (δ / 2) ((a / 24) ^ 2)]
      linarith
    · rw [hval 0 le_rfl, if_pos rfl, norm_zero]; linarith
  -- large times
  obtain ⟨C, hC⟩ := exists_norm_fwdMapInv_sub_le hWc hW0 hs
  obtain ⟨Q₀, hQ₀⟩ := (tendsto_atTop.1 htr (2 * a + C)).exists_forall_of_atTop
  set Q₁ : ℝ := max Q₀ q₀ with hQ₁
  have hlarge : ∀ q : ℝ, Q₁ ≤ q → 2 * a ≤ ‖trace V q‖ := by
    intro q hq
    have hq0 : 0 < q := lt_of_lt_of_le hq₀pos (le_trans (le_max_right _ _) hq)
    rw [hval q hq0.le, if_neg hq0.ne']
    have hmem := trace_mem_compl_hull hinj hH hhull hs hq0
    have hfH : fwdMap W s (trace W (s + q)) ∈ H := FwdHolo.mapsTo_fwdMap hWc hs hmem
    have hinv := RS.fwdMapInv_fwdMap hWc hW0 hs hmem
    have h1 := hC _ hfH
    rw [hinv] at h1
    have h2 := hQ₀ (s + q) (by linarith [le_max_left Q₀ q₀, hq])
    have h3 := norm_sub_le_norm_sub_add_norm_sub (trace W (s + q)) (fwdMap W s (trace W (s + q))) 0
    rw [sub_zero, sub_zero] at h3
    linarith
  -- intermediate times: a compact subset of `ℍ`
  have hcont : ContinuousOn (fun q : ℝ => fwdMap W s (trace W (s + q))) (Icc q₀ Q₁) := by
    intro q hq
    have hq0 : 0 < q := lt_of_lt_of_le hq₀pos hq.1
    have hmem := trace_mem_compl_hull hinj hH hhull hs hq0
    have hca : ContinuousAt (fwdMap W s) (trace W (s + q)) :=
      RS.continuousAt_fwdMap_of_mem_complHull hWc hs hmem
    have htc : ContinuousWithinAt (fun q : ℝ => trace W (s + q)) (Icc q₀ Q₁) q := by
      have h1 : ContinuousWithinAt (trace W) (Ici 0) (s + q) :=
        hW.2.2.2.1 (s + q) (by simp only [mem_Ici]; linarith)
      refine h1.comp (continuous_const.add continuous_id).continuousWithinAt ?_
      intro r hr
      simp only [mem_Ici]
      linarith [hr.1, hq₀pos]
    exact ContinuousAt.comp_continuousWithinAt (g := fwdMap W s)
      (f := fun q : ℝ => trace W (s + q)) hca htc
  have hne : (Icc q₀ Q₁).Nonempty := ⟨q₀, le_rfl, le_max_right _ _⟩
  obtain ⟨q₂, hq₂, hmin⟩ := isCompact_Icc.exists_isMinOn hne
    (Complex.continuous_im.comp_continuousOn hcont)
  set m : ℝ := (fwdMap W s (trace W (s + q₂))).im with hmdef
  have hm : 0 < m := by
    have hq0 : 0 < q₂ := lt_of_lt_of_le hq₀pos hq₂.1
    exact FwdHolo.mapsTo_fwdMap hWc hs (trace_mem_compl_hull hinj hH hhull hs hq0)
  -- conclusion
  set ε : ℝ := min (a / 2) m with hεdef
  have hε : 0 < ε := lt_min (by positivity) hm
  have hfar : ∀ q : ℝ, 0 ≤ q → ε ≤ dist (trace V q) x := by
    intro q hq
    have hxa : ‖(x : ℂ)‖ = a := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg hx]
    by_cases h1 : q ≤ q₀
    · have := hsmall q hq h1
      have h4 := norm_sub_norm_le (x : ℂ) (trace V q)
      rw [dist_comm, dist_eq_norm]
      linarith [min_le_left (a / 2) m]
    by_cases h2 : Q₁ ≤ q
    · have := hlarge q h2
      have h4 := norm_sub_norm_le (trace V q) (x : ℂ)
      rw [dist_eq_norm]
      linarith [min_le_left (a / 2) m]
    push Not at h1 h2
    have hq0 : 0 < q := lt_trans hq₀pos h1
    have hmq : m ≤ (fwdMap W s (trace W (s + q))).im := hmin ⟨h1.le, h2.le⟩
    rw [hval q hq, if_neg hq0.ne', dist_eq_norm]
    have h5 := Complex.abs_im_le_norm (fwdMap W s (trace W (s + q)) - x)
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at h5
    have h6 := le_abs_self (fwdMap W s (trace W (s + q))).im
    linarith [min_le_right (a / 2) m]
  rw [hcong]
  intro hmemC
  have hsub : closure (range fun q : ℚ≥0 => trace V (q : ℝ)) ⊆ {w | ε ≤ dist w x} :=
    closure_minimal (by rintro _ ⟨q, rfl⟩; exact hfar q (by positivity))
      (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have := hsub hmemC
  simp only [mem_setOf_eq, dist_self] at this
  linarith

end R18
end QuantumZipper
