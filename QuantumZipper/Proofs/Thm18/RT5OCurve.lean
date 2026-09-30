import QuantumZipper.Proofs.Thm18.R18RTMaskNeg
import QuantumZipper.Proofs.RS.TraceShift

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D86 input: the unzipped remaining curve meets `ℝ` only at `0`

Two-sided, rescaled form of `R18.neg_real_not_mem_curveOf_outDrv` (R18RTMaskNeg.lean): for a
driver whose trace is a transient simple curve in `ℍ` with hulls `η(0,t]` (Rohde–Schramm facts
carried by `Thm18Inputs`), the curve of `outDrv W s a` (the remaining curve after unzipping by
`s` and rescaling by `a > 0`) contains no real point `x ≠ 0`. The same compactness argument as
there, with `|x|` in place of `−x`, then Brownian scaling of the trace (`RS.trace_scale`).
Own elementary argument (compactness) on top of the cited Rohde–Schramm facts (Rohde–Schramm,
*Basic properties of SLE*, Ann. Math. 161 (2005), proof of Thm 6.1, p. 23).
-/

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

/-- The trace of the shifted driver stays at positive distance from every real `x ≠ 0`. -/
theorem exists_dist_trace_shift_ge {W : ℝ → ℝ} (hW : RS.RadialGood W)
    (hinj : InjOn (trace W) (Ici 0)) (hH : ∀ t > (0 : ℝ), trace W t ∈ H)
    (htr : Tendsto (fun t => ‖trace W t‖) atTop atTop) {s : ℝ} (hs : 0 ≤ s)
    (hhull : fwdHull W s = trace W '' Ioc 0 s) {x : ℝ} (hx : x ≠ 0) :
    ∃ ε > 0, ∀ q : ℝ, 0 ≤ q → ε ≤ dist (trace (RS.shiftDrive W s) q) (x : ℂ) := by
  have hWc := hW.1
  have hW0 := hW.2.1
  set V := RS.shiftDrive W s with hVdef
  have hVc : Continuous V := (hWc.comp (continuous_const.add continuous_id)).sub continuous_const
  have hV0 : V 0 = 0 := by simp [hVdef, RS.shiftDrive]
  have htend := fun (q : ℝ) (hq : 0 ≤ q) =>
    tendsto_fwdMapInv_shift hW hinj hH hhull hs hq
  have hval : ∀ q : ℝ, 0 ≤ q →
      trace V q = if q = 0 then 0 else fwdMap W s (trace W (s + q)) :=
    fun q hq => (htend q hq).limUnder_eq
  set a : ℝ := |x| with hadef
  have ha : 0 < a := abs_pos.2 hx
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
  refine ⟨min (a / 2) m, lt_min (by positivity) hm, fun q hq => ?_⟩
  have hxa : ‖(x : ℂ)‖ = a := by rw [Complex.norm_real, Real.norm_eq_abs]
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

/-- **The rescaled unzipped remaining curve meets `ℝ` only at `0`** (deterministic). -/
theorem real_not_mem_curveOf_outDrv {W : ℝ → ℝ} (hW : RS.RadialGood W)
    (hinj : InjOn (trace W) (Ici 0)) (hH : ∀ t > (0 : ℝ), trace W t ∈ H)
    (htr : Tendsto (fun t => ‖trace W t‖) atTop atTop) {s : ℝ} (hs : 0 ≤ s)
    (hhull : fwdHull W s = trace W '' Ioc 0 s) {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : x ≠ 0) :
    (x : ℂ) ∉ curveOf (outDrv W s a) := by
  have hWc := hW.1
  set V := RS.shiftDrive W s with hVdef
  have hVc : Continuous V := (hWc.comp (continuous_const.add continuous_id)).sub continuous_const
  have hV0 : V 0 = 0 := by simp [hVdef, RS.shiftDrive]
  have hcong : curveOf (outDrv W s a) = curveOf (fun r => V (a ^ 2 * r) / a) :=
    curveOf_congr fun u hu => by
      have hau : 0 ≤ a ^ 2 * u := by positivity
      simp only [outDrv, hVdef, RS.shiftDrive, max_eq_left hu, max_eq_left hau]
  have hax : a * x ≠ 0 := mul_ne_zero ha.ne' hx
  obtain ⟨ε, hε, hfar⟩ := exists_dist_trace_shift_ge hW hinj hH htr hs hhull hax
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  have hpt : ∀ q : ℚ≥0, ε / a ≤ dist (trace (fun r => V (a ^ 2 * r) / a) (q : ℝ)) (x : ℂ) := by
    intro q
    have hq : (0 : ℝ) ≤ a ^ 2 * (q : ℝ) := by positivity
    have hp := tendsto_fwdMapInv_shift hW hinj hH hhull hs hq
    rw [(RS.trace_scale hVc hV0 ha (by positivity) hp).2]
    have h1 := hfar _ hq
    have e : dist (trace V (a ^ 2 * (q : ℝ)) / (a : ℂ)) (x : ℂ) =
        dist (trace V (a ^ 2 * (q : ℝ))) ((a * x : ℝ) : ℂ) / a := by
      rw [dist_eq_norm, dist_eq_norm]
      have : trace V (a ^ 2 * (q : ℝ)) / (a : ℂ) - (x : ℂ) =
          (trace V (a ^ 2 * (q : ℝ)) - ((a * x : ℝ) : ℂ)) / (a : ℂ) := by
        push_cast
        field_simp
      rw [this, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    rw [e]
    exact div_le_div_of_nonneg_right h1 ha.le
  rw [hcong]
  intro hmemC
  have hsub : closure (range fun q : ℚ≥0 => trace (fun r => V (a ^ 2 * r) / a) (q : ℝ)) ⊆
      {w | ε / a ≤ dist w x} :=
    closure_minimal (by rintro _ ⟨q, rfl⟩; exact hpt q)
      (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have := hsub hmemC
  simp only [mem_setOf_eq, dist_self] at this
  have : 0 < ε / a := by positivity
  linarith

end R18
end QuantumZipper
