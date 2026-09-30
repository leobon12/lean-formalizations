import QuantumZipper.Proofs.Zipper.D3PlusN2H3WinPsi

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2-H3 on folded circles: the deterministic core of the lateral/radial splitting

Task N2H3-SPLITWIN. Deterministic core of `N2H3SplitWinCircStmt` (`D3PlusN2H3WinCirc.lean`):
three field samples `M` (model), `Y` (lateral data) and `Z` (local field) which, on the local
dyadic folded circles, satisfy

  `M(fc) = Z(fc) + ∫ α(−log‖u‖) dfc + c₀`,   `Y(fc) = Z(fc) − ∫ ψ(‖u‖) dfc`,

where `ψ` is a log-dominated radial profile (`LogDom`, the radial part `h_{|u|}(0)` of `Z`), and
whose dyadic circle averages `Z(fc(dₙ w, 2^{−k}))` converge (to `Φ k w`). Then, at every finite
measure `ν` carried by a compact part of `Hbar \ {0}` inside the window, with `log‖·‖`
integrable, at which the regularizations `∫ Φ k dν` converge,

  `evalReg M ν = evalReg Y ν + ∫ (ψ(‖w‖) + α(−log‖w‖) + c₀) dν`

(`evalReg_split_core`). This is the pathwise form of DMS arXiv:1409.7055 p. 77–78,
`h = h† + h_{|·|}(0)`: the lateral part is the field minus its radial part, and the regularized
evaluation commutes with this splitting. Own elementary argument (dominated convergence and the
circle-smoothing lemmas of `D3PlusN2H3WinPsi.lean`).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace QuantumZipper
namespace D3Plus

/-- Circle-smoothing of a radial profile at radius `s`. -/
def radJ (ψ : ℝ → ℝ) (s : ℝ) (w : ℂ) : ℝ := ∫ u, ψ ‖u‖ ∂foldedCircle w s

theorem LogDom.aestronglyMeasurable_radJ {ψ : ℝ → ℝ} {R C D : ℝ} (h : LogDom ψ R C D) {s m : ℝ}
    (hs : 0 < s) (hms : m + s < R) {ν : Measure ℂ} (hν : ∀ᵐ w ∂ν, ‖w‖ ≤ m) :
    AEStronglyMeasurable (radJ ψ s) ν := by
  set S : Set ℂ := Metric.ball 0 (R - s) with hS
  have hc : ContinuousOn (radJ ψ s) S := by
    intro w hw
    have hw' : ‖w‖ + s < R := by
      rw [hS, Metric.mem_ball, dist_zero_right] at hw; linarith
    refine ContinuousAt.continuousWithinAt ?_
    exact tendsto_nhds_iff_seq_tendsto.2 fun c hc => h.tendsto_fc_center hs hc hw'
  have hνS : ∀ᵐ w ∂ν, w ∈ S := by
    filter_upwards [hν] with w hw
    rw [hS, Metric.mem_ball, dist_zero_right]; linarith
  rw [← Measure.restrict_eq_self_of_ae_mem hνS]
  exact hc.aestronglyMeasurable Metric.isOpen_ball.measurableSet

theorem log_div_norm {R : ℝ} (hR : 0 < R) {w : ℂ} (hw : w ≠ 0) :
    Real.log (R / ‖w‖) = Real.log R - Real.log ‖w‖ :=
  Real.log_div hR.ne' (norm_ne_zero_iff.2 hw)

/-- The logarithmic bound is integrable. -/
theorem integrable_logBound {R C D : ℝ} {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hlog : Integrable (fun w => Real.log ‖w‖) ν) :
    Integrable (fun w : ℂ => C + D * (Real.log R - Real.log ‖w‖)) ν :=
  (integrable_const C).add (((integrable_const (Real.log R)).sub hlog).const_mul D)

theorem LogDom.integrable_radJ {ψ : ℝ → ℝ} {R C D : ℝ} (h : LogDom ψ R C D) (hR : 0 < R)
    {s m : ℝ} (hs : 0 < s) (hms : m + s < R) {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hν : ∀ᵐ w ∂ν, w ∈ Hbar ∧ w ≠ 0 ∧ ‖w‖ ≤ m)
    (hlog : Integrable (fun w => Real.log ‖w‖) ν) : Integrable (radJ ψ s) ν := by
  refine (integrable_logBound (R := R) (C := C) (D := D) hlog).mono'
    (h.aestronglyMeasurable_radJ hs hms (hν.mono fun w hw => hw.2.2)) ?_
  filter_upwards [hν] with w hw
  rw [Real.norm_eq_abs, ← log_div_norm hR hw.2.1]
  exact h.abs_integral_fc_le hs (by linarith [hw.2.2]) hw.2.1

theorem LogDom.integrable_comp_norm {ψ : ℝ → ℝ} {R C D : ℝ} (h : LogDom ψ R C D) (hR : 0 < R)
    {m : ℝ} (hmR : m ≤ R) {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hν : ∀ᵐ w ∂ν, w ∈ Hbar ∧ w ≠ 0 ∧ ‖w‖ ≤ m)
    (hlog : Integrable (fun w => Real.log ‖w‖) ν) : Integrable (fun w : ℂ => ψ ‖w‖) ν := by
  refine (integrable_logBound (R := R) (C := C) (D := D) hlog).mono'
    (h.1.comp measurable_norm).aestronglyMeasurable ?_
  filter_upwards [hν] with w hw
  rw [Real.norm_eq_abs, ← log_div_norm hR hw.2.1]
  exact h.2.2.2 ‖w‖ (norm_pos_iff.2 hw.2.1) (hw.2.2.trans hmR)

/-- Dominated convergence of the circle-smoothings: `∫ radJ ψ 2^{−k} dν → ∫ ψ(‖w‖) dν`. -/
theorem LogDom.tendsto_integral_radJ {ψ : ℝ → ℝ} {R C D : ℝ} (h : LogDom ψ R C D) (hR : 0 < R)
    {m : ℝ} (hmR : m < R) {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hν : ∀ᵐ w ∂ν, w ∈ Hbar ∧ w ≠ 0 ∧ ‖w‖ ≤ m)
    (hlog : Integrable (fun w => Real.log ‖w‖) ν) :
    Tendsto (fun k => ∫ w, radJ ψ (radius k) w ∂ν) atTop (𝓝 (∫ w, ψ ‖w‖ ∂ν)) := by
  have hev : ∀ᶠ k in atTop, radius k < R - m :=
    (RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).eventually
      (gt_mem_nhds (by linarith))
  refine tendsto_integral_filter_of_dominated_convergence
    (fun w : ℂ => C + D * (Real.log R - Real.log ‖w‖)) ?_ ?_ (integrable_logBound hlog) ?_
  · filter_upwards [hev] with k hk
    exact h.aestronglyMeasurable_radJ (radius_pos k) (by linarith) (hν.mono fun w hw => hw.2.2)
  · filter_upwards [hev] with k hk
    filter_upwards [hν] with w hw
    rw [Real.norm_eq_abs, ← log_div_norm hR hw.2.1]
    exact h.abs_integral_fc_le (radius_pos k) (by linarith [hw.2.2]) hw.2.1
  · filter_upwards [hν] with w hw
    exact h.tendsto_fc_radius hw.1 hw.2.1

/-- Dyadic rounding stays in the window eventually. -/
theorem eventually_dyadic_le {w : ℂ} {s r₁ : ℝ} (hw : ‖w‖ + s < r₁) :
    ∀ᶠ n in atTop, ‖dyadicRoundC n w‖ + s ≤ r₁ := by
  have hδ : 0 < r₁ - (‖w‖ + s) := by linarith
  filter_upwards [(RegClosure.tendsto_dyadicRoundC w).eventually (Metric.ball_mem_nhds w hδ)]
    with n hn
  rw [dist_eq_norm] at hn
  have := norm_sub_norm_le (dyadicRoundC n w) w
  linarith

section Core

variable {M Y Z : FieldSample} {Φ : ℕ → ℂ → ℝ} {ψ : ℝ → ℝ} {α c₀ r₁ R Cψ Dψ : ℝ}

theorem avgReg_model_eq (hR : 0 < R) (hr₁R : r₁ ≤ R)
    (hM : ∀ n k, ∀ c ∈ range (dyadicRoundC n), ‖c‖ + radius k ≤ r₁ →
      M (foldedCircle c (radius k)) = Z (foldedCircle c (radius k)) +
        ∫ u, α * -Real.log ‖u‖ ∂foldedCircle c (radius k) + c₀)
    (hZ : ∀ k, ∀ w ∈ Hbar, ‖w‖ + radius k < r₁ →
      Tendsto (fun n => Z (foldedCircle (dyadicRoundC n w) (radius k))) atTop (𝓝 (Φ k w)))
    {k : ℕ} {w : ℂ} (hw : w ∈ Hbar) (hwk : ‖w‖ + radius k < r₁) :
    avgReg M k w = Φ k w + radJ (fun ρ => α * -Real.log ρ) (radius k) w + c₀ := by
  unfold avgReg
  apply Tendsto.limUnder_eq
  have hJ := (logDom_neg_log α hR).tendsto_fc_center (radius_pos k)
    (RegClosure.tendsto_dyadicRoundC w) (by linarith : ‖w‖ + radius k < R)
  refine (((hZ k w hw hwk).add hJ).add_const c₀).congr' ?_
  filter_upwards [eventually_dyadic_le hwk] with n hn
  rw [hM n k _ (Set.mem_range_self w) hn]

theorem avgReg_lat_eq (h : LogDom ψ R Cψ Dψ) (hr₁R : r₁ ≤ R)
    (hY : ∀ n k, ∀ c ∈ range (dyadicRoundC n), ‖c‖ + radius k ≤ r₁ →
      Y (foldedCircle c (radius k)) = Z (foldedCircle c (radius k)) -
        ∫ u, ψ ‖u‖ ∂foldedCircle c (radius k))
    (hZ : ∀ k, ∀ w ∈ Hbar, ‖w‖ + radius k < r₁ →
      Tendsto (fun n => Z (foldedCircle (dyadicRoundC n w) (radius k))) atTop (𝓝 (Φ k w)))
    {k : ℕ} {w : ℂ} (hw : w ∈ Hbar) (hwk : ‖w‖ + radius k < r₁) :
    avgReg Y k w = Φ k w - radJ ψ (radius k) w := by
  unfold avgReg
  apply Tendsto.limUnder_eq
  have hJ := h.tendsto_fc_center (radius_pos k) (RegClosure.tendsto_dyadicRoundC w)
    (by linarith : ‖w‖ + radius k < R)
  refine ((hZ k w hw hwk).sub hJ).congr' ?_
  filter_upwards [eventually_dyadic_le hwk] with n hn
  rw [hY n k _ (Set.mem_range_self w) hn]

/-- **The deterministic core of the lateral/radial splitting.** -/
theorem evalReg_split_core (h : LogDom ψ R Cψ Dψ) (hR : 0 < R) (hr₁R : r₁ ≤ R) {m : ℝ}
    (hm : m < r₁)
    (hM : ∀ n k, ∀ c ∈ range (dyadicRoundC n), ‖c‖ + radius k ≤ r₁ →
      M (foldedCircle c (radius k)) = Z (foldedCircle c (radius k)) +
        ∫ u, α * -Real.log ‖u‖ ∂foldedCircle c (radius k) + c₀)
    (hY : ∀ n k, ∀ c ∈ range (dyadicRoundC n), ‖c‖ + radius k ≤ r₁ →
      Y (foldedCircle c (radius k)) = Z (foldedCircle c (radius k)) -
        ∫ u, ψ ‖u‖ ∂foldedCircle c (radius k))
    (hZ : ∀ k, ∀ w ∈ Hbar, ‖w‖ + radius k < r₁ →
      Tendsto (fun n => Z (foldedCircle (dyadicRoundC n w) (radius k))) atTop (𝓝 (Φ k w)))
    {ν : Measure ℂ} [IsFiniteMeasure ν] (hν : ∀ᵐ w ∂ν, w ∈ Hbar ∧ w ≠ 0 ∧ ‖w‖ ≤ m)
    (hlog : Integrable (fun w => Real.log ‖w‖) ν)
    (hΦi : ∀ᶠ k in atTop, Integrable (Φ k) ν) {l : ℝ}
    (hΦ : Tendsto (fun k => ∫ w, Φ k w ∂ν) atTop (𝓝 l)) :
    Integrable (fun w : ℂ => ψ ‖w‖) ν ∧
      evalReg M ν = evalReg Y ν + ∫ w, (ψ ‖w‖ + α * -Real.log ‖w‖ + c₀) ∂ν := by
  have hα := logDom_neg_log α hR
  have hmR : m < R := hm.trans_le hr₁R
  have hev : ∀ᶠ k in atTop, radius k < r₁ - m :=
    (RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).eventually
      (gt_mem_nhds (by linarith))
  have hψi := h.integrable_comp_norm hR hmR.le hν hlog
  have hαi : Integrable (fun w : ℂ => α * -Real.log ‖w‖) ν := hlog.neg.const_mul α
  -- the two sequences of regularizations
  have hA : ∀ᶠ k in atTop, ∫ w, avgReg M k w ∂ν =
      ∫ w, Φ k w ∂ν + ∫ w, radJ (fun ρ => α * -Real.log ρ) (radius k) w ∂ν +
        ν.real univ * c₀ := by
    filter_upwards [hev, hΦi] with k hk hΦk
    have hJi := hα.integrable_radJ hR (radius_pos k) (by linarith) hν hlog
    rw [integral_congr_ae (g := fun w => Φ k w + radJ (fun ρ => α * -Real.log ρ) (radius k) w + c₀)
      (by filter_upwards [hν] with w hw
          exact avgReg_model_eq hR hr₁R hM hZ hw.1 (by linarith [hw.2.2])),
      integral_add, integral_add hΦk hJi, integral_const, smul_eq_mul]
    · exact hΦk.add hJi
    · exact integrable_const _
  have hB : ∀ᶠ k in atTop, ∫ w, avgReg Y k w ∂ν =
      ∫ w, Φ k w ∂ν - ∫ w, radJ ψ (radius k) w ∂ν := by
    filter_upwards [hev, hΦi] with k hk hΦk
    have hJi := h.integrable_radJ hR (radius_pos k) (by linarith) hν hlog
    rw [integral_congr_ae (g := fun w => Φ k w - radJ ψ (radius k) w)
      (by filter_upwards [hν] with w hw
          exact avgReg_lat_eq h hr₁R hY hZ hw.1 (by linarith [hw.2.2])),
      integral_sub hΦk hJi]
  have hAl : Tendsto (fun k => ∫ w, avgReg M k w ∂ν) atTop
      (𝓝 (l + ∫ w, α * -Real.log ‖w‖ ∂ν + ν.real univ * c₀)) :=
    ((hΦ.add (hα.tendsto_integral_radJ hR hmR hν hlog)).add_const _).congr'
      (hA.mono fun k hk => hk.symm)
  have hBl : Tendsto (fun k => ∫ w, avgReg Y k w ∂ν) atTop
      (𝓝 (l - ∫ w, ψ ‖w‖ ∂ν)) :=
    (hΦ.sub (h.tendsto_integral_radJ hR hmR hν hlog)).congr' (hB.mono fun k hk => hk.symm)
  refine ⟨hψi, ?_⟩
  unfold evalReg
  rw [hAl.limUnder_eq, hBl.limUnder_eq, integral_add, integral_add hψi hαi, integral_const,
    smul_eq_mul]
  · ring
  · exact hψi.add hαi
  · exact integrable_const _

end Core

end D3Plus
end QuantumZipper
