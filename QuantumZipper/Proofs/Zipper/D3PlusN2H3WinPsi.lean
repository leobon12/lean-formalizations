import QuantumZipper.Proofs.Zipper.D3PlusN2H1Reg
import QuantumZipper.Proofs.Zipper.WedgeShiftRaw
import QuantumZipper.Proofs.GFF.CoordRegLog

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2-H3 (window form): folded-circle averages of log-dominated radial profiles

Task N2H3-SPLITWIN, analytic input. A radial profile `ψ : ℝ → ℝ`, continuous on `(0, ∞)` and
dominated on `(0, R]` by `C + D log (R/ρ)` (`LogDom ψ R C D`), has folded-circle averages
`∫ ψ ‖u‖ dfc(c, s)` which

* are finite and bounded by `C + D log (R/‖c‖)` (`LogDom.abs_integral_fc_le`), since the
  folded-circle average of `log‖·‖` is `log max(s, ‖c‖)` (from `RegClosure.integral_neg_log_fc`);
* depend continuously on the centre (`LogDom.tendsto_fc_center`), by the generalized dominated
  convergence theorem (Royden–Fitzpatrick, *Real Analysis*, 4th ed., §4.4, "general Lebesgue
  dominated convergence theorem"), with the moving dominators
  `C + D (log R − log‖circleMap c s θ‖)`, whose integrals converge by the explicit formula above;
* converge to `ψ ‖w‖` as the radius shrinks, for `w ≠ 0` (`LogDom.tendsto_fc_radius`).

The generalized DCT is derived here from the ordinary one (`tendsto_integral_gdct`) by the
Scheffé-type splitting `|f_n − f| ≤ min(|f_n − f|, 2g) + (g_n − g)⁺`: own elementary proof of a
textbook fact.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal Real

namespace QuantumZipper
namespace D3Plus

/-! ## Generalized dominated convergence -/

/-- **Generalized dominated convergence** (Royden–Fitzpatrick, *Real Analysis*, §4.4): moving
dominators `g n → G` a.e. with `∫ g n → ∫ G`. -/
theorem tendsto_integral_gdct {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : ℕ → α → ℝ} {F G : α → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hF : AEStronglyMeasurable F μ)
    (hg : ∀ n, Integrable (g n) μ) (hG : Integrable G μ)
    (hb : ∀ᶠ n in atTop, ∀ᵐ x ∂μ, |f n x| ≤ g n x)
    (hfl : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (F x)))
    (hgl : ∀ᵐ x ∂μ, Tendsto (fun n => g n x) atTop (𝓝 (G x)))
    (hint : Tendsto (fun n => ∫ x, g n x ∂μ) atTop (𝓝 (∫ x, G x ∂μ))) :
    Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, F x ∂μ)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hb
  have hb' : ∀ᵐ x ∂μ, ∀ n, N ≤ n → |f n x| ≤ g n x := by
    refine ae_all_iff.2 fun n => ?_
    by_cases h : N ≤ n
    · exact (hN n h).mono fun x hx _ => hx
    · exact ae_of_all _ fun x h' => absurd h' h
  have hFG : ∀ᵐ x ∂μ, |F x| ≤ G x := by
    filter_upwards [hb', hfl, hgl] with x hx h1 h2
    exact le_of_tendsto_of_tendsto h1.abs h2 (eventually_atTop.2 ⟨N, fun n hn => hx n hn⟩)
  have hG0 : ∀ᵐ x ∂μ, 0 ≤ G x := hFG.mono fun x hx => (abs_nonneg _).trans hx
  have hFi : Integrable F μ :=
    hG.mono' hF (hFG.mono fun x hx => by rw [Real.norm_eq_abs]; exact hx)
  -- the negative parts `(G − g n)⁺`
  have hq : Tendsto (fun n => ∫ x, max (G x - g n x) 0 ∂μ) atTop (𝓝 (∫ _x, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence G (Eventually.of_forall fun n =>
      ((hG.1.aemeasurable.sub (hg n).1.aemeasurable).max aemeasurable_const).aestronglyMeasurable)
      (eventually_atTop.2 ⟨N, fun n hn => ?_⟩) hG ?_
    · filter_upwards [hb', hG0] with x hx h0
      have h1 := hx n hn
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [abs_nonneg (f n x)]) h0
    · filter_upwards [hgl] with x h2
      have h3 := ((tendsto_const_nhds (x := G x)).sub h2).max (tendsto_const_nhds (x := (0 : ℝ)))
      rw [sub_self, max_self] at h3
      exact h3
  have hqi : ∀ n, Integrable (fun x => max (G x - g n x) 0) μ := fun n =>
    ((hg n).sub hG).abs.mono'
      ((hG.1.aemeasurable.sub (hg n).1.aemeasurable).max aemeasurable_const).aestronglyMeasurable
      (ae_of_all _ fun x => by
        simp only [Real.norm_eq_abs, Pi.sub_apply]
        rw [abs_of_nonneg (le_max_right _ _)]
        exact max_le (by rw [abs_sub_comm]; exact le_abs_self _) (abs_nonneg _))
  have hpi : ∀ n, Integrable (fun x => max (g n x - G x) 0) μ := fun n =>
    ((hg n).sub hG).abs.mono'
      (((hg n).1.aemeasurable.sub hG.1.aemeasurable).max aemeasurable_const).aestronglyMeasurable
      (ae_of_all _ fun x => by
        simp only [Real.norm_eq_abs, Pi.sub_apply]
        rw [abs_of_nonneg (le_max_right _ _)]
        exact max_le (le_abs_self _) (abs_nonneg _))
  -- the positive parts `(g n − G)⁺`
  have hp : Tendsto (fun n => ∫ x, max (g n x - G x) 0 ∂μ) atTop (𝓝 0) := by
    have e : ∀ n, ∫ x, max (g n x - G x) 0 ∂μ =
        (∫ x, g n x ∂μ - ∫ x, G x ∂μ) + ∫ x, max (G x - g n x) 0 ∂μ := fun n => by
      rw [← integral_sub (hg n) hG, ← integral_add (f := fun x => g n x - G x)
        ((hg n).sub hG) (hqi n)]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only
      rcases le_total (g n x) (G x) with h | h
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
    simp_rw [e]
    have := (hint.sub_const (∫ x, G x ∂μ)).add hq
    simpa using this
  -- the truncated differences
  have hmm : ∀ n, AEStronglyMeasurable (fun x => min ‖f n x - F x‖ (2 * G x)) μ := fun n =>
    (((hf n).sub hF).norm.aemeasurable.min (hG.1.aemeasurable.const_mul 2)).aestronglyMeasurable
  have hmb : ∀ n, ∀ᵐ x ∂μ, ‖min ‖f n x - F x‖ (2 * G x)‖ ≤ 2 * G x := fun n => by
    filter_upwards [hG0] with x h0
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (norm_nonneg _) (by linarith))]
    exact min_le_right _ _
  have hm : Tendsto (fun n => ∫ x, min ‖f n x - F x‖ (2 * G x) ∂μ) atTop
      (𝓝 (∫ _x, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => 2 * G x)
      (Eventually.of_forall hmm) (Eventually.of_forall hmb) (hG.const_mul 2) ?_
    filter_upwards [hfl, hG0] with x h1 h0
    have h3 := ((h1.sub_const (F x)).norm).min (tendsto_const_nhds (x := 2 * G x))
    simp only [sub_self, norm_zero] at h3
    rwa [min_eq_left (by linarith)] at h3
  have hmi : ∀ n, Integrable (fun x => min ‖f n x - F x‖ (2 * G x)) μ := fun n =>
    (hG.const_mul 2).mono' (hmm n) (hmb n)
  -- squeeze
  have hsq : Tendsto (fun n => ∫ x, f n x ∂μ - ∫ x, F x ∂μ) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun n => ∫ x, min ‖f n x - F x‖ (2 * G x) ∂μ +
      ∫ x, max (g n x - G x) 0 ∂μ) (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
      (by have h4 := hm.add hp; rw [integral_zero, zero_add] at h4; exact h4)
    have hfi : Integrable (f n) μ :=
      (hg n).mono' (hf n) ((hN n hn).mono fun x hx => by rw [Real.norm_eq_abs]; exact hx)
    rw [← integral_sub hfi hFi, ← integral_add (hmi n) (hpi n)]
    refine (norm_integral_le_integral_norm _).trans (integral_mono_ae (hfi.sub hFi).norm
      ((hmi n).add (hpi n)) ?_)
    filter_upwards [hFG, hb'] with x hx hx'
    have h1 := hx' n hn
    have h2 := norm_sub_le (f n x) (F x)
    rw [Real.norm_eq_abs (f n x), Real.norm_eq_abs (F x)] at h2
    show ‖f n x - F x‖ ≤ min ‖f n x - F x‖ (2 * G x) + max (g n x - G x) 0
    rcases le_total ‖f n x - F x‖ (2 * G x) with h | h
    · rw [min_eq_left h]; linarith [le_max_right (g n x - G x) 0]
    · rw [min_eq_right h]; linarith [le_max_left (g n x - G x) 0]
  exact tendsto_sub_nhds_zero_iff.1 hsq

/-! ## The angle parametrization of folded circles -/

/-- The normalized angle measure on `[0, 2π)`. -/
def fcPar : Measure ℝ := (ENNReal.ofReal (2 * π))⁻¹ • volume.restrict (Ico 0 (2 * π))

theorem measurable_fcPath (c : ℂ) (s : ℝ) : Measurable fun θ : ℝ => foldH (circleMap c s θ) :=
  measurable_foldH.comp (continuous_circleMap c s).measurable

theorem fc_eq_map_fcPar (c : ℂ) (s : ℝ) :
    foldedCircle c s = fcPar.map fun θ => foldH (circleMap c s θ) := by
  rw [foldedCircle, circleUnif, fcPar, Measure.map_smul, Measure.map_smul,
    Measure.map_map measurable_foldH (continuous_circleMap c s).measurable]
  all_goals first | rfl | exact (measurable_fcPath c s).aemeasurable |
    exact measurable_foldH.aemeasurable

instance isProbabilityMeasure_fcPar : IsProbabilityMeasure fcPar := by
  constructor
  have h := congrArg (fun m : Measure ℂ => m univ) (fc_eq_map_fcPar 0 0)
  rw [Measure.map_apply (measurable_fcPath 0 0) MeasurableSet.univ, preimage_univ,
    measure_univ] at h
  exact h.symm

theorem integral_fc_par {φ : ℂ → ℝ} (hφ : Measurable φ) (c : ℂ) (s : ℝ) :
    ∫ u, φ u ∂foldedCircle c s = ∫ θ, φ (foldH (circleMap c s θ)) ∂fcPar := by
  rw [fc_eq_map_fcPar, integral_map (measurable_fcPath c s).aemeasurable hφ.aestronglyMeasurable]

theorem ae_fc_of_forall {p : ℂ → Prop} (hp : MeasurableSet {u | p u}) (c : ℂ) (s : ℝ)
    (h : ∀ θ, p (foldH (circleMap c s θ))) : ∀ᵐ u ∂foldedCircle c s, p u := by
  rw [fc_eq_map_fcPar, ae_map_iff (measurable_fcPath c s).aemeasurable hp]
  exact ae_of_all _ h

theorem norm_foldH_psi (z : ℂ) : ‖foldH z‖ = ‖z‖ := by
  unfold foldH; split_ifs <;> simp

theorem circleMap_eq_add (c : ℂ) (s θ : ℝ) : circleMap c s θ = c + circleMap 0 s θ := by
  simp [circleMap]

theorem norm_circleMap_le' (c : ℂ) {s : ℝ} (hs : 0 ≤ s) (θ : ℝ) :
    ‖circleMap c s θ‖ ≤ ‖c‖ + s := by
  rw [circleMap_eq_add]
  exact (norm_add_le _ _).trans (le_of_eq (by rw [norm_circleMap_zero, abs_of_nonneg hs]))

theorem norm_circleMap_ge' (c : ℂ) {s : ℝ} (hs : 0 ≤ s) (θ : ℝ) :
    ‖c‖ - s ≤ ‖circleMap c s θ‖ := by
  rw [circleMap_eq_add]
  have h : ‖c‖ ≤ ‖c + circleMap 0 s θ‖ + ‖circleMap 0 s θ‖ := by
    simpa using norm_add_le (c + circleMap 0 s θ) (-circleMap 0 s θ)
  rw [norm_circleMap_zero, abs_of_nonneg hs] at h
  linarith

theorem ae_fcPar_ne_zero (c : ℂ) {s : ℝ} (hs : 0 < s) : ∀ᵐ θ ∂fcPar, circleMap c s θ ≠ 0 := by
  have h := F1.ae_ne_zero_fc c hs
  rw [fc_eq_map_fcPar, ae_map_iff (p := fun u : ℂ => u ≠ 0) (measurable_fcPath c s).aemeasurable
    (measurableSet_singleton (0 : ℂ)).compl] at h
  filter_upwards [h] with θ hθ h0
  exact hθ (by rw [← norm_eq_zero, norm_foldH_psi, h0, norm_zero])

theorem integral_log_norm_fc (c : ℂ) {s : ℝ} (hs : 0 < s) :
    ∫ u, Real.log ‖u‖ ∂foldedCircle c s = Real.log (max s ‖c‖) := by
  have h := RegClosure.integral_neg_log_fc c hs 0
  have e3 : CircleCont.circPot s c ((0 : ℝ) : ℂ) = -2 * Real.log (max s ‖c‖) := by
    unfold CircleCont.circPot; simp only [Complex.ofReal_zero, map_zero, sub_zero]; ring
  rw [e3, integral_neg] at h
  simp only [Complex.ofReal_zero, sub_zero] at h
  linarith

/-! ## Log-dominated radial profiles -/

/-- A radial profile dominated by a logarithm on `(0, R]`. -/
def LogDom (ψ : ℝ → ℝ) (R C D : ℝ) : Prop :=
  Measurable ψ ∧ ContinuousOn ψ (Set.Ioi 0) ∧ 0 ≤ D ∧
    ∀ ρ, 0 < ρ → ρ ≤ R → |ψ ρ| ≤ C + D * Real.log (R / ρ)

theorem LogDom.add {ψ φ : ℝ → ℝ} {R C D C' D' : ℝ} (h : LogDom ψ R C D)
    (h' : LogDom φ R C' D') : LogDom (fun ρ => ψ ρ + φ ρ) R (C + C') (D + D') := by
  refine ⟨h.1.add h'.1, h.2.1.add h'.2.1, add_nonneg h.2.2.1 h'.2.2.1, fun ρ hρ hρR => ?_⟩
  have h1 := h.2.2.2 ρ hρ hρR
  have h2 := h'.2.2.2 ρ hρ hρR
  calc |ψ ρ + φ ρ| ≤ |ψ ρ| + |φ ρ| := abs_add_le _ _
    _ ≤ _ := by linarith

theorem logDom_neg_log (α : ℝ) {R : ℝ} (hR : 0 < R) :
    LogDom (fun ρ => α * -Real.log ρ) R (|α| * |Real.log R|) |α| := by
  refine ⟨measurable_const.mul Real.measurable_log.neg,
    continuousOn_const.mul (Real.continuousOn_log.mono fun x hx => ne_of_gt hx).neg,
    abs_nonneg _, fun ρ hρ hρR => ?_⟩
  have hl : Real.log (R / ρ) = Real.log R - Real.log ρ := Real.log_div hR.ne' hρ.ne'
  have hl0 : 0 ≤ Real.log (R / ρ) := Real.log_nonneg ((one_le_div hρ).2 hρR)
  rw [abs_mul, abs_neg]
  have : |Real.log ρ| ≤ |Real.log R| + Real.log (R / ρ) := by
    have e : Real.log ρ = Real.log R - Real.log (R / ρ) := by rw [hl]; ring
    rw [e]
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg hl0])
  nlinarith [abs_nonneg α]

theorem LogDom.bound' {ψ : ℝ → ℝ} {R C D : ℝ} (h : LogDom ψ R C D) {ρ : ℝ} (hρ : 0 < ρ)
    (hρR : ρ ≤ R) : |ψ ρ| ≤ C + D * (Real.log R - Real.log ρ) := by
  have := h.2.2.2 ρ hρ hρR
  rwa [Real.log_div (hρ.trans_le hρR).ne' hρ.ne'] at this

theorem integrable_dom_fc (C D R : ℝ) (c : ℂ) (s : ℝ) :
    Integrable (fun u : ℂ => C + D * (Real.log R - Real.log ‖u‖)) (foldedCircle c s) :=
  (integrable_const C).add (((integrable_const (Real.log R)).sub
    (CoordReg.integrable_log_norm_foldedCircle c s)).const_mul D)

theorem integral_dom_fc (C D R : ℝ) (c : ℂ) {s : ℝ} (hs : 0 < s) :
    ∫ u, (C + D * (Real.log R - Real.log ‖u‖)) ∂foldedCircle c s =
      C + D * (Real.log R - Real.log (max s ‖c‖)) := by
  have hL : Integrable (fun u : ℂ => Real.log ‖u‖) (foldedCircle c s) :=
    CoordReg.integrable_log_norm_foldedCircle c s
  have hI : Integrable (fun u : ℂ => D * (Real.log R - Real.log ‖u‖)) (foldedCircle c s) :=
    ((integrable_const (Real.log R)).sub hL).const_mul D
  rw [integral_add (integrable_const _) hI, integral_const,
    integral_const_mul, integral_sub (integrable_const _) hL, integral_const,
    integral_log_norm_fc c hs]
  simp

theorem LogDom.integrable_fc {ψ : ℝ → ℝ} {R C D : ℝ} (h : LogDom ψ R C D) {c : ℂ} {s : ℝ}
    (hs : 0 < s) (hcs : ‖c‖ + s ≤ R) : Integrable (fun u : ℂ => ψ ‖u‖) (foldedCircle c s) := by
  have hle : ∀ᵐ u ∂foldedCircle c s, ‖u‖ ≤ ‖c‖ + s :=
    ae_fc_of_forall (isClosed_le continuous_norm continuous_const).measurableSet c s
      fun θ => by rw [norm_foldH_psi]; exact norm_circleMap_le' c hs.le θ
  refine (integrable_dom_fc C D R c s).mono' (h.1.comp measurable_norm).aestronglyMeasurable ?_
  filter_upwards [F1.ae_ne_zero_fc c hs, hle] with u hu hu'
  rw [Real.norm_eq_abs]
  exact h.bound' (norm_pos_iff.2 hu) (hu'.trans hcs)

theorem LogDom.abs_integral_fc_le {ψ : ℝ → ℝ} {R C D : ℝ} (h : LogDom ψ R C D) {c : ℂ} {s : ℝ}
    (hs : 0 < s) (hcs : ‖c‖ + s ≤ R) (hc : c ≠ 0) :
    |∫ u, ψ ‖u‖ ∂foldedCircle c s| ≤ C + D * Real.log (R / ‖c‖) := by
  have hle : ∀ᵐ u ∂foldedCircle c s, ‖u‖ ≤ ‖c‖ + s :=
    ae_fc_of_forall (isClosed_le continuous_norm continuous_const).measurableSet c s
      fun θ => by rw [norm_foldH_psi]; exact norm_circleMap_le' c hs.le θ
  have hc0 : 0 < ‖c‖ := norm_pos_iff.2 hc
  have hR : 0 < R := by linarith
  have h1 : ∫ u, |ψ ‖u‖| ∂foldedCircle c s ≤
      ∫ u, (C + D * (Real.log R - Real.log ‖u‖)) ∂foldedCircle c s := by
    refine integral_mono_ae (h.integrable_fc hs hcs).abs (integrable_dom_fc C D R c s) ?_
    filter_upwards [F1.ae_ne_zero_fc c hs, hle] with u hu hu'
    exact h.bound' (norm_pos_iff.2 hu) (hu'.trans hcs)
  rw [integral_dom_fc C D R c hs] at h1
  have h2 : Real.log ‖c‖ ≤ Real.log (max s ‖c‖) := Real.log_le_log hc0 (le_max_right _ _)
  rw [Real.log_div hR.ne' hc0.ne']
  have h3 := abs_integral_le_integral_abs (f := fun u : ℂ => ψ ‖u‖) (μ := foldedCircle c s)
  nlinarith [h.2.2.1]

theorem LogDom.tendsto_fc_center {ψ : ℝ → ℝ} {R C D : ℝ} (h : LogDom ψ R C D) {s : ℝ}
    (hs : 0 < s) {c : ℕ → ℂ} {w : ℂ} (hc : Tendsto c atTop (𝓝 w)) (hw : ‖w‖ + s < R) :
    Tendsto (fun n => ∫ u, ψ ‖u‖ ∂foldedCircle (c n) s) atTop
      (𝓝 (∫ u, ψ ‖u‖ ∂foldedCircle w s)) := by
  have hψm : Measurable fun u : ℂ => ψ ‖u‖ := h.1.comp measurable_norm
  have e : ∀ c' : ℂ, ∫ u, ψ ‖u‖ ∂foldedCircle c' s = ∫ θ, ψ ‖circleMap c' s θ‖ ∂fcPar :=
    fun c' => by rw [integral_fc_par hψm]; simp only [norm_foldH_psi]
  have hdm : ∀ c' : ℂ, Measurable fun u : ℂ => C + D * (Real.log R - Real.log ‖u‖) := fun c' =>
    measurable_const.add (measurable_const.mul
      (measurable_const.sub (Real.measurable_log.comp measurable_norm)))
  have ed : ∀ c' : ℂ, ∫ θ, (C + D * (Real.log R - Real.log ‖circleMap c' s θ‖)) ∂fcPar =
      C + D * (Real.log R - Real.log (max s ‖c'‖)) := fun c' => by
    rw [← integral_dom_fc C D R c' hs, integral_fc_par (hdm c')]
    simp only [norm_foldH_psi]
  have hdi : ∀ c' : ℂ, Integrable
      (fun θ => C + D * (Real.log R - Real.log ‖circleMap c' s θ‖)) fcPar := fun c' => by
    have h0 := integrable_dom_fc C D R c' s
    rw [fc_eq_map_fcPar, integrable_map_measure (hdm c').aestronglyMeasurable
      (measurable_fcPath c' s).aemeasurable] at h0
    refine h0.congr (ae_of_all _ fun θ => ?_)
    simp only [Function.comp_apply, norm_foldH_psi]
  rw [show (fun n => ∫ u, ψ ‖u‖ ∂foldedCircle (c n) s) =
      fun n => ∫ θ, ψ ‖circleMap (c n) s θ‖ ∂fcPar from funext fun n => e (c n), e w]
  have hcm : ∀ θ, Tendsto (fun n => circleMap (c n) s θ) atTop (𝓝 (circleMap w s θ)) :=
    fun θ => by
      rw [show (fun n => circleMap (c n) s θ) = fun n => c n + circleMap 0 s θ from
        funext fun n => circleMap_eq_add _ _ _, circleMap_eq_add w]
      exact hc.add_const _
  have hcont : Continuous fun c' : ℂ => Real.log (max s ‖c'‖) :=
    (continuous_const.max continuous_norm).log fun c' => (hs.trans_le (le_max_left _ _)).ne'
  refine tendsto_integral_gdct (f := fun n θ => ψ ‖circleMap (c n) s θ‖)
    (F := fun θ => ψ ‖circleMap w s θ‖)
    (g := fun n θ => C + D * (Real.log R - Real.log ‖circleMap (c n) s θ‖))
    (G := fun θ => C + D * (Real.log R - Real.log ‖circleMap w s θ‖))
    (fun n => (h.1.comp (continuous_circleMap _ _).norm.measurable).aestronglyMeasurable)
    (h.1.comp (continuous_circleMap _ _).norm.measurable).aestronglyMeasurable
    (fun n => hdi (c n)) (hdi w) ?_ ?_ ?_ ?_
  · filter_upwards [(hc.norm.add_const s).eventually (gt_mem_nhds hw)] with n hn
    filter_upwards [ae_fcPar_ne_zero (c n) hs] with θ hθ
    exact h.bound' (norm_pos_iff.2 hθ) ((norm_circleMap_le' (c n) hs.le θ).trans hn.le)
  · filter_upwards [ae_fcPar_ne_zero w hs] with θ hθ
    exact (h.2.1.continuousAt (Ioi_mem_nhds (norm_pos_iff.2 hθ))).tendsto.comp (hcm θ).norm
  · filter_upwards [ae_fcPar_ne_zero w hs] with θ hθ
    exact tendsto_const_nhds.add (tendsto_const_nhds.mul (tendsto_const_nhds.sub
      ((Real.continuousAt_log (norm_ne_zero_iff.2 hθ)).tendsto.comp (hcm θ).norm)))
  · show Tendsto _ atTop (𝓝 (∫ θ, (C + D * (Real.log R - Real.log ‖circleMap w s θ‖)) ∂fcPar))
    rw [ed w]
    refine Tendsto.congr (fun n => (ed (c n)).symm) ?_
    exact ((continuous_const.add (continuous_const.mul (continuous_const.sub hcont))).tendsto
      w).comp hc

theorem LogDom.tendsto_fc_radius {ψ : ℝ → ℝ} {R C D : ℝ} (h : LogDom ψ R C D) {w : ℂ}
    (hw : w ∈ Hbar) (hw0 : w ≠ 0) :
    Tendsto (fun k => ∫ u, ψ ‖u‖ ∂foldedCircle w (radius k)) atTop (𝓝 (ψ ‖w‖)) := by
  set δ := ‖w‖ / 2 with hδ
  have hw' : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hgc : Continuous fun u : ℂ => ψ (max ‖u‖ δ) :=
    h.2.1.comp_continuous (continuous_norm.max continuous_const)
      fun u => show 0 < max ‖u‖ δ from lt_of_lt_of_le hδ0 (le_max_right _ _)
  have hT := tendsto_integral_fc_radius hgc hw
  have hgw : max ‖w‖ δ = ‖w‖ := max_eq_left (by rw [hδ]; linarith)
  rw [hgw] at hT
  refine hT.congr' ?_
  filter_upwards [(RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).eventually
    (gt_mem_nhds hδ0)] with k hk
  rw [integral_fc_par hgc.measurable,
    integral_fc_par (show Measurable fun u : ℂ => ψ ‖u‖ from h.1.comp measurable_norm)]
  refine integral_congr_ae (ae_of_all _ fun θ => ?_)
  simp only [norm_foldH_psi]
  rw [max_eq_left]
  have := norm_circleMap_ge' w (radius_pos k).le θ
  rw [hδ] at hk ⊢
  linarith

end D3Plus
end QuantumZipper
