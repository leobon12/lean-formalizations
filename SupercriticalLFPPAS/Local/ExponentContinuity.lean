import SupercriticalLFPPAS.Field.LocalizedApproximation
import SupercriticalLQGUniqueness.B2.Polylog.P1LocalizedCont
import LQGMetric.Papers.DFGPS.L2_1Cont
import LQGMetric.Field.MeasurableAvg
import LQGMetric.Field.Measurable

/-!
# Continuity of the localized field in its exponent, at every scale (packet P32)

The landed `Field.continuousAt_plPairing_exponent` (packet D5) proves that `q ↦ ⟨g, ψ_{q,δ}(z − ·) p⟩`
is continuous when `1 < log δ⁻¹`. The same proof works for every `δ ∈ (0, 1)` once the cutoff radius
`δ (log δ⁻¹)^q = δ e^{q log log δ⁻¹}` is bounded using `|log log δ⁻¹|`; this file records that
version (its auxiliary kernel is private in D5's module, so it is restated here). It is used for the
joint measurability of `(g, L) ↦ Y_{δ,L}[g]` in the measurability clause of Lemma 3.2
(`Local/Interface.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open LQGMetric (DistC)
open SupercriticalLQGUniqueness.B2.Polylog

namespace SupercriticalLFPPAS.Local

/-- The localized test kernel as a smooth function of the exponent. -/
def expKernel (δ t : ℝ) (z : ℂ) (q : ℝ) (w : ℂ) : ℝ :=
  LQGMetric.DFGPS.locProf (2 * (Real.log δ + q * Real.log t)) (z - w) *
    LQGMetric.heatKernel (δ ^ 2 / 2) z w

theorem plRad_eq_exp {δ t q : ℝ} (ht : 0 < t) (htδ : t = Real.log δ⁻¹) :
    plRad q δ = δ * Real.exp (q * Real.log t) := by
  rw [plRad, ← htδ, Real.rpow_def_of_pos ht]
  ring_nf

theorem log_plRad_sq_eq {δ t q : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) (ht : 0 < t)
    (htδ : t = Real.log δ⁻¹) :
    Real.log (plRad q δ ^ 2) = 2 * (Real.log δ + q * Real.log t) := by
  have hrad := plRad_eq_exp ht htδ (q := q)
  have hrad' : plRad q δ = Real.exp (Real.log δ + q * Real.log t) := by
    rw [hrad, ← Real.exp_log hδ.1, ← Real.exp_add]
    simp only [Real.log_exp]
  rw [hrad', ← Real.exp_nat_mul]
  simp only [Real.log_exp]
  ring

theorem expKernel_contDiff (δ t : ℝ) (z : ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℂ => expKernel δ t z p.1 p.2) := by
  have hcoord : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℂ => (2 * (Real.log δ + p.1 * Real.log t), z - p.2)) := by
    fun_prop
  exact (LQGMetric.DFGPS.contDiff_locProf.comp hcoord).mul
    ((LQGMetric.LFPP.contDiff_heatKernel_left (δ ^ 2 / 2) z).comp contDiff_snd)

/-- **Pairing a distribution with the localized test is continuous in the exponent**, at every
`δ ∈ (0, 1)`. -/
theorem continuousAt_plPairing_exponent_all {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) (h : DistC)
    (z : ℂ) (q₀ : ℝ) : ContinuousAt (fun q => h (plTest q δ hδ z)) q₀ := by
  let t := Real.log δ⁻¹
  have htδ : t = Real.log δ⁻¹ := rfl
  have ht : 0 < t := log_inv_pos hδ
  let R := δ * Real.exp ((|q₀| + 1) * |Real.log t|)
  let K : TopologicalSpace.Compacts ℂ := ⟨closedBall z R, isCompact_closedBall _ _⟩
  let X := closedBall q₀ 1
  let Ψ : ℝ × ℂ → ℂ → ℝ := fun p w => expKernel δ t z p.1 w
  have hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry Ψ) := by
    have hmap : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : (ℝ × ℂ) × ℂ => (p.1.1, p.2)) := by fun_prop
    exact (expKernel_contDiff δ t z).comp hmap
  have hs : ∀ x : X, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Ψ (x.1, 0)) := by
    intro x
    exact (expKernel_contDiff δ t z).comp (contDiff_const.prodMk contDiff_id)
  have hzero : ∀ x : X, ∀ w ∉ (K : Set ℂ), Ψ (x.1, 0) w = 0 := by
    intro x w hw
    have hx : |x.1 - q₀| ≤ 1 := by
      have hx0 : dist x.1 q₀ ≤ 1 := x.2
      simpa only [Real.dist_eq] using hx0
    have hx' : |x.1| ≤ |q₀| + 1 := by
      calc |x.1| = |(x.1 - q₀) + q₀| := by ring_nf
        _ ≤ |x.1 - q₀| + |q₀| := abs_add_le _ _
        _ ≤ |q₀| + 1 := by linarith
    have hrad : plRad x.1 δ ≤ R := by
      rw [plRad_eq_exp ht htδ (q := x.1)]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hδ.1.le
      calc x.1 * Real.log t ≤ |x.1 * Real.log t| := le_abs_self _
        _ = |x.1| * |Real.log t| := abs_mul _ _
        _ ≤ (|q₀| + 1) * |Real.log t| := mul_le_mul_of_nonneg_right hx' (abs_nonneg _)
    have hw' : R < ‖z - w‖ := by
      change w ∉ closedBall z R at hw
      rw [mem_closedBall, dist_eq_norm, not_le] at hw
      simpa only [norm_sub_rev] using hw
    have heq := log_plRad_sq_eq hδ ht htδ (q := x.1)
    have hbump := plBump_eq_locProf x.1 δ hδ (z - w)
    change LQGMetric.DFGPS.locProf
      (2 * (Real.log δ + x.1 * Real.log (Real.log δ⁻¹))) (z - w) *
        LQGMetric.heatKernel (δ ^ 2 / 2) z w = 0
    rw [← heq, ← hbump, plBump_eq_zero x.1 δ hδ]
    · simp
    · exact hrad.trans hw'.le
  have hD : ∀ i : ℕ, Continuous fun p : X × ℂ => iteratedFDeriv ℝ i (Ψ (p.1.1, 0)) p.2 := by
    intro i
    have hc := LQGMetric.DFGPS.continuous_iteratedFDeriv_snd_rc hΨ i
    have hmap : Continuous fun p : X × ℂ => ((p.1.1, (0 : ℂ)), p.2) := by fun_prop
    exact hc.comp hmap
  have hc := LQGMetric.continuous_testFamK K (fun x : X => Ψ (x.1, 0)) hs hzero hD
  have he : (fun x : X => plTest x.1 δ hδ z) =
      (LQGMetric.ofSuppC K) ∘ LQGMetric.testFamK K (fun x : X => Ψ (x.1, 0)) hs hzero := by
    funext x
    ext w
    rw [plTest_apply, plBump_eq_locProf, log_plRad_sq_eq hδ ht htδ (q := x.1)]
    rfl
  have hB : Continuous fun x : X => plTest x.1 δ hδ z := by
    rw [he]
    exact (LQGMetric.ofSuppC K).continuous.comp hc
  have hval : Continuous fun x : X => h (plTest x.1 δ hδ z) := (map_continuous h).comp hB
  exact (continuousOn_iff_continuous_domRestrict.2 hval).continuousAt
    (closedBall_mem_nhds q₀ one_pos)

/-- The normalizing mass is continuous in the exponent, at every `δ ∈ (0, 1)`. -/
theorem continuousAt_plZ_exponent_all {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) (q₀ : ℝ) :
    ContinuousAt (fun q => plZ q δ hδ) q₀ := by
  let one : C(ℂ, ℝ) := ContinuousMap.const ℂ 1
  have h := continuousAt_plPairing_exponent_all hδ (LQGMetric.ofCont one) 0 q₀
  have heq : (fun q => (LQGMetric.ofCont one) (plTest q δ hδ 0)) = fun q => plZ q δ hδ := by
    funext q
    rw [LQGMetric.ofCont_apply, plZ]
    simp [one]
  rw [heq] at h
  exact h

/-- **The localized field is continuous in its exponent**, at every `δ ∈ (0, 1)` and every
distribution. -/
theorem continuous_plMollify_exponent {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) (h : DistC) (z : ℂ) :
    Continuous (fun q => plMollify q δ hδ h z) := by
  rw [continuous_iff_continuousAt]
  intro q₀
  have hnum := continuousAt_plPairing_exponent_all hδ h z q₀
  have hden := continuousAt_plZ_exponent_all hδ q₀
  have hinv : ContinuousAt (fun q => (plZ q δ hδ)⁻¹) q₀ := hden.inv₀ (plZ_pos q₀ δ hδ).ne'
  change ContinuousAt ((fun q : ℝ => (plZ q δ hδ)⁻¹) * (fun q => h (plTest q δ hδ z))) q₀
  exact hinv.mul hnum

end SupercriticalLFPPAS.Local
