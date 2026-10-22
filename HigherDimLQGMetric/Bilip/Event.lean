import HigherDimLQGMetric.Bilip.MetricShell
import HigherDimLQGMetric.Sharp.CountableShell

/-!
# A Borel shell comparison event

The larger shell `A_{r/4,4r}` directly observes both metric quantities.  A
countable dense sphere sequence supplies the Borel infimum and supremum.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open HigherDimLFPP (Rd)
open scoped ENNReal

namespace HigherDimLQGMetric

variable {d : ℕ}

def bilipOuterEvent (D₁ D₂ : ContMetric d) (z : Rd d) (r C : ℝ) : Prop :=
  internalDiamRd D₂ (sphere z r) (shellOpen z (r / 4) (4 * r)) ≤
    ENNReal.ofReal C * infPairs D₁.1 (sphere z (r / 2)) (sphere z r)

theorem bilip_outerEvent_of_inner (D₁ D₂ : ContMetric d) (z : Rd d)
    {r C : ℝ} (hr : 0 < r)
    (h : internalDiamRd D₂ (sphere z r) (shellOpen z (r / 2) (2 * r)) ≤
      ENNReal.ofReal C * infPairs D₁.1 (sphere z (r / 2)) (sphere z r)) :
    bilipOuterEvent D₁ D₂ z r C := by
  have hsub : (shellOpen z (r / 2) (2 * r) : Set (Rd d)) ⊆
      (shellOpen z (r / 4) (4 * r) : Set (Rd d)) := by
    intro x hx
    constructor
    · exact (ball_subset_ball (by linarith) hx.1)
    · intro hxsmall
      exact hx.2 (by
        rw [mem_closedBall] at hxsmall ⊢
        linarith)
  unfold bilipOuterEvent internalDiamRd
  calc
    (⨆ u ∈ sphere z r, ⨆ v ∈ sphere z r,
        D₂.internal (shellOpen z (r / 4) (4 * r)) u v) ≤
      ⨆ u ∈ sphere z r, ⨆ v ∈ sphere z r,
        D₂.internal (shellOpen z (r / 2) (2 * r)) u v := by
          exact iSup₂_mono fun u _ => iSup₂_mono fun v _ => D₂.internal_anti hsub u v
    _ ≤ _ := h

private theorem bilip_sphere_outer {r : ℝ} (hr : 0 < r) (z : Rd d) :
    sphere z r ⊆ (shellOpen z (r / 4) (4 * r) : Set (Rd d)) := by
  intro u hu
  rw [mem_sphere, dist_eq_norm] at hu
  constructor
  · rw [mem_ball, dist_eq_norm, hu]; linarith
  · rw [mem_closedBall, dist_eq_norm]; linarith

private theorem bilip_halfsphere_outer {r : ℝ} (hr : 0 < r) (z : Rd d) :
    sphere z (r / 2) ⊆ (shellOpen z (r / 4) (4 * r) : Set (Rd d)) := by
  intro u hu
  rw [mem_sphere, dist_eq_norm] at hu
  constructor
  · rw [mem_ball, dist_eq_norm, hu]; linarith
  · rw [mem_closedBall, dist_eq_norm]; linarith

private theorem bilip_closed_half_outer {r : ℝ} (hr : 0 < r) (z : Rd d) :
    annCl z (r / 2) r ⊆ (shellOpen z (r / 4) (4 * r) : Set (Rd d)) := by
  intro u hu
  constructor
  · rw [mem_ball, dist_eq_norm]; linarith [hu.2]
  · rw [mem_closedBall, dist_eq_norm]; linarith [hu.1]

/-- The event used in the global comparison has a representative measurable
from the two rescaled internal metrics on the larger shell. -/
theorem bilipOuterEvent_aeLocal (hd : 2 ≤ d) {Ω : Type*}
    [mΩ : MeasurableSpace Ω] {P : Measure[mΩ] Ω}
    {ξ : ℝ} {h : Ω → DistRd d} {D₁ D₂ : Ω → ContMetric d}
    (hxi : IsXiAdditiveRd ξ P h D₁ D₂)
    (z : Rd d) {r : ℝ} (hr : 0 < r) (C : ℝ) :
    ∃ E' : Set Ω,
      MeasurableSet[
        fieldSigmaRd (fun ω => l7b_recenter (h ω) r z)
          (shellOpen z ((1 / 4) * r) (4 * r)) ⊔
        famSigmaRd (rescFam ξ h D₁ z r)
          (shellOpen z ((1 / 4) * r) (4 * r)) ⊔
        famSigmaRd (rescFam ξ h D₂ z r)
          (shellOpen z ((1 / 4) * r) (4 * r))] E' ∧
      {ω | bilipOuterEvent (D₁ ω) (D₂ ω) z r C} =ᵐ[P] E' := by
  classical
  have : Nontrivial (Rd d) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  let J := shellOpen z (r / 4) (4 * r)
  obtain ⟨s, hs, hsDense⟩ := exists_denseSeq_rd
    (S := sphere z r) (NormedSpace.sphere_nonempty.2 hr.le)
  obtain ⟨t, ht, htDense⟩ := exists_denseSeq_rd
    (S := sphere z (r / 2)) (NormedSpace.sphere_nonempty.2 (half_pos hr).le)
  let X : Ω → ℝ≥0∞ := fun ω =>
    ⨆ p : ℕ × ℕ, rescFam ξ h D₂ z r ω J (s p.1) (s p.2)
  let Y : Ω → ℝ≥0∞ := fun ω =>
    ⨅ p : ℕ × ℕ, rescFam ξ h D₁ z r ω J (t p.1) (s p.2)
  let M : MeasurableSpace Ω :=
    fieldSigmaRd (fun ω => l7b_recenter (h ω) r z) J ⊔
      famSigmaRd (rescFam ξ h D₁ z r) J ⊔
      famSigmaRd (rescFam ξ h D₂ z r) J
  have hXm : Measurable[M] X := by
    apply Measurable.iSup
    intro p
    exact ((measurable_pi_apply (s p.2)).comp
      ((measurable_pi_apply (s p.1)).comp
        (comap_measurable (fun ω => rescFam ξ h D₂ z r ω J)))).mono
          le_sup_right le_rfl
  have hYm : Measurable[M] Y := by
    apply Measurable.iInf
    intro p
    exact ((measurable_pi_apply (s p.2)).comp
      ((measurable_pi_apply (t p.1)).comp
        (comap_measurable (fun ω => rescFam ξ h D₁ z r ω J)))).mono
          (le_sup_of_le_left le_sup_right) le_rfl
  let E' : Set Ω := {ω | X ω ≤ ENNReal.ofReal C * Y ω}
  have hE' : MeasurableSet[M] E' := measurableSet_le hXm (measurable_const.mul hYm)
  refine ⟨E', ?_, ?_⟩
  · rw [show (1 / 4 : ℝ) * r = r / 4 by ring]
    exact hE'
  · have hlen₁ : ∀ᵐ ω ∂P, (D₁ ω).IsLength :=
      hxi.2.2.1.mono fun ω hω => hω.1
    have hlen₂ : ∀ᵐ ω ∂P, (D₂ ω).IsLength :=
      hxi.2.2.1.mono fun ω hω => hω.2
    filter_upwards [hlen₁, hlen₂] with ω hD₁ hD₂
    have hsJ : ∀ n, s n ∈ J := fun n => bilip_sphere_outer hr z (hs n)
    have htJ : ∀ n, t n ∈ J := fun n => bilip_halfsphere_outer hr z (ht n)
    have hdiam := sphereDiam_eq_iSup_dense (D₂ ω) hD₂ J.isOpen
      (bilip_sphere_outer hr z) hs hsDense
    have hacross := acrossDist_eq_setDistIn (D₁ ω) hD₁ J.isOpen
      (by linarith : r / 2 < r) (bilip_closed_half_outer hr z)
    have hdense := setDistIn_eq_iInf_dense (D₁ ω) hD₁ J.isOpen
      (bilip_halfsphere_outer hr z) (bilip_sphere_outer hr z)
      ht hs htDense hsDense
    let c : ℝ≥0∞ := l7b_scale ξ h r z ω
    have hc0 : c ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
    have hctop : c ≠ ∞ := ENNReal.ofReal_ne_top
    have hX : X ω = c * internalDiamRd (D₂ ω) (sphere z r) J := by
      simp only [X, rescFam, ← ENNReal.mul_iSup]
      exact congrArg (c * ·) hdiam.symm
    have hY : Y ω = c * infPairs (D₁ ω).1 (sphere z (r / 2)) (sphere z r) := by
      simp only [Y, rescFam]
      change (⨅ p : ℕ × ℕ, c * (D₁ ω).internal J (t p.1) (s p.2)) =
        c * acrossDist (D₁ ω) z (r / 2) r
      rw [hacross, hdense, ENNReal.mul_iInf_of_ne hc0 hctop]
    apply propext
    change internalDiamRd (D₂ ω) (sphere z r) J ≤
      ENNReal.ofReal C * infPairs (D₁ ω).1 (sphere z (r / 2)) (sphere z r) ↔
      X ω ≤ ENNReal.ofReal C * Y ω
    rw [hX, hY, mul_left_comm (ENNReal.ofReal C) c,
      ENNReal.mul_le_mul_iff_right hc0 hctop]

end HigherDimLQGMetric
