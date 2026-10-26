import SupercriticalConformalCovariance.GoodAnnulus.Literal
import SupercriticalConformalCovariance.Regular.Measurability
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.S35Separator
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events.StepEvent
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events.StepEvent
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Consolidated.RationalAround

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter Topology Metric LQGMetric.MetricGeometry Metric LQGMetric.MetricGeometry
open scoped ENNReal

namespace SupercriticalConformalCovariance.Improve
open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.Uniqueness
open SupercriticalLQGUniqueness.Uniqueness.TwoScale

/-- Printed (G5), lines 405–410. The source pair includes (7)–(8); the two
extra conditions are exactly (9). No metric or topology is required of `e`. -/
def G5 (D : LSCMetric) (e : ℂ × ℂ → ℝ≥0∞)
    (ξ Q : ℝ) (z : ℂ) (r : Ioi (0 : ℝ)) (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1) (θ : Ioi (0 : ℝ))
    (k c η : ℝ) : Prop :=
  ∀ u v : ℂ,
    SupercriticalConformalCovariance.Regular.SourceRegularPair D z u v r a θ
      ((r : ℝ) ^ (ξ * Q) * Real.exp (ξ * c)) →
    dist u v ≤ (q : ℝ) * r →
    SupercriticalLQGUniqueness.Uniqueness.TwoScale.Consolidated.aroundRat
      (D, (v, (q : ℝ) * r, Real.sqrt (q : ℝ) * r)) ≤
        ENNReal.ofReal k * SupercriticalConformalCovariance.GoodAnnulus.barrier D z r →
    e (u, v) ≤ ENNReal.ofReal (1 + η) * D (u, v)

/-- The fifth clause added to the four literal source clauses. -/
def Good (D : LSCMetric) (e : ℂ × ℂ → ℝ≥0∞)
    (ξ Q : ℝ) (z : ℂ) (r : Ioi (0 : ℝ))
    (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ))
    (θ : Ioi (0 : ℝ)) (k c η : ℝ) : Prop :=
  SupercriticalConformalCovariance.GoodAnnulus.LiteralGood D ξ Q z r q a K θ k c ∧
    G5 D e ξ Q z r q a θ k c η

/-- Formula (11). -/
def newConstant (C η A : ℝ) : ℝ :=
  (1 + η) + A / (A + 1) * (C - 1 - η)

theorem constant_gap {C η A : ℝ} (hA : 0 ≤ A) :
    C - newConstant C η A = (C - 1 - η) / (A + 1) := by
  unfold newConstant
  have hden : A + 1 ≠ 0 := by linarith
  field_simp
  ring

theorem newConstant_lt {C η A : ℝ} (hA : 0 ≤ A) (hη : 1 + η < C) :
    newConstant C η A < C := by
  have hden : 0 < A + 1 := by linarith
  have hgap : 0 < (C - 1 - η) / (A + 1) := div_pos (by linarith) hden
  linarith [constant_gap (C := C) (η := η) hA]

theorem newConstant_ge {C η A : ℝ} (hA : 0 ≤ A) (hη : 0 ≤ η)
    (hC : 1 + η ≤ C) : 1 ≤ newConstant C η A := by
  unfold newConstant
  have hden : 0 < A + 1 := by linarith
  have hfac : 0 ≤ A / (A + 1) := div_nonneg hA hden.le
  have hdiff : 0 ≤ C - 1 - η := by linarith
  have hmul : 0 ≤ A / (A + 1) * (C - 1 - η) := mul_nonneg hfac hdiff
  linarith

/-- The one-step arithmetic behind (12)–(14): the old portion is at
most `A` times the improved portion. -/
theorem weighted_step {C η A a b : ℝ}
    (hA : 0 ≤ A)
    (hC : 1 + η ≤ C) (hratio : a ≤ A * b) :
    C * a + (1 + η) * b ≤ newConstant C η A * (a + b) := by
  have hden : 0 < A + 1 := by linarith
  have ht : 0 ≤ C - 1 - η := by linarith
  have hr : a ≤ A / (A + 1) * (a + b) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hden).2
    nlinarith only [hratio]
  have hmul := mul_le_mul_of_nonneg_left hr ht
  unfold newConstant
  nlinarith only [hmul]

/-- Extended-real one-step version, consuming only a triangle inequality for
`e`, the two source-cost estimates, and (14)'s ratio. -/
theorem improved_two_pieces
    (e : ℂ × ℂ → ℝ≥0∞) (x y z : ℂ) {C η A a b : ℝ}
    (hA : 0 ≤ A) (ha : 0 ≤ a) (hb : 0 ≤ b) (hη : 0 ≤ η)
    (hC : 1 + η ≤ C) (hratio : a ≤ A * b)
    (htri : e (x, z) ≤ e (x, y) + e (y, z))
    (hold : e (x, y) ≤ ENNReal.ofReal (C * a))
    (hnew : e (y, z) ≤ ENNReal.ofReal ((1 + η) * b)) :
    e (x, z) ≤ ENNReal.ofReal (newConstant C η A * (a + b)) := by
  calc
    e (x, z) ≤ e (x, y) + e (y, z) := htri
    _ ≤ ENNReal.ofReal (C * a) + ENNReal.ofReal ((1 + η) * b) :=
      add_le_add hold hnew
    _ = ENNReal.ofReal (C * a + (1 + η) * b) := by
      rw [ENNReal.ofReal_add]
      exact mul_nonneg (by linarith) ha
      exact mul_nonneg (by linarith) hb
    _ ≤ ENNReal.ofReal (newConstant C η A * (a + b)) :=
      ENNReal.ofReal_le_ofReal (weighted_step hA hC hratio)

/-- The retained-step telescope for a raw function `e`. It uses only the
triangle inequality and the already derived per-step bound; in particular no
lower semicontinuity, symmetry, or length-space structure of `e` is involved. -/
theorem raw_steps_telescope
    (e : ℂ × ℂ → ℝ≥0∞) (U : Set ℂ)
    (htri : ∀ x ∈ U, ∀ y ∈ U, ∀ v ∈ U,
      e (x, v) ≤ e (x, y) + e (y, v))
    {P : ℝ → ℂ} {Good : ℂ → ℝ → Prop}
    {ε b α L a T : ℝ} {z w : ℂ}
    (steps : List (SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.CoveredStep P Good ε b α z w))
    (hne : steps ≠ []) (hL : 0 ≤ L)
    (htrace : ∀ t ∈ Icc (0 : ℝ) T, P t ∈ U)
    (ha0 : 0 ≤ a)
    (hend : SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.StepsEnd a steps ≤ T)
    (hfrom : SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.StepsFrom a steps)
    (hstep : ∀ st ∈ steps,
      e (P st.a, P st.t) ≤ ENNReal.ofReal (L * (st.t - st.a))) :
    e (P a, P (SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.StepsEnd a steps)) ≤
      ENNReal.ofReal (L * (SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.StepsEnd a steps - a)) := by
  induction steps generalizing a with
  | nil => exact False.elim (hne rfl)
  | cons st rest ih =>
      obtain ⟨ha, hrest⟩ := hfrom
      have hfirst := hstep st (List.mem_cons_self)
      cases rest with
      | nil =>
          change e (P a, P st.t) ≤ ENNReal.ofReal (L * (st.t - a))
          simpa only [ha] using hfirst
      | cons q qs =>
          have htail : ∀ q' ∈ q :: qs,
              e (P q'.a, P q'.t) ≤ ENNReal.ofReal (L * (q'.t - q'.a)) := by
            intro q' hq'
            exact hstep q' (List.mem_cons_of_mem st hq')
          have hsta0 : 0 ≤ st.a := by rw [ha]; exact ha0
          have hst0 : 0 ≤ st.t := hsta0.trans (st.a_lt_s.trans st.s_lt_t).le
          have htailend :=
            SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.stepsEnd_ge_start
              (q :: qs) hrest
          have hih := ih (by simp) hst0 hend hrest htail
          have hleft : 0 ≤ L * (st.t - st.a) :=
            mul_nonneg hL (sub_nonneg.mpr (st.a_lt_s.trans st.s_lt_t).le)
          have hright : 0 ≤ L *
              (SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.StepsEnd st.t (q :: qs) - st.t) :=
            mul_nonneg hL (sub_nonneg.mpr
              (SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.stepsEnd_ge_start (q :: qs) hrest))
          change e (P a, P (SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.StepsEnd st.t (q :: qs))) ≤
            ENNReal.ofReal (L * (SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.StepsEnd st.t (q :: qs) - a))
          calc
            e (P a, P (SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.StepsEnd st.t (q :: qs))) ≤
                e (P a, P st.t) +
                  e (P st.t, P (SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.StepsEnd st.t (q :: qs))) :=
              htri _ (htrace a ⟨ha0, by
                rw [← ha]
                exact (st.a_lt_s.trans st.s_lt_t).le.trans (htailend.trans hend)⟩)
                _ (htrace st.t ⟨hst0, htailend.trans hend⟩)
                _ (htrace _ ⟨hst0.trans htailend, hend⟩)
            _ ≤ ENNReal.ofReal (L * (st.t - st.a)) +
                ENNReal.ofReal
                  (L * (SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.StepsEnd st.t (q :: qs) - st.t)) := by
              rw [← ha]
              exact add_le_add hfirst hih
            _ = ENNReal.ofReal
                  (L * (SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.StepsEnd st.t (q :: qs) - a)) := by
              rw [← ENNReal.ofReal_add hleft hright, ha]
              congr 1
              ring

/-- Printed (14) for a retained stop, from (G4) and geodesic
minimality. The stopping record already includes the repaired condition that
both global endpoints are outside `B_{2r}`. -/
theorem covered_step_old_length_le
    (D : LSCMetric) {P : ℝ → ℂ} {Good : ℂ → ℝ → Prop}
    {ε b α T : ℝ} {z w : ℂ}
    (st : SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.CoveredStep
      P Good ε b α z w)
    (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ))
    (hα : α = (a : ℝ))
    (hP : ContinuousOn P (Icc 0 T))
    (hgeo : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (hP0 : P 0 = z) (hPT : P T = w)
    (hε : 0 < ε) (hb : 0 < b)
    (ha0 : 0 < st.a) (htT : st.t < T)
    (hG4 : SupercriticalConformalCovariance.GoodAnnulus.G4 D st.center
      ⟨st.radius, lt_of_lt_of_le (by positivity : 0 < ε ^ 2 * b)
        st.radius_min⟩ a K) :
    st.s - st.a ≤ (K : ℝ) * (st.t - st.s) := by
  have hr : 0 < st.radius :=
    lt_of_lt_of_le (by positivity : 0 < ε ^ 2 * b) st.radius_min
  have haHalf : 1 / 2 < α := by
    rw [hα]
    linarith [a.2.1, q.2.2]
  have haOne : α < 1 := by rw [hα]; exact a.2.2
  apply SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.ordinary_increment_le_K_crossing
    D hP hgeo hunit hP0 hPT hr haHalf haOne (le_trans (by norm_num : (0 : ℝ) ≤ 1) K.2.le)
    ha0 st.a_lt_s st.s_lt_t htT st.start_half st.inner_hit st.outer_hit
    st.z_far st.w_far
  simpa only [hα, SupercriticalConformalCovariance.GoodAnnulus.G4, S36.E4Prop, S36.shortAnn] using hG4

/-- The second condition in (9), at the exit endpoint of a retained
step, follows from dyadic (G1), the outer-loop bound (G2), and the two-sided
outer passage. -/
theorem covered_step_tiny_loop_le_barrier
    (D : LSCMetric) {P : ℝ → ℂ} {Good : ℂ → ℝ → Prop}
    {ε b α T : ℝ} {z w : ℂ}
    (st : SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.CoveredStep
      P Good ε b α z w)
    (ξ Q : ℝ) (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1) (θ : Ioi (0 : ℝ))
    (k c : ℝ) (n : ℕ) (hdyad : (q : ℝ) = (1 / 2 : ℝ) ^ n)
    (hα : α = (a : ℝ))
    (hP : ContinuousOn P (Icc 0 T))
    (hgeo : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (hP0 : P 0 = z) (hPT : P T = w)
    (hε : 0 < ε) (hb : 0 < b)
    (ha0 : 0 < st.a) (htT : st.t < T)
    (hG1 : SupercriticalConformalCovariance.GoodAnnulus.G1 D st.center
      ⟨st.radius, lt_of_lt_of_le (by positivity : 0 < ε ^ 2 * b)
        st.radius_min⟩ q θ)
    (hG2 : SupercriticalConformalCovariance.GoodAnnulus.G2 D ξ Q st.center
      ⟨st.radius, lt_of_lt_of_le (by positivity : 0 < ε ^ 2 * b)
        st.radius_min⟩ q a θ k c) :
    SupercriticalLQGUniqueness.Uniqueness.TwoScale.Consolidated.aroundRat
      (D, (P st.t, (q : ℝ) * st.radius,
        Real.sqrt (q : ℝ) * st.radius)) ≤
      ENNReal.ofReal k * SupercriticalConformalCovariance.GoodAnnulus.barrier D st.center
        ⟨st.radius, lt_of_lt_of_le (by positivity : 0 < ε ^ 2 * b)
          st.radius_min⟩ := by
  let r : Ioi (0 : ℝ) := ⟨st.radius,
    lt_of_lt_of_le (by positivity : 0 < ε ^ 2 * b) st.radius_min⟩
  have hhalf : 1 / 2 < α := by rw [hα]; linarith [a.2.1, q.2.2]
  obtain ⟨σ, τ, hσ0, hσs, htτ, hτT, hinternal⟩ :=
    S36Events.CoveredStep.internal_boundary_geodesic D st hP hgeo hunit
      hP0 hPT r.2 hhalf ha0 htT
  obtain ⟨_, _, htmid, _, _, _, _, _⟩ :=
    S36Events.CoveredStep.event_endpoint_geometry st q a hα hP0 hPT r.2
  have hhit : ∃ v ∈ Icc σ τ,
      P v ∈ ball (P st.t) (((1 / 2 : ℝ) ^ n) * r) := by
    refine ⟨st.t, ⟨hσs.le.trans st.s_lt_t.le, htτ.le⟩, ?_⟩
    exact Metric.mem_ball_self (mul_pos (hdyad ▸ q.2.1) r.2)
  obtain ⟨A, hc, hρ, hσ, hreg⟩ :=
    hG1 P σ τ hinternal n (by rw [← hdyad]) (P st.t) htmid hhit
  let At : EuclideanAnnulus :=
    ⟨(P st.t, ((q : ℝ) * st.radius,
      Real.sqrt (q : ℝ) * st.radius)),
      Consolidated.loop_annulus_valid r.2 q.2.1
        (q.2.2.trans (by norm_num : (1 / 100 : ℝ) < 1))⟩
  have hA : A = At := by
    apply S36Events.annulus_eq_of_data
    · exact hc
    · change A.innerRadius = (q : ℝ) * st.radius
      simpa only [← hdyad, Subtype.coe_mk] using hρ
    · change A.outerRadius = Real.sqrt (q : ℝ) * st.radius
      simpa only [← hdyad, Subtype.coe_mk] using hσ
  have hreg' : aroundDist D At ≤
      ENNReal.ofReal ((q : ℝ) ^ (θ : ℝ)) * acrossDist D At := by
    simpa only [hA, ← hdyad] using hreg
  obtain ⟨_, hcross⟩ :=
    S36Events.CoveredStep.outer_and_tiny_bounds D st hP hgeo hunit
      hP0 hPT r.2 ha0.le htT q
  have houter : aroundDist D (S36.outerAnn st.center r) ≤
      ENNReal.ofReal (k * (q : ℝ) ^ (-(θ : ℝ))) *
        SupercriticalConformalCovariance.GoodAnnulus.barrier D st.center r := by
    exact hG2.trans (min_le_right _ _)
  have hcross' : acrossDist D At ≤
      aroundDist D (S36.outerAnn st.center r) := by
    simpa only [S36.outerAnn] using hcross
  have hshield :=
    S36Events.shield_cost_of_reg_and_outer q.2.1 hreg' hcross' houter
  rw [Consolidated.aroundDist_eq_aroundRat] at hshield
  simpa only [At, r, EuclideanAnnulus.center, EuclideanAnnulus.innerRadius,
    EuclideanAnnulus.outerRadius] using hshield

theorem dyadic_eq_half_pow (j : ℕ) :
    SupercriticalConformalCovariance.Regular.dyadic j = (1 / 2 : ℝ) ^ j := by
  rw [SupercriticalConformalCovariance.Regular.dyadic, zpow_neg, zpow_natCast, one_div, inv_pow]

/-- Both endpoint tests in (8), for either endpoint of a retained step. -/
theorem covered_step_dyadic_endpoint
    (D : LSCMetric) {P : ℝ → ℂ} {Good : ℂ → ℝ → Prop}
    {ε b α T : ℝ} {z w : ℂ}
    (st : SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.CoveredStep
      P Good ε b α z w)
    (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1) (θ : Ioi (0 : ℝ))
    (hα : α = (a : ℝ))
    (hP : ContinuousOn P (Icc 0 T))
    (hgeo : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (hP0 : P 0 = z) (hPT : P T = w)
    (hε : 0 < ε) (hb : 0 < b)
    (ha0 : 0 < st.a) (htT : st.t < T)
    (hG1 : SupercriticalConformalCovariance.GoodAnnulus.G1 D st.center
      ⟨st.radius, lt_of_lt_of_le (by positivity : 0 < ε ^ 2 * b)
        st.radius_min⟩ q θ)
    (x : ℂ) (c : ℝ)
    (hwhich : x = P st.s ∨ x = P st.t)
    (hxc : P c = x) (hc0 : 0 < c) (hcT : c < T)
    (hmid : x ∈ S36Events.eventMiddle st.center st.radius)
    (h0x : st.radius ≤ dist (P 0) x)
    (hTx : st.radius ≤ dist (P T) x) :
    ∀ j : ℕ, 0 < SupercriticalConformalCovariance.Regular.dyadic j →
      SupercriticalConformalCovariance.Regular.dyadic j ≤ (1 - (a : ℝ)) ^ 2 →
      S36Events.pointSphereDist D x
        (SupercriticalConformalCovariance.Regular.dyadic j * st.radius) ≤
          ENNReal.ofReal ((SupercriticalConformalCovariance.Regular.dyadic j) ^ (θ : ℝ)) *
            D (P st.s, P st.t) ∧
      Consolidated.aroundRat
        (D, (x, SupercriticalConformalCovariance.Regular.dyadic j * st.radius,
          Real.sqrt (SupercriticalConformalCovariance.Regular.dyadic j) * st.radius)) ≤
          ENNReal.ofReal ((SupercriticalConformalCovariance.Regular.dyadic j) ^ (θ : ℝ)) *
            D (P st.s, P st.t) := by
  have hr : 0 < st.radius :=
    lt_of_lt_of_le (by positivity : 0 < ε ^ 2 * b) st.radius_min
  have hhalf : 1 / 2 < α := by rw [hα]; linarith [a.2.1, q.2.2]
  obtain ⟨σ, τ, hσ0, hσs, htτ, hτT, hinternal⟩ :=
    S36Events.CoveredStep.internal_boundary_geodesic D st hP hgeo hunit
      hP0 hPT hr hhalf ha0 htT
  obtain ⟨hsmall, _, _, hsep, _, _, _, _⟩ :=
    S36Events.CoveredStep.event_endpoint_geometry st q a hα hP0 hPT hr
  intro j hδpos hδa
  let δ := SupercriticalConformalCovariance.Regular.dyadic j
  have hδq : δ ≤ (q : ℝ) := hδa.trans hsmall
  have hδ1 : δ < 1 := hδq.trans_lt (q.2.2.trans (by norm_num))
  have hρ : 0 < δ * st.radius := mul_pos hδpos hr
  have hρσ : δ * st.radius < Real.sqrt δ * st.radius :=
    mul_lt_mul_of_pos_right (Consolidated.lt_sqrt_self hδpos hδ1) hr
  let Aj : EuclideanAnnulus :=
    ⟨(x, (δ * st.radius, Real.sqrt δ * st.radius)), ⟨hρ, hρσ⟩⟩
  have hhit : ∃ v ∈ Icc σ τ, P v ∈ ball x (((1 / 2 : ℝ) ^ j) * st.radius) := by
    rcases hwhich with hs | ht
    · refine ⟨st.s, ⟨hσs.le, st.s_lt_t.le.trans htτ.le⟩, ?_⟩
      rw [hs, ← dyadic_eq_half_pow]
      exact Metric.mem_ball_self hρ
    · refine ⟨st.t, ⟨hσs.le.trans st.s_lt_t.le, htτ.le⟩, ?_⟩
      rw [ht, ← dyadic_eq_half_pow]
      exact Metric.mem_ball_self hρ
  obtain ⟨A, hcenter, hinner, houter, hreg⟩ :=
    hG1 P σ τ hinternal j (by simpa only [← dyadic_eq_half_pow] using hδq)
      x hmid hhit
  have hA : A = Aj := by
    apply S36Events.annulus_eq_of_data
    · exact hcenter
    · change A.innerRadius = δ * st.radius
      simpa only [← dyadic_eq_half_pow] using hinner
    · change A.outerRadius = Real.sqrt δ * st.radius
      simpa only [← dyadic_eq_half_pow] using houter
  have hreg' : aroundDist D Aj ≤
      ENNReal.ofReal (δ ^ (θ : ℝ)) * acrossDist D Aj := by
    simpa only [hA, ← dyadic_eq_half_pow] using hreg
  have hroot : Real.sqrt δ ≤ 1 - (a : ℝ) := by
    calc
      Real.sqrt δ ≤ Real.sqrt ((1 - (a : ℝ)) ^ 2) := Real.sqrt_le_sqrt hδa
      _ = 1 - (a : ℝ) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith [a.2.2])]
  have hfar : Real.sqrt δ * st.radius ≤ dist (P st.s) (P st.t) :=
    (mul_le_mul_of_nonneg_right hroot hr.le).trans hsep
  have hcross : acrossDist D Aj ≤ D (P st.s, P st.t) := by
    rcases hwhich with hs | ht
    · simpa only [Aj, hs] using
        (S36Events.across_le_geodesic_from_start D hP hgeo hunit
          (ha0.le.trans st.a_lt_s.le) st.s_lt_t.le htT.le hρ hρσ
            (by rw [dist_comm]; exact hfar))
    · simpa only [Aj, ht] using
        (S36Events.across_le_geodesic_from_end D hP hgeo hunit
          (ha0.le.trans st.a_lt_s.le) st.s_lt_t.le htT.le hρ hρσ hfar)
  have hloop : aroundDist D Aj ≤
      ENNReal.ofReal (δ ^ (θ : ℝ)) * D (P st.s, P st.t) :=
    hreg'.trans (by gcongr)
  have hδr : Aj.outerRadius ≤ st.radius := by
    change Real.sqrt δ * st.radius ≤ st.radius
    have hsqrt : Real.sqrt δ ≤ 1 := by
      simpa using Real.sqrt_le_sqrt hδ1.le
    nlinarith only [mul_le_mul_of_nonneg_right hsqrt hr.le]
  have hpoint := S36Events.pointSphereDist_le_around D Aj hc0 hcT hP hgeo
    hunit hxc (hδr.trans h0x) (hδr.trans hTx)
  constructor
  · have heq : S36Events.pointSphereDist D x (δ * st.radius) =
        SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios.setDist D
          {x} (Metric.sphere x (δ * st.radius)) := by
      simp [S36Events.pointSphereDist, S36Events.spherePairInf_zero_eq,
        SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios.setDist]
    exact heq.trans_le (hpoint.trans hloop)
  · rw [Consolidated.aroundDist_eq_aroundRat] at hloop
    simpa only [Aj, δ, EuclideanAnnulus.center, EuclideanAnnulus.innerRadius,
      EuclideanAnnulus.outerRadius] using hloop

/-- The printed estimate (12), with (7)–(9) derived from (G1)–(G3)
and geodesic minimality. `e` remains a raw distance function. -/
theorem covered_step_improved_length
    (D : LSCMetric) (e : ℂ × ℂ → ℝ≥0∞)
    {P : ℝ → ℂ} {Good : ℂ → ℝ → Prop}
    {ε b α T : ℝ} {z w : ℂ}
    (st : SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.CoveredStep
      P Good ε b α z w)
    (ξ Q : ℝ) (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1) (θ : Ioi (0 : ℝ))
    (k c η : ℝ) (hη : 0 ≤ η) (n : ℕ) (hdyad : (q : ℝ) = (1 / 2 : ℝ) ^ n)
    (hα : α = (a : ℝ))
    (hP : ContinuousOn P (Icc 0 T))
    (hgeo : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (hP0 : P 0 = z) (hPT : P T = w)
    (hε : 0 < ε) (hb : 0 < b)
    (ha0 : 0 < st.a) (htT : st.t < T)
    (hG1 : SupercriticalConformalCovariance.GoodAnnulus.G1 D st.center
      ⟨st.radius, lt_of_lt_of_le (by positivity : 0 < ε ^ 2 * b)
        st.radius_min⟩ q θ)
    (hG2 : SupercriticalConformalCovariance.GoodAnnulus.G2 D ξ Q st.center
      ⟨st.radius, lt_of_lt_of_le (by positivity : 0 < ε ^ 2 * b)
        st.radius_min⟩ q a θ k c)
    (hG3 : SupercriticalConformalCovariance.GoodAnnulus.G3 D st.center
      ⟨st.radius, lt_of_lt_of_le (by positivity : 0 < ε ^ 2 * b)
        st.radius_min⟩ q a)
    (hG5 : G5 D e ξ Q st.center
      ⟨st.radius, lt_of_lt_of_le (by positivity : 0 < ε ^ 2 * b)
        st.radius_min⟩ q a θ k c η) :
    e (P st.s, P st.t) ≤ ENNReal.ofReal ((1 + η) * (st.t - st.s)) := by
  let r : Ioi (0 : ℝ) := ⟨st.radius,
    lt_of_lt_of_le (by positivity : 0 < ε ^ 2 * b) st.radius_min⟩
  have hhalf : 1 / 2 < α := by rw [hα]; linarith [a.2.1, q.2.2]
  obtain ⟨σ, τ, hσ0, hσs, htτ, hτT, hinternal⟩ :=
    S36Events.CoveredStep.internal_boundary_geodesic D st hP hgeo hunit
      hP0 hPT r.2 hhalf ha0 htT
  obtain ⟨_, hsmid, htmid, _, h0s, hTs, h0t, hTt⟩ :=
    S36Events.CoveredStep.event_endpoint_geometry st q a hα hP0 hPT r.2
  have hshort : ∀ u ∈ Icc st.s st.t,
      P u ∈ closedBall st.center st.radius \ ball st.center ((a : ℝ) * st.radius) := by
    intro u hu
    change P u ∈ closedBall st.center st.radius ∧
      P u ∉ ball st.center ((a : ℝ) * st.radius)
    simpa only [hα] using st.annulus_segment u hu
  have hdiam := hG3 P σ τ hinternal st.s st.t
    (ha0.trans st.a_lt_s) hσs.le htτ.le hshort
  have hsmall : dist (P st.s) (P st.t) ≤ (q : ℝ) * st.radius := by
    have hsMem : P st.s ∈ P '' Icc st.s st.t :=
      ⟨st.s, ⟨le_rfl, st.s_lt_t.le⟩, rfl⟩
    have htMem : P st.t ∈ P '' Icc st.s st.t :=
      ⟨st.t, ⟨st.s_lt_t.le, le_rfl⟩, rfl⟩
    have hbdd : Bornology.IsBounded (P '' Icc st.s st.t) :=
      ((isCompact_Icc : IsCompact (Icc st.s st.t)).image_of_continuousOn
        (hP.mono (Icc_subset_Icc
          (ha0.le.trans st.a_lt_s.le) htT.le))).isBounded
    exact (Metric.dist_le_diam_of_mem hbdd hsMem htMem).trans hdiam
  have houter :=
    (S36Events.CoveredStep.outer_and_tiny_bounds D st hP hgeo hunit
      hP0 hPT r.2 ha0.le htT q).1
  have h7 : D (P st.s, P st.t) ≤
      ENNReal.ofReal ((1 - (a : ℝ))⁻¹ *
        st.radius ^ (ξ * Q) * Real.exp (ξ * c)) := by
    calc
      D (P st.s, P st.t) ≤ aroundDist D (S36.outerAnn st.center r) := by
        simpa only [S36.outerAnn] using houter
      _ ≤ min (ENNReal.ofReal ((1 - (a : ℝ))⁻¹ *
          st.radius ^ (ξ * Q) * Real.exp (ξ * c)))
          (ENNReal.ofReal (k * (q : ℝ) ^ (-(θ : ℝ))) *
            SupercriticalConformalCovariance.GoodAnnulus.barrier D st.center r) := hG2
      _ ≤ _ := min_le_left _ _
  have h8s := covered_step_dyadic_endpoint D st q a θ hα hP hgeo hunit
    hP0 hPT hε hb ha0 htT hG1 (P st.s) st.s (Or.inl rfl) rfl
    (ha0.trans st.a_lt_s) (st.s_lt_t.trans htT) hsmid h0s hTs
  have h8t := covered_step_dyadic_endpoint D st q a θ hα hP hgeo hunit
    hP0 hPT hε hb ha0 htT hG1 (P st.t) st.t (Or.inr rfl) rfl
    (ha0.trans (st.a_lt_s.trans st.s_lt_t)) htT htmid h0t hTt
  have hgeoSeg := S36Events.geodesic_of_unit_speed D hgeo hunit
    (ha0.le.trans st.a_lt_s.le) st.s_lt_t.le htT.le rfl rfl
  have htrace : P '' Icc st.s st.t ⊆
      SupercriticalConformalCovariance.Regular.closedAnnulus st.center ((a : ℝ) * st.radius) st.radius := by
    rintro x ⟨u, hu, rfl⟩
    exact hshort u hu
  have hpair : SupercriticalConformalCovariance.Regular.SourceRegularPair D st.center
      (P st.s) (P st.t) st.radius a θ
      (st.radius ^ (ξ * Q) * Real.exp (ξ * c)) := by
    refine ⟨⟨P, st.s, st.t, hgeoSeg, htrace⟩, ?_, st.outer_hit, (by simpa only [mul_assoc] using h7), h8s, h8t⟩
    simpa only [hα] using st.inner_hit
  have h9 := covered_step_tiny_loop_le_barrier D st ξ Q q a θ k c n
    hdyad hα hP hgeo hunit hP0 hPT hε hb ha0 htT hG1 hG2
  have hG5' := hG5 (P st.s) (P st.t) hpair hsmall h9
  have hsT : st.s ∈ Icc (0 : ℝ) T :=
    ⟨(ha0.trans st.a_lt_s).le, st.s_lt_t.le.trans htT.le⟩
  have htT' : st.t ∈ Icc (0 : ℝ) T :=
    ⟨(ha0.trans (st.a_lt_s.trans st.s_lt_t)).le, htT.le⟩
  have htime : D (P st.s, P st.t) = ENNReal.ofReal (st.t - st.s) :=
    hgeo.edist_eq_of_hasUnitSpeedOn hunit hsT htT' st.s_lt_t.le
  calc
    e (P st.s, P st.t) ≤ ENNReal.ofReal (1 + η) * D (P st.s, P st.t) := hG5'
    _ = ENNReal.ofReal ((1 + η) * (st.t - st.s)) := by
      rw [htime, ENNReal.ofReal_mul]
      linarith [hη]

/-- Printed (13), using only the comparison at the two points of the
ordinary portion and the source unit-speed geodesic. -/
theorem covered_step_old_cost_le
    (D : LSCMetric) (e : ℂ × ℂ → ℝ≥0∞)
    {P : ℝ → ℂ} {Good : ℂ → ℝ → Prop}
    {ε b α T : ℝ} {z w : ℂ}
    (st : SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.CoveredStep
      P Good ε b α z w)
    (C : ℝ) (hC : 0 ≤ C)
    (hgeo : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (ha0 : 0 ≤ st.a) (htT : st.t ≤ T)
    (hcmp : e (P st.a, P st.s) ≤
      ENNReal.ofReal C * D (P st.a, P st.s)) :
    e (P st.a, P st.s) ≤ ENNReal.ofReal (C * (st.s - st.a)) := by
  have ha : st.a ∈ Icc (0 : ℝ) T :=
    ⟨ha0, (st.a_lt_s.trans st.s_lt_t).le.trans htT⟩
  have hs : st.s ∈ Icc (0 : ℝ) T :=
    ⟨ha0.trans st.a_lt_s.le, st.s_lt_t.le.trans htT⟩
  have htime : D (P st.a, P st.s) = ENNReal.ofReal (st.s - st.a) :=
    hgeo.edist_eq_of_hasUnitSpeedOn hunit ha hs st.a_lt_s.le
  calc
    e (P st.a, P st.s) ≤ ENNReal.ofReal C * D (P st.a, P st.s) := hcmp
    _ = ENNReal.ofReal (C * (st.s - st.a)) := by
      rw [htime, ENNReal.ofReal_mul hC]

/-- One retained step consumes (12), (13), and (14); this is the precise
non-metric telescope adapter for the paper's raw `e`. -/
theorem covered_step_new_cost_le
    (D : LSCMetric) (e : ℂ × ℂ → ℝ≥0∞)
    {P : ℝ → ℂ} {Good : ℂ → ℝ → Prop}
    {ε b α T : ℝ} {z w : ℂ}
    (st : SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.CoveredStep
      P Good ε b α z w)
    (ξ Q : ℝ) (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ))
    (θ : Ioi (0 : ℝ)) (k c η C : ℝ)
    (hη : 0 ≤ η) (hC : 1 + η ≤ C)
    (n : ℕ) (hdyad : (q : ℝ) = (1 / 2 : ℝ) ^ n)
    (hα : α = (a : ℝ))
    (hP : ContinuousOn P (Icc 0 T))
    (hgeo : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (hP0 : P 0 = z) (hPT : P T = w)
    (hε : 0 < ε) (hb : 0 < b)
    (ha0 : 0 < st.a) (htT : st.t < T)
    (hG1 : SupercriticalConformalCovariance.GoodAnnulus.G1 D st.center
      ⟨st.radius, lt_of_lt_of_le (by positivity : 0 < ε ^ 2 * b)
        st.radius_min⟩ q θ)
    (hG2 : SupercriticalConformalCovariance.GoodAnnulus.G2 D ξ Q st.center
      ⟨st.radius, lt_of_lt_of_le (by positivity : 0 < ε ^ 2 * b)
        st.radius_min⟩ q a θ k c)
    (hG3 : SupercriticalConformalCovariance.GoodAnnulus.G3 D st.center
      ⟨st.radius, lt_of_lt_of_le (by positivity : 0 < ε ^ 2 * b)
        st.radius_min⟩ q a)
    (hG4 : SupercriticalConformalCovariance.GoodAnnulus.G4 D st.center
      ⟨st.radius, lt_of_lt_of_le (by positivity : 0 < ε ^ 2 * b)
        st.radius_min⟩ a K)
    (hG5 : G5 D e ξ Q st.center
      ⟨st.radius, lt_of_lt_of_le (by positivity : 0 < ε ^ 2 * b)
        st.radius_min⟩ q a θ k c η)
    (htri : e (P st.a, P st.t) ≤
      e (P st.a, P st.s) + e (P st.s, P st.t))
    (hcmp : e (P st.a, P st.s) ≤
      ENNReal.ofReal C * D (P st.a, P st.s)) :
    e (P st.a, P st.t) ≤
      ENNReal.ofReal (newConstant C η K * (st.t - st.a)) := by
  have hbad := covered_step_old_cost_le D e st C (by linarith [hη, hC])
    hgeo hunit ha0.le htT.le hcmp
  have hgood := covered_step_improved_length D e st ξ Q q a θ k c η hη n
    hdyad hα hP hgeo hunit hP0 hPT hε hb ha0 htT hG1 hG2 hG3 hG5
  have hratio := covered_step_old_length_le D st q a K hα hP hgeo hunit
    hP0 hPT hε hb ha0 htT hG4
  have ha : 0 ≤ st.s - st.a := sub_nonneg.mpr st.a_lt_s.le
  have hb' : 0 ≤ st.t - st.s := sub_nonneg.mpr st.s_lt_t.le
  have hstep := improved_two_pieces e (P st.a) (P st.s) (P st.t)
    (le_trans (by norm_num : (0 : ℝ) ≤ 1) K.2.le) ha hb' hη hC
    hratio htri hbad hgood
  have htime : (st.s - st.a) + (st.t - st.s) = st.t - st.a := by ring
  simpa only [htime] using hstep

theorem unit_geodesic_injOn (D : LSCMetric) {P : ℝ → ℂ} {T : ℝ}
    (hgeo : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T)) :
    Set.InjOn P (Icc 0 T) := by
  intro s hs t ht hst
  rcases le_total s t with hle | hle
  · have hd := hgeo.edist_eq_of_hasUnitSpeedOn hunit hs ht hle
    have heq : (D.pt ∘ P) s = (D.pt ∘ P) t := congrArg D.pt hst
    rw [heq, edist_self] at hd
    have hzero : t - s ≤ 0 := ENNReal.ofReal_eq_zero.mp hd.symm
    linarith
  · have hd := hgeo.edist_eq_of_hasUnitSpeedOn hunit ht hs hle
    have heq : (D.pt ∘ P) t = (D.pt ∘ P) s := congrArg D.pt hst.symm
    rw [heq, edist_self] at hd
    have hzero : s - t ≤ 0 := ENNReal.ofReal_eq_zero.mp hd.symm
    linarith

/-- A Euclidean-continuous injective geodesic cannot return near its
starting endpoint at a time bounded away from the start. This is the
compact-inverse step in lines 500–503, stated without any metric on `e`. -/
theorem start_time_of_small_euclidean_ball
    {P : ℝ → ℂ} {T τ : ℝ}
    (hP : ContinuousOn P (Icc 0 T))
    (hinj : Set.InjOn P (Icc 0 T))
    (hτ0 : 0 < τ) (hτT : τ ≤ T) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Icc (0 : ℝ) T,
      dist (P t) (P 0) < δ → t < τ := by
  have hcompact : IsCompact (P '' Icc τ T) :=
    (isCompact_Icc : IsCompact (Icc τ T)).image_of_continuousOn
      (hP.mono (Icc_subset_Icc hτ0.le le_rfl))
  have hnot : P 0 ∉ P '' Icc τ T := by
    rintro ⟨t, ht, heq⟩
    have heq' : t = 0 := hinj
      ⟨hτ0.le.trans ht.1, ht.2⟩ ⟨le_rfl, hτ0.le.trans hτT⟩ heq
    linarith [ht.1]
  have hnhds : (P '' Icc τ T)ᶜ ∈ 𝓝 (P 0) :=
    hcompact.isClosed.isOpen_compl.mem_nhds hnot
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨δ, hδ, ?_⟩
  intro t ht hdist
  by_contra hlate
  have htτ : τ ≤ t := le_of_not_gt hlate
  have hmem : P t ∈ P '' Icc τ T := ⟨t, ⟨htτ, ht.2⟩, rfl⟩
  exact (hball (Metric.mem_ball.mpr (by simpa only [dist_comm (P 0) (P t)] using hdist))) hmem

/-- Terminal analogue of `start_time_of_small_euclidean_ball`. -/
theorem end_time_of_small_euclidean_ball
    {P : ℝ → ℂ} {T τ : ℝ}
    (hP : ContinuousOn P (Icc 0 T))
    (hinj : Set.InjOn P (Icc 0 T))
    (hτ0 : 0 ≤ τ) (hτT : τ < T) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Icc (0 : ℝ) T,
      dist (P t) (P T) < δ → τ < t := by
  have hcompact : IsCompact (P '' Icc 0 τ) :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) τ)).image_of_continuousOn
      (hP.mono (Icc_subset_Icc le_rfl hτT.le))
  have hnot : P T ∉ P '' Icc 0 τ := by
    rintro ⟨t, ht, heq⟩
    have heq' : t = T := hinj
      ⟨ht.1, ht.2.trans hτT.le⟩ ⟨hτ0.trans hτT.le, le_rfl⟩ heq
    linarith [ht.2]
  have hnhds : (P '' Icc 0 τ)ᶜ ∈ 𝓝 (P T) :=
    hcompact.isClosed.isOpen_compl.mem_nhds hnot
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨δ, hδ, ?_⟩
  intro t ht hdist
  by_contra hearly
  have htτ : t ≤ τ := le_of_not_gt hearly
  have hmem : P t ∈ P '' Icc 0 τ := ⟨t, ⟨ht.1, htτ⟩, rfl⟩
  exact (hball (Metric.mem_ball.mpr
    (by simpa only [dist_comm (P T) (P t)] using hdist))) hmem

/-- Display (10) along one deterministic sequence of scales and a countable
compact exhaustion. This is a genuine geometric cover predicate, not a
statement of the desired comparison. -/
def GoodCover (D : LSCMetric) (e : ℂ × ℂ → ℝ≥0∞)
    (ξ Q : ℝ) (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ))
    (θ : Ioi (0 : ℝ)) (k η : ℝ)
    (exhaustion : ℕ → Set ℂ) (ε : ℕ → ℝ) : Prop :=
  Tendsto ε atTop (nhds 0) ∧
    (∀ j, 0 < ε j ∧ ε j ≤ 1) ∧
    ∀ n, ∀ᶠ j in atTop, ∀ x ∈ exhaustion n,
      ∃ z : ℂ, ∃ r : ℝ, ∃ hr : 0 < r, ∃ c : ℝ,
        Good D e ξ Q z ⟨r, hr⟩ q a K θ k c η ∧
          (ε j) ^ 2 ≤ r ∧ r ≤ ε j ∧ x ∈ ball z (r / 2)

/-- On a whole-plane geodesic contained in U, the domain internal metric
agrees with the whole-plane distance between any two ordered times. -/
theorem internal_eq_of_unit_geodesic_segment
    (D : LSCMetric) (U : Set ℂ) {P : ℝ → ℂ} {T s t : ℝ}
    (hgeo : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (htrace : ∀ v ∈ Icc (0 : ℝ) T, P v ∈ U)
    (hs : s ∈ Icc (0 : ℝ) T) (ht : t ∈ Icc (0 : ℝ) T)
    (hst : s ≤ t) :
    D.internal U (⟨P s, htrace s hs⟩, ⟨P t, htrace t ht⟩) =
      D (P s, P t) := by
  have hsub : Icc s t ⊆ Icc (0 : ℝ) T := Icc_subset_Icc hs.1 ht.2
  have hP : D.IsCurve P s t := ⟨hst, hgeo.2.1.mono hsub⟩
  have hU : ∀ v ∈ Icc s t, P v ∈ U := fun v hv => htrace v (hsub hv)
  have hlen : D.len P s t = ENNReal.ofReal (t - s) :=
    curveLength_of_hasUnitSpeedOn hunit hs ht
  have hdist : D (P s, P t) = ENNReal.ofReal (t - s) :=
    hgeo.edist_eq_of_hasUnitSpeedOn hunit hs ht hst
  apply le_antisymm
  · calc
      D.internal U (⟨P s, htrace s hs⟩, ⟨P t, htrace t ht⟩) ≤
          D.len P s t := by
            simpa using D.internal_le_len U P s t hP hU
      _ = D (P s, P t) := hlen.trans hdist.symm
  · exact D.edist_le_internal U (⟨P s, htrace s hs⟩, ⟨P t, htrace t ht⟩)

theorem internal_self_eq_zero (D : LSCMetric) (U : Set ℂ)
    (x : U) : D.internal U (x, x) = 0 := by
  apply le_antisymm
  · have hP : D.IsCurve (fun _ : ℝ => (x : ℂ)) 0 0 :=
      ⟨le_rfl, continuousOn_const⟩
    have hU : ∀ t ∈ Icc (0 : ℝ) 0, (x : ℂ) ∈ U := fun _ _ => x.property
    have h := D.internal_le_len U (fun _ : ℝ => (x : ℂ)) 0 0 hP hU
    simpa [LSCMetric.len] using h
  · exact bot_le

/-- The retained finite corridor, with good clauses read directly from each
stopping record. This is the telescoping conclusion before the endpoint pieces
are restored. -/
theorem retained_corridor_cost_le
    (D : LSCMetric) (e : ℂ × ℂ → ℝ≥0∞)
    (U : Set ℂ) {P : ℝ → ℂ} {ε b α T t₀ : ℝ} {z w : ℂ}
    (ξ Q : ℝ) (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ))
    (θ : Ioi (0 : ℝ)) (k η C : ℝ)
    (hη : 0 ≤ η) (hC : 1 + η ≤ C)
    (n : ℕ) (hdyad : (q : ℝ) = (1 / 2 : ℝ) ^ n)
    (hα : α = (a : ℝ))
    (steps : List
      (SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.CoveredStep P
        (fun z r => ∃ hr : 0 < r, ∃ c : ℝ,
          Good D e ξ Q z ⟨r, hr⟩ q a K θ k c η)
        ε b α z w))
    (hne : steps ≠ [])
    (hfrom : SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.StepsFrom t₀ steps)
    (hlast : ∀ st ∈ steps, st.t < T)
    (hP : ContinuousOn P (Icc 0 T))
    (hgeo : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (hP0 : P 0 = z) (hPT : P T = w)
    (htrace : ∀ t ∈ Icc (0 : ℝ) T, P t ∈ U)
    (hε : 0 < ε) (hb : 0 < b) (ht₀ : 0 < t₀)
    (htri : ∀ x ∈ U, ∀ y ∈ U, ∀ v ∈ U,
      e (x, v) ≤ e (x, y) + e (y, v))
    (hcmp : ∀ x y : U,
      e (x, y) ≤ ENNReal.ofReal C * D.internal U (x, y)) :
    e (P t₀,
      P (SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.StepsEnd t₀ steps)) ≤
      ENNReal.ofReal (newConstant C η K *
        (SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.StepsEnd t₀ steps - t₀)) := by
  have hstarts :=
    SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.steps_start_pos
      steps ht₀ hfrom
  have hstep : ∀ st ∈ steps,
      e (P st.a, P st.t) ≤
        ENNReal.ofReal (newConstant C η K * (st.t - st.a)) := by
    intro st hst
    obtain ⟨hr, c, hLit, hG5⟩ := st.good
    obtain ⟨hG1, hG2, hG3, hG4⟩ := hLit
    have hst0 : 0 ≤ st.a := (hstarts st hst).le
    have hsa : st.a ∈ Icc (0 : ℝ) T :=
      ⟨hst0, (st.a_lt_s.trans st.s_lt_t).le.trans (hlast st hst).le⟩
    have hss : st.s ∈ Icc (0 : ℝ) T :=
      ⟨hst0.trans st.a_lt_s.le, st.s_lt_t.le.trans (hlast st hst).le⟩
    have hstt : st.t ∈ Icc (0 : ℝ) T :=
      ⟨hst0.trans (st.a_lt_s.trans st.s_lt_t).le, (hlast st hst).le⟩
    exact covered_step_new_cost_le D e st ξ Q q a K θ k c η C hη hC
      n hdyad hα hP hgeo hunit hP0 hPT hε hb (hstarts st hst)
      (hlast st hst) hG1 hG2 hG3 hG4 hG5
      (htri _ (htrace st.a hsa) _ (htrace st.s hss) _ (htrace st.t hstt))
      (by
        have h := hcmp ⟨P st.a, htrace st.a hsa⟩
          ⟨P st.s, htrace st.s hss⟩
        simpa only [internal_eq_of_unit_geodesic_segment D U hgeo hunit
          htrace hsa hss st.a_lt_s.le] using h)
  have hend : SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.StepsEnd
      t₀ steps ≤ T :=
    (SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.stepsEnd_lt_T
      steps hne hlast).le
  exact raw_steps_telescope e U htri steps hne
    (le_trans (by norm_num : (0 : ℝ) ≤ 1)
      (newConstant_ge (le_trans (by norm_num : (0 : ℝ) ≤ 1) K.2.le)
        hη hC)) htrace ht₀.le hend hfrom hstep

/-- One good-cover scale, with endpoint time bounds supplied separately
by the compact-inverse lemmas. This helper is consumed only in the limit proof. -/
private theorem fixed_scale_geodesic_bound
    (D : LSCMetric) (e : ℂ × ℂ → ℝ≥0∞)
    (U V : Set ℂ) {P : ℝ → ℂ} {T : ℝ} {z w : ℂ}
    (ξ Q : ℝ) (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ))
    (θ : Ioi (0 : ℝ)) (k η C : ℝ)
    (hη : 0 ≤ η) (hC : 1 + η ≤ C)
    (n : ℕ) (hdyad : (q : ℝ) = (1 / 2 : ℝ) ^ n)
    (hP : ContinuousOn P (Icc 0 T))
    (hgeo : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (hP0 : P 0 = z) (hPT : P T = w) (hT : 0 < T)
    (htraceU : ∀ t ∈ Icc (0 : ℝ) T, P t ∈ U)
    (htraceV : ∀ t ∈ Icc (0 : ℝ) T, P t ∈ V)
    (htri : ∀ x ∈ U, ∀ y ∈ U, ∀ v ∈ U,
      e (x, v) ≤ e (x, y) + e (y, v))
    (hcmp : ∀ x y : U,
      e (x, y) ≤ ENNReal.ofReal C * D.internal U (x, y))
    (κ ε τ : ℝ) (hκ : 0 < κ) (hκdist : κ ≤ dist z w)
    (hε : 0 < ε) (hεκ : ε ≤ κ / 32)
    (hτ : 0 < τ) (hτT : τ < T)
    (hstartLoc : ∀ t ∈ Icc (0 : ℝ) T,
      dist (P t) z < 7 * ε → t < τ)
    (hendLoc : ∀ t ∈ Icc (0 : ℝ) T,
      dist (P t) w < 7 * ε → T - τ < t)
    (hcover : ∀ x ∈ V, ∃ center r,
      (∃ hr : 0 < r, ∃ c : ℝ,
        Good D e ξ Q center ⟨r, hr⟩ q a K θ k c η) ∧
      ε ^ 2 ≤ r ∧ r ≤ ε ∧ x ∈ ball center (r / 2)) :
    e (z, w) ≤ ENNReal.ofReal
      (newConstant C η K * T + 2 * C * τ) := by
  obtain ⟨t₀, τ₀, steps, ht₀, ht₀τ, hτ₀T, hne, hfrom, hτend,
      hlast, hstart, hfinish⟩ :=
    SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.stopping_construction
      V hε (by norm_num : (0 : ℝ) < 1) hεκ
      (by linarith [a.2.1, q.2.2] : 1 / 2 < (a : ℝ)) a.2.2
      hP hT hP0 hPT (by simpa using hκdist) htraceV
      (by simpa only [one_mul, mul_one] using hcover)
  let t₁ := SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.StepsEnd t₀ steps
  have ht₁T : t₁ < T :=
    SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.stepsEnd_lt_T steps hne hlast
  have ht₀T : t₀ < T := by linarith [hτ₀T]
  have ht₁0 : 0 ≤ t₁ := ht₀.le.trans
    (SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.stepsEnd_ge_start steps hfrom)
  have hloc₀ : t₀ < τ := hstartLoc t₀ ⟨ht₀.le, ht₀T.le⟩ (by
    simpa only [mul_one] using Metric.mem_ball.mp hstart)
  have hloc₁ : T - τ < t₁ := hendLoc t₁ ⟨ht₁0, ht₁T.le⟩ (by
    simpa only [mul_one] using Metric.mem_ball.mp hfinish)
  have hret := retained_corridor_cost_le D e U ξ Q q a K θ k η C
    hη hC n hdyad rfl steps hne hfrom hlast hP hgeo hunit hP0 hPT
    htraceU hε (by norm_num : (0 : ℝ) < 1) ht₀ htri hcmp
  have h0 : P 0 ∈ U := htraceU 0 ⟨le_rfl, hT.le⟩
  have hTmem : P T ∈ U := htraceU T ⟨hT.le, le_rfl⟩
  have ht₀mem : P t₀ ∈ U := htraceU t₀ ⟨ht₀.le, ht₀T.le⟩
  have ht₁mem : P t₁ ∈ U := htraceU t₁ ⟨ht₁0, ht₁T.le⟩
  have htime₀ : D (z, P t₀) = ENNReal.ofReal t₀ := by
    have htime : D (P 0, P t₀) = ENNReal.ofReal (t₀ - 0) :=
      hgeo.edist_eq_of_hasUnitSpeedOn hunit
        ⟨le_rfl, hT.le⟩ ⟨ht₀.le, ht₀T.le⟩ ht₀.le
    simpa only [hP0, sub_zero] using htime
  have htime₁ : D (P t₁, w) = ENNReal.ofReal (T - t₁) := by
    rw [← hPT]
    exact hgeo.edist_eq_of_hasUnitSpeedOn hunit
      ⟨ht₁0, ht₁T.le⟩ ⟨hT.le, le_rfl⟩ ht₁T.le
  have hC0 : 0 ≤ C := by linarith [hη, hC]
  have hN0 : 0 ≤ newConstant C η K :=
    (le_trans (by norm_num : (0 : ℝ) ≤ 1)
      (newConstant_ge (le_trans (by norm_num : (0 : ℝ) ≤ 1) K.2.le)
        hη hC))
  have hlen : 0 ≤ t₁ - t₀ := sub_nonneg.mpr
    (SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.stepsEnd_ge_start steps hfrom)
  have hreal : C * t₀ + newConstant C η K * (t₁ - t₀) +
      C * (T - t₁) ≤ newConstant C η K * T + 2 * C * τ := by
    have h0bound : C * t₀ ≤ C * τ :=
      mul_le_mul_of_nonneg_left hloc₀.le hC0
    have h1bound : C * (T - t₁) ≤ C * τ :=
      mul_le_mul_of_nonneg_left (by linarith [hloc₁]) hC0
    have hmidbound : newConstant C η K * (t₁ - t₀) ≤
        newConstant C η K * T :=
      mul_le_mul_of_nonneg_left (by linarith [ht₁T, ht₀]) hN0
    nlinarith only [h0bound, h1bound, hmidbound]
  have hstartCost : e (z, P t₀) ≤ ENNReal.ofReal (C * t₀) := by
    calc
      e (z, P t₀) ≤ ENNReal.ofReal C * D (z, P t₀) := by
        have h := hcmp ⟨P 0, h0⟩ ⟨P t₀, ht₀mem⟩
        rw [internal_eq_of_unit_geodesic_segment D U hgeo hunit
          htraceU ⟨le_rfl, hT.le⟩ ⟨ht₀.le, ht₀T.le⟩ ht₀.le] at h
        simpa only [hP0] using h
      _ = ENNReal.ofReal (C * t₀) := by rw [htime₀, ENNReal.ofReal_mul hC0]
  have hendCost : e (P t₁, w) ≤ ENNReal.ofReal (C * (T - t₁)) := by
    calc
      e (P t₁, w) ≤ ENNReal.ofReal C * D (P t₁, w) := by
        have h := hcmp ⟨P t₁, ht₁mem⟩ ⟨P T, hTmem⟩
        rw [internal_eq_of_unit_geodesic_segment D U hgeo hunit
          htraceU ⟨ht₁0, ht₁T.le⟩ ⟨hT.le, le_rfl⟩ ht₁T.le] at h
        simpa only [hPT] using h
      _ = ENNReal.ofReal (C * (T - t₁)) := by rw [htime₁, ENNReal.ofReal_mul hC0]
  have hnonneg₀ : 0 ≤ C * t₀ := mul_nonneg hC0 ht₀.le
  have hnonneg₁ : 0 ≤ newConstant C η K * (t₁ - t₀) :=
    mul_nonneg hN0 hlen
  have hnonneg₂ : 0 ≤ C * (T - t₁) :=
    mul_nonneg hC0 (sub_nonneg.mpr ht₁T.le)
  calc
    e (z, w) = e (P 0, P T) := by rw [hP0, hPT]
    _ ≤ e (P 0, P t₀) + e (P t₀, P T) :=
      htri _ h0 _ ht₀mem _ hTmem
    _ ≤ e (P 0, P t₀) + (e (P t₀, P t₁) + e (P t₁, P T)) := by
      gcongr
      exact htri _ ht₀mem _ ht₁mem _ hTmem
    _ ≤ ENNReal.ofReal (C * t₀) +
        (ENNReal.ofReal (newConstant C η K * (t₁ - t₀)) +
          ENNReal.ofReal (C * (T - t₁))) := by
      rw [hP0, hPT]
      exact add_le_add hstartCost (add_le_add hret hendCost)
    _ = ENNReal.ofReal (C * t₀ + newConstant C η K * (t₁ - t₀) +
          C * (T - t₁)) := by
      rw [← ENNReal.ofReal_add hnonneg₁ hnonneg₂,
        ← ENNReal.ofReal_add hnonneg₀ (add_nonneg hnonneg₁ hnonneg₂)]
      ring
    _ ≤ ENNReal.ofReal (newConstant C η K * T + 2 * C * τ) :=
      ENNReal.ofReal_le_ofReal hreal

/-- The actual endpoint limit for a source geodesic whose trace lies in one
member of the compact exhaustion. This uses only the good-cover event and the
raw comparison and triangle properties of `e`. -/
theorem geodesic_bound_of_goodCover
    (D : LSCMetric) (e : ℂ × ℂ → ℝ≥0∞)
    (U : Set ℂ) {P : ℝ → ℂ} {T : ℝ} {z w : ℂ}
    (ξ Q : ℝ) (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ))
    (θ : Ioi (0 : ℝ)) (k η C : ℝ)
    (hη : 0 ≤ η) (hC : 1 + η ≤ C)
    (n : ℕ) (hdyad : (q : ℝ) = (1 / 2 : ℝ) ^ n)
    (exhaustion : ℕ → Set ℂ) (ε : ℕ → ℝ)
    (hgood : GoodCover D e ξ Q q a K θ k η exhaustion ε)
    (N : ℕ) (htraceN : ∀ t ∈ Icc (0 : ℝ) T, P t ∈ exhaustion N)
    (hP : ContinuousOn P (Icc 0 T))
    (hgeo : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (hP0 : P 0 = z) (hPT : P T = w) (hT : 0 < T) (hzw : z ≠ w)
    (htraceU : ∀ t ∈ Icc (0 : ℝ) T, P t ∈ U)
    (htri : ∀ x ∈ U, ∀ y ∈ U, ∀ v ∈ U,
      e (x, v) ≤ e (x, y) + e (y, v))
    (hcmp : ∀ x y : U,
      e (x, y) ≤ ENNReal.ofReal C * D.internal U (x, y)) :
    e (z, w) ≤ ENNReal.ofReal (newConstant C η K * T) := by
  have hinj := unit_geodesic_injOn D hgeo hunit
  have hκ : 0 < dist z w := dist_pos.mpr hzw
  have hτbound : ∀ τ : ℝ, 0 < τ → τ < T →
      e (z, w) ≤ ENNReal.ofReal
        (newConstant C η K * T + 2 * C * τ) := by
    intro τ hτ hτT
    obtain ⟨δ₀, hδ₀, hloc₀⟩ :=
      start_time_of_small_euclidean_ball hP hinj hτ hτT.le
    obtain ⟨δ₁, hδ₁, hloc₁⟩ :=
      end_time_of_small_euclidean_ball hP hinj (by linarith : 0 ≤ T - τ)
        (by linarith : T - τ < T)
    have hsmall : ∀ᶠ j in atTop,
        ε j < min (dist z w / 32) (min (δ₀ / 7) (δ₁ / 7)) :=
      hgood.1.eventually (eventually_lt_nhds (by
        apply lt_min
        · positivity
        · apply lt_min <;> positivity))
    obtain ⟨j, ⟨hj, hjcover⟩, hjε⟩ :=
      ((hsmall.and (hgood.2.2 N)).and (Filter.Eventually.of_forall
        (fun j => hgood.2.1 j))).exists
    have hεκ : ε j ≤ dist z w / 32 := hj.le.trans (min_le_left _ _)
    have hε₀ : 7 * ε j < δ₀ := by
      have := hj.trans_le (min_le_right _ _)
      have := this.trans_le (min_le_left _ _)
      linarith
    have hε₁ : 7 * ε j < δ₁ := by
      have := hj.trans_le (min_le_right _ _)
      have := this.trans_le (min_le_right _ _)
      linarith
    apply fixed_scale_geodesic_bound D e U (exhaustion N) ξ Q q a K θ k η C
      hη hC n hdyad hP hgeo hunit hP0 hPT hT htraceU htraceN htri hcmp
      (dist z w) (ε j) τ hκ le_rfl hjε.1 hεκ hτ hτT
    · intro t ht hdist
      exact hloc₀ t ht (by simpa only [hP0] using lt_trans hdist hε₀)
    · intro t ht hdist
      exact hloc₁ t ht (by simpa only [hPT] using lt_trans hdist hε₁)
    · intro x hx
      obtain ⟨center, r, hr, c, hgood', hrlo, hrhi, hxball⟩ := hjcover x hx
      exact ⟨center, r, ⟨hr, c, hgood'⟩, hrlo, hrhi, hxball⟩
  have hτpos (j : ℕ) : 0 < (T / 2) / ((j : ℝ) + 1) :=
    div_pos (div_pos hT (by norm_num)) (by positivity)
  have hτlt (j : ℕ) : (T / 2) / ((j : ℝ) + 1) < T := by
    have hd : 1 ≤ (j : ℝ) + 1 := by nlinarith [Nat.cast_nonneg (α := ℝ) j]
    have hp : 0 < (j : ℝ) + 1 := by positivity
    have hle : (T / 2) / ((j : ℝ) + 1) ≤ T / 2 :=
      (div_le_iff₀ hp).2 (by nlinarith)
    linarith
  have hreal : Tendsto
      (fun j : ℕ => newConstant C η K * T +
        2 * C * ((T / 2) / ((j : ℝ) + 1)))
      atTop (nhds (newConstant C η K * T)) := by
    convert (tendsto_const_nhds (x := newConstant C η K * T)).add
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (C * T)) using 1
    · ext j
      ring
    · ring
  exact ge_of_tendsto (ENNReal.tendsto_ofReal hreal)
    (Filter.Eventually.of_forall (fun j => hτbound _ (hτpos j) (hτlt j)))

/-- Lower semicontinuity alone gives the positive compact margin used in
lines 509–515: disjoint compact sets have positive `D`-separation. -/
theorem positive_compact_separation (D : LSCMetric)
    {A B : Set ℂ} (hA : IsCompact A) (hB : IsCompact B)
    (hneA : A.Nonempty) (hneB : B.Nonempty) (hdisj : Disjoint A B) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ x ∈ A, ∀ y ∈ B, δ ≤ D (x, y) := by
  let S : Set (ℂ × ℂ) := A ×ˢ B
  have hS : IsCompact S := hA.prod hB
  have hSne : S.Nonempty := by
    rcases hneA with ⟨x, hx⟩
    rcases hneB with ⟨y, hy⟩
    exact ⟨(x, y), ⟨hx, hy⟩⟩
  obtain ⟨p, hp, hmin⟩ :=
    D.lowerSemicontinuous.lowerSemicontinuousOn S |>.exists_isMinOn hSne hS
  refine ⟨D p, ?_, ?_⟩
  · rcases eq_zero_or_pos (D p) with hz | hz
    · have heq := D.isExtMetric.2.1 p.1 p.2 hz
      have hmem : p.1 ∈ A ∩ B := by
        exact ⟨hp.1, heq ▸ hp.2⟩
      have hempty : p.1 ∈ (∅ : Set ℂ) := hdisj.le_bot hmem
      simp at hempty
    · exact hz
  · intro x hx y hy
    exact hmin ⟨hx, hy⟩

/-- A compact trace inside an open domain has a compact buffer. -/
theorem compact_buffer_of_trace {A U : Set ℂ} (hA : IsCompact A)
    (hU : IsOpen U) (hAU : A ⊆ U) :
    ∃ K₀ : Set ℂ, IsCompact K₀ ∧ A ⊆ interior K₀ ∧ K₀ ⊆ U := by
  obtain ⟨ρ, hρ, hsub⟩ := hA.exists_cthickening_subset_open hU hAU
  refine ⟨cthickening ρ A, hA.cthickening, ?_, hsub⟩
  exact (self_subset_thickening hρ A).trans
    (thickening_subset_interior_cthickening ρ A)

/-- The compact trace has a uniform positive source-metric distance from the
boundary of its compact buffer. -/
theorem compact_buffer_margin (D : LSCMetric) {A K₀ : Set ℂ}
    (hA : IsCompact A) (hneA : A.Nonempty) (hK₀ : IsCompact K₀)
    (hAK : A ⊆ interior K₀) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧
      ∀ x ∈ A, ∀ y ∈ frontier K₀, δ ≤ D (x, y) := by
  let B := frontier K₀
  have hB : IsCompact B :=
    hK₀.of_isClosed_subset isClosed_frontier hK₀.isClosed.frontier_subset
  have hdisj : Disjoint A B := by
    apply disjoint_left.mpr
    intro x hxA hxB
    exact hxB.2 (hAK hxA)
  by_cases hneB : B.Nonempty
  · exact positive_compact_separation D hA hB hneA hneB hdisj
  · refine ⟨1, by norm_num, ?_⟩
    intro x hx y hy
    exact False.elim (hneB ⟨y, hy⟩)

/-- A geodesic shorter than the trace-to-boundary margin stays in the compact
buffer. In particular its image lies in the open domain containing the buffer. -/
theorem short_geodesic_stays_in_buffer
    (D : LSCMetric) {A K₀ : Set ℂ} {x y : ℂ} {R : ℝ → ℂ}
    {T : ℝ} {δ : ℝ≥0∞}
    (hK₀ : IsCompact K₀) (hAK : A ⊆ interior K₀)
    (hx : x ∈ A)
    (hmargin : ∀ x ∈ A, ∀ y ∈ frontier K₀, δ ≤ D (x, y))
    (hshort : D (x, y) < δ)
    (hfin : D (x, y) < ∞)
    (hT : T = (D (x, y)).toReal)
    (hR : ContinuousOn R (Icc 0 T))
    (hgeo : IsGeodesicCurve (D.pt ∘ R) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ R) (Icc 0 T))
    (hR0 : R 0 = x) :
    ∀ t ∈ Icc (0 : ℝ) T, R t ∈ interior K₀ := by
  intro t ht
  by_contra hout
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T :=
    Icc_subset_Icc le_rfl ht.2
  obtain ⟨γ, -, hrange⟩ :=
    LQGMetric.MetricGeometry.exists_path_of_curve ht.1 (hR.mono hsub)
  have hsource : R 0 ∈ interior K₀ := hAK (hR0 ▸ hx)
  obtain ⟨s, hs⟩ :=
    LQGMetric.MetricGeometry.exists_mem_frontier_of_path isOpen_interior
      γ hsource hout
  obtain ⟨q, hq, hγq⟩ := hrange ⟨s, rfl⟩
  have hqT : q ∈ Icc (0 : ℝ) T := hsub hq
  have hbd : R q ∈ frontier K₀ :=
    frontier_interior_subset (hγq ▸ hs)
  have hlower : δ ≤ D (x, R q) := hmargin x hx (R q) hbd
  have htime : D (x, R q) = ENNReal.ofReal q := by
    have ht' : D (R 0, R q) = ENNReal.ofReal (q - 0) :=
      hgeo.edist_eq_of_hasUnitSpeedOn hunit
        ⟨le_rfl, hqT.1.trans hqT.2⟩ hqT hq.1
    simpa only [hR0, sub_zero] using ht'
  have hqle : D (x, R q) ≤ D (x, y) := by
    rw [htime, ← ENNReal.ofReal_toReal hfin.ne, ← hT]
    exact ENNReal.ofReal_le_ofReal hqT.2
  exact (not_lt_of_ge hlower) (hqle.trans_lt hshort)

/-- A finite ordered partition of a source curve whose consecutive vertices
are closer than any prescribed positive source distance. Its total chord
length is bounded by the curve length. -/
theorem short_partition_of_curve (D : LSCMetric) {P : ℝ → ℂ}
    {a b : ℝ} (hab : a < b) (hP : D.IsCurve P a b)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ n : ℕ, 0 < n ∧ ∃ t : ℕ → ℝ,
      Monotone t ∧ t 0 = a ∧ t n = b ∧
      (∀ i ≤ n, t i ∈ Icc a b) ∧
      (∀ i < n, D (P (t i), P (t (i + 1))) < δ) ∧
      (∑ i ∈ Finset.range n, D (P (t i), P (t (i + 1)))) ≤ D.len P a b := by
  have huc : UniformContinuousOn (D.pt ∘ P) (Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hP.2
  obtain ⟨ηE, hηE, hclose⟩ := EMetric.uniformContinuousOn_iff.mp huc δ hδ
  let ηf : ℝ≥0∞ := min ηE 1
  have hηfpos : 0 < ηf := lt_min hηE (by norm_num)
  have hηffin : ηf ≠ ∞ :=
    (lt_of_le_of_lt (min_le_right ηE 1) ENNReal.one_lt_top).ne
  let η : ℝ := ηf.toReal / 2
  have hηpos : 0 < η := half_pos (ENNReal.toReal_pos hηfpos.ne' hηffin)
  have hηsmall : ENNReal.ofReal η < ηE := by
    apply lt_of_lt_of_le _ (min_le_left ηE 1)
    apply (ENNReal.ofReal_lt_iff_lt_toReal hηpos.le hηffin).2
    dsimp [η]
    exact half_lt_self (ENNReal.toReal_pos hηfpos.ne' hηffin)
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / η)
  have hnpos : 0 < n := by
    have : 0 ≤ (b - a) / η := div_nonneg (sub_nonneg.mpr hab.le) hηpos.le
    exact Nat.pos_of_ne_zero (by intro h; subst n; norm_num at hn; linarith)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hstep : (b - a) / (n : ℝ) < η := by
    rw [div_lt_iff₀ hnreal]
    rw [div_lt_iff₀ hηpos] at hn
    linarith
  let t : ℕ → ℝ := fun i => min (a + (b - a) * (i : ℝ) / n) b
  have hmono : Monotone t := by
    intro i j hij
    dsimp [t]
    apply min_le_min_right
    gcongr
  have htmem (i : ℕ) : t i ∈ Icc a b := by
    refine ⟨?_, min_le_right _ _⟩
    dsimp [t]
    apply le_min
    · have : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
      have : 0 ≤ (b - a) * (i : ℝ) / n :=
        div_nonneg (mul_nonneg (sub_nonneg.mpr hab.le) this) hnreal.le
      linarith
    · exact hab.le
  have hti (i : ℕ) (hi : i ≤ n) : t i = a + (b - a) * (i : ℝ) / n := by
    dsimp [t]
    apply min_eq_left
    have hic : (i : ℝ) ≤ n := by exact_mod_cast hi
    have hm : (b - a) * (i : ℝ) / n ≤ b - a :=
      (div_le_iff₀ hnreal).2
        (mul_le_mul_of_nonneg_left hic (sub_nonneg.mpr hab.le))
    linarith
  have ht0 : t 0 = a := by simp [hti 0 (Nat.zero_le n)]
  have htn : t n = b := by
    rw [hti n le_rfl]
    field_simp
    ring
  have hshort (i : ℕ) (hi : i < n) :
      D (P (t i), P (t (i + 1))) < δ := by
    have hi' : i + 1 ≤ n := Nat.succ_le_iff.mpr hi
    have hdist : edist (t i) (t (i + 1)) < ENNReal.ofReal η := by
      rw [edist_dist]
      rw [ENNReal.ofReal_lt_ofReal_iff hηpos]
      rw [hti i hi.le, hti (i + 1) hi', Real.dist_eq]
      have heq : a + (b - a) * (i : ℝ) / n -
          (a + (b - a) * ((i + 1 : ℕ) : ℝ) / n) = -(b - a) / n := by
        push_cast
        ring
      rw [heq, neg_div, abs_neg, abs_of_nonneg
        (div_nonneg (sub_nonneg.mpr hab.le) hnreal.le)]
      exact hstep
    have hh := hclose (htmem i) (htmem (i + 1))
      (hdist.trans hηsmall)
    exact hh
  refine ⟨n, hnpos, t, hmono, ht0, htn, fun i _ => htmem i, hshort, ?_⟩
  have hsum := eVariationOn.sum_le (f := D.pt ∘ P) (s := Icc a b)
    (n := n) hmono (fun i => htmem i)
  change (∑ i ∈ Finset.range n, D (P (t (i + 1)), P (t i))) ≤
    D.len P a b at hsum
  calc
    (∑ i ∈ Finset.range n, D (P (t i), P (t (i + 1)))) =
        ∑ i ∈ Finset.range n, D (P (t (i + 1)), P (t i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact D.isExtMetric.2.2.1 _ _
    _ ≤ D.len P a b := hsum

/-- The elementary finite-chain triangle inequality for a raw cost `e`. -/
theorem raw_chain_triangle (e : ℂ × ℂ → ℝ≥0∞) (U : Set ℂ)
    (htri : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U,
      e (x, z) ≤ e (x, y) + e (y, z))
    (hdiag : ∀ x ∈ U, e (x, x) = 0)
    (v : ℕ → ℂ) (n : ℕ) (hv : ∀ i ≤ n, v i ∈ U) :
    e (v 0, v n) ≤ ∑ i ∈ Finset.range n, e (v i, v (i + 1)) := by
  induction n with
  | zero => simp [hdiag (v 0) (hv 0 le_rfl)]
  | succ n ih =>
      calc
        e (v 0, v (n + 1)) ≤ e (v 0, v n) + e (v n, v (n + 1)) :=
          htri _ (hv 0 (Nat.zero_le _)) _ (hv n (Nat.le_succ n))
            _ (hv (n + 1) le_rfl)
        _ ≤ (∑ i ∈ Finset.range n, e (v i, v (i + 1))) +
            e (v n, v (n + 1)) :=
              add_le_add (ih (fun i hi => hv i (hi.trans (Nat.le_succ n)))) le_rfl
        _ = ∑ i ∈ Finset.range (n + 1), e (v i, v (i + 1)) := by
          rw [Finset.sum_range_succ]

/-- Proposition 6.1 for one finite source curve in the open domain. -/
theorem finite_curve_bound_of_goodCover
    (D : LSCMetric) (e : ℂ × ℂ → ℝ≥0∞) (U : Set ℂ)
    (hU : IsOpen U)
    (hB : BiLipschitz.Barrier.Barrier D) (hL : D.IsLengthSpace)
    (ξ Q : ℝ) (q : Ioo (0 : ℝ) (1 / 100))
    (α : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ))
    (θ : Ioi (0 : ℝ)) (k η C : ℝ)
    (hη : 0 ≤ η) (hC : 1 + η ≤ C)
    (m : ℕ) (hdyad : (q : ℝ) = (1 / 2 : ℝ) ^ m)
    (exhaustion : ℕ → Set ℂ) (ε : ℕ → ℝ)
    (hcofinal : ∀ A : Set ℂ, IsCompact A → A ⊆ U →
      ∃ N, A ⊆ exhaustion N)
    (hgood : GoodCover D e ξ Q q α K θ k η exhaustion ε)
    (htri : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U,
      e (x, z) ≤ e (x, y) + e (y, z))
    (hcmp : ∀ x y : U,
      e (x, y) ≤ ENNReal.ofReal C * D.internal U (x, y))
    {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b)
    (htrace : ∀ t ∈ Icc a b, P t ∈ U)
    (hlen : D.len P a b < ∞) :
    e (P a, P b) ≤ ENNReal.ofReal (newConstant C η K) * D.len P a b := by
  have hdiag : ∀ x ∈ U, e (x, x) = 0 := by
    intro x hx
    have := hcmp ⟨x, hx⟩ ⟨x, hx⟩
    have hle : e (x, x) ≤ 0 := by
      simpa only [internal_self_eq_zero, mul_zero] using this
    exact le_antisymm hle bot_le
  have hN0 : 0 ≤ newConstant C η K :=
    (le_trans (by norm_num : (0 : ℝ) ≤ 1)
      (newConstant_ge (le_trans (by norm_num : (0 : ℝ) ≤ 1) K.2.le)
        hη hC))
  rcases lt_or_eq_of_le hP.1 with hab | hab
  · have hEuclid : ContinuousOn P (Icc a b) :=
      BiLipschitz.Barrier.continuousOn_of_barrier_of_length D hB hL hP
    let A : Set ℂ := P '' Icc a b
    have hA : IsCompact A := isCompact_Icc.image_of_continuousOn hEuclid
    have hAU : A ⊆ U := by
      rintro x ⟨t, ht, rfl⟩
      exact htrace t ht
    have hAne : A.Nonempty := ⟨P a, ⟨a, ⟨le_rfl, hab.le⟩, rfl⟩⟩
    obtain ⟨K₀, hK₀, hAK, hKU⟩ := compact_buffer_of_trace hA hU hAU
    obtain ⟨δ, hδ, hmargin⟩ := compact_buffer_margin D hA hAne hK₀ hAK
    obtain ⟨n, hn, t, hmono, ht0, htn, htmem, hshort, hsum⟩ :=
      short_partition_of_curve D hab hP hδ
    have hstep : ∀ i < n,
        e (P (t i), P (t (i + 1))) ≤
          ENNReal.ofReal (newConstant C η K) *
            D (P (t i), P (t (i + 1))) := by
      intro i hi
      have hi' : i + 1 ≤ n := Nat.succ_le_iff.mpr hi
      have hxi : P (t i) ∈ A := ⟨t i, htmem i hi.le, rfl⟩
      by_cases heq : P (t i) = P (t (i + 1))
      · simp [heq, hdiag _ (hAU ⟨t (i + 1), htmem (i + 1) hi', rfl⟩)]
      · have hfinpair : D (P (t i), P (t (i + 1))) < ∞ :=
          (hshort i hi).trans_le le_top
        obtain ⟨R, hR, hgeo, hunit, hR0, hRT⟩ :=
          S36.exists_unit_geodesic D hB hL hfinpair
        let T := (D (P (t i), P (t (i + 1)))).toReal
        have hRin : ∀ s ∈ Icc (0 : ℝ) T, R s ∈ interior K₀ :=
          short_geodesic_stays_in_buffer D hK₀ hAK hxi hmargin
            (hshort i hi) hfinpair rfl hR hgeo hunit hR0
        have hRU : ∀ s ∈ Icc (0 : ℝ) T, R s ∈ U :=
          fun s hs => hKU (interior_subset (hRin s hs))
        have hRcompact : IsCompact (R '' Icc (0 : ℝ) T) :=
          isCompact_Icc.image_of_continuousOn hR
        obtain ⟨N, hN⟩ := hcofinal _ hRcompact (by
          rintro x ⟨s, hs, rfl⟩
          exact hRU s hs)
        have hRN : ∀ s ∈ Icc (0 : ℝ) T, R s ∈ exhaustion N :=
          fun s hs => hN ⟨s, hs, rfl⟩
        have hDpos : 0 < D (P (t i), P (t (i + 1))) := by
          apply pos_iff_ne_zero.mpr
          intro hz
          exact heq (D.isExtMetric.2.1 _ _ hz)
        have hTpos : 0 < T := ENNReal.toReal_pos hDpos.ne' hfinpair.ne
        have hb := geodesic_bound_of_goodCover D e U ξ Q q α K θ k η C
          hη hC m hdyad exhaustion ε hgood N hRN hR hgeo hunit
          hR0 hRT hTpos heq hRU htri hcmp
        calc
          e (P (t i), P (t (i + 1))) ≤
              ENNReal.ofReal (newConstant C η K * T) := hb
          _ = ENNReal.ofReal (newConstant C η K) *
              D (P (t i), P (t (i + 1))) := by
            rw [ENNReal.ofReal_mul hN0, ENNReal.ofReal_toReal hfinpair.ne]
    have hv : ∀ i ≤ n, P (t i) ∈ U :=
      fun i hi => htrace (t i) (htmem i hi)
    have hchain := raw_chain_triangle e U htri hdiag (P ∘ t) n hv
    calc
      e (P a, P b) = e (P (t 0), P (t n)) := by rw [ht0, htn]
      _ ≤ ∑ i ∈ Finset.range n, e (P (t i), P (t (i + 1))) := hchain
      _ ≤ ∑ i ∈ Finset.range n,
          ENNReal.ofReal (newConstant C η K) *
            D (P (t i), P (t (i + 1))) := by
              apply Finset.sum_le_sum
              intro i hi
              exact hstep i (Finset.mem_range.mp hi)
      _ = ENNReal.ofReal (newConstant C η K) *
          (∑ i ∈ Finset.range n, D (P (t i), P (t (i + 1)))) := by
            rw [Finset.mul_sum]
      _ ≤ ENNReal.ofReal (newConstant C η K) * D.len P a b :=
        by simpa only [mul_comm] using
          (mul_le_mul_left hsum (ENNReal.ofReal (newConstant C η K)))
  · subst b
    simpa [hdiag (P a) (htrace a ⟨le_rfl, le_rfl⟩)]

/-- Proposition 6.1's deterministic all-pairs improvement, with the source
domain metric defined by paths contained in U. -/
theorem all_pairs_bound_of_goodCover
    (D : LSCMetric) (e : ℂ × ℂ → ℝ≥0∞) (U : Set ℂ)
    (hU : IsOpen U)
    (hB : BiLipschitz.Barrier.Barrier D) (hL : D.IsLengthSpace)
    (ξ Q : ℝ) (q : Ioo (0 : ℝ) (1 / 100))
    (α : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ))
    (θ : Ioi (0 : ℝ)) (k η C : ℝ)
    (hη : 0 ≤ η) (hC : 1 + η ≤ C)
    (m : ℕ) (hdyad : (q : ℝ) = (1 / 2 : ℝ) ^ m)
    (exhaustion : ℕ → Set ℂ) (ε : ℕ → ℝ)
    (hcofinal : ∀ A : Set ℂ, IsCompact A → A ⊆ U →
      ∃ N, A ⊆ exhaustion N)
    (hgood : GoodCover D e ξ Q q α K θ k η exhaustion ε)
    (htri : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U,
      e (x, z) ≤ e (x, y) + e (y, z))
    (hcmp : ∀ x y : U,
      e (x, y) ≤ ENNReal.ofReal C * D.internal U (x, y)) :
    ∀ x y : U,
      e (x, y) ≤
        ENNReal.ofReal (newConstant C η K) * D.internal U (x, y) := by
  intro x y
  have hc0 : ENNReal.ofReal (newConstant C η K) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
        (newConstant_ge (le_trans (by norm_num : (0 : ℝ) ≤ 1) K.2.le)
          hη hC))).ne'
  have hct : ENNReal.ofReal (newConstant C η K) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  unfold LSCMetric.internal
  simp only [ENNReal.mul_iInf_of_ne hc0 hct]
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b =>
    le_iInf fun hP => le_iInf fun htrace =>
      le_iInf fun ha => le_iInf fun hb => ?_
  by_cases hlen : D.len P a b < ⊤
  · have h := finite_curve_bound_of_goodCover D e U hU hB hL
      ξ Q q α K θ k η C hη hC m hdyad exhaustion ε hcofinal hgood
      htri hcmp hP htrace hlen
    simpa only [ha, hb] using h
  · have htop : D.len P a b = ⊤ := top_le_iff.mp (le_of_not_gt hlen)
    simp [htop, hc0]

section OptimalConstant
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (U : Set ℂ) (D : Ω → LSCMetric)
    (e : Ω → ℂ × ℂ → ℝ≥0∞)

/-- The admissible constants in the printed infimum, with `a.s.` read as
`∀ᵐ`; the all-pairs event need not be measurable. -/
def Admissible (c : ℝ) : Prop :=
  1 ≤ c ∧ ∀ᵐ ω ∂P, ∀ u v : U,
    e ω (u, v) ≤ ENNReal.ofReal c * (D ω).internal U (u, v)

def optimalConstant : ℝ :=
  sInf {c : ℝ | Admissible P U D e c}

theorem admissible_mono {c c' : ℝ} (h : Admissible P U D e c)
    (hcc' : c ≤ c') : Admissible P U D e c' := by
  refine ⟨h.1.trans hcc', ?_⟩
  filter_upwards [h.2] with ω hω
  intro u v
  exact (hω u v).trans
    (by simpa only [mul_comm] using
      (mul_le_mul_right (ENNReal.ofReal_le_ofReal hcc')
        ((D ω).internal U (u, v))))

theorem optimal_lower (hNonempty : ∃ C, Admissible P U D e C) :
    1 ≤ optimalConstant P U D e := by
  apply le_csInf
  · exact ⟨hNonempty.choose, hNonempty.choose_spec⟩
  · intro c hc
    exact hc.1

theorem optimal_le_of_admissible {C : ℝ}
    (hC : Admissible P U D e C) : optimalConstant P U D e ≤ C := by
  apply csInf_le
  · exact ⟨(1 : ℝ), fun c hc => hc.1⟩
  · exact hC

theorem admissible_above (hNonempty : ∃ C, Admissible P U D e C)
    {c : ℝ} (hc : optimalConstant P U D e < c) :
    Admissible P U D e c := by
  obtain ⟨b, hb, hbc⟩ :=
    exists_lt_of_csInf_lt
      (s := {c : ℝ | Admissible P U D e c})
      ⟨hNonempty.choose, hNonempty.choose_spec⟩ hc
  exact admissible_mono P U D e hb hbc.le

/-- Countable intersection of bounds just above the infimum, then a closed
order limit. This does not assume measurability of the all-pairs event. -/
theorem optimal_attained (hNonempty : ∃ C, Admissible P U D e C) :
    Admissible P U D e (optimalConstant P U D e) := by
  have hlow := optimal_lower P U D e hNonempty
  have hn (n : ℕ) : Admissible P U D e
      (optimalConstant P U D e + 1 / ((n : ℝ) + 1)) := by
    apply admissible_above P U D e hNonempty
    have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hae : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ u v : U,
      e ω (u, v) ≤
        ENNReal.ofReal (optimalConstant P U D e + 1 / ((n : ℝ) + 1)) *
          (D ω).internal U (u, v) := ae_all_iff.mpr (fun n => (hn n).2)
  refine ⟨hlow, ?_⟩
  filter_upwards [hae] with ω hω
  intro u v
  by_cases htop : (D ω).internal U (u, v) = ∞
  · have hpos : ENNReal.ofReal (optimalConstant P U D e) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (by linarith)).ne'
    simp [htop, hpos]
  · have hc : Tendsto
        (fun n : ℕ => optimalConstant P U D e + 1 / ((n : ℝ) + 1))
        atTop (nhds (optimalConstant P U D e)) := by
        simpa only [add_zero] using
          (tendsto_const_nhds (x := optimalConstant P U D e)).add
            (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hmul : Tendsto
        (fun n : ℕ =>
          ENNReal.ofReal (optimalConstant P U D e + 1 / ((n : ℝ) + 1)) *
          (D ω).internal U (u, v)) atTop
        (nhds (ENNReal.ofReal (optimalConstant P U D e) *
          (D ω).internal U (u, v))) :=
      (ENNReal.continuousAt_mul_const
        (a := (D ω).internal U (u, v)) (Or.inl htop)).tendsto.comp
        (ENNReal.tendsto_ofReal hc)
    exact ge_of_tendsto hmul (Filter.Eventually.of_forall fun n => hω n u v)

/-- Final order contradiction once the source geometric improvement has
actually been proved for the given samplewise good-cover event. -/
theorem optimal_improvement_contradiction
    (η A : ℝ) (hη : 0 ≤ η) (hA : 0 ≤ A)
    (hgap : 1 + η < optimalConstant P U D e)
    (hImproved : ∀ᵐ ω ∂P, ∀ u v : U,
      e ω (u, v) ≤
        ENNReal.ofReal (newConstant (optimalConstant P U D e) η A) *
          (D ω).internal U (u, v)) : False := by
  have hAdm : Admissible P U D e
      (newConstant (optimalConstant P U D e) η A) :=
    ⟨newConstant_ge hA hη hgap.le, hImproved⟩
  have hle := optimal_le_of_admissible P U D e hAdm
  exact (not_le_of_gt (newConstant_lt hA hgap)) hle

/-- Proposition 6.1: the deterministic improvement and countable
optimal-constant argument, with every comparison in the source domain
internal metric. The cover parameters and exhaustion are fixed before η. -/
theorem almost_everywhere_internal_bound
    (hU : IsOpen U)
    (ξ Q : ℝ) (q : Ioo (0 : ℝ) (1 / 100))
    (α : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ))
    (θ : Ioi (0 : ℝ)) (k : ℝ)
    (m : ℕ) (hdyad : (q : ℝ) = (1 / 2 : ℝ) ^ m)
    (exhaustion : ℕ → Set ℂ) (ε : ℕ → ℝ)
    (hcofinal : ∀ A : Set ℂ, IsCompact A → A ⊆ U →
      ∃ N, A ⊆ exhaustion N)
    (hInitial : ∃ C, Admissible P U D e C)
    (hSample : ∀ᵐ ω ∂P,
      BiLipschitz.Barrier.Barrier (D ω) ∧
      (D ω).IsLengthSpace ∧
      (∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U,
        e ω (x, z) ≤ e ω (x, y) + e ω (y, z)))
    (hCover : ∀ η : ℝ,
      0 < η → η < optimalConstant P U D e - 1 →
      ∀ᵐ ω ∂P, GoodCover (D ω) (e ω) ξ Q q α K θ k η exhaustion ε) :
    ∀ᵐ ω ∂P, ∀ x y : U,
      e ω (x, y) ≤ (D ω).internal U (x, y) := by
  have hAtt := optimal_attained P U D e hInitial
  have hOpt : optimalConstant P U D e = 1 := by
    have hlow := optimal_lower P U D e hInitial
    by_contra hne
    have hgt : 1 < optimalConstant P U D e :=
      lt_of_le_of_ne hlow (Ne.symm hne)
    let η : ℝ := (optimalConstant P U D e - 1) / 2
    have hη : 0 < η := by dsimp [η]; linarith
    have hηmax : η < optimalConstant P U D e - 1 := by
      dsimp [η]
      linarith
    have hgap : 1 + η < optimalConstant P U D e := by linarith
    have hImproved : ∀ᵐ ω ∂P, ∀ x y : U,
        e ω (x, y) ≤
          ENNReal.ofReal
            (newConstant (optimalConstant P U D e) η K) *
              (D ω).internal U (x, y) := by
      filter_upwards [hSample, hAtt.2, hCover η hη hηmax] with
        ω hs hc hg
      exact all_pairs_bound_of_goodCover (D ω) (e ω) U hU
        hs.1 hs.2.1 ξ Q q α K θ k η
        (optimalConstant P U D e) hη.le hgap.le
        m hdyad exhaustion ε hcofinal hg hs.2.2 hc
    exact optimal_improvement_contradiction P U D e η K hη.le
      (le_trans (by norm_num : (0 : ℝ) ≤ 1) K.2.le)
      hgap hImproved
  filter_upwards [hAtt.2] with ω hω
  intro x y
  simpa only [hOpt, ENNReal.ofReal_one, one_mul] using hω x y

end OptimalConstant

end SupercriticalConformalCovariance.Improve
