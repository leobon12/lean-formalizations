import HigherDimLQGMetric.Weak.DetWeylCont
import LQGMetric.Metric.InternalLimit

/-!
# Local internal metrics under locally uniform limits

The first deterministic step in the internal metric tightness argument of MA5 A10.
On a fixed small ball around a point of an open domain, the approximating
internal metric eventually agrees with the global metric, uniformly in pairs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- A positive metric distance from a point to a Euclidean sphere. -/
theorem ContMetric.exists_sphere_gap_at (D : ContMetric d) (x : Rd d) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ c : ℝ, 0 < c ∧ ∀ w ∈ Metric.sphere x ρ, c ≤ D.1 (x,w) := by
  by_cases hne : (Metric.sphere x ρ).Nonempty
  · obtain ⟨w, hw, hmin⟩ := (isCompact_sphere x ρ).exists_isMinOn hne
      (D.1.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
    refine ⟨D.1 (x,w), D.apply_pos ?_, fun y hy => hmin hy⟩
    intro h
    rw [Metric.mem_sphere] at hw
    rw [← h, dist_self] at hw
    linarith
  · exact ⟨1, one_pos, fun w hw => (hne ⟨w,hw⟩).elim⟩

/-- On a small ball compactly inside `U`, internal distances of `Dn` equal global distances
eventually, uniformly in the endpoints. This is the local confinement step of MA5 A10. -/
theorem eventually_internal_eq_on_small_ball
    (Dn : ℕ → ContMetric d) (D : ContMetric d)
    (hDn : ∀ n, (Dn n).IsLength)
    (hconv : ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(Dn n).1) ⇑D.1 atTop
      (Metric.closedBall (0 : Rd d) R ×ˢ Metric.closedBall (0 : Rd d) R))
    {U : Set (Rd d)} (hU : IsOpen U) {x : Rd d} (hx : x ∈ U) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall x r ⊆ U ∧
      ∀ᶠ n : ℕ in atTop, ∀ u ∈ Metric.ball x r, ∀ v ∈ Metric.ball x r,
        (Dn n).internal U u v = ENNReal.ofReal ((Dn n).1 (u,v)) := by
  obtain ⟨ρ₀, hρ₀, hρ₀U⟩ := Metric.isOpen_iff.mp hU x hx
  let ρ : ℝ := ρ₀ / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hballU : Metric.ball x ρ ⊆ U :=
    (Metric.ball_subset_ball (by dsimp [ρ]; linarith)).trans hρ₀U
  obtain ⟨c, hc, hgap⟩ := D.exists_sphere_gap_at x hρ
  obtain ⟨r₀, hr₀, hsmall⟩ := Metric.continuous_iff.mp D.continuous_pt x (c / 8)
    (by positivity)
  let r : ℝ := min (r₀ / 2) (ρ / 4)
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrρ : r < ρ := by
    have := min_le_right (r₀ / 2) (ρ / 4)
    dsimp [r]
    linarith
  have hclosedU : Metric.closedBall x r ⊆ U :=
    (Metric.closedBall_subset_ball hrρ).trans hballU
  refine ⟨r, hr, hclosedU, ?_⟩
  let S : ℝ := ‖x‖ + ρ + 1
  have hS : 0 < S := by dsimp [S]; positivity
  have hK : Metric.closedBall x ρ ⊆ Metric.closedBall (0 : Rd d) S := by
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right]
    have hnorm := norm_add_le (y - x) x
    have heq : y - x + x = y := by abel
    rw [heq] at hnorm
    have hxy : ‖y - x‖ ≤ ρ := by simpa [dist_eq_norm, norm_sub_rev] using hy
    dsimp [S]
    linarith
  -- A single index threshold works for every pair and every point on the sphere.
  filter_upwards [eventually_dist_lt_on_closedBall
    (fun n => (Dn n).1) D.1 hconv S (c / 8) hS (by positivity)] with n hn u hu v hv
  have huρ : u ∈ Metric.ball x ρ := Metric.ball_subset_ball hrρ.le hu
  have hvρ : v ∈ Metric.ball x ρ := Metric.ball_subset_ball hrρ.le hv
  have huK : u ∈ Metric.closedBall x ρ := Metric.ball_subset_closedBall huρ
  have hvK : v ∈ Metric.closedBall x ρ := Metric.ball_subset_closedBall hvρ
  have hux : D.1 (x,u) < c / 8 := by
    have hru : dist u x < r := hu
    have hr₀' : r ≤ r₀ / 2 := min_le_left _ _
    dsimp [r] at hr₀'
    simpa only [D.dist_pt, D.apply_comm u x] using hsmall u (by linarith)
  have hvx : D.1 (x,v) < c / 8 := by
    have hrv : dist v x < r := hv
    have hr₀' : r ≤ r₀ / 2 := min_le_left _ _
    dsimp [r] at hr₀'
    simpa only [D.dist_pt, D.apply_comm v x] using hsmall v (by linarith)
  have huv : (Dn n).1 (u,v) < c / 2 := by
    have htri := D.2.triangle u x v
    have hsym := D.2.symm u x
    have hconvuv := abs_lt.mp (hn u (hK huK) v (hK hvK))
    linarith
  have hbar : ∀ w ∈ Metric.sphere x ρ, c / 2 ≤ (Dn n).1 (u,w) := by
    intro w hw
    have hwK : w ∈ Metric.closedBall x ρ := Metric.sphere_subset_closedBall hw
    have htri := D.2.triangle x u w
    have hconvuw := abs_lt.mp (hn u (hK huK) w (hK hwK))
    linarith [hgap w hw]
  have hInf : ENNReal.ofReal (c / 2) ≤
      Metric.infEDist ((Dn n).pt u) ((Dn n).pt '' frontier (Metric.ball x ρ)) := by
    refine le_infEDist.2 ?_
    rintro _ ⟨w, hw, rfl⟩
    rw [(Dn n).edist_pt]
    exact ENNReal.ofReal_le_ofReal (hbar w (Metric.frontier_ball_subset_sphere hw))
  have hlt : edist ((Dn n).pt u) ((Dn n).pt v) <
      Metric.infEDist ((Dn n).pt u) ((Dn n).pt '' frontier (Metric.ball x ρ)) := by
    rw [(Dn n).edist_pt]
    exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg ((Dn n).nonneg u v)).2 huv).trans_le hInf
  have hlocal := ContMetric.internal_eq_of_lt_infEDist_frontier (hDn n)
    Metric.isOpen_ball huρ hlt
  apply le_antisymm
  · calc (Dn n).internal U u v ≤ (Dn n).internal (Metric.ball x ρ) u v :=
        (Dn n).internal_anti hballU _ _
      _ = ENNReal.ofReal ((Dn n).1 (u,v)) := by rw [hlocal.2, (Dn n).edist_pt]
  · exact (Dn n).ofReal_le_internal U u v

/-- Local equality of two continuous metrics gives equality of their internal metrics. -/
theorem internal_eq_of_locally_eq (D E : ContMetric d) {U : Set (Rd d)}
    (hloc : ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ ∀ u ∈ Metric.ball x r,
      ∀ v ∈ Metric.ball x r, D.1 (u,v) = E.1 (u,v))
    {u v : Rd d} (hu : u ∈ U) (hv : v ∈ U) :
    D.internal U u v = E.internal U u v := by
  let Y₁ : Set D.Space := D.pt '' U
  let Y₂ : Set E.Space := E.pt '' U
  have hY₂ (z : Y₁) : E.pt (D.unpt z.1) ∈ Y₂ := by
    obtain ⟨x,hx,hx'⟩ := z.2
    exact ⟨x,hx, by rw [← hx']; rfl⟩
  have hY₁ (z : Y₂) : D.pt (E.unpt z.1) ∈ Y₁ := by
    obtain ⟨x,hx,hx'⟩ := z.2
    exact ⟨x,hx, by rw [← hx']; rfl⟩
  let e : Y₁ ≃ₜ Y₂ :=
    { toFun := fun z => ⟨E.pt (D.unpt z.1), hY₂ z⟩
      invFun := fun z => ⟨D.pt (E.unpt z.1), hY₁ z⟩
      left_inv := fun z => Subtype.ext (by simp)
      right_inv := fun z => Subtype.ext (by simp)
      continuous_toFun :=
        ((E.continuous_pt.comp (D.continuous_unpt.comp continuous_subtype_val)).subtype_mk hY₂)
      continuous_invFun :=
        ((D.continuous_pt.comp (E.continuous_unpt.comp continuous_subtype_val)).subtype_mk hY₁) }
  have he : LQGMetric.MetricGeometry.IsLocalIsometryOn e := by
    intro z
    have hz : D.unpt z.1 ∈ U := by
      obtain ⟨x,hx,hx'⟩ := z.2
      simpa [← hx'] using hx
    obtain ⟨r,hr,hEq⟩ := hloc _ hz
    refine ⟨{q : Y₁ | D.unpt q.1 ∈ Metric.ball (D.unpt z.1) r},
      (D.continuous_unpt.comp continuous_subtype_val).continuousAt.preimage_mem_nhds
        (Metric.ball_mem_nhds _ hr), ?_⟩
    intro a ha b hb
    rw [edist_dist, edist_dist]
    congr 1
    exact (hEq _ ha _ hb).symm
  have h := LQGMetric.MetricGeometry.internalEDist_eq_of_isLocalIsometryOn he
    (⟨D.pt u, ⟨u,hu,rfl⟩⟩ : Y₁) (⟨D.pt v, ⟨v,hv,rfl⟩⟩ : Y₁)
  change E.internal U u v = D.internal U u v at h
  exact h.symm

/-- Lemma 3.5 for a continuous metric `E` on the ambient space: a pointwise limit of
internal metrics has the same internal metric as the limit of the global metrics. -/
theorem internal_eq_of_tendsto_internal
    (Dn : ℕ → ContMetric d) (D E : ContMetric d)
    (hDn : ∀ n, (Dn n).IsLength)
    (hconv : ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(Dn n).1) ⇑D.1 atTop
      (Metric.closedBall (0 : Rd d) R ×ˢ Metric.closedBall (0 : Rd d) R))
    {U : Set (Rd d)} (hU : IsOpen U)
    (hE : ∀ u ∈ U, ∀ v ∈ U,
      Tendsto (fun n => ((Dn n).internal U u v).toReal) atTop (𝓝 (E.1 (u,v))))
    {u v : Rd d} (hu : u ∈ U) (hv : v ∈ U) :
    D.internal U u v = E.internal U u v := by
  apply internal_eq_of_locally_eq D E ?_ hu hv
  intro x hx
  obtain ⟨r, hr, hball, hevent⟩ := eventually_internal_eq_on_small_ball Dn D hDn hconv hU hx
  refine ⟨r, hr, fun a ha b hb => ?_⟩
  have haU : a ∈ U := hball (Metric.ball_subset_closedBall ha)
  have hbU : b ∈ U := hball (Metric.ball_subset_closedBall hb)
  let S : ℝ := ‖a‖ + ‖b‖ + 1
  have hS : 0 < S := by dsimp [S]; positivity
  have haS : a ∈ Metric.closedBall (0 : Rd d) S := by
    rw [Metric.mem_closedBall, dist_zero_right]
    dsimp [S]; linarith [norm_nonneg b]
  have hbS : b ∈ Metric.closedBall (0 : Rd d) S := by
    rw [Metric.mem_closedBall, dist_zero_right]
    dsimp [S]; linarith [norm_nonneg a]
  have hDab : Tendsto (fun n => (Dn n).1 (a,b)) atTop (𝓝 (D.1 (a,b))) :=
    (hconv S hS).tendsto_at ⟨haS,hbS⟩
  have heq : (fun n => ((Dn n).internal U a b).toReal) =ᶠ[atTop]
      (fun n => (Dn n).1 (a,b)) := by
    filter_upwards [hevent] with n hn
    rw [hn a ha b hb, ENNReal.toReal_ofReal ((Dn n).nonneg a b)]
  have hlim : Tendsto (fun n => ((Dn n).internal U a b).toReal) atTop
      (𝓝 (D.1 (a,b))) := hDab.congr' heq.symm
  exact tendsto_nhds_unique hlim (hE a haU b hbU)

/-- Internal distances between any two points of a connected open domain are eventually
bounded along a locally uniformly convergent sequence of length metrics. -/
theorem eventually_internal_bounded_of_isPreconnected
    (Dn : ℕ → ContMetric d) (D : ContMetric d)
    (hDn : ∀ n, (Dn n).IsLength)
    (hconv : ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(Dn n).1) ⇑D.1 atTop
      (Metric.closedBall (0 : Rd d) R ×ˢ Metric.closedBall (0 : Rd d) R))
    {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U)
    {u v : Rd d} (hu : u ∈ U) (hv : v ∈ U) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n : ℕ in atTop,
      (Dn n).internal U u v ≤ ENNReal.ofReal B := by
  let P : Rd d → Rd d → Prop := fun a b =>
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n : ℕ in atTop,
      (Dn n).internal U a b ≤ ENNReal.ofReal B
  have hlocal : ∀ a ∈ U, ∀ᶠ b in 𝓝[U] a, P a b := by
    intro a ha
    obtain ⟨r, hr, hball, hevent⟩ := eventually_internal_eq_on_small_ball Dn D hDn hconv hU ha
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Metric.ball_mem_nhds a hr)] with b hb
    let S : ℝ := ‖a‖ + ‖b‖ + 1
    have hS : 0 < S := by dsimp [S]; positivity
    have haS : a ∈ Metric.closedBall (0 : Rd d) S := by
      rw [Metric.mem_closedBall, dist_zero_right]
      dsimp [S]; linarith [norm_nonneg b]
    have hbS : b ∈ Metric.closedBall (0 : Rd d) S := by
      rw [Metric.mem_closedBall, dist_zero_right]
      dsimp [S]; linarith [norm_nonneg a]
    refine ⟨D.1 (a,b) + 1, by linarith [D.nonneg a b], ?_⟩
    filter_upwards [hevent, eventually_dist_lt_on_closedBall
      (fun n => (Dn n).1) D.1 hconv S 1 hS one_pos] with n hn hclose
    rw [hn a (Metric.mem_ball_self hr) b hb]
    exact ENNReal.ofReal_le_ofReal (by
      have hab := abs_lt.mp (hclose a haS b hbS)
      linarith)
  have htrans : ∀ a b c, a ∈ U → b ∈ U → c ∈ U → P a b → P b c → P a c := by
    intro a b c _ _ _ ⟨B₁,hB₁,h₁⟩ ⟨B₂,hB₂,h₂⟩
    refine ⟨B₁+B₂, add_nonneg hB₁ hB₂, ?_⟩
    filter_upwards [h₁,h₂] with n h₁' h₂'
    calc (Dn n).internal U a c
        ≤ (Dn n).internal U a b + (Dn n).internal U b c := (Dn n).internal_triangle U a b c
      _ ≤ ENNReal.ofReal B₁ + ENNReal.ofReal B₂ := add_le_add h₁' h₂'
      _ = ENNReal.ofReal (B₁+B₂) := (ENNReal.ofReal_add hB₁ hB₂).symm
  have hsymm : ∀ a b, a ∈ U → b ∈ U → P a b → P b a := by
    intro a b _ _ ⟨B,hB,h⟩
    refine ⟨B,hB, ?_⟩
    filter_upwards [h] with n hn
    rwa [(Dn n).internal_comm]
  exact hUc.induction₂ P hlocal htrans hsymm hu hv

end HigherDimLQGMetric
