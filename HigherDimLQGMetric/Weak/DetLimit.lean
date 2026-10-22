import HigherDimLQGMetric.Weak.DetDefs
import LQGMetric.Metric.Midpoint

/-!
# Deterministic length-metric limits

MA5 DL1. Approximate midpoints of the approximants are confined to one
Euclidean compact ball by the properness-at-infinity gap of the limit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry (IsLengthSpace)

variable {d : ℕ}

/-- A short connection to a point outside a Euclidean ball has a point on its sphere. -/
theorem ContMetric.exists_sphere_le_of_outside (D : ContMetric d) (hD : D.IsLength)
    {x z : Rd d} {R ε : ℝ} (hx : x ∈ Metric.ball (0 : Rd d) R)
    (hz : z ∉ Metric.ball (0 : Rd d) R) (hε : 0 < ε) :
    ∃ u ∈ Metric.sphere (0 : Rd d) R, D.1 (x, u) ≤ D.1 (x, z) + ε := by
  obtain ⟨γ, hlen⟩ := hD (D.pt x) (D.pt z) ε hε
  let Q : Path x z := γ.map D.continuous_unpt
  obtain ⟨t, ht⟩ := LQGMetric.MetricGeometry.exists_mem_frontier_of_path
    Metric.isOpen_ball Q hx hz
  set u : Rd d := Q t
  have hu : u ∈ Metric.sphere (0 : Rd d) R :=
    Metric.frontier_ball_subset_sphere ht
  refine ⟨u, hu, ?_⟩
  have hcost := (LQGMetric.MetricGeometry.edist_le_pathLength_apply γ t).trans hlen
  have hγu : γ t = D.pt u := by
    change γ t = D.pt (D.unpt (γ t))
    exact (D.pt_unpt _).symm
  rw [hγu, D.edist_pt, D.edist_pt] at hcost
  have hcost' : ENNReal.ofReal (D.1 (x, u)) ≤
      ENNReal.ofReal (D.1 (x, z)) + ENNReal.ofReal ε := by
    exact hcost
  rw [← ENNReal.ofReal_add (D.nonneg x z) hε.le] at hcost'
  exact (ENNReal.ofReal_le_ofReal_iff
    (add_nonneg (D.nonneg x z) hε.le)).1 hcost'

/-- The working form of locally uniform convergence on a Euclidean compact square. -/
theorem eventually_dist_lt_on_closedBall
    (Dn : ℕ → C(Rd d × Rd d, ℝ)) (D : C(Rd d × Rd d, ℝ))
    (hconv : ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(Dn n)) ⇑D atTop
      (Metric.closedBall (0 : Rd d) R ×ˢ Metric.closedBall (0 : Rd d) R))
    (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ x ∈ Metric.closedBall (0 : Rd d) R,
      ∀ y ∈ Metric.closedBall (0 : Rd d) R,
        |Dn n (x, y) - D (x, y)| < ε := by
  have h := (Metric.tendstoUniformlyOn_iff).1 (hconv R hR) ε hε
  filter_upwards [h] with n hn x hx y hy
  have hn' := hn (x, y) ⟨hx, hy⟩
  simpa [Real.dist_eq, abs_sub_comm] using hn'

/-- The infimum formulation of properness gives a uniform sphere barrier. -/
theorem IsProperFn.exists_sphere_barrier
    (D : ContMetric d) (hproper : IsProperFn D.1) {r : ℝ} (hr : 0 < r)
    (M : ℝ) : ∃ R : ℝ, r < R ∧ ∀ x ∈ Metric.closedBall (0 : Rd d) r,
      ∀ u ∈ Metric.sphere (0 : Rd d) R, M ≤ D.1 (x, u) := by
  obtain ⟨R, hrR, hM⟩ := hproper r hr M
  refine ⟨R, hrR, fun x hx u hu => ?_⟩
  have hle : ENNReal.ofReal M ≤ ENNReal.ofReal (D.1 (x, u)) := by
    exact hM.trans (iInf_le_of_le x (iInf_le_of_le hx
      (iInf_le_of_le u (iInf_le_of_le hu le_rfl))))
  exact (ENNReal.ofReal_le_ofReal_iff (D.nonneg x u)).1 hle

/-- Sphere barriers persist outside the sphere for local limits of length metrics. -/
theorem exists_outside_barrier_of_length_limit
    (Dn : ℕ → ContMetric d) (D : ContMetric d)
    (hDn : ∀ n, (Dn n).IsLength) (hproper : IsProperFn D.1)
    (hconv : ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(Dn n).1) ⇑D.1 atTop
      (Metric.closedBall (0 : Rd d) R ×ˢ Metric.closedBall (0 : Rd d) R))
    {r : ℝ} (hr : 0 < r) (M : ℝ) :
    ∃ R : ℝ, r < R ∧ ∀ x ∈ Metric.closedBall (0 : Rd d) r,
      ∀ z, z ∉ Metric.ball (0 : Rd d) R → M ≤ D.1 (x, z) := by
  obtain ⟨R, hrR, hbar⟩ := hproper.exists_sphere_barrier D hr (M + 1)
  refine ⟨R, hrR, fun x hx z hz => ?_⟩
  have hR : 0 < R := lt_trans hr hrR
  have hxR : x ∈ Metric.ball (0 : Rd d) R := by
    rw [Metric.mem_ball, dist_zero_right]
    have := hx
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith
  let S : ℝ := R + ‖z‖ + 1
  have hS : 0 < S := by dsimp [S]; positivity
  have hxS : x ∈ Metric.closedBall (0 : Rd d) S := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have hx' : ‖x‖ < R := by simpa [Metric.mem_ball] using hxR
    dsimp [S]; linarith [norm_nonneg z]
  have hzS : z ∈ Metric.closedBall (0 : Rd d) S := by
    rw [Metric.mem_closedBall, dist_zero_right]
    dsimp [S]; linarith
  obtain ⟨n, hn⟩ := (eventually_dist_lt_on_closedBall
    (fun n => (Dn n).1) D.1 hconv S (1 / 4) hS (by norm_num)).exists
  obtain ⟨u, hu, hnu⟩ := (Dn n).exists_sphere_le_of_outside (hDn n) hxR hz (by norm_num : (0 : ℝ) < 1 / 4)
  have huS : u ∈ Metric.closedBall (0 : Rd d) S := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have hu' : ‖u‖ = R := by simpa [Metric.mem_sphere] using hu
    dsimp [S]; linarith [norm_nonneg z]
  have hxu := abs_lt.mp (hn x hxS u huS)
  have hxz := abs_lt.mp (hn x hxS z hzS)
  have hbar' := hbar x hx u hu
  linarith

/-- Local limits inherit metric properness from length approximants and sphere barriers. -/
theorem properSpace_of_length_limit
    (Dn : ℕ → ContMetric d) (D : ContMetric d)
    (hDn : ∀ n, (Dn n).IsLength) (hproper : IsProperFn D.1)
    (hconv : ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(Dn n).1) ⇑D.1 atTop
      (Metric.closedBall (0 : Rd d) R ×ˢ Metric.closedBall (0 : Rd d) R)) :
    ProperSpace D.Space := by
  refine ⟨fun a k => ?_⟩
  obtain ⟨R, -, hbar⟩ := exists_outside_barrier_of_length_limit Dn D hDn hproper hconv
    (by norm_num : (0 : ℝ) < 1) (D.1 (0, D.unpt a) + k + 1)
  have hK : IsCompact (D.pt ⁻¹' Metric.closedBall a k) := by
    refine (isCompact_closedBall (0 : Rd d) R).of_isClosed_subset
      (Metric.isClosed_closedBall.preimage D.continuous_pt) ?_
    intro z hz
    have hza : D.1 (z, D.unpt a) ≤ k := by
      change dist (D.pt z) a ≤ k at hz
      rw [← D.pt_unpt a] at hz
      exact hz
    have h0z : D.1 (0, z) ≤ D.1 (0, D.unpt a) + k := by
      have ht := D.2.triangle 0 (D.unpt a) z
      rw [D.2.symm (D.unpt a) z] at ht
      linarith
    have hzR : z ∈ Metric.ball (0 : Rd d) R := by
      by_contra hn
      have hb := hbar 0 (by simp) z hn
      linarith
    exact Metric.ball_subset_closedBall hzR
  have himg := hK.image D.continuous_pt
  rwa [Set.image_preimage_eq _ (fun y => ⟨D.unpt y, D.pt_unpt y⟩)] at himg

/-- Approximate midpoints pass to the limit once the candidates are confined by a sphere barrier. -/
theorem hasApproxMidpoints_of_length_limit
    (Dn : ℕ → ContMetric d) (D : ContMetric d)
    (hDn : ∀ n, (Dn n).IsLength) (hproper : IsProperFn D.1)
    (hconv : ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(Dn n).1) ⇑D.1 atTop
      (Metric.closedBall (0 : Rd d) R ×ˢ Metric.closedBall (0 : Rd d) R)) :
    LQGMetric.MetricGeometry.HasApproxMidpoints D.Space := by
  intro a b ε hε
  let x : Rd d := D.unpt a
  let y : Rd d := D.unpt b
  let r : ℝ := ‖x‖ + ‖y‖ + 1
  have hr : 0 < r := by dsimp [r]; positivity
  have hx : x ∈ Metric.closedBall (0 : Rd d) r := by
    rw [Metric.mem_closedBall, dist_zero_right]
    dsimp [r]; linarith [norm_nonneg y]
  have hy : y ∈ Metric.closedBall (0 : Rd d) r := by
    rw [Metric.mem_closedBall, dist_zero_right]
    dsimp [r]; linarith [norm_nonneg x]
  obtain ⟨R, hrR, hbar⟩ := hproper.exists_sphere_barrier D hr (D.1 (x,y) + 2)
  have hR : 0 < R := lt_trans hr hrR
  have hxR : x ∈ Metric.ball (0 : Rd d) R := by
    rw [Metric.mem_ball, dist_zero_right]
    have hx' : ‖x‖ ≤ r := by simpa [Metric.mem_closedBall] using hx
    linarith
  have hxyR : x ∈ Metric.closedBall (0 : Rd d) R ∧
      y ∈ Metric.closedBall (0 : Rd d) R := by
    constructor <;> rw [Metric.mem_closedBall, dist_zero_right]
    · have hx' : ‖x‖ ≤ r := by simpa [Metric.mem_closedBall] using hx
      linarith
    · have hy' : ‖y‖ ≤ r := by simpa [Metric.mem_closedBall] using hy
      linarith
  let δ : ℝ := min (ε / 4) (1 / 4)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ1 : δ ≤ 1 / 4 := min_le_right _ _
  have hδε : δ ≤ ε / 4 := min_le_left _ _
  obtain ⟨n, hn⟩ := (eventually_dist_lt_on_closedBall
    (fun n => (Dn n).1) D.1 hconv R δ hR hδ).exists
  obtain ⟨m, hm₁, hm₂⟩ :=
    LQGMetric.MetricGeometry.hasApproxMidpoints_of_isLengthSpace (hDn n)
      ((Dn n).pt x) ((Dn n).pt y) δ hδ
  let z : Rd d := (Dn n).unpt m
  have hmz : m = (Dn n).pt z := ((Dn n).pt_unpt m).symm
  have hmid₁ : (Dn n).1 (x,z) ≤ (Dn n).1 (x,y) / 2 + δ := by
    simpa only [hmz, ContMetric.dist_pt] using hm₁
  have hmid₂ : (Dn n).1 (y,z) ≤ (Dn n).1 (x,y) / 2 + δ := by
    simpa only [hmz, ContMetric.dist_pt] using hm₂
  have hzR : z ∈ Metric.closedBall (0 : Rd d) R := by
    by_contra hz
    have hz' : z ∉ Metric.ball (0 : Rd d) R := fun h => hz (Metric.ball_subset_closedBall h)
    obtain ⟨u, hu, hnu⟩ := (Dn n).exists_sphere_le_of_outside (hDn n) hxR hz' hδ
    have huR : u ∈ Metric.closedBall (0 : Rd d) R := Metric.sphere_subset_closedBall hu
    have hxu := abs_lt.mp (hn x hxyR.1 u huR)
    have hxy := abs_lt.mp (hn x hxyR.1 y hxyR.2)
    have hB := hbar x hx u hu
    have hnonneg := D.nonneg x y
    linarith
  have hxy := abs_lt.mp (hn x hxyR.1 y hxyR.2)
  have hxz := abs_lt.mp (hn x hxyR.1 z hzR)
  have hyz := abs_lt.mp (hn y hxyR.2 z hzR)
  refine ⟨D.pt z, ?_, ?_⟩
  · change D.1 (x,z) ≤ D.1 (x,y) / 2 + ε
    linarith
  · change D.1 (y,z) ≤ D.1 (x,y) / 2 + ε
    linarith

/-- MA5 DL1: a proper locally uniform limit of continuous length metrics is a length metric. -/
theorem l6c_lengthLimit : L6c_lengthLimit := by
  intro d Dn D hDn hD hproper hconv
  let D' : ContMetric d := ⟨D, hD⟩
  let Dn' : ℕ → ContMetric d := fun n => ⟨Dn n, (hDn n).choose⟩
  have hDn' : ∀ n, (Dn' n).IsLength := fun n => (hDn n).choose_spec
  have hconv' : ∀ R : ℝ, 0 < R → TendstoUniformlyOn
      (fun n => ⇑(Dn' n).1) ⇑D'.1 atTop
      (Metric.closedBall (0 : Rd d) R ×ˢ Metric.closedBall (0 : Rd d) R) := hconv
  refine ⟨hD, ?_⟩
  exact @LQGMetric.MetricGeometry.isLengthSpace_of_hasApproxMidpoints D'.Space _
    (@complete_of_proper D'.Space _
      (properSpace_of_length_limit Dn' D' hDn' hproper hconv'))
    (hasApproxMidpoints_of_length_limit Dn' D' hDn' hproper hconv')

end HigherDimLQGMetric
