import SupercriticalConformalCovariance.Small.EndpointConfinement
import SupercriticalConformalCovariance.Regular.Measurability
import SupercriticalConformalCovariance.Recovery.Recovery
import SupercriticalConformalCovariance.Small.RegularAdapters

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace SupercriticalConformalCovariance.Small
open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.Uniqueness

/-- A geodesic whose trace stays in the disk remains a geodesic after confinement. -/
theorem exists_conf_geodesic_of_trace
    (D : LSCMetric) (c : ℂ) (R : ℝ) (u v : ℂ)
    (P : ℝ → ℂ) (a b : ℝ)
    (hgeo : OptimalConstants.Ratios.Geodesic D P a b u v)
    (hK : ∀ t ∈ Icc a b, P t ∈ closedBall c R) :
    ∃ (Q : ℝ → ℂ) (L : ℝ),
      OptimalConstants.Ratios.Geodesic (conf D c R) Q 0 L u v ∧
      Q '' Icc 0 L = P '' Icc a b := by
  rcases hgeo with ⟨hP,hu,hv,hlen,hfin⟩
  have hlenfin : D.len P a b ≠ ⊤ := by
    rw [hlen]
    exact hfin.ne
  obtain ⟨Q,L,hQc,hQ0,hQL,htrace,hlenQ⟩ :=
    exists_conf_curve_same_trace_len D c R P a b hP hlenfin hK
  have hu' : Q 0 = u := hQ0.trans hu
  have hv' : Q L = v := hQL.trans hv
  have hcostle : conf D c R (u,v) ≤ (conf D c R).len Q 0 L := by
    rw [← hu', ← hv']
    exact (conf D c R).apply_le_len Q hQc.1
  have hcostge : D (u,v) ≤ conf D c R (u,v) := original_le_conf D c R u v
  have hcosteq : conf D c R (u,v) = D (u,v) := by
    apply le_antisymm
    · calc
      _ ≤ (conf D c R).len Q 0 L := hcostle
      _ = D.len P a b := hlenQ
      _ = D (u,v) := hlen
    · exact hcostge
  refine ⟨Q,L,⟨hQc,hu',hv',?_,?_⟩,htrace⟩
  · rw [hlenQ,hlen,hcosteq]
  · rw [hcosteq]
    exact hfin


theorem conf_cost_eq_of_geodesic_trace
    (D : LSCMetric) (c : ℂ) (R : ℝ) (u v : ℂ)
    (P : ℝ → ℂ) (a b : ℝ)
    (hgeo : OptimalConstants.Ratios.Geodesic D P a b u v)
    (hK : ∀ t ∈ Icc a b, P t ∈ closedBall c R) :
    conf D c R (u,v) = D (u,v) := by
  rcases hgeo with ⟨hP, hu, hv, hlen, hfin⟩
  have hlenfin : D.len P a b ≠ ⊤ := by
    rw [hlen]
    exact hfin.ne
  obtain ⟨Q,L,hQc,hQ0,hQL,_,hlenQ⟩ :=
    exists_conf_curve_same_trace_len D c R P a b hP hlenfin hK
  apply le_antisymm
  · calc
      conf D c R (u,v) = conf D c R (Q 0,Q L) := by rw [hQ0, hQL, hu, hv]
      _ ≤ (conf D c R).len Q 0 L := (conf D c R).apply_le_len Q hQc.1
      _ = D.len P a b := hlenQ
      _ = D (u,v) := hlen
  · exact original_le_conf D c R u v


theorem aroundRat_eq_conf_of_annulus
    (D : LSCMetric) (c : ℂ) (R : ℝ) (x : ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hsub : (SupercriticalConformalCovariance.Recovery.shortAnnulus x ρ hρ hρ1).toSet ⊆ closedBall c R) :
    TwoScale.Consolidated.aroundRat
        (conf D c R, (x, ρ, Real.sqrt ρ)) =
      TwoScale.Consolidated.aroundRat
        (D, (x, ρ, Real.sqrt ρ)) := by
  let A := SupercriticalConformalCovariance.Recovery.shortAnnulus x ρ hρ hρ1
  change TwoScale.Consolidated.aroundRat
      (conf D c R, (A.center, A.innerRadius, A.outerRadius)) =
    TwoScale.Consolidated.aroundRat
      (D, (A.center, A.innerRadius, A.outerRadius))
  rw [← TwoScale.Consolidated.aroundDist_eq_aroundRat (conf D c R) A,
    ← TwoScale.Consolidated.aroundDist_eq_aroundRat D A]
  exact aroundDist_eq_conf D c R A hsub


/-- Transfer the printed regular-pair predicate to the corrected confined metric.
The geometric hypotheses only say that each tested ball and annulus lies in the disk. -/
theorem sourceRegularPair_conf_of_geometry
    (D : LSCMetric) (hL : D.IsLengthSpace)
    (hC : ∀ (P : ℝ → ℂ) (a b : ℝ), D.IsCurve P a b →
      D.len P a b < ⊤ → ContinuousOn P (Icc a b))
    (R α θ m : ℝ) (u v : ℂ)
    (hann : SupercriticalConformalCovariance.Regular.closedAnnulus 0 α 1 ⊆ closedBall 0 R)
    (hsmall : ∀ j : ℕ, 0 < SupercriticalConformalCovariance.Regular.dyadic j →
      SupercriticalConformalCovariance.Regular.dyadic j ≤ (1 - α) ^ 2 → SupercriticalConformalCovariance.Regular.dyadic j < 1)
    (hball : ∀ (x : ℂ), x = u ∨ x = v →
      ∀ j : ℕ, (hj : 0 < SupercriticalConformalCovariance.Regular.dyadic j) →
      SupercriticalConformalCovariance.Regular.dyadic j ≤ (1 - α) ^ 2 →
        closedBall x (SupercriticalConformalCovariance.Regular.dyadic j) ⊆ closedBall 0 R)
    (hloop : ∀ (x : ℂ), x = u ∨ x = v →
      ∀ j : ℕ, (hj : 0 < SupercriticalConformalCovariance.Regular.dyadic j) →
      (hj1 : SupercriticalConformalCovariance.Regular.dyadic j < 1) →
      SupercriticalConformalCovariance.Regular.dyadic j ≤ (1 - α) ^ 2 →
      (SupercriticalConformalCovariance.Recovery.shortAnnulus x (SupercriticalConformalCovariance.Regular.dyadic j) hj hj1).toSet
        ⊆ closedBall 0 R)
    (hreg : SupercriticalConformalCovariance.Regular.SourceRegularPair D 0 u v 1 α θ m) :
    SupercriticalConformalCovariance.Regular.SourceRegularPair (conf D 0 R) 0 u v 1 α θ m := by
  rcases hreg with ⟨⟨P,a,b,hgeo,htrace⟩,hu,hv,h7,h8u,h8v⟩
  simp only [mul_one] at h8u h8v
  have hK : ∀ t ∈ Icc a b, P t ∈ closedBall 0 R := by
    intro t ht
    exact hann (by simpa only [mul_one] using htrace ⟨t,ht,rfl⟩)
  obtain ⟨Q,L,hQgeo,hQtrace⟩ :=
    exists_conf_geodesic_of_trace D 0 R u v P a b hgeo hK
  have hcost := conf_cost_eq_of_geodesic_trace D 0 R u v P a b hgeo hK
  refine ⟨⟨Q,0,L,hQgeo,?_⟩,hu,hv,?_,?_,?_⟩
  · rw [hQtrace]
    exact htrace
  · rw [hcost]
    exact h7
  · intro j hj hjα
    obtain ⟨hp,hl⟩ := h8u j hj hjα
    constructor
    · simp only [mul_one]
      rw [pointSphereDist_eq_conf D hL hC 0 R u hj (hball u (.inl rfl) j hj hjα),
        hcost]
      exact hp
    · simp only [mul_one]
      rw [aroundRat_eq_conf_of_annulus D 0 R u _ hj (hsmall j hj hjα)
        (hloop u (.inl rfl) j hj (hsmall j hj hjα) hjα), hcost]
      exact hl
  · intro j hj hjα
    obtain ⟨hp,hl⟩ := h8v j hj hjα
    constructor
    · simp only [mul_one]
      rw [pointSphereDist_eq_conf D hL hC 0 R v hj (hball v (.inr rfl) j hj hjα),
        hcost]
      exact hp
    · simp only [mul_one]
      rw [aroundRat_eq_conf_of_annulus D 0 R v _ hj (hsmall j hj hjα)
        (hloop v (.inr rfl) j hj (hsmall j hj hjα) hjα), hcost]
      exact hl


private theorem unit_center_ball_subset_two (x : ℂ)
    (hx : x ∈ closedBall 0 1) : closedBall x 1 ⊆ closedBall 0 2 := by
  intro y hy
  change dist y 0 ≤ 2
  calc
    dist y 0 ≤ dist y x + dist x 0 := dist_triangle y x 0
    _ ≤ 1 + 1 := add_le_add hy (by
      simpa only [Metric.mem_closedBall, dist_comm] using hx)
    _ = 2 := by norm_num

/-- A unit-scale regular pair has all the needed local geometry inside the radius-two disk. -/
theorem sourceRegularPair_conf_two
    (D : LSCMetric) (hL : D.IsLengthSpace)
    (hC : ∀ (P : ℝ → ℂ) (a b : ℝ), D.IsCurve P a b →
      D.len P a b < ⊤ → ContinuousOn P (Icc a b))
    (α θ m : ℝ) (u v : ℂ)
    (hα : (3 / 4 : ℝ) < α ∧ α < 1)
    (hreg : SupercriticalConformalCovariance.Regular.SourceRegularPair D 0 u v 1 α θ m) :
    SupercriticalConformalCovariance.Regular.SourceRegularPair (conf D 0 2) 0 u v 1 α θ m := by
  have hu : u ∈ closedBall 0 1 := by
    have hs := hreg.2.1
    change dist u 0 = α * 1 at hs
    change dist u 0 ≤ 1
    simpa only [mul_one] using hs
      |>.trans_le (by simpa only [mul_one] using hα.2.le)
  have hv : v ∈ closedBall 0 1 := by
    have hs := hreg.2.2.1
    change dist v 0 = (1 : ℝ) at hs
    change dist v 0 ≤ 1
    exact hs.le
  have hsquare : (1 - α) ^ 2 < 1 := by nlinarith [sq_nonneg α]
  have hsmall : ∀ j : ℕ, 0 < SupercriticalConformalCovariance.Regular.dyadic j →
      SupercriticalConformalCovariance.Regular.dyadic j ≤ (1 - α) ^ 2 → SupercriticalConformalCovariance.Regular.dyadic j < 1 :=
    fun j _ hj => lt_of_le_of_lt hj hsquare
  have hunit : ∀ x : ℂ, x = u ∨ x = v → closedBall x 1 ⊆ closedBall 0 2 := by
    intro x hx
    rcases hx with hx | hx
    · simpa only [hx] using unit_center_ball_subset_two u hu
    · simpa only [hx] using unit_center_ball_subset_two v hv
  apply sourceRegularPair_conf_of_geometry D hL hC 2 α θ m u v
  · intro x hx
    exact (closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2)) hx.1
  · exact hsmall
  · intro x hx j hj hjα
    exact (closedBall_subset_closedBall (le_of_lt (hsmall j hj hjα))).trans
      (hunit x hx)
  · intro x hx j hj hj1 hjα y hy
    apply hunit x hx
    change dist y x ≤ 1
    have hy' : dist y x < Real.sqrt (SupercriticalConformalCovariance.Regular.dyadic j) := by
      exact hy.1
    exact le_of_lt (lt_trans hy' (by
      simpa only [Real.sqrt_one] using
        Real.sqrt_lt_sqrt hj.le hj1))
  · exact hreg


/-- A source witness survives confinement; the target cost may only increase. -/
theorem sourceFailure_conf_of_target_mono
    (D F : LSCMetric) (hL : D.IsLengthSpace)
    (hC : ∀ (P : ℝ → ℂ) (a b : ℝ), D.IsCurve P a b →
      D.len P a b < ⊤ → ContinuousOn P (Icc a b))
    (α θ m T η : ℝ) (u v : ℂ) (eCost : ℝ≥0∞)
    (hα : (3 / 4 : ℝ) < α ∧ α < 1)
    (hmT : m ≤ T)
    (hreg : SupercriticalConformalCovariance.Regular.SourceRegularPair D 0 u v 1 α θ m)
    (hfail : ENNReal.ofReal (1 + η) * D (u,v) ≤ eCost)
    (hmono : eCost ≤ F (u,v)) :
    SupercriticalConformalCovariance.Regular.SourceFailure (conf D 0 2) F 0 u v 1 α θ T
      ((1 - α)⁻¹ * T) (1 - α) η := by
  have hreg' := sourceRegularPair_conf_two D hL hC α θ m u v hα hreg
  obtain ⟨P,a,b,hgeo,htrace⟩ := hreg.1
  have hcost := conf_cost_eq_of_geodesic_trace D 0 2 u v P a b hgeo (by
    intro t ht
    exact (closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2))
      (htrace ⟨t,ht,rfl⟩).1)
  apply sourceFailure_of_regular_and_bound (conf D 0 2) F 0 u v
    α θ m T η hα.2 hmT hreg'
  rw [hcost]
  exact hfail.trans hmono
