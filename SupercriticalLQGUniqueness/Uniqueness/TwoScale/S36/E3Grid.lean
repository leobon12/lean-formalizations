import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.GeodLebDet
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.ChainCover
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.UnitParam
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.LMIter2T




 













set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

open LQGMetric (DistC)

 

 
def gridPt (z : ℂ) (r : ℝ) (N j : ℕ) : ℂ :=
  z + (r : ℂ) * Complex.exp (Complex.I * ((-Real.pi + 2 * Real.pi * j / N : ℝ) : ℂ))

theorem norm_exp_I_sub_exp_I_le (θ φ : ℝ) :
    ‖Complex.exp (Complex.I * (θ : ℂ)) - Complex.exp (Complex.I * (φ : ℂ))‖ ≤ |θ - φ| := by
  have hsplit : Complex.exp (Complex.I * (θ : ℂ)) - Complex.exp (Complex.I * (φ : ℂ)) =
      Complex.exp (Complex.I * (φ : ℂ)) * (Complex.exp (Complex.I * ((θ - φ : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    push_cast
    ring
  rw [hsplit, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ - φ)
  rwa [Real.norm_eq_abs] at this

theorem dist_gridPt_center (z : ℂ) {r : ℝ} (hr : 0 ≤ r) (N j : ℕ) : dist (gridPt z r N j) z = r := by
  rw [gridPt, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_exp_I_mul_ofReal,
    mul_one, Complex.norm_real, Real.norm_of_nonneg hr]

 
theorem exists_gridPt_near (z : ℂ) {r a : ℝ} (hr : 0 < r) (ha : 0 < a) {N : ℕ} (hN : 0 < N)
    {y : ℂ} (hy1 : a * r ≤ dist y z) (hy2 : dist y z ≤ r) :
    ∃ j ≤ N, dist y (gridPt z r N j) ≤ (1 - a) * r + Real.pi * r / N := by
  have hyz : y - z ≠ 0 := by
    intro h0
    have : dist y z = 0 := by rw [dist_eq_norm, h0, norm_zero]
    nlinarith
  set θ := Complex.arg (y - z) with hθdef
  have hθ1 : -Real.pi < θ := Complex.neg_pi_lt_arg _
  have hθ2 : θ ≤ Real.pi := Complex.arg_le_pi _
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set u : ℝ := (θ + Real.pi) * N / (2 * Real.pi) with hudef
  have hu0 : 0 ≤ u := by rw [hudef]; apply div_nonneg <;> nlinarith [Real.pi_pos]
  have huN : u ≤ N := by
    rw [hudef, div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  set j := ⌊u + 1 / 2⌋₊ with hjdef
  have hj1 : (j : ℝ) ≤ u + 1 / 2 := Nat.floor_le (by linarith)
  have hj2 : u + 1 / 2 < j + 1 := Nat.lt_floor_add_one _
  have hjN : j ≤ N := by
    have : (j : ℝ) < N + 1 := by linarith
    exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
  refine ⟨j, hjN, ?_⟩
  
  have hang : |(-Real.pi + 2 * Real.pi * j / N) - θ| ≤ Real.pi / N := by
    have hident : (-Real.pi + 2 * Real.pi * j / N) - θ = 2 * Real.pi / N * (j - u) := by
      rw [hudef]
      field_simp
      ring
    rw [hident, abs_mul, abs_of_pos (by positivity)]
    have hju : |(j : ℝ) - u| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    calc 2 * Real.pi / N * |(j : ℝ) - u| ≤ 2 * Real.pi / N * (1 / 2) :=
          mul_le_mul_of_nonneg_left hju (by positivity)
      _ = Real.pi / N := by ring
  
  have hpolar : y - z = (‖y - z‖ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := by
    have := Complex.norm_mul_exp_arg_mul_I (y - z)
    rw [mul_comm (↑(Complex.arg (y - z))) Complex.I] at this
    exact this.symm
  have hρ : ‖y - z‖ = dist y z := (dist_eq_norm y z).symm
  rw [dist_eq_norm]
  have hrw : y - gridPt z r N j = (y - z) -
      (r : ℂ) * Complex.exp (Complex.I * ((-Real.pi + 2 * Real.pi * j / N : ℝ) : ℂ)) := by
    rw [gridPt]
    ring
  rw [hrw, hpolar]
  calc ‖(‖y - z‖ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) -
        (r : ℂ) * Complex.exp (Complex.I * ((-Real.pi + 2 * Real.pi * j / N : ℝ) : ℂ))‖
      ≤ ‖(‖y - z‖ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) -
          (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ +
        ‖(r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) -
          (r : ℂ) * Complex.exp (Complex.I * ((-Real.pi + 2 * Real.pi * j / N : ℝ) : ℂ))‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = |dist y z - r| + r * ‖Complex.exp (Complex.I * (θ : ℂ)) -
          Complex.exp (Complex.I * ((-Real.pi + 2 * Real.pi * j / N : ℝ) : ℂ))‖ := by
        rw [← sub_mul, ← mul_sub, norm_mul, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one,
          Complex.norm_real, Real.norm_of_nonneg hr.le, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs, hρ]
    _ ≤ (1 - a) * r + r * (Real.pi / N) := by
        gcongr
        · rw [abs_of_nonpos (by linarith)]
          nlinarith
        · calc ‖Complex.exp (Complex.I * (θ : ℂ)) -
                Complex.exp (Complex.I * ((-Real.pi + 2 * Real.pi * j / N : ℝ) : ℂ))‖
              ≤ |θ - (-Real.pi + 2 * Real.pi * j / N)| := norm_exp_I_sub_exp_I_le _ _
            _ = |(-Real.pi + 2 * Real.pi * j / N) - θ| := abs_sub_comm _ _
            _ ≤ Real.pi / N := hang
    _ = (1 - a) * r + Real.pi * r / N := by ring

 

 
def leScale (ρ₀ : ℝ) (k : ℕ) : ℝ := ρ₀ * (1 / 5 : ℝ) ^ k / 4

theorem leScale_pos {ρ₀ : ℝ} (h : 0 < ρ₀) (k : ℕ) : 0 < leScale ρ₀ k := by
  unfold leScale
  positivity

 

theorem good_point_prob (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) :
    ∃ α c : ℝ, 0 < α ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
        ∀ (x : ℂ) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) (m : ℕ), 1 ≤ m →
          P {ω | ¬ ∃ k ∈ Finset.Icc 1 m, RatioEv (D (h ω)) (leScale_pos hρ₀ k) x} ≤
            ENNReal.ofReal (c * Real.exp (-α * m)) := by
  obtain ⟨p₀, hp₀, hbump⟩ := bump_marginal ξ Q hQ D hD
  set p' : ℝ := min p₀ (1 / 2) with hp'def
  have hp' : 0 < p' := lt_min hp₀ (by norm_num)
  have hp'1 : p' < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨α, β, c, hα, hβ, -, hc, hiter⟩ :=
    annulus_iteration2_ae_translated_open (1 / 5) (4 / 5) (by norm_num) (by norm_num)
      (by norm_num) p' hp' hp'1
  refine ⟨α, c, hα, hc, ?_⟩
  intro Ω _ P _ h hh x ρ₀ hρ₀ m hm
  let R : ℕ → ℝ := fun k => ρ₀ * (1 / 5 : ℝ) ^ k
  let E : ℕ → Set Ω := fun k => {ω | RatioEv (D (h ω)) (leScale_pos hρ₀ k) x}
  have hR : ∀ k, 0 < R k := fun k => by positivity
  have hanti : Antitone R := by
    intro k k' hkk'
    have : (1 / 5 : ℝ) ^ k' ≤ (1 / 5 : ℝ) ^ k :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hkk'
    exact mul_le_mul_of_nonneg_left this hρ₀.le
  have hratio : ∀ k, R (k + 1) / R k ≤ 1 / 5 := by
    intro k
    have hRk := hR k
    rw [div_le_iff₀ hRk]
    change ρ₀ * (1 / 5 : ℝ) ^ (k + 1) ≤ 1 / 5 * (ρ₀ * (1 / 5 : ℝ) ^ k)
    rw [pow_succ]
    ring_nf
    exact le_rfl
  have hU : ∀ k, ratioCarrier (leScale ρ₀ k) x ⊆
      (LQGMetric.Blueprint.annulus x ((1 / 5 : ℝ) * R k) ((4 / 5 : ℝ) * R k) : Set ℂ) := by
    intro k y hy
    obtain ⟨h1, h2⟩ := hy
    change (1 / 5 : ℝ) * R k < ‖y - x‖ ∧ ‖y - x‖ < (4 / 5 : ℝ) * R k
    have e1 : 4 * leScale ρ₀ k / 5 = (1 / 5 : ℝ) * R k := by
      simp only [leScale, R]
      ring
    have e2 : 16 * leScale ρ₀ k / 5 = (4 / 5 : ℝ) * R k := by
      simp only [leScale, R]
      ring
    rw [← e1, ← e2]
    exact ⟨h1, h2⟩
  have hloc : ∀ k, LQGMetric.Blueprint.AEEventIn P
      (LQGMetric.Blueprint.fieldSigma
        (fun ω => LQGMetric.addConst (h ω) (-LQGMetric.circleAvg (h ω) (R k) x))
        (LQGMetric.Blueprint.annulus x ((1 / 5 : ℝ) * R k) ((4 / 5 : ℝ) * R k))) (E k) :=
    fun k => ratio_centered_local P h hh ξ Q hQ D hD (leScale_pos hρ₀ k) x _ (hU k) (R k)
  have hprob : ∀ k, ENNReal.ofReal p' ≤ P (E k) := fun k =>
    (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans
      (hbump P h hh (leScale ρ₀ k) (leScale_pos hρ₀ k) x)
  have hit := hiter P h hh.1 x R E hR hanti hratio hloc hprob m
  refine (measure_mono ?_).trans hit
  intro ω hω
  have hzero : LQGMetric.Blueprint.countOcc E m ω = 0 := by
    classical
    unfold LQGMetric.Blueprint.countOcc
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro k hk hkE
    exact hω ⟨k, hk, hkE⟩
  change (LQGMetric.Blueprint.countOcc E m ω : ℝ) < β * m
  rw [hzero, Nat.cast_zero]
  have : (1 : ℝ) ≤ m := by exact_mod_cast hm
  positivity

 

 


theorem segment_dist_le_of_grid (d : LSCMetric)
    (hcont : ∀ (γ : ℝ → ℂ) (a b : ℝ), d.IsCurve γ a b → ContinuousOn γ (Icc a b))
    (z : ℂ) {r a ε ρ₀ : ℝ} (hr : 0 < r) (ha0 : 0 < a) (hε : 0 < ε) (hρ₀ : 0 < ρ₀)
    {N m : ℕ} (hN : 0 < N) (hnear : (1 - a) * r + Real.pi * r / N < ε * r)
    (hsm : ∀ k ∈ Finset.Icc 1 m, ε * r ≤ leScale ρ₀ k)
    (hs1 : ∀ k ∈ Finset.Icc 1 m, 3 * leScale ρ₀ k ≤ r / 2)
    (Bad : Finset ℕ)
    (hgood : ∀ j ≤ N, j ∉ Bad →
      ∃ k ∈ Finset.Icc 1 m, RatioEv d (leScale_pos hρ₀ k) (gridPt z r N j))
    {P : ℝ → ℂ} {s t : ℝ} (hP : TwoScale.S36Events.InternalBoundaryGeodesic d z r P s t)
    {v w : ℝ} (hvs : v ∈ Icc s t) (hws : w ∈ Icc s t) (hvw : v ≤ w)
    (hseg : ∀ τ ∈ Icc v w, P τ ∈ Metric.closedBall z r \ Metric.ball z (a * r)) :
    dist (P v) (P w) ≤ 2 * (ε * r) * ((Bad.image (gridPt z r N)).card + 1) := by
  obtain ⟨Pth, T, hT0, hcurve, -, hgeo, hP0, hPT, hpre⟩ := exists_unit_internal_param d z r hP
  obtain ⟨-, -, hcurveP, -, hbs, hbt, -, -⟩ := hP
  have hPthc : ContinuousOn Pth (Icc 0 T) := hcont Pth 0 T hcurve
  have hPc : ContinuousOn P (Icc s t) := hcont P s t hcurveP
  
  have hfar : ∀ (j : ℕ) (k : ℕ), k ∈ Finset.Icc 1 m → ∀ y ∈ TwoScale.S36Events.eventBoundary z r,
      3 * leScale ρ₀ k ≤ dist y (gridPt z r N j) := by
    intro j k hk y hy
    have hxz := dist_gridPt_center z hr.le N j
    have h3 := hs1 k hk
    rcases hy with hy | hy
    · have hyz : dist y z = r / 2 := Metric.mem_sphere.mp hy
      have htri := dist_triangle (gridPt z r N j) y z
      rw [dist_comm (gridPt z r N j) y] at htri
      linarith
    · have hyz : dist y z = 2 * r := Metric.mem_sphere.mp hy
      have htri := dist_triangle y (gridPt z r N j) z
      linarith
  
  have havoid : ∀ j ≤ N, j ∉ Bad → ∀ σ ∈ Icc 0 T, ε * r ≤ dist (Pth σ) (gridPt z r N j) := by
    intro j hj hjB σ hσ
    obtain ⟨k, hk, hE⟩ := hgood j hj hjB
    have hBY : Metric.closedBall (gridPt z r N j) (3 * leScale ρ₀ k) ⊆ TwoScale.S36Events.eventCarrier z r := by
      intro y hy
      have hy' := Metric.mem_closedBall.mp hy
      have hxz := dist_gridPt_center z hr.le N j
      have h3 := hs1 k hk
      refine ⟨Metric.mem_closedBall.mpr ?_, ?_⟩
      · have := dist_triangle y (gridPt z r N j) z
        linarith
      · rw [Metric.mem_ball, not_lt]
        have := dist_triangle (gridPt z r N j) y z
        rw [dist_comm (gridPt z r N j) y] at this
        linarith
    have h0 : 3 * leScale ρ₀ k ≤ dist (Pth 0) (gridPt z r N j) := by
      rw [hP0]
      exact hfar j k hk _ hbs
    have hT' : 3 * leScale ρ₀ k ≤ dist (Pth T) (gridPt z r N j) := by
      rw [hPT]
      exact hfar j k hk _ hbt
    have hav := internal_geodesic_avoids d (TwoScale.S36Events.eventCarrier z r) hPthc hgeo
      (leScale_pos hρ₀ k) (gridPt z r N j) hBY h0 hT' (around_lt_across_of_ratioEv hE) σ hσ
    exact (hsm k hk).trans hav
  
  set F : Finset ℂ := Bad.image (gridPt z r N) with hFdef
  have hcov : P '' Icc v w ⊆ ⋃ c ∈ F, Metric.ball c (ε * r) := by
    rintro y ⟨τ, hτ, rfl⟩
    have hτst : τ ∈ Icc s t := ⟨hvs.1.trans hτ.1, hτ.2.trans hws.2⟩
    obtain ⟨σ, hσ, hσe⟩ := hpre τ hτst
    have hann := hseg τ hτ
    have h1 : a * r ≤ dist (P τ) z := not_lt.mp fun h => hann.2 (Metric.mem_ball.mpr h)
    have h2 : dist (P τ) z ≤ r := Metric.mem_closedBall.mp hann.1
    obtain ⟨j, hjN, hjd⟩ := exists_gridPt_near z hr ha0 hN h1 h2
    have hjB : j ∈ Bad := by
      by_contra hjB
      have := havoid j hjN hjB σ hσ
      rw [hσe] at this
      linarith
    simp only [mem_iUnion, exists_prop]
    exact ⟨gridPt z r N j, Finset.mem_image_of_mem _ hjB, Metric.mem_ball.mpr (by linarith)⟩
  have hS : IsPreconnected (P '' Icc v w) :=
    isPreconnected_Icc.image P (hPc.mono (Icc_subset_Icc hvs.1 hws.2))
  exact dist_le_of_preconnected_cover hS F (by positivity) hcov
    ⟨v, left_mem_Icc.mpr hvw, rfl⟩ ⟨w, right_mem_Icc.mpr hvw, rfl⟩

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
