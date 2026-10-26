import SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.FixedUnit.Infimum
import SupercriticalLQGUniqueness.B2.LscTop.Limits

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalConformalCovariance.Recovery

open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios
open SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.FixedUnit
open SupercriticalLQGUniqueness.Uniqueness.TwoScale.Transfer

/-- The annulus in formula (6), for a radius strictly between zero and one. -/
def shortAnnulus (x : ℂ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    EuclideanAnnulus := by
  refine ⟨(x, (r, Real.sqrt r)), hr, ?_⟩
  have hsq := Real.sq_sqrt hr.le
  have ht1 : Real.sqrt r < 1 := by
    nlinarith [Real.sqrt_nonneg r]
  nlinarith [mul_pos (Real.sqrt_pos.mpr hr) (sub_pos.mpr ht1)]

/-- The point-to-circle distance cannot increase when the circle is moved
inward, provided finite-length metric paths are Euclidean continuous. -/
theorem setDist_sphere_mono_radius
    (D : LSCMetric) (hDlen : D.IsLengthSpace)
    (hDreg : ∀ (P : ℝ → ℂ) (a b : ℝ),
      D.IsCurve P a b → D.len P a b < ⊤ → ContinuousOn P (Icc a b))
    (x : ℂ) {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) :
    setDist D {x} (Metric.sphere x r) ≤
      setDist D {x} (Metric.sphere x R) := by
  conv_rhs => rw [setDist_eq_curveLenInf D hDlen]
  refine le_iInf fun x' => le_iInf fun hx' =>
    le_iInf fun y => le_iInf fun hy => le_iInf fun P =>
    le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
      le_iInf fun hPa => le_iInf fun hPb => ?_
  by_cases htop : D.len P a b = ⊤
  · rw [htop]
    exact le_top
  have hfin : D.len P a b < ⊤ := lt_top_iff_ne_top.mpr htop
  have hcont : ContinuousOn (fun t => dist (P t) x) (Icc a b) :=
    continuous_dist.comp_continuousOn
      ((hDreg P a b hP hfin).prodMk continuousOn_const)
  have ha : dist (P a) x = 0 := by rw [hPa, Set.mem_singleton_iff.mp hx', dist_self]
  have hb : dist (P b) x = R := by
    rw [hPb]
    exact Metric.mem_sphere.mp hy
  have hmem : r ∈ Icc (dist (P a) x) (dist (P b) x) := by
    rw [ha, hb]
    exact ⟨hr, hrR⟩
  obtain ⟨t, ht, htr⟩ := (intermediate_value_Icc hP.1 hcont) hmem
  have htSphere : P t ∈ Metric.sphere x r :=
    Metric.mem_sphere.mpr htr
  have hleft : setDist D {x} (Metric.sphere x r) ≤ D (P a, P t) := by
    simpa only [setDist, hPa] using
      (iInf₂_le_of_le x' hx' (iInf₂_le (P t) htSphere) :
        setDist D {x} (Metric.sphere x r) ≤ D (x', P t))
  exact hleft.trans (trace_pair_le_len D P
    ⟨a, ⟨le_rfl, hP.1⟩, rfl⟩ ⟨t, ht, rfl⟩)

/-- Finite-length version of the library's infimum-level separator splice.
Only paths with finite candidate cost need Euclidean continuity. -/
theorem two_endpoint_infimum_splice_finite_reg
    (D E : LSCMetric) (c : NNReal) (hc : 0 < c)
    (hDlen : D.IsLengthSpace) (hElen : E.IsLengthSpace)
    (hDreg : ∀ (P : ℝ → ℂ) (a b : ℝ),
      D.IsCurve P a b → D.len P a b < ⊤ → ContinuousOn P (Icc a b))
    (hEreg : ∀ (P : ℝ → ℂ) (a b : ℝ),
      E.IsCurve P a b → E.len P a b < ⊤ → ContinuousOn P (Icc a b))
    (hcomp : ∀ x y : ℂ, E (x, y) ≤ (c : ℝ≥0∞) * D (x, y))
    (u v : ℂ) (rU RU rV RV : ℝ) (AU AV : EuclideanAnnulus)
    (hrU0 : 0 ≤ rU) (hrV0 : 0 ≤ rV)
    (hrU : rU ≤ RU) (hrV : rV ≤ RV)
    (huSub : Metric.closedBall u rU ⊆ Metric.ball u RU)
    (hvSub : Metric.closedBall v rV ⊆ Metric.ball v RV)
    (hdisj : Disjoint (Metric.ball u RU) (Metric.ball v RV))
    (hAUc : AU.center = u) (hAUr : AU.innerRadius = rU)
    (hAUR : AU.outerRadius = RU)
    (hAVc : AV.center = v) (hAVr : AV.innerRadius = rV)
    (hAVR : AV.outerRadius = RV) :
    E (u, v) ≤
      (c : ℝ≥0∞) * setDist D {u} (Metric.sphere u RU) +
      (c : ℝ≥0∞) * aroundDist D AU +
      setDist E (Metric.ball u rU) (Metric.ball v rV) +
      (c : ℝ≥0∞) * aroundDist D AV +
      (c : ℝ≥0∞) * setDist D {v} (Metric.sphere v RV) := by
  let Cu := BetweenCurve D {u} (Metric.sphere u RU)
  let Cv := BetweenCurve D {v} (Metric.sphere v RV)
  let Cp := BetweenCurve E (Metric.ball u rU) (Metric.ball v rV)
  let Lu := AroundCurve D AU
  let Lv := AroundCurve D AV
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.ne'
  have hcost (qu : Cu) (lu : Lu) (p : Cp) (lv : Lv) (qv : Cv) :
      E (u, v) ≤
        (c : ℝ≥0∞) * D.len qu.path qu.startTime qu.endTime +
        (c : ℝ≥0∞) * D.len lu.path lu.startTime lu.endTime +
        E.len p.path p.startTime p.endTime +
        (c : ℝ≥0∞) * D.len lv.path lv.startTime lv.endTime +
        (c : ℝ≥0∞) * D.len qv.path qv.startTime qv.endTime := by
    by_cases hqu : D.len qu.path qu.startTime qu.endTime = ⊤
    · simp [hqu, ENNReal.mul_top hc0]
    by_cases hlu : D.len lu.path lu.startTime lu.endTime = ⊤
    · simp [hlu, ENNReal.mul_top hc0]
    by_cases hp : E.len p.path p.startTime p.endTime = ⊤
    · simp [hp]
    by_cases hlv : D.len lv.path lv.startTime lv.endTime = ⊤
    · simp [hlv, ENNReal.mul_top hc0]
    by_cases hqv : D.len qv.path qv.startTime qv.endTime = ⊤
    · simp [hqv, ENNReal.mul_top hc0]
    have hsepU : LQGMetric.Disconnects
        (lu.path '' Icc lu.startTime lu.endTime)
        (Metric.sphere u rU) (Metric.sphere u RU) := by
      have hs := (disconnects_iff_lqgMetric_disconnects
        lu.isCurve.isClosed_image).1 lu.separates
      simpa only [EuclideanAnnulus.innerBoundary, EuclideanAnnulus.outerBoundary,
        hAUc, hAUr, hAUR] using hs
    have hsepV : LQGMetric.Disconnects
        (lv.path '' Icc lv.startTime lv.endTime)
        (Metric.sphere v rV) (Metric.sphere v RV) := by
      have hs := (disconnects_iff_lqgMetric_disconnects
        lv.isCurve.isClosed_image).1 lv.separates
      simpa only [EuclideanAnnulus.innerBoundary, EuclideanAnnulus.outerBoundary,
        hAVc, hAVr, hAVR] using hs
    have hqua : qu.path qu.startTime = u := Set.mem_singleton_iff.mp qu.start_mem
    have hqva : qv.path qv.startTime = v := Set.mem_singleton_iff.mp qv.start_mem
    have hpaid := two_endpoint_paid_paths E
      p.isCurve.1 (hEreg p.path p.startTime p.endTime p.isCurve
        (lt_top_iff_ne_top.mpr hp))
      (Metric.ball_subset_closedBall p.start_mem)
      (Metric.ball_subset_closedBall p.end_mem)
      hrU0 hrV0 hrU hrV huSub hvSub hdisj
      qu.isCurve.1 qv.isCurve.1
      (hDreg qu.path qu.startTime qu.endTime qu.isCurve
        (lt_top_iff_ne_top.mpr hqu))
      (hDreg qv.path qv.startTime qv.endTime qv.isCurve
        (lt_top_iff_ne_top.mpr hqv))
      hqua hqva qu.end_mem qv.end_mem hsepU hsepV
    have hqu' := len_le_mul_of_allPairs_le D E c hcomp
      qu.path qu.startTime qu.endTime
    have hlu' := len_le_mul_of_allPairs_le D E c hcomp
      lu.path lu.startTime lu.endTime
    have hlv' := len_le_mul_of_allPairs_le D E c hcomp
      lv.path lv.startTime lv.endTime
    have hqv' := len_le_mul_of_allPairs_le D E c hcomp
      qv.path qv.startTime qv.endTime
    exact hpaid.trans (add_le_add
      (add_le_add (add_le_add (add_le_add hqu' hlu') le_rfl) hlv') hqv')
  have hInf := le_five_infima
    (fun qu : Cu => (c : ℝ≥0∞) * D.len qu.path qu.startTime qu.endTime)
    (fun lu : Lu => (c : ℝ≥0∞) * D.len lu.path lu.startTime lu.endTime)
    (fun p : Cp => E.len p.path p.startTime p.endTime)
    (fun lv : Lv => (c : ℝ≥0∞) * D.len lv.path lv.startTime lv.endTime)
    (fun qv : Cv => (c : ℝ≥0∞) * D.len qv.path qv.startTime qv.endTime)
    (E (u, v)) hcost
  have hcTop : (c : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  dsimp only [Cu, Lu, Cp, Lv, Cv] at hInf
  simp only [← ENNReal.mul_iInf_of_ne hc0 hcTop,
    ← setDist_eq_iInf_betweenCurve D hDlen,
    ← setDist_eq_iInf_betweenCurve E hElen,
    ← aroundDist_eq_iInf_aroundCurve] at hInf
  exact hInf

/-- The corrected two-scale splice: the short point-to-circle path is paid at
radius `T`, strictly beyond the outer radius `R` of the short separator. -/
theorem two_scale_splice
    (D E : LSCMetric) (c : NNReal) (hc : 0 < c)
    (hDlen : D.IsLengthSpace) (hElen : E.IsLengthSpace)
    (hDreg : ∀ (P : ℝ → ℂ) (a b : ℝ),
      D.IsCurve P a b → D.len P a b < ⊤ → ContinuousOn P (Icc a b))
    (hEreg : ∀ (P : ℝ → ℂ) (a b : ℝ),
      E.IsCurve P a b → E.len P a b < ⊤ → ContinuousOn P (Icc a b))
    (hcomp : ∀ x y : ℂ, E (x, y) ≤ (c : ℝ≥0∞) * D (x, y))
    (u v : ℂ) {r R T : ℝ}
    (hr : 0 < r) (hrR : r < R) (hRT : R ≤ T)
    (hsep : 2 * R < dist u v)
    {A B : ℝ≥0∞}
    (hpointU : setDist D {u} (Metric.sphere u T) ≤ A)
    (hpointV : setDist D {v} (Metric.sphere v T) ≤ A)
    (hloopU : aroundDist D ⟨(u, (r, R)), hr, hrR⟩ ≤ B)
    (hloopV : aroundDist D ⟨(v, (r, R)), hr, hrR⟩ ≤ B) :
    E (u, v) ≤
      (c : ℝ≥0∞) * A + (c : ℝ≥0∞) * B +
      setDist E (Metric.ball u r) (Metric.ball v r) +
      (c : ℝ≥0∞) * B + (c : ℝ≥0∞) * A := by
  have hballs : Disjoint (Metric.ball u R) (Metric.ball v R) := by
    apply Metric.ball_disjoint_ball
    linarith
  have hbase := two_endpoint_infimum_splice_finite_reg D E c hc hDlen hElen
    hDreg hEreg hcomp u v r R r R
    (⟨(u, (r, R)), hr, hrR⟩ : EuclideanAnnulus)
    (⟨(v, (r, R)), hr, hrR⟩ : EuclideanAnnulus)
    hr.le hr.le hrR.le hrR.le
    (Metric.closedBall_subset_ball hrR)
    (Metric.closedBall_subset_ball hrR)
    hballs rfl rfl rfl rfl rfl rfl
  have hcircleU : setDist D {u} (Metric.sphere u R) ≤ A :=
    (setDist_sphere_mono_radius D hDlen hDreg u (le_trans hr.le hrR.le) hRT).trans hpointU
  have hcircleV : setDist D {v} (Metric.sphere v R) ≤ A :=
    (setDist_sphere_mono_radius D hDlen hDreg v (le_trans hr.le hrR.le) hRT).trans hpointV
  apply hbase.trans
  gcongr

/-- Epigraph recovery endpoints eventually enter any fixed balls around moving
endpoints with the same Euclidean limits. -/
theorem recovery_setDist_eventually_le
    {E : ℕ → LSCMetric} {d : LSCMetric}
    (hE : Tendsto E atTop (𝓝 d))
    {u v : ℂ} {un vn : ℕ → ℂ}
    (hu : Tendsto un atTop (𝓝 u)) (hv : Tendsto vn atTop (𝓝 v))
    {r : ℝ} (hr : 0 < r) {B : ℝ≥0∞} (hB : d (u, v) < B) :
    ∀ᶠ n in atTop,
      setDist (E n) (Metric.ball (un n) r) (Metric.ball (vn n) r) < B := by
  obtain ⟨p, hp, hval⟩ := (LSCMetric.tendsto_iff.mp hE).2 (u, v)
  have hleft : Tendsto (fun n => dist (p n).1 (un n)) atTop (𝓝 (0 : ℝ)) := by
    have hp₁ : Tendsto (fun n => (p n).1) atTop (𝓝 u) :=
      (continuous_fst.tendsto (u, v)).comp hp
    simpa only [dist_self] using hp₁.dist hu
  have hright : Tendsto (fun n => dist (p n).2 (vn n)) atTop (𝓝 (0 : ℝ)) := by
    have hp₂ : Tendsto (fun n => (p n).2) atTop (𝓝 v) :=
      (continuous_snd.tendsto (u, v)).comp hp
    simpa only [dist_self] using hp₂.dist hv
  have hleft' : ∀ᶠ n in atTop, (p n).1 ∈ Metric.ball (un n) r := by
    filter_upwards [hleft.eventually (Iio_mem_nhds hr)] with n hn
    exact hn
  have hright' : ∀ᶠ n in atTop, (p n).2 ∈ Metric.ball (vn n) r := by
    filter_upwards [hright.eventually (Iio_mem_nhds hr)] with n hn
    exact hn
  have hval' : ∀ᶠ n in atTop, E n (p n) < B :=
    hval.eventually (Iio_mem_nhds hB)
  filter_upwards [hleft', hright', hval'] with n hnU hnV hnB
  exact (iInf₂_le_of_le _ hnU (iInf₂_le _ hnV)).trans_lt hnB

/-- A finite upper bound and separated Euclidean limits give a positive
limit distance. -/
theorem positive_limit_distance
    (d : LSCMetric) {u v : ℂ} {b : ℝ}
    (hb : 0 < b) (hsep : b ≤ dist u v) {M : ℝ≥0∞}
    (hfin : d (u, v) ≤ M) (hM : M < ⊤) :
    0 < d (u, v) ∧ d (u, v) < ⊤ := by
  have huv : u ≠ v := by
    intro heq
    subst v
    simp only [dist_self] at hsep
    exact (not_lt_of_ge hsep) hb
  refine ⟨pos_iff_ne_zero.mpr ?_, lt_of_le_of_lt hfin hM⟩
  intro hzero
  exact huv (d.isExtMetric.2.1 u v hzero)

/-- The final contradiction needs only an epigraph lower bound, arbitrarily
accurate eventual upper bounds for the competing distances, and positivity. -/
theorem no_persistent_ratio_gap
    {d ratio : ℝ≥0∞} (hd0 : 0 < d) (hdtop : d < ⊤) (hratio : 1 < ratio)
    {D E : ℕ → ℝ≥0∞}
    (hD : d ≤ liminf D atTop)
    (hE : ∀ ε : NNReal, 0 < ε → ∀ᶠ n in atTop, E n ≤ d + (ε : ℝ≥0∞))
    (hgap : ∀ᶠ n in atTop, ratio * D n ≤ E n) : False := by
  have hmul : ratio * d ≤ liminf (fun n => ratio * D n) atTop := by
    have h := ENNReal.le_liminf_mul (f := atTop)
      (u := fun _ : ℕ => ratio) (v := D)
    have hleft : ratio * d ≤ ratio * liminf D atTop := by gcongr
    have hright : ratio * liminf D atTop ≤
        liminf (fun n => ratio * D n) atTop := by
      have hfun : (fun _ : ℕ => ratio) * D = fun n => ratio * D n := by
        funext n
        rfl
      rw [hfun] at h
      simpa only [liminf_const] using h
    exact hleft.trans hright
  have hgaplim : liminf (fun n => ratio * D n) atTop ≤ liminf E atTop :=
    liminf_le_liminf hgap
  have hElim : liminf E atTop ≤ d := by
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    exact liminf_le_of_frequently_le' (hE ε hε).frequently
  have hstrict : d < ratio * d := by
    have := (ENNReal.mul_lt_mul_iff_right hd0.ne' hdtop.ne).2 hratio
    simpa only [mul_one, mul_comm] using this
  exact (not_le_of_gt hstrict) (hmul.trans (hgaplim.trans hElim))

/-- Endpoint regularity at a sequence of scales gives recovery of the moving
endpoint distance from the epigraph limit. The point-to-circle estimate and
the loop estimate are exactly the two halves of (6), with a general cost
sequence tending to zero. -/
theorem endpoint_regular_upper
    (D E : ℕ → LSCMetric) (d : LSCMetric)
    (hE : Tendsto E atTop (𝓝 d))
    (c : NNReal) (hc : 0 < c)
    (hDlen : ∀ n, (D n).IsLengthSpace)
    (hElen : ∀ n, (E n).IsLengthSpace)
    (hDreg : ∀ n (P : ℝ → ℂ) (a b : ℝ),
      (D n).IsCurve P a b → (D n).len P a b < ⊤ → ContinuousOn P (Icc a b))
    (hEreg : ∀ n (P : ℝ → ℂ) (a b : ℝ),
      (E n).IsCurve P a b → (E n).len P a b < ⊤ → ContinuousOn P (Icc a b))
    (hcomp : ∀ n : ℕ, ∀ x y : ℂ,
      E n (x, y) ≤ (c : ℝ≥0∞) * D n (x, y))
    (un vn : ℕ → ℂ) (u v : ℂ)
    (hu : Tendsto un atTop (𝓝 u)) (hv : Tendsto vn atTop (𝓝 v))
    (b : ℝ) (hb : 0 < b) (hsep : ∀ n, b ≤ dist (un n) (vn n))
    (s : ℕ → ℝ) (hs : Tendsto s atTop (𝓝 0))
    (hspos : ∀ j, 0 < s j) (hsone : ∀ j, s j < 1)
    (cost : ℕ → ℝ≥0∞) (hcost : Tendsto cost atTop (𝓝 0))
    (hpoint : ∀ j, ∀ᶠ n in atTop,
      setDist (D n) {un n} (Metric.sphere (un n) (s j)) ≤ cost j ∧
      setDist (D n) {vn n} (Metric.sphere (vn n) (s j)) ≤ cost j)
    (hloop : ∀ j, ∀ᶠ n in atTop,
      aroundDist (D n) (shortAnnulus (un n) (s j) (hspos j) (hsone j)) ≤ cost j ∧
      aroundDist (D n) (shortAnnulus (vn n) (s j) (hspos j) (hsone j)) ≤ cost j)
    {B : ℝ≥0∞} (hB : d (u, v) < B) :
    ∀ᶠ n in atTop, E n (un n, vn n) < B := by
  obtain ⟨B₀, hB₀lo, hB₀hi⟩ := exists_between hB
  let err (j : ℕ) : ℝ≥0∞ :=
    (c : ℝ≥0∞) * cost j + (c : ℝ≥0∞) * cost j
  have hcmul : Tendsto (fun j => (c : ℝ≥0∞) * cost j) atTop (𝓝 0) := by
    have hcTop : (c : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    have h := ((ENNReal.continuous_mul_const hcTop).tendsto (0 : ℝ≥0∞)).comp hcost
    have h' : Tendsto (fun j => cost j * (c : ℝ≥0∞)) atTop
        (𝓝 ((0 : ℝ≥0∞) * c)) := by
      simpa only [Function.comp_def] using h
    have h'' : Tendsto (fun j => cost j * (c : ℝ≥0∞)) atTop (𝓝 0) := by
      simpa only [zero_mul] using h'
    convert h'' using 1
    funext j
    exact mul_comm (c : ℝ≥0∞) (cost j)
  have herr : Tendsto err atTop (𝓝 0) := by
    simpa only [err, zero_add] using hcmul.add hcmul
  have hB₀err : Tendsto (fun j => B₀ + err j) atTop (𝓝 B₀) := by
    simpa only [add_zero] using (tendsto_const_nhds.add herr :
      Tendsto (fun j => B₀ + err j) atTop (𝓝 (B₀ + 0)))
  have hsSmall : ∀ᶠ k in atTop, s k < b / 4 :=
    hs.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < b / 4))
  obtain ⟨k, hkB, hkS⟩ : ∃ k, B₀ + err k < B ∧ s k < b / 4 := by
    exact (hB₀err.eventually (Iio_mem_nhds hB₀hi)).and hsSmall |>.exists
  have hsqrt : Tendsto (fun j => Real.sqrt (s j)) atTop (𝓝 (0 : ℝ)) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hs
    simpa only [Function.comp_def, Real.sqrt_zero] using h
  have hB₀err2 : Tendsto (fun j => B₀ + err k + err j) atTop
      (𝓝 (B₀ + err k)) := by
    simpa only [add_zero] using (tendsto_const_nhds.add herr :
      Tendsto (fun j => B₀ + err k + err j) atTop (𝓝 (B₀ + err k + 0)))
  have hsmallR : ∀ᶠ j in atTop, Real.sqrt (s j) < s k :=
    hsqrt.eventually (Iio_mem_nhds (hspos k))
  have hsepR : ∀ᶠ j in atTop, 2 * Real.sqrt (s j) < b := by
    have h2 : Tendsto (fun j => 2 * Real.sqrt (s j)) atTop (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hsqrt
    exact h2.eventually (Iio_mem_nhds hb)
  obtain ⟨j, hjB, hjR, hjSep⟩ :
      ∃ j, B₀ + err k + err j < B ∧
        Real.sqrt (s j) < s k ∧ 2 * Real.sqrt (s j) < b := by
    simpa only [and_assoc] using
      (((hB₀err2.eventually (Iio_mem_nhds hkB)).and hsmallR).and hsepR).exists
  have hrR : s j < Real.sqrt (s j) := by
    have hsq := Real.sq_sqrt (le_of_lt (hspos j))
    have ht1 : Real.sqrt (s j) < 1 := by
      nlinarith [Real.sqrt_nonneg (s j), hsone j]
    nlinarith [mul_pos (Real.sqrt_pos.mpr (hspos j)) (sub_pos.mpr ht1)]
  have hrec := recovery_setDist_eventually_le hE hu hv (hspos j) hB₀lo
  filter_upwards [hpoint k, hloop j, hrec] with n hp hl hmid
  have hsplit := two_scale_splice (D n) (E n) c hc
    (hDlen n) (hElen n) (hDreg n) (hEreg n) (hcomp n)
    (un n) (vn n) (hspos j) hrR hjR.le
    (lt_of_lt_of_le hjSep (hsep n)) hp.1 hp.2 hl.1 hl.2
  calc
    E n (un n, vn n) ≤
        (c : ℝ≥0∞) * cost k + (c : ℝ≥0∞) * cost j +
        setDist (E n) (Metric.ball (un n) (s j)) (Metric.ball (vn n) (s j)) +
        (c : ℝ≥0∞) * cost j + (c : ℝ≥0∞) * cost k := hsplit
    _ ≤ (c : ℝ≥0∞) * cost k + (c : ℝ≥0∞) * cost j +
        B₀ + (c : ℝ≥0∞) * cost j + (c : ℝ≥0∞) * cost k := by gcongr
    _ = B₀ + err k + err j := by dsimp [err]; ac_rfl
    _ < B := hjB

/-- Convergent-endpoint form of Lemma 4.1, with formula (6) represented by a
general vanishing cost sequence. The next theorem specializes the costs to
`M s_j^θ`. -/
theorem no_ratio_gap_convergent
    (D E : ℕ → LSCMetric) (d : LSCMetric)
    (hD : Tendsto D atTop (𝓝 d)) (hE : Tendsto E atTop (𝓝 d))
    (c : NNReal) (hc : 0 < c)
    (hDlen : ∀ n, (D n).IsLengthSpace)
    (hElen : ∀ n, (E n).IsLengthSpace)
    (hDreg : ∀ n (P : ℝ → ℂ) (a b : ℝ),
      (D n).IsCurve P a b → (D n).len P a b < ⊤ → ContinuousOn P (Icc a b))
    (hEreg : ∀ n (P : ℝ → ℂ) (a b : ℝ),
      (E n).IsCurve P a b → (E n).len P a b < ⊤ → ContinuousOn P (Icc a b))
    (hcomp : ∀ n : ℕ, ∀ x y : ℂ,
      E n (x, y) ≤ (c : ℝ≥0∞) * D n (x, y))
    (un vn : ℕ → ℂ) (u v : ℂ)
    (hu : Tendsto un atTop (𝓝 u)) (hv : Tendsto vn atTop (𝓝 v))
    (b : ℝ) (hb : 0 < b) (hsep : ∀ n, b ≤ dist (un n) (vn n))
    (M : ℝ≥0∞) (hM : M < ⊤) (hbound : ∀ n, D n (un n, vn n) ≤ M)
    (s : ℕ → ℝ) (hs : Tendsto s atTop (𝓝 0))
    (hspos : ∀ j, 0 < s j) (hsone : ∀ j, s j < 1)
    (cost : ℕ → ℝ≥0∞) (hcost : Tendsto cost atTop (𝓝 0))
    (hpoint : ∀ j, ∀ᶠ n in atTop,
      setDist (D n) {un n} (Metric.sphere (un n) (s j)) ≤ cost j ∧
      setDist (D n) {vn n} (Metric.sphere (vn n) (s j)) ≤ cost j)
    (hloop : ∀ j, ∀ᶠ n in atTop,
      aroundDist (D n) (shortAnnulus (un n) (s j) (hspos j) (hsone j)) ≤ cost j ∧
      aroundDist (D n) (shortAnnulus (vn n) (s j) (hspos j) (hsone j)) ≤ cost j)
    (ratio : ℝ≥0∞) (hratio : 1 < ratio) :
    ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ n, ratio * D (φ n) (un (φ n), vn (φ n)) ≤
        E (φ n) (un (φ n), vn (φ n)) := by
  have hpair : Tendsto (fun n => (un n, vn n)) atTop (𝓝 (u, v)) :=
    hu.prodMk_nhds hv
  have hlow : d (u, v) ≤ liminf (fun n => D n (un n, vn n)) atTop :=
    (LSCMetric.tendsto_iff.mp hD).1 _ _ hpair
  have hupperM : liminf (fun n => D n (un n, vn n)) atTop ≤ M :=
    liminf_le_of_frequently_le' (Frequently.of_forall hbound)
  have hseplimit : b ≤ dist u v := by
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds (hu.dist hv) hsep
  obtain ⟨hdpos, hdfin⟩ :=
    positive_limit_distance d hb hseplimit (hlow.trans hupperM) hM
  have hEupper (ε : NNReal) (hε : 0 < ε) :
      ∀ᶠ n in atTop, E n (un n, vn n) ≤ d (u, v) + (ε : ℝ≥0∞) := by
    have hε' : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) := by exact_mod_cast hε
    have hB : d (u, v) < d (u, v) + (ε : ℝ≥0∞) := by
      have h := (ENNReal.add_lt_add_iff_left hdfin.ne).2 hε'
      simpa only [add_zero, zero_add] using h
    exact (endpoint_regular_upper D E d hE c hc hDlen hElen
      hDreg hEreg hcomp un vn u v hu hv b hb hsep s hs hspos hsone
      cost hcost hpoint hloop hB).mono fun _ h => h.le
  rintro ⟨φ, hφ, hgap⟩
  have hDφ : Tendsto (fun n => D (φ n)) atTop (𝓝 d) :=
    hD.comp hφ.tendsto_atTop
  have hpairφ : Tendsto (fun n => (un (φ n), vn (φ n))) atTop (𝓝 (u, v)) :=
    hpair.comp hφ.tendsto_atTop
  have hlowφ : d (u, v) ≤
      liminf (fun n => D (φ n) (un (φ n), vn (φ n))) atTop :=
    (LSCMetric.tendsto_iff.mp hDφ).1 _ _ hpairφ
  have hEupperφ (ε : NNReal) (hε : 0 < ε) :
      ∀ᶠ n in atTop,
        E (φ n) (un (φ n), vn (φ n)) ≤ d (u, v) + (ε : ℝ≥0∞) :=
    hφ.tendsto_atTop.eventually (hEupper ε hε)
  exact no_persistent_ratio_gap hdpos hdfin hratio hlowφ hEupperφ
    (Eventually.of_forall hgap)

/-- The bound in formula (6) vanishes along the prescribed sequence. -/
theorem powerCost_tendsto (M : NNReal) {θ : ℝ} (hθ : 0 < θ)
    {s : ℕ → ℝ} (hs : Tendsto s atTop (𝓝 0)) :
    Tendsto (fun j => ENNReal.ofReal ((M : ℝ) * (s j) ^ θ)) atTop
      (𝓝 (0 : ℝ≥0∞)) := by
  have hpow : Tendsto (fun j => (s j) ^ θ) atTop (𝓝 (0 : ℝ)) := by
    have h := (Real.continuousAt_rpow_const 0 θ (Or.inr hθ.le)).tendsto.comp hs
    simpa only [Function.comp_def, Real.zero_rpow hθ.ne'] using h
  have hreal : Tendsto (fun j => (M : ℝ) * (s j) ^ θ) atTop
      (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hpow
  simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hreal

/-- Lemma 4.1 with compact moving endpoints and the quantitative condition
(6), expressed using the existing `LSCMetric`, `setDist`, and `aroundDist`.
The conclusion excludes every strictly increasing bad subsequence. -/
theorem deterministic_recovery_ratio
    (D E : ℕ → LSCMetric) (d : LSCMetric)
    (hD : Tendsto D atTop (𝓝 d)) (hE : Tendsto E atTop (𝓝 d))
    (c : NNReal) (hc : 0 < c)
    (hDlen : ∀ n, (D n).IsLengthSpace)
    (hElen : ∀ n, (E n).IsLengthSpace)
    (hDreg : ∀ n (P : ℝ → ℂ) (a b : ℝ),
      (D n).IsCurve P a b → (D n).len P a b < ⊤ → ContinuousOn P (Icc a b))
    (hEreg : ∀ n (P : ℝ → ℂ) (a b : ℝ),
      (E n).IsCurve P a b → (E n).len P a b < ⊤ → ContinuousOn P (Icc a b))
    (hcomp : ∀ n : ℕ, ∀ x y : ℂ,
      D n (x, y) ≤ (c : ℝ≥0∞) * E n (x, y) ∧
      E n (x, y) ≤ (c : ℝ≥0∞) * D n (x, y))
    (un vn : ℕ → ℂ) (K : Set ℂ) (hK : IsCompact K)
    (hKend : ∀ n, un n ∈ K ∧ vn n ∈ K)
    (b : ℝ) (hb : 0 < b) (hsep : ∀ n, b ≤ dist (un n) (vn n))
    (M : NNReal) (hbound : ∀ n, D n (un n, vn n) ≤ (M : ℝ≥0∞))
    (θ : ℝ) (hθ : 0 < θ)
    (s : ℕ → ℝ) (hs : Tendsto s atTop (𝓝 0))
    (hspos : ∀ j, 0 < s j) (hsone : ∀ j, s j < 1)
    (hpoint : ∀ j, ∀ᶠ n in atTop,
      setDist (D n) {un n} (Metric.sphere (un n) (s j)) ≤
        ENNReal.ofReal ((M : ℝ) * (s j) ^ θ) ∧
      setDist (D n) {vn n} (Metric.sphere (vn n) (s j)) ≤
        ENNReal.ofReal ((M : ℝ) * (s j) ^ θ))
    (hloop : ∀ j, ∀ᶠ n in atTop,
      aroundDist (D n) (shortAnnulus (un n) (s j) (hspos j) (hsone j)) ≤
        ENNReal.ofReal ((M : ℝ) * (s j) ^ θ) ∧
      aroundDist (D n) (shortAnnulus (vn n) (s j) (hspos j) (hsone j)) ≤
        ENNReal.ofReal ((M : ℝ) * (s j) ^ θ))
    (ratio : ℝ≥0∞) (hratio : 1 < ratio) :
    ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ n, ratio * D (φ n) (un (φ n), vn (φ n)) ≤
        E (φ n) (un (φ n), vn (φ n)) := by
  rintro ⟨φ, hφ, hbad⟩
  have hpairK : ∀ n, (un (φ n), vn (φ n)) ∈ K ×ˢ K :=
    fun n => ⟨(hKend (φ n)).1, (hKend (φ n)).2⟩
  obtain ⟨p, hpK, ψ, hψ, hpconv⟩ :=
    (hK.prod hK).tendsto_subseq hpairK
  let χ : ℕ → ℕ := φ ∘ ψ
  have hχ : StrictMono χ := hφ.comp hψ
  have hχt : Tendsto χ atTop atTop := hχ.tendsto_atTop
  have hu : Tendsto (fun n => un (χ n)) atTop (𝓝 p.1) :=
    (continuous_fst.tendsto p).comp hpconv
  have hv : Tendsto (fun n => vn (χ n)) atTop (𝓝 p.2) :=
    (continuous_snd.tendsto p).comp hpconv
  have hresult := no_ratio_gap_convergent
    (fun n => D (χ n)) (fun n => E (χ n)) d
    (hD.comp hχt) (hE.comp hχt) c hc
    (fun n => hDlen (χ n)) (fun n => hElen (χ n))
    (fun n => hDreg (χ n)) (fun n => hEreg (χ n))
    (fun n x y => (hcomp (χ n) x y).2)
    (fun n => un (χ n)) (fun n => vn (χ n)) p.1 p.2
    hu hv b hb (fun n => hsep (χ n))
    (M : ℝ≥0∞) ENNReal.coe_lt_top (fun n => hbound (χ n))
    s hs hspos hsone
    (fun j => ENNReal.ofReal ((M : ℝ) * (s j) ^ θ))
    (powerCost_tendsto M hθ hs)
    (fun j => hχt.eventually (hpoint j))
    (fun j => hχt.eventually (hloop j)) ratio hratio
  apply hresult
  refine ⟨id, strictMono_id, ?_⟩
  intro n
  exact hbad (ψ n)

/-- Lemma 4.1 in the paper's `1 + η` form. -/
theorem deterministic_recovery
    (D E : ℕ → LSCMetric) (d : LSCMetric)
    (hD : Tendsto D atTop (𝓝 d)) (hE : Tendsto E atTop (𝓝 d))
    (c : NNReal) (hc : 0 < c)
    (hDlen : ∀ n, (D n).IsLengthSpace)
    (hElen : ∀ n, (E n).IsLengthSpace)
    (hDreg : ∀ n (P : ℝ → ℂ) (a b : ℝ),
      (D n).IsCurve P a b → (D n).len P a b < ⊤ → ContinuousOn P (Icc a b))
    (hEreg : ∀ n (P : ℝ → ℂ) (a b : ℝ),
      (E n).IsCurve P a b → (E n).len P a b < ⊤ → ContinuousOn P (Icc a b))
    (hcomp : ∀ n : ℕ, ∀ x y : ℂ,
      D n (x, y) ≤ (c : ℝ≥0∞) * E n (x, y) ∧
      E n (x, y) ≤ (c : ℝ≥0∞) * D n (x, y))
    (un vn : ℕ → ℂ) (K : Set ℂ) (hK : IsCompact K)
    (hKend : ∀ n, un n ∈ K ∧ vn n ∈ K)
    (b : ℝ) (hb : 0 < b) (hsep : ∀ n, b ≤ dist (un n) (vn n))
    (M : NNReal) (hbound : ∀ n, D n (un n, vn n) ≤ (M : ℝ≥0∞))
    (θ : ℝ) (hθ : 0 < θ)
    (s : ℕ → ℝ) (hs : Tendsto s atTop (𝓝 0))
    (hspos : ∀ j, 0 < s j) (hsone : ∀ j, s j < 1)
    (hpoint : ∀ j, ∀ᶠ n in atTop,
      setDist (D n) {un n} (Metric.sphere (un n) (s j)) ≤
        ENNReal.ofReal ((M : ℝ) * (s j) ^ θ) ∧
      setDist (D n) {vn n} (Metric.sphere (vn n) (s j)) ≤
        ENNReal.ofReal ((M : ℝ) * (s j) ^ θ))
    (hloop : ∀ j, ∀ᶠ n in atTop,
      aroundDist (D n) (shortAnnulus (un n) (s j) (hspos j) (hsone j)) ≤
        ENNReal.ofReal ((M : ℝ) * (s j) ^ θ) ∧
      aroundDist (D n) (shortAnnulus (vn n) (s j) (hspos j) (hsone j)) ≤
        ENNReal.ofReal ((M : ℝ) * (s j) ^ θ))
    (η : ℝ) (hη : 0 < η) :
    ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ n, ENNReal.ofReal (1 + η) *
        D (φ n) (un (φ n), vn (φ n)) ≤
        E (φ n) (un (φ n), vn (φ n)) := by
  have hratio : (1 : ℝ≥0∞) < ENNReal.ofReal (1 + η) := by
    have hpos : (0 : ℝ) < 1 + η := by linarith
    have hreal : (1 : ℝ) < 1 + η := by linarith
    simpa only [ENNReal.ofReal_one] using
      (ENNReal.ofReal_lt_ofReal_iff hpos).2 hreal
  exact deterministic_recovery_ratio D E d hD hE c hc hDlen hElen
    hDreg hEreg hcomp un vn K hK hKend b hb hsep M hbound θ hθ
    s hs hspos hsone hpoint hloop _ hratio


end SupercriticalConformalCovariance.Recovery
