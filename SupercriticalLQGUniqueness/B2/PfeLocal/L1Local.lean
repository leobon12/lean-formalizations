import SupercriticalLQGUniqueness.B2.PfeLocal.L1Prob
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalizedLFPP
import SupercriticalLQGUniqueness.B2.PfeAxioms.RecenteredGeometrySB
import LQGMetric.Papers.DFGPS.L2_17CoreB
import LQGMetric.Field.CircleAvgRate

 













set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.PfeLocal

 

theorem l1_acrossCost_sub_const (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) (z : ℂ)
    (r : ℝ) (t : ℝ) (i : ℂ) :
    l1AcrossCost ξ a (φ - ContinuousMap.const ℂ t) z r i =
      ENNReal.ofReal (Real.exp (ξ * (-t))) * l1AcrossCost ξ a φ z r i := by
  unfold l1AcrossCost
  have : (⇑(φ - ContinuousMap.const ℂ t) : ℂ → ℝ) = fun x => φ x + (-t) := by
    funext x; simp [sub_eq_add_neg]
  rw [this, B2.DG20Pt.crossLenIn_add_const]
  ring

theorem l1_aroundCost_sub_const (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) (z : ℂ)
    (r : ℝ) (t : ℝ) (k : Fin 4) :
    l1AroundCost ξ a (φ - ContinuousMap.const ℂ t) z r k =
      ENNReal.ofReal (Real.exp (ξ * (-t))) * l1AroundCost ξ a φ z r k := by
  unfold l1AroundCost
  have : (⇑(φ - ContinuousMap.const ℂ t) : ℂ → ℝ) = fun x => φ x + (-t) := by
    funext x; simp [sub_eq_add_neg]
  rw [this, B2.DG20Pt.crossLenIn_add_const]
  ring

 

theorem l1_heatGood_sub_const (ξ : ℝ) (a b : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) (q : Finset ℂ)
    (z : ℂ) (r C c t : ℝ) :
    l1HeatGood ξ a b φ q z r C c ↔
      l1HeatGood ξ a b (φ - ContinuousMap.const ℂ t) q z r C (c - t) := by
  have hE0 : ENNReal.ofReal (Real.exp (ξ * (-t))) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have e1 : ∀ x : ℝ, ENNReal.ofReal (x * Real.exp (ξ * (c - t))) =
      ENNReal.ofReal (Real.exp (ξ * (-t))) * ENNReal.ofReal (x * Real.exp (ξ * c)) := by
    intro x
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    rw [show ξ * (c - t) = ξ * c + ξ * (-t) by ring, Real.exp_add]
    ring
  unfold l1HeatGood
  simp only [l1_acrossCost_sub_const, l1_aroundCost_sub_const, e1]
  simp_rw [ENNReal.mul_lt_mul_iff_right hE0 ENNReal.ofReal_ne_top]

 
theorem l1_across_domain_subset (q : Finset ℂ) (hq : ∀ i ∈ q, i ∈ l1Shell)
    (z : ℂ) {r : ℝ} (hr : 0 < r) {i : ℂ} (hi : i ∈ q) {x : ℂ}
    (hx : x ∈ closedBall (z + (r : ℂ) * i) (r * l1d)) {ρ : ℝ} (hρ : ρ ≤ r / 16) :
    closedBall x ρ ⊆ {w | r / 4 < ‖w - z‖ ∧ ‖w - z‖ < 3 * r} := by
  intro w hw
  exact l1_net_ball_subset q hq z hr hi
    (mem_cthickening_of_dist_le w x (r / 16) _ hx ((mem_closedBall.1 hw).trans hρ))

theorem l1_around_domain_subset (z : ℂ) {r : ℝ} (hr : 0 < r) (k : Fin 4) {x : ℂ}
    (hx : x ∈ l1AroundOpen z r k) {ρ : ℝ} (hρ : ρ ≤ r / 16) :
    closedBall x ρ ⊆ {w | r / 4 < ‖w - z‖ ∧ ‖w - z‖ < 3 * r} := by
  have hx' := Strong.cfgOpens_subset_toSet (outerAnnulus z r hr) k
    (l1AroundClosed_subset_cfgOpens z r hr k (l1AroundOpen_subset_closed z r k hx))
  rw [EuclideanAnnulus.toSet_eq] at hx'
  obtain ⟨h1, h2⟩ := hx'
  change r < dist x z at h1
  change dist x z < 2 * r at h2
  intro w hw
  have hw' := mem_closedBall.1 hw
  have t1 : dist x z ≤ dist x w + dist w z := dist_triangle _ _ _
  have t2 : dist w z ≤ dist w x + dist x z := dist_triangle _ _ _
  rw [dist_comm] at hw'
  have hc := dist_comm w x
  show r / 4 < ‖w - z‖ ∧ ‖w - z‖ < 3 * r
  rw [← dist_eq_norm]
  constructor <;> linarith

theorem l1_domains_subset_ball (q : Finset ℂ) (hq : ∀ i ∈ q, i ∈ l1Shell)
    (z : ℂ) {r : ℝ} (hr : 0 < r) :
    (∀ i ∈ q, closedBall (z + (r : ℂ) * i) (r * l1d) ⊆ ball z (3 * r)) ∧
      ∀ k : Fin 4, l1AroundOpen z r k ⊆ ball z (3 * r) := by
  constructor
  · intro i hi x hx
    have := l1_across_domain_subset q hq z hr hi hx (ρ := 0) (by positivity) (mem_closedBall_self le_rfl)
    rw [mem_ball, dist_eq_norm]; exact this.2
  · intro k x hx
    have := l1_around_domain_subset z hr k hx (ρ := 0) (by positivity) (mem_closedBall_self le_rfl)
    rw [mem_ball, dist_eq_norm]; exact this.2

theorem l1_ofReal_div_lt {s e : ℝ} (_hs : 0 < s) (he : 0 < e) {X Y : ℝ≥0∞}
    (hX : ENNReal.ofReal s < X) (hXY : X ≤ ENNReal.ofReal e * Y) :
    ENNReal.ofReal (s / e) < Y := by
  have he0 : ENNReal.ofReal e ≠ 0 := (ENNReal.ofReal_pos.2 he).ne'
  rw [← ENNReal.mul_lt_mul_iff_right he0 ENNReal.ofReal_ne_top,
    ← ENNReal.ofReal_mul he.le, mul_div_cancel₀ s he.ne']
  exact hX.trans_le hXY

theorem l1_lt_ofReal_mul {e t : ℝ} (he : 0 < e) {X Y : ℝ≥0∞}
    (hXY : X ≤ ENNReal.ofReal e * Y) (hY : Y < ENNReal.ofReal t) :
    X < ENNReal.ofReal (e * t) := by
  have he0 : ENNReal.ofReal e ≠ 0 := (ENNReal.ofReal_pos.2 he).ne'
  rw [ENNReal.ofReal_mul he.le]
  exact hXY.trans_lt ((ENNReal.mul_lt_mul_iff_right he0 ENNReal.ofReal_ne_top).2 hY)

 

theorem l1_heatGood_mono (ξ : ℝ) (a b : Set.Ioi (0 : ℝ)) (φ φ' : C(ℂ, ℝ)) (q : Finset ℂ)
    (hq : ∀ i ∈ q, i ∈ l1Shell) (z : ℂ) {r : ℝ} (hr : 0 < r) {C : ℝ} (hC : 0 < C)
    (c δ : ℝ) (hφ : ∀ x ∈ ball z (3 * r), |φ x - φ' x| ≤ δ)
    (h : l1HeatGood ξ a b φ q z r C c) :
    l1HeatGood ξ a b φ' q z r (C * Real.exp (|ξ| * δ)) c := by
  have ha : (0 : ℝ) < a := a.2
  have hb : (0 : ℝ) < b := b.2
  obtain ⟨hdom1, hdom2⟩ := l1_domains_subset_ball q hq z hr
  have hE := Real.exp_pos (|ξ| * δ)
  have hκ : 0 < r * b / a * Real.exp (ξ * c) := by positivity
  refine ⟨fun i hi => ?_, fun k => ?_⟩
  · have hle : l1AcrossCost ξ a φ z r i ≤
        ENNReal.ofReal (Real.exp (|ξ| * δ)) * l1AcrossCost ξ a φ' z r i := by
      unfold l1AcrossCost
      calc _ ≤ ENNReal.ofReal (a : ℝ)⁻¹ * (ENNReal.ofReal (Real.exp (|ξ| * δ)) *
            crossLenIn ξ φ' (closedBall (z + (r : ℂ) * i) (r * l1d))
              (sphere (z + (r : ℂ) * i) (r * l1d / 16))
              (sphere (z + (r : ℂ) * i) (3 * (r * l1d) / 4))) :=
          mul_le_mul_right (crossLenIn_le_of_abs_sub_le fun x hx => hφ x (hdom1 i hi hx)) _
        _ = _ := by ring
    have := l1_ofReal_div_lt (by positivity) hE (h.1 i hi) hle
    convert this using 2
    field_simp
  · have hle : l1AroundCost ξ a φ' z r k ≤
        ENNReal.ofReal (Real.exp (|ξ| * δ)) * l1AroundCost ξ a φ z r k := by
      unfold l1AroundCost
      calc _ ≤ ENNReal.ofReal ((a : ℝ)⁻¹) * (ENNReal.ofReal (Real.exp (|ξ| * δ)) *
            crossLenIn ξ φ (l1AroundOpen z r k) {l1Start z r k} {l1End z r k}) :=
          mul_le_mul_right (crossLenIn_le_of_abs_sub_le fun x hx => by
            rw [abs_sub_comm]; exact hφ x (hdom2 k hx)) _
        _ = _ := by ring
    have := l1_lt_ofReal_mul hE hle (h.2 k)
    convert this using 2
    ring

 

 
def l1LocGood (ξ : ℝ) (a b : Set.Ioi (0 : ℝ)) (ε : ℝ) (hε : 0 < ε) (y : DistC)
    (q : Finset ℂ) (z : ℂ) (r C : ℝ) : Prop :=
  l1HeatGood ξ a b (LQGMetric.DFGPS.L217.locMollifyC ε hε y) q z r C (circleAvg y r z)

theorem l1_tsupport_bumpTest (n : ℕ) (x : ℂ) :
    tsupport (bumpTest n x : ℂ → ℝ) ⊆ closedBall x ((2 : ℝ)⁻¹ ^ n) := by
  change tsupport (((⟨(2 : ℝ)⁻¹ ^ (n + 1), (2 : ℝ)⁻¹ ^ n, by positivity,
      pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (Nat.lt_succ_self n)⟩ :
      ContDiffBump x).normed volume : ℂ → ℝ)) ⊆ _
  rw [ContDiffBump.tsupport_normed_eq]

 
theorem l1_circleAvg_congr {O : TopologicalSpace.Opens ℂ} {y y' : DistC}
    (he : restrictTo O y = restrictTo O y') {r : ℝ} {z : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hO : ∀ x ∈ sphere z |r|, closedBall x δ ⊆ O) :
    circleAvg y r z = circleAvg y' r z := by
  unfold circleAvg limUnder
  congr 1
  refine Filter.map_congr ?_
  have hlim : Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  filter_upwards [(tendsto_order.1 hlim).2 δ hδ] with n hn
  refine Real.circleAverage_congr_sphere fun x hx => ?_
  exact LQGMetric.DFGPS.L217.apply_eq_of_restrictTo_eq he _
    ((l1_tsupport_bumpTest n x).trans ((closedBall_subset_closedBall hn.le).trans (hO x hx)))

theorem l1_mem_annulus_iff (z : ℂ) (r₁ r₂ : ℝ) (w : ℂ) :
    w ∈ (Blueprint.annulus z r₁ r₂ : Set ℂ) ↔ r₁ < ‖w - z‖ ∧ ‖w - z‖ < r₂ := Iff.rfl

 

theorem l1_locGood_congr (ξ : ℝ) (a b : Set.Ioi (0 : ℝ)) {ε : ℝ} (hε : 0 < ε)
    (q : Finset ℂ) (hq : ∀ i ∈ q, i ∈ l1Shell) (z : ℂ) {r : ℝ} (hr : 0 < r) (C : ℝ)
    (hsq : Real.sqrt ε ≤ r / 16) {y y' : DistC}
    (he : restrictTo (Blueprint.annulus z (r / 4) (3 * r)) y =
      restrictTo (Blueprint.annulus z (r / 4) (3 * r)) y') :
    l1LocGood ξ a b ε hε y q z r C ↔ l1LocGood ξ a b ε hε y' q z r C := by
  have hmoll : ∀ x : ℂ, closedBall x (Real.sqrt ε) ⊆ {w | r / 4 < ‖w - z‖ ∧ ‖w - z‖ < 3 * r} →
      LQGMetric.DFGPS.L217.locMollifyC ε hε y x = LQGMetric.DFGPS.L217.locMollifyC ε hε y' x :=
    fun x hx => LQGMetric.DFGPS.L217.apply_eq_of_restrictTo_eq he _
      ((LQGMetric.LFPP.tsupport_locTest_subset ε hε x).trans hx)
  have hc : circleAvg y r z = circleAvg y' r z := by
    refine l1_circleAvg_congr he (δ := r / 2) (by positivity) fun x hx w hw => ?_
    rw [abs_of_pos hr, mem_sphere] at hx
    have hw' := mem_closedBall.1 hw
    rw [l1_mem_annulus_iff, ← dist_eq_norm]
    have t1 : dist x z ≤ dist x w + dist w z := dist_triangle _ _ _
    have t2 : dist w z ≤ dist w x + dist x z := dist_triangle _ _ _
    have := dist_comm w x
    constructor <;> linarith
  unfold l1LocGood l1HeatGood
  rw [hc]
  have hA : ∀ i ∈ q, l1AcrossCost ξ a (LQGMetric.DFGPS.L217.locMollifyC ε hε y) z r i =
      l1AcrossCost ξ a (LQGMetric.DFGPS.L217.locMollifyC ε hε y') z r i := by
    intro i hi
    unfold l1AcrossCost
    rw [crossLenIn_congr' fun x hx => hmoll x
      (l1_across_domain_subset q hq z hr hi hx hsq)]
  have hO : ∀ k : Fin 4, l1AroundCost ξ a (LQGMetric.DFGPS.L217.locMollifyC ε hε y) z r k =
      l1AroundCost ξ a (LQGMetric.DFGPS.L217.locMollifyC ε hε y') z r k := by
    intro k
    unfold l1AroundCost
    rw [crossLenIn_congr' fun x hx => hmoll x (l1_around_domain_subset z hr k hx hsq)]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i hi => (hA i hi) ▸ h1 i hi, fun k => (hO k) ▸ h2 k⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i hi => (hA i hi).symm ▸ h1 i hi, fun k => (hO k).symm ▸ h2 k⟩

theorem l1_measurable_acrossCost (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) {W : DistC → C(ℂ, ℝ)}
    (hW : Measurable W) (z : ℂ) (r : ℝ) (i : ℂ) :
    Measurable fun g => l1AcrossCost ξ a (W g) z r i :=
  measurable_const.mul (DDDF.measurable_crossLenIn (isCompact_closedBall _ _)
    (Y := fun x g => W g x) (fun g => (W g).continuous)
    (fun x => (continuous_eval_const x).measurable.comp hW))

theorem l1_measurable_aroundCost (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) {W : DistC → C(ℂ, ℝ)}
    (hW : Measurable W) (z : ℂ) (r : ℝ) (k : Fin 4) :
    Measurable fun g => l1AroundCost ξ a (W g) z r k :=
  measurable_const.mul (B2.DG20Pt.measurable_crossLenIn_open ξ
    ⟨l1AroundOpen z r k, isOpen_l1AroundOpen z r k⟩ _ _ (fun x g => W g x)
    (fun g => (W g).continuous) (fun x => (continuous_eval_const x).measurable.comp hW))

theorem l1_measurableSet_heatGood (ξ : ℝ) (a b : Set.Ioi (0 : ℝ)) {W : DistC → C(ℂ, ℝ)}
    (hW : Measurable W) (q : Finset ℂ) (z : ℂ) (r C : ℝ) {c : DistC → ℝ} (hc : Measurable c) :
    MeasurableSet {g | l1HeatGood ξ a b (W g) q z r C (c g)} := by
  have hthr : ∀ x : ℝ, Measurable fun g => ENNReal.ofReal (x * Real.exp (ξ * c g)) :=
    fun x => ENNReal.measurable_ofReal.comp
      (measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul hc)))
  have e : {g | l1HeatGood ξ a b (W g) q z r C (c g)} =
      (⋂ i ∈ (q : Set ℂ), {g | ENNReal.ofReal (C⁻¹ * (r * b / a) * Real.exp (ξ * c g)) <
        l1AcrossCost ξ a (W g) z r i}) ∩
        ⋂ k : Fin 4, {g | l1AroundCost ξ a (W g) z r k <
          ENNReal.ofReal (C * (r * b / a) * Real.exp (ξ * c g))} := by
    ext g; simp [l1HeatGood]
  rw [e]
  exact (MeasurableSet.biInter q.countable_toSet fun i _ =>
      measurableSet_lt (hthr _) (l1_measurable_acrossCost ξ a hW z r i)).inter
    (MeasurableSet.iInter fun k => measurableSet_lt (l1_measurable_aroundCost ξ a hW z r k)
      (hthr _))

theorem l1_measurableSet_locGood (ξ : ℝ) (a b : Set.Ioi (0 : ℝ)) {ε : ℝ} (hε : 0 < ε)
    (q : Finset ℂ) (z : ℂ) (r C : ℝ) :
    MeasurableSet {y | l1LocGood ξ a b ε hε y q z r C} :=
  l1_measurableSet_heatGood ξ a b (LQGMetric.DFGPS.L217.measurable_locMollifyC ε hε) q z r C
    (measurable_circleAvg_left r z)

 

theorem l1_measurableSet_fieldSigma_of_local {Ω : Type} [MeasurableSpace Ω]
    (S : Set DistC) (hS : MeasurableSet S) (O : TopologicalSpace.Opens ℂ)
    (hloc : ∀ y y' : DistC, restrictTo O y = restrictTo O y' → (y ∈ S ↔ y' ∈ S))
    (Y : Ω → DistC) : MeasurableSet[Blueprint.fieldSigma Y O] (Y ⁻¹' S) := by
  have hle := LQGMetric.DFGPS.L217.comap_le_fieldSigma_of_local
    (Φ := S.indicator (fun _ => (1 : ℝ))) (measurable_const.indicator hS) O
    (fun y y' he => by
      by_cases hy : y ∈ S
      · rw [indicator_of_mem hy, indicator_of_mem ((hloc y y' he).1 hy)]
      · rw [indicator_of_notMem hy,
          indicator_of_notMem (fun h' => hy ((hloc y y' he).2 h'))]) Y
  apply hle
  refine ⟨{1}, measurableSet_singleton 1, ?_⟩
  ext ω
  simp only [mem_preimage, mem_singleton_iff]
  by_cases hy : Y ω ∈ S
  · simp [hy]
  · simp [hy]

 
theorem l1_measurableSet_fieldSigma_locGood {Ω : Type} [MeasurableSpace Ω]
    (ξ : ℝ) (a b : Set.Ioi (0 : ℝ)) {ε : ℝ} (hε : 0 < ε)
    (q : Finset ℂ) (hq : ∀ i ∈ q, i ∈ l1Shell) (z : ℂ) {r : ℝ} (hr : 0 < r) (C : ℝ)
    (hsq : Real.sqrt ε ≤ r / 16) (Y : Ω → DistC) :
    MeasurableSet[Blueprint.fieldSigma Y (Blueprint.annulus z (r / 4) (3 * r))]
      {ω | l1LocGood ξ a b ε hε (Y ω) q z r C} :=
  l1_measurableSet_fieldSigma_of_local _ (l1_measurableSet_locGood ξ a b hε q z r C) _
    (fun _ _ he => l1_locGood_congr ξ a b hε q hq z hr C hsq he) Y

end SupercriticalLQGUniqueness.B2.PfeLocal
