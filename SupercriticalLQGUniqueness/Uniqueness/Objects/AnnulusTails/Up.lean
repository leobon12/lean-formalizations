import SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails.Low




 


















set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails

open LQGMetric (DistC)

 
theorem exists_loop_of_aroundDist_lt (D : LSCMetric) (w : ℂ) (t : Ioi (0 : ℝ)) {X : ℝ≥0∞}
    (hX : aroundDist D (ann12 w t) < X) :
    ∃ (P : ℝ → ℂ) (a b : ℝ), D.IsCurve P a b ∧ P '' Icc a b ⊆ Objects.CorrectedEvent.ann w t (2 * t) ∧
      LQGMetric.Disconnects (P '' Icc a b) (sphere w t) (sphere w (2 * t)) ∧
      D.len P a b < X := by
  unfold aroundDist at hX
  simp only [iInf_lt_iff] at hX
  obtain ⟨P, a, b, hP, hPA, hdis, hlen⟩ := hX
  refine ⟨P, a, b, hP, ?_, ?_, hlen⟩
  · rintro x ⟨τ, hτ, rfl⟩
    have h := hPA τ hτ
    rw [EuclideanAnnulus.toSet_eq] at h
    simp only [ann12_center, ann12_innerRadius, ann12_outerRadius, mem_ofPred_eq] at h
    exact h
  · have h := (disconnects_iff_lqgMetric_disconnects hP.isClosed_image).1 hdis
    have hin : (ann12 w t).innerBoundary = sphere w t := by
      change sphere (ann12 w t).center (ann12 w t).innerRadius = _
      rw [ann12_center, ann12_innerRadius]
    have hout : (ann12 w t).outerBoundary = sphere w (2 * t) := by
      change sphere (ann12 w t).center (ann12 w t).outerRadius = _
      rw [ann12_center, ann12_outerRadius]
    rw [hin, hout] at h
    exact h

 

theorem upper_scale_arith {ξ Q lam q s : ℝ} {n j : ℕ} (hξ : 0 < ξ) (hQ : 0 < Q)
    (hlam : 0 < lam) (hs : 0 < s) {ht hs' : ℝ} (hgap : |ht - hs'| < q * n * lam) :
    (Real.exp (-(j : ℝ) * lam) * s) ^ (ξ * Q) * Real.exp (ξ * ht) ≤
      Real.exp (ξ * q * n * lam) * (s ^ (ξ * Q) * Real.exp (ξ * hs')) := by
  have hpow : (Real.exp (-(j : ℝ) * lam) * s) ^ (ξ * Q) =
      Real.exp (-(j : ℝ) * lam * (ξ * Q)) * s ^ (ξ * Q) := by
    rw [Real.mul_rpow (Real.exp_pos _).le hs.le, ← Real.exp_mul]
  rw [hpow]
  have hspos : 0 < s ^ (ξ * Q) := Real.rpow_pos_of_pos hs _
  have h1 : Real.exp (-(j : ℝ) * lam * (ξ * Q)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ (j : ℝ) * lam * (ξ * Q) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg j) hlam.le) (mul_pos hξ hQ).le
    linarith
  have h2 : Real.exp (ξ * ht) ≤ Real.exp (ξ * q * n * lam) * Real.exp (ξ * hs') := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := (abs_lt.1 hgap).2
    have := mul_le_mul_of_nonneg_left this.le hξ.le
    linarith
  calc Real.exp (-(j : ℝ) * lam * (ξ * Q)) * s ^ (ξ * Q) * Real.exp (ξ * ht)
      ≤ 1 * s ^ (ξ * Q) * (Real.exp (ξ * q * n * lam) * Real.exp (ξ * hs')) := by
        gcongr
    _ = Real.exp (ξ * q * n * lam) * (s ^ (ξ * Q) * Real.exp (ξ * hs')) := by ring

 


theorem around_upper_of_good (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q) (D : DistC → LSCMetric)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) {M q : ℝ} (hM0 : 0 < M) {n : ℕ}
    (hgeo : 4 * Real.exp (-(n * Real.log 16)) < b - a) (s : Ioi (0 : ℝ)) (y : ℂ) {Nm : ℕ}
    (hNm0 : 0 < Nm) (hNmgt : Real.pi * ((a + b) / 2) * Real.exp (2 * n * Real.log 16) < Nm)
    (g : DistC)
    (hgood : ∀ w ∈ gridSet y ((a + b) / 2 * s) Nm, ∃ j ∈ Finset.Icc n (2 * n),
      g ∈ goodAnn ξ Q D M w (scale16 s j))
    (hgap : ∀ w ∈ gridSet y ((a + b) / 2 * s) Nm, ∀ j ∈ Finset.Icc n (2 * n),
      |LQGMetric.circleAvg g (scale16 s j) w - LQGMetric.circleAvg g s y| <
        q * n * Real.log 16) :
    Objects.CorrectedEvent.around (D g) y (a * s) (b * s) ≤
      ENNReal.ofReal (4 * M * (gridSet y ((a + b) / 2 * s) Nm).card *
        Real.exp (ξ * q * n * Real.log 16)) * nrm ξ Q g s y := by
  set lam : ℝ := Real.log 16 with hlamdef
  have hlam : 0 < lam := Real.log_pos (by norm_num)
  have hξ : (0 : ℝ) < ξ := ξ.2
  have hs : (0 : ℝ) < s := s.2
  set m : ℝ := (a + b) / 2 with hmdef
  have hm0 : 0 < m := by rw [hmdef]; linarith
  set W : Finset ℂ := gridSet y (m * s) Nm with hWdef
  choose! jw hjwJ hjwG using hgood
  let t : ℂ → Ioi (0 : ℝ) := fun w => scale16 s (jw w)
  have hbounds : ∀ w ∈ W, Real.exp (-(2 * n * lam)) * s ≤ (t w : ℝ) ∧
      (t w : ℝ) ≤ Real.exp (-(n * lam)) * s := fun w hw =>
    scale16_mem_bounds s (Finset.mem_Icc.1 (hjwJ w hw)).1 (Finset.mem_Icc.1 (hjwJ w hw)).2
  
  let X : ℂ → ℝ := fun w => 2 * M * ((t w : ℝ) ^ ((ξ : ℝ) * Q) *
    Real.exp ((ξ : ℝ) * LQGMetric.circleAvg g (t w) w))
  have hXpos : ∀ w, 0 < X w := fun w => by
    have ht0 : (0 : ℝ) < t w := (t w).2
    exact mul_pos (mul_pos two_pos hM0) (mul_pos (Real.rpow_pos_of_pos ht0 _) (Real.exp_pos _))
  have hloop : ∀ w ∈ W, ∃ (P : ℝ → ℂ) (a b : ℝ), (D g).IsCurve P a b ∧
      P '' Icc a b ⊆ Objects.CorrectedEvent.ann w (t w) (2 * t w) ∧
      LQGMetric.Disconnects (P '' Icc a b) (sphere w (t w)) (sphere w (2 * t w)) ∧
      (D g).len P a b < ENNReal.ofReal (X w) := by
    intro w hw
    apply exists_loop_of_aroundDist_lt (D g) w (t w)
    refine lt_of_le_of_lt (goodAnn_around_upper (hjwG w hw)) ?_
    rw [ENNReal.ofReal_lt_ofReal_iff (hXpos w)]
    have hN : 0 < (t w : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * LQGMetric.circleAvg g (t w) w) :=
      mul_pos (Real.rpow_pos_of_pos (t w).2 _) (Real.exp_pos _)
    change M * _ < 2 * M * _
    nlinarith
  choose! P a' b' hP hPA hPD hPlen using hloop
  have hcov : ∀ x ∈ sphere y (m * s), ∃ w ∈ W, dist x w < t w := by
    intro x hx
    obtain ⟨w, hwW, hdw⟩ := exists_gridSet_near y (mul_pos hm0 hs) hNm0 (mem_sphere.1 hx)
    refine ⟨w, hwW, lt_of_le_of_lt hdw (lt_of_lt_of_le ?_ (hbounds w hwW).1)⟩
    rw [div_lt_iff₀ (by exact_mod_cast hNm0)]
    have hE : Real.exp (-(2 * n * lam)) * Real.exp (2 * n * lam) = 1 := by
      rw [← Real.exp_add]; simp
    have hprod : 0 < Real.exp (-(2 * n * lam)) * s := mul_pos (Real.exp_pos _) hs
    calc Real.pi * (m * s) = Real.pi * m * Real.exp (2 * n * lam) *
          (Real.exp (-(2 * n * lam)) * s) := by
          rw [show Real.pi * m * Real.exp (2 * n * lam) * (Real.exp (-(2 * n * lam)) * s) =
            Real.pi * m * s * (Real.exp (-(2 * n * lam)) * Real.exp (2 * n * lam)) by ring, hE]
          ring
      _ < Nm * (Real.exp (-(2 * n * lam)) * s) := mul_lt_mul_of_pos_right hNmgt hprod
      _ = Real.exp (-(2 * n * lam)) * s * Nm := by ring
  have hin : ∀ w ∈ W, closedBall w (2 * t w) ⊆ Objects.CorrectedEvent.ann y (a * s) (b * s) := by
    intro w hw x hx
    have hwy : dist w y = m * s := mem_gridSet_dist y (mul_pos hm0 hs).le Nm hw
    have hxw : dist x w ≤ 2 * t w := mem_closedBall.1 hx
    have ht2 : 2 * (t w : ℝ) < (b - a) / 2 * s := by
      have h1 := (hbounds w hw).2
      have h2 : 2 * (Real.exp (-(n * lam)) * s) < (b - a) / 2 * s := by
        have := mul_lt_mul_of_pos_right hgeo hs
        linarith
      linarith
    have hm : m * s = a * s + (b - a) / 2 * s := by rw [hmdef]; ring
    have hm' : m * s = b * s - (b - a) / 2 * s := by rw [hmdef]; ring
    constructor
    · have := dist_triangle w x y
      rw [dist_comm w x] at this
      linarith
    · have := dist_triangle x w y
      linarith
  have h₁ : a * s < m * s := by rw [hmdef]; nlinarith
  have h₂ : m * s < b * s := by rw [hmdef]; nlinarith
  have hcover := around_le_of_loop_cover (D g) h₁ h₂ (mul_pos hm0 hs) W (fun w => t w)
    (fun w _ => (t w).2) P a' b' hP hPA hPD hcov hin
  
  have hXle : ∀ w ∈ W, X w ≤ 2 * M * (Real.exp ((ξ : ℝ) * q * n * lam) *
      ((s : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * LQGMetric.circleAvg g s y))) := by
    intro w hw
    have harith := upper_scale_arith (ξ := (ξ : ℝ)) (Q := Q) (lam := lam) (q := q) (s := s)
      (n := n) (j := jw w) hξ hQ hlam hs (hgap w hw (jw w) (hjwJ w hw))
    rw [← scale16_eq_exp s (jw w)] at harith
    change 2 * M * ((scale16 s (jw w) : ℝ) ^ ((ξ : ℝ) * Q) *
      Real.exp ((ξ : ℝ) * LQGMetric.circleAvg g (scale16 s (jw w)) w)) ≤ _
    exact mul_le_mul_of_nonneg_left harith (by positivity)
  set B : ℝ := 2 * M * (Real.exp ((ξ : ℝ) * q * n * lam) *
      ((s : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * LQGMetric.circleAvg g s y))) with hBdef
  have hB0 : 0 ≤ B := by positivity
  calc Objects.CorrectedEvent.around (D g) y (a * s) (b * s)
      ≤ 2 * ∑ w ∈ W, (D g).len (P w) (a' w) (b' w) := hcover
    _ ≤ 2 * ∑ _w ∈ W, ENNReal.ofReal B := by
        gcongr with w hw
        exact (hPlen w hw).le.trans (ENNReal.ofReal_le_ofReal (hXle w hw))
    _ = ENNReal.ofReal (4 * M * W.card * Real.exp ((ξ : ℝ) * q * n * lam)) *
          nrm ξ Q g s y := by
        rw [sum_const_ofReal, nrm, ← ENNReal.ofReal_mul (by positivity)]
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
          ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        rw [hBdef]
        ring

 


theorem around_upper_tail_dyadic (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) {a b : ℝ} (ha : 0 < a) (hab : a < b) (κ : ℝ) (hκ : 0 < κ) :
    ∃ (n₀ : ℕ) (C : ℝ), 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
        ∀ n : ℕ, n₀ ≤ n → ∀ (s : Ioi (0 : ℝ)) (y : ℂ),
          P {ω | ENNReal.ofReal (Real.exp (n * Real.log 16 *
              (3 + ξ * Real.sqrt (6 * (κ + 3))))) * nrm ξ Q (h ω) s y <
              Objects.CorrectedEvent.around (D (h ω)) y (a * s) (b * s)} ≤
            ENNReal.ofReal (C * Real.exp (-(κ * n * Real.log 16))) := by
  have hlam : 0 < Real.log 16 := Real.log_pos (by norm_num)
  have hξ : (0 : ℝ) < ξ := ξ.2
  set m : ℝ := (a + b) / 2 with hmdef
  have hm0 : 0 < m := by rw [hmdef]; linarith
  obtain ⟨M, c, hM1, hc0, hgood⟩ :=
    goodAnn_no_good_scale ξ Q hQ D hD ((κ + 2) * Real.log 16) (by positivity)
  have hM0 : 0 < M := lt_of_lt_of_le one_pos hM1
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1
    (eventually_dyadic_conditions (g := b - a) (L₁ := 2 * Real.log (m + 1))
      (L₂ := Real.log (4 * M * (Real.pi * m + 3))) (by linarith) hlam)
  refine ⟨n₀, (Real.pi * m + 3) * (c + 2), by positivity, ?_⟩
  intro Ω _ P _ h hh n hn s y
  obtain ⟨hn1, hgeo, hvarn, hMn⟩ := hn₀ n hn
  have hs : (0 : ℝ) < s := s.2
  obtain ⟨hNm0, hNmgt, hcardW⟩ := mesh_card_bound m hm0 n y (m * s)
  set Nm : ℕ := ⌈Real.pi * m * Real.exp (2 * n * Real.log 16)⌉₊ + 1 with hNmdef
  set W : Finset ℂ := gridSet y (m * s) Nm with hWdef
  set J : Finset ℕ := Finset.Icc n (2 * n) with hJdef
  have hJne : J.Nonempty := ⟨n, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩⟩
  have hJ1 : ∀ j ∈ J, 1 ≤ j := fun j hj => le_trans hn1 (Finset.mem_Icc.1 hj).1
  have hJcard : J.card = n + 1 := by rw [hJdef, Nat.card_Icc]; omega
  set q : ℝ := Real.sqrt (6 * (κ + 3)) with hqdef
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  let F : ℂ → Set Ω := fun w => {ω | ∀ j ∈ J, h ω ∉ goodAnn ξ Q D M w (scale16 s j)}
  let G : ℂ → ℕ → Set Ω := fun w j => {ω | q * n * Real.log 16 ≤
    |LQGMetric.circleAvg (h ω) (scale16 s j) w - LQGMetric.circleAvg (h ω) s y|}
  
  have habsorb : 4 * M * (W.card : ℝ) * Real.exp ((ξ : ℝ) * q * n * Real.log 16) ≤
      Real.exp (n * Real.log 16 * (3 + ξ * q)) := by
    have h1 : 4 * M * (Real.pi * m + 3) ≤ Real.exp (n * Real.log 16) := by
      rw [← Real.exp_log (by positivity : 0 < 4 * M * (Real.pi * m + 3))]
      exact Real.exp_le_exp.mpr hMn
    calc 4 * M * (W.card : ℝ) * Real.exp ((ξ : ℝ) * q * n * Real.log 16)
        ≤ 4 * M * ((Real.pi * m + 3) * Real.exp (2 * n * Real.log 16)) *
            Real.exp ((ξ : ℝ) * q * n * Real.log 16) := by gcongr
      _ = 4 * M * (Real.pi * m + 3) *
            (Real.exp (2 * n * Real.log 16) * Real.exp ((ξ : ℝ) * q * n * Real.log 16)) := by ring
      _ ≤ Real.exp (n * Real.log 16) *
            (Real.exp (2 * n * Real.log 16) * Real.exp ((ξ : ℝ) * q * n * Real.log 16)) := by
          gcongr
      _ = Real.exp (n * Real.log 16 * (3 + ξ * q)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
  have hsub : {ω | ENNReal.ofReal (Real.exp (n * Real.log 16 * (3 + ξ * q))) *
      nrm ξ Q (h ω) s y < Objects.CorrectedEvent.around (D (h ω)) y (a * s) (b * s)} ⊆
      (⋃ w ∈ W, F w) ∪ ⋃ w ∈ W, ⋃ j ∈ J, G w j := by
    intro ω hω
    by_contra hno
    simp only [mem_union, mem_iUnion₂, not_or, not_exists] at hno
    obtain ⟨hnoF, hnoG⟩ := hno
    have hch : ∀ w ∈ W, ∃ j ∈ J, h ω ∈ goodAnn ξ Q D M w (scale16 s j) := by
      intro w hw
      by_contra hc
      push Not at hc
      exact hnoF w hw hc
    have hgap : ∀ w ∈ W, ∀ j ∈ J, |LQGMetric.circleAvg (h ω) (scale16 s j) w -
        LQGMetric.circleAvg (h ω) s y| < q * n * Real.log 16 := by
      intro w hw j hj
      have := hnoG w hw j hj
      simp only [G, mem_ofPred_eq, not_le] at this
      exact this
    have hup := around_upper_of_good ξ Q hQ D ha hab hM0 hgeo s y hNm0
      (by rw [← hmdef]; exact hNmgt) (h ω) hch hgap
    have hle : Objects.CorrectedEvent.around (D (h ω)) y (a * s) (b * s) ≤
        ENNReal.ofReal (Real.exp (n * Real.log 16 * (3 + ξ * q))) * nrm ξ Q (h ω) s y :=
      hup.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal habsorb) le_rfl)
    exact absurd hω (not_lt.2 hle)
  have hF : ∀ w, P (F w) ≤ ENNReal.ofReal (c * Real.exp (-((κ + 2) * Real.log 16) * (n + 1))) := by
    intro w
    have := hgood P h hh w s J hJne hJ1
    rw [hJcard] at this
    push_cast at this
    exact this
  have hGb : ∀ w ∈ W, ∀ j ∈ J, P (G w j) ≤
      ENNReal.ofReal (2 * Real.exp (-((κ + 3) * n * Real.log 16))) := by
    intro w hw j hj
    have hjn := Finset.mem_Icc.1 hj
    exact gauss_pair_bound hh.1 hκ hm0 hn1 hjn.1 hjn.2 hvarn s
      (mem_gridSet_dist y (mul_pos hm0 hs).le Nm hw)
  have hsum := dyadic_sum_bound hκ hc0.le (by positivity : (0 : ℝ) ≤ Real.pi * m + 3)
    (n := n) hcardW
  calc P {ω | ENNReal.ofReal (Real.exp (n * Real.log 16 * (3 + ξ * q))) *
        nrm ξ Q (h ω) s y < Objects.CorrectedEvent.around (D (h ω)) y (a * s) (b * s)}
      ≤ P ((⋃ w ∈ W, F w) ∪ ⋃ w ∈ W, ⋃ j ∈ J, G w j) := measure_mono hsub
    _ ≤ P (⋃ w ∈ W, F w) + P (⋃ w ∈ W, ⋃ j ∈ J, G w j) := measure_union_le _ _
    _ ≤ ∑ w ∈ W, P (F w) + ∑ w ∈ W, ∑ j ∈ J, P (G w j) := by
        gcongr
        · exact measure_biUnion_finset_le _ _
        · refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun w _ => ?_)
          exact measure_biUnion_finset_le _ _
    _ ≤ ∑ _w ∈ W, ENNReal.ofReal (c * Real.exp (-((κ + 2) * Real.log 16) * (n + 1))) +
          ∑ w ∈ W, ∑ _j ∈ J, ENNReal.ofReal (2 * Real.exp (-((κ + 3) * n * Real.log 16))) :=
        add_le_add (Finset.sum_le_sum fun w _ => hF w)
          (Finset.sum_le_sum fun w hw => Finset.sum_le_sum fun j hj => hGb w hw j hj)
    _ = ENNReal.ofReal (W.card * (c * Real.exp (-((κ + 2) * Real.log 16) * (n + 1))) +
          W.card * ((n + 1) * (2 * Real.exp (-((κ + 3) * n * Real.log 16))))) := by
        rw [sum_const_ofReal, Finset.sum_congr rfl (fun w _ => sum_const_ofReal J _),
          sum_const_ofReal, hJcard, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        push_cast
        rfl
    _ ≤ ENNReal.ofReal ((Real.pi * m + 3) * (c + 2) * Real.exp (-(κ * n * Real.log 16))) :=
        ENNReal.ofReal_le_ofReal hsum

end SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails
