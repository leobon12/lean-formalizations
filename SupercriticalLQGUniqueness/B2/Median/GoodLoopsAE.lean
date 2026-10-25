import SupercriticalLQGUniqueness.B2.Median.GoodLoopsLocal
import SupercriticalLQGUniqueness.B2.Median.SurgeryPred
import SupercriticalLQGUniqueness.B2.DG20Lim.DyadicLatticeBorelCantelli
import SupercriticalLQGUniqueness.B2.DG20Lim.DyadicGoodSurrounds

 












set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Median

open SupercriticalLQGUniqueness.Uniqueness
open B2.DG20Lim

 
def latC (K : ℕ) (v : ℤ × ℤ) : ℂ :=
  ⟨((dyadicLatticeCenter K v).1 : ℝ), ((dyadicLatticeCenter K v).2 : ℝ)⟩

 
theorem ae_lattice_loopGood
    (ξ : Set.Ioi (0 : ℝ)) (D : LQGMetric.DistC → LSCMetric)
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hweak : B2.Iface.IsPfeWeakMetric ξ D c)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → LQGMetric.DistC) (hh : IsNormalizedWholePlaneGFF h P) :
    ∃ C : ℝ, 0 < C ∧ ∀ᵐ ω ∂P, ∀ R₀ : ℕ, ∀ᶠ K in atTop, ∀ v ∈ dyadicLatticeBox R₀ K,
      ∃ i ∈ sparseDyadicIndices K,
        LoopGood C (D (h ω)) (latC K v) (loopScale i) (loopScale_pos i) := by
  obtain ⟨p, c₀, hp0, hp1, hc0, hiter⟩ := loopGood_site_iteration 120 (by norm_num)
  obtain ⟨C, hC, hprob⟩ := exists_loopGood_prob ξ D c hweak P h hh p hp1
  refine ⟨C, hC, ?_⟩
  rw [ae_all_iff]
  intro R₀
  let E : ℕ → Set Ω := fun K => {ω | ∃ v ∈ dyadicLatticeBox R₀ K, ∀ i ∈ sparseDyadicIndices K,
    ¬ LoopGood C (D (h ω)) (latC K v) (loopScale i) (loopScale_pos i)}
  have hE : ∀ K, 12 ≤ K →
      P (E K) ≤ ((dyadicLatticeBox R₀ K).card : ℝ≥0∞) *
        ENNReal.ofReal (c₀ * Real.exp (-(120 : ℝ) * (sparseDyadicIndices K).card)) := by
    intro K hK
    apply measure_exists_site_bad_le P R₀ K
      (fun v => {ω | ∀ i ∈ sparseDyadicIndices K,
        ¬ LoopGood C (D (h ω)) (latC K v) (loopScale i) (loopScale_pos i)})
    intro v _
    exact hiter P h hh ξ D c hweak C (latC K v) (sparseDyadicIndices K)
      (sparseDyadicIndices_nonempty hK)
      (fun j hj => by
        have := (Finset.mem_Icc.mp hj).1
        omega)
      (fun j _ => hprob (latC K v) (loopScale j) (loopScale_pos j))
  have hev := ae_eventually_not_dyadic_bad_of_bound P E R₀ c₀ hc0.le hE
  filter_upwards [hev] with ω hω
  filter_upwards [hω] with K hK v hv
  by_contra hno
  push Not at hno
  exact hK ⟨v, hv, hno⟩

 
theorem sum_crossIn_le_len (d : LSCMetric) (cs : ℕ → ℂ) (rs : ℕ → ℝ)
    (hrs : ∀ j, 0 < rs j)
    (hnest : ∀ j, closedBall (cs (j + 1)) (2 * rs (j + 1)) ⊆ ball (cs j) (rs j)) :
    ∀ (N : ℕ) (P : ℝ → ℂ) (a b : ℝ), d.IsCurve P a b → ContinuousOn P (Icc a b) →
      (0 < N → dist (P a) (cs (N - 1)) < rs (N - 1)) →
      (∀ j < N, 2 * rs j < dist (P b) (cs j)) →
      ∑ j ∈ Finset.range N, crossIn d (cs j) (rs j) ≤ d.len P a b := by
  intro N
  induction N with
  | zero =>
    intro P a b _ _ _ _
    simp
  | succ N ih =>
    intro P a b hP hcont hstart hend
    have hs : dist (P a) (cs N) < rs N := by simpa using hstart (Nat.succ_pos N)
    have he : 2 * rs N < dist (P b) (cs N) := hend N (Nat.lt_succ_self N)
    obtain ⟨σ, τ, haσ, hστ, hτb, hσd, hτd, hbetween⟩ :=
      SupercriticalLQGUniqueness.crossing_extract hP.1 hcont (by linarith [hrs N]) hs he
    have hcross : crossIn d (cs N) (rs N) ≤ d.len P σ τ := by
      unfold crossIn
      apply compactPathInf_le_of_curve d _ _ _ P σ τ
        ⟨hστ.le, hP.2.mono (Icc_subset_Icc haσ hτb)⟩
      · intro u hu
        have := hbetween u hu
        rw [dist_eq_norm] at this
        exact ⟨this.1, this.2⟩
      · exact mem_sphere.mpr hσd
      · exact mem_sphere.mpr hτd
    have hrest : ∑ j ∈ Finset.range N, crossIn d (cs j) (rs j) ≤ d.len P τ b := by
      apply ih P τ b ⟨hτb, hP.2.mono (Icc_subset_Icc (haσ.trans hστ.le) le_rfl)⟩
        (hcont.mono (Icc_subset_Icc (haσ.trans hστ.le) le_rfl))
      · intro hN
        have h1 : P τ ∈ closedBall (cs (N - 1 + 1)) (2 * rs (N - 1 + 1)) := by
          rw [Nat.sub_add_cancel hN]; exact mem_closedBall.mpr hτd.le
        exact mem_ball.mp (hnest (N - 1) h1)
      · intro j hj
        exact hend j (Nat.lt_succ_of_lt hj)
    rw [Finset.sum_range_succ]
    calc ∑ j ∈ Finset.range N, crossIn d (cs j) (rs j) + crossIn d (cs N) (rs N)
        ≤ d.len P τ b + d.len P σ τ := add_le_add hrest hcross
      _ = d.len P σ b := by
          rw [add_comm]
          exact (LQGMetric.MetricGeometry.curveLength_add (d.pt ∘ P) hστ.le hτb)
      _ ≤ d.len P a b := LQGMetric.MetricGeometry.curveLength_mono _ haσ le_rfl

theorem loopScale_le_of_sparse {K i M : ℕ} (hi : i ∈ sparseDyadicIndices K) (hKM : 2 * M ≤ K) :
    loopScale i ≤ 1 / (2 : ℝ) ^ M := by
  have hsc := sparseDyadicIndices_scale hi
  rw [loopScale_eq]
  exact one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num) (by omega))

theorem loopScale_ge_of_sparse {K i : ℕ} (hi : i ∈ sparseDyadicIndices K) :
    1 / (2 : ℝ) ^ K ≤ loopScale i := by
  have hsc := sparseDyadicIndices_scale hi
  rw [loopScale_eq]
  exact one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num) hsc.2)

theorem latC_dist_lt (K : ℕ) (z : ℂ) :
    dist z (latC K (dyadicRoundCenter K z)) < 1 / (2 : ℝ) ^ (K + 3) := by
  have h := dyadicRoundCenter_dist_lt K z
  have : (2 : ℝ) / (2 : ℝ) ^ (K + 4) = 1 / (2 : ℝ) ^ (K + 3) := by
    rw [pow_succ]; field_simp
  rw [this] at h
  exact h

 
theorem goodLoops_of_lattice (d : LSCMetric) (C : ℝ) (hC : 0 < C)
    (hgood : ∀ R₀ : ℕ, ∀ᶠ K in atTop, ∀ v ∈ dyadicLatticeBox R₀ K,
      ∃ i ∈ sparseDyadicIndices K, LoopGood C d (latC K v) (loopScale i) (loopScale_pos i)) :
    GoodLoops d := by
  intro P a b hP hbdd hfin hne ρ η hρ hη
  classical
  set z := P a with hz
  have hcont : ContinuousOn P (Icc a b) :=
    Uniqueness.Toolkit.PathInfimum.continuousOn_euclidean_of_bounded d P hP hbdd
  set δb := dist (P b) z with hδb
  have hδb0 : 0 < δb := dist_pos.mpr (Ne.symm hne)
  
  obtain ⟨R₀, hR₀⟩ := exists_nat_gt ‖z‖
  obtain ⟨K₀, hK₀⟩ := (hgood (R₀ + 1)).exists_forall_of_atTop
  have hsite : ∀ K, K₀ ≤ K → ∃ i ∈ sparseDyadicIndices K,
      LoopGood C d (latC K (dyadicRoundCenter K z)) (loopScale i) (loopScale_pos i) :=
    fun K hK => hK₀ K hK _ (dyadicRoundCenter_mem_box R₀ K z hR₀)
  choose! ifun hifun hgoodf using hsite
  
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (show 0 < min ρ δb / 3 by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  have hM' : 3 * (1 / (2 : ℝ) ^ M) < min ρ δb := by
    rw [one_div_pow] at hM; linarith
  
  set L : ℝ := (d.len P a b).toReal with hL
  obtain ⟨N, hN⟩ := exists_nat_gt (C * L / η)
  
  let Ks : ℕ → ℕ := fun j => Nat.rec (max K₀ (max (2 * M) 12)) (fun _ K => 2 * K + 4) j
  have hKs0 : Ks 0 = max K₀ (max (2 * M) 12) := rfl
  have hKsS : ∀ j, Ks (j + 1) = 2 * Ks j + 4 := fun j => rfl
  have hKsge : ∀ j, max K₀ (max (2 * M) 12) ≤ Ks j := by
    intro j
    induction j with
    | zero => exact le_rfl
    | succ j ih => rw [hKsS]; omega
  have hK0 : ∀ j, K₀ ≤ Ks j := fun j => le_trans (le_max_left _ _) (hKsge j)
  have hKM : ∀ j, 2 * M ≤ Ks j := fun j =>
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (hKsge j)
  let cs : ℕ → ℂ := fun j => latC (Ks j) (dyadicRoundCenter (Ks j) z)
  let rs : ℕ → ℝ := fun j => loopScale (ifun (Ks j))
  have hrs : ∀ j, 0 < rs j := fun j => loopScale_pos _
  have hmem : ∀ j, ifun (Ks j) ∈ sparseDyadicIndices (Ks j) := fun j => hifun _ (hK0 j)
  have hdist : ∀ j, dist z (cs j) < rs j := by
    intro j
    have h1 := latC_dist_lt (Ks j) z
    have h2 := loopScale_ge_of_sparse (hmem j)
    have h3 : 1 / (2 : ℝ) ^ (Ks j + 3) ≤ 1 / (2 : ℝ) ^ (Ks j) :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
    exact lt_of_lt_of_le h1 (h3.trans h2)
  have hsmall : ∀ j, rs j ≤ 1 / (2 : ℝ) ^ M := fun j => loopScale_le_of_sparse (hmem j) (hKM j)
  have hnest : ∀ j, closedBall (cs (j + 1)) (2 * rs (j + 1)) ⊆ ball (cs j) (rs j) := by
    intro j w hw
    rw [mem_closedBall] at hw
    rw [mem_ball]
    set K := Ks j
    have hK' : Ks (j + 1) = 2 * K + 4 := hKsS j
    have hr1 : rs (j + 1) ≤ 1 / (2 : ℝ) ^ (K + 2) :=
      loopScale_le_of_sparse (hmem (j + 1)) (by rw [hK']; omega)
    have hr0 : 1 / (2 : ℝ) ^ K ≤ rs j := loopScale_ge_of_sparse (hmem j)
    have hd1 : dist z (cs (j + 1)) < 1 / (2 : ℝ) ^ (K + 3) := by
      have := latC_dist_lt (Ks (j + 1)) z
      refine lt_of_lt_of_le this (one_div_le_one_div_of_le (by positivity)
        (pow_le_pow_right₀ (by norm_num) (by rw [hK']; omega)))
    have hd0 : dist z (cs j) < 1 / (2 : ℝ) ^ (K + 3) := latC_dist_lt K z
    have hp : (0 : ℝ) < 1 / (2 : ℝ) ^ K := by positivity
    have e2 : 1 / (2 : ℝ) ^ (K + 2) = (1 / (2 : ℝ) ^ K) / 4 := by
      rw [pow_add]; field_simp; norm_num
    have e3 : 1 / (2 : ℝ) ^ (K + 3) = (1 / (2 : ℝ) ^ K) / 8 := by
      rw [pow_add]; field_simp; norm_num
    have htri := dist_triangle4 w (cs (j + 1)) z (cs j)
    rw [dist_comm (cs (j + 1)) z] at htri
    rw [e2] at hr1
    rw [e3] at hd1 hd0
    linarith
  have hstartN : 0 < N → dist (P a) (cs (N - 1)) < rs (N - 1) := fun _ => hdist (N - 1)
  have hendN : ∀ j < N, 2 * rs j < dist (P b) (cs j) := by
    intro j _
    have h1 := hdist j
    have h2 := hsmall j
    have h3 := dist_triangle (P b) (cs j) z
    rw [dist_comm (cs j) z] at h3
    have h4 : 3 * rs j < δb := by
      have := (min_le_right ρ δb)
      linarith
    linarith
  have hsum := sum_crossIn_le_len d cs rs hrs hnest N P a b hP hcont hstartN hendN
  
  have hexists : ∃ j < N, aroundDist d (loopAnn (cs j) (rs j) (hrs j)) < ENNReal.ofReal η := by
    by_contra hall
    push Not at hall
    have hlow : ∀ j ∈ Finset.range N, ENNReal.ofReal (η / C) ≤ crossIn d (cs j) (rs j) := by
      intro j hj
      have h1 := hall j (Finset.mem_range.mp hj)
      have h2 : aroundDist d (loopAnn (cs j) (rs j) (hrs j)) ≤
          ENNReal.ofReal C * crossIn d (cs j) (rs j) := hgoodf _ (hK0 j)
      have h3 : ENNReal.ofReal η ≤ ENNReal.ofReal C * crossIn d (cs j) (rs j) := h1.trans h2
      have hC0 : ENNReal.ofReal C ≠ 0 := (ENNReal.ofReal_pos.mpr hC).ne'
      have hCt : ENNReal.ofReal C ≠ ∞ := ENNReal.ofReal_ne_top
      rw [ENNReal.ofReal_div_of_pos hC]
      rw [ENNReal.div_le_iff hC0 hCt, mul_comm]
      exact h3
    have hsum' : (N : ℝ≥0∞) * ENNReal.ofReal (η / C) ≤ d.len P a b := by
      calc (N : ℝ≥0∞) * ENNReal.ofReal (η / C)
          = ∑ j ∈ Finset.range N, ENNReal.ofReal (η / C) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ ∑ j ∈ Finset.range N, crossIn d (cs j) (rs j) := Finset.sum_le_sum hlow
        _ ≤ d.len P a b := hsum
    rw [← ENNReal.ofReal_toReal hfin, ← hL, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg N)] at hsum'
    have hreal := (ENNReal.ofReal_le_ofReal_iff (by rw [hL]; exact ENNReal.toReal_nonneg)).mp hsum'
    rw [div_lt_iff₀ hη] at hN
    have : (N : ℝ) * (η / C) * C = N * η := by field_simp
    nlinarith
  obtain ⟨j, _, hj⟩ := hexists
  refine ⟨cs j, rs j, hrs j, ?_, hdist j, ?_⟩
  · have := hsmall j
    have := (min_le_left ρ δb)
    linarith
  · unfold aroundDist at hj
    simp only [iInf_lt_iff] at hj
    obtain ⟨Lc, s, t, hLc, hLin, hLdis, hLlen⟩ := hj
    refine ⟨Lc, s, t, hLc, ?_, hLdis, hLlen⟩
    intro u hu
    have := hLin u hu
    rw [loopAnn_toSet] at this
    exact this

 
theorem ae_goodLoops
    (ξ : Set.Ioi (0 : ℝ)) (D : LQGMetric.DistC → LSCMetric)
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hweak : B2.Iface.IsPfeWeakMetric ξ D c)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → LQGMetric.DistC) (hh : IsNormalizedWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, GoodLoops (D (h ω)) := by
  obtain ⟨C, hC, hae⟩ := ae_lattice_loopGood ξ D c hweak P h hh
  filter_upwards [hae] with ω hω
  exact goodLoops_of_lattice (D (h ω)) C hC hω

end SupercriticalLQGUniqueness.B2.Median
