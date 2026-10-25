import SupercriticalLQGUniqueness.Uniqueness.Positivity.SignDuality.SignDuality
import SupercriticalLQGUniqueness.Uniqueness.Positivity.Grids.AX11Grid
import SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX12




 





set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Set Topology
open LQGMetric (DistC circleAvg)
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Positivity.Assembly

private theorem rate_base_lt_one : (4 : ℝ) * Real.exp (-2) < 1 := by
  have hh : (3 / 2 : ℝ) ≤ Real.exp (1 / 2) := by
    have h := Real.add_one_le_exp (1 / 2 : ℝ)
    norm_num at h ⊢
    exact h
  have h : (2 : ℝ) < Real.exp 1 := by
    have heq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [← heq]
    nlinarith [Real.exp_pos (1 / 2)]
  have he : (4 : ℝ) < Real.exp 2 := by
    have h2 : Real.exp 1 * Real.exp 1 = Real.exp 2 := by
      rw [← Real.exp_add]
      norm_num
    have hp : 0 < Real.exp 1 := Real.exp_pos _
    rw [← h2]
    nlinarith [Real.exp_pos 1]
  rw [Real.exp_neg]
  change (4 : ℝ) / Real.exp 2 < 1
  exact (div_lt_iff₀ (Real.exp_pos 2)).mpr (by linarith)

private theorem eventually_rate_small (c₀ : ℝ) :
    ∀ᶠ K : ℕ in atTop,
      (2 : ℝ) ^ 26 * c₀ * Real.exp (-4) *
        (4 * Real.exp (-2)) ^ K ≤ 1 / 16 := by
  have hq : 0 ≤ (4 : ℝ) * Real.exp (-2) := by positivity
  have hlim : Tendsto (fun K : ℕ =>
      (2 : ℝ) ^ 26 * c₀ * Real.exp (-4) *
        (4 * Real.exp (-2)) ^ K) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq rate_base_lt_one).const_mul
        ((2 : ℝ) ^ 26 * c₀ * Real.exp (-4))
  exact (hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 16))).mono
    (fun K hK => hK)

private theorem exists_large_even_K (c₀ c M : ℝ) :
    ∃ K : ℕ, K % 2 = 0 ∧ 8 ≤ K ∧
      4 * (M + 1) / c < ((K / 2 + 1 : ℕ) : ℝ) ∧
      (2 : ℝ) ^ 26 * c₀ * Real.exp (-4) *
        (4 * Real.exp (-2)) ^ K ≤ 1 / 16 := by
  obtain ⟨K₀, hK₀⟩ := (eventually_atTop.1 (eventually_rate_small c₀))
  obtain ⟨n, hn⟩ := exists_nat_gt (4 * (M + 1) / c)
  let t := max K₀ (max 8 n)
  refine ⟨2 * t, by omega, by omega, ?_, hK₀ (2 * t) (by omega)⟩
  have ht : n ≤ (2 * t) / 2 + 1 := by omega
  have htr : (n : ℝ) ≤ (((2 * t) / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast ht
  linarith

 
theorem probability_contradiction
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U V : Set Ω) (hUm : MeasurableSet U)
    (hU : μ Uᶜ ≤ ENNReal.ofReal (1 / 16 : ℝ))
    (hV : ENNReal.ofReal (7 / 8 : ℝ) ≤ μ V)
    (hdual : (2 : ℝ≥0∞) * μ (U ∩ V) ≤ 1) : False := by
  have hcover : μ V ≤ μ (U ∩ V) + μ Uᶜ := by
    calc
      μ V = μ (V ∩ U) + μ (V \ U) := (measure_inter_add_sdiff V hUm).symm
      _ ≤ μ (U ∩ V) + μ Uᶜ := by
        calc
          μ (V ∩ U) + μ (V \ U) = μ (V \ U) + μ (U ∩ V) := by rw [inter_comm]; ac_rfl
          _ ≤ μ Uᶜ + μ (U ∩ V) :=
            add_le_add_left (μ.mono (by aesop : V \ U ⊆ Uᶜ)) _
          _ = μ (U ∩ V) + μ Uᶜ := by ac_rfl
  have h13 : ENNReal.ofReal (13 / 16 : ℝ) ≤ μ (U ∩ V) := by
    have hsum : ENNReal.ofReal (13 / 16 : ℝ) + ENNReal.ofReal (1 / 16 : ℝ) ≤
        μ (U ∩ V) + ENNReal.ofReal (1 / 16 : ℝ) := by
      have heq : ENNReal.ofReal (13 / 16 : ℝ) + ENNReal.ofReal (1 / 16 : ℝ) =
          ENNReal.ofReal (7 / 8 : ℝ) := by
        rw [← ENNReal.ofReal_add (by norm_num : 0 ≤ (13 / 16 : ℝ))
          (by norm_num : 0 ≤ (1 / 16 : ℝ))]
        norm_num
      rw [heq]
      exact hV.trans (hcover.trans (by simpa only [add_comm] using
        (add_le_add_left hU (μ (U ∩ V)))))
    exact (ENNReal.add_le_add_iff_right (by simp)).mp hsum
  have hlarge : (1 : ℝ≥0∞) < 2 * μ (U ∩ V) := by
    calc
      (1 : ℝ≥0∞) < 2 * ENNReal.ofReal (13 / 16 : ℝ) := by
        have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by norm_num
        rw [h2, ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
        simpa only [ENNReal.ofReal_one] using
          (ENNReal.ofReal_lt_ofReal_iff
            (by norm_num : 0 < (2 * (13 / 16) : ℝ))).2
              (by norm_num : (1 : ℝ) < 2 * (13 / 16))
      _ ≤ 2 * μ (U ∩ V) := by gcongr
  exact (not_lt_of_ge hdual) hlarge

 
theorem grid_mesh (K : ℕ) :
    ∀ w : ℂ, dist w 0 < 2 →
      ∃ z : Positivity.Grids.grid K, dist w z.1 ≤ Positivity.Grids.mesh K := by
  apply Positivity.SignDuality.mesh_of_lattice_grid (Positivity.Grids.grid K) (Positivity.Grids.mesh K)
    (Positivity.Grids.mesh_pos K) ?_ ?_
  · unfold Positivity.Grids.mesh
    have hp : (1 : ℝ) < 2 ^ (K + 10) := by
      have h : (2 : ℝ) ^ 1 ≤ 2 ^ (K + 10) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      norm_num at h
      linarith
    exact inv_lt_one_of_one_lt₀ hp
  · intro n m hn
    apply (Positivity.Grids.mem_grid_iff K _).2
    constructor
    · refine ⟨n, m, ?_⟩
      apply Complex.ext <;> simp [Positivity.SignDuality.latticePoint, mul_comm]
    · exact hn

private def pairAt (K : ℕ)
    (q : (Positivity.Grids.grid K) × (Finset.Icc (K / 2) K)) : Set.Ioi (0 : ℝ) × ℂ :=
  (⟨((2 : ℝ) ^ q.2.1)⁻¹, Set.mem_Ioi.mpr (by positivity)⟩, q.1.1)

 
theorem ax14_at_grid (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (K : ℕ) (E : Set DistC)
    (hJoint : ∀ u ∈ E,
      ∃ (S₀ : Set ℂ) (S : ℕ → Set ℂ),
        IsCompact S₀ ∧ IsPathConnected S₀ ∧
        S₀ ⊆ {z : ℂ | 1 < dist z 0 ∧ dist z 0 < 2} ∧
        Disconnects S₀ (Metric.sphere (0 : ℂ) 1)
          (Metric.sphere (0 : ℂ) 2) ∧
        (∀ j ≤ 10, LQGMetric.Disconnects (S j)
          (Metric.sphere (((1 + (j : ℝ) / 10 : ℝ) : ℂ)) (1 / 15 : ℝ))
          (Metric.sphere (((1 + (j : ℝ) / 10 : ℝ) : ℂ)) (2 / 15 : ℝ))) ∧
        (∀ j ≤ 10, IsCompact (S j)) ∧
        (∀ j ≤ 10, IsPathConnected (S j)) ∧
        (∀ j ≤ 10, S j ⊆ Metric.ball (0 : ℂ) 3) ∧
        (∀ w ∈ S₀, ∀ z : Positivity.Grids.grid K, dist w z.1 ≤ Positivity.Grids.mesh K →
          Positivity.SignDuality.low (Positivity.Grids.grid K) (Finset.Icc (K / 2) K)
            (fun z j => circleAvg u (pairAt K (z, j)).1 (pairAt K (z, j)).2) z) ∧
        (∀ j ≤ 10, ∀ w ∈ S j, ∀ z : Positivity.Grids.grid K,
          dist w z.1 ≤ Positivity.Grids.mesh K →
          Positivity.SignDuality.low (Positivity.Grids.grid K) (Finset.Icc (K / 2) K)
            (fun z j => circleAvg u (pairAt K (z, j)).1 (pairAt K (z, j)).2) z)) :
    (2 : ℝ≥0∞) * μ E ≤ 1 := by
  apply Positivity.SignDuality.ax14_probability_bound
    (Positivity.Grids.grid K) (Finset.Icc (K / 2) K) (Positivity.Grids.mesh K)
    μ id hμ (pairAt K)
    (fun p u => circleAvg u p.1 p.2)
  · intro q
    exact ae_isCircleAverage_old hμ.1 (pairAt K q).1 (pairAt K q).2
  · intro q
    exact LQGMetric.measurable_circleAvg_left (pairAt K q).1 (pairAt K q).2
  · exact grid_mesh K
  · exact hJoint

 


theorem axpos_of_steps
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D)
    (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (U : ℝ → ℝ → ℝ → ℕ → Set DistC)
    (hAX11 : ∀ (p c₀ c : ℝ), 0 < p → p < 1 → 0 < c₀ → 0 < c →
      ∀ K : ℕ, K % 2 = 0 →
        MeasurableSet (U p c₀ c K) ∧
        μ (U p c₀ c K)ᶜ ≤ ENNReal.ofReal
          ((2 : ℝ) ^ 26 * c₀ * Real.exp (-4) *
            (4 * Real.exp (-2)) ^ K))
    (hAX13 : ∀ (p c₀ c M : ℝ) (V : Set DistC),
      (∀ᵐ u ∂μ, u ∈ V → ∀ i : Fin 12,
        ∃ (C : ℝ → ℂ) (a b : ℝ), (D u).IsCurve C a b ∧
          (∀ t ∈ Set.Icc a b, C t ∈ (Positivity.Witnesses.witnessAnnulus i).toSet) ∧
          (∀ t ∈ Set.Icc a b, C t ∈ Metric.ball (0 : ℂ) 3) ∧
          Disconnects (C '' Set.Icc a b)
            (Positivity.Witnesses.witnessAnnulus i).innerBoundary
            (Positivity.Witnesses.witnessAnnulus i).outerBoundary ∧
          (D u).len C a b ≤ ENNReal.ofReal (M + 1) ∧
          IsCompact (C '' Set.Icc a b) ∧
          IsPathConnected (C '' Set.Icc a b) ∧
          (∃ x ∈ C '' Set.Icc a b, ∃ y ∈ C '' Set.Icc a b,
            2 * (Positivity.Witnesses.witnessAnnulus i).innerRadius ≤ dist x y)) →
      ∀ K : ℕ, K % 2 = 0 → 8 ≤ K →
        4 * (M + 1) / c < ((K / 2 + 1 : ℕ) : ℝ) →
        Q ≤ 0 →
        ∃ E : Set DistC,
          MeasurableSet E ∧ E ⊆ U p c₀ c K ∩ V ∧
          μ E = μ (U p c₀ c K ∩ V) ∧
          ∀ u ∈ E,
          ∃ (S₀ : Set ℂ) (S : ℕ → Set ℂ),
            IsCompact S₀ ∧ IsPathConnected S₀ ∧
            S₀ ⊆ {z : ℂ | 1 < dist z 0 ∧ dist z 0 < 2} ∧
            Disconnects S₀ (Metric.sphere (0 : ℂ) 1)
              (Metric.sphere (0 : ℂ) 2) ∧
            (∀ j ≤ 10, LQGMetric.Disconnects (S j)
              (Metric.sphere (((1 + (j : ℝ) / 10 : ℝ) : ℂ)) (1 / 15 : ℝ))
              (Metric.sphere (((1 + (j : ℝ) / 10 : ℝ) : ℂ)) (2 / 15 : ℝ))) ∧
            (∀ j ≤ 10, IsCompact (S j)) ∧
            (∀ j ≤ 10, IsPathConnected (S j)) ∧
            (∀ j ≤ 10, S j ⊆ Metric.ball (0 : ℂ) 3) ∧
            (∀ w ∈ S₀, ∀ z : Positivity.Grids.grid K, dist w z.1 ≤ Positivity.Grids.mesh K →
              Positivity.SignDuality.low (Positivity.Grids.grid K) (Finset.Icc (K / 2) K)
                (fun z j => circleAvg u (pairAt K (z, j)).1 (pairAt K (z, j)).2) z) ∧
            (∀ j ≤ 10, ∀ w ∈ S j, ∀ z : Positivity.Grids.grid K,
              dist w z.1 ≤ Positivity.Grids.mesh K →
              Positivity.SignDuality.low (Positivity.Grids.grid K) (Finset.Icc (K / 2) K)
                (fun z j => circleAvg u (pairAt K (z, j)).1 (pairAt K (z, j)).2) z)) :
    0 < Q := by
  by_contra hn
  have hQ : Q ≤ 0 := le_of_not_gt hn
  obtain ⟨p, c₀, hp, hp1, hc₀, _⟩ :=
    LQGMetric.LM.lmLem3_1a (1 / 2) (9 / 10)
      (by norm_num) (by norm_num) (by norm_num)
      4 (by norm_num) (3 / 4) (by norm_num) (by norm_num)
  obtain ⟨c, hc, _⟩ := Positivity.Witnesses.ax9_canonical_tail μ hμ ξ Q D hD p hp hp1
  obtain ⟨M, V, hM, hVm, hV, hW⟩ :=
    Positivity.Witnesses.ax12_canonical_witnesses μ hμ ξ Q D hD
  obtain ⟨K, hK, hK8, hN, hrate⟩ := exists_large_even_K c₀ c M
  obtain ⟨hUm, hUrate⟩ := hAX11 p c₀ c hp hp1 hc₀ hc K hK
  have hU : μ (U p c₀ c K)ᶜ ≤ ENNReal.ofReal (1 / 16 : ℝ) :=
    hUrate.trans (ENNReal.ofReal_le_ofReal hrate)
  obtain ⟨E, _, _, hEmeasure, hJoint⟩ :=
    hAX13 p c₀ c M V hW K hK hK8 hN hQ
  have hdual : (2 : ℝ≥0∞) * μ (U p c₀ c K ∩ V) ≤ 1 := by
    rw [← hEmeasure]
    exact ax14_at_grid μ hμ K E hJoint
  exact (probability_contradiction μ (U p c₀ c K) V hUm hU hV hdual).elim


end SupercriticalLQGUniqueness.Uniqueness.Positivity.Assembly
