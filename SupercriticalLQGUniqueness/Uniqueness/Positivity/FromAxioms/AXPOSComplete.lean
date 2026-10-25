import SupercriticalLQGUniqueness.Uniqueness.Positivity.Assembly.AxposAssembly
import SupercriticalLQGUniqueness.Uniqueness.Positivity.GoodScales.AX13Full




 





set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open LQGMetric (DistC circleAvg)
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Positivity.FromAxioms

private theorem exists_large_even_K (c₀ c M : ℝ) :
    ∃ K : ℕ, K % 2 = 0 ∧ 8 ≤ K ∧
      4 * (M + 1) / c < ((K / 2 + 1 : ℕ) : ℝ) ∧
      (2 : ℝ) ^ 26 * c₀ * Real.exp (-4) *
        (4 * Real.exp (-2)) ^ K ≤ 1 / 16 := by
  have hq : 0 ≤ (4 : ℝ) * Real.exp (-2) := by positivity
  have hlim : Tendsto (fun K : ℕ =>
      (2 : ℝ) ^ 26 * c₀ * Real.exp (-4) *
        (4 * Real.exp (-2)) ^ K) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq Positivity.GoodScales.grid_rate_base_lt_one).const_mul
        ((2 : ℝ) ^ 26 * c₀ * Real.exp (-4))
  obtain ⟨K₀, hK₀⟩ :=
    eventually_atTop.1 ((hlim.eventually (eventually_le_nhds
      (by norm_num : (0 : ℝ) < 1 / 16))).mono (fun K hK => hK))
  obtain ⟨n, hn⟩ := exists_nat_gt (4 * (M + 1) / c)
  let t := max K₀ (max 8 n)
  refine ⟨2 * t, by omega, by omega, ?_, hK₀ (2 * t) (by omega)⟩
  have ht : n ≤ (2 * t) / 2 + 1 := by omega
  have htr : (n : ℝ) ≤ (((2 * t) / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast ht
  linarith

private theorem probability_contradiction
    (μ : Measure DistC) [IsProbabilityMeasure μ]
    (U V : Set DistC)
    (hU : μ Uᶜ ≤ ENNReal.ofReal (1 / 16 : ℝ))
    (hV : ENNReal.ofReal (7 / 8 : ℝ) ≤ μ V)
    (hdual : (2 : ℝ≥0∞) * μ (U ∩ V) ≤ 1) : False := by
  have hcover : μ V ≤ μ (U ∩ V) + μ Uᶜ := by
    calc
      μ V ≤ μ ((U ∩ V) ∪ Uᶜ) := μ.mono (by
        intro x hx
        by_cases hUmem : x ∈ U
        · exact Or.inl ⟨hUmem, hx⟩
        · exact Or.inr hUmem)
      _ ≤ μ (U ∩ V) + μ Uᶜ := measure_union_le _ _
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

private theorem low_of_count (K : ℕ) (hK : K % 2 = 0)
    (u : DistC) (z : Positivity.Grids.grid K)
    (hcount : (((Finset.Icc (K / 2) K).filter
      (fun k => 0 ≤ circleAvg u (Positivity.GoodScales.dyadicRadius k) z.1)).card : ℝ) <
        (1 / 2 : ℝ) * ((K / 2 + 1 : ℕ) : ℝ)) :
    Positivity.SignDuality.low (Positivity.Grids.grid K) (Finset.Icc (K / 2) K)
      (fun z j => circleAvg u (Positivity.GoodScales.dyadicRadius j.1) z.1) z := by
  classical
  rw [Positivity.SignDuality.low_iff]
  have hcard : (Finset.Icc (K / 2) K).card = K / 2 + 1 := by
    rw [Nat.card_Icc]
    omega
  have hfilter :
      (Finset.univ.filter (fun j : Finset.Icc (K / 2) K =>
        0 ≤ circleAvg u (Positivity.GoodScales.dyadicRadius j.1) z.1)).card =
      ((Finset.Icc (K / 2) K).filter
        (fun k => 0 ≤ circleAvg u (Positivity.GoodScales.dyadicRadius k) z.1)).card := by
    have h := congrArg Finset.card (Finset.filter_attach
      (fun k => 0 ≤ circleAvg u (Positivity.GoodScales.dyadicRadius k) z.1)
      (Finset.Icc (K / 2) K))
    simp only [Finset.card_map, Finset.card_attach] at h
    simpa only [Finset.attach_eq_univ] using h
  rw [hfilter, hcard]
  exact_mod_cast (by linarith only [hcount] :
    (2 : ℝ) * (((Finset.Icc (K / 2) K).filter
      (fun k => 0 ≤ circleAvg u (Positivity.GoodScales.dyadicRadius k) z.1)).card : ℝ) <
      ((K / 2 + 1 : ℕ) : ℝ))

 
theorem axpos : ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ,
    ∀ D : DistC → LSCMetric, IsWeakLQGMetric ξ Q D → 0 < Q := by
  intro ξ Q D hD
  by_contra hn
  have hQ : Q ≤ 0 := le_of_not_gt hn
  obtain ⟨μ, hμprob, hμ⟩ := Positivity.Witnesses.exists_canonical_normalized_law
  letI : IsProbabilityMeasure μ := hμprob
  obtain ⟨p, c₀, c, M, E, V, hp, hp1, hc₀, hc, hM, hbase,
    hVm, hVprob, hgrid, hwitness⟩ :=
    Positivity.GoodScales.ax13_trace_to_low μ hμ ξ Q hQ D hD
  obtain ⟨K, hKeven, hK8, hlarge, hrate⟩ := exists_large_even_K c₀ c M
  let U : Set DistC := Positivity.GoodScales.gridGood E K
  have hU : μ Uᶜ ≤ ENNReal.ofReal (1 / 16 : ℝ) :=
    (hgrid K hKeven).trans (ENNReal.ofReal_le_ofReal hrate)
  obtain ⟨W, hWae, hWm, hWsub⟩ := hwitness.exists_measurable_mem
  let T : Set DistC := W ∩ (U ∩ V)
  have hTmeasure : μ T = μ (U ∩ V) := Measure.measure_inter_eq_of_ae hWae
  have hJoint : ∀ u ∈ T,
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
            (fun z j => circleAvg u (Positivity.GoodScales.dyadicRadius j.1) z.1) z) ∧
        (∀ j ≤ 10, ∀ w ∈ S j, ∀ z : Positivity.Grids.grid K,
          dist w z.1 ≤ Positivity.Grids.mesh K →
          Positivity.SignDuality.low (Positivity.Grids.grid K) (Finset.Icc (K / 2) K)
            (fun z j => circleAvg u (Positivity.GoodScales.dyadicRadius j.1) z.1) z) := by
    intro u hu
    have huW : u ∈ W := hu.1
    have huU : u ∈ U := hu.2.1
    have huV : u ∈ V := hu.2.2
    have hwi := hWsub u huW huV
    classical
    choose C a b hC hA hB hdisc hlen hcompact hpc hdiam hlow using hwi
    let S₀ : Set ℂ := C 0 '' Icc (a 0) (b 0)
    let S : ℕ → Set ℂ := fun j =>
      if hj : j ≤ 10 then C ⟨j + 1, by omega⟩ '' Icc (a ⟨j + 1, by omega⟩)
        (b ⟨j + 1, by omega⟩) else ∅
    refine ⟨S₀, S, hcompact 0, hpc 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro w hw
      obtain ⟨t, ht, rfl⟩ := hw
      have hh := hA 0 t ht
      simpa only [Positivity.Witnesses.witnessAnnulus_zero, Positivity.Witnesses.largeAnnulus,
        EuclideanAnnulus.toSet, EuclideanAnnulus.center,
        EuclideanAnnulus.innerRadius, EuclideanAnnulus.outerRadius,
        closure_ball _ (by norm_num : (1 : ℝ) ≠ 0), mem_diff,
        Metric.mem_ball, Metric.mem_closedBall, not_le, mem_setOf_eq,
        and_comm] using hh
    · simpa only [S₀, Positivity.Witnesses.witnessAnnulus_zero, Positivity.Witnesses.largeAnnulus,
        EuclideanAnnulus.innerBoundary, EuclideanAnnulus.outerBoundary,
        EuclideanAnnulus.center, EuclideanAnnulus.innerRadius,
        EuclideanAnnulus.outerRadius] using hdisc 0
    · intro j hj
      let i : Fin 12 := ⟨j + 1, by omega⟩
      have hd := disconnects_implies_path_disconnects (hdisc i)
      have hwi : Positivity.Witnesses.witnessAnnulus i = Positivity.Witnesses.smallAnnulus ⟨j, by omega⟩ := by
        simpa only [i, Fin.val_mk] using
          (Positivity.Witnesses.witnessAnnulus_succ (⟨j, by omega⟩ : Fin 11))
      rw [hwi] at hd
      simpa only [S, dif_pos hj, Positivity.Witnesses.smallAnnulus,
        EuclideanAnnulus.innerBoundary, EuclideanAnnulus.outerBoundary,
        EuclideanAnnulus.center, EuclideanAnnulus.innerRadius,
        EuclideanAnnulus.outerRadius] using hd
    · intro j hj
      simpa only [S, dif_pos hj] using hcompact (⟨j + 1, by omega⟩ : Fin 12)
    · intro j hj
      simpa only [S, dif_pos hj] using hpc (⟨j + 1, by omega⟩ : Fin 12)
    · intro j hj
      intro w hw
      have hh : w ∈ C ⟨j + 1, by omega⟩ '' Icc
          (a ⟨j + 1, by omega⟩) (b ⟨j + 1, by omega⟩) := by
        simpa only [S, dif_pos hj] using hw
      obtain ⟨t, ht, rfl⟩ := hh
      exact hB ⟨j + 1, by omega⟩ t ht
    · intro w hw z hz
      obtain ⟨t, ht, rfl⟩ := hw
      obtain ⟨σ, τ, hcross, hsep, hsum, hcount⟩ :=
        hlow 0 K hKeven hK8 hlarge huU z.1 z.2 ⟨t, ht, hz⟩
      exact low_of_count K hKeven u z hcount
    · intro j hj w hw z hz
      have hw' : w ∈ C ⟨j + 1, by omega⟩ '' Icc
          (a ⟨j + 1, by omega⟩) (b ⟨j + 1, by omega⟩) := by
        simpa only [S, dif_pos hj] using hw
      obtain ⟨t, ht, rfl⟩ := hw'
      obtain ⟨σ, τ, hcross, hsep, hsum, hcount⟩ :=
        hlow ⟨j + 1, by omega⟩ K hKeven hK8 hlarge huU z.1 z.2 ⟨t, ht, hz⟩
      exact low_of_count K hKeven u z hcount
  have hdual : (2 : ℝ≥0∞) * μ (U ∩ V) ≤ 1 := by
    rw [← hTmeasure]
    exact Positivity.Assembly.ax14_at_grid μ hμ K T hJoint
  exact (probability_contradiction μ U V hU hVprob hdual).elim


end SupercriticalLQGUniqueness.Uniqueness.Positivity.FromAxioms
