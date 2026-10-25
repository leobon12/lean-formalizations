import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS5.S5Sum




 






set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS5

open SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails
open LQGMetric (DistC)

theorem compareScale_inv16_tendsto :
    Tendsto (fun k : ℕ => (Objects.CorrectedEvent.compareScale k) ^ (-(1:ℝ)/16)) atTop atTop := by
  have hlog : 0 < Real.log ((21:ℝ)/20) := Real.log_pos (by norm_num)
  have he : (fun k : ℕ => (Objects.CorrectedEvent.compareScale k) ^ (-(1:ℝ)/16)) =
      fun k : ℕ => Real.exp ((k:ℝ) * (Real.log ((21:ℝ)/20) / 16)) := by
    funext k
    unfold Objects.CorrectedEvent.compareScale
    rw [← Real.rpow_mul (by norm_num), Real.rpow_def_of_pos (by norm_num)]
    congr 1
    ring
  rw [he]
  have ht : Tendsto (fun k : ℕ => (k:ℝ) * (Real.log ((21:ℝ)/20) / 16)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity)
  exact Real.tendsto_exp_atTop.comp ht

 


theorem exists_s5_budget (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (pbar : Ioo (0 : ℝ) 1) :
    ∃ a₀ : ℝ, 0 < a₀ ∧
      ∀ C : Objects.CorrectedEvent.Constants, C.ξ = ξ → C.Q = Q → C.A_nar < a₀ →
        μ {g | ¬ Objects.CorrectedEvent.S5 C (D g)} ≤
          ENNReal.ofReal ((1 - (pbar : ℝ)) / 10) := by
  obtain ⟨R₀, CU, CL, hR₀, hCU, hCL, hsite⟩ :=
    exists_s5_site_tail ξ Q hQ D hD
  let b : ℕ → ℝ := fun k => 490000 * (CU + CL) * (Objects.CorrectedEvent.compareScale k)^2
  have hb0 : ∀ k, 0 ≤ b k := fun k => by dsimp [b]; positivity
  have hbs : Summable b := summable_compareScale_sq.mul_left _
  have hε : 0 < (1 - (pbar : ℝ)) / 10 := by linarith [pbar.2.2]
  have htail : ∀ᶠ n : ℕ in atTop,
      ∑' k, b (k+n) < (1 - (pbar : ℝ)) / 10 :=
    (tendsto_sum_nat_add b).eventually (gt_mem_nhds hε)
  have hR : ∀ᶠ k : ℕ in atTop,
      R₀ ≤ (Objects.CorrectedEvent.compareScale k)^(-(1:ℝ)/16) :=
    compareScale_inv16_tendsto.eventually_ge_atTop R₀
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (htail.and hR)
  refine ⟨Objects.CorrectedEvent.compareScale n₀, compareScale_pos n₀, ?_⟩
  intro C hCξ hCQ hNar
  have hk₀ : ∀ k : ℕ, Objects.CorrectedEvent.compareScale k ≤ C.A_nar → n₀ ≤ k := by
    intro k hk
    by_contra h
    have hkn : k ≤ n₀ := by omega
    have hmono := compareScale_antitone hkn
    linarith
  let Fail : ℕ → ℂ → Set DistC := fun k z => {g | ¬ s5Site C (D g) k z}
  have hsub : {g | ¬ Objects.CorrectedEvent.S5 C (D g)} ⊆
      ⋃ j : ℕ, ⋃ z ∈ compareFinset C (j+n₀), Fail (j+n₀) z := by
    intro g hg
    simp only [Objects.CorrectedEvent.S5, not_forall] at hg
    obtain ⟨k, htk, z, hz, hbad⟩ := hg
    have hkn := hk₀ k htk
    refine mem_iUnion.2 ⟨k-n₀, ?_⟩
    rw [Nat.sub_add_cancel hkn]
    exact mem_iUnion₂.2 ⟨z, Finset.mem_coe.1 (compareSites_subset C k hz), hbad⟩
  have hlevel : ∀ j : ℕ,
      μ (⋃ z ∈ compareFinset C (j+n₀), Fail (j+n₀) z) ≤
        ENNReal.ofReal (b (j+n₀)) := by
    intro j
    set k := j+n₀ with hkdef
    have hkn : n₀ ≤ k := by omega
    have hRk := (hn₀ k hkn).2
    have hper : ∀ z ∈ compareFinset C k,
        μ (Fail k z) ≤ ENNReal.ofReal ((CU+CL)*(Objects.CorrectedEvent.compareScale k)^4) := by
      intro z _
      have hh := hsite μ hμ C hCξ hCQ k hRk z
      rw [compareScale_pow_four] at hh
      convert hh using 1
      norm_num
    have hcard := card_compareFinset_le C k
    have hpow : (Objects.CorrectedEvent.compareScale k)⁻¹ ^ 2 *
        (Objects.CorrectedEvent.compareScale k)^4 = (Objects.CorrectedEvent.compareScale k)^2 := by
      have ht := compareScale_pos k
      field_simp
    calc μ (⋃ z ∈ compareFinset C k, Fail k z)
        ≤ ∑ z ∈ compareFinset C k, μ (Fail k z) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _z ∈ compareFinset C k,
          ENNReal.ofReal ((CU+CL)*(Objects.CorrectedEvent.compareScale k)^4) :=
          Finset.sum_le_sum hper
      _ = ENNReal.ofReal (((compareFinset C k).card : ℝ) *
          ((CU+CL)*(Objects.CorrectedEvent.compareScale k)^4)) := sum_const_ofReal _ _
      _ ≤ ENNReal.ofReal (b k) := by
        apply ENNReal.ofReal_le_ofReal
        dsimp [b]
        calc ((compareFinset C k).card : ℝ) *
            ((CU+CL)*(Objects.CorrectedEvent.compareScale k)^4)
            ≤ (490000 * (Objects.CorrectedEvent.compareScale k)⁻¹ ^ 2) *
              ((CU+CL)*(Objects.CorrectedEvent.compareScale k)^4) :=
                mul_le_mul_of_nonneg_right hcard (by positivity)
          _ = 490000 * (CU+CL) * (Objects.CorrectedEvent.compareScale k)^2 := by
              rw [show 490000 * (Objects.CorrectedEvent.compareScale k)⁻¹ ^ 2 *
                  ((CU+CL)*(Objects.CorrectedEvent.compareScale k)^4) =
                490000*(CU+CL) *
                  ((Objects.CorrectedEvent.compareScale k)⁻¹ ^ 2 *
                    (Objects.CorrectedEvent.compareScale k)^4) by ring, hpow]
  obtain ⟨hsum, -⟩ := hn₀ n₀ le_rfl
  calc μ {g | ¬ Objects.CorrectedEvent.S5 C (D g)}
      ≤ μ (⋃ j : ℕ, ⋃ z ∈ compareFinset C (j+n₀), Fail (j+n₀) z) :=
        measure_mono hsub
    _ ≤ ∑' j : ℕ, μ (⋃ z ∈ compareFinset C (j+n₀), Fail (j+n₀) z) :=
        measure_iUnion_le _
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (b (j+n₀)) :=
        ENNReal.tsum_le_tsum hlevel
    _ = ENNReal.ofReal (∑' j : ℕ, b (j+n₀)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun j => hb0 _) ((summable_nat_add_iff n₀).2 hbs)).symm
    _ ≤ ENNReal.ofReal ((1-(pbar:ℝ))/10) :=
        ENNReal.ofReal_le_ofReal hsum.le

end SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS5
