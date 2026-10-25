import SupercriticalLQGUniqueness.Uniqueness.EndSaving.FivePath.Grid




 
set_option autoImplicit false
noncomputable section

open Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.FivePath

 
theorem exists_rpow_small_below
    (α K ε : ℝ) (hα : 0 < α) (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → K * δ ^ α < ε := by
  have hcont : ContinuousAt (fun δ : ℝ => K * δ ^ α) 0 :=
    continuousAt_const.mul (continuousAt_id.rpow_const (Or.inr hα.le))
  have hlim : Tendsto (fun δ : ℝ => K * δ ^ α) (𝓝[>] 0) (𝓝 0) := by
    have h0 : K * (0 : ℝ) ^ α = 0 := by simp [Real.zero_rpow hα.ne']
    simpa only [h0] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hev : {δ : ℝ | K * δ ^ α < ε} ∈ 𝓝[>] 0 :=
    hlim.eventually (Iio_mem_nhds hε)
  obtain ⟨r, hr, hrSub⟩ := (mem_nhdsGT_iff_exists_Ioc_subset).mp hev
  have hr0 : 0 < r := hr
  let δ₀ := min (r / 2) (1 / 2)
  have hδ₀ : 0 < δ₀ := lt_min (half_pos hr) (by norm_num)
  refine ⟨δ₀, hδ₀, ?_, ?_⟩
  · exact (min_le_right _ _).trans_lt (by norm_num)
  intro δ hδ hδle
  apply hrSub
  exact ⟨hδ, hδle.trans ((min_le_left _ _).trans
    (by linarith only [hr0] : r / 2 ≤ r))⟩

 
theorem double_rpow_eq_scaled (δ ν t : ℝ) (hδ : 0 < δ) :
    (2 * δ ^ ν) ^ t = (2 : ℝ) ^ t * δ ^ (ν * t - 1) * δ := by
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hδ.le _)]
  rw [← Real.rpow_mul hδ.le]
  have hexp : ν * t = (ν * t - 1) + 1 := by ring
  rw [hexp, Real.rpow_add hδ, Real.rpow_one]
  ring_nf

 

theorem exists_small_splice_error
    (a : Set.Ioo (3 / 4 : ℝ) 1)
    (θ : Set.Ioi (0 : ℝ)) (C ν : ℝ)
    (hν : 2 / (θ : ℝ) < ν) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        2 * C * ((2 * δ ^ ν) ^ ((θ : ℝ) / 2) +
          (2 * δ ^ ν) ^ (θ : ℝ)) <
          ((1 - (a : ℝ)) / 4) * δ := by
  have hθ : 0 < (θ : ℝ) := θ.property
  have hνθ : 2 < ν * (θ : ℝ) := by
    have h := mul_lt_mul_of_pos_right hν hθ
    have hsimp : (2 / (θ : ℝ)) * (θ : ℝ) = 2 := by
      field_simp [hθ.ne']
    rw [hsimp] at h
    exact h
  have hα : 0 < ν * ((θ : ℝ) / 2) - 1 := by
    nlinarith only [hνθ]
  have hβ : 0 < ν * (θ : ℝ) - 1 := by linarith only [hνθ]
  have hε : 0 < (1 - (a : ℝ)) / 8 := by
    have := a.property.2
    positivity
  obtain ⟨δ₁, hδ₁, hδ₁one, hsmall₁⟩ :=
    exists_rpow_small_below (ν * ((θ : ℝ) / 2) - 1)
      (2 * C * (2 : ℝ) ^ ((θ : ℝ) / 2))
      ((1 - (a : ℝ)) / 8) hα hε
  obtain ⟨δ₂, hδ₂, hδ₂one, hsmall₂⟩ :=
    exists_rpow_small_below (ν * (θ : ℝ) - 1)
      (2 * C * (2 : ℝ) ^ (θ : ℝ))
      ((1 - (a : ℝ)) / 8) hβ hε
  let δ₀ := min δ₁ δ₂
  have hδ₀ : 0 < δ₀ := lt_min hδ₁ hδ₂
  refine ⟨δ₀, hδ₀, (min_le_left _ _).trans_lt hδ₁one, ?_⟩
  intro δ hδ hδle
  have h₁ := hsmall₁ δ hδ (hδle.trans (min_le_left _ _))
  have h₂ := hsmall₂ δ hδ (hδle.trans (min_le_right _ _))
  have hsum :
      2 * C * ((2 : ℝ) ^ ((θ : ℝ) / 2) *
        δ ^ (ν * ((θ : ℝ) / 2) - 1) +
        (2 : ℝ) ^ (θ : ℝ) * δ ^ (ν * (θ : ℝ) - 1)) <
      (1 - (a : ℝ)) / 4 := by
    nlinarith only [h₁, h₂]
  rw [double_rpow_eq_scaled δ ν ((θ : ℝ) / 2) hδ,
    double_rpow_eq_scaled δ ν (θ : ℝ) hδ]
  nlinarith only [hsum, hδ]

 

theorem strict_ratio_of_paid_saving
    (d E : ℝ≥0∞) (hd0 : 0 < d) (hdtop : d < ⊤)
    (C x e : ℝ) (hx : 0 < x) (hCx : x < C)
    (he0 : 0 ≤ e) (he : e < x)
    (hpaid : E + ENNReal.ofReal (4 * x) * d ≤
      ENNReal.ofReal C * d + ENNReal.ofReal e * d) :
    E < ENNReal.ofReal (C - x) * d := by
  have hC0 : 0 ≤ C := by linarith only [hx, hCx]
  have h4x : 0 ≤ 4 * x := by positivity
  have hCx0 : 0 ≤ C - x := sub_nonneg.mpr hCx.le
  have hdne : d ≠ ⊤ := hdtop.ne
  have hRfin :
      ENNReal.ofReal C * d + ENNReal.ofReal e * d < ⊤ := by
    rw [ENNReal.add_lt_top]
    exact ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hdtop,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hdtop⟩
  have hLfin : E + ENNReal.ofReal (4 * x) * d < ⊤ :=
    lt_of_le_of_lt hpaid hRfin
  have hEne : E ≠ ⊤ := (ENNReal.add_lt_top.mp hLfin).1.ne
  have hSaveNe : ENNReal.ofReal (4 * x) * d ≠ ⊤ :=
    (ENNReal.add_lt_top.mp hLfin).2.ne
  have hCne : ENNReal.ofReal C * d ≠ ⊤ :=
    (ENNReal.add_lt_top.mp hRfin).1.ne
  have hene : ENNReal.ofReal e * d ≠ ⊤ :=
    (ENNReal.add_lt_top.mp hRfin).2.ne
  have hpaidReal := (ENNReal.toReal_le_toReal hLfin.ne hRfin.ne).2 hpaid
  rw [ENNReal.toReal_add hEne hSaveNe,
    ENNReal.toReal_add hCne hene] at hpaidReal
  simp only [ENNReal.toReal_ofReal_mul _ _ h4x,
    ENNReal.toReal_ofReal_mul _ _ hC0,
    ENNReal.toReal_ofReal_mul _ _ he0] at hpaidReal
  have hdreal : 0 < d.toReal := ENNReal.toReal_pos hd0.ne' hdne
  have hmul : e * d.toReal < x * d.toReal :=
    mul_lt_mul_of_pos_right he hdreal
  have hTargetFin : ENNReal.ofReal (C - x) * d ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hdtop).ne
  apply (ENNReal.toReal_lt_toReal hEne hTargetFin).1
  rw [ENNReal.toReal_ofReal_mul _ _ hCx0]
  nlinarith only [hpaidReal, hmul, hx, hdreal]

 

theorem exists_uniform_R53_scale
    (a : Set.Ioo (3 / 4 : ℝ) 1) (θ : Set.Ioi (0 : ℝ))
    (C : NNReal) (hC : 0 < C)
    (ν : Set.Ioi (0 : ℝ)) (hν : 2 / (θ : ℝ) < (ν : ℝ)) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        100 * δ ^ (ν : ℝ) ≤ 1 - (a : ℝ) ∧
        2 * δ ^ (ν : ℝ) ≤ (1 - (a : ℝ)) ^ 4 ∧
        2 * (C : ℝ) *
          ((2 * δ ^ (ν : ℝ)) ^ ((θ : ℝ) / 2) +
            (2 * δ ^ (ν : ℝ)) ^ (θ : ℝ)) <
          ((1 - (a : ℝ)) / 4) * δ ∧
        ((1 - (a : ℝ)) / 4) * δ < (C : ℝ) := by
  have haGap : 0 < 1 - (a : ℝ) := sub_pos.mpr a.property.2
  obtain ⟨δm, hδm, hδm1, hm⟩ :=
    exists_rpow_small_below (ν : ℝ) 100 (1 - (a : ℝ))
      ν.property haGap
  obtain ⟨δi, hδi, hδi1, hi⟩ :=
    exists_rpow_small_below (ν : ℝ) 2 ((1 - (a : ℝ)) ^ 4)
      ν.property (pow_pos haGap _)
  obtain ⟨δe, hδe, hδe1, he⟩ :=
    exists_small_splice_error a θ (C : ℝ) (ν : ℝ) hν
  let δ₀ := min δm (min δi (min δe ((C : ℝ) / 2)))
  have hC0 : 0 < (C : ℝ) := by exact_mod_cast hC
  have hδ₀ : 0 < δ₀ :=
    lt_min hδm (lt_min hδi (lt_min hδe (half_pos hC0)))
  refine ⟨δ₀, hδ₀, (min_le_left _ _).trans_lt hδm1, ?_⟩
  intro δ hδ hδle
  have hδmle : δ ≤ δm := hδle.trans (min_le_left _ _)
  have hδile : δ ≤ δi :=
    hδle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδele : δ ≤ δe :=
    hδle.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hδCle : δ ≤ (C : ℝ) / 2 :=
    hδle.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨(hm δ hδ hδmle).le, (hi δ hδ hδile).le,
    he δ hδ hδele, ?_⟩
  have hGapSmall : 1 - (a : ℝ) < 1 := by
    linarith only [a.property.1]
  nlinarith only [hδCle, hGapSmall, hδ, hC0]


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.FivePath
