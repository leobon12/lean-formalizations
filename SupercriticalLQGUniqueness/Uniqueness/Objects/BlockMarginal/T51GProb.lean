import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal.T51GEvent




 










set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal

open LQGMetric (DistC)

theorem le_measure_of_compl_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {s : Set Ω} (hs : MeasurableSet s) {p : ℝ} (hp1 : p ≤ 1)
    (h : μ sᶜ ≤ ENNReal.ofReal (1 - p)) : ENNReal.ofReal p ≤ μ s := by
  rcases lt_or_ge p 0 with hp0 | hp0
  · rw [ENNReal.ofReal_of_nonpos hp0.le]
    exact bot_le
  have hsum : ENNReal.ofReal p + ENNReal.ofReal (1 - p) = 1 := by
    rw [← ENNReal.ofReal_add hp0 (by linarith)]
    simp
  have h1 : ENNReal.ofReal p + μ sᶜ ≤ μ s + μ sᶜ := by
    rw [measure_add_measure_compl hs, measure_univ, ← hsum]
    gcongr
  exact ENNReal.le_of_add_le_add_right (measure_ne_top μ _) h1

 
theorem clauseI_bound_le {C : ℝ≥0∞} (hC : C < ⊤) {p lam R ε : ℝ} (hp : 0 < p) (hlam : 0 < lam)
    (hR : 0 < R) (hε : 0 < ε)
    (hRM : 2 * Real.pi * C.toReal / (ε * (lam / 2)) ≤ R ^ p) :
    ((volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) Set.univ *
        (C / (ENNReal.ofReal R) ^ p)) / ENNReal.ofReal (lam / 2) ≤ ENNReal.ofReal ε := by
  have hRp : 0 < R ^ p := Real.rpow_pos_of_pos hR p
  have hc : 0 ≤ C.toReal := ENNReal.toReal_nonneg
  rw [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
    ENNReal.ofReal_rpow_of_nonneg hR.le hp.le, ← ENNReal.ofReal_toReal hC.ne,
    ← ENNReal.ofReal_div_of_pos hRp, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_div_of_pos (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hM : 2 * Real.pi * C.toReal ≤ R ^ p * (ε * (lam / 2)) :=
    (div_le_iff₀ (by positivity)).1 hRM
  rw [div_le_iff₀ (by positivity), mul_div_assoc', div_le_iff₀ hRp]
  nlinarith

 
theorem exists_GEv_radius (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (lam : ℝ) (hlam : 0 < lam) (p₁ : ℝ) (hp₁ : p₁ < 1) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ (μ : Measure DistC) [IsProbabilityMeasure μ],
      IsNormalizedWholePlaneGFF (id : DistC → DistC) μ → ∀ (w : ℂ) (s : Ioi (0 : ℝ)),
        ENNReal.ofReal p₁ ≤ μ {g | GEv ξ Q lam R D w s g} := by
  obtain ⟨p, hp, C₁, hC₁, h1⟩ :=
    Objects.BoundaryDecay.source_clauseI_failure_probability_decays ξ Q hQ D hD lam hlam
  obtain ⟨R₂, C₂, -, hC₂, h2⟩ := Objects.AnnulusTails.around_upper_tail ξ Q hQ D hD (a := 1 / 2) (b := 1)
    (by norm_num) (by norm_num) 1 one_pos
  obtain ⟨R₃, C₃, -, hC₃, h3⟩ := Objects.AnnulusTails.acr_lower_tail ξ Q hQ D hD (a := 1 / 2) (b := 1)
    (by norm_num) (by norm_num) 1 one_pos
  set ε : ℝ := (1 - p₁) / 3 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have ev : ∀ᶠ R : ℝ in atTop, 2 * Real.pi * C₁.toReal / (ε * (lam / 2)) ≤ R ^ p ∧ 1 ≤ R ∧
      R₂ ≤ R ∧ R₃ ≤ R ∧ C₂ / ε ≤ R ∧ C₃ / ε ≤ R :=
    ((tendsto_rpow_atTop hp).eventually_ge_atTop _).and ((eventually_ge_atTop 1).and
      ((eventually_ge_atTop R₂).and ((eventually_ge_atTop R₃).and
        ((eventually_ge_atTop _).and (eventually_ge_atTop _)))))
  obtain ⟨R, hRM, hR1, hR2, hR3, hRC2, hRC3⟩ := ev.exists
  have hR0 : 0 < R := by linarith
  refine ⟨R, hR1, ?_⟩
  intro μ _ hμ w s
  have hs : (0 : ℝ) < s := s.2
  set A1 : Set DistC := {g | ENNReal.ofReal ((lam / 2) * s) <
    Objects.Shadow.circleOuter w (s : ℝ).toNNReal 0
      {x | ∃ hx : x ∈ sphere w (s : ℝ), ENNReal.ofReal R * Objects.AnnulusTails.nrm ξ Q g s w <
        Objects.BoundaryDecay.annulusBoundaryCost (D g) (half_lt_self_of_pos s.2) ⟨x, hx⟩}} with hA1def
  set A2 : Set DistC := {g | ENNReal.ofReal R * Objects.AnnulusTails.nrm ξ Q g s w <
    Objects.CorrectedEvent.around (D g) w ((1 / 2) * s) (1 * s)} with hA2def
  set A3 : Set DistC := {g | Objects.CorrectedEvent.acr (D g) w ((1 / 2) * s) (1 * s) <
    ENNReal.ofReal R⁻¹ * Objects.AnnulusTails.nrm ξ Q g s w} with hA3def
  have hA1 : μ A1 ≤ ENNReal.ofReal ε :=
    (h1 μ hμ w s R hs hR0).trans (clauseI_bound_le hC₁ hp hlam hR0 hε hRM)
  have hpow : R ^ (-(1 : ℝ)) = R⁻¹ := Real.rpow_neg_one R
  have hA2 : μ A2 ≤ ENNReal.ofReal ε := by
    refine (h2 μ id hμ R hR2 s w).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hpow, ← div_eq_mul_inv, div_le_iff₀ hR0]
    have := (div_le_iff₀ hε).1 hRC2
    linarith
  have hA3 : μ A3 ≤ ENNReal.ofReal ε := by
    refine (h3 μ id hμ R hR3 s w).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hpow, ← div_eq_mul_inv, div_le_iff₀ hR0]
    have := (div_le_iff₀ hε).1 hRC3
    linarith
  have hsub : {g | GEv ξ Q lam R D w s g}ᶜ ⊆ A1 ∪ A2 ∪ A3 := by
    intro g hg
    simp only [mem_compl_iff, mem_ofPred_eq, GEv, not_and_or, not_le] at hg
    rcases hg with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  apply le_measure_of_compl_le μ (measurableSet_GEv ξ Q lam R D hD.measurable w s) hp₁.le
  calc μ {g | GEv ξ Q lam R D w s g}ᶜ ≤ μ (A1 ∪ A2 ∪ A3) := measure_mono hsub
    _ ≤ μ A1 + μ A2 + μ A3 :=
        (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
    _ ≤ ENNReal.ofReal ε + ENNReal.ofReal ε + ENNReal.ofReal ε :=
        add_le_add (add_le_add hA1 hA2) hA3
    _ = ENNReal.ofReal (1 - p₁) := by
        rw [← ENNReal.ofReal_add hε.le hε.le, ← ENNReal.ofReal_add (by positivity) hε.le]
        congr 1
        rw [hεdef]
        ring

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal
