import SupercriticalLQGUniqueness.B2.PfeLocal.L4Bilip

 














set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.PfeLocal

theorem l4_setDistance_eq_iInf_prod (D : LSCMetric) (O O' : Set ℂ) :
    Iface.setDistance D.1 O O' = ⨅ q ∈ O ×ˢ O', D q := by
  refine le_antisymm (le_iInf₂ fun q hq => ?_) (le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_)
  · exact iInf₂_le_of_le q.1 hq.1 (iInf₂_le q.2 hq.2)
  · exact iInf₂_le (x, y) ⟨hx, hy⟩

theorem l4_measurable_setDistance {O O' : Set ℂ} (hO : IsCompact O) (hO' : IsCompact O') :
    Measurable fun D : LSCMetric => Iface.setDistance D.1 O O' := by
  simp only [l4_setDistance_eq_iInf_prod]
  exact (LSCMetric.lowerSemicontinuous_iInf_of_isCompact (hO.prod hO')).measurable

theorem l4_isCompact_rationalCircle {O : Set ℂ} (hO : Iface.IsRationalCircle O) : IsCompact O := by
  obtain ⟨x, y, r, -, rfl⟩ := hO
  exact isCompact_sphere _ _

 
theorem l4_card_good_eq_countOcc {Ω : Type} [MeasurableSpace Ω] (ξ : ℝ) (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (h : Ω → DistC) (L : Ω → LSCMetric) (w : ℂ) (k₀ : ℕ) (C : Set.Ioi (1 : ℝ)) (ω : Ω) :
    (l4Good ξ c (h ω) (L ω) w k₀ C).card = LQGMetric.Blueprint.countOcc (fun k =>
      annulusEvent ξ c h L w ⟨l1Scale k₀ k, l1Scale_pos k₀ k⟩ C) k₀ ω := by
  classical
  unfold l4Good LQGMetric.Blueprint.countOcc
  rfl

theorem l4_measurableSet_count {Ω : Type} [MeasurableSpace Ω] (ξ : ℝ)
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) {h : Ω → DistC} {L : Ω → LSCMetric}
    (hh : Measurable h) (hL : Measurable L) (w : ℂ) (k₀ : ℕ) (C : Set.Ioi (1 : ℝ)) (x : ℝ) :
    MeasurableSet {ω | (LQGMetric.Blueprint.countOcc (fun k =>
      annulusEvent ξ c h L w ⟨l1Scale k₀ k, l1Scale_pos k₀ k⟩ C) k₀ ω : ℝ) < x} :=
  measurableSet_lt (measurable_from_nat.comp (l1_measurable_countOcc
    (fun k => measurableSet_annulusEvent ξ c h L hh hL w _ C) k₀)) measurable_const

 

theorem l4_lattice_bad_le {Ω' : Type} [MeasurableSpace Ω'] [StandardBorelSpace Ω'] [Nonempty Ω']
    (P' : Measure Ω') [IsProbabilityMeasure P'] (h' : Ω' → DistC) (hh' : Measurable h')
    (L : Ω' → LSCMetric) (hL : Measurable L) (ξ : ℝ) (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (C : Set.Ioi (1 : ℝ)) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hL1 : ∀ (z : ℂ) (k₀ J : ℕ), P' {ω | (LQGMetric.Blueprint.countOcc (fun k =>
      annulusEvent ξ c h' L z ⟨l1Scale k₀ k, l1Scale_pos k₀ k⟩ C) J ω : ℝ) < (3 / 4) * J} ≤
        ENNReal.ofReal (c₀ * Real.exp (-(5 * Real.log 16) * J)))
    (k₀ : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    l4Copy P' h' hh' {p | ¬ l4LatticeGood ξ c (h' p.1) (L p.1) (L p.2) k₀ R C} ≤
      ENNReal.ofReal (2 * c₀ * (8 * R + 11) ^ 2 * (1 / 16 : ℝ) ^ k₀) := by
  set Q := l4Copy P' h' hh'
  set Λ := l4Lattice k₀ R
  set B₁ : ℂ → Set (Ω' × Ω') := fun w => Prod.fst ⁻¹' {ω | (LQGMetric.Blueprint.countOcc
    (fun k => annulusEvent ξ c h' L w ⟨l1Scale k₀ k, l1Scale_pos k₀ k⟩ C) k₀ ω : ℝ) <
      (3 / 4) * k₀}
  set B₂ : ℂ → Set (Ω' × Ω') := fun w => Prod.snd ⁻¹' {ω | (LQGMetric.Blueprint.countOcc
    (fun k => annulusEvent ξ c h' L w ⟨l1Scale k₀ k, l1Scale_pos k₀ k⟩ C) k₀ ω : ℝ) <
      (3 / 4) * k₀}
  have hsub : {p | ¬ l4LatticeGood ξ c (h' p.1) (L p.1) (L p.2) k₀ R C} ≤ᵐ[Q]
      ⋃ w ∈ Λ, (B₁ w ∪ B₂ w) := by
    filter_upwards [l4Copy_same_field P' h' hh'] with p hp hbad
    simp only [mem_ofPred_eq, l4LatticeGood, not_forall, not_and_or, not_le] at hbad
    obtain ⟨w, hw, hbad⟩ := hbad
    refine mem_biUnion hw ?_
    rcases hbad with h1 | h2
    · left
      change (LQGMetric.Blueprint.countOcc _ k₀ p.1 : ℝ) < _
      rw [← l4_card_good_eq_countOcc]; exact h1
    · right
      change (LQGMetric.Blueprint.countOcc _ k₀ p.2 : ℝ) < _
      rw [← l4_card_good_eq_countOcc, hp]; exact h2
  have hone : ∀ w, Q (B₁ w) + Q (B₂ w) ≤
      2 * ENNReal.ofReal (c₀ * Real.exp (-(5 * Real.log 16) * k₀)) := by
    intro w
    rw [two_mul]
    refine add_le_add ?_ ?_
    · rw [l4Copy_fst_measure P' h' hh' (l4_measurableSet_count ξ c hh' hL w k₀ C _)]
      exact hL1 w k₀ k₀
    · rw [l4Copy_snd_measure P' h' hh' (l4_measurableSet_count ξ c hh' hL w k₀ C _)]
      exact hL1 w k₀ k₀
  
  set X : ℝ := (16 : ℝ) ^ k₀ with hX
  have hX1 : 1 ≤ X := one_le_pow₀ (by norm_num)
  have hs : l4Spacing k₀ = (X ^ 2)⁻¹ / 4 := by
    unfold l4Spacing l1Scale
    rw [hX, ← pow_mul, show k₀ * 2 = k₀ + k₀ by ring, one_div, inv_pow]
  have hN : (l4N k₀ R : ℝ) ≤ (4 * R + 5) * X ^ 2 := by
    have h1 : (l4N k₀ R : ℝ) < (R + 1) / l4Spacing k₀ + 1 := Nat.ceil_lt_add_one (by
      have := l4Spacing_pos k₀; positivity)
    rw [hs] at h1
    have h2 : (R + 1) / ((X ^ 2)⁻¹ / 4) = 4 * (R + 1) * X ^ 2 := by field_simp
    rw [h2] at h1
    nlinarith
  have hcard : ((Λ.card : ℕ) : ℝ) ≤ (8 * R + 11) ^ 2 * X ^ 4 := by
    refine (l4Lattice_card_le k₀ R).trans ?_
    have : 2 * (l4N k₀ R : ℝ) + 1 ≤ (8 * R + 11) * X ^ 2 := by nlinarith
    calc (2 * (l4N k₀ R : ℝ) + 1) ^ 2 ≤ ((8 * R + 11) * X ^ 2) ^ 2 := by
          gcongr
      _ = (8 * R + 11) ^ 2 * X ^ 4 := by ring
  have hexp : Real.exp (-(5 * Real.log 16) * k₀) = (X ^ 5)⁻¹ := by
    rw [hX, ← pow_mul, show -(5 * Real.log 16) * (k₀ : ℝ) = -(((k₀ * 5 : ℕ) : ℝ) * Real.log 16)
      by push_cast; ring, Real.exp_neg, ← Real.log_pow, Real.exp_log (by positivity)]
  calc Q {p | ¬ l4LatticeGood ξ c (h' p.1) (L p.1) (L p.2) k₀ R C}
      ≤ Q (⋃ w ∈ Λ, (B₁ w ∪ B₂ w)) := measure_mono_ae hsub
    _ ≤ ∑ w ∈ Λ, Q (B₁ w ∪ B₂ w) := measure_biUnion_finset_le _ _
    _ ≤ ∑ w ∈ Λ, 2 * ENNReal.ofReal (c₀ * Real.exp (-(5 * Real.log 16) * k₀)) :=
        Finset.sum_le_sum fun w _ => (measure_union_le _ _).trans (hone w)
    _ = ENNReal.ofReal ((Λ.card : ℝ) * (2 * (c₀ * (X ^ 5)⁻¹))) := by
        rw [Finset.sum_const, nsmul_eq_mul, hexp, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (2 * c₀ * (8 * R + 11) ^ 2 * (1 / 16 : ℝ) ^ k₀) := by
        apply ENNReal.ofReal_le_ofReal
        have hX0 : 0 < X := by positivity
        have e : (1 / 16 : ℝ) ^ k₀ = X⁻¹ := by rw [hX, one_div, inv_pow]
        rw [e]
        calc (Λ.card : ℝ) * (2 * (c₀ * (X ^ 5)⁻¹))
            ≤ (8 * R + 11) ^ 2 * X ^ 4 * (2 * (c₀ * (X ^ 5)⁻¹)) := by gcongr
          _ = 2 * c₀ * (8 * R + 11) ^ 2 * X⁻¹ := by field_simp

theorem l4LatticeGood_comm (ξ : ℝ) (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (g : DistC)
    (D₁ D₂ : LSCMetric) (k₀ : ℕ) (R : ℝ) (C : Set.Ioi (1 : ℝ)) :
    l4LatticeGood ξ c g D₁ D₂ k₀ R C ↔ l4LatticeGood ξ c g D₂ D₁ k₀ R C :=
  ⟨fun h w hw => (h w hw).symm, fun h w hw => (h w hw).symm⟩

theorem l4_tendsto_bound (c₀ : ℝ) (R : ℝ) :
    Tendsto (fun k₀ : ℕ => ENNReal.ofReal (2 * c₀ * (8 * R + 11) ^ 2 * (1 / 16 : ℝ) ^ k₀)) atTop
      (𝓝 0) := by
  rw [← ENNReal.ofReal_zero]
  refine ENNReal.tendsto_ofReal ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 16)
    (by norm_num)).const_mul (2 * c₀ * (8 * R + 11) ^ 2)

 
theorem l4_bilip_copy {Ω' : Type} [MeasurableSpace Ω'] [StandardBorelSpace Ω'] [Nonempty Ω']
    (P' : Measure Ω') [IsProbabilityMeasure P'] (h' : Ω' → DistC) (hh' : Measurable h')
    (L : Ω' → LSCMetric) (hL : Measurable L) (ξ : ℝ) (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (C : Set.Ioi (1 : ℝ)) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hL1 : ∀ (z : ℂ) (k₀ J : ℕ), P' {ω | (LQGMetric.Blueprint.countOcc (fun k =>
      annulusEvent ξ c h' L z ⟨l1Scale k₀ k, l1Scale_pos k₀ k⟩ C) J ω : ℝ) < (3 / 4) * J} ≤
        ENNReal.ofReal (c₀ * Real.exp (-(5 * Real.log 16) * J)))
    (hgeo : ∀ᵐ ω ∂P', (∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
        ∀ v : ℂ, (L ω).1 (u, v) < ENNReal.ofReal η → dist u v < δ) ∧
      (∀ u v : ℂ, (L ω).1 (u, v) < ∞ → ∃ (γ : ℝ → ℂ) (a b : ℝ),
        (L ω).IsCurve γ a b ∧ γ a = u ∧ γ b = v ∧ (L ω).len γ a b = (L ω).1 (u, v))) :
    ∀ᵐ p ∂(l4Copy P' h' hh'), ∀ O O' : Set ℂ, Iface.IsRationalCircle O →
      Iface.IsRationalCircle O' →
      Iface.setDistance (L p.2).1 O O' ≤
          ENNReal.ofReal ((C : ℝ) ^ 2) * Iface.setDistance (L p.1).1 O O' ∧
        Iface.setDistance (L p.1).1 O O' ≤
          ENNReal.ofReal ((C : ℝ) ^ 2) * Iface.setDistance (L p.2).1 O O' := by
  have hprob : ∀ R : ℕ, Tendsto (fun k₀ => l4Copy P' h' hh'
      {p | ¬ l4LatticeGood ξ c (h' p.1) (L p.1) (L p.2) k₀ R C}) atTop (𝓝 0) := by
    intro R
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (l4_tendsto_bound c₀ R)
      (fun _ => zero_le) (fun k₀ => l4_lattice_bad_le P' h' hh' L hL ξ c C c₀ hc₀ hL1 k₀
        (by positivity))
  have h1 := l4_bilip_general (l4Copy P' h' hh') ξ c C (fun p => h' p.1) (fun p => L p.1)
    (fun p => L p.2) (l4Copy_ae_fst P' h' hh' hgeo) hprob
  have hprob' : ∀ R : ℕ, Tendsto (fun k₀ => l4Copy P' h' hh'
      {p | ¬ l4LatticeGood ξ c (h' p.1) (L p.2) (L p.1) k₀ R C}) atTop (𝓝 0) := by
    intro R
    simpa only [l4LatticeGood_comm] using hprob R
  have h2 := l4_bilip_general (l4Copy P' h' hh') ξ c C (fun p => h' p.1) (fun p => L p.2)
    (fun p => L p.1) (l4Copy_ae_snd P' h' hh' hgeo) hprob'
  filter_upwards [h1, h2] with p hp1 hp2 O O' hO hO'
  exact ⟨hp1 O O' hO hO', hp2 O O' hO hO'⟩

 

def l4CondMean {Ω' : Type} [MeasurableSpace Ω'] [StandardBorelSpace Ω'] [Nonempty Ω']
    (P' : Measure Ω') [IsProbabilityMeasure P'] (h' : Ω' → DistC) (F : Ω' → ℝ≥0∞) (g : DistC) :
    ℝ≥0∞ :=
  ∫⁻ ω₂, F ω₂ ∂(condDistrib id h' P' g)

 

theorem l4_lem51 {Ω' : Type} [MeasurableSpace Ω'] [StandardBorelSpace Ω'] [Nonempty Ω']
    (P' : Measure Ω') [IsProbabilityMeasure P'] (h' : Ω' → DistC) (hh' : Measurable h')
    (F : Ω' → ℝ≥0∞) (hF : Measurable F) (K : ℝ≥0∞)
    (hcopy : ∀ᵐ p ∂(l4Copy P' h' hh'), F p.2 ≤ K * F p.1 ∧ F p.1 ≤ K * F p.2) :
    ∀ᵐ ω ∂P', l4CondMean P' h' F (h' ω) ≤ K * F ω ∧ F ω ≤ K * l4CondMean P' h' F (h' ω) := by
  have hmeas1 : MeasurableSet {p : Ω' × Ω' | F p.2 ≤ K * F p.1 ∧ F p.1 ≤ K * F p.2} :=
    (measurableSet_le (hF.comp measurable_snd) ((hF.comp measurable_fst).const_mul K)).inter
      (measurableSet_le (hF.comp measurable_fst) ((hF.comp measurable_snd).const_mul K))
  have hae := (Measure.ae_compProd_iff hmeas1).1 hcopy
  filter_upwards [hae] with ω hω
  have hκ : IsProbabilityMeasure (condDistrib id h' P' (h' ω)) := inferInstance
  change ∀ᵐ ω₂ ∂(condDistrib id h' P' (h' ω)), F ω₂ ≤ K * F ω ∧ F ω ≤ K * F ω₂ at hω
  refine ⟨?_, ?_⟩
  · calc l4CondMean P' h' F (h' ω) ≤ ∫⁻ _, K * F ω ∂(condDistrib id h' P' (h' ω)) :=
          lintegral_mono_ae (hω.mono fun _ h => h.1)
      _ = K * F ω := by rw [lintegral_const, measure_univ, mul_one]
  · calc F ω = ∫⁻ _, F ω ∂(condDistrib id h' P' (h' ω)) := by
          rw [lintegral_const, measure_univ, mul_one]
      _ ≤ ∫⁻ ω₂, K * F ω₂ ∂(condDistrib id h' P' (h' ω)) :=
          lintegral_mono_ae (hω.mono fun _ h => h.2)
      _ = K * l4CondMean P' h' F (h' ω) := lintegral_const_mul K hF

end SupercriticalLQGUniqueness.B2.PfeLocal
