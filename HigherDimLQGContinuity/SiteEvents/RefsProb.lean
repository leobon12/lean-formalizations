import HigherDimLQGContinuity.SiteEvents.RefsGeom
import HigherDimLQGContinuity.Events.RefsProb

/-! Probability bounds for site and seed doubled-ball references. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open MeasureTheory Metric Set
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

private theorem q10_dupper_mono {d : ℕ} {G : ContMetric d} {W : Set (Rd d)}
    {H H' σ : ℝ} (hHH' : H ≤ H') (h : DUpper G W H σ) : DUpper G W H' σ := by
  intro z r hr hball
  exact (h z r hr hball).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hHH' (Real.rpow_nonneg hr.le _)))

/-- Uniform high probability of the doubled-ball upper reference on the site annulus. -/
theorem dupper_prob_bound {d : ℕ} (hd : 2 ≤ d) {ξbar : ℝ}
    (hU : UniformEstimates d ξbar 1) {p : ℝ} (hp : 0 < p) :
    ∃ Hsd σsd : ℝ, 1 ≤ Hsd ∧ 0 < σsd ∧ σsd ≤ 1 ∧
      ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ∀ D : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D →
          pinLaw d 1 {g | ¬ DUpper (rho D g) (siteA d) Hsd σsd} ≤ ENNReal.ofReal p := by
  obtain ⟨p₁, σ, β, C, A, hp₁, hσ, hσ1, hβ, hC, hA, henv⟩ := hU.envelope
  let c₀ : ℝ := C * (1 + 4) ^ A
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  let Hsd : ℝ := max 1 ((c₀ / p) ^ p₁⁻¹)
  have hHsd : 1 ≤ Hsd := le_max_left _ _
  have hHsd0 : 0 < Hsd := lt_of_lt_of_le one_pos hHsd
  refine ⟨Hsd, σ, hHsd, hσ, hσ1.le, ?_⟩
  intro ξ hξ D hD
  have hprob := isProbabilityMeasure_pinLaw hd (1 : ℝ)
  obtain ⟨H, hHm, hH1, hHint, hHae⟩ := henv ξ hξ D hD 4 (by norm_num)
  let N : Set (DistRd d) := {g | ¬ (∀ z ∈ closedBall (0 : Rd d) 4,
      ∀ r ∈ Ioc (0 : ℝ) 1,
        diamIn (rho D g) (ball z (2 * r)) (ball z r) ≤ ENNReal.ofReal (H g * r ^ σ))}
  let B : Set (DistRd d) := {g | ENNReal.ofReal (Hsd ^ p₁) ≤ ENNReal.ofReal (H g ^ p₁)}
  have hN0 : pinLaw d 1 N = 0 := by
    apply ae_iff.mp
    filter_upwards [hHae] with g hg
    exact hg.1
  have hsub : {g | ¬ DUpper (rho D g) (siteA d) Hsd σ} ⊆ N ∪ B := by
    intro g hbad
    by_contra hcon
    simp only [mem_union, N, B, Set.mem_ofPred_eq, not_or, not_not] at hcon
    have hHt : H g ≤ Hsd := by
      by_contra hgt
      have hgt' : Hsd < H g := lt_of_not_ge hgt
      apply hcon.2
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hHsd0.le hgt'.le hp₁.le)
    apply hbad
    exact q10_dupper_mono hHt (q10_dupper_of_envelope hcon.1)
  have hHpow : c₀ / p ≤ Hsd ^ p₁ := by
    calc
      c₀ / p = ((c₀ / p) ^ p₁⁻¹) ^ p₁ :=
        (Real.rpow_inv_rpow (by positivity) hp₁.ne').symm
      _ ≤ Hsd ^ p₁ := Real.rpow_le_rpow (by positivity) (le_max_right _ _) hp₁.le
  have hmk := p5b_markov (μ := pinLaw d 1)
    (f := fun g => ENNReal.ofReal (H g ^ p₁))
    (ENNReal.measurable_ofReal.comp (hHm.pow_const p₁)).aemeasurable
    (Real.rpow_pos_of_pos hHsd0 p₁) hHint
  have hB : pinLaw d 1 B ≤ ENNReal.ofReal p := by
    refine hmk.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hHsd0 p₁)]
    rw [div_le_iff₀ hp] at hHpow
    linarith
  calc
    pinLaw d 1 {g | ¬ DUpper (rho D g) (siteA d) Hsd σ} ≤ pinLaw d 1 (N ∪ B) := measure_mono hsub
    _ ≤ pinLaw d 1 N + pinLaw d 1 B := measure_union_le _ _
    _ ≤ ENNReal.ofReal p := by simpa only [hN0, zero_add] using hB

/-- Uniform high probability of all four site references (F1). -/
theorem siteRefs_prob_bound {d : ℕ} (hd : 2 ≤ d) {ξbar : ℝ}
    (hU : UniformEstimates d ξbar 1) {p : ℝ} (hp : 0 < p) :
    ∃ Hup σ Hlo β mc A0 : ℝ,
      1 ≤ Hup ∧ 0 < σ ∧ σ ≤ 1 ∧ 1 ≤ Hlo ∧ 1 ≤ β ∧ 0 < mc ∧ Hlo⁻¹ ≤ A0 ∧
      ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ∀ D : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D →
          pinLaw d 1 {g | ¬ SiteRefs Hup σ Hlo β mc A0 (rho D g)} ≤ ENNReal.ofReal p := by
  obtain ⟨p₁, σ, β, C, A, hp₁, hσ, hσ1, hβ, hC, hA, henv⟩ := hU.envelope
  obtain ⟨K₁, hK₁⟩ := hU.cross 0 1 (3 / 2) 1 (by norm_num) (by norm_num) one_pos
  obtain ⟨K₂, hK₂⟩ := hU.cross 0 (5 / 2) 3 1 (by norm_num) (by norm_num) one_pos
  obtain ⟨pp, hpp, hdiam⟩ := hU.diam
  have hsiteCompact := q10_siteC_isCompact (d := d)
  have hsiteA := q10_siteC_subset_siteA (d := d)
  obtain ⟨K₃, hK₃⟩ := hdiam (siteA d) (siteC d) isOpen_annA p5b_isBounded_annA
    (p5b_isConnected_annA hd) hsiteCompact hsiteA
  let ε : ℝ := p / 4
  have hε : 0 < ε := by dsimp [ε]; positivity
  let c₀ : ℝ := C * (1 + 4) ^ A
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  let H0 : ℝ := max 1 ((c₀ / ε) ^ p₁⁻¹)
  have hH0 : 1 ≤ H0 := le_max_left _ _
  have hH0pos : 0 < H0 := lt_of_lt_of_le one_pos hH0
  let Kcross : ℝ := max (max K₁ K₂) 1
  have hKcross : 1 ≤ Kcross := le_max_right _ _
  let mc : ℝ := ε / Kcross
  have hmc : 0 < mc := div_pos hε (lt_of_lt_of_le one_pos hKcross)
  let Kdiam : ℝ := max K₃ 1
  have hKdiam : 1 ≤ Kdiam := le_max_right _ _
  let A0 : ℝ := max H0⁻¹ ((Kdiam / ε) ^ pp⁻¹)
  have hA0 : H0⁻¹ ≤ A0 := le_max_left _ _
  have hA0pos : 0 < A0 := (inv_pos.mpr hH0pos).trans_le hA0
  refine ⟨H0, σ, H0, β, mc, A0, hH0, hσ, hσ1.le, hH0, hβ.le, hmc, hA0, ?_⟩
  intro ξ hξ D hD
  have hprob := isProbabilityMeasure_pinLaw hd (1 : ℝ)
  have hl := p5b_ae_isLength_rho hd hD one_pos
  obtain ⟨H, hHm, hH1, hHint, hHae⟩ := henv ξ hξ D hD 4 (by norm_num)
  let N : Set (DistRd d) := {g | ¬ ((∀ z ∈ closedBall (0 : Rd d) 4,
      ∀ r ∈ Ioc (0 : ℝ) 1,
        diamIn (rho D g) (ball z (2 * r)) (ball z r) ≤ ENNReal.ofReal (H g * r ^ σ)) ∧
      (∀ x ∈ closedBall (0 : Rd d) 4, ∀ y ∈ closedBall (0 : Rd d) 4,
        (H g)⁻¹ * ‖x - y‖ ^ β ≤ (rho D g).1 (x, y)))}
  let B₀ : Set (DistRd d) := {g | ENNReal.ofReal (H0 ^ p₁) ≤ ENNReal.ofReal (H g ^ p₁)}
  let B₁ : Set (DistRd d) := {g | ENNReal.ofReal mc⁻¹ ≤
    (setDistIn (rho D g) univ (sphere 0 1) (sphere 0 (3 / 2)))⁻¹ ^ (1 : ℝ)}
  let B₂ : Set (DistRd d) := {g | ENNReal.ofReal mc⁻¹ ≤
    (setDistIn (rho D g) univ (sphere 0 (5 / 2)) (sphere 0 3))⁻¹ ^ (1 : ℝ)}
  let B₃ : Set (DistRd d) := {g | ENNReal.ofReal (A0 ^ pp) ≤
    diamIn (rho D g) (siteA d) (siteC d) ^ pp}
  have hN0 : pinLaw d 1 N = 0 := by
    apply ae_iff.mp
    filter_upwards [hHae] with g hg
    exact hg
  have hB0 : pinLaw d 1 B₀ ≤ ENNReal.ofReal ε := by
    have hmk := p5b_markov (μ := pinLaw d 1)
      (f := fun g => ENNReal.ofReal (H g ^ p₁))
      (ENNReal.measurable_ofReal.comp (hHm.pow_const p₁)).aemeasurable
      (Real.rpow_pos_of_pos hH0pos p₁) hHint
    refine hmk.trans (ENNReal.ofReal_le_ofReal ?_)
    have hpow : c₀ / ε ≤ H0 ^ p₁ := by
      calc
        c₀ / ε = ((c₀ / ε) ^ p₁⁻¹) ^ p₁ :=
          (Real.rpow_inv_rpow (by positivity) hp₁.ne').symm
        _ ≤ H0 ^ p₁ := Real.rpow_le_rpow (by positivity) (le_max_right _ _) hp₁.le
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hH0pos p₁)]
    rw [div_le_iff₀ hε] at hpow
    linarith
  have hcrossProb (a b : ℝ) (K : ℝ) (hKK : K ≤ Kcross)
      (hKint : ∫⁻ g, (setDistIn (rho D g) univ (sphere (0 : Rd d) a) (sphere 0 b))⁻¹ ^
          (1 : ℝ) ∂(pinLaw d 1) ≤ ENNReal.ofReal K) :
      pinLaw d 1 {g | ENNReal.ofReal mc⁻¹ ≤
        (setDistIn (rho D g) univ (sphere 0 a) (sphere 0 b))⁻¹ ^ (1 : ℝ)} ≤
        ENNReal.ofReal ε := by
    have hX := p5b_aemeasurable_setDistIn_univ hD.measurable (pinLaw d 1) hl
      (sphere 0 a) (sphere 0 b)
    have hmk := p5b_markov (μ := pinLaw d 1)
      (f := fun g => (setDistIn (rho D g) univ (sphere 0 a) (sphere 0 b))⁻¹ ^ (1 : ℝ))
      (hX.inv.pow_const 1) (inv_pos.mpr hmc) hKint
    refine hmk.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [div_inv_eq_mul]
    calc K * mc ≤ Kcross * mc := mul_le_mul_of_nonneg_right hKK hmc.le
      _ = ε := by dsimp [mc]; field_simp
  have hB1 : pinLaw d 1 B₁ ≤ ENNReal.ofReal ε :=
    hcrossProb 1 (3 / 2) K₁ (le_trans (le_max_left _ _) (le_max_left _ _)) (hK₁ ξ hξ D hD)
  have hB2 : pinLaw d 1 B₂ ≤ ENNReal.ofReal ε :=
    hcrossProb (5 / 2) 3 K₂ (le_trans (le_max_right _ _) (le_max_left _ _)) (hK₂ ξ hξ D hD)
  have hB3 : pinLaw d 1 B₃ ≤ ENNReal.ofReal ε := by
    have hY := aemeasurable_diamIn_of_ae_length (pinLaw d 1) (rho D)
      (measurable_rho hD.measurable) hl isOpen_annA hsiteA
    have hmk := p5b_markov (μ := pinLaw d 1)
      (f := fun g => diamIn (rho D g) (siteA d) (siteC d) ^ pp)
      (hY.pow_const pp) (Real.rpow_pos_of_pos hA0pos pp) (hK₃ ξ hξ D hD)
    refine hmk.trans (ENNReal.ofReal_le_ofReal ?_)
    have hpow : Kdiam / ε ≤ A0 ^ pp := by
      calc
        Kdiam / ε = ((Kdiam / ε) ^ pp⁻¹) ^ pp :=
          (Real.rpow_inv_rpow (by positivity) hpp.ne').symm
        _ ≤ A0 ^ pp := Real.rpow_le_rpow (by positivity) (le_max_right _ _) hpp.le
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hA0pos pp)]
    rw [div_le_iff₀ hε] at hpow
    nlinarith only [hpow, le_max_left K₃ 1]
  have hsub : {g | ¬ SiteRefs H0 σ H0 β mc A0 (rho D g)} ⊆ N ∪ B₀ ∪ B₁ ∪ B₂ ∪ B₃ := by
    intro g hg
    by_contra hcon
    simp only [mem_union, N, B₀, B₁, B₂, B₃, Set.mem_ofPred_eq, not_or, not_not] at hcon
    obtain ⟨⟨⟨⟨hgood, hnot0⟩, hnot1⟩, hnot2⟩, hnot3⟩ := hcon
    have hHle : H g ≤ H0 := by
      by_contra hgt
      exact hnot0 (ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow hH0pos.le (le_of_not_ge hgt) hp₁.le))
    apply hg
    have hdup : DUpper (rho D g) (siteA d) H0 σ :=
      q10_dupper_mono hHle (q10_dupper_of_envelope hgood.1)
    have hlow : ∀ x ∈ siteC d, ∀ y ∈ siteC d,
        ENNReal.ofReal (H0⁻¹ * ‖x - y‖ ^ β) ≤ (rho D g).internal (siteA d) x y := by
      intro x hx y hy
      have hxy := hgood.2 x (q10_siteC_subset_closedBall_four hx) y
        (q10_siteC_subset_closedBall_four hy)
      have hHpos : 0 < H g := by linarith [hH1 g]
      have hinv : H0⁻¹ ≤ (H g)⁻¹ := inv_anti₀ hHpos hHle
      have hpow : 0 ≤ ‖x - y‖ ^ β := Real.rpow_nonneg (norm_nonneg _) _
      have hreal := (mul_le_mul_of_nonneg_right hinv hpow).trans hxy
      exact (ENNReal.ofReal_le_ofReal hreal).trans ((rho D g).ofReal_le_internal (siteA d) x y)
    have hcross (a b : ℝ) (hnot : ¬ ENNReal.ofReal mc⁻¹ ≤
        (setDistIn (rho D g) univ (sphere 0 a) (sphere 0 b))⁻¹ ^ (1 : ℝ)) :
        ENNReal.ofReal mc ≤ setDistIn (rho D g) (siteA d) (sphere 0 a) (sphere 0 b) := by
      have hcr : ENNReal.ofReal mc ≤ setDistIn (rho D g) univ (sphere 0 a) (sphere 0 b) := by
        by_contra hlt
        apply hnot
        rw [ENNReal.rpow_one]
        rw [ENNReal.ofReal_inv_of_pos hmc]
        exact ENNReal.inv_le_inv.2 (le_of_not_ge hlt)
      exact hcr.trans (p5b_setDistIn_univ_le (rho D g) (siteA d) (sphere 0 a) (sphere 0 b))
    have hdiam : diamIn (rho D g) (siteA d) (siteC d) ≤ ENNReal.ofReal A0 := by
      by_contra hlt
      apply hnot3
      rw [← ENNReal.ofReal_rpow_of_nonneg hA0pos.le hpp.le]
      exact ENNReal.rpow_le_rpow (le_of_not_ge hlt) hpp.le
    exact ⟨hdup, hlow, hcross 1 (3 / 2) hnot1,
      hcross (5 / 2) 3 hnot2, hdiam⟩
  calc
    pinLaw d 1 {g | ¬ SiteRefs H0 σ H0 β mc A0 (rho D g)} ≤
        pinLaw d 1 (N ∪ B₀ ∪ B₁ ∪ B₂ ∪ B₃) := measure_mono hsub
    _ ≤ pinLaw d 1 N + pinLaw d 1 B₀ + pinLaw d 1 B₁ + pinLaw d 1 B₂ + pinLaw d 1 B₃ := by
      refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
      refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
      refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
      exact measure_union_le _ _
    _ ≤ ENNReal.ofReal p := by
      rw [hN0]
      calc
        0 + pinLaw d 1 B₀ + pinLaw d 1 B₁ + pinLaw d 1 B₂ + pinLaw d 1 B₃ ≤
          0 + ENNReal.ofReal ε + ENNReal.ofReal ε + ENNReal.ofReal ε + ENNReal.ofReal ε := by
            gcongr
        _ = ENNReal.ofReal p := by
          rw [zero_add, ← ENNReal.ofReal_add hε.le hε.le,
            ← ENNReal.ofReal_add (by positivity) hε.le,
            ← ENNReal.ofReal_add (by positivity) hε.le]
          congr 1
          dsimp [ε]
          ring

end HigherDimLQGContinuity
