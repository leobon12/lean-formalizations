import QuantumZipper.Proofs.RS.OnePointFinal
import QuantumZipper.Proofs.RS.TraceMeas

/-!
# Corollary 1.5, input R: the mass of hull neighbourhoods (probabilistic part)

Task COR15-R. For a finite measure `σ` carried by `ℍ` with `∫ (Im z)^{-1/4} dσ < ∞` (e.g. a
folded circle) and `0 < κ < 4`, almost surely

  `σ{z : dist(z, η[0,∞)) ≤ ε} ≤ c ε^{1/8}` for all `0 < ε ≤ 1`

(`ae_measure_infDist_le_pow`), with a random `c`. Through the strip transfer
(`Cor15Group.map_revMapInv_im_le`) this is the boundary-layer input for the pushed measures of
(R), since the hull `η(0,t]` contains every point of `ℍ \ f_t⁻¹(ℍ)` (Rohde–Schramm 2005,
Thm 6.1; `RS.ae_fwdHull_eq_sleTrace_image_of_le_four`).

Sources: the one-point estimate `P(dist(z, η) < ε) ≤ C (ε / Im z)^{1-κ/8}` (Beffara, *The
dimension of the SLE curves*, Ann. Probab. 36 (2008), Prop. 4, p. 6; project theorem
`RS.sleOnePointBound`). The passage to an almost-sure bound uniform in `ε` (Tonelli over
`P ⊗ σ` with the measurable trace `RS.exists_measurable_sleTrace`, a weighted dyadic sum and
Markov) is an **own elementary argument**; the measurability step follows
`Thm11Area.measurableSet_mem_image_Ici`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric EMetric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

/-- Joint measurability of `(ω, z) ↦ infEDist z (η_ω[0,∞))` for a jointly measurable family of
continuous paths (countable dense times). -/
theorem measurable_infEDist_image_Ici {Ω : Type*} [MeasurableSpace Ω] {η : Ω → ℝ → ℂ}
    (hη : Measurable η) (hc : ∀ ω, Continuous (η ω)) :
    Measurable fun p : Ω × ℂ => infEDist p.2 (η p.1 '' Ici 0) := by
  set D : Set ℝ := Ici 0 ∩ range ((↑) : ℚ → ℝ) with hDdef
  have hDc : D.Countable := (countable_range _).mono inter_subset_right
  have hkey : ∀ ω, closure (η ω '' D) = closure (η ω '' Ici 0) := by
    intro ω
    refine subset_antisymm (closure_mono (image_mono inter_subset_left)) ?_
    refine closure_minimal ?_ isClosed_closure
    have h1 : Ici (0 : ℝ) ⊆ closure D := by
      rw [← closure_Ioi (0 : ℝ)]
      exact closure_minimal ((Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioi).trans
        (closure_mono (inter_subset_inter_left _ Ioi_subset_Ici_self))) isClosed_closure
    exact (image_mono h1).trans (image_closure_subset_closure_image (hc ω))
  have e : (fun p : Ω × ℂ => infEDist p.2 (η p.1 '' Ici 0))
      = fun p => ⨅ t : D, edist p.2 (η p.1 t) := by
    funext p
    rw [← infEDist_closure, ← hkey, infEDist_closure, infEDist, iInf_image, iInf_subtype']
  rw [e]
  have := hDc.to_subtype
  exact Measurable.iInf fun t => measurable_snd.edist
    ((measurable_pi_apply (t : ℝ)).comp (hη.comp measurable_fst))

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

/-- The one-point estimate in the form used here: for `z ∈ ℍ` and every `ε > 0`,
`P(dist(z, η) < ε) ≤ C₁ (ε / Im z)^{1/4}`. -/
theorem exists_prob_infDist_lt_le {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) :
    ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P → ∀ z ∈ H, ∀ ε : ℝ,
      0 < ε → P {ω | infDist z (sleTrace κ B ω '' Ici 0) < ε} ≤
        ENNReal.ofReal (C₁ * (ε / z.im) ^ (1 / 4 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := Blueprint.sleOnePointBound_pos_const RS.sleOnePointBound κ hκ hκ4
  refine ⟨max C 1, le_max_right _ _, fun P _ B hB z hz ε hε => ?_⟩
  have hz0 : 0 < z.im := hz
  have hx0 : 0 < ε / z.im := div_pos hε hz0
  by_cases hεz : ε ≤ z.im
  · refine (hC P B hB z hz ε hε hεz).trans (ENNReal.ofReal_le_ofReal ?_)
    have hx1 : ε / z.im ≤ 1 := (div_le_one hz0).2 hεz
    have h1 : (ε / z.im) ^ (1 - κ / 8) ≤ (ε / z.im) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)
    have hy0 : 0 ≤ z.im / ‖z‖ := div_nonneg hz0.le (norm_nonneg _)
    have hy1 : z.im / ‖z‖ ≤ 1 := div_le_one_of_le₀ (Complex.im_le_norm z) (norm_nonneg _)
    have h2 : (z.im / ‖z‖) ^ (8 / κ - 1) ≤ 1 :=
      Real.rpow_le_one hy0 hy1 (by rw [sub_nonneg, le_div_iff₀ hκ]; linarith)
    have h3 : 0 ≤ (ε / z.im) ^ (1 - κ / 8) := Real.rpow_nonneg hx0.le _
    calc C * (ε / z.im) ^ (1 - κ / 8) * (z.im / ‖z‖) ^ (8 / κ - 1)
        ≤ C * (ε / z.im) ^ (1 - κ / 8) * 1 := by gcongr
      _ ≤ max C 1 * (ε / z.im) ^ (1 / 4 : ℝ) := by
        rw [mul_one]; exact mul_le_mul (le_max_left _ _) h1 h3 (by positivity)
  · refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have hx1 : 1 ≤ ε / z.im := (one_le_div hz0).2 (le_of_not_ge hεz)
    have h1 : 1 ≤ (ε / z.im) ^ (1 / 4 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
    nlinarith [le_max_right C 1]

theorem rpow_one_div_pow_natCast {x : ℝ} (hx : 0 ≤ x) (n k : ℕ) (hk : k ≠ 0) :
    ((x ^ k) ^ n) ^ ((k : ℝ)⁻¹) = x ^ n := by
  rw [← pow_mul, mul_comm, pow_mul]
  exact Real.pow_rpow_inv_natCast (pow_nonneg hx n) hk

/-- **A.s. polynomial mass of hull neighbourhoods** (own elementary argument from Beffara's
one-point estimate). -/
theorem ae_measure_infDist_le_pow (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {σ : Measure ℂ} [IsFiniteMeasure σ] (hσH : ∀ᵐ z ∂σ, z ∈ H)
    (hσI : ∫⁻ z, ENNReal.ofReal (z.im ^ (-(1 / 4 : ℝ))) ∂σ ≠ ⊤) :
    ∀ᵐ ω ∂P, ∃ c : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      σ {z | infDist z (sleTrace κ B ω '' Ici 0) ≤ ε} ≤
        ENNReal.ofReal (c * ε ^ (1 / 8 : ℝ)) := by
  obtain ⟨C₁, hC₁, hone⟩ := exists_prob_infDist_lt_le hκ hκ4
  obtain ⟨η, -, hηm, hηc, hηeq⟩ := RS.exists_measurable_sleTrace hB hκ (by linarith)
  have himg : ∀ᵐ ω ∂P, η ω '' Ici 0 = sleTrace κ B ω '' Ici 0 :=
    hηeq.mono fun ω h => h.image_eq
  set δ : ℕ → ℝ := fun n => 2 * ((1 : ℝ) / 256) ^ n with hδ
  have hδ0 : ∀ n, 0 < δ n := fun n => by positivity
  set E : ℕ → Set (Ω × ℂ) :=
    fun n => {p | infEDist p.2 (η p.1 '' Ici 0) < ENNReal.ofReal (δ n)} with hE
  have hEm : ∀ n, MeasurableSet (E n) := fun n =>
    measurableSet_lt (measurable_infEDist_image_Ici hηm hηc) measurable_const
  set A : ℕ → Ω → ℝ≥0∞ := fun n ω => σ (Prod.mk ω ⁻¹' E n) with hA
  have hAm : ∀ n, Measurable (A n) := fun n => measurable_measure_prodMk_left (hEm n)
  have hconv : ∀ ω (z : ℂ) (r : ℝ), infEDist z (η ω '' Ici 0) < ENNReal.ofReal r ↔
      infDist z (η ω '' Ici 0) < r := by
    intro ω z r
    have hne : (η ω '' Ici 0).Nonempty := ⟨_, mem_image_of_mem _ (mem_Ici.2 (le_refl (0 : ℝ)))⟩
    rw [infEDist_lt_iff, infDist_lt_iff hne]
    simp only [edist_lt_ofReal]
  set M := ∫⁻ z, ENNReal.ofReal (z.im ^ (-(1 / 4 : ℝ))) ∂σ with hM
  have hexp : ∀ n, ∫⁻ ω, A n ω ∂P ≤ ENNReal.ofReal (C₁ * δ n ^ (1 / 4 : ℝ)) * M := by
    intro n
    rw [← Measure.prod_apply (hEm n), Measure.prod_apply_symm (hEm n),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [hσH] with z hz
    have hz0 : 0 < z.im := hz
    have hset : (fun ω => (ω, z)) ⁻¹' E n =ᵐ[P]
        {ω | infDist z (sleTrace κ B ω '' Ici 0) < δ n} := by
      filter_upwards [himg] with ω hω
      apply propext
      show infEDist z (η ω '' Ici 0) < ENNReal.ofReal (δ n) ↔
        infDist z (sleTrace κ B ω '' Ici 0) < δ n
      rw [hconv, hω]
    rw [measure_congr hset]
    refine (hone P B hB z hz (δ n) (hδ0 n)).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (by positivity), Real.div_rpow (hδ0 n).le hz0.le,
      Real.rpow_neg hz0.le]
    congr 1
    rw [div_eq_mul_inv]
    ring
  have h4 : ∀ n : ℕ, (((1 : ℝ) / 256) ^ n) ^ (1 / 4 : ℝ) = ((1 : ℝ) / 4) ^ n := by
    intro n
    have e : ((1 : ℝ) / 256) ^ n = (((1 : ℝ) / 4) ^ 4) ^ n := by norm_num
    rw [e, show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
    exact rpow_one_div_pow_natCast (by norm_num) n 4 (by norm_num)
  have hδq : ∀ n : ℕ, (2 : ℝ) ^ n * (C₁ * δ n ^ (1 / 4 : ℝ)) =
      C₁ * 2 ^ (1 / 4 : ℝ) * ((1 : ℝ) / 2) ^ n := by
    intro n
    simp only [hδ]
    rw [Real.mul_rpow (by norm_num) (by positivity), h4]
    have : (2 : ℝ) ^ n * ((1 : ℝ) / 4) ^ n = ((1 : ℝ) / 2) ^ n := by rw [← mul_pow]; norm_num
    calc (2 : ℝ) ^ n * (C₁ * (2 ^ (1 / 4 : ℝ) * ((1 : ℝ) / 4) ^ n))
        = C₁ * 2 ^ (1 / 4 : ℝ) * ((2 : ℝ) ^ n * ((1 : ℝ) / 4) ^ n) := by ring
      _ = _ := by rw [this]
  set Y : Ω → ℝ≥0∞ := fun ω => ∑' n, (2 : ℝ≥0∞) ^ n * A n ω with hY
  have hYm : Measurable Y := Measurable.ennreal_tsum fun n => (hAm n).const_mul _
  have hhalf : ENNReal.ofReal ((1 : ℝ) / 2) = 2⁻¹ := by
    rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; simp
  have hYint : ∫⁻ ω, Y ω ∂P ≠ ⊤ := by
    rw [hY, lintegral_tsum fun n => ((hAm n).const_mul _).aemeasurable]
    have hle : ∀ n, ∫⁻ ω, (2 : ℝ≥0∞) ^ n * A n ω ∂P ≤
        ENNReal.ofReal (C₁ * 2 ^ (1 / 4 : ℝ)) * M * 2⁻¹ ^ n := by
      intro n
      rw [lintegral_const_mul _ (hAm n)]
      calc (2 : ℝ≥0∞) ^ n * ∫⁻ ω, A n ω ∂P
          ≤ (2 : ℝ≥0∞) ^ n * (ENNReal.ofReal (C₁ * δ n ^ (1 / 4 : ℝ)) * M) := by
            gcongr; exact hexp n
        _ = ENNReal.ofReal ((2 : ℝ) ^ n * (C₁ * δ n ^ (1 / 4 : ℝ))) * M := by
            rw [ENNReal.ofReal_mul (p := (2 : ℝ) ^ n) (by positivity),
              ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
            ring
        _ = _ := by
            rw [hδq, ENNReal.ofReal_mul (p := C₁ * 2 ^ (1 / 4 : ℝ)) (by positivity),
              ENNReal.ofReal_pow (by norm_num), hhalf]
            ring
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hσI) ENNReal.ofNat_ne_top
  filter_upwards [ae_lt_top hYm hYint, himg] with ω hYω hω
  refine ⟨2 * (Y ω).toReal, fun ε hε hε1 => ?_⟩
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (x := 1 / ε) (y := (256 : ℝ))
    (by rw [le_div_iff₀ hε]; linarith) (by norm_num)
  have hεδ : ε ≤ ((1 : ℝ) / 256) ^ n := by
    rw [div_pow, one_pow, le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ hε] at hn1
    linarith
  have hεδ' : ((1 : ℝ) / 256) ^ (n + 1) < ε := by
    rw [div_pow, one_pow, div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hn2
    linarith
  -- the set is inside the `n`-th section
  have hsub : {z | infDist z (sleTrace κ B ω '' Ici 0) ≤ ε} ⊆ Prod.mk ω ⁻¹' E n := by
    intro z hz
    show infEDist z (η ω '' Ici 0) < ENNReal.ofReal (δ n)
    rw [hconv, hω]
    have : ((1 : ℝ) / 256) ^ n < δ n := by
      simp only [hδ]; linarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 256) n]
    exact lt_of_le_of_lt (hz.trans hεδ) this
  have hA2 : A n ω ≤ (2 : ℝ≥0∞)⁻¹ ^ n * Y ω := by
    have h2 : (2 : ℝ≥0∞) ^ n * A n ω ≤ Y ω :=
      ENNReal.le_tsum (f := fun n => (2 : ℝ≥0∞) ^ n * A n ω) n
    calc A n ω = (2 : ℝ≥0∞)⁻¹ ^ n * ((2 : ℝ≥0∞) ^ n * A n ω) := by
          rw [← mul_assoc, ← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num),
            one_pow, one_mul]
      _ ≤ _ := by gcongr
  have hYr : (2 : ℝ≥0∞)⁻¹ ^ n * Y ω = ENNReal.ofReal (((1 : ℝ) / 2) ^ n * (Y ω).toReal) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hYω.ne,
      ENNReal.ofReal_pow (by norm_num), hhalf]
  have h8 : ((1 : ℝ) / 2) ^ n ≤ 2 * ε ^ (1 / 8 : ℝ) := by
    have e : ((1 : ℝ) / 256) ^ (n + 1) = (((1 : ℝ) / 2) ^ 8) ^ (n + 1) := by norm_num
    have h1 := Real.rpow_le_rpow (by positivity) hεδ'.le (by norm_num : (0 : ℝ) ≤ 1 / 8)
    rw [e, show (1 / 8 : ℝ) = ((8 : ℕ) : ℝ)⁻¹ by norm_num,
      rpow_one_div_pow_natCast (by norm_num) (n + 1) 8 (by norm_num)] at h1
    rw [show (1 / 8 : ℝ) = ((8 : ℕ) : ℝ)⁻¹ by norm_num]
    rw [pow_succ] at h1
    linarith
  calc σ {z | infDist z (sleTrace κ B ω '' Ici 0) ≤ ε} ≤ A n ω := measure_mono hsub
    _ ≤ ENNReal.ofReal (((1 : ℝ) / 2) ^ n * (Y ω).toReal) := hA2.trans hYr.le
    _ ≤ ENNReal.ofReal (2 * (Y ω).toReal * ε ^ (1 / 8 : ℝ)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hY0 : 0 ≤ (Y ω).toReal := ENNReal.toReal_nonneg
        nlinarith

end Cor15Group
end QuantumZipper
