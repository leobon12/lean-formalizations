import LQGMetric.Papers.DDDF.S6P26Up0




 



set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Exponent.Moments

 


theorem moment_consequences (μ lam M₂ R S : ℝ) (hlam : 0 < lam)
    (hgeomLower : Real.exp (-R) * lam ≤ μ)
    (hgeomUpper : μ ≤ Real.exp R * lam)
    (hgeomSecond : M₂ ≤ (Real.exp S * lam) ^ 2) :
    0 < μ ∧ |Real.log μ - Real.log lam| ≤ R ∧
      Real.sqrt M₂ / μ ≤ Real.exp (S + R) := by
  have hμ : 0 < μ := (mul_pos (Real.exp_pos _) hlam).trans_le hgeomLower
  have hloglo : -R + Real.log lam ≤ Real.log μ := by
    have h := Real.log_le_log (mul_pos (Real.exp_pos _) hlam) hgeomLower
    rw [Real.log_mul (Real.exp_pos _).ne' hlam.ne', Real.log_exp] at h
    exact h
  have hloghi : Real.log μ ≤ R + Real.log lam := by
    have h := Real.log_le_log hμ hgeomUpper
    rw [Real.log_mul (Real.exp_pos _).ne' hlam.ne', Real.log_exp] at h
    exact h
  have hlog : |Real.log μ - Real.log lam| ≤ R := by
    rw [abs_le]
    constructor <;> linarith
  have hM : Real.sqrt M₂ ≤ Real.exp S * lam := by
    have h := Real.sqrt_le_sqrt hgeomSecond
    rwa [Real.sqrt_sq_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) hlam)] at h
  have hlamμ : lam ≤ Real.exp R * μ := by
    calc
      lam = Real.exp R * (Real.exp (-R) * lam) := by
        rw [← mul_assoc, ← Real.exp_add]
        simp
      _ ≤ Real.exp R * μ := mul_le_mul_of_nonneg_left hgeomLower (Real.exp_pos _).le
  refine ⟨hμ, hlog, ?_⟩
  apply (div_le_div_of_nonneg_right hM hμ.le).trans
  apply (div_le_iff₀ hμ).2
  rw [Real.exp_add]
  nlinarith [mul_le_mul_of_nonneg_left hlamμ (Real.exp_pos S).le]


 


theorem l1_07_of_annular_moments (μ lam M₂ : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hlam : ∀ n, 0 < lam n)
    (hgeomLower : ∀ n : ℕ, Real.exp (-(C * Real.sqrt n + C)) * lam n ≤ μ n)
    (hgeomUpper : ∀ n : ℕ, μ n ≤ Real.exp (C * Real.sqrt n + C) * lam n)
    (hgeomSecond : ∀ n : ℕ, M₂ n ≤
      (Real.exp (C * Real.sqrt n + C) * lam n) ^ 2) :
    ∀ n : ℕ, 0 < μ n ∧
      |Real.log (μ n) - Real.log (lam n)| ≤ C * Real.sqrt n + C ∧
      Real.sqrt (M₂ n) / μ n ≤ Real.exp (2 * C) * Real.exp (2 * C * Real.sqrt n) := by
  intro n
  have hR : 0 ≤ C * Real.sqrt n + C := by positivity
  have h := moment_consequences (μ n) (lam n) (M₂ n)
    (C * Real.sqrt n + C) (C * Real.sqrt n + C)
    (hlam n) (hgeomLower n) (hgeomUpper n) (hgeomSecond n)
  refine ⟨h.1, h.2.1, ?_⟩
  convert h.2.2 using 1
  rw [← Real.exp_add]
  congr 1
  ring


 

theorem four_power_absorbed (A c : ℝ) (hA : 0 ≤ A) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, m < n →
      A * (4 : ℝ) ^ m * Real.exp (-c * (n : ℝ) ^ (4 / 3 : ℝ)) ≤
        A * Real.exp (-(c / 2) * (n : ℝ) ^ (4 / 3 : ℝ)) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ n : ℕ in atTop,
      2 * Real.log 4 / c ≤ (n : ℝ) ^ (1 / 3 : ℝ) :=
    ht.eventually (eventually_ge_atTop _)
  filter_upwards [hev, eventually_ge_atTop (1 : ℕ)] with n hn hn1 m hmn
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hmreal : (m : ℝ) ≤ n := by exact_mod_cast hmn.le
  have hnfrac : (n : ℝ) ^ (4 / 3 : ℝ) = (n : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) := by
    rw [show (4 / 3 : ℝ) = 1 + 1 / 3 by ring, Real.rpow_add (by positivity),
      Real.rpow_one]
  have hcoef : 2 * Real.log 4 ≤ c * (n : ℝ) ^ (1 / 3 : ℝ) := by
    calc
      2 * Real.log 4 = c * (2 * Real.log 4 / c) := by field_simp
      _ ≤ c * (n : ℝ) ^ (1 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_left hn hc.le
  have hexp : (m : ℝ) * Real.log 4 - c * (n : ℝ) ^ (4 / 3 : ℝ) ≤
      -(c / 2) * (n : ℝ) ^ (4 / 3 : ℝ) := by
    rw [hnfrac]
    have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_right hmreal hlog,
      mul_le_mul_of_nonneg_left hcoef (by positivity : (0 : ℝ) ≤ n)]
  have h4m : (4 : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log 4) := by
    calc
      (4 : ℝ) ^ m = (Real.exp (Real.log 4)) ^ m := by rw [Real.exp_log (by norm_num)]
      _ = Real.exp ((m : ℝ) * Real.log 4) := by rw [← Real.exp_nat_mul]
  calc
    A * (4 : ℝ) ^ m * Real.exp (-c * (n : ℝ) ^ (4 / 3 : ℝ))
        = A * Real.exp ((m : ℝ) * Real.log 4 - c * (n : ℝ) ^ (4 / 3 : ℝ)) := by
            rw [h4m, mul_assoc, ← Real.exp_add, sub_eq_add_neg]
            ring_nf
    _ ≤ A * Real.exp (-(c / 2) * (n : ℝ) ^ (4 / 3 : ℝ)) := by
          gcongr


 


theorem coarse_event_tail_of_gradient_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (g : ℕ → Ω → ℝ)
    (A c D : ℝ) (hA : 0 ≤ A) (hc : 0 < c) (hD : 0 < D)
    (hGradientTail : ∀ (m : ℕ) (x : ℝ), 0 ≤ x →
      P.real {ω | x ≤ g m ω} ≤
        A * (4 : ℝ) ^ m * Real.exp (-c * x ^ 2)) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, m < n →
      P.real ({ω | g m ω ≤ D * (n : ℝ) ^ (2 / 3 : ℝ)}ᶜ) ≤
        A * Real.exp (-(c * D ^ 2 / 2) * (n : ℝ) ^ (4 / 3 : ℝ)) := by
  have hAbsorb := four_power_absorbed A (c * D ^ 2) hA (by positivity)
  filter_upwards [hAbsorb] with n hn m hmn
  let x : ℝ := D * (n : ℝ) ^ (2 / 3 : ℝ)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hset : {ω | g m ω ≤ x}ᶜ ⊆ {ω | x ≤ g m ω} := by
    intro ω hω
    change ¬g m ω ≤ x at hω
    exact (le_of_lt (not_le.mp hω))
  have hmeasure : P.real ({ω | g m ω ≤ x}ᶜ) ≤
      P.real {ω | x ≤ g m ω} := measureReal_mono hset
  have hpow : ((n : ℝ) ^ (2 / 3 : ℝ)) ^ 2 =
      (n : ℝ) ^ (4 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    ring
  have hx2 : -c * x ^ 2 = -(c * D ^ 2) * (n : ℝ) ^ (4 / 3 : ℝ) := by
    dsimp [x]
    rw [mul_pow, hpow]
    ring
  change P.real ({ω | g m ω ≤ x}ᶜ) ≤ _
  calc
    P.real ({ω | g m ω ≤ x}ᶜ) ≤ P.real {ω | x ≤ g m ω} := hmeasure
    _ ≤ A * (4 : ℝ) ^ m * Real.exp (-c * x ^ 2) := hGradientTail m x hx
    _ = A * (4 : ℝ) ^ m *
          Real.exp (-(c * D ^ 2) * (n : ℝ) ^ (4 / 3 : ℝ)) := by rw [hx2]
    _ ≤ A * Real.exp (-(c * D ^ 2 / 2) * (n : ℝ) ^ (4 / 3 : ℝ)) :=
      hn m hmn


 

theorem exp_sqrt_sub_four_thirds_eventually_half
    (K M c : ℝ) (hK : 0 ≤ K) (hM : 0 ≤ M) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      K * Real.exp (M * Real.sqrt n - c * (n : ℝ) ^ (4 / 3 : ℝ)) ≤ 1 / 2 := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      tendsto_natCast_atTop_atTop
  have hroot : ∀ᶠ n : ℕ in atTop,
      (M + 1) / c ≤ (n : ℝ) ^ (1 / 3 : ℝ) :=
    ht.eventually (eventually_ge_atTop _)
  have hlim : Tendsto (fun n : ℕ => K * Real.exp (-(n : ℝ))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      tendsto_natCast_atTop_atTop).const_mul K
  have hsmall : ∀ᶠ n : ℕ in atTop, K * Real.exp (-(n : ℝ)) < 1 / 2 :=
    hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hroot, hsmall, eventually_ge_atTop (1 : ℕ)] with n hn hsmalln hn1
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hsqrt : Real.sqrt n ≤ (n : ℝ) := by
    simpa only [Real.sqrt_eq_rpow, Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hnreal (by norm_num : (1 / 2 : ℝ) ≤ 1))
  have hnfrac : (n : ℝ) ^ (4 / 3 : ℝ) = (n : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) := by
    rw [show (4 / 3 : ℝ) = 1 + 1 / 3 by ring, Real.rpow_add (by positivity),
      Real.rpow_one]
  have hcoef : M + 1 ≤ c * (n : ℝ) ^ (1 / 3 : ℝ) := by
    calc
      M + 1 = c * ((M + 1) / c) := by field_simp
      _ ≤ c * (n : ℝ) ^ (1 / 3 : ℝ) := mul_le_mul_of_nonneg_left hn hc.le
  have hpow : (M + 1) * (n : ℝ) ≤ c * (n : ℝ) ^ (4 / 3 : ℝ) := by
    rw [hnfrac]
    nlinarith [mul_le_mul_of_nonneg_left hcoef (by positivity : (0 : ℝ) ≤ n)]
  have hexp : M * Real.sqrt n - c * (n : ℝ) ^ (4 / 3 : ℝ) ≤ -(n : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hsqrt hM]
  calc
    K * Real.exp (M * Real.sqrt n - c * (n : ℝ) ^ (4 / 3 : ℝ))
        ≤ K * Real.exp (-(n : ℝ)) := by gcongr
    _ ≤ 1 / 2 := hsmalln.le


 
theorem cs_lintegral_indicator {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ≥0∞) (E : Set Ω)
    (hX : Measurable X) (hE : MeasurableSet E) :
    (∫⁻ ω in E, X ω ∂P) ≤
      (∫⁻ ω, X ω ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) * (P E) ^ (1 / 2 : ℝ) := by
  let I : Ω → ℝ≥0∞ := E.indicator (fun _ => 1)
  have hI : Measurable I := measurable_const.indicator hE
  have hleft : (∫⁻ ω, X ω * I ω ∂P) = ∫⁻ ω in E, X ω ∂P := by
    rw [← lintegral_indicator hE]
    apply lintegral_congr
    intro ω
    by_cases hω : ω ∈ E <;> simp [I, hω]
  have hIpow : ∀ ω, I ω ^ (2 : ℝ) = I ω := by
    intro ω
    by_cases hω : ω ∈ E <;> simp [I, hω]
  have hright : (∫⁻ ω, I ω ^ (2 : ℝ) ∂P) = P E := by
    rw [lintegral_congr hIpow]
    simpa only [I, one_mul] using
      (lintegral_indicator_const₀ (μ := P) hE.nullMeasurableSet (1 : ℝ≥0∞))
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq P
    Real.HolderConjugate.two_two hX.aemeasurable hI.aemeasurable
  calc
    (∫⁻ ω in E, X ω ∂P) = ∫⁻ ω, X ω * I ω ∂P := hleft.symm
    _ ≤ (∫⁻ ω, X ω ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) *
        (∫⁻ ω, I ω ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) := by simpa using hHolder
    _ = _ := by rw [hright]


 
theorem recursion_absorb_half (u good coeff : ℝ) (hu : 0 ≤ u)
    (hcoeff : coeff ≤ 1 / 2) (hsplit : u ≤ good + coeff * u) :
    u ≤ 2 * good := by
  have hbad : coeff * u ≤ (1 / 2 : ℝ) * u :=
    mul_le_mul_of_nonneg_right hcoeff hu
  linarith


 



theorem recursion_of_covered_split (μ : ℕ → ℝ) (C K M c : ℝ)
    (hμ : ∀ n, 0 ≤ μ n) (hK : 0 ≤ K)
    (hM : 0 ≤ M) (hc : 0 < c)
    (hgeomCoveredSplit : ∀ m k : ℕ, 8 ≤ m → 1 ≤ k →
      μ (m + k) ≤
        C * Real.exp (C * ((m + k : ℕ) : ℝ) ^ (2 / 3 : ℝ)) * μ m * μ k +
        K * Real.exp (M * Real.sqrt (m + k : ℕ) -
          c * ((m + k : ℕ) : ℝ) ^ (4 / 3 : ℝ)) * μ (m + k)) :
    ∃ n₀ : ℕ, ∀ m k : ℕ, 8 ≤ m → 1 ≤ k → n₀ ≤ m + k →
      μ (m + k) ≤
        2 * C * Real.exp (C * ((m + k : ℕ) : ℝ) ^ (2 / 3 : ℝ)) * μ m * μ k := by
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1
    (exp_sqrt_sub_four_thirds_eventually_half K M c hK hM hc)
  refine ⟨n₀, ?_⟩
  intro m k hm hk hmk
  have hhalf := hn₀ (m + k) hmk
  have hsplit := hgeomCoveredSplit m k hm hk
  have habs := recursion_absorb_half (μ (m + k))
    (C * Real.exp (C * ((m + k : ℕ) : ℝ) ^ (2 / 3 : ℝ)) * μ m * μ k)
    (K * Real.exp (M * Real.sqrt (m + k : ℕ) -
      c * ((m + k : ℕ) : ℝ) ^ (4 / 3 : ℝ))) (hμ _) hhalf hsplit
  convert habs using 1; ring


 



theorem fine_annulus_mean_of_full_field_law
    {Ω F : Type*} [MeasurableSpace Ω] [MeasurableSpace F]
    (P : Measure Ω) (m : ℕ) (A : F → ℝ≥0∞)
    (fineField refField : Ω → F) (Dtile : Ω → ℝ≥0∞)
    (hA : Measurable A) (hfine : Measurable fineField)
    (href : Measurable refField)
    (hfullFieldLaw : P.map fineField = P.map refField)
    (hgeomScaleCost : ∀ ω,
      Dtile ω = ENNReal.ofReal ((2 : ℝ) ^ (-(m : ℝ))) * A (fineField ω)) :
    ∫⁻ ω, Dtile ω ∂P =
      ENNReal.ofReal ((2 : ℝ) ^ (-(m : ℝ))) *
        ∫⁻ ω, A (refField ω) ∂P := by
  have hfieldInt : (∫⁻ ω, A (fineField ω) ∂P) =
      ∫⁻ ω, A (refField ω) ∂P := by
    calc
      (∫⁻ ω, A (fineField ω) ∂P) = ∫⁻ f, A f ∂(P.map fineField) :=
        (lintegral_map hA hfine).symm
      _ = ∫⁻ f, A f ∂(P.map refField) := by rw [hfullFieldLaw]
      _ = ∫⁻ ω, A (refField ω) ∂P := lintegral_map hA href
  calc
    (∫⁻ ω, Dtile ω ∂P) =
        ∫⁻ ω, ENNReal.ofReal ((2 : ℝ) ^ (-(m : ℝ))) * A (fineField ω) ∂P :=
      lintegral_congr hgeomScaleCost
    _ = ENNReal.ofReal ((2 : ℝ) ^ (-(m : ℝ))) *
        ∫⁻ ω, A (fineField ω) ∂P :=
      lintegral_const_mul _ (hA.comp hfine)
    _ = _ := by rw [hfieldInt]


end SupercriticalLQGUniqueness.Exponent.Moments
