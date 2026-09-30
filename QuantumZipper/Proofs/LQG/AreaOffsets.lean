import QuantumZipper.Proofs.LQG.AreaOffsetsModulus

/-!
# Area analogue of M4-B4 (M4-A1 item 5), and almost sure goodness of the free field

* `ae_hasAreaLimit`: for the free field, almost surely `HasAreaLimit γ (X ω) (qAreaMeasure γ (X ω))`
  (vague convergence on `ℍ`, uniformly in the offset `a ∈ [1,2]`). Same grid-plus-modulus
  argument as `AllOffsets.ae_hasBdryLimit`, on the compacts `K_n` of `ℍ`, at scales
  `2 · 2^{-k} ≤ d_n` where folded circles are genuine circles.
* `ae_isLQGGood`: **almost surely `IsLQGGood γ (X ω)`** (regularity, boundary B4, area B4).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real Set
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace AreaOffsets

open BdryExist GaussTK TwoRadius TwoRadiusC AreaExist AllOffsets GoodSample VagueH

/-! ## Dense family along `goodFilter` -/

theorem tendsto_goodFilter_of_denseFamily {μr : ℕ × ℝ → Measure ℂ} {μ : Measure ℂ}
    (hμK : ∀ K, IsCompact K → K ⊆ H → μ K < ∞)
    (hfin : ∀ K, IsCompact K → K ⊆ H → ∀ᶠ i in goodFilter, μr i K < ∞)
    {F : Set (ℂ → ℝ)} (hF : IsDenseTestFamily F)
    (hconv : ∀ f ∈ F, Tendsto (fun i => ∫ z, f z ∂μr i) goodFilter (𝓝 (∫ z, f z ∂μ)))
    {f : ℂ → ℝ} (hf : IsTestH f) :
    Tendsto (fun i => ∫ z, f z ∂μr i) goodFilter (𝓝 (∫ z, f z ∂μ)) := by
  obtain ⟨K, hK, hKH, hfK, ⟨φ, hφF, hφ0, hφ1⟩, happrox⟩ := hF.2 f hf
  have hφ := hF.1 φ hφF
  set B := ∫ z, φ z ∂μ with hB
  have hB0 : 0 ≤ B := integral_nonneg hφ0
  have happ : ∀ (ν : Measure ℂ), ν K < ∞ → ν (tsupport φ) < ∞ → ∀ (δ : ℝ) (g : ℂ → ℝ),
      g ∈ F → tsupport g ⊆ K → (∀ z, |f z - g z| ≤ δ) → 0 ≤ δ →
      |∫ z, f z ∂ν - ∫ z, g z ∂ν| ≤ δ * ∫ z, φ z ∂ν := by
    intro ν hνK hνφ δ g hgF hgK hfg hδ
    have hi1 : Integrable f ν := hf.integrable ((measure_mono hfK).trans_lt hνK)
    have hi2 : Integrable g ν := (hF.1 g hgF).integrable ((measure_mono hgK).trans_lt hνK)
    have hi3 : Integrable φ ν := hφ.integrable hνφ
    rw [← integral_sub hi1 hi2]
    have hpt : ∀ z, ‖f z - g z‖ ≤ δ * φ z := by
      intro z
      rw [Real.norm_eq_abs]
      by_cases hz : z ∈ K
      · exact (hfg z).trans (le_mul_of_one_le_right hδ (hφ1 z hz))
      · have h1 : f z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (hfK h)
        have h2 : g z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (hgK h)
        rw [h1, h2, sub_zero, abs_zero]; exact mul_nonneg hδ (hφ0 z)
    have := norm_integral_le_of_norm_le (hi3.const_mul δ) (ae_of_all _ hpt)
    rwa [Real.norm_eq_abs, integral_const_mul] at this
  rw [Metric.tendsto_nhds]
  intro η hη
  set δ := η / (4 * (B + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨g, hgF, hgK, hfg⟩ := happrox δ hδ0
  have h1 := Metric.tendsto_nhds.1 (hconv g hgF) (η / 4) (by positivity)
  have h2 := Metric.tendsto_nhds.1 (hconv φ hφF) 1 one_pos
  have hφK := hφ.2.1.isCompact
  filter_upwards [hfin K hK hKH, hfin _ hφK hφ.2.2, h1, h2] with i hiK hiφ hi1 hi2
  rw [Real.dist_eq] at hi1 hi2 ⊢
  have ha := happ (μr i) hiK hiφ δ g hgF hgK hfg hδ0.le
  have hb := happ μ (hμK K hK hKH) (hμK _ hφK hφ.2.2) δ g hgF hgK hfg hδ0.le
  have hbi : ∫ z, φ z ∂μr i ≤ B + 1 := by linarith [(abs_lt.1 hi2).2]
  have e1 : δ * ∫ z, φ z ∂μr i ≤ η / 4 := by
    calc δ * ∫ z, φ z ∂μr i ≤ δ * (B + 1) := mul_le_mul_of_nonneg_left hbi hδ0.le
      _ = η / 4 := by rw [hδ]; field_simp
  have e2 : δ * B ≤ η / 4 := by
    calc δ * B ≤ δ * (B + 1) := mul_le_mul_of_nonneg_left (by linarith) hδ0.le
      _ = η / 4 := by rw [hδ]; field_simp
  have t1 := abs_sub_le (∫ z, f z ∂μr i) (∫ z, g z ∂μr i) (∫ z, f z ∂μ)
  have t2 := abs_sub_le (∫ z, g z ∂μr i) (∫ z, g z ∂μ) (∫ z, f z ∂μ)
  rw [abs_sub_comm (∫ z, g z ∂μ)] at t2
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-! ## Pathwise bound -/

theorem measurable_chainT_Htc (hX : IsFreeGFFModConstH X P) (γ R ε : ℝ) (m n : ℕ) :
    Measurable (fun p : Ω × ℂ => chainT m n (fun a => Htc γ X R ε p.2 a p.1)) := by
  have hH : ∀ a, Measurable (fun p : Ω × ℂ => Htc γ X R ε p.2 a p.1) := by
    intro a
    show Measurable (fun p : Ω × ℂ => (a / 2) ^ (γ ^ 2 / 2) *
      exp (γ * (zVc X R (a * ε) p.2 p.1 - zVc X R (2 * ε) p.2 p.1)))
    exact measurable_const.mul ((((measurable_zVc_swap hX R _).sub
      (measurable_zVc_swap hX R _)).const_mul _).exp)
  unfold chainT incr
  exact Finset.measurable_sum _ fun j _ => measurable_const.add
    ((Finset.measurable_sum _ fun l _ => ((hH _).sub (hH _)).pow_const 4).div_const _)

theorem pathwise_boundA (hX : IsFreeGFFModConstH X P) {γ R : ℝ} {f : ℂ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) {ω : Ω} {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith (X ω) F) (L : ℝ) {ε : ℝ} (hε : 0 < ε) (m d : ℕ) {i : ℕ}
    (hi : i ≤ 2 ^ (m + d)) :
    ENNReal.ofReal |aB γ X R f (dpt (m + d) i * ε) ω - L| ≤
      (∫⁻ z, ENNReal.ofReal (|f z| * (areaDens γ (zField X R ω) (2 * ε) z *
        chainT m (m + d) (fun a => Htc γ X R ε z a ω)))) +
      ∑ l ∈ Finset.range (2 ^ m + 1), ENNReal.ofReal |aB γ X R f (dpt m l * ε) ω - L| := by
  have hFZ := regular_zField (R := R) hF
  have ha : 0 < dpt (m + d) i := by linarith [dpt_ge_one (m + d) i]
  have ha' : 0 < dpt m (i / 2 ^ d) := by linarith [dpt_ge_one m (i / 2 ^ d)]
  have hint : ∀ r, 0 < r → Integrable (fun z => areaDens γ (zField X R ω) r z * f z) :=
    fun r hr => ((continuous_areaDens γ hFZ hr).mul hf).integrable_of_hasCompactSupport
      hfc.mul_left
  have hil : i / 2 ^ d ≤ 2 ^ m :=
    Nat.div_le_of_le_mul (by rw [pow_add] at hi; rw [mul_comm]; exact hi)
  have h1 := mul_pos ha hε
  have h2 := mul_pos ha' hε
  have hmod : ENNReal.ofReal |aB γ X R f (dpt (m + d) i * ε) ω -
      aB γ X R f (dpt m (i / 2 ^ d) * ε) ω| ≤
      ∫⁻ z, ENNReal.ofReal (|f z| * (areaDens γ (zField X R ω) (2 * ε) z *
        chainT m (m + d) (fun a => Htc γ X R ε z a ω))) := by
    rw [aB_eq_integral hX γ R h1, aB_eq_integral hX γ R h2,
      ← integral_sub (hint _ h1).integrableOn (hint _ h2).integrableOn]
    have hi2 : Integrable (fun z => |areaDens γ (zField X R ω) (dpt (m + d) i * ε) z * f z -
        areaDens γ (zField X R ω) (dpt m (i / 2 ^ d) * ε) z * f z|) :=
      ((hint _ h1).sub (hint _ h2)).abs
    refine (ENNReal.ofReal_le_ofReal (abs_integral_le_integral_abs)).trans ?_
    rw [ofReal_integral_eq_lintegral_ofReal hi2.integrableOn (ae_of_all _ fun _ => abs_nonneg _)]
    refine (setLIntegral_le_lintegral _ _).trans (lintegral_mono fun z => ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    rw [areaDens_eq_mul_Htc γ R hε ha z ω, areaDens_eq_mul_Htc γ R hε ha' z ω, ← sub_mul,
      ← mul_sub, abs_mul, abs_mul,
      abs_of_nonneg (areaDens_nonneg γ _ (by positivity : (0 : ℝ) < 2 * ε) z)]
    have hc : |Htc γ X R ε z (dpt (m + d) i) ω - Htc γ X R ε z (dpt m (i / 2 ^ d)) ω| ≤
        chainT m (m + d) (fun b => Htc γ X R ε z b ω) :=
      chain_bound (fun b => Htc γ X R ε z b ω) m d i hi
    have hd0 := areaDens_nonneg γ (zField X R ω) (show (0 : ℝ) < 2 * ε by positivity) z
    calc areaDens γ (zField X R ω) (2 * ε) z *
          |Htc γ X R ε z (dpt (m + d) i) ω - Htc γ X R ε z (dpt m (i / 2 ^ d)) ω| * |f z|
        ≤ areaDens γ (zField X R ω) (2 * ε) z *
          chainT m (m + d) (fun b => Htc γ X R ε z b ω) * |f z| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hd0) (abs_nonneg _)
      _ = _ := by ring
  have hgrid : ENNReal.ofReal |aB γ X R f (dpt m (i / 2 ^ d) * ε) ω - L| ≤
      ∑ l ∈ Finset.range (2 ^ m + 1), ENNReal.ofReal |aB γ X R f (dpt m l * ε) ω - L| :=
    Finset.single_le_sum (f := fun l => ENNReal.ofReal |aB γ X R f (dpt m l * ε) ω - L|)
      (fun _ _ => bot_le) (Finset.mem_range.2 (by omega))
  calc ENNReal.ofReal |aB γ X R f (dpt (m + d) i * ε) ω - L|
      ≤ ENNReal.ofReal (|aB γ X R f (dpt (m + d) i * ε) ω -
          aB γ X R f (dpt m (i / 2 ^ d) * ε) ω| +
          |aB γ X R f (dpt m (i / 2 ^ d) * ε) ω - L|) :=
        ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)
    _ ≤ _ := ENNReal.ofReal_add_le.trans (add_le_add hmod hgrid)

/-! ## Expectation at a fixed level -/

theorem lintegral_sup_levelA_le [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {S : Set ℂ} {R d : ℝ} (hreg : Region S R d)
    {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (hfS : ∀ z ∉ S, f z = 0)
    {Cg : ℝ} (hCg0 : 0 ≤ Cg) {k : ℕ} (hk : 2 * radius k ≤ d)
    (hCg : ∀ c ∈ Icc (1 : ℝ) 2,
      AEMeasurable (fun ω => aB γ X R f (c * radius k) ω - LfA γ X R f ω) P ∧
      ∫⁻ ω, ENNReal.ofReal |aB γ X R f (c * radius k) ω - LfA γ X R f ω| ∂P ≤
        ENNReal.ofReal (Cg * exp (-areaRate γ * (k * log 2))))
    (m e : ℕ) :
    ∫⁻ ω, ⨆ i : Fin (2 ^ (m + e) + 1), ENNReal.ofReal
        |aB γ X R f (dpt (m + e) i * radius k) ω - LfA γ X R f ω| ∂P ≤
      ENNReal.ofReal ((∫ z, |f z|) * (exp (γ ^ 2 / 2 * (2 * log R - log (2 * d))) *
          ((8 + 4 * (5436416 * exp 32)) * θm ^ m)) +
        (2 ^ m + 1) * (Cg * exp (-areaRate γ * (k * log 2)))) := by
  set ε := radius k with hεd
  have hε := radius_pos k
  set K := exp (γ ^ 2 / 2 * (2 * log R - log (2 * d))) *
    ((8 + 4 * (5436416 * exp 32)) * θm ^ m) with hK
  have hK0 : 0 ≤ K := by have := θm_pos; positivity
  set Mod : Ω → ℝ≥0∞ := fun ω => ∫⁻ z, ENNReal.ofReal (|f z| *
    (areaDens γ (zField X R ω) (2 * ε) z * chainT m (m + e) (fun a => Htc γ X R ε z a ω)))
    with hMod
  set Gr : Ω → ℝ≥0∞ := fun ω => ∑ l ∈ Finset.range (2 ^ m + 1),
    ENNReal.ofReal |aB γ X R f (dpt m l * ε) ω - LfA γ X R f ω| with hGr
  have hpt : ∀ᵐ ω ∂P, (⨆ i : Fin (2 ^ (m + e) + 1), ENNReal.ofReal
      |aB γ X R f (dpt (m + e) i * ε) ω - LfA γ X R f ω|) ≤ Mod ω + Gr ω := by
    filter_upwards [RegSample.ae_isRegularSample hX] with ω hreg'
    obtain ⟨F, hF⟩ := hreg'
    exact iSup_le fun i => pathwise_boundA hX hf hfc hF _ hε m e (i := (i : ℕ))
      (Nat.lt_succ_iff.1 i.2)
  refine (lintegral_mono_ae hpt).trans ?_
  have hFm : Measurable (fun p : Ω × ℂ => ENNReal.ofReal (|f p.2| *
      (areaDens γ (zField X R p.1) (2 * ε) p.2 *
        chainT m (m + e) (fun a => Htc γ X R ε p.2 a p.1)))) :=
    ENNReal.measurable_ofReal.comp ((continuous_abs.measurable.comp
      (hf.measurable.comp measurable_snd)).mul
      ((measurable_areaDens_zField hX γ R _).mul (measurable_chainT_Htc hX γ R ε m (m + e))))
  have hModm : Measurable Mod := hFm.lintegral_prod_right'
  rw [lintegral_add_left' hModm.aemeasurable]
  have hgi : Integrable (fun z => |f z|) := (hf.integrable_of_hasCompactSupport hfc).abs
  have hI0 : 0 ≤ ∫ z, |f z| := integral_nonneg fun _ => abs_nonneg _
  have hModb : ∫⁻ ω, Mod ω ∂P ≤ ENNReal.ofReal ((∫ z, |f z|) * K) := by
    simp only [hMod]
    rw [lintegral_lintegral_swap hFm.aemeasurable]
    have hpt2 : ∀ z, ∫⁻ ω, ENNReal.ofReal (|f z| * (areaDens γ (zField X R ω) (2 * ε) z *
        chainT m (m + e) (fun a => Htc γ X R ε z a ω))) ∂P ≤
        ENNReal.ofReal |f z| * ENNReal.ofReal K := by
      intro z
      simp_rw [ENNReal.ofReal_mul (abs_nonneg (f z))]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      by_cases hz : z ∈ S
      · gcongr
        exact lintegral_densA_chainT_le hX hγ hγ2 hε hk hreg.d_le (hreg.im_ge z hz)
          (hreg.normR z hz) m (m + e)
      · rw [hfS z hz, abs_zero, ENNReal.ofReal_zero, zero_mul, zero_mul]
    refine (lintegral_mono hpt2).trans (le_of_eq ?_)
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
      ← ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ fun _ => abs_nonneg _),
      ← ENNReal.ofReal_mul hI0]
  have hGrb : ∫⁻ ω, Gr ω ∂P ≤
      ENNReal.ofReal ((2 ^ m + 1) * (Cg * exp (-areaRate γ * (k * log 2)))) := by
    have hmem : ∀ l ∈ Finset.range (2 ^ m + 1), dpt m l ∈ Icc (1 : ℝ) 2 := fun l hl =>
      ⟨dpt_ge_one m l, dpt_le_two (by have := Finset.mem_range.1 hl; omega)⟩
    have hael : ∀ l ∈ Finset.range (2 ^ m + 1), AEMeasurable (fun ω =>
        ENNReal.ofReal |aB γ X R f (dpt m l * ε) ω - LfA γ X R f ω|) P := fun l hl =>
      (continuous_abs.measurable.comp_aemeasurable (hCg _ (hmem l hl)).1).ennreal_ofReal
    simp only [hGr]
    rw [lintegral_finset_sum' _ hael]
    refine (Finset.sum_le_sum fun l hl => (hCg _ (hmem l hl)).2).trans (le_of_eq ?_)
    have hC0 : 0 ≤ (2 : ℝ) ^ m + 1 := by positivity
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul hC0,
      show ((2 : ℝ) ^ m + 1) = ((2 ^ m + 1 : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
  refine (add_le_add hModb hGrb).trans (le_of_eq ?_)
  have hCg0' : 0 ≤ (2 ^ m + 1) * (Cg * exp (-areaRate γ * (k * log 2))) := by positivity
  rw [← ENNReal.ofReal_add (mul_nonneg hI0 hK0) hCg0']

/-! ## Summation over the scales -/

def supGA (γ : ℝ) (X : Ω → FieldSample) (R : ℝ) (f : ℂ → ℝ) (k : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (i : Fin (2 ^ n + 1)),
    ENNReal.ofReal |aB γ X R f (dpt n i * radius k) ω - LfA γ X R f ω|

omit [MeasurableSpace Ω] in
theorem levelA_mono (γ : ℝ) (X : Ω → FieldSample) (R : ℝ) (f : ℂ → ℝ) (k : ℕ) (ω : Ω) :
    Monotone (fun n : ℕ => ⨆ i : Fin (2 ^ n + 1),
      ENNReal.ofReal |aB γ X R f (dpt n i * radius k) ω - LfA γ X R f ω|) := by
  refine monotone_nat_of_le_succ fun n => iSup_le fun i => ?_
  have hi : 2 * (i : ℕ) < 2 ^ (n + 1) + 1 := by have := i.2; rw [pow_succ]; omega
  refine le_iSup_of_le (⟨2 * i, hi⟩ : Fin (2 ^ (n + 1) + 1)) (le_of_eq ?_)
  rw [dpt_double n i]

theorem summable_bndβ {β : ℝ} (hβ : 0 < β) {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) :
    Summable (fun k : ℕ => A * θm ^ (⌊β * k / 2⌋₊) +
      (2 ^ (⌊β * k / 2⌋₊) + 1) * (C * exp (-β * (k * log 2)))) := by
  have hlθ : log θm < 0 := log_neg θm_pos θm_lt_one
  have hl2 : 0 < log 2 := log_pos one_lt_two
  set q₁ := exp (β / 2 * log θm) with hq₁
  set q₂ := exp (-(β / 2) * log 2) with hq₂
  have hq₁1 : q₁ < 1 := exp_lt_one_iff.2 (mul_neg_of_pos_of_neg (by positivity) hlθ)
  have hq₂1 : q₂ < 1 := exp_lt_one_iff.2 (by nlinarith)
  have b1 : ∀ k : ℕ, θm ^ (⌊β * k / 2⌋₊) ≤ θm⁻¹ * q₁ ^ k := by
    intro k
    have hk1 : β * k / 2 - 1 < (⌊β * k / 2⌋₊ : ℝ) := by
      have := Nat.lt_floor_add_one (β * k / 2); linarith
    have e1 : θm ^ (⌊β * k / 2⌋₊) = exp ((⌊β * k / 2⌋₊ : ℝ) * log θm) := by
      rw [Real.exp_nat_mul, Real.exp_log θm_pos]
    have e2 : θm⁻¹ * q₁ ^ k = exp ((β * k / 2 - 1) * log θm) := by
      rw [hq₁, ← Real.exp_nat_mul, show θm⁻¹ = exp (-log θm) by rw [exp_neg, exp_log θm_pos],
        ← exp_add]
      congr 1; ring
    rw [e1, e2]
    exact exp_le_exp.2 (by nlinarith)
  have b2 : ∀ k : ℕ, (2 ^ (⌊β * k / 2⌋₊) + 1) * exp (-β * (k * log 2)) ≤ 2 * q₂ ^ k := by
    intro k
    have hk1 : (⌊β * k / 2⌋₊ : ℝ) ≤ β * k / 2 := Nat.floor_le (by positivity)
    have h1 : (1 : ℝ) ≤ 2 ^ (⌊β * k / 2⌋₊) := one_le_pow₀ (by norm_num)
    have e1 : (2 : ℝ) ^ (⌊β * k / 2⌋₊) = exp ((⌊β * k / 2⌋₊ : ℝ) * log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log two_pos]
    have h2 : (2 : ℝ) ^ (⌊β * k / 2⌋₊) * exp (-β * (k * log 2)) ≤ q₂ ^ k := by
      rw [e1, ← exp_add, hq₂, ← Real.exp_nat_mul]
      exact exp_le_exp.2 (by nlinarith)
    calc (2 ^ (⌊β * k / 2⌋₊) + 1) * exp (-β * (k * log 2))
        ≤ (2 * 2 ^ (⌊β * k / 2⌋₊)) * exp (-β * (k * log 2)) :=
          mul_le_mul_of_nonneg_right (by linarith) (exp_pos _).le
      _ = 2 * (2 ^ (⌊β * k / 2⌋₊) * exp (-β * (k * log 2))) := by ring
      _ ≤ 2 * q₂ ^ k := mul_le_mul_of_nonneg_left h2 (by norm_num)
  refine Summable.of_nonneg_of_le (fun k => add_nonneg (mul_nonneg hA (pow_nonneg θm_pos.le _))
    (mul_nonneg (by positivity) (mul_nonneg hC (exp_pos _).le))) (fun k => ?_)
    (((summable_geometric_of_lt_one (exp_pos _).le hq₁1).mul_left (A * θm⁻¹)).add
      ((summable_geometric_of_lt_one (exp_pos _).le hq₂1).mul_left (C * 2)))
  have := θm_pos
  calc A * θm ^ (⌊β * k / 2⌋₊) + (2 ^ (⌊β * k / 2⌋₊) + 1) * (C * exp (-β * (k * log 2)))
      = A * θm ^ (⌊β * k / 2⌋₊) + C * ((2 ^ (⌊β * k / 2⌋₊) + 1) * exp (-β * (k * log 2))) := by
        ring
    _ ≤ A * (θm⁻¹ * q₁ ^ k) + C * (2 * q₂ ^ k) :=
        add_le_add (mul_le_mul_of_nonneg_left (b1 k) hA) (mul_le_mul_of_nonneg_left (b2 k) hC)
    _ = A * θm⁻¹ * q₁ ^ k + C * 2 * q₂ ^ k := by ring

/-! ## Almost sure uniform convergence for the normalized field -/

theorem ae_tendsto_aB_goodFilter [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {S : Set ℂ} {R d : ℝ} (hreg : Region S R d)
    {f : ℂ → ℝ} (hf : IsTestH f) (hfS' : tsupport f ⊆ S) :
    ∀ᵐ ω ∂P, Tendsto (fun i : ℕ × ℝ => aB γ X R f (goodRad i) ω) goodFilter
      (𝓝 (LfA γ X R f ω)) := by
  have hfS : ∀ z ∉ S, f z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport fun h => hz (hfS' h)
  obtain ⟨Cg, hCg0, k₀, hCg⟩ := exists_grid_rateA hX hγ hγ2 hreg hf hfS'
  set β := areaRate γ with hβd
  have hβ : 0 < β := areaRate_pos hγ hγ2
  set I := ∫ z, |f z| with hI
  have hI0 : 0 ≤ I := integral_nonneg fun _ => abs_nonneg _
  set D := exp (γ ^ 2 / 2 * (2 * log R - log (2 * d))) * (8 + 4 * (5436416 * exp 32)) with hD
  have hA0 : 0 ≤ I * D := mul_nonneg hI0 (by positivity)
  set b : ℕ → ℝ := fun k => I * D * θm ^ (⌊β * k / 2⌋₊) +
    (2 ^ (⌊β * k / 2⌋₊) + 1) * (Cg * exp (-β * (k * log 2))) with hb
  have hb0 : ∀ k, 0 ≤ b k := fun k => add_nonneg (mul_nonneg hA0 (pow_nonneg θm_pos.le _))
    (mul_nonneg (by positivity) (mul_nonneg hCg0 (exp_pos _).le))
  have hsum : Summable (fun k => b (k + k₀)) :=
    (summable_nat_add_iff k₀).2 (summable_bndβ hβ hA0 hCg0)
  have hGm : ∀ k, k₀ ≤ k → AEMeasurable (supGA γ X R f k) P := fun k hk =>
    AEMeasurable.iSup fun n => AEMeasurable.iSup fun i =>
      (continuous_abs.measurable.comp_aemeasurable ((hCg k hk).2 _
        ⟨dpt_ge_one n i, dpt_le_two (Nat.lt_succ_iff.1 i.2)⟩).1).ennreal_ofReal
  have hlev : ∀ k, k₀ ≤ k → ∫⁻ ω, supGA γ X R f k ω ∂P ≤ ENNReal.ofReal (b k) := by
    intro k hk
    obtain ⟨hk2, hc⟩ := hCg k hk
    set m := ⌊β * k / 2⌋₊
    have hmeas : ∀ n, AEMeasurable (fun ω => ⨆ i : Fin (2 ^ n + 1), ENNReal.ofReal
        |aB γ X R f (dpt n i * radius k) ω - LfA γ X R f ω|) P :=
      fun n => AEMeasurable.iSup fun i =>
        (continuous_abs.measurable.comp_aemeasurable (hc _
          ⟨dpt_ge_one n i, dpt_le_two (Nat.lt_succ_iff.1 i.2)⟩).1).ennreal_ofReal
    show ∫⁻ ω, ⨆ n : ℕ, (⨆ i : Fin (2 ^ n + 1), ENNReal.ofReal
        |aB γ X R f (dpt n i * radius k) ω - LfA γ X R f ω|) ∂P ≤ _
    rw [lintegral_iSup' hmeas (ae_of_all _ fun ω => levelA_mono γ X R f k ω)]
    refine iSup_le fun n => ?_
    obtain ⟨e, he⟩ : ∃ e, max n m = m + e := ⟨max n m - m, by omega⟩
    refine (lintegral_mono fun ω => levelA_mono γ X R f k ω (show n ≤ m + e by omega)).trans
      ((lintegral_sup_levelA_le hX hγ hγ2 hreg hf.1 hf.2.1 hfS hCg0 hk2 hc m e).trans
        (le_of_eq ?_))
    congr 1; simp only [hb, hD]; ring
  have hint : ∫⁻ ω, ∑' k, supGA γ X R f (k + k₀) ω ∂P ≠ ∞ := by
    rw [lintegral_tsum fun k => hGm _ (by omega)]
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑' k, b (k + k₀))) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun k => hb0 _) hsum]
    exact ENNReal.tsum_le_tsum fun k => hlev _ (by omega)
  have hae := ae_lt_top' (AEMeasurable.ennreal_tsum fun k => hGm _ (by omega)) hint
  filter_upwards [hae, RegSample.ae_isRegularSample hX] with ω hω hreg'
  obtain ⟨F, hF⟩ := hreg'
  have hFZ := regular_zField (R := R) hF
  have hG0 : Tendsto (fun k => supGA γ X R f k ω) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat k₀).1 (ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne)
  have hGfin : ∀ k, k₀ ≤ k → supGA γ X R f k ω ≠ ∞ := fun k hk => by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + k₀ := ⟨k - k₀, by omega⟩
    exact ne_top_of_le_ne_top hω.ne (ENNReal.le_tsum (f := fun k => supGA γ X R f (k + k₀) ω) j)
  have hbound : ∀ k : ℕ, k₀ ≤ k → ∀ a ∈ Icc (1 : ℝ) 2,
      |aB γ X R f (a * radius k) ω - LfA γ X R f ω| ≤ (supGA γ X R f k ω).toReal := by
    intro k hk a ha
    set ε := radius k with hεd
    have hε := radius_pos k
    set φ : ℝ → ℝ := fun s => ∫ z in tsupport f,
      areaDens γ (zField X R ω) (max s 1 * ε) z * f z with hφ
    have hpos : ∀ s : ℝ, 0 < max s 1 * ε := fun s => mul_pos (lt_max_of_lt_right one_pos) hε
    have hcont : Continuous (fun p : ℝ × ℂ =>
        areaDens γ (zField X R ω) (max p.1 1 * ε) p.2 * f p.2) := by
      have e : (fun p : ℝ × ℂ => areaDens γ (zField X R ω) (max p.1 1 * ε) p.2 * f p.2) =
          fun p => (max p.1 1 * ε) ^ (γ ^ 2 / 2) * exp (γ *
            (F (foldH p.2, max p.1 1 * ε) + -X ω (foldedCircle 0 R))) * f p.2 := by
        funext p
        rw [areaDens, hFZ.evalReg_fc p.2 (hpos p.1)]
      rw [e]
      have hm : Continuous (fun p : ℝ × ℂ => max p.1 1 * ε) := by fun_prop
      have hF' : Continuous (fun p : ℝ × ℂ => F (foldH p.2, max p.1 1 * ε)) :=
        hF.1.comp_continuous ((CircleFubini.continuous_foldH'.comp continuous_snd).prodMk hm)
          (fun p => ⟨CircleFubini.foldH_mem_Hbar' _, hpos p.1⟩)
      exact ((hm.rpow_const fun _ => Or.inr (by positivity)).mul
        (Real.continuous_exp.comp ((hF'.add continuous_const).const_mul _))).mul
        (hf.1.comp continuous_snd)
    have hφc : Continuous φ := continuous_parametric_integral_of_continuous hcont hf.2.1
    have hφeq : ∀ s ∈ Icc (1 : ℝ) 2, aB γ X R f (s * ε) ω = φ s := by
      intro s hs
      rw [aB_eq_integral hX γ R (mul_pos (by linarith [hs.1]) hε) f ω, hφ]
      simp only [max_eq_left hs.1]
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := H) fun z hz => by
          rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hf.2.2 h)), mul_zero],
        setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
          rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]]
    set an : ℕ → ℕ := fun n => ⌊(a - 1) * 2 ^ n⌋₊ with han
    have hy0 : ∀ n : ℕ, 0 ≤ (a - 1) * 2 ^ n := fun n =>
      mul_nonneg (by linarith [ha.1]) (by positivity)
    have han_le : ∀ n, an n ≤ 2 ^ n := fun n =>
      Nat.floor_le_of_le (by push_cast; nlinarith [ha.2, pow_pos (two_pos (α := ℝ)) n])
    have hmem : ∀ n, dpt n (an n) ∈ Icc (1 : ℝ) 2 := fun n =>
      ⟨dpt_ge_one n _, dpt_le_two (han_le n)⟩
    have hconv : Tendsto (fun n => dpt n (an n)) atTop (𝓝 a) := by
      have hup : ∀ n, dpt n (an n) ≤ a := fun n => by
        have h1 : (an n : ℝ) ≤ (a - 1) * 2 ^ n := Nat.floor_le (hy0 n)
        unfold dpt
        have : (an n : ℝ) / 2 ^ n ≤ a - 1 := by
          rw [div_le_iff₀ (by positivity)]; exact h1
        linarith
      have hlow : ∀ n, a - (1 / 2) ^ n ≤ dpt n (an n) := fun n => by
        have h1 : (a - 1) * 2 ^ n - 1 < (an n : ℝ) := by
          have := Nat.lt_floor_add_one ((a - 1) * 2 ^ n); linarith
        unfold dpt
        have h2 : a - 1 - (1 / 2) ^ n ≤ (an n : ℝ) / 2 ^ n := by
          have hpw : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by rw [← mul_pow]; norm_num
          rw [le_div_iff₀ (by positivity), sub_mul, hpw]
          linarith
        linarith
      have hl : Tendsto (fun n : ℕ => a - (1 / 2 : ℝ) ^ n) atTop (𝓝 a) := by
        have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num)).const_sub a
        simpa using this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds hlow hup
    have hbd : ∀ n, |φ (dpt n (an n)) - LfA γ X R f ω| ≤ (supGA γ X R f k ω).toReal := by
      intro n
      rw [← hφeq _ (hmem n), ← ENNReal.ofReal_le_iff_le_toReal (hGfin k hk)]
      exact le_iSup₂_of_le (f := fun (n : ℕ) (i : Fin (2 ^ n + 1)) => ENNReal.ofReal
        |aB γ X R f (dpt n i * radius k) ω - LfA γ X R f ω|) n
        ⟨an n, Nat.lt_succ_of_le (han_le n)⟩ le_rfl
    have hlim : Tendsto (fun n => |φ (dpt n (an n)) - LfA γ X R f ω|) atTop
        (𝓝 |φ a - LfA γ X R f ω|) :=
      (continuous_abs.tendsto _).comp (((hφc.tendsto a).comp hconv).sub_const _)
    rw [hφeq a ha]
    exact le_of_tendsto' hlim hbd
  rw [Metric.tendsto_nhds]
  intro η hη
  have h1 : ∀ᶠ k in atTop, (supGA γ X R f k ω).toReal < η := by
    have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hG0
    simp only [ENNReal.toReal_zero] at ht
    exact ht.eventually (gt_mem_nhds hη)
  rw [goodFilter, eventually_prod_principal_iff]
  filter_upwards [h1, eventually_ge_atTop k₀] with k hk hk0 a ha
  rw [Real.dist_eq, goodRad]
  exact (hbound k hk0 a ha).trans_lt hk

/-! ## Back to the free field -/

theorem integral_areaR_eq_mul_aB {ω : Ω} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith (X ω) F)
    (γ R : ℝ) {r : ℝ} (hr : 0 < r) (f : ℂ → ℝ) :
    ∫ z, f z ∂areaR γ (X ω) r = exp (γ * X ω (foldedCircle 0 R)) * aB γ X R f r ω := by
  have hFZ := regular_zField (R := R) hF
  rw [aB, areaR, areaR,
    integral_withDensity_ofReal (continuous_areaDens γ hF hr).measurable
      (fun z => areaDens_nonneg γ _ hr z),
    integral_withDensity_ofReal (continuous_areaDens γ hFZ hr).measurable
      (fun z => areaDens_nonneg γ _ hr z), ← integral_const_mul]
  congr 1
  funext z
  rw [areaDens, areaDens, hF.evalReg_fc z hr, hFZ.evalReg_fc z hr]
  have e : exp (γ * F (foldH z, r)) = exp (γ * X ω (foldedCircle 0 R)) *
      exp (γ * (F (foldH z, r) + -X ω (foldedCircle 0 R))) := by
    rw [← exp_add]; congr 1; ring
  rw [e]; ring

theorem ae_qAreaMeasure_zField_eq [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (R : ℝ) :
    ∀ᵐ ω ∂P, qAreaMeasure γ (zField X R ω) =
      ENNReal.ofReal (exp (-(γ * X ω (foldedCircle 0 R)))) • qAreaMeasure γ (X ω) := by
  filter_upwards [ae_isVagueLimitOn_qAreaMeasure hX hγ hγ2,
    ae_areaApprox_aZ_eq (P := P) hX γ R] with ω ⟨h0, hK, ht⟩ hsc
  set c := ENNReal.ofReal (exp (-(γ * X ω (foldedCircle 0 R)))) with hc
  have hμ : IsVagueLimitOn H (areaApprox γ (zField X R ω)) (c • qAreaMeasure γ (X ω)) := by
    refine ⟨by rw [Measure.smul_apply, h0, smul_zero], fun K hKc hKH => ?_,
      fun f hf hfc hfH => ?_⟩
    · rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hK K hKc hKH)
    · have e : areaApprox γ (zField X R ω) = fun k => c • areaApprox γ (X ω) k :=
        funext fun k => hsc k
      rw [e]
      simp_rw [integral_smul_measure]
      exact (ht f hf hfc hfH).const_smul _
  exact qAreaMeasure_eq hμ

/-- **Area analogue of M4-B4.** For the free field, almost surely the approximating area
measures `μ_{a 2^{-k}}(X ω)` converge vaguely on `ℍ` to `qAreaMeasure γ (X ω)`, uniformly in
`a ∈ [1,2]`. -/
theorem ae_hasAreaLimit [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, HasAreaLimit γ (X ω) (qAreaMeasure γ (X ω)) := by
  obtain ⟨Fam, hFc, hFd⟩ := exists_denseTestFamily
  have hloc : ∀ f ∈ Fam, ∃ n : ℕ, tsupport f ⊆ Kset n := fun f hf =>
    exists_Kset (hFd.1 f hf).2.1.isCompact (hFd.1 f hf).2.2
  choose! nf hnf using hloc
  have hregn : ∀ n : ℕ, Region (Kset n) ((n : ℝ) + 1) (dK n) := fun n =>
    { meas := (isCompact_Kset n).isClosed.measurableSet
      fin := (isCompact_Kset n).measure_lt_top
      subH := Kset_subset_H n
      d_pos := (dK_spec n).1
      d_le := (dK_spec n).2.1
      normR := Kset_R n
      im_ge := (dK_spec n).2.2 }
  have hT : ∀ᵐ ω ∂P, ∀ f ∈ Fam, Tendsto (fun i : ℕ × ℝ =>
      aB γ X ((nf f : ℝ) + 1) f (goodRad i) ω) goodFilter
      (𝓝 (LfA γ X ((nf f : ℝ) + 1) f ω)) :=
    (ae_ball_iff hFc).2 fun f hf =>
      ae_tendsto_aB_goodFilter hX hγ hγ2 (hregn (nf f)) (hFd.1 f hf) (hnf f hf)
  have hQ : ∀ᵐ ω ∂P, ∀ n : ℕ, qAreaMeasure γ (zField X ((n : ℝ) + 1) ω) =
      ENNReal.ofReal (exp (-(γ * X ω (foldedCircle 0 ((n : ℝ) + 1))))) •
        qAreaMeasure γ (X ω) :=
    ae_all_iff.2 fun n => ae_qAreaMeasure_zField_eq hX hγ hγ2 _
  filter_upwards [hT, hQ, ae_isVagueLimitOn_qAreaMeasure hX hγ hγ2,
    RegSample.ae_isRegularSample hX] with ω hT hQ hv hreg
  obtain ⟨F, hF⟩ := hreg
  refine ⟨hv.1, hv.2.1, fun f hf hfc hfH => ?_⟩
  have htr : ∀ g ∈ Fam, Tendsto (fun i => ∫ z, g z ∂areaR γ (X ω) (goodRad i)) goodFilter
      (𝓝 (∫ z, g z ∂qAreaMeasure γ (X ω))) := by
    intro g hg
    set n := nf g
    have hLf : LfA γ X ((n : ℝ) + 1) g ω =
        exp (-(γ * X ω (foldedCircle 0 ((n : ℝ) + 1)))) * ∫ z, g z ∂qAreaMeasure γ (X ω) := by
      rw [LfA, hQ n, integral_smul_measure, ENNReal.toReal_ofReal (exp_pos _).le, smul_eq_mul]
    have h := (hT g hg).const_mul (exp (γ * X ω (foldedCircle 0 ((n : ℝ) + 1))))
    rw [hLf, ← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul] at h
    refine h.congr' (eventually_goodRad_pos.mono fun i hi => ?_)
    exact (integral_areaR_eq_mul_aB hF γ _ hi g).symm
  exact tendsto_goodFilter_of_denseFamily hv.2.1
    (fun K hK _ => eventually_goodRad_pos.mono fun i hi => areaR_lt_top γ hF hi hK)
    hFd htr ⟨hf, hfc, hfH⟩

/-- **Key milestone: almost every free-field sample is good.** -/
theorem ae_isLQGGood [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) : ∀ᵐ ω ∂P, IsLQGGood γ (X ω) := by
  filter_upwards [RegSample.ae_isRegularSample hX, ae_hasBdryLimit hX hγ hγ2,
    ae_hasAreaLimit hX hγ hγ2] with ω h1 h2 h3
  exact ⟨h1, ⟨_, h2⟩, ⟨_, h3⟩⟩

end AreaOffsets
end QuantumZipper
