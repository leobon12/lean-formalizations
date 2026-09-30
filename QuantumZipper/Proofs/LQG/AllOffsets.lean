import QuantumZipper.Proofs.LQG.AllOffsetsModulus

/-!
# M4-B4: the boundary measure along all offsets `a 2^{-k}` simultaneously; M4-T2

Blueprint `M4_BLUEPRINT.md`, nodes M4-B4 and M4-T2.

* `ae_hasBdryLimit`: for the free field (any additive-constant convention), almost surely
  `HasBdryLimit γ (X ω) (qBoundaryMeasure γ (X ω))`, i.e. the approximations `ν_{a 2^{-k}}`
  converge vaguely to `qBoundaryMeasure γ (X ω)` **uniformly in `a ∈ [1,2]`**.
  Proof (grid plus modulus): for `f` in the countable test family and a level-`n` dyadic offset
  `a`, `|ν_{aε}(f) − ν(f)| ≤ ∫ |f| d_{2ε} · chainT + ∑_{grid} |ν_{cε}(f) − ν(f)|`
  (`pathwise_bound`); the expectation of the right side is `≤ C θ^m + (2^m+1) C 2^{-βk}`
  uniformly in `n` (`lintegral_sup_level_le`); with `m = ⌊βk/2⌋` this is summable in `k`, and the
  continuity of the densities in the radius (every-circle regularity) passes from dyadic
  offsets to all of `[1,2]`.
* M4-T2: `qBoundaryMeasure_translate` and `qBoundaryMeasure_reflectH` (for good samples and
  every real `t` at once).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace AllOffsets

open BdryExist BdryVague GaussTK TwoRadius GoodSample

/-! ## C0. Countable test family along `goodFilter` -/

theorem tendsto_goodFilter_of_testFam {νr : ℕ × ℝ → Measure ℝ} {ν : Measure ℝ}
    [IsFiniteMeasureOnCompacts ν]
    (hfin : ∀ᶠ i in goodFilter, IsFiniteMeasureOnCompacts (νr i))
    (hconv : ∀ N m, Tendsto (fun i => ∫ x, testFam N m x ∂νr i) goodFilter
      (𝓝 (∫ x, testFam N m x ∂ν)))
    (hbump : ∀ N, Tendsto (fun i => ∫ x, bump N x ∂νr i) goodFilter
      (𝓝 (∫ x, bump N x ∂ν)))
    {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) :
    Tendsto (fun i => ∫ x, f x ∂νr i) goodFilter (𝓝 (∫ x, f x ∂ν)) := by
  obtain ⟨N, hN⟩ := exists_testFam_approx hf hcs
  set B := ∫ x, bump N x ∂ν with hB
  have hB0 : 0 ≤ B := integral_nonneg (bump_nonneg N)
  have happ : ∀ (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ] (δ : ℝ) (m : ℕ),
      (∀ x, |f x - testFam N m x| ≤ δ * bump N x) →
      |∫ x, f x ∂μ - ∫ x, testFam N m x ∂μ| ≤ δ * ∫ x, bump N x ∂μ := by
    intro μ _ δ m hm
    have hi1 : Integrable f μ := hf.integrable_of_hasCompactSupport hcs
    have hi2 : Integrable (testFam N m) μ :=
      (continuous_testFam N m).integrable_of_hasCompactSupport (hasCompactSupport_testFam N m)
    have hi3 : Integrable (bump N) μ :=
      (continuous_bump N).integrable_of_hasCompactSupport (hasCompactSupport_bump N)
    rw [← integral_sub hi1 hi2]
    have := norm_integral_le_of_norm_le (hi3.const_mul δ)
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hm x)
    rwa [Real.norm_eq_abs, integral_const_mul] at this
  rw [Metric.tendsto_nhds]
  intro η hη
  set δ := η / (4 * (B + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨m, hm⟩ := hN δ hδ0
  have h1 := Metric.tendsto_nhds.1 (hconv N m) (η / 4) (by positivity)
  have h2 := Metric.tendsto_nhds.1 (hbump N) 1 one_pos
  filter_upwards [hfin, h1, h2] with i hi hi1 hi2
  rw [Real.dist_eq] at hi1 hi2 ⊢
  have ha := happ (νr i) δ m hm
  have hb := happ ν δ m hm
  have hbi : ∫ x, bump N x ∂νr i ≤ B + 1 := by linarith [(abs_lt.1 hi2).2]
  have e1 : δ * ∫ x, bump N x ∂νr i ≤ η / 4 := by
    calc δ * ∫ x, bump N x ∂νr i ≤ δ * (B + 1) := mul_le_mul_of_nonneg_left hbi hδ0.le
      _ = η / 4 := by rw [hδ]; field_simp
  have e2 : δ * B ≤ η / 4 := by
    calc δ * B ≤ δ * (B + 1) := mul_le_mul_of_nonneg_left (by linarith) hδ0.le
      _ = η / 4 := by rw [hδ]; field_simp
  have t1 := abs_sub_le (∫ x, f x ∂νr i) (∫ x, testFam N m x ∂νr i) (∫ x, f x ∂ν)
  have t2 := abs_sub_le (∫ x, testFam N m x ∂νr i) (∫ x, testFam N m x ∂ν) (∫ x, f x ∂ν)
  rw [abs_sub_comm (∫ x, testFam N m x ∂ν)] at t2
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-! ## C1. Pathwise bound -/

/-- `L(ω) = ∫ g dν(Z ω)`. -/
def Lf (γ : ℝ) (X : Ω → FieldSample) (R : ℝ) (g : ℝ → ℝ) (ω : Ω) : ℝ :=
  ∫ t, g t ∂qBoundaryMeasure γ (zField X R ω)

theorem bA_eq_integral (hX : IsFreeGFFModConstH X P) (γ R : ℝ) {r : ℝ} (hr : 0 < r)
    (g : ℝ → ℝ) (ω : Ω) :
    bA γ X R g r ω = ∫ t, bdryDens γ (zField X R ω) r t * g t := by
  have hd : Measurable (fun t => bdryDens γ (zField X R ω) r t) := by
    have h : Measurable (fun t : ℝ => ((ω, t) : Ω × ℝ)) := measurable_const.prodMk measurable_id
    exact Measurable.comp (g := fun p : Ω × ℝ => bdryDens γ (zField X R p.1) r p.2)
      (f := fun t : ℝ => ((ω, t) : Ω × ℝ)) (measurable_bdryDens_zField hX γ R r) h
  rw [bA, bdryR, GoodSample.integral_withDensity_ofReal hd
    (fun t => GoodSample.bdryDens_nonneg γ _ hr t)]

theorem measurable_chainT_Ht (hX : IsFreeGFFModConstH X P) (γ R ε : ℝ) (m n : ℕ) :
    Measurable (fun p : Ω × ℝ => chainT m n (fun a => Ht γ X R ε p.2 a p.1)) := by
  have hz : ∀ r, Measurable (fun p : Ω × ℝ => zV X R r p.2 p.1) := fun r =>
    Measurable.comp (g := fun p : ℝ × Ω => zV X R r p.1 p.2) (f := Prod.swap)
      (measurable_zV hX R r) measurable_swap
  have hH : ∀ a, Measurable (fun p : Ω × ℝ => Ht γ X R ε p.2 a p.1) := by
    intro a
    show Measurable (fun p : Ω × ℝ => (a / 2) ^ (γ ^ 2 / 4) *
      exp (γ / 2 * (zV X R (a * ε) p.2 p.1 - zV X R (2 * ε) p.2 p.1)))
    exact measurable_const.mul ((((hz _).sub (hz _)).const_mul _).exp)
  unfold chainT incr
  exact Finset.measurable_sum _ fun j _ => measurable_const.add
    ((Finset.measurable_sum _ fun l _ => ((hH _).sub (hH _)).pow_const 4).div_const _)

theorem pathwise_bound (hX : IsFreeGFFModConstH X P) {γ R : ℝ} {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) {ω : Ω} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith (X ω) F)
    (L : ℝ) {ε : ℝ} (hε : 0 < ε) (m d : ℕ) {i : ℕ} (hi : i ≤ 2 ^ (m + d)) :
    ENNReal.ofReal |bA γ X R g (dpt (m + d) i * ε) ω - L| ≤
      (∫⁻ t, ENNReal.ofReal (|g t| * (bdryDens γ (zField X R ω) (2 * ε) t *
        chainT m (m + d) (fun a => Ht γ X R ε t a ω)))) +
      ∑ l ∈ Finset.range (2 ^ m + 1), ENNReal.ofReal |bA γ X R g (dpt m l * ε) ω - L| := by
  have hFZ := regular_zField (R := R) hF
  have ha : 0 < dpt (m + d) i := by linarith [dpt_ge_one (m + d) i]
  have ha' : 0 < dpt m (i / 2 ^ d) := by linarith [dpt_ge_one m (i / 2 ^ d)]
  have hint : ∀ r, 0 < r → Integrable (fun t => bdryDens γ (zField X R ω) r t * g t) :=
    fun r hr => ((continuous_bdryDens γ hFZ hr).mul hg).integrable_of_hasCompactSupport
      hgc.mul_left
  have hil : i / 2 ^ d ≤ 2 ^ m :=
    Nat.div_le_of_le_mul (by rw [pow_add] at hi; rw [mul_comm]; exact hi)
  have h1 := mul_pos ha hε
  have h2 := mul_pos ha' hε
  have hmod : ENNReal.ofReal |bA γ X R g (dpt (m + d) i * ε) ω -
      bA γ X R g (dpt m (i / 2 ^ d) * ε) ω| ≤
      ∫⁻ t, ENNReal.ofReal (|g t| * (bdryDens γ (zField X R ω) (2 * ε) t *
        chainT m (m + d) (fun a => Ht γ X R ε t a ω))) := by
    rw [bA_eq_integral hX γ R h1, bA_eq_integral hX γ R h2,
      ← integral_sub (hint _ h1) (hint _ h2)]
    have hi2 : Integrable (fun t => |bdryDens γ (zField X R ω) (dpt (m + d) i * ε) t * g t -
        bdryDens γ (zField X R ω) (dpt m (i / 2 ^ d) * ε) t * g t|) :=
      ((hint _ h1).sub (hint _ h2)).abs
    refine (ENNReal.ofReal_le_ofReal (abs_integral_le_integral_abs)).trans ?_
    rw [ofReal_integral_eq_lintegral_ofReal hi2 (ae_of_all _ fun _ => abs_nonneg _)]
    refine lintegral_mono fun t => ENNReal.ofReal_le_ofReal ?_
    rw [bdryDens_eq_mul_Ht γ R hε ha t ω, bdryDens_eq_mul_Ht γ R hε ha' t ω, ← sub_mul,
      ← mul_sub, abs_mul, abs_mul,
      abs_of_nonneg (bdryDens_nonneg γ _ (by positivity : (0 : ℝ) < 2 * ε) t)]
    have hc : |Ht γ X R ε t (dpt (m + d) i) ω - Ht γ X R ε t (dpt m (i / 2 ^ d)) ω| ≤
        chainT m (m + d) (fun b => Ht γ X R ε t b ω) :=
      chain_bound (fun b => Ht γ X R ε t b ω) m d i hi
    have hd0 := bdryDens_nonneg γ (zField X R ω) (show (0 : ℝ) < 2 * ε by positivity) t
    calc bdryDens γ (zField X R ω) (2 * ε) t *
          |Ht γ X R ε t (dpt (m + d) i) ω - Ht γ X R ε t (dpt m (i / 2 ^ d)) ω| * |g t|
        ≤ bdryDens γ (zField X R ω) (2 * ε) t *
          chainT m (m + d) (fun b => Ht γ X R ε t b ω) * |g t| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hd0) (abs_nonneg _)
      _ = _ := by ring
  have hgrid : ENNReal.ofReal |bA γ X R g (dpt m (i / 2 ^ d) * ε) ω - L| ≤
      ∑ l ∈ Finset.range (2 ^ m + 1), ENNReal.ofReal |bA γ X R g (dpt m l * ε) ω - L| :=
    Finset.single_le_sum (f := fun l => ENNReal.ofReal |bA γ X R g (dpt m l * ε) ω - L|)
      (fun _ _ => bot_le) (Finset.mem_range.2 (by omega))
  calc ENNReal.ofReal |bA γ X R g (dpt (m + d) i * ε) ω - L|
      ≤ ENNReal.ofReal (|bA γ X R g (dpt (m + d) i * ε) ω -
          bA γ X R g (dpt m (i / 2 ^ d) * ε) ω| +
          |bA γ X R g (dpt m (i / 2 ^ d) * ε) ω - L|) :=
        ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)
    _ ≤ _ := ENNReal.ofReal_add_le.trans (add_le_add hmod hgrid)

/-! ## C2. Expectation at a fixed level -/

theorem lintegral_sup_level_le [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {N : ℕ} {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgS : ∀ t ∉ Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1), g t = 0)
    {Cg : ℝ} (hCg0 : 0 ≤ Cg) (hCg : ∀ k : ℕ, ∀ c ∈ Icc (1 : ℝ) 2,
      AEMeasurable (fun ω => bA γ X ((N : ℝ) + 3) g (c * radius k) ω -
        Lf γ X ((N : ℝ) + 3) g ω) P ∧
      ∫⁻ ω, ENNReal.ofReal |bA γ X ((N : ℝ) + 3) g (c * radius k) ω -
        Lf γ X ((N : ℝ) + 3) g ω| ∂P ≤
        ENNReal.ofReal (Cg * exp (-bdryRate γ * (k * log 2))))
    (k m d : ℕ) :
    ∫⁻ ω, ⨆ i : Fin (2 ^ (m + d) + 1), ENNReal.ofReal
        |bA γ X ((N : ℝ) + 3) g (dpt (m + d) i * radius k) ω - Lf γ X ((N : ℝ) + 3) g ω| ∂P ≤
      ENNReal.ofReal ((∫ t, |g t|) * (((N : ℝ) + 3) ^ (γ ^ 2 / 4) *
          ((8 + 4 * (2544 * exp 16)) * θm ^ m)) +
        (2 ^ m + 1) * (Cg * exp (-bdryRate γ * (k * log 2)))) := by
  set R : ℝ := (N : ℝ) + 3 with hR
  set ε := radius k with hεd
  have hε := radius_pos k
  have hε1 := radius_le_one k
  set K := R ^ (γ ^ 2 / 4) * ((8 + 4 * (2544 * exp 16)) * θm ^ m) with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ R := by positivity
    have := θm_pos
    positivity
  set Mod : Ω → ℝ≥0∞ := fun ω => ∫⁻ t, ENNReal.ofReal (|g t| *
    (bdryDens γ (zField X R ω) (2 * ε) t * chainT m (m + d) (fun a => Ht γ X R ε t a ω)))
    with hMod
  set Gr : Ω → ℝ≥0∞ := fun ω => ∑ l ∈ Finset.range (2 ^ m + 1),
    ENNReal.ofReal |bA γ X R g (dpt m l * ε) ω - Lf γ X R g ω| with hGr
  have hpt : ∀ᵐ ω ∂P, (⨆ i : Fin (2 ^ (m + d) + 1), ENNReal.ofReal
      |bA γ X R g (dpt (m + d) i * ε) ω - Lf γ X R g ω|) ≤ Mod ω + Gr ω := by
    filter_upwards [RegSample.ae_isRegularSample hX] with ω hreg
    obtain ⟨F, hF⟩ := hreg
    exact iSup_le fun i => pathwise_bound hX hg hgc hF _ hε m d (i := (i : ℕ)) (Nat.lt_succ_iff.1 i.2)
  refine (lintegral_mono_ae hpt).trans ?_
  have hFm : Measurable (fun p : Ω × ℝ => ENNReal.ofReal (|g p.2| *
      (bdryDens γ (zField X R p.1) (2 * ε) p.2 *
        chainT m (m + d) (fun a => Ht γ X R ε p.2 a p.1)))) :=
    ENNReal.measurable_ofReal.comp ((continuous_abs.measurable.comp (hg.measurable.comp measurable_snd)).mul
      ((measurable_bdryDens_zField hX γ R _).mul (measurable_chainT_Ht hX γ R ε m (m + d))))
  have hModm : Measurable Mod := hFm.lintegral_prod_right'
  rw [lintegral_add_left' hModm.aemeasurable]
  have hgi : Integrable (fun t => |g t|) := (hg.integrable_of_hasCompactSupport hgc).abs
  have hI0 : 0 ≤ ∫ t, |g t| := integral_nonneg fun _ => abs_nonneg _
  have hModb : ∫⁻ ω, Mod ω ∂P ≤ ENNReal.ofReal ((∫ t, |g t|) * K) := by
    simp only [hMod]
    rw [lintegral_lintegral_swap hFm.aemeasurable]
    have hpt2 : ∀ t, ∫⁻ ω, ENNReal.ofReal (|g t| * (bdryDens γ (zField X R ω) (2 * ε) t *
        chainT m (m + d) (fun a => Ht γ X R ε t a ω))) ∂P ≤
        ENNReal.ofReal |g t| * ENNReal.ofReal K := by
      intro t
      simp_rw [ENNReal.ofReal_mul (abs_nonneg (g t))]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      by_cases ht : t ∈ Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1)
      · have htR : |t| + 2 * ε ≤ R := by
          have := abs_le.2 ⟨ht.1, ht.2⟩
          rw [hR]; linarith
        gcongr
        exact lintegral_dens_chainT_le hX hγ hγ2 hε htR m (m + d)
      · rw [hgS t ht, abs_zero, ENNReal.ofReal_zero, zero_mul, zero_mul]
    refine (lintegral_mono hpt2).trans (le_of_eq ?_)
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
      ← ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ fun _ => abs_nonneg _),
      ← ENNReal.ofReal_mul hI0]
  have hGrb : ∫⁻ ω, Gr ω ∂P ≤
      ENNReal.ofReal ((2 ^ m + 1) * (Cg * exp (-bdryRate γ * (k * log 2)))) := by
    have hmem : ∀ l ∈ Finset.range (2 ^ m + 1), dpt m l ∈ Icc (1 : ℝ) 2 := fun l hl =>
      ⟨dpt_ge_one m l, dpt_le_two (by have := Finset.mem_range.1 hl; omega)⟩
    simp only [hGr]
    have hael : ∀ l ∈ Finset.range (2 ^ m + 1), AEMeasurable (fun ω =>
        ENNReal.ofReal |bA γ X R g (dpt m l * ε) ω - Lf γ X R g ω|) P := fun l hl =>
      (continuous_abs.measurable.comp_aemeasurable (hCg k _ (hmem l hl)).1).ennreal_ofReal
    rw [lintegral_finset_sum' _ hael]
    refine (Finset.sum_le_sum fun l hl => (hCg k _ (hmem l hl)).2).trans (le_of_eq ?_)
    have hC0 : 0 ≤ (2 : ℝ) ^ m + 1 := by positivity
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul hC0,
      show ((2 : ℝ) ^ m + 1) = ((2 ^ m + 1 : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
  refine (add_le_add hModb hGrb).trans (le_of_eq ?_)
  have hCg0' : 0 ≤ (2 ^ m + 1) * (Cg * exp (-bdryRate γ * (k * log 2))) := by positivity
  rw [← ENNReal.ofReal_add (mul_nonneg hI0 hK0) hCg0']

theorem aemeasurable_Lf [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {R : ℝ} {S : Set ℝ} (hS : MeasurableSet S)
    (hSf : volume S < ∞) (hSR : ∀ t ∈ S, |t| + 1 ≤ R) {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgS : ∀ t ∉ S, g t = 0) :
    AEMeasurable (Lf γ X R g) P := by
  obtain ⟨M, hM⟩ := hg.bounded_above_of_compact_support hgc
  have hM' : ∀ t, |g t| ≤ M := fun t => by simpa [Real.norm_eq_abs] using hM t
  obtain ⟨C₂, -, h₂⟩ :=
    integral_abs_bdryApprox_sub_qBoundaryMeasure_le hX hγ hγ2 hS hSf hSR hg hgc hgS
  have hB := integrable_integral_bdryApprox hX hS hSf hSR γ hg.measurable hM' hgS 0
  refine (hB.sub (h₂ 0).1).aemeasurable.congr (ae_of_all _ fun ω => ?_)
  simp only [Pi.sub_apply, Lf]
  ring

/-! ## C3. Summation over the scales -/

/-- The supremum over all dyadic offsets at scale `k`. -/
def supG (γ : ℝ) (X : Ω → FieldSample) (R : ℝ) (g : ℝ → ℝ) (k : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (i : Fin (2 ^ n + 1)),
    ENNReal.ofReal |bA γ X R g (dpt n i * radius k) ω - Lf γ X R g ω|

theorem dpt_double (n i : ℕ) : dpt n i = dpt (n + 1) (2 * i) := by
  unfold dpt; push_cast; rw [pow_succ]; field_simp

theorem level_mono (γ : ℝ) (X : Ω → FieldSample) (R : ℝ) (g : ℝ → ℝ) (k : ℕ) (ω : Ω) :
    Monotone (fun n : ℕ => ⨆ i : Fin (2 ^ n + 1),
      ENNReal.ofReal |bA γ X R g (dpt n i * radius k) ω - Lf γ X R g ω|) := by
  refine monotone_nat_of_le_succ fun n => iSup_le fun i => ?_
  have hi : 2 * (i : ℕ) < 2 ^ (n + 1) + 1 := by have := i.2; rw [pow_succ]; omega
  refine le_iSup_of_le (⟨2 * i, hi⟩ : Fin (2 ^ (n + 1) + 1)) (le_of_eq ?_)
  rw [dpt_double n i]

theorem lintegral_supG_le [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {N : ℕ} {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgS : ∀ t ∉ Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1), g t = 0)
    {Cg : ℝ} (hCg0 : 0 ≤ Cg) (hCg : ∀ k : ℕ, ∀ c ∈ Icc (1 : ℝ) 2,
      AEMeasurable (fun ω => bA γ X ((N : ℝ) + 3) g (c * radius k) ω -
        Lf γ X ((N : ℝ) + 3) g ω) P ∧
      ∫⁻ ω, ENNReal.ofReal |bA γ X ((N : ℝ) + 3) g (c * radius k) ω -
        Lf γ X ((N : ℝ) + 3) g ω| ∂P ≤
        ENNReal.ofReal (Cg * exp (-bdryRate γ * (k * log 2))))
    (k m : ℕ) :
    ∫⁻ ω, supG γ X ((N : ℝ) + 3) g k ω ∂P ≤
      ENNReal.ofReal ((∫ t, |g t|) * (((N : ℝ) + 3) ^ (γ ^ 2 / 4) *
          ((8 + 4 * (2544 * exp 16)) * θm ^ m)) +
        (2 ^ m + 1) * (Cg * exp (-bdryRate γ * (k * log 2)))) := by
  have hmeas : ∀ n, AEMeasurable (fun ω => ⨆ i : Fin (2 ^ n + 1), ENNReal.ofReal
      |bA γ X ((N : ℝ) + 3) g (dpt n i * radius k) ω - Lf γ X ((N : ℝ) + 3) g ω|) P :=
    fun n => AEMeasurable.iSup fun i =>
      (continuous_abs.measurable.comp_aemeasurable (hCg k _
        ⟨dpt_ge_one n i, dpt_le_two (Nat.lt_succ_iff.1 i.2)⟩).1).ennreal_ofReal
  show ∫⁻ ω, ⨆ n : ℕ, (⨆ i : Fin (2 ^ n + 1), ENNReal.ofReal
      |bA γ X ((N : ℝ) + 3) g (dpt n i * radius k) ω - Lf γ X ((N : ℝ) + 3) g ω|) ∂P ≤ _
  rw [lintegral_iSup' hmeas (ae_of_all _ fun ω => level_mono γ X _ g k ω)]
  refine iSup_le fun n => ?_
  obtain ⟨d, hd⟩ : ∃ d, max n m = m + d := ⟨max n m - m, by omega⟩
  exact (lintegral_mono fun ω => level_mono γ X _ g k ω (show n ≤ m + d by omega)).trans
    (lintegral_sup_level_le hX hγ hγ2 hg hgc hgS hCg0 hCg k m d)

theorem summable_bnd {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {A C : ℝ} (hA : 0 ≤ A)
    (hC : 0 ≤ C) :
    Summable (fun k : ℕ => A * θm ^ (⌊bdryRate γ * k / 2⌋₊) +
      (2 ^ (⌊bdryRate γ * k / 2⌋₊) + 1) * (C * exp (-bdryRate γ * (k * log 2)))) := by
  set β := bdryRate γ with hβd
  have hβ : 0 < β := bdryRate_pos hγ hγ2
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

/-! ## C4. Almost sure uniform convergence for the normalized field -/

theorem ae_tendsto_bA_goodFilter [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (N : ℕ) {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgS : ∀ t ∉ Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1), g t = 0) :
    ∀ᵐ ω ∂P, Tendsto (fun i : ℕ × ℝ => bA γ X ((N : ℝ) + 3) g (goodRad i) ω) goodFilter
      (𝓝 (Lf γ X ((N : ℝ) + 3) g ω)) := by
  set R : ℝ := (N : ℝ) + 3 with hR
  set S := Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1) with hS
  have hSR : ∀ t ∈ S, |t| + 2 ≤ R := fun t ht => by
    have := abs_le.2 ⟨ht.1, ht.2⟩; rw [hR]; linarith
  have hSR1 : ∀ t ∈ S, |t| + 1 ≤ R := fun t ht => by linarith [hSR t ht]
  obtain ⟨Cg, hCg0, hCg⟩ := exists_grid_rate hX hγ hγ2 measurableSet_Icc
    (volume_testSet_lt_top N) hSR hg hgc hgS
  have hLm := aemeasurable_Lf hX hγ hγ2 measurableSet_Icc (volume_testSet_lt_top N) hSR1 hg hgc
    hgS
  obtain ⟨M, hM⟩ := hg.bounded_above_of_compact_support hgc
  have hM' : ∀ t, |g t| ≤ M := fun t => by simpa [Real.norm_eq_abs] using hM t
  have hCg' : ∀ k : ℕ, ∀ c ∈ Icc (1 : ℝ) 2,
      AEMeasurable (fun ω => bA γ X R g (c * radius k) ω - Lf γ X R g ω) P ∧
      ∫⁻ ω, ENNReal.ofReal |bA γ X R g (c * radius k) ω - Lf γ X R g ω| ∂P ≤
        ENNReal.ofReal (Cg * exp (-bdryRate γ * (k * log 2))) := by
    intro k c hc
    have hcε : 0 < c * radius k := mul_pos (by linarith [hc.1]) (radius_pos k)
    have hcε2 : c * radius k ≤ 2 := by nlinarith [hc.2, radius_le_one k, radius_pos k]
    refine ⟨((integrable_bA hX hcε measurableSet_Icc (volume_testSet_lt_top N)
      (fun t ht => by linarith [hSR t ht]) γ hg.measurable hM' hgS).aemeasurable).sub hLm, ?_⟩
    exact hCg k c hc
  set I := ∫ t, |g t| with hI
  have hI0 : 0 ≤ I := integral_nonneg fun _ => abs_nonneg _
  set D := 8 + 4 * (2544 * exp 16) with hD
  have hR0 : 0 ≤ R := by positivity
  have hA0 : 0 ≤ I * (R ^ (γ ^ 2 / 4) * D) :=
    mul_nonneg hI0 (mul_nonneg (rpow_nonneg hR0 _) (by positivity))
  have hsum := summable_bnd hγ hγ2 hA0 hCg0
  have hGm : ∀ k, AEMeasurable (supG γ X R g k) P := fun k =>
    AEMeasurable.iSup fun n => AEMeasurable.iSup fun i =>
      (continuous_abs.measurable.comp_aemeasurable (hCg' k _
        ⟨dpt_ge_one n i, dpt_le_two (Nat.lt_succ_iff.1 i.2)⟩).1).ennreal_ofReal
  have hint : ∫⁻ ω, ∑' k, supG γ X R g k ω ∂P ≠ ∞ := by
    rw [lintegral_tsum hGm]
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑' k : ℕ, (I * (R ^ (γ ^ 2 / 4) * D) *
      θm ^ (⌊bdryRate γ * k / 2⌋₊) + (2 ^ (⌊bdryRate γ * k / 2⌋₊) + 1) *
        (Cg * exp (-bdryRate γ * (k * log 2)))))) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun k => add_nonneg (mul_nonneg hA0
      (pow_nonneg θm_pos.le _)) (mul_nonneg (by positivity) (mul_nonneg hCg0 (exp_pos _).le)))
      hsum]
    refine ENNReal.tsum_le_tsum fun k => ?_
    refine (lintegral_supG_le hX hγ hγ2 hg hgc hgS hCg0 hCg' k
      (⌊bdryRate γ * k / 2⌋₊)).trans (le_of_eq ?_)
    congr 1; ring
  have hae := ae_lt_top' (AEMeasurable.ennreal_tsum hGm) hint
  filter_upwards [hae, RegSample.ae_isRegularSample hX] with ω hω hreg
  obtain ⟨F, hF⟩ := hreg
  have hFZ := regular_zField (R := R) hF
  have hG0 : Tendsto (fun k => supG γ X R g k ω) atTop (𝓝 0) :=
    ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
  have hGfin : ∀ k, supG γ X R g k ω ≠ ∞ := fun k =>
    ne_top_of_le_ne_top hω.ne (ENNReal.le_tsum (f := fun k => supG γ X R g k ω) k)
  -- continuity in the offset
  have hbound : ∀ k : ℕ, ∀ a ∈ Icc (1 : ℝ) 2,
      |bA γ X R g (a * radius k) ω - Lf γ X R g ω| ≤ (supG γ X R g k ω).toReal := by
    intro k a ha
    set ε := radius k with hεd
    have hε := radius_pos k
    set φ : ℝ → ℝ := fun s => ∫ t in tsupport g,
      bdryDens γ (zField X R ω) (max s 1 * ε) t * g t with hφ
    have hpos : ∀ s : ℝ, 0 < max s 1 * ε := fun s => mul_pos (lt_max_of_lt_right one_pos) hε
    have hcont : Continuous (fun p : ℝ × ℝ =>
        bdryDens γ (zField X R ω) (max p.1 1 * ε) p.2 * g p.2) := by
      have e : (fun p : ℝ × ℝ => bdryDens γ (zField X R ω) (max p.1 1 * ε) p.2 * g p.2) =
          fun p => (max p.1 1 * ε) ^ (γ ^ 2 / 4) * exp (γ / 2 *
            (F ((p.2 : ℂ), max p.1 1 * ε) + -X ω (foldedCircle 0 R))) * g p.2 := by
        funext p
        rw [bdryDens, hFZ.evalReg_fc_of_mem (ofReal_mem_Hbar p.2) (hpos p.1)]
      rw [e]
      have hm : Continuous (fun p : ℝ × ℝ => max p.1 1 * ε) := by fun_prop
      have hF' : Continuous (fun p : ℝ × ℝ => F ((p.2 : ℂ), max p.1 1 * ε)) :=
        hF.1.comp_continuous (by fun_prop) (fun p => ⟨ofReal_mem_Hbar p.2, hpos p.1⟩)
      exact ((hm.rpow_const fun _ => Or.inr (by positivity)).mul
        (Real.continuous_exp.comp ((hF'.add continuous_const).const_mul _))).mul (hg.comp continuous_snd)
    have hφc : Continuous φ := continuous_parametric_integral_of_continuous hcont hgc
    have hφeq : ∀ s ∈ Icc (1 : ℝ) 2, bA γ X R g (s * ε) ω = φ s := by
      intro s hs
      rw [bA_eq_integral hX γ R (mul_pos (by linarith [hs.1]) hε) g ω, hφ]
      simp only [max_eq_left hs.1]
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => by
        rw [image_eq_zero_of_notMem_tsupport ht, mul_zero]]
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
    have hbd : ∀ n, |φ (dpt n (an n)) - Lf γ X R g ω| ≤ (supG γ X R g k ω).toReal := by
      intro n
      rw [← hφeq _ (hmem n), ← ENNReal.ofReal_le_iff_le_toReal (hGfin k)]
      exact le_iSup₂_of_le (f := fun (n : ℕ) (i : Fin (2 ^ n + 1)) => ENNReal.ofReal
        |bA γ X R g (dpt n i * radius k) ω - Lf γ X R g ω|) n
        ⟨an n, Nat.lt_succ_of_le (han_le n)⟩ le_rfl
    have hlim : Tendsto (fun n => |φ (dpt n (an n)) - Lf γ X R g ω|) atTop
        (𝓝 |φ a - Lf γ X R g ω|) :=
      (continuous_abs.tendsto _).comp (((hφc.tendsto a).comp hconv).sub_const _)
    rw [hφeq a ha]
    exact le_of_tendsto' hlim hbd
  rw [Metric.tendsto_nhds]
  intro η hη
  have h1 : ∀ᶠ k in atTop, (supG γ X R g k ω).toReal < η := by
    have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hG0
    simp only [ENNReal.toReal_zero] at ht
    exact ht.eventually (gt_mem_nhds hη)
  rw [goodFilter, eventually_prod_principal_iff]
  filter_upwards [h1] with k hk a ha
  rw [Real.dist_eq, goodRad]
  exact (hbound k a ha).trans_lt hk

/-! ## C5. Back to the free field -/

theorem integral_bdryR_eq_mul_bA {ω : Ω} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith (X ω) F)
    (γ R : ℝ) {r : ℝ} (hr : 0 < r) (g : ℝ → ℝ) :
    ∫ t, g t ∂bdryR γ (X ω) r = exp (γ / 2 * X ω (foldedCircle 0 R)) * bA γ X R g r ω := by
  have hFZ := regular_zField (R := R) hF
  rw [bA, bdryR, bdryR,
    integral_withDensity_ofReal (continuous_bdryDens γ hF hr).measurable
      (fun t => bdryDens_nonneg γ _ hr t),
    integral_withDensity_ofReal (continuous_bdryDens γ hFZ hr).measurable
      (fun t => bdryDens_nonneg γ _ hr t), ← integral_const_mul]
  congr 1
  funext t
  rw [bdryDens, bdryDens, hF.evalReg_fc_of_mem (ofReal_mem_Hbar t) hr,
    hFZ.evalReg_fc_of_mem (ofReal_mem_Hbar t) hr]
  have e : exp (γ / 2 * F ((t : ℂ), r)) = exp (γ / 2 * X ω (foldedCircle 0 R)) *
      exp (γ / 2 * (F ((t : ℂ), r) + -X ω (foldedCircle 0 R))) := by
    rw [← exp_add]; congr 1; ring
  rw [e]; ring

theorem ae_qBoundaryMeasure_eq_smul [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (R : ℝ) :
    ∀ᵐ ω ∂P, qBoundaryMeasure γ (X ω) =
      ENNReal.ofReal (exp (γ / 2 * X ω (foldedCircle 0 R))) •
        qBoundaryMeasure γ (zField X R ω) := by
  filter_upwards [ae_isVagueLimitR_qBoundaryMeasure_zField hX hγ hγ2 R,
    ae_bdryApprox_eq_smul hX γ R] with ω hv hs
  have h := IsVagueLimitR.const_smul hv (ENNReal.ofReal_ne_top (r := exp (γ / 2 * X ω (foldedCircle 0 R))))
  have e : (fun k => ENNReal.ofReal (exp (γ / 2 * X ω (foldedCircle 0 R))) •
      bdryApprox γ (zField X R ω) k) = bdryApprox γ (X ω) := funext fun k => (hs k).symm
  rw [e] at h
  exact qBoundaryMeasure_eq h

/-- **M4-B4.** For the free field (any additive-constant convention), almost surely the
approximating boundary measures `ν_{a 2^{-k}}(X ω)` converge vaguely to
`qBoundaryMeasure γ (X ω)`, uniformly in the offset `a ∈ [1,2]`. -/
theorem ae_hasBdryLimit [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, HasBdryLimit γ (X ω) (qBoundaryMeasure γ (X ω)) := by
  have hT : ∀ᵐ ω ∂P, ∀ N m : ℕ, Tendsto (fun i : ℕ × ℝ =>
      bA γ X ((N : ℝ) + 3) (testFam N m) (goodRad i) ω) goodFilter
      (𝓝 (Lf γ X ((N : ℝ) + 3) (testFam N m) ω)) :=
    ae_all_iff.2 fun N => ae_all_iff.2 fun m => ae_tendsto_bA_goodFilter hX hγ hγ2 N
      (continuous_testFam N m) (hasCompactSupport_testFam N m)
      (fun t ht => by simp [testFam, bump_eq_zero_of_notMem ht])
  have hB : ∀ᵐ ω ∂P, ∀ N : ℕ, Tendsto (fun i : ℕ × ℝ =>
      bA γ X ((N : ℝ) + 3) (bump N) (goodRad i) ω) goodFilter
      (𝓝 (Lf γ X ((N : ℝ) + 3) (bump N) ω)) :=
    ae_all_iff.2 fun N => ae_tendsto_bA_goodFilter hX hγ hγ2 N (continuous_bump N)
      (hasCompactSupport_bump N) (fun t ht => bump_eq_zero_of_notMem ht)
  have hQ : ∀ᵐ ω ∂P, ∀ N : ℕ, qBoundaryMeasure γ (X ω) =
      ENNReal.ofReal (exp (γ / 2 * X ω (foldedCircle 0 ((N : ℝ) + 3)))) •
        qBoundaryMeasure γ (zField X ((N : ℝ) + 3) ω) :=
    ae_all_iff.2 fun N => ae_qBoundaryMeasure_eq_smul hX hγ hγ2 _
  filter_upwards [hT, hB, hQ, ae_isVagueLimitR_qBoundaryMeasure hX hγ hγ2,
    RegSample.ae_isRegularSample hX] with ω hT hB hQ hv hreg
  obtain ⟨F, hF⟩ := hreg
  have : IsLocallyFiniteMeasure (qBoundaryMeasure γ (X ω)) := hv.1
  refine ⟨hv.1, fun f hf hfc => ?_⟩
  have htr : ∀ (N : ℕ) (g : ℝ → ℝ), Tendsto (fun i : ℕ × ℝ =>
      bA γ X ((N : ℝ) + 3) g (goodRad i) ω) goodFilter (𝓝 (Lf γ X ((N : ℝ) + 3) g ω)) →
      Tendsto (fun i => ∫ x, g x ∂bdryR γ (X ω) (goodRad i)) goodFilter
        (𝓝 (∫ x, g x ∂qBoundaryMeasure γ (X ω))) := by
    intro N g h
    rw [hQ N, integral_smul_measure, ENNReal.toReal_ofReal (exp_pos _).le, smul_eq_mul]
    refine (h.const_mul _).congr' (eventually_goodRad_pos.mono fun i hi => ?_)
    exact (integral_bdryR_eq_mul_bA hF γ _ hi g).symm
  exact tendsto_goodFilter_of_testFam
    (eventually_goodRad_pos.mono fun i hi => ⟨fun K hK => bdryR_lt_top γ hF hi hK⟩)
    (fun N m => htr N _ (hT N m)) (fun N => htr N _ (hB N)) hf hfc

/-! ## T2. Translation and reflection (M4-T2) -/

section T2

variable {x : FieldSample} {γ : ℝ}

theorem bdryDens_translate {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F) (γ t : ℝ) {r : ℝ}
    (hr : 0 < r) (s : ℝ) : bdryDens γ (translate x (t : ℂ)) r s = bdryDens γ x r (s + t) := by
  rw [bdryDens, bdryDens, (hF.translate' t).evalReg_fc_of_mem (ofReal_mem_Hbar s) hr,
    hF.evalReg_fc_of_mem (ofReal_mem_Hbar _) hr, Complex.ofReal_add]

theorem integral_bdryR_translate {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F) (γ t : ℝ) {r : ℝ}
    (hr : 0 < r) (f : ℝ → ℝ) :
    ∫ s, f s ∂bdryR γ (translate x (t : ℂ)) r = ∫ u, f (u - t) ∂bdryR γ x r := by
  have hFt := hF.translate' t
  rw [bdryR, bdryR, integral_withDensity_ofReal (continuous_bdryDens γ hFt hr).measurable
      (fun s => bdryDens_nonneg γ _ hr s),
    integral_withDensity_ofReal (continuous_bdryDens γ hF hr).measurable
      (fun s => bdryDens_nonneg γ _ hr s)]
  simp_rw [bdryDens_translate hF γ t hr]
  have h := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun u => bdryDens γ x r u * f (u - t)) t
  simp only [add_sub_cancel_right] at h
  exact h

theorem hasBdryLimit_translate (hx : IsRegularSample x) {ν : Measure ℝ}
    (hν : HasBdryLimit γ x ν) (t : ℝ) :
    HasBdryLimit γ (translate x (t : ℂ)) (ν.map (· - t)) := by
  obtain ⟨F, hF⟩ := hx
  have := hν.1
  have hmeas : Measurable (fun u : ℝ => u - t) := measurable_id.sub_const t
  have : IsFiniteMeasureOnCompacts (ν.map (· - t)) := ⟨fun K hK => by
    rw [Measure.map_apply hmeas hK.isClosed.measurableSet]
    exact ((Homeomorph.subRight t).isCompact_preimage.2 hK).measure_lt_top⟩
  refine ⟨inferInstance, fun f hf hfc => ?_⟩
  rw [integral_map hmeas.aemeasurable hf.aestronglyMeasurable]
  refine (hν.2 (fun u => f (u - t)) (hf.comp (continuous_sub_right t))
    (hfc.comp_homeomorph (Homeomorph.subRight t))).congr'
    (eventually_goodRad_pos.mono fun i hi => ?_)
  exact (integral_bdryR_translate hF γ t hi f).symm

/-- **M4-T2 (translation)**: for a good sample and every real `t`,
`ν_{h(· + t)} = (· − t)_* ν_h`. -/
theorem qBoundaryMeasure_translate (hx : IsLQGGood γ x) (t : ℝ) :
    qBoundaryMeasure γ (translate x (t : ℂ)) = (qBoundaryMeasure γ x).map (· - t) :=
  qBoundaryMeasure_eq_of_hasBdryLimit (hx.1.translate' t)
    (hasBdryLimit_translate hx.1 hx.qBoundaryMeasure_spec t)

theorem bdryDens_reflectH {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F) (γ : ℝ) {r : ℝ}
    (hr : 0 < r) (s : ℝ) : bdryDens γ (RegClosure.reflectH x) r s = bdryDens γ x r (-s) := by
  rw [bdryDens, bdryDens, hF.reflectH'.evalReg_fc_of_mem (ofReal_mem_Hbar s) hr,
    hF.evalReg_fc_of_mem (ofReal_mem_Hbar _) hr, Complex.conj_ofReal, Complex.ofReal_neg]

theorem integral_bdryR_reflectH {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F) (γ : ℝ) {r : ℝ}
    (hr : 0 < r) (f : ℝ → ℝ) :
    ∫ s, f s ∂bdryR γ (RegClosure.reflectH x) r = ∫ u, f (-u) ∂bdryR γ x r := by
  rw [bdryR, bdryR, integral_withDensity_ofReal (continuous_bdryDens γ hF.reflectH' hr).measurable
      (fun s => bdryDens_nonneg γ _ hr s),
    integral_withDensity_ofReal (continuous_bdryDens γ hF hr).measurable
      (fun s => bdryDens_nonneg γ _ hr s)]
  simp_rw [bdryDens_reflectH hF γ hr]
  have h := integral_neg_eq_self (fun u => bdryDens γ x r u * f (-u)) (volume : Measure ℝ)
  simp only [neg_neg] at h
  exact h

theorem hasBdryLimit_reflectH (hx : IsRegularSample x) {ν : Measure ℝ}
    (hν : HasBdryLimit γ x ν) :
    HasBdryLimit γ (RegClosure.reflectH x) (ν.map fun s => -s) := by
  obtain ⟨F, hF⟩ := hx
  have := hν.1
  have hmeas : Measurable (fun u : ℝ => -u) := measurable_neg
  have : IsFiniteMeasureOnCompacts (ν.map fun s => -s) := ⟨fun K hK => by
    rw [Measure.map_apply hmeas hK.isClosed.measurableSet]
    exact ((Homeomorph.neg ℝ).isCompact_preimage.2 hK).measure_lt_top⟩
  refine ⟨inferInstance, fun f hf hfc => ?_⟩
  rw [integral_map hmeas.aemeasurable hf.aestronglyMeasurable]
  refine (hν.2 (fun u => f (-u)) (hf.comp continuous_neg)
    (hfc.comp_homeomorph (Homeomorph.neg ℝ))).congr'
    (eventually_goodRad_pos.mono fun i hi => ?_)
  exact (integral_bdryR_reflectH hF γ hi f).symm

/-- **M4-T2 (reflection)**: for a good sample, `ν_{h(−·̄)} = (−·)_* ν_h`. -/
theorem qBoundaryMeasure_reflectH (hx : IsLQGGood γ x) :
    qBoundaryMeasure γ (RegClosure.reflectH x) = (qBoundaryMeasure γ x).map fun s => -s :=
  qBoundaryMeasure_eq_of_hasBdryLimit hx.1.reflectH'
    (hasBdryLimit_reflectH hx.1 hx.qBoundaryMeasure_spec)

end T2

end AllOffsets
end QuantumZipper
