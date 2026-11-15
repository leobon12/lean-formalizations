import InteractingSLE.GFF.LocalSets.Prop38Version

/-!
# Proposition 3.8: Borel–Cantelli on random dyadic layers

Specification §3.2, proof of Proposition 3.8 (p. 60: "There are at most `C δ^{-2}` such squares at
scale `δ`. … Markov's inequality and Borel–Cantelli show that on `E`, simultaneously on all
sufficiently small squares, `sup_Q |𝒞_B| ≤ δ^β`"), packet PROVE-LS-C.

This is the Borel–Cantelli step of Proposition 3.3 (`GFF.ae_eventually_abs_lt`, landed) with a
**random** domain `O(ω)` and an event `E`: the dyadic layers
`L_n(ω) = {y ∈ O(ω) ∩ B(c, 3R) : 2^{-n-2} ≤ dist(y, ∂O(ω)) ≤ 2 · 2^{-n}}` replace the Whitney
squares, the sub-mean-value inequality for `e^{±λ u}` (`u` harmonic) bounds the supremum over the
inner layer by `4^n` times the integral over `L_n`, and the pointwise exponential moments on `E`
(the hypothesis `hmom`, supplied by `lintegral_indicator_exp_meanDiff_le` and the Koebe bound) give
summable probabilities with `λ_n = n log 8 / η`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology TopologicalSpace Metric
open scoped ENNReal

namespace InteractingSLE
namespace LocalSets

open QuantumZipper LQGMetric
open QuantumZipper.CA.Koebe (koebeCovConst koebeDistExp koebeCovConst_pos koebeDistExp_pos)
open GFF (layerSet closedBall_subset_layerSet eventually_params eight_pow_mul_half_pow_sq
  ofReal_exp_mul_le_lintegral_of_harmonic bumpMass bumpMass_pos)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Borel–Cantelli on random dyadic layers.** Let `u(ω)` be harmonic on `O(ω) ∩ B(c, 4R)` for
almost every `ω ∈ E`, with jointly measurable versions `G_n` on the layers, and suppose the
pointwise exponential moments `E[1_E 1_{y ∈ L_n} e^{l G_n(·, y)}] ≤ e` hold for `2 l² τ_n ≤ 1`.
Then for every `η > 0`, almost surely on `E`, eventually `|u| < η` on the inner layers
`{w ∈ O ∩ B(c, 2R) : 2^{-n-1} ≤ dist(w, ∂O) ≤ 2^{-n}}`. -/
theorem ae_eventually_abs_lt_of_layer {O : Ω → Set ℂ} {E : Set Ω} (hE : MeasurableSet E)
    {u : Ω → ℂ → ℝ} {G : ℕ → Ω × ℂ → ℝ} (hGm : ∀ n, Measurable (G n)) {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hL : ∀ n, MeasurableSet {p : Ω × ℂ | p.2 ∈ layerSet (O p.1) c R n})
    {n₁ : ℕ} (hu : ∀ᵐ ω ∂P, ω ∈ E → IsOpen (O ω) ∧
      InnerProductSpace.HarmonicOnNhd (u ω) (O ω ∩ ball c (4 * R)) ∧
      ∀ n ≥ n₁, ∀ y ∈ layerSet (O ω) c R n, G n (ω, y) = u ω y)
    (hmom : ∀ n ≥ n₁, ∀ y : ℂ, ∀ l : ℝ,
      2 * l ^ 2 * (2 * (2 * (1 / 2 : ℝ) ^ n) / (koebeCovConst * R)) ^ koebeDistExp⁻¹ ≤ 1 →
      ∫⁻ ω, (E ∩ {ω | y ∈ layerSet (O ω) c R n}).indicator
        (fun ω => ENNReal.ofReal (Real.exp (l * G n (ω, y)))) ω ∂P ≤ ENNReal.ofReal (Real.exp 1))
    {η : ℝ} (hη : 0 < η) :
    ∀ᵐ ω ∂P, ω ∈ E → ∃ N : ℕ, ∀ n ≥ N, ∀ w ∈ O ω, dist w c < 2 * R →
      (1 / 2 : ℝ) ^ (n + 1) ≤ infDist w (O ω)ᶜ → infDist w (O ω)ᶜ ≤ (1 / 2 : ℝ) ^ n →
        |u ω w| < η := by
  set lam : ℕ → ℝ := fun n => n * Real.log 8 / η with hlam
  set e₁ := expNegInvGlue 1 with he₁
  set Ls : ℕ → Set (Ω × ℂ) := fun n => {p : Ω × ℂ | p.2 ∈ layerSet (O p.1) c R n} with hLs
  set f : ℕ → ℝ → Ω × ℂ → ℝ≥0∞ := fun n l => (Ls n).indicator
    fun p => ENNReal.ofReal (Real.exp (l * G n p)) with hf
  have hfm : ∀ n l, Measurable (f n l) := fun n l =>
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul (hGm n)))).indicator (hL n)
  set I : ℕ → ℝ → Ω → ℝ≥0∞ := fun n l ω => ∫⁻ y, f n l (ω, y) with hI
  have hIm : ∀ n l, Measurable (I n l) := fun n l => (hfm n l).lintegral_prod_right'
  -- the expected layer integral on `E`
  set X : ℝ≥0∞ := ENNReal.ofReal (Real.exp 1) * volume (ball c (3 * R)) with hX
  have hEI : ∀ n ≥ n₁, ∀ l : ℝ,
      2 * l ^ 2 * (2 * (2 * (1 / 2 : ℝ) ^ n) / (koebeCovConst * R)) ^ koebeDistExp⁻¹ ≤ 1 →
      ∫⁻ ω, E.indicator (I n l) ω ∂P ≤ X := by
    intro n hn l hl
    have hm2 : Measurable fun p : Ω × ℂ => E.indicator (fun ω => f n l (ω, p.2)) p.1 := by
      have : (fun p : Ω × ℂ => E.indicator (fun ω => f n l (ω, p.2)) p.1) =
          (E ×ˢ univ).indicator (f n l) := by
        funext p
        by_cases hp : p.1 ∈ E
        · rw [indicator_of_mem hp, indicator_of_mem (mk_mem_prod hp (mem_univ _))]
        · rw [indicator_of_notMem hp, indicator_of_notMem (fun h => hp (mem_prod.1 h).1)]
      rw [this]
      exact (hfm n l).indicator (hE.prod MeasurableSet.univ)
    have e1 : ∀ ω, E.indicator (I n l) ω = ∫⁻ y, E.indicator (fun ω => f n l (ω, y)) ω := by
      intro ω
      by_cases hω : ω ∈ E
      · simp only [indicator_of_mem hω]; rfl
      · simp only [indicator_of_notMem hω, lintegral_zero]
    simp_rw [e1]
    rw [lintegral_lintegral_swap hm2.aemeasurable]
    calc ∫⁻ y, ∫⁻ ω, E.indicator (fun ω => f n l (ω, y)) ω ∂P
        ≤ ∫⁻ y, (ball c (3 * R)).indicator (fun _ => ENNReal.ofReal (Real.exp 1)) y := by
          refine lintegral_mono fun y => ?_
          by_cases hy : y ∈ ball c (3 * R)
          · rw [indicator_of_mem hy]
            refine le_trans (le_of_eq ?_) (hmom n hn y l hl)
            congr 1; funext ω
            by_cases hω : ω ∈ E
            · by_cases hyL : y ∈ layerSet (O ω) c R n
              · rw [indicator_of_mem hω, indicator_of_mem
                  (show ω ∈ E ∩ {ω | y ∈ layerSet (O ω) c R n} from ⟨hω, hyL⟩)]
                simp only [hf, hLs]; rw [indicator_of_mem (show (ω, y) ∈ Ls n from hyL)]
              · rw [indicator_of_mem hω, indicator_of_notMem (fun h => hyL h.2)]
                simp only [hf, hLs]; rw [indicator_of_notMem (show (ω, y) ∉ Ls n from hyL)]
            · rw [indicator_of_notMem hω, indicator_of_notMem (fun h => hω h.1)]
          · rw [indicator_of_notMem hy]
            have h0 : ∀ ω, E.indicator (fun ω => f n l (ω, y)) ω = 0 := fun ω => by
              by_cases hω : ω ∈ E
              · rw [indicator_of_mem hω]
                simp only [hf, hLs]
                rw [indicator_of_notMem]
                exact fun h => hy (GFF.layerSet_subset_ball _ _ _ _ h)
              · rw [indicator_of_notMem hω]
            simp only [h0, lintegral_zero, le_refl]
      _ = X := by rw [lintegral_indicator_const measurableSet_ball, hX]
  set F : ℕ → Set Ω := fun n => {ω | ENNReal.ofReal (Real.exp (lam n * η) *
      (((1 / 2 : ℝ) ^ (n + 2)) ^ 2 * bumpMass)) ≤
      E.indicator (fun ω => ENNReal.ofReal e₁ * (I n (lam n) ω + I n (-lam n) ω)) ω} with hF
  obtain ⟨n₀', hn₀'⟩ := eventually_atTop.1 (eventually_params hR η)
  set n₀ := max n₀' n₁ with hn₀def
  have hn₀ : ∀ n ≥ n₀, (1 / 2 : ℝ) ^ (n + 2) ≤ R ∧
      (2 * (2 * (1 / 2 : ℝ) ^ n) / (koebeCovConst * R)) ^ koebeDistExp⁻¹ ≤ 1 / 4 ∧
      2 * ((n : ℝ) * Real.log 8 / η) ^ 2 *
        (2 * (2 * (1 / 2 : ℝ) ^ n) / (koebeCovConst * R)) ^ koebeDistExp⁻¹ ≤ 1 :=
    fun n hn => hn₀' n (le_of_max_le_left hn)
  set K : ℝ≥0∞ := ENNReal.ofReal e₁ * (X + X) / ENNReal.ofReal (bumpMass / 16) with hK
  have hc₁ := bumpMass_pos
  have hPF : ∀ n ≥ n₀, P (F n) ≤ K * 2⁻¹ ^ n := by
    intro n hn
    obtain ⟨-, -, hl⟩ := hn₀ n hn
    have hn1 : n ≥ n₁ := le_of_max_le_right hn
    have hl' : 2 * (-lam n) ^ 2 *
        (2 * (2 * (1 / 2 : ℝ) ^ n) / (koebeCovConst * R)) ^ koebeDistExp⁻¹ ≤ 1 := by
      rwa [neg_sq]
    have h1 := hEI n hn1 (lam n) hl
    have h2 := hEI n hn1 (-lam n) hl'
    have hexp : Real.exp (lam n * η) = 8 ^ n := by
      have : lam n * η = n * Real.log 8 := by simp only [hlam]; field_simp
      rw [this, Real.exp_nat_mul, Real.exp_log (by norm_num)]
    have hden : ENNReal.ofReal (Real.exp (lam n * η) * (((1 / 2 : ℝ) ^ (n + 2)) ^ 2 * bumpMass)) =
        ENNReal.ofReal (bumpMass / 16) * 2 ^ n := by
      rw [hexp, ← mul_assoc, eight_pow_mul_half_pow_sq, show (2 : ℝ) ^ n / 16 * bumpMass =
        bumpMass / 16 * 2 ^ n by ring, ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
    have ha0 : ENNReal.ofReal (bumpMass / 16) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have hden0 : ENNReal.ofReal (bumpMass / 16) * 2 ^ n ≠ 0 :=
      mul_ne_zero ha0 (pow_ne_zero _ two_ne_zero)
    have hdentop : ENNReal.ofReal (bumpMass / 16) * 2 ^ n ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
    have hgm : Measurable fun ω => ENNReal.ofReal e₁ * (I n (lam n) ω + I n (-lam n) ω) :=
      measurable_const.mul ((hIm n _).add (hIm n _))
    have hmeasF : AEMeasurable (E.indicator
        fun ω => ENNReal.ofReal e₁ * (I n (lam n) ω + I n (-lam n) ω)) P :=
      (hgm.indicator hE).aemeasurable
    have hsplit : ∀ ω, E.indicator (fun ω => ENNReal.ofReal e₁ * (I n (lam n) ω +
        I n (-lam n) ω)) ω = ENNReal.ofReal e₁ * (E.indicator (I n (lam n)) ω +
          E.indicator (I n (-lam n)) ω) := fun ω => by
      by_cases hω : ω ∈ E
      · simp only [indicator_of_mem hω]
      · simp only [indicator_of_notMem hω, add_zero, mul_zero]
    calc P (F n) ≤ (∫⁻ ω, E.indicator (fun ω => ENNReal.ofReal e₁ * (I n (lam n) ω +
          I n (-lam n) ω)) ω ∂P) / (ENNReal.ofReal (bumpMass / 16) * 2 ^ n) := by
          have := meas_ge_le_lintegral_div hmeasF hden0 hdentop
          simp only [hF, hden]
          exact this
      _ = ENNReal.ofReal e₁ * ((∫⁻ ω, E.indicator (I n (lam n)) ω ∂P) +
          ∫⁻ ω, E.indicator (I n (-lam n)) ω ∂P) /
          (ENNReal.ofReal (bumpMass / 16) * 2 ^ n) := by
          simp_rw [hsplit]
          rw [lintegral_const_mul (f := fun ω => E.indicator (I n (lam n)) ω +
              E.indicator (I n (-lam n)) ω) _
              (((hIm n _).indicator hE).add ((hIm n _).indicator hE)),
            lintegral_add_left (f := E.indicator (I n (lam n))) ((hIm n _).indicator hE)]
      _ ≤ ENNReal.ofReal e₁ * (X + X) / (ENNReal.ofReal (bumpMass / 16) * 2 ^ n) := by
          gcongr
      _ = K * 2⁻¹ ^ n := by
          rw [hK, div_eq_mul_inv, ENNReal.mul_inv (Or.inl ha0) (Or.inl ENNReal.ofReal_ne_top),
            ENNReal.inv_pow, ← mul_assoc, ← div_eq_mul_inv]
  have hKtop : K ≠ ⊤ := by
    refine ENNReal.div_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_)
      (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have : X ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
    exact ENNReal.add_ne_top.2 ⟨this, this⟩
  have hsum : ∑' k, P (F (k + n₀)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∑' k : ℕ, K * 2⁻¹ ^ k) ?_ (ENNReal.tsum_le_tsum fun k =>
      (hPF (k + n₀) (by omega)).trans (mul_le_mul_right
        (pow_le_pow_of_le_one zero_le (ENNReal.inv_le_one.2 one_le_two) (Nat.le_add_right k n₀))
        K))
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.mul_ne_top hKtop ENNReal.ofNat_ne_top
  -- Borel–Cantelli
  filter_upwards [ae_eventually_notMem hsum, hu] with ω hev hωu hωE
  obtain ⟨hOo, hharm, hGu⟩ := hωu hωE
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 hev
  refine ⟨K₀ + n₀, fun n hn w hwO hwc h1 h2 => ?_⟩
  have hn' : n₀ ≤ n := by omega
  have hnotF : ω ∉ F n := by
    have := hK₀ (n - n₀) (by omega)
    rwa [Nat.sub_add_cancel hn'] at this
  obtain ⟨hεR, -, -⟩ := hn₀ n hn'
  have hball := closedBall_subset_layerSet (D := O ω) hεR hwc h1 h2
  have hLU : layerSet (O ω) c R n ⊆ O ω ∩ ball c (4 * R) := fun y hy =>
    ⟨hy.1.1.1, by have := hy.1.1.2; rw [mem_ball] at this ⊢; linarith⟩
  have hBU : closedBall w ((1 / 2 : ℝ) ^ (n + 2)) ⊆ O ω ∩ ball c (4 * R) := hball.trans hLU
  have hIeq : ∀ l, ∫⁻ y in layerSet (O ω) c R n, ENNReal.ofReal (Real.exp (l * u ω y)) =
      I n l ω := by
    intro l
    have hLm : MeasurableSet (layerSet (O ω) c R n) := measurable_prodMk_left (hL n)
    rw [hI, ← lintegral_indicator hLm]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ layerSet (O ω) c R n
    · rw [indicator_of_mem hy]
      simp only [hf, hLs]
      rw [indicator_of_mem (show (ω, y) ∈ Ls n from hy), hGu n (le_of_max_le_right hn') y hy]
    · rw [indicator_of_notMem hy]
      simp only [hf, hLs]
      rw [indicator_of_notMem (show (ω, y) ∉ Ls n from hy)]
  have hJ := fun l => ofReal_exp_mul_le_lintegral_of_harmonic (hOo.inter isOpen_ball) hharm
    (by positivity) hBU l hball
  by_contra hlt
  push Not at hlt
  apply hnotF
  show ENNReal.ofReal (Real.exp (lam n * η) * (((1 / 2 : ℝ) ^ (n + 2)) ^ 2 * bumpMass)) ≤
    E.indicator (fun ω => ENNReal.ofReal e₁ * (I n (lam n) ω + I n (-lam n) ω)) ω
  rw [indicator_of_mem hωE]
  have hlam0 : 0 ≤ lam n := by simp only [hlam]; positivity
  have hpos : 0 ≤ ((1 / 2 : ℝ) ^ (n + 2)) ^ 2 * bumpMass := by positivity
  rcases le_abs'.1 hlt with hneg | hpos'
  · calc ENNReal.ofReal (Real.exp (lam n * η) * (((1 / 2 : ℝ) ^ (n + 2)) ^ 2 * bumpMass))
        ≤ ENNReal.ofReal (Real.exp (-lam n * u ω w) * (((1 / 2 : ℝ) ^ (n + 2)) ^ 2 * bumpMass)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
            (Real.exp_le_exp.2 (by nlinarith)) hpos)
      _ ≤ ENNReal.ofReal e₁ * I n (-lam n) ω := by rw [← hIeq]; exact hJ (-lam n)
      _ ≤ _ := by gcongr; exact le_add_self
  · calc ENNReal.ofReal (Real.exp (lam n * η) * (((1 / 2 : ℝ) ^ (n + 2)) ^ 2 * bumpMass))
        ≤ ENNReal.ofReal (Real.exp (lam n * u ω w) * (((1 / 2 : ℝ) ^ (n + 2)) ^ 2 * bumpMass)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
            (Real.exp_le_exp.2 (by nlinarith)) hpos)
      _ ≤ ENNReal.ofReal e₁ * I n (lam n) ω := by rw [← hIeq]; exact hJ (lam n)
      _ ≤ _ := by gcongr; exact le_self_add

end LocalSets
end InteractingSLE
