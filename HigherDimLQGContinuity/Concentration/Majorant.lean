import HigherDimLQGContinuity.Concentration.Confine

/-!
# The majorant `U`: specification, exponential moment, tail and moments (packet N4)

Blueprint Part C Lemma `c:lem-confine` (b)–(c) and the probabilistic half of (a); NA4 A1 Step 2.

Fix a metric family `ρ` and envelopes `H_k` at the dyadic radii `2^(k+1)` (the (U1) envelopes of
`lemma21_core`), and let `K = confinementExp ρ`, `U = geodMajorant σ H K`.

* `ae_exists_confineGood`: by (U2) the confinement test passes at some scale a.s.
* `measure_le_confinementExp`: `ℙ{K ≥ k} ≤ C_U 2^{-k p_esc}`; `lintegral_two_rpow_confinementExp_le`:
  `∫ 2^{(p_esc/2) K} ≤ C_U / (1 - 2^{-p_esc/2})`.
* `envSum`: `W = 1 + ∑_k 2^{-k} (1 + 2^{k+1})^{-A} H_k^{p_*}` with `∫ W ≤ 1 + 2 C_U` (`lintegral_envSum_le`) and
  `H_k^{p_*} ≤ 2^k (1 + 2^{k+1})^A W` where `W < ∞` (`rpow_le_of_envSum_lt_top`). (This replaces the blueprint's
  union bound over `κ` dyadic scales for `log Ĥ`: a summed envelope controls all scales at once.)
* `geodMajorant_spec`: a.s., every constant-speed `ρ`-geodesic from `0` to `e₁` lies in `B̄_S` and
  `ν_η(B̄_r(z)) ≤ B r^σ`, with `S = 2^(K+1)`, `B = 2 H_K H_0`, `U = 1 + (log B + 1)/σ + log(2 + S)`.
* `lintegral_exp_geodMajorant_le`: `∫ e^{c U} ≤ M` with explicit `c > 0`, `M` depending only on
  `(p_*, σ, A, p_esc, C_U)` (`majorantRate`, `majorantBound`); hence the exponential tail
  (`tail_geodMajorant`, the blueprint's (b)) and `∫ U^q ≤ (q/c)^q M` (`lintegral_geodMajorant_rpow_le`).
* (c): `abs_logRho_le_logEnvelope` (`|log ρ(0, e₁)| ≤ log H₁`) and `lintegral_log_rpow_le`
  (`∫ (log H)^q ≤ (q/p)^q ∫ H^p`).
* `exists_geodMajorant`: everything packaged for strong metrics from `lemma21_core`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

variable {d : ℕ}

/-! ## Elementary moment bounds -/

/-- `x^q ≤ (q/c)^q e^{c x}` for `x ≥ 0` and `q, c > 0` (from `log y ≤ y - 1`). -/
theorem n4_rpow_le_mul_exp {x q c : ℝ} (hx : 0 ≤ x) (hq : 0 < q) (hc : 0 < c) :
    x ^ q ≤ (q / c) ^ q * Real.exp (c * x) := by
  rcases hx.eq_or_lt with rfl | hx0
  · rw [Real.zero_rpow hq.ne']
    positivity
  have hqc : 0 < q / c := div_pos hq hc
  rw [Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos hqc, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h1 : Real.log (x / (q / c)) ≤ x / (q / c) - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hx0.ne' hqc.ne'] at h1
  have h2 : q * (Real.log x - Real.log (q / c)) ≤ q * (x / (q / c) - 1) :=
    mul_le_mul_of_nonneg_left h1 hq.le
  have h3 : q * (x / (q / c) - 1) = c * x - q := by
    field_simp
  nlinarith

/-- Moments from an exponential moment: if `∫ e^{c U} ≤ M` and `U ≥ 0`, then `∫ U^q ≤ (q/c)^q M` (`q > 0`). -/
theorem n4_lintegral_rpow_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {U : α → ℝ}
    (hU : ∀ g, 0 ≤ U g) {c M : ℝ} (hc : 0 < c)
    (hM : ∫⁻ g, ENNReal.ofReal (Real.exp (c * U g)) ∂μ ≤ ENNReal.ofReal M) {q : ℝ} (hq : 0 < q) :
    ∫⁻ g, ENNReal.ofReal (U g ^ q) ∂μ ≤ ENNReal.ofReal ((q / c) ^ q * M) := by
  have hqc : 0 ≤ (q / c) ^ q := by positivity
  calc ∫⁻ g, ENNReal.ofReal (U g ^ q) ∂μ
      ≤ ∫⁻ g, ENNReal.ofReal ((q / c) ^ q) * ENNReal.ofReal (Real.exp (c * U g)) ∂μ := by
        refine lintegral_mono fun g => ?_
        rw [← ENNReal.ofReal_mul hqc]
        exact ENNReal.ofReal_le_ofReal (n4_rpow_le_mul_exp (hU g) hq hc)
    _ = ENNReal.ofReal ((q / c) ^ q) * ∫⁻ g, ENNReal.ofReal (Real.exp (c * U g)) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((q / c) ^ q) * ENNReal.ofReal M := by gcongr
    _ = ENNReal.ofReal ((q / c) ^ q * M) := (ENNReal.ofReal_mul hqc).symm

/-- The exponential tail from an exponential moment (Markov): `ℙ{U > u} ≤ M e^{-c u}`. -/
theorem n4_measure_lt_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {U : α → ℝ}
    (hUm : Measurable U) {c M : ℝ} (hc : 0 < c)
    (hM : ∫⁻ g, ENNReal.ofReal (Real.exp (c * U g)) ∂μ ≤ ENNReal.ofReal M) (u : ℝ) :
    μ {g | u < U g} ≤ ENNReal.ofReal (M * Real.exp (-(c * u))) := by
  have hmeas : AEMeasurable (fun g => ENNReal.ofReal (Real.exp (c * U g))) μ :=
    ((hUm.const_mul c).exp.ennreal_ofReal).aemeasurable
  have h1 := mul_meas_ge_le_lintegral₀ hmeas (ENNReal.ofReal (Real.exp (c * u)))
  have hsub : {g | u < U g} ⊆
      {g | ENNReal.ofReal (Real.exp (c * u)) ≤ ENNReal.ofReal (Real.exp (c * U g))} := by
    intro g hg
    have hg' : u < U g := hg
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by nlinarith))
  have hpos : ENNReal.ofReal (Real.exp (c * u)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  calc μ {g | u < U g}
      ≤ μ {g | ENNReal.ofReal (Real.exp (c * u)) ≤ ENNReal.ofReal (Real.exp (c * U g))} :=
        measure_mono hsub
    _ ≤ ENNReal.ofReal M / ENNReal.ofReal (Real.exp (c * u)) := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
        exact h1.trans hM
    _ = ENNReal.ofReal (M * Real.exp (-(c * u))) := by
        rw [Real.exp_neg, ← div_eq_mul_inv, ENNReal.ofReal_div_of_pos (Real.exp_pos _)]

/-- `(2^n)^{-a} = (2^{-a})^n`. -/
theorem n4_two_pow_rpow_neg (n : ℕ) (a : ℝ) : ((2 : ℝ) ^ n) ^ (-a) = ((2 : ℝ) ^ (-a)) ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
    Real.rpow_natCast]

/-! ## The confinement exponent: a.s. finiteness and tail -/

section Tail

variable {ρ : DistRd d → ContMetric d} {μ : Measure (DistRd d)} {CU pesc : ℝ}

/-- The escape bound (U2) as a hypothesis. -/
def EscapeBound (ρ : DistRd d → ContMetric d) (μ : Measure (DistRd d)) (CU pesc : ℝ) : Prop :=
  ∀ S : ℝ, 1 ≤ S → μ {g | ∃ y : Rd d, S ≤ ‖y‖ ∧ (ρ g).1 (0, y) ≤ (ρ g).1 (0, e₁ d)} ≤
    ENNReal.ofReal (CU * S ^ (-pesc))

/-- A failed test at scale `k` has probability at most `C_U 2^{-(k+1) p_esc}`. -/
theorem measure_not_confineGood_le (hesc : EscapeBound ρ μ CU pesc) (k : ℕ) :
    μ {g | ¬ confineGood ρ k g} ≤ ENNReal.ofReal (CU * ((2 : ℝ) ^ (-pesc)) ^ (k + 1)) := by
  rw [← n4_two_pow_rpow_neg]
  refine (measure_mono fun g hg => exists_of_not_confineGood hg).trans (hesc _ ?_)
  exact one_le_pow₀ (by norm_num)

/-- **The confinement test passes at some scale almost surely.** -/
theorem ae_exists_confineGood (hpesc : 0 < pesc) (hesc : EscapeBound ρ μ CU pesc) :
    ∀ᵐ g ∂μ, ∃ k, confineGood ρ k g := by
  rw [ae_iff]
  have hr0 : 0 ≤ (2 : ℝ) ^ (-pesc) := by positivity
  have hr1 : (2 : ℝ) ^ (-pesc) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hlim : Tendsto (fun k : ℕ => ENNReal.ofReal (CU * ((2 : ℝ) ^ (-pesc)) ^ (k + 1))) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => ((2 : ℝ) ^ (-pesc)) ^ (k + 1)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp (tendsto_add_atTop_nat 1)
    have h2 := ENNReal.tendsto_ofReal (h1.const_mul CU)
    rwa [mul_zero, ENNReal.ofReal_zero] at h2
  refine nonpos_iff_eq_zero.1 (ge_of_tendsto' hlim fun k => ?_)
  refine (measure_mono fun g hg => ?_).trans (measure_not_confineGood_le hesc k)
  simp only [not_exists, mem_ofPred_eq] at hg ⊢
  exact hg k

/-- **Tail of the confinement exponent** (blueprint `c:lem-confine`, "tail of `K`"):
`ℙ{K ≥ k} ≤ C_U 2^{-k p_esc}`. -/
theorem measure_le_confinementExp [IsProbabilityMeasure μ] (hCU : 1 ≤ CU)
    (hesc : EscapeBound ρ μ CU pesc) (k : ℕ) :
    μ {g | k ≤ confinementExp ρ g} ≤ ENNReal.ofReal (CU * ((2 : ℝ) ^ (-pesc)) ^ k) := by
  rcases k with _ | k
  · rw [pow_zero, mul_one]
    exact prob_le_one.trans (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hCU)
  · refine (measure_mono fun g hg => ?_).trans (measure_not_confineGood_le hesc k)
    exact not_confineGood_of_lt_confinementExp (Nat.lt_of_succ_le hg)

/-- **Exponential moment of the confinement exponent**: `∫ 2^{(p_esc/2) K} ≤ C_U / (1 - 2^{-p_esc/2})`. -/
theorem lintegral_two_rpow_confinementExp_le [IsProbabilityMeasure μ] (hρ : Measurable ρ)
    (hCU : 1 ≤ CU) (hpesc : 0 < pesc) (hesc : EscapeBound ρ μ CU pesc) :
    ∫⁻ g, ENNReal.ofReal ((2 : ℝ) ^ (pesc / 2 * (confinementExp ρ g : ℝ))) ∂μ ≤
      ENNReal.ofReal (CU / (1 - (2 : ℝ) ^ (-(pesc / 2)))) := by
  set K := confinementExp ρ with hKdef
  have hK : Measurable K := measurable_confinementExp hρ
  set s : ℝ := (2 : ℝ) ^ (-(pesc / 2)) with hs
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hmeasK : ∀ k : ℕ, MeasurableSet {g | k ≤ K g} := fun k =>
    measurableSet_le measurable_const hK
  -- pointwise: `2^{λ K} ≤ ∑_k 1{K ≥ k} 2^{λ k}`
  have hpt : ∀ g, ENNReal.ofReal ((2 : ℝ) ^ (pesc / 2 * (K g : ℝ))) ≤
      ∑' k : ℕ, {g | k ≤ K g}.indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (pesc / 2 * (k : ℝ)))) g := by
    intro g
    refine le_trans (le_of_eq ?_) (ENNReal.le_tsum (K g))
    rw [Set.indicator_of_mem (s := {g' | K g ≤ K g'}) (show g ∈ {g' | K g ≤ K g'} from le_refl (K g))]
  -- the factor `2^{λ k} 2^{-p_esc k} = s^k`
  have hfac : ∀ k : ℕ, (2 : ℝ) ^ (pesc / 2 * (k : ℝ)) * (CU * ((2 : ℝ) ^ (-pesc)) ^ k) =
      CU * s ^ k := by
    intro k
    rw [Real.rpow_mul (by norm_num), Real.rpow_natCast, hs, mul_left_comm, ← mul_pow,
      ← Real.rpow_add (by norm_num)]
    congr 3
    ring
  calc ∫⁻ g, ENNReal.ofReal ((2 : ℝ) ^ (pesc / 2 * (K g : ℝ))) ∂μ
      ≤ ∫⁻ g, ∑' k : ℕ, {g | k ≤ K g}.indicator
          (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (pesc / 2 * (k : ℝ)))) g ∂μ := lintegral_mono hpt
    _ = ∑' k : ℕ, ENNReal.ofReal ((2 : ℝ) ^ (pesc / 2 * (k : ℝ))) * μ {g | k ≤ K g} := by
        rw [lintegral_tsum fun k => (measurable_const.indicator (hmeasK k)).aemeasurable]
        exact tsum_congr fun k => lintegral_indicator_const (hmeasK k) _
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (CU * s ^ k) := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        calc ENNReal.ofReal ((2 : ℝ) ^ (pesc / 2 * (k : ℝ))) * μ {g | k ≤ K g}
            ≤ ENNReal.ofReal ((2 : ℝ) ^ (pesc / 2 * (k : ℝ))) *
                ENNReal.ofReal (CU * ((2 : ℝ) ^ (-pesc)) ^ k) := by
              gcongr
              exact measure_le_confinementExp hCU hesc k
          _ = ENNReal.ofReal (CU * s ^ k) := by
              rw [← ENNReal.ofReal_mul (by positivity), hfac]
    _ = ENNReal.ofReal (CU / (1 - s)) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
          ((summable_geometric_of_lt_one hs0 hs1).mul_left CU), tsum_mul_left,
          tsum_geometric_of_lt_one hs0 hs1, div_eq_mul_inv]

end Tail

/-! ## The summed envelope -/

/-- The summed envelope `W = 1 + ∑_k 2^{-k} (1 + 2^{k+1})^{-A} H_k^{p}` (valued in `[1, ∞]`). -/
def envSum (A p : ℝ) (H : ℕ → DistRd d → ℝ) (g : DistRd d) : ℝ≥0∞ :=
  1 + ∑' k : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ k * (1 + (2 : ℝ) ^ (k + 1)) ^ (-A) * H k g ^ p)

theorem one_le_envSum (A p : ℝ) (H : ℕ → DistRd d → ℝ) (g : DistRd d) : 1 ≤ envSum A p H g :=
  le_self_add

theorem measurable_envSum {A p : ℝ} {H : ℕ → DistRd d → ℝ} (hH : ∀ k, Measurable (H k)) :
    Measurable (envSum A p H) := by
  unfold envSum
  refine measurable_const.add (Measurable.tsum (E := ℝ≥0∞) (L := SummationFilter.unconditional ℕ)
    fun k => ?_)
  exact (measurable_const.mul ((hH k).pow_const p)).ennreal_ofReal

/-- `∫ W ≤ 1 + 2 C_U` when `∫ H_k^p ≤ C_U (1 + 2^{k+1})^A`. -/
theorem lintegral_envSum_le {μ : Measure (DistRd d)} [IsProbabilityMeasure μ] {A p CU : ℝ}
    (hCU : 0 ≤ CU) {H : ℕ → DistRd d → ℝ} (hH : ∀ k, Measurable (H k))
    (hHint : ∀ k : ℕ, ∫⁻ g, ENNReal.ofReal (H k g ^ p) ∂μ ≤
      ENNReal.ofReal (CU * (1 + (2 : ℝ) ^ (k + 1)) ^ A)) :
    ∫⁻ g, envSum A p H g ∂μ ≤ 1 + ENNReal.ofReal (2 * CU) := by
  have hw : ∀ k : ℕ, 0 ≤ (1 / 2 : ℝ) ^ k * (1 + (2 : ℝ) ^ (k + 1)) ^ (-A) := fun k => by positivity
  have hcancel : ∀ k : ℕ, (1 / 2 : ℝ) ^ k * (1 + (2 : ℝ) ^ (k + 1)) ^ (-A) *
      (CU * (1 + (2 : ℝ) ^ (k + 1)) ^ A) = CU * (1 / 2 : ℝ) ^ k := by
    intro k
    have hpos : 0 < 1 + (2 : ℝ) ^ (k + 1) := by positivity
    rw [Real.rpow_neg hpos.le]
    field_simp
  unfold envSum
  have hmk : ∀ k : ℕ, AEMeasurable (fun g => ENNReal.ofReal ((1 / 2 : ℝ) ^ k *
      (1 + (2 : ℝ) ^ (k + 1)) ^ (-A) * H k g ^ p)) μ := fun k =>
    (Measurable.ennreal_ofReal (measurable_const.mul ((hH k).pow_const p))).aemeasurable
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
    lintegral_tsum hmk]
  gcongr
  calc ∑' k : ℕ, ∫⁻ g, ENNReal.ofReal ((1 / 2 : ℝ) ^ k * (1 + (2 : ℝ) ^ (k + 1)) ^ (-A) *
        H k g ^ p) ∂μ
      = ∑' k : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ k * (1 + (2 : ℝ) ^ (k + 1)) ^ (-A)) *
          ∫⁻ g, ENNReal.ofReal (H k g ^ p) ∂μ := by
        refine tsum_congr fun k => ?_
        simp_rw [ENNReal.ofReal_mul (hw k)]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (CU * (1 / 2 : ℝ) ^ k) := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        calc ENNReal.ofReal ((1 / 2 : ℝ) ^ k * (1 + (2 : ℝ) ^ (k + 1)) ^ (-A)) *
              ∫⁻ g, ENNReal.ofReal (H k g ^ p) ∂μ
            ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k * (1 + (2 : ℝ) ^ (k + 1)) ^ (-A)) *
                ENNReal.ofReal (CU * (1 + (2 : ℝ) ^ (k + 1)) ^ A) := by gcongr; exact hHint k
          _ = ENNReal.ofReal (CU * (1 / 2 : ℝ) ^ k) := by
              rw [← ENNReal.ofReal_mul (hw k), hcancel]
    _ = ENNReal.ofReal (2 * CU) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
          (summable_geometric_two.mul_left CU), tsum_mul_left, tsum_geometric_two, mul_comm]

/-- Where `W < ∞`: `H_k^p ≤ 2^k (1 + 2^{k+1})^A W`. -/
theorem rpow_le_of_envSum_lt_top {A p : ℝ} {H : ℕ → DistRd d → ℝ} {g : DistRd d}
    (hW : envSum A p H g < ⊤) (k : ℕ) :
    H k g ^ p ≤ 2 ^ k * (1 + (2 : ℝ) ^ (k + 1)) ^ A * (envSum A p H g).toReal := by
  set w : ℝ := (1 / 2 : ℝ) ^ k * (1 + (2 : ℝ) ^ (k + 1)) ^ (-A) with hwdef
  have hpos : 0 < 1 + (2 : ℝ) ^ (k + 1) := by positivity
  have hw : 0 < w := by positivity
  have hle : ENNReal.ofReal (w * H k g ^ p) ≤ envSum A p H g :=
    (ENNReal.le_tsum (f := fun k => ENNReal.ofReal ((1 / 2 : ℝ) ^ k *
      (1 + (2 : ℝ) ^ (k + 1)) ^ (-A) * H k g ^ p)) k).trans le_add_self
  have hle' : w * H k g ^ p ≤ (envSum A p H g).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hW.ne).1 hle
  have hinv : 2 ^ k * (1 + (2 : ℝ) ^ (k + 1)) ^ A * w = 1 := by
    have h2 : (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k = 1 := by rw [← mul_pow]; norm_num
    have h3 : (1 + (2 : ℝ) ^ (k + 1)) ^ A * (1 + (2 : ℝ) ^ (k + 1)) ^ (-A) = 1 := by
      rw [← Real.rpow_add hpos, add_neg_cancel, Real.rpow_zero]
    calc 2 ^ k * (1 + (2 : ℝ) ^ (k + 1)) ^ A * w
        = ((2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k) *
            ((1 + (2 : ℝ) ^ (k + 1)) ^ A * (1 + (2 : ℝ) ^ (k + 1)) ^ (-A)) := by
          rw [hwdef]; ring
      _ = 1 := by rw [h2, h3, one_mul]
  calc H k g ^ p = (2 ^ k * (1 + (2 : ℝ) ^ (k + 1)) ^ A * w) * H k g ^ p := by rw [hinv, one_mul]
    _ = 2 ^ k * (1 + (2 : ℝ) ^ (k + 1)) ^ A * (w * H k g ^ p) := by ring
    _ ≤ 2 ^ k * (1 + (2 : ℝ) ^ (k + 1)) ^ A * (envSum A p H g).toReal :=
        mul_le_mul_of_nonneg_left hle' (by positivity)


/-! ## Specification of the majorant -/

/-- **Specification of the majorant** (blueprint `c:lem-confine` (a)): almost surely, every constant-speed
`ρ`-geodesic `η` from `0` to `e₁` stays in `B̄_S`, `S = 2^(K+1)`, and `ν_η(B̄_r(z)) ≤ B r^σ` for `0 < r ≤ 1/2`,
`B = 2 H_K H_0`; here `H_k` are envelopes at the radii `2^(k+1)` and `K = confinementExp ρ`. -/
theorem geodMajorant_spec (hd : 1 ≤ d) {ρ : DistRd d → ContMetric d} {μ : Measure (DistRd d)}
    {H : ℕ → DistRd d → ℝ} {σ β : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hH1 : ∀ k g, 1 ≤ H k g)
    (hHae : ∀ k : ℕ, ∀ᵐ g ∂μ, ∀ x ∈ closedBall (0 : Rd d) ((2 : ℝ) ^ (k + 1)),
      ∀ y ∈ closedBall (0 : Rd d) ((2 : ℝ) ^ (k + 1)),
        (H k g)⁻¹ * ‖x - y‖ ^ β ≤ (ρ g).1 (x, y) ∧
          (‖x - y‖ ≤ 1 → (ρ g).1 (x, y) ≤ H k g * ‖x - y‖ ^ σ))
    (hgood : ∀ᵐ g ∂μ, ∃ k, confineGood ρ k g) :
    ∀ᵐ g ∂μ, ∀ η : C(unitInterval, Rd d), IsConstSpeedGeod (ρ g) 0 (e₁ d) η →
      range η ⊆ closedBall (0 : Rd d) ((2 : ℝ) ^ (confinementExp ρ g + 1)) ∧
      ∀ z : Rd d, ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
        (pathMeasure η (closedBall z r)).toReal ≤
          2 * H (confinementExp ρ g) g * H 0 g * r ^ σ := by
  filter_upwards [ae_all_iff.2 hHae, hgood] with g hHg hg η hη
  set K := confinementExp ρ g with hKdef
  have hK : confineGood ρ K g := confineGood_confinementExp hg
  have hS : (1 : ℝ) < 2 ^ (K + 1) := one_lt_pow₀ (by norm_num) (by omega)
  have hrange := range_subset_closedBall_of_dense hd hS hK hη
  refine ⟨hrange, fun z r hr hr2 => ?_⟩
  have he₁ : e₁ d ∈ closedBall (0 : Rd d) ((2 : ℝ) ^ (0 + 1)) := by
    rw [mem_closedBall_zero_iff, HigherDimLFPP.norm_e₁ (by omega)]
    norm_num
  have hlow : (H 0 g)⁻¹ ≤ (ρ g).1 (0, e₁ d) := by
    have h0 := (hHg 0 0 (mem_closedBall_self (by positivity)) (e₁ d) he₁).1
    rwa [zero_sub, norm_neg, HigherDimLFPP.norm_e₁ (by omega), Real.one_rpow, mul_one] at h0
  exact pathMeasure_closedBall_le_of_confined hd (by linarith [hH1 K g]) (by linarith [hH1 0 g])
    hσ hσ1 (fun x hx y hy hxy => (hHg K x hx y hy).2 hxy) hlow hη hrange z hr hr2

/-! ## The exponential moment of the majorant -/

/-- The slope `a₁ = (1 + A) log 2 / (p σ) + log 2` of the majorant in the confinement exponent. -/
def majorantSlope (p σ A : ℝ) : ℝ := (1 + A) * Real.log 2 / (p * σ) + Real.log 2

/-- The exponential rate `c` of the majorant (blueprint `c:lem-confine` (b), `c₁`). -/
def majorantRate (p σ A pesc : ℝ) : ℝ :=
  min (p * σ / 4) (pesc * Real.log 2 / (4 * majorantSlope p σ A))

/-- The offset `a₀ = 1 + (log 2 + 4 A log 2 / p + 1)/σ + 2 log 2`. -/
def majorantOffset (p σ A : ℝ) : ℝ :=
  1 + (Real.log 2 + 4 * A * Real.log 2 / p + 1) / σ + 2 * Real.log 2

/-- The exponential-moment bound `M` of the majorant (blueprint `c:lem-confine` (b), `C₁`). -/
def majorantBound (p σ A pesc CU : ℝ) : ℝ :=
  Real.exp (majorantRate p σ A pesc * majorantOffset p σ A) *
    (CU / (1 - (2 : ℝ) ^ (-(pesc / 2))) + 1 + 2 * CU)

theorem majorantSlope_pos {p σ A : ℝ} (hp : 0 < p) (hσ : 0 < σ) (hA : 0 ≤ A) :
    0 < majorantSlope p σ A := by
  unfold majorantSlope
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  positivity

theorem majorantRate_pos {p σ A pesc : ℝ} (hp : 0 < p) (hσ : 0 < σ) (hA : 0 ≤ A)
    (hpesc : 0 < pesc) : 0 < majorantRate p σ A pesc := by
  unfold majorantRate
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have := majorantSlope_pos hp hσ hA
  exact lt_min (by positivity) (by positivity)

theorem majorantBound_nonneg {p σ A pesc CU : ℝ} (hpesc : 0 < pesc) (hCU : 0 ≤ CU) :
    0 ≤ majorantBound p σ A pesc CU := by
  unfold majorantBound
  have hs1 : (2 : ℝ) ^ (-(pesc / 2)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have : 0 ≤ CU / (1 - (2 : ℝ) ^ (-(pesc / 2))) := div_nonneg hCU (by linarith)
  positivity

/-- `log (1 + 2^(k+1)) ≤ (k + 2) log 2` and `log (2 + 2^(k+1)) ≤ (k + 2) log 2`. -/
theorem n4_log_two_add_pow_le (k : ℕ) {a : ℝ} (ha0 : 0 < a + (2 : ℝ) ^ (k + 1)) (ha : a ≤ 2) :
    Real.log (a + (2 : ℝ) ^ (k + 1)) ≤ ((k : ℝ) + 2) * Real.log 2 := by
  have h1 : a + (2 : ℝ) ^ (k + 1) ≤ 2 ^ (k + 2) := by
    have h2 : (2 : ℝ) ≤ 2 ^ (k + 1) := by
      calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h3 : (2 : ℝ) ^ (k + 2) = 2 ^ (k + 1) * 2 := pow_succ 2 (k + 1)
    linarith
  calc Real.log (a + (2 : ℝ) ^ (k + 1)) ≤ Real.log (2 ^ (k + 2)) := Real.log_le_log ha0 h1
    _ = ((k : ℝ) + 2) * Real.log 2 := by rw [Real.log_pow]; push_cast; ring

/-- The pointwise log bound: `p log H_k ≤ (k + A (k + 2)) log 2 + log W` where `W < ∞`. -/
theorem n4_mul_log_le_of_envSum {A p : ℝ} (hA : 0 ≤ A) {H : ℕ → DistRd d → ℝ}
    (hH1 : ∀ k g, 1 ≤ H k g) {g : DistRd d} (hW : envSum A p H g < ⊤) (k : ℕ) :
    p * Real.log (H k g) ≤
      ((k : ℝ) + A * ((k : ℝ) + 2)) * Real.log 2 + Real.log (envSum A p H g).toReal := by
  have hHpos : 0 < H k g := by linarith [hH1 k g]
  have hWr : 1 ≤ (envSum A p H g).toReal := by
    have := ENNReal.toReal_mono hW.ne (one_le_envSum A p H g)
    rwa [ENNReal.toReal_one] at this
  have hpow : 0 < (1 + (2 : ℝ) ^ (k + 1)) := by positivity
  have h1 := rpow_le_of_envSum_lt_top hW k
  have h2 : Real.log (H k g ^ p) ≤
      Real.log (2 ^ k * (1 + (2 : ℝ) ^ (k + 1)) ^ A * (envSum A p H g).toReal) :=
    Real.log_le_log (Real.rpow_pos_of_pos hHpos p) h1
  rw [Real.log_rpow hHpos, Real.log_mul (by positivity) (by linarith), Real.log_mul (by positivity)
    (by positivity), Real.log_pow, Real.log_rpow hpow] at h2
  have h3 := n4_log_two_add_pow_le k (a := 1) (by positivity) (by norm_num)
  have h4 : A * Real.log (1 + (2 : ℝ) ^ (k + 1)) ≤ A * (((k : ℝ) + 2) * Real.log 2) :=
    mul_le_mul_of_nonneg_left h3 hA
  nlinarith

/-- **The majorant is linear in `(K, log W)`**: where `W < ∞`,
`U ≤ a₀ + a₁ K + (2/(p σ)) log W`. -/
theorem geodMajorant_le_of_envSum {A p σ : ℝ} (hp : 0 < p) (hσ : 0 < σ) (hA : 0 ≤ A)
    {H : ℕ → DistRd d → ℝ} (hH1 : ∀ k g, 1 ≤ H k g) (K : DistRd d → ℕ) {g : DistRd d}
    (hW : envSum A p H g < ⊤) :
    geodMajorant σ H K g ≤ majorantOffset p σ A + majorantSlope p σ A * (K g : ℝ) +
      2 / (p * σ) * Real.log (envSum A p H g).toReal := by
  set LW := Real.log (envSum A p H g).toReal with hLW
  set l2 := Real.log 2 with hl2
  have hl2pos : 0 < l2 := Real.log_pos (by norm_num)
  have hK := n4_mul_log_le_of_envSum hA hH1 hW (K g)
  have h0 := n4_mul_log_le_of_envSum hA hH1 hW 0
  rw [← hLW] at hK h0
  push_cast at h0
  have hHK : 0 < H (K g) g := by linarith [hH1 (K g) g]
  have hH0 : 0 < H 0 g := by linarith [hH1 0 g]
  have hlogB : Real.log (2 * H (K g) g * H 0 g) =
      l2 + Real.log (H (K g) g) + Real.log (H 0 g) := by
    rw [Real.log_mul (by positivity) hH0.ne', Real.log_mul (by norm_num) hHK.ne']
  have hlogS := n4_log_two_add_pow_le (K g) (a := 2) (by positivity) le_rfl
  have hLK : Real.log (H (K g) g) ≤ (((K g : ℝ) + A * ((K g : ℝ) + 2)) * l2 + LW) / p := by
    rw [le_div_iff₀ hp]; linarith
  have hL0 : Real.log (H 0 g) ≤ ((A * 2) * l2 + LW) / p := by
    rw [le_div_iff₀ hp]; linarith
  have hsum : (l2 + Real.log (H (K g) g) + Real.log (H 0 g) + 1) / σ ≤
      (l2 + (((K g : ℝ) + A * ((K g : ℝ) + 2)) * l2 + LW) / p + ((A * 2) * l2 + LW) / p + 1) / σ :=
    div_le_div_of_nonneg_right (by linarith) hσ.le
  unfold geodMajorant
  rw [hlogB]
  have hrhs : (l2 + (((K g : ℝ) + A * ((K g : ℝ) + 2)) * l2 + LW) / p + ((A * 2) * l2 + LW) / p + 1) / σ
      + ((K g : ℝ) + 2) * l2 + 1 =
      majorantOffset p σ A + majorantSlope p σ A * (K g : ℝ) + 2 / (p * σ) * LW := by
    unfold majorantOffset majorantSlope
    rw [← hl2]
    field_simp
    ring
  linarith

/-- **Exponential moment of the majorant** (blueprint `c:lem-confine` (b)): with the (U1) envelopes `H_k` at the
radii `2^(k+1)` and the escape bound (U2),
`∫ e^{c U} ≤ M` for `c = majorantRate p σ A p_esc`, `M = majorantBound p σ A p_esc C_U`. -/
theorem lintegral_exp_geodMajorant_le {μ : Measure (DistRd d)} [IsProbabilityMeasure μ]
    {ρ : DistRd d → ContMetric d} (hρ : Measurable ρ) {H : ℕ → DistRd d → ℝ}
    {p σ A pesc CU : ℝ} (hp : 0 < p) (hσ : 0 < σ) (hA : 0 ≤ A) (hpesc : 0 < pesc) (hCU : 1 ≤ CU)
    (hH : ∀ k, Measurable (H k)) (hH1 : ∀ k g, 1 ≤ H k g)
    (hHint : ∀ k : ℕ, ∫⁻ g, ENNReal.ofReal (H k g ^ p) ∂μ ≤
      ENNReal.ofReal (CU * (1 + (2 : ℝ) ^ (k + 1)) ^ A))
    (hesc : EscapeBound ρ μ CU pesc) :
    ∫⁻ g, ENNReal.ofReal (Real.exp (majorantRate p σ A pesc *
        geodMajorant σ H (confinementExp ρ) g)) ∂μ ≤
      ENNReal.ofReal (majorantBound p σ A pesc CU) := by
  set c := majorantRate p σ A pesc with hc
  set a₁ := majorantSlope p σ A with ha₁
  set a₀ := majorantOffset p σ A with ha₀
  set K := confinementExp ρ with hKdef
  have hKm : Measurable K := measurable_confinementExp hρ
  have hc0 : 0 < c := majorantRate_pos hp hσ hA hpesc
  have ha₁0 : 0 < a₁ := majorantSlope_pos hp hσ hA
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc1 : 2 * c * (2 / (p * σ)) ≤ 1 := by
    have : c ≤ p * σ / 4 := min_le_left _ _
    have hpσ : 0 < p * σ := mul_pos hp hσ
    rw [show 2 * c * (2 / (p * σ)) = 4 * c / (p * σ) by ring, div_le_one hpσ]
    linarith
  have hc2 : 2 * c * a₁ ≤ pesc / 2 * Real.log 2 := by
    have : c ≤ pesc * Real.log 2 / (4 * a₁) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  -- the summed envelope is a.s. finite
  have hWint := lintegral_envSum_le (μ := μ) (by linarith) hH hHint
  have hWfin : ∀ᵐ g ∂μ, envSum A p H g < ⊤ :=
    ae_lt_top (measurable_envSum hH) (ne_top_of_le_ne_top
      (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.ofReal_ne_top⟩) hWint)
  -- pointwise bound
  have hpt : ∀ᵐ g ∂μ, ENNReal.ofReal (Real.exp (c * geodMajorant σ H K g)) ≤
      ENNReal.ofReal (Real.exp (c * a₀)) *
        (ENNReal.ofReal ((2 : ℝ) ^ (pesc / 2 * (K g : ℝ))) + envSum A p H g) := by
    filter_upwards [hWfin] with g hW
    set Wr := (envSum A p H g).toReal with hWr
    have hWr1 : 1 ≤ Wr := by
      have := ENNReal.toReal_mono hW.ne (one_le_envSum A p H g)
      rwa [ENNReal.toReal_one] at this
    have hLW : 0 ≤ Real.log Wr := Real.log_nonneg hWr1
    have hU := geodMajorant_le_of_envSum hp hσ hA hH1 K hW
    rw [← hWr] at hU
    set x := Real.exp (c * a₁ * (K g : ℝ)) with hx
    set y := Real.exp (c * (2 / (p * σ)) * Real.log Wr) with hy
    have hK0 : (0 : ℝ) ≤ K g := Nat.cast_nonneg _
    have hexp : Real.exp (c * geodMajorant σ H K g) ≤ Real.exp (c * a₀) * (x * y) := by
      rw [hx, hy, ← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have := mul_le_mul_of_nonneg_left hU hc0.le
      nlinarith
    have hxpos : 0 < x := Real.exp_pos _
    have hypos : 0 < y := Real.exp_pos _
    have hxy : x * y ≤ x ^ 2 + y ^ 2 := by
      nlinarith [sq_nonneg (x - y)]
    have hx2 : x ^ 2 ≤ (2 : ℝ) ^ (pesc / 2 * (K g : ℝ)) := by
      rw [hx, ← Real.exp_nat_mul, Real.rpow_def_of_pos (by norm_num)]
      refine Real.exp_le_exp.2 ?_
      push_cast
      nlinarith
    have hy2 : y ^ 2 ≤ Wr := by
      rw [hy, ← Real.exp_nat_mul]
      calc Real.exp (((2 : ℕ) : ℝ) * (c * (2 / (p * σ)) * Real.log Wr))
          ≤ Real.exp (Real.log Wr) := by
            refine Real.exp_le_exp.2 ?_
            push_cast
            nlinarith
        _ = Wr := Real.exp_log (by linarith)
    calc ENNReal.ofReal (Real.exp (c * geodMajorant σ H K g))
        ≤ ENNReal.ofReal (Real.exp (c * a₀) * ((2 : ℝ) ^ (pesc / 2 * (K g : ℝ)) + Wr)) := by
          refine ENNReal.ofReal_le_ofReal (hexp.trans ?_)
          exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = ENNReal.ofReal (Real.exp (c * a₀)) *
            (ENNReal.ofReal ((2 : ℝ) ^ (pesc / 2 * (K g : ℝ))) + ENNReal.ofReal Wr) := by
          rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_add (by positivity)
            (by linarith)]
      _ ≤ ENNReal.ofReal (Real.exp (c * a₀)) *
            (ENNReal.ofReal ((2 : ℝ) ^ (pesc / 2 * (K g : ℝ))) + envSum A p H g) := by
          gcongr
          exact ENNReal.ofReal_toReal_le
  have hKint := lintegral_two_rpow_confinementExp_le (μ := μ) hρ hCU hpesc hesc
  have hmeas2 : Measurable fun g => ENNReal.ofReal ((2 : ℝ) ^ (pesc / 2 * (K g : ℝ))) :=
    ((measurable_from_top (f := fun k : ℕ => (2 : ℝ) ^ (pesc / 2 * (k : ℝ)))).comp
      hKm).ennreal_ofReal
  have hs1 : (2 : ℝ) ^ (-(pesc / 2)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hMK : 0 ≤ CU / (1 - (2 : ℝ) ^ (-(pesc / 2))) := div_nonneg (by linarith) (by linarith)
  calc ∫⁻ g, ENNReal.ofReal (Real.exp (c * geodMajorant σ H K g)) ∂μ
      ≤ ∫⁻ g, ENNReal.ofReal (Real.exp (c * a₀)) *
          (ENNReal.ofReal ((2 : ℝ) ^ (pesc / 2 * (K g : ℝ))) + envSum A p H g) ∂μ :=
        lintegral_mono_ae hpt
    _ = ENNReal.ofReal (Real.exp (c * a₀)) *
          (∫⁻ g, ENNReal.ofReal ((2 : ℝ) ^ (pesc / 2 * (K g : ℝ))) ∂μ +
            ∫⁻ g, envSum A p H g ∂μ) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hmeas2]
    _ ≤ ENNReal.ofReal (Real.exp (c * a₀)) *
          (ENNReal.ofReal (CU / (1 - (2 : ℝ) ^ (-(pesc / 2)))) + (1 + ENNReal.ofReal (2 * CU))) := by
        gcongr
    _ = ENNReal.ofReal (majorantBound p σ A pesc CU) := by
        unfold majorantBound
        rw [← hc, ← ha₀, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by linarith),
          ← ENNReal.ofReal_add hMK (by linarith), ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        congr 2
        ring


/-! ## Tail and moments -/

/-- **Exponential tail of the majorant** (blueprint `c:lem-confine` (b)): `ℙ{U > u} ≤ M e^{-c u}`. -/
theorem tail_geodMajorant {μ : Measure (DistRd d)} [IsProbabilityMeasure μ]
    {ρ : DistRd d → ContMetric d} (hρ : Measurable ρ) {H : ℕ → DistRd d → ℝ}
    {p σ A pesc CU : ℝ} (hp : 0 < p) (hσ : 0 < σ) (hA : 0 ≤ A) (hpesc : 0 < pesc) (hCU : 1 ≤ CU)
    (hH : ∀ k, Measurable (H k)) (hH1 : ∀ k g, 1 ≤ H k g)
    (hHint : ∀ k : ℕ, ∫⁻ g, ENNReal.ofReal (H k g ^ p) ∂μ ≤
      ENNReal.ofReal (CU * (1 + (2 : ℝ) ^ (k + 1)) ^ A))
    (hesc : EscapeBound ρ μ CU pesc) (u : ℝ) :
    μ {g | u < geodMajorant σ H (confinementExp ρ) g} ≤
      ENNReal.ofReal (majorantBound p σ A pesc CU * Real.exp (-(majorantRate p σ A pesc * u))) :=
  n4_measure_lt_le (measurable_geodMajorant hH (measurable_confinementExp hρ))
    (majorantRate_pos hp hσ hA hpesc)
    (lintegral_exp_geodMajorant_le hρ hp hσ hA hpesc hCU hH hH1 hHint hesc) u

/-- **Moments of the majorant** (blueprint `c:lem-confine` (b)): `∫ U^q ≤ (q/c)^q M` for `q > 0`. -/
theorem lintegral_geodMajorant_rpow_le {μ : Measure (DistRd d)} [IsProbabilityMeasure μ]
    {ρ : DistRd d → ContMetric d} (hρ : Measurable ρ) {H : ℕ → DistRd d → ℝ}
    {p σ A pesc CU : ℝ} (hp : 0 < p) (hσ : 0 < σ) (hA : 0 ≤ A) (hpesc : 0 < pesc) (hCU : 1 ≤ CU)
    (hH : ∀ k, Measurable (H k)) (hH1 : ∀ k g, 1 ≤ H k g)
    (hHint : ∀ k : ℕ, ∫⁻ g, ENNReal.ofReal (H k g ^ p) ∂μ ≤
      ENNReal.ofReal (CU * (1 + (2 : ℝ) ^ (k + 1)) ^ A))
    (hesc : EscapeBound ρ μ CU pesc) {q : ℝ} (hq : 0 < q) :
    ∫⁻ g, ENNReal.ofReal (geodMajorant σ H (confinementExp ρ) g ^ q) ∂μ ≤
      ENNReal.ofReal ((q / majorantRate p σ A pesc) ^ q * majorantBound p σ A pesc CU) :=
  n4_lintegral_rpow_le (fun g => (zero_le_one.trans (one_le_geodMajorant hσ hH1 _ g)))
    (majorantRate_pos hp hσ hA hpesc)
    (lintegral_exp_geodMajorant_le hρ hp hσ hA hpesc hCU hH hH1 hHint hesc) hq

/-- **The unit distance is controlled by the envelope** (blueprint `c:lem-confine` (c)): if
`H⁻¹ |0 - e₁|^β ≤ G(0, e₁) ≤ H |0 - e₁|^σ` (the (U1) bounds at `R = 1`), then `|log G(0, e₁)| ≤ log H`. -/
theorem abs_logRho_le_logEnvelope (hd : 1 ≤ d) {G : ContMetric d} {H σ β : ℝ} (hH : 1 ≤ H)
    (hlow : H⁻¹ * ‖(0 : Rd d) - e₁ d‖ ^ β ≤ G.1 (0, e₁ d))
    (hup : ‖(0 : Rd d) - e₁ d‖ ≤ 1 → G.1 (0, e₁ d) ≤ H * ‖(0 : Rd d) - e₁ d‖ ^ σ) :
    |Real.log (G.1 (0, e₁ d))| ≤ Real.log H := by
  have hn : ‖(0 : Rd d) - e₁ d‖ = 1 := by
    rw [zero_sub, norm_neg, HigherDimLFPP.norm_e₁ (by omega)]
  rw [hn, Real.one_rpow, mul_one] at hlow hup
  have hup' := hup le_rfl
  have hH0 : 0 < H := by linarith
  have hL : 0 < G.1 (0, e₁ d) := lt_of_lt_of_le (inv_pos.2 hH0) hlow
  rw [abs_le]
  constructor
  · have h1 : Real.log H⁻¹ ≤ Real.log (G.1 (0, e₁ d)) := Real.log_le_log (inv_pos.2 hH0) hlow
    rw [Real.log_inv] at h1
    linarith
  · exact Real.log_le_log hL hup'

/-- **Moments of `log H`** (blueprint `c:lem-confine` (c)): for an envelope `H ≥ 1` with `∫ H^p ≤ K`,
`∫ (log H)^q ≤ (q/p)^q K` for every `q > 0`. -/
theorem lintegral_log_rpow_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {H : α → ℝ}
    (hH : ∀ g, 1 ≤ H g) {p K : ℝ} (hp : 0 < p)
    (hK : ∫⁻ g, ENNReal.ofReal (H g ^ p) ∂μ ≤ ENNReal.ofReal K) {q : ℝ} (hq : 0 < q) :
    ∫⁻ g, ENNReal.ofReal (Real.log (H g) ^ q) ∂μ ≤ ENNReal.ofReal ((q / p) ^ q * K) := by
  refine n4_lintegral_rpow_le (fun g => Real.log_nonneg (hH g)) hp ?_ hq
  have hpt : ∀ g, Real.exp (p * Real.log (H g)) = H g ^ p := fun g => by
    rw [Real.rpow_def_of_pos (by linarith [hH g]), mul_comm]
  simp_rw [hpt]
  exact hK

/-! ## Packaging with Lemma 2.1's core -/

/-- **The majorant for strong metrics** (blueprint `c:lem-confine`, all clauses, packaged from `lemma21_core`):
there are `0 < σ < 1`, `c > 0` and `M ≥ 0` (depending only on `d`, `ξ̄`) such that for every `ξ ∈ (0, ξ̄]` and
every `D` strong at `ξ` there is a measurable `U ≥ 1` with `∫ e^{c U} dℙ ≤ M` and, a.s., numbers `S, B ≥ 1` with
`U = 1 + (log B + 1)/σ + log(2 + S)` such that every constant-speed `rho D`-geodesic `η` from `0` to `e₁` lies in
`B̄_S` and satisfies `ν_η(B̄_r(z)) ≤ B r^σ` (`0 < r ≤ 1/2`). -/
theorem exists_geodMajorant {d : ℕ} (hd : 3 ≤ d) {ξbar : ℝ} (hU : UniformEstimates d ξbar 1) :
    ∃ σ c M : ℝ, 0 < σ ∧ σ < 1 ∧ 0 < c ∧ 0 ≤ M ∧
    ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ∀ D : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) D →
      ∃ U : DistRd d → ℝ, Measurable U ∧ (∀ g, 1 ≤ U g) ∧
        ∫⁻ g, ENNReal.ofReal (Real.exp (c * U g)) ∂(normLGFLaw d) ≤ ENNReal.ofReal M ∧
        ∀ᵐ g ∂(normLGFLaw d), ∃ S B : ℝ, 1 ≤ S ∧ 1 ≤ B ∧
          U g = 1 + (Real.log B + 1) / σ + Real.log (2 + S) ∧
          ∀ η : C(unitInterval, Rd d), IsConstSpeedGeod (rho D g) 0 (e₁ d) η →
            range η ⊆ closedBall (0 : Rd d) S ∧
            ∀ z : Rd d, ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
              (pathMeasure η (closedBall z r)).toReal ≤ B * r ^ σ := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨p, σ, β, CU, A, pesc, hp, hσ, hσ1, _hβ, hCU, hA, hpesc, hcore⟩ := lemma21_core hd hU
  refine ⟨σ, majorantRate p σ A pesc, majorantBound p σ A pesc CU, hσ, hσ1,
    majorantRate_pos hp hσ hA hpesc, majorantBound_nonneg hpesc (by linarith),
    fun ξ hξ D hD => ?_⟩
  have : IsProbabilityMeasure (normLGFLaw d) := (normLGFLaw_spec_holds d (by omega)).1
  obtain ⟨_, hU1, hU2, _⟩ := hcore ξ hξ D hD
  have hρ : Measurable (rho D) := measurable_rho hD.measurable
  have hR : ∀ k : ℕ, (1 : ℝ) ≤ 2 ^ (k + 1) := fun k => one_le_pow₀ (by norm_num)
  choose H hHm hH1 hHint hHae using fun k : ℕ => hU1 ((2 : ℝ) ^ (k + 1)) (hR k)
  have hesc : EscapeBound (rho D) (normLGFLaw d) CU pesc := hU2
  refine ⟨geodMajorant σ H (confinementExp (rho D)),
    measurable_geodMajorant hHm (measurable_confinementExp hρ),
    one_le_geodMajorant hσ hH1 _,
    lintegral_exp_geodMajorant_le hρ hp hσ hA hpesc hCU hHm hH1 hHint hesc, ?_⟩
  filter_upwards [geodMajorant_spec hd1 hσ hσ1.le hH1 hHae (ae_exists_confineGood hpesc hesc)]
    with g hg
  set K := confinementExp (rho D) g with hKdef
  refine ⟨(2 : ℝ) ^ (K + 1), 2 * H K g * H 0 g, one_le_pow₀ (by norm_num),
    by nlinarith [hH1 K g, hH1 0 g], rfl, fun η hη => ⟨(hg η hη).1, fun z r hr hr2 => ?_⟩⟩
  exact (hg η hη).2 z r hr hr2

end HigherDimLQGContinuity
