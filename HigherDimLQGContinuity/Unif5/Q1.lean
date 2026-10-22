import HigherDimLQGContinuity.Unif4.AcrossLower
import HigherDimLQGMetric.DGZ.BadBoxQ1

/-!
# Uniform DGZ Lemma 5.5 and the uniform coarse-graining parameters (packet U2)

Blueprint Part D, `d:conv-coarse` and `d:lem-u55` (NA3 §2.5, §2.15 rows 9–13; [8]-bp `r2:conv:coarse`,
`r2:lem:55`). Port of `HigherDimLQGMetric.DGZ.acrossTail_uniform`, `DGZ.q1_le`, `DGZ.q1_tendsto`
(`DGZ/BadBoxQ1.lean`, MA7 D-5.5).

* The **λ-generic constant lemmas** (`d:conv-coarse`): the uniform `λ = uLambda d b μ = α/(4(α + d))` of the constant
  package (A.7) (`UnifBase/Consts.lean`) satisfies `0 < λ ≤ 1/4` (`uLambda_le_quarter`; the hypotheses of the
  sequence lemmas of `DGZ/NiceBoxConst.lean`, which take `λ` free), `(d + α)(1 - 2λ) = d + α/2`
  (`u2_add_mul_one_sub_two_mul_lambda`, Lemma 5.9), and `λ = dgzLambda d (√(2(d + 2α)))`
  (`u2_dgzLambda_sqrt_eq`), which lets the `ξ`-free fixed-`Q` lemma `DGZ.prob_J2'_compl_le` serve the uniform `λ`.
* `uNiceParams d b μ ξ θ ε L K R n k`: DGZ's parameters at `(ξ, Q(ξ))` with the uniform exponent sequence
  `a = dgzSeq λ K`, `λ = uLambda d b μ` (the planned `uNiceParams` of `d:conv-coarse`; `θ`, `R` stay free as in
  `DGZ.dgzParams`).
* `acrossTail_unif` (**target**): for `ε, η > 0` there is `L₀ > 1` (depending only on `d, κ, b, μ, ε, η`) with
  `P*[D_k(across B₂(0) \ B₁(0)) ≤ L⁻¹ 2^{-(1-ξQ(ξ)+ε)k}] ≤ η` for every `ξ` with `UHyp d κ b μ ξ`, every dyadic
  realization, every `L ≥ L₀` and every `k ≥ 1`.
* `q1_le_unif` (uniform form of Lemma 5.5): for every `A` and `η > 0` there is `L₀` with `q₁ ≤ η` whenever
  `a₀ = 0`, `a₁ ≤ A`, `L ≥ L₀`, for all `ξ ∈ S(b, μ)`, all `n, k`, boxes and dyadic realizations.
* `q1_tendsto_unif` (**target**, `d:lem-u55`): `lim_{L→∞} sup {q₁ : ξ ∈ S(b, μ), n, k, u} = 0` for the uniform
  parameters, in every dyadic realization (the realization-uniform form is `q1_le_unif`).

**Proof** (`d:lem-u55`: [8]-bp `r2:lem:55` with two changes). For `k ≥ k₁` the uniform Prop 4.8
(`acrossLower_unif`, `δ = ε`) replaces the fixed-`ξ` Prop 4.8. For `1 ≤ k < k₁`, `D_k(across) ≥ e^{-ξ sup_{B̄₂}|h_k|}`
(`DGZ.exp_mul_le_acrossDist`) and the Gaussian supremum tail (`DGZ.exists_sup_cbox_gaussian_tail`): on
`{sup |h_k| ≤ M}`, `ξ sup |h_k| ≤ b M` (as `ξ ≤ b`), and `2^{-(1-ξQ+ε)k} ≤ 2^{√(2d) b k₁}` (as
`ξ Q(ξ) ≤ 1 + √(2d) b`, `u1_phi_bounds`), so `L₀ = max(2, e^{bM} 2^{√(2d) b k₁} + 1)` is uniform in `ξ`.
Condition (1′) is `ξ`-free (`DGZ.prob_not_niceOscOne_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLQGMetric.DGZ
open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt latPt_apply cbox obox)

variable {d : ℕ}

/-! ## The λ-generic constant lemmas -/

/-- `λ = α/(4(α + d)) ≤ 1/4` for `α > 0` (the hypothesis `λ ≤ 1/4` of DGZ's sequence lemmas). -/
theorem u2_lambda_le_quarter {α : ℝ} (hα : 0 < α) : α / (4 * (α + d)) ≤ 1 / 4 := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- `(d + α)(1 - 2λ) = d + α/2` for `λ = α/(4(α + d))`, `α > 0` (the arithmetic of DGZ Lemma 5.9). -/
theorem u2_add_mul_one_sub_two_mul_lambda {α : ℝ} (hα : 0 < α) :
    ((d : ℝ) + α) * (1 - 2 * (α / (4 * (α + d)))) = d + α / 2 := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hne : (α + d : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- `dgzAlpha d √(2(d + 2α)) = α` for `α ≥ 0`. -/
theorem u2_dgzAlpha_sqrt_eq {α : ℝ} (hα : 0 ≤ α) : dgzAlpha d √(2 * (d + 2 * α)) = α := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  unfold dgzAlpha
  rw [Real.sq_sqrt (by positivity)]
  ring

/-- `λ = α/(4(α + d)) = dgzLambda d √(2(d + 2α))` for `α ≥ 0`: the uniform `λ` is DGZ's `λ` at the exponent
`√(2(d + 2α))`. -/
theorem u2_dgzLambda_sqrt_eq {α : ℝ} (hα : 0 ≤ α) :
    dgzLambda d √(2 * (d + 2 * α)) = α / (4 * (α + d)) := by
  unfold dgzLambda
  rw [u2_dgzAlpha_sqrt_eq hα]

/-- `√(2d) < √(2(d + 2α))` for `α > 0`. -/
theorem u2_sqrt_lt_sqrt {α : ℝ} (hα : 0 < α) : √(2 * d) < √(2 * (d + 2 * α)) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  exact Real.sqrt_lt_sqrt (by positivity) (by linarith)

/-- **`0 < λ ≤ 1/4` for the uniform `λ`** (`d:conv-coarse`). -/
theorem uLambda_le_quarter {b μ : ℝ} (hb : 0 < b) (hμ : 0 < μ) : uLambda d b μ ≤ 1 / 4 :=
  u2_lambda_le_quarter (uAlpha_pos hb hμ)

/-! ## The uniform parameters -/

/-- **The parameters of DGZ §5 with the uniform exponent sequence** (blueprint `d:conv-coarse`): `ξ`, `Q = Q(ξ)`, the
margins `θ`, `ε`, the constants `L, K, R`, the scales `n, k`, and `a = dgzSeq λ K` with the uniform
`λ = uLambda d b μ` of the constant package (A.7). -/
def uNiceParams (d : ℕ) (b μ ξ θ ε L : ℝ) (K R n k : ℕ) : NiceParams :=
  ⟨ξ, distExp d ξ, θ, ε, L, K, R, n, k, dgzSeq (uLambda d b μ) K⟩

/-! ## The uniform lower tail of `D_k(across B₂(0) \ B₁(0))` -/

/-- **Uniform DGZ Lemma 5.5, the across tail** (`d:lem-u55`; port of `DGZ.acrossTail_uniform`): for `d ≥ 2`, `κ`
admissible and `b, μ, ε, η > 0` there is `L₀ > 1` (depending only on `d, κ, b, μ, ε, η`) such that
`P*[D_k(across B₂(0) \ B₁(0)) ≤ L⁻¹ 2^{-(1-ξQ(ξ)+ε)k}] ≤ η` for every `ξ` with `UHyp d κ b μ ξ`, every dyadic
realization, every `L ≥ L₀` and every `k ≥ 1`. -/
theorem acrossTail_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ : ℝ} (hb : 0 < b)
    (hμ : 0 < μ) {ε : ℝ} (hε : 0 < ε) {η : ℝ} (hη : 0 < η) :
    ∃ L₀ : ℝ, 1 < L₀ ∧ ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
        (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ L : ℝ, L₀ ≤ L → ∀ k : ℕ, 1 ≤ k →
          P {ω | acrossDist ξ (fun z => H k z ω) 0 2 1 ≤
            L⁻¹ * (2 : ℝ) ^ (-(1 - ξ * distExp d ξ + ε) * k)} ≤ ENNReal.ofReal η := by
  have hd0 : 0 < d := by omega
  obtain ⟨hL2, -⟩ := log_two_pos_lt_one
  -- large `k`: the uniform Prop 4.8 (lower half) with `δ = ε`
  obtain ⟨C₁, hC₁, hlow⟩ := acrossLower_unif hd hκ hb hμ hε
  obtain ⟨k₁, hk₁⟩ := exists_mul_exp_neg_div_le hC₁ hη
  -- small `k`: the supremum of `|h_k|` on `B̄₂(0)`
  obtain ⟨C₂, hC₂, hsup⟩ := exists_sup_cbox_gaussian_tail.{0} hκ (R := 2) (by norm_num)
  set V : ℝ := k₁ * Real.log 2 with hV
  have hV0 : 0 ≤ V := by positivity
  set u : ℝ := √(2 * V * |Real.log (2 / η)|) with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  set M : ℝ := √(2 * d) * V + C₂ * √V + C₂ + u with hM
  have hM0 : 0 ≤ M := by positivity
  set c : ℝ := √(2 * d) * b with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨max 2 (Real.exp (b * M) * (2 : ℝ) ^ (c * k₁) + 1), lt_of_lt_of_le one_lt_two
    (le_max_left _ _), fun ξ hξh Ω _ P W H hH L hL k hk => ?_⟩
  have hξ : 0 < ξ := hξh.base.xi_pos
  have hξb : ξ ≤ b := hξh.le_b
  have hphi := (u1_phi_bounds hd hξ hξb).2
  set Q : ℝ := distExp d ξ with hQ
  have hL1 : 1 < L := lt_of_lt_of_le one_lt_two ((le_max_left _ _).trans hL)
  have hL0 : 0 < L := by linarith
  have hW := hH.whiteNoise
  have := hW.isProbabilityMeasure
  rcases le_or_gt k₁ k with hkk | hkk
  · -- `k ≥ k₁`: the event is contained in `{D_k < 2^{-(1-ξQ+ε)k}}`
    refine (measure_mono fun ω hω => ?_).trans ((hlow ξ hξh Ω P W H hH k).trans
      (ENNReal.ofReal_le_ofReal (hk₁ k hkk)))
    simp only [mem_ofPred_eq] at hω ⊢
    refine lt_of_le_of_lt hω ?_
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) := Real.rpow_pos_of_pos two_pos _
    calc L⁻¹ * (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) < 1 * (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) :=
          mul_lt_mul_of_pos_right (inv_lt_one_of_one_lt₀ hL1) hpos
      _ = (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) := one_mul _
  · -- `1 ≤ k < k₁`: the field bound
    have hX := hH.band k
    have hlogk := log_one_div_inv_two_pow k
    set v : ℝ := Real.log (1 / (2 : ℝ)⁻¹ ^ k) with hv
    have hv0 : 0 < v := by
      rw [hlogk]
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      positivity
    have hvV : v ≤ V := by
      rw [hlogk, hV]
      have : (k : ℝ) ≤ k₁ := by exact_mod_cast hkk.le
      exact mul_le_mul_of_nonneg_right this hL2.le
    have hb' := hsup hW (a := (2 : ℝ)⁻¹ ^ k) (b := 1) (by positivity)
      (pow_le_one₀ (by norm_num) (by norm_num)) hX 0 hu0
    rw [mul_one, ← hv] at hb'
    -- the threshold of the field event is at most `M`
    have hMk : √(2 * d) * v + C₂ * √v + C₂ + u ≤ M := by
      have h1 : √v ≤ √V := Real.sqrt_le_sqrt hvV
      have h2 : √(2 * d) * v ≤ √(2 * d) * V := mul_le_mul_of_nonneg_left hvV (Real.sqrt_nonneg _)
      have h3 : C₂ * √v ≤ C₂ * √V := mul_le_mul_of_nonneg_left h1 hC₂
      linarith
    refine (measure_mono fun ω hω => ?_).trans (hb'.trans (ENNReal.ofReal_le_ofReal ?_))
    · -- if `|h_k| ≤ M_k` on `B̄₂(0)` the across distance exceeds the threshold
      simp only [mem_ofPred_eq] at hω ⊢
      by_contra hcon
      push Not at hcon
      have hlow' := exp_mul_le_acrossDist (ξ := ξ) (c := (0 : Rd d)) hd0 ((hX.continuous ω))
        (zero_le_one) (one_lt_two) (m := -(ξ * (√(2 * d) * v + C₂ * √v + C₂ + u)))
        (fun z hz => by
          have h0 := hcon z hz.1
          have h1 := neg_abs_le (H k z ω)
          have h2 := mul_le_mul_of_nonneg_left h0 hξ.le
          have h3 := mul_le_mul_of_nonneg_left h1 hξ.le
          linarith)
      -- `ξ ≤ b` multiplies the threshold through
      have hexpM : Real.exp (-(b * M)) ≤
          Real.exp (-(ξ * (√(2 * d) * v + C₂ * √v + C₂ + u))) := by
        rw [Real.exp_le_exp, neg_le_neg_iff]
        calc ξ * (√(2 * d) * v + C₂ * √v + C₂ + u) ≤ ξ * M :=
              mul_le_mul_of_nonneg_left hMk hξ.le
          _ ≤ b * M := mul_le_mul_of_nonneg_right hξb hM0
      have hthr : L⁻¹ * (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) < Real.exp (-(b * M)) := by
        have hck : (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) ≤ (2 : ℝ) ^ (c * k₁) := by
          refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
          have h1 : -(1 - ξ * Q + ε) ≤ c := by rw [hc]; linarith
          have h2 : (k : ℝ) ≤ k₁ := by exact_mod_cast hkk.le
          have h3 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          calc -(1 - ξ * Q + ε) * k ≤ c * k := mul_le_mul_of_nonneg_right h1 h3
            _ ≤ c * k₁ := mul_le_mul_of_nonneg_left h2 hc0
        have hLM : Real.exp (b * M) * (2 : ℝ) ^ (c * k₁) < L :=
          lt_of_lt_of_le (lt_add_one _) ((le_max_right _ _).trans hL)
        rw [inv_mul_lt_iff₀ hL0, Real.exp_neg, ← div_eq_mul_inv, lt_div_iff₀ (Real.exp_pos _)]
        calc (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) * Real.exp (b * M)
            ≤ (2 : ℝ) ^ (c * k₁) * Real.exp (b * M) :=
              mul_le_mul_of_nonneg_right hck (Real.exp_pos _).le
          _ < L := by rw [mul_comm]; exact hLM
      have : Real.exp (-(b * M)) ≤ acrossDist ξ (fun z => H k z ω) 0 2 1 := by
        calc Real.exp (-(b * M)) ≤ Real.exp (-(ξ * (√(2 * d) * v + C₂ * √v + C₂ + u))) := hexpM
          _ = Real.exp (-(ξ * (√(2 * d) * v + C₂ * √v + C₂ + u))) * (2 - 1) := by ring
          _ ≤ _ := hlow'
      linarith
    · -- the Gaussian tail is at most `η`
      have hlog : Real.log (2 / η) ≤ u ^ 2 / (2 * v) := by
        rw [le_div_iff₀ (by positivity), hu, Real.sq_sqrt (by positivity)]
        have h1 := le_abs_self (Real.log (2 / η))
        have h2 : 0 ≤ |Real.log (2 / η)| := abs_nonneg _
        nlinarith
      calc 2 * Real.exp (-u ^ 2 / (2 * v)) ≤ 2 * Real.exp (-Real.log (2 / η)) := by
            gcongr
            rw [neg_div]
            linarith
        _ = η := by
            rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
            field_simp

/-! ## Lemma 5.5 -/

/-- **Uniform DGZ Lemma 5.5** (`d:lem-u55`; port of `DGZ.q1_le`): for `d ≥ 2`, `κ` admissible, `b, μ, ε, η > 0` and
every `A : ℕ` there is `L₀` (depending only on `d, κ, b, μ, ε, A, η`) such that for every `ξ` with `UHyp d κ b μ ξ`,
every dyadic realization and all parameters with `p.ξ = ξ`, `p.Q = Q(ξ)`, `p.ε = ε`, `a₀ = 0`, `a₁ ≤ A` and
`L ≥ L₀`, every `a₁`-box is bad with probability at most `η` (all `n`, `k`, all boxes). -/
theorem q1_le_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ : ℝ} (hb : 0 < b)
    (hμ : 0 < μ) {ε : ℝ} (hε : 0 < ε) (A : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ L₀ : ℝ, ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
        (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H →
        ∀ p : NiceParams, p.ξ = ξ → p.Q = distExp d ξ → p.ε = ε → p.a 0 = 0 → p.a 1 ≤ A →
          L₀ ≤ p.L → ∀ u : Zd d,
            P {ω | ¬ NiceBox p (fun q z => H q z ω) 1 u} ≤ ENNReal.ofReal η := by
  have hd0 : 0 < d := by omega
  set B : ℝ := ((2 : ℝ) * 2 ^ A) ^ d with hB
  have hB0 : 0 < B := by positivity
  -- (1′)
  obtain ⟨C₀, hC₀, hone⟩ := prob_not_niceOscOne_le (d := d) hκ
  obtain ⟨x₀, hx₀⟩ := BadBox.exists_mul_two_exp_neg_sq_le hC₀ hB0.le (half_pos hη)
  -- (3)
  obtain ⟨L₁, hL₁, hacr⟩ := acrossTail_unif hd hκ hb hμ hε (η := η / 2 / B) (by positivity)
  refine ⟨max (max L₁ (3 * x₀)) (3 * C₀),
    fun ξ hξh Ω _ P W H hH p hpξ hpQ hpε ha0 ha1 hL u => ?_⟩
  have hL₁' : L₁ ≤ p.L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hx₀' : x₀ ≤ p.L / 3 := by
    have := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
    linarith
  have hC₀' : C₀ ≤ p.L / 3 := by
    have := (le_max_right _ _).trans hL
    linarith
  have hL1 : 1 < p.L := lt_of_lt_of_le hL₁ hL₁'
  have hc : ∀ q ω, Continuous fun z => H q z ω := fun q => (hH.band q).continuous
  have hsplit : {ω | ¬ NiceBox p (fun q z => H q z ω) 1 u} ⊆
      {ω | ¬ NiceOscOne p (fun q z => H q z ω) u} ∪
        {ω | ¬ NiceAcrossOne p (fun q z => H q z ω) u} := by
    intro ω hω
    simp only [mem_ofPred_eq, niceBox_one_iff, not_and_or] at hω
    exact hω
  refine (measure_mono hsplit).trans ((measure_union_le _ _).trans ?_)
  have hB1 : ((2 : ℝ) * 2 ^ p.a 1) ^ d ≤ B := by
    rw [hB]
    gcongr
    · exact one_le_two
  -- (1′)
  have h1 : P {ω | ¬ NiceOscOne p (fun q z => H q z ω) u} ≤ ENNReal.ofReal (η / 2) := by
    refine (hone Ω P W H hH p ha0 hC₀' u).trans (ENNReal.ofReal_le_ofReal ?_)
    calc ((2 : ℝ) * 2 ^ p.a 1) ^ d * (2 * Real.exp (-(p.L / 3 - C₀) ^ 2 / C₀))
        ≤ B * (2 * Real.exp (-(p.L / 3 - C₀) ^ 2 / C₀)) := by gcongr
      _ ≤ η / 2 := hx₀ _ hx₀'
  -- (3)
  have h3 : P {ω | ¬ NiceAcrossOne p (fun q z => H q z ω) u} ≤ ENNReal.ofReal (η / 2) := by
    rcases Nat.eq_zero_or_pos p.k with hk | hk
    · have hempty : {ω | ¬ NiceAcrossOne p (fun q z => H q z ω) u} = ∅ := by
        ext ω
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_not]
        exact niceAcrossOne_of_k_eq_zero hd0 p ha0 hk hL1 _ (fun q => hc q ω) u
      rw [hempty, measure_empty]
      exact zero_le
    · refine (prob_not_niceAcrossOne_le hκ hH p ha0 u).trans ?_
      have ht := hacr ξ hξh Ω P W H hH p.L hL₁' p.k hk
      rw [hpξ, hpQ, hpε]
      calc ENNReal.ofReal (((2 : ℝ) * 2 ^ p.a 1) ^ d) *
            P {ω | acrossDist ξ (fun z => H p.k z ω) 0 2 1 ≤
              p.L⁻¹ * (2 : ℝ) ^ (-(1 - ξ * distExp d ξ + ε) * p.k)}
          ≤ ENNReal.ofReal B * ENNReal.ofReal (η / 2 / B) := by
            gcongr
        _ = ENNReal.ofReal (η / 2) := by
            rw [← ENNReal.ofReal_mul hB0.le]
            congr 1
            field_simp
  calc _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := add_le_add h1 h3
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf

/-- **Uniform DGZ Lemma 5.5, limit form** (target `q1_tendsto_unif`; `d:lem-u55`; port of `DGZ.q1_tendsto`): for the
uniform parameters with a fixed `K` (any `θ`, `R`) and every dyadic realization,
`lim_{L→∞} sup {q₁ : ξ ∈ S(b, μ), n, k, u} = 0`, where `q₁ = P[B_{s₁}(s₁ u) is bad]` (the supremum over `ξ` runs over
`UHyp d κ b μ ξ`, which is `ξ ∈ S(b, μ)` by `uHyp_iff`). The rate is also uniform over realizations: `q1_le_unif`. -/
theorem q1_tendsto_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ : ℝ} (hb : 0 < b)
    (hμ : 0 < μ) {ε : ℝ} (hε : 0 < ε) (θ : ℝ) (K R : ℕ) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) :
    Tendsto (fun L : ℝ => ⨆ (ξ : ℝ) (_ : UHyp d κ b μ ξ) (n : ℕ) (k : ℕ) (u : Zd d),
      P {ω | ¬ NiceBox (uNiceParams d b μ ξ θ ε L K R n k) (fun q z => H q z ω) 1 u}) atTop
      (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  rcases eq_or_ne η ⊤ with rfl | hηtop
  · exact Eventually.of_forall fun _ => le_top
  · have hη' : 0 < η.toReal := ENNReal.toReal_pos hη.ne' hηtop
    obtain ⟨L₀, hL₀⟩ := q1_le_unif hd hκ hb hμ hε (K ^ 4) hη'
    filter_upwards [eventually_ge_atTop L₀] with L hL
    refine iSup_le fun ξ => iSup_le fun hξh => iSup_le fun n => iSup_le fun k =>
      iSup_le fun u => ?_
    refine (hL₀ ξ hξh Ω P W H hH _ rfl rfl rfl rfl le_rfl hL u).trans ?_
    rw [ENNReal.ofReal_toReal hηtop]

end HigherDimLQGContinuity
