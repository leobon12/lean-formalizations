import GaussianLQG.Energy.Basic

/-!
# The coupling estimate (blueprint Lemma `lem:coupling`; source (4.7) and proof of Lemma 5.2)

Let `ν, ν'` be regular probability measures with `ν(B_r(u)) ≤ B r^α`, `ν'(B_r(u)) ≤ B' r^α`
for `r ∈ (0, 1]`, and let `P` be a coupling of `ν` and `ν'` with `P{|x - y| > η} = 0`. Then for
every `ρ ∈ (0, 1]`,
`ℰ(ν,ν) - 2ℰ(ν,ν') + ℰ(ν',ν') ≤ 2η/ρ + (B + B') ρ^α / α` (`energy_sub_le_of_coupling`).

Proof (blueprint): by `energy_sub_eq_logEnergy` the left side is
`L(ν,ν) - L(ν,ν') - L(ν',ν) + L(ν',ν')`. Split `-log|x-y| = k_ρ + d_ρ` with the truncated kernel
`k_ρ(x,y) = -log max(|x-y|, ρ)` (`kTrunc`, `1/ρ`-Lipschitz in each variable) and
`d_ρ(x,y) = log⁺(ρ/|x-y|) ≥ 0` (`dTrunc`). The `k_ρ` part is an expectation over two independent
copies of the coupling, bounded by `2η/ρ` (`kTrunc_four_term_le`); the `d_ρ` cross terms are
nonpositive and the diagonal terms are bounded by the layer-cake formula.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal Real

namespace GaussianLQG

/-! ## The truncated kernel and the singular remainder -/

/-- The truncated kernel `k_ρ(x,y) = -log max(|x-y|, ρ)`. -/
def kTrunc (ρ : ℝ) (x y : ℂ) : ℝ := -Real.log (max ‖x - y‖ ρ)

/-- The singular remainder `d_ρ(x,y) = log⁺(ρ/|x-y|)`. -/
def dTrunc (ρ : ℝ) (x y : ℂ) : ℝ := log⁺ (ρ / ‖x - y‖)

@[fun_prop]
theorem measurable_kTrunc (ρ : ℝ) : Measurable fun p : ℂ × ℂ => kTrunc ρ p.1 p.2 := by
  unfold kTrunc
  fun_prop

theorem dTrunc_nonneg (ρ : ℝ) (x y : ℂ) : 0 ≤ dTrunc ρ x y := Real.posLog_nonneg

/-- `-log|x-y| = k_ρ(x,y) + d_ρ(x,y)` off the diagonal. -/
theorem neg_log_norm_sub_eq_kTrunc_add_dTrunc {ρ : ℝ} (hρ : 0 < ρ) {x y : ℂ} (hxy : x ≠ y) :
    -Real.log ‖x - y‖ = kTrunc ρ x y + dTrunc ρ x y := by
  have hd : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  unfold kTrunc dTrunc
  rcases le_total ρ ‖x - y‖ with h | h
  · rw [max_eq_left h]
    have h0 : log⁺ (ρ / ‖x - y‖) = 0 := by
      rw [Real.posLog_eq_zero_iff, abs_of_nonneg (by positivity)]
      exact (div_le_one hd).2 h
    rw [h0, add_zero]
  · rw [max_eq_right h]
    have h1 : 1 ≤ |ρ / ‖x - y‖| := by
      rw [abs_of_nonneg (by positivity)]
      exact (one_le_div hd).2 h
    rw [Real.posLog_eq_log h1, Real.log_div hρ.ne' hd.ne']
    ring

/-- `t ↦ log max(t, ρ)` is `1/ρ`-Lipschitz. -/
theorem abs_log_max_sub_log_max_le {ρ : ℝ} (hρ : 0 < ρ) (s t : ℝ) :
    |Real.log (max s ρ) - Real.log (max t ρ)| ≤ |s - t| / ρ := by
  have key : ∀ a b : ℝ, ρ ≤ a → ρ ≤ b → Real.log a - Real.log b ≤ |a - b| / ρ := by
    intro a b ha hb
    have ha0 : 0 < a := hρ.trans_le ha
    have hb0 : 0 < b := hρ.trans_le hb
    rw [← Real.log_div ha0.ne' hb0.ne']
    calc Real.log (a / b) ≤ a / b - 1 := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
      _ = (a - b) / b := by field_simp
      _ ≤ |a - b| / b := by gcongr; exact le_abs_self _
      _ ≤ |a - b| / ρ := by gcongr
  have hab : |max s ρ - max t ρ| ≤ |s - t| := abs_max_sub_max_le_abs s t ρ
  have h1 := key (max s ρ) (max t ρ) (le_max_right _ _) (le_max_right _ _)
  have h2 := key (max t ρ) (max s ρ) (le_max_right _ _) (le_max_right _ _)
  rw [abs_sub_comm (max t ρ)] at h2
  have h3 : |max s ρ - max t ρ| / ρ ≤ |s - t| / ρ := by gcongr
  rw [abs_le]
  constructor <;> linarith

/-- `k_ρ` is `1/ρ`-Lipschitz in its first variable. -/
theorem abs_kTrunc_sub_kTrunc_le {ρ : ℝ} (hρ : 0 < ρ) (a b c : ℂ) :
    |kTrunc ρ a c - kTrunc ρ b c| ≤ ‖a - b‖ / ρ := by
  unfold kTrunc
  rw [show -Real.log (max ‖a - c‖ ρ) - -Real.log (max ‖b - c‖ ρ) =
      -(Real.log (max ‖a - c‖ ρ) - Real.log (max ‖b - c‖ ρ)) by ring, abs_neg]
  refine (abs_log_max_sub_log_max_le hρ _ _).trans ?_
  gcongr
  calc |‖a - c‖ - ‖b - c‖| ≤ ‖(a - c) - (b - c)‖ := abs_norm_sub_norm_le _ _
    _ = ‖a - b‖ := by rw [sub_sub_sub_cancel_right]

/-! ## Integrability and the splitting of the logarithmic energy -/

variable {μ ν ν' : Measure ℂ}

theorem IsRegular.integrable_dTrunc (hμ : IsRegular μ) (hν : IsRegular ν) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) : Integrable (fun p : ℂ × ℂ => dTrunc ρ p.1 p.2) (μ.prod ν) :=
  hμ.integrable_posLog_div hν hρ hρ1

theorem IsRegular.integrable_kTrunc (hμ : IsRegular μ) (hν : IsRegular ν) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) : Integrable (fun p : ℂ × ℂ => kTrunc ρ p.1 p.2) (μ.prod ν) := by
  have := hμ.1
  refine ((hμ.integrable_neg_log_norm_sub hν).sub (hμ.integrable_dTrunc hν hρ hρ1)).congr ?_
  filter_upwards [hν.ae_prod_ne (μ := μ)] with p hp
  simp only [Pi.sub_apply]
  rw [neg_log_norm_sub_eq_kTrunc_add_dTrunc hρ hp]
  ring

/-- `L(μ,ν) = ∫ k_ρ d(μ ⊗ ν) + ∫ d_ρ d(μ ⊗ ν)` for regular `μ, ν` and `0 < ρ ≤ 1`. -/
theorem logEnergy_eq_kTrunc_add_dTrunc (hμ : IsRegular μ) (hν : IsRegular ν) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    logEnergy μ ν = ∫ p, kTrunc ρ p.1 p.2 ∂(μ.prod ν) + ∫ p, dTrunc ρ p.1 p.2 ∂(μ.prod ν) := by
  have := hμ.1
  rw [logEnergy_eq_integral_prod hμ hν, ← integral_add (hμ.integrable_kTrunc hν hρ hρ1)
    (hμ.integrable_dTrunc hν hρ hρ1)]
  refine integral_congr_ae ?_
  filter_upwards [hν.ae_prod_ne (μ := μ)] with p hp
  exact neg_log_norm_sub_eq_kTrunc_add_dTrunc hρ hp

/-- Layer-cake bound for the diagonal `d_ρ` terms: `∫ d_ρ d(ν ⊗ ν) ≤ B ρ^α / α`. -/
theorem integral_dTrunc_le [IsProbabilityMeasure ν] {ρ α B : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hα : 0 < α) (hB : 0 ≤ B)
    (hb : ∀ u : ℂ, ∀ r : ℝ, 0 < r → r ≤ 1 → (ν (ball u r)).toReal ≤ B * r ^ α) :
    ∫ p, dTrunc ρ p.1 p.2 ∂(ν.prod ν) ≤ B * ρ ^ α / α := by
  have hb' : ∀ u : ℂ, ∀ r : ℝ, 0 < r → r ≤ 1 → ν (ball u r) ≤ ENNReal.ofReal (B * r ^ α) := by
    intro u r hr hr1
    rw [← ENNReal.ofReal_toReal (measure_ne_top ν _)]
    exact ENNReal.ofReal_le_ofReal (hb u r hr hr1)
  have h := (integrable_posLog_div_prod (μ := ν) (ν := ν) hρ hρ1 hα hB hb').2
  rwa [probReal_univ, one_mul] at h

/-! ## The coupling bound for the truncated kernel -/

/-- A measure on `ℂ × ℂ` whose first marginal is a probability measure is a probability
measure. -/
theorem isProbabilityMeasure_of_map_fst {P : Measure (ℂ × ℂ)} [IsProbabilityMeasure ν]
    (hP : P.map Prod.fst = ν) : IsProbabilityMeasure P := by
  have : IsProbabilityMeasure (P.map Prod.fst) := by
    rw [hP]
    infer_instance
  exact Measure.isProbabilityMeasure_of_map measurable_fst.aemeasurable

/-- Transfer of `∫ k_ρ d(μ₁ ⊗ μ₂)` to the product of two copies of a measure `P` whose images
under `f` and `g` are `μ₁` and `μ₂`. -/
theorem integrable_and_integral_kTrunc_map {P : Measure (ℂ × ℂ)} [IsFiniteMeasure P]
    {f g : ℂ × ℂ → ℂ} (hf : Measurable f) (hg : Measurable g) {μ₁ μ₂ : Measure ℂ}
    (h1 : P.map f = μ₁) (h2 : P.map g = μ₂) (hμ₁ : IsRegular μ₁) (hμ₂ : IsRegular μ₂)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    Integrable (fun q : (ℂ × ℂ) × (ℂ × ℂ) => kTrunc ρ (f q.1) (g q.2)) (P.prod P) ∧
      ∫ p, kTrunc ρ p.1 p.2 ∂(μ₁.prod μ₂) =
        ∫ q : (ℂ × ℂ) × (ℂ × ℂ), kTrunc ρ (f q.1) (g q.2) ∂(P.prod P) := by
  have hmap : μ₁.prod μ₂ = (P.prod P).map (Prod.map f g) := by
    rw [← h1, ← h2, Measure.map_prod_map P P hf hg]
  have hint := hμ₁.integrable_kTrunc hμ₂ hρ hρ1
  rw [hmap] at hint
  refine ⟨(integrable_map_measure (measurable_kTrunc ρ).aestronglyMeasurable
    (hf.prodMap hg).aemeasurable).1 hint, ?_⟩
  rw [hmap, integral_map (hf.prodMap hg).aemeasurable (measurable_kTrunc ρ).aestronglyMeasurable]
  rfl

/-- The `k_ρ` part of the coupling estimate:
`K(ν,ν) - K(ν,ν') - K(ν',ν) + K(ν',ν') ≤ 2η/ρ` with `K(μ₁,μ₂) = ∫ k_ρ d(μ₁ ⊗ μ₂)`. -/
theorem kTrunc_four_term_le [IsProbabilityMeasure ν] (hν : IsRegular ν) (hν' : IsRegular ν')
    {P : Measure (ℂ × ℂ)} (hP1 : P.map Prod.fst = ν) (hP2 : P.map Prod.snd = ν') {η : ℝ}
    (hPη : P {p | η < ‖p.1 - p.2‖} = 0) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    (∫ p, kTrunc ρ p.1 p.2 ∂(ν.prod ν)) - (∫ p, kTrunc ρ p.1 p.2 ∂(ν.prod ν')) -
        (∫ p, kTrunc ρ p.1 p.2 ∂(ν'.prod ν)) + (∫ p, kTrunc ρ p.1 p.2 ∂(ν'.prod ν')) ≤
      2 * η / ρ := by
  have := isProbabilityMeasure_of_map_fst hP1
  obtain ⟨i11, e11⟩ := integrable_and_integral_kTrunc_map measurable_fst measurable_fst hP1 hP1
    hν hν hρ hρ1
  obtain ⟨i12, e12⟩ := integrable_and_integral_kTrunc_map measurable_fst measurable_snd hP1 hP2
    hν hν' hρ hρ1
  obtain ⟨i21, e21⟩ := integrable_and_integral_kTrunc_map measurable_snd measurable_fst hP2 hP1
    hν' hν hρ hρ1
  obtain ⟨i22, e22⟩ := integrable_and_integral_kTrunc_map measurable_snd measurable_snd hP2 hP2
    hν' hν' hρ hρ1
  have i112 : Integrable (fun q : (ℂ × ℂ) × (ℂ × ℂ) =>
      kTrunc ρ q.1.1 q.2.1 - kTrunc ρ q.1.1 q.2.2) (P.prod P) := i11.sub i12
  have i1123 : Integrable (fun q : (ℂ × ℂ) × (ℂ × ℂ) =>
      kTrunc ρ q.1.1 q.2.1 - kTrunc ρ q.1.1 q.2.2 - kTrunc ρ q.1.2 q.2.1) (P.prod P) :=
    i112.sub i21
  have i11234 : Integrable (fun q : (ℂ × ℂ) × (ℂ × ℂ) =>
      kTrunc ρ q.1.1 q.2.1 - kTrunc ρ q.1.1 q.2.2 - kTrunc ρ q.1.2 q.2.1 +
        kTrunc ρ q.1.2 q.2.2) (P.prod P) :=
    i1123.add i22
  have hsum : (∫ p, kTrunc ρ p.1 p.2 ∂(ν.prod ν)) - (∫ p, kTrunc ρ p.1 p.2 ∂(ν.prod ν')) -
        (∫ p, kTrunc ρ p.1 p.2 ∂(ν'.prod ν)) + (∫ p, kTrunc ρ p.1 p.2 ∂(ν'.prod ν')) =
      ∫ q : (ℂ × ℂ) × (ℂ × ℂ), (kTrunc ρ q.1.1 q.2.1 - kTrunc ρ q.1.1 q.2.2 -
        kTrunc ρ q.1.2 q.2.1 + kTrunc ρ q.1.2 q.2.2) ∂(P.prod P) := by
    rw [integral_add i1123 i22, integral_sub i112 i21, integral_sub i11 i12, e11, e12, e21, e22]
  rw [hsum]
  have hae : ∀ᵐ p ∂P, ‖p.1 - p.2‖ ≤ η := by
    rw [ae_iff]
    refine measure_mono_null (fun p hp => ?_) hPη
    simp only [mem_ofPred_eq, not_le] at hp
    exact hp
  have hae2 : ∀ᵐ q ∂(P.prod P), ‖q.1.1 - q.1.2‖ ≤ η :=
    (Measure.quasiMeasurePreserving_fst (μ := P) (ν := P)).ae hae
  calc ∫ q : (ℂ × ℂ) × (ℂ × ℂ), (kTrunc ρ q.1.1 q.2.1 - kTrunc ρ q.1.1 q.2.2 -
          kTrunc ρ q.1.2 q.2.1 + kTrunc ρ q.1.2 q.2.2) ∂(P.prod P)
      ≤ ∫ _q : (ℂ × ℂ) × (ℂ × ℂ), 2 * η / ρ ∂(P.prod P) := by
        refine integral_mono_ae i11234 (integrable_const _) ?_
        filter_upwards [hae2] with q hq
        have h1 := abs_kTrunc_sub_kTrunc_le hρ q.1.1 q.1.2 q.2.1
        have h2 := abs_kTrunc_sub_kTrunc_le hρ q.1.1 q.1.2 q.2.2
        have h3 : ‖q.1.1 - q.1.2‖ / ρ ≤ η / ρ := by gcongr
        have e : 2 * η / ρ = η / ρ + η / ρ := by ring
        rw [e]
        linarith [le_abs_self (kTrunc ρ q.1.1 q.2.1 - kTrunc ρ q.1.2 q.2.1),
          neg_abs_le (kTrunc ρ q.1.1 q.2.2 - kTrunc ρ q.1.2 q.2.2)]
    _ = 2 * η / ρ := by rw [integral_const, probReal_univ, one_smul]

/-! ## The coupling estimate -/

/-- Blueprint Lemma `lem:coupling`: for regular probability measures `ν, ν'` with ball-mass
bounds `B r^α`, `B' r^α` (`r ∈ (0,1]`) and a coupling `P` with displacement at most `η`,
`ℰ(ν,ν) - 2ℰ(ν,ν') + ℰ(ν',ν') ≤ 2η/ρ + (B + B') ρ^α / α` for every `ρ ∈ (0, 1]`.

The blueprint also assumes `α ≤ 1`, `B, B' ≥ 1` and `η ≥ 0`; these are not needed. -/
theorem energy_sub_le_of_coupling [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (hν : IsRegular ν) (hν' : IsRegular ν') {α B B' : ℝ} (hα : 0 < α) (hB : 0 ≤ B)
    (hB' : 0 ≤ B')
    (hνb : ∀ u : ℂ, ∀ r : ℝ, 0 < r → r ≤ 1 → (ν (ball u r)).toReal ≤ B * r ^ α)
    (hν'b : ∀ u : ℂ, ∀ r : ℝ, 0 < r → r ≤ 1 → (ν' (ball u r)).toReal ≤ B' * r ^ α)
    {P : Measure (ℂ × ℂ)} (hP1 : P.map Prod.fst = ν) (hP2 : P.map Prod.snd = ν') {η : ℝ}
    (hPη : P {p | η < ‖p.1 - p.2‖} = 0) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    energy ν ν - 2 * energy ν ν' + energy ν' ν' ≤ 2 * η / ρ + (B + B') * ρ ^ α / α := by
  rw [energy_sub_eq_logEnergy hν hν' (by rw [measure_univ, measure_univ]),
    logEnergy_eq_kTrunc_add_dTrunc hν hν hρ hρ1, logEnergy_eq_kTrunc_add_dTrunc hν hν' hρ hρ1,
    logEnergy_eq_kTrunc_add_dTrunc hν' hν hρ hρ1, logEnergy_eq_kTrunc_add_dTrunc hν' hν' hρ hρ1]
  have hK := kTrunc_four_term_le hν hν' hP1 hP2 hPη hρ hρ1
  have hD1 := integral_dTrunc_le (ν := ν) hρ hρ1 hα hB hνb
  have hD2 := integral_dTrunc_le (ν := ν') hρ hρ1 hα hB' hν'b
  have hD12 : 0 ≤ ∫ p, dTrunc ρ p.1 p.2 ∂(ν.prod ν') :=
    integral_nonneg fun p => dTrunc_nonneg ρ p.1 p.2
  have hD21 : 0 ≤ ∫ p, dTrunc ρ p.1 p.2 ∂(ν'.prod ν) :=
    integral_nonneg fun p => dTrunc_nonneg ρ p.1 p.2
  have e : (B + B') * ρ ^ α / α = B * ρ ^ α / α + B' * ρ ^ α / α := by ring
  rw [e]
  linarith

end GaussianLQG
