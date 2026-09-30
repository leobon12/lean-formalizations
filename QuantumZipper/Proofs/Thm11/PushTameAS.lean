import QuantumZipper.Proofs.Thm11.PushTame
import QuantumZipper.Proofs.Thm11.NonSwallowingClock

/-!
# RG-3b: almost-sure strip decay of the pushforward test measures

Blueprint `THM11_BLUEPRINT.md` §7, node RG-3 (probabilistic part). Driver `W = drive κ B ω`,
`κ ∈ (0,4]`, `ν_T^ω = pushTest (drive κ B ω) T φ` (see `PushTame.lean`).

* `prob_clock_gt_pow_unif`: DF-1 with constants uniform over `{‖a‖ ≤ r, -log‖a‖ ≤ ℓ}`
  (a re-run of `NonSwallow.prob_fwdClock_gt_le_pow` with uniform bounds).
* Measurability: `measurable_fwdMap_alive` (joint measurability of `(a, ω) ↦ f_T(a)` on the alive
  set), `measurableSet_aliveSet`, `measurable_pushTest_drive` (`ω ↦ ν_T^ω(S)`, `S` Borel, e.g.
  the strips `{Im < δ}`), and the Tonelli formula `lintegral_pushTest_drive`.
* `ae_strip_decay_pushTest`: a.s. there is `C` with `ν_T{Im < exp(-exp t)} ≤ C t^{-2}` for
  `t ≥ 1`, which is RG-2's strip-decay hypothesis with `η = 1`;
  `ae_strip_decay_testFun` gives it for `φ = ρ^±`, `ρ ∈ TestFun H`.

Proof of the strip decay. With `δ_j = exp(-exp j)` and `Y_T = Im a · e^{-2S_T}`, a point of
`K ∩ D_T` with `Im f_T(a) < δ_j` has `S_T(a) > e^j/4` once `e^j ≥ -2 log min_K Im`, so
`E ν_T{Im < δ_j} ≤ c |K| sup_K P(S_T > e^j/4) ≤ A e^{-j/4}`. Hence `E Σ_j j² ν_T{Im < δ_j} < ∞`,
so a.s. `ν_T{Im < δ_j} ≤ Y/j²`; interpolate at `j = ⌊t⌋`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace QuantumZipper
namespace PushTameAS

open FwdClock Thm11Lyap FwdHolo NonSwallow PushTame

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-! ## DF-1 with uniform constants -/

/-- **DF-1, uniform form.** Constants uniform over `a ∈ ℍ` with `‖a‖ ≤ r`, `-log‖a‖ ≤ ℓ`. -/
theorem prob_clock_gt_pow_unif (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) (T : ℝ≥0)
    (r ℓ : ℝ) :
    ∃ K t₀ : ℝ, 1 ≤ t₀ ∧ ∀ a : ℂ, 0 < a.im → ‖a‖ ≤ r → -Real.log ‖a‖ ≤ ℓ → ∀ t : ℝ, t₀ ≤ t →
      P {ω | t ^ 12 < fwdClock (drive κ B ω) T a} ≤ ENNReal.ofReal (K / t ^ 3) := by
  set μG : ℝ := (4 - κ) / 4 * (2 * Real.pi ^ 2 / κ) with hμG
  have hμ : 0 ≤ μG := mul_nonneg (div_nonneg (by linarith) (by norm_num)) (by positivity)
  have hclock : ∃ K₂ : ℝ, 0 ≤ K₂ ∧ ∀ a : ℂ, 0 < a.im → -Real.log ‖a‖ ≤ ℓ →
      ∀ {ρ R c : ℝ}, 0 < ρ → 0 < c → 1 ≤ R → Real.log ρ = -R →
      ∃ Φ : ℂ → ℝ, ∃ lam M : ℝ, (∀ z : ℂ, 0 < z.im → ContDiffAt ℝ 3 Φ z) ∧ lam ≠ 0 ∧
        (∀ z ∈ annReg ρ R c,
          dynkinGen (tamedZField c) (-((Real.sqrt κ : ℝ) : ℂ)) Φ z = lam / ‖z‖ ^ 2) ∧
        (∀ z ∈ annReg ρ R c, (Φ z - Φ a) / lam ≤ M) ∧ M ≤ K₂ * (R ^ 2 + 1) := by
    rcases hκ4.lt_or_eq with hlt | rfl
    · have h4 : 0 < 4 - κ := by linarith
      refine ⟨2 * (|ℓ| + 1 + 2 * μG) / (4 - κ), by positivity, ?_⟩
      intro a ha haℓ ρ R c hρ hc hR1 _
      obtain ⟨hΦ, hlam, hgen, hbound⟩ := clock_data_lt_four hκ hlt (R := R) hρ hc a
      refine ⟨lyapV κ 0, _, _, hΦ, hlam, hgen, hbound, ?_⟩
      have hlogR : Real.log R ≤ R :=
        (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
      have hR2 : R ≤ R ^ 2 + 1 := by nlinarith
      have h1 : 1 ≤ R ^ 2 + 1 := by nlinarith
      have hV := lyapV_le hκ hκ4 0 ha
      simp only [zero_mul, add_zero] at hV
      have hl := le_abs_self ℓ
      have hX := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ |ℓ| + 2 * μG)
      have hnum : 2 * (lyapV κ 0 a + Real.log R + μG)
          ≤ 2 * (|ℓ| + 1 + 2 * μG) * (R ^ 2 + 1) := by nlinarith
      calc 2 * (lyapV κ 0 a + Real.log R + (4 - κ) / 4 * (2 * Real.pi ^ 2 / κ)) / (4 - κ)
          = 2 * (lyapV κ 0 a + Real.log R + μG) / (4 - κ) := by rw [hμG]
        _ ≤ 2 * (|ℓ| + 1 + 2 * μG) * (R ^ 2 + 1) / (4 - κ) :=
            div_le_div_of_nonneg_right hnum h4.le
        _ = 2 * (|ℓ| + 1 + 2 * μG) / (4 - κ) * (R ^ 2 + 1) := by ring
    · refine ⟨(1 + Real.pi ^ 2) / 4, by positivity, ?_⟩
      intro a _ _ ρ R c hρ hc hR1 hlogρ
      obtain ⟨hΦ, hlam, hgen, hbound⟩ := clock_data_four (R := R) hρ hc a
      refine ⟨logSq, 4, _, hΦ, hlam, hgen, hbound, ?_⟩
      have hlogR0 : 0 ≤ Real.log R := Real.log_nonneg hR1
      have hlogR : Real.log R ≤ R :=
        (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
      have hmax : max |Real.log ρ| |Real.log R| = R := by
        rw [hlogρ, abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ R), abs_of_nonneg hlogR0]
        exact max_eq_left hlogR
      rw [hmax]
      have : 1 ≤ R ^ 2 + 1 := by nlinarith
      nlinarith [Real.pi_pos]
  obtain ⟨K₂, hK₂, hclock⟩ := hclock
  set A : ℝ := ℓ + 2 * μG with hA
  set Bq : ℝ := r ^ 2 + (T : ℝ) * (κ + 4) with hBq
  refine ⟨|A| + |Bq| + 4 + 2 * K₂, max 1 (max r ℓ) + 1, by
    linarith [le_max_left 1 (max r ℓ)], fun a ha har haℓ t ht => ?_⟩
  have hna : 0 < ‖a‖ := norm_pos_iff.2 (fun h => by simp [h] at ha)
  have ht1 : 1 ≤ t := by linarith [le_max_left 1 (max r ℓ)]
  have ht0 : 0 < t := by linarith
  set R : ℝ := t ^ 4 with hRdef
  have htR : t ≤ R := by
    rw [hRdef]
    calc t = t ^ 1 := (pow_one t).symm
      _ ≤ t ^ 4 := pow_le_pow_right₀ ht1 (by norm_num)
  have hR1 : 1 ≤ R := ht1.trans htR
  have hRgt : max 1 (max r ℓ) < R := by linarith
  have hRa : ‖a‖ < R := har.trans_lt (((le_max_left _ _).trans (le_max_right _ _)).trans_lt hRgt)
  have hRl : -Real.log ‖a‖ < R :=
    haℓ.trans_lt (((le_max_right _ _).trans (le_max_right _ _)).trans_lt hRgt)
  set ρ : ℝ := Real.exp (-R) with hρdef
  have hρ : 0 < ρ := Real.exp_pos _
  have hlogρ : Real.log ρ = -R := Real.log_exp _
  have hρa : ρ < ‖a‖ := by
    rw [hρdef, ← Real.exp_log hna]; exact Real.exp_lt_exp.2 (by linarith)
  have hρR : ρ < R := hρa.trans hRa
  set c : ℝ := a.im * Real.exp (-2 * ((T : ℝ) / ρ ^ 2)) / 2 with hcdef
  have hpos : 0 < a.im * Real.exp (-2 * ((T : ℝ) / ρ ^ 2)) := by positivity
  have hc : 0 < c := by positivity
  have hcs : c < a.im * Real.exp (-2 * ((T : ℝ) / ρ ^ 2)) := by linarith
  have hexp : Real.exp (-2 * ((T : ℝ) / ρ ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ (T : ℝ) / ρ ^ 2 := by positivity
    linarith
  have hca : c < a.im := hcs.trans_le (mul_le_of_le_one_right ha.le hexp)
  have haO : a ∈ annOpen ρ R c := ⟨hρa, hRa, hca⟩
  have hε : 0 < 1 / R := by positivity
  obtain ⟨Φ, lam, M, hΦ, hlam, hgen, hbound, hM⟩ := hclock a ha haℓ hρ hc hR1 hlogρ
  have hu : 0 < t ^ 12 := by positivity
  have hmain := prob_clock_gt_le hB hBm hBc hκ hκ4 T hρ hρR hc hε haO hcs Φ hΦ hlam hgen
    hbound hu
  refine hmain.trans ?_
  have hlogR : Real.log R ≤ 4 * t := by
    rw [hRdef, Real.log_pow]; push_cast
    have := Real.log_le_sub_one_of_pos ht0; linarith
  have hlogR0 : 0 ≤ Real.log R := Real.log_nonneg hR1
  have hRR : 1 / R * R ^ 2 = R := by field_simp
  have hm : min (Real.log R - Real.log ρ) (1 / R * R ^ 2) = R := by
    rw [hlogρ, hRR]; apply min_eq_right; linarith
  have hV := lyapV_le hκ hκ4 (1 / R) ha
  have har2 : ‖a‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) har 2
  have har2' : 1 / R * ‖a‖ ^ 2 ≤ 1 / R * r ^ 2 := mul_le_mul_of_nonneg_left har2 hε.le
  have hQ : lyapV κ (1 / R) a + T * (1 / R * (κ + 4)) + Real.log R + μG
      ≤ A + Bq / R + Real.log R := by
    have e : Bq / R = 1 / R * r ^ 2 + (T : ℝ) * (1 / R * (κ + 4)) := by
      simp only [hBq]; ring
    rw [e, hA]; linarith
  have hBR : Bq / R ≤ |Bq| :=
    (div_le_div_of_nonneg_right (le_abs_self Bq) (by positivity)).trans
      (div_le_self (abs_nonneg _) hR1)
  have hnum : A + Bq / R + Real.log R ≤ (|A| + |Bq| + 4) * t := by
    have := le_abs_self A
    nlinarith [abs_nonneg A, abs_nonneg Bq]
  have hexit : (lyapV κ (1 / R) a + T * (1 / R * (κ + 4)) + Real.log R + μG)
      / min (Real.log R - Real.log ρ) (1 / R * R ^ 2) ≤ (|A| + |Bq| + 4) / t ^ 3 := by
    rw [hm, div_le_div_iff₀ (by positivity) (by positivity)]
    calc (lyapV κ (1 / R) a + T * (1 / R * (κ + 4)) + Real.log R + μG) * t ^ 3
        ≤ ((|A| + |Bq| + 4) * t) * t ^ 3 :=
          mul_le_mul_of_nonneg_right (hQ.trans hnum) (by positivity)
      _ = (|A| + |Bq| + 4) * R := by rw [hRdef]; ring
  have hclk : M / t ^ 12 ≤ 2 * K₂ / t ^ 3 := by
    rw [div_le_div_iff₀ hu (by positivity)]
    have h11 : t ^ 11 ≤ t ^ 12 := pow_le_pow_right₀ ht1 (by norm_num)
    have h3 : t ^ 3 ≤ t ^ 12 := pow_le_pow_right₀ ht1 (by norm_num)
    have h8 : M * t ^ 3 ≤ K₂ * (t ^ 8 + 1) * t ^ 3 := by
      have : R ^ 2 = t ^ 8 := by rw [hRdef]; ring
      rw [this] at hM
      exact mul_le_mul_of_nonneg_right hM (by positivity)
    have : K₂ * (t ^ 8 + 1) * t ^ 3 = K₂ * (t ^ 11 + t ^ 3) := by ring
    rw [this] at h8
    linarith [mul_le_mul_of_nonneg_left h11 hK₂, mul_le_mul_of_nonneg_left h3 hK₂]
  have hsplit : (|A| + |Bq| + 4 + 2 * K₂) / t ^ 3
      = (|A| + |Bq| + 4) / t ^ 3 + 2 * K₂ / t ^ 3 := by ring
  rw [hsplit, ENNReal.ofReal_add (by positivity) (by positivity)]
  exact add_le_add (ENNReal.ofReal_le_ofReal hexit) (ENNReal.ofReal_le_ofReal hclk)

/-! ## Joint measurability -/

/-- The set of `(a, ω)` with `a` alive at time `T` and `f_T(a) ∈ S`. -/
def aliveSet (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (T : ℝ) (S : Set ℂ) : Set (ℂ × Ω) :=
  {p | p.1 ∈ H \ fwdHull (drive κ B p.2) T ∧ fwdMap (drive κ B p.2) T p.1 ∈ S}

theorem measurableSet_alive (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) (κ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    MeasurableSet {p : ℂ × Ω | p.1 ∈ H \ fwdHull (drive κ B p.2) T} := by
  have e : {p : ℂ × Ω | p.1 ∈ H \ fwdHull (drive κ B p.2) T} =
      {p : ℂ × Ω | 0 < p.1.im} \ {p : ℂ × Ω | p.1 ∈ fwdHull (drive κ B p.2) T} := by
    ext p; exact Iff.rfl
  rw [e]
  exact (measurableSet_lt measurable_const (Complex.measurable_im.comp measurable_fst)).diff
    (measurableSet_fwdHull_prod hBm hBc κ hT)

open Classical in
/-- **Joint measurability of the forward map on the alive set** (junk `0` elsewhere). -/
theorem measurable_fwdMap_alive (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) (κ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    Measurable fun p : ℂ × Ω =>
      if p.1 ∈ H \ fwdHull (drive κ B p.2) T then fwdMap (drive κ B p.2) T p.1 else 0 := by
  have hG := measurableSet_alive hBm hBc κ hT
  refine measurable_of_tendsto_metrizable (f := fun (k : ℕ) (p : ℂ × Ω) =>
    if p.1 ∈ H \ fwdHull (drive κ B p.2) T then
      tamedZ (drive κ B p.2) (1 / ((k : ℝ) + 1)) p.1 T else 0) (fun k => ?_) ?_
  · exact Measurable.ite hG
      (measurable_tamed_drive κ Nat.one_div_pos_of_nat B hBc hT (fun r _ => hBm r)).1 measurable_const
  · refine tendsto_pi_nhds.2 fun p => ?_
    by_cases hp : p.1 ∈ H \ fwdHull (drive κ B p.2) T
    · simp only [if_pos hp]
      have hW : Continuous (drive κ B p.2) := continuous_drive_ns hBc κ p.2
      have ha : 0 < p.1.im := hp.1
      obtain ⟨u, hu⟩ := exists_isForwardSol_of_not_mem_fwdHull hT hp.1 hp.2
      have hmono := im_isForwardSol_le hW ha hu
      have hm : 0 < (u T).im := hmono.2 T ⟨hT, le_rfl⟩
      obtain ⟨k₀, hk₀⟩ := exists_nat_one_div_lt hm
      refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨k₀, fun k hk => ?_⟩)
      have hc : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      have hck : 1 / ((k : ℝ) + 1) ≤ (u T).im := (Nat.one_div_le_one_div hk).trans hk₀.le
      refine (tamedZ_eq_fwdMap hW hc hT ha ⟨u, hu⟩ (fun t ht => ?_) T ⟨hT, le_rfl⟩).symm
      rw [fwdMap_eq hW ha hu ht]
      exact hck.trans (hmono.1 ht ⟨hT, le_rfl⟩ ht.2)
    · simp only [if_neg hp]
      exact tendsto_const_nhds

open Classical in
theorem measurableSet_aliveSet (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) (κ : ℝ) {T : ℝ} (hT : 0 ≤ T) {S : Set ℂ}
    (hS : MeasurableSet S) : MeasurableSet (aliveSet κ B T S) := by
  have e : aliveSet κ B T S = {p : ℂ × Ω | p.1 ∈ H \ fwdHull (drive κ B p.2) T} ∩
      (fun p : ℂ × Ω => if p.1 ∈ H \ fwdHull (drive κ B p.2) T then
        fwdMap (drive κ B p.2) T p.1 else 0) ⁻¹' S := by
    ext p
    simp only [aliveSet, mem_inter_iff, mem_setOf_eq, mem_preimage]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [if_pos h1]; exact h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [if_pos h1] at h2⟩
  rw [e]
  exact (measurableSet_alive hBm hBc κ hT).inter (measurable_fwdMap_alive hBm hBc κ hT hS)

/-- `ν_T^ω(S)` as an integral of the indicator of `aliveSet`. -/
theorem pushTest_drive_eq (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) (κ : ℝ) {T : ℝ} (hT : 0 ≤ T) (φ : ℂ → ℝ≥0∞)
    {S : Set ℂ} (hS : MeasurableSet S) (ω : Ω) :
    pushTest (drive κ B ω) T φ S =
      ∫⁻ a, (aliveSet κ B T S).indicator (fun p => φ p.1) (a, ω) := by
  have hsec : fwdMap (drive κ B ω) T ⁻¹' S ∩ (H \ fwdHull (drive κ B ω) T) =
      (fun a => (a, ω)) ⁻¹' aliveSet κ B T S := by
    ext a
    simp only [aliveSet, mem_inter_iff, mem_preimage, mem_setOf_eq]
    exact and_comm
  rw [pushTest_apply (continuous_drive_ns hBc κ ω) hT hS, hsec,
    ← lintegral_indicator ((measurableSet_aliveSet hBm hBc κ hT hS).preimage
      measurable_prodMk_right)]
  rfl

/-- **Measurability in `ω`** of `ν_T^ω(S)` for Borel `S`. -/
theorem measurable_pushTest_drive (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) (κ : ℝ) {T : ℝ} (hT : 0 ≤ T) {φ : ℂ → ℝ≥0∞}
    (hφ : Measurable φ) {S : Set ℂ} (hS : MeasurableSet S) :
    Measurable fun ω => pushTest (drive κ B ω) T φ S := by
  rw [funext fun ω => pushTest_drive_eq hBm hBc κ hT φ hS ω]
  exact ((hφ.comp measurable_fst).indicator
    (measurableSet_aliveSet hBm hBc κ hT hS)).lintegral_prod_left'

/-- **Tonelli:** `E ν_T(S) = ∫ φ(a) P(a alive, f_T(a) ∈ S) da`. -/
theorem lintegral_pushTest_drive (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) (κ : ℝ) {T : ℝ} (hT : 0 ≤ T) {φ : ℂ → ℝ≥0∞}
    (hφ : Measurable φ) {S : Set ℂ} (hS : MeasurableSet S) (P : Measure Ω) [SFinite P] :
    ∫⁻ ω, pushTest (drive κ B ω) T φ S ∂P =
      ∫⁻ a, φ a * P {ω | (a, ω) ∈ aliveSet κ B T S} := by
  have hE := measurableSet_aliveSet hBm hBc κ hT hS
  have hf : Measurable ((aliveSet κ B T S).indicator fun p : ℂ × Ω => φ p.1) :=
    (hφ.comp measurable_fst).indicator hE
  rw [funext fun ω => pushTest_drive_eq hBm hBc κ hT φ hS ω,
    lintegral_lintegral_swap
      (f := fun ω a => (aliveSet κ B T S).indicator (fun p => φ p.1) (a, ω))
      (Measurable.aemeasurable (by exact hf.comp measurable_swap))]
  refine lintegral_congr fun a => ?_
  have : (fun ω => (aliveSet κ B T S).indicator (fun p : ℂ × Ω => φ p.1) (a, ω)) =
      {ω | (a, ω) ∈ aliveSet κ B T S}.indicator (fun _ => φ a) := by
    funext ω
    by_cases h : (a, ω) ∈ aliveSet κ B T S <;> simp [indicator, h]
  rw [this, lintegral_indicator_const (s := {ω | (a, ω) ∈ aliveSet κ B T S})
    (hE.preimage measurable_prodMk_left) (φ a)]

/-! ## The strip decay -/

/-- The clock identity turns thin strips into large clocks. -/
lemma lt_fwdClock_of_im_lt {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {a : ℂ}
    (ha : a ∈ H \ fwdHull W T) {m δ u : ℝ} (hm : 0 < m) (hma : m ≤ a.im) (_hδ : 0 < δ)
    (hu : u ≤ (Real.log m - Real.log δ) / 2) (hlt : (fwdMap W T a).im < δ) :
    u < fwdClock W T a := by
  have ha0 : 0 < a.im := ha.1
  have hsol := exists_isForwardSol_of_not_mem_fwdHull hT ha.1 ha.2
  have him := im_fwdMap_eq_clock hW ha0 hsol (⟨hT, le_rfl⟩ : T ∈ Icc (0 : ℝ) T)
  rw [him] at hlt
  have h := Real.log_lt_log (by positivity) hlt
  rw [Real.log_mul ha0.ne' (Real.exp_pos _).ne', Real.log_exp] at h
  have := Real.log_le_log hm hma
  linarith

/-- **RG-3b, strip decay.** For `κ ∈ (0,4]`, almost surely `ν_T{Im < exp(-exp t)} ≤ C t^{-2}`
for all `t ≥ 1`: the hypothesis `hS` of `evalReg_pushTest_ae_eq` with `η = 1`. -/
theorem ae_strip_decay_pushTest (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) (T : ℝ≥0)
    {φ : ℂ → ℝ≥0∞} (hφ : Measurable φ) {c : ℝ≥0∞} (hc : c < ⊤) (hφc : ∀ z, φ z ≤ c)
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) (hφK : ∀ z ∉ K, φ z = 0) :
    ∀ᵐ ω ∂P, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      pushTest (drive κ B ω) T φ {z | z.im < Real.exp (-Real.exp t)} ≤
        ENNReal.ofReal (C * t ^ (-(1 + (1 : ℝ)))) := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hT0 : (0 : ℝ) ≤ T := T.2
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  -- uniform bounds on `K`
  obtain ⟨Bd, hBd⟩ := hK.exists_bound_of_continuousOn (f := fun a : ℂ => -Real.log a.im)
    (fun a ha => ((Real.continuousAt_log (ne_of_gt (hKH ha))).comp
      Complex.continuous_im.continuousAt).neg.continuousWithinAt)
  obtain ⟨r, hr⟩ := hK.isBounded.exists_norm_le
  set m : ℝ := Real.exp (-Bd) with hmdef
  have hm : 0 < m := Real.exp_pos _
  have hmK : ∀ a ∈ K, m ≤ a.im := fun a ha => by
    have h1 : -Real.log a.im ≤ Bd := (le_abs_self _).trans (by simpa using hBd a ha)
    have h2 : 0 < a.im := hKH ha
    calc m = Real.exp (-Bd) := rfl
      _ ≤ Real.exp (Real.log a.im) := Real.exp_le_exp.2 (by linarith)
      _ = a.im := Real.exp_log h2
  have hlK : ∀ a ∈ K, -Real.log ‖a‖ ≤ -Real.log m := fun a ha => by
    have := Real.log_le_log hm ((hmK a ha).trans (Complex.im_le_norm a)); linarith
  obtain ⟨Kc, t₀, ht₀, htail⟩ := prob_clock_gt_pow_unif hB hBm hBc hκ hκ4 T r (-Real.log m)
  -- the strip masses
  set δ : ℕ → ℝ := fun j => Real.exp (-Real.exp j) with hδ
  set X : ℕ → Ω → ℝ≥0∞ := fun j ω => pushTest (drive κ B ω) T φ {z | z.im < δ j} with hX
  have hSm : ∀ j, MeasurableSet {z : ℂ | z.im < δ j} := fun j =>
    measurableSet_lt Complex.measurable_im measurable_const
  have hXm : ∀ j, Measurable (X j) := fun j =>
    measurable_pushTest_drive hBm hBc κ hT0 hφ (hSm j)
  set ρ : ℝ := Real.exp (-(1 / 4)) with hρdef
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hρ1 : ρ < 1 := (Real.exp_lt_exp.2 (by norm_num : -(1 / 4 : ℝ) < 0)).trans_eq Real.exp_zero
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j →
      t₀ ≤ Real.exp ((j - Real.log 4) / 12) ∧ -2 * Real.log m ≤ Real.exp j := by
    refine ⟨⌈12 * t₀ + Real.log 4 + |2 * Real.log m|⌉₊, fun j hj => ?_⟩
    have hjr : 12 * t₀ + Real.log 4 + |2 * Real.log m| ≤ j :=
      (Nat.le_ceil _).trans (by exact_mod_cast hj)
    have h1 := Real.add_one_le_exp ((j - Real.log 4) / 12)
    have h2 := Real.add_one_le_exp (j : ℝ)
    have h3 := neg_abs_le (2 * Real.log m)
    have h4 : 0 ≤ |2 * Real.log m| := abs_nonneg _
    have h5 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    constructor <;> linarith
  set A' : ℝ := max (|Kc| * Real.exp (Real.log 4 / 4)) (ρ⁻¹ ^ j₀) with hA'
  have hA'0 : 0 < A' := lt_max_of_lt_right (by positivity)
  -- pointwise probability bound, uniform on `K`
  have hPj : ∀ j : ℕ, ∀ a ∈ K,
      P {ω | (a, ω) ∈ aliveSet κ B T {z | z.im < δ j}} ≤ ENNReal.ofReal (A' * ρ ^ j) := by
    intro j a ha
    by_cases hj : j₀ ≤ j
    · set tj : ℝ := Real.exp ((j - Real.log 4) / 12) with htj
      have htj12 : tj ^ 12 = Real.exp j / 4 := by
        rw [htj, ← Real.exp_nat_mul,
          show ((12 : ℕ) : ℝ) * ((j - Real.log 4) / 12) = j - Real.log 4 by push_cast; ring,
          Real.exp_sub, Real.exp_log (by norm_num)]
      have htj3 : tj ^ 3 = Real.exp ((j - Real.log 4) / 4) := by
        rw [htj, ← Real.exp_nat_mul]; congr 1; push_cast; ring
      have hsub : {ω | (a, ω) ∈ aliveSet κ B T {z | z.im < δ j}} ⊆
          {ω | tj ^ 12 < fwdClock (drive κ B ω) T a} := by
        rintro ω ⟨hD, hlt⟩
        refine lt_fwdClock_of_im_lt (continuous_drive_ns hBc κ ω) hT0 hD hm (hmK a ha)
          (Real.exp_pos _) ?_ hlt
        have h2 := (hj₀ j hj).2
        have key : Real.exp j / 4 ≤ (Real.log m - Real.log (Real.exp (-Real.exp j))) / 2 := by
          rw [Real.log_exp (-Real.exp j)]; linarith
        rw [htj12]; exact key
      refine (measure_mono hsub).trans ((htail a (hKH ha) (hr a ha) (hlK a ha) tj
        (hj₀ j hj).1).trans (ENNReal.ofReal_le_ofReal ?_))
      rw [htj3, div_eq_mul_inv, ← Real.exp_neg, hρdef, ← Real.exp_nat_mul]
      have e : Real.exp (-((j - Real.log 4) / 4)) =
          Real.exp (Real.log 4 / 4) * Real.exp (j * (-(1 / 4))) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [e, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      exact (mul_le_mul_of_nonneg_right (le_abs_self Kc) (Real.exp_pos _).le).trans
        (le_max_left _ _)
    · refine prob_le_one.trans (ENNReal.one_le_ofReal.2 ?_)
      have h1 : ρ ^ j₀ ≤ ρ ^ j := pow_le_pow_of_le_one hρ0.le hρ1.le (not_le.1 hj).le
      calc (1 : ℝ) = ρ⁻¹ ^ j₀ * ρ ^ j₀ := by
            rw [inv_pow, inv_mul_cancel₀ (pow_pos hρ0 _).ne']
        _ ≤ A' * ρ ^ j := mul_le_mul (le_max_right _ _) h1 (by positivity) hA'0.le
  -- expected strip masses
  have hE : ∀ j : ℕ, ∫⁻ ω, X j ω ∂P ≤ c * volume K * ENNReal.ofReal (A' * ρ ^ j) := by
    intro j
    rw [hX, lintegral_pushTest_drive hBm hBc κ hT0 hφ (hSm j) P]
    calc ∫⁻ a, φ a * P {ω | (a, ω) ∈ aliveSet κ B T {z | z.im < δ j}}
        ≤ ∫⁻ a, K.indicator (fun _ => c) a * ENNReal.ofReal (A' * ρ ^ j) := by
          refine lintegral_mono fun a => ?_
          by_cases ha : a ∈ K
          · rw [indicator_of_mem ha]
            exact mul_le_mul' (hφc a) (hPj j a ha)
          · rw [hφK a ha, zero_mul]; exact zero_le
      _ = c * volume K * ENNReal.ofReal (A' * ρ ^ j) := by
          rw [lintegral_mul_const _ (measurable_const.indicator hKm),
            lintegral_indicator_const hKm]
  -- the weighted sum has finite expectation
  set Y : Ω → ℝ≥0∞ := fun ω => ∑' j : ℕ, ((j : ℝ≥0∞)) ^ 2 * X j ω with hY
  have hYm : Measurable Y := Measurable.ennreal_tsum fun j => (hXm j).const_mul _
  have hsum : Summable fun j : ℕ => (j : ℝ) ^ 2 * (A' * ρ ^ j) := by
    have := (summable_pow_mul_geometric_of_norm_lt_one 2
      (by rw [Real.norm_eq_abs, abs_of_pos hρ0]; exact hρ1) :
        Summable fun n : ℕ => (n : ℝ) ^ 2 * ρ ^ n).mul_left A'
    exact this.congr fun j => by ring
  have hYint : ∫⁻ ω, Y ω ∂P < ⊤ := by
    rw [hY, lintegral_tsum fun j => ((hXm j).const_mul _).aemeasurable]
    calc ∑' j : ℕ, ∫⁻ ω, ((j : ℝ≥0∞)) ^ 2 * X j ω ∂P
        = ∑' j : ℕ, ((j : ℝ≥0∞)) ^ 2 * ∫⁻ ω, X j ω ∂P := by
          congr 1; funext j; exact lintegral_const_mul _ (hXm j)
      _ ≤ ∑' j : ℕ, ((j : ℝ≥0∞)) ^ 2 * (c * volume K * ENNReal.ofReal (A' * ρ ^ j)) :=
          ENNReal.tsum_le_tsum fun j => by gcongr; exact hE j
      _ = c * volume K * ∑' j : ℕ, ENNReal.ofReal ((j : ℝ) ^ 2 * (A' * ρ ^ j)) := by
          rw [← ENNReal.tsum_mul_left]
          congr 1; funext j
          rw [ENNReal.ofReal_mul (sq_nonneg (j : ℝ)), ENNReal.ofReal_pow (Nat.cast_nonneg j),
            ENNReal.ofReal_natCast]
          ring
      _ < ⊤ := by
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (sq_nonneg _)
            (mul_nonneg hA'0.le (pow_nonneg hρ0.le _))) hsum]
          exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hc hK.measure_lt_top)
            ENNReal.ofReal_lt_top
  filter_upwards [ae_lt_top hYm hYint.ne] with ω hω
  refine ⟨4 * (Y ω).toReal, by positivity, fun t ht => ?_⟩
  set j := ⌊t⌋₊ with hjdef
  have hj1 : 1 ≤ j := Nat.le_floor (by exact_mod_cast ht)
  have hjt : (j : ℝ) ≤ t := Nat.floor_le (by linarith)
  have htj : t < j + 1 := Nat.lt_floor_add_one t
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
  have hj2 : t ≤ 2 * j := by
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    linarith
  have h1 : ((j : ℝ≥0∞)) ^ 2 * X j ω ≤ Y ω :=
    ENNReal.le_tsum (f := fun i : ℕ => ((i : ℝ≥0∞)) ^ 2 * X i ω) j
  have hjne : ((j : ℝ≥0∞)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (Nat.cast_ne_zero.2 (by omega))
  have hXj : X j ω ≤ Y ω / ((j : ℝ≥0∞)) ^ 2 := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hjne) (Or.inl (ENNReal.pow_ne_top
      (ENNReal.natCast_ne_top j))), mul_comm]
    exact h1
  have hYeq : Y ω / ((j : ℝ≥0∞)) ^ 2 = ENNReal.ofReal ((Y ω).toReal / (j : ℝ) ^ 2) := by
    rw [ENNReal.ofReal_div_of_pos (pow_pos hj0 2), ENNReal.ofReal_toReal hω.ne,
      ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  calc pushTest (drive κ B ω) T φ {z | z.im < Real.exp (-Real.exp t)}
      ≤ X j ω := measure_mono fun z (hz : z.im < _) =>
        (show z.im < δ j from lt_of_lt_of_le hz
          (Real.exp_le_exp.2 (neg_le_neg (Real.exp_le_exp.2 hjt))))
    _ ≤ ENNReal.ofReal ((Y ω).toReal / (j : ℝ) ^ 2) := hXj.trans hYeq.le
    _ ≤ ENNReal.ofReal (4 * (Y ω).toReal * t ^ (-(1 + (1 : ℝ)))) := by
        apply ENNReal.ofReal_le_ofReal
        rw [show (-(1 + (1 : ℝ))) = -2 by norm_num, Real.rpow_neg (by linarith),
          Real.rpow_two]
        have ht0 : 0 < t := by linarith
        have hY0 : 0 ≤ (Y ω).toReal := ENNReal.toReal_nonneg
        calc (Y ω).toReal / (j : ℝ) ^ 2 ≤ (Y ω).toReal / (t ^ 2 / 4) :=
              div_le_div_of_nonneg_left hY0 (by positivity) (by nlinarith)
          _ = 4 * (Y ω).toReal * (t ^ 2)⁻¹ := by field_simp

/-- **RG-3b for test functions.** For `ρ` continuous with compact support in `ℍ` (use `ρ.1`
and `-ρ.1` for `ρ ∈ TestFun H`), the strip decay holds a.s. for `ν_T = pushTest … (ρ⁺ Leb)`,
in the exact form of the hypothesis `hS` of `evalReg_pushTest_ae_eq` (`η = 1`). -/
theorem ae_strip_decay_ofReal (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) (T : ℝ≥0)
    {ρ : ℂ → ℝ} (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) (hρH : tsupport ρ ⊆ H) :
    ∀ᵐ ω ∂P, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      pushTest (drive κ B ω) T (fun z => ENNReal.ofReal (ρ z))
        {z | z.im < Real.exp (-Real.exp t)} ≤ ENNReal.ofReal (C * t ^ (-(1 + (1 : ℝ)))) := by
  obtain ⟨Bρ, hBρ⟩ := hρ.bounded_above_of_compact_support hρc
  exact ae_strip_decay_pushTest hB hBm hBc hκ hκ4 T hρ.measurable.ennreal_ofReal
    (c := ENNReal.ofReal Bρ) ENNReal.ofReal_lt_top
    (fun z => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸
      hBρ z))) hρc hρH
    (fun z hz => by rw [image_eq_zero_of_notMem_tsupport hz, ENNReal.ofReal_zero])

/-- **RG-3b for `ρ ∈ TestFun H`**, both parts `ρ^±` at once. -/
theorem ae_strip_decay_testFun (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) (T : ℝ≥0)
    (ρ : TestFun H) :
    ∀ᵐ ω ∂P, (∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      pushTest (drive κ B ω) T (fun z => ENNReal.ofReal (ρ.1 z))
        {z | z.im < Real.exp (-Real.exp t)} ≤ ENNReal.ofReal (C * t ^ (-(1 + (1 : ℝ))))) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      pushTest (drive κ B ω) T (fun z => ENNReal.ofReal (-ρ.1 z))
        {z | z.im < Real.exp (-Real.exp t)} ≤ ENNReal.ofReal (C * t ^ (-(1 + (1 : ℝ))))) := by
  have hρ : Continuous ρ.1 := ρ.2.1.continuous
  have hp := ae_strip_decay_ofReal hB hBm hBc hκ hκ4 T hρ ρ.2.2.1 ρ.2.2.2
  have hn := ae_strip_decay_ofReal (ρ := fun z => -ρ.1 z) hB hBm hBc hκ hκ4 T hρ.neg
    ρ.2.2.1.neg (by rw [show (fun z => -ρ.1 z) = -ρ.1 from rfl, tsupport_neg]; exact ρ.2.2.2)
  filter_upwards [hp, hn] with ω h1 h2 using ⟨h1, h2⟩

end PushTameAS
end QuantumZipper
