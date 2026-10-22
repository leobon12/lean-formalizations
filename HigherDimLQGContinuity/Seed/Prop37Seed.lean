import HigherDimLQGContinuity.Seed.Basic
import HigherDimLQGContinuity.Witness.Subdiv

/-!
# Proposition 3.7 with a supplied seed (packet P8b)

Blueprint Part A, Proposition `a:prop37-seed` ([C] Prop. 3.7, last sentence, p. 10, l. 494–495; NA1 item 29, R12;
NA0 §2.5; erratum EA `a:err-37`).

**Statement** (`prop37_of_seed`). Let `d ≥ 2` and assume Lemma 2.1 (`UniformEstimates d ξ̄ s`, interface I1) for all
pins `s ∈ [1, 10]`. There are `p_s > 0` and `c' ∈ (0, 1]` such that for every `R_s ≥ 1` and `R ≥ 1` there are
`M₇, C₇, c₇ > 0` with: for `ξ, η ∈ (0, ξ̄]`, `D, E` strong, `δ ∈ (0, 1/8)` and `n`, if
`𝐏₁₀{g : supd_{R_s}(ρ^D_g, ρ^E_g) > c'δ} ≤ p_s`, `n ≥ C₇ δ^{-M₇} log(C₇/δ)` and `|ξ − η| n ≤ c₇ δ`, then
`𝐏{g : supd_R(log(1 + ρ^D_g), log(1 + ρ^E_g)) > δ} ≤ C₇ δ^{-M₇} e^{-c₇ δ^{M₇} n}`.

The event is written with `supDistLU` and `logProfile` (the form of `Prop37Shape`); it is the event
`∃ x, y ∈ B̄_R, |log(1 + ρ^D(x, y)) − log(1 + ρ^E(x, y))| > δ` of the blueprint by `p8b_logEvent_eq`. The extra
clause `c' ≤ 1` (a strengthening; `c' = min(d∗/8, 1)`) lets Proposition 3.7 apply Proposition 3.6 at `u = c'δ < 1`.

**Proof** (blueprint, NA1 R12). Fixed data: `p₀` of Proposition 3.3; references `𝓡` at pin `10` with failure
`p₀/4` (`refs_prob`); `d∗ = subdivD 𝓡`; `p_s = p₀/4`, `c' = min(d∗/8, 1)`; `(M₃, C₃, c₃)` of Proposition 3.3 for
`C_b = 2`, `𝓡`, local pin `10`, global pin `1`. Local events from the seed: off the seed event, on the references and
on the length event, Lemma `a:lem-subdiv`(c) (`not_mem_hup_of_supDistLU_le`) excludes `H↑(D, E; 1 + c'δ/d∗)` and
`H↑(E, D; 1 + c'δ/d∗)`, hence `H↑(·, ·; 1 + δ/8)` (antitone in the coefficient); so both local bad events have
`𝐏₁₀`-probability `≤ p₀/2` (`p8b_seed_local`). Amplification: Proposition 3.3 for `(D, E)` and `(E, D)` with
`b = 1 + δ/8`, slack `δ/8`, error `δ/4`, radius `R` (global pin `1`, `𝐏₁ = 𝐏`). On the complement of both bad events,
`|log(1 + ρ^D) − log(1 + ρ^E)| ≤ log(1 + δ/4) ≤ δ/4 < δ` on `B̄_R²` (`p8b_abs_log_sub_le`). Constants:
`M₇ = M₃`, `c₇ = min(c₃ 8^{-M₃}, c₃/8)`, `C₇ = max(2C₃8^{M₃}(R^{M₃} + 1), 32e(1 + R))` (`p8b_seed_depth`,
`p8b_seed_bound`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ## The local events from the seed -/

/-- **Local events from the seed** (blueprint `a:prop37-seed`, step 1; NA1 R12): off the seed event
`supd_{R_s}(ρ^D, ρ^E) > u`, on the references and on the length event, neither `H↑(D, E; b)` nor `H↑(E, D; b)` holds
for `b ≥ 1 + u/d∗`; hence both local bad events of Proposition 3.3 have `𝐏₁₀`-probability at most `p + q`. -/
theorem p8b_seed_local (hd : 2 ≤ d) {ξ η : ℝ} {D E : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ (distExp d ξ) D) (hE : IsStrongExpMetric d η (distExp d η) E)
    {H₀ σ₀ β₀ m M : ℝ} (hH₀ : 0 < H₀) (hσ₀ : 0 < σ₀) (hβ₀ : 0 < β₀) (hm : 0 < m)
    {Rs u b p q : ℝ} (hRs : 1 ≤ Rs) (hu : 0 ≤ u) (hb : 1 + u / subdivD H₀ σ₀ β₀ m M ≤ b)
    (hseed : pinLaw d 10 {g | ENNReal.ofReal u < supDistLU d Rs (rho D g).1 (rho E g).1} ≤
      ENNReal.ofReal p)
    (hrefs : pinLaw d 10 (PairRefs D E H₀ σ₀ β₀ m M)ᶜ ≤ ENNReal.ofReal q) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    pinLaw d 10 (Hup D E b ∪ (PairRefs D E H₀ σ₀ β₀ m M)ᶜ) ≤ ENNReal.ofReal (p + q) ∧
      pinLaw d 10 (Hup E D b ∪ (PairRefs E D H₀ σ₀ β₀ m M)ᶜ) ≤ ENNReal.ofReal (p + q) := by
  set S : Set (DistRd d) := {g | ENNReal.ofReal u < supDistLU d Rs (rho D g).1 (rho E g).1} with hS
  set N : Set (DistRd d) := {g | ¬ ((rho D g).IsLength ∧ (rho E g).IsLength)} with hN
  have hN0 : pinLaw d 10 N = 0 := by
    have hlD := p5b_ae_isLength_rho hd hD (s := 10) (by norm_num)
    have hlE := p5b_ae_isLength_rho hd hE (s := 10) (by norm_num)
    exact ae_iff.1 (hlD.and hlE)
  -- the common majorant
  have hmaj : pinLaw d 10 (S ∪ (PairRefs D E H₀ σ₀ β₀ m M)ᶜ ∪ N) ≤ ENNReal.ofReal (p + q) := by
    calc pinLaw d 10 (S ∪ (PairRefs D E H₀ σ₀ β₀ m M)ᶜ ∪ N)
        ≤ pinLaw d 10 S + pinLaw d 10 (PairRefs D E H₀ σ₀ β₀ m M)ᶜ + pinLaw d 10 N := by
          refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
          exact measure_union_le _ _
      _ ≤ ENNReal.ofReal p + ENNReal.ofReal q + 0 := by
          rw [hN0]
          gcongr
      _ = ENNReal.ofReal (p + q) := by rw [add_zero, ENNReal.ofReal_add hp hq]
  -- the deterministic exclusion
  have hgood : ∀ g, g ∉ S → g ∈ PairRefs D E H₀ σ₀ β₀ m M → (rho D g).IsLength → (rho E g).IsLength →
      g ∉ Hup D E b ∧ g ∉ Hup E D b := by
    intro g hgS hgR hlD hlE
    have hsup : supDistLU d Rs (rho D g).1 (rho E g).1 ≤ ENNReal.ofReal u := not_lt.1 hgS
    obtain ⟨h1, h2⟩ := not_mem_hup_of_supDistLU_le hlD hlE hH₀ hσ₀ hβ₀ hm hgR hRs hu hsup
    exact ⟨fun h => h1 (p8b_hup_anti hb h), fun h => h2 (p8b_hup_anti hb h)⟩
  constructor
  · refine le_trans (measure_mono ?_) hmaj
    intro g hg
    by_contra hcon
    simp only [mem_union, mem_compl_iff, not_or, not_not, hN, mem_ofPred_eq] at hcon
    obtain ⟨⟨hgS, hgR⟩, hlD, hlE⟩ := hcon
    rcases hg with hg | hg
    · exact (hgood g hgS hgR hlD hlE).1 hg
    · exact hg hgR
  · refine le_trans (measure_mono ?_) hmaj
    intro g hg
    by_contra hcon
    simp only [mem_union, mem_compl_iff, not_or, not_not, hN, mem_ofPred_eq] at hcon
    obtain ⟨⟨hgS, hgR⟩, hlD, hlE⟩ := hcon
    rcases hg with hg | hg
    · exact (hgood g hgS hgR hlD hlE).2 hg
    · exact hg ⟨hgR.2, hgR.1⟩

/-! ## The target event -/

/-- **The target event** (blueprint `a:prop37-seed`, last step): if both comparisons with coefficient `1 + t` and error
`t < δ` hold on `B̄_R`, the logarithmic profiles differ by at most `t < δ`. -/
theorem p8b_target_subset (D E : DistRd d → ContMetric d) {t δ R : ℝ} (ht : 0 ≤ t) (htδ : t < δ) :
    {g | ENNReal.ofReal δ < supDistLU d R (logProfile (rho D g).1) (logProfile (rho E g).1)} ⊆
      {g | ¬ CompOn (rho E g) (rho D g) (1 + t) t R} ∪ {g | ¬ CompOn (rho D g) (rho E g) (1 + t) t R} := by
  intro g hg
  by_contra hcon
  simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hcon
  have h := p8b_supDistLU_logProfile_le_of_compOn ht hcon.1 hcon.2
  exact absurd (lt_of_lt_of_le hg h) (not_lt.2 (ENNReal.ofReal_le_ofReal htδ.le))

/-! ## Numerics -/

/-- `(δ/8)^{-M} = 8^M δ^{-M}`. -/
theorem p8b_div8_rpow_neg {δ M : ℝ} (hδ : 0 < δ) : (δ / 8) ^ (-M) = 8 ^ M * δ ^ (-M) := by
  rw [Real.div_rpow hδ.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8), div_inv_eq_mul,
    mul_comm]

/-- `(δ/8)^M = 8^{-M} δ^M`. -/
theorem p8b_div8_rpow {δ M : ℝ} (hδ : 0 < δ) : (δ / 8) ^ M = 8 ^ (-M) * δ ^ M := by
  rw [Real.div_rpow hδ.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8), div_eq_mul_inv,
    mul_comm]

/-- The depth condition of Proposition 3.3 (slack `δ/8`, error `δ/4`) from the depth condition of `a:prop37-seed`. -/
theorem p8b_seed_depth {C₃ M₃ R δ C₇ n : ℝ} (hC₃ : 0 < C₃) (hR : 1 ≤ R) (hδ : 0 < δ) (hδ8 : δ < 1 / 8)
    (hC₇a : 2 * C₃ * 8 ^ M₃ ≤ C₇) (hC₇b : 32 * Real.exp 1 * (1 + R) ≤ C₇)
    (hn : C₇ * δ ^ (-M₃) * Real.log (C₇ / δ) ≤ n) :
    C₃ * (δ / 8) ^ (-M₃) * (1 + Real.log (1 + R) + Real.log (δ / 4)⁻¹ + Real.log (δ / 8)⁻¹) ≤ n := by
  have hδinv : 0 < δ⁻¹ := inv_pos.2 hδ
  set L : ℝ := Real.log δ⁻¹ with hL
  have hL0 : 0 < L := Real.log_pos (by rw [lt_inv_comm₀ one_pos hδ, inv_one]; linarith)
  have hX : 0 < δ ^ (-M₃) := Real.rpow_pos_of_pos hδ _
  have hY : 0 < (8 : ℝ) ^ M₃ := Real.rpow_pos_of_pos (by norm_num) _
  set A : ℝ := 1 + Real.log (1 + R) + Real.log 32 with hA
  have hlogR : 0 ≤ Real.log (1 + R) := Real.log_nonneg (by linarith)
  have hl32 : 0 ≤ Real.log 32 := Real.log_nonneg (by norm_num)
  have hA0 : 0 ≤ A := by rw [hA]; linarith
  have h4 : Real.log (δ / 4)⁻¹ = Real.log 4 + L := by
    rw [inv_div, div_eq_mul_inv, Real.log_mul (by norm_num) hδinv.ne']
  have h8 : Real.log (δ / 8)⁻¹ = Real.log 8 + L := by
    rw [inv_div, div_eq_mul_inv, Real.log_mul (by norm_num) hδinv.ne']
  have h32 : Real.log 4 + Real.log 8 = Real.log 32 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have hC₇pos : 0 < C₇ := lt_of_lt_of_le (by positivity) hC₇b
  have hlogC₇ : A ≤ Real.log C₇ := by
    have h1 : Real.log (32 * Real.exp 1 * (1 + R)) = Real.log 32 + 1 + Real.log (1 + R) := by
      rw [Real.log_mul (by positivity) (by linarith), Real.log_mul (by norm_num) (Real.exp_pos 1).ne',
        Real.log_exp]
    have h2 : Real.log (32 * Real.exp 1 * (1 + R)) ≤ Real.log C₇ :=
      Real.log_le_log (by positivity) hC₇b
    rw [hA]
    linarith
  have hlogC₇δ : Real.log (C₇ / δ) = Real.log C₇ + L := by
    rw [div_eq_mul_inv, Real.log_mul hC₇pos.ne' hδinv.ne']
  rw [p8b_div8_rpow_neg hδ, h4, h8]
  rw [hlogC₇δ] at hn
  have hbr : 1 + Real.log (1 + R) + (Real.log 4 + L) + (Real.log 8 + L) = A + 2 * L := by
    rw [hA, ← h32]
    ring
  rw [hbr]
  have hAL : A + 2 * L ≤ 2 * (Real.log C₇ + L) := by linarith
  have hlogpos : 0 ≤ Real.log C₇ + L := by linarith
  calc C₃ * (8 ^ M₃ * δ ^ (-M₃)) * (A + 2 * L)
      = (C₃ * 8 ^ M₃) * δ ^ (-M₃) * (A + 2 * L) := by ring
    _ ≤ (C₃ * 8 ^ M₃) * δ ^ (-M₃) * (2 * (Real.log C₇ + L)) := by gcongr
    _ = (2 * C₃ * 8 ^ M₃) * δ ^ (-M₃) * (Real.log C₇ + L) := by ring
    _ ≤ C₇ * δ ^ (-M₃) * (Real.log C₇ + L) := by gcongr
    _ ≤ n := hn

/-- The sum of the two failure bounds of Proposition 3.3 (slack `δ/8`) is at most the bound of `a:prop37-seed`. -/
theorem p8b_seed_bound {C₃ M₃ c₃ R δ n C₇ c₇ : ℝ} (hC₃ : 0 < C₃) (hR : 1 ≤ R) (hδ : 0 < δ) (hn : 0 ≤ n)
    (hC₇ : 2 * C₃ * 8 ^ M₃ * R ^ M₃ ≤ C₇) (hc₇ : c₇ ≤ c₃ * 8 ^ (-M₃)) :
    C₃ * R ^ M₃ * (δ / 8) ^ (-M₃) * Real.exp (-c₃ * (δ / 8) ^ M₃ * n) +
        C₃ * R ^ M₃ * (δ / 8) ^ (-M₃) * Real.exp (-c₃ * (δ / 8) ^ M₃ * n) ≤
      C₇ * δ ^ (-M₃) * Real.exp (-(c₇ * δ ^ M₃ * n)) := by
  have hX : 0 < δ ^ (-M₃) := Real.rpow_pos_of_pos hδ _
  have hδM : 0 ≤ δ ^ M₃ := (Real.rpow_pos_of_pos hδ _).le
  have hRM : 0 < R ^ M₃ := Real.rpow_pos_of_pos (by linarith) _
  have hexp : Real.exp (-c₃ * (δ / 8) ^ M₃ * n) ≤ Real.exp (-(c₇ * δ ^ M₃ * n)) := by
    apply Real.exp_le_exp.2
    rw [p8b_div8_rpow hδ]
    have h1 : c₇ * δ ^ M₃ * n ≤ c₃ * 8 ^ (-M₃) * δ ^ M₃ * n := by
      have := mul_le_mul_of_nonneg_right hc₇ hδM
      exact mul_le_mul_of_nonneg_right this hn
    have h2 : -c₃ * (8 ^ (-M₃) * δ ^ M₃) * n = -(c₃ * 8 ^ (-M₃) * δ ^ M₃ * n) := by ring
    rw [h2]
    linarith
  rw [p8b_div8_rpow_neg hδ]
  have hE0 : 0 ≤ Real.exp (-c₃ * (δ / 8) ^ M₃ * n) := (Real.exp_pos _).le
  have hC₇0 : 0 ≤ C₇ * δ ^ (-M₃) :=
    mul_nonneg (le_trans (by positivity) hC₇) hX.le
  calc C₃ * R ^ M₃ * (8 ^ M₃ * δ ^ (-M₃)) * Real.exp (-c₃ * (δ / 8) ^ M₃ * n) +
        C₃ * R ^ M₃ * (8 ^ M₃ * δ ^ (-M₃)) * Real.exp (-c₃ * (δ / 8) ^ M₃ * n)
      = (2 * C₃ * 8 ^ M₃ * R ^ M₃) * δ ^ (-M₃) * Real.exp (-c₃ * (δ / 8) ^ M₃ * n) := by ring
    _ ≤ C₇ * δ ^ (-M₃) * Real.exp (-(c₇ * δ ^ M₃ * n)) := by gcongr

/-! ## Proposition 3.7 with a supplied seed -/

/-- **Proposition 3.7 with a supplied seed** (blueprint `a:prop37-seed`; [C] Prop. 3.7, last sentence; NA1 R12). -/
theorem prop37_of_seed (hd : 2 ≤ d) {ξbar : ℝ} (hU : ∀ s ∈ Icc (1 : ℝ) 10, UniformEstimates d ξbar s) :
    ∃ ps c' : ℝ, 0 < ps ∧ 0 < c' ∧ c' ≤ 1 ∧ ∀ Rs R : ℝ, 1 ≤ Rs → 1 ≤ R →
      ∃ M C c : ℝ, 0 < M ∧ 0 < C ∧ 0 < c ∧
      ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ∀ η ∈ Ioc (0 : ℝ) ξbar, ∀ D E : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D → IsStrongExpMetric d η (distExp d η) E →
        ∀ δ : ℝ, 0 < δ → δ < 1 / 8 → ∀ n : ℝ,
          pinLaw d 10 {g | ENNReal.ofReal (c' * δ) < supDistLU d Rs (rho D g).1 (rho E g).1} ≤
            ENNReal.ofReal ps →
          C * δ ^ (-M) * Real.log (C / δ) ≤ n → |ξ - η| * n ≤ c * δ →
          normLGFLaw d {g | ENNReal.ofReal δ <
              supDistLU d R (logProfile (rho D g).1) (logProfile (rho E g).1)} ≤
            ENNReal.ofReal (C * δ ^ (-M) * Real.exp (-(c * δ ^ M * n))) := by
  obtain ⟨p₀, hp₀, h33⟩ := prop33 hd hU
  have hU10 := hU 10 ⟨by norm_num, le_rfl⟩
  obtain ⟨H₀, σ₀, β₀, m, M, hσ₀, -, hβ₀, hm, hmM, hH₀, hrefs⟩ :=
    refs_prob hd (by norm_num : (0 : ℝ) < 10) hU10 (p := p₀ / 4) (by positivity)
  have hH₀0 : 0 < H₀ := lt_of_lt_of_le one_pos hH₀
  have hβ₀0 : 0 < β₀ := lt_trans one_pos hβ₀
  set ds : ℝ := subdivD H₀ σ₀ β₀ m M with hds
  have hds0 : 0 < ds := subdivD_pos hm
  obtain ⟨M₃, C₃, c₃, hM₃, hC₃, hc₃, hamp⟩ :=
    h33 2 H₀ σ₀ β₀ m M two_pos hm hmM.le 10 1 (by norm_num) le_rfl le_rfl (by norm_num)
  set c' : ℝ := min (ds / 8) 1 with hc'
  have hc'0 : 0 < c' := lt_min (by positivity) one_pos
  refine ⟨p₀ / 4, c', by positivity, hc'0, min_le_right _ _, fun Rs R hRs hR => ?_⟩
  set C₇ : ℝ := max (2 * C₃ * 8 ^ M₃ * (R ^ M₃ + 1)) (32 * Real.exp 1 * (1 + R)) with hC₇
  set c₇ : ℝ := min (c₃ * 8 ^ (-M₃)) (c₃ / 8) with hc₇
  have hY : 0 < (8 : ℝ) ^ M₃ := Real.rpow_pos_of_pos (by norm_num) _
  have hRM : 0 < R ^ M₃ := Real.rpow_pos_of_pos (by linarith) _
  have hC₇a : 2 * C₃ * 8 ^ M₃ ≤ C₇ := by
    refine le_trans ?_ (le_max_left _ _)
    have : 2 * C₃ * 8 ^ M₃ * 1 ≤ 2 * C₃ * 8 ^ M₃ * (R ^ M₃ + 1) := by gcongr; linarith
    linarith
  have hC₇b : 32 * Real.exp 1 * (1 + R) ≤ C₇ := le_max_right _ _
  have hC₇c : 2 * C₃ * 8 ^ M₃ * R ^ M₃ ≤ C₇ := by
    refine le_trans ?_ (le_max_left _ _)
    have : 2 * C₃ * 8 ^ M₃ * R ^ M₃ ≤ 2 * C₃ * 8 ^ M₃ * (R ^ M₃ + 1) := by gcongr; linarith
    exact this
  have hC₇pos : 0 < C₇ := lt_of_lt_of_le (by positivity) hC₇a
  have hc₇pos : 0 < c₇ := lt_min (by positivity) (by positivity)
  refine ⟨M₃, C₇, c₇, hM₃, hC₇pos, hc₇pos, ?_⟩
  intro ξ hξ η hη D E hD hE δ hδ hδ8 n hseed hn hdrift
  -- the local events
  have hb : 1 + c' * δ / ds ≤ 1 + δ / 8 := by
    have h1 : c' * δ ≤ ds / 8 * δ := mul_le_mul_of_nonneg_right (min_le_left _ _) hδ.le
    have h2 : c' * δ / ds ≤ ds / 8 * δ / ds := div_le_div_of_nonneg_right h1 hds0.le
    have h3 : ds / 8 * δ / ds = δ / 8 := by field_simp
    linarith
  obtain ⟨hloc₁, hloc₂⟩ := p8b_seed_local hd hD hE hH₀0 hσ₀ hβ₀0 hm hRs (by positivity) hb hseed
    (hrefs ξ hξ η hη D E hD hE) (by positivity) (by positivity)
  have hp₀q : ENNReal.ofReal (p₀ / 4 + p₀ / 4) ≤ ENNReal.ofReal p₀ := ENNReal.ofReal_le_ofReal (by linarith)
  -- the depth and drift conditions of Proposition 3.3
  have hn0 : 0 ≤ n := by
    refine le_trans ?_ hn
    have hlog : 0 ≤ Real.log (C₇ / δ) := by
      refine Real.log_nonneg ?_
      rw [le_div_iff₀ hδ, one_mul]
      have : (1 : ℝ) ≤ C₇ := le_trans (by nlinarith [Real.add_one_le_exp 1]) hC₇b
      linarith
    have := Real.rpow_pos_of_pos hδ (-M₃)
    positivity
  have hdepth := p8b_seed_depth hC₃ hR hδ hδ8 hC₇a hC₇b hn
  have hdr : |ξ - η| * n ≤ c₃ * (δ / 8) := by
    have : c₇ * δ ≤ c₃ / 8 * δ := mul_le_mul_of_nonneg_right (min_le_right _ _) hδ.le
    linarith
  have hdr' : |η - ξ| * n ≤ c₃ * (δ / 8) := by rwa [abs_sub_comm]
  have hb2 : 1 + δ / 8 ≤ 2 := by linarith
  have h1 := hamp ξ hξ η hη D E hD hE (1 + δ / 8) (by positivity) hb2 (hloc₁.trans hp₀q) R (δ / 8) (δ / 4) n
    hR (by positivity) (by linarith) (by positivity) (by linarith) hdepth hdr'
  have h2 := hamp η hη ξ hξ E D hE hD (1 + δ / 8) (by positivity) hb2 (hloc₂.trans hp₀q) R (δ / 8) (δ / 4) n
    hR (by positivity) (by linarith) (by positivity) (by linarith) hdepth hdr
  have hco : 1 + δ / 8 + δ / 8 = 1 + δ / 4 := by ring
  rw [hco] at h1 h2
  -- the target event
  have hsub := p8b_target_subset D E (R := R) (t := δ / 4) (δ := δ) (by positivity) (by linarith)
  rw [← pinLaw_one hd]
  calc pinLaw d 1 {g | ENNReal.ofReal δ <
          supDistLU d R (logProfile (rho D g).1) (logProfile (rho E g).1)}
      ≤ pinLaw d 1 {g | ¬ CompOn (rho E g) (rho D g) (1 + δ / 4) (δ / 4) R} +
          pinLaw d 1 {g | ¬ CompOn (rho D g) (rho E g) (1 + δ / 4) (δ / 4) R} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (C₃ * R ^ M₃ * (δ / 8) ^ (-M₃) * Real.exp (-c₃ * (δ / 8) ^ M₃ * n)) +
          ENNReal.ofReal (C₃ * R ^ M₃ * (δ / 8) ^ (-M₃) * Real.exp (-c₃ * (δ / 8) ^ M₃ * n)) :=
        add_le_add h1 h2
    _ ≤ ENNReal.ofReal (C₇ * δ ^ (-M₃) * Real.exp (-(c₇ * δ ^ M₃ * n))) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (p8b_seed_bound hC₃ hR hδ hn0 hC₇c (min_le_left _ _))

end HigherDimLQGContinuity
