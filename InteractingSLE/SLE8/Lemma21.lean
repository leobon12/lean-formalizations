import InteractingSLE.SLE8.AL14.DerivComparison
import InteractingSLE.SLE8.TimeGrid
import QuantumZipper.Proofs.RS.TransienceCanon
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# SLE₈ note, Lemma 2.1 (consequence of Alvisio–Lawler)

Source: `source/sle8-continuity.pdf`, §2.1 (anchors `lem-2.1`, `lem-2.1-proof`, PDF pp. 2–3),
transcription `source/sle8/sle8-continuity.md`; Alvisio–Lawler [AL14],
`source/external/AL14/AL14.md` (anchors `lem-1`, `id-Dn`, `thm-2`, `cor-1`); the route recorded in
`planning/handoffs/SRC-EXT-S8.md` ("Note's Lemma 2.1 from AL14").

**Lemma 2.1.** For every `β ∈ (0, 1/4)`, almost surely there is a finite `C_β` such that
`sup_{0 ≤ t ≤ 1} y_k |F_t'(i y_k)| ≤ C_β k^{-β}` for every integer `k ≥ 1` (2.1).

Here `y_k = 2^{-k}` (`dyadicHeight`), `A_k(t) = y_k |F_t'(i y_k)|` (`normalizedDeriv`),
`F_t = fwdMapInv W t` with `W = √8 B` (`drive 8 B ω`), as in `InteractingSLE/SLE8/TimeGrid.lean`;
[AL14]'s map is `F̄_t = barInv B t` with `F̄_t'(z) = F_t'(√8 z)`, and `D_k`, `D_k^*` are
`derivGridMax`, `derivGridMaxStar p` (`InteractingSLE/SLE8/AL14/DerivComparison.lean`).

## Inputs

* [AL14] Lemma 1, `D̂_k ≤ c D_k^*` (landed: `exists_norm_deriv_barInv_le_derivGridMaxStar`, with the
  exponent `p ≥ alExp` in place of `4`);
* [AL14] Theorem 2 ((2.4)) and the convergent half of [AL14] Corollary 1: not landed yet (packets
  PROVE-AL14-T2 and PROVE-AL14-T4). They are stated as `AL14TheoremTwoStatement P` and
  `AL14CorollaryOneStatement P`, and they are the only hypotheses of `lemma21_of_al14`. Both are
  stated in a form weaker than [AL14]'s (only for Brownian motions with measurable coordinates and
  continuous paths started at `0` everywhere; Theorem 2 with an unspecified power of `log k`), so
  that the theorems of the two packets imply them directly.
* Lemma 2.2 of the note (`revFlow_revDriver_bounds`), for the finitely many small `k`:
  `A_k(t) ≤ √5`.
* Koebe distortion along a vertical segment (`RS.deriv_ratio_le_vertical`).

## Proof

Fix `β' = (β + 1/4)/2 ∈ (β, 1/4)` and `b = 1/4 > β`. Borel–Cantelli and Corollary 1 at `β'` give
`D_k ≤ 2^k k^{-β'}` eventually (`ae_eventually_derivGridMax_le`). Theorem 2 at `b` then gives
`D_k^* ≤ C 2^k (k^{-b} + (log k)^q k^{-β'}) ≤ 2C 2^k k^{-β}` eventually, and Lemma 1 gives
`y_k |F̄_t'(i y_k)| ≤ 2cC k^{-β}` for every `t ∈ [0, 1]`. Since `√8 y_{k+2} = (√8/4) y_k` and
`√8/4 ∈ [1/2, 2]`, Koebe distortion gives `A_k(t) ≤ 4K² y_{k+2} |F̄_t'(i y_{k+2})|`
(`normalizedDeriv_le_barInv`). The finitely many remaining `k` use `A_k(t) ≤ √5`
(`normalizedDeriv_le_sqrt_five`). Finally the statement passes from a regular version of `B`
(`RS.exists_good_version0`) to `B`.

## Main results

* `normalizedDeriv_le_sqrt_five`: `A_k(t) ≤ √5` for `t ∈ [0, 1]` (Lemma 2.2).
* `normalizedDeriv_le_barInv`: the Koebe transfer from [AL14]'s normalization.
* `exists_normalizedDeriv_le_of_eventually`: the pathwise deduction of (2.1).
* `ae_eventually_derivGridMax_le`: Borel–Cantelli for Corollary 1.
* `lemma21_of_al14`: Lemma 2.1, from [AL14] Theorem 2 and Corollary 1, in exactly the form of the
  hypothesis `hL21` of `ae_exists_continuous_trace_of_scale_count` (`Radial.lean`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped NNReal ENNReal Topology

namespace InteractingSLE.SLE8

open QuantumZipper AL14

/-! ## The inputs from [AL14] that have not landed -/

/-- **[AL14] Corollary 1, convergent half**, for the Brownian motions on `(Ω, P)`: for
`β ∈ (0, 1/4)`, `∑_{n ≥ 1} ∑_{t ∈ 𝒟_n} P(|F̄_t'(i 2^{-n})| ≥ 2^n n^{-β}) < ∞`, where
`𝒟_n = {j 4^{-n} : 0 ≤ j ≤ 4^n}` and `F̄_t = barInv B t` is [AL14]'s map. Stated only for Brownian
motions with measurable coordinates and continuous paths started at `0` everywhere (a weaker
statement than [AL14]'s). -/
def AL14CorollaryOneStatement {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) : Prop :=
  ∀ B : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (B t)) → (∀ ω, Continuous (B · ω)) → (∀ ω, B 0 ω = 0) →
    IsBrownianReal B P → ∀ β : ℝ, 0 < β → β < 1 / 4 →
      ∑' n : ℕ, ∑ j ∈ Finset.range (4 ^ (n + 1) + 1),
        P {ω | (2 : ℝ) ^ (n + 1) * ((n : ℝ) + 1) ^ (-β) ≤
          ‖deriv (barInv (fun r => B r.toNNReal ω) (alTime (n + 1) j))
            ((alHeight (n + 1) : ℂ) * I)‖} ≠ ∞

/-- **[AL14] Theorem 2** (the note's (2.4)), for the Brownian motions on `(Ω, P)`: for every `b > 0`
and every exponent `p ≥ alExp` of `Δ_{j,k}` in `D_k^*`, there are deterministic `C` and `q` such
that almost surely, for all large `k`, `D_k^* ≤ C (2^k k^{-b} + (log k)^q D_k)`. [AL14] prints
`p = 4` and `q = 2` (with `Δ^p`, `q = p/2`); the power of `log k` is left unspecified here, and the
statement is made only for Brownian motions with measurable coordinates and continuous paths
started at `0` everywhere (both weaker than [AL14]'s statement). -/
def AL14TheoremTwoStatement {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) : Prop :=
  ∀ B : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (B t)) → (∀ ω, Continuous (B · ω)) → (∀ ω, B 0 ω = 0) →
    IsBrownianReal B P → ∀ b : ℝ, 0 < b → ∀ p : ℕ, alExp ≤ p →
      ∃ C q : ℝ, ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop,
        derivGridMaxStar p (fun r => B r.toNNReal ω) k ≤
          C * ((2 : ℝ) ^ k * (k : ℝ) ^ (-b) +
            Real.log k ^ q * derivGridMax (fun r => B r.toNNReal ω) k)

/-! ## Deterministic bounds -/

/-- **Lemma 2.2 at the dyadic heights**: `A_k(t) = y_k |F_t'(i y_k)| ≤ √(y_k² + 4t) ≤ √5` for
`t ∈ [0, 1]`. -/
theorem normalizedDeriv_le_sqrt_five {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) (k : ℕ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : normalizedDeriv W k t ≤ Real.sqrt 5 := by
  have hy0 : 0 < dyadicHeight k := dyadicHeight_pos k
  have hy1 : dyadicHeight k ≤ 1 := dyadicHeight_le_one k
  have hz : ((dyadicHeight k : ℂ) * I) ∈ H := by
    show 0 < ((dyadicHeight k : ℂ) * I).im
    simpa using hy0
  have him : ((dyadicHeight k : ℂ) * I).im = dyadicHeight k := by simp
  obtain ⟨-, h2, h3, -⟩ := revFlow_revDriver_bounds hW hz (s := t) ⟨ht.1, le_rfl⟩
  rw [him] at h2 h3
  unfold normalizedDeriv
  rw [norm_deriv_fwdMapInv_eq_norm_deriv_revFlow hW hW0 ht.1 hz]
  calc dyadicHeight k * ‖deriv (revFlow (revDriver W t) t) ((dyadicHeight k : ℂ) * I)‖
      ≤ dyadicHeight k *
          ((revMap (revDriver W t) t ((dyadicHeight k : ℂ) * I)).im / dyadicHeight k) := by
        gcongr
    _ = (revMap (revDriver W t) t ((dyadicHeight k : ℂ) * I)).im := by field_simp
    _ ≤ Real.sqrt (dyadicHeight k ^ 2 + 4 * t) := h2
    _ ≤ Real.sqrt 5 := by
        apply Real.sqrt_le_sqrt
        nlinarith [ht.2]

/-- `y_k = 4 y_{k+2}`. -/
theorem dyadicHeight_eq_four_mul_alHeight (k : ℕ) : dyadicHeight k = 4 * alHeight (k + 2) := by
  unfold dyadicHeight alHeight
  rw [pow_add]
  field_simp
  norm_num

/-- **Koebe transfer** (proof of Lemma 2.1, last step): with `W = √8 U`,
`A_k(t) = y_k |F_t'(i y_k)| ≤ 4K² y_{k+2} |F̄_t'(i y_{k+2})|`, because
`F̄_t'(i y_{k+2}) = F_t'(i √8 y_{k+2})`, `√8 y_{k+2} = (√8/4) y_k` and `√8/4 ∈ [1/2, 2]`. -/
theorem normalizedDeriv_le_barInv {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) (k : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    normalizedDeriv (fun r => Real.sqrt 8 * U r) k t ≤
      4 * RS.koebeStepConst ^ 2 *
        (alHeight (k + 2) * ‖deriv (barInv U t) ((alHeight (k + 2) : ℂ) * I)‖) := by
  have hW : Continuous fun r => Real.sqrt 8 * U r := continuous_const.mul hU
  have hW0 : (fun r => Real.sqrt 8 * U r) 0 = 0 := by simp [hU0]
  have hd := RS.differentiableOn_fwdMapInv hW hW0 ht
  have hinj := RS.injOn_fwdMapInv hW hW0 ht
  have hsq : Real.sqrt 8 ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 8 := Real.sqrt_nonneg 8
  have h8 : 2 ≤ Real.sqrt 8 := by nlinarith
  have h8' : Real.sqrt 8 ≤ 3 := by nlinarith
  have hs1 : 1 / 2 ≤ Real.sqrt 8 / 4 := by linarith
  have hs2 : Real.sqrt 8 / 4 ≤ 2 := by linarith
  have hK := (RS.deriv_ratio_le_vertical hd hinj (dyadicHeight_pos k) hs1 hs2).2
  have hpt : (((Real.sqrt 8 / 4 * dyadicHeight k : ℝ)) : ℂ) * I =
      (Real.sqrt 8 : ℂ) * ((alHeight (k + 2) : ℂ) * I) := by
    rw [dyadicHeight_eq_four_mul_alHeight]
    push_cast
    ring
  rw [hpt, ← deriv_barInv] at hK
  unfold normalizedDeriv
  calc dyadicHeight k * ‖deriv (fwdMapInv (fun r => Real.sqrt 8 * U r) t)
        ((dyadicHeight k : ℂ) * I)‖
      ≤ dyadicHeight k * (RS.koebeStepConst ^ 2 *
          ‖deriv (barInv U t) ((alHeight (k + 2) : ℂ) * I)‖) :=
        mul_le_mul_of_nonneg_left hK (dyadicHeight_pos k).le
    _ = 4 * RS.koebeStepConst ^ 2 *
        (alHeight (k + 2) * ‖deriv (barInv U t) ((alHeight (k + 2) : ℂ) * I)‖) := by
        rw [dyadicHeight_eq_four_mul_alHeight]
        ring

/-- For `β < β'` and any real `q`, eventually `(log k)^q k^{-β'} ≤ k^{-β}`. -/
theorem eventually_log_rpow_mul_rpow_le (q : ℝ) {β β' : ℝ} (h : β < β') :
    ∀ᶠ k : ℕ in atTop, Real.log k ^ q * (k : ℝ) ^ (-β') ≤ (k : ℝ) ^ (-β) := by
  have h1 := (isLittleO_log_rpow_rpow_atTop q (sub_pos.2 h)).comp_tendsto
    tendsto_natCast_atTop_atTop
  filter_upwards [h1.bound one_pos, eventually_ge_atTop 1] with k hk hk1
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hk0 : (0 : ℝ) < k := by linarith
  have hlog : 0 ≤ Real.log k := Real.log_nonneg hk1'
  simp only [Function.comp, one_mul, Real.norm_eq_abs] at hk
  rw [abs_of_nonneg (Real.rpow_nonneg hlog _), abs_of_nonneg (Real.rpow_nonneg hk0.le _)] at hk
  calc Real.log k ^ q * (k : ℝ) ^ (-β') ≤ (k : ℝ) ^ (β' - β) * (k : ℝ) ^ (-β') :=
        mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg hk0.le _)
    _ = (k : ℝ) ^ (-β) := by
        rw [← Real.rpow_add hk0]
        ring_nf

theorem derivGridMax_nonneg (U : ℝ → ℝ) (k : ℕ) : 0 ≤ derivGridMax U k :=
  (norm_nonneg _).trans (Finset.le_sup' (f := fun j =>
    ‖deriv (barInv U (alTime k j)) ((alHeight k : ℂ) * I)‖) (Finset.self_mem_range_succ (4 ^ k)))

/-- **The deduction of (2.1) in [AL14]'s normalization** (proof of Lemma 2.1): if eventually
`D_k ≤ 2^k k^{-β'}` (Corollary 1 and Borel–Cantelli) and `D_k^* ≤ C (2^k k^{-b} + (log k)^q D_k)`
(Theorem 2), with `β < β'` and `β < b`, then eventually `y_k |F̄_t'(i y_k)| ≤ 2 c C⁺ k^{-β}` for all
`t ∈ [0, 1]`, with `c` the constant of [AL14] Lemma 1. -/
theorem eventually_alHeight_mul_norm_deriv_barInv_le {U : ℝ → ℝ} {p : ℕ} {β β' b C q c : ℝ}
    (hββ' : β < β') (hβb : β < b)
    (hc : ∀ k : ℕ, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖deriv (barInv U t) ((alHeight k : ℂ) * I)‖ ≤ c * derivGridMaxStar p U k)
    (hc0 : 0 ≤ c)
    (hD : ∀ᶠ k : ℕ in atTop, derivGridMax U k ≤ (2 : ℝ) ^ k * (k : ℝ) ^ (-β'))
    (hDs : ∀ᶠ k : ℕ in atTop, derivGridMaxStar p U k ≤
        C * ((2 : ℝ) ^ k * (k : ℝ) ^ (-b) + Real.log k ^ q * derivGridMax U k)) :
    ∀ᶠ k : ℕ in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      alHeight k * ‖deriv (barInv U t) ((alHeight k : ℂ) * I)‖ ≤
        2 * c * max C 0 * (k : ℝ) ^ (-β) := by
  filter_upwards [hD, hDs, eventually_log_rpow_mul_rpow_le q hββ', eventually_ge_atTop 1]
    with k h1 h2 h3 h4 t ht
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast h4
  have hk0 : (0 : ℝ) < k := by linarith
  have hlog : 0 ≤ Real.log k ^ q := Real.rpow_nonneg (Real.log_nonneg hk1) _
  have hDnn := derivGridMax_nonneg U k
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hX : 0 ≤ (2 : ℝ) ^ k * (k : ℝ) ^ (-b) + Real.log k ^ q * derivGridMax U k := by
    have := Real.rpow_nonneg hk0.le (-b)
    positivity
  have hb : (k : ℝ) ^ (-b) ≤ (k : ℝ) ^ (-β) :=
    Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
  have hal : alHeight k * (2 : ℝ) ^ k = 1 := by
    unfold alHeight
    exact inv_mul_cancel₀ (by positivity)
  have hstar : derivGridMaxStar p U k ≤
      max C 0 * ((2 : ℝ) ^ k * ((k : ℝ) ^ (-b) + Real.log k ^ q * (k : ℝ) ^ (-β'))) := by
    calc derivGridMaxStar p U k
        ≤ C * ((2 : ℝ) ^ k * (k : ℝ) ^ (-b) + Real.log k ^ q * derivGridMax U k) := h2
      _ ≤ max C 0 * ((2 : ℝ) ^ k * (k : ℝ) ^ (-b) + Real.log k ^ q * derivGridMax U k) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hX
      _ ≤ max C 0 * ((2 : ℝ) ^ k * (k : ℝ) ^ (-b) +
            Real.log k ^ q * ((2 : ℝ) ^ k * (k : ℝ) ^ (-β'))) := by gcongr
      _ = max C 0 * ((2 : ℝ) ^ k * ((k : ℝ) ^ (-b) + Real.log k ^ q * (k : ℝ) ^ (-β'))) := by
          ring
  have hal0 : 0 ≤ alHeight k := (alHeight_pos k).le
  calc alHeight k * ‖deriv (barInv U t) ((alHeight k : ℂ) * I)‖
      ≤ alHeight k * (c * derivGridMaxStar p U k) :=
        mul_le_mul_of_nonneg_left (hc k t ht) hal0
    _ ≤ alHeight k * (c * (max C 0 *
          ((2 : ℝ) ^ k * ((k : ℝ) ^ (-b) + Real.log k ^ q * (k : ℝ) ^ (-β'))))) := by
        gcongr
    _ = c * max C 0 * ((k : ℝ) ^ (-b) + Real.log k ^ q * (k : ℝ) ^ (-β')) *
          (alHeight k * 2 ^ k) := by
        ring
    _ = c * max C 0 * ((k : ℝ) ^ (-b) + Real.log k ^ q * (k : ℝ) ^ (-β')) := by
        rw [hal, mul_one]
    _ ≤ c * max C 0 * ((k : ℝ) ^ (-β) + (k : ℝ) ^ (-β)) := by gcongr
    _ = 2 * c * max C 0 * (k : ℝ) ^ (-β) := by ring

/-- **Lemma 2.1, pathwise deduction** (proof of Lemma 2.1, for one driver `U` with `W = √8 U`):
if eventually `D_k ≤ 2^k k^{-β'}` and `D_k^* ≤ C (2^k k^{-b} + (log k)^q D_k)` for an exponent
`p ≥ alExp`, with `0 < β < β'` and `β < b`, then there is `C'` with `A_k(t) ≤ C' k^{-β}` for every
`k ≥ 1` and `t ∈ [0, 1]`. -/
theorem exists_normalizedDeriv_le_of_eventually {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    {p : ℕ} (hp : alExp ≤ p) {β β' b C q : ℝ} (hβ : 0 < β) (hββ' : β < β') (hβb : β < b)
    (hD : ∀ᶠ k : ℕ in atTop, derivGridMax U k ≤ (2 : ℝ) ^ k * (k : ℝ) ^ (-β'))
    (hDs : ∀ᶠ k : ℕ in atTop, derivGridMaxStar p U k ≤
        C * ((2 : ℝ) ^ k * (k : ℝ) ^ (-b) + Real.log k ^ q * derivGridMax U k)) :
    ∃ C' : ℝ, ∀ k : ℕ, 1 ≤ k → ∀ t ∈ Icc (0 : ℝ) 1,
      normalizedDeriv (fun r => Real.sqrt 8 * U r) k t ≤ C' * (k : ℝ) ^ (-β) := by
  obtain ⟨c, hc1, hc⟩ := exists_norm_deriv_barInv_le_derivGridMaxStar
  have hE := eventually_alHeight_mul_norm_deriv_barInv_le hββ' hβb
    (fun k t ht => hc U hU hU0 p hp k t ht) (by linarith) hD hDs
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hE
  have hW : Continuous fun r => Real.sqrt 8 * U r := continuous_const.mul hU
  have hW0 : (fun r => Real.sqrt 8 * U r) 0 = 0 := by simp [hU0]
  set K : ℝ := RS.koebeStepConst ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hc0 : 0 ≤ c := by linarith
  have hA0 : 0 ≤ 8 * K * c * max C 0 := by positivity
  have hB0 : 0 ≤ Real.sqrt 5 * (k₀ : ℝ) ^ β := by
    have := Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) k₀) β
    positivity
  refine ⟨8 * K * c * max C 0 + Real.sqrt 5 * (k₀ : ℝ) ^ β, fun k hk t ht => ?_⟩
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hkβ : 0 ≤ (k : ℝ) ^ (-β) := Real.rpow_nonneg hk0.le _
  rcases le_or_gt k₀ k with h | h
  · -- large `k`: Lemma 1, Theorem 2, Corollary 1 at scale `k + 2`, and the Koebe transfer
    have h1 := normalizedDeriv_le_barInv hU hU0 k ht.1
    have h2 := hk₀ (k + 2) (by omega) t ht
    have h3 : ((k + 2 : ℕ) : ℝ) ^ (-β) ≤ (k : ℝ) ^ (-β) :=
      Real.rpow_le_rpow_of_nonpos hk0 (by push_cast; linarith) (by linarith)
    calc normalizedDeriv (fun r => Real.sqrt 8 * U r) k t
        ≤ 4 * K * (alHeight (k + 2) *
            ‖deriv (barInv U t) ((alHeight (k + 2) : ℂ) * I)‖) := h1
      _ ≤ 4 * K * (2 * c * max C 0 * ((k + 2 : ℕ) : ℝ) ^ (-β)) := by gcongr
      _ ≤ 4 * K * (2 * c * max C 0 * (k : ℝ) ^ (-β)) := by gcongr
      _ = 8 * K * c * max C 0 * (k : ℝ) ^ (-β) := by ring
      _ ≤ (8 * K * c * max C 0 + Real.sqrt 5 * (k₀ : ℝ) ^ β) * (k : ℝ) ^ (-β) := by
          gcongr
          linarith
  · -- the finitely many small `k`: `A_k(t) ≤ √5` (Lemma 2.2)
    have h1 := normalizedDeriv_le_sqrt_five hW hW0 k ht
    have h2 : (k : ℝ) ^ β ≤ (k₀ : ℝ) ^ β :=
      Real.rpow_le_rpow hk0.le (by exact_mod_cast h.le) hβ.le
    have h3 : (k : ℝ) ^ β * (k : ℝ) ^ (-β) = 1 := by
      rw [← Real.rpow_add hk0, add_neg_cancel, Real.rpow_zero]
    have h4 : 1 ≤ (k₀ : ℝ) ^ β * (k : ℝ) ^ (-β) := by
      rw [← h3]
      exact mul_le_mul_of_nonneg_right h2 hkβ
    calc normalizedDeriv (fun r => Real.sqrt 8 * U r) k t ≤ Real.sqrt 5 := h1
      _ ≤ Real.sqrt 5 * ((k₀ : ℝ) ^ β * (k : ℝ) ^ (-β)) :=
          le_mul_of_one_le_right (Real.sqrt_nonneg 5) h4
      _ = Real.sqrt 5 * (k₀ : ℝ) ^ β * (k : ℝ) ^ (-β) := by ring
      _ ≤ (8 * K * c * max C 0 + Real.sqrt 5 * (k₀ : ℝ) ^ β) * (k : ℝ) ^ (-β) := by
          gcongr
          linarith

/-! ## Borel–Cantelli and Lemma 2.1 -/

/-- **Corollary 1 and Borel–Cantelli** (proof of Lemma 2.1): if
`∑_{n ≥ 1} ∑_{j ≤ 4^n} P(|F̄'_{j 4^{-n}}(i 2^{-n})| ≥ 2^n n^{-β'}) < ∞` for the drivers `U ω`, then
almost surely `D_k ≤ 2^k k^{-β'}` for all large `k`. -/
theorem ae_eventually_derivGridMax_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (U : Ω → ℝ → ℝ) {β' : ℝ}
    (hsum : ∑' n : ℕ, ∑ j ∈ Finset.range (4 ^ (n + 1) + 1),
      P {ω | (2 : ℝ) ^ (n + 1) * ((n : ℝ) + 1) ^ (-β') ≤
        ‖deriv (barInv (U ω) (alTime (n + 1) j)) ((alHeight (n + 1) : ℂ) * I)‖} ≠ ∞) :
    ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop, derivGridMax (U ω) k ≤ (2 : ℝ) ^ k * (k : ℝ) ^ (-β') := by
  set E : ℕ → Set Ω := fun n => ⋃ j ∈ Finset.range (4 ^ (n + 1) + 1),
    {ω | (2 : ℝ) ^ (n + 1) * ((n : ℝ) + 1) ^ (-β') ≤
      ‖deriv (barInv (U ω) (alTime (n + 1) j)) ((alHeight (n + 1) : ℂ) * I)‖} with hEdef
  have hE : ∑' n, P (E n) ≠ ∞ :=
    ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum fun n => measure_biUnion_finset_le _ _)
  filter_upwards [ae_eventually_notMem hE] with ω hω
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hω
  refine eventually_atTop.2 ⟨n₀ + 1, fun k hk => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have h := hn₀ n (by omega)
  simp only [hEdef, mem_iUnion, mem_ofPred_eq, not_exists, not_le] at h
  unfold derivGridMax
  refine Finset.sup'_le _ _ fun j hj => ?_
  push_cast
  exact (h j hj).le

/-- **Lemma 2.1 of the SLE₈ note (consequence of Alvisio–Lawler)**, from [AL14] Theorem 2 and the
convergent half of [AL14] Corollary 1 (stated as `AL14TheoremTwoStatement P` and
`AL14CorollaryOneStatement P`; [AL14] Lemma 1 is used as a proved result): for every Brownian motion
`B` on `(Ω, P)` and every `β ∈ (0, 1/4)`, almost surely there is a finite `C_β` with
`sup_{0 ≤ t ≤ 1} y_k |F_t'(i y_k)| ≤ C_β k^{-β}` for every `k ≥ 1`, where `F_t` is the centred
inverse Loewner map driven by `W = √8 B`. The conclusion is exactly the hypothesis `hL21` of
`ae_exists_continuous_trace_of_scale_count` (`Radial.lean`). -/
theorem lemma21_of_al14 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (hC1 : AL14CorollaryOneStatement P) (hT2 : AL14TheoremTwoStatement P)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (β : ℝ) (hβ : 0 < β) (hβ4 : β < 1 / 4) :
    ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k →
      ∀ t ∈ Icc (0 : ℝ) 1, normalizedDeriv (drive 8 B ω) k t ≤ C * (k : ℝ) ^ (-β) := by
  obtain ⟨B', hm, hc, h0, hB', hae⟩ := RS.exists_good_version0 hB
  set β' : ℝ := (β + 1 / 4) / 2 with hβ'def
  have hβ' : 0 < β' := by rw [hβ'def]; linarith
  have hβ'4 : β' < 1 / 4 := by rw [hβ'def]; linarith
  have hββ' : β < β' := by rw [hβ'def]; linarith
  obtain ⟨C, q, hT⟩ := hT2 B' hm hc h0 hB' (1 / 4) (by norm_num) alExp le_rfl
  have hD := ae_eventually_derivGridMax_le (P := P) (fun ω r => B' r.toNNReal ω)
    (hC1 B' hm hc h0 hB' β' hβ' hβ'4)
  filter_upwards [hT, hD, hae] with ω hTω hDω hω
  have hU : Continuous fun r : ℝ => B' r.toNNReal ω := (hc ω).comp continuous_real_toNNReal
  have hU0 : (fun r : ℝ => B' r.toNNReal ω) 0 = 0 := by simp [h0 ω]
  obtain ⟨C', hC'⟩ := exists_normalizedDeriv_le_of_eventually hU hU0 le_rfl hβ hββ' hβ4 hDω hTω
  have hdr : drive 8 B ω = fun r => Real.sqrt 8 * B' r.toNNReal ω := by
    funext r
    simp only [drive, hω]
  exact ⟨C', fun k hk t ht => by rw [hdr]; exact hC' k hk t ht⟩

end InteractingSLE.SLE8
