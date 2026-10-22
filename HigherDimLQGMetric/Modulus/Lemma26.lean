import HigherDimLQGMetric.Modulus.OneBall
import HigherDimLQGMetric.Modulus.Grid

/-!
# [S] Lemma 2.6: the uniform upper modulus, sharp class (packet W3b)

Source: [S] Lemma 2.6 (l. 385–447), completed in MA1 Details (a) **A8** (with the midpoint fix of
the covering step, erratum E-8); blueprint Part A `lem:2-6`. The diameter-moment input (E5) enters
through the orchestrator's interface `E5SharpMoment d ξ Q D` (`Core/Interfaces`, proved by packet
W3; the assembly discharges it).

* `lemma26_modulus_rate`: for `0 < α < s < ξ(Q − √(2d))` and `L > 0` there is `C` with
  `P[∃ x, y ∈ B_{LR}: |x − y| ≤ εR, D_h(x, y) > ε^α s_R(0)] ≤ C ε^{(ξQ − s)²/(2ξ²) − d}`
  for all `R > 0`, `ε ∈ (0, 1)` (outer measure; uniform in `R`);
* `lemma26_modulus`: MA1's probe with the extra hypothesis `hE5`, **with a real exponent**
  `∃ a > (0 : ℝ)` (see the note below);
* `lemma26_modulus_nat`: MA1's literal probe (`a : ℕ`) under `α < ξ(Q − √(2d + 2))`, the range where
  the natural-exponent form holds.

**Note on the statement (W3b STOP report).** In MA1's probe (`MA1Surface.lean.txt`, l. 706–714) the
binder `∃ a > 0` has no type ascription; Lean elaborates it with `a : ℕ` (`ε ^ a` is then
`Monoid.npow`), i.e. it claims a decay `C ε^a` with an integer exponent `a ≥ 1`. That is stronger
than [S] Lemma 2.6 and MA1 A8 (`a = θ − d > 0` real, which tends to `0` as `α ↑ ξ(Q − √(2d))`), and
it is false for α close to the threshold whenever a sharp assignment exists (thick points: the
probability is at least of order `ε^{(ξQ − α)²/(2ξ²) − d + o(1)}`, whose exponent is `< 1` for
`α > ξ(Q − √(2d + 2))`). The corrected form, proved here, writes `∃ a > (0 : ℝ)`; everything else is
MA1's probe verbatim.

Proof (MA1 A8). Fix `s = (α + ξ(Q − √(2d)))/2`, `p = (ξQ − s)/ξ²`, `t = εR`. Step 1–2:
`w3b_oneBall_moment` and Markov: `P[s_R(0)⁻¹ sup_{B̄_t(w)} D_h > ε^s] ≤ C₁ (2ε)^{ξQp−ξ²p²/2}/ε^{sp}`
for `|w| ≤ (L+1)R`. Step 3: union bound over the grid (`≤ (16d(L+1)+5)^d ε^{-d}` points). Step 4: on
the complement, `D_h(x,y) ≤ 2 ε^s s_R(0) ≤ ε^α s_R(0)` for `ε ≤ ε₀`
(`w3b_apply_le_two_mul_of_grid`); for `ε > ε₀` the bound is trivial with `C ≥ ε₀^{-a}`. The exponent
is `ξQp − ξ²p²/2 − sp − d = (ξQ − s)²/(2ξ²) − d > 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ}

/-- The decay exponent `(ξQ − s)²/(2ξ²) − d` is positive for `s < ξ(Q − √(2d))`. -/
theorem w3b_exponent_pos {ξ Q s : ℝ} (hξ : 0 < ξ) (d : ℕ)
    (hs : s < ξ * (Q - Real.sqrt (2 * d))) : 0 < (ξ * Q - s) ^ 2 / (2 * ξ ^ 2) - d := by
  have hsq : 0 ≤ Real.sqrt (2 * d) := Real.sqrt_nonneg _
  have h1 : ξ * Real.sqrt (2 * d) < ξ * Q - s := by nlinarith
  have h2 : (ξ * Real.sqrt (2 * d)) ^ 2 < (ξ * Q - s) ^ 2 :=
    pow_lt_pow_left₀ h1 (by positivity) two_ne_zero
  have h3 : (ξ * Real.sqrt (2 * d)) ^ 2 = ξ ^ 2 * (2 * d) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  rw [sub_pos, lt_div_iff₀ (by positivity)]
  nlinarith

/-- `ε ≤ (1/2)^{1/(s−α)}` gives `2 ε^s ≤ ε^α` (absorbing the covering factor `2`). -/
theorem w3b_two_mul_rpow_le {α s ε : ℝ} (hαs : α < s) (hε : 0 < ε)
    (hle : ε ≤ (1 / 2 : ℝ) ^ (1 / (s - α))) : 2 * ε ^ s ≤ ε ^ α := by
  have hsa : 0 < s - α := by linarith
  have h1 : ε ^ (s - α) ≤ 1 / 2 := by
    calc ε ^ (s - α) ≤ ((1 / 2 : ℝ) ^ (1 / (s - α))) ^ (s - α) :=
          Real.rpow_le_rpow hε.le hle hsa.le
      _ = 1 / 2 := by
          rw [← Real.rpow_mul (by norm_num), div_mul_cancel₀ 1 hsa.ne', Real.rpow_one]
  have h2 : ε ^ s = ε ^ (s - α) * ε ^ α := by
    rw [← Real.rpow_add hε]
    congr 1
    ring
  have h3 : 0 < ε ^ α := Real.rpow_pos_of_pos hε _
  rw [h2]
  nlinarith

/-- **[S] Lemma 2.6 with an explicit rate** (MA1 A8): for `0 < α < s < ξ(Q − √(2d))` and `L > 0`,
uniformly in `R > 0` and `ε ∈ (0,1)`,
`P[∃ x, y ∈ B_{LR}: |x − y| ≤ εR, D_h(x,y) > ε^α s_R(0)] ≤ C ε^{(ξQ − s)²/(2ξ²) − d}`. -/
theorem lemma26_modulus_rate (hd : 2 ≤ d) {ξ Q : ℝ} (hξ : 0 < ξ)
    {D : DistRd d → ContMetric d} (hD : IsSharpWeakExpMetric d ξ Q D)
    (hE5 : E5SharpMoment d ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    {α s : ℝ} (hα : 0 < α) (hαs : α < s) (hs : s < ξ * (Q - Real.sqrt (2 * d)))
    (L : ℝ) (hL : 0 < L) :
    ∃ C : ℝ, ∀ R : ℝ, 0 < R → ∀ ε ∈ Ioo (0 : ℝ) 1,
      P {ω | ∃ x y : Rd d, ‖x‖ < L * R ∧ ‖y‖ < L * R ∧ ‖x - y‖ ≤ ε * R ∧
        ε ^ α * sNorm ξ Q (h ω) R 0 < (D (h ω)).1 (x, y)} ≤
        ENNReal.ofReal (C * ε ^ ((ξ * Q - s) ^ 2 / (2 * ξ ^ 2) - d)) := by
  have hW : IsWeakExpMetric d ξ D (fun r => r ^ (ξ * Q)) := hD
  have hd1 : 1 ≤ d := by omega
  have hsqrt : 0 ≤ Real.sqrt (2 * d) := Real.sqrt_nonneg _
  have hs0 : 0 < s := hα.trans hαs
  have hsQ : s < ξ * Q := by nlinarith [mul_nonneg hξ.le hsqrt]
  set p : ℝ := (ξ * Q - s) / ξ ^ 2 with hp_def
  have hp : 0 < p := div_pos (by linarith) (by positivity)
  have hpQ : p < Q / ξ := by
    rw [hp_def, div_lt_div_iff₀ (by positivity) hξ]
    nlinarith
  obtain ⟨C₁, hC₁, hone⟩ :=
    w3b_oneBall_moment hd hξ hD hE5 hp hpQ (A := L + 1) (by linarith)
  set e₁ : ℝ := ξ * Q * p - ξ ^ 2 * p ^ 2 / 2 with he₁
  set ex : ℝ := (ξ * Q - s) ^ 2 / (2 * ξ ^ 2) - d with hex
  have hexpo : e₁ - s * p = (ξ * Q - s) ^ 2 / (2 * ξ ^ 2) := by
    rw [he₁, hp_def]
    field_simp
    ring
  have hex_pos : 0 < ex := w3b_exponent_pos hξ d hs
  set ε₀ : ℝ := min (1 / 2) ((1 / 2 : ℝ) ^ (1 / (s - α))) with hε₀
  have hε₀pos : 0 < ε₀ := lt_min (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)
  set K : ℝ := (16 * d * (L + 1) + 5) ^ d * C₁ * 2 ^ e₁ with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K + (ε₀ ^ ex)⁻¹, fun R hR ε hε => ?_⟩
  obtain ⟨hε0, hε1⟩ := hε
  by_cases hεε₀ : ε₀ < ε
  · -- large `ε`: the bound is trivial
    calc P _ ≤ 1 := prob_le_one
      _ ≤ ENNReal.ofReal ((K + (ε₀ ^ ex)⁻¹) * ε ^ ex) := by
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        have h1 : ε₀ ^ ex ≤ ε ^ ex := Real.rpow_le_rpow hε₀pos.le hεε₀.le hex_pos.le
        have h2 : 0 < ε₀ ^ ex := Real.rpow_pos_of_pos hε₀pos _
        have h3 : 0 ≤ K * ε ^ ex := by positivity
        calc (1 : ℝ) = (ε₀ ^ ex)⁻¹ * ε₀ ^ ex := (inv_mul_cancel₀ h2.ne').symm
          _ ≤ (ε₀ ^ ex)⁻¹ * ε ^ ex := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 h2.le)
          _ ≤ (K + (ε₀ ^ ex)⁻¹) * ε ^ ex := by nlinarith
  · -- small `ε`: grid, Markov, union bound
    replace hεε₀ : ε ≤ ε₀ := not_lt.1 hεε₀
    have hε12 : ε ≤ 1 / 2 := hεε₀.trans (min_le_left _ _)
    have hεs : 2 * ε ^ s ≤ ε ^ α := w3b_two_mul_rpow_le hαs hε0 (hεε₀.trans (min_le_right _ _))
    have hεs0 : 0 < ε ^ s := Real.rpow_pos_of_pos hε0 _
    set t : ℝ := ε * R with ht_def
    have ht : 0 < t := by positivity
    have h2t : 2 * t ≤ R := by rw [ht_def]; nlinarith
    set Y : Rd d → Ω → ℝ≥0∞ := fun w ω =>
      ENNReal.ofReal (sNorm ξ Q (h ω) R 0)⁻¹ * w3bBallDiam (D (h ω)) w t with hY
    -- Step 4: the event is covered by the grid events
    have hsub : {ω | ∃ x y : Rd d, ‖x‖ < L * R ∧ ‖y‖ < L * R ∧ ‖x - y‖ ≤ ε * R ∧
        ε ^ α * sNorm ξ Q (h ω) R 0 < (D (h ω)).1 (x, y)} ⊆
        ⋃ w ∈ w3bGrid d L R ε, {ω | ENNReal.ofReal (ε ^ s) < Y w ω} := by
      intro ω hω
      obtain ⟨x, y, hx, hy, hxy, hlt⟩ := hω
      by_contra hnot
      have hall : ∀ w ∈ w3bGrid d L R ε,
          ENNReal.ofReal (sNorm ξ Q (h ω) R 0)⁻¹ * w3bBallDiam (D (h ω)) w (ε * R) ≤
            ENNReal.ofReal (ε ^ s) := by
        intro w hw
        by_contra hc
        exact hnot (mem_iUnion₂.2 ⟨w, hw, lt_of_not_ge hc⟩)
      have hS : 0 < sNorm ξ Q (h ω) R 0 := by
        unfold sNorm
        positivity
      have hle := w3b_apply_le_two_mul_of_grid hd1 hL hR hε0 hε1.le hS hεs0.le hall hx hy hxy
      have : 2 * ε ^ s * sNorm ξ Q (h ω) R 0 ≤ ε ^ α * sNorm ξ Q (h ω) R 0 :=
        mul_le_mul_of_nonneg_right hεs hS.le
      linarith
    -- Steps 1–2: Markov for each grid ball
    have hmarkov : ∀ w ∈ w3bGrid d L R ε, P {ω | ENNReal.ofReal (ε ^ s) < Y w ω} ≤
        ENNReal.ofReal (C₁ * (2 * ε) ^ e₁ / ε ^ (s * p)) := by
      intro w hw
      have hwn : ‖w‖ ≤ (L + 1) * R := (w3b_norm_lt_of_mem_grid hw).le
      have hint := hone P h hh ht h2t w hwn
      have h2tR : 2 * t / R = 2 * ε := by
        rw [ht_def]
        field_simp
      rw [h2tR] at hint
      have hmeasS : Measurable fun ω => sNorm ξ Q (h ω) R 0 := by
        unfold sNorm
        exact measurable_const.mul (Real.measurable_exp.comp
          (((measurable_sphereAvg_left R 0).comp hh.measurable).const_mul ξ))
      have hmeasY : Measurable (Y w) :=
        hmeasS.inv.ennreal_ofReal.mul
          (w3b_measurable_ballDiam (hW.measurable.comp hh.measurable) w t)
      have hc0 : ENNReal.ofReal (ε ^ s) ^ p ≠ 0 :=
        (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 hεs0) ENNReal.ofReal_ne_top).ne'
      have hctop : ENNReal.ofReal (ε ^ s) ^ p ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top
      calc P {ω | ENNReal.ofReal (ε ^ s) < Y w ω}
          ≤ P {ω | ENNReal.ofReal (ε ^ s) ^ p ≤ Y w ω ^ p} :=
            measure_mono fun ω hω => ENNReal.rpow_le_rpow (le_of_lt hω) hp.le
        _ ≤ (∫⁻ ω, Y w ω ^ p ∂P) / ENNReal.ofReal (ε ^ s) ^ p :=
            meas_ge_le_lintegral_div (hmeasY.pow_const p).aemeasurable hc0 hctop
        _ ≤ ENNReal.ofReal (C₁ * (2 * ε) ^ e₁) / ENNReal.ofReal (ε ^ s) ^ p :=
            ENNReal.div_le_div_right hint _
        _ = ENNReal.ofReal (C₁ * (2 * ε) ^ e₁ / ε ^ (s * p)) := by
            rw [ENNReal.ofReal_rpow_of_nonneg hεs0.le hp.le, ← Real.rpow_mul hε0.le,
              ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hε0 _)]
    -- Step 3: union bound and counting
    have hB : 0 ≤ C₁ * (2 * ε) ^ e₁ / ε ^ (s * p) := by positivity
    have hcard := w3b_card_grid_le (d := d) hd1 hL hR hε0 hε1.le
    have hexeq : ε ^ ex = ε ^ e₁ / ε ^ (s * p) / ε ^ d := by
      rw [hex, ← hexpo, Real.rpow_sub hε0, Real.rpow_sub hε0, Real.rpow_natCast]
    have hmain : (16 * d * (L + 1) + 5) ^ d / ε ^ d * (C₁ * (2 * ε) ^ e₁ / ε ^ (s * p)) =
        K * ε ^ ex := by
      rw [hexeq, hK, Real.mul_rpow (by norm_num) hε0.le]
      have : 0 < ε ^ d := pow_pos hε0 d
      have : 0 < ε ^ (s * p) := Real.rpow_pos_of_pos hε0 _
      field_simp
    calc P {ω | ∃ x y : Rd d, ‖x‖ < L * R ∧ ‖y‖ < L * R ∧ ‖x - y‖ ≤ ε * R ∧
          ε ^ α * sNorm ξ Q (h ω) R 0 < (D (h ω)).1 (x, y)}
        ≤ P (⋃ w ∈ w3bGrid d L R ε, {ω | ENNReal.ofReal (ε ^ s) < Y w ω}) := measure_mono hsub
      _ ≤ ∑ w ∈ w3bGrid d L R ε, P {ω | ENNReal.ofReal (ε ^ s) < Y w ω} :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _w ∈ w3bGrid d L R ε, ENNReal.ofReal (C₁ * (2 * ε) ^ e₁ / ε ^ (s * p)) :=
          Finset.sum_le_sum hmarkov
      _ = ENNReal.ofReal ((w3bGrid d L R ε).card * (C₁ * (2 * ε) ^ e₁ / ε ^ (s * p))) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ((K + (ε₀ ^ ex)⁻¹) * ε ^ ex) := by
          apply ENNReal.ofReal_le_ofReal
          calc ((w3bGrid d L R ε).card : ℝ) * (C₁ * (2 * ε) ^ e₁ / ε ^ (s * p))
              ≤ (16 * d * (L + 1) + 5) ^ d / ε ^ d * (C₁ * (2 * ε) ^ e₁ / ε ^ (s * p)) :=
                mul_le_mul_of_nonneg_right hcard hB
            _ = K * ε ^ ex := hmain
            _ ≤ (K + (ε₀ ^ ex)⁻¹) * ε ^ ex := by
                have : 0 ≤ (ε₀ ^ ex)⁻¹ * ε ^ ex := by positivity
                nlinarith

/-- **[S] Lemma 2.6 (uniform upper modulus), sharp class** (MA1 A8; MA1's probe `lemma26_modulus`
with the interface hypothesis `hE5` and the exponent typed as a real number, `∃ a > (0 : ℝ)`): for
`0 < α < ξ(Q − √(2d))` and `L > 0` there are `a > 0` and `C` with
`P[∃ x, y ∈ B_{LR}: |x − y| ≤ εR, D_h(x,y) > ε^α s_R(0)] ≤ C ε^a` for all `R > 0`, `ε ∈ (0,1)`. -/
theorem lemma26_modulus (hd : 3 ≤ d) {ξ Q : ℝ} (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    {D : DistRd d → ContMetric d} (hD : IsSharpWeakExpMetric d ξ Q D)
    (hE5 : E5SharpMoment d ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    (α : ℝ) (hα : 0 < α) (hα' : α < ξ * (Q - Real.sqrt (2 * d))) (L : ℝ) (hL : 0 < L) :
    ∃ a > (0 : ℝ), ∃ C : ℝ, ∀ R : ℝ, 0 < R → ∀ ε ∈ Ioo (0 : ℝ) 1,
      P {ω | ∃ x y : Rd d, ‖x‖ < L * R ∧ ‖y‖ < L * R ∧ ‖x - y‖ ≤ ε * R ∧
        ε ^ α * sNorm ξ Q (h ω) R 0 < (D (h ω)).1 (x, y)} ≤ ENNReal.ofReal (C * ε ^ a) := by
  -- `hQ` is implied by `hα`, `hα'` (kept for fidelity with MA1's probe)
  have _hQ' : 0 < Q - Real.sqrt (2 * d) := sub_pos.2 hQ
  have hαs : α < (α + ξ * (Q - Real.sqrt (2 * d))) / 2 := by linarith
  have hs : (α + ξ * (Q - Real.sqrt (2 * d))) / 2 < ξ * (Q - Real.sqrt (2 * d)) := by linarith
  obtain ⟨C, hC⟩ := lemma26_modulus_rate (by omega) hξ hD hE5 P h hh hα hαs hs L hL
  exact ⟨_, w3b_exponent_pos hξ d hs, C, hC⟩

/-- **MA1's literal probe (natural exponent) in the range where it holds.** Without a type
ascription `∃ a > 0` elaborates with `a : ℕ`. That form holds (with `a = 1`) when
`α < ξ(Q − √(2d + 2))`: then some `s ∈ (α, ξ(Q − √(2d+2)))` has decay exponent
`(ξQ − s)²/(2ξ²) − d > 1`. For `α ∈ (ξ(Q − √(2d+2)), ξ(Q − √(2d)))` it fails whenever a sharp
assignment exists (the thick-point lower bound `ε^{(ξQ − α)²/(2ξ²) − d + o(1)}` decays slower than
`ε`), so `lemma26_modulus` uses `a : ℝ`. -/
theorem lemma26_modulus_nat (hd : 3 ≤ d) {ξ Q : ℝ} (hξ : 0 < ξ)
    {D : DistRd d → ContMetric d} (hD : IsSharpWeakExpMetric d ξ Q D)
    (hE5 : E5SharpMoment d ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    (α : ℝ) (hα : 0 < α) (hα' : α < ξ * (Q - Real.sqrt (2 * d + 2))) (L : ℝ) (hL : 0 < L) :
    ∃ a > 0, ∃ C : ℝ, ∀ R : ℝ, 0 < R → ∀ ε ∈ Ioo (0 : ℝ) 1,
      P {ω | ∃ x y : Rd d, ‖x‖ < L * R ∧ ‖y‖ < L * R ∧ ‖x - y‖ ≤ ε * R ∧
        ε ^ α * sNorm ξ Q (h ω) R 0 < (D (h ω)).1 (x, y)} ≤ ENNReal.ofReal (C * ε ^ a) := by
  set s : ℝ := (α + ξ * (Q - Real.sqrt (2 * d + 2))) / 2 with hs_def
  have hαs : α < s := by linarith
  have hs2 : s < ξ * (Q - Real.sqrt (2 * d + 2)) := by linarith
  have hsqrt : Real.sqrt (2 * d) < Real.sqrt (2 * d + 2) :=
    Real.sqrt_lt_sqrt (by positivity) (by linarith)
  have hs : s < ξ * (Q - Real.sqrt (2 * d)) := by nlinarith
  obtain ⟨C, hC⟩ := lemma26_modulus_rate (by omega) hξ hD hE5 P h hh hα hαs hs L hL
  have hex : 1 ≤ (ξ * Q - s) ^ 2 / (2 * ξ ^ 2) - d := by
    have h0 : 0 ≤ Real.sqrt (2 * d + 2) := Real.sqrt_nonneg _
    have h1 : ξ * Real.sqrt (2 * d + 2) < ξ * Q - s := by nlinarith
    have h2 : (ξ * Real.sqrt (2 * d + 2)) ^ 2 < (ξ * Q - s) ^ 2 :=
      pow_lt_pow_left₀ h1 (by positivity) two_ne_zero
    have h3 : (ξ * Real.sqrt (2 * d + 2)) ^ 2 = ξ ^ 2 * (2 * d + 2) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    rw [le_sub_iff_add_le, le_div_iff₀ (by positivity)]
    nlinarith
  refine ⟨1, one_pos, max C 0, fun R hR ε hε => (hC R hR ε hε).trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  have hle : ε ^ ((ξ * Q - s) ^ 2 / (2 * ξ ^ 2) - d) ≤ ε ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hε.1 hε.2.le hex
  rw [Real.rpow_one] at hle
  have hpos : 0 ≤ ε ^ ((ξ * Q - s) ^ 2 / (2 * ξ ^ 2) - d) := Real.rpow_nonneg hε.1.le _
  rw [pow_one]
  calc C * ε ^ ((ξ * Q - s) ^ 2 / (2 * ξ ^ 2) - d)
      ≤ max C 0 * ε ^ ((ξ * Q - s) ^ 2 / (2 * ξ ^ 2) - d) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
    _ ≤ max C 0 * ε := mul_le_mul_of_nonneg_left hle (le_max_right _ _)

end HigherDimLQGMetric
