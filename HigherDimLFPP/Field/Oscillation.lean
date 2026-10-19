import HigherDimLFPP.Field.OscBlock
import HigherDimLFPP.Field.RootAverage

/-!
# The oscillation of the cutoff field (packet P-OSC, target T1)

Source: `source/higher-dimensional-lfpp-limit.pdf`, Lemma 4.1 ("Moreover": `ω_ε = o_P(log 1/ε)`);
planning audit HA3, Details D3 (b) and its Lean statement `OscillationBound` in (c).

For a continuous version `H` of `H_{ε,b}` (any upper cutoff `b`) let
`ω = Upper.osc H (5ε)` be its oscillation at distance `5ε` on `closure U`.

* `Osc.osc_event` (deterministic): if `ω > 2t`, then for some point `g` of the grid of mesh `ε` in
  `[-2,2]^d` (at most `(4/ε + 1)^d` points) some `z ∈ B̄(g, (5 + √d) ε)` has `|H z - H g| > t`.
* `Osc.osc_measure_le` (quantitative form of HA3 D3 (b)): with the block bound `Osc.block_tail`
  and a union bound,
  `P*(ω > 2 (C + s)) ≤ (4/ε + 1)^d e^{-c s²}` for all `s ≥ 0`, with explicit `C = Osc.oscConst d L`
  and `c = Osc.oscRate d L`, `L` the constant of the increment bound
  `‖k_z - k_w‖² ≤ L ‖z - w‖²/ε²` (`exists_norm_bandVec_sub_sq_le`).  (The factor `2` of the
  two-sided block bound is absorbed in `C`.)
* `exists_osc_measure_le`: the same with constants `C ≥ 0`, `c > 0` depending only on `κ` and `d`.
* `osc_tendsto` (target T1): for every `c > 0`,
  `P*(c log(1/ε) < ω_ε) → 0` as `ε ↓ 0`, for continuous versions `H ε` of `H_{ε,1}`.
* `Upper.OscillationBound`, `Upper.oscillationBound`: HA3's node statement (Lemma 4.1,
  probabilistic part: `ω_ε(5ε) = o_P(log 1/ε)` and `H_root = O_P(1)`), stated with the frozen
  field model of ruling H10 (white noise and continuous versions), and proved from `osc_tendsto`
  and `segAvg_cutoff_bounded` (`HigherDimLFPP.Field.RootAverage`, target T2).

All probabilities of possibly non-measurable events are outer measures (`P S`), as in HA3 (c).

2D template: `LQGDimension/LFPP/OscillationAux.lean` (`Osc37.osc_event`, `osc_prob_le`,
`osc_tendsto`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open scoped RealInnerProductSpace

namespace HigherDimLFPP

namespace Osc

variable {d : ℕ}

/-- `0 ∈ U`. -/
theorem zero_mem_cube : (0 : Rd d) ∈ cube d := fun i => by
  simp only [PiLp.zero_apply, abs_zero]
  norm_num

/-- If the oscillation at distance `5ε` exceeds `2t`, some block of the grid of mesh `ε` has an
increment exceeding `t`. -/
theorem osc_event {φ : Rd d → ℝ} {ε t : ℝ} (hε : 0 < ε) (h : 2 * t < Upper.osc φ (5 * ε)) :
    ∃ g ∈ grid 0 2 ε, ∃ z ∈ closedBall g ((5 + √(d : ℝ)) * ε), t < |φ z - φ g| := by
  unfold Upper.osc at h
  have hne : {v | ∃ z w : Rd d, z ∈ closure (cube d) ∧ w ∈ closure (cube d) ∧
      ‖z - w‖ ≤ 5 * ε ∧ v = |φ z - φ w|}.Nonempty :=
    ⟨_, 0, 0, subset_closure zero_mem_cube, subset_closure zero_mem_cube,
      by rw [sub_self, norm_zero]; positivity, rfl⟩
  obtain ⟨v, ⟨z, w, hz, -, hzw, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hne h
  have hzB : z ∈ box 0 2 := closure_cube_subset_box hz
  refine ⟨gridOf 0 2 ε z, gridOf_mem_grid 0 hε hzB, ?_⟩
  set g := gridOf 0 2 ε z
  have hzg : ‖z - g‖ ≤ √(d : ℝ) * ε := norm_sub_gridOf_le 0 hε hzB
  have htri : |φ z - φ w| ≤ |φ z - φ g| + |φ w - φ g| := by
    have := abs_sub_le (φ z) (φ g) (φ w)
    rwa [abs_sub_comm (φ g) (φ w)] at this
  by_cases h1 : t < |φ z - φ g|
  · refine ⟨z, ?_, h1⟩
    rw [mem_closedBall, dist_eq_norm]
    have : 0 ≤ 5 * ε := by positivity
    linarith
  · refine ⟨w, ?_, by linarith⟩
    rw [mem_closedBall, dist_eq_norm]
    calc ‖w - g‖ ≤ ‖w - z‖ + ‖z - g‖ := norm_sub_le_norm_sub_add_norm_sub w z g
      _ ≤ 5 * ε + √(d : ℝ) * ε := by rw [norm_sub_rev w z]; linarith
      _ = (5 + √(d : ℝ)) * ε := by ring

/-- The block radius (in units of `ε`) of the oscillation bound. -/
def oscRadius (d : ℕ) : ℝ := 5 + √(d : ℝ)

/-- `oscRadius d > 0`. -/
theorem oscRadius_pos (d : ℕ) : 0 < oscRadius d := by
  unfold oscRadius
  positivity

/-- The constant `C` of the oscillation bound: the chaining constant of a block plus the shift
absorbing the factor `2` of the two-sided block tail. -/
def oscConst (d : ℕ) (L : ℝ) : ℝ :=
  blockConst d L (oscRadius d) + oscRadius d * √L * √(2 * Real.log 2)

/-- The rate `c = 1 / (2 r² L)` of the oscillation bound. -/
def oscRate (d : ℕ) (L : ℝ) : ℝ := 1 / (2 * (oscRadius d ^ 2 * L))

/-- `oscConst d L ≥ 0`. -/
theorem oscConst_nonneg (d : ℕ) (L : ℝ) : 0 ≤ oscConst d L := by
  unfold oscConst
  have := blockConst_nonneg d (L := L) (oscRadius_pos d).le
  have := oscRadius_pos d
  positivity

/-- `oscRate d L > 0` for `L > 0`. -/
theorem oscRate_pos (d : ℕ) {L : ℝ} (hL : 0 < L) : 0 < oscRate d L := by
  unfold oscRate
  have := oscRadius_pos d
  positivity

/-- `2 e^{-(s + δ)²/(2σ²)} ≤ e^{-s²/(2σ²)}` for `δ = σ √(2 log 2)`. -/
theorem two_mul_exp_le {σ s : ℝ} (hσ : 0 < σ) (hs : 0 ≤ s) :
    2 * Real.exp (-(s + σ * √(2 * Real.log 2)) ^ 2 / (2 * σ ^ 2)) ≤
      Real.exp (-s ^ 2 / (2 * σ ^ 2)) := by
  set δ := σ * √(2 * Real.log 2) with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hδ2 : δ ^ 2 = σ ^ 2 * (2 * Real.log 2) := by
    rw [hδ, mul_pow, Real.sq_sqrt (by positivity)]
  have hexp : -(s + δ) ^ 2 / (2 * σ ^ 2) ≤ -s ^ 2 / (2 * σ ^ 2) + -Real.log 2 := by
    have h1 : s ^ 2 + δ ^ 2 ≤ (s + δ) ^ 2 := by nlinarith
    have h2 : -(s + δ) ^ 2 / (2 * σ ^ 2) ≤ -(s ^ 2 + δ ^ 2) / (2 * σ ^ 2) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have h3 : -(s ^ 2 + δ ^ 2) / (2 * σ ^ 2) = -s ^ 2 / (2 * σ ^ 2) + -Real.log 2 := by
      rw [hδ2]
      field_simp
      ring
    linarith
  calc 2 * Real.exp (-(s + δ) ^ 2 / (2 * σ ^ 2))
      ≤ 2 * Real.exp (-s ^ 2 / (2 * σ ^ 2) + -Real.log 2) := by gcongr
    _ = Real.exp (-s ^ 2 / (2 * σ ^ 2)) := by
        rw [Real.exp_add, Real.exp_neg, Real.exp_log two_pos]
        field_simp

section Field

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ} {κ : Rd d → ℝ}

/-- **Quantitative oscillation bound** (HA3 D3 (b)), with the explicit constants of the increment
bound `‖k_z - k_w‖² ≤ L ‖z - w‖²/ε²` (`L > 0`): for every continuous version `H` of `H_{ε,b}`
and `s ≥ 0`,
`P*(osc_{closure U} H (5ε) > 2 (oscConst d L + s)) ≤ (4/ε + 1)^d e^{-oscRate d L · s²}`. -/
theorem osc_measure_le (hW : IsWhiteNoise P W) {ε b : ℝ} (hε : 0 < ε) {H : Rd d → Ω → ℝ}
    (hH : IsBandVersion P W κ ε b H) {L : ℝ} (hL0 : 0 < L)
    (hL : ∀ z w : Rd d, ‖bandVec κ ε b z - bandVec κ ε b w‖ ^ 2 ≤ L * ‖z - w‖ ^ 2 / ε ^ 2)
    {s : ℝ} (hs : 0 ≤ s) :
    P {ω | 2 * (oscConst d L + s) < Upper.osc (fun z => H z ω) (5 * ε)} ≤
      ENNReal.ofReal ((4 / ε + 1) ^ d * Real.exp (-oscRate d L * s ^ 2)) := by
  set r := oscRadius d with hr
  have hr0 : 0 < r := oscRadius_pos d
  set σ := r * √L with hσ
  have hσ0 : 0 < σ := by positivity
  have hσ2 : σ ^ 2 = r ^ 2 * L := by rw [hσ, mul_pow, Real.sq_sqrt hL0.le]
  set u := s + σ * √(2 * Real.log 2) with hu
  have hu0 : 0 ≤ u := by positivity
  have hCu : oscConst d L + s = blockConst d L r + u := by
    rw [hu, oscConst, ← hr, ← hσ]
    ring
  have hsub : {ω | 2 * (oscConst d L + s) < Upper.osc (fun z => H z ω) (5 * ε)} ⊆
      ⋃ g ∈ grid 0 2 ε,
        {ω | ∃ z ∈ closedBall g (r * ε), blockConst d L r + u < |H z ω - H g ω|} := by
    intro ω hω
    obtain ⟨g, hg, z, hz, hlt⟩ := osc_event (φ := fun z => H z ω)
      (t := blockConst d L r + u) hε (by rw [← hCu]; exact hω)
    exact mem_iUnion₂.2 ⟨g, hg, z, hz, hlt⟩
  have hblock : ∀ g, P {ω | ∃ z ∈ closedBall g (r * ε), blockConst d L r + u < |H z ω - H g ω|} ≤
      ENNReal.ofReal (Real.exp (-s ^ 2 / (2 * σ ^ 2))) := by
    intro g
    refine (block_tail hW hε hH hL0.le hL g hr0.le hu0).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [← hσ2]
    exact two_mul_exp_le hσ0 hs
  have hcard := card_grid_le (0 : Rd d) (R := 2) (by norm_num) hε
  have hrate : -oscRate d L * s ^ 2 = -s ^ 2 / (2 * σ ^ 2) := by
    rw [oscRate, ← hr, hσ2]
    field_simp
  calc P {ω | 2 * (oscConst d L + s) < Upper.osc (fun z => H z ω) (5 * ε)}
      ≤ P (⋃ g ∈ grid 0 2 ε,
          {ω | ∃ z ∈ closedBall g (r * ε), blockConst d L r + u < |H z ω - H g ω|}) :=
        measure_mono hsub
    _ ≤ ∑ g ∈ grid 0 2 ε,
          P {ω | ∃ z ∈ closedBall g (r * ε), blockConst d L r + u < |H z ω - H g ω|} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _g ∈ grid (0 : Rd d) 2 ε, ENNReal.ofReal (Real.exp (-s ^ 2 / (2 * σ ^ 2))) :=
        Finset.sum_le_sum fun g _ => hblock g
    _ = ENNReal.ofReal ((grid (0 : Rd d) 2 ε).card * Real.exp (-s ^ 2 / (2 * σ ^ 2))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((4 / ε + 1) ^ d * Real.exp (-oscRate d L * s ^ 2)) := by
        rw [hrate]
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
        refine hcard.trans (le_of_eq ?_)
        ring

end Field

end Osc

open Osc

variable {d : ℕ}

/-- **Quantitative oscillation bound** (HA3 D3 (b)) with constants depending only on `κ` and `d`:
there are `C ≥ 0` and `c > 0` such that for every white noise `W`, every `ε > 0`, every `b`, every
continuous version `H` of `H_{ε,b}` and every `s ≥ 0`,
`P*(osc_{closure U} H (5ε) > 2 (C + s)) ≤ (4/ε + 1)^d e^{-c s²}`. -/
theorem exists_osc_measure_le {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ},
        IsWhiteNoise P W → ∀ {ε b : ℝ}, 0 < ε → ∀ {H : Rd d → Ω → ℝ},
          IsBandVersion P W κ ε b H → ∀ {s : ℝ}, 0 ≤ s →
            P {ω | 2 * (C + s) < Upper.osc (fun z => H z ω) (5 * ε)} ≤
              ENNReal.ofReal ((4 / ε + 1) ^ d * Real.exp (-c * s ^ 2)) := by
  obtain ⟨L, hL0, hL⟩ := exists_norm_bandVec_sub_sq_le hκ
  have hL1 : 0 < L + 1 := by linarith
  refine ⟨oscConst d (L + 1), oscRate d (L + 1), oscConst_nonneg d _, oscRate_pos d hL1, ?_⟩
  intro Ω _ P W hW ε b hε H hH s hs
  refine osc_measure_le hW hε hH hL1 (fun z w => (hL ε hε b z w).trans ?_) hs
  gcongr
  linarith

/-- **Target T1** (HA3 D3 (b); Lemma 4.1 "Moreover"): for continuous versions `H ε` of `H_{ε,1}`,
`ω_ε = osc_{closure U} (H ε) (5ε) = o_P(log 1/ε)`: for every `c > 0`,
`P*(c log(1/ε) < ω_ε) → 0` as `ε ↓ 0`.  (In fact `P*(c log(1/ε) < ω_ε) ≤ 5^d ε` for small `ε`.) -/
theorem osc_tendsto {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
    {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) {H : ℝ → Rd d → Ω → ℝ}
    (hH : ∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun ε => P {ω | c * Real.log (1 / ε) < Upper.osc (fun z => H ε z ω) (5 * ε)})
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, c₀, hC0, hc₀, hbound⟩ := exists_osc_measure_le (d := d) hκ
  set L₁ : ℝ := max (4 * C / c) (16 * ((d : ℝ) + 1) / (c₀ * c ^ 2)) with hL₁
  have hL₁0 : 0 ≤ L₁ := le_max_of_le_left (by positivity)
  set ε₁ := Real.exp (-L₁) with hε₁def
  have hε₁ : 0 < ε₁ := Real.exp_pos _
  have hε₁1 : ε₁ ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hmain : ∀ ε ∈ Ioo 0 ε₁,
      P {ω | c * Real.log (1 / ε) < Upper.osc (fun z => H ε z ω) (5 * ε)} ≤
        ENNReal.ofReal (5 ^ d * ε) := by
    rintro ε ⟨hε0, hεε₁⟩
    set x := Real.log (1 / ε) with hx
    have hxe : x = -Real.log ε := by rw [hx, one_div, Real.log_inv]
    have hLx : L₁ < x := by
      have := Real.log_lt_log hε0 hεε₁
      rw [hε₁def, Real.log_exp] at this
      linarith
    have hx0 : 0 ≤ x := by linarith
    have h4C : 4 * C / c ≤ x := (le_max_left _ _).trans hLx.le
    have h16 : 16 * ((d : ℝ) + 1) / (c₀ * c ^ 2) ≤ x := (le_max_right _ _).trans hLx.le
    rw [div_le_iff₀ hc] at h4C
    rw [div_le_iff₀ (by positivity)] at h16
    set s := c * x / 2 - C with hs
    have hs4 : c * x / 4 ≤ s := by linarith
    have hs0 : 0 ≤ s := le_trans (by positivity) hs4
    have hε1 : ε < 1 := lt_of_lt_of_le hεε₁ hε₁1
    have h := hbound hW hε0 (hH ε ⟨hε0, hε1⟩) hs0
    have e2 : 2 * (C + s) = c * Real.log (1 / ε) := by rw [hs, ← hx]; ring
    rw [e2] at h
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have h45 : 4 / ε + 1 ≤ 5 / ε := by
      rw [div_add_one hε0.ne', div_le_div_iff_of_pos_right hε0]
      linarith
    have hpow : (4 / ε + 1) ^ d ≤ (5 / ε) ^ d := pow_le_pow_left₀ (by positivity) h45 d
    have hexp1 : (5 / ε) ^ d = 5 ^ d * Real.exp (d * x) := by
      have e : 1 / ε = Real.exp x := by rw [hx, Real.exp_log (by positivity)]
      rw [Real.exp_nat_mul, ← e, div_eq_mul_one_div 5 ε, mul_pow]
    have hexp2 : Real.exp (-c₀ * s ^ 2) ≤ Real.exp (-((d : ℝ) + 1) * x) := by
      refine Real.exp_le_exp.2 ?_
      have h1 : (c * x / 4) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (by positivity) hs4 2
      have h2 : ((d : ℝ) + 1) * x ≤ c₀ * (c * x / 4) ^ 2 := by
        have e : c₀ * (c * x / 4) ^ 2 = x * (x * (c₀ * c ^ 2)) / 16 := by ring
        rw [e, le_div_iff₀ (by norm_num : (0 : ℝ) < 16)]
        have := mul_le_mul_of_nonneg_left h16 hx0
        linarith
      have h3 : c₀ * (c * x / 4) ^ 2 ≤ c₀ * s ^ 2 := mul_le_mul_of_nonneg_left h1 hc₀.le
      linarith
    have hεx : Real.exp (-x) = ε := by rw [hxe, neg_neg, Real.exp_log hε0]
    calc (4 / ε + 1) ^ d * Real.exp (-c₀ * s ^ 2)
        ≤ (5 / ε) ^ d * Real.exp (-((d : ℝ) + 1) * x) :=
          mul_le_mul hpow hexp2 (Real.exp_pos _).le (by positivity)
      _ = 5 ^ d * (Real.exp (d * x) * Real.exp (-((d : ℝ) + 1) * x)) := by rw [hexp1]; ring
      _ = 5 ^ d * ε := by rw [← Real.exp_add, ← hεx]; ring_nf
  have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal (5 ^ d * ε)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun ε : ℝ => 5 ^ d * ε) (𝓝 0) (𝓝 0) := by
      have h := (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul ((5 : ℝ) ^ d)
      rw [mul_zero] at h
      exact h
    have h2 := (ENNReal.tendsto_ofReal h1).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [Ioo_mem_nhdsGT hε₁] with ε hε
  exact hmain ε hε

namespace Upper

/-- **Lemma 4.1, probabilistic part** (HA3 (c) `OscillationBound`, with the frozen field model of
ruling H10): for every admissible kernel, white noise `W` and continuous versions `H ε` of
`H_{ε,1}` (`ε ∈ (0,1)`), `ω_ε(5ε) = o_P(log 1/ε)` and `H_root = ⟨H ε, ν_{[0,e₁]}⟩ = O_P(1)`
uniformly in `ε` (outer measures). -/
def OscillationBound (d : ℕ) [NeZero d] : Prop :=
  ∀ κ : Rd d → ℝ, IsLFPPKernel κ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ), IsWhiteNoise P W →
    ∀ H : ℝ → Rd d → Ω → ℝ, (∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) →
      (∀ c > 0, Tendsto (fun ε => P {ω | c * Real.log (1 / ε) <
          osc (fun z => H ε z ω) (5 * ε)}) (𝓝[>] 0) (𝓝 0)) ∧
      ∀ θ > 0, ∃ M : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1,
        P {ω | M < |segAvg (fun z => H ε z ω) 0 (e₁ d)|} ≤ ENNReal.ofReal θ

/-- **Lemma 4.1, probabilistic part**, proved (targets T1 and T2). -/
theorem oscillationBound (d : ℕ) [NeZero d] : OscillationBound d := by
  intro κ hκ Ω _ P W hW H hH
  exact ⟨fun c hc => osc_tendsto hκ hW hH hc, fun θ hθ => segAvg_cutoff_bounded hκ hW hH hθ⟩

end Upper

end HigherDimLFPP
