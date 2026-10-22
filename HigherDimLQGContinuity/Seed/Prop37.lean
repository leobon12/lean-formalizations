import HigherDimLQGContinuity.Seed.Prop36
import HigherDimLQGContinuity.Seed.Prop37Seed

/-!
# Proposition 3.7: the increment bound, and `Prop37Shape` (packet P8b)

Blueprint Part A, Proposition `a:prop37` ([C] Prop. 3.7, p. 10, l. 486–501; NA1 item 29, R12; NA0 §2.3, §2.5;
erratum EA `a:err-37`) and Part C, Lemma `c:lem-p37` (NA4 §6.3 item 2, F5.2e; interface I16).

**Statements.**
* `prop37`: let `d ≥ 2`, assume Lemma 2.1 (`UniformEstimates d ξ̄ s`, interface I1) for all pins `s ∈ [1, 10]` and
  Proposition 3.5 (`Prop35Shape d ξ̄`, interface I15). For each `R ≥ 1` there are `B, M₇, C₇, c₇ > 0` such that for
  all `a ∈ (0, ξ̄]`, `ξ, η ∈ [a, ξ̄]`, `D, E` strong, `δ ∈ (0, 1/8)` and `n` with
  `|ξ − η| ≤ e^{-C₇ a^{-B} δ^{-B}}`, `n ≥ C₇ δ^{-M₇} log(C₇/δ)` and `|ξ − η| n ≤ c₇ δ`:
  `𝐏{g : supd_R(log(1 + ρ^D_g), log(1 + ρ^E_g)) > δ} ≤ C₇ δ^{-M₇} e^{-c₇ δ^{M₇} n}` (the blueprint's event
  `∃ x, y ∈ B̄_R, |log(1 + ρ^D(x, y)) − log(1 + ρ^E(x, y))| > δ`, by `p8b_logEvent_eq`).
* `prop37Shape_of` (interface I16, Part C `c:lem-p37`): for `d ≥ 3`, from `Prop35Shape d ξ̄` and
  `UniformEstimates d ξ̄ s` (`s ∈ [1, 10]`) at every positive subcritical `ξ̄`, `Prop37Shape d` holds.

**Proofs.** `prop37` (blueprint): take `R_s` of Proposition 3.6 and `p_s, c'` of `prop37_of_seed` (`c' ≤ 1`);
Proposition 3.6 with this `p_s` and `u = c'δ ∈ (0, 1)` gives the seed whenever
`τ ≤ exp(-C₆ a^{-B} (c'δ)^{-B})`, which holds if `τ ≤ e^{-C₇ a^{-B} δ^{-B}}` with `C₇ ≥ C₆ c'^{-B}`; then
`prop37_of_seed`. `prop37Shape_of` (Part C `c:lem-p37`; IA1's scratch `ia_prop37Shape_of_partA`): under (G) apply
`prop37`, under (S) apply `prop37_of_seed` at `R_s = 1`; `M = max(M₇, M₇')`, `C = max(C₇, C₇', 1)`,
`c = min(c₇, c₇', 1)` (both conclusions are monotone in `(M, C, c)` for `δ < 1/8`, `p8b_const_mono`), and
`p_s := min(p_s, 1/2) < 1` (IA1's remark: `Prop37Shape` asks `p_s < 1`; the seed premise only gets stronger).
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

/-- **Monotonicity of the constants** (Part C `c:lem-p37`, last sentence; IA1's `ia_mono`): for `δ < 1/8` the depth
condition `C δ^{-M} log(C/δ) ≤ n` gets weaker and the bound `C δ^{-M} e^{-c δ^M n}` gets larger when `M, C` decrease and
`c` increases (`1 ≤ C`). -/
theorem p8b_const_mono {δ n M C c M₁ C₁ c₁ : ℝ} (hδ : 0 < δ) (hδ8 : δ < 1 / 8) (hC₁ : 0 < C₁) (hc : 0 < c)
    (hMM : M₁ ≤ M) (hCC : C₁ ≤ C) (hC1 : 1 ≤ C) (hcc : c ≤ c₁)
    (hn : C * δ ^ (-M) * Real.log (C / δ) ≤ n) :
    C₁ * δ ^ (-M₁) * Real.log (C₁ / δ) ≤ n ∧
      C₁ * δ ^ (-M₁) * Real.exp (-(c₁ * δ ^ M₁ * n)) ≤ C * δ ^ (-M) * Real.exp (-(c * δ ^ M * n)) := by
  have hδ1 : δ ≤ 1 := by linarith
  have hpow : δ ^ (-M₁) ≤ δ ^ (-M) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hpow' : δ ^ M ≤ δ ^ M₁ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hMM
  have hp0 : 0 < δ ^ (-M₁) := Real.rpow_pos_of_pos hδ _
  have hp1 : 0 < δ ^ (-M) := Real.rpow_pos_of_pos hδ _
  have hq0 : 0 ≤ δ ^ M := (Real.rpow_pos_of_pos hδ _).le
  have hCδ : 1 < C / δ := by rw [lt_div_iff₀ hδ]; linarith
  have hlogC : 0 < Real.log (C / δ) := Real.log_pos hCδ
  have hnpos : 0 < n := lt_of_lt_of_le (by positivity) hn
  refine ⟨?_, ?_⟩
  · rcases le_or_gt (Real.log (C₁ / δ)) 0 with hle | hlt
    · have : C₁ * δ ^ (-M₁) * Real.log (C₁ / δ) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hle
      linarith
    · have hlog : Real.log (C₁ / δ) ≤ Real.log (C / δ) :=
        Real.log_le_log (div_pos hC₁ hδ) (div_le_div_of_nonneg_right hCC hδ.le)
      calc C₁ * δ ^ (-M₁) * Real.log (C₁ / δ) ≤ C * δ ^ (-M) * Real.log (C / δ) := by
            apply mul_le_mul (mul_le_mul hCC hpow hp0.le (by linarith)) hlog hlt.le (by positivity)
        _ ≤ n := hn
  · have hexp : Real.exp (-(c₁ * δ ^ M₁ * n)) ≤ Real.exp (-(c * δ ^ M * n)) := by
      apply Real.exp_le_exp.2
      have : c * δ ^ M ≤ c₁ * δ ^ M₁ := mul_le_mul hcc hpow' hq0 (by linarith)
      nlinarith
    exact mul_le_mul (mul_le_mul hCC hpow hp0.le (by linarith)) hexp (Real.exp_pos _).le (by positivity)

/-- **Proposition 3.7** (the increment bound; blueprint `a:prop37`; [C] Prop. 3.7; NA1 item 29, R12). -/
theorem prop37 (hd : 2 ≤ d) {ξbar : ℝ} (hU : ∀ s ∈ Icc (1 : ℝ) 10, UniformEstimates d ξbar s)
    (h35 : Prop35Shape d ξbar) :
    ∀ R : ℝ, 1 ≤ R → ∃ B M C c : ℝ, 0 < B ∧ 0 < M ∧ 0 < C ∧ 0 < c ∧
      ∀ a ∈ Ioc (0 : ℝ) ξbar, ∀ ξ ∈ Icc a ξbar, ∀ η ∈ Icc a ξbar, ∀ D E : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D → IsStrongExpMetric d η (distExp d η) E →
        ∀ δ : ℝ, 0 < δ → δ < 1 / 8 → ∀ n : ℝ,
          |ξ - η| ≤ Real.exp (-(C * a ^ (-B) * δ ^ (-B))) →
          C * δ ^ (-M) * Real.log (C / δ) ≤ n → |ξ - η| * n ≤ c * δ →
          normLGFLaw d {g | ENNReal.ofReal δ <
              supDistLU d R (logProfile (rho D g).1) (logProfile (rho E g).1)} ≤
            ENNReal.ofReal (C * δ ^ (-M) * Real.exp (-(c * δ ^ M * n))) := by
  obtain ⟨ps, cs, hps, hcs, hcs1, hS⟩ := prop37_of_seed hd hU
  obtain ⟨Rs, hRs, h36⟩ := prop36 hd hU h35
  obtain ⟨B, C₆, hB, hC₆, h36'⟩ := h36 ps hps
  intro R hR
  obtain ⟨M₇, C₇, c₇, hM₇, hC₇, hc₇, hS'⟩ := hS Rs R hRs hR
  set C : ℝ := max (max C₇ (C₆ * cs ^ (-B))) 1 with hCdef
  have hC1 : 1 ≤ C := le_max_right _ _
  have hC₇C : C₇ ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC₆C : C₆ * cs ^ (-B) ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  refine ⟨B, M₇, C, c₇, hB, hM₇, lt_of_lt_of_le one_pos hC1, hc₇, ?_⟩
  intro a ha ξ hξ η hη D E hD hE δ hδ hδ8 n hτ hn hdrift
  -- the seed from Proposition 3.6 at `u = c'δ`
  have hu : 0 < cs * δ := mul_pos hcs hδ
  have hu1 : cs * δ < 1 := by nlinarith
  have hτ' : |ξ - η| ≤ Real.exp (-(C₆ * a ^ (-B) * (cs * δ) ^ (-B))) := by
    refine hτ.trans (Real.exp_le_exp.2 ?_)
    rw [Real.mul_rpow hcs.le hδ.le]
    have hpos : 0 ≤ a ^ (-B) * δ ^ (-B) :=
      mul_nonneg (Real.rpow_pos_of_pos ha.1 _).le (Real.rpow_pos_of_pos hδ _).le
    have := mul_le_mul_of_nonneg_right hC₆C hpos
    have e1 : C₆ * a ^ (-B) * (cs ^ (-B) * δ ^ (-B)) = C₆ * cs ^ (-B) * (a ^ (-B) * δ ^ (-B)) := by ring
    have e2 : C * a ^ (-B) * δ ^ (-B) = C * (a ^ (-B) * δ ^ (-B)) := by ring
    rw [e1, e2]
    linarith
  have hseed := h36' a ha ξ hξ η hη D E hD hE (cs * δ) hu hu1 hτ'
  have hξ' : ξ ∈ Ioc (0 : ℝ) ξbar := ⟨lt_of_lt_of_le ha.1 hξ.1, hξ.2⟩
  have hη' : η ∈ Ioc (0 : ℝ) ξbar := ⟨lt_of_lt_of_le ha.1 hη.1, hη.2⟩
  obtain ⟨hdepth, hbound⟩ := p8b_const_mono (M₁ := M₇) (C₁ := C₇) (c₁ := c₇) hδ hδ8 hC₇ hc₇ le_rfl hC₇C
    hC1 le_rfl hn
  exact (hS' ξ hξ' η hη' D E hD hE δ hδ hδ8 n hseed hdepth hdrift).trans (ENNReal.ofReal_le_ofReal hbound)

/-- **`Prop37Shape d`** (interface I16; Part C `c:lem-p37`): Propositions 3.7 and 3.7-with-a-supplied-seed, merged into
one set of constants (seed at radius `R_s = 1`, `p_s < 1`). Hypotheses: the interfaces I15 (`Prop35Shape`, producer
Q11) and I1 (`UniformEstimates`, producer L4) at every positive subcritical `ξ̄`. -/
theorem prop37Shape_of {d : ℕ} (hd : 3 ≤ d)
    (h35 : ∀ ξbar : ℝ, 0 < ξbar → Real.sqrt (2 * d) < distExp d ξbar → Prop35Shape d ξbar)
    (hU : ∀ ξbar : ℝ, 0 < ξbar → Real.sqrt (2 * d) < distExp d ξbar →
      ∀ s : ℝ, 1 ≤ s → s ≤ 10 → UniformEstimates d ξbar s) :
    Prop37Shape d := by
  intro ξbar h0 hsub
  have hd2 : 2 ≤ d := by omega
  have hU' : ∀ s ∈ Icc (1 : ℝ) 10, UniformEstimates d ξbar s := fun s hs => hU ξbar h0 hsub s hs.1 hs.2
  obtain ⟨ps, cs, hps, hcs, -, hS⟩ := prop37_of_seed hd2 hU'
  have h37 := prop37 hd2 hU' (h35 ξbar h0 hsub)
  refine ⟨min ps (1 / 2), cs, lt_min hps (by norm_num), (min_le_right _ _).trans_lt (by norm_num), hcs,
    fun R hR => ?_⟩
  obtain ⟨M₁, C₁, c₁, hM₁, hC₁, hc₁, hS'⟩ := hS 1 R le_rfl hR
  obtain ⟨B, M₂, C₂, c₂, hB, hM₂, hC₂, hc₂, hG⟩ := h37 R hR
  have hcpos : 0 < min (min c₁ c₂) 1 := lt_min (lt_min hc₁ hc₂) one_pos
  refine ⟨B, max M₁ M₂, max (max C₁ C₂) 1, min (min c₁ c₂) 1, hB, lt_max_of_lt_left hM₁, hcpos,
    min_le_right _ _, le_max_right _ _, ?_⟩
  intro a ha ξ hξ η hη D E hD hE δ hδ hδ8 n hn hdrift hbranch
  have hC1 : 1 ≤ max (max C₁ C₂) 1 := le_max_right _ _
  have hδ0 : 0 ≤ δ := hδ.le
  rcases hbranch with hGb | hSb
  · -- (G): Proposition 3.7 with its constants
    obtain ⟨hdepth, hbound⟩ := p8b_const_mono (M₁ := M₂) (C₁ := C₂) (c₁ := c₂) hδ hδ8 hC₂ hcpos
      (le_max_right _ _) ((le_max_right _ _).trans (le_max_left _ _)) hC1
      ((min_le_left _ _).trans (min_le_right _ _)) hn
    have hG' : |ξ - η| ≤ Real.exp (-(C₂ * a ^ (-B) * δ ^ (-B))) := by
      refine hGb.trans (Real.exp_le_exp.2 ?_)
      have hpos : 0 ≤ a ^ (-B) * δ ^ (-B) :=
        mul_nonneg (Real.rpow_pos_of_pos ha.1 _).le (Real.rpow_pos_of_pos hδ _).le
      have hCC : C₂ ≤ max (max C₁ C₂) 1 := (le_max_right _ _).trans (le_max_left _ _)
      have := mul_le_mul_of_nonneg_right hCC hpos
      have e1 : C₂ * a ^ (-B) * δ ^ (-B) = C₂ * (a ^ (-B) * δ ^ (-B)) := by ring
      have e2 : max (max C₁ C₂) 1 * a ^ (-B) * δ ^ (-B) = max (max C₁ C₂) 1 * (a ^ (-B) * δ ^ (-B)) := by
        ring
      rw [e1, e2]
      linarith
    have hdr : |ξ - η| * n ≤ c₂ * δ := hdrift.trans (mul_le_mul_of_nonneg_right
      ((min_le_left _ _).trans (min_le_right _ _)) hδ0)
    exact (hG a ha ξ hξ η hη D E hD hE δ hδ hδ8 n hG' hdepth hdr).trans (ENNReal.ofReal_le_ofReal hbound)
  · -- (S): Proposition 3.7 with a supplied seed, at `R_s = 1`
    obtain ⟨hdepth, hbound⟩ := p8b_const_mono (M₁ := M₁) (C₁ := C₁) (c₁ := c₁) hδ hδ8 hC₁ hcpos
      (le_max_left _ _) ((le_max_left _ _).trans (le_max_left _ _)) hC1
      ((min_le_left _ _).trans (min_le_left _ _)) hn
    have hdr : |ξ - η| * n ≤ c₁ * δ := hdrift.trans (mul_le_mul_of_nonneg_right
      ((min_le_left _ _).trans (min_le_left _ _)) hδ0)
    have hξ' : ξ ∈ Ioc (0 : ℝ) ξbar := ⟨ha.1.trans_le hξ.1, hξ.2⟩
    have hη' : η ∈ Ioc (0 : ℝ) ξbar := ⟨ha.1.trans_le hη.1, hη.2⟩
    have hSb' : pinLaw d 10 {g | ENNReal.ofReal (cs * δ) < supDistLU d 1 (rho D g).1 (rho E g).1} ≤
        ENNReal.ofReal ps := hSb.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _))
    exact (hS' ξ hξ' η hη' D E hD hE δ hδ hδ8 n hSb' hdepth hdr).trans (ENNReal.ofReal_le_ofReal hbound)

end HigherDimLQGContinuity
