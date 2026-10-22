import HigherDimLQGMetric.Sec9.Claim32Grid
import HigherDimLQGMetric.ScaleBin.Lemma81
import HigherDimLQGMetric.Modulus.Lemma26
import HigherDimLQGMetric.Sharp.W3Tail
import HigherDimLQGMetric.Field.LGFPlusCont

/-!
# Claim (32) of [S] §9 (packet S8e; MA4 Details (a) A17)

Source: [S] §9, l. 1434–1475; MA4 §1.3 item 12, §1.7 (parameter order P0–P8), Details (a) A17;
planning draft `planning/drafts/S7b-S8-plan.md` §3 (S8e, steps 1–10); ruling M35.

**Target.** `claim32_of (hP86 : Prop86Stmt) (hMR : ∀ d ξ Q, 2 ≤ d → MacroRatioShape d ξ Q) :
Claim32Stmt`: for two sharp weak assignments `D, D̃` with the a.s. comparison
`c_* D ≤ D̃ ≤ C_* D` (`0 < c_* ≤ C_*`), the conclusions of `sec6Package_of_sharp` (`TrapFamily`,
`ConfigLocal`, `Cor63`) and `p_*, ℓ₊, β₊ > 0`, for **every** whole-space LGF `h` there is a
deterministic `t ∈ (0, C_*)` such that `P[H⁺_R(t)] < p_*` at every scale `R > 0` satisfying (19)
(`P[H⁻_R(1/c₀)] ≥ p_*`).

**Proof** (MA4 A17, for the fixed LGF; the modulus constants of Lemma 2.6 depend on the LGF,
E-P89-1):
1. Lemma 7.2 (`lemma72`): trap datum `T`, covering failure `≤ C₇ ε` for `R` with (19), `ε < ε₇`.
2. Lemma 8.1 (`lemma81`): bin exponent `B`, bin failure `≤ C₈ ε^{a₈}` for `ε < 1/3`.
3. (33) (`hMR` at `δ = p_*/10`): `L ≥ 1` with `P[L S < s_R(0)] ≤ p_*/10` for every `R`.
4. Lemma 2.6 (`lemma26_modulus`, `L = 3`, `α = ξ(Q − √(2d))/2`, (E5) from `e5_sharp_moment`):
   the modulus failure at scale `e` is `≤ C₂ e^{a₂}`.
5. `β = min(β₊, ℓ₊/2, ℓ₊⁻¹, 1)`, `ν = (B + 2)/α + 1` (`να > B + 2`); D-H (v)
   (`s6b_witEvent_subset_gEvent`) turns `H⁺_R(t)` into a ratio event with `D(x, y) ≤ β⁻¹ s_R(0)`.
6. Proposition 8.6 (`hP86`) at `η = β/2`, `N = 2νd + 2`: `C_N`, `ε₁`.
7. One `ε` (`s8e_exists_eps`); the grid scale is `e = ε^ν`.
8. `t := C_* − β ε^{B+1}/(4L)` ((34) with `ℓ₊` replaced by `β⁻¹`, E-P89-2).
9. For each `R` with (19): `h⁻¹' H⁺_R(t)` lies in the union of the covering/bin failure, the (33)
   failure, the modulus failure, a null set (length metrics and `D̃ ≤ C_* D`), and the events
   `𝒜^ε_R ∩ (27)(x′, y′)` over grid pairs (`s8e_gridPair_of_witEvent`).
10. Outer-measure subadditivity (`s8e_measure_lt`): the total is
    `< 2p_*/5 + p_*/10 + p_*/5 + p_*/5 < p_*`; the grid count `≤ (K_g/ε^{νd})²` cancels against
    `C_N ε^N = C_N ε^{2νd+2}` (`s8e_rpow_grid`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)
open scoped ENNReal

/-- **Claim (32)** ([S] §9, l. 1434–1475; MA4 A17), from Proposition 8.6 (`Prop86Stmt`, S7b's
export) and the macro-normalizer bound (33) (`MacroRatioShape`, S8d's export). -/
theorem claim32_of (hP86 : Prop86Stmt)
    (hMR : ∀ (d : ℕ) (ξ Q : ℝ), 2 ≤ d → MacroRatioShape d ξ Q) : Claim32Stmt := by
  intro d hd ξ Q hξ hQ D Dt hD hDt cs Cs c0 c1 aL A₀L ℓL β₀L aU A₀U ℓU β₀U pstar
    hcs hcsCs hpstar hℓU hβ₀U hcomp hTrap hLoc hCor Ω _ P _ h hh
  have hd1 : 1 ≤ d := by omega
  have hCs : 0 < Cs := lt_of_lt_of_le hcs hcsCs
  -- Step 1: Lemma 7.2 (trap datum, covering event)
  obtain ⟨T, C₇, ε₇, hε₇, hcov⟩ := lemma72 hd hξ hQ hTrap hLoc hCor
  -- Step 2: Lemma 8.1 (bin exponent, bin event)
  have hQpos : 0 < Q := lt_of_le_of_lt (Real.sqrt_nonneg _) hQ
  obtain ⟨B, a₈, C₈, hB, ha₈, hbin⟩ := lemma81 hd hξ hQpos
  -- Step 3: (33)
  obtain ⟨L, hL1, hmac⟩ := hMR d ξ Q (by omega) (pstar / 10) (by positivity)
  have hL : 0 < L := lt_of_lt_of_le one_pos hL1
  -- Step 4: Lemma 2.6 (upper modulus on `B_{3R}`) for the fixed LGF
  have hgap : 0 < Q - Real.sqrt (2 * d) := sub_pos.2 hQ
  obtain ⟨α, hα_def⟩ : ∃ α : ℝ, α = ξ * (Q - Real.sqrt (2 * d)) / 2 := ⟨_, rfl⟩
  have hξgap : 0 < ξ * (Q - Real.sqrt (2 * d)) := mul_pos hξ hgap
  have hα : 0 < α := by rw [hα_def]; positivity
  have hα' : α < ξ * (Q - Real.sqrt (2 * d)) := by rw [hα_def]; linarith
  obtain ⟨a₂, ha₂, C₂, hmod⟩ := lemma26_modulus hd hξ hQ hD (e5_sharp_moment hd hξ hQ hD)
    P h hh α hα hα' 3 (by norm_num)
  -- Step 5: `β`, `ν`
  obtain ⟨β, hβ_def⟩ : ∃ β : ℝ, β = min (min β₀U (ℓU / 2)) (min ℓU⁻¹ 1) := ⟨_, rfl⟩
  have hβ : 0 < β := by
    rw [hβ_def]
    exact lt_min (lt_min hβ₀U (by positivity)) (lt_min (inv_pos.2 hℓU) one_pos)
  have hββ₀ : β ≤ β₀U := by rw [hβ_def]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hβℓ : β ≤ ℓU / 2 := by rw [hβ_def]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hβℓ' : β ≤ ℓU⁻¹ := by rw [hβ_def]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hβ1 : β ≤ 1 := by rw [hβ_def]; exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨ν, hν_def⟩ : ∃ ν : ℝ, ν = (B + 2) / α + 1 := ⟨_, rfl⟩
  have hν : 0 < ν := by rw [hν_def]; positivity
  have hνα : B + 1 < ν * α := by
    have h1 : (B + 2) / α * α = B + 2 := div_mul_cancel₀ _ hα.ne'
    have h2 : ν * α = B + 2 + α := by rw [hν_def, add_mul, h1, one_mul]
    linarith
  -- Step 6: Proposition 8.6 at `η = β/2`, `N = 2νd + 2`
  obtain ⟨N, hN_def⟩ : ∃ N : ℝ, N = 2 * ν * d + 2 := ⟨_, rfl⟩
  have hN : 0 < N := by rw [hN_def]; positivity
  obtain ⟨CN, ε₁, hε₁, hP⟩ := hP86 d hd hξ hQ hD hDt hcs hcsCs hcomp T hB (β / 2)
    (by positivity) (by linarith) N hN
  -- Step 7: one `ε`
  obtain ⟨Kg, hKg_def⟩ : ∃ Kg : ℝ, Kg = (16 * (d : ℝ) * (3 + 1) + 5) ^ d := ⟨_, rfl⟩
  obtain ⟨ε, hε, hε₇', hε₁', hε3, hεν, hεmod, hεt, hs7, hs8, hs2, hsN⟩ :=
    s8e_exists_eps (L := L) (C₇ := max C₇ 0) (C₈ := max C₈ 0) (C₂ := max C₂ 0)
      (K := Kg ^ 2 * max CN 0) hε₇ hε₁ hCs hβ hB hν hνα ha₈ ha₂ hpstar
  have hq : 0 < ε ^ (B + 1) := Real.rpow_pos_of_pos hε _
  have hgapt : 0 < β * ε ^ (B + 1) / (4 * L) := div_pos (mul_pos hβ hq) (by positivity)
  -- Step 8: `t := C_* − β ε^{B+1}/(4L)`
  refine ⟨Cs - β * ε ^ (B + 1) / (4 * L), sub_pos.2 hεt, sub_lt_self _ hgapt, ?_⟩
  intro R hR h19
  have he0 : 0 < ε ^ ν := Real.rpow_pos_of_pos hε _
  have he1 : ε ^ ν < 1 := Real.rpow_lt_one hε.le (by linarith) hν
  -- Step 9: the inclusion
  have hsub : h ⁻¹' WitEvent D Dt ξ Q Cs aU A₀U ℓU β₀U (Cs - β * ε ^ (B + 1) / (4 * L)) R 0 ⊆
      {ω | h ω ∉ sec8AEvent D Dt ξ Q T.J T.N B ε R} ∪
      {ω | L * macroS ξ Q (h ω) R < sNorm ξ Q (h ω) R 0} ∪
      {ω | ∃ x y : Rd d, ‖x‖ < 3 * R ∧ ‖y‖ < 3 * R ∧ ‖x - y‖ ≤ ε ^ ν * R ∧
        (ε ^ ν) ^ α * sNorm ξ Q (h ω) R 0 < (D (h ω)).1 (x, y)} ∪
      {ω | ¬ ((D (h ω)).IsLength ∧ (Dt (h ω)).IsLength ∧
        ∀ u v : Rd d, (Dt (h ω)).1 (u, v) ≤ Cs * (D (h ω)).1 (u, v))} ∪
      ⋃ p ∈ ((w3bGrid d 3 R (ε ^ ν)) ×ˢ (w3bGrid d 3 R (ε ^ ν))).filter
          (fun p : Rd d × Rd d => ‖p.1‖ < 3 * R ∧ ‖p.2‖ < 3 * R ∧ β / 2 * R ≤ ‖p.1 - p.2‖),
        {ω | h ω ∈ sec8AEvent D Dt ξ Q T.J T.N B ε R ∧
          sec8C1 D Dt ξ Q Cs (ε ^ (B + 1)) R p.1 p.2 (h ω)} := by
    intro ω hω
    by_cases h0 : h ω ∈ sec8AEvent D Dt ξ Q T.J T.N B ε R
    swap
    · exact Or.inl (Or.inl (Or.inl (Or.inl h0)))
    by_cases h1 : L * macroS ξ Q (h ω) R < sNorm ξ Q (h ω) R 0
    · exact Or.inl (Or.inl (Or.inl (Or.inr h1)))
    by_cases h2 : ∃ x y : Rd d, ‖x‖ < 3 * R ∧ ‖y‖ < 3 * R ∧ ‖x - y‖ ≤ ε ^ ν * R ∧
        (ε ^ ν) ^ α * sNorm ξ Q (h ω) R 0 < (D (h ω)).1 (x, y)
    · exact Or.inl (Or.inl (Or.inr h2))
    by_cases h3 : (D (h ω)).IsLength ∧ (Dt (h ω)).IsLength ∧
        ∀ u v : Rd d, (Dt (h ω)).1 (u, v) ≤ Cs * (D (h ω)).1 (u, v)
    swap
    · exact Or.inl (Or.inr h3)
    refine Or.inr ?_
    have hmod' : ∀ x y : Rd d, ‖x‖ < 3 * R → ‖y‖ < 3 * R → ‖x - y‖ ≤ ε ^ ν * R →
        (D (h ω)).1 (x, y) ≤ (ε ^ ν) ^ α * sNorm ξ Q (h ω) R 0 := by
      intro x y hx hy hxy
      by_contra hcon
      exact h2 ⟨x, y, hx, hy, hxy, not_le.1 hcon⟩
    obtain ⟨p, hp, hpC⟩ := s8e_gridPair_of_witEvent (D := D) (Dt := Dt) (aU := aU) (A₀U := A₀U)
      hd1 hR hℓU hβ hββ₀ hβℓ hβℓ' hCs.le hL hq.le he0 he1.le hεν (by ring) hεmod
      (not_lt.1 h1) hmod' h3.1 h3.2.1 h3.2.2 hω
    exact Set.mem_iUnion₂.2 ⟨p, hp, h0, hpC⟩
  -- Step 10: the union bound
  refine s8e_measure_lt (x0 := max C₇ 0 * ε + max C₈ 0 * ε ^ a₈)
    (x2 := max C₂ 0 * (ε ^ ν) ^ a₂) (xN := max CN 0 * ε ^ N)
    hsub ?_ (hmac P h hh R hR) ?_ ?_ ?_ ?_ (by positivity) ?_ ?_ ?_
  · -- covering and bin failures
    have hsplit : {ω | h ω ∉ sec8AEvent D Dt ξ Q T.J T.N B ε R} ⊆
        {ω | h ω ∉ sec8CoverEvent D Dt ξ Q T.J T.N ε R} ∪
          {ω | h ω ∉ sec8BinEvent d ξ Q B ε R} := by
      intro ω hω
      by_contra hcon
      simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hcon
      exact hω ⟨hcon.1, hcon.2⟩
    have hc : P {ω | h ω ∉ sec8CoverEvent D Dt ξ Q T.J T.N ε R} ≤ ENNReal.ofReal (C₇ * ε) :=
      hcov P h hh R hR h19 ε hε hε₇'
    have hb : P {ω | h ω ∉ sec8BinEvent d ξ Q B ε R} ≤ ENNReal.ofReal (C₈ * ε ^ a₈) := by
      refine le_trans (le_of_eq ?_) (hbin P h hh R hR ε ⟨hε, hε3⟩)
      congr 1
      ext ω
      simp only [sec8BinEvent, mem_ofPred_eq, not_forall, exists_prop]
    calc P {ω | h ω ∉ sec8AEvent D Dt ξ Q T.J T.N B ε R}
        ≤ P {ω | h ω ∉ sec8CoverEvent D Dt ξ Q T.J T.N ε R} +
            P {ω | h ω ∉ sec8BinEvent d ξ Q B ε R} :=
          (measure_mono hsplit).trans (measure_union_le _ _)
      _ ≤ ENNReal.ofReal (max C₇ 0 * ε) + ENNReal.ofReal (max C₈ 0 * ε ^ a₈) := by
          gcongr
          · exact hc.trans (ENNReal.ofReal_le_ofReal
              (mul_le_mul_of_nonneg_right (le_max_left _ _) hε.le))
          · exact hb.trans (ENNReal.ofReal_le_ofReal
              (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hε.le _)))
      _ = ENNReal.ofReal (max C₇ 0 * ε + max C₈ 0 * ε ^ a₈) :=
          (ENNReal.ofReal_add (mul_nonneg (le_max_right _ _) hε.le)
            (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hε.le _))).symm
  · -- modulus failure
    exact (hmod R hR (ε ^ ν) ⟨he0, he1⟩).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg he0.le _)))
  · -- the null event: length metrics and `D̃ ≤ C_* D`
    have hW : IsWeakExpMetric d ξ D (fun r => r ^ (ξ * Q)) := hD
    have hWt : IsWeakExpMetric d ξ Dt (fun r => r ^ (ξ * Q)) := hDt
    refine ae_iff.1 ?_
    filter_upwards [hW.length P h hh.isLGFPlusCont, hWt.length P h hh.isLGFPlusCont,
      hcomp P h hh] with ω h1 h2 h3
    exact ⟨h1, h2, fun u v => (h3 u v).2⟩
  · -- the grid pairs: Proposition 8.6
    intro p hp
    obtain ⟨-, hp1, hp2, hp3⟩ := Finset.mem_filter.1 hp
    exact (hP P h hh R hR p.1 p.2 hp1 hp2 hp3 ε hε hε₁').trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hε.le _)))
  · exact add_nonneg (mul_nonneg (le_max_right _ _) hε.le)
      (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hε.le _))
  · exact mul_nonneg (le_max_right _ _) (Real.rpow_nonneg he0.le _)
  · exact mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hε.le _)
  · -- the final sum
    have hcard := s8e_card_gridPairs_le hd1 hR he0 he1.le
      (fun p : Rd d × Rd d => ‖p.1‖ < 3 * R ∧ ‖p.2‖ < 3 * R ∧ β / 2 * R ≤ ‖p.1 - p.2‖)
    rw [← hKg_def] at hcard
    have hed : (ε ^ ν) ^ d ≠ 0 := pow_ne_zero _ he0.ne'
    have hxN : ((((w3bGrid d 3 R (ε ^ ν)) ×ˢ (w3bGrid d 3 R (ε ^ ν))).filter
          (fun p : Rd d × Rd d => ‖p.1‖ < 3 * R ∧ ‖p.2‖ < 3 * R ∧
            β / 2 * R ≤ ‖p.1 - p.2‖)).card : ℝ) * (max CN 0 * ε ^ N) ≤
        Kg ^ 2 * max CN 0 * ε ^ (2 : ℝ) := by
      calc _ ≤ (Kg / (ε ^ ν) ^ d) ^ 2 * (max CN 0 * ε ^ N) :=
            mul_le_mul_of_nonneg_right hcard
              (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hε.le _))
        _ = Kg ^ 2 * max CN 0 * ε ^ (2 : ℝ) := by
            rw [hN_def, s8e_rpow_grid hε ν d]
            field_simp
    linarith

end HigherDimLQGMetric
