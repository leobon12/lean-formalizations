/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.TargetChangeProcessBrownianTC
import InteractingSLE.WangWu.CouplingFrozen

/-!
# `b̃` is a Brownian motion, part 6: the limit at the new horizon

Packet PROVE-SEC7-C9. When the new horizon `T̃` is finite, the new-time noise `bv0` has a limit as `u ↑ T̃`, almost
surely (`ae_tendsto_bv0`). This is the step "the a.s. limit of `N` at `S(τ_sep)`" of PROVE-SEC7-C8's plan.

**Abstract step** (`ae_osc_small`, the argument of PROVE-WW-A's `exists_martingale_frozenMean` with a horizon `U`):
for bounded continuous martingales `Y_n` consistent along nondecreasing stopping times `S_n`
(`Y_n = Y_m(· ∧ S_n)`, `n ≤ m`) with `E Y_n(U)² ≤ c`, the `L²` norms `a_n = E Y_n(U)²` increase (optional sampling:
`E(Y_m(U) − Y_n(U))² = a_m − a_n`) and converge, so Doob's weak-type maximal inequality makes
`sup_{i ≤ U} |Y_m(i) − Y_n(i)|` small for `m ≥ n` from some `n` on, almost surely.

Applied to `Y_n(u) = bv0(u ∧ S_n)` (`E Y_n(U)² = E(U ∧ S_n) ≤ U`), the oscillation of `bv0` on `[S_n, T̃)` is
eventually small whenever `T̃ ≤ U`, and WW-A's `exists_tendsto_nhdsLT_of_osc` gives the left limit.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Zhan

namespace Retarget

/-! ### The abstract oscillation bound -/

section Abstract

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **Consistent martingales along stopping times have eventually small oscillation**, almost surely. -/
theorem ae_osc_small [IsProbabilityMeasure P] {𝓗 : Filtration ℝ≥0 mΩ} {Y : ℕ → ℝ≥0 → Ω → ℝ}
    (hY : ∀ n, Martingale (Y n) 𝓗 P) (hYc : ∀ n ω, Continuous (Y n · ω))
    (hYb : ∀ n, ∃ C, ∀ t ω, |Y n t ω| ≤ C)
    {S : ℕ → Ω → ℝ≥0} (hS : ∀ n, IsStoppingTime 𝓗 fun ω => (S n ω : WithTop ℝ≥0))
    (hSmono : ∀ ω, Monotone fun n => S n ω)
    (hYS : ∀ n t ω, Y n t ω = Y n (min t (S n ω)) ω)
    (hcons : ∀ n m', n ≤ m' → ∀ t ω, Y n t ω = Y m' (min t (S n ω)) ω)
    (U : ℝ≥0) {c : ℝ} (hL2 : ∀ n, ∫ ω, Y n U ω ^ 2 ∂P ≤ c) :
    ∀ᵐ ω ∂P, ∀ k : ℕ, ∃ n, ∀ m', n ≤ m' →
      ⨆ i : Iic U, ‖Y m' i ω - Y n i ω‖ < 1 / ((k : ℝ) + 1) := by
  choose C hC using hYb
  have hYrc : ∀ n ω t, ContinuousWithinAt (Y n · ω) (Ici t) t := fun n ω t =>
    (hYc n ω).continuousWithinAt
  have hstab : ∀ n m', n ≤ m' → ∀ t ω, Y n (min t (S m' ω)) ω = Y n t ω := by
    intro n m' hnm t ω
    rw [hYS n (min t (S m' ω)) ω, min_assoc, min_eq_right (hSmono ω hnm), ← hYS]
  -- the `L²` norms at the horizon `U`
  set a : ℕ → ℝ := fun n => ∫ ω, Y n U ω ^ 2 ∂P with hadef
  have horth : ∀ n m', n ≤ m' → ∫ ω, (Y m' U ω - Y n U ω) ^ 2 ∂P = a m' - a n := fun n m' hnm =>
    WangWu.integral_sq_sub_eq_of_stopped (hY m') (hYrc m') (fun t ω => hC m' t ω) (hS n)
      (fun ω => hcons n m' hnm U ω)
  have ha_mono : Monotone a := fun n m' hnm => by
    have h := horth n m' hnm
    have : 0 ≤ ∫ ω, (Y m' U ω - Y n U ω) ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
    linarith
  have ha_bdd : BddAbove (range a) := ⟨c, by rintro _ ⟨n, rfl⟩; exact hL2 n⟩
  have ha_tend : Tendsto a atTop (𝓝 (⨆ n, a n)) := tendsto_atTop_ciSup ha_mono ha_bdd
  -- the oscillations
  set osc : ℕ → ℕ → Ω → ℝ := fun n m' ω => ⨆ i : Iic U, ‖Y m' i ω - Y n i ω‖ with hoscdef
  have hosc_bdd : ∀ n m' ω, BddAbove (range fun i : Iic U => ‖Y m' i ω - Y n i ω‖) := fun n m' ω =>
    ⟨C m' + C n, by
      rintro _ ⟨i, rfl⟩
      show ‖Y m' i ω - Y n i ω‖ ≤ C m' + C n
      rw [Real.norm_eq_abs]
      have := abs_sub (Y m' i ω) (Y n i ω)
      linarith [hC m' i ω, hC n i ω]⟩
  have hosc_mono : ∀ n m₁ m₂ ω, n ≤ m₁ → m₁ ≤ m₂ → osc n m₁ ω ≤ osc n m₂ ω := by
    intro n m₁ m₂ ω hnm hmm
    refine ciSup_le fun i => ?_
    refine le_ciSup_of_le (hosc_bdd n m₂ ω)
      ⟨min i (S m₁ ω), Set.mem_Iic.2 ((min_le_left _ _).trans (Set.mem_Iic.1 i.2))⟩ ?_
    show ‖Y m₁ i ω - Y n i ω‖ ≤ ‖Y m₂ (min i (S m₁ ω)) ω - Y n (min i (S m₁ ω)) ω‖
    rw [← hcons m₁ m₂ hmm i ω, hstab n m₁ hnm i ω]
  have hprob : ∀ n m', n ≤ m' → ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      P.real {ω | ε ≤ osc n m' ω} ≤ ((a m' - a n) / δ + δ) / (2 * ε) := by
    intro n m' hnm ε δ hε hδ
    have hD := (hY m').sub (hY n)
    have hDrc : ∀ ω, IsRightContinuous ((Y m' - Y n) · ω) := fun ω t =>
      (((hYc m' ω).sub (hYc n ω)).continuousAt (x := t)).continuousWithinAt
    have hDb : ∀ ω, |(Y m' - Y n) U ω| ≤ C m' + C n := fun ω => by
      simp only [Pi.sub_apply]
      have := abs_sub (Y m' U ω) (Y n U ω)
      linarith [hC m' U ω, hC n U ω]
    have hDint : Integrable (fun ω => (Y m' - Y n) U ω ^ 2) P := by
      refine Integrable.of_bound ((((hY m').1 U).mono (Filtration.le _ U)).aestronglyMeasurable.sub
        (((hY n).1 U).mono (Filtration.le _ U)).aestronglyMeasurable |>.pow 2) ((C m' + C n) ^ 2)
        (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hDb ω) 2
    have h := WangWu.measureReal_iSup_ge_le hD hDrc U hε hδ hDint
    simp only [Pi.sub_apply] at h
    rwa [horth n m' hnm] at h
  -- almost surely the oscillations are eventually small
  rw [ae_all_iff]
  intro k
  set ε : ℝ := 1 / ((k : ℝ) + 1) with hεdef
  have hε : 0 < ε := by positivity
  set Bad : Set Ω := ⋂ n, ⋃ i, {ω | ε ≤ osc n (n + i) ω} with hBad
  have hBadle : ∀ n δ, 0 < δ → P.real Bad ≤ (((⨆ n, a n) - a n) / δ + δ) / (2 * ε) := by
    intro n δ hδ
    have hmonoS : Monotone fun i => {ω | ε ≤ osc n (n + i) ω} := fun i i' hii' ω hω =>
      le_trans hω (hosc_mono n (n + i) (n + i') ω (Nat.le_add_right _ _) (by omega))
    have hbound : 0 ≤ (((⨆ n, a n) - a n) / δ + δ) / (2 * ε) := by
      have : a n ≤ ⨆ n, a n := le_ciSup ha_bdd n
      have : 0 ≤ (⨆ n, a n) - a n := by linarith
      positivity
    have hUn : P (⋃ i, {ω | ε ≤ osc n (n + i) ω}) ≤
        ENNReal.ofReal ((((⨆ n, a n) - a n) / δ + δ) / (2 * ε)) := by
      rw [hmonoS.measure_iUnion]
      refine iSup_le fun i => ?_
      rw [← ofReal_measureReal (measure_ne_top _ _)]
      refine ENNReal.ofReal_le_ofReal ((hprob n (n + i) (Nat.le_add_right _ _) ε δ hε hδ).trans ?_)
      have : a (n + i) ≤ ⨆ n, a n := le_ciSup ha_bdd _
      gcongr
    have h1 : P.real Bad ≤ P.real (⋃ i, {ω | ε ≤ osc n (n + i) ω}) :=
      measureReal_mono (iInter_subset _ n)
    exact h1.trans (ENNReal.toReal_le_of_le_ofReal hbound hUn)
  have hBad0 : P.real Bad ≤ 0 := by
    by_contra hpos
    push Not at hpos
    set p := P.real Bad
    have hδ : 0 < ε * p := mul_pos hε hpos
    have hlim : Tendsto (fun n => (((⨆ n, a n) - a n) / (ε * p) + ε * p) / (2 * ε)) atTop
        (𝓝 ((((⨆ n, a n) - (⨆ n, a n)) / (ε * p) + ε * p) / (2 * ε))) :=
      (((tendsto_const_nhds.sub ha_tend).div_const _).add_const _).div_const _
    have := ge_of_tendsto' hlim fun n => hBadle n (ε * p) hδ
    rw [sub_self, zero_div, zero_add] at this
    have : p ≤ p / 2 := by
      calc p ≤ ε * p / (2 * ε) := this
        _ = p / 2 := by field_simp
    linarith
  have hBadz : P Bad = 0 :=
    (measureReal_eq_zero_iff (measure_ne_top _ _)).1 (le_antisymm hBad0 measureReal_nonneg)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hBadz] with ω hω
  simp only [hBad, mem_iInter, mem_iUnion, mem_ofPred_eq, not_forall, not_exists, not_le] at hω
  obtain ⟨n, hn⟩ := hω
  refine ⟨n, fun m' hnm => ?_⟩
  have := hn (m' - n)
  rwa [Nat.add_sub_cancel' hnm] at this

end Abstract

/-! ### The stopped new-time noise -/

section Apply

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {nL j m : ℕ} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {xL : Fin nL → ℝ} {xR : Fin (j + 1 + m) → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin (j + 1 + m) → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin (j + 1 + m) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {G : Set Ω} {T : ℕ → Ω → ℝ≥0}

variable (hgood : ∀ ω ∈ G, IsRGood κ xL xR ρL ρR W VL VR B ζ T ω) (hD : LP.IsDistinctForceWord xL xR)
  (hj : 1 ≤ j)

include hgood hD hj in
theorem newS_mono (hTm : ∀ ω, Monotone (T · ω)) (ω : Ω) :
    Monotone fun n => newS xR G T W VL VR B ζ n ω := by
  intro n n' hnn'
  by_cases hω : ω ∈ G
  · have hpos : 0 < LP.retargetPos xR := LP.retargetPos_pos hD.2.2 hD.1.2.2.2 hj
    have hg := hgood ω hω
    have hS := sepUpTo_of_good hg hD hj
    have hσT := rLoc_lt_sepT hg hω hD hj (T := T) (B := B) (VL := VL) n'
    obtain ⟨S', hσS', hS'T⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hσT
    have hR := (hS.isSep_of_lt hS'T).isRate hpos
    have hle : rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω ≤ rLoc (LP.retargetIdx j m) G T W VL VR B ζ n' ω :=
      rLoc_mono hgood hTm ω hnn'
    have hσS'' : rLoc (LP.retargetIdx j m) G T W VL VR B ζ n' ω ≤ S' := by exact_mod_cast hσS'.le
    refine Real.toNNReal_le_toNNReal ?_
    exact hR.strictMonoOn_clk.monotoneOn
      ⟨(rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω).coe_nonneg, by exact_mod_cast hle.trans hσS''⟩
      ⟨(rLoc (LP.retargetIdx j m) G T W VL VR B ζ n' ω).coe_nonneg, by exact_mod_cast hσS''⟩
      (by exact_mod_cast hle)
  · simp only [newS, rLoc_of_not_mem hω, NNReal.coe_zero, clk_zero, Real.toNNReal_zero, le_refl]

include hgood hD hj in
/-- `S_n` is before the new horizon on the good event. -/
theorem newS_lt_horT {ω : Ω} (hω : ω ∈ G) (n : ℕ) :
    (newS xR G T W VL VR B ζ n ω : ℝ≥0∞) < horT xR W VR ζ ω := by
  have hpos : 0 < LP.retargetPos xR := LP.retargetPos_pos hD.2.2 hD.1.2.2.2 hj
  have hg := hgood ω hω
  exact (clk_lt_newHorizon' (sepUpTo_of_good hg hD hj) hpos (rLoc_lt_sepT hg hω hD hj n)).2

include hgood hD hj in
/-- The stopped new-time noise in terms of the stopped observable. -/
theorem bv0_min_eq (n : ℕ) (u : ℝ≥0) (ω : Ω) :
    bv0 κ xL xR ρL ρR G W VL VR B (min u (newS xR G T W VL VR B ζ n ω)) ω =
      (obs κ xL xR ρL ρR (LP.retargetIdx j m)
        (rCoord xL xR (LP.retargetPos xR) (LP.retargetIdx j m) G W VL VR
          (min (invClk (rateT xR W VR ω) (min u (newS xR G T W VL VR B ζ n ω) : ℝ≥0)).toNNReal
            (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω,
         Sec2.TwoSeed.brownG G B (min (invClk (rateT xR W VR ω) (min u (newS xR G T W VL VR B ζ n ω) : ℝ≥0)).toNNReal
            (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω) -
        obs κ xL xR ρL ρR (LP.retargetIdx j m) (rInit xL xR (LP.retargetPos xR))) / Real.sqrt κ := by
  by_cases hω : ω ∈ G
  · have e := min_capTime_newT_rLoc (hgood ω hω) hω hD hj n u
    have hle : (invClk (rateT xR W VR ω) (min u (newS xR G T W VL VR B ζ n ω) : ℝ≥0)).toNNReal ≤
        rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω := by rw [← e]; exact min_le_right _ _
    rw [min_eq_left hle]
    rfl
  · simp only [bv0, rCoord, Sec2.TwoSeed.brownG, hω, ↓reduceIte]

include hgood in
theorem bv0_zero (ω : Ω) : bv0 κ xL xR ρL ρR G W VL VR B 0 ω = 0 := by
  by_cases hω : ω ∈ G
  · have hF := (hgood ω hω).1.isForcePath
    have h0 : rCoordAt (LP.retargetPos xR) (LP.retargetIdx j m) (W · ω) (fun i t => VL i t ω)
        (fun i t => VR i t ω) 0 = (xL, xR, LP.retargetPos xR, -1, 0) := rCoordAt_zero hF.vL_zero hF.vR_zero
    simp only [bv0, NNReal.coe_zero, invClk_zero_eq, Real.toNNReal_zero, rCoord, Sec2.TwoSeed.brownG, hω,
      ↓reduceIte, h0, (hgood ω hω).2.2.1, rInit, sub_self, zero_div]
  · simp only [bv0, rCoord, Sec2.TwoSeed.brownG, hω, ↓reduceIte, rInit, sub_self, zero_div]

include hgood hD hj in
theorem continuous_bv0_stopped (n : ℕ) (ω : Ω) :
    Continuous fun u => bv0 κ xL xR ρL ρR G W VL VR B (min u (newS xR G T W VL VR B ζ n ω)) ω := by
  simp only [bv0_min_eq hgood hD hj n]
  by_cases hω : ω ∈ G
  · have hpos : 0 < LP.retargetPos xR := LP.retargetPos_pos hD.2.2 hD.1.2.2.2 hj
    have hg := hgood ω hω
    have hS := sepUpTo_of_good hg hD hj
    have hσT := rLoc_lt_sepT hg hω hD hj (T := T) (B := B) (VL := VL) n
    have hR := (hS.isSep_of_lt hσT).isRate hpos
    obtain ⟨h0, -⟩ := clk_lt_newHorizon' hS hpos hσT
    have h0' : 0 ≤ clk (rateT xR W VR ω) (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω) := h0
    have hSn : ((newS xR G T W VL VR B ζ n ω : ℝ≥0) : ℝ) =
        clk (rateT xR W VR ω) (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω) := by
      rw [newS, Real.coe_toNNReal _ h0']
    have ht : Continuous fun u : ℝ≥0 =>
        (invClk (rateT xR W VR ω) ((min u (newS xR G T W VL VR B ζ n ω) : ℝ≥0) : ℝ)).toNNReal := by
      refine continuous_real_toNNReal.comp (hR.continuousOn_invClk.comp_continuous
        (NNReal.continuous_coe.comp (continuous_id.min continuous_const)) fun u => ?_)
      refine ⟨(min u _).coe_nonneg, ?_⟩
      have : ((min u (newS xR G T W VL VR B ζ n ω) : ℝ≥0) : ℝ) ≤ newS xR G T W VL VR B ζ n ω := by
        exact_mod_cast min_le_right _ _
      rw [hSn] at this; exact this
    have hZ := continuous_rObs (κ := κ) (ρL := ρL) (ρR := ρR) hgood hD hj
      (contDiffOn_obs (κ := κ) (xL := xL) (xR := xR) (ρL := ρL) (ρR := ρR) (k := LP.retargetIdx j m)
        (n := 0)).continuousOn n ω
    exact ((hZ.comp ht).sub continuous_const).div_const _
  · simp only [rCoord, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
    exact continuous_const

include hgood hD hj in
theorem exists_bound_bv0_stopped (n : ℕ) :
    ∃ C, ∀ u ω, |bv0 κ xL xR ρL ρR G W VL VR B (min u (newS xR G T W VL VR B ζ n ω)) ω| ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_rObs (κ := κ) (ρL := ρL) (ρR := ρR) hgood hD hj
    (contDiffOn_obs (κ := κ) (xL := xL) (xR := xR) (ρL := ρL) (ρR := ρR) (k := LP.retargetIdx j m)
      (n := 0)).continuousOn n
  set c := obs κ xL xR ρL ρR (LP.retargetIdx j m) (rInit xL xR (LP.retargetPos xR))
  refine ⟨(C + |c|) / Real.sqrt κ, fun u ω => ?_⟩
  rw [bv0_min_eq hgood hD hj n, abs_div, abs_of_nonneg (Real.sqrt_nonneg κ)]
  refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg κ)
  exact (abs_sub _ _).trans (add_le_add (hC _ ω) le_rfl)

include hgood hD hj in
/-- **Exhaustion in the new time**: every new time before the horizon is below some `S_n`. -/
theorem exists_le_newS (hTm : ∀ ω, Monotone (T · ω)) {ω : Ω} (hω : ω ∈ G) {r : ℝ≥0}
    (hr : (r : ℝ≥0∞) < horT xR W VR ζ ω) : ∃ n, r ≤ newS xR G T W VL VR B ζ n ω := by
  have hpos : 0 < LP.retargetPos xR := LP.retargetPos_pos hD.2.2 hD.1.2.2.2 hj
  have hg := hgood ω hω
  have hS := sepUpTo_of_good hg hD hj
  obtain ⟨n, hn⟩ := exists_forall_le_rLoc hg hω hD hj hgood (hTm ω) (invClk_lt hS hpos hr)
  refine ⟨n, ?_⟩
  have hσT := rLoc_lt_sepT hg hω hD hj (T := T) (B := B) (VL := VL) n
  have h1 : (r : ℝ) ≤ clk (rate (LP.retargetPos xR) (W · ω) (VR (LP.retargetIdx j m) · ω))
      (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω) := (invClk_le_iff hS hpos hr hσT).1 (hn n le_rfl)
  obtain ⟨h0, -⟩ := clk_lt_newHorizon' hS hpos hσT
  exact (Real.le_toNNReal_iff_coe_le h0).2 h1

end Apply

/-! ### The limit at the horizon -/

section Main

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {nL j m : ℕ} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {xL : Fin nL → ℝ} {xR : Fin (j + 1 + m) → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin (j + 1 + m) → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin (j + 1 + m) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {G : Set Ω} {T : ℕ → Ω → ℝ≥0}

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsRGood κ xL xR ρL ρR W VL VR B ζ T ω)
  (hT : Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P) P ζ T)
  (hD : LP.IsDistinctForceWord xL xR) (hj : 1 ≤ j)

include hE hGm hGc hgood hT hD hj in
/-- `E bv0(U ∧ S_n)² = E(U ∧ S_n) ≤ U`. -/
theorem integral_bv0_sq_le (hκ : 0 < κ) (n : ℕ) (U : ℝ≥0) :
    ∫ ω, bv0 κ xL xR ρL ρR G W VL VR B (min U (newS xR G T W VL VR B ζ n ω)) ω ^ 2 ∂P ≤ U := by
  have hP := hE.1.isProbabilityMeasure'
  have hM := martingale_bv0_sq_stopped hE hGm hGc hgood hT hD hj hκ n
  have hM1 := martingale_bv0_stopped hE hGm hGc hgood hT hD hj hκ n
  set Y : Ω → ℝ := fun ω => bv0 κ xL xR ρL ρR G W VL VR B (min U (newS xR G T W VL VR B ζ n ω)) ω with hY
  set S : Ω → ℝ := fun ω => ((min U (newS xR G T W VL VR B ζ n ω) : ℝ≥0) : ℝ) with hS
  have h0 := hM.setIntegral_eq (zero_le (a := U)) (@MeasurableSet.univ _ (filtH hE hGm hGc hgood hT hD hj 0))
  simp only [Measure.restrict_univ, zero_min, bv0_zero hgood, NNReal.coe_zero, sub_zero] at h0
  obtain ⟨C, hC⟩ := exists_bound_bv0_stopped (κ := κ) (ρL := ρL) (ρR := ρR) hgood hD hj n
  have hYm : StronglyMeasurable Y := ((hM1.1 U).mono ((filtH hE hGm hGc hgood hT hD hj).le U))
  have hY2 : Integrable (fun ω => Y ω ^ 2) P := by
    refine Integrable.of_bound (hYm.aestronglyMeasurable.pow 2) (C ^ 2) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hC U ω) 2
  have hdiff : Integrable (fun ω => Y ω ^ 2 - S ω) P := hM.integrable U
  have hSi : Integrable S P := (hY2.sub hdiff).congr (Eventually.of_forall fun ω => by simp)
  have hsplit : ∫ ω, Y ω ^ 2 ∂P = ∫ ω, (Y ω ^ 2 - S ω) ∂P + ∫ ω, S ω ∂P := by
    rw [← integral_add hdiff hSi]; congr 1; funext ω; ring
  have hzero : ∫ ω, (Y ω ^ 2 - S ω) ∂P = 0 := by
    rw [← h0]; simp
  have hSle : ∫ ω, S ω ∂P ≤ U := by
    have : ∫ ω, S ω ∂P ≤ ∫ _ω, (U : ℝ) ∂P :=
      integral_mono hSi (integrable_const _) fun ω => by
        simp only [hS]; exact_mod_cast min_le_left _ _
    simpa using this
  rw [hsplit, hzero, zero_add]
  exact hSle

include hE hGm hGc hgood hT hD hj in
/-- **The new-time noise has a limit at a finite new horizon**, almost surely. -/
theorem ae_tendsto_bv0 (hκ : 0 < κ) :
    ∀ᵐ ω ∂P, ω ∈ G → horT xR W VR ζ ω ≠ ⊤ → ∃ L, Tendsto (fun u => bv0 κ xL xR ρL ρR G W VL VR B u ω)
      (𝓝[<] (horT xR W VR ζ ω).toNNReal) (𝓝 L) := by
  have hP := hE.1.isProbabilityMeasure'
  set Y : ℕ → ℝ≥0 → Ω → ℝ := fun n u ω =>
    bv0 κ xL xR ρL ρR G W VL VR B (min u (newS xR G T W VL VR B ζ n ω)) ω with hYdef
  have hYS : ∀ n t ω, Y n t ω = Y n (min t (newS xR G T W VL VR B ζ n ω)) ω := fun n t ω => by
    simp only [hYdef, min_assoc, min_self]
  have hcons : ∀ n m', n ≤ m' → ∀ t ω, Y n t ω = Y m' (min t (newS xR G T W VL VR B ζ n ω)) ω := by
    intro n m' hnm t ω
    simp only [hYdef, min_assoc, min_eq_left (newS_mono hgood hD hj hT.2.1 ω hnm)]
  have hosc : ∀ U : ℕ, ∀ᵐ ω ∂P, ∀ k : ℕ, ∃ n, ∀ m', n ≤ m' →
      ⨆ i : Iic (U : ℝ≥0), ‖Y m' i ω - Y n i ω‖ < 1 / ((k : ℝ) + 1) := fun U =>
    ae_osc_small (fun n => martingale_bv0_stopped hE hGm hGc hgood hT hD hj hκ n)
      (fun n ω => continuous_bv0_stopped hgood hD hj n ω)
      (fun n => exists_bound_bv0_stopped hgood hD hj n)
      (fun n => isStoppingTime_newS hE hGm hGc hgood hT hD hj n) (newS_mono hgood hD hj hT.2.1)
      hYS hcons (U : ℝ≥0) (c := (U : ℝ)) fun n => integral_bv0_sq_le hE hGm hGc hgood hT hD hj hκ n U
  filter_upwards [ae_all_iff.2 hosc] with ω hω hωG hfin
  set h := (horT xR W VR ζ ω).toNNReal with hh
  have hhc : ((h : ℝ≥0) : ℝ≥0∞) = horT xR W VR ζ ω := ENNReal.coe_toNNReal hfin
  have hρs : ∀ n, newS xR G T W VL VR B ζ n ω < h := fun n => by
    have := newS_lt_horT hgood hD hj (T := T) (B := B) (VL := VL) hωG n
    rw [← hhc] at this; exact_mod_cast this
  obtain ⟨U, hU⟩ := exists_nat_gt (h : ℝ)
  refine WangWu.exists_tendsto_nhdsLT_of_osc (f := fun u => bv0 κ xL xR ρL ρR G W VL VR B u ω) hρs
    fun ε hε => ?_
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨n, hn⟩ := hω U k
  refine ⟨n, fun r hr hrh => ?_⟩
  have hrH : (r : ℝ≥0∞) < horT xR W VR ζ ω := by rw [← hhc]; exact_mod_cast hrh
  obtain ⟨m₀, hm₀⟩ := exists_le_newS hgood hD hj hT.2.1 hωG hrH
  set m' := max n m₀
  have hrm' : r ≤ newS xR G T W VL VR B ζ m' ω :=
    hm₀.trans (newS_mono hgood hD hj hT.2.1 ω (le_max_right _ _))
  have h1 : Y m' r ω = bv0 κ xL xR ρL ρR G W VL VR B r ω := by simp only [hYdef, min_eq_left hrm']
  have h2 : Y n r ω = bv0 κ xL xR ρL ρR G W VL VR B (newS xR G T W VL VR B ζ n ω) ω := by
    simp only [hYdef, min_eq_right hr]
  have hrU : r ≤ (U : ℝ≥0) := by
    have : (r : ℝ) < U := lt_trans (by exact_mod_cast hrh) hU
    exact_mod_cast this.le
  obtain ⟨C₁, hC₁⟩ := exists_bound_bv0_stopped (κ := κ) (ρL := ρL) (ρR := ρR) hgood hD hj m'
  obtain ⟨C₂, hC₂⟩ := exists_bound_bv0_stopped (κ := κ) (ρL := ρL) (ρR := ρR) hgood hD hj n
  have hbdd : BddAbove (range fun i : Iic (U : ℝ≥0) => ‖Y m' i ω - Y n i ω‖) :=
    ⟨C₁ + C₂, by
      rintro _ ⟨i, rfl⟩
      show ‖Y m' i ω - Y n i ω‖ ≤ C₁ + C₂
      rw [Real.norm_eq_abs]
      have := abs_sub (Y m' i ω) (Y n i ω)
      linarith [hC₁ i ω, hC₂ i ω]⟩
  have hle : ‖Y m' r ω - Y n r ω‖ ≤ ⨆ i : Iic (U : ℝ≥0), ‖Y m' i ω - Y n i ω‖ :=
    le_ciSup (f := fun i : Iic (U : ℝ≥0) => ‖Y m' i ω - Y n i ω‖) hbdd ⟨r, hrU⟩
  rw [h1, h2, Real.norm_eq_abs] at hle
  exact (hle.trans (hn m' (le_max_left _ _)).le).trans hk.le

end Main

end Retarget

end Zhan

end InteractingSLE
