/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.TargetChangeProcessBrownianLimit
import InteractingSLE.WangWu.CouplingFrozenTwo

/-!
# `b̃` is a Brownian motion, part 7: the noise extended past the horizon

Packet PROVE-SEC7-C9. On a good event on which the new-time noise `bv0` has a left limit at every finite new horizon
(part 6), the noise frozen at its limit after the horizon,

  `bvF u = bv0 u` (`u < T̃`), `lim_{v ↑ T̃} bv0 v` (`u ≥ T̃`), `0` off the good event,

has every path continuous (`continuous_bvF`), starts at `0`, and agrees with `bv0` before every `S_n`. Before the
horizon `bv0` is the transformed Brownian path `b̃ = newB` of PROVE-SEC7-C8 (`bv0_eq_newB`, from
`sqrt_mul_newB_eq`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Zhan

namespace Retarget

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {nL j m : ℕ} {κ : ℝ}
  {xL : Fin nL → ℝ} {xR : Fin (j + 1 + m) → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin (j + 1 + m) → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin (j + 1 + m) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {G : Set Ω} {T : ℕ → Ω → ℝ≥0}

open scoped Classical in
/-- **The noise frozen at its limit after the horizon** (`0` off the good event). -/
def bvF (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin (j + 1 + m) → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin (j + 1 + m) → ℝ)
    (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin (j + 1 + m) → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (u : ℝ≥0) (ω : Ω) : ℝ :=
  if ω ∈ G then
    (if (u : ℝ≥0∞) < horT xR W VR ζ ω then bv0 κ xL xR ρL ρR G W VL VR B u ω
      else limUnder (𝓝[<] (horT xR W VR ζ ω).toNNReal) fun v => bv0 κ xL xR ρL ρR G W VL VR B v ω)
  else 0

theorem bv0_of_not_mem {ω : Ω} (hω : ω ∉ G) (u : ℝ≥0) : bv0 κ xL xR ρL ρR G W VL VR B u ω = 0 := by
  simp only [bv0, rCoord, Sec2.TwoSeed.brownG, hω, ↓reduceIte, rInit, sub_self, zero_div]

section Good

variable (hgood : ∀ ω ∈ G, IsRGood κ xL xR ρL ρR W VL VR B ζ T ω) (hD : LP.IsDistinctForceWord xL xR)
  (hj : 1 ≤ j) (hTm : ∀ ω, Monotone (T · ω))
include hgood hD hj hTm

/-- Before the horizon, `bv0` is continuous on every `[0, U]`. -/
theorem continuousOn_bv0_Icc {ω : Ω} (hω : ω ∈ G) {U : ℝ≥0} (hU : (U : ℝ≥0∞) < horT xR W VR ζ ω) :
    ContinuousOn (fun u => bv0 κ xL xR ρL ρR G W VL VR B u ω) (Icc 0 U) := by
  obtain ⟨n, hn⟩ := exists_le_newS hgood hD hj hTm hω hU
  refine (continuous_bv0_stopped hgood hD hj n ω).continuousOn.congr fun u hu => ?_
  simp only [min_eq_left (hu.2.trans hn)]

/-- On a good path with an infinite horizon, `bv0` is continuous. -/
theorem continuous_bv0_of_top {ω : Ω} (hω : ω ∈ G) (htop : horT xR W VR ζ ω = ⊤) :
    Continuous fun u => bv0 κ xL xR ρL ρR G W VL VR B u ω := by
  refine continuous_iff_continuousAt.2 fun u => ?_
  have hU : ((u + 1 : ℝ≥0) : ℝ≥0∞) < horT xR W VR ζ ω := by rw [htop]; exact ENNReal.coe_lt_top
  have hc := continuousOn_bv0_Icc hgood hD hj hTm hω hU
  refine hc.continuousAt ?_
  have : Icc (0 : ℝ≥0) (u + 1) = Iic (u + 1) := by ext x; simp
  rw [this]
  exact Iic_mem_nhds (lt_add_one u)

/-- **Every path of the frozen noise is continuous**, given the left limit at a finite horizon. -/
theorem continuous_bvF
    (hlim : ∀ ω ∈ G, horT xR W VR ζ ω ≠ ⊤ → ∃ L, Tendsto (fun u => bv0 κ xL xR ρL ρR G W VL VR B u ω)
      (𝓝[<] (horT xR W VR ζ ω).toNNReal) (𝓝 L)) (ω : Ω) :
    Continuous fun u => bvF κ xL xR ρL ρR G W VL VR B ζ u ω := by
  by_cases hω : ω ∈ G
  · by_cases htop : horT xR W VR ζ ω = ⊤
    · have e : (fun u => bvF κ xL xR ρL ρR G W VL VR B ζ u ω) =
          fun u => bv0 κ xL xR ρL ρR G W VL VR B u ω := by
        funext u; simp [bvF, hω, htop]
      rw [e]; exact continuous_bv0_of_top hgood hD hj hTm hω htop
    · obtain ⟨L, hL⟩ := hlim ω hω htop
      set S := horT xR W VR ζ ω with hSdef
      have hSc : ((S.toNNReal : ℝ≥0) : ℝ≥0∞) = S := ENNReal.coe_toNNReal htop
      have hf := WangWu.continuous_frozen_path (g := fun u => bv0 κ xL xR ρL ρR G W VL VR B u ω)
        (S := S) (σ := S.toNNReal)
        (fun U hU _ => continuousOn_bv0_Icc hgood hD hj hTm hω hU)
        (fun _ => by
          have : (𝓝[<] S.toNNReal).NeBot := by
            refine nhdsLT_neBot_of_exists_lt ⟨0, ?_⟩
            have hpos : (0 : ℝ≥0∞) < S := by
              have := newS_lt_horT hgood hD hj (T := T) (B := B) (VL := VL) hω 0
              exact lt_of_le_of_lt bot_le this
            rw [← hSc] at hpos; exact_mod_cast hpos
          rwa [hL.limUnder_eq])
      convert hf using 1
      funext u
      simp only [bvF, hω, ↓reduceIte]
      rw [← hSdef]
      by_cases hu : (u : ℝ≥0∞) < S
      · have hus : u ≤ S.toNNReal := by
          rw [← hSc] at hu; exact_mod_cast hu.le
        simp only [hu, ↓reduceIte, min_eq_left hus]
      · have hus : S.toNNReal ≤ u := by
          rw [← hSc, not_lt] at hu; exact_mod_cast hu
        have hnot : ¬ ((min u S.toNNReal : ℝ≥0) : ℝ≥0∞) < S := by
          rw [min_eq_right hus, hSc]; exact lt_irrefl _
        simp only [hu, ↓reduceIte, hnot]
  · simp only [bvF, hω, ↓reduceIte]; exact continuous_const

omit hTm in
theorem bvF_zero (ω : Ω) : bvF κ xL xR ρL ρR G W VL VR B ζ 0 ω = 0 := by
  by_cases hω : ω ∈ G
  · have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < horT xR W VR ζ ω :=
      lt_of_le_of_lt bot_le (newS_lt_horT hgood hD hj (T := T) (B := B) (VL := VL) hω 0)
    simp only [bvF, hω, ↓reduceIte, h0, bv0_zero hgood]
  · simp only [bvF, hω, ↓reduceIte]

omit hTm in
/-- Before every `S_n` the frozen noise is `bv0`. -/
theorem bvF_min_newS (n : ℕ) (u : ℝ≥0) (ω : Ω) :
    bvF κ xL xR ρL ρR G W VL VR B ζ (min u (newS xR G T W VL VR B ζ n ω)) ω =
      bv0 κ xL xR ρL ρR G W VL VR B (min u (newS xR G T W VL VR B ζ n ω)) ω := by
  by_cases hω : ω ∈ G
  · have h : ((min u (newS xR G T W VL VR B ζ n ω) : ℝ≥0) : ℝ≥0∞) < horT xR W VR ζ ω :=
      lt_of_le_of_lt (by exact_mod_cast min_le_right _ _) (newS_lt_horT hgood hD hj hω n)
    simp only [bvF, hω, ↓reduceIte, h]
  · simp only [bvF, hω, ↓reduceIte, bv0_of_not_mem hω]

end Good

/-! ### Identification with `b̃` -/

theorem rCoordAt_toNNReal {nR : ℕ} {xk : ℝ} {k : Fin nR} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ}
    {vR : Fin nR → ℝ≥0 → ℝ} {s : ℝ} (hs : 0 ≤ s) :
    rCoordAt xk k w vL vR s.toNNReal = ((fun i => vL i s.toNNReal), (fun i => vR i s.toNNReal),
      alpha xk w (vR k) s, beta xk w (vR k) s, clk (rate xk w (vR k)) s) := by
  simp only [rCoordAt, Real.coe_toNNReal _ hs]

/-- **Before the horizon, the new-time noise is the transformed Brownian path `b̃`** of PROVE-SEC7-C8. -/
theorem bv0_eq_newB (hκ : 0 < κ) (hgood : ∀ ω ∈ G, IsRGood κ xL xR ρL ρR W VL VR B ζ T ω)
    (hD : LP.IsDistinctForceWord xL xR) (hj : 1 ≤ j) {ω : Ω} (hω : ω ∈ G) {u : ℝ≥0}
    (hu : (u : ℝ≥0∞) < horT xR W VR ζ ω) :
    bv0 κ xL xR ρL ρR G W VL VR B u ω =
      newB κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) u := by
  have hg := hgood ω hω
  have hp := hg.1.isSLEPathUpTo (sepTime_le (W · ω) (VR (LP.retargetIdx j m) · ω) (ζ ω))
  have hd := retargetData_of_isSLEPathUpTo hp hD hj fun _ ht => lt_of_lt_sepTime ht
  have hκs : Real.sqrt κ ≠ 0 := Real.sqrt_ne_zero'.2 hκ
  have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < horT xR W VR ζ ω := lt_of_le_of_lt bot_le hu
  have e0 := sqrt_mul_newB_eq hp hd hκ h0
  have eu := sqrt_mul_newB_eq hp hd hκ hu
  have hB0 : newB κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) 0 = 0 := by
    simp only [newB, newW_zero hp hd, newVL_zero hp hd hD, newVR_zero hp hD, sub_self, mul_zero,
      Finset.sum_const_zero, add_zero, zero_div]
  -- the initial value of the observable is `X̃`
  obtain ⟨S₀, _, _, _, hm0, _⟩ := newTime_spec hd.sep hd.pos h0
  have hF := hg.1.isForcePath
  have hinit : obs κ xL xR ρL ρR (LP.retargetIdx j m) (rInit xL xR (LP.retargetPos xR)) =
      obs κ xL xR ρL ρR (LP.retargetIdx j m)
        (((fun i => VL i (invClk (rate (LP.retargetPos xR) (W · ω) (VR (LP.retargetIdx j m) · ω)) (0 : ℝ≥0)).toNNReal
          ω), (fun i => VR i (invClk (rate (LP.retargetPos xR) (W · ω) (VR (LP.retargetIdx j m) · ω))
            (0 : ℝ≥0)).toNNReal ω),
          alpha (LP.retargetPos xR) (W · ω) (VR (LP.retargetIdx j m) · ω)
            (invClk (rate (LP.retargetPos xR) (W · ω) (VR (LP.retargetIdx j m) · ω)) (0 : ℝ≥0)),
          beta (LP.retargetPos xR) (W · ω) (VR (LP.retargetIdx j m) · ω)
            (invClk (rate (LP.retargetPos xR) (W · ω) (VR (LP.retargetIdx j m) · ω)) (0 : ℝ≥0)),
          clk (rate (LP.retargetPos xR) (W · ω) (VR (LP.retargetIdx j m) · ω))
            (invClk (rate (LP.retargetPos xR) (W · ω) (VR (LP.retargetIdx j m) · ω)) (0 : ℝ≥0))),
          B (invClk (rate (LP.retargetPos xR) (W · ω) (VR (LP.retargetIdx j m) · ω)) (0 : ℝ≥0)).toNNReal ω) := by
    simp only [NNReal.coe_zero, invClk_zero_eq, Real.toNNReal_zero, hF.vL_zero, hF.vR_zero, alpha_zero,
      beta_zero, clk_zero, hg.2.2.1, rInit]
  rw [hB0, mul_zero, ← hinit] at e0
  -- the value at `u`
  obtain ⟨S, _, _, _, hm, _⟩ := newTime_spec hd.sep hd.pos hu
  have hval : obs κ xL xR ρL ρR (LP.retargetIdx j m)
      (rCoord xL xR (LP.retargetPos xR) (LP.retargetIdx j m) G W VL VR (invClk (rateT xR W VR ω) u).toNNReal ω,
        Sec2.TwoSeed.brownG G B (invClk (rateT xR W VR ω) u).toNNReal ω) =
      Real.sqrt κ * newB κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) u +
        obs κ xL xR ρL ρR (LP.retargetIdx j m) (rInit xL xR (LP.retargetPos xR)) := by
    rw [eu]
    simp only [rCoord, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
    rw [show rateT xR W VR ω = rate (LP.retargetPos xR) (W · ω) (VR (LP.retargetIdx j m) · ω) from rfl,
      rCoordAt_toNNReal hm.1]
    linarith
  rw [bv0, hval]
  field_simp
  ring

end Retarget

end Zhan

end InteractingSLE
