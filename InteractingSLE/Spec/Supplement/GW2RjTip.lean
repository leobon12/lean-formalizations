/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RqLoew
import InteractingSLE.Spec.Supplement.GW2RqShellX
import InteractingSLE.Spec.Supplement.GB6LifeBase
import InteractingSLE.Spec.Supplement.GW2BsFlow
import InteractingSLE.Spec.Supplement.GW2GmJ32Shift
import InteractingSLE.Spec.Sec5.Prop49QExitMainNR
import InteractingSLE.Spec.Sec5.Aux61CptJump
import InteractingSLE.Spec.Sec7.StripSideHeightProbSide
import InteractingSLE.Spec.Sec7.Aux37SideGerm
import InteractingSLE.Spec.Sec5.CrossCondGenFinalMarks
import InteractingSLE.Spec.Sec5.CrossCondGenCloseMarks
import InteractingSLE.WangWu.ReverseContactBdryLimit
import InteractingSLE.Foundations.SLE.SpaceFilling.Swallow

/-!
# A window of a stage-1 chain: interior tip and split-freeness (decision D33)

PROVE-GW2-ROOTX round 9, deterministic. Fix a global Loewner trace `η` of a driver `U` (the stage-1 chain: the root
piece mapped out) and a window `[a, a + T]` of it, read in the chart mapped out at `a`
(`ψ = loewnerTip (shiftDrive U a)`).

* **`shiftTip_mem_H`**: the window's tip at `u` is interior if `η(a + u) ∈ ℍ` (the test), the window trace does not
  hit `(jL, jR) \ {0}` (avoidance), does not return to `0`, and `jL ≤ baseL U a`, `baseR U a ≤ jR`. Real points beyond
  the base images pull back to real points (`Supp8.GB6.exists_extendFrom_eq_alive_of_gt`,
  `…_of_lt_baseL`, and `tendsto_extendFrom_of_real` at the base images themselves).
* **`splitFree_window`**: a record whose driver is the window's on `[0, T]` is split-free at `(aL, aR)` (round 8's
  `splitFreeR_of_trace`/`splitFreeL_of_trace` through `markPos_congr`), with an interior tip at `T`.
* **`baseR_le_junctionR`**, **`junctionL_le_baseL`**: along the decoded past `pastOf cf R b`, SDE's junctions dominate
  the base images of the stage-1 driver `U = R(b₁ + ·) − R(b₁)` (`rightImg_shiftDrv`, monotone images).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMapInv)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE.Theorem14.GW2Rj

open Restart Exist.StagedLaw MartChar.RealFlow GW2Rq GW2Wm

/-! ### The image of the seed at time `0` -/

theorem rightImg_zero_time_le {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) : rightImg w 0 0 ≤ 0 := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hX : IsPosSol w ε 0 (fun _ => ε) := by
    refine ⟨continuousOn_const, fun s hs => ?_⟩
    have hs0 : s = 0 := le_antisymm hs.2 hs.1
    subst hs0
    simp [hw0, hε]
  have hA : Alive w ε 0 := ⟨_, hX⟩
  have hg : gImg w ε 0 = ε := by
    rw [gImg, cflow_eq_of_isPosSol hw hX ⟨le_rfl, le_rfl⟩, hw0, zero_add]
  have hmem : ε ∈ imgSet w 0 0 := ⟨ε, hε, hA, hg⟩
  rw [zero_add]
  exact csInf_le (imgSet_bddBelow hw 0 le_rfl) hmem

theorem baseR_zero_le {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) : Supp8.GB6.baseR w 0 ≤ 0 := by
  unfold Supp8.GB6.baseR
  rw [hw0, sub_zero]
  exact rightImg_zero_time_le hw hw0

theorem zero_le_baseL {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) : 0 ≤ Supp8.GB6.baseL w 0 := by
  unfold Supp8.GB6.baseL
  have h := rightImg_zero_time_le (w := fun r => -w r) hw.neg (by simp [hw0])
  rw [hw0]
  linarith

/-! ### The interior tip of a window -/

variable {U : ℝ → ℝ} {η : ℝ → ℂ}

/-- The boundary value at a real point at or beyond the right base image is real. -/
theorem im_extendFrom_eq_zero_of_baseR_le (hU : Continuous U) (hU0 : U 0 = 0) {a : ℝ} (ha : 0 ≤ a)
    (hB : HasBdryLimits (fwdMapInv U a)) {y : ℝ} (hy : Supp8.GB6.baseR U a ≤ y) :
    (extendFrom H (fwdMapInv U a) (y : ℂ)).im = 0 := by
  have hgt : ∀ y' : ℝ, Supp8.GB6.baseR U a < y' → (extendFrom H (fwdMapInv U a) (y' : ℂ)).im = 0 := by
    intro y' hy'
    obtain ⟨x₀, hx, -⟩ := Supp8.GB6.exists_extendFrom_eq_alive_of_gt hU hU0 ha hB hy'
    rw [hx]
    simp
  have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hc : Tendsto (fun n : ℕ => y + 1 / ((n : ℝ) + 1)) atTop (𝓝 y) := by
    simpa using (tendsto_const_nhds (x := y)).add h1
  have hlim := (Complex.continuous_im.tendsto _).comp (Supp8.GB6.tendsto_extendFrom_of_real hB hc)
  have hval : ∀ n : ℕ, (extendFrom H (fwdMapInv U a) (((y + 1 / ((n : ℝ) + 1) : ℝ)) : ℂ)).im = 0 := fun n =>
    hgt _ (lt_of_le_of_lt hy (lt_add_of_pos_right _ (by positivity)))
  have h0 : Tendsto (fun n : ℕ => (extendFrom H (fwdMapInv U a)
      (((y + 1 / ((n : ℝ) + 1) : ℝ)) : ℂ)).im) atTop (𝓝 0) := by
    simp only [hval]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim h0

/-- The boundary value at a real point at or before the left base image is real. -/
theorem im_extendFrom_eq_zero_of_le_baseL (hU : Continuous U) (hU0 : U 0 = 0) {a : ℝ} (ha : 0 ≤ a)
    (hB : HasBdryLimits (fwdMapInv U a)) {y : ℝ} (hy : y ≤ Supp8.GB6.baseL U a) :
    (extendFrom H (fwdMapInv U a) (y : ℂ)).im = 0 := by
  have hlt : ∀ y' : ℝ, y' < Supp8.GB6.baseL U a → (extendFrom H (fwdMapInv U a) (y' : ℂ)).im = 0 := by
    intro y' hy'
    obtain ⟨x₀, hx, -⟩ := Supp8.GB6.exists_extendFrom_eq_of_lt_baseL hU hU0 ha hB hy'
    rw [hx]
    simp
  have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hc : Tendsto (fun n : ℕ => y - 1 / ((n : ℝ) + 1)) atTop (𝓝 y) := by
    simpa using (tendsto_const_nhds (x := y)).sub h1
  have hlim := (Complex.continuous_im.tendsto _).comp (Supp8.GB6.tendsto_extendFrom_of_real hB hc)
  have hval : ∀ n : ℕ, (extendFrom H (fwdMapInv U a) (((y - 1 / ((n : ℝ) + 1) : ℝ)) : ℂ)).im = 0 := fun n =>
    hlt _ (lt_of_lt_of_le (sub_lt_self _ (by positivity)) hy)
  have h0 : Tendsto (fun n : ℕ => (extendFrom H (fwdMapInv U a)
      (((y - 1 / ((n : ℝ) + 1) : ℝ)) : ℂ)).im) atTop (𝓝 0) := by
    simp only [hval]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim h0

/-- **The interior tip of a window.** If the original trace is interior at `a + u`, the window trace does not hit
`(jL, jR) \ {0}` at `u` nor return to `0`, and the window's base images lie in `[jL, jR]`, the window's tip is in
`ℍ`. -/
theorem shiftTip_mem_H (hU : Continuous U) (hU0 : U 0 = 0) (hη : IsLoewnerTrace U η) {a u : ℝ} (ha : 0 ≤ a)
    (hu : 0 ≤ u) (hH : η (a + u) ∈ H) {jL jR : ℝ} (hjL : jL ≤ Supp8.GB6.baseL U a)
    (hjR : Supp8.GB6.baseR U a ≤ jR)
    (hav : ∀ z : ℝ, jL < z → z < jR → z ≠ 0 → loewnerTip (shiftDrive U a) u ≠ (z : ℂ))
    (hret : loewnerTip (shiftDrive U a) u ≠ 0) : loewnerTip (shiftDrive U a) u ∈ H := by
  obtain ⟨hψ, hext⟩ := hη.isLoewnerTrace_shift_and_extendFrom hU hU0 ha
  have hpH : loewnerTip (shiftDrive U a) u ∈ Hbar :=
    GW2TipSystem.Gm.loewnerTrace_mem_Hbar hψ (QuantumZipper.RS.continuous_shiftDrive hU a)
      (QuantumZipper.RS.shiftDrive_zero U a) hu
  have hB := hη.hasBdryLimits hU hU0 ha
  by_contra hpn
  set z : ℝ := (loewnerTip (shiftDrive U a) u).re with hz
  have him : (loewnerTip (shiftDrive U a) u).im = 0 := le_antisymm (not_lt.1 hpn) hpH
  have hp : loewnerTip (shiftDrive U a) u = (z : ℂ) := Complex.ext (by simp [hz]) (by simp [him])
  have hHim : 0 < (η (a + u)).im := hH
  have hreal : (extendFrom H (fwdMapInv U a) (z : ℂ)).im ≠ 0 := by
    rw [← hp, hext u hu]
    exact hHim.ne'
  rcases le_or_gt (Supp8.GB6.baseR U a) z with hzR | hzR
  · exact hreal (im_extendFrom_eq_zero_of_baseR_le hU hU0 ha hB hzR)
  rcases le_or_gt z (Supp8.GB6.baseL U a) with hzL | hzL
  · exact hreal (im_extendFrom_eq_zero_of_le_baseL hU hU0 ha hB hzL)
  by_cases hz0 : z = 0
  · exact hret (hp.trans (by rw [hz0]; simp))
  · exact hav z (lt_of_le_of_lt hjL hzL) (lt_of_lt_of_le hzR hjR) hz0 hp

/-! ### A split-free window -/

/-- **A record driven by a window of a stage-1 chain is split-free**, with an interior tip at its end. -/
theorem splitFree_window {r : RecData} {T : ℝ≥0} (hrt : rtime r = T) (hU : Continuous U) (hU0 : U 0 = 0)
    (hη : IsLoewnerTrace U η) {a : ℝ} (ha : 0 ≤ a) (hrd : ∀ v ∈ Icc (0 : ℝ) T, rdrv r v = shiftDrive U a v)
    {aL aR : ℝ} (haL : aL ≤ 0) (haR : 0 ≤ aR) (hjL : aL ≤ Supp8.GB6.baseL U a)
    (hjR : Supp8.GB6.baseR U a ≤ aR)
    (hav : ∀ t : ℝ, 0 ≤ t → t ≤ T → ∀ z : ℝ, aL < z → z < aR → z ≠ 0 → loewnerTip (shiftDrive U a) t ≠ (z : ℂ))
    (hret : ∀ t : ℝ, 0 < t → t ≤ T → loewnerTip (shiftDrive U a) t ≠ 0)
    (hH : 0 < T → η (a + T) ∈ H) :
    SplitFree r aL aR ∧ (0 < T → loewnerTip (shiftDrive U a) T ∈ H) := by
  set ψ := loewnerTip (shiftDrive U a) with hψdef
  obtain ⟨hψ, -⟩ := hη.isLoewnerTrace_shift_and_extendFrom hU hU0 ha
  have hUa : Continuous (shiftDrive U a) := QuantumZipper.RS.continuous_shiftDrive hU a
  set wN : ℝ≥0 → ℝ := fun t => shiftDrive U a t with hwN
  have hwc : Continuous wN := hUa.comp NNReal.continuous_coe
  have hw0 : wN 0 = 0 := by simp only [hwN, NNReal.coe_zero, QuantumZipper.RS.shiftDrive_zero]
  have hψ' : IsLoewnerTrace (fun s : ℝ => wN s.toNNReal) ψ := by
    refine (isLoewnerTrace_congr_drive fun t ht => ?_).1 hψ
    simp only [hwN, Real.coe_toNNReal _ ht]
  have hgen : IsGeneratingTrace wN ⊤ (fun t : ℝ≥0 => ψ t) := IsLoewnerTrace.isGeneratingTrace hψ'
  have htip : 0 < T → ψ T ∈ H := fun hT =>
    shiftTip_mem_H hU hU0 hη ha T.coe_nonneg (hH hT) hjL hjR (hav T T.coe_nonneg le_rfl)
      (hret T (NNReal.coe_pos.2 hT) le_rfl)
  have hvis : ∀ t : ℝ≥0, t ≤ T → (ψ t).im = 0 → (ψ t).re ∉ Ioo aL 0 ∧ (ψ t).re ∉ Ioo 0 aR := by
    intro t ht him
    have hp : ψ t = (((ψ t).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    have htT : (t : ℝ) ≤ T := NNReal.coe_le_coe.2 ht
    refine ⟨fun hm => hav t t.coe_nonneg htT _ hm.1 (hm.2.trans_le haR) hm.2.ne hp,
      fun hm => hav t t.coe_nonneg htT _ (haL.trans_lt hm.1) hm.2 hm.1.ne' hp⟩
  have hTζ : (T : ℝ≥0∞) < ⊤ := ENNReal.coe_lt_top
  have heq : EqOn (rdrv r) (fun x : ℝ => wN x.toNNReal) (Icc 0 T) := by
    intro v hv
    rw [hrd v hv]
    simp only [hwN, Real.coe_toNNReal _ hv.1]
  refine ⟨?_, htip⟩
  unfold SplitFree
  rw [hrt]
  have eR : markPos (rdrv r) T = markPos (fun x : ℝ => wN x.toNNReal) T :=
    funext (Sec7.StripSideHeightProb.markPos_congr heq)
  have eL : markPosL (rdrv r) T = markPosL (fun x : ℝ => wN x.toNNReal) T :=
    funext (Sec7.StripSideHeightProb.markPosL_congr heq)
  rw [eR, eL]
  exact ⟨splitFreeR_of_trace hwc hw0 hTζ hgen haR (fun t ht him => (hvis t ht him).2) htip,
    splitFreeL_of_trace hwc hw0 hTζ hgen haL (fun t ht him => (hvis t ht him).1) htip⟩

/-- **The seed image of a window with an interior tip is positive.** -/
theorem markPos_zero_pos_window {r : RecData} {T : ℝ≥0} (hrt : rtime r = T) (hT : 0 < T) (hU : Continuous U)
    (hU0 : U 0 = 0) (hη : IsLoewnerTrace U η) {a : ℝ} (ha : 0 ≤ a)
    (hrd : ∀ v ∈ Icc (0 : ℝ) T, rdrv r v = shiftDrive U a v) (htip : loewnerTip (shiftDrive U a) T ∈ H) :
    0 < markPos (rdrv r) (rtime r) 0 ∧ markPosL (rdrv r) (rtime r) 0 < 0 := by
  obtain ⟨hψ, -⟩ := hη.isLoewnerTrace_shift_and_extendFrom hU hU0 ha
  have hUa : Continuous (shiftDrive U a) := QuantumZipper.RS.continuous_shiftDrive hU a
  have hUa0 : shiftDrive U a 0 = 0 := QuantumZipper.RS.shiftDrive_zero U a
  have hT' : (0 : ℝ) < T := NNReal.coe_pos.2 hT
  have heq : EqOn (rdrv r) (shiftDrive U a) (Icc 0 T) := fun v hv => hrd v hv
  rw [hrt]
  have hR := Sec5.CrossCond.Gen.chartAR_pos_of_interior_tip hψ htip hUa hUa0 hT'
  have hL := Sec5.CrossCond.Gen.chartAL_neg_of_interior_tip hψ htip hUa hUa0 hT'
  constructor
  · rw [Sec7.StripSideHeightProb.markPos_congr heq, Sec5.CrossCond.Gen.markPos_eq_rightImg_of_nonneg hUa hUa0
      hT'.le le_rfl]
    exact hR
  · rw [Sec7.StripSideHeightProb.markPosL_congr heq]
    unfold markPosL
    have hUn : Continuous fun s => -shiftDrive U a s := hUa.neg
    rw [Sec5.CrossCond.Gen.markPos_eq_rightImg_of_nonneg hUn (by simp [hUa0]) hT'.le (le_of_eq neg_zero.symm)]
    simp only [neg_zero]
    unfold WangWu.chartAL at hL
    linarith

/-! ### Junctions dominate the stage-1 base images -/

section Junction

variable {R : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R 0 = 0) {b : ℕ → ℝ≥0} (hb : Monotone b) (cf : RecData)
  {U : ℝ → ℝ} (hUc : Continuous U) {B : ℝ≥0}
  (hU : ∀ t : ℝ, 0 ≤ t → (b 1 : ℝ) + t ≤ B → U t = GW2Bh.rp R (b 1 + t) - GW2Bh.rp R (b 1))
include hR hR0 hb hUc hU

omit hR hR0 hb hUc hU in
theorem junctionR_nonneg : ∀ k, 0 ≤ GW2Sdp.junctionR k (pastOf cf R b k)
  | 0 => le_rfl
  | k + 1 => by
    change 0 ≤ markPos (rdrv (recOf (((b (k + 1) - b k : ℝ≥0)) : ℝ≥0∞) (fun u => GW2Rd.stgDrv R (b k) u, ⊤)))
      (rtime (recOf (((b (k + 1) - b k : ℝ≥0)) : ℝ≥0∞) (fun u => GW2Rd.stgDrv R (b k) u, ⊤)))
      (GW2Sdp.junctionR k (pastOf cf R b k))
    rw [GW2Bh.rtime_stage]
    exact GW2Bh.markPos_nonneg (continuous_rdrv _) (rdrv_zero _) (NNReal.coe_nonneg _) (junctionR_nonneg k)

omit hR hR0 hb hUc hU in
theorem junctionL_nonpos : ∀ k, GW2Sdp.junctionL k (pastOf cf R b k) ≤ 0
  | 0 => le_rfl
  | k + 1 => by
    change markPosL (rdrv (recOf (((b (k + 1) - b k : ℝ≥0)) : ℝ≥0∞) (fun u => GW2Rd.stgDrv R (b k) u, ⊤)))
      (rtime (recOf (((b (k + 1) - b k : ℝ≥0)) : ℝ≥0∞) (fun u => GW2Rd.stgDrv R (b k) u, ⊤)))
      (GW2Sdp.junctionL k (pastOf cf R b k)) ≤ 0
    rw [GW2Bh.rtime_stage]
    unfold markPosL
    have h := GW2Bh.markPos_nonneg (w := fun s => -rdrv (recOf (((b (k + 1) - b k : ℝ≥0)) : ℝ≥0∞)
        (fun u => GW2Rd.stgDrv R (b k) u, ⊤)) s) (continuous_rdrv _).neg (by simp [rdrv_zero])
      (NNReal.coe_nonneg (b (k + 1) - b k)) (neg_nonneg.2 (junctionL_nonpos k))
    linarith

omit hR hR0 hUc in
theorem shiftDrv_eq_of_le {k : ℕ} (hk : 1 ≤ k) (hkB : b (k + 1) ≤ B) :
    ∀ v ∈ Icc (0 : ℝ) ((b (k + 1) - b k : ℝ≥0) : ℝ),
      Sec5.Prop59NodeTree.shiftDrv (GW2Bh.rp R) (b k) v =
        Sec5.Prop59NodeTree.shiftDrv U ((b k : ℝ) - b 1) v := by
  intro v hv
  have h1k : b 1 ≤ b k := hb hk
  have hkk : b k ≤ b (k + 1) := hb (Nat.le_succ k)
  have hv2 : v ≤ (b (k + 1) : ℝ) - b k := by rw [← NNReal.coe_sub hkk]; exact hv.2
  have h1k' : (b 1 : ℝ) ≤ b k := NNReal.coe_le_coe.2 h1k
  have hkB' : (b (k + 1) : ℝ) ≤ B := NNReal.coe_le_coe.2 hkB
  unfold Sec5.Prop59NodeTree.shiftDrv
  rw [hU _ (by linarith [hv.1]) (by linarith), hU _ (by linarith) (by linarith)]
  have e1 : (b 1 : ℝ) + ((b k : ℝ) - b 1 + v) = b k + v := by ring
  have e2 : (b 1 : ℝ) + ((b k : ℝ) - b 1) = b k := by ring
  rw [e1, e2]
  ring

omit hR0 in
/-- **The right junctions dominate the right base images of the stage-1 driver.** -/
theorem baseR_le_junctionR : ∀ k : ℕ, 1 ≤ k → b k ≤ B →
    Supp8.GB6.baseR U ((b k : ℝ) - b 1) ≤ GW2Sdp.junctionR k (pastOf cf R b k)
  | 0, h, _ => absurd h (by norm_num)
  | 1, _, h1B => by
    have hU0 : U 0 = 0 := by rw [hU 0 le_rfl (by simpa using h1B)]; simp
    rw [sub_self]
    exact (baseR_zero_le hUc hU0).trans (junctionR_nonneg (R := R) (b := b) cf 1)
  | k + 2, _, hkB => by
    have hk1 : 1 ≤ k + 1 := Nat.le_add_left 1 k
    have hkB' : b (k + 1) ≤ B := (hb (Nat.le_succ (k + 1))).trans hkB
    have ih := baseR_le_junctionR (k + 1) hk1 hkB'
    have hkk : b (k + 1) ≤ b (k + 2) := hb (Nat.le_succ (k + 1))
    have h1k : (b 1 : ℝ) ≤ b (k + 1) := NNReal.coe_le_coe.2 (hb hk1)
    have ha0 : 0 ≤ (b (k + 1) : ℝ) - b 1 := by linarith
    have hx := junctionR_nonneg (R := R) (b := b) cf (k + 1)
    change Supp8.GB6.baseR U ((b (k + 2) : ℝ) - b 1) ≤
      markPos (rdrv (recOf (((b (k + 2) - b (k + 1) : ℝ≥0)) : ℝ≥0∞) (fun u => GW2Rd.stgDrv R (b (k + 1)) u, ⊤)))
        (rtime (recOf (((b (k + 2) - b (k + 1) : ℝ≥0)) : ℝ≥0∞) (fun u => GW2Rd.stgDrv R (b (k + 1)) u, ⊤)))
        (GW2Sdp.junctionR (k + 1) (pastOf cf R b (k + 1)))
    rw [GW2Bh.markPos_stage_eq hR (b (k + 1)) (b (k + 2) - b (k + 1)) hx]
    have hcU := Sec5.Prop59NodeTree.continuous_shiftDrv hUc ((b (k + 1) : ℝ) - b 1)
    have hcongr : ∀ v ∈ Icc (0 : ℝ) ((b (k + 2) - b (k + 1) : ℝ≥0) : ℝ),
        Sec5.Prop59NodeTree.shiftDrv (GW2Bh.rp R) (b (k + 1)) v =
          Sec5.Prop59NodeTree.shiftDrv U ((b (k + 1) : ℝ) - b 1) v := shiftDrv_eq_of_le hb hU hk1 hkB
    have hT0 : (0 : ℝ) ≤ ((b (k + 2) - b (k + 1) : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
    rw [Supp8.GB6.rightImg_congr hcU hT0 hcongr, hcongr _ ⟨hT0, le_rfl⟩]
    have hmono := Sec7.Aux37Side.rightImg_mono hcU ih hT0
    have hflow := Sec5.Prop59NodeTree.rightImg_shiftDrv hUc ha0 hT0 0
    have hT' : ((b (k + 2) - b (k + 1) : ℝ≥0) : ℝ) = (b (k + 2) : ℝ) - b (k + 1) := NNReal.coe_sub hkk
    have hsum : (b (k + 1) : ℝ) - b 1 + ((b (k + 2) - b (k + 1) : ℝ≥0) : ℝ) = (b (k + 2) : ℝ) - b 1 := by
      rw [hT']; ring
    have hev : Sec5.Prop59NodeTree.shiftDrv U ((b (k + 1) : ℝ) - b 1) ((b (k + 2) - b (k + 1) : ℝ≥0) : ℝ) =
        U ((b (k + 1) : ℝ) - b 1 + ((b (k + 2) - b (k + 1) : ℝ≥0) : ℝ)) - U ((b (k + 1) : ℝ) - b 1) := rfl
    rw [hev, hsum]
    unfold Supp8.GB6.baseR at hmono ⊢
    rw [hflow, hsum] at hmono
    linarith

omit hR0 in
/-- **The left junctions are dominated by the left base images of the stage-1 driver.** -/
theorem junctionL_le_baseL : ∀ k : ℕ, 1 ≤ k → b k ≤ B →
    GW2Sdp.junctionL k (pastOf cf R b k) ≤ Supp8.GB6.baseL U ((b k : ℝ) - b 1)
  | 0, h, _ => absurd h (by norm_num)
  | 1, _, h1B => by
    have hU0 : U 0 = 0 := by rw [hU 0 le_rfl (by simpa using h1B)]; simp
    rw [sub_self]
    exact (junctionL_nonpos (R := R) (b := b) cf 1).trans (zero_le_baseL hUc hU0)
  | k + 2, _, hkB => by
    have hk1 : 1 ≤ k + 1 := Nat.le_add_left 1 k
    have hkB' : b (k + 1) ≤ B := (hb (Nat.le_succ (k + 1))).trans hkB
    have ih := junctionL_le_baseL (k + 1) hk1 hkB'
    have hkk : b (k + 1) ≤ b (k + 2) := hb (Nat.le_succ (k + 1))
    have h1k : (b 1 : ℝ) ≤ b (k + 1) := NNReal.coe_le_coe.2 (hb hk1)
    have ha0 : 0 ≤ (b (k + 1) : ℝ) - b 1 := by linarith
    have hx := junctionL_nonpos (R := R) (b := b) cf (k + 1)
    change markPosL (rdrv (recOf (((b (k + 2) - b (k + 1) : ℝ≥0)) : ℝ≥0∞) (fun u => GW2Rd.stgDrv R (b (k + 1)) u, ⊤)))
        (rtime (recOf (((b (k + 2) - b (k + 1) : ℝ≥0)) : ℝ≥0∞) (fun u => GW2Rd.stgDrv R (b (k + 1)) u, ⊤)))
        (GW2Sdp.junctionL (k + 1) (pastOf cf R b (k + 1))) ≤ Supp8.GB6.baseL U ((b (k + 2) : ℝ) - b 1)
    rw [GW2Bh.markPosL_stage_eq hR (b (k + 1)) (b (k + 2) - b (k + 1)) hx]
    have hcongr : ∀ v ∈ Icc (0 : ℝ) ((b (k + 2) - b (k + 1) : ℝ≥0) : ℝ),
        Sec5.Prop59NodeTree.shiftDrv (GW2Bh.rp R) (b (k + 1)) v =
          Sec5.Prop59NodeTree.shiftDrv U ((b (k + 1) : ℝ) - b 1) v := shiftDrv_eq_of_le hb hU hk1 hkB
    have hT0 : (0 : ℝ) ≤ ((b (k + 2) - b (k + 1) : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
    have hcongr' : ∀ v ∈ Icc (0 : ℝ) ((b (k + 2) - b (k + 1) : ℝ≥0) : ℝ),
        (fun v => -Sec5.Prop59NodeTree.shiftDrv (GW2Bh.rp R) (b (k + 1)) v) v =
          Sec5.Prop59NodeTree.shiftDrv (fun r => -U r) ((b (k + 1) : ℝ) - b 1) v := by
      intro v hv
      simp only
      rw [hcongr v hv]
      simp only [Sec5.Prop59NodeTree.shiftDrv]
      ring
    have hcU := Sec5.Prop59NodeTree.continuous_shiftDrv (w := fun r => -U r) hUc.neg ((b (k + 1) : ℝ) - b 1)
    rw [Supp8.GB6.rightImg_congr hcU hT0 hcongr', hcongr _ ⟨hT0, le_rfl⟩]
    have hle : rightImg (fun r => -U r) 0 ((b (k + 1) : ℝ) - b 1) - (fun r => -U r) ((b (k + 1) : ℝ) - b 1) ≤
        -GW2Sdp.junctionL (k + 1) (pastOf cf R b (k + 1)) := by
      unfold Supp8.GB6.baseL at ih
      simp only
      linarith
    have hmono := Sec7.Aux37Side.rightImg_mono hcU hle hT0
    have hflow := Sec5.Prop59NodeTree.rightImg_shiftDrv (w := fun r => -U r) hUc.neg ha0 hT0 0
    have hT' : ((b (k + 2) - b (k + 1) : ℝ≥0) : ℝ) = (b (k + 2) : ℝ) - b (k + 1) := NNReal.coe_sub hkk
    have hsum : (b (k + 1) : ℝ) - b 1 + ((b (k + 2) - b (k + 1) : ℝ≥0) : ℝ) = (b (k + 2) : ℝ) - b 1 := by
      rw [hT']; ring
    have hev : Sec5.Prop59NodeTree.shiftDrv U ((b (k + 1) : ℝ) - b 1) ((b (k + 2) - b (k + 1) : ℝ≥0) : ℝ) =
        U ((b (k + 1) : ℝ) - b 1 + ((b (k + 2) - b (k + 1) : ℝ≥0) : ℝ)) - U ((b (k + 1) : ℝ) - b 1) := rfl
    rw [hflow, hsum] at hmono
    rw [hev, hsum]
    unfold Supp8.GB6.baseL
    linarith

end Junction

end InteractingSLE.Theorem14.GW2Rj
