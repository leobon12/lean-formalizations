/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5FreshSplit
import InteractingSLE.Spec.Sec5.Prop59NodeTreeFlow
import InteractingSLE.Spec.Sec7.Lemma71PTrace

/-!
# Lemma R.5's seed-interval landings at a real corner, from the counterflow's no-return

Packet PROVE-R5-FRESHTIP (second round). `R5Fresh.R7SeedLand(Inf)` (every coordinate of the current open seed
interval lands in `ℍ`) is proved pathwise for pockets whose corner is not real (`r7SeedLand_of_corner_mem_H`). Here the
remaining case — the pocket closes at the flow target, its corner is the counterflow's start `0` — is reduced to
**the counterflow does not return to its start**:

* `rightImg_le_add_index`, `rightImg_sub_le_shift`: the centred seed image at `t` differs from the seed image at `t − s`
  of the increment started at `s` by at most the seed image at `s` (`Prop59NodeTree.rightImg_shiftDrv` and the
  `1`-Lipschitz flow of alive points);
* **`exists_mem_shift_seed_interval`**: a coordinate of the open seed interval at `t` is in the open seed interval of
  the increment started at a small `s > 0`;
* **`extendFrom_ne_zero_of_noReturn`**: *base-point (G5)* — if a continuous Loewner trace does not return to `0` on
  `(0, t]`, no coordinate strictly between the seed images at `t` has boundary value `0` (the coordinate is a middle
  coordinate of a recent increment, whose boundary value is a point `γ(s + r)` of the trace, `s + r > 0`);
* `exists_isLoewnerTrace_of_driven'`, **`not_tendsto_corner`**: the relative chain version (a current coordinate does
  not land at a point where the base coordinate is continuous with value `0`);
* `cfArcR_one_mem_H_or_eq_zero`, **`capTrace_ne_zero_of_noReturn`**, **`r7SeedLand_of_noReturn`** and their seed-opening
  twins: `R7SeedLand(Inf)` at every capacity from "almost surely `η(t) ≠ 0` for `t > 0`".

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open QuantumZipper.RS (shiftDrive)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Fresh

open MartChar.RealFlow

/-! ### Base-point (G5) for a Loewner chain whose trace does not return to `0` -/

/-- **The geometric image is `1`-Lipschitz in the index**: `V_t(x') ≤ V_t(x) + (x' − x)` for `x ≤ x'`. -/
theorem rightImg_le_add_index {w : ℝ → ℝ} (hw : Continuous w) {x x' t : ℝ} (ht : 0 ≤ t) (hxx : x ≤ x') :
    rightImg w x' t ≤ rightImg w x t + (x' - x) := by
  rcases hxx.eq_or_lt with rfl | hlt
  · simp
  rw [← sub_le_iff_le_add]
  refine le_csInf (imgSet_nonempty hw x ht) ?_
  rintro _ ⟨y, hxy, hy, rfl⟩
  have hd : y < y + (x' - x) := by linarith
  have hy' : Alive w (y + (x' - x)) t := hy.of_le hw hd.le ht
  have h1 := rightImg_le_gImg hw ht (show x' < y + (x' - x) by linarith) hy'
  have h2 := (cflow_lt_and_sub_le hw hy hd ht ⟨ht, le_rfl⟩).2
  simp only [gImg] at h1 ⊢
  linarith

/-- **The seed image at `t` against the increment's seed image** (right side): with `Ṽ = V(s + ·) − V s`,
`h = t − s`, `R_s = V_s(0) − V(s) ≥ 0`: `R_t ≤ (Ṽ_h(0) − Ṽ(h)) + R_s` (centred images). -/
theorem rightImg_sub_le_shift {V : ℝ → ℝ} (hV : Continuous V) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    rightImg V 0 t - V t ≤ (rightImg (shiftDrive V s) 0 (t - s) - shiftDrive V s (t - s)) +
      (rightImg V 0 s - V s) := by
  have hh : 0 ≤ t - s := sub_nonneg.2 hst
  have hVs : Continuous (shiftDrive V s) := QuantumZipper.RS.continuous_shiftDrive hV s
  have heq := Sec5.Prop59NodeTree.rightImg_shiftDrv hV hs hh 0
  change rightImg (shiftDrive V s) (rightImg V 0 s - V s) (t - s) = rightImg V 0 (s + (t - s)) - V s at heq
  rw [add_sub_cancel] at heq
  have hR0 : 0 ≤ rightImg V 0 s - V s := sub_nonneg.2 (le_rightImg hV 0 hs)
  have hlip := rightImg_le_add_index hVs hh hR0
  rw [heq, sub_zero] at hlip
  have hVt : shiftDrive V s (t - s) = V t - V s := by simp only [shiftDrive, add_sub_cancel]
  rw [hVt]
  linarith

/-- **A coordinate of the open seed interval lies in the open seed interval of a recent-start increment**: for
`x ∈ (L_t, R_t)` (centred seed images at `t > 0`) some `s ∈ (0, t)` has `x` strictly between the centred seed
images at `t − s` of the chain driven by `V(s + ·) − V s` (the latter differ from `L_t, R_t` by at most
`|L_s|, R_s`, which tend to `0`). -/
theorem exists_mem_shift_seed_interval {V : ℝ → ℝ} (hV : Continuous V) (hV0 : V 0 = 0) {t : ℝ} (ht : 0 < t)
    {x : ℝ} (hxL : -rightImg (fun r => -V r) 0 t - V t < x) (hxR : x < rightImg V 0 t - V t) :
    ∃ s ∈ Ioo 0 t, -rightImg (fun r => -shiftDrive V s r) 0 (t - s) - shiftDrive V s (t - s) < x ∧
      x < rightImg (shiftDrive V s) 0 (t - s) - shiftDrive V s (t - s) := by
  have hVn : Continuous fun r => -V r := hV.neg
  have hVn0 : (fun r => -V r) 0 = 0 := by simp [hV0]
  set ε := min (rightImg V 0 t - V t - x) (x - (-rightImg (fun r => -V r) 0 t - V t)) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
  -- the seeds tend to `0` at `0`
  have hR : ContinuousWithinAt (fun s => rightImg V 0 s - V s) (Ici 0) 0 :=
    ((continuousOn_rightImg hV 0).sub hV.continuousOn) 0 (Set.mem_Ici.2 le_rfl)
  have hL : ContinuousWithinAt (fun s => rightImg (fun r => -V r) 0 s + V s) (Ici 0) 0 :=
    ((continuousOn_rightImg hVn 0).add hV.continuousOn) 0 (Set.mem_Ici.2 le_rfl)
  have hR0 : rightImg V 0 0 - V 0 = 0 := by rw [rightImg_zero hV hV0 le_rfl, hV0, sub_zero]
  have hL0 : rightImg (fun r => -V r) 0 0 + V 0 = 0 := by rw [rightImg_zero hVn hVn0 le_rfl, hV0, add_zero]
  rw [Metric.continuousWithinAt_iff] at hR hL
  obtain ⟨δ₁, hδ₁, h₁⟩ := hR ε hε0
  obtain ⟨δ₂, hδ₂, h₂⟩ := hL ε hε0
  set s := min (t / 2) (min δ₁ δ₂ / 2) with hsdef
  have hs0 : 0 < s := lt_min (half_pos ht) (half_pos (lt_min hδ₁ hδ₂))
  have hst : s < t := lt_of_le_of_lt (min_le_left _ _) (half_lt_self ht)
  have hsd₁ : dist s 0 < δ₁ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hs0]
    linarith [min_le_right (t / 2) (min δ₁ δ₂ / 2), min_le_left δ₁ δ₂]
  have hsd₂ : dist s 0 < δ₂ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hs0]
    linarith [min_le_right (t / 2) (min δ₁ δ₂ / 2), min_le_right δ₁ δ₂]
  have e₁ := h₁ (show s ∈ Ici (0 : ℝ) from hs0.le) hsd₁
  have e₂ := h₂ (show s ∈ Ici (0 : ℝ) from hs0.le) hsd₂
  rw [hR0, Real.dist_eq, sub_zero] at e₁
  rw [hL0, Real.dist_eq, sub_zero] at e₂
  have e₁' := (abs_lt.1 e₁).2
  have e₂' := (abs_lt.1 e₂).2
  refine ⟨s, ⟨hs0, hst⟩, ?_, ?_⟩
  · have key := rightImg_sub_le_shift hVn hs0.le hst.le
    have hshift : shiftDrive (fun r => -V r) s = fun r => -shiftDrive V s r := by
      funext r
      simp only [shiftDrive]
      ring
    rw [hshift] at key
    have hεL := min_le_right (rightImg V 0 t - V t - x) (x - (-rightImg (fun r => -V r) 0 t - V t))
    simp only [sub_neg_eq_add] at key
    linarith
  · have key := rightImg_sub_le_shift hV hs0.le hst.le
    have hεR := min_le_left (rightImg V 0 t - V t - x) (x - (-rightImg (fun r => -V r) 0 t - V t))
    linarith

open YuanSimpleApprox in
/-- **The base point of a Loewner chain is not a middle landing when the trace does not return to it.** Let `V`
drive a continuous Loewner trace `γ` with `γ(s) ≠ 0` for `s ∈ (0, t]`. Then no coordinate strictly between the centred
seed images at `t` has boundary value `0`: for a recent start `s` the coordinate is a middle coordinate of the
increment (`exists_mem_shift_seed_interval`), whose boundary value is a point of the increment trace
(`Lemma71P.mem_image_of_mid`), and `F̄_s` maps that point to `γ(s + r)`, `s + r > 0`
(`IsLoewnerTrace.extendFrom_shift_tip`). -/
theorem extendFrom_ne_zero_of_noReturn {V : ℝ → ℝ} {γ : ℝ → ℂ} (hγ : IsLoewnerTrace V γ) (hV : Continuous V)
    (hV0 : V 0 = 0) {t : ℝ} (ht : 0 < t) (hnr : ∀ s ∈ Ioc (0 : ℝ) t, γ s ≠ 0) {x : ℝ}
    (hxL : -rightImg (fun r => -V r) 0 t - V t < x) (hxR : x < rightImg V 0 t - V t) :
    extendFrom H (fwdMapInv V t) x ≠ 0 := by
  obtain ⟨s, hs, hsL, hsR⟩ := exists_mem_shift_seed_interval hV hV0 ht hxL hxR
  have hσ := isLoewnerTrace_shift' hγ hV hV0 hs.1.le
  have hmid := Lemma71P.mem_image_of_mid hσ (QuantumZipper.RS.continuous_shiftDrive hV s)
    (QuantumZipper.RS.shiftDrive_zero V s) (sub_nonneg.2 hs.2.le) hsL hsR
  obtain ⟨r, hr, hreq⟩ := hmid
  have hxbar : ((x : ℝ) : ℂ) ∈ Hbar := show (0 : ℝ) ≤ ((x : ℝ) : ℂ).im by rw [ofReal_im]
  have hcomp := trMap_trMap hγ hV hV0 le_rfl hs.1.le hs.2.le hxbar
  rw [trMap_zero_left hV0 s, trMap_zero_left hV0 t] at hcomp
  rw [← hcomp]
  have htr : trMap V s t (x : ℂ) = loewnerTip (shiftDrive V s) r := hreq.symm
  rw [htr, (hγ.extendFrom_shift_tip hV hV0 hs.1.le hr.1).2.1]
  exact hnr (s + r) ⟨by linarith [hs.1, hr.1], by linarith [hr.2]⟩

/-! ### The relative chain -/

section Relative

open PocketTraversal PocketStop Lemma71C

/-- `exists_isLoewnerTrace_of_driven` with the trace identity: the global trace agrees with the capacity trace on
`[0, q₁]`. -/
theorem exists_isLoewnerTrace_of_driven' {γ₀ : ℝ → ℂ} (hγ : IsDrivenCurve γ₀) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife γ₀) :
    ∃ (V : ℝ → ℝ) (γ₁ : ℝ → ℂ) (q₁ : ℝ), (q : ℝ) < q₁ ∧ Continuous V ∧ V 0 = 0 ∧ IsLoewnerTrace V γ₁ ∧
      (∀ s ∈ Icc (0 : ℝ) q₁, segDriver γ₀ s.toNNReal = V s) ∧ ∀ s ∈ Icc (0 : ℝ) q₁, γ₁ s = capTrace γ₀ s.toNNReal := by
  obtain ⟨q₂, hqq₂, hq₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hq
  have hqq₂' : (q : ℝ) < q₂ := by exact_mod_cast hqq₂
  set W₁ := Ito.clampDrv (Ito.rpath fun s => segDriver γ₀ s) q₂
  have hW₁ : Continuous W₁ := Ito.continuous_clampDrv q₂.coe_nonneg
    (Ito.continuousOn_rpath hγ.segDriver_spec.2.1 hq₂)
  have heq₁ : EqOn W₁ (Ito.rpath fun s => segDriver γ₀ s) (Icc 0 q₂) := Ito.clampDrv_eqOn
  have hW₁0 : W₁ 0 = 0 := by
    rw [heq₁ ⟨le_rfl, q₂.coe_nonneg⟩]
    simpa only [Ito.rpath, Real.toNNReal_zero] using hγ.segDriver_spec.1
  have hLT := Theorem14.CounterflowRange.isLoewnerTraceLT_of_isGeneratingTrace (hγ.isGeneratingTrace hq₂)
  have hLT₁ : IsLoewnerTraceLT W₁ q₂ (fun s : ℝ => capTrace γ₀ s.toNNReal) :=
    ⟨hLT.1, hLT.2.1, fun s hs hsq => by
      rw [← hLT.2.2 s hs hsq]
      exact fwdHull_eq_of_eqOn hs hsq fun r hr => heq₁ hr⟩
  set q₁ : ℝ := ((q : ℝ) + q₂) / 2
  have hqq₁ : (q : ℝ) < q₁ := by dsimp [q₁]; linarith
  have hq₁q₂ : q₁ < q₂ := by dsimp [q₁]; linarith
  have hq₁0 : 0 ≤ q₁ := q.coe_nonneg.trans hqq₁.le
  refine ⟨YuanCorollary13.extDrive W₁ q₁, YuanCorollary13.extTrace W₁ (fun s : ℝ => capTrace γ₀ s.toNNReal) q₁, q₁,
    hqq₁, YuanCorollary13.continuous_extDrive hW₁, YuanCorollary13.extDrive_zero hW₁0 hq₁0,
    hLT₁.isLoewnerTrace_ext hW₁ hW₁0 hq₁0 hq₁q₂, fun s hs => ?_, fun s hs => YuanCorollary13.extTrace_eq hs.2⟩
  rw [YuanCorollary13.extDrive_eq hs.2]
  exact (heq₁ ⟨hs.1, hs.2.trans hq₁q₂.le⟩).symm

variable {Ω : Type*} {c : Ω → Chart} {γ : Ω → ℝ → ℂ} {ω : Ω}

/-- **A current coordinate does not land at a point where the base coordinate is `0`**, if the relative capacity trace
does not return to `0`. Let `ψ` invert the base chart on `ℍ` and be continuous, with value `0`, at `y₀` along a set
`S` containing the current inverse. If a coordinate `u` of the open seed interval at `q > 0` landed at `y₀`, then
`ψ ∘ cur⁻¹ = F_q` would give `F̄_q(u) = 0`, contrary to `extendFrom_ne_zero_of_noReturn`. -/
theorem not_tendsto_corner {nL nR : ℕ} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    (hxL : xL ω 0 = 0) (hxR : xR ω 0 = 0) (hγ : IsDrivenCurve (γ ω)) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife (γ ω)) (hq0 : 0 < q) {ψ : ℂ → ℂ} (hψc : ∀ w ∈ H, ψ ((c ω).2.1 w) = w)
    {S : Set ℂ} {y₀ : ℂ} (hS : ∀ z ∈ H, (relChart c γ q ω).2.1 z ∈ S) (hψy : ContinuousWithinAt ψ S y₀)
    (hψ0 : ψ y₀ = 0) (hnr : ∀ s : ℝ, 0 < s → s ≤ q → capTrace (γ ω) s.toNNReal ≠ 0) {u : ℝ}
    (hu : u ∈ Ioo (geomLW (fun t ω => segDriver (γ ω) t) xL 0 q ω - segDriver (γ ω) q)
      (geomRW (fun t ω => segDriver (γ ω) t) xR 0 q ω - segDriver (γ ω) q)) :
    ¬ Tendsto (relChart c γ q ω).2.1 (𝓝[H] (u : ℂ)) (𝓝 y₀) := by
  intro hlim
  obtain ⟨V, γ₁, q₁, hqq₁, hV, hV0, htr, hVeq, hγ₁⟩ := exists_isLoewnerTrace_of_driven' hγ hq
  have hrel : relChart c γ q ω = (c ω).loewner V q := loewner_congr (c ω) q.coe_nonneg hqq₁ hVeq
  have hEqV : EqOn (fun r : ℝ => (fun t ω => segDriver (γ ω) t) r.toNNReal ω) V (Icc 0 (q : ℝ)) :=
    fun r hr => hVeq r ⟨hr.1, hr.2.trans hqq₁.le⟩
  obtain ⟨hLeq, hReq⟩ := geom_positions_eq_of_driver_eqOn (fun t ω => segDriver (γ ω) t) xL xR hV hEqV
  have hL' := congrFun hLeq 0
  have hR' := congrFun hReq 0
  simp only [hxL, hxR, neg_zero] at hL' hR'
  rw [hL', hR'] at hu
  have hB := htr.hasBdryLimits hV hV0 q.coe_nonneg
  have hubar : (u : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (u : ℂ).im by rw [ofReal_im]
  have hb : Tendsto (fwdMapInv V q) (𝓝[H] (u : ℂ)) (𝓝 (extendFrom H (fwdMapInv V q) u)) := hB.tendsto hubar
  have h1 : Tendsto (fun z => ψ ((relChart c γ q ω).2.1 z)) (𝓝[H] (u : ℂ)) (𝓝 (ψ y₀)) :=
    hψy.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, eventually_nhdsWithin_of_forall hS⟩)
  have h2 : Tendsto (fun z => ψ ((relChart c γ q ω).2.1 z)) (𝓝[H] (u : ℂ))
      (𝓝 (extendFrom H (fwdMapInv V q) u)) :=
    hb.congr' (eventually_nhdsWithin_of_forall fun z hz => by
      rw [hrel]
      exact (hψc _ (QuantumZipper.RS.fwdMapInv_mem_H hV hV0 q.coe_nonneg hz)).symm)
  have := R5Lift.nhdsWithin_H_neBot u
  have hb0 : extendFrom H (fwdMapInv V q) u = 0 := (tendsto_nhds_unique h2 h1).trans hψ0
  have hnr' : ∀ s ∈ Ioc (0 : ℝ) q, γ₁ s ≠ 0 := fun s hs => by
    rw [hγ₁ s ⟨hs.1.le, hs.2.trans hqq₁.le⟩]
    exact hnr s hs.1 hs.2
  exact extendFrom_ne_zero_of_noReturn htr hV hV0 (NNReal.coe_pos.2 hq0) hnr' hu.1 hu.2 hb0

end Relative

/-! ### Bounded change pocket -/

section Bounded

open LocalSets PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt PocketCoupling PocketStopSide PhaseSel
  PocketWordAssembly PocketSeedOpen PocketCoord PocketJordan R5Phase R5Same R5Ref Sec6 PocketStopWallsFin
  PocketStopMarked R5Lift

/-- **The closing corner is in `ℍ` or is `0`** (bounded change pocket): `m(y₀)` with `y₀` an interior wall point or
the flow target (`cfPt 1 = 0`). -/
theorem cfArcR_one_mem_H_or_eq_zero {R L : ℝ≥0 → ℂ} {r : ℝ≥0} (h : IsChangeConfigInc R L r) :
    cfArcR R L r 1 ∈ H ∨ cfArcR R L r 1 = 0 := by
  have e : cfArcR R L r 1 = cfPt (WangWu.toDisc (Lemma71I.realPath R) (rightHi R L r)) := by simp [cfArcR]
  obtain ⟨hu, hv, huv, -⟩ := h.changeCorner_props
  have hαR := h.isDiscCrosscut_right
  rw [e]
  rcases hv.2.lt_or_eq with h1 | h1
  · exact Or.inl (cfPt_mem_H (hαR.mem_disc _ ⟨hu.1.trans_lt huv, h1⟩))
  · rw [h1, hαR.one]
    exact Or.inr cfPt_one

variable {Ω : Type*} [MeasurableSpace Ω] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}
  {A : Set Ω}

omit [MeasurableSpace Ω] in
/-- **The relative capacity trace does not return to the corner** (bounded change pocket): if the corner is `0` and
the counterflow does not return to `0`, the capacity trace of the traversal is nonzero at positive live capacities
(the traversal reads `ψ(η(t))` at a time `t` after the entrance with clock value `> 0`, and `ψ` is injective off the
pole with `ψ(corner) = 0`). -/
theorem capTrace_ne_zero_of_noReturn {W : Ω → ℝ → ℝ} {ω : Ω} (hcfg : IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) (hy₀ : cfArcR (R ω) (L ω) r 1 = 0)
    (hnr : ∀ t : ℝ, 0 < t → η ω t ≠ 0) {s : ℝ} (hs : 0 < s)
    (hsl : ENNReal.ofReal s < capLife (travAll R L r η ψ ω)) :
    capTrace (travAll R L r η ψ ω) s.toNNReal ≠ 0 := by
  obtain ⟨hP, hψ'⟩ := pocket_of_cfg hcfg hψ
  have hAC := hcfg.attach
  have hγ : IsDrivenCurve (travAll R L r η ψ ω) := (hcfg.isDrivenCurve hψ).1
  have hspec : 0 ≤ capInv (travAll R L r η ψ ω) s ∧
      capClock (travAll R L r η ψ ω) (capInv (travAll R L r η ψ ω) s) = s := hγ.capInv_spec hs.le hsl
  set u := capInv (travAll R L r η ψ ω) s with hudef
  have hc0 : capClock (travAll R L r η ψ ω) 0 = 0 := hγ.capClock_zero
  have hupos : 0 < u := by
    refine lt_of_le_of_ne hspec.1 fun h => ?_
    have h2 := hspec.2
    rw [← h, hc0] at h2
    linarith
  set L₀ := pocketClock (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) with hL₀
  have hL : 0 < L₀ := hP.clock_σ_pos hAC
  set v := clockOf L₀ u with hvdef
  have hv : v ∈ Ico 0 L₀ := clockOf_mem_Ico hL hspec.1
  have hvpos : 0 < v := by
    simp only [hvdef, clockOf]
    have : 0 < u / (1 + u) := by positivity
    positivity
  have hm := hP.erasedPath_mem hv
  have hpk := hcfg.conf.isCfPocket (PocketMarks.zero_notMem_closure_of_rightLo_pos hcfg.conf hcfg.bounded)
  have hy₀m : cfArcR (R ω) (L ω) r 1 ∈ closure (cfPocket (R ω) (L ω) r) \ {cfArcR (R ω) (L ω) r 0} := by
    refine ⟨frontier_subset_closure ?_, fun h => ?_⟩
    · rw [hpk.frontier_eq]
      exact Or.inl ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
    · have := hpk.inj₁ ⟨zero_le_one, le_rfl⟩ ⟨le_rfl, zero_le_one⟩ (mem_singleton_iff.1 h)
      exact one_ne_zero this
  intro h0
  have hval : capTrace (travAll R L r η ψ ω) s.toNNReal = ψ ω (erasedPath (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) v) := by
    simp only [capTrace, Real.coe_toNNReal _ hs.le]
    rfl
  rw [hval] at h0
  have heqp := hψ'.2.1 hm hy₀m (h0.trans hψ'.2.2.2.2.2.1.symm)
  have hf := hP.fibre_mem v
  have hcf := hP.clock_fibre (⟨hv.1, hv.2.le⟩ : v ∈ Icc 0 L₀)
  have hτ := hP.nonneg
  have hfpos : 0 < pocketFibre (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) v := by
    rcases (hτ.trans hf.1).lt_or_eq with h | h
    · exact h
    · exfalso
      have hfτ := le_antisymm (h ▸ hτ) hf.1
      rw [hfτ, IsReversePocket.clock_τ] at hcf
      linarith
  exact hnr _ hfpos (heqp.trans hy₀)

omit [MeasurableSpace Ω] in
/-- **The seed-interval landings at one sample from the counterflow's no-return** (bounded change pocket): if the
counterflow does not return to `0` at positive times, every coordinate of the current open seed interval lands in `ℍ`
(the only other candidate is the corner, which is then `0`, `not_tendsto_corner`). -/
theorem seedLand_of_noReturn_sample {W : Ω → ℝ → ℝ} {c : Ω → Chart} {ω : Ω} (hω : ω ∈ A)
    (hcfg : IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω)) (hψ : IsCfJordan (R ω) (L ω) r (ψ ω))
    (hc : (c ω).IsConformal) (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) {nL nR : ℕ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} (hxL : xL ω 0 = 0) (hxR : xR ω 0 = 0) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω)) (hnr : ∀ t : ℝ, 0 < t → η ω t ≠ 0) :
    ∀ u ∈ Ioo (geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) xL 0 q ω - segDriver (travAll R L r η ψ ω) q)
        (geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) xR 0 q ω - segDriver (travAll R L r η ψ ω) q),
      extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 u ∈ H := by
  intro u hu
  have hγ := (hcfg.isDrivenCurve hψ).1
  have hq0 : 0 < q := by
    rcases (show (0 : ℝ≥0) ≤ q from zero_le).eq_or_lt with h0q | h0q
    · exfalso
      subst h0q
      rw [seed_interval_eq_empty_zero (c := c) hxL hxR hγ hq] at hu
      exact hu
    · exact h0q
  obtain ⟨hland, hcl, -⟩ := current_landing hω hcfg hψ hc hdom heq hq u
  obtain ⟨hP, hψ'⟩ := pocket_of_cfg hcfg hψ
  have hpk := hcfg.conf.isCfPocket (PocketMarks.zero_notMem_closure_of_rightLo_pos hcfg.conf hcfg.bounded)
  rcases closure_cfPocket_subset_H_union_seed hpk hP.subset_H hcl with h | h
  · exact h
  rw [mem_singleton_iff] at h
  rcases cfArcR_one_mem_H_or_eq_zero hcfg.conf with h1 | h1
  · rw [h]
    exact h1
  exfalso
  have hx₀ : cfArcR (R ω) (L ω) r 0 ∉ cfPocket (R ω) (L ω) r := fun hx => by
    have hfr : cfArcR (R ω) (L ω) r 0 ∈ frontier (cfPocket (R ω) (L ω) r) := by
      rw [hpk.frontier_eq]
      exact Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
    rw [hpk.isOpen.frontier_eq] at hfr
    exact hfr.2 hx
  have hy₀m : cfArcR (R ω) (L ω) r 1 ∈ closure (cfPocket (R ω) (L ω) r) \ {cfArcR (R ω) (L ω) r 0} := by
    refine ⟨frontier_subset_closure ?_, fun h => ?_⟩
    · rw [hpk.frontier_eq]
      exact Or.inl ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
    · have := hpk.inj₁ ⟨zero_le_one, le_rfl⟩ ⟨le_rfl, zero_le_one⟩ (mem_singleton_iff.1 h)
      exact one_ne_zero this
  have hcur := isConformal_relChart_of_driven (c := c) hγ hq hc
  have hd := current_dom_eq hω hcfg hψ hc hdom heq hq
  refine not_tendsto_corner (c := c) hxL hxR hγ hq hq0 (ψ := ψ ω) (fun w hw => ?_)
    (S := closure (cfPocket (R ω) (L ω) r) \ {cfArcR (R ω) (L ω) r 0}) (fun z hz => ?_) (hψ'.1 _ hy₀m)
    hψ'.2.2.2.2.2.1 (fun s hs hsq => capTrace_ne_zero_of_noReturn hcfg hψ h1 hnr hs
      (lt_of_le_of_lt (by rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal hsq) hq)) hu
    (h ▸ hland)
  · have hmem : (c ω).2.1 w ∈ cfPocket (R ω) (L ω) r := by rw [← hdom]; exact hc.inv_mem_dom hw
    rw [← heq hmem]
    exact hc.2.2 w hw
  · have hz' := hcur.inv_mem_dom hz
    rw [← SetLike.mem_coe, hd] at hz'
    exact ⟨subset_closure hz'.1, fun h => hx₀ (mem_singleton_iff.1 h ▸ hz'.1)⟩

/-- **`R7SeedLand` from the counterflow's no-return** (bounded change pocket): if almost surely on the test the
counterflow does not return to its start at positive times, the seed-interval landings hold at every capacity. -/
theorem r7SeedLand_of_noReturn {nL nR : ℕ} {P : Measure Ω} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {q : ℝ≥0}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) (hxL : ∀ ω, xL ω 0 = 0)
    (hxR : ∀ ω, xR ω 0 = 0) (hnr : ∀ᵐ ω ∂P, ω ∈ A → ∀ t : ℝ, 0 < t → η ω t ≠ 0) :
    R7SeedLand P A R L r η ψ xL xR c q := by
  filter_upwards [hnr] with ω hω hA hlive
  exact seedLand_of_noReturn_sample (W := fun ω (s : ℝ) => W' s.toNNReal ω) hA (hcfg ω hA) (hψ ω hA) (hc ω hA)
    (hdom ω hA) (heq ω hA) (hxL ω) (hxR ω) hlive (hω hA)

end Bounded

/-! ### Change pocket opening at the flow seed -/

section SeedOpen

open LocalSets PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt PocketCoupling PocketStopSide PhaseSel
  PocketWordAssembly PocketSeedOpen PocketCoord PocketJordan R5Phase R5Same R5Ref Sec6 PocketStopWallsFin
  PocketStopMarked R5Lift

/-- **The corner is in `ℍ` or is `0`** (pocket opening at the flow seed). -/
theorem cfArcRInf_zero_mem_H_or_eq_zero {R L : ℝ≥0 → ℂ} {r : ℝ≥0} (h : IsChangeConfigInc R L r)
    (h0 : rightLo R L r = 0) : cfArcRInf R L r 0 ∈ H ∨ cfArcRInf R L r 0 = 0 := by
  have e : cfArcRInf R L r 0 = cfPt (WangWu.toDisc (Lemma71I.realPath R) (rightHi R L r)) := by
    simp [cfArcRInf]
  obtain ⟨-, hv, huv, -⟩ := h.changeCorner_props
  have hαR := h.isDiscCrosscut_right
  rw [e]
  rcases hv.2.lt_or_eq with h1 | h1
  · exact Or.inl (cfPt_mem_H (hαR.mem_disc _ ⟨h0 ▸ huv, h1⟩))
  · rw [h1, hαR.one]
    exact Or.inr cfPt_one

variable {Ω : Type*} [MeasurableSpace Ω] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}
  {A : Set Ω}

omit [MeasurableSpace Ω] in
/-- **The relative capacity trace does not return to the corner** (pocket opening at the flow seed). -/
theorem capTrace_ne_zero_of_noReturnInf {W : Ω → ℝ → ℝ} {ω : Ω}
    (hcfg : IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω)) (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hy₀ : cfArcRInf (R ω) (L ω) r 0 = 0) (hnr : ∀ t : ℝ, 0 < t → η ω t ≠ 0) {s : ℝ} (hs : 0 < s)
    (hsl : ENNReal.ofReal s < capLife (travAllInf R L r η ψ ω)) :
    capTrace (travAllInf R L r η ψ ω) s.toNNReal ≠ 0 := by
  obtain ⟨hP, hψ'⟩ := pocket_of_cfgInf hcfg hψ
  have hAC := hcfg.attach
  have hγ : IsDrivenCurve (travAllInf R L r η ψ ω) := (hcfg.isDrivenCurve hψ).1
  have hspec : 0 ≤ capInv (travAllInf R L r η ψ ω) s ∧
      capClock (travAllInf R L r η ψ ω) (capInv (travAllInf R L r η ψ ω) s) = s := hγ.capInv_spec hs.le hsl
  set u := capInv (travAllInf R L r η ψ ω) s with hudef
  have hc0 : capClock (travAllInf R L r η ψ ω) 0 = 0 := hγ.capClock_zero
  have hupos : 0 < u := by
    refine lt_of_le_of_ne hspec.1 fun h => ?_
    have h2 := hspec.2
    rw [← h, hc0] at h2
    linarith
  set L₀ := clockEnd (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) with hL₀
  have hL : 0 < L₀ := hP.clockEnd_pos hAC
  set v := clockOf L₀ u with hvdef
  have hv : v ∈ Ico 0 L₀ := clockOf_mem_Ico hL hspec.1
  have hvpos : 0 < v := by
    simp only [hvdef, clockOf]
    have : 0 < u / (1 + u) := by positivity
    positivity
  have hm := hP.erasedPath_mem hv
  have hpk := hcfg.conf.isCfPocketInf hcfg.seed
  have hy₀m : cfArcRInf (R ω) (L ω) r 0 ∈ closure (cfPocket (R ω) (L ω) r) := by
    refine frontier_subset_closure ?_
    rw [hpk.frontier_eq]
    exact Or.inl ⟨0, Set.mem_Ici.2 le_rfl, rfl⟩
  intro h0
  have hval : capTrace (travAllInf R L r η ψ ω) s.toNNReal = ψ ω (erasedPathInf (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) v) := by
    simp only [capTrace, Real.coe_toNNReal _ hs.le]
    rfl
  rw [hval] at h0
  have heqp := hψ'.2.1 hm hy₀m (h0.trans hψ'.2.2.2.2.2.1.symm)
  have hf := hP.fibre_mem hv
  have hcf := hP.clock_fibre hv
  have hτ := hP.nonneg
  have hfpos : 0 < pocketFibreInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) v := by
    rcases (hτ.trans hf).lt_or_eq with h | h
    · exact h
    · exfalso
      have hfτ := le_antisymm (h ▸ hτ) hf
      rw [hfτ, IsReversePocketInf.clock_τ] at hcf
      linarith
  exact hnr _ hfpos (heqp.trans hy₀)

omit [MeasurableSpace Ω] in
/-- **The seed-interval landings at one sample from the counterflow's no-return** (pocket opening at the flow seed). -/
theorem seedLandInf_of_noReturn_sample {W : Ω → ℝ → ℝ} {c : Ω → Chart} {ω : Ω} (hω : ω ∈ A)
    (hcfg : IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω)) (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hc : (c ω).IsConformal) (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) {nL nR : ℕ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} (hxL : xL ω 0 = 0) (hxR : xR ω 0 = 0) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)) (hnr : ∀ t : ℝ, 0 < t → η ω t ≠ 0) :
    ∀ u ∈ Ioo (geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL 0 q ω -
          segDriver (travAllInf R L r η ψ ω) q)
        (geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR 0 q ω - segDriver (travAllInf R L r η ψ ω) q),
      extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 u ∈ H := by
  intro u hu
  have hγ := (hcfg.isDrivenCurve hψ).1
  have hq0 : 0 < q := by
    rcases (show (0 : ℝ≥0) ≤ q from zero_le).eq_or_lt with h0q | h0q
    · exfalso
      subst h0q
      rw [seed_interval_eq_empty_zero (c := c) hxL hxR hγ hq] at hu
      exact hu
    · exact h0q
  obtain ⟨hland, hcl, -⟩ := current_landingInf hω hcfg hψ hc hdom heq hq u
  obtain ⟨hP, hψ'⟩ := pocket_of_cfgInf hcfg hψ
  have hpk := hcfg.conf.isCfPocketInf hcfg.seed
  rcases closure_cfPocketInf_subset_H_union_seed hpk hcl with h | h
  · exact h
  rw [mem_singleton_iff] at h
  rcases cfArcRInf_zero_mem_H_or_eq_zero hcfg.conf hcfg.seed with h1 | h1
  · rw [h]
    exact h1
  exfalso
  have hy₀m : cfArcRInf (R ω) (L ω) r 0 ∈ closure (cfPocket (R ω) (L ω) r) := by
    refine frontier_subset_closure ?_
    rw [hpk.frontier_eq]
    exact Or.inl ⟨0, Set.mem_Ici.2 le_rfl, rfl⟩
  have hcur := isConformal_relChart_of_driven (c := c) hγ hq hc
  have hd := current_dom_eqInf hω hcfg hψ hc hdom heq hq
  refine not_tendsto_corner (c := c) hxL hxR hγ hq hq0 (ψ := ψ ω) (fun w hw => ?_)
    (S := closure (cfPocket (R ω) (L ω) r)) (fun z hz => ?_) (hψ'.1 _ hy₀m) hψ'.2.2.2.2.2.1
    (fun s hs hsq => capTrace_ne_zero_of_noReturnInf hcfg hψ h1 hnr hs
      (lt_of_le_of_lt (by rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal hsq) hq)) hu
    (h ▸ hland)
  · have hmem : (c ω).2.1 w ∈ cfPocket (R ω) (L ω) r := by rw [← hdom]; exact hc.inv_mem_dom hw
    rw [← heq hmem]
    exact hc.2.2 w hw
  · have hz' := hcur.inv_mem_dom hz
    rw [← SetLike.mem_coe, hd] at hz'
    exact subset_closure hz'.1

/-- **`R7SeedLandInf` from the counterflow's no-return** (pocket opening at the flow seed). -/
theorem r7SeedLandInf_of_noReturn {nL nR : ℕ} {P : Measure Ω} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {q : ℝ≥0}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) (hxL : ∀ ω, xL ω 0 = 0)
    (hxR : ∀ ω, xR ω 0 = 0) (hnr : ∀ᵐ ω ∂P, ω ∈ A → ∀ t : ℝ, 0 < t → η ω t ≠ 0) :
    R7SeedLandInf P A R L r η ψ xL xR c q := by
  filter_upwards [hnr] with ω hω hA hlive
  exact seedLandInf_of_noReturn_sample (W := fun ω (s : ℝ) => W' s.toNNReal ω) hA (hcfg ω hA) (hψ ω hA) (hc ω hA)
    (hdom ω hA) (heq ω hA) (hxL ω) (hxR ω) hlive (hω hA)

end SeedOpen

end InteractingSLE.Sec7.R5Fresh
