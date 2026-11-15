/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Prop418Side
import InteractingSLE.WangWu.SideValues
import InteractingSLE.Foundations.Loewner.FiniteEndpoint
import InteractingSLE.Foundations.SLE.SpaceFilling.SwallowReal
import InteractingSLE.Spec.Supplement.LPProbReflect
import InteractingSLE.Foundations.Loewner.YuanCorollary13
import InteractingSLE.Foundations.Loewner.YuanCorollary13Finite
import InteractingSLE.Spec.Sec6.DrivingUnconditional

/-!
# The tip and the base of a simple Loewner trace under the boundary extension

Packet PROVE-WW-B14 (the deterministic half of the contact step's N3, PROVE-WW-B13). Wang–Wu
(`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), proof of Proposition 4.18 (text dump
L1611–1615: "The only exceptions are the finitely many slit tips, starting prime ends, and original boundary jumps").
The boundary correspondence of the two-slit chart needs to know which real points the boundary extension
`F̄_t = extendFrom ℍ (fwdMapInv W t)` of the inverse Loewner map sends to the tip `η(t)` and to the starting point `0`
of a simple trace `η`.

Setting: `W` a continuous driver with `W 0 = 0`, `η` a continuous Loewner trace of `W` (`IsLoewnerTrace`) which is a
simple proper arc of `ℍ` (`IsProperArc`).

* `fwdMap_eq_futureArc`: `f_s(η(t)) = γ_s(t − s)` for `s < t` (the mapped future of PROVE-WW-B6).
* **`eq_zero_of_extendFrom_eq_tip`** (the tip is a single prime end): if `F̄_t(x) = η(t)` for a real `x`, then
  `x = 0`. Proof: for `s < t`, `F_t = F_s ∘ F^{(s)}_{t−s}` moves points by at most `24 M + 8 √(t − s)`
  (`M` the oscillation of `W` on `[s, t]`), and `f_s(η(t)) = γ_s(t − s)` is at most as large; let `s ↑ t`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE.WangWu

/-! ### The tip -/

section Tip

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- **The centred image of a later trace point is the mapped future**: `f_s(η(t)) = γ_s(t − s)` for `s < t`. -/
theorem fwdMap_eq_futureArc (hη : IsLoewnerTrace W η) (hγ : IsProperArc η) (hW : Continuous W)
    (hW0 : W 0 = 0) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) : fwdMap W s (η t) = futureArc W s (t - s) := by
  have hu : 0 < t - s := sub_pos.2 hst
  obtain ⟨-, h2⟩ := extendFrom_futureArc hη hW hW0 hs hu.le
  have hH := futureArc_mem_H hη hγ hW hW0 hs hu
  rw [extendFrom_fwdMapInv_eq hW hW0 hs hH, add_sub_cancel] at h2
  rw [← h2, QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 hs hH]

/-- The estimate behind the tip lemma: if `F̄_t(x) = η(t)` and `|W(s + ·) − W(s)| ≤ M` on `[0, t − s]`, then
`|x| ≤ 2 (24 M + 8 √(t − s))`. -/
theorem norm_le_of_extendFrom_eq_tip (hη : IsLoewnerTrace W η) (hγ : IsProperArc η) (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 < t) {x : ℝ} (hx : extendFrom H (fwdMapInv W t) x = η t) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) t) {M : ℝ} (hM : ∀ r ∈ Icc (0 : ℝ) (t - s), |shiftDrive W s r| ≤ M) :
    ‖(x : ℂ)‖ ≤ 2 * (24 * M + 8 * Real.sqrt (t - s)) := by
  have hWs := QuantumZipper.RS.continuous_shiftDrive hW s
  have hWs0 := QuantumZipper.RS.shiftDrive_zero W s
  have hts : 0 ≤ t - s := sub_nonneg.2 hs.2.le
  have hxH : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
  have hNe : (𝓝[H] (x : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (closure_H ▸ hxH)
  have hlimF : Tendsto (fwdMapInv W t) (𝓝[H] (x : ℂ)) (𝓝 (η t)) := by
    have h := (hη.hasBdryLimits hW hW0 ht.le).tendsto hxH
    rwa [hx] at h
  -- `ζ = F^{(s)}_{t−s}(w)`, with `F_s(ζ) = F_t(w)`
  set ζ : ℂ → ℂ := fun w => fwdMapInv (shiftDrive W s) (t - s) w with hζdef
  have hηt : η t ∈ H \ fwdHull W s := mem_H_diff_fwdHull hη hγ hs.1 hs.2
  have hcont : ContinuousAt (fwdMap W s) (η t) :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW hs.1).continuousOn.continuousAt
      ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW hs.1).mem_nhds hηt)
  have hlimζ : Tendsto ζ (𝓝[H] (x : ℂ)) (𝓝 (fwdMap W s (η t))) := by
    refine (hcont.tendsto.comp hlimF).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hζH : ζ w ∈ H := QuantumZipper.RS.fwdMapInv_mem_H hWs hWs0 hts hw
    have hF : fwdMapInv W s (ζ w) = fwdMapInv W t w := by
      have := QuantumZipper.RS.fwdMapInv_add_shift hW hW0 hs.1 hts hw
      rw [show s + (t - s) = t by ring] at this
      exact this.symm
    simp only [Function.comp_apply, ← hF]
    exact QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 hs.1 hζH
  have hlimw : Tendsto (fun w : ℂ => w) (𝓝[H] (x : ℂ)) (𝓝 (x : ℂ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have h1 : ‖fwdMap W s (η t) - x‖ ≤ 24 * M + 8 * Real.sqrt (t - s) := by
    refine le_of_tendsto ((hlimζ.sub hlimw).norm) ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact norm_fwdMapInv_sub_le hWs hWs0 hts hM hw
  have h2 : ‖fwdMap W s (η t)‖ ≤ 24 * M + 8 * Real.sqrt (t - s) := by
    rw [fwdMap_eq_futureArc hη hγ hW hW0 hs.1 hs.2]
    exact hη.norm_shift_tip_le hW hW0 hs.1 hts hM
  calc ‖(x : ℂ)‖ = ‖fwdMap W s (η t) - (fwdMap W s (η t) - x)‖ := by rw [sub_sub_cancel]
    _ ≤ ‖fwdMap W s (η t)‖ + ‖fwdMap W s (η t) - x‖ := norm_sub_le _ _
    _ ≤ 2 * (24 * M + 8 * Real.sqrt (t - s)) := by linarith

/-- **The tip is a single prime end.** For a simple proper Loewner trace `η` of `W` and `t > 0`, the only real point
sent to the tip `η(t)` by the boundary extension `F̄_t` of the inverse Loewner map is `0`. -/
theorem eq_zero_of_extendFrom_eq_tip (hη : IsLoewnerTrace W η) (hγ : IsProperArc η) (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 < t) {x : ℝ} (hx : extendFrom H (fwdMapInv W t) x = η t) : x = 0 := by
  by_contra hne
  set a : ℝ := ‖(x : ℂ)‖ with ha
  have hapos : 0 < a := by rw [ha, Complex.norm_real, Real.norm_eq_abs]; exact abs_pos.2 hne
  set e : ℝ := a / 200 with he
  have hepos : 0 < e := by positivity
  obtain ⟨δ, hδ, hWδ⟩ := Metric.continuousAt_iff.1 hW.continuousAt e hepos
  set m : ℝ := min (min (δ / 2) (t / 2)) ((a / 64) ^ 2) with hm
  have hmpos : 0 < m := lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  have hmδ : m ≤ δ / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hmt : m ≤ t / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hma : m ≤ (a / 64) ^ 2 := min_le_right _ _
  set s : ℝ := t - m with hsdef
  have hs : s ∈ Ico (0 : ℝ) t := ⟨by linarith, by linarith⟩
  have hM : ∀ r ∈ Icc (0 : ℝ) (t - s), |shiftDrive W s r| ≤ 2 * e := by
    intro r hr
    have hr' : r ≤ m := by linarith [hr.2]
    have h1 := hWδ (show dist (s + r) t < δ by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hr.1])
    have h2 := hWδ (show dist s t < δ by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    rw [Real.dist_eq] at h1 h2
    simp only [shiftDrive]
    rw [abs_le]
    constructor <;> linarith [abs_lt.1 h1, abs_lt.1 h2]
  have hk := norm_le_of_extendFrom_eq_tip hη hγ hW hW0 ht hx hs hM
  have hsq : Real.sqrt (t - s) ≤ a / 64 := by
    have : t - s = m := by rw [hsdef]; ring
    rw [this]
    calc Real.sqrt m ≤ Real.sqrt ((a / 64) ^ 2) := Real.sqrt_le_sqrt hma
      _ = a / 64 := Real.sqrt_sq (by positivity)
  rw [← ha] at hk
  have : a ≤ 2 * (24 * (2 * e) + 8 * (a / 64)) := by nlinarith
  rw [he] at this
  linarith

end Tip

/-! ### Real points stay alive; the composition rule at the boundary -/

section Alive

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- **Real points other than `0` are never swallowed by a simple proper trace**: the forward flow from a real
`x ≠ 0` exists on every `[0, T]`. (A real point swallowed at `σ > 0` would force `η(σ) ∉ ℍ`,
`FiniteEndpoint.notMem_H_of_tendsto_fwdMap`; the left side by the reflection `W ↦ −W`.) -/
theorem exists_isForwardSol_of_isProperArc (hη : IsLoewnerTrace W η) (hγ : IsProperArc η) (hW : Continuous W)
    (hW0 : W 0 = 0) {x : ℝ} (hx : x ≠ 0) {T : ℝ} (hT : 0 ≤ T) :
    ∃ v, QuantumZipper.IsForwardSol W (x : ℂ) T v := by
  have hfill : ∀ t ∈ Ico (0 : ℝ) T, IsFilling (fwdHull W t) (η '' Icc 0 t) := fun t ht => by
    rw [hη.2.2 t ht.1]
    exact isFilling_fillH (isCompact_Icc.image_of_continuousOn (hγ.cont.mono Icc_subset_Ici_self))
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · -- the left side, through `W ↦ −W`
    rw [← exists_isForwardSol_neg_iff]
    by_contra hdead
    have hW' : Continuous (fun s => -W s) := hW.neg
    have hW0' : (fun s => -W s) 0 = 0 := by simp [hW0]
    obtain ⟨σ, hσ, hsw⟩ := exists_realSwallowAt hW' hW0' (neg_pos.2 hneg) hT hdead
    have hlim := tendsto_fwdMap_of_realSwallowAt hW' hW0' (neg_pos.2 hneg) hsw
    have hfill' : ∀ t ∈ Ico (0 : ℝ) σ,
        IsFilling (fwdHull (fun s => -W s) t) ((fun s => LP.reflectC (η s)) '' Icc 0 t) := by
      intro t ht
      have h1 := LP.isFilling_reflectC (hfill t ⟨ht.1, ht.2.trans_le hσ.2⟩)
      rw [image_image] at h1
      have h2 : fwdHull (fun s => -W s) t = LP.reflectC '' fwdHull W t := LP.fwdHull_neg W t
      rw [h2]
      exact h1
    have hmain := FiniteEndpoint.notMem_H_of_tendsto_fwdMap hW' hW0' hσ.1 (neg_pos.2 hneg)
      (γ := fun s => LP.reflectC (η s)) (by simp [hγ.zero, LP.reflectC])
      (LP.continuous_reflectC.comp_continuousOn (hγ.cont.mono Icc_subset_Ici_self)) hfill' hsw.2.1 hlim
    exact hmain (LP.reflectC_mem_H_iff.2 (hγ.mem_H σ hσ.1))
  · by_contra hdead
    obtain ⟨σ, hσ, hsw⟩ := exists_realSwallowAt hW hW0 hpos hT hdead
    have hlim := tendsto_fwdMap_of_realSwallowAt hW hW0 hpos hsw
    have hmain := FiniteEndpoint.notMem_H_of_tendsto_fwdMap hW hW0 hσ.1 hpos (γ := η) hγ.zero
      (hγ.cont.mono Icc_subset_Ici_self) (fun t ht => hfill t ⟨ht.1, ht.2.trans_le hσ.2⟩) hsw.2.1 hlim
    exact hmain (hγ.mem_H σ hσ.1)

/-- `F̄_t` takes values in `ℍ̄`. -/
theorem extendFrom_mem_Hbar (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) {x : ℂ} (hx : x ∈ Hbar) : extendFrom H (fwdMapInv W t) x ∈ Hbar := by
  have hNe : (𝓝[H] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (closure_H ▸ hx)
  rw [← closure_H]
  exact mem_closure_of_tendsto ((hη.hasBdryLimits hW hW0 ht).tendsto hx)
    (eventually_nhdsWithin_of_forall fun w hw => QuantumZipper.RS.fwdMapInv_mem_H hW hW0 ht hw)

/-- **The composition rule at the boundary**: `F̄_{u+r} = F̄_u ∘ F̄^{(u)}_r` on `ℍ̄`, where `F^{(u)}` is the inverse
map of the shifted driver `W(u + ·) − W(u)`. -/
theorem extendFrom_fwdMapInv_add_shift (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {u r : ℝ}
    (hu : 0 ≤ u) (hr : 0 ≤ r) {x : ℂ} (hx : x ∈ Hbar) :
    extendFrom H (fwdMapInv W (u + r)) x =
      extendFrom H (fwdMapInv W u) (extendFrom H (fwdMapInv (shiftDrive W u) r) x) := by
  have hWs := QuantumZipper.RS.continuous_shiftDrive hW u
  have hWs0 := QuantumZipper.RS.shiftDrive_zero W u
  have hηs := hη.isLoewnerTrace_shift hW hW0 hu
  set y := extendFrom H (fwdMapInv (shiftDrive W u) r) x with hy
  have hyH : y ∈ Hbar := extendFrom_mem_Hbar hηs hWs hWs0 hr hx
  have h1 : Tendsto (fwdMapInv (shiftDrive W u) r) (𝓝[H] x) (𝓝[H] y) :=
    tendsto_nhdsWithin_iff.2 ⟨(hηs.hasBdryLimits hWs hWs0 hr).tendsto hx,
      eventually_nhdsWithin_of_forall fun w hw => QuantumZipper.RS.fwdMapInv_mem_H hWs hWs0 hr hw⟩
  have h2 := ((hη.hasBdryLimits hW hW0 hu).tendsto hyH).comp h1
  have h3 : Tendsto (fwdMapInv W (u + r)) (𝓝[H] x) (𝓝 (extendFrom H (fwdMapInv W u) y)) := by
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact (QuantumZipper.RS.fwdMapInv_add_shift hW hW0 hu hr hw).symm
  exact extendFrom_eq (by rw [closure_H]; exact hx) h3

/-- **A real point sent to a real alive point is its forward image**: if the flow `v` from a real `r` exists on
`[0, s]` and `F̄_s(r') = r` for some `r' ∈ ℍ̄`, then `r' = v(s)`. -/
theorem eq_of_extendFrom_eq_of_isForwardSol (hW : Continuous W) (hW0 : W 0 = 0) {s : ℝ} (hs : 0 ≤ s)
    {r : ℝ} {v : ℝ → ℂ} (hv : QuantumZipper.IsForwardSol W (r : ℂ) s v)
    (hη : IsLoewnerTrace W η) {r' : ℂ} (hr' : r' ∈ Hbar) (hF : extendFrom H (fwdMapInv W s) r' = r) :
    r' = v s := by
  have hNe : (𝓝[H] r').NeBot := mem_closure_iff_nhdsWithin_neBot.1 (closure_H ▸ hr')
  have h1 : Tendsto (fwdMapInv W s) (𝓝[H] r') (𝓝[H] (r : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun w hw =>
      QuantumZipper.RS.fwdMapInv_mem_H hW hW0 hs hw⟩
    have := (hη.hasBdryLimits hW hW0 hs).tendsto hr'
    rwa [hF] at this
  have h2 := (tendsto_fwdMap_of_isForwardSol hW hs hv).comp h1
  have h3 : Tendsto (fun w => fwdMap W s (fwdMapInv W s w)) (𝓝[H] r') (𝓝 r') := by
    refine (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact (QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 hs hw).symm
  exact tendsto_nhds_unique h3 h2

end Alive

/-! ### A positive real solution started at the driver is the right force image -/

section Ode

open MeasureTheory MartChar.RealFlow

variable {W : ℝ → ℝ}

/-- **A positive solution started at the driver is the right image of `0⁺`.** Let `Y` be continuous on `[0, t]`,
`Y(0) = 0`, `Y > 0` on `(0, t]`, solving the centred real Loewner equation `Y(s) = Y(u) − (W(s) − W(u)) +
∫_u^s 2/Y` for `0 < u ≤ s ≤ t`. Then `Y(t) + W(t) = rightImg W 0 t` (`eq_rightImg_of_forceEq`, after passing to
the limit `u ↓ 0`; the reciprocal gap is integrable at `0` because its integrals over `[u, t]` stay bounded). -/
theorem add_eq_rightImg_of_pos (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 < t) {Y : ℝ → ℝ}
    (hY0 : Y 0 = 0) (hYc : ContinuousOn Y (Icc 0 t)) (hYpos : ∀ u ∈ Ioc 0 t, 0 < Y u)
    (hYeq : ∀ u s, 0 < u → u ≤ s → s ≤ t → Y s = Y u - (W s - W u) + ∫ r in u..s, 2 / Y r) :
    Y t + W t = rightImg W 0 t := by
  set f : ℝ → ℝ := fun r => 2 / Y r with hf
  have hfc : ∀ u, 0 < u → ContinuousOn f (Icc u t) := fun u hu =>
    continuousOn_const.div (hYc.mono (Icc_subset_Icc_left hu.le)) fun r hr =>
      (hYpos r ⟨hu.trans_le hr.1, hr.2⟩).ne'
  have hfnn : ∀ r ∈ Ioc 0 t, 0 ≤ f r := fun r hr => div_nonneg zero_le_two (hYpos r hr).le
  -- a bound for `|W|` on `[0, t]`
  obtain ⟨MW, hMW⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn hW.continuousOn
  -- integrability of `f` on `(0, t]`
  set a : ℕ → ℝ := fun n => t / ((n : ℝ) + 2) with ha
  have ha0 : ∀ n, 0 < a n := fun n => by positivity
  have hat : ∀ n, a n ≤ t := fun n => by
    rw [ha]; exact div_le_self ht.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hatend : Tendsto a atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    have h2 := h.inv_tendsto_atTop.const_mul t
    rw [mul_zero] at h2
    refine h2.congr fun n => ?_
    simp only [ha, Pi.inv_apply, div_eq_mul_inv]
  have hint : IntegrableOn f (Ioc 0 t) := by
    refine integrableOn_Ioc_of_intervalIntegral_norm_bounded_left (a := a) (l := atTop)
      (I := Y t + MW + MW) (fun n => ?_) hatend (Eventually.of_forall fun n => ?_)
    · exact ((hfc _ (ha0 n)).integrableOn_Icc).mono_set Ioc_subset_Icc_self
    · have hI : IntegrableOn f (Ioc (a n) t) :=
        ((hfc _ (ha0 n)).integrableOn_Icc).mono_set Ioc_subset_Icc_self
      have e1 : (∫ x in Ioc (a n) t, ‖f x‖) = ∫ x in Ioc (a n) t, f x := by
        refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
        exact Real.norm_of_nonneg (hfnn r ⟨(ha0 n).trans hr.1, hr.2⟩)
      rw [e1, ← intervalIntegral.integral_of_le (hat n)]
      have h := hYeq (a n) t (ha0 n) (hat n) le_rfl
      have hYa : 0 < Y (a n) := hYpos _ ⟨ha0 n, hat n⟩
      have h1 := hMW t ⟨ht.le, le_rfl⟩
      have h2 := hMW (a n) ⟨(ha0 n).le, hat n⟩
      rw [Real.norm_eq_abs] at h1 h2
      linarith [abs_le.1 h1, abs_le.1 h2]
  have hii : ∀ s ∈ Icc (0 : ℝ) t, IntervalIntegrable f volume 0 s := fun s hs =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hs.1).2 (hint.mono_set (Ioc_subset_Ioc_right hs.2))
  -- the integral equation from `0`
  have heq : ∀ s ∈ Icc (0 : ℝ) t, Y s + W s = ∫ r in (0 : ℝ)..s, f r := by
    intro s hs
    rcases hs.1.eq_or_lt with h0 | hspos
    · rw [← h0, hY0, hW0, intervalIntegral.integral_same, add_zero]
    have hprim : ContinuousOn (fun u => ∫ r in u..s, f r) (uIcc 0 s) := by
      refine intervalIntegral.continuousOn_primitive_interval_left ?_
      rw [uIcc_of_le hs.1]
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le hs.1).1 (hii s hs)
    have hl : Tendsto (fun u => Y u - (W s - W u) + ∫ r in u..s, f r) (𝓝[>] 0)
        (𝓝 (Y 0 - (W s - W 0) + ∫ r in (0 : ℝ)..s, f r)) := by
      have hIoc : 𝓝[>] (0 : ℝ) ≤ 𝓝[Icc 0 s] 0 :=
        nhdsWithin_le_of_mem (mem_nhdsWithin.2 ⟨Iio s, isOpen_Iio, hspos, fun u hu =>
          ⟨le_of_lt hu.2, le_of_lt hu.1⟩⟩)
      have hY : Tendsto Y (𝓝[>] 0) (𝓝 (Y 0)) :=
        ((hYc 0 ⟨le_rfl, ht.le⟩).mono (Icc_subset_Icc_right hs.2)).tendsto.mono_left hIoc
      have hWt : Tendsto W (𝓝[>] 0) (𝓝 (W 0)) := hW.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have hP : Tendsto (fun u => ∫ r in u..s, f r) (𝓝[>] 0) (𝓝 (∫ r in (0 : ℝ)..s, f r)) := by
        have := hprim 0 (by rw [uIcc_of_le hs.1]; exact ⟨le_rfl, hs.1⟩)
        rw [uIcc_of_le hs.1] at this
        exact this.tendsto.mono_left hIoc
      exact (hY.sub (tendsto_const_nhds.sub hWt)).add hP
    have hr : Tendsto (fun u => Y u - (W s - W u) + ∫ r in u..s, f r) (𝓝[>] 0) (𝓝 (Y s)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hspos] with u hu
      exact hYeq u s hu.1 hu.2.le hs.2
    have := tendsto_nhds_unique hr hl
    rw [hY0, hW0] at this
    linarith
  -- apply the uniqueness of the force coordinate
  have hv : ∀ s, (Y s + W s) - W s = Y s := fun s => by ring
  refine eq_rightImg_of_forceEq (w := W) (v := fun s => Y s + W s) (x := 0) (T := t) hW hW0 le_rfl
    (hYc.add hW.continuousOn) (fun s hs => ?_) ?_ (fun s hs => ?_) ?_ ⟨ht.le, le_rfl⟩
  · rcases hs.1.eq_or_lt with h0 | hpos
    · rw [← h0, hY0, zero_add]
    · linarith [hYpos s ⟨hpos, hs.2⟩]
  · simp only [hv]
    exact hii t ⟨ht.le, le_rfl⟩
  · simp only [hv, zero_add]
    exact heq s hs
  · refine measure_mono_null (fun s hs => ?_) (measure_singleton (0 : ℝ))
    rcases hs.1.1.eq_or_lt with h0 | hpos
    · exact h0.symm
    · have := hYpos s ⟨hpos, hs.1.2⟩
      have h2 : W s = Y s + W s := hs.2
      linarith

end Ode

/-! ### The base -/

section Base

open MeasureTheory MartChar.RealFlow

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- `F̄_u` moves points of `ℍ̄` by at most `24 M + 8 √u` if `|W| ≤ M` on `[0, u]`. -/
theorem norm_extendFrom_sub_le (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {u M : ℝ}
    (hu : 0 ≤ u) (hM : ∀ r ∈ Icc (0 : ℝ) u, |W r| ≤ M) {ξ : ℂ} (hξ : ξ ∈ Hbar) :
    ‖extendFrom H (fwdMapInv W u) ξ - ξ‖ ≤ 24 * M + 8 * Real.sqrt u := by
  have hNe : (𝓝[H] ξ).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (closure_H ▸ hξ)
  have hlim := (hη.hasBdryLimits hW hW0 hu).tendsto hξ
  exact le_of_tendsto ((hlim.sub (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)).norm)
    (eventually_nhdsWithin_of_forall fun w hw => norm_fwdMapInv_sub_le hW hW0 hu hM hw)

/-- `F̄_0 = id` on `ℍ̄`. -/
theorem extendFrom_fwdMapInv_zero (hW : Continuous W) (hW0 : W 0 = 0) {ξ : ℂ} (hξ : ξ ∈ Hbar) :
    extendFrom H (fwdMapInv W 0) ξ = ξ := by
  refine extendFrom_eq (by rw [closure_H]; exact hξ) ?_
  refine (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  exact (fwdMapInv_zero_time hW hW0 hw).symm

/-- **The base has exactly the two force prime ends.** For a simple proper Loewner trace `η` of `W` and `t > 0`, a
real point `x` sent to the starting point `0` by `F̄_t` is one of the two images of `0∓`: `x + W_t` is the right image
`rightImg W 0 t` of `0⁺` or the left image `−rightImg (−W) 0 t` of `0⁻`.

Proof: the backward points `y(u) = F̄^{(u)}_{t−u}(x)` (`F^{(u)}` the inverse map of `W(u + ·) − W(u)`) satisfy
`F̄_u(y(u)) = 0` (composition rule), so they are real and nonzero for `u ∈ (0, t]` (`F̄_u(0) = η(u) ∈ ℍ`); real points
are never swallowed, so `u ↦ y(u)` solves the centred real Loewner equation, and `|y(u)| ≤ 24 osc + 8 √u → 0`. Hence
`y + W` is a force-point solution started at `0⁺` (or `0⁻`), which is the geometric image (`eq_rightImg_of_forceEq`). -/
theorem extendFrom_eq_zero_imp (hη : IsLoewnerTrace W η) (hγ : IsProperArc η) (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 < t) {x : ℝ} (hx : extendFrom H (fwdMapInv W t) x = 0) :
    x + W t = rightImg W 0 t ∨ x + W t = -rightImg (fun s => -W s) 0 t := by
  have hxH : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
  have hWs : ∀ u, Continuous (shiftDrive W u) := fun u => QuantumZipper.RS.continuous_shiftDrive hW u
  have hWs0 : ∀ u, shiftDrive W u 0 = 0 := fun u => QuantumZipper.RS.shiftDrive_zero W u
  have hηs : ∀ u, 0 ≤ u → IsLoewnerTrace (shiftDrive W u) (futureArc W u) := fun u hu =>
    hη.isLoewnerTrace_shift hW hW0 hu
  have hγs : ∀ u, 0 ≤ u → IsProperArc (futureArc W u) := fun u hu => isProperArc_futureArc hη hγ hW hW0 hu
  set y : ℝ → ℂ := fun u => extendFrom H (fwdMapInv (shiftDrive W u) (t - u)) x with hy
  have hyH : ∀ u ∈ Icc (0 : ℝ) t, y u ∈ Hbar := fun u hu =>
    extendFrom_mem_Hbar (hηs u hu.1) (hWs u) (hWs0 u) (sub_nonneg.2 hu.2) hxH
  have hFy : ∀ u ∈ Icc (0 : ℝ) t, extendFrom H (fwdMapInv W u) (y u) = 0 := by
    intro u hu
    have h := extendFrom_fwdMapInv_add_shift hη hW hW0 hu.1 (sub_nonneg.2 hu.2) hxH
    rw [add_sub_cancel, hx] at h
    exact h.symm
  have hyim : ∀ u ∈ Ioc (0 : ℝ) t, (y u).im = 0 := by
    intro u hu
    refine le_antisymm (not_lt.1 fun hpos => ?_) (hyH u ⟨hu.1.le, hu.2⟩)
    have h1 := hFy u ⟨hu.1.le, hu.2⟩
    rw [extendFrom_fwdMapInv_eq hW hW0 hu.1.le hpos] at h1
    have h2 := QuantumZipper.RS.fwdMapInv_mem_H hW hW0 hu.1.le (show y u ∈ H from hpos)
    rw [h1] at h2
    exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from h2)
  set Y : ℝ → ℝ := fun u => (y u).re with hYdef
  have hyY : ∀ u ∈ Ioc (0 : ℝ) t, y u = (Y u : ℂ) := fun u hu =>
    Complex.ext (by simp [hYdef]) (by simp [hyim u hu])
  have hYne : ∀ u ∈ Ioc (0 : ℝ) t, Y u ≠ 0 := by
    intro u hu h0
    have h1 := hFy u ⟨hu.1.le, hu.2⟩
    rw [hyY u hu, h0, Complex.ofReal_zero, extendFrom_zero hη hW hW0 hu.1.le] at h1
    have h2 := hγ.mem_H u hu.1
    rw [h1] at h2
    exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from h2)
  -- the chain rule along the backward points
  have hchain : ∀ u ∈ Ioc (0 : ℝ) t, ∀ ρ ∈ Icc (0 : ℝ) (t - u),
      extendFrom H (fwdMapInv (shiftDrive W u) ρ) (y (u + ρ)) = y u := by
    intro u hu ρ hρ
    have h := extendFrom_fwdMapInv_add_shift (hηs u hu.1.le) (hWs u) (hWs0 u) hρ.1
      (show 0 ≤ t - u - ρ by linarith [hρ.2]) hxH
    rw [YuanCorollary13.shiftDrive_shiftDrive, show ρ + (t - u - ρ) = t - u by ring,
      show t - u - ρ = t - (u + ρ) by ring] at h
    exact h.symm
  -- the flows from the backward points
  have hflow : ∀ u ∈ Ioc (0 : ℝ) t, ∃ v : ℝ → ℂ, QuantumZipper.IsForwardSol (shiftDrive W u) (Y u : ℂ) (t - u) v ∧
      ∀ ρ ∈ Icc (0 : ℝ) (t - u), y (u + ρ) = v ρ := by
    intro u hu
    obtain ⟨v, hv⟩ := exists_isForwardSol_of_isProperArc (hηs u hu.1.le) (hγs u hu.1.le) (hWs u) (hWs0 u)
      (hYne u hu) (sub_nonneg.2 hu.2)
    refine ⟨v, hv, fun ρ hρ => ?_⟩
    have hvρ : QuantumZipper.IsForwardSol (shiftDrive W u) (Y u : ℂ) ρ v :=
      ⟨hv.1.mono (Icc_subset_Icc_right hρ.2), fun r hr => hv.2 r ⟨hr.1, hr.2.trans hρ.2⟩⟩
    refine eq_of_extendFrom_eq_of_isForwardSol (hWs u) (hWs0 u) hρ.1 hvρ (hηs u hu.1.le)
      (hyH (u + ρ) ⟨by linarith [hu.1, hρ.1], by linarith [hρ.2]⟩) ?_
    rw [hchain u hu ρ hρ, hyY u hu]
  -- the real Loewner equation
  have hYeq' : ∀ u ∈ Ioc (0 : ℝ) t, ∀ ρ ∈ Icc (0 : ℝ) (t - u),
      Y (u + ρ) = Y u - shiftDrive W u ρ + ∫ r in (0 : ℝ)..ρ, 2 / Y (u + r) := by
    intro u hu ρ hρ
    obtain ⟨v, hv, hyv⟩ := hflow u hu
    have h := (hv.2 ρ hρ).2
    have hint : (∫ r in (0 : ℝ)..ρ, 2 / v r) = ((∫ r in (0 : ℝ)..ρ, 2 / Y (u + r) : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hρ.1] at hr
      have hr' : u + r ∈ Ioc (0 : ℝ) t := ⟨by linarith [hu.1, hr.1], by linarith [hr.2, hρ.2]⟩
      rw [← hyv r ⟨hr.1, hr.2.trans hρ.2⟩, hyY _ hr', Complex.ofReal_div, Complex.ofReal_ofNat]
    rw [hint, ← hyv ρ hρ] at h
    have h2 := congrArg Complex.re h
    simpa [hYdef] using h2
  -- endpoint values
  have hYt : Y t = x := by
    have : y t = x := by
      simp only [hy, sub_self]
      exact extendFrom_fwdMapInv_zero (hWs t) (hWs0 t) hxH
    simp [hYdef, this]
  have hY0 : Y 0 = 0 := by
    have hs0 : shiftDrive W 0 = W := by funext r; simp [shiftDrive, hW0]
    have : y 0 = 0 := by simp only [hy, hs0, sub_zero]; exact hx
    simp [hYdef, this]
  -- continuity of `Y` on `[0, t]`
  have hYcU : ∀ u ∈ Ioc (0 : ℝ) t, ContinuousOn Y (Icc u t) := by
    intro u hu
    obtain ⟨v, hv, hyv⟩ := hflow u hu
    have hc : ContinuousOn (fun s => (v (s - u)).re) (Icc u t) :=
      Complex.continuous_re.comp_continuousOn (hv.1.comp (continuousOn_id.sub continuousOn_const)
        fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩)
    refine hc.congr fun s hs => ?_
    have := hyv (s - u) ⟨by linarith [hs.1], by linarith [hs.2]⟩
    rw [add_sub_cancel] at this
    simp [hYdef, this]
  have hYc : ContinuousOn Y (Icc 0 t) := by
    intro u hu
    rcases hu.1.eq_or_lt with h0 | hpos
    · rw [← h0]
      rw [Metric.continuousWithinAt_iff]
      intro ε hε
      obtain ⟨δ, hδ, hWδ⟩ := Metric.continuousAt_iff.1 hW.continuousAt (ε / 48) (by positivity)
      refine ⟨min δ ((ε / 16) ^ 2), lt_min hδ (by positivity), fun {v} hv hvd => ?_⟩
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hv.1] at hvd
      rw [Real.dist_eq, hY0, sub_zero]
      rcases hv.1.eq_or_lt with hv0 | hvpos
      · rw [← hv0, hY0, abs_zero]; exact hε
      have hM : ∀ r ∈ Icc (0 : ℝ) v, |W r| ≤ ε / 48 := fun r hr => by
        have := hWδ (show dist r 0 < δ by
          rw [Real.dist_eq, sub_zero, abs_of_nonneg hr.1]; linarith [hr.2, min_le_left δ ((ε / 16) ^ 2)])
        rw [Real.dist_eq, hW0, sub_zero] at this
        exact this.le
      have hb := norm_extendFrom_sub_le hη hW hW0 hvpos.le hM (hyH v ⟨hv.1, hv.2⟩)
      rw [hFy v ⟨hv.1, hv.2⟩, zero_sub, norm_neg, hyY v ⟨hvpos, hv.2⟩, Complex.norm_real,
        Real.norm_eq_abs] at hb
      have hsq : Real.sqrt v < ε / 16 := by
        calc Real.sqrt v < Real.sqrt ((ε / 16) ^ 2) :=
              Real.sqrt_lt_sqrt hv.1 (lt_of_lt_of_le hvd (min_le_right _ _))
          _ = ε / 16 := Real.sqrt_sq (by positivity)
      linarith
    · have h1 := hYcU (u / 2) ⟨by linarith, by linarith [hu.2]⟩ u ⟨by linarith, hu.2⟩
      refine h1.mono_of_mem_nhdsWithin ?_
      refine mem_nhdsWithin.2 ⟨Ioi (u / 2), isOpen_Ioi, by simp; linarith, fun s hs => ?_⟩
      exact ⟨le_of_lt hs.1, hs.2.2⟩
  -- the equation in the form of `add_eq_rightImg_of_pos`
  have hYeq : ∀ u s, 0 < u → u ≤ s → s ≤ t → Y s = Y u - (W s - W u) + ∫ r in u..s, 2 / Y r := by
    intro u s hu hus hst
    have h := hYeq' u ⟨hu, hus.trans hst⟩ (s - u) ⟨by linarith, by linarith⟩
    rw [add_sub_cancel, intervalIntegral.integral_comp_add_left (fun r => 2 / Y r) u, add_zero,
      add_sub_cancel] at h
    simpa only [shiftDrive, add_sub_cancel] using h
  -- the sign of `Y` on `(0, t]` is the sign of `x`
  have hsign : ∀ u ∈ Ioc (0 : ℝ) t, ∀ c : ℝ, c * x > 0 → c * Y u > 0 := by
    intro u hu c hc
    by_contra hle
    push Not at hle
    have hYu : c * Y u < 0 := lt_of_le_of_ne hle fun h => hYne u hu (by
      rcases mul_eq_zero.1 h with h | h
      · rw [h, zero_mul] at hc; exact absurd hc (lt_irrefl _)
      · exact h)
    have hcY : ContinuousOn (fun s => c * Y s) (Icc u t) := continuousOn_const.mul (hYcU u hu)
    have hmem : (0 : ℝ) ∈ Icc (c * Y u) (c * Y t) := ⟨hYu.le, by rw [hYt]; exact hc.le⟩
    obtain ⟨d, hd, hd0⟩ := intermediate_value_Icc hu.2 hcY hmem
    have hdI : d ∈ Ioc (0 : ℝ) t := ⟨hu.1.trans_le hd.1, hd.2⟩
    rcases mul_eq_zero.1 hd0 with h | h
    · rw [h, zero_mul] at hc; exact lt_irrefl _ hc
    · exact hYne d hdI h
  rcases lt_or_gt_of_ne (show x ≠ 0 by
      intro h0
      have := hYne t ⟨ht, le_rfl⟩
      rw [hYt] at this
      exact this h0) with hneg | hpos
  · right
    have hYp : ∀ u ∈ Ioc (0 : ℝ) t, 0 < -Y u := fun u hu => by
      have := hsign u hu (-1) (by linarith); linarith
    have hres := add_eq_rightImg_of_pos (W := fun s => -W s) hW.neg (by simp [hW0]) ht
      (Y := fun s => -Y s) (by simp [hY0]) hYc.neg hYp (fun u s hu hus hst => by
        rw [hYeq u s hu hus hst]
        have : (∫ r in u..s, 2 / -Y r) = -∫ r in u..s, 2 / Y r := by
          rw [← intervalIntegral.integral_neg]
          exact intervalIntegral.integral_congr fun r _ => by simp only [div_neg]
        rw [this]
        ring)
    rw [hYt] at hres
    linarith
  · left
    have hYp : ∀ u ∈ Ioc (0 : ℝ) t, 0 < Y u := fun u hu => by
      have := hsign u hu 1 (by linarith); linarith
    have hres := add_eq_rightImg_of_pos hW hW0 ht hY0 hYc hYp hYeq
    rwa [hYt] at hres

end Base

/-! ### A simple curve on a compact interval is a Loewner trace after capacity parametrization -/

section Simple

variable {γ : ℝ → ℂ} {S : ℝ}

/-- **A simple curve in `ℍ` on `[0, S]` is generated by a continuous driver, and its frozen slit extension is a simple
proper Loewner trace.** Let `γ` be continuous and injective on `[0, S]`, `γ(0) = 0`, `γ((0, S]) ⊆ ℍ`, and `0 < t < S`.
There are a continuous driver `W` with `W(0) = 0` and a strictly increasing continuous capacity clock `σ` on `[0, S]`,
`σ(0) = 0`, with `K_{σ(u)} = γ((0, u])`; and for the driver frozen after `σ(t)` (`extDrive`) there is a simple proper
Loewner trace `η` with `η(σ(u)) = γ(u)` for `u ∈ [0, t]` (the capacity reparametrization of `γ` on `[0, t]`,
continued by the image of the vertical slit, `extTrace`). (Proposition 6.12 through `Sec6`'s driving criteria; the
criteria (a), (b) hold since `fill(γ[0, u]) = γ((0, u])`.) -/
theorem exists_trace_of_simple (hS : 0 < S) (hc : ContinuousOn γ (Icc 0 S)) (hinj : InjOn γ (Icc 0 S))
    (h0 : γ 0 = 0) (hH : ∀ u ∈ Ioc 0 S, γ u ∈ H) {t : ℝ} (ht : t ∈ Ioo 0 S) :
    ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ ∃ σ : ℝ → ℝ, σ 0 = 0 ∧ StrictMonoOn σ (Icc 0 S) ∧
      ContinuousOn σ (Icc 0 S) ∧ (∀ u ∈ Icc 0 S, fwdHull W (σ u) = γ '' Ioc 0 u) ∧
      ∃ η : ℝ → ℂ, IsLoewnerTrace (YuanCorollary13.extDrive W (σ t)) η ∧ IsProperArc η ∧
        (∀ u ∈ Icc 0 t, η (σ u) = γ u) ∧
        fwdHull (YuanCorollary13.extDrive W (σ t)) (σ t) = γ '' Ioc 0 t := by
  have hHbar : MapsTo γ (Icc 0 S) Hbar := fun u hu => by
    rcases hu.1.eq_or_lt with h | h
    · rw [← h, h0]; exact zero_mem_Hbar
    · exact le_of_lt (show (0 : ℝ) < (γ u).im from hH u ⟨h, hu.2⟩)
  have hfill : ∀ u ∈ Icc 0 S, fillH (γ '' Icc 0 u) = γ '' Ioc 0 u := fun u hu =>
    YuanCharacterisation.fillH_image_eq hu.1 (hc.mono (Icc_subset_Icc_right hu.2))
      (hinj.mono (Icc_subset_Icc_right hu.2)) (by rw [h0, zero_im]) fun v hv => hH v ⟨hv.1, hv.2.trans hu.2⟩
  have hnc := Sec6.hasSimpleApproxOn_of_injOn hS hc hinj h0 hHbar
  have ha : Sec6.DrivingCriterionA γ S := by
    intro u hu
    rw [hfill u ⟨hu.1.le, hu.2.le⟩]
    rintro _ ⟨v, hv, rfl⟩
    refine subset_closure ⟨hH v ⟨hu.1.trans hv.1, hv.2⟩, ?_⟩
    rintro ⟨v', hv', e⟩
    have := hinj ⟨hv'.1.le, hv'.2.trans hu.2.le⟩ ⟨(hu.1.trans hv.1).le, hv.2⟩ e
    linarith [hv'.2, hv.1]
  have hb : Sec6.DrivingCriterionB γ S := by
    intro u hu
    suffices hE : {v ∈ Ioo u S | γ v ∈ γ '' Icc 0 u ∨ (γ v).im = 0} = ∅ by rw [hE, interior_empty]
    refine eq_empty_iff_forall_notMem.2 ?_
    rintro v ⟨hv, hv'⟩
    rcases hv' with ⟨v', hv', e⟩ | him
    · have := hinj ⟨hv'.1, hv'.2.trans hu.2.le⟩ ⟨(hu.1.trans hv.1).le, hv.2.le⟩ e
      linarith [hv'.2, hv.1]
    · have h2 : (0 : ℝ) < (γ v).im := hH v ⟨hu.1.trans hv.1, hv.2.le⟩
      rw [him] at h2
      exact lt_irrefl _ h2
  obtain ⟨W, hW, hW0, σ, hσ0, hσm, hσc, hK⟩ :=
    Sec6.exists_driver_of_drivingCriteria_of_yuanDriverInput Sec6.yuanDriverInput hS hc h0 hnc ha hb
  have hσK : ∀ u ∈ Icc 0 S, fwdHull W (σ u) = γ '' Ioc 0 u := fun u hu => by
    rw [(hK u hu).2.1, hfill u hu]
  refine ⟨W, hW, hW0, σ, hσ0, hσm, hσc, hσK, ?_⟩
  -- the capacity clock as an order isomorphism `[0, S] ≃o [0, σ S]`
  have hσS : 0 < σ S := by
    have := hσm ⟨le_rfl, hS.le⟩ ⟨hS.le, le_rfl⟩ hS
    rwa [hσ0] at this
  set f : Icc (0 : ℝ) S → Icc (0 : ℝ) (σ S) := fun u => ⟨σ u, (hK u u.2).1,
    hσm.monotoneOn u.2 ⟨hS.le, le_rfl⟩ u.2.2⟩ with hf
  have hfm : StrictMono f := fun a b hab => hσm a.2 b.2 hab
  have hfs : Function.Surjective f := by
    intro τ
    have hivt := intermediate_value_Icc hS.le hσc
    rw [hσ0] at hivt
    obtain ⟨u, hu, hut⟩ := hivt τ.2
    exact ⟨⟨u, hu⟩, Subtype.ext hut⟩
  set e : Icc (0 : ℝ) S ≃o Icc (0 : ℝ) (σ S) := StrictMono.orderIsoOfSurjective f hfm hfs with he
  have heσ : ∀ u : Icc (0 : ℝ) S, ((e u : Icc (0 : ℝ) (σ S)) : ℝ) = σ u := fun u => rfl
  set c : ℝ → ℝ := fun τ => ((e.symm (projIcc 0 (σ S) hσS.le τ) : Icc (0 : ℝ) S) : ℝ) with hcdef
  have hcc : Continuous c := continuous_subtype_val.comp (e.symm.continuous.comp continuous_projIcc)
  have hcI : ∀ τ, c τ ∈ Icc (0 : ℝ) S := fun τ => (e.symm _).2
  have hσc' : ∀ τ ∈ Icc (0 : ℝ) (σ S), σ (c τ) = τ := fun τ hτ => by
    have h1 := heσ (e.symm (projIcc 0 (σ S) hσS.le τ))
    rw [e.apply_symm_apply, projIcc_of_mem _ hτ] at h1
    show σ ((e.symm (projIcc 0 (σ S) hσS.le τ) : Icc (0 : ℝ) S) : ℝ) = τ
    rw [projIcc_of_mem _ hτ]
    exact h1.symm
  have hcσ : ∀ u ∈ Icc (0 : ℝ) S, c (σ u) = u := fun u hu => by
    have h1 : projIcc 0 (σ S) hσS.le (σ u) = e ⟨u, hu⟩ := by
      rw [projIcc_of_mem _ (f ⟨u, hu⟩).2]; rfl
    simp only [hcdef, h1, e.symm_apply_apply]
  have hcmono : Monotone c := fun a b hab =>
    (e.symm.monotone (monotone_projIcc hσS.le hab) : _)
  set η₀ : ℝ → ℂ := fun τ => γ (c τ) with hη₀
  have hη₀c : Continuous η₀ := hc.comp_continuous hcc hcI
  have hc0 : c 0 = 0 := by simpa [hσ0] using hcσ 0 ⟨le_rfl, hS.le⟩
  have himg : ∀ τ ∈ Icc (0 : ℝ) (σ S), η₀ '' Icc 0 τ = γ '' Icc 0 (c τ) := by
    intro τ hτ
    ext z
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨c r, ⟨(hcI r).1, hcmono hr.2⟩, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      have huS : u ∈ Icc (0 : ℝ) S := ⟨hu.1, hu.2.trans (hcI τ).2⟩
      refine ⟨σ u, ⟨?_, ?_⟩, by simp only [hη₀, hcσ u huS]⟩
      · rw [← hσ0]; exact hσm.monotoneOn ⟨le_rfl, hS.le⟩ huS hu.1
      · rw [← hσc' τ hτ]; exact hσm.monotoneOn huS (hcI τ) hu.2
  have hLT : IsLoewnerTraceLT W (σ S) η₀ := by
    refine ⟨by simp [hη₀, hc0, h0], hη₀c.continuousOn, fun τ hτ hτS => ?_⟩
    rw [himg τ ⟨hτ, hτS.le⟩, hfill (c τ) (hcI τ), ← hσK (c τ) (hcI τ), hσc' τ ⟨hτ, hτS.le⟩]
  have hσt : 0 ≤ σ t := by
    rw [← hσ0]; exact hσm.monotoneOn ⟨le_rfl, hS.le⟩ ⟨ht.1.le, ht.2.le⟩ ht.1.le
  have hσtS : σ t < σ S := hσm ⟨ht.1.le, ht.2.le⟩ ⟨hS.le, le_rfl⟩ ht.2
  have hext := hLT.isLoewnerTrace_ext hW hW0 hσt hσtS
  refine ⟨_, hext, ?_, fun u hu => ?_, ?_⟩
  · -- the extension is a simple proper arc
    have hWt := hσK t ⟨ht.1.le, ht.2.le⟩
    have hF : ∀ r : ℝ, 0 < r → YuanCorollary13.extTrace W η₀ (σ t) (σ t + r) =
        fwdMapInv W (σ t) (((2 * Real.sqrt r : ℝ) : ℂ) * I) ∧
        fwdMapInv W (σ t) (((2 * Real.sqrt r : ℝ) : ℂ) * I) ∈ H \ fwdHull W (σ t) := by
      intro r hr
      have hwH : (((2 * Real.sqrt r : ℝ) : ℂ) * I) ∈ H := by
        show (0 : ℝ) < ((((2 * Real.sqrt r : ℝ) : ℂ) * I)).im
        simpa using Real.sqrt_pos.2 hr
      refine ⟨?_, QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 hσt hwH⟩
      simp only [YuanCorollary13.extTrace, show ¬ (σ t + r ≤ σ t) by linarith, ↓reduceIte,
        add_sub_cancel_left]
      exact extendFrom_fwdMapInv_eq hW hW0 hσt hwH
    have hpre : ∀ τ ∈ Icc (0 : ℝ) (σ t), YuanCorollary13.extTrace W η₀ (σ t) τ = γ (c τ) ∧
        c τ ∈ Icc (0 : ℝ) t := fun τ hτ => by
      refine ⟨YuanCorollary13.extTrace_eq hτ.2, (hcI τ).1, ?_⟩
      rw [← hcσ t ⟨ht.1.le, ht.2.le⟩]; exact hcmono hτ.2
    have hpos : ∀ τ ∈ Ioc (0 : ℝ) (σ t), 0 < c τ := fun τ hτ => by
      by_contra hle
      have hc0' : c τ = 0 := le_antisymm (not_lt.1 hle) (hcI τ).1
      have := hσc' τ ⟨hτ.1.le, hτ.2.trans hσtS.le⟩
      rw [hc0', hσ0] at this
      linarith [hτ.1]
    refine ⟨hext.2.1, fun a ha b hb hab => ?_, hext.1, fun τ hτ => ?_, ?_⟩
    · rcases le_or_gt a (σ t) with hat | hat <;> rcases le_or_gt b (σ t) with hbt | hbt
      · obtain ⟨e1, hc1⟩ := hpre a ⟨ha, hat⟩
        obtain ⟨e2, hc2⟩ := hpre b ⟨hb, hbt⟩
        rw [e1, e2] at hab
        have := hinj ⟨hc1.1, hc1.2.trans ht.2.le⟩ ⟨hc2.1, hc2.2.trans ht.2.le⟩ hab
        rw [← hσc' a ⟨ha, hat.trans hσtS.le⟩, ← hσc' b ⟨hb, hbt.trans hσtS.le⟩, this]
      · exfalso
        obtain ⟨e1, hc1⟩ := hpre a ⟨ha, hat⟩
        obtain ⟨e2, hm⟩ := hF (b - σ t) (by linarith)
        rw [show σ t + (b - σ t) = b by ring] at e2
        rw [e1, e2] at hab
        refine hm.2 ?_
        rw [← hab, hWt]
        rcases (hcI a).1.eq_or_lt with h | h
        · exfalso; have := hm.1; rw [← hab, ← h, h0] at this
          exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
        · exact ⟨c a, ⟨h, hc1.2⟩, rfl⟩
      · exfalso
        obtain ⟨e2, hc2⟩ := hpre b ⟨hb, hbt⟩
        obtain ⟨e1, hm⟩ := hF (a - σ t) (by linarith)
        rw [show σ t + (a - σ t) = a by ring] at e1
        rw [e1, e2] at hab
        refine hm.2 ?_
        rw [hab, hWt]
        rcases (hcI b).1.eq_or_lt with h | h
        · exfalso; have := hm.1; rw [hab, ← h, h0] at this
          exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
        · exact ⟨c b, ⟨h, hc2.2⟩, rfl⟩
      · obtain ⟨e1, -⟩ := hF (a - σ t) (by linarith)
        obtain ⟨e2, -⟩ := hF (b - σ t) (by linarith)
        rw [show σ t + (a - σ t) = a by ring] at e1
        rw [show σ t + (b - σ t) = b by ring] at e2
        rw [e1, e2] at hab
        have hwa : (((2 * Real.sqrt (a - σ t) : ℝ) : ℂ) * I) ∈ H := by
          show (0 : ℝ) < ((((2 * Real.sqrt (a - σ t) : ℝ) : ℂ) * I)).im
          simpa using Real.sqrt_pos.2 (show 0 < a - σ t by linarith)
        have hwb : (((2 * Real.sqrt (b - σ t) : ℝ) : ℂ) * I) ∈ H := by
          show (0 : ℝ) < ((((2 * Real.sqrt (b - σ t) : ℝ) : ℂ) * I)).im
          simpa using Real.sqrt_pos.2 (show 0 < b - σ t by linarith)
        have h2 := congrArg (fwdMap W (σ t)) hab
        rw [QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 hσt hwa,
          QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 hσt hwb] at h2
        have h3 := congrArg Complex.im h2
        simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero] at h3
        have h4 : Real.sqrt (a - σ t) = Real.sqrt (b - σ t) := by linarith
        have h5 := congrArg (fun x => x ^ 2) h4
        simp only [Real.sq_sqrt (show 0 ≤ a - σ t by linarith),
          Real.sq_sqrt (show 0 ≤ b - σ t by linarith)] at h5
        linarith
    · rcases le_or_gt τ (σ t) with hτt | hτt
      · obtain ⟨e1, -⟩ := hpre τ ⟨hτ.le, hτt⟩
        rw [e1]
        exact hH _ ⟨hpos τ ⟨hτ, hτt⟩, (hcI τ).2⟩
      · obtain ⟨e1, hm⟩ := hF (τ - σ t) (by linarith)
        rw [show σ t + (τ - σ t) = τ by ring] at e1
        rw [e1]; exact hm.1
    · -- tends to `∞`
      obtain ⟨C, hC⟩ := exists_norm_fwdMapInv_sub_le hW hW0 hσt
      rw [tendsto_atTop_atTop]
      intro B
      refine ⟨σ t + ((|B| + C + 1) / 2) ^ 2 + 1, fun τ hτ => ?_⟩
      have hr : 0 < τ - σ t := by nlinarith [sq_nonneg ((|B| + C + 1) / 2)]
      obtain ⟨e1, hm⟩ := hF (τ - σ t) hr
      rw [show σ t + (τ - σ t) = τ by ring] at e1
      rw [e1]
      have hwH : (((2 * Real.sqrt (τ - σ t) : ℝ) : ℂ) * I) ∈ H := by
        show (0 : ℝ) < ((((2 * Real.sqrt (τ - σ t) : ℝ) : ℂ) * I)).im
        simpa using Real.sqrt_pos.2 hr
      have h1 := hC _ hwH
      have hn : ‖(((2 * Real.sqrt (τ - σ t) : ℝ) : ℂ) * I)‖ = 2 * Real.sqrt (τ - σ t) := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity)]
      have hC0 : 0 ≤ C := (norm_nonneg _).trans h1
      have hsq : (|B| + C + 1) / 2 ≤ Real.sqrt (τ - σ t) := by
        rw [show (|B| + C + 1) / 2 = Real.sqrt (((|B| + C + 1) / 2) ^ 2) from
          (Real.sqrt_sq (by have := abs_nonneg B; linarith)).symm]
        exact Real.sqrt_le_sqrt (by linarith)
      have h2 := norm_sub_norm_le (fwdMapInv W (σ t) (((2 * Real.sqrt (τ - σ t) : ℝ) : ℂ) * I))
        (((2 * Real.sqrt (τ - σ t) : ℝ) : ℂ) * I)
      have h3 := norm_sub_rev (fwdMapInv W (σ t) (((2 * Real.sqrt (τ - σ t) : ℝ) : ℂ) * I))
        (((2 * Real.sqrt (τ - σ t) : ℝ) : ℂ) * I)
      linarith [le_abs_self B, norm_sub_norm_le (((2 * Real.sqrt (τ - σ t) : ℝ) : ℂ) * I)
        (fwdMapInv W (σ t) (((2 * Real.sqrt (τ - σ t) : ℝ) : ℂ) * I))]
  · rw [YuanCorollary13.extTrace_eq (by
      exact hσm.monotoneOn ⟨hu.1, hu.2.trans ht.2.le⟩ ⟨ht.1.le, ht.2.le⟩ hu.2)]
    simp only [hη₀, hcσ u ⟨hu.1, hu.2.trans ht.2.le⟩]
  · rw [hLT.fwdHull_extDrive_of_le hW hσtS hσt le_rfl]
    have h2 : YuanCorollary13.extTrace W η₀ (σ t) '' Icc 0 (σ t) = η₀ '' Icc 0 (σ t) :=
      image_congr fun τ hτ => YuanCorollary13.extTrace_eq hτ.2
    rw [h2, himg (σ t) ⟨hσt, hσtS.le⟩, hcσ t ⟨ht.1.le, ht.2.le⟩, hfill t ⟨ht.1.le, ht.2.le⟩]

end Simple

end InteractingSLE.WangWu
