/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.AvoidObs
import InteractingSLE.Spec.Zhan.AvoidHeight
import InteractingSLE.Spec.Zhan.AvoidPassive
import InteractingSLE.Spec.Sec4.RepulsionDrift
import InteractingSLE.Spec.Sec2.AddMarksMerge

/-!
# The whole strip clock is finite (`κ ≤ 4`)

Packet PROVE-ZHAN-B. Astra, *Formalization proofs and dependency audit* (`source/external/AstraIG1/`,
text dump L1336–1376, ruling R35): in the proof of the avoidance lemma, "Brownian motion is unbounded
above, so `S < ∞`", for the strip chart sending two real points `r₊ < r₋ < 0` (all left marks between
them) to the strip ends.

For an integrated `SLE_κ(ρ)` evolution, `0 < κ ≤ 4`, of an ordered word whose marks are separated from
the seed and whose side partial sums are admissible, almost surely the strip clock
`∫₀^∞ (1/c_t − 1/a_t)² dt` is finite, where `a_t = g_t(r₋) − W_t` and `c_t = g_t(r₊) − W_t`
(`IsIntegratedSLEEvolution.ae_stripClock_bounded`). Proof: the observable `Φ` of `AvoidObs.lean` along
the evolution (state `(g(r₋), g(r₊), g(r), W − √κ B, V)`, `r` = the first right mark, or `1`) is a
positive function with nonpositive drift, and `∂_b Φ = −√κ (1/α − 1/γ)`; apply
`ae_bddAbove_integral_sq_partialSnd`.

§1 is pathwise: the image `t ↦ W_t + Re f_t(x)` of a real point that is never swallowed solves the
force-point equation and keeps its order with the marks.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Zhan

open QuantumZipper

/-! ### §1. Real flows along one path -/

section RealFlow

variable {w : ℝ≥0 → ℝ}

/-- The image `g_t(x) = W_t + Re f_t(x)` of a real point under the Loewner flow. -/
def realFlow (w : ℝ≥0 → ℝ) (x : ℝ) (t : ℝ≥0) : ℝ :=
  w t + (fwdMap (fun s : ℝ => w s.toNNReal) t x).re

variable (hw : Continuous fun s : ℝ => w s.toNNReal) (hw0 : w 0 = 0) {x : ℝ}
  (hx : ∀ T : ℝ, 0 ≤ T → ∃ v, IsForwardSol (fun s : ℝ => w s.toNNReal) (x : ℂ) T v)

include hw hx in
/-- On `[0, T]` the centred flow is the forward solution. -/
theorem fwdMap_real_eq {T : ℝ} (hT : 0 ≤ T) :
    ∃ v, IsForwardSol (fun s : ℝ => w s.toNNReal) (x : ℂ) T v ∧
      ∀ s ∈ Icc (0 : ℝ) T, fwdMap (fun s : ℝ => w s.toNNReal) s x = v s := by
  obtain ⟨v, hv⟩ := hx T hT
  exact ⟨v, hv, fun s hs => fwdMap_eq_of_isForwardSol hw hv hs⟩

theorem continuous_toNNReal_comp_iff' : Continuous w ↔ Continuous fun s : ℝ => w s.toNNReal := by
  constructor
  · exact fun h => h.comp continuous_real_toNNReal
  · intro h
    have : w = (fun s : ℝ => w s.toNNReal) ∘ (fun t : ℝ≥0 => (t : ℝ)) := by
      funext t; simp
    rw [this]; exact h.comp NNReal.continuous_coe

include hw hx in
theorem continuous_realFlow : Continuous (realFlow w x) := by
  have hwc : Continuous w := continuous_toNNReal_comp_iff'.2 hw
  rw [continuous_iff_continuousAt]
  intro t₀
  obtain ⟨v, hv, heq⟩ := fwdMap_real_eq hw hx (T := t₀ + 1) (by positivity)
  have hS : Iic (t₀ + 1 : ℝ≥0) ∈ 𝓝 t₀ := Iic_mem_nhds (by
    rw [← NNReal.coe_lt_coe]; push_cast; linarith)
  have hc : ContinuousOn (fun t : ℝ≥0 => (fwdMap (fun s : ℝ => w s.toNNReal) t x).re)
      (Iic (t₀ + 1)) := by
    have h1 : ContinuousOn (fun t : ℝ≥0 => (v t).re) (Iic (t₀ + 1)) :=
      (Complex.continuous_re.comp_continuousOn hv.1).comp NNReal.continuous_coe.continuousOn
        fun t ht => ⟨t.coe_nonneg, by have : t ≤ t₀ + 1 := ht; exact_mod_cast this⟩
    refine h1.congr fun t ht => ?_
    have : t ≤ t₀ + 1 := ht
    simp only [heq t ⟨t.coe_nonneg, by exact_mod_cast this⟩]
  exact (hwc.continuousAt).add (hc.continuousAt hS)

/-- The centred flow in terms of the flow. -/
theorem realFlow_sub_eq {s : ℝ} (hs : 0 ≤ s) :
    (fwdMap (fun s : ℝ => w s.toNNReal) s x).re = realFlow w x s.toNNReal - w s.toNNReal := by
  simp only [realFlow, Real.coe_toNNReal _ hs]
  ring

include hw hx in
/-- **The force-point equation** `g_t(x) = x + ∫₀ᵗ 2/(g_s(x) − W_s)`. -/
theorem realFlow_eq (t : ℝ≥0) :
    realFlow w x t = x + ∫ s in (0 : ℝ)..t, 2 / (realFlow w x s.toNNReal - w s.toNNReal) := by
  obtain ⟨v, hv, heq⟩ := fwdMap_real_eq hw hx t.coe_nonneg
  have h := Sec4.re_add_eq_of_isForwardSol hw hv ⟨t.coe_nonneg, le_rfl⟩
  have hvt : (v t).re = (fwdMap (fun s : ℝ => w s.toNNReal) t x).re := by
    rw [heq t ⟨t.coe_nonneg, le_rfl⟩]
  rw [realFlow, ← hvt, show w t = (fun s : ℝ => w s.toNNReal) t by simp, add_comm, h]
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le t.coe_nonneg] at hs
  rw [← heq s hs, realFlow_sub_eq hs.1]

include hw hw0 hx in
theorem realFlow_lt_of_neg (hxn : x < 0) (t : ℝ≥0) : realFlow w x t < w t := by
  obtain ⟨v, hv, heq⟩ := fwdMap_real_eq hw hx t.coe_nonneg
  have hW0 : (fun s : ℝ => w s.toNNReal) 0 = 0 := by simp [hw0]
  have := re_neg_of_isForwardSol hw hW0 hxn hv ⟨t.coe_nonneg, le_rfl⟩
  rw [realFlow, heq t ⟨t.coe_nonneg, le_rfl⟩]
  linarith

include hw hw0 hx in
theorem lt_realFlow_of_pos (hxp : 0 < x) (t : ℝ≥0) : w t < realFlow w x t := by
  obtain ⟨v, hv, heq⟩ := fwdMap_real_eq hw hx t.coe_nonneg
  have hW0 : (fun s : ℝ => w s.toNNReal) 0 = 0 := by simp [hw0]
  have hT : (0 : ℝ) ≤ t := t.coe_nonneg
  -- the reflected flow
  have hvn := RS.isForwardSol_neg hv
  have hcn : Continuous fun s : ℝ => -w s.toNNReal := hw.neg
  have hn0 : (fun s : ℝ => -w s.toNNReal) 0 = 0 := by simp [hw0]
  have hvn' : IsForwardSol (fun s : ℝ => -w s.toNNReal) ((-x : ℝ) : ℂ) t fun t => -v t := by
    simpa using hvn
  have hneg := re_neg_of_isForwardSol hcn hn0 (neg_neg_of_pos hxp) hvn' ⟨t.coe_nonneg, le_rfl⟩
  rw [realFlow, heq t ⟨t.coe_nonneg, le_rfl⟩]
  simp only [Complex.neg_re] at hneg
  linarith

include hw hw0 hx in
theorem intervalIntegrable_realFlow (hx0 : x ≠ 0) (t : ℝ≥0) :
    IntervalIntegrable (fun s : ℝ => 2 / (realFlow w x s.toNNReal - w s.toNNReal)) volume 0 t := by
  refine ContinuousOn.intervalIntegrable ?_
  have hc : Continuous fun s : ℝ => realFlow w x s.toNNReal - w s.toNNReal :=
    ((continuous_realFlow hw hx).comp continuous_real_toNNReal).sub hw
  refine continuousOn_const.div hc.continuousOn fun s _ => ?_
  rcases lt_or_gt_of_ne hx0 with h | h
  · exact (sub_neg.2 (realFlow_lt_of_neg hw hw0 hx h _)).ne
  · exact (sub_pos.2 (lt_realFlow_of_pos hw hw0 hx h _)).ne'

/-! #### Order -/

omit hw0 in
include hw in
theorem realFlow_lt_realFlow {y : ℝ} (hxy : x < y) (hx : ∀ T : ℝ, 0 ≤ T →
      ∃ v, IsForwardSol (fun s : ℝ => w s.toNNReal) (x : ℂ) T v)
    (hy : ∀ T : ℝ, 0 ≤ T → ∃ v, IsForwardSol (fun s : ℝ => w s.toNNReal) (y : ℂ) T v)
    (t : ℝ≥0) : realFlow w x t < realFlow w y t := by
  obtain ⟨vx, hvx, heqx⟩ := fwdMap_real_eq hw hx t.coe_nonneg
  obtain ⟨vy, hvy, heqy⟩ := fwdMap_real_eq hw hy t.coe_nonneg
  have h := re_lt_re_of_isForwardSol hw hxy hvx hvy ⟨t.coe_nonneg, le_rfl⟩
  simp only [realFlow, heqx t ⟨t.coe_nonneg, le_rfl⟩, heqy t ⟨t.coe_nonneg, le_rfl⟩]
  linarith

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}

theorem intervalIntegrable_two_div_of_inv {u : ℝ≥0 → ℝ} {t : ℝ}
    (h : IntervalIntegrable (fun s : ℝ => (w s.toNNReal - u s.toNNReal)⁻¹) volume 0 t) :
    IntervalIntegrable (fun s : ℝ => 2 / (u s.toNNReal - w s.toNNReal)) volume 0 t := by
  have := h.const_mul (-2)
  refine this.congr fun s _ => ?_
  show -2 * (w s.toNNReal - u s.toNNReal)⁻¹ = 2 / (u s.toNNReal - w s.toNNReal)
  rw [div_eq_mul_inv, ← neg_sub, inv_neg]; ring

include hw hw0 hx in
/-- A left mark started at or beyond `x < 0` stays at or beyond `g_t(x)`. -/
theorem IsIntegratedSLEPath.vL_le_realFlow
    (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ⊤) (hxn : x < 0) (i : Fin nL)
    (hi : xL i ≤ x) (t : ℝ≥0) : vL i t ≤ realFlow w x t := by
  obtain ⟨-, -, -, -, hvLc, -, -, hvLw, -, -, hgL, -, -, hvLeq, -, hcolL, -⟩ := hp
  refine Sec2.le_of_forceEq_left (τ := ⊤) (w := w) (u := realFlow w x) (v := vL i) hi
    (continuous_realFlow hw hx).continuousOn (hvLc i) (fun {t} _ => realFlow_eq hw hx t)
    (fun {t} ht => hvLeq t ht i) (fun {t} _ => intervalIntegrable_realFlow hw hw0 hx hxn.ne t)
    (fun {t} ht => intervalIntegrable_two_div_of_inv (hgL t ht i)) (fun {t} ht => hvLw t ht i)
    (hcolL i) ENNReal.coe_lt_top

include hw hw0 hx in
/-- `g_t(x) ≤ v^{i,L}_t` for a real point `x < 0` beyond the mark. -/
theorem IsIntegratedSLEPath.realFlow_le_vL
    (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ⊤) (hxn : x < 0) (i : Fin nL)
    (hi : x ≤ xL i) (t : ℝ≥0) : realFlow w x t ≤ vL i t := by
  obtain ⟨-, -, -, -, hvLc, -, -, -, -, -, hgL, -, -, hvLeq, -, -, -⟩ := hp
  have hcoll : volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ⊤ ∧
      w s.toNNReal = realFlow w x s.toNNReal} = 0 := by
    have : {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ⊤ ∧ w s.toNNReal = realFlow w x s.toNNReal} = ∅ := by
      ext s
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      exact fun _ _ h => (realFlow_lt_of_neg hw hw0 hx hxn s.toNNReal).ne' h
    rw [this, measure_empty]
  refine Sec2.le_of_forceEq_left (τ := ⊤) (w := w) (u := vL i) (v := realFlow w x) hi
    (hvLc i) (continuous_realFlow hw hx).continuousOn (fun {t} ht => hvLeq t ht i)
    (fun {t} _ => realFlow_eq hw hx t) (fun {t} ht => intervalIntegrable_two_div_of_inv (hgL t ht i))
    (fun {t} _ => intervalIntegrable_realFlow hw hw0 hx hxn.ne t)
    (fun {t} _ => (realFlow_lt_of_neg hw hw0 hx hxn t).le) hcoll ENNReal.coe_lt_top

include hw hw0 hx in
/-- `g_t(x) ≤ v^{j,R}_t` for a real point `0 < x` before the mark. -/
theorem IsIntegratedSLEPath.realFlow_le_vR
    (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ⊤) (hxp : 0 < x) (j : Fin nR)
    (hj : x ≤ xR j) (t : ℝ≥0) : realFlow w x t ≤ vR j t := by
  obtain ⟨-, -, -, -, -, hvRc, -, -, hwvR, -, -, hgR, -, -, hvReq, -, hcolR, -⟩ := hp
  refine Sec2.le_of_forceEq_right (τ := ⊤) (w := w) (u := vR j) (v := realFlow w x) hj
    (hvRc j) (continuous_realFlow hw hx).continuousOn (fun {t} ht => hvReq t ht j)
    (fun {t} _ => realFlow_eq hw hx t) (fun {t} ht => intervalIntegrable_two_div_of_inv (hgR t ht j))
    (fun {t} _ => intervalIntegrable_realFlow hw hw0 hx hxp.ne' t) (fun {t} ht => hwvR t ht j)
    (hcolR j) ENNReal.coe_lt_top

end RealFlow

/-! ### §2. Adapted versions of the real flows -/

section Passive

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞}
  {W : ℝ≥0 → Ω → ℝ}

/-- **The mark equals every continuous solution.** On a path along which `W` is continuous before `ζ`,
the mark `markFlow F y` at `t < ζ` is the value at `t` of any continuous solution of
`u = y + ∫ F(u − W)` on `[0, t]`. -/
theorem markFlow_eq_of_sol {F : ℝ → ℝ} {K : ℝ≥0} (hF : LipschitzWith K F) {y : ℝ} {ω : Ω}
    (hWc : ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω}) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ ω) {u : ℝ → ℝ} (huc : ContinuousOn u (Icc 0 t))
    (hu : ∀ s ∈ Icc (0 : ℝ) t, u s = y + ∫ r in (0 : ℝ)..s, F (u r - W r.toNNReal ω)) :
    Sec2.markFlow F y ζ W t ω = u t := by
  set wt : ℝ → ℝ := fun s => W (min s.toNNReal t) ω with hwt
  have hwtc : Continuous wt := by
    refine hWc.comp_continuous (continuous_real_toNNReal.min continuous_const) fun s => ?_
    exact lt_of_le_of_lt (by exact_mod_cast min_le_right _ _) ht
  have hwt_eq : ∀ s ∈ Icc (0 : ℝ) t, wt s = W s.toNNReal ω := fun s hs => by
    simp only [hwt, min_eq_left (Real.toNNReal_le_iff_le_coe.2 hs.2)]
  have hu' : ∀ s ∈ Icc (0 : ℝ) t, u s = y + ∫ r in (0 : ℝ)..s, F (u r - wt r) := by
    intro s hs
    rw [hu s hs]
    congr 1
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hs.1] at hr
    simp only [hwt_eq r ⟨hr.1, hr.2.trans hs.2⟩]
  have hT := Sec2.tendsto_eulerAt (y := y) (t := t) hF t.coe_nonneg hwtc.continuousOn huc hu'
    (wk := fun n k => Girsanov.killed ζ W (Girsanov.grid n k) ω) fun n k hk => by
      have hgk : ((Girsanov.grid n k : ℝ≥0) : ℝ) = k / 2 ^ n := Girsanov.coe_grid n k
      have hle : Girsanov.grid n k ≤ t := by
        rw [← NNReal.coe_le_coe, hgk]; exact hk
      rw [Girsanov.killed_of_lt (lt_of_le_of_lt (by exact_mod_cast hle) ht), hwt]
      simp only
      congr 1
      rw [← hgk, Real.toNNReal_coe, min_eq_left hle]
  unfold Sec2.markFlow Sec2.markEuler
  exact hT.limsup_eq

/-- The passive left flow: the `limsup` over the cut levels `1/(n+1)` of the cut marks from `r`. -/
def passiveL (r : ℝ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  limsup (fun n : ℕ => Sec2.leftMark (1 / ((n : ℝ) + 1)) r ζ W t ω) atTop

/-- The passive right flow. -/
def passiveR (r : ℝ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  limsup (fun n : ℕ => Sec2.rightMark (1 / ((n : ℝ) + 1)) r ζ W t ω) atTop

theorem measurable_passiveL (hW : AdaptedBefore 𝓕 ζ W) (r : ℝ) (t : ℝ≥0) :
    Measurable[𝓕 t] (passiveL r ζ W t) :=
  @Sec2.measurable_limsup_aux Ω (𝓕 t) _ fun n =>
    Sec2.measurable_markFlow (Sec2.lipschitzWith_leftMarkDrift (δ := 1 / ((n : ℝ) + 1))
      (by positivity)).continuous.measurable hW t

theorem measurable_passiveR (hW : AdaptedBefore 𝓕 ζ W) (r : ℝ) (t : ℝ≥0) :
    Measurable[𝓕 t] (passiveR r ζ W t) :=
  @Sec2.measurable_limsup_aux Ω (𝓕 t) _ fun n =>
    Sec2.measurable_markFlow (Sec2.lipschitzWith_rightMarkDrift (δ := 1 / ((n : ℝ) + 1))
      (by positivity)).continuous.measurable hW t

/-- The cut mark agrees with the true flow once the cut level is below the gap on `[0, t]`. -/
theorem eventually_cutMark_eq {ω : Ω} (hζ : ζ ω = ⊤)
    (hw : Continuous fun s : ℝ => W s.toNNReal ω) (hw0 : W 0 ω = 0) {r : ℝ} (hr : r ≠ 0)
    (hx : ∀ T : ℝ, 0 ≤ T → ∃ v, IsForwardSol (fun s : ℝ => W s.toNNReal ω) (r : ℂ) T v)
    (t : ℝ≥0) {F : ℕ → ℝ → ℝ} {K : ℕ → ℝ≥0} (hF : ∀ n, LipschitzWith (K n) (F n))
    (hFeq : ∀ ε > 0, ∀ᶠ n in atTop, ∀ x : ℝ, ε ≤ |x| → (0 < x ↔ 0 < r) → F n x = 2 / x) :
    ∀ᶠ n in atTop, Sec2.markFlow (F n) r ζ W t ω = realFlow (W · ω) r t := by
  have hwc : Continuous (W · ω) := continuous_toNNReal_comp_iff'.2 hw
  have hWc : ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω} := hwc.continuousOn
  set A := realFlow (W · ω) r with hA
  have hAc : Continuous A := continuous_realFlow (w := fun t => W t ω) hw hx
  -- the gap on `[0, t]`
  have hgap : ∀ s : ℝ≥0, 0 < |A s - W s ω| ∧ (0 < A s - W s ω ↔ 0 < r) := fun s => by
    rcases lt_or_gt_of_ne hr with h | h
    · have := realFlow_lt_of_neg (w := fun t => W t ω) hw hw0 hx h s
      exact ⟨abs_pos.2 (by linarith), ⟨fun h' => by linarith, fun h' => by linarith⟩⟩
    · have := lt_realFlow_of_pos (w := fun t => W t ω) hw hw0 hx h s
      exact ⟨abs_pos.2 (by linarith), ⟨fun _ => h, fun _ => by linarith⟩⟩
  obtain ⟨s₀, hs₀, hmin⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).exists_isMinOn
    (nonempty_Icc.2 zero_le) ((hAc.sub hwc).abs.continuousOn)
  have hδ : 0 < |A s₀ - W s₀ ω| := (hgap s₀).1
  filter_upwards [hFeq _ hδ] with n hn
  have key := markFlow_eq_of_sol (hF n) (y := r) (t := t) hWc
    (by rw [hζ]; exact ENNReal.coe_lt_top) (u := fun s : ℝ => A s.toNNReal)
    (hAc.comp continuous_real_toNNReal).continuousOn ?_
  · rw [key]; simp
  intro s hs
  have h := realFlow_eq (w := fun t => W t ω) hw hx s.toNNReal
  rw [Real.coe_toNNReal _ hs.1] at h
  show A s.toNNReal = _
  rw [hA, h]
  congr 1
  refine intervalIntegral.integral_congr fun q hq => ?_
  rw [uIcc_of_le hs.1] at hq
  have hq' : q.toNNReal ∈ Icc 0 t := ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 (hq.2.trans hs.2)⟩
  have hle : |A s₀ - W s₀ ω| ≤ |A q.toNNReal - W q.toNNReal ω| := hmin hq'
  exact (hn _ hle (hgap _).2).symm

theorem passiveL_eq_realFlow {ω : Ω} (hζ : ζ ω = ⊤)
    (hw : Continuous fun s : ℝ => W s.toNNReal ω) (hw0 : W 0 ω = 0) {r : ℝ} (hr : r < 0)
    (hx : ∀ T : ℝ, 0 ≤ T → ∃ v, IsForwardSol (fun s : ℝ => W s.toNNReal ω) (r : ℂ) T v)
    (t : ℝ≥0) : passiveL r ζ W t ω = realFlow (W · ω) r t := by
  have hev := eventually_cutMark_eq (F := fun n => Sec2.leftMarkDrift (1 / ((n : ℝ) + 1)))
    hζ hw hw0 hr.ne hx t (fun n => Sec2.lipschitzWith_leftMarkDrift (by positivity))
    fun ε hε => by
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
      filter_upwards [eventually_ge_atTop N] with n hn x hx hsgn
      have hxn : x < 0 := lt_of_not_ge fun h => absurd ((hsgn.1 (lt_of_le_of_ne h fun h0 => by
        rw [← h0, abs_zero] at hx; linarith))) (not_lt.2 hr.le)
      refine Sec2.leftMarkDrift_of_le ?_
      rw [abs_of_neg hxn] at hx
      refine le_trans ?_ hx
      refine (one_div_le_one_div_of_le (by positivity) ?_).trans hN.le
      exact_mod_cast Nat.add_le_add_right hn 1
  unfold passiveL Sec2.leftMark
  exact (tendsto_const_nhds.congr' (hev.mono fun n h => h.symm)).limsup_eq

theorem passiveR_eq_realFlow {ω : Ω} (hζ : ζ ω = ⊤)
    (hw : Continuous fun s : ℝ => W s.toNNReal ω) (hw0 : W 0 ω = 0) {r : ℝ} (hr : 0 < r)
    (hx : ∀ T : ℝ, 0 ≤ T → ∃ v, IsForwardSol (fun s : ℝ => W s.toNNReal ω) (r : ℂ) T v)
    (t : ℝ≥0) : passiveR r ζ W t ω = realFlow (W · ω) r t := by
  have hev := eventually_cutMark_eq (F := fun n => Sec2.rightMarkDrift (1 / ((n : ℝ) + 1)))
    hζ hw hw0 hr.ne' hx t (fun n => Sec2.lipschitzWith_rightMarkDrift (by positivity))
    fun ε hε => by
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
      filter_upwards [eventually_ge_atTop N] with n hn x hx hsgn
      have hxp : 0 < x := hsgn.2 hr
      refine Sec2.rightMarkDrift_of_le ?_
      rw [abs_of_pos hxp] at hx
      refine le_trans ?_ hx
      refine (one_div_le_one_div_of_le (by positivity) ?_).trans hN.le
      exact_mod_cast Nat.add_le_add_right hn 1
  unfold passiveR Sec2.rightMark
  exact (tendsto_const_nhds.congr' (hev.mono fun n h => h.symm)).limsup_eq

end Passive

/-! ### §3. The strip clock of an evolution -/

section Assembly

open scoped Classical

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- The good paths: the integrated path conditions, infinite lifetime, no real point swallowed, the
marks separated from the driver, a continuous Brownian path started at `0`. -/
def IsGoodClock (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : Prop :=
  IsIntegratedSLEPath κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (B · ω)
    (ζ ω) ∧ ζ ω = ⊤ ∧
  (∀ x : ℝ, x ≠ 0 → ∀ T : ℝ, 0 ≤ T → ∃ v, IsForwardSol (fun s : ℝ => W s.toNNReal ω) (x : ℂ) T v) ∧
  (∀ t, (∀ i, VL i t ω < W t ω) ∧ ∀ j, W t ω < VR j t ω) ∧ Continuous (B · ω) ∧ B 0 ω = 0

theorem exists_good_clock [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (hF : IsOrderedForceWord xL xR) (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hxL : ∀ i, xL i < 0) (hxR : ∀ i, 0 < xR i)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ ω ∈ G, IsGoodClock κ xL xR ρL ρR W VL VR B ζ ω := by
  have hae : ∀ᵐ ω ∂P, IsGoodClock κ xL xR ρL ρR W VL VR B ζ ω := by
    filter_upwards [hE.2.2.2.2, hE.ae_real_alive_of_hasAdmissiblePartialSums hκ hκ4 hF hadm hxL hxR,
      Sec4.aux6Statement hκ xL xR ρL ρR P 𝓕 W VL VR B ζ hF hadm hE, hE.1.1.cont,
      hE.1.1.eval_zero_ae_eq_zero] with ω hp hal h6 hBc hB0
    refine ⟨hp, hal.1, hal.2, fun t => ?_, hBc, hB0⟩
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with ht | ht
    · subst ht
      have h0 : W 0 ω = 0 := hp.1
      refine ⟨fun i => ?_, fun j => ?_⟩
      · have hv : VL i 0 ω = xL i := hp.2.1 i
        rw [h0, hv]; exact hxL i
      · have hv : VR j 0 ω = xR j := hp.2.2.1 j
        rw [h0, hv]; exact hxR j
    · exact h6.2 t ht
  refine ⟨(toMeasurable P {ω | ¬ IsGoodClock κ xL xR ρL ρR W VL VR B ζ ω})ᶜ,
    (measurableSet_toMeasurable _ _).compl, ?_, fun ω hω => ?_⟩
  · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
  · by_contra h; exact hω (subset_toMeasurable _ _ h)

/-- The right reference point: the first right mark, or `1` if there is none. -/
def rightRef (xR : Fin nR → ℝ) : ℝ := if h : 0 < nR then xR ⟨0, h⟩ else 1

theorem rightRef_pos (hxR : ∀ i, 0 < xR i) : 0 < rightRef xR := by
  unfold rightRef; split_ifs with h
  · exact hxR _
  · exact one_pos

theorem rightRef_le (hF : IsOrderedForceWord xL xR) (j : Fin nR) : rightRef xR ≤ xR j := by
  unfold rightRef
  have h : 0 < nR := Nat.zero_lt_of_lt j.2
  simp only [h, ↓reduceDIte]
  exact hF.2.2.1 (Fin.mk_le_mk.2 (Nat.zero_le _) : (⟨0, h⟩ : Fin nR) ≤ j)

/-- The state process `(g(r₋), g(r₊), g(r), W − √κB, (V^L, V^R))` on `G` (the initial state off `G`). -/
def clockState (κ : ℝ) (G : Set Ω) (rm rp r : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (t : ℝ≥0) (ω : Ω) : ObsE nL nR :=
  if ω ∈ G then
    (passiveL rm ζ W t ω, passiveL rp ζ W t ω, passiveR r ζ W t ω,
      Girsanov.killed ζ W t ω - Real.sqrt κ * B t ω,
      (fun i => Girsanov.killed ζ (VL i) t ω, fun j => Girsanov.killed ζ (VR j) t ω))
  else (rm, rp, r, 0, (xL, xR))

/-- The Brownian motion on `G` (`0` off `G`). -/
def clockBrown (G : Set Ω) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ := if ω ∈ G then B t ω else 0

end Assembly

section AssemblyFacts

open scoped Classical

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω} {rm rp r : ℝ}

theorem IsGoodClock.continuous_w {ω : Ω} (h : IsGoodClock κ xL xR ρL ρR W VL VR B ζ ω) :
    Continuous fun s : ℝ => W s.toNNReal ω := by
  obtain ⟨hp, hζ, -⟩ := h
  have hc : Continuous (W · ω) := by
    rw [← continuousOn_univ]
    refine hp.2.2.2.1.mono fun t _ => ?_
    show (t : ℝ≥0∞) < ζ ω
    rw [hζ]; exact ENNReal.coe_lt_top
  exact hc.comp continuous_real_toNNReal

/-- On a good path the state is the explicit one. -/
theorem clockState_of_good {ω : Ω} (hω : ω ∈ G) (h : IsGoodClock κ xL xR ρL ρR W VL VR B ζ ω)
    (hrm : rm < 0) (hrp : rp < 0) (hr : 0 < r) (t : ℝ≥0) :
    clockState κ G rm rp r xL xR W VL VR B ζ t ω =
      (realFlow (W · ω) rm t, realFlow (W · ω) rp t, realFlow (W · ω) r t,
        W t ω - Real.sqrt κ * B t ω, (fun i => VL i t ω, fun j => VR j t ω)) := by
  have hw := h.continuous_w
  obtain ⟨hp, hζ, hal, -⟩ := h
  have hw0 : W 0 ω = 0 := hp.1
  have hlt : (t : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
  simp only [clockState, hω, ↓reduceIte, Girsanov.killed_of_lt hlt,
    passiveL_eq_realFlow hζ hw hw0 hrm (hal rm hrm.ne), passiveL_eq_realFlow hζ hw hw0 hrp
      (hal rp hrp.ne), passiveR_eq_realFlow hζ hw hw0 hr (hal r hr.ne')]

theorem clockState_zero (hgood : ∀ ω ∈ G, IsGoodClock κ xL xR ρL ρR W VL VR B ζ ω)
    (hrm : rm < 0) (hrp : rp < 0) (hr : 0 < r) (ω : Ω) :
    clockState κ G rm rp r xL xR W VL VR B ζ 0 ω = (rm, rp, r, 0, (xL, xR)) := by
  by_cases hω : ω ∈ G
  · have h := hgood ω hω
    rw [clockState_of_good hω h hrm hrp hr]
    obtain ⟨hp, -, hal, -, -, hB0⟩ := h
    have hw0 : W 0 ω = 0 := hp.1
    have hflow : ∀ x : ℝ, x ≠ 0 → realFlow (W · ω) x 0 = x := fun x hx => by
      obtain ⟨v, hv⟩ := hal x hx 0 le_rfl
      have h0 := (hv.2 0 ⟨le_rfl, le_rfl⟩).2
      simp only [intervalIntegral.integral_same, add_zero] at h0
      have hm := fwdMap_eq_of_isForwardSol (hgood ω hω).continuous_w hv ⟨le_rfl, le_rfl⟩
      simp only [realFlow, hw0, zero_add]
      rw [show ((0 : ℝ≥0) : ℝ) = 0 from rfl, hm, h0]
      simp [hw0]
    have hvL : (fun i => VL i 0 ω) = xL := funext fun i => hp.2.1 i
    have hvR : (fun j => VR j 0 ω) = xR := funext fun j => hp.2.2.1 j
    rw [hflow rm hrm.ne, hflow rp hrp.ne, hflow r hr.ne', hw0, hB0, hvL, hvR]
    simp
  · simp [clockState, hω]

theorem continuous_clockState (hgood : ∀ ω ∈ G, IsGoodClock κ xL xR ρL ρR W VL VR B ζ ω)
    (hrm : rm < 0) (hrp : rp < 0) (hr : 0 < r) (ω : Ω) :
    Continuous fun t => clockState κ G rm rp r xL xR W VL VR B ζ t ω := by
  by_cases hω : ω ∈ G
  · have h := hgood ω hω
    simp only [clockState_of_good hω h hrm hrp hr]
    have hw := h.continuous_w
    obtain ⟨hp, hζ, hal, -, hBc, -⟩ := h
    have hcw : Continuous (W · ω) := continuous_toNNReal_comp_iff'.2 hw
    have hsub : ∀ {f : ℝ≥0 → ℝ}, ContinuousOn f {t | (t : ℝ≥0∞) < ζ ω} → Continuous f :=
      fun {f} hf => by
        rw [← continuousOn_univ]
        exact hf.mono fun t _ => show (t : ℝ≥0∞) < ζ ω by rw [hζ]; exact ENNReal.coe_lt_top
    refine (continuous_realFlow hw (hal rm hrm.ne)).prodMk ((continuous_realFlow hw
      (hal rp hrp.ne)).prodMk ((continuous_realFlow hw (hal r hr.ne')).prodMk
      ((hcw.sub (continuous_const.mul hBc)).prodMk ((continuous_pi fun i =>
        hsub (hp.2.2.2.2.1 i)).prodMk (continuous_pi fun j => hsub (hp.2.2.2.2.2.1 j))))))
  · simp only [clockState, hω, ↓reduceIte]; exact continuous_const

theorem measurable_clockState [IsProbabilityMeasure P]
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
    (hGc : P Gᶜ = 0) (t : ℝ≥0) :
    Measurable[Ito.nullAugmented 𝓕 P t] (clockState κ G rm rp r xL xR W VL VR B ζ t) := by
  obtain ⟨hB, hWa, hVLa, hVRa, -⟩ := hE
  have hGt : MeasurableSet[Ito.nullAugmented 𝓕 P t] G := by
    have := (Ito.measurableSet_nullAugmented_of_null (𝓕 := 𝓕) hGm.compl hGc t).compl
    rwa [compl_compl] at this
  have hle := Ito.le_nullAugmented 𝓕 P t
  have h1 := (measurable_passiveL hWa rm t).mono hle le_rfl
  have h2 := (measurable_passiveL hWa rp t).mono hle le_rfl
  have h3 := (measurable_passiveR hWa r t).mono hle le_rfl
  have h4 : Measurable[Ito.nullAugmented 𝓕 P t] fun ω =>
      Girsanov.killed ζ W t ω - Real.sqrt κ * B t ω :=
    ((Girsanov.measurable_killed hWa t).sub
      ((hB.2.1 t).const_mul (Real.sqrt κ))).mono hle le_rfl
  have h5 : Measurable[Ito.nullAugmented 𝓕 P t] fun ω =>
      ((fun i => Girsanov.killed ζ (VL i) t ω, fun j => Girsanov.killed ζ (VR j) t ω) :
        (Fin nL → ℝ) × (Fin nR → ℝ)) :=
    (@Measurable.of_eval Ω (Fin nL) (fun _ => ℝ) (Ito.nullAugmented 𝓕 P t) _ _ fun i =>
      (Girsanov.measurable_killed (hVLa i) t).mono hle le_rfl).prodMk
    (@Measurable.of_eval Ω (Fin nR) (fun _ => ℝ) (Ito.nullAugmented 𝓕 P t) _ _ fun j =>
      (Girsanov.measurable_killed (hVRa j) t).mono hle le_rfl)
  exact Measurable.ite hGt (h1.prodMk (h2.prodMk (h3.prodMk (h4.prodMk h5)))) measurable_const

end AssemblyFacts

section Main

open scoped Classical

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

theorem clm_intervalIntegral {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (L : E →L[ℝ] F) {f : ℝ → E} {t : ℝ}
    (hf : IntervalIntegrable f volume 0 t) : L (∫ s in (0 : ℝ)..t, f s) = ∫ s in (0 : ℝ)..t, L (f s) :=
  (L.intervalIntegral_comp_comm hf).symm

/-- On a good path, the driver of the state is `W`. -/
theorem obsW_clockState {G : Set Ω} {ω : Ω} (hω : ω ∈ G)
    (h : IsGoodClock κ xL xR ρL ρR W VL VR B ζ ω) {rm rp r : ℝ} (hrm : rm < 0) (hrp : rp < 0)
    (hr : 0 < r) (t : ℝ≥0) :
    obsW (pathX (clockState κ G rm rp r xL xR W VL VR B ζ) (clockBrown G B) t ω) κ = W t ω := by
  simp only [obsW, pathX, clockState_of_good hω h hrm hrp hr, clockBrown, hω, ↓reduceIte]
  ring

theorem clockState_mem_stripRegion {G : Set Ω} {ω : Ω} (hω : ω ∈ G)
    (h : IsGoodClock κ xL xR ρL ρR W VL VR B ζ ω) {rm rp r : ℝ} (hrm : rm < 0) (hrprm : rp < rm)
    (hr : 0 < r) (t : ℝ≥0) :
    pathX (clockState κ G rm rp r xL xR W VL VR B ζ) (clockBrown G B) t ω ∈ stripRegion κ := by
  have hrp : rp < 0 := hrprm.trans hrm
  have hw := h.continuous_w
  have hal := h.2.2.1
  have hsep := h.2.2.2.1
  have hw0 : W 0 ω = 0 := h.1.1
  have hst := clockState_of_good hω h hrm hrp hr t
  refine ⟨?_, ?_, ?_, fun i => ?_, fun j => ?_⟩ <;>
    simp only [obsW, obsA, obsC, obsP, obsVL, obsVR, pathX, hst, clockBrown, hω, ↓reduceIte]
  · have := realFlow_lt_of_neg (w := fun t => W t ω) hw hw0 (hal rm hrm.ne) hrm t
    linarith
  · exact realFlow_lt_realFlow hw hrprm (hal rp hrp.ne) (hal rm hrm.ne) t
  · have := lt_realFlow_of_pos (w := fun t => W t ω) hw hw0 (hal r hr.ne') hr t
    linarith
  · have := (hsep t).1 i
    linarith
  · have := (hsep t).2 j
    linarith

theorem IsGoodClock.path_top {ω : Ω} (h : IsGoodClock κ xL xR ρL ρR W VL VR B ζ ω) :
    IsIntegratedSLEPath κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (B · ω)
      ⊤ := by
  rw [← h.2.1]; exact h.1

/-- **The drift of `Φ` along a good path is nonpositive.** -/
theorem itoGen_clockState_nonpos {G : Set Ω} {ω : Ω} (hω : ω ∈ G)
    (h : IsGoodClock κ xL xR ρL ρR W VL VR B ζ ω) (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (hF : IsOrderedForceWord xL xR) (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hxR : ∀ i, 0 < xR i) {rm rp : ℝ} (hrm : rm < 0) (hrprm : rp < rm)
    (hmarks : ∀ i, rp ≤ xL i ∧ xL i ≤ rm) (t : ℝ≥0) :
    Ito.itoGen (stripObs κ ((∑ j, |ρR j|) / 2))
      (pathX (clockState κ G rm rp (rightRef xR) xL xR W VL VR B ζ) (clockBrown G B) t ω)
      (stripField κ ρL ρR
        (pathX (clockState κ G rm rp (rightRef xR) xL xR W VL VR B ζ) (clockBrown G B) t ω)) ≤ 0 := by
  have hrp : rp < 0 := hrprm.trans hrm
  have hr := rightRef_pos hxR
  have hmem := clockState_mem_stripRegion hω h hrm hrprm hr t (κ := κ)
  have hw := h.continuous_w
  have hal := h.2.2.1
  have hsep := h.2.2.2.1
  have hw0 : W 0 ω = 0 := h.1.1
  have hp := h.path_top
  have hst := clockState_of_good hω h hrm hrp hr t
  have hW := obsW_clockState hω h hrm hrp hr t (κ := κ)
  refine itoGen_stripObs_nonpos hκ.le hκ4 hmem (fun i => ?_) (fun j => ?_) (fun hn => ?_)
  · simp only [obsVL, obsA, pathX, hst]
    exact IsIntegratedSLEPath.vL_le_realFlow hw hw0 (hal rm hrm.ne) hp hrm i (hmarks i).2 t
  · simp only [obsVR, obsP, pathX, hst]
    exact IsIntegratedSLEPath.realFlow_le_vR hw hw0 (hal _ hr.ne') hp hr j (rightRef_le hF j) t
  · rw [hW]
    simp only [obsVL, pathX, hst]
    obtain ⟨-, -, -, -, -, -, hanti, -⟩ := hp
    have hlt : ((t : ℝ≥0) : ℝ≥0∞) < ⊤ := ENNReal.coe_lt_top
    refine Sec4.le_sum_div_of_hasGroupEndSums hn (x := fun i => -xL i)
      (d := fun i => W t ω - VL i t ω) (fun i j hij => neg_le_neg (hF.1 hij))
      (Sec4.hasGroupEndSums_left hadm hF.1 hF.2.1) (fun i j hij => ?_) (fun i => ?_)
      (fun i j hij => ?_)
    · have := hanti t hlt hij
      show W t ω - VL i t ω ≤ W t ω - VL j t ω
      linarith
    · exact sub_pos.2 ((hsep t).1 i)
    · have hxx : xL i = xL j := by simpa using hij
      show W t ω - VL i t ω = W t ω - VL j t ω
      rw [IsIntegratedSLEPath.vL_eq_of_xL_eq h.path_top hlt hxx]

/-- Components of an integral in the state space. -/
theorem integral_obsE_components {f : ℝ → ObsE nL nR} {t : ℝ}
    (hf : IntervalIntegrable f volume 0 t) :
    (∫ s in (0 : ℝ)..t, f s).1 = (∫ s in (0 : ℝ)..t, (f s).1) ∧
    (∫ s in (0 : ℝ)..t, f s).2.1 = (∫ s in (0 : ℝ)..t, (f s).2.1) ∧
    (∫ s in (0 : ℝ)..t, f s).2.2.1 = (∫ s in (0 : ℝ)..t, (f s).2.2.1) ∧
    (∫ s in (0 : ℝ)..t, f s).2.2.2.1 = (∫ s in (0 : ℝ)..t, (f s).2.2.2.1) ∧
    (∀ i, (∫ s in (0 : ℝ)..t, f s).2.2.2.2.1 i = (∫ s in (0 : ℝ)..t, (f s).2.2.2.2.1 i)) ∧
    (∀ j, (∫ s in (0 : ℝ)..t, f s).2.2.2.2.2 j = (∫ s in (0 : ℝ)..t, (f s).2.2.2.2.2 j)) := by
  set S1 := ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ)))
  set S2 := ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ)))
  set S3 := ContinuousLinearMap.snd ℝ ℝ (ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ)))
  set S4 := ContinuousLinearMap.snd ℝ ℝ ((Fin nL → ℝ) × (Fin nR → ℝ))
  refine ⟨?_, ?_, ?_, ?_, fun i => ?_, fun j => ?_⟩
  · exact clm_intervalIntegral (ContinuousLinearMap.fst ℝ ℝ _) hf
  · exact clm_intervalIntegral ((ContinuousLinearMap.fst ℝ ℝ _).comp S1) hf
  · exact clm_intervalIntegral ((ContinuousLinearMap.fst ℝ ℝ _).comp (S2.comp S1)) hf
  · exact clm_intervalIntegral ((ContinuousLinearMap.fst ℝ ℝ _).comp (S3.comp (S2.comp S1))) hf
  · exact clm_intervalIntegral ((ContinuousLinearMap.proj i).comp ((ContinuousLinearMap.fst ℝ _ _).comp
      (S4.comp (S3.comp (S2.comp S1))))) hf
  · exact clm_intervalIntegral ((ContinuousLinearMap.proj j).comp ((ContinuousLinearMap.snd ℝ _ _).comp
      (S4.comp (S3.comp (S2.comp S1))))) hf

/-- **The state solves `Λ' = Ψ(Λ, B)`** on a good path. -/
theorem clockState_eq_integral {G : Set Ω}
    (hgood : ∀ ω ∈ G, IsGoodClock κ xL xR ρL ρR W VL VR B ζ ω) {ω : Ω} (hω : ω ∈ G)
    {rm rp r : ℝ} (hrm : rm < 0) (hrprm : rp < rm) (hr : 0 < r) (t : ℝ≥0) :
    clockState κ G rm rp r xL xR W VL VR B ζ t ω = (rm, rp, r, 0, (xL, xR)) +
      ∫ s in (0 : ℝ)..t, stripField κ ρL ρR
        (pathX (clockState κ G rm rp r xL xR W VL VR B ζ) (clockBrown G B) s.toNNReal ω) := by
  have hrp : rp < 0 := hrprm.trans hrm
  have h := hgood ω hω
  have hw := h.continuous_w
  have hal := h.2.2.1
  have hw0 : W 0 ω = 0 := h.1.1
  have hp := h.path_top
  set X := fun s : ℝ => pathX (clockState κ G rm rp r xL xR W VL VR B ζ) (clockBrown G B)
    s.toNNReal ω with hX
  have hXc : Continuous X :=
    (continuous_pathX (continuous_clockState hgood hrm hrp hr)
      (fun ω => by
        by_cases hω' : ω ∈ G
        · simp only [clockBrown, hω', ↓reduceIte]; exact (hgood ω hω').2.2.2.2.1
        · simp only [clockBrown, hω', ↓reduceIte]; exact continuous_const) ω).comp
      continuous_real_toNNReal
  have hint : IntervalIntegrable (fun s => stripField κ ρL ρR (X s)) volume 0 t := by
    refine ContinuousOn.intervalIntegrable ?_
    exact (continuousOn_stripField κ ρL ρR).comp hXc.continuousOn fun s _ =>
      clockState_mem_stripRegion hω h hrm hrprm hr s.toNNReal
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := integral_obsE_components hint
  have hXs : ∀ s : ℝ, X s = ((realFlow (W · ω) rm s.toNNReal, realFlow (W · ω) rp s.toNNReal,
      realFlow (W · ω) r s.toNNReal, W s.toNNReal ω - Real.sqrt κ * B s.toNNReal ω,
      (fun i => VL i s.toNNReal ω, fun j => VR j s.toNNReal ω)), B s.toNNReal ω) := fun s => by
    simp only [hX, pathX, clockState_of_good hω h hrm hrp hr, clockBrown, hω, ↓reduceIte]
  have hWs : ∀ s : ℝ, obsW (X s) κ = W s.toNNReal ω := fun s => by
    rw [hXs]; simp only [obsW]; ring
  rw [clockState_of_good hω h hrm hrp hr]
  show _ = (rm, rp, r, 0, (xL, xR)) + ∫ s in (0 : ℝ)..t, stripField κ ρL ρR (X s)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hgL, hgR, hweq, hvLeq, hvReq, -⟩ := hp
  have hlt : ((t : ℝ≥0) : ℝ≥0∞) < ⊤ := ENNReal.coe_lt_top
  have e1 := realFlow_eq (w := fun t => W t ω) (x := rm) hw (hal rm hrm.ne) t
  have e2 := realFlow_eq (w := fun t => W t ω) (x := rp) hw (hal rp hrp.ne) t
  have e3 := realFlow_eq (w := fun t => W t ω) (x := r) hw (hal r hr.ne') t
  have i1 : ∀ s : ℝ, (stripField κ ρL ρR (X s)).1 =
      2 / (realFlow (W · ω) rm s.toNNReal - W s.toNNReal ω) := fun s => by
    simp only [stripField]; rw [hWs]; simp only [obsA, hXs]
  have i2 : ∀ s : ℝ, (stripField κ ρL ρR (X s)).2.1 =
      2 / (realFlow (W · ω) rp s.toNNReal - W s.toNNReal ω) := fun s => by
    simp only [stripField]; rw [hWs]; simp only [obsC, hXs]
  have i3 : ∀ s : ℝ, (stripField κ ρL ρR (X s)).2.2.1 =
      2 / (realFlow (W · ω) r s.toNNReal - W s.toNNReal ω) := fun s => by
    simp only [stripField]; rw [hWs]; simp only [obsP, hXs]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext (funext fun i => ?_)
    (funext fun j => ?_)))))
  · rw [Prod.fst_add, c1]; simp only [i1]; exact e1
  · rw [Prod.snd_add, Prod.fst_add, c2]; simp only [i2]; exact e2
  · rw [Prod.snd_add, Prod.snd_add, Prod.fst_add, c3]; simp only [i3]; exact e3
  · simp only [Prod.snd_add, Prod.fst_add, c4, zero_add]
    have hwt := hweq t hlt
    have hdrift : ∀ s : ℝ, (stripField κ ρL ρR (X s)).2.2.2.1 =
        (∑ i, ρL i / (W s.toNNReal ω - VL i s.toNNReal ω)) +
          ∑ j, ρR j / (W s.toNNReal ω - VR j s.toNNReal ω) := fun s => by
      simp only [stripField, obsDrift]; rw [hWs]; simp only [obsVL, obsVR, hXs]
    simp only [hdrift]
    have hiL : ∀ i ∈ Finset.univ, IntervalIntegrable
        (fun s : ℝ => ρL i / (W s.toNNReal ω - VL i s.toNNReal ω)) volume 0 t := fun i _ =>
      ((hgL t hlt i).const_mul (ρL i)).congr fun s _ => by simp [div_eq_mul_inv]
    have hiR : ∀ j ∈ Finset.univ, IntervalIntegrable
        (fun s : ℝ => ρR j / (W s.toNNReal ω - VR j s.toNNReal ω)) volume 0 t := fun j _ =>
      ((hgR t hlt j).const_mul (ρR j)).congr fun s _ => by simp [div_eq_mul_inv]
    have hA : IntervalIntegrable (fun s : ℝ => ∑ i, ρL i / (W s.toNNReal ω - VL i s.toNNReal ω))
        volume 0 t := by
      have := IntervalIntegrable.sum Finset.univ hiL
      refine this.congr fun s _ => ?_
      simp only [Finset.sum_apply]
    have hB : IntervalIntegrable (fun s : ℝ => ∑ j, ρR j / (W s.toNNReal ω - VR j s.toNNReal ω))
        volume 0 t := by
      have := IntervalIntegrable.sum Finset.univ hiR
      refine this.congr fun s _ => ?_
      simp only [Finset.sum_apply]
    rw [intervalIntegral.integral_add hA hB, intervalIntegral.integral_finsetSum hiL,
      intervalIntegral.integral_finsetSum hiR]
    simp only at hwt
    linarith
  · simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, c5]
    have hv := hvLeq t hlt i
    simp only at hv
    rw [hv]
    congr 1
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [stripField]; rw [hWs]; simp only [obsVL, hXs]
  · simp only [Prod.snd_add, Pi.add_apply, c6]
    have hv := hvReq t hlt j
    simp only at hv
    rw [hv]
    congr 1
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [stripField]; rw [hWs]; simp only [obsVR, hXs]

/-- **The whole strip clock is finite** (`0 < κ ≤ 4`). For an integrated `SLE_κ(ρ)` evolution of an ordered
word with all marks separated from the seed and admissible side partial sums, and real points
`r₊ < r₋ < 0` with every left mark in `[r₊, r₋]`, almost surely `∫₀^∞ (1/c_t − 1/a_t)² dt < ∞`, where
`a_t = f_t(r₋)`, `c_t = f_t(r₊)` are the centred images. -/
theorem IsIntegratedSLEEvolution.ae_stripClock_bounded [IsProbabilityMeasure P] (hκ : 0 < κ)
    (hκ4 : κ ≤ 4) (hF : IsOrderedForceWord xL xR)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR) (hxL : ∀ i, xL i < 0)
    (hxR : ∀ i, 0 < xR i) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {rm rp : ℝ} (hrm : rm < 0) (hrprm : rp < rm) (hmarks : ∀ i, rp ≤ xL i ∧ xL i ≤ rm) :
    ∀ᵐ ω ∂P, ∃ S : ℝ, ∀ t : ℝ, 0 ≤ t →
      ∫ s in (0 : ℝ)..t, stripRate (fun s => fwdMap (fun s : ℝ => W s.toNNReal ω) s (rm : ℂ))
        (fun s => fwdMap (fun s : ℝ => W s.toNNReal ω) s (rp : ℂ)) s ≤ S := by
  obtain ⟨G, hGm, hGc, hgood⟩ := exists_good_clock hκ hκ4 hF hadm hxL hxR hE
  have hrp : rp < 0 := hrprm.trans hrm
  have hr := rightRef_pos hxR
  set m := (∑ j, |ρR j|) / 2 with hmdef
  have hm0 : 0 ≤ m := by positivity
  obtain ⟨hB', hB'c⟩ := Ito.isFilteredBrownianReal_modify hE.1 hGm hGc
    fun ω hω => (hgood ω hω).2.2.2.2.1
  have hG0 : MeasurableSet[Ito.nullAugmented 𝓕 P 0] G := by
    have := (Ito.measurableSet_nullAugmented_of_null (𝓕 := 𝓕) hGm.compl hGc 0).compl
    rwa [compl_compl] at this
  have hB0 : ∀ ω, clockBrown G B 0 ω = 0 := fun ω => by
    by_cases hω : ω ∈ G
    · simp only [clockBrown, hω, ↓reduceIte]; exact (hgood ω hω).2.2.2.2.2
    · simp [clockBrown, hω]
  have key := ae_bddAbove_integral_sq_partialSnd (𝓖 := Ito.nullAugmented 𝓕 P)
    (B := clockBrown G B) (U := stripRegion κ) (Φ := stripObs κ m) (Ψ := stripField κ ρL ρR)
    (Λ := clockState κ G rm rp (rightRef xR) xL xR W VL VR B ζ) (G := G)
    (p₀ := (rm, rp, rightRef xR, 0, (xL, xR)))
    hB' hB'c (isOpen_stripRegion κ) (compl_stripRegion_nonempty κ) (contDiffOn_stripObs κ m)
    (fun p hp => stripObs_nonneg hm0 hp) (continuousOn_stripField κ ρL ρR)
    (fun ω hω t => itoGen_clockState_nonpos hω (hgood ω hω) hκ hκ4 hF hadm hxR hrm hrprm hmarks t)
    (measurable_clockState hE hGm hGc) (continuous_clockState hgood hrm hrp hr) hG0 hGc
    (clockState_zero hgood hrm hrp hr) hB0
    (fun ω hω t => clockState_eq_integral hgood hω hrm hrprm hr t)
    (fun ω hω t => clockState_mem_stripRegion hω (hgood ω hω) hrm hrprm hr t)
  filter_upwards [key, (ae_iff.2 hGc : ∀ᵐ ω ∂P, ω ∈ G)] with ω hω hωG
  obtain ⟨S, hS⟩ := hω
  refine ⟨S / κ, fun t ht => ?_⟩
  have h := hS t.toNNReal
  rw [Real.coe_toNNReal _ ht] at h
  have hgω := hgood ω hωG
  have hw := hgω.continuous_w
  have hal := hgω.2.2.1
  -- the pointwise identity `stripRate = (∂_b Φ)²/κ`
  have hpt : ∀ s ∈ uIcc (0 : ℝ) t,
      stripRate (fun s => fwdMap (fun s : ℝ => W s.toNNReal ω) s (rm : ℂ))
        (fun s => fwdMap (fun s : ℝ => W s.toNNReal ω) s (rp : ℂ)) s =
      Ito.partialSnd (stripObs κ m) (pathX (clockState κ G rm rp (rightRef xR) xL xR W VL VR B ζ)
        (clockBrown G B) s.toNNReal ω) ^ 2 / κ := by
    intro s hs
    rw [uIcc_of_le ht] at hs
    have hmem := clockState_mem_stripRegion hωG hgω hrm hrprm hr s.toNNReal (κ := κ)
    rw [partialSnd_stripObs hmem, obsW_clockState hωG hgω hrm hrp hr]
    simp only [obsA, obsC, pathX, clockState_of_good hωG hgω hrm hrp hr, stripRate]
    rw [realFlow_sub_eq (w := fun t => W t ω) (x := rm) hs.1,
      realFlow_sub_eq (w := fun t => W t ω) (x := rp) hs.1]
    have ha := realFlow_lt_of_neg (w := fun t => W t ω) hw hgω.1.1 (hal rm hrm.ne) hrm s.toNNReal
    have hc := realFlow_lt_of_neg (w := fun t => W t ω) hw hgω.1.1 (hal rp hrp.ne) hrp s.toNNReal
    have hκ' : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ.le
    have h1 : W s.toNNReal ω - realFlow (fun t => W t ω) rm s.toNNReal ≠ 0 := by linarith
    have h2 : W s.toNNReal ω - realFlow (fun t => W t ω) rp s.toNNReal ≠ 0 := by linarith
    have h3 : realFlow (fun t => W t ω) rm s.toNNReal - W s.toNNReal ω ≠ 0 := by linarith
    have h4 : realFlow (fun t => W t ω) rp s.toNNReal - W s.toNNReal ω ≠ 0 := by linarith
    field_simp
    rw [hκ']
    ring
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_div]
  exact div_le_div_of_nonneg_right h hκ.le

end Main

end Zhan

end InteractingSLE
