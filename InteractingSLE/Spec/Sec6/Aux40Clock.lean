/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Order.Monotone

/-!
# The quotient clock of the pocket erasure (Aux. lemmas 39–41)

Specification §6.2, **Aux.** lemma 40 (`source/spec/p193-240.md` L188–L211, p. 203): "For an
explicit
quotient clock take `ℓ(t) = ∫_τ^t e^{-s} 1_I(s) ds`. It is continuous and nondecreasing. It is
constant on an interval exactly when that interval has no interior visit, since `I` is open. The
erased path is constant on every such fiber, so it factors through `ℓ` to a continuous path."
The continuity of the collapsed path is the last paragraph of the proof of **Aux.** lemma 39
(p. 202), used again for the mapped erasure in **Aux.** lemma 41 (p. 205) and in Proposition 1.6
of the ZTip-elimination note (ruling R41; `source/external/AstraIG1/ig1_ztip_elimination.txt`
L273–L315: "choose the right endpoint of each clock fibre").

This file is pure real analysis.

## Main definitions

* `erasureClock I τ t = ∫_τ^t e^{-s} 1_I(s) ds`;
* `fibreRight ℓ τ S v`: the right endpoint of the fibre `ℓ⁻¹(v)` inside `[τ, S]` (for a
  continuous nondecreasing `ℓ` and `v ∈ [ℓ τ, ℓ S]`).

## Main results

* `continuous_erasureClock`, `monotone_erasureClock`;
* `erasureClock_eq_iff`: for an open `I` and `a < b`, `ℓ a = ℓ b` iff `(a, b)` contains no point
  of `I`;
* `fibreRight_mem`, `clock_fibreRight`, `le_fibreRight`, `monotone_fibreRight`;
* `continuousOn_comp_fibreRight`: **the collapsed path is continuous**: if `X` is continuous on
  `[τ, S]` and takes equal values at the two endpoints of every nondegenerate maximal fibre of `ℓ`,
  then `v ↦ X(fibreRight v)` is continuous on `[ℓ τ, ℓ S]`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory intervalIntegral

namespace InteractingSLE.Sec6

/-! ### The clock -/

/-- The quotient clock of **Aux.** lemma 40: `ℓ(t) = ∫_τ^t e^{-s} 1_I(s) ds`. -/
def erasureClock (I : Set ℝ) (τ t : ℝ) : ℝ :=
  ∫ s in τ..t, I.indicator (fun s => Real.exp (-s)) s

section Clock

variable {I : Set ℝ} {τ : ℝ}

theorem indicator_exp_nonneg (s : ℝ) : 0 ≤ I.indicator (fun s => Real.exp (-s)) s :=
  indicator_nonneg (fun _ _ => (Real.exp_pos _).le) s

theorem intervalIntegrable_indicator_exp (hI : MeasurableSet I) (a b : ℝ) :
    IntervalIntegrable (I.indicator fun s : ℝ => Real.exp (-s)) volume a b := by
  have h := (Real.continuous_exp.comp continuous_neg).intervalIntegrable (μ := volume) a b
  exact ⟨h.1.indicator hI, h.2.indicator hI⟩

theorem continuous_erasureClock (hI : MeasurableSet I) : Continuous (erasureClock I τ) :=
  continuous_primitive (intervalIntegrable_indicator_exp hI) τ

theorem erasureClock_sub (hI : MeasurableSet I) (a b : ℝ) :
    erasureClock I τ b - erasureClock I τ a =
      ∫ s in a..b, I.indicator (fun s => Real.exp (-s)) s := by
  rw [erasureClock, erasureClock, integral_interval_sub_left
    (intervalIntegrable_indicator_exp hI τ b) (intervalIntegrable_indicator_exp hI τ a)]

theorem monotone_erasureClock (hI : MeasurableSet I) : Monotone (erasureClock I τ) := by
  intro a b hab
  have h := erasureClock_sub (τ := τ) hI a b
  have h0 : 0 ≤ ∫ s in a..b, I.indicator (fun s => Real.exp (-s)) s :=
    integral_nonneg hab fun s _ => indicator_exp_nonneg s
  linarith

/-- **The clock is constant exactly on the intervals without interior visits** (`I` open). -/
theorem erasureClock_eq_iff (hI : IsOpen I) {a b : ℝ} (hab : a < b) :
    erasureClock I τ a = erasureClock I τ b ↔ Disjoint (Ioo a b) I := by
  have hIm := hI.measurableSet
  have hsub := erasureClock_sub (τ := τ) hIm a b
  constructor
  · intro heq
    rw [Set.disjoint_left]
    intro x hx hxI
    obtain ⟨ε, hε, hεI⟩ := Metric.isOpen_iff.1 hI x hxI
    set c := max a (x - ε / 2) with hc
    set d := min b (x + ε / 2) with hd
    have hcx : c < x := max_lt hx.1 (by linarith)
    have hxd : x < d := lt_min hx.2 (by linarith)
    have hac : a ≤ c := le_max_left _ _
    have hdb : d ≤ b := min_le_left _ _
    have hcd : c ≤ d := (hcx.trans hxd).le
    have hpos : 0 < ∫ s in c..d, I.indicator (fun s => Real.exp (-s)) s := by
      have heqOn : EqOn (I.indicator fun s : ℝ => Real.exp (-s)) (fun s => Real.exp (-s))
          (Icc c d) := by
        intro s hs
        refine indicator_of_mem (hεI ?_) _
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        have h1 : x - ε / 2 ≤ c := le_max_right _ _
        have h2 : d ≤ x + ε / 2 := min_le_right _ _
        constructor <;> linarith [hs.1, hs.2]
      rw [integral_congr (by rwa [uIcc_of_le hcd])]
      exact intervalIntegral_pos_of_pos_on
        ((Real.continuous_exp.comp continuous_neg).intervalIntegrable c d)
        (fun s _ => Real.exp_pos _) (hcx.trans hxd)
    have hii := intervalIntegrable_indicator_exp hIm
    have hsplit := (integral_add_adjacent_intervals (hii a c) (hii c d)).symm
    have hsplit2 := (integral_add_adjacent_intervals (hii a d) (hii d b)).symm
    have h1 : 0 ≤ ∫ s in a..c, I.indicator (fun s => Real.exp (-s)) s :=
      integral_nonneg hac fun s _ => indicator_exp_nonneg s
    have h2 : 0 ≤ ∫ s in d..b, I.indicator (fun s => Real.exp (-s)) s :=
      integral_nonneg hdb fun s _ => indicator_exp_nonneg s
    linarith
  · intro hdis
    have hzero : ∫ s in a..b, I.indicator (fun s => Real.exp (-s)) s = 0 := by
      rw [integral_of_le hab.le]
      refine setIntegral_eq_zero_of_ae_eq_zero ?_
      filter_upwards [Measure.ae_ne volume b] with s hsb hs
      exact indicator_of_notMem (fun hsI =>
        Set.disjoint_left.1 hdis ⟨hs.1, lt_of_le_of_ne hs.2 hsb⟩ hsI) _
    linarith

end Clock

/-! ### Right endpoints of fibres and the collapsed path -/

/-- The **right endpoint of the fibre** `ℓ⁻¹(v)` inside `[τ, S]`: `sup {t ∈ [τ, S] : ℓ t ≤ v}`
(with `v` raised to `ℓ τ`, so that the set is nonempty for every `v`). -/
def fibreRight (ℓ : ℝ → ℝ) (τ S v : ℝ) : ℝ := sSup {t ∈ Icc τ S | ℓ t ≤ max v (ℓ τ)}

section Fibre

variable {ℓ : ℝ → ℝ} {τ S : ℝ}

theorem fibreRight_set_nonempty (hτS : τ ≤ S) (v : ℝ) :
    {t ∈ Icc τ S | ℓ t ≤ max v (ℓ τ)}.Nonempty :=
  ⟨τ, ⟨le_rfl, hτS⟩, le_max_right _ _⟩

theorem fibreRight_set_bddAbove (v : ℝ) : BddAbove {t ∈ Icc τ S | ℓ t ≤ max v (ℓ τ)} :=
  ⟨S, fun _ ht => ht.1.2⟩

theorem fibreRight_set_isClosed (hℓ : Continuous ℓ) (v : ℝ) :
    IsClosed {t ∈ Icc τ S | ℓ t ≤ max v (ℓ τ)} :=
  isClosed_Icc.inter (isClosed_le hℓ continuous_const)

theorem fibreRight_mem_set (hℓ : Continuous ℓ) (hτS : τ ≤ S) (v : ℝ) :
    fibreRight ℓ τ S v ∈ {t ∈ Icc τ S | ℓ t ≤ max v (ℓ τ)} :=
  (fibreRight_set_isClosed hℓ v).csSup_mem (fibreRight_set_nonempty hτS v)
    (fibreRight_set_bddAbove v)

theorem fibreRight_mem (hℓ : Continuous ℓ) (hτS : τ ≤ S) (v : ℝ) :
    fibreRight ℓ τ S v ∈ Icc τ S :=
  (fibreRight_mem_set hℓ hτS v).1

theorem le_fibreRight {v t : ℝ} (ht : t ∈ Icc τ S) (hℓt : ℓ t ≤ max v (ℓ τ)) :
    t ≤ fibreRight ℓ τ S v :=
  le_csSup (fibreRight_set_bddAbove v) ⟨ht, hℓt⟩

theorem monotone_fibreRight (hτS : τ ≤ S) : Monotone (fibreRight ℓ τ S) := by
  intro v w hvw
  refine csSup_le_csSup (fibreRight_set_bddAbove w) (fibreRight_set_nonempty hτS v) ?_
  intro t ht
  exact ⟨ht.1, ht.2.trans (max_le_max hvw le_rfl)⟩

/-- On `[ℓ τ, ℓ S]`, `fibreRight v` lies in the fibre of `v`. -/
theorem clock_fibreRight (hℓ : Continuous ℓ) (hτS : τ ≤ S) {v : ℝ}
    (hv : v ∈ Icc (ℓ τ) (ℓ S)) : ℓ (fibreRight ℓ τ S v) = v := by
  have hm := fibreRight_mem_set hℓ hτS v
  rw [max_eq_left hv.1] at hm
  refine le_antisymm hm.2 ?_
  by_contra hlt
  push Not at hlt
  -- intermediate value: some `t ∈ [fibreRight v, S]` has `ℓ t = v`, and then `t ≤ fibreRight v`
  have hcS : fibreRight ℓ τ S v ≤ S := hm.1.2
  obtain ⟨t, ht, hℓt⟩ := intermediate_value_Icc hcS hℓ.continuousOn ⟨hlt.le, hv.2⟩
  have htle : t ≤ fibreRight ℓ τ S v :=
    le_fibreRight ⟨hm.1.1.trans ht.1, ht.2⟩ (by rw [hℓt, max_eq_left hv.1])
  have : t = fibreRight ℓ τ S v := le_antisymm htle ht.1
  rw [this] at hℓt
  exact (ne_of_lt hlt) hℓt

theorem fibreRight_clock {t : ℝ} (ht : t ∈ Icc τ S) : t ≤ fibreRight ℓ τ S (ℓ t) :=
  le_fibreRight ht (le_max_left _ _)

/-- **The collapsed path is continuous.** Let `ℓ` be continuous and nondecreasing and let `X` be
continuous on `[τ, S]`. Suppose `X` takes the same value at the two endpoints of every
nondegenerate maximal fibre `[a, b]` of `ℓ` in `[τ, S]` ((GC1), (RG2)). Then
`v ↦ X(fibreRight v)` is continuous on `[ℓ τ, ℓ S]`. -/
theorem continuousOn_comp_fibreRight {E : Type*} [TopologicalSpace E] {X : ℝ → E}
    (hℓ : Continuous ℓ) (hℓm : Monotone ℓ) (hτS : τ ≤ S) (hX : ContinuousOn X (Icc τ S))
    (hfib : ∀ a ∈ Icc τ S, ∀ b ∈ Icc τ S, a < b → ℓ a = ℓ b →
      (∀ t ∈ Icc τ S, ℓ t = ℓ a → t ∈ Icc a b) → X a = X b) :
    ContinuousOn (fun v => X (fibreRight ℓ τ S v)) (Icc (ℓ τ) (ℓ S)) := by
  set g := fibreRight ℓ τ S with hg
  have hgm : Monotone g := monotone_fibreRight hτS
  have hgmem : ∀ v, g v ∈ Icc τ S := fibreRight_mem hℓ hτS
  intro v hv
  have hXc : ∀ c ∈ Icc τ S, Tendsto X (𝓝[Icc τ S] c) (𝓝 (X c)) := fun c hc => hX c hc
  -- right limits: `g` is right-continuous at `v`
  have hright : Tendsto g (𝓝[>] v) (𝓝 (g v)) := by
    have hlim := Monotone.tendsto_nhdsGT hgm v
    set c := sInf (g '' Ioi v) with hc
    have hcv : g v ≤ c := le_csInf (Set.Nonempty.image g nonempty_Ioi)
      (by rintro _ ⟨w, hw, rfl⟩; exact hgm (le_of_lt hw))
    -- `ℓ c = v` by continuity, so `c ≤ g v`
    have hcmem : c ∈ Icc τ S := (isClosed_Icc.mem_of_tendsto hlim
      (Eventually.of_forall fun w => hgmem w))
    have hℓlim : Tendsto (fun w => ℓ (g w)) (𝓝[>] v) (𝓝 (ℓ c)) :=
      (hℓ.tendsto c).comp hlim
    have hℓc : ℓ c ≤ max v (ℓ τ) := by
      have hle : ∀ᶠ w in 𝓝[>] v, ℓ (g w) ≤ max w (ℓ τ) :=
        Eventually.of_forall fun w => (fibreRight_mem_set hℓ hτS w).2
      have h2 : Tendsto (fun w => max w (ℓ τ)) (𝓝[>] v) (𝓝 (max v (ℓ τ))) :=
        ((continuous_id.max continuous_const).tendsto v).mono_left nhdsWithin_le_nhds
      exact le_of_tendsto_of_tendsto hℓlim h2 hle
    have hcg : c ≤ g v := le_fibreRight hcmem hℓc
    rw [le_antisymm hcg hcv] at hlim
    exact hlim
  -- left limits: `g` tends to the left endpoint of the fibre of `v`
  have hleft : Tendsto (fun w => X (g w)) (𝓝[<] v) (𝓝 (X (g v))) := by
    by_cases hvτ : v ≤ ℓ τ
    · -- left of `ℓ τ` the function is constant
      have hconst : ∀ w ≤ ℓ τ, g w = g (ℓ τ) := by
        intro w hw
        simp only [hg, fibreRight, max_eq_right hw, max_self]
      have hvτ' : v = ℓ τ := le_antisymm hvτ hv.1
      refine tendsto_nhds_of_eventually_eq ?_
      filter_upwards [self_mem_nhdsWithin] with w hw
      rw [hconst w (hvτ' ▸ (le_of_lt hw)), hconst v hvτ]
    push Not at hvτ
    have hlim := Monotone.tendsto_nhdsLT hgm v
    set c := sSup (g '' Iio v) with hc
    have hcmem : c ∈ Icc τ S := isClosed_Icc.mem_of_tendsto hlim
      (Eventually.of_forall fun w => hgmem w)
    have hcv : c ≤ g v := csSup_le (Set.Nonempty.image g nonempty_Iio)
      (by rintro _ ⟨w, hw, rfl⟩; exact hgm (le_of_lt hw))
    -- `ℓ c = v`
    have hℓlim : Tendsto (fun w => ℓ (g w)) (𝓝[<] v) (𝓝 (ℓ c)) := (hℓ.tendsto c).comp hlim
    have hev : ∀ᶠ w in 𝓝[<] v, ℓ (g w) = w := by
      have : ∀ᶠ w in 𝓝[<] v, ℓ τ < w := by
        exact (eventually_gt_nhds hvτ).filter_mono nhdsWithin_le_nhds
      filter_upwards [this, self_mem_nhdsWithin] with w hw hwv
      exact clock_fibreRight hℓ hτS ⟨hw.le, (le_of_lt hwv).trans hv.2⟩
    have hℓc : ℓ c = v := by
      have h2 : Tendsto (fun w => ℓ (g w)) (𝓝[<] v) (𝓝 v) :=
        (tendsto_congr' hev).2 (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
      exact tendsto_nhds_unique hℓlim h2
    have hℓgv : ℓ (g v) = v := clock_fibreRight hℓ hτS hv
    -- `c` is the left endpoint of the fibre of `v`
    have hcmin : ∀ t ∈ Icc τ S, ℓ t = v → c ≤ t := by
      intro t ht hℓt
      refine csSup_le (Set.Nonempty.image g nonempty_Iio) ?_
      rintro _ ⟨w, hw, rfl⟩
      by_contra hlt
      push Not at hlt
      have h1 : ℓ t ≤ ℓ (g w) := hℓm hlt.le
      have h2 : ℓ (g w) ≤ max w (ℓ τ) := (fibreRight_mem_set hℓ hτS w).2
      have h3 : max w (ℓ τ) < v := max_lt hw hvτ
      linarith
    have hXeq : X c = X (g v) := by
      rcases eq_or_lt_of_le hcv with h | h
      · rw [h]
      · refine hfib c hcmem (g v) (hgmem v) h (by rw [hℓc, hℓgv]) fun t ht hℓt => ?_
        rw [hℓc] at hℓt
        exact ⟨hcmin t ht hℓt, le_fibreRight ht (by rw [hℓt]; exact le_max_left _ _)⟩
    rw [← hXeq]
    exact (hXc c hcmem).comp (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall
      fun w => hgmem w⟩)
  -- assemble
  have hright' : Tendsto (fun w => X (g w)) (𝓝[>] v) (𝓝 (X (g v))) :=
    (hXc (g v) (hgmem v)).comp (tendsto_nhdsWithin_iff.2 ⟨hright, Eventually.of_forall
      fun w => hgmem w⟩)
  have hboth : Tendsto (fun w => X (g w)) (𝓝[≠] v) (𝓝 (X (g v))) := by
    rw [← nhdsLT_sup_nhdsGT]
    exact hleft.sup hright'
  have hfull : Tendsto (fun w => X (g w)) (𝓝 v) (𝓝 (X (g v))) := by
    rw [← nhdsNE_sup_pure v]
    exact hboth.sup (tendsto_pure_nhds _ _)
  exact hfull.mono_left nhdsWithin_le_nhds

end Fibre

end InteractingSLE.Sec6
