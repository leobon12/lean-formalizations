/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedLaw2Stop

/-!
# The position of a force mark read from the driver

Packet PROVE-STAGEDLAW3. The word `β (c, θ, record)` of `StopCondLawStatement` needs the centred positions of the force
marks at the stop as a **measurable function of the record**. A right mark of an integrated evolution is the solution
of the integrated Loewner equation `d_s = x − w_s + ∫₀ˢ 2/d` with `d ≥ 0` (`d = V − W`); after it is swallowed it
moves with the right end of the hull. Here it is read from the driver alone:

* `markPos w T x = inf {f_T(q) : q ∈ ℚ, q > x, q alive at T}` (an `EReal` infimum, read in `ℝ`);
* **`markPos_eq`**: for every continuous driver `w` with `w 0 = 0` and every solution `d ≥ 0` of the integrated
  equation on `[0, T]` whose collision set `{d = 0}` is null, `markPos w T x = d T`;
* `markPosL w T x = −markPos (−w) T (−x)` and **`markPosL_eq`** for left marks (`d ≤ 0`);
* `measurable_markPos`, `measurable_markPosL`: measurability for measurable families of continuous drivers.

## The argument (deterministic)

1. **Comparison** (`le_re_of_mark`): a solution `d` from `x` stays below the real flow `U = Re f(q)` from every alive
   `q > x`: on an interval where `d > U > 0`, `(d − U)' = 2/d − 2/U < 0`, so `d − U` cannot become positive.
2. **Contraction** (`antitoneOn_re_sub_mark`): `U − d` does not increase (`2/U ≤ 2/d` off the null collision set).
   Hence `f_T(q) − d_T ≤ f_s(q) − d_s ≤ f_s(q)` for `s ≤ T`, and `f_T(q) − d_T ≤ q − x`.
3. **Infimum.** If every `q > x` is alive, take `q ↓ x`. Otherwise let `a = inf {q > x alive} > x`: pick a dead `y₁`
   just below `a` (swallowed at `σ ≤ T`, `f_s(y₁) → 0` as `s ↑ σ`) and a rational alive `q` just above `a`; by step 2
   applied to the classical solution from `y₁`, `f_s(q) ≤ f_s(y₁) + (q − y₁)`, small for `s` close to `σ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Exist

namespace StagedLaw

open QuantumZipper

/-! ### The definition -/

open scoped Classical in
/-- The term of the infimum defining `markPos`. -/
def markTerm (w : ℝ → ℝ) (T x : ℝ) (q : ℚ) : EReal :=
  if x < q ∧ ∃ u, IsForwardSol w ((q : ℝ) : ℂ) T u then (((fwdMap w T ((q : ℝ) : ℂ)).re : ℝ) : EReal) else ⊤

/-- **The position of a right mark from `x` read from the driver `w` at time `T`**: the infimum of the real forward
map over the alive rational points right of `x`. -/
def markPos (w : ℝ → ℝ) (T x : ℝ) : ℝ := (⨅ q : ℚ, markTerm w T x q).toReal

/-- **The position of a left mark from `x`**, by reflection. -/
def markPosL (w : ℝ → ℝ) (T x : ℝ) : ℝ := -markPos (fun s => -w s) T (-x)

/-! ### The real flow solves the real integrated equation -/

section Flow

variable {w : ℝ → ℝ}

/-- The real part of a forward solution from a real point solves the real integrated equation. -/
theorem re_isForwardSol_eq (hw : Continuous w) {y S : ℝ} (hS : 0 ≤ S) {v : ℝ → ℂ}
    (hv : IsForwardSol w (y : ℂ) S v) {s : ℝ} (hs : s ∈ Icc 0 S) :
    (v s).re = y - w s + ∫ r in (0 : ℝ)..s, 2 / (v r).re := by
  have him := im_isForwardSol_real hw hS hv
  have hvr : ∀ r ∈ Icc (0 : ℝ) S, v r = (((v r).re : ℝ) : ℂ) := fun r hr =>
    Complex.ext (by simp) (by simp [him r hr])
  have heq := (hv.2 s hs).2
  have hint : (∫ r in (0 : ℝ)..s, 2 / v r) = ((∫ r in (0 : ℝ)..s, 2 / (v r).re : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun r hr => ?_
    have hr' : r ∈ Icc (0 : ℝ) S := by
      rw [uIcc_of_le hs.1] at hr
      exact ⟨hr.1, hr.2.trans hs.2⟩
    rw [hvr r hr']
    push_cast
    rfl
  have := congrArg Complex.re heq
  rw [hint] at this
  simpa using this

/-- The real flow from `y > 0` is positive. -/
theorem re_pos_of_isForwardSol (hw : Continuous w) (hw0 : w 0 = 0) {y S : ℝ} (hy : 0 < y) {v : ℝ → ℂ}
    (hv : IsForwardSol w (y : ℂ) S v) {s : ℝ} (hs : s ∈ Icc 0 S) : 0 < (v s).re := by
  have h := re_fwdMap_pos hw hw0 hy hv hs
  rwa [fwdMap_eq_of_isForwardSol hw hv hs] at h

theorem continuousOn_re_of_isForwardSol {y S : ℝ} {v : ℝ → ℂ} (hv : IsForwardSol w (y : ℂ) S v) :
    ContinuousOn (fun s => (v s).re) (Icc 0 S) :=
  Complex.continuous_re.comp_continuousOn hv.1

end Flow

/-! ### Marks: solutions of the integrated equation -/

/-- **A right mark on `[0, S]`**: a nonnegative solution of `d_s = x − w_s + ∫₀ˢ 2/d` with integrable `2/d` and a null
collision set. -/
def IsMark (w : ℝ → ℝ) (S x : ℝ) (d : ℝ → ℝ) : Prop :=
  (∀ s ∈ Icc 0 S, 0 ≤ d s) ∧ (∀ s ∈ Icc 0 S, d s = x - w s + ∫ r in (0 : ℝ)..s, 2 / d r) ∧
    IntervalIntegrable (fun r => 2 / d r) volume 0 S ∧ volume {s | s ∈ Icc 0 S ∧ d s = 0} = 0

section Mark

variable {w : ℝ → ℝ} {S x : ℝ} {d : ℝ → ℝ}

theorem IsMark.zero (hd : IsMark w S x d) (hw0 : w 0 = 0) (hS : 0 ≤ S) : d 0 = x := by
  rw [hd.2.1 0 ⟨le_rfl, hS⟩, hw0, intervalIntegral.integral_same]
  ring

theorem IsMark.continuousOn (hd : IsMark w S x d) (hw : Continuous w) (hS : 0 ≤ S) :
    ContinuousOn d (Icc 0 S) := by
  have hp : ContinuousOn (fun s => ∫ r in (0 : ℝ)..s, 2 / d r) (Icc 0 S) := by
    have hI : IntegrableOn (fun r => 2 / d r) (uIcc 0 S) volume := by
      rw [uIcc_of_le hS]
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le hS).1 hd.2.2.1
    have h := intervalIntegral.continuousOn_primitive_interval (μ := volume) hI
    rwa [uIcc_of_le hS] at h
  have hc : ContinuousOn (fun s => x - w s + ∫ r in (0 : ℝ)..s, 2 / d r) (Icc 0 S) :=
    (continuousOn_const.sub hw.continuousOn).add hp
  exact hc.congr fun s hs => hd.2.1 s hs

theorem IsMark.mono (hd : IsMark w S x d) {S' : ℝ} (hS' : 0 ≤ S') (hS : S' ≤ S) : IsMark w S' x d := by
  have hsub : uIcc 0 S' ⊆ uIcc 0 S := by
    rw [uIcc_of_le hS', uIcc_of_le (hS'.trans hS)]
    exact Icc_subset_Icc_right hS
  have hnull : {s | s ∈ Icc 0 S' ∧ d s = 0} ⊆ {s | s ∈ Icc 0 S ∧ d s = 0} :=
    fun s (hs : s ∈ Icc 0 S' ∧ d s = 0) => ⟨⟨hs.1.1, hs.1.2.trans hS⟩, hs.2⟩
  exact ⟨fun s hs => hd.1 s ⟨hs.1, hs.2.trans hS⟩, fun s hs => hd.2.1 s ⟨hs.1, hs.2.trans hS⟩,
    hd.2.2.1.mono_set hsub, measure_mono_null hnull hd.2.2.2⟩

/-- **A classical solution from a positive real point is a mark.** -/
theorem isMark_of_isForwardSol (hw : Continuous w) (hw0 : w 0 = 0) {y : ℝ} (hy : 0 < y) (hS : 0 ≤ S)
    {v : ℝ → ℂ} (hv : IsForwardSol w (y : ℂ) S v) : IsMark w S y fun s => (v s).re := by
  have hpos : ∀ s ∈ Icc (0 : ℝ) S, 0 < (v s).re := fun s hs => re_pos_of_isForwardSol hw hw0 hy hv hs
  refine ⟨fun s hs => (hpos s hs).le, fun s hs => re_isForwardSol_eq hw hS hv hs, ?_, ?_⟩
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hS]
    exact continuousOn_const.div (continuousOn_re_of_isForwardSol hv) fun s hs => (hpos s hs).ne'
  · have : {s | s ∈ Icc (0 : ℝ) S ∧ (v s).re = 0} = ∅ := by
      ext s
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      exact fun hs => (hpos s hs).ne'
    rw [this, measure_empty]

/-! ### Comparison with the real flow -/

theorem IsMark.intervalIntegrable_of_le (hd : IsMark w S x d) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ S) : IntervalIntegrable (fun r => 2 / d r) volume a b := by
  refine hd.2.2.1.mono_set ?_
  rw [uIcc_of_le hab, uIcc_of_le ((ha.trans hab).trans hb)]
  exact Icc_subset_Icc ha hb

/-- **Comparison**: a mark from `x` stays below the real flow from every alive `y > x`. -/
theorem le_re_of_mark (hw : Continuous w) (hw0 : w 0 = 0) (hS : 0 ≤ S) (hd : IsMark w S x d) {y : ℝ}
    (hxy : x < y) {v : ℝ → ℂ} (hv : IsForwardSol w (y : ℂ) S v) : ∀ s ∈ Icc 0 S, d s ≤ (v s).re := by
  have hx0 : 0 ≤ x := by rw [← hd.zero hw0 hS]; exact hd.1 0 ⟨le_rfl, hS⟩
  have hy : 0 < y := lt_of_le_of_lt hx0 hxy
  have hU := isMark_of_isForwardSol hw hw0 hy hS hv
  set U : ℝ → ℝ := fun s => (v s).re with hUdef
  set e : ℝ → ℝ := fun s => d s - U s with hedef
  have hec : ContinuousOn e (Icc 0 S) := (hd.continuousOn hw hS).sub (hU.continuousOn hw hS)
  have he : ∀ s ∈ Icc 0 S, e s = (x - y) + ∫ r in (0 : ℝ)..s, (2 / d r - 2 / U r) := by
    intro s hs
    rw [intervalIntegral.integral_sub (hd.intervalIntegrable_of_le le_rfl hs.1 hs.2)
      (hU.intervalIntegrable_of_le le_rfl hs.1 hs.2)]
    simp only [hedef]
    rw [hd.2.1 s hs, hU.2.1 s hs]
    ring
  intro s₁ hs₁
  by_contra hlt
  push Not at hlt
  have he₁ : 0 < e s₁ := sub_pos.2 hlt
  set A : Set ℝ := Icc 0 s₁ ∩ e ⁻¹' Iic 0 with hAdef
  have hAc : IsClosed A :=
    (hec.mono (Icc_subset_Icc_right hs₁.2)).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have he0 : e 0 = x - y := by rw [he 0 ⟨le_rfl, hS⟩, intervalIntegral.integral_same, add_zero]
  have h0A : (0 : ℝ) ∈ A := ⟨⟨le_rfl, hs₁.1⟩, show e 0 ≤ 0 by rw [he0]; linarith⟩
  have hbdd : BddAbove A := ⟨s₁, fun r hr => hr.1.2⟩
  set s₀ := sSup A with hs₀def
  have hs₀A : s₀ ∈ A := hAc.csSup_mem ⟨0, h0A⟩ hbdd
  have hs₀s₁ : s₀ < s₁ := by
    refine lt_of_le_of_ne hs₀A.1.2 fun h => ?_
    have : e s₁ ≤ 0 := by rw [← h]; exact hs₀A.2
    linarith
  have hs₀S : s₀ ∈ Icc 0 S := ⟨hs₀A.1.1, hs₀A.1.2.trans hs₁.2⟩
  -- on `(s₀, s₁)` the mark is above the flow, so the integrand is nonpositive
  have hneg : ∀ r ∈ Ioo s₀ s₁, 2 / d r - 2 / U r ≤ 0 := by
    intro r hr
    have hrS : r ∈ Icc 0 S := ⟨hs₀A.1.1.trans hr.1.le, hr.2.le.trans hs₁.2⟩
    have her : 0 < e r := by
      by_contra hle
      push Not at hle
      have : r ≤ s₀ := le_csSup hbdd ⟨⟨hs₀A.1.1.trans hr.1.le, hr.2.le⟩, hle⟩
      linarith [hr.1]
    have hUr : 0 < U r := re_pos_of_isForwardSol hw hw0 hy hv hrS
    have hdU : U r < d r := sub_pos.1 her
    have : 2 / d r ≤ 2 / U r := div_le_div_of_nonneg_left (by norm_num) hUr hdU.le
    linarith
  have hdiff : e s₁ - e s₀ = ∫ r in s₀..s₁, (2 / d r - 2 / U r) := by
    rw [he s₁ hs₁, he s₀ hs₀S, add_sub_add_left_eq_sub,
      intervalIntegral.integral_interval_sub_left
        ((hd.intervalIntegrable_of_le le_rfl hs₁.1 hs₁.2).sub (hU.intervalIntegrable_of_le le_rfl hs₁.1 hs₁.2))
        ((hd.intervalIntegrable_of_le le_rfl hs₀S.1 hs₀S.2).sub (hU.intervalIntegrable_of_le le_rfl hs₀S.1 hs₀S.2))]
  have hle : (∫ r in s₀..s₁, (2 / d r - 2 / U r)) ≤ ∫ _ in s₀..s₁, (0 : ℝ) :=
    intervalIntegral.integral_mono_on_of_le_Ioo hs₀s₁.le
      ((hd.intervalIntegrable_of_le hs₀S.1 hs₀s₁.le hs₁.2).sub (hU.intervalIntegrable_of_le hs₀S.1 hs₀s₁.le hs₁.2))
      intervalIntegrable_const hneg
  rw [intervalIntegral.integral_zero, ← hdiff] at hle
  have h2 : e s₀ ≤ 0 := hs₀A.2
  linarith

/-- **Contraction**: the gap between the real flow from an alive `y > x` and a mark from `x` does not increase. -/
theorem antitoneOn_re_sub_mark (hw : Continuous w) (hw0 : w 0 = 0) (hS : 0 ≤ S) (hd : IsMark w S x d) {y : ℝ}
    (hxy : x < y) {v : ℝ → ℂ} (hv : IsForwardSol w (y : ℂ) S v) :
    AntitoneOn (fun s => (v s).re - d s) (Icc 0 S) := by
  have hx0 : 0 ≤ x := by rw [← hd.zero hw0 hS]; exact hd.1 0 ⟨le_rfl, hS⟩
  have hy : 0 < y := lt_of_le_of_lt hx0 hxy
  have hU := isMark_of_isForwardSol hw hw0 hy hS hv
  have hcmp := le_re_of_mark hw hw0 hS hd hxy hv
  intro a ha b hb hab
  have hrep : ∀ s ∈ Icc 0 S, (v s).re - d s = (y - x) + ∫ r in (0 : ℝ)..s, (2 / (v r).re - 2 / d r) := by
    intro s hs
    rw [intervalIntegral.integral_sub (hU.intervalIntegrable_of_le le_rfl hs.1 hs.2)
      (hd.intervalIntegrable_of_le le_rfl hs.1 hs.2)]
    have h1 : (v s).re = y - w s + ∫ r in (0 : ℝ)..s, 2 / (v r).re := hU.2.1 s hs
    rw [h1, hd.2.1 s hs]
    ring
  have hIa := (hU.intervalIntegrable_of_le le_rfl ha.1 ha.2).sub (hd.intervalIntegrable_of_le le_rfl ha.1 ha.2)
  have hIb := (hU.intervalIntegrable_of_le le_rfl hb.1 hb.2).sub (hd.intervalIntegrable_of_le le_rfl hb.1 hb.2)
  have hdiff : ((v b).re - d b) - ((v a).re - d a) = ∫ r in a..b, (2 / (v r).re - 2 / d r) := by
    rw [hrep b hb, hrep a ha, add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left hIb hIa]
  -- off the null collision set the integrand is nonpositive
  have hae : (fun r => 2 / (v r).re - 2 / d r) ≤ᵐ[volume.restrict (Icc a b)] fun _ => (0 : ℝ) := by
    have hnull : ∀ᵐ r ∂volume, ¬ (r ∈ Icc 0 S ∧ d r = 0) := by
      have := hd.2.2.2
      rw [← compl_mem_ae_iff] at this
      filter_upwards [this] with r hr using hr
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hnull] with r hr hrab
    have hrS : r ∈ Icc 0 S := ⟨ha.1.trans hrab.1, hrab.2.trans hb.2⟩
    have hdr : 0 < d r := lt_of_le_of_ne (hd.1 r hrS) fun h => hr ⟨hrS, h.symm⟩
    have : 2 / (v r).re ≤ 2 / d r := div_le_div_of_nonneg_left (by norm_num) hdr (hcmp r hrS)
    show 2 / (v r).re - 2 / d r ≤ 0
    linarith
  have hle := intervalIntegral.integral_mono_ae_restrict hab
    ((hU.intervalIntegrable_of_le ha.1 hab hb.2).sub (hd.intervalIntegrable_of_le ha.1 hab hb.2))
    intervalIntegrable_const hae
  rw [intervalIntegral.integral_zero] at hle
  show (v b).re - d b ≤ (v a).re - d a
  linarith

end Mark

/-! ### The identification -/

section Ident

variable {w : ℝ → ℝ} {T x : ℝ} {d : ℝ → ℝ}

theorem re_sol_zero {y : ℝ} (hw0 : w 0 = 0) (hT : 0 ≤ T) {v : ℝ → ℂ} (hv : IsForwardSol w (y : ℂ) T v) :
    (v 0).re = y := by
  have h := (hv.2 0 ⟨le_rfl, hT⟩).2
  rw [intervalIntegral.integral_same, add_zero, hw0] at h
  rw [h]
  simp

/-- **Approximation from above**: for every `ε > 0` some alive rational `q > x` has `f_T(q) < d_T + ε`. -/
theorem exists_rat_alive_re_lt (hw : Continuous w) (hw0 : w 0 = 0) (hT : 0 ≤ T) (hd : IsMark w T x d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℚ, x < q ∧ (∃ u, IsForwardSol w ((q : ℝ) : ℂ) T u) ∧ (fwdMap w T ((q : ℝ) : ℂ)).re < d T + ε := by
  have hx0 : 0 ≤ x := by rw [← hd.zero hw0 hT]; exact hd.1 0 ⟨le_rfl, hT⟩
  have hdT0 : d 0 = x := hd.zero hw0 hT
  have hRH := isRealHalf_fwd hw hw0 hT
  by_cases hall : ∀ y : ℝ, x < y → ∃ u, IsForwardSol w (y : ℂ) T u
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show x < x + ε by linarith)
    obtain ⟨v, hv⟩ := hall q hq1
    have h := antitoneOn_re_sub_mark hw hw0 hT hd hq1 hv ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT
    simp only at h
    rw [re_sol_zero hw0 hT hv, hdT0] at h
    refine ⟨q, hq1, ⟨v, hv⟩, ?_⟩
    rw [fwdMap_eq_of_isForwardSol hw hv ⟨hT, le_rfl⟩]
    linarith
  obtain ⟨y₀, hy₀'⟩ := not_forall.1 hall
  obtain ⟨hxy₀, hdead₀⟩ := not_imp.1 hy₀'
  have hy₀ : 0 < y₀ := lt_of_le_of_lt hx0 hxy₀
  set A : Set ℝ := {y | x < y ∧ ∃ u, IsForwardSol w (y : ℂ) T u} with hAdef
  obtain ⟨M, hM⟩ := hRH.2.2.1
  have hne : A.Nonempty := ⟨max M (x + 1), lt_of_lt_of_le (lt_add_one x) (le_max_right _ _),
    hM _ (le_max_left _ _)⟩
  have hbdd : BddBelow A := ⟨x, fun y hy => hy.1.le⟩
  set a := sInf A with hadef
  have hy₀a : y₀ ≤ a := by
    refine le_csInf hne fun y hy => ?_
    by_contra hlt
    push Not at hlt
    exact hdead₀ (hRH.2.1 y y₀ (lt_of_le_of_lt hx0 hy.1) hlt hy.2)
  -- a rational alive point just above `a`
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show a < a + ε / 4 by linarith)
  obtain ⟨y', hy'A, hy'q⟩ := (csInf_lt_iff hbdd hne).1 hq1
  have hxq : x < (q : ℝ) := hxy₀.trans_le (hy₀a.trans hq1.le)
  obtain ⟨vq, hvq⟩ := hRH.2.1 y' q (lt_of_le_of_lt hx0 hy'A.1) hy'q hy'A.2
  -- a dead point just below `a`
  set y₁ := max y₀ (a - ε / 4) with hy₁def
  have hy₁a : y₁ ≤ a := max_le hy₀a (by linarith)
  have hy₁pos : 0 < y₁ := lt_of_lt_of_le hy₀ (le_max_left _ _)
  have hay₁ : a - y₁ ≤ ε / 4 := by linarith [le_max_right y₀ (a - ε / 4)]
  have hdead₁ : ¬ ∃ u, IsForwardSol w (y₁ : ℂ) T u := by
    by_cases h : a - ε / 4 ≤ y₀
    · rw [hy₁def, max_eq_left h]; exact hdead₀
    · push Not at h
      rw [hy₁def, max_eq_right h.le]
      intro hal
      have : a ≤ a - ε / 4 := csInf_le hbdd ⟨by linarith, hal⟩
      linarith
  have hy₁q : y₁ < q := lt_of_le_of_lt hy₁a hq1
  -- its swallowing time and a time where it is close to the driver
  obtain ⟨σ, hσ, hsw⟩ := exists_realSwallowAt hw hw0 hy₁pos hT hdead₁
  have hlim := tendsto_fwdMap_of_realSwallowAt hw hw0 hy₁pos hsw
  have hev : ∀ᶠ s in 𝓝[<] σ, s ∈ Ioo 0 σ ∧ ‖fwdMap w s (y₁ : ℂ)‖ < ε / 4 := by
    refine Filter.Eventually.and (Ioo_mem_nhdsLT hσ.1 : ∀ᶠ s in 𝓝[<] σ, s ∈ Ioo 0 σ) ?_
    have := (continuous_norm.tendsto (0 : ℂ)).comp hlim
    rw [norm_zero] at this
    exact this (gt_mem_nhds (by linarith))
  obtain ⟨s, hs, hsmall⟩ := hev.exists
  have hs0 : 0 ≤ s := hs.1.le
  have hsT : s ≤ T := hs.2.le.trans hσ.2
  obtain ⟨v₁, hv₁⟩ := hsw.2.1 s ⟨hs0, hs.2⟩
  have hvqs : IsForwardSol w ((q : ℝ) : ℂ) s vq := isForwardSol_restrict hvq hs0 hsT
  have hm₁ := isMark_of_isForwardSol hw hw0 hy₁pos hs0 hv₁
  have h1 := antitoneOn_re_sub_mark hw hw0 hs0 hm₁ hy₁q hvqs ⟨le_rfl, hs0⟩ ⟨hs0, le_rfl⟩ hs0
  simp only at h1
  rw [re_sol_zero hw0 hs0 hvqs, re_sol_zero hw0 hs0 hv₁] at h1
  have h2 := antitoneOn_re_sub_mark hw hw0 hT hd hxq hvq ⟨hs0, hsT⟩ ⟨hT, le_rfl⟩ hsT
  simp only at h2
  have hds : 0 ≤ d s := hd.1 s ⟨hs0, hsT⟩
  have hv₁s : (v₁ s).re < ε / 4 := by
    rw [← fwdMap_eq_of_isForwardSol hw hv₁ ⟨hs0, le_rfl⟩]
    exact (Complex.re_le_norm _).trans_lt hsmall
  refine ⟨q, hxq, ⟨vq, hvq⟩, ?_⟩
  rw [fwdMap_eq_of_isForwardSol hw hvq ⟨hT, le_rfl⟩]
  linarith

/-- **The position of a right mark is read from the driver.** -/
theorem markPos_eq (hw : Continuous w) (hw0 : w 0 = 0) (hT : 0 ≤ T) (hd : IsMark w T x d) :
    markPos w T x = d T := by
  suffices h : (⨅ q : ℚ, markTerm w T x q) = ((d T : ℝ) : EReal) by
    unfold markPos
    rw [h, EReal.toReal_coe]
  refine le_antisymm ?_ (le_iInf fun q => ?_)
  · by_contra hlt
    push Not at hlt
    obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
    have hr : d T < r := by exact_mod_cast hr1
    obtain ⟨q, hxq, hal, hlt'⟩ := exists_rat_alive_re_lt hw hw0 hT hd (sub_pos.2 hr)
    have hq : markTerm w T x q = (((fwdMap w T ((q : ℝ) : ℂ)).re : ℝ) : EReal) := by
      unfold markTerm
      exact ite_eq_left_of_eq_true _ _ (eq_true ⟨hxq, hal⟩)
    have h1 : (⨅ q : ℚ, markTerm w T x q) ≤ (((fwdMap w T ((q : ℝ) : ℂ)).re : ℝ) : EReal) :=
      hq ▸ iInf_le _ q
    have h2 : (((fwdMap w T ((q : ℝ) : ℂ)).re : ℝ) : EReal) < (r : EReal) := by
      exact_mod_cast (show (fwdMap w T ((q : ℝ) : ℂ)).re < r by linarith)
    exact absurd (h1.trans_lt h2) (not_lt.2 hr2.le)
  · unfold markTerm
    split_ifs with h
    · obtain ⟨hxq, u, hu⟩ := h
      rw [fwdMap_eq_of_isForwardSol hw hu ⟨hT, le_rfl⟩]
      exact_mod_cast le_re_of_mark hw hw0 hT hd hxq hu T ⟨hT, le_rfl⟩
    · exact le_top

/-- **The position of a left mark is read from the driver** (`d ≤ 0`; the reflected mark is a right mark). -/
theorem markPosL_eq (hw : Continuous w) (hw0 : w 0 = 0) (hT : 0 ≤ T)
    (hd : IsMark (fun s => -w s) T (-x) fun s => -d s) : markPosL w T x = d T := by
  unfold markPosL
  rw [markPos_eq (w := fun s => -w s) hw.neg (by simp [hw0]) hT hd]
  ring

end Ident

/-! ### Measurability -/

section Meas

variable {α : Type*} [MeasurableSpace α] {W : α → ℝ → ℝ}

theorem measurable_markPos (hWc : ∀ a, Continuous (W a)) (hWm : ∀ t, Measurable fun a => W a t)
    (hW0 : ∀ a, W a 0 = 0) {τ : α → ℝ} (hτ : Measurable τ) (hτ0 : ∀ a, 0 ≤ τ a) {x : α → ℝ}
    (hx : Measurable x) : Measurable fun a => markPos (W a) (τ a) (x a) := by
  refine Measurable.ereal_toReal (Measurable.iInf fun q => ?_)
  obtain ⟨h1, h2⟩ := measurable_fwdMap_param hWc hWm hW0 hτ hτ0 (measurable_const (a := ((q : ℝ) : ℂ)))
  unfold markTerm
  refine Measurable.ite ((measurableSet_lt hx measurable_const).inter h2) ?_ measurable_const
  exact measurable_coe_real_ereal.comp (Complex.measurable_re.comp h1)

theorem measurable_markPosL (hWc : ∀ a, Continuous (W a)) (hWm : ∀ t, Measurable fun a => W a t)
    (hW0 : ∀ a, W a 0 = 0) {τ : α → ℝ} (hτ : Measurable τ) (hτ0 : ∀ a, 0 ≤ τ a) {x : α → ℝ}
    (hx : Measurable x) : Measurable fun a => markPosL (W a) (τ a) (x a) := by
  unfold markPosL
  refine (measurable_markPos (W := fun a s => -W a s) (fun a => (hWc a).neg) (fun t => (hWm t).neg)
    (fun a => by simp [hW0 a]) hτ hτ0 hx.neg).neg

end Meas

end StagedLaw

end Exist

end InteractingSLE
