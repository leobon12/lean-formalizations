/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.RestartGenReflect

/-!
# The switched-wall restart law: deterministic steps

Packet PROVE-SWITCHED (Lemma 5.7 with `ℓ = 2`, spec p. 138: "We apply a conformal transformation `ψ` … which sends
`η(σ)` to `0` … This implies that `η′` almost surely exits `𝒮 ∖ η([0, σ])` at `η(σ)`"). Three pathwise facts used by
the assembly `RestartSwMain`:

* **`isFirstHitQ_of_forall_rat`** (all real times from the rational ones): if the counterflow first contacts the flow
  path at `γ(r)` for every positive rational `r`, it does so at every positive real time. The first-contact times are
  antitone in the flow time (reverse chronological order), and the first contact at `q` is the supremum of those at the
  rationals `r > q`.
* **`isFirstHitQ_of_chart`** (the pull-back through the chart of the remaining domain): if the wall `R` is, after its
  switch time `t₀`, the image `F(β₂(s))` of a path `β₂` in `ℍ` under a map `F` injective on `ℍ`, the wall prefix
  `R((0, t₀])` lies outside `F(ℍ)`, and the physical counterflow, time-changed by a continuous increasing clock `ℓ` from
  `0`, is `F` of the image counterflow at positive times, then the first contact of the image counterflow with
  `β₂((0, q′])` at `β₂(q′)` gives the first contact of the physical counterflow with `R((0, t₀ + q′])` at `R(t₀ + q′)`.
* **`isHeightBounded44_of_cond44`**: (4.4) for the angle-`θ` flow-line word of `b` gives the (4.4) heights of `b` at
  `θ` (the converse of `Sec7.StripDet.cond44_flowLine_of_heights`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Function
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)

namespace InteractingSLE.Sec5.RestartSw

open WangWu (negInv negInv_negInv')
open Prop411Q (IsFirstHitQ negInv_eq_iff)
open Sec7.StripHeights44 (IsHeightBounded44)
open Sec7.Lemma71I (realPath)

/-! ### All real times from the rational ones -/

section Real

variable {γ β : ℝ → ℂ}

/-- **Reverse chronological order of the first contacts**: for `0 < r′ < r`, the first contact with `γ((0, r′])`
does not happen before the first contact with `γ((0, r])`. -/
theorem le_of_isFirstHitQ {r r' u u' : ℝ} (hr' : 0 < r') (hrr : r' ≤ r)
    (hbefore : ∀ v ∈ Ioo 0 u, negInv (β v) ∉ γ '' Ioc 0 r) (hu' : 0 < u') (he : negInv (β u') = γ r') :
    u ≤ u' := by
  by_contra hlt
  exact hbefore u' ⟨hu', lt_of_not_ge hlt⟩ ⟨r', ⟨hr', hrr⟩, he.symm⟩

/-- **The first contact at every positive real time from the rational times**: if the counterflow `R ∘ β` (`β`
continuous) first contacts `γ((0, r])` at `γ(r)` for every positive rational `r`, and `γ` is continuous and nonzero at
positive times, then it first contacts `γ((0, q])` at `γ(q)` for every real `q > 0`. -/
theorem isFirstHitQ_of_forall_rat (hγ : ContinuousOn γ (Ioi 0)) (hγ0 : ∀ s, 0 < s → γ s ≠ 0) (hβ : Continuous β)
    (h : ∀ r : ℚ, 0 < r → IsFirstHitQ γ β r) {q : ℝ} (hq : 0 < q) : IsFirstHitQ γ β q := by
  classical
  -- the first-contact time at a rational time above `q`
  have hex : ∀ r : ℚ, ∃ u : ℝ, q < r → 0 < u ∧ negInv (β u) = γ r ∧ ∀ v ∈ Ioo 0 u, negInv (β v) ∉ γ '' Ioc 0 r :=
    fun r => by
      by_cases hr : q < r
      · obtain ⟨u, hu⟩ := h r (by exact_mod_cast hq.trans hr)
        exact ⟨u, fun _ => hu⟩
      · exact ⟨0, fun h' => absurd h' hr⟩
  choose U hU using hex
  -- a rational time below `q` bounds every first-contact time above `q`
  obtain ⟨r₀, hr₀0, hr₀q⟩ := exists_rat_btwn hq
  obtain ⟨u₀, hu₀0, hu₀, -⟩ := h r₀ (by exact_mod_cast hr₀0)
  have hbdd : ∀ r : ℚ, q < r → U r ≤ u₀ := fun r hr =>
    le_of_isFirstHitQ hr₀0 (hr₀q.trans hr).le (hU r hr).2.2 hu₀0 hu₀
  set S : Set ℝ := U '' {r : ℚ | q < (r : ℝ)} with hSdef
  have hSne : S.Nonempty := by
    obtain ⟨r₁, hr₁⟩ := exists_rat_gt q
    exact ⟨U r₁, r₁, hr₁, rfl⟩
  have hSbdd : BddAbove S := ⟨u₀, by rintro _ ⟨r, hr, rfl⟩; exact hbdd r hr⟩
  set u := sSup S with hudef
  have hle : ∀ r : ℚ, q < r → U r ≤ u := fun r hr => le_csSup hSbdd ⟨r, hr, rfl⟩
  obtain ⟨r₁, hr₁⟩ := exists_rat_gt q
  have hu0 : 0 < u := ((hU r₁ hr₁).1).trans_le (hle r₁ hr₁)
  -- a sequence of rationals decreasing to `q`
  have hseq : ∀ n : ℕ, ∃ r : ℚ, q < r ∧ (r : ℝ) < q + 1 / (n + 1) := fun n =>
    exists_rat_btwn (lt_add_of_pos_right q (by positivity))
  choose r hr using hseq
  have hrq : Tendsto (fun n => (r n : ℝ)) atTop (𝓝[>] q) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => (hr n).1⟩
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => (hr n).1.le)
      (fun n => (hr n).2.le)
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add q
  -- the first-contact times converge to `u`
  have hUu : Tendsto (fun n => U (r n)) atTop (𝓝 u) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨_, ⟨r', hr', rfl⟩, hr'u⟩ := exists_lt_of_lt_csSup hSne (show u - ε < u by linarith)
    have hev : ∀ᶠ n in atTop, (r n : ℝ) < r' :=
      (tendsto_nhdsWithin_iff.1 hrq).1.eventually (gt_mem_nhds hr')
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine ⟨N, fun n hn => ?_⟩
    have h1 : U r' ≤ U (r n) :=
      le_of_isFirstHitQ (hq.trans (hr n).1) (hN n hn).le (hU r' hr').2.2 (hU (r n) (hr n).1).1
        (hU (r n) (hr n).1).2.1
    have h2 := hle (r n) (hr n).1
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  -- the limit point is the contact point
  have hγq : γ q ≠ 0 := hγ0 q hq
  have hlim1 : Tendsto (fun n => β (U (r n))) atTop (𝓝 (β u)) := (hβ.tendsto u).comp hUu
  have hlim2 : Tendsto (fun n => β (U (r n))) atTop (𝓝 (negInv (γ q))) := by
    have hγt : Tendsto (fun n => γ (r n)) atTop (𝓝 (γ q)) :=
      ((hγ.continuousAt (Ioi_mem_nhds hq)).continuousWithinAt.tendsto).comp
        (tendsto_nhdsWithin_mono_right (fun x hx => hx) hrq)
    have := ((WangWu.continuousAt_negInv hγq).tendsto).comp hγt
    refine this.congr fun n => ?_
    simp only [comp_apply]
    exact (negInv_eq_iff.1 (hU (r n) (hr n).1).2.1).symm
  have hβu : β u = negInv (γ q) := tendsto_nhds_unique hlim1 hlim2
  refine ⟨u, hu0, negInv_eq_iff.2 hβu, fun v hv hmem => ?_⟩
  obtain ⟨_, ⟨r', hr', rfl⟩, hvr'⟩ := exists_lt_of_lt_csSup hSne hv.2
  obtain ⟨s, hs, hse⟩ := hmem
  exact (hU r' hr').2.2 v ⟨hv.1, hvr'⟩ ⟨s, ⟨hs.1, hs.2.trans (le_of_lt hr')⟩, hse⟩

end Real

/-! ### The pull-back through the chart of the remaining domain -/

section Chart

variable {R β₂ η η₂ : ℝ≥0 → ℂ} {F : ℂ → ℂ} {t₀ : ℝ≥0} {ℓ : ℝ≥0 → ℝ≥0}

/-- **The first contact after the switch, from the first contact in the chart of the remaining domain.** Let the wall
`R` be `F ∘ β₂` after its switch time `t₀` (`F` injective on `ℍ`, `β₂` in `ℍ` at positive times) with its prefix
`R((0, t₀])` outside `F(ℍ)`, and let the physical counterflow at the times `ℓ(u)` (a continuous increasing clock from
`0`) be `F` of the image counterflow at time `u > 0`, which lies in `ℍ`. Then the image counterflow's first contact
with `β₂((0, q′])` at `β₂(q′)` is the physical counterflow's first contact with `R((0, t₀ + q′])` at `R(t₀ + q′)`. -/
theorem isFirstHitQ_of_chart (hF : InjOn F H) (hjoin : ∀ s : ℝ≥0, 0 < s → R (t₀ + s) = F (β₂ s))
    (hβ₂ : ∀ s : ℝ≥0, 0 < s → β₂ s ∈ H) (hpre : ∀ t : ℝ≥0, 0 < t → t ≤ t₀ → R t ∉ F '' H)
    (hℓc : Continuous ℓ) (hℓm : StrictMono ℓ) (hℓ0 : ℓ 0 = 0)
    (hrel : ∀ u : ℝ≥0, 0 < u → negInv (η₂ u) ∈ H ∧ negInv (η (ℓ u)) = F (negInv (η₂ u)))
    {q' : ℝ} (hq' : 0 < q') (h : IsFirstHitQ (realPath β₂) (fun s : ℝ => η₂ s.toNNReal) q') :
    IsFirstHitQ (realPath R) (fun s : ℝ => η s.toNNReal) ((t₀ : ℝ) + q') := by
  obtain ⟨u, hu0, hu, hbefore⟩ := h
  have hu0' : 0 < u.toNNReal := Real.toNNReal_pos.2 hu0
  have hq0' : 0 < q'.toNNReal := Real.toNNReal_pos.2 hq'
  have hsum : ((t₀ : ℝ) + q').toNNReal = t₀ + q'.toNNReal := by
    apply NNReal.eq
    rw [NNReal.coe_add, Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ hq'.le]
  have hℓpos : 0 < ℓ u.toNNReal := by rw [← hℓ0]; exact hℓm hu0'
  refine ⟨(ℓ u.toNNReal : ℝ), hℓpos, ?_, fun v hv hmem => ?_⟩
  · simp only [Real.toNNReal_coe, realPath, hsum]
    rw [(hrel _ hu0').2, hjoin _ hq0']
    exact congrArg F hu
  · -- the time `v` is the clock of some image time `w ∈ (0, u)`
    have hv0 : 0 < v.toNNReal := Real.toNNReal_pos.2 hv.1
    have hvu : v.toNNReal < ℓ u.toNNReal := by
      rw [← Real.toNNReal_coe (r := ℓ u.toNNReal)]
      exact (Real.toNNReal_lt_toNNReal_iff hℓpos).2 hv.2
    obtain ⟨w, hw, hwv⟩ := intermediate_value_Icc (show (0 : ℝ≥0) ≤ u.toNNReal from hu0'.le)
      hℓc.continuousOn ⟨by rw [hℓ0]; exact hv0.le, hvu.le⟩
    have hw0 : 0 < w := by
      rcases eq_or_lt_of_le (show (0 : ℝ≥0) ≤ w from hw.1) with h0 | h0
      · rw [← h0, hℓ0] at hwv
        exact absurd hwv.symm hv0.ne'
      · exact h0
    have hwu : w < u.toNNReal := by
      rcases eq_or_lt_of_le hw.2 with he | he
      · rw [he] at hwv
        exact absurd hwv hvu.ne'
      · exact he
    obtain ⟨hH, hrelw⟩ := hrel w hw0
    obtain ⟨s, hs, hse⟩ := hmem
    simp only [realPath] at hse
    have hv' : η v.toNNReal = η (ℓ w) := by rw [hwv]
    rw [hv', hrelw] at hse
    by_cases hst : s.toNNReal ≤ t₀
    · exact hpre s.toNNReal (Real.toNNReal_pos.2 hs.1) hst ⟨_, hH, hse.symm⟩
    · -- after the switch: injectivity of `F` on `ℍ`
      rw [not_le] at hst
      set σ : ℝ≥0 := s.toNNReal - t₀ with hσ
      have hσ0 : 0 < σ := tsub_pos_of_lt hst
      have hsσ : s.toNNReal = t₀ + σ := (add_tsub_cancel_of_le hst.le).symm
      rw [hsσ, hjoin σ hσ0] at hse
      have heq : β₂ σ = negInv (η₂ w) := hF (hβ₂ σ hσ0) hH hse
      have hσq : (σ : ℝ) ≤ q' := by
        have h1 : (s.toNNReal : ℝ) ≤ t₀ + q' := by
          rw [Real.coe_toNNReal _ hs.1.le]; exact hs.2
        have h2 : (s.toNNReal : ℝ) = t₀ + σ := by rw [hsσ, NNReal.coe_add]
        linarith
      refine hbefore (w : ℝ) ⟨hw0, ?_⟩ ⟨(σ : ℝ), ⟨hσ0, hσq⟩, ?_⟩
      · rw [← Real.toNNReal_lt_toNNReal_iff hu0, Real.toNNReal_coe]; exact hwu
      · simp only [realPath, Real.toNNReal_coe]
        exact heq

end Chart

/-! ### (4.4) heights from (4.4) for the flow-line word -/

/-- **The (4.4) heights of `b` at `θ` from (4.4) for its angle-`θ` flow-line word** from `0`: off the jumps, the force
boundary data of the word is `b + θχ` (`Exist.forceBoundaryData_flowLine_seed`), which (4.4) bounds by `−λ + πχ` on the
left and by `λ` from below on the right (`Sec4.forceBoundaryData_bounds_of_cond44`). -/
theorem isHeightBounded44_of_cond44 {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) {θ : ℝ}
    (h44 : Sec4.Cond44 κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)) : IsHeightBounded44 κ b J θ := by
  obtain ⟨hL, hR⟩ := Sec4.forceBoundaryData_bounds_of_cond44 hκ hκ4 (Theorem15.isOrderedForceWord_flowLine b J 0) h44
  refine ⟨fun y hy hyJ => ?_, fun y hy hyJ => ?_⟩
  · have e := Exist.forceBoundaryData_flowLine_seed hκ hb 0 θ hy.ne (by rwa [add_zero])
    rw [add_zero] at e
    rw [← e]
    exact hL y hy
  · have e := Exist.forceBoundaryData_flowLine_seed hκ hb 0 θ hy.ne' (by rwa [add_zero])
    rw [add_zero] at e
    rw [← e]
    exact hR y hy.le

end InteractingSLE.Sec5.RestartSw
