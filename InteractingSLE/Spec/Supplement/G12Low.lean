/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G12LowAe
import InteractingSLE.Spec.Supplement.G12LowPath
import InteractingSLE.Spec.Supplement.G12RemBridge
import InteractingSLE.Spec.Supplement.GB7aCmp

/-!
# Lemma G12 when the weight before the point is `≤ −2` (the G4 / Aux. lemma 132 case)

Packet PROVE-G12C. Supplement §7.9, Lemma G12 (p. 504), the case left open by PROVE-G12B: a right point `y > 0` with a
right mark strictly below it, cumulative weight `S' = Σ_{x_i < y} ρ_i ≤ −2` strictly before `y` and
`S_y = Σ_{x_i ≤ y} ρ_i > κ/2 − 4` up to it. The source proves it by Lemma G4 (the first new contact cannot be an
outward jump above its marked-point threshold) and the first-swallow table of Aux. lemma 132. Here:

* *(pathwise, `G12LowPath.lean`)* at the first visit `t₀` of `y` the inner gap `V^k − W` is positive before `t₀`, and
  after a rational restart time the marks stay off the driver with bounded drift energy to the two-mark reference;
* *(probabilistic, `G12LowLyap` … `G12LowAe`)* for the reference (weight `S'` at the last mark `x_k` below `y`, the
  group weight `ρ_Y` at `y`), the Lyapunov function `h = −1/cosh(α(Y − Y₀))` of `Y = log(o/e)` has generator
  `≥ c·β o²` (Aux. lemma 132's gap equation (SS5)–(SS6), `b(−∞) = S' − c < 0`, `b(+∞) = S_y − d > 0`); the drift
  difference of the actual word is absorbed by its energy, so the two-mark budget `∫ β` is almost surely finite;
* *(deterministic, `G12Det.trace_ne_of_budget_lt`)* a finite budget forbids the visit.

Main results:

* `ae_trace_ne_right_low_mark`, `ae_trace_ne_right_low`, `ae_trace_ne_left_low`: Lemma G12 in this case (marks and
  passive points, both sides);
* `G12Remainder3Statement` (named input, **not proved**): only the case without any mark strictly between the seed
  and `y` on its side remains; `g12EvolStatement_of_remainder3 : G12Remainder3Statement → G12EvolStatement`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Supp7

namespace G12Low

open G12 (rhoY)

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- The two-mark budget is integrable on `[0, s]` while both gaps are positive. -/
theorem intervalIntegrable_pairBudget {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {ζ : ℝ≥0∞} (hF : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {k j₀ : Fin nR} {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) < ζ) (ho : ∀ r ≤ s, w r < vR k r) (hu : ∀ r ≤ s, w r < vR j₀ r) :
    IntervalIntegrable (G12.pairBudget w (vR k) (vR j₀)) volume 0 s := by
  have hmaps : MapsTo Real.toNNReal (Icc 0 (s : ℝ)) {r : ℝ≥0 | (r : ℝ≥0∞) < ζ} := fun r hr =>
    Sec2.toNNReal_lt_of_mem_Icc hs hr
  have hcw : ContinuousOn (fun r : ℝ => w r.toNNReal) (Icc 0 (s : ℝ)) :=
    hF.continuousOn_w.comp continuous_real_toNNReal.continuousOn hmaps
  have hcv : ∀ j, ContinuousOn (fun r : ℝ => vR j r.toNNReal) (Icc 0 (s : ℝ)) := fun j =>
    (hF.continuousOn_vR j).comp continuous_real_toNNReal.continuousOn hmaps
  have hle : ∀ r ∈ Icc (0 : ℝ) s, r.toNNReal ≤ s := fun r hr => Sec2.toNNReal_le_of_mem_Icc hr
  have hc : ContinuousOn (fun r : ℝ => 4 * (vR j₀ r.toNNReal - vR k r.toNNReal) /
      ((vR j₀ r.toNNReal - w r.toNNReal) ^ 2 * (vR k r.toNNReal - w r.toNNReal)) +
        4 * (vR j₀ r.toNNReal - vR k r.toNNReal) / (vR j₀ r.toNNReal - w r.toNNReal) ^ 3) (Icc 0 (s : ℝ)) :=
    ContinuousOn.add (ContinuousOn.div (continuousOn_const.mul ((hcv j₀).sub (hcv k)))
      ((((hcv j₀).sub hcw).pow 2).mul ((hcv k).sub hcw)) fun r hr =>
        mul_ne_zero (pow_ne_zero 2 (sub_pos.2 (hu _ (hle r hr))).ne') (sub_pos.2 (ho _ (hle r hr))).ne')
      (ContinuousOn.div (continuousOn_const.mul ((hcv j₀).sub (hcv k))) (((hcv j₀).sub hcw).pow 3)
        fun r hr => pow_ne_zero 3 (sub_pos.2 (hu _ (hle r hr))).ne')
  exact hc.intervalIntegrable_of_Icc s.coe_nonneg

section Evolution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- `Σ_{x_i ≤ y} ρ_i = Σ_{x_i < y} ρ_i + ρ_Y`. -/
theorem sum_le_eq_sum_lt_add_rhoY (j₀ : Fin nR) :
    ∑ i ∈ univ.filter (fun i => xR i ≤ xR j₀), ρR i =
      ∑ i ∈ univ.filter (fun i => xR i < xR j₀), ρR i + rhoY xR ρR j₀ := by
  have hsplit : univ.filter (fun j => xR j ≤ xR j₀) =
      univ.filter (fun j => xR j < xR j₀) ∪ univ.filter (fun j => xR j = xR j₀) := by
    ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, le_iff_lt_or_eq]
  have hdisj : Disjoint (univ.filter (fun j => xR j < xR j₀)) (univ.filter (fun j => xR j = xR j₀)) :=
    Finset.disjoint_filter.2 fun j _ h1 h2 => h1.ne h2
  rw [hsplit, Finset.sum_union hdisj]
  rfl

/-- **Lemma G12 for a right mark with weight `≤ −2` strictly before it.** For an integrated `SLE_κ(ρ)` evolution
(`0 < κ < 4`) of an ordered force word and a generating trace `η`: if `y = x_{j₀}`, `x_k < y` is the last right mark
below `y`, `Σ_{x_i < y} ρ_i ≤ −2` and `Σ_{x_i ≤ y} ρ_i > κ/2 − 4`, then almost surely `η` never visits `y` on
`[0, ζ]`. -/
theorem ae_trace_ne_right_low_mark [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ < 4)
    (hord : IsOrderedForceWord xL xR) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {η : Ω → ℝ≥0 → ℂ} (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) {k j₀ : Fin nR}
    (hkjx : xR k < xR j₀) (hnext : ∀ j, xR j < xR j₀ → xR j ≤ xR k)
    (hS' : ∑ i ∈ univ.filter (fun i => xR i < xR j₀), ρR i ≤ -2)
    (hS : κ / 2 - 4 < ∑ i ∈ univ.filter (fun i => xR i ≤ xR j₀), ρR i) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ xR j₀ := by
  classical
  set S := ∑ i ∈ univ.filter (fun i => xR i < xR j₀), ρR i with hSdef
  have hy : 0 < xR j₀ := lt_of_le_of_lt (hord.2.2.2 k) hkjx
  have hkj : k ≤ j₀ := not_lt.1 fun hjk => absurd hkjx (not_lt.2 (hord.2.2.1 hjk.le))
  have hbp : 0 < lowBp κ S (rhoY xR ρR j₀) := by
    have := sum_le_eq_sum_lt_add_rhoY (xR := xR) (ρR := ρR) j₀
    simp only [lowBp]
    linarith
  rcases (hord.2.2.2 k).lt_or_eq with hxk | hxk0
  swap
  · -- `x_k = 0`: the seed is a threshold, the lifetime vanishes
    have hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR := by
      right
      have e : univ.filter (fun i => xR i = 0) = univ.filter (fun i => xR i < xR j₀) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hi; rw [hi]; exact hy
        · intro hi; exact le_antisymm (hxk0 ▸ hnext i hi) (hord.2.2.2 i)
      rw [e]
      exact hS'
    filter_upwards [hE.2.2.2.2, hη] with ω hp hηω t ht
    have hζ : ζ ω = 0 := by
      by_contra hne
      have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [ENNReal.coe_zero]; exact pos_iff_ne_zero.2 hne
      have := hp.isForcePath.not_threshold h0
      have hw : W 0 ω = 0 := hp.isForcePath.w_zero
      have hL : (fun i => VL i 0 ω) = xL := funext hp.isForcePath.vL_zero
      have hR : (fun i => VR i 0 ω) = xR := funext hp.isForcePath.vR_zero
      simp only [hw, hL, hR] at this
      exact this hseed
    rw [hζ, nonpos_iff_eq_zero, ENNReal.coe_eq_zero] at ht
    rw [ht, hηω.1]
    exact_mod_cast hy.ne
  have hinj := Theorem15.aux25Statement κ hκ hκ4 xL xR ρL ρR hord P 𝓕 W VL VR B ζ hE
  have hlim := hE.ae_tendsto_threshold hκ
  have hbud := ae_lowBudget_bounded (S := S) hκ hord hE hkj hkjx hxk hS' hbp
  filter_upwards [hinj, hlim, hE.2.2.2.2, hη, hbud] with ω h1 h2 h3 h4 h5
  intro t₁ ht₁ he₁
  have hF := h3.isForcePath
  -- the first visit `t₀`
  set Sv : Set ℝ≥0 := {t | (t : ℝ≥0∞) ≤ ζ ω} ∩ η ω ⁻¹' {(xR j₀ : ℂ)} with hSv
  have hζc : IsClosed {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ ω} := isClosed_le ENNReal.continuous_coe continuous_const
  have hSc : IsClosed Sv := h4.2.1.preimage_isClosed_of_isClosed hζc isClosed_singleton
  have hSne : Sv.Nonempty := ⟨t₁, ht₁, he₁⟩
  set t₀ := sInf Sv with ht₀def
  have ht₀S : t₀ ∈ Sv := hSc.csInf_mem hSne (OrderBot.bddBelow Sv)
  have ht₀ζ : (t₀ : ℝ≥0∞) ≤ ζ ω := ht₀S.1
  have hvis₀ : η ω t₀ = xR j₀ := ht₀S.2
  have hfirst : ∀ s < t₀, η ω s ≠ xR j₀ := fun s hs he =>
    absurd (csInf_le (OrderBot.bddBelow Sv) ⟨(ENNReal.coe_le_coe.2 hs.le).trans ht₀ζ, he⟩) (not_le.2 hs)
  have hltζ : ∀ s : ℝ≥0, s < t₀ → (s : ℝ≥0∞) < ζ ω := fun s hs =>
    (ENNReal.coe_lt_coe.2 hs).trans_le ht₀ζ
  obtain ⟨hupos, hopos⟩ := gap_pos_of_first_visit hF hord h4 hkjx hnext hS' ht₀ζ hvis₀ hfirst
  -- the picture and the almost-sure budget bound
  obtain ⟨q, hq0, hqt₀, C, hpic⟩ := lowPic_of_first_visit hκ hF hord h4 (h1 _ h4)
    (fun T hT hζ => let ⟨w₀, vL₀, vR₀, hl, _⟩ := h2 T hT hζ; ⟨w₀, vL₀, vR₀, hl⟩) hkjx hnext rfl hS' ht₀ζ hvis₀
    hfirst
  obtain ⟨K, hK⟩ := h5 q C t₀ hpic
  set q' : ℝ≥0 := (q : ℝ).toNNReal with hq'def
  have hq'N : (q' : ℝ) = q := Real.coe_toNNReal _ hq0.le
  have hq't₀ : q' < t₀ := by rw [← NNReal.coe_lt_coe, hq'N]; exact hqt₀
  have hK0 : 0 ≤ K := by
    have := hK q' le_rfl hq't₀
    rwa [intervalIntegral.integral_same] at this
  -- the budget before `q`
  have hlifeq : G11.IsMarkLife (W · ω) (VR j₀ · ω) (ζ ω) q' :=
    ⟨hltζ q' hq't₀, fun u hu => hupos u (lt_of_le_of_lt hu hq't₀)⟩
  have hiq := intervalIntegrable_pairBudget hF (k := k) (j₀ := j₀) (hltζ q' hq't₀)
    (fun r hr => hopos r (lt_of_le_of_lt hr hq't₀)) (fun r hr => hupos r (lt_of_le_of_lt hr hq't₀))
  set Bq := ∫ x in (0 : ℝ)..q', G12.pairBudget (W · ω) (VR k · ω) (VR j₀ · ω) x
  refine absurd hvis₀ (G12.trace_ne_of_budget_lt hF hkj (hord.2.2.2 k) hkjx h4 ht₀ζ (C := Bq + K)
    fun s hs hst₀ => ?_)
  rcases le_total s q' with hsq | hqs
  · have := intervalIntegral.integral_mono_interval (μ := volume) le_rfl s.coe_nonneg
      (by exact_mod_cast hsq) ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun x hx =>
        G12.pairBudget_nonneg hF hkj hlifeq ⟨hx.1.le, hx.2⟩)) hiq
    linarith
  · have his := intervalIntegrable_pairBudget hF (k := k) (j₀ := j₀) (hltζ s hst₀)
      (fun r hr => hopos r (lt_of_le_of_lt hr hst₀)) (fun r hr => hupos r (lt_of_le_of_lt hr hst₀))
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hiq (hiq.symm.trans his)
    have hKs := hK s hqs hst₀
    have e : ∫ x in (q' : ℝ)..s, lowBudget W VR k j₀ ω x =
        ∫ x in (q' : ℝ)..s, G12.pairBudget (W · ω) (VR k · ω) (VR j₀ · ω) x := rfl
    rw [e] at hKs
    linarith

/-- **Lemma G12 for a right point with weight `≤ −2` strictly before it** (a mark or a passive point): for
`0 < κ < 4`, `y > 0`, some right mark below `y`, `Σ_{x_i < y} ρ_i ≤ −2` and `Σ_{x_i ≤ y} ρ_i > κ/2 − 4`, almost surely
`η` never visits `y` on `[0, ζ]`. -/
theorem ae_trace_ne_right_low [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ < 4)
    (hord : IsOrderedForceWord xL xR) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {η : Ω → ℝ≥0 → ℂ} (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) {y : ℝ} (hy : 0 < y)
    (hex : ∃ j, xR j < y) (hS' : ∑ i ∈ univ.filter (fun i => xR i < y), ρR i ≤ -2)
    (hS : κ / 2 - 4 < ∑ i ∈ univ.filter (fun i => xR i ≤ y), ρR i) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ y := by
  classical
  obtain ⟨j₁, hj₁⟩ := hex
  have hne : (univ.filter (fun j => xR j < y)).Nonempty := ⟨j₁, Finset.mem_filter.2 ⟨mem_univ _, hj₁⟩⟩
  set k := (univ.filter (fun j => xR j < y)).max' hne with hkdef
  have hk : xR k < y := (Finset.mem_filter.1 (Finset.max'_mem _ hne)).2
  have hky : ∀ j, xR j < y → j ≤ k := fun j hj => Finset.le_max' _ j (Finset.mem_filter.2 ⟨mem_univ _, hj⟩)
  by_cases hmark : ∃ j₀, xR j₀ = y
  · obtain ⟨j₀, rfl⟩ := hmark
    exact ae_trace_ne_right_low_mark hκ hκ4 hord hE hη hk (fun j hj => hord.2.2.1 (hky j hj)) hS' hS
  push Not at hmark
  -- insert a passive mark at `y`
  set p : Fin (nR + 1) := k.succ with hpdef
  have hE' := G12.isIntegratedSLEEvolution_insertPassive hE hord hy hk hky
  have hb : ∀ j : Fin nR, j.castSucc < p → xR j ≤ y := fun j hj => by
    rw [hpdef, Fin.castSucc_lt_succ_iff] at hj
    exact (hord.2.2.1 hj).trans hk.le
  have ha : ∀ j : Fin nR, p ≤ j.castSucc → y ≤ xR j := fun j hj => by
    have hkj : k < j := by
      rw [hpdef] at hj
      by_contra hjk; rw [not_lt] at hjk
      exact absurd hj (not_le.2 (Fin.castSucc_lt_succ_iff.2 hjk))
    by_contra hlt; rw [not_le] at hlt
    exact absurd (hky j hlt) (not_le.2 hkj)
  have hmono := G12.monotone_insertNth hord.2.2.1 p hb ha
  have hord' : IsOrderedForceWord xL (Fin.insertNth (α := fun _ => ℝ) p y xR) := by
    refine ⟨hord.1, hord.2.1, hmono, fun i => ?_⟩
    rcases Fin.eq_self_or_eq_succAbove p i with rfl | ⟨j, rfl⟩
    · simp only [Fin.insertNth_apply_same]; exact hy.le
    · simp only [Fin.insertNth_apply_succAbove]; exact hord.2.2.2 j
  have hyp : Fin.insertNth (α := fun _ => ℝ) p y xR p = y := Fin.insertNth_apply_same _ _ _
  have hkp : Fin.insertNth (α := fun _ => ℝ) p y xR (p.succAbove k) = xR k := Fin.insertNth_apply_succAbove _ _ _ _
  have hnext : ∀ i, Fin.insertNth (α := fun _ => ℝ) p y xR i < Fin.insertNth (α := fun _ => ℝ) p y xR p →
      Fin.insertNth (α := fun _ => ℝ) p y xR i ≤ Fin.insertNth (α := fun _ => ℝ) p y xR (p.succAbove k) := by
    intro i hi
    rw [hyp] at hi
    rw [hkp]
    rcases Fin.eq_self_or_eq_succAbove p i with rfl | ⟨j, rfl⟩
    · rw [hyp] at hi; exact absurd hi (lt_irrefl y)
    · rw [Fin.insertNth_apply_succAbove] at hi ⊢
      exact hord.2.2.1 (hky j hi)
  have hsum : ∀ (r : ℝ → Prop) [DecidablePred r], ¬ r y →
      ∑ i ∈ univ.filter (fun i => r (Fin.insertNth (α := fun _ => ℝ) p y xR i)),
          Fin.insertNth (α := fun _ => ℝ) p 0 ρR i =
        ∑ j ∈ univ.filter (fun j => r (xR j)), ρR j := by
    intro r _ hr
    rw [Finset.sum_filter, Finset.sum_filter, G12.sum_insertNth_of_eq_zero p _ (by simp)]
    simp only [Fin.insertNth_apply_succAbove]
  have h1 := hsum (fun x => x < y) (lt_irrefl y)
  have h3 : ∑ i ∈ univ.filter (fun i => Fin.insertNth (α := fun _ => ℝ) p y xR i ≤ y),
      Fin.insertNth (α := fun _ => ℝ) p 0 ρR i = ∑ j ∈ univ.filter (fun j => xR j ≤ y), ρR j := by
    rw [Finset.sum_filter, Finset.sum_filter, G12.sum_insertNth_of_eq_zero p _ (by simp)]
    simp only [Fin.insertNth_apply_succAbove]
  have h := ae_trace_ne_right_low_mark (k := p.succAbove k) (j₀ := p) hκ hκ4 hord' hE' hη
    (by rw [hkp, hyp]; exact hk) hnext (by rw [hyp, h1]; exact hS') (by rw [hyp, h3]; exact hS)
  rw [hyp] at h
  exact h

/-- **Lemma G12 for a left point with weight `≤ −2` strictly before it**, the reflection of
`ae_trace_ne_right_low`. -/
theorem ae_trace_ne_left_low [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ < 4)
    (hord : IsOrderedForceWord xL xR) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {η : Ω → ℝ≥0 → ℂ} (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) {y : ℝ} (hy : y < 0)
    (hex : ∃ j, y < xL j) (hS' : ∑ i ∈ univ.filter (fun i => y < xL i), ρL i ≤ -2)
    (hS : κ / 2 - 4 < ∑ i ∈ univ.filter (fun i => y ≤ xL i), ρL i) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ y := by
  have hE' := hE.reflect
  have hη' : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => (-W) t ω) (ζ ω) (fun t => LP.reflectC (η ω t)) := by
    filter_upwards [hη] with ω h
    exact LP.isGeneratingTrace_reflect h
  obtain ⟨j₁, hj₁⟩ := hex
  have hf1 : univ.filter (fun k => (-xL) k < -y) = univ.filter (fun k => y < xL k) :=
    Finset.filter_congr fun k _ => by simp
  have hf2 : univ.filter (fun k => (-xL) k ≤ -y) = univ.filter (fun k => y ≤ xL k) :=
    Finset.filter_congr fun k _ => by simp
  have h := ae_trace_ne_right_low (y := -y) hκ hκ4 (G12.isOrderedForceWord_reflect hord) hE' hη'
    (by linarith) ⟨j₁, by simpa using hj₁⟩ (by rw [hf1]; exact hS') (by rw [hf2]; exact hS)
  filter_upwards [h] with ω hω t ht heq
  apply hω t ht
  rw [heq]
  simp [LP.reflectC]

end Evolution

end G12Low

namespace G12

/-- **The remainder of Lemma G12 after PROVE-G12C** (a conditional input, **not proved**): `G12EvolStatement`
restricted to the points with no mark strictly between the seed and the point on its side (case 3b of PROVE-G12B;
flow-line words always carry the seed mark `0^±`, so Corollary W0a never needs it). -/
def G12Remainder3Statement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ), IsOrderedForceWord xL xR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
    ∀ η : Ω → ℝ≥0 → ℂ, (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) →
    ∀ y : ℝ,
      (0 < y → κ / 2 - 4 < ∑ i ∈ univ.filter (fun i => xR i ≤ y), ρR i → (∀ i, ¬ xR i < y) →
        ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ y) ∧
      (y < 0 → κ / 2 - 4 < ∑ i ∈ univ.filter (fun i => y ≤ xL i), ρL i → (∀ i, ¬ y < xL i) →
        ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ y)

/-- PROVE-G12B's remainder follows from the smaller one (the weight-`≤ −2` case is `G12Low.ae_trace_ne_*_low`). -/
theorem g12Remainder2Statement_of_remainder3 (h : G12Remainder3Statement.{u}) : G12Remainder2Statement.{u} := by
  intro κ hκ hκ4 nL nR xL xR ρL ρR hord Ω mΩ P _ 𝓕 W VL VR B ζ hE η hη y
  refine ⟨fun hy hS hc => ?_, fun hy hS hc => ?_⟩
  · by_cases hex : ∃ i, xR i < y
    · have hS' : ∑ i ∈ univ.filter (fun i => xR i < y), ρR i ≤ -2 := by
        by_contra hlt
        exact hc ⟨hex, lt_of_not_ge hlt⟩
      exact G12Low.ae_trace_ne_right_low hκ hκ4 hord hE hη hy hex hS' hS
    · push Not at hex
      exact (h κ hκ hκ4 xL xR ρL ρR hord P 𝓕 W VL VR B ζ hE η hη y).1 hy hS fun i => not_lt.2 (hex i)
  · by_cases hex : ∃ i, y < xL i
    · have hS' : ∑ i ∈ univ.filter (fun i => y < xL i), ρL i ≤ -2 := by
        by_contra hlt
        exact hc ⟨hex, lt_of_not_ge hlt⟩
      exact G12Low.ae_trace_ne_left_low hκ hκ4 hord hE hη hy hex hS' hS
    · push Not at hex
      exact (h κ hκ hκ4 xL xR ρL ρR hord P 𝓕 W VL VR B ζ hE η hη y).2 hy hS fun i => not_lt.2 (hex i)

/-- **Lemma G12 in the source's form from the smaller remainder** (only the points without a mark strictly between
the seed and the point remain). -/
theorem g12EvolStatement_of_remainder3 (h : G12Remainder3Statement.{u}) : G12EvolStatement.{u} :=
  g12EvolStatement_of_remainder2 (g12Remainder2Statement_of_remainder3 h)

end G12


namespace G12Low

section Covered

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **Lemma G12 at every right point with a right mark strictly below it** (`0 < κ < 4`): if
`Σ_{x_i ≤ y} ρ_i > κ/2 − 4`, almost surely `η` never visits `y` on `[0, ζ]` — whatever the weight strictly before
`y` (`> −2`: PROVE-G12B; `≤ −2`: this packet). -/
theorem ae_trace_ne_right_of_exists [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ < 4)
    (hord : IsOrderedForceWord xL xR) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {η : Ω → ℝ≥0 → ℂ} (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) {y : ℝ} (hy : 0 < y)
    (hex : ∃ j, xR j < y) (hS : κ / 2 - 4 < ∑ i ∈ univ.filter (fun i => xR i ≤ y), ρR i) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ y := by
  by_cases hS' : -2 < ∑ i ∈ univ.filter (fun i => xR i < y), ρR i
  · exact G12.ae_trace_ne_of_rightCovered2 hκ hord hE hη hy hS ⟨hex, hS'⟩
  · exact ae_trace_ne_right_low hκ hκ4 hord hE hη hy hex (le_of_not_gt hS') hS

/-- **Lemma G12 at every left point with a left mark strictly above it**, the reflection. -/
theorem ae_trace_ne_left_of_exists [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ < 4)
    (hord : IsOrderedForceWord xL xR) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {η : Ω → ℝ≥0 → ℂ} (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) {y : ℝ} (hy : y < 0)
    (hex : ∃ j, y < xL j) (hS : κ / 2 - 4 < ∑ i ∈ univ.filter (fun i => y ≤ xL i), ρL i) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ y := by
  by_cases hS' : -2 < ∑ i ∈ univ.filter (fun i => y < xL i), ρL i
  · exact G12.ae_trace_ne_of_leftCovered2 hκ hord hE hη hy hS ⟨hex, hS'⟩
  · exact ae_trace_ne_left_low hκ hκ4 hord hE hη hy hex (le_of_not_gt hS') hS

/-- **Aux. lemma 132, the `x₂` entries of the first-swallow table (SS1)** (the "G4 entry"): for an integrated
`SLE_κ(r₁, r₂)` evolution with two right marks `0 < x₁ < x₂` (`0 < κ < 4`, any left marks), if
`S = r₁ + r₂ > κ/2 − 4 = d` then almost surely the trace never visits `x₂` (in particular `x₂` is never the endpoint of
the first swallow of `x₁`): the table's entry `x₂` occurs only for `S ≤ d`. -/
theorem aux132_trace_ne_x₂ [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ < 4) {xR ρR : Fin 2 → ℝ}
    {VR : Fin 2 → ℝ≥0 → Ω → ℝ} (hord : IsOrderedForceWord xL xR) (hx : xR 0 < xR 1)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) (hS : κ / 2 - 4 < ρR 0 + ρR 1) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ xR 1 := by
  have hy : 0 < xR 1 := lt_of_le_of_lt (hord.2.2.2 0) hx
  have hall : Finset.univ.filter (fun i : Fin 2 => xR i ≤ xR 1) = Finset.univ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    fin_cases i
    · exact iff_true_intro hx.le
    · exact iff_true_intro le_rfl
  refine ae_trace_ne_right_of_exists hκ hκ4 hord hE hη hy ⟨0, hx⟩ ?_
  rw [hall, Fin.sum_univ_two]
  exact hS

end Covered

end G12Low

/-- **Lemma G12 for a flow line, unconditional** (`Supp9.G12FlowStatement`, the form in which Corollary W0a uses it):
the flow-line word always carries the seed marks `0^±`, so every point beyond the seed has a mark strictly between the
seed and it, and `G12Low.ae_trace_ne_right_of_exists` / `ae_trace_ne_left_of_exists` apply. -/
theorem g12FlowStatement : Supp9.G12FlowStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x θ y Ω _ P _ h _ η ζ hη
  obtain ⟨_h', 𝓕, W, VL, VR, B, -, hcpl, htr⟩ := hη
  have hord := Theorem15.isOrderedForceWord_flowLine b jumps x
  have key : ∀ ω t, η ω t = y → η ω t - x = ((y - x : ℝ) : ℂ) := fun ω t he => by
    rw [he]; push_cast; ring
  refine ⟨fun hxy hS => ?_, fun hyx hS => ?_⟩
  · have hex : ∃ j, flowLineXR b jumps x j < y - x := by
      refine ⟨⟨0, Nat.succ_pos _⟩, ?_⟩
      have h0 : flowLineXR b jumps x ⟨0, Nat.succ_pos _⟩ = 0 := Fin.cons_zero _ _
      rw [h0]; linarith
    filter_upwards [G12Low.ae_trace_ne_right_of_exists hκ hκ4 hord hcpl.1 htr (sub_pos.2 hxy) hex
      (by rwa [sum_filter_flowLineXR_le hκ hb θ hxy])] with ω hω t ht he
    exact hω t ht (key ω t he)
  · have hex : ∃ j, y - x < flowLineXL b jumps x j := by
      refine ⟨⟨0, Nat.succ_pos _⟩, ?_⟩
      have h0 : flowLineXL b jumps x ⟨0, Nat.succ_pos _⟩ = 0 := Fin.cons_zero _ _
      rw [h0]; linarith
    filter_upwards [G12Low.ae_trace_ne_left_of_exists hκ hκ4 hord hcpl.1 htr (sub_neg.2 hyx) hex
      (by rwa [sum_filter_flowLineXL_ge hκ hb θ hyx])] with ω hω t ht he
    exact hω t ht (key ω t he)

/-- **Corollary W0a, unconditional** (p. 528): opposite original seeds are not visited. -/
theorem w0aStatement : Supp9.W0aStatement.{u} :=
  Supp9.w0aStatement_of_g12 g12FlowStatement

end Supp7

end InteractingSLE
