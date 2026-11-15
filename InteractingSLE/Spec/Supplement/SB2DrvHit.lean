/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvRule

/-!
# The first visit of a point as a parameterized Galmarino rule on rational path coordinates

Packet PROVE-T14-SB2DRV (round 3). SB2(1)'s entrance time `T_L` (the first visit of the real point `L` by the upper
flow; p. 632, "Its first visit [...] is a stopping rule of this retained staged history") must be a rule in the
Galmarino form of `SB2DrvRule` (`IsParamGalmarino`), with the point `L` as parameter. The rational first entrance
times of open sets (`Sec6.firstEntrance`) are not Galmarino for arbitrary coordinates; the first hit of a point is,
once only *attained* hits are kept (the device of `Restart.FlowStopIdentG.hitRule` for dyadic records):

* `gapQ z c t`: the distance from `z` of the coordinates `c` at rational times `≤ t`;
* `hitStartQ z c`: the first time with zero gap; **`hitQ z c`**: `hitStartQ` when it is finite and attained, `⊤`
  otherwise;
* **`isParamGalmarino_hitQ`**, **`measurable_hitQ`**;
* **`hitQ_pathCoord`**: for a continuous path, `hitQ z (pathCoord γ) = inf {s : γ s = z}`; `exists_hitQ_pathCoord`:
  the infimum is attained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Lv

open Sec6

/-- The distance of `z` from the coordinates at rational times up to `t`. -/
def gapQ (z : ℂ) (c : ℚ≥0 → ℂ) (t : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ q : ℚ≥0, if (((q : ℝ≥0) : ℝ≥0∞) ≤ t) then edist (c q) z else ⊤

/-- The first time with zero gap. -/
def hitStartQ (z : ℂ) (c : ℚ≥0 → ℂ) : ℝ≥0∞ := ⨅ (t : ℝ≥0∞) (_ : gapQ z c t = 0), t

open Classical in
/-- **The first hit of `z`**: `hitStartQ` when it is finite and attained (zero gap at it), `⊤` otherwise. -/
def hitQ (z : ℂ) (c : ℚ≥0 → ℂ) : ℝ≥0∞ :=
  if hitStartQ z c < ⊤ ∧ gapQ z c (hitStartQ z c) = 0 then hitStartQ z c else ⊤

theorem gapQ_congr {z : ℂ} {c c' : ℚ≥0 → ℂ} {t : ℝ≥0∞}
    (h : ∀ q : ℚ≥0, (((q : ℝ≥0) : ℝ≥0∞) ≤ t) → c q = c' q) : gapQ z c t = gapQ z c' t := by
  unfold gapQ
  refine iInf_congr fun q => ?_
  by_cases hq : (((q : ℝ≥0) : ℝ≥0∞) ≤ t)
  · rw [ite_eq_left hq, ite_eq_left hq, h q hq]
  · rw [ite_eq_right hq, ite_eq_right hq]

theorem gapQ_eq_zero_iff {z : ℂ} {c : ℚ≥0 → ℂ} {t : ℝ≥0∞} :
    gapQ z c t = 0 ↔ ∀ ε > (0 : ℝ≥0∞), ∃ q : ℚ≥0, (((q : ℝ≥0) : ℝ≥0∞) ≤ t) ∧ edist (c q) z < ε := by
  constructor
  · intro h ε hε
    have hlt : gapQ z c t < ε := by rw [h]; exact hε
    obtain ⟨q, hq⟩ := iInf_lt_iff.1 hlt
    by_cases hqt : (((q : ℝ≥0) : ℝ≥0∞) ≤ t)
    · rw [ite_eq_left hqt] at hq
      exact ⟨q, hqt, hq⟩
    · rw [ite_eq_right hqt] at hq
      exact absurd hq (not_lt.2 le_top)
  · intro h
    by_contra hne
    obtain ⟨q, hqt, hq⟩ := h _ (pos_iff_ne_zero.2 hne)
    have hle : gapQ z c t ≤ edist (c q) z := by
      refine (iInf_le _ q).trans ?_
      rw [ite_eq_left hqt]
    exact lt_irrefl _ (hle.trans_lt hq)

/-- The first rational time within `1/n` of `z`. -/
def nearQ (n : ℕ) (z : ℂ) (c : ℚ≥0 → ℂ) : ℝ≥0∞ :=
  ⨅ q : ℚ≥0, if edist (c q) z < (n : ℝ≥0∞)⁻¹ then (((q : ℝ≥0) : ℝ≥0∞)) else ⊤

theorem nearQ_le {n : ℕ} {z : ℂ} {c : ℚ≥0 → ℂ} {q : ℚ≥0} (hq : edist (c q) z < (n : ℝ≥0∞)⁻¹) :
    nearQ n z c ≤ (((q : ℝ≥0) : ℝ≥0∞)) := by
  refine (iInf_le _ q).trans ?_
  rw [ite_eq_left hq]

/-- The first time with zero gap is the supremum of the first rational times within `1/n`. -/
theorem hitStartQ_eq_iSup (z : ℂ) (c : ℚ≥0 → ℂ) : hitStartQ z c = ⨆ n : ℕ, nearQ n z c := by
  refine le_antisymm ?_ ?_
  · refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
    refine iInf₂_le r (gapQ_eq_zero_iff.2 fun ε hε => ?_)
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hε.ne'
    have hlt : nearQ n z c < r := (le_iSup (fun n => nearQ n z c) n).trans_lt hr
    obtain ⟨q, hq⟩ := iInf_lt_iff.1 hlt
    by_cases hqn : edist (c q) z < (n : ℝ≥0∞)⁻¹
    · rw [ite_eq_left hqn] at hq
      exact ⟨q, hq.le, hqn.trans hn⟩
    · rw [ite_eq_right hqn] at hq
      exact absurd hq (not_lt.2 le_top)
  · refine iSup_le fun n => le_iInf₂ fun t ht => ?_
    obtain ⟨q, hqt, hq⟩ := gapQ_eq_zero_iff.1 ht _ (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top n))
    exact (nearQ_le hq).trans hqt

/-- **The first hit is a parameterized Galmarino rule.** -/
theorem isParamGalmarino_hitQ : IsParamGalmarino hitQ := by
  intro z c c' hag
  by_cases hA : hitStartQ z c < ⊤ ∧ gapQ z c (hitStartQ z c) = 0
  · have he : hitQ z c = hitStartQ z c := ite_eq_left hA
    have hgap : ∀ s, s ≤ hitStartQ z c → gapQ z c' s = gapQ z c s := fun s hs =>
      (gapQ_congr fun q hq => hag q (by rw [he]; exact hq.trans hs)).symm
    have hs : hitStartQ z c' = hitStartQ z c := by
      refine le_antisymm (iInf₂_le _ (by rw [hgap _ le_rfl]; exact hA.2)) (le_iInf₂ fun t ht => ?_)
      by_cases htT : t ≤ hitStartQ z c
      · rw [hgap t htT] at ht
        exact iInf₂_le t ht
      · exact (not_le.1 htT).le
    have hA' : hitStartQ z c' < ⊤ ∧ gapQ z c' (hitStartQ z c') = 0 := by
      rw [hs, hgap _ le_rfl]
      exact hA
    rw [he]
    show (if hitStartQ z c' < ⊤ ∧ gapQ z c' (hitStartQ z c') = 0 then hitStartQ z c' else ⊤) = _
    rw [ite_eq_left hA', hs]
  · have he : hitQ z c = ⊤ := ite_eq_right hA
    have hcc : c = c' := funext fun q => hag q (by rw [he]; exact le_top)
    rw [hcc]

theorem measurable_gapQ :
    Measurable fun x : (ℂ × (ℚ≥0 → ℂ)) × ℝ≥0∞ => gapQ x.1.1 x.1.2 x.2 := by
  refine Measurable.iInf fun q => ?_
  refine Measurable.ite (measurableSet_le measurable_const measurable_snd) ?_ measurable_const
  exact ((measurable_pi_apply q).comp (measurable_snd.comp measurable_fst)).edist
    (measurable_fst.comp measurable_fst)

theorem measurable_hitStartQ : Measurable fun p : ℂ × (ℚ≥0 → ℂ) => hitStartQ p.1 p.2 := by
  simp only [hitStartQ_eq_iSup]
  refine Measurable.iSup fun n => Measurable.iInf fun q => ?_
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_lt (((measurable_pi_apply q).comp measurable_snd).edist measurable_fst) measurable_const

/-- **The first hit is measurable** in the point and the coordinates. -/
theorem measurable_hitQ : Measurable (Function.uncurry hitQ) := by
  classical
  have hg : Measurable fun p : ℂ × (ℚ≥0 → ℂ) => gapQ p.1 p.2 (hitStartQ p.1 p.2) :=
    measurable_gapQ.comp (measurable_id.prodMk measurable_hitStartQ)
  have hset : MeasurableSet {p : ℂ × (ℚ≥0 → ℂ) | hitStartQ p.1 p.2 < ⊤ ∧ gapQ p.1 p.2 (hitStartQ p.1 p.2) = 0} :=
    (measurableSet_lt measurable_hitStartQ measurable_const).inter (hg (measurableSet_singleton 0))
  have e : Function.uncurry hitQ = fun p : ℂ × (ℚ≥0 → ℂ) =>
      if hitStartQ p.1 p.2 < ⊤ ∧ gapQ p.1 p.2 (hitStartQ p.1 p.2) = 0 then hitStartQ p.1 p.2 else ⊤ := by
    funext p
    simp only [Function.uncurry, hitQ]
  rw [e]
  exact Measurable.ite hset measurable_hitStartQ measurable_const

/-! ### Continuous paths -/

section Path

variable {γ : ℝ≥0 → ℂ} {z : ℂ}

/-- For a continuous path, the gap at a finite time vanishes iff the path has visited `z` by then. -/
theorem gapQ_pathCoord_eq_zero_iff (hγ : Continuous γ) (r : ℝ≥0) :
    gapQ z (pathCoord γ) r = 0 ↔ ∃ s : ℝ≥0, s ≤ r ∧ γ s = z := by
  rw [gapQ_eq_zero_iff]
  constructor
  · intro h
    have hK : IsClosed (γ '' Icc 0 r) := (isCompact_Icc.image hγ).isClosed
    have hz : z ∈ closure (γ '' Icc 0 r) := by
      refine EMetric.mem_closure_iff.2 fun ε hε => ?_
      obtain ⟨q, hqr, hq⟩ := h ε hε
      refine ⟨γ q, ⟨q, ⟨zero_le, ENNReal.coe_le_coe.1 hqr⟩, rfl⟩, ?_⟩
      rw [edist_comm]
      exact hq
    rw [hK.closure_eq] at hz
    obtain ⟨s, hs, hsz⟩ := hz
    exact ⟨s, hs.2, hsz⟩
  · rintro ⟨s, hsr, hsz⟩ ε hε
    have hev : ∀ᶠ t in 𝓝 s, edist (γ t) z < ε := by
      have ht := hγ.tendsto s
      rw [hsz] at ht
      exact EMetric.tendsto_nhds.1 ht ε hε
    rcases eq_or_ne s 0 with rfl | hs0
    · refine ⟨0, by simp, ?_⟩
      have : pathCoord γ 0 = z := by simpa [pathCoord] using hsz
      rw [this, edist_self]
      exact hε
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
    have hspos : (0 : ℝ) < s := lt_of_le_of_ne s.2 (fun h => hs0 (NNReal.eq h.symm))
    obtain ⟨r', hr1, hr2⟩ := exists_rat_btwn (show max 0 ((s : ℝ) - δ) < s by
      rw [max_lt_iff]; exact ⟨hspos, by linarith⟩)
    have hr0 : (0 : ℝ) ≤ r' := (le_max_left _ _).trans hr1.le
    set q : ℚ≥0 := r'.toNNRat with hqdef
    have hqt : ((q : ℝ≥0) : ℝ) = r' := by
      rw [show ((q : ℝ≥0) : ℝ) = ((q : ℚ) : ℝ) by norm_cast, hqdef, Rat.coe_toNNRat r' (by exact_mod_cast hr0)]
    have hm := (le_max_right 0 ((s : ℝ) - δ)).trans_lt hr1
    have hqs : (q : ℝ≥0) ≤ s := by
      rw [← NNReal.coe_le_coe, hqt]; exact hr2.le
    refine ⟨q, ENNReal.coe_le_coe.2 (hqs.trans hsr), ?_⟩
    have hq := hball (show dist ((q : ℝ≥0)) s < δ by
      rw [NNReal.dist_eq, hqt, abs_sub_lt_iff]
      constructor
      · linarith
      · linarith)
    exact hq

/-- **The first hit of a point by a continuous path**, when there is one: it is attained, it is the rule's value,
and it is below every visit. -/
theorem exists_hitQ_pathCoord (hγ : Continuous γ) (hex : ∃ s, γ s = z) :
    ∃ s₀ : ℝ≥0, γ s₀ = z ∧ hitQ z (pathCoord γ) = s₀ ∧ ∀ s, γ s = z → s₀ ≤ s := by
  have hZ : IsClosed (γ ⁻¹' {z}) := isClosed_singleton.preimage hγ
  have hmem := hZ.csInf_mem hex (OrderBot.bddBelow _)
  set s₀ := sInf (γ ⁻¹' {z}) with hs₀
  have hmin : ∀ s, γ s = z → s₀ ≤ s := fun s hs => csInf_le (OrderBot.bddBelow _) hs
  have hstart : hitStartQ z (pathCoord γ) = s₀ := by
    refine le_antisymm ?_ (le_iInf₂ fun t ht => ?_)
    · unfold hitStartQ
      exact iInf₂_le (s₀ : ℝ≥0∞) ((gapQ_pathCoord_eq_zero_iff hγ s₀).2 ⟨s₀, le_rfl, hmem⟩)
    induction t using ENNReal.recTopCoe with
    | top => exact le_top
    | coe r =>
      obtain ⟨s, hsr, hsz⟩ := (gapQ_pathCoord_eq_zero_iff hγ r).1 ht
      exact ENNReal.coe_le_coe.2 ((hmin s hsz).trans hsr)
  have hA : hitStartQ z (pathCoord γ) < ⊤ ∧ gapQ z (pathCoord γ) (hitStartQ z (pathCoord γ)) = 0 := by
    rw [hstart]
    exact ⟨ENNReal.coe_lt_top, (gapQ_pathCoord_eq_zero_iff hγ s₀).2 ⟨s₀, le_rfl, hmem⟩⟩
  refine ⟨s₀, hmem, ?_, hmin⟩
  rw [← hstart]
  exact ite_eq_left hA

/-- A continuous path that never visits `z` has infinite first hit. -/
theorem hitQ_pathCoord_eq_top (hγ : Continuous γ) (hno : ∀ s, γ s ≠ z) : hitQ z (pathCoord γ) = ⊤ := by
  refine ite_eq_right fun hA => ?_
  have htop : hitStartQ z (pathCoord γ) = ⊤ := by
    refine iInf₂_eq_top.2 fun t ht => ?_
    induction t using ENNReal.recTopCoe with
    | top => rfl
    | coe r =>
      obtain ⟨s, -, hsz⟩ := (gapQ_pathCoord_eq_zero_iff hγ r).1 ht
      exact absurd hsz (hno s)
  exact absurd hA.1 (by rw [htop]; exact lt_irrefl _)

/-- **For a continuous path, the rule is the first visit time** `inf {s : γ s = z}`. -/
theorem hitQ_pathCoord (hγ : Continuous γ) (z : ℂ) :
    hitQ z (pathCoord γ) = ⨅ (s : ℝ≥0) (_ : γ s = z), (s : ℝ≥0∞) := by
  by_cases hex : ∃ s, γ s = z
  · obtain ⟨s₀, hs₀, he, hmin⟩ := exists_hitQ_pathCoord hγ hex
    rw [he]
    exact le_antisymm (le_iInf₂ fun s hs => ENNReal.coe_le_coe.2 (hmin s hs)) (iInf₂_le s₀ hs₀)
  · push Not at hex
    rw [hitQ_pathCoord_eq_top hγ hex]
    exact (iInf₂_eq_top.2 fun s hs => absurd hs (hex s)).symm

end Path

end InteractingSLE.Theorem14.SB.Lv
