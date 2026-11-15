/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1DetCode
import InteractingSLE.Spec.Supplement.BW1DetPhys

/-!
# BW1's terminal relation: the hits of the root and the piece

Packet PROVE-BW1-DET. For a regular piece `D` (trace `α` on `[0, L]`, `L = D.2 < ∞`) and a regular counterflow `V`
(trace `γ`), the launch-coordinate tip of `V` at time `t` lies in `termSet D` iff `γ t = −1/α(p)` for some
`p ≤ L` with `α(p) ≠ 0` (`hit_iff`). The set of such values is closed in `ℂ` (`limit_hit`: a limit of values
`−1/α(pₖ)` is again one), which gives the countable tests of `witnessSet` for "no hit up to time `a`"
(`noHit_iff_rat`) and for "a hit at time `s`" (`hit_iff_rat`), and then the range clause of `IsTermRelOf`
(`range_iff_tests`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal NNRat
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.BW1Det

open Exist Exist.StagedLaw GW1Borel BW1Term

/-! ### Rational approximation from below -/

/-- Every `t ≥ 0` is a limit of rationals `≤ t`. -/
theorem exists_seq_nnrat_le_tendsto (t : ℝ≥0) :
    ∃ q : ℕ → ℚ≥0, (∀ m, (q m : ℝ≥0) ≤ t) ∧ Tendsto (fun m => (q m : ℝ≥0)) atTop (𝓝 t) := by
  have h : ∀ m : ℕ, ∃ q : ℚ≥0, (q : ℝ≥0) ≤ t ∧ (t : ℝ) ≤ (q : ℝ≥0) + 1 / ((m : ℝ) + 1) := by
    intro m
    have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    rcases eq_or_ne t 0 with ht | ht
    · exact ⟨0, by simp [ht], by simp [ht]; positivity⟩
    · have hlt : t - (1 / ((m : ℝ) + 1)).toNNReal < t := by
        refine tsub_lt_self (pos_iff_ne_zero.2 ht) ?_
        exact Real.toNNReal_pos.2 hpos
      obtain ⟨q, hq1, hq2⟩ := Sec7.Coding.exists_nnrat_btwn hlt
      refine ⟨q, hq2.le, ?_⟩
      have h1 : ((t - (1 / ((m : ℝ) + 1)).toNNReal : ℝ≥0) : ℝ) < (q : ℝ≥0) := by exact_mod_cast hq1
      have h2 : (t : ℝ) - 1 / ((m : ℝ) + 1) ≤ ((t - (1 / ((m : ℝ) + 1)).toNNReal : ℝ≥0) : ℝ) := by
        rw [NNReal.coe_sub_def]
        refine le_trans ?_ (le_max_left _ _)
        rw [Real.coe_toNNReal _ hpos.le]
      linarith
  choose q hq1 hq2 using h
  refine ⟨q, hq1, ?_⟩
  rw [← NNReal.tendsto_coe]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun m : ℕ => (t : ℝ) - 1 / ((m : ℝ) + 1))
    (h := fun _ => (t : ℝ)) ?_ tendsto_const_nhds (fun m => by linarith [hq2 m])
    (fun m => by exact_mod_cast hq1 m)
  have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_sub (t : ℝ)
  simpa only [sub_zero] using this

/-! ### Records and charts of regular pieces -/

section Piece

variable {D : (ℝ≥0 → ℝ) × ℝ≥0∞}

theorem recOf_snd_fst : (recOf ⊤ D).2.1 = D.2 := min_top_left _

/-- The continuous driver of the record of a regular piece is its stopped driver. -/
theorem recDrvC_recOf (hWc : ContinuousOn D.1 {t | (t : ℝ≥0∞) ≤ D.2}) (hW0 : D.1 0 = 0) :
    recDrvC (recOf ⊤ D) = (retOf ⊤ D).1 := by
  have hc : Continuous (retOf ⊤ D).1 := by
    have := CounterflowRange.continuous_stopped (W := D.1) (S := min ⊤ D.2) (by rwa [min_top_left])
    exact this
  have h0 : (retOf ⊤ D).1 0 = 0 := by
    change D.1 (min ((0 : ℝ≥0) : ℝ≥0∞) (min ⊤ D.2)).toNNReal = 0
    rw [ENNReal.coe_zero, zero_min, ENNReal.toNNReal_zero, hW0]
  have hcode : recCode (recOf ⊤ D) = fun q : ℚ≥0 => (retOf ⊤ D).1 q := by
    funext q
    change (retOf ⊤ D).1 (((q : ℚ) : ℝ).toNNReal) = (retOf ⊤ D).1 q
    rw [toNNReal_ratCast_nnrat]
  unfold recDrvC
  rw [hcode]
  exact GW1Det.regQ_restrict hc h0

/-- The chart of the record of a regular piece is the chart after the piece. -/
theorem recChart_recOf (hWc : ContinuousOn D.1 {t | (t : ℝ≥0∞) ≤ D.2}) (hW0 : D.1 0 = 0) :
    recChart (recOf ⊤ D) = termChart D := by
  unfold recChart termChart
  rw [recDrvC_recOf hWc hW0, recOf_snd_fst,
    show stopTime ⊤ D = ((D.2.toNNReal : ℝ≥0) : ℝ) by unfold stopTime; rw [min_top_left]]
  rfl

/-- The trace read from the record of a regular piece, before the lifetime. -/
theorem recPath_recOf {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace D.1 D.2 α)
    (hWc : ContinuousOn D.1 {t | (t : ℝ≥0∞) ≤ D.2}) (hW0 : D.1 0 = 0) {p : ℝ≥0} (hp : (p : ℝ≥0∞) ≤ D.2) :
    WalkLeaf.recPath (recOf ⊤ D) p = α p := by
  have h := WalkLeaf.recPath_recOf_top (w := D.1) (ζ := D.2) hWc hW0 hα p
  rw [h, min_eq_left hp, ENNReal.toNNReal_coe]

/-- The root and the piece, in the launch coordinate. -/
theorem termSet_eq {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace D.1 D.2 α)
    (hWc : ContinuousOn D.1 {t | (t : ℝ≥0∞) ≤ D.2}) (hW0 : D.1 0 = 0) :
    termSet D = {(0 : ℂ)} ∪ α '' {t | (t : ℝ≥0∞) ≤ D.2} := by
  have hα' : IsGeneratingTrace D.1 (min ⊤ D.2) α := by rwa [min_top_left]
  have hWc' : ContinuousOn D.1 {t | (t : ℝ≥0∞) ≤ min ⊤ D.2} := by rwa [min_top_left]
  have h := CounterflowRange.tipSet_stopped_eq_of_tendsto (c := Chart.id.recenter 0)
    (f := fun z : ℂ => z + ((0 : ℝ) : ℂ)) hα' hWc' hW0 fun t _ => by
      rw [CounterflowRange.recenter_id_inv]
      exact ((continuous_id.add continuous_const).tendsto _).mono_left nhdsWithin_le_nhds
  unfold termSet
  change {(0 : ℂ)} ∪ (Chart.id.recenter 0).tipSet (fun r : ℝ≥0 => D.1 (min (r : ℝ≥0∞) (min ⊤ D.2)).toNNReal)
    (min ⊤ D.2) = _
  rw [h, min_top_left]
  simp only [Complex.ofReal_zero, add_zero, image_id']

end Piece

/-! ### Hits of the root and the piece -/

/-- **The counterflow's launch-coordinate tip at time `t` is on the piece**: `γ t = −1/α(p)` for some `p ≤ L`
with `α(p) ≠ 0`. -/
def IsHit (γ α : ℝ≥0 → ℂ) (L : ℝ≥0) (t : ℝ≥0) : Prop :=
  ∃ p : ℝ≥0, p ≤ L ∧ α p ≠ 0 ∧ γ t = negInv (α p)

theorem hit_iff {D : (ℝ≥0 → ℝ) × ℝ≥0∞} {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace D.1 D.2 α)
    (hWc : ContinuousOn D.1 {t | (t : ℝ≥0∞) ≤ D.2}) (hW0 : D.1 0 = 0) (hfin : D.2 ≠ ⊤)
    {V : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace V ⊤ γ) (hV : Continuous V) (hV0 : V 0 = 0) (t : ℝ≥0) :
    (∃ z ∈ termSet D, infinitySourceChart.tipAt V t z) ↔ IsHit γ α D.2.toNNReal t := by
  have hle : ∀ p : ℝ≥0, (p : ℝ≥0∞) ≤ D.2 ↔ p ≤ D.2.toNNReal := fun p => by
    rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hfin]
  rw [termSet_eq hα hWc hW0]
  constructor
  · rintro ⟨z, hz, htip⟩
    obtain ⟨hne, rfl⟩ := (GW4Leaf.tipAt_infinitySourceChart_iff hγ hV hV0 t z).1 htip
    rcases hz with h0 | ⟨p, hp, hpz⟩
    · rw [mem_singleton_iff, neg_eq_zero, inv_eq_zero] at h0
      exact absurd h0 hne
    · refine ⟨p, (hle p).1 hp, ?_, ?_⟩
      · rw [hpz]
        exact neg_ne_zero.2 (inv_ne_zero hne)
      · rw [hpz]
        exact (GW4Traverse.negInv_negInv' (γ t)).symm
  · rintro ⟨p, hp, hne, he⟩
    have hγ0 : γ t ≠ 0 := by
      rw [he]
      exact neg_ne_zero.2 (inv_ne_zero hne)
    refine ⟨α p, Or.inr ⟨p, (hle p).2 hp, rfl⟩, (GW4Leaf.tipAt_infinitySourceChart_iff hγ hV hV0 t _).2
      ⟨hγ0, ?_⟩⟩
    rw [he]
    exact (GW4Traverse.negInv_negInv' (α p)).symm

/-- **The values `−1/α(p)` form a closed set**: a limit of such values is again one. -/
theorem limit_hit {α : ℝ≥0 → ℂ} {L : ℝ≥0} (hαc : ContinuousOn α (Icc 0 L)) {p : ℕ → ℝ≥0}
    (hp : ∀ k, p k ≤ L) (hne : ∀ k, α (p k) ≠ 0) {w : ℂ}
    (hw : Tendsto (fun k => negInv (α (p k))) atTop (𝓝 w)) :
    ∃ p₀ : ℝ≥0, p₀ ≤ L ∧ α p₀ ≠ 0 ∧ w = negInv (α p₀) := by
  obtain ⟨p₀, hp₀, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq (x := p) fun k => ⟨zero_le, hp k⟩
  have hαlim : Tendsto (fun k => α (p (φ k))) atTop (𝓝 (α p₀)) :=
    (hαc p₀ hp₀).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun k => ⟨zero_le, hp _⟩⟩)
  have hw' : Tendsto (fun k => negInv (α (p (φ k)))) atTop (𝓝 w) := hw.comp hφ.tendsto_atTop
  by_cases h0 : α p₀ = 0
  · exfalso
    have hn : Tendsto (fun k => ‖α (p (φ k))‖) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => norm_pos_iff.2 (hne _)⟩
      simpa only [h0, norm_zero] using hαlim.norm
    have hinf : Tendsto (fun k => ‖negInv (α (p (φ k)))‖) atTop atTop := by
      simp only [negInv, norm_neg, norm_inv]
      exact tendsto_inv_nhdsGT_zero.comp hn
    exact not_tendsto_atTop_of_tendsto_nhds hw'.norm hinf
  · exact ⟨p₀, hp₀.2, h0, tendsto_nhds_unique hw' (hαlim.inv₀ h0).neg⟩

variable {γ α β : ℝ≥0 → ℂ} {L : ℝ≥0}

/-- **No hit up to time `a`, as a countable test.** -/
theorem noHit_iff_rat (hγc : Continuous γ) (hαc : ContinuousOn α (Icc 0 L))
    (hβ : ∀ p : ℝ≥0, p ≤ L → β p = α p) (a : ℝ≥0) :
    (∀ t ≤ a, ¬ IsHit γ α L t) ↔ ∃ k : ℕ, ∀ q p : ℚ≥0, (q : ℝ≥0) ≤ a → ((p : ℝ≥0) : ℝ≥0∞) ≤ (L : ℝ≥0∞) →
      β p ≠ 0 → (1 : ℝ) / ((k : ℝ) + 1) ≤ ‖γ q - negInv (β p)‖ := by
  constructor
  · intro hno
    by_contra hcon
    push Not at hcon
    choose qs ps hq hp hne hlt using hcon
    have hp' : ∀ k, (ps k : ℝ≥0) ≤ L := fun k => by exact_mod_cast hp k
    obtain ⟨t, ht, φ, hφ, hlim⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := a)).tendsto_subseq
      (x := fun k => (qs k : ℝ≥0))
      fun k => ⟨zero_le, hq k⟩
    have hγlim : Tendsto (fun k => γ (qs (φ k))) atTop (𝓝 (γ t)) := (hγc.tendsto t).comp hlim
    have hε : Tendsto (fun k => (1 : ℝ) / (((φ k : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    have hw : Tendsto (fun k => negInv (α (ps (φ k)))) atTop (𝓝 (γ t)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hg : Tendsto (fun k => (1 : ℝ) / (((φ k : ℕ) : ℝ) + 1) + ‖γ (qs (φ k)) - γ t‖) atTop (𝓝 0) := by
        simpa only [add_zero] using hε.add (tendsto_iff_norm_sub_tendsto_zero.1 hγlim)
      refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) hg
      · have h1 := hlt (φ k)
        rw [hβ _ (hp' _)] at h1
        calc ‖negInv (α (ps (φ k))) - γ t‖
            ≤ ‖negInv (α (ps (φ k))) - γ (qs (φ k))‖ + ‖γ (qs (φ k)) - γ t‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ _ := by rw [norm_sub_rev]; exact add_le_add_left h1.le _
    obtain ⟨p₀, hp₀, hne₀, he₀⟩ := limit_hit hαc (fun k => hp' (φ k))
      (fun k => by rw [← hβ _ (hp' _)]; exact hne (φ k)) hw
    exact hno t ht.2 ⟨p₀, hp₀, hne₀, he₀⟩
  · rintro ⟨k, hk⟩ t ht ⟨p, hp, hne, he⟩
    obtain ⟨qs, hqs1, hqs2⟩ := exists_seq_nnrat_le_tendsto t
    obtain ⟨ps, hps1, hps2⟩ := exists_seq_nnrat_le_tendsto p
    have hγlim : Tendsto (fun m => γ (qs m)) atTop (𝓝 (γ t)) := (hγc.tendsto t).comp hqs2
    have hαlim : Tendsto (fun m => α (ps m)) atTop (𝓝 (α p)) :=
      (hαc p ⟨zero_le, hp⟩).tendsto.comp (tendsto_nhdsWithin_iff.2
        ⟨hps2, Eventually.of_forall fun m => ⟨zero_le, (hps1 m).trans hp⟩⟩)
    have hlim : Tendsto (fun m => ‖γ (qs m) - negInv (α (ps m))‖) atTop (𝓝 0) := by
      have : Tendsto (fun m => ‖γ (qs m) - negInv (α (ps m))‖) atTop (𝓝 ‖γ t - negInv (α p)‖) :=
        (hγlim.sub (hαlim.inv₀ hne).neg).norm
      rwa [← he, sub_self, norm_zero] at this
    have hbound : ∀ᶠ m in atTop, (1 : ℝ) / ((k : ℝ) + 1) ≤ ‖γ (qs m) - negInv (α (ps m))‖ := by
      filter_upwards [hαlim.eventually_ne hne] with m hm
      have hm' : (ps m : ℝ≥0) ≤ L := (hps1 m).trans hp
      have := hk (qs m) (ps m) ((hqs1 m).trans ht) (by exact_mod_cast hm') (by rwa [hβ _ hm'])
      rwa [hβ _ hm'] at this
    have h0 := ge_of_tendsto hlim hbound
    have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    linarith

/-- **A hit at time `s`, as a countable test.** -/
theorem hit_iff_rat (hαc : ContinuousOn α (Icc 0 L)) (hβ : ∀ p : ℝ≥0, p ≤ L → β p = α p) (s : ℝ≥0) :
    IsHit γ α L s ↔ ∀ k : ℕ, ∃ p : ℚ≥0, ((p : ℝ≥0) : ℝ≥0∞) ≤ (L : ℝ≥0∞) ∧ β p ≠ 0 ∧
      ‖γ s - negInv (β p)‖ < (1 : ℝ) / ((k : ℝ) + 1) := by
  constructor
  · rintro ⟨p, hp, hne, he⟩ k
    obtain ⟨ps, hps1, hps2⟩ := exists_seq_nnrat_le_tendsto p
    have hαlim : Tendsto (fun m => α (ps m)) atTop (𝓝 (α p)) :=
      (hαc p ⟨zero_le, hp⟩).tendsto.comp (tendsto_nhdsWithin_iff.2
        ⟨hps2, Eventually.of_forall fun m => ⟨zero_le, (hps1 m).trans hp⟩⟩)
    have hlim : Tendsto (fun m => ‖γ s - negInv (α (ps m))‖) atTop (𝓝 0) := by
      have : Tendsto (fun m => ‖γ s - negInv (α (ps m))‖) atTop (𝓝 ‖γ s - negInv (α p)‖) :=
        ((tendsto_const_nhds (x := γ s)).sub (hαlim.inv₀ hne).neg).norm
      rwa [← he, sub_self, norm_zero] at this
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    obtain ⟨m, hm1, hm2⟩ := ((hαlim.eventually_ne hne).and (hlim.eventually (gt_mem_nhds hpos))).exists
    have hm' : (ps m : ℝ≥0) ≤ L := (hps1 m).trans hp
    exact ⟨ps m, by exact_mod_cast hm', by rwa [hβ _ hm'], by rwa [hβ _ hm']⟩
  · intro h
    choose ps hps hne hlt using h
    have hp' : ∀ k, (ps k : ℝ≥0) ≤ L := fun k => by exact_mod_cast hps k
    have hw : Tendsto (fun k => negInv (α (ps k))) atTop (𝓝 (γ s)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
      have h1 := hlt k
      rw [hβ _ (hp' _), norm_sub_rev] at h1
      exact h1.le
    obtain ⟨p₀, hp₀, hne₀, he₀⟩ := limit_hit hαc hp' (fun k => by rw [← hβ _ (hp' _)]; exact hne k) hw
    exact ⟨p₀, hp₀, hne₀, he₀⟩

/-! ### The first hit and the clock range -/

/-- The first hit time of the piece by the counterflow's launch-coordinate tip. -/
def hitTime (γ α : ℝ≥0 → ℂ) (L : ℝ≥0) : ℝ≥0∞ := ⨅ (t : ℝ≥0) (_ : IsHit γ α L t), (t : ℝ≥0∞)

theorem firstTipTime_eq_hitTime {D : (ℝ≥0 → ℝ) × ℝ≥0∞} {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace D.1 D.2 α)
    (hWc : ContinuousOn D.1 {t | (t : ℝ≥0∞) ≤ D.2}) (hW0 : D.1 0 = 0) (hfin : D.2 ≠ ⊤)
    {V : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace V ⊤ γ) (hV : Continuous V) (hV0 : V 0 = 0) :
    firstTipTime infinitySourceChart V (termSet D) = hitTime γ α D.2.toNNReal := by
  unfold firstTipTime hitTime
  exact iInf_congr fun t => iInf_congr_Prop (hit_iff hα hWc hW0 hfin hγ hV hV0 t) fun _ => rfl

theorem hitTime_le {t : ℝ≥0} (h : IsHit γ α L t) : hitTime γ α L ≤ t := iInf₂_le t h

theorem not_hit_of_lt {t : ℝ≥0} (h : (t : ℝ≥0∞) < hitTime γ α L) : ¬ IsHit γ α L t := fun hh =>
  (hitTime_le hh).not_gt h

theorem le_hitTime {a : ℝ≥0} (h : ∀ t ≤ a, ¬ IsHit γ α L t) : (a : ℝ≥0∞) ≤ hitTime γ α L :=
  le_iInf₂ fun t ht => by
    by_contra hlt
    exact h t (ENNReal.coe_le_coe.1 (not_le.1 hlt).le) ht

/-- **A finite first hit is a hit** (the values `−1/α(p)` form a closed set). -/
theorem hit_hitTime (hγc : Continuous γ) (hαc : ContinuousOn α (Icc 0 L)) (hT : hitTime γ α L < ⊤) :
    IsHit γ α L (hitTime γ α L).toNNReal := by
  set T := hitTime γ α L with hTdef
  set T' := T.toNNReal with hT'def
  have hTT : (T' : ℝ≥0∞) = T := ENNReal.coe_toNNReal hT.ne
  have hseq : ∀ m : ℕ, ∃ t : ℝ≥0, IsHit γ α L t ∧ t < T' + 1 / ((m : ℝ≥0) + 1) := by
    intro m
    have hlt : T < ((T' + 1 / ((m : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞) := by
      rw [← hTT, ENNReal.coe_lt_coe]
      exact lt_add_of_pos_right _ (by positivity)
    obtain ⟨t, ht⟩ := iInf_lt_iff.1 hlt
    obtain ⟨hh, ht'⟩ := iInf_lt_iff.1 ht
    exact ⟨t, hh, ENNReal.coe_lt_coe.1 ht'⟩
  choose ts hts hlt using hseq
  have hge : ∀ m, T' ≤ ts m := fun m => by
    have h := hitTime_le (hts m)
    rw [← hTdef, ← hTT] at h
    exact ENNReal.coe_le_coe.1 h
  have hlim : Tendsto ts atTop (𝓝 T') := by
    rw [← NNReal.tendsto_coe]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (h := fun m : ℕ => (T' : ℝ) + 1 / ((m : ℝ) + 1)) ?_ (fun m => by exact_mod_cast hge m) (fun m => ?_)
    · simpa only [add_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_add (T' : ℝ)
    · have h := NNReal.coe_lt_coe.2 (hlt m)
      push_cast at h
      exact h.le
  choose ps hps hne he using hts
  have hw : Tendsto (fun m => negInv (α (ps m))) atTop (𝓝 (γ T')) :=
    ((hγc.tendsto T').comp hlim).congr fun m => he m
  exact limit_hit hαc hps hne hw

/-- **The range clause of the relation, as countable tests.** -/
theorem range_iff_tests (hγc : Continuous γ) (hαc : ContinuousOn α (Icc 0 L)) (hβ : ∀ p : ℝ≥0, p ≤ L → β p = α p)
    {ℓ : ℝ≥0 → ℝ≥0} (hc : Continuous ℓ) (hm : StrictMono ℓ) (h0 : ℓ 0 = 0) :
    range ℓ = {s : ℝ≥0 | (s : ℝ≥0∞) < hitTime γ α L} ↔
      (∀ n : ℕ, ∃ k : ℕ, ∀ q p : ℚ≥0, (q : ℝ≥0) ≤ ℓ n → ((p : ℝ≥0) : ℝ≥0∞) ≤ (L : ℝ≥0∞) → β p ≠ 0 →
        (1 : ℝ) / ((k : ℝ) + 1) ≤ ‖γ q - negInv (β p)‖) ∧
      ((⨆ n : ℕ, (ℓ n : ℝ≥0∞)) < ⊤ → ∀ k : ℕ, ∃ p : ℚ≥0, ((p : ℝ≥0) : ℝ≥0∞) ≤ (L : ℝ≥0∞) ∧ β p ≠ 0 ∧
        ‖γ (⨆ n : ℕ, (ℓ n : ℝ≥0∞)).toNNReal - negInv (β p)‖ < (1 : ℝ) / ((k : ℝ) + 1)) := by
  rw [GW1Borel.range_clock_iff hc hm h0]
  constructor
  · rintro ⟨hlt, hS⟩
    refine ⟨fun n => (noHit_iff_rat hγc hαc hβ (ℓ n)).1 fun t ht =>
      not_hit_of_lt (lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht) (hlt n)), fun hfin => ?_⟩
    rw [hS] at hfin ⊢
    exact (hit_iff_rat hαc hβ _).1 (hit_hitTime hγc hαc hfin)
  · rintro ⟨h3, h4⟩
    have hno : ∀ n : ℕ, ∀ t ≤ ℓ n, ¬ IsHit γ α L t := fun n => (noHit_iff_rat hγc hαc hβ (ℓ n)).2 (h3 n)
    have hlt : ∀ n : ℕ, (ℓ n : ℝ≥0∞) < hitTime γ α L := fun n =>
      lt_of_lt_of_le (ENNReal.coe_lt_coe.2 (hm (Nat.cast_lt.2 (Nat.lt_succ_self n)))) (le_hitTime (hno (n + 1)))
    refine ⟨hlt, le_antisymm (iSup_le fun n => (hlt n).le) ?_⟩
    rcases lt_or_eq_of_le (le_top : (⨆ n : ℕ, (ℓ n : ℝ≥0∞)) ≤ ⊤) with hS | hS
    · have hh := (hit_iff_rat hαc hβ _).2 (h4 hS)
      calc hitTime γ α L ≤ (((⨆ n : ℕ, (ℓ n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ≥0∞) := hitTime_le hh
        _ = _ := ENNReal.coe_toNNReal hS.ne
    · rw [hS]
      exact le_top

end InteractingSLE.Theorem14.BW1Det
