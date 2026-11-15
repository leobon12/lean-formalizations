/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProb6Shift
import InteractingSLE.Spec.Sec7.ContinuityProb3Lift
import InteractingSLE.Spec.Sec2.JacobiExists

/-!
# §7.3: the two-seed ratio restart for weights `> −2`

Packet PROVE-SEC7-C6. Specification pp. 354–355 (Aux. lemma 106, the case `a, b > 0`) by the route of Astra's
follow-up note, §B.3 L1266–L1279 (ruling R38; additional note Lemma 1.7, R39: "This calculation and transfer use no
restriction on `κ`"): stop the two-seed law when `R/L = r`, normalize by a positive dilation, and transfer the
seed transience through the strong Markov restart.

ZhanGT4-B (`ZhanGT4.eq_zero_of_restart_ratio`, `ZhanGT4.codeLaw_nt_eq_zero_of_ratio`) proved this for admissible seed
weights (`ρ ≥ κ/2 − 2`), where the driver never meets a mark at positive times. For weights in `(−2, κ/2 − 2)` the
driver meets the marks; here only the separation `V^L < V^R` at positive times is used (at a time with `R = r L` and
`V^R − V^L > 0`, `L > 0`), the lifetime is infinite (`Sec2.Assembly2.ae_lifetime_eq_top_twoSeed`), the ratio is
recurrent (ZhanGT4's `ae_exists_ratio_lt` and the reflection, which only need weights `> −2`), and the seed trace with
its transience comes from the two-seed premise (`LP.IsCompleteForceWord` of the seed word, in the universe of the
statement: the canonical two-seed evolution is lifted to `ULift`).

## Main results

* `eq_zero_of_restart_ratio_sep`: ZhanGT4's restart with the separation of the marks in place of the separation of
  the driver from the left mark.
* `ae_exists_ratioGap_eq_zero`: recurrence of the two-seed gap ratio for weights `> −2`.
* **`codeLaw_nt_eq_zero_of_twoSeed`**: under the two-seed premise, the canonical probability of a non-transient trace
  is `0` at every strictly separated pair `(−L, R)`, `L, R > 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace Positive

open ZhanGT4 Sec7.RandRestart Sec2

/-! ### The restart at the ratio hitting time, with separated marks -/

section Restart

/-- The pathwise facts of a two-seed law used at the restart (weights `> −2`): infinite lifetime, continuity, the
separation `V^L < V^R` at positive times, a time `≥ 1` with `R = r L`, and a transient trace. -/
def GoodRatioSep {Ω : Type*} (r : ℝ) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (ω : Ω) : Prop :=
  ζ ω = ⊤ ∧ Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧ Continuous (fun t => VL 0 t ω) ∧
    Continuous (fun t => VR 0 t ω) ∧ (∀ t : ℝ≥0, 0 < t → VL 0 t ω < VR 0 t ω) ∧
    (∃ t : ℝ≥0, 1 ≤ t ∧ ratioGap r W VL VR t ω = 0) ∧ HasTrace (fun t => W t ω) ∧
    ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η → Tendsto (fun t => ‖η t‖) atTop atTop

variable {κ : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {ρL ρR : Fin 1 → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The strong Markov restart at the ratio hitting time** (B.3 L1273–L1276), with separated marks. For a two-seed
evolution (in a filtration where the null set `N` is measurable at every time) whose paths off `N` have the facts
`GoodRatioSep r`, `r > 0`, if the canonical probability of a non-transient trace is a constant `K` along the ray of
words `(−L, r L)`, `L > 0`, then `K = 0`. (The proof of `ZhanGT4.eq_zero_of_restart_ratio`, which assumed `V^L < W`.) -/
theorem eq_zero_of_restart_ratio_sep [IsProbabilityMeasure P] (hκ : 0 < κ)
    (hE : IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P 𝓖 W VL VR B ζ) {r : ℝ} (hr : 0 < r)
    {N : Set Ω} (hNm : ∀ t, MeasurableSet[𝓖 t] N) (hN0 : P N = 0)
    (hgood : ∀ ω ∉ N, GoodRatioSep r W VL VR ζ ω) {K : ℝ≥0∞}
    (hdil : ∀ L : ℝ, 0 < L → codeLaw κ ρL ρR ntCodeSet ((fun _ => -L), fun _ => r * L) = K) : K = 0 := by
  set Y := ratioGap r W VL VR with hY
  -- adaptedness of the processes defining the hitting time
  have hYa : AdaptedBefore 𝓖 ζ (posAfter Y) :=
    adaptedBefore_of_eq (fun t p => max ((p.2.2 - p.1) - r * (p.1 - p.2.1)) (1 - (t : ℝ)))
      (fun t => by fun_prop) hE.2.1 (hE.2.2.1 0) (hE.2.2.2.1 0) fun t ω => rfl
  have hYa' : AdaptedBefore 𝓖 ζ (posAfter (-Y)) :=
    adaptedBefore_of_eq (fun t p => max (-((p.2.2 - p.1) - r * (p.1 - p.2.1))) (1 - (t : ℝ)))
      (fun t => by fun_prop) hE.2.1 (hE.2.2.1 0) (hE.2.2.2.1 0) fun t ω => rfl
  have hZa : AdaptedBefore 𝓖 ζ (zeroProc (Ω := Ω)) :=
    adaptedBefore_of_eq (fun _ _ => 0) (fun _ => measurable_const) hE.2.1 (hE.2.2.1 0) (hE.2.2.2.1 0)
      fun _ _ => rfl
  have hYc : ∀ ω ∉ N, Continuous fun t => Y t ω := fun ω hω => by
    obtain ⟨-, hw, -, hl, hr', -⟩ := hgood ω hω
    exact (hr'.sub hw).sub (continuous_const.mul (hw.sub hl))
  have hT₁ := Sec7.isStoppingTime_firstMeet_off hZa hYa hNm fun ω hω =>
    continuousOn_posAfter_sub (hYc ω hω) _
  have hT₂ := Sec7.isStoppingTime_firstMeet_off hZa hYa' hNm fun ω hω =>
    continuousOn_posAfter_sub (Y := -Y) (hYc ω hω).neg _
  set Th : Ω → ℝ≥0∞ := fun ω => max (Sec7.zeroOn N (Sec7.firstMeet zeroProc (posAfter Y) ζ) ω)
    (Sec7.zeroOn N (Sec7.firstMeet zeroProc (posAfter (-Y)) ζ) ω) with hTh
  have hThs : IsStoppingTime 𝓖 fun ω => (Th ω : WithTop ℝ≥0) := hT₁.max hT₂
  have hhit : ∀ ω ∉ N, ∃ m : ℝ≥0, Th ω = m ∧ 1 ≤ m ∧ Y m ω = 0 := fun ω hω => by
    obtain ⟨hζ, -, -, -, -, -, ⟨t₀, ht₀, hz⟩, -⟩ := hgood ω hω
    have : Th ω = hitAfter Y ζ ω := by
      simp only [hTh, hitAfter, Sec7.zeroOn_of_notMem hω]
    rw [this]
    exact exists_hitAfter (hYc ω hω) hζ ht₀ hz
  -- the capped stopping times and the restart events
  set Tn : ℕ → Ω → ℝ≥0 := fun n ω => (min (Th ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal with hTn
  have hTn_coe : ∀ n ω, ((Tn n ω : ℝ≥0) : ℝ≥0∞) = min (Th ω) ((n : ℝ≥0) : ℝ≥0∞) := fun n ω =>
    ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))
  have hTns : ∀ n, IsStoppingTime 𝓖 fun ω => ((Tn n ω : ℝ≥0) : WithTop ℝ≥0) := fun n => by
    have h := hThs.min_const (n : ℝ≥0)
    have he : (fun ω => ((Tn n ω : ℝ≥0) : WithTop ℝ≥0)) = fun ω => min (Th ω : WithTop ℝ≥0) (n : ℝ≥0) :=
      funext fun ω => hTn_coe n ω
    rw [he]; exact h
  set A : ℕ → Set Ω := fun n => Nᶜ ∩ {ω | Th ω < ((n : ℝ≥0) : ℝ≥0∞)} with hA
  have hTnA : ∀ n, ∀ ω ∈ A n, ((Tn n ω : ℝ≥0) : ℝ≥0∞) = Th ω := fun n ω hω => by
    rw [hTn_coe]; exact min_eq_left hω.2.le
  have hAm : ∀ n, MeasurableSet[(hTns n).measurableSpace] (A n) := by
    intro n
    have key : ∀ i : ℝ≥0, MeasurableSet[𝓖 i] (A n ∩ {ω | ((Tn n ω : ℝ≥0) : WithTop ℝ≥0) ≤ i}) := by
      intro i
      have heq : A n ∩ {ω | ((Tn n ω : ℝ≥0) : WithTop ℝ≥0) ≤ i} =
          Nᶜ ∩ ({ω | Th ω < ((n : ℝ≥0) : ℝ≥0∞)} ∩ {ω | Th ω ≤ (i : ℝ≥0∞)}) := by
        ext ω
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          refine ⟨h1, h2, ?_⟩
          have h3' : ((Tn n ω : ℝ≥0) : ℝ≥0∞) ≤ i := h3
          rwa [hTnA n ω ⟨h1, h2⟩] at h3'
        · rintro ⟨h1, h2, h3⟩
          refine ⟨⟨h1, h2⟩, ?_⟩
          show ((Tn n ω : ℝ≥0) : ℝ≥0∞) ≤ i
          rw [hTnA n ω ⟨h1, h2⟩]; exact h3
      rw [heq]
      refine (hNm i).compl.inter ?_
      rcases lt_or_ge i (n : ℝ≥0) with hin | hni
      · have he : {ω | Th ω < ((n : ℝ≥0) : ℝ≥0∞)} ∩ {ω | Th ω ≤ (i : ℝ≥0∞)} = {ω | Th ω ≤ (i : ℝ≥0∞)} := by
          refine inter_eq_right.2 fun ω (hω : Th ω ≤ i) => ?_
          exact lt_of_le_of_lt hω (by exact_mod_cast hin)
        rw [he]; exact hThs i
      · have he : {ω | Th ω < ((n : ℝ≥0) : ℝ≥0∞)} ∩ {ω | Th ω ≤ (i : ℝ≥0∞)} = {ω | Th ω < ((n : ℝ≥0) : ℝ≥0∞)} := by
          refine inter_eq_left.2 fun ω (hω : Th ω < (n : ℝ≥0)) => ?_
          exact le_trans hω.le (by exact_mod_cast hni)
        rw [he]; exact 𝓖.mono hni _ (hThs.measurableSet_lt (n : ℝ≥0))
    refine ((hTns n).measurableSet _).2 ⟨?_, key⟩
    have h := key (n : ℝ≥0)
    have hsub : A n ∩ {ω | ((Tn n ω : ℝ≥0) : WithTop ℝ≥0) ≤ ((n : ℝ≥0) : WithTop ℝ≥0)} = A n :=
      inter_eq_left.2 fun ω _ => by
        show ((Tn n ω : ℝ≥0) : ℝ≥0∞) ≤ ((n : ℝ≥0) : ℝ≥0∞)
        rw [hTn_coe]; exact min_le_right _ _
    rw [hsub] at h
    exact le_iSup (fun t => 𝓖 t) (n : ℝ≥0) _ h
  have hAT : ∀ n, ∀ ω ∈ A n, ((Tn n ω : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
      (0 < Tn n ω ∨ ∀ i j, (fun _ : Fin 1 => (0 : ℝ)) i < (fun _ : Fin 1 => (0 : ℝ)) j) := fun n ω hω => by
    obtain ⟨hζ, -⟩ := hgood ω hω.1
    obtain ⟨m, hm, hm1, -⟩ := hhit ω hω.1
    refine ⟨by rw [hζ]; exact ENNReal.coe_lt_top, Or.inl ?_⟩
    have hTm : Tn n ω = m := by exact_mod_cast (hTnA n ω hω).trans hm
    rw [hTm]; exact lt_of_lt_of_le one_pos hm1
  -- the restart formula
  have hlaw := fun n => measure_restart_codeEvent hκ hE (hTns n) (hAm n) (hAT n)
    (Φ := NonTransientEvent) measurableSet_ntCodeSet (fun _ _ _ => Iff.rfl) nonTransientEvent_congr
  -- the future has no non-transient trace
  have hLHS : ∀ n, A n ∩ {ω | NonTransientEvent (fun t => W (Tn n ω + t) ω - W (Tn n ω) ω)
      (ζ ω - Tn n ω)} = ∅ := by
    intro n
    refine eq_empty_iff_forall_notMem.2 fun ω ⟨hω, hnt⟩ => ?_
    obtain ⟨hζ, hwc, hw0, -, -, -, -, ⟨η, hη⟩, htr⟩ := hgood ω hω.1
    have hζ' : ζ ω - Tn n ω = ⊤ := by rw [hζ]; exact ENNReal.top_sub_coe
    have hnt' : NonTransientEvent (Sec7.shiftNN (fun t => W t ω) (Tn n ω)) ⊤ := by
      rw [← hζ']; exact hnt
    have hwc₂ : Continuous (Sec7.shiftNN (fun t => W t ω) (Tn n ω)) :=
      (hwc.comp (continuous_const.add continuous_id)).sub continuous_const
    rw [nonTransientEvent_iff hwc₂ (Sec7.shiftNN_zero _ _)] at hnt'
    obtain ⟨⟨η₂, hη₂⟩, hnot⟩ := hnt'
    exact hnot ⟨η₂, hη₂, tendsto_norm_of_shift hwc hw0 hη (htr η hη) hη₂⟩
  -- the restarted word lies on the ray
  have hRHS : ∀ n, ∫⁻ ω in A n, codeLaw κ ρL ρR ntCodeSet (wordAt W VL VR (Tn n) ω) ∂P = K * P (A n) := by
    intro n
    have hAmeas : MeasurableSet (A n) := (hTns n).measurableSpace_le _ (hAm n)
    rw [← setLIntegral_const]
    refine setLIntegral_congr_fun hAmeas fun ω hω => ?_
    obtain ⟨-, -, -, -, -, hsep, -⟩ := hgood ω hω.1
    obtain ⟨m, hm, hm1, hYm⟩ := hhit ω hω.1
    have hTm : Tn n ω = m := by exact_mod_cast (hTnA n ω hω).trans hm
    have hYm' : VR 0 m ω - W m ω = r * (W m ω - VL 0 m ω) := by
      simp only [hY, ratioGap] at hYm; linarith
    have hL : 0 < W m ω - VL 0 m ω := by
      by_contra hle
      push Not at hle
      have h1 := hsep m (lt_of_lt_of_le one_pos hm1)
      have h2 : r * (W m ω - VL 0 m ω) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr.le hle
      linarith
    have hword : wordAt W VL VR (Tn n) ω =
        ((fun _ => -(W m ω - VL 0 m ω)), fun _ => r * (W m ω - VL 0 m ω)) := by
      simp only [wordAt, hTm]
      refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
      · rw [Fin.fin_one_eq_zero i]; simp only; ring
      · rw [Fin.fin_one_eq_zero j]; exact hYm'
    rw [hword, hdil _ hL]
  have hzero : ∀ n, K * P (A n) = 0 := fun n => by
    rw [← hRHS n, ← hlaw n, hLHS n, measure_empty]
  -- some restart event has positive probability
  have hcover : Nᶜ ⊆ ⋃ n, A n := fun ω hω => by
    obtain ⟨m, hm, -, -⟩ := hhit ω hω
    obtain ⟨n, hn⟩ := exists_nat_gt (m : ℝ)
    refine mem_iUnion.2 ⟨n, hω, ?_⟩
    show Th ω < ((n : ℝ≥0) : ℝ≥0∞)
    rw [hm]
    exact_mod_cast (show m < (n : ℝ≥0) by rw [← NNReal.coe_lt_coe]; exact_mod_cast hn)
  by_contra hK
  have hA0 : ∀ n, P (A n) = 0 := fun n => (mul_eq_zero.1 (hzero n)).resolve_left hK
  have h0 : P Nᶜ = 0 := measure_mono_null hcover (measure_iUnion_null hA0)
  have h1 : P Nᶜ = 1 := by
    rw [prob_compl_eq_one_sub (𝓖.le 0 _ (hNm 0)), hN0, tsub_zero]
  rw [h0] at h1
  exact zero_ne_one h1

end Restart

/-! ### Recurrence of the gap ratio for weights `> −2` -/

section Recurrence

variable {κ : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {ρL ρR : Fin 1 → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **Recurrence of the two-seed gap ratio** (B.3 (E13)) for weights `> −2` and infinite lifetime: for every `r > 0`,
almost surely `R_t = r L_t` at some time `t ≥ 1` (the proof of `ZhanGT4.twoSeedRatioRecurrenceStatement`, whose
admissibility hypothesis served only to give the infinite lifetime). -/
theorem ae_exists_ratioGap_eq_zero [IsProbabilityMeasure P] (hκ : 0 < κ) (hρL : -2 < ρL 0) (hρR : -2 < ρR 0)
    (hE : IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P 𝓕 W VL VR B ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∃ t : ℝ≥0, 1 ≤ t ∧ ratioGap r W VL VR t ω = 0 := by
  -- the reflected evolution is a two-seed evolution with the weights exchanged
  have hEr := hE.reflect
  have hz : -(fun _ : Fin 1 => (0 : ℝ)) = fun _ => 0 := by funext i; simp
  rw [hz] at hEr
  have hlt := ae_exists_ratio_lt hκ hρL hρR hE hζ hr
  have hgt := ae_exists_ratio_lt hκ hρR hρL hEr hζ (inv_pos.2 hr)
  filter_upwards [hlt, hgt, hE.2.2.2.2, hζ] with ω ⟨t₁, ht₁, h₁⟩ ⟨t₂, ht₂, h₂⟩ hp hζω
  -- `h₂ : (−V_L) − (−W) < r⁻¹ ((−W) − (−V_R))`, i.e. `r L < R`
  simp only [Pi.neg_apply] at h₂
  have h₂' : r * (W t₂ ω - VL 0 t₂ ω) < VR 0 t₂ ω - W t₂ ω := by
    have := mul_lt_mul_of_pos_left h₂ hr
    rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] at this
    linarith
  -- intermediate values of `R − r L`
  have hcont : ∀ {f : ℝ≥0 → ℝ}, ContinuousOn f {t | (t : ℝ≥0∞) < ζ ω} → Continuous f := fun hf =>
    continuousOn_univ.1 (hf.mono fun t _ => by
      show (t : ℝ≥0∞) < ζ ω
      rw [hζω]; exact ENNReal.coe_lt_top)
  have hY : Continuous fun t : ℝ≥0 => (VR 0 t ω - W t ω) - r * (W t ω - VL 0 t ω) :=
    ((hcont (hp.2.2.2.2.2.1 0)).sub (hcont hp.2.2.2.1)).sub
      (continuous_const.mul ((hcont hp.2.2.2.1).sub (hcont (hp.2.2.2.2.1 0))))
  have hY₁ : (VR 0 t₁ ω - W t₁ ω) - r * (W t₁ ω - VL 0 t₁ ω) ≤ 0 := by linarith
  have hY₂ : 0 ≤ (VR 0 t₂ ω - W t₂ ω) - r * (W t₂ ω - VL 0 t₂ ω) := by linarith
  rcases le_total t₁ t₂ with h12 | h21
  · obtain ⟨t, ht, hYt⟩ := intermediate_value_Icc h12 hY.continuousOn ⟨hY₁, hY₂⟩
    exact ⟨t, ht₁.trans ht.1, by simp only [ratioGap]; linarith⟩
  · obtain ⟨t, ht, hYt⟩ := intermediate_value_Icc' h21 hY.continuousOn ⟨hY₁, hY₂⟩
    exact ⟨t, ht₂.trans ht.1, by simp only [ratioGap]; linarith⟩

end Recurrence

end Positive

end Sec7

end InteractingSLE
