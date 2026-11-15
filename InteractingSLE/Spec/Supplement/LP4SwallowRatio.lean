/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.LP4SwallowEvent
import InteractingSLE.Spec.ZhanGT4.TwoForceRecur

/-!
# LP4's right swallowing: the restart at the gap-ratio hitting time

Packet PROVE-LP18. Specification p. 482: "After the first `D = 1` level, wait for a right-seed collision … Map out,
center, and divide by `D`." Instead of waiting for a collision we restart at the first time `T ≥ 1` at which the gap
ratio `R/L` (`L = W − V^L`, `R = V^R − W`) equals a prescribed `r > 0`; the restarted word is `L_T · (−1, r)`, a
positive multiple of the fixed separated word `(−1, r)`, so for an event whose canonical probability is constant along
that ray the restart formula gives a deterministic factor.

* `ae_exists_ratio_eq`: for every two-seed evolution with weights `> −2` (any `κ > 0`) and every `r > 0`, almost surely
  `R_t = r L_t` at some time `t ≥ 1` (the proof of `ZhanGT4.twoSeedRatioRecurrenceStatement` without its
  admissibility hypothesis, which is only used there for the lifetime; here the lifetime is infinite by
  `Sec2.Assembly2.ae_lifetime_eq_top_twoSeed`);
* `exists_ratio_restart`: for a start-dependent code event `Φ` whose canonical probability is `K` along the ray
  `(−L, r L)`, `L > 0`, an event `A` of positive probability and a time `T ≥ 1` with
  `P(A ∩ {Φ(restarted at T)}) = K · P(A)`, on which the path is good.

The stopping time and the restart events are those of `ZhanGT4.eq_zero_of_restart_ratio` (PROVE-ZHAN-GT4-B).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.LP.LP4S

open QuantumZipper Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart ZhanGT4

variable {κ : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {ρL ρR : Fin 1 → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The gap ratio of the two-seed law hits every level after time `1`** (weights `> −2`, every `κ > 0`). -/
theorem ae_exists_ratio_eq [IsProbabilityMeasure P] (hκ : 0 < κ) (hρL : -2 < ρL 0) (hρR : -2 < ρR 0)
    (hE : IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P 𝓕 W VL VR B ζ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∃ t : ℝ≥0, 1 ≤ t ∧ VR 0 t ω - W t ω = r * (W t ω - VL 0 t ω) := by
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := Sec2.Assembly2.ae_lifetime_eq_top_twoSeed hκ hE hρL hρR
  have hEr := hE.reflect
  have hz : -(fun _ : Fin 1 => (0 : ℝ)) = fun _ => 0 := by funext i; simp
  rw [hz] at hEr
  have hlt := ae_exists_ratio_lt hκ hρL hρR hE hζ hr
  have hgt := ae_exists_ratio_lt hκ hρR hρL hEr hζ (inv_pos.2 hr)
  filter_upwards [hlt, hgt, hE.2.2.2.2, hζ] with ω ⟨t₁, ht₁, h₁⟩ ⟨t₂, ht₂, h₂⟩ hp hζω
  simp only [Pi.neg_apply] at h₂
  have h₂' : r * (W t₂ ω - VL 0 t₂ ω) < VR 0 t₂ ω - W t₂ ω := by
    have := mul_lt_mul_of_pos_left h₂ hr
    rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] at this
    linarith
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
    exact ⟨t, ht₁.trans ht.1, by linarith⟩
  · obtain ⟨t, ht, hYt⟩ := intermediate_value_Icc' h21 hY.continuousOn ⟨hY₁, hY₂⟩
    exact ⟨t, ht₂.trans ht.1, by linarith⟩

/-- The pathwise facts used at the ratio restart. -/
def GoodR (κ : ℝ) (ρL ρR : Fin 1 → ℝ) (r : ℝ) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : Prop :=
  ζ ω = ⊤ ∧ IsIntegratedSLEPath κ (fun _ => 0) (fun _ => 0) ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
    (fun i t => VR i t ω) (fun t => B t ω) ⊤ ∧ ∃ t : ℝ≥0, 1 ≤ t ∧ ratioGap r W VL VR t ω = 0

/-- **The restart at the ratio hitting time.** For a two-seed evolution (weights `> −2`), `r > 0`, and a
start-dependent code event `Φ` whose canonical probability is `K` along the ray of words `(−L, r L)`, `L > 0`, there
are an event `A` of positive probability and a time `T ≥ 1` (a stopping time of the usual augmentation) with
`P(A ∩ {Φ(V_T − W_T, W_{T+·} − W_T, ζ − T)}) = K · P(A)`; on `A` the path is good (infinite lifetime, Definition
2.1). -/
theorem exists_ratio_restart [IsProbabilityMeasure P] (hκ : 0 < κ) (hρL : -2 < ρL 0) (hρR : -2 < ρR 0)
    (hE : IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P 𝓕 W VL VR B ζ) {r : ℝ} (hr : 0 < r)
    {Φ : (Fin 1 → ℝ) × (Fin 1 → ℝ) → (ℝ≥0 → ℝ) → ℝ≥0∞ → Prop} {S : Set (XCode 1 1)} (hS : MeasurableSet S)
    (hSΦ : ∀ x ∈ CRelF κ ρL ρR, HasLimW x → (x ∈ S ↔ Φ (startOf x) (cw x) (cζ x)))
    (hΦ : ∀ (s : (Fin 1 → ℝ) × (Fin 1 → ℝ)) (w w' : ℝ≥0 → ℝ) (τ : ℝ≥0∞),
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t) → Φ s w τ → Φ s w' τ)
    {K : ℝ≥0∞} (hdil : ∀ L : ℝ, 0 < L → codeLaw κ ρL ρR S ((fun _ => -L), fun _ => r * L) = K) :
    ∃ (A : Set Ω) (T : Ω → ℝ≥0), MeasurableSet A ∧ P A ≠ 0 ∧
      P (A ∩ {ω | Φ (wordAt W VL VR T ω) (fun t => W (T ω + t) ω - W (T ω) ω) (ζ ω - T ω)}) = K * P A ∧
      ∀ ω ∈ A, 1 ≤ T ω ∧ GoodR κ ρL ρR r W VL VR B ζ ω := by
  have hEa := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  set 𝓖 := usualAugmentation 𝓕 P with h𝓖
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := Sec2.Assembly2.ae_lifetime_eq_top_twoSeed hκ hE hρL hρR
  have hgood : ∀ᵐ ω ∂P, GoodR κ ρL ρR r W VL VR B ζ ω := by
    filter_upwards [hζ, hE.2.2.2.2, ae_exists_ratio_eq hκ hρL hρR hE hr] with ω hζω hp ⟨t₀, ht₀, hz⟩
    rw [hζω] at hp
    refine ⟨hζω, hp, t₀, ht₀, ?_⟩
    simp only [ratioGap]
    linarith
  obtain ⟨N, hNsub, hNm', hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hNm : ∀ t, MeasurableSet[𝓖 t] N := fun t => Ito.measurableSet_usualAugmentation_of_null hNm' hN0 t
  have hgoodN : ∀ ω ∉ N, GoodR κ ρL ρR r W VL VR B ζ ω := fun ω hω => by
    by_contra h
    exact hω (hNsub h)
  set Y := ratioGap r W VL VR with hY
  have hYa : AdaptedBefore 𝓖 ζ (posAfter Y) :=
    adaptedBefore_of_eq (fun t p => max ((p.2.2 - p.1) - r * (p.1 - p.2.1)) (1 - (t : ℝ)))
      (fun t => by fun_prop) hEa.2.1 (hEa.2.2.1 0) (hEa.2.2.2.1 0) fun t ω => rfl
  have hYa' : AdaptedBefore 𝓖 ζ (posAfter (-Y)) :=
    adaptedBefore_of_eq (fun t p => max (-((p.2.2 - p.1) - r * (p.1 - p.2.1))) (1 - (t : ℝ)))
      (fun t => by fun_prop) hEa.2.1 (hEa.2.2.1 0) (hEa.2.2.2.1 0) fun t ω => rfl
  have hZa : AdaptedBefore 𝓖 ζ (zeroProc (Ω := Ω)) :=
    adaptedBefore_of_eq (fun _ _ => 0) (fun _ => measurable_const) hEa.2.1 (hEa.2.2.1 0) (hEa.2.2.2.1 0)
      fun _ _ => rfl
  have hcontω : ∀ ω ∉ N, Continuous (fun t => W t ω) ∧ Continuous (fun t => VL 0 t ω) ∧
      Continuous (fun t => VR 0 t ω) := fun ω hω => by
    obtain ⟨-, hp, -⟩ := hgoodN ω hω
    have hcont : ∀ {f : ℝ≥0 → ℝ}, ContinuousOn f {t | (t : ℝ≥0∞) < ⊤} → Continuous f := fun hf =>
      continuousOn_univ.1 (hf.mono fun t _ => ENNReal.coe_lt_top)
    exact ⟨hcont hp.2.2.2.1, hcont (hp.2.2.2.2.1 0), hcont (hp.2.2.2.2.2.1 0)⟩
  have hYc : ∀ ω ∉ N, Continuous fun t => Y t ω := fun ω hω => by
    obtain ⟨hw, hl, hr'⟩ := hcontω ω hω
    exact (hr'.sub hw).sub (continuous_const.mul (hw.sub hl))
  have hT₁ := Sec7.isStoppingTime_firstMeet_off hZa hYa hNm fun ω hω =>
    continuousOn_posAfter_sub (hYc ω hω) _
  have hT₂ := Sec7.isStoppingTime_firstMeet_off hZa hYa' hNm fun ω hω =>
    continuousOn_posAfter_sub (Y := -Y) (hYc ω hω).neg _
  set Th : Ω → ℝ≥0∞ := fun ω => max (Sec7.zeroOn N (Sec7.firstMeet zeroProc (posAfter Y) ζ) ω)
    (Sec7.zeroOn N (Sec7.firstMeet zeroProc (posAfter (-Y)) ζ) ω) with hTh
  have hThs : IsStoppingTime 𝓖 fun ω => (Th ω : WithTop ℝ≥0) := hT₁.max hT₂
  have hhit : ∀ ω ∉ N, ∃ m : ℝ≥0, Th ω = m ∧ 1 ≤ m ∧ Y m ω = 0 := fun ω hω => by
    obtain ⟨hζω, -, ⟨t₀, ht₀, hz⟩⟩ := hgoodN ω hω
    have : Th ω = hitAfter Y ζ ω := by
      simp only [hTh, hitAfter, Sec7.zeroOn_of_notMem hω]
    rw [this]
    exact exists_hitAfter (hYc ω hω) hζω ht₀ hz
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
      · have he : {ω | Th ω < ((n : ℝ≥0) : ℝ≥0∞)} ∩ {ω | Th ω ≤ (i : ℝ≥0∞)} =
            {ω | Th ω < ((n : ℝ≥0) : ℝ≥0∞)} := by
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
  have hTnm : ∀ n, ∀ ω ∈ A n, ∃ m : ℝ≥0, Tn n ω = m ∧ 1 ≤ m ∧ Y m ω = 0 := fun n ω hω => by
    obtain ⟨m, hm, hm1, hYm⟩ := hhit ω hω.1
    exact ⟨m, by exact_mod_cast (hTnA n ω hω).trans hm, hm1, hYm⟩
  have hAT : ∀ n, ∀ ω ∈ A n, ((Tn n ω : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
      (0 < Tn n ω ∨ ∀ i j, (fun _ : Fin 1 => (0 : ℝ)) i < (fun _ : Fin 1 => (0 : ℝ)) j) := fun n ω hω => by
    obtain ⟨hζω, -⟩ := hgoodN ω hω.1
    obtain ⟨m, hm, hm1, -⟩ := hTnm n ω hω
    refine ⟨by rw [hζω]; exact ENNReal.coe_lt_top, Or.inl ?_⟩
    rw [hm]; exact lt_of_lt_of_le one_pos hm1
  have hlaw := fun n => measure_restart_codeEventS hκ hEa (hTns n) (hAm n) (hAT n) hS hSΦ hΦ
  -- the restarted word lies on the ray
  have hRHS : ∀ n, ∫⁻ ω in A n, codeLaw κ ρL ρR S (wordAt W VL VR (Tn n) ω) ∂P = K * P (A n) := by
    intro n
    have hAmeas : MeasurableSet (A n) := (hTns n).measurableSpace_le _ (hAm n)
    rw [← setLIntegral_const]
    refine setLIntegral_congr_fun hAmeas fun ω hω => ?_
    obtain ⟨-, hp, -⟩ := hgoodN ω hω.1
    obtain ⟨m, hm, hm1, hYm⟩ := hTnm n ω hω
    have hsepm := Sec2.TwoSeed.sepN_pos hp (ENNReal.coe_lt_top (r := m)) (lt_of_lt_of_le one_pos hm1)
    simp only [Sec2.TwoSeed.sepN] at hsepm
    have hYm' : VR 0 m ω - W m ω = r * (W m ω - VL 0 m ω) := by
      simp only [hY, ratioGap] at hYm; linarith
    have hL : 0 < W m ω - VL 0 m ω := by
      by_contra hle
      push Not at hle
      nlinarith
    have hword : wordAt W VL VR (Tn n) ω =
        ((fun _ => -(W m ω - VL 0 m ω)), fun _ => r * (W m ω - VL 0 m ω)) := by
      simp only [wordAt, hm]
      refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
      · rw [Fin.fin_one_eq_zero i]; simp only; ring
      · rw [Fin.fin_one_eq_zero j]; exact hYm'
    rw [hword, hdil _ hL]
  -- some restart event has positive probability
  have hcover : Nᶜ ⊆ ⋃ n, A n := fun ω hω => by
    obtain ⟨m, hm, -, -⟩ := hhit ω hω
    obtain ⟨n, hn⟩ := exists_nat_gt (m : ℝ)
    refine mem_iUnion.2 ⟨n, hω, ?_⟩
    show Th ω < ((n : ℝ≥0) : ℝ≥0∞)
    rw [hm]
    exact_mod_cast (show m < (n : ℝ≥0) by rw [← NNReal.coe_lt_coe]; exact_mod_cast hn)
  have hpos : ∃ n, P (A n) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 : P Nᶜ = 0 := measure_mono_null hcover (measure_iUnion_null hcon)
    have h1 : P Nᶜ = 1 := by rw [prob_compl_eq_one_sub hNm', hN0, tsub_zero]
    rw [h0] at h1
    exact zero_ne_one h1
  obtain ⟨n, hn⟩ := hpos
  refine ⟨A n, Tn n, (hTns n).measurableSpace_le _ (hAm n), hn, ?_, fun ω hω => ?_⟩
  · rw [hlaw n, hRHS n]
  · obtain ⟨m, hm, hm1, -⟩ := hTnm n ω hω
    exact ⟨hm ▸ hm1, hgoodN ω hω.1⟩

end InteractingSLE.LP.LP4S
