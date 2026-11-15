/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A2Part1Girsanov
import InteractingSLE.Spec.ZhanGT4.A2Part1Exit
import InteractingSLE.Spec.Sec5.Prop49QExitAux22

/-!
# A.2, part 1: the simple trace with its endpoint beyond the last left mark

Packet PROVE-ZHAN-A2P1. Source: Astra, *Follow-up proofs*, §A.2 L524–L536. In the reflected chart (the span
`(x₂, p₂)` of the source becomes the left span beyond the last left mark), for an integrated `SLE_k(ρ)` evolution,
`0 < k ≤ 4`, of an ordered word with one right mark, strictly ordered left marks, the last one `x^{L,last} < 0` carrying
the only non-admissible weight, and Zhan's strip conditions (3.3) on the image strip word:

* part 1's noncollision and simple trace before `ζ` (`ae_noncollision_simpleTrace`, A2Part1Girsanov);
* at a positive rational time `q < ζ` the restarted word is strictly separated, so the restarted code is in
  PROVE-GLUECOND9's `exitCode` (`ae_restart_mem`, `codeLaw_compl_exitCode_eq_zero`): the restarted driver has a left
  strip end — a trace converging at a finite time `S` to a real point `y` left of the restarted last mark;
* the pathwise exit (`exit_of_restart`) gives `ζ = q + S < ∞` and the convergence of the trace to `F̄_q(y)`, a real
  point left of `x^{L,last}` (`exists_extendFrom_eq_lt_last`).

## Main result

* **`ae_exit_trace`**: almost surely `0 < ζ < ∞` and there is a generating trace `η` on `[0, ζ]` (continuous up to and
  including `ζ`), injective on `[0, ζ]`, in `ℍ` on `(0, ζ)`, whose endpoint `η(ζ)` is a real point left of
  `x^{L,last}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4.A2P1

open QuantumZipper (H Hbar fwdMapInv)
open Sec2 Sec2.Assembly Sec7.RandRestart Sec5.Prop49Exit

variable {k : ℝ} {j : ℕ} {xL : Fin (j + 1) → ℝ} {xR : Fin 1 → ℝ} {ρL ρL' : Fin (j + 1) → ℝ}
  {ρR : Fin 1 → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin (j + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **The restarted word at a positive time is strictly separated** (part 1's noncollision and strictly ordered
initial left marks). -/
theorem strictStart_wordAt {w : ℝ≥0 → ℝ} {vL : Fin (j + 1) → ℝ≥0 → ℝ} {vR : Fin 1 → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
    {ζ₀ : ℝ≥0∞} (hp : IsIntegratedSLEPath k xL xR ρL ρR w vL vR b ζ₀) (hF : IsOrderedForceWord xL xR)
    (hxL : StrictAnti xL)
    (hsep : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < ζ₀ → (∀ i, vL i t < w t) ∧ ∀ i, w t < vR i t)
    {q : ℝ≥0} (hq0 : 0 < q) (hqζ : (q : ℝ≥0∞) < ζ₀) :
    StrictStart ((fun i => vL i q - w q), fun i => vR i q - w q) := by
  have hfp := hp.isForcePath
  refine ⟨fun i i' hii' => ?_, fun i => sub_neg.2 ((hsep q hq0 hqζ).1 i), fun a b hab => ?_,
    fun i => sub_pos.2 ((hsep q hq0 hqζ).2 i)⟩
  · refine sub_lt_sub_right (hfp.vL_lt_vL_of_lt hqζ (hxL hii') fun r hr => ?_) _
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ r) with h | h
    · rw [← h, hfp.vL_zero, hfp.w_zero]
      exact (hxL hii').trans_le (hF.2.1 i)
    · exact (hsep r h (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) hqζ)).1 i'
  · exact absurd hab (by rw [Subsingleton.elim a b]; exact lt_irrefl b)

/-- The rational positive restart times are `𝓕_q`-events. -/
theorem measurableSet_lt_lifetime_const (hE : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (q : ℝ≥0) :
    MeasurableSet[(isStoppingTime_const 𝓕 q).measurableSpace] {ω | (q : ℝ≥0∞) < ζ ω} := by
  rw [IsStoppingTime.measurableSpace_const]
  simpa using hE.2.1 q univ MeasurableSet.univ

/-- **A.2, part 1, in the reflected chart: the simple trace with its endpoint beyond the last left mark.** For an
integrated `SLE_k(ρ)` evolution, `0 < k ≤ 4`, of an ordered word with one right mark and strictly ordered left marks,
whose last left mark `x^{L,last} < 0` carries the only non-admissible weight, with every proper left prefix and the
right weight above `−2`, total left weight at most `−2`, and Zhan's strip conditions (3.3) on the image strip word:
almost surely `0 < ζ < ∞` and there is a generating trace `η` on `[0, ζ]`, injective on `[0, ζ]`, in `ℍ` on `(0, ζ)`,
whose endpoint `η(ζ)` is a real point left of `x^{L,last}`. -/
theorem ae_exit_trace (hk : 0 < k) (hk4 : k ≤ 4) (hF : IsOrderedForceWord xL xR) (hxL : StrictAnti xL)
    (hlast : xL (Fin.last j) < 0) (hρ' : ∀ i, i ≠ Fin.last j → ρL' i = ρL i)
    (hadm : Sec4.HasAdmissiblePartialSums k ρL' ρR xL xR) (hsum : ∑ i, ρL i ≤ -2)
    (hpreL : ∀ m : Fin (j + 1), m ≠ Fin.last j → -2 < ∑ i ∈ Finset.Iic m, ρL i)
    (hpreR : ∀ m : Fin 1, -2 < ∑ i ∈ Finset.Iic m, ρR i)
    (hpre : Strip.HasStripPrefixSums k (Fin.init ρL) ρR)
    (hq : |Strip.chargePlus k (Fin.init ρL) ρR (ρL (Fin.last j)) -
      Strip.chargeMinus (Fin.init ρL) (ρL (Fin.last j))| < 2)
    (hE : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, 0 < ζ ω ∧ ζ ω ≠ ⊤ ∧ ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
      InjOn η {t | (t : ℝ≥0∞) ≤ ζ ω} ∧ (∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < ζ ω → η t ∈ H) ∧
      ∃ x : ℝ, x < xL (Fin.last j) ∧ η (ζ ω).toNNReal = x := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hG := ae_noncollision_simpleTrace hk hk4 hF hlast hρ' hadm hsum hpreL hpreR hE
  set S : Set (XCode (j + 1) 1) := exitCode k ρL ρR fun s => s.1 (Fin.last j) with hS
  have hSm : MeasurableSet S := measurableSet_exitCode (by fun_prop)
  have hR : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 < q → (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω →
      ∃ x : XCode (j + 1) 1, x ∈ CRel k (wordAt W VL VR (fun _ => (q : ℝ).toNNReal) ω).1
          (wordAt W VL VR (fun _ => (q : ℝ).toNNReal) ω).2 ρL ρR ∧ x ∈ S ∧
        cζ x = ζ ω - ((q : ℝ).toNNReal : ℝ≥0∞) ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω - ((q : ℝ).toNNReal : ℝ≥0∞) →
          cw x t = W ((q : ℝ).toNNReal + t) ω - W ((q : ℝ).toNNReal) ω := by
    rw [ae_all_iff]
    intro q
    by_cases hq0 : 0 < q
    · have hq0' : 0 < (q : ℝ).toNNReal := Real.toNNReal_pos.2 (by exact_mod_cast hq0)
      have h := ae_restart_mem hk hE (isStoppingTime_const 𝓕 (q : ℝ).toNNReal)
        (measurableSet_lt_lifetime_const hE _) (fun ω hω => ⟨hω, hq0'⟩) hSm
        (fun s hsep hord => codeLaw_compl_exitCode_eq_zero hk hk4 hpre hq s hsep hord)
      filter_upwards [h] with ω hω _ hqζ using hω hqζ
    · exact Eventually.of_forall fun ω h => absurd h hq0
  filter_upwards [hG, hR, hE.2.2.2.2] with ω ⟨hζ0, hsep, hgen, hinj, hH⟩ hRω hp
  have hfp := hp.isForcePath
  set γ : ℝ≥0 → ℂ := fun t => LP.traceAt t (fun r => W r ω) with hγ
  -- a positive rational restart time
  obtain ⟨q, -, hq0, hqζ⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hζ0
  have hq'0 : 0 < (q : ℝ).toNNReal := by exact_mod_cast hq0
  have hqpos : 0 < q := by exact_mod_cast Real.toNNReal_pos.1 hq'0
  set q' : ℝ≥0 := (q : ℝ).toNNReal with hq'
  obtain ⟨x, hxC, hxS, hxζ, hxw⟩ := hRω q hqpos hqζ
  have hstrict : StrictStart (wordAt W VL VR (fun _ => q') ω) :=
    strictStart_wordAt hp hF hxL hsep hq'0 hqζ
  obtain ⟨Sx, y, hend⟩ := (mem_exitCode_iff hstrict hxC).1 hxS
  have hcp := hxC.1.2.2.isForcePath
  have hγIcc : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ ω → Sec7.IsGeneratingTraceIcc (fun t => W t ω) s γ := by
    intro s hs
    obtain ⟨s', hss', hs'ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs
    exact Sec7.IsGeneratingTrace.isGeneratingTraceIcc (hgen s' hs'ζ)
      (hfp.continuousOn_w.mono fun t ht => lt_trans (show (t : ℝ≥0∞) < s' from ht) hs'ζ) hfp.w_zero hss'
  have hgap : ∀ r : ℝ≥0, r ≤ q' → VL (Fin.last j) r ω < W r ω := fun r hr =>
    vL_last_lt hp hsum (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) hqζ)
  have hgeo : ∀ y' : ℝ, y' < (wordAt W VL VR (fun _ => q') ω).1 (Fin.last j) →
      extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal ω) q') y' ∉ H := by
    intro y' hy' hmem
    obtain ⟨x₁, -, hx₁⟩ := exists_extendFrom_eq_lt_last hp hqζ hgap (hγIcc q' hqζ) (yt := y') hy'
    have hpos : (0 : ℝ) < (extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal ω) q') y').im := hmem
    rw [hx₁, Complex.ofReal_im] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨hζeq, hconv⟩ := exit_of_restart hfp.continuousOn_w hfp.w_zero hγIcc (fun t ht0 ht => hH t ht0 ht)
    hq'0 hqζ hcp.continuousOn_w hcp.w_zero (fun t ht => hxw t ht) hxζ.le hend hgeo
  obtain ⟨x₀, hx₀, hFx₀⟩ := exists_extendFrom_eq_lt_last hp hqζ hgap (hγIcc q' hqζ) (yt := y) hend.2.2.2.1
  rw [hFx₀] at hconv
  set Z : ℝ≥0 := q' + Sx with hZdef
  have hZ : ζ ω = (Z : ℝ≥0∞) := hζeq
  have hx₀0 : x₀ < 0 := hx₀.trans hlast
  set η : ℝ≥0 → ℂ := fun t => if (t : ℝ≥0∞) < ζ ω then γ t else (x₀ : ℂ) with hη
  have hηγ : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → η t = γ t := fun t ht => by simp only [hη, ht, ↓reduceIte]
  have hηZ : η Z = x₀ := by simp only [hη, hZ, lt_irrefl, ↓reduceIte]
  have hγne : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → γ t ≠ x₀ := by
    intro t ht h
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0 | h0
    · have h1 : γ 0 = 0 := (hgen 0 hζ0).1
      rw [← h0, h1] at h
      have : (x₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx₀0.ne
      exact this h.symm
    · have hpos : (0 : ℝ) < (γ t).im := hH t h0 ht
      rw [h, Complex.ofReal_im] at hpos
      exact lt_irrefl _ hpos
  refine ⟨hζ0, by rw [hZ]; exact ENNReal.coe_ne_top, η, ⟨?_, ?_, ?_⟩, ?_, ?_, x₀, hx₀, ?_⟩
  · rw [hηγ 0 hζ0]
    exact (hgen 0 hζ0).1
  · intro t ht
    rcases (show (t : ℝ≥0∞) ≤ ζ ω from ht).lt_or_eq with hlt | heq
    · obtain ⟨s', hts', hs'ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
      have hts'' : t < s' := by exact_mod_cast hts'
      have hγc : ContinuousAt γ t :=
        ((hgen s' hs'ζ).2.1.mono fun r (hr : r ∈ Iic s') =>
          (by exact_mod_cast hr : (r : ℝ≥0∞) ≤ s')).continuousAt (Iic_mem_nhds hts'')
      have hev : η =ᶠ[𝓝 t] γ := by
        filter_upwards [Iio_mem_nhds hts''] with r hr
        exact hηγ r (lt_trans (by exact_mod_cast hr) hs'ζ)
      exact (hγc.congr hev.symm).continuousWithinAt
    · have htZ : t = Z := by rw [hZ] at heq; exact_mod_cast heq
      have hset : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ ω} = Iic Z := by
        ext r
        simp only [mem_ofPred_eq, mem_Iic, hZ, ENNReal.coe_le_coe]
      rw [hset, htZ]
      refine continuousWithinAt_Iio_iff_Iic.1 ?_
      show Tendsto η (𝓝[<] Z) (𝓝 (η Z))
      rw [hηZ]
      refine hconv.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact (hηγ r (by rw [hZ]; exact_mod_cast hr)).symm
  · intro t ht
    obtain ⟨s', hts', hs'ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
    have e : η '' Icc 0 t = γ '' Icc 0 t :=
      image_congr fun r hr => hηγ r (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr.2) ht)
    rw [e]
    exact (hgen s' hs'ζ).2.2 t hts'
  · intro t₁ ht₁ t₂ ht₂ heq
    have ht₁' : (t₁ : ℝ≥0∞) ≤ ζ ω := ht₁
    have ht₂' : (t₂ : ℝ≥0∞) ≤ ζ ω := ht₂
    by_cases h1 : (t₁ : ℝ≥0∞) < ζ ω <;> by_cases h2 : (t₂ : ℝ≥0∞) < ζ ω
    · rw [hηγ t₁ h1, hηγ t₂ h2] at heq
      exact hinj h1 h2 heq
    · have e2 : η t₂ = x₀ := by simp only [hη, h2, ↓reduceIte]
      rw [hηγ t₁ h1, e2] at heq
      exact absurd heq (hγne t₁ h1)
    · have e1 : η t₁ = x₀ := by simp only [hη, h1, ↓reduceIte]
      rw [hηγ t₂ h2, e1] at heq
      exact absurd heq.symm (hγne t₂ h2)
    · have e1 : (t₁ : ℝ≥0∞) = ζ ω := le_antisymm ht₁' (not_lt.1 h1)
      have e2 : (t₂ : ℝ≥0∞) = ζ ω := le_antisymm ht₂' (not_lt.1 h2)
      exact_mod_cast e1.trans e2.symm
  · intro t ht0 ht
    rw [hηγ t ht]
    exact hH t ht0 ht
  · rw [hZ, ENNReal.toNNReal_coe]
    exact hηZ

end InteractingSLE.ZhanGT4.A2P1
