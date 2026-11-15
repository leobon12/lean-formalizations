/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseSelAdapt

/-!
# §7.4, Aux. lemma 122 before a stopping lifetime, without assuming the phase adapted

Packet PROVE-STRIPSYS6 (specification §7.4, Aux. lemma 122, `source/spec/p385-432.md` L104–L131, pp. 389–391).

`aux122_adapt` and `ae_phase_eq_zero_adapt`: PROVE-STRIPSYS5's `PhaseSelFull.aux122_before` /
`ae_phase_eq_zero_before` without the extra hypothesis (A2) `hda : ∀ t, Measurable[𝓕 t] (d t)`. The source's step
("Equation (PS9.1) therefore makes `d_t` an adapted continuous function of `t > 0` […] The usual right continuity of the
filtration makes `d` measurable at time zero", p. 390) is `PhaseSelAdapt.exists_phaseEvents`: the events
`{j < T, d_j = c}` (rational `j > 0`) agree almost surely with events `D c j ∈ 𝓕_j` read off (PS9.1) at far points
before the localizing times. The time-zero events of the proof are built from these `D` instead of `d`; the rest of
the proof is PROVE-STRIPSYS5's.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace PhaseSelAdapt

open MartChar Aux117 PhaseSel PhaseSelFull

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- **Aux. lemma 122 before a stopping lifetime, with a random initial word, the phase only described**
(PROVE-STRIPSYS5's `PhaseSelFull.aux122_before` without its extra hypothesis (A2)): put `k > 4`, `Λ = π/√k`,
`χ = −χ(k) > 0`, `A = k/2 − 2`. Let the driver and the force coordinates of a finite word (seeds `0⁻, 0⁺` at index `0`
started at `0`, weights `r_L, r_R ∈ (−2, 2A − 2)`, other marks started at random positions strictly away from `0`) be
continuous adapted processes with the deterministic properties of geometric force images, in a right-continuous
filtration, and let `T` be a stopping time. Assume the exact boundary description for `0 < t ≤ T`: the actual mean is
the coupling mean of the bounded harmonic extension of the word's heights with the exposed interval raised by one
common phase `d_t ∈ 2πχℤ` (`phaseData`); these means are local martingales before swallowing and before `T`, and
continuous in time up to `T` before swallowing (stated for every choice of the extensions). **No measurability of `d`
is assumed**: (PS9.1) makes it adapted (`exists_phaseEvents`). Then there is a time-zero event `A` of full measure
within `{T > 0}` on which `T > 0` and `d_t = 0` for every `0 < t ≤ T`, and, conditionally on `A`, the canonical
explicit means are local martingales. -/
theorem aux122_adapt [IsProbabilityMeasure P] [𝓕.IsRightContinuous] {k : ℝ} (hk : 4 < k)
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    (hrL : -2 < ρL 0) (hrL' : ρL 0 < 2 * (k / 2 - 2) - 2) (hrR : -2 < ρR 0) (hrR' : ρR 0 < 2 * (k / 2 - 2) - 2)
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ}
    (hseedL : ∀ ω, VL 0 0 ω = 0) (hseedR : ∀ ω, VR 0 0 ω = 0)
    (hxLd : ∀ ω (i : Fin nL), VL i.succ 0 ω < 0) (hxRd : ∀ ω (j : Fin nR), 0 < VR j.succ 0 ω)
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓕 W)
    (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i)) (hVRa : ∀ i, StronglyAdapted 𝓕 (VR i))
    (hordL : ∀ ω t i, VL i t ω ≤ W t ω) (hordR : ∀ ω t i, W t ω ≤ VR i t ω)
    (hpathL : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VL i t ω))
    (hpathR : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VR i t ω))
    (hantiL : ∀ ω i, Antitone fun t => VL i t ω) (hmonoR : ∀ ω j, Monotone fun t => VR j t ω)
    (hidxL : ∀ ω t, Antitone fun i => VL i t ω) (hidxR : ∀ ω t, Monotone fun j => VR j t ω)
    (hmergeL : ∀ ω i j s t, s ≤ t → VL i s ω = VL j s ω → VL i t ω = VL j t ω)
    (hmergeR : ∀ ω i j s t, s ≤ t → VR i s ω = VR j s ω → VR i t ω = VR j t ω)
    (hsep : ∀ ω t, 0 < t → ∀ i j, VL i t ω = W t ω → VR j t ω ≠ W t ω)
    {T : Ω → WithTop ℝ≥0} (hT : IsStoppingTime 𝓕 T)
    {d : ℝ≥0 → Ω → ℝ}
    (hd : ∀ (t : ℝ≥0) ω, 0 < t → (t : WithTop ℝ≥0) ≤ T ω → ∃ n : ℤ, d t ω = n * phaseStep k)
    (hmart : ∀ U : Ω → ℝ≥0 → ℂ → ℝ, (∀ ω t, IsBoundedHarmonicExtension
        (phaseData k ρL ρR (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω) (d t ω))
        (forceJumpSet (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω)) (U ω t)) →
      ∀ z ∈ H, IsLocalMartingaleBefore 𝓕 P
        (fun ω => min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (T ω))
        (fun t ω => couplingMean k (wpath W ω) t (U ω t) z))
    (hcont : ∀ U : Ω → ℝ≥0 → ℂ → ℝ, (∀ ω t, IsBoundedHarmonicExtension
        (phaseData k ρL ρR (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω) (d t ω))
        (forceJumpSet (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω)) (U ω t)) →
      ∀ ω (z : ℂ) (T' : ℝ), 0 ≤ T' → (T'.toNNReal : WithTop ℝ≥0) ≤ T ω →
        z ∈ H \ QuantumZipper.fwdHull (wpath W ω) T' →
        ContinuousOn (fun t : ℝ => couplingMean k (wpath W ω) t (U ω t.toNNReal) z) (Icc 0 T')) :
    ∃ A : Set Ω, MeasurableSet[𝓕 0] A ∧
      (∀ ω ∈ A, 0 < T ω ∧ ∀ t : ℝ≥0, 0 < t → (t : WithTop ℝ≥0) ≤ T ω → d t ω = 0) ∧
      (∀ᵐ ω ∂P, 0 < T ω → ω ∈ A) ∧
      (P A ≠ 0 → ∀ z ∈ H, IsLocalMartingaleBefore (subFilt 𝓕 A) (condSub P A)
        (fun ω : A => min (QuantumZipper.swallowTime (wpath (fun t (ω : A) => W t ω) ω) z : WithTop ℝ≥0) (T ω))
        (coupProc k ρL ρR (fun t (ω : A) => W t ω) (fun i t (ω : A) => VL i t ω) (fun j t (ω : A) => VR j t ω) z))
    := by
  have hk0 : 0 < k := by linarith
  have hA : 0 < k / 2 - 2 := by linarith
  have hvL : ∀ ω t, VL 0 t ω - W t ω ≤ 0 := fun ω t => sub_nonpos.2 (hordL ω t 0)
  have hvR : ∀ ω t, 0 ≤ VR 0 t ω - W t ω := fun ω t => sub_nonneg.2 (hordR ω t 0)
  -- the natural extensions of the phase-shifted data
  set U₀ : Ω → ℝ≥0 → ℂ → ℝ := fun ω t ξ => meanExt k (shiftL k ρL (d t ω)) (shiftR k ρR (d t ω)) (W t ω)
    (fun i => VL i t ω) (fun j => VR j t ω) ξ + d t ω with hU₀def
  have hU₀ : ∀ ω t, IsBoundedHarmonicExtension
      (phaseData k ρL ρR (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω) (d t ω))
      (forceJumpSet (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω)) (U₀ ω t) := fun ω t =>
    isBoundedHarmonicExtension_unshift hk0 (hvL ω t) (hvR ω t)
      (isBoundedHarmonicExtension_meanExt k _ _ (W t ω) _ _)
  -- the phase is constant on `(0, T]`, along every path
  have hconst : ∀ ω (s t : ℝ≥0), 0 < s → 0 < t → (s : WithTop ℝ≥0) ≤ T ω → (t : WithTop ℝ≥0) ≤ T ω →
      d s ω = d t ω := fun ω s t hs ht hsT htT =>
    phase_eq_of_pos_before (L := T ω) (phaseStep_ne_zero hk) (hWc ω) (fun i => (hpathL ω i).1)
      (fun j => (hpathR ω j).1) (hordL ω) (hordR ω) (hantiL ω 0) (hmonoR ω 0) (hpathL ω 0).2.2.2
      (fun t ht htT => hd t ω ht htT) (hU₀ ω) (hcont U₀ hU₀ ω) hs ht hsT htT
  -- the time-zero events: the phase at arbitrarily small rational times before `T`
  set c₀ : ℝ := phaseStep k with hc₀
  obtain ⟨D, hDm, hDsub, hDae⟩ := exists_phaseEvents (P := P) hk0 hWc hWa hVLa hVRa hordL hordR hpathL hantiL
    hmonoR hT hmart
  set B : ℤ → ℕ → Set Ω := fun n m => ⋃ j : ℚ, {ω | 0 < j ∧ (j : ℝ) < 1 / ((m : ℝ) + 1) ∧
    ω ∈ D (n * c₀) j} with hBdef
  set A : ℤ → Set Ω := fun n => ⋂ m, B n m with hAdef
  have hBmono : ∀ n {m m' : ℕ}, m ≤ m' → B n m' ⊆ B n m := by
    intro n m m' hmm' ω hω
    simp only [hBdef, mem_iUnion, mem_ofPred_eq] at hω ⊢
    obtain ⟨j, hj0, hj1, hj2⟩ := hω
    refine ⟨j, hj0, hj1.trans_le ?_, hj2⟩
    gcongr
  have hBm : ∀ n (m : ℕ) (r : ℝ≥0), 1 / ((m : ℝ) + 1) ≤ r → MeasurableSet[𝓕 r] (B n m) := by
    intro n m r hmr
    refine MeasurableSet.iUnion fun j => ?_
    by_cases hj : 0 < j ∧ (j : ℝ) < 1 / ((m : ℝ) + 1)
    · have hjr : (j : ℝ).toNNReal ≤ r := Real.toNNReal_le_iff_le_coe.2 (hj.2.le.trans hmr)
      have e : {ω | 0 < j ∧ (j : ℝ) < 1 / ((m : ℝ) + 1) ∧ ω ∈ D (n * c₀) j} = D (n * c₀) j := by
        ext ω
        simp only [mem_ofPred_eq]
        exact ⟨fun h => h.2.2, fun h => ⟨hj.1, hj.2, h⟩⟩
      rw [e]
      exact 𝓕.mono hjr _ (hDm _ j)
    · have e : {ω | 0 < j ∧ (j : ℝ) < 1 / ((m : ℝ) + 1) ∧ ω ∈ D (n * c₀) j} = ∅ := by
        ext ω
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun h => hj ⟨h.1, h.2.1⟩
      rw [e]; exact @MeasurableSet.empty _ (𝓕 r)
  have hA0 : ∀ n, MeasurableSet[𝓕 0] (A n) := by
    intro n
    refine measurableSet_zero_of_forall_pos fun r hr => ?_
    obtain ⟨M, hM⟩ := exists_nat_one_div_lt (show (0 : ℝ) < r from hr)
    have e : A n = ⋂ m : ℕ, B n (m + M) := by
      ext ω
      simp only [hAdef, mem_iInter]
      exact ⟨fun h m => h (m + M), fun h m => hBmono n (Nat.le_add_right m M) (h m)⟩
    rw [e]
    refine MeasurableSet.iInter fun m => hBm n (m + M) r ?_
    refine le_trans ?_ hM.le
    gcongr
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  -- the events through the phase
  have hmemA : ∀ n ω, ω ∈ A n → 0 < T ω ∧ ∀ t : ℝ≥0, 0 < t → (t : WithTop ℝ≥0) ≤ T ω → d t ω = n * c₀ := by
    intro n ω hω
    have h0 := (mem_iInter.1 hω) 0
    simp only [hBdef, mem_iUnion, mem_ofPred_eq] at h0
    obtain ⟨j, hj0, -, hjD⟩ := h0
    obtain ⟨hjT, hjd⟩ := hDsub _ j ω hj0 hjD
    have hjpos : 0 < (j : ℝ).toNNReal := Real.toNNReal_pos.2 (by exact_mod_cast hj0)
    refine ⟨lt_of_le_of_lt bot_le hjT, fun t ht htT => ?_⟩
    rw [hconst ω t _ ht hjpos htT hjT.le]
    exact hjd
  have hmemA' : ∀ (n : ℤ) ω, (∀ c (j : ℚ), 0 < j → (((j : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0) < T ω →
      d (j : ℝ).toNNReal ω = c → ω ∈ D c j) →
      ∀ (s : ℝ≥0), 0 < s → (s : WithTop ℝ≥0) ≤ T ω → d s ω = n * c₀ → ω ∈ A n := by
    intro n ω hgood s hs hsT hds
    refine mem_iInter.2 fun m => ?_
    simp only [hBdef, mem_iUnion, mem_ofPred_eq]
    have hTpos : (0 : ℝ≥0∞) < T ω := lt_of_lt_of_le (ENNReal.coe_pos.2 hs) hsT
    obtain ⟨r, hr0, hrT⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hTpos
    have hb : (0 : ℝ) < min (1 / ((m : ℝ) + 1)) r := lt_min (by positivity) (by exact_mod_cast hr0)
    obtain ⟨j, hj0, hjb⟩ := exists_rat_btwn hb
    have hj0' : (0 : ℚ) < j := by exact_mod_cast hj0
    have hjr : (((j : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0) < T ω := by
      refine lt_of_le_of_lt ?_ hrT
      exact ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 (hjb.le.trans (min_le_right _ _)))
    refine ⟨j, hj0', hjb.trans_le (min_le_left _ _), hgood _ j hj0' hjr ?_⟩
    rw [hconst ω _ s (Real.toNNReal_pos.2 hj0) hs hjr.le hsT]
    exact hds
  -- on each time-zero event of positive probability the shifted explicit means are local martingales
  have hsub : ∀ n : ℤ, P (A n) ≠ 0 → ∀ z ∈ H, IsLocalMartingaleBefore (subFilt 𝓕 (A n)) (condSub P (A n))
        (fun ω : A n => min (QuantumZipper.swallowTime (wpath (fun t (ω : A n) => W t ω) ω) z : WithTop ℝ≥0)
          (T ω))
        (coupProc k (shiftL k ρL (n * c₀)) (shiftR k ρR (n * c₀)) (fun t (ω : A n) => W t ω)
          (fun i t (ω : A n) => VL i t ω) (fun j t (ω : A n) => VR j t ω) z) := by
    intro n h0
    have hQ : IsProbabilityMeasure (condSub P (A n)) := isProbabilityMeasure_condSub (𝓕.le 0 _ (hA0 n)) h0
    set c : ℝ := n * c₀ with hc
    classical
    -- an extension equal to the shifted canonical one plus `c` on `A n` up to `T`
    set U₁ : Ω → ℝ≥0 → ℂ → ℝ := fun ω t => if ω ∈ A n ∧ (t : WithTop ℝ≥0) ≤ T ω then
      (fun ξ => meanExt k (shiftL k ρL c) (shiftR k ρR c) (W t ω) (fun i => VL i t ω) (fun j => VR j t ω) ξ + c)
      else U₀ ω t with hU₁def
    have hU₁ : ∀ ω t, IsBoundedHarmonicExtension
        (phaseData k ρL ρR (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω) (d t ω))
        (forceJumpSet (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω)) (U₁ ω t) := by
      intro ω t
      by_cases hω : ω ∈ A n ∧ (t : WithTop ℝ≥0) ≤ T ω
      · simp only [hU₁def, hω, and_self, ↓reduceIte]
        have hext := isBoundedHarmonicExtension_unshift (c := c) hk0 (hvL ω t) (hvR ω t)
          (isBoundedHarmonicExtension_meanExt k (shiftL k ρL c) (shiftR k ρR c) (W t ω) (fun i => VL i t ω)
            (fun j => VR j t ω))
        rcases (zero_le : (0 : ℝ≥0) ≤ t).eq_or_lt with h0t | h0t
        · subst h0t
          refine isBoundedHarmonicExtension_congr_data hext fun x _ => ?_
          simp only [phaseData, hseedL, hseedR, hW0, sub_self, Ioo_self, indicator_empty, mul_zero]
        · rwa [(hmemA n ω hω.1).2 t h0t hω.2]
      · simp only [hU₁def, hω, ↓reduceIte]
        exact hU₀ ω t
    intro z hz
    have h1 := isLocalMartingaleBefore_sub (hA0 n) h0 (hmart U₁ hU₁ z hz)
    refine isLocalMartingaleBefore_sub_const_before c h1 fun t ω ht => ?_
    have hω : (ω : Ω) ∈ A n ∧ (t : WithTop ℝ≥0) ≤ T ω := ⟨ω.2, ht.trans (min_le_right _ _)⟩
    simp only [coupProc, hU₁def, hω, and_self, ↓reduceIte]
    rw [← couplingMean_sub_const]
    simp only [add_sub_cancel_right]
    rfl
  -- every nonzero phase is excluded (Aux. lemmas 117 and 104 before the lifetime, on the subtype)
  have hnull : ∀ n : ℤ, n ≠ 0 → P (A n) = 0 := by
    intro n hn
    by_contra h0
    have hAm : MeasurableSet (A n) := 𝓕.le 0 _ (hA0 n)
    have hQ : IsProbabilityMeasure (condSub P (A n)) := isProbabilityMeasure_condSub hAm h0
    set c : ℝ := n * c₀ with hc
    have hcΛ : c / (Real.pi / Real.sqrt k) = n * (2 * (k / 2 - 2)) := by
      rw [hc, hc₀, mul_div_assoc, phaseStep_div hk0]
    have hab := opposite_of_ne_zero hA hrL hrL' hrR hrR' hn
    rw [← hcΛ] at hab
    have hT0 := ae_lifetime_eq_zero_of_couplingMean_of_opposite (P := condSub P (A n))
      (𝓕 := subFilt 𝓕 (A n)) hk0 (ρL := shiftL k ρL c) (ρR := shiftR k ρR c) (W := fun t (ω : A n) => W t ω)
      (VL := fun i t (ω : A n) => VL i t ω) (VR := fun j t (ω : A n) => VR j t ω) (fun ω => hseedL ω)
      (fun ω => hseedR ω) (fun ω => hxLd ω) (fun ω => hxRd ω) ?_ (fun ω => hW0 ω) (fun ω => hWc ω)
      (stronglyAdapted_sub hWa) (fun i => stronglyAdapted_sub (hVLa i)) (fun i => stronglyAdapted_sub (hVRa i))
      (fun ω => hordL ω) (fun ω => hordR ω) (fun ω => hpathL ω) (fun ω => hpathR ω) (fun ω => hantiL ω)
      (fun ω => hmonoR ω) (fun ω => hidxL ω) (fun ω => hidxR ω) (fun ω => hmergeL ω) (fun ω => hmergeR ω)
      (fun ω => hsep ω) (T := fun ω : A n => T ω) (isStoppingTime_sub hT) (hsub n h0)
    · have hpos : ∀ ω : A n, ¬ T ω = 0 := fun ω h => by
        have := (hmemA n ω ω.2).1
        rw [h] at this
        exact lt_irrefl _ this
      rw [ae_iff] at hT0
      have e : {ω : A n | ¬ T ω = 0} = univ := by ext ω; simp [hpos ω]
      rw [e, measure_univ] at hT0
      exact one_ne_zero hT0
    · simp only [shiftL_zero, shiftR_zero]
      rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by linarith, by linarith⟩
      · exact Or.inr ⟨by linarith, by linarith⟩
  -- conclusion
  have hall : ∀ᵐ ω ∂P, ∀ n : ℤ, n ≠ 0 → ω ∉ A n :=
    ae_all_iff.2 fun n => by
      by_cases hn : n = 0
      · exact Eventually.of_forall fun ω h => absurd hn h
      · exact (measure_eq_zero_iff_ae_notMem.1 (hnull n hn)).mono fun ω h _ => h
  refine ⟨A 0, hA0 0, fun ω hω => ⟨(hmemA 0 ω hω).1, fun t ht htT => ?_⟩, ?_, fun h0 z hz => ?_⟩
  · rw [(hmemA 0 ω hω).2 t ht htT, Int.cast_zero, zero_mul]
  · filter_upwards [hall, hDae] with ω hω hgood hTpos
    obtain ⟨r, hr0, hrT⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hTpos
    have hr0' : 0 < r := ENNReal.coe_pos.1 hr0
    have hrT' : (r : WithTop ℝ≥0) ≤ T ω := hrT.le
    obtain ⟨n, hn⟩ := hd r ω hr0' hrT'
    have hmem := hmemA' n ω hgood r hr0' hrT' hn
    have hn0 : n = 0 := by
      by_contra hne
      exact hω n hne hmem
    rw [hn0] at hmem
    exact hmem
  · have h := hsub 0 h0 z hz
    simp only [Int.cast_zero, zero_mul, shiftL_zero_eq, shiftR_zero_eq] at h
    exact h

/-- **Aux. lemma 122 before a stopping lifetime, with a random initial word: the phase is zero** almost surely at
every `0 < t ≤ T` (the hypotheses of `aux122_adapt`; no measurability of `d` assumed). -/
theorem ae_phase_eq_zero_adapt [IsProbabilityMeasure P] [𝓕.IsRightContinuous] {k : ℝ} (hk : 4 < k)
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    (hrL : -2 < ρL 0) (hrL' : ρL 0 < 2 * (k / 2 - 2) - 2) (hrR : -2 < ρR 0) (hrR' : ρR 0 < 2 * (k / 2 - 2) - 2)
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ}
    (hseedL : ∀ ω, VL 0 0 ω = 0) (hseedR : ∀ ω, VR 0 0 ω = 0)
    (hxLd : ∀ ω (i : Fin nL), VL i.succ 0 ω < 0) (hxRd : ∀ ω (j : Fin nR), 0 < VR j.succ 0 ω)
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓕 W)
    (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i)) (hVRa : ∀ i, StronglyAdapted 𝓕 (VR i))
    (hordL : ∀ ω t i, VL i t ω ≤ W t ω) (hordR : ∀ ω t i, W t ω ≤ VR i t ω)
    (hpathL : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VL i t ω))
    (hpathR : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VR i t ω))
    (hantiL : ∀ ω i, Antitone fun t => VL i t ω) (hmonoR : ∀ ω j, Monotone fun t => VR j t ω)
    (hidxL : ∀ ω t, Antitone fun i => VL i t ω) (hidxR : ∀ ω t, Monotone fun j => VR j t ω)
    (hmergeL : ∀ ω i j s t, s ≤ t → VL i s ω = VL j s ω → VL i t ω = VL j t ω)
    (hmergeR : ∀ ω i j s t, s ≤ t → VR i s ω = VR j s ω → VR i t ω = VR j t ω)
    (hsep : ∀ ω t, 0 < t → ∀ i j, VL i t ω = W t ω → VR j t ω ≠ W t ω)
    {T : Ω → WithTop ℝ≥0} (hT : IsStoppingTime 𝓕 T)
    {d : ℝ≥0 → Ω → ℝ}
    (hd : ∀ (t : ℝ≥0) ω, 0 < t → (t : WithTop ℝ≥0) ≤ T ω → ∃ n : ℤ, d t ω = n * phaseStep k)
    (hmart : ∀ U : Ω → ℝ≥0 → ℂ → ℝ, (∀ ω t, IsBoundedHarmonicExtension
        (phaseData k ρL ρR (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω) (d t ω))
        (forceJumpSet (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω)) (U ω t)) →
      ∀ z ∈ H, IsLocalMartingaleBefore 𝓕 P
        (fun ω => min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (T ω))
        (fun t ω => couplingMean k (wpath W ω) t (U ω t) z))
    (hcont : ∀ U : Ω → ℝ≥0 → ℂ → ℝ, (∀ ω t, IsBoundedHarmonicExtension
        (phaseData k ρL ρR (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω) (d t ω))
        (forceJumpSet (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω)) (U ω t)) →
      ∀ ω (z : ℂ) (T' : ℝ), 0 ≤ T' → (T'.toNNReal : WithTop ℝ≥0) ≤ T ω →
        z ∈ H \ QuantumZipper.fwdHull (wpath W ω) T' →
        ContinuousOn (fun t : ℝ => couplingMean k (wpath W ω) t (U ω t.toNNReal) z) (Icc 0 T')) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → (t : WithTop ℝ≥0) ≤ T ω → d t ω = 0 := by
  obtain ⟨A, -, hA, hae, -⟩ := aux122_adapt hk hrL hrL' hrR hrR' hseedL hseedR hxLd hxRd hW0 hWc hWa hVLa hVRa
    hordL hordR hpathL hpathR hantiL hmonoR hidxL hidxR hmergeL hmergeR hsep hT hd hmart hcont
  filter_upwards [hae] with ω hω t ht htT
  exact (hA ω (hω (lt_of_lt_of_le (ENNReal.coe_pos.2 ht) htT))).2 t ht htT

end PhaseSelAdapt

end Sec7

end InteractingSLE
