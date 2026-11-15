/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactImgLevy
import InteractingSLE.Spec.Restart.ConverseBefore

/-!
# Wang–Wu Lemma 2.11 for a killed word with the standard noise space

Packet PROVE-STAGED-REP2. `WangWu.ImgDrv.IsKilledWord.exists_isWordEntrance` (PROVE-WW-B16) produces the driving
Brownian motion of a killed word on `Ω × Ω₀` with an **existential** noise space `Ω₀`; the disintegration of a stopped
representation over the past (`StagedKCand.IsStoppedRep.isStageLawFarK`) needs a standard Borel space. This file gives
the same two results with the explicit noise space `ℕ → ℝ` of `Restart.ConverseBefore.exists_noiseBM`
(`exists_brownian_std`, **`exists_isWordEntrance_std`**): the proofs are PROVE-WW-B16's, verbatim, with
`OneForce.exists_filteredBrownian` replaced by `exists_noiseBM` (as PROVE-STRIPSYS5's
`Restart.ConverseBefore.exists_brownian_continuation_std` did for `PhaseSelFull.exists_brownian_continuation`).

R48: nothing here uses Theorem 1.2/1.3 or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.StagedRepLater

open WangWu WangWu.ImgDrv MartChar Sec7.PhaseSelAdapt Sec7.PhaseSelFull Sec7.Aux117

section Std

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {nL nR : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓖 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {T : Ω → WithTop ℝ≥0} {σ : ℕ → Ω → ℝ≥0} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

variable (hκ : 0 < κ) (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s)
  (hK : IsKilledWord W VL VR T) (hWa : StronglyAdapted 𝓖 W) (hVLa : ∀ i, StronglyAdapted 𝓖 (VL i))
  (hVRa : ∀ j, StronglyAdapted 𝓖 (VR j)) (hσ : ∀ n, IsStoppingTime 𝓖 fun ω => (σ n ω : WithTop ℝ≥0))
  (hσm : ∀ ω, Monotone (σ · ω)) (hσT : ∀ n ω, (σ n ω : WithTop ℝ≥0) < T ω)
  (hσlim : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, (u : WithTop ℝ≥0) < T ω → ∃ n, u ≤ σ n ω)
  (hmart : ∀ z ∈ H, IsLocalMartingaleBefore 𝓖 P
    (fun ω => min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (T ω))
    (coupProc κ ρL ρR W VL VR z))
include hκ hnull hK hWa hVLa hVRa hσ hσm hσT hσlim hmart

/-- **The driving Brownian motion of a killed word, continued after the killing time.** On `Ω × (ℕ → ℝ)` there is a
Brownian motion `B` of the product filtration, with continuous paths and `B₀ = 0`, and a time-zero event `G` of full
measure on which the localizing times exhaust `[0, T)` and `B = M/√κ` before `T`. -/
theorem exists_brownian_std :
    ∃ (P₀ : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure P₀)
      (𝓦 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (ℕ → ℝ))) (B : ℝ≥0 → Ω × (ℕ → ℝ) → ℝ),
      IsFilteredBrownianReal (WholeField.prodFiltration 𝓖 𝓦) B (P.prod P₀) ∧ (∀ p, Continuous fun t => B t p) ∧
        (∀ p, B 0 p = 0) ∧ ∃ G : Set Ω, MeasurableSet[𝓖 0] G ∧ P Gᶜ = 0 ∧
          (∀ ω ∈ G, ∀ u : ℝ≥0, (u : WithTop ℝ≥0) < T ω → ∃ n, u ≤ locN W VL VR σ n ω) ∧
          ∀ (p : Ω × (ℕ → ℝ)) (t : ℝ≥0), p.1 ∈ G → (t : WithTop ℝ≥0) < T p.1 →
            B t p = martProc (jointρ ρL ρR) W (jointV VL VR) t p.1 / Real.sqrt κ := by
  classical
  set ρ := jointρ ρL ρR with hρ
  set V := jointV VL VR with hV
  -- the good event
  set Good : Set Ω := {ω | (∀ u : ℝ≥0, (u : WithTop ℝ≥0) < T ω → ∃ n, u ≤ σ n ω) ∧
    ∀ T₀ : ℝ≥0, T ω = T₀ → ∃ L, Tendsto (fun t => martProc ρ W V t ω) (𝓝[<] T₀) (𝓝 L)} with hGood
  have hgood : ∀ᵐ ω ∂P, ω ∈ Good := by
    filter_upwards [hσlim, hK.ae_tendsto_martProc hσT hσ hWa hVLa hVRa hκ hmart hσm hσlim] with ω h1 h2
    exact ⟨h1, h2⟩
  set N := toMeasurable P Goodᶜ with hN
  have hN0 : P N = 0 := by rw [hN, measure_toMeasurable]; exact ae_iff.1 hgood
  set G := Nᶜ with hGdef
  have hG0 : MeasurableSet[𝓖 0] G := (hnull N (measurableSet_toMeasurable _ _) hN0).compl
  have hGsub : ∀ ω ∈ G, ω ∈ Good := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable _ _ h)
  have hGc : P Gᶜ = 0 := by rw [hGdef, compl_compl]; exact hN0
  have hGex : ∀ ω ∈ G, ∀ u : ℝ≥0, (u : WithTop ℝ≥0) < T ω → ∃ n, u ≤ locN W VL VR σ n ω :=
    fun ω hω u hu => hK.exists_le_locN hσT hσm (hGsub ω hω).1 hu
  -- the frozen noise
  set Bv : ℝ≥0 → Ω → ℝ := fun t ω => frzM ρ W V T G t ω / Real.sqrt κ with hBvdef
  have hBvc : ∀ ω, Continuous fun t => Bv t ω := fun ω =>
    (continuous_frzM (fun ω _ => hK.continuousOn_martProc ρ ω) (fun ω hω => (hGsub ω hω).2) ω).div_const _
  have hT0 : ∀ ω, ((0 : ℝ≥0) : WithTop ℝ≥0) < T ω := fun ω =>
    lt_of_le_of_lt (WithTop.coe_le_coe.2 zero_le) (hσT 0 ω)
  have hBv0 : ∀ ω, Bv 0 ω = 0 := fun ω => by
    by_cases hω : ω ∈ G
    · simp only [hBvdef, frzM_of_lt hω (hT0 ω), martProc, martValue, sub_self, mul_zero,
        Finset.sum_const_zero, add_zero, zero_div]
    · simp only [hBvdef, frzM_of_notMem hω, zero_div]
  -- the stopping times
  set S : ℕ → Ω → ℝ≥0 := fun m ω => if ω ∈ G then locN W VL VR σ m ω else 0 with hSdef
  have hSmono : ∀ ω, Monotone fun m => S m ω := fun ω m m' hmm' => by
    by_cases hω : ω ∈ G
    · simp only [hSdef, hω, ↓reduceIte]
      exact hK.locN_mono hσT hσm ω hmm'
    · simp only [hSdef, hω, ↓reduceIte, le_refl]
  have hSst : ∀ m, IsStoppingTime 𝓖 fun ω => (S m ω : WithTop ℝ≥0) := fun m => by
    convert isStoppingTime_ite hG0 (hK.isStoppingTime_locN hσT hσ hWa hVLa hVRa m) using 1
    funext ω
    by_cases hω : ω ∈ G
    · simp only [hSdef, hω, ↓reduceIte]
    · simp [hSdef, hω]
  have hSm : ∀ (m : ℕ) (u : ℝ≥0), Measurable[(fun _ : ℕ => 𝓖) m u] fun ω => min u (S m ω) := fun m u =>
    measurable_min_of_isStoppingTime (hSst m) u
  -- the exponential martingales
  have hexp : ∀ m (a : ℝ), Martingale (fun t ω => Real.exp (a * Bv (min t (S m ω)) ω -
      a ^ 2 * ((min t (S m ω) : ℝ≥0) : ℝ) / 2)) ((fun _ : ℕ => 𝓖) m) P := by
    intro m a
    have hMM := hK.martingale_lifeLoc_sys hσT hσ hWa hVLa hVRa hκ hmart m
    have hE : Martingale (fun t ω => Real.exp (a * (martProc ρ (sysW W (σ m)) (sysV W VL VR (σ m))
        (min t (locN W VL VR σ m ω)) ω / Real.sqrt κ) - a ^ 2 * ((min t (locN W VL VR σ m ω) : ℝ≥0) : ℝ) / 2))
        𝓖 P :=
      martingale_exp_lifeLoc hκ (fun ω => hK.continuous_sysW (hσT m) ω) (hK.continuous_sysV hσT m) hMM.1 hMM.2 a
    have h1 := Sec6.Prop65.martingale_indicator_of_measurable hE hG0
    have h2 := Sec6.Prop65.martingale_indicator_of_measurable (martingale_const 𝓖 P (1 : ℝ)) hG0.compl
    convert h1.add h2 using 1
    funext t ω
    simp only [Pi.add_apply]
    by_cases hω : ω ∈ G
    · have hle : min t (locN W VL VR σ m ω) ≤ locN W VL VR σ m ω := min_le_right _ _
      have hlt : ((min t (locN W VL VR σ m ω) : ℝ≥0) : WithTop ℝ≥0) < T ω :=
        lt_of_le_sys (hσT m) (hle.trans (locN_le_σ m ω))
      rw [indicator_of_mem hω, indicator_of_notMem (not_not.2 hω)]
      simp only [hSdef, hω, ↓reduceIte, hBvdef, frzM_of_lt hω hlt, add_zero]
      rw [hK.martProc_sys_eq hσT ρ (hle.trans (locN_le_σ m ω))]
    · rw [indicator_of_notMem hω, indicator_of_mem (show ω ∈ Gᶜ from hω)]
      simp only [hSdef, hω, ↓reduceIte, min_zero, hBvdef, frzM_of_notMem hω, zero_div, mul_zero,
        NNReal.coe_zero, sub_zero, Real.exp_zero, zero_add]
  have hTC := WholeField.isTCExpMartingale_annClock (𝒢 := fun _ : ℕ => 𝓖) (fun _ => monotone_const) hSmono hSm
    hBvc hBv0 hexp
  rw [iSupFiltration_const] at hTC
  obtain ⟨P₀, hP₀, 𝓦, β, hβ, hβc, hβ0⟩ := Restart.ConverseBefore.exists_noiseBM
  obtain ⟨hB, hBc⟩ := WholeField.IsTCExpMartingale.isFilteredBrownianReal_complNoise hTC
    (LocalTime.isFilteredPreBrownian_of_isFilteredBrownianReal hβ) hβc hβ0
  refine ⟨P₀, hP₀, 𝓦, _, hB, hBc, fun p => ?_, G, hG0, hGc, hGex, fun p t hpG ht => ?_⟩
  · simp only [WholeField.complNoise, WholeField.annClock_zero, hBv0, hβ0, sub_self, zero_add]
  · obtain ⟨m, hm⟩ := hGex p.1 hpG t ht
    have hSm' : t ≤ S m p.1 := by simp only [hSdef, hpG, ↓reduceIte]; exact hm
    have hc : WholeField.annClock S t p.1 = t := WholeField.annClock_eq_of_le hSm'
    rw [WholeField.complNoise_of_eq hc]
    simp only [hc, hBvdef, frzM_of_lt hpG ht]

/-- **Wang–Wu Lemma 2.11 for a killed word** (up to the stopped lifetime). Let `(W, VL, VR)` be a killed word before
`T`, adapted to `𝓖` (whose time-zero σ-algebra contains the null sets), with explicit coupling means that are local
martingales before `min (swallowTime z) T`, and let `σₙ < T` be stopping times increasing to `T` almost surely. Then on
`Ω × (ℕ → ℝ)` there is a Brownian motion `B` of the product filtration such that, almost surely, the integrated driving
and force equations of the random word `(V₀)` hold on `[0, T)` driven by `B`. -/
theorem exists_isWordEntrance_std :
    ∃ (P₀ : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure P₀)
      (𝓦 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (ℕ → ℝ))) (B : ℝ≥0 → Ω × (ℕ → ℝ) → ℝ),
      IsFilteredBrownianReal (WholeField.prodFiltration 𝓖 𝓦) B (P.prod P₀) ∧ (∀ p, Continuous fun t => B t p) ∧
        ∀ᵐ p ∂(P.prod P₀), IsWordEntrance κ (fun i => VL i 0 p.1) (fun j => VR j 0 p.1) ρL ρR
          (fun t => W t p.1) (fun i t => VL i t p.1) (fun j t => VR j t p.1) (fun t => B t p) (T p.1 : ℝ≥0∞) := by
  classical
  obtain ⟨P₀, hP₀, 𝓦, B, hB, hBc, hB0, G, hG0, hGc, hGex, hBeq⟩ :=
    exists_brownian_std hκ hnull hK hWa hVLa hVRa hσ hσm hσT hσlim hmart
  refine ⟨P₀, hP₀, 𝓦, B, hB, hBc, ?_⟩
  set 𝓘 := WholeField.prodFiltration 𝓖 𝓦 with h𝓘
  have hBpre := LocalTime.isFilteredPreBrownian_of_isFilteredBrownianReal hB
  have hsk : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  set S : ℕ → Ω → ℝ≥0 := fun m ω => if ω ∈ G then locN W VL VR σ m ω else 0 with hSdef
  have hSst : ∀ m, IsStoppingTime 𝓖 fun ω => (S m ω : WithTop ℝ≥0) := fun m => by
    convert isStoppingTime_ite hG0 (hK.isStoppingTime_locN hσT hσ hWa hVLa hVRa m) using 1
  -- the integrated equations of the `n`-th continued system before `locN n`
  have hTan : ∀ n, ∀ᵐ p ∂(P.prod P₀), p.1 ∈ G → IsWordEntrance κ (fun i => VL i 0 p.1) (fun j => VR j 0 p.1)
      ρL ρR (fun t => sysW W (σ n) t p.1) (fun i t => sysVL W VL (σ n) i t p.1)
      (fun j t => sysVR W VR (σ n) j t p.1) (fun t => B t p) (locN W VL VR σ n p.1 : ℝ≥0∞) := by
    intro n
    have hς : IsStoppingTime 𝓘 fun p : Ω × (ℕ → ℝ) => (S n p.1 : WithTop ℝ≥0) := isStoppingTime_fst (hSst n)
    have hW' : ∀ (t : ℝ≥0) (p : Ω × (ℕ → ℝ)), (t : WithTop ℝ≥0) ≤ (S n p.1 : WithTop ℝ≥0) →
        sysW W (σ n) t p.1 = Real.sqrt κ * B t p - (1 / 2) * ((∑ i, ρL i * (sysVL W VL (σ n) i t p.1 - VL i 0 p.1))
          + ∑ j, ρR j * (sysVR W VR (σ n) j t p.1 - VR j 0 p.1)) := by
      intro t p ht
      by_cases hpG : p.1 ∈ G
      · have htl : t ≤ locN W VL VR σ n p.1 := by
          simp only [hSdef, hpG, ↓reduceIte] at ht; exact WithTop.coe_le_coe.1 ht
        have htσ : t ≤ σ n p.1 := htl.trans (locN_le_σ n p.1)
        have htT : (t : WithTop ℝ≥0) < T p.1 := lt_of_le_sys (hσT n) htσ
        have hVL' : ∀ i, sysVL W VL (σ n) i t p.1 = VL i t p.1 := fun i => hK.sysVL_of_le (hσT n) htσ i
        have hVR' : ∀ j, sysVR W VR (σ n) j t p.1 = VR j t p.1 := fun j => hK.sysVR_of_le (hσT n) htσ j
        rw [sysW_of_le htσ, hBeq p t hpG htT]
        simp only [hVL', hVR']
        exact driver_eq_martProc hκ hK.w_zero t p.1
      · have ht0 : t = 0 := by
          simp only [hSdef, hpG, ↓reduceIte] at ht
          exact le_antisymm (WithTop.coe_le_coe.1 ht) zero_le
        subst ht0
        have hVL' : ∀ i, sysVL W VL (σ n) i 0 p.1 = VL i 0 p.1 := fun i => hK.sysVL_of_le (hσT n) zero_le i
        have hVR' : ∀ j, sysVR W VR (σ n) j 0 p.1 = VR j 0 p.1 := fun j => hK.sysVR_of_le (hσT n) zero_le j
        simp only [sysW_zero hK.w_zero, hB0 p, hVL', hVR', sub_self, mul_zero, Finset.sum_const_zero, add_zero]
    have hL := ae_forceDefect_left_eq_zero_before (P := P.prod P₀) (𝓕 := 𝓘) (ρL := ρL) (ρR := ρR)
      (xL := fun p i => VL i 0 p.1) (xR := fun p j => VR j 0 p.1) (W := fun t p => sysW W (σ n) t p.1)
      (VL := fun i t p => sysVL W VL (σ n) i t p.1) (VR := fun j t p => sysVR W VR (σ n) j t p.1) hsk hBpre hς hW'
      (fun p => hK.continuous_sysW (hσT n) p.1) (stronglyAdapted_fst (hK.stronglyAdapted_sysW (hσT n) (hσ n) hWa))
      (fun i => stronglyAdapted_fst (hK.stronglyAdapted_sysVL (hσT n) (hσ n) hWa hVLa i))
      (fun j => stronglyAdapted_fst (hK.stronglyAdapted_sysVR (hσT n) (hσ n) hWa hVRa j))
      (fun p i => hK.isForcePath_sysVL (hσT n) p.1 i) (fun p j => hK.isForcePath_sysVR (hσT n) p.1 j)
      (fun _ t _ => contV_left_le_contW t) (fun p i => hK.antitone_sysVL (hσT n) p.1 i)
      (fun p j => hK.monotone_sysVR (hσT n) p.1 j) (fun p i j s t hst h => hK.merge_sysVL (hσT n) p.1 i j s t hst h)
      (fun p t => hK.antitone_idx_sysVL (hσT n) p.1 t) (fun p t ht i j h => hK.sep_sys (hσT n) p.1 t ht i j h)
    have hR := ae_forceDefect_right_eq_zero_before (P := P.prod P₀) (𝓕 := 𝓘) (ρL := ρL) (ρR := ρR)
      (xL := fun p i => VL i 0 p.1) (xR := fun p j => VR j 0 p.1) (W := fun t p => sysW W (σ n) t p.1)
      (VL := fun i t p => sysVL W VL (σ n) i t p.1) (VR := fun j t p => sysVR W VR (σ n) j t p.1) hsk hBpre hς hW'
      (fun p => hK.continuous_sysW (hσT n) p.1) (stronglyAdapted_fst (hK.stronglyAdapted_sysW (hσT n) (hσ n) hWa))
      (fun i => stronglyAdapted_fst (hK.stronglyAdapted_sysVL (hσT n) (hσ n) hWa hVLa i))
      (fun j => stronglyAdapted_fst (hK.stronglyAdapted_sysVR (hσT n) (hσ n) hWa hVRa j))
      (fun p i => hK.isForcePath_sysVL (hσT n) p.1 i) (fun p j => hK.isForcePath_sysVR (hσT n) p.1 j)
      (fun _ t _ => contW_le_contV_right t) (fun p i => hK.antitone_sysVL (hσT n) p.1 i)
      (fun p j => hK.monotone_sysVR (hσT n) p.1 j) (fun p i j s t hst h => hK.merge_sysVR (hσT n) p.1 i j s t hst h)
      (fun p t => hK.monotone_idx_sysVR (hσT n) p.1 t) (fun p t ht i j h => hK.sep_sys (hσT n) p.1 t ht i j h)
    filter_upwards [hL, hR] with p hLp hRp hpG
    have hSp : S n p.1 = locN W VL VR σ n p.1 := by simp only [hSdef, hpG, ↓reduceIte]
    have hcolL : ∀ u : ℝ≥0, 0 < u → ColliderNe ρL (fun t => sysW W (σ n) t p.1)
        (fun i t => sysVL W VL (σ n) i t p.1) u := fun u hu => by
      unfold ColliderNe
      rw [Finset.filter_false_of_mem fun i _ => (hK.sysVL_lt_sysW (hσT n) p.1 hu i).ne, Finset.sum_empty]
      norm_num
    have hcolR : ∀ u : ℝ≥0, 0 < u → ColliderNe ρR (fun t => sysW W (σ n) t p.1)
        (fun j t => sysVR W VR (σ n) j t p.1) u := fun u hu => by
      unfold ColliderNe
      rw [Finset.filter_false_of_mem fun j _ => (hK.sysW_lt_sysVR (hσT n) p.1 hu j).ne', Finset.sum_empty]
      norm_num
    set b' : ℝ≥0 → ℝ := fun t => (sysW W (σ n) t p.1 + (1 / 2) * ((∑ i, ρL i * (sysVL W VL (σ n) i t p.1 -
      VL i 0 p.1)) + ∑ j, ρR j * (sysVR W VR (σ n) j t p.1 - VR j 0 p.1))) / Real.sqrt κ with hb'
    have hw' : ∀ t, sysW W (σ n) t p.1 = Real.sqrt κ * b' t - (1 / 2) * ((∑ i, ρL i *
        (sysVL W VL (σ n) i t p.1 - VL i 0 p.1)) + ∑ j, ρR j * (sysVR W VR (σ n) j t p.1 - VR j 0 p.1)) :=
      fun t => by simp only [hb']; field_simp; ring
    have hle : ∀ t : ℝ≥0, (t : ℝ≥0∞) < (locN W VL VR σ n p.1 : ℝ≥0∞) →
        (t : WithTop ℝ≥0) ≤ (S n p.1 : WithTop ℝ≥0) := fun t ht => by
      rw [hSp]; exact WithTop.coe_le_coe.2 (ENNReal.coe_lt_coe.1 ht).le
    have hE := isWordEntrance_of_forceDefect_eq_zero (a := κ) (b := b') (xL := fun i => VL i 0 p.1)
      (xR := fun j => VR j 0 p.1) (sysW_zero hK.w_zero p.1) (fun i => hK.sysVL_of_le (hσT n) zero_le i)
      (fun j => hK.sysVR_of_le (hσT n) zero_le j) (hK.continuous_sysW (hσT n) p.1)
      (fun i => hK.isForcePath_sysVL (hσT n) p.1 i) (fun j => hK.isForcePath_sysVR (hσT n) p.1 j)
      (fun t _ => contV_left_le_contW t) (fun t _ => contW_le_contV_right t)
      (hK.antitone_idx_sysVL (hσT n) p.1) (hK.monotone_idx_sysVR (hσT n) p.1) hw'
      (fun t ht i => hLp t (hle t ht) (fun u hu _ => hcolL u hu) i)
      (fun t ht j => hRp t (hle t ht) (fun u hu _ => hcolR u hu) j)
    refine IsWordEntrance.congr_b hE fun t ht => ?_
    have h := hW' t p (hle t ht)
    simp only [hb']
    rw [div_eq_iff hsk]
    linarith
  -- the killed word before `T`
  have hGae : ∀ᵐ p ∂(P.prod P₀), p.1 ∈ G :=
    Measure.quasiMeasurePreserving_fst.ae (ae_iff.2 hGc)
  filter_upwards [ae_all_iff.2 hTan, hGae] with p hp hpG
  refine isWordEntrance_of_seq (wn := fun n t => sysW W (σ n) t p.1)
    (vLn := fun n i t => sysVL W VL (σ n) i t p.1) (vRn := fun n j t => sysVR W VR (σ n) j t p.1)
    (s := fun n => locN W VL VR σ n p.1) (fun n => hp n hpG) (fun n t ht => ?_) (fun t ht => ?_)
  · have htσ : t ≤ σ n p.1 := ht.trans (locN_le_σ n p.1)
    exact ⟨sysW_of_le htσ, fun i => hK.sysVL_of_le (hσT n) htσ i, fun j => hK.sysVR_of_le (hσT n) htσ j⟩
  · obtain ⟨r, htr, hrT⟩ := WithTop.lt_iff_exists_coe_btwn.1 (show (t : WithTop ℝ≥0) < T p.1 from ht)
    obtain ⟨n, hn⟩ := hGex p.1 hpG r hrT
    exact ⟨n, lt_of_lt_of_le (WithTop.coe_lt_coe.1 htr) hn⟩

end Std

end InteractingSLE.Sec5.CrossCond.StagedRepLater
