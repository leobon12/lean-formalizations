/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondGenBrownian
import InteractingSLE.Spec.Sec7.PocketMartLife

/-!
# A contact word's integrated equations up to its threshold

Packet PROVE-CROSSCOND-GEN. The killed-word converse of WangWu.ReverseContactImgLevy
extends through one-sided force collisions. Its local Tanaka step only needs the colliding
total to differ from `-2`, which follows before `thresholdTime`. All original labels stay in
the word. One Brownian motion works for the entire announced lifetime.

This is conditional on the explicitly typed image-mean martingale hypothesis `hmart`.
Establishing that hypothesis for the general cross-conditioned image remains separate.
The announcement is strictly below `T` at every sample, so this helper concerns positive
available lifetimes; it does not remove the zero-lifetime case from any source statement.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.Gen

open WangWu.ImgDrv MartChar Sec7.PhaseSelAdapt Sec7.PhaseSelFull Sec7.Aux117

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {nL nR : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓖 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {T : Ω → WithTop ℝ≥0} {σ : ℕ → Ω → ℝ≥0} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  (hκ : 0 < κ) (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s)
  (hK : IsContactWord W VL VR T) (hWa : StronglyAdapted 𝓖 W)
  (hVLa : ∀ i, StronglyAdapted 𝓖 (VL i)) (hVRa : ∀ j, StronglyAdapted 𝓖 (VR j))
  (hσ : ∀ n, IsStoppingTime 𝓖 fun ω => (σ n ω : WithTop ℝ≥0))
  (hσm : ∀ ω, Monotone (σ · ω)) (hσT : ∀ n ω, (σ n ω : WithTop ℝ≥0) < T ω)
  (hσlim : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, (u : WithTop ℝ≥0) < T ω → ∃ n, u ≤ σ n ω)
  (hmart : ∀ z ∈ H, IsLocalMartingaleBefore 𝓖 P
    (fun ω => min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (T ω))
    (coupProc κ ρL ρR W VL VR z))
include hκ hnull hK hWa hVLa hVRa hσ hσm hσT hσlim hmart

/-- Integrated word equations until the killing time or the continuation threshold, with one
Brownian motion across all localization buffers and with every force label retained. -/
theorem IsContactWord.exists_isWordEntrance_threshold :
    ∃ (Ω₀ : Type) (m₀ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (_ : IsProbabilityMeasure P₀)
      (𝓦 : Filtration ℝ≥0 m₀) (B : ℝ≥0 → Ω × Ω₀ → ℝ),
      IsFilteredBrownianReal (WholeField.prodFiltration 𝓖 𝓦) B (P.prod P₀) ∧ (∀ p, Continuous fun t => B t p) ∧
        ∀ᵐ p ∂(P.prod P₀), IsWordEntrance κ (fun i => VL i 0 p.1) (fun j => VR j 0 p.1) ρL ρR
          (fun t => W t p.1) (fun i t => VL i t p.1) (fun j t => VR j t p.1) (fun t => B t p) (min (T p.1 : ℝ≥0∞)
            (thresholdTime ρL ρR (W · p.1) (fun i t => VL i t p.1) (fun j t => VR j t p.1))) := by
  classical
  obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓦, B, hB, hBc, hB0, G, hG0, hGc, hGex, hBeq⟩ :=
    hK.exists_brownian hκ hnull hWa hVLa hVRa hσ hσm hσT hσlim hmart
  refine ⟨Ω₀, m₀, P₀, hP₀, 𝓦, B, hB, hBc, ?_⟩
  set 𝓘 := WholeField.prodFiltration 𝓖 𝓦 with h𝓘
  have hBpre := LocalTime.isFilteredPreBrownian_of_isFilteredBrownianReal hB
  have hsk : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  set S : ℕ → Ω → ℝ≥0 := fun m ω => if ω ∈ G then locN W VL VR σ m ω else 0 with hSdef
  have hSst : ∀ m, IsStoppingTime 𝓖 fun ω => (S m ω : WithTop ℝ≥0) := fun m => by
    convert isStoppingTime_ite hG0 (hK.isStoppingTime_locN hσT hσ hWa hVLa hVRa m) using 1
  -- the integrated equations of the `n`-th continued system before `locN n`
  have hTan : ∀ n, ∀ᵐ p ∂(P.prod P₀), p.1 ∈ G → IsWordEntrance κ
      (fun i => VL i 0 p.1) (fun j => VR j 0 p.1) ρL ρR
      (W · p.1) (fun i t => VL i t p.1) (fun j t => VR j t p.1) (B · p)
      (min (locN W VL VR σ n p.1 : ℝ≥0∞)
        (thresholdTime ρL ρR (W · p.1) (fun i t => VL i t p.1) (fun j t => VR j t p.1))) := by
    intro n
    have hς : IsStoppingTime 𝓘 fun p : Ω × Ω₀ => (S n p.1 : WithTop ℝ≥0) := isStoppingTime_fst (hSst n)
    have hW' : ∀ (t : ℝ≥0) (p : Ω × Ω₀), (t : WithTop ℝ≥0) ≤ (S n p.1 : WithTop ℝ≥0) →
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
    let L := min (locN W VL VR σ n p.1 : ℝ≥0∞)
      (thresholdTime ρL ρR (W · p.1) (fun i t => VL i t p.1) (fun j t => VR j t p.1))
    have hleσ : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ L → t ≤ σ n p.1 := fun t ht =>
      (ENNReal.coe_le_coe.1 (ht.trans (min_le_left _ _))).trans (locN_le_σ n p.1)
    have hcol : ∀ u : ℝ≥0, 0 < u → (u : ℝ≥0∞) < L →
        ColliderNe ρL (sysW W (σ n) · p.1) (fun i t => sysVL W VL (σ n) i t p.1) u ∧
        ColliderNe ρR (sysW W (σ n) · p.1) (fun j t => sysVR W VR (σ n) j t p.1) u := by
      intro u _ hu
      have hus := hleσ u hu.le
      have hc := colliderNe_of_not_thresholdCondition
        (notMem_thresholdSet_of_lt (hu.trans_le (min_le_right _ _)))
      simpa only [ColliderNe, sysW_of_le hus, hK.sysVL_of_le (hσT n) hus,
        hK.sysVR_of_le (hσT n) hus] using hc
    set b' : ℝ≥0 → ℝ := fun t => (sysW W (σ n) t p.1 + (1 / 2) * ((∑ i, ρL i * (sysVL W VL (σ n) i t p.1 -
      VL i 0 p.1)) + ∑ j, ρR j * (sysVR W VR (σ n) j t p.1 - VR j 0 p.1))) / Real.sqrt κ with hb'
    have hw' : ∀ t, sysW W (σ n) t p.1 = Real.sqrt κ * b' t - (1 / 2) * ((∑ i, ρL i *
        (sysVL W VL (σ n) i t p.1 - VL i 0 p.1)) + ∑ j, ρR j * (sysVR W VR (σ n) j t p.1 - VR j 0 p.1)) :=
      fun t => by simp only [hb']; field_simp; ring
    have hle : ∀ t : ℝ≥0, (t : ℝ≥0∞) < L →
        (t : WithTop ℝ≥0) ≤ (S n p.1 : WithTop ℝ≥0) := fun t ht => by
      rw [hSp]
      exact WithTop.coe_le_coe.2 (ENNReal.coe_le_coe.1 (ht.le.trans (min_le_left _ _)))
    have hE := isWordEntrance_of_forceDefect_eq_zero (a := κ) (b := b') (xL := fun i => VL i 0 p.1)
      (xR := fun j => VR j 0 p.1) (sysW_zero hK.w_zero p.1) (fun i => hK.sysVL_of_le (hσT n) zero_le i)
      (fun j => hK.sysVR_of_le (hσT n) zero_le j) (hK.continuous_sysW (hσT n) p.1)
      (fun i => hK.isForcePath_sysVL (hσT n) p.1 i) (fun j => hK.isForcePath_sysVR (hσT n) p.1 j)
      (fun t _ => contV_left_le_contW t) (fun t _ => contW_le_contV_right t)
      (hK.antitone_idx_sysVL (hσT n) p.1) (hK.monotone_idx_sysVR (hσT n) p.1) hw'
      (fun t ht i => hLp t (hle t ht)
        (fun u hu hut => (hcol u hu ((ENNReal.coe_le_coe.2 hut).trans_lt ht)).1) i)
      (fun t ht j => hRp t (hle t ht)
        (fun u hu hut => (hcol u hu ((ENNReal.coe_le_coe.2 hut).trans_lt ht)).2) j)
    have hEB := IsWordEntrance.congr_b hE (b' := (B · p)) fun t ht => by
      have h := hW' t p (hle t ht)
      simp only [hb']
      rw [div_eq_iff hsk]
      linarith
    exact Sec7.PocketMartLife.isWordEntrance_congr_le hEB
      (fun t ht => (sysW_of_le (hleσ t ht)).symm)
      (fun t ht i => (hK.sysVL_of_le (hσT n) (hleσ t ht) i).symm)
      (fun t ht j => (hK.sysVR_of_le (hσT n) (hleσ t ht) j).symm)
      (fun _ _ => rfl)
  -- the killed word before `T`
  have hGae : ∀ᵐ p ∂(P.prod P₀), p.1 ∈ G :=
    Measure.quasiMeasurePreserving_fst.ae (ae_iff.2 hGc)
  filter_upwards [ae_all_iff.2 hTan, hGae] with p hp hpG
  refine Sec7.PocketMartLife.isWordEntrance_of_forall (fun n => hp n hpG) ?_
  intro t ht
  have htT : (t : WithTop ℝ≥0) < T p.1 := ht.trans_le (min_le_left _ _)
  obtain ⟨r, htr, hrT⟩ := WithTop.lt_iff_exists_coe_btwn.1 htT
  obtain ⟨n, hn⟩ := hGex p.1 hpG r hrT
  refine ⟨n, lt_min ?_ (ht.trans_le (min_le_right _ _))⟩
  exact ENNReal.coe_lt_coe.2 ((WithTop.coe_lt_coe.1 htr).trans_le hn)

end InteractingSLE.Sec5.CrossCond.Gen
