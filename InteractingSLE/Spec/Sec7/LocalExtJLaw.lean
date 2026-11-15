/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtJCont

/-!
# (U): uniqueness in law through the local stop

Packet PROVE-LOCEXT-J. **`stoppedTwoSeedLawStatement`**: PROVE-LOCEXT-H's named input `StoppedTwoSeedLawStatement κ`
holds for every `κ > 0`: the merged two-seed history of a stopped seed coupling, stopped at its local stop `S`, has the
law of a two-seed reference's history stopped at its capped local stop (empty seed sides normalized).

Proof (Theorem 2.2's entrance argument, step 4, through the local stop):

1. under the measure `Q'` of clause (a) the stopped history has the same law as under `Q`, and the driver and the seed
   marks continue after `S` to an evolution `G` of the **seed-only word** (`IsStoppedSeedCoupling.exists_seedCont`);
2. the reference, read as an evolution of the same seed-only word (`IsIntegratedSLEEvolution.splitSeed`), has infinite
   lifetime; so has `G` (`ae_lifetime_eq_top_of_twin`), and the two dyadic codes have the same law
   (`map_stCode_eq_of_top`, Theorem 2.2's uniqueness in law);
3. both stopped histories are one measurable function of the code (`histOfCode`): for the reference directly; for `G`
   because `G` agrees with the original processes through `S`, and the local stop of `G`'s driver is `S` unless that
   driver pauses at the level `r/4` (`localStopPath_eq_of_not_isLevelPause`), which has probability `0`: the code law is
   the reference's, whose driver does not pause (`ae_not_isLevelPause_twoSeed`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace LocalExt

open Sec2 Sec2.Assembly Sec2.Assembly2 Sec2.Assembly3 Sec7

/-- The seed mark recorded on the left side of a seed-only code (`none` without a seed). -/
def seedPick (m : ℕ) : Option (Fin m) := if h : 0 < m then some ⟨0, h⟩ else none

theorem seedPick_of_pos {m : ℕ} (h : 0 < m) : seedPick m = some ⟨0, h⟩ := by simp [seedPick, h]

theorem seedPick_of_zero {m : ℕ} (h : ¬ 0 < m) : seedPick m = none := by simp [seedPick, h]

/-- The value recorded by `histOfCode` on one side, through a decoded code. -/
theorem seedVal_eq_pick {n : ℕ} {x : Fin n → ℝ} {v : Fin n → ℝ} {w : ℝ}
    (hv : ∀ i k, x i = 0 → x k = 0 → v i = v k) {u : Fin (seedCount x) → ℝ} (hu : ∀ j, u j = v (seedEmb x j)) :
    seedVal x v w = match seedPick (seedCount x) with
      | some j => u j
      | none => w := by
  by_cases h : 0 < seedCount x
  · rw [seedPick_of_pos h]
    show seedVal x v w = u ⟨0, h⟩
    rw [hu]
    exact seedVal_of_eq_zero hv (seedEmb_eq_zero x _)
  · rw [seedPick_of_zero h]
    show seedVal x v w = w
    have hn : ¬ ∃ i, x i = 0 := fun hex => h ((exists_seed_iff_pos x).1 hex)
    simp only [seedVal, hn, ↓reduceDIte]

/-- **(U): uniqueness in law through the local stop** (PROVE-LOCEXT-H's `StoppedTwoSeedLawStatement`). -/
theorem stoppedTwoSeedLawStatement {κ : ℝ} (hκ : 0 < κ) : StoppedTwoSeedLawStatement.{u} κ := by
  intro nL nR xL xR ρL ρR r hF hr hL hR Ω mΩ Q hQ W VL VR S h hc Ωr mΩr Pr hPr 𝓕r Wr VLr VRr Br ζr hEr Gr hGm hG0 hG
  classical
  obtain ⟨Q', hQ', 𝓖, Gw, GVL, GVR, BG, ζG, hY, hY', hlaw, hEG, hgood⟩ := hc.exists_seedCont hκ hr hL hR
  -- the reference as a seed-only evolution
  have hEr' : IsIntegratedSLEEvolution κ (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0) (fun _ => seedSumL xL ρL)
      (fun _ => seedSumR xR ρR) Pr 𝓕r Wr VLr VRr Br ζr := hEr
  have hζr : ∀ᵐ ω ∂Pr, ζr ω = ⊤ := ae_lifetime_eq_top_twoSeed hκ hEr' hL hR
  set VLs : Fin (seedCount xL) → ℝ≥0 → Ωr → ℝ := fun _ => VLr 0 with hVLs
  set VRs : Fin (seedCount xR) → ℝ≥0 → Ωr → ℝ := fun _ => VRr 0 with hVRs
  have hEs : IsIntegratedSLEEvolution κ (fun _ : Fin (seedCount xL) => 0) (fun _ : Fin (seedCount xR) => 0)
      (seedWL xL ρL) (seedWR xR ρR) Pr 𝓕r Wr VLs VRs Br ζr :=
    IsIntegratedSLEEvolution.splitSeed hEr' hζr (sum_seedEmb_L xL ρL) (sum_seedEmb_R xR ρR)
  have hζG : ∀ᵐ ω ∂Q', ζG ω = ⊤ := ae_lifetime_eq_top_of_twin hκ isOrderedForceWord_zero hEs hζr hEG
  have hcode := map_stCode_eq_of_top hκ isOrderedForceWord_zero hEG hζG hEs hζr
  -- `G`'s driver does not pause at `r/4`
  have hr4 : 0 < r / 4 := by positivity
  have hnoP : ∀ᵐ ω ∂Q', ¬ IsLevelPause (r / 4) (Gw · ω) := by
    have h1 := ae_not_isLevelPause_twoSeed hκ hL hR hEr' hr4
    rw [ae_iff] at h1 ⊢
    simp only [not_not] at h1 ⊢
    rw [measure_isLevelPause_eq hEG hζG, hcode, ← measure_isLevelPause_eq hEs hζr]
    exact h1
  -- the history read from the code
  set Φ := histOfCode (nL := seedCount xL) (nR := seedCount xR) r (seedPick (seedCount xL)) (seedPick (seedCount xR))
    with hΦ
  have hΦm : Measurable Φ := measurable_histOfCode r _ _
  -- claim A: the stopped coupling's history
  have hA : ∀ᵐ ω ∂Q', twoSeedProj xL xR (stoppedHistory (drivingState W VL VR) S ω) =
      Φ (stCode ζG Gw GVL GVR BG ω) := by
    filter_upwards [hgood, hζG, hEG.2.2.2.2, hnoP] with ω ⟨hreg, ⟨ζ₀, hSζ, hSl, hWc⟩, hW0, hcoL, hcoR, hagree⟩ hζω hp hnp
    obtain ⟨hmem, hdW, hdL, hdR⟩ := stCode_decode_of_top hζω hp
    rw [hζω] at hp
    obtain ⟨hGwc, hGLc, hGRc⟩ := continuous_of_isIntegratedSLEPath_top hp
    obtain ⟨hS0, hSfin, hcont⟩ := hreg
    obtain ⟨S₀, hS₀⟩ := WithTop.ne_top_iff_exists.1 hSfin
    have hS₀' : S ω = S₀ := hS₀.symm
    have hS₀0 : 0 < S₀ := by rw [hS₀'] at hS0; exact_mod_cast hS0
    have hIic : {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ S ω} = Iic S₀ := by
      ext t; simp only [mem_ofPred_eq, mem_Iic, hS₀', WithTop.coe_le_coe]
    have hcW : ContinuousOn (fun t => W t ω) (Iic S₀) := hIic ▸ continuous_fst.comp_continuousOn hcont
    have hcVL : ∀ i, ContinuousOn (fun t => VL i t ω) (Iic S₀) := fun i => hIic ▸
      (continuous_apply i).comp_continuousOn (continuous_fst.comp_continuousOn (continuous_snd.comp_continuousOn hcont))
    have hcVR : ∀ j, ContinuousOn (fun t => VR j t ω) (Iic S₀) := fun j => hIic ▸
      (continuous_apply j).comp_continuousOn (continuous_snd.comp_continuousOn (continuous_snd.comp_continuousOn hcont))
    have hlt : ∀ t : ℝ≥0, t < S₀ → (t : WithTop ℝ≥0) < S ω := fun t ht => by rw [hS₀']; exact_mod_cast ht
    -- agreement through `S`
    have hW : ∀ t ≤ S₀, Gw t ω = W t ω := fun t ht => by
      rcases lt_or_eq_of_le ht with h1 | rfl
      · exact (hagree t (hlt t h1)).1
      · exact eq_of_eqOn_Iio hS₀0 hGwc.continuousOn hcW fun s hs => (hagree s (hlt s hs)).1
    have hVLe : ∀ j, ∀ t ≤ S₀, GVL j t ω = VL (seedEmb xL j) t ω := fun j t ht => by
      rcases lt_or_eq_of_le ht with h1 | rfl
      · exact (hagree t (hlt t h1)).2.1 j
      · exact eq_of_eqOn_Iio hS₀0 (hGLc j).continuousOn (hcVL _) fun s hs => (hagree s (hlt s hs)).2.1 j
    have hVRe : ∀ j, ∀ t ≤ S₀, GVR j t ω = VR (seedEmb xR j) t ω := fun j t ht => by
      rcases lt_or_eq_of_le ht with h1 | rfl
      · exact (hagree t (hlt t h1)).2.2 j
      · exact eq_of_eqOn_Iio hS₀0 (hGRc j).continuousOn (hcVR _) fun s hs => (hagree s (hlt s hs)).2.2 j
    -- the local stop of `G`'s driver
    have hloc : locStopCode r (stCode ζG Gw GVL GVR BG ω) = S ω := by
      simp only [locStopCode, hmem, ↓reduceIte, hdW]
      rw [hS₀']
      have hSζ' : ((S₀ : ℝ≥0) : ℝ≥0∞) < ζ₀ := by
        have := hSζ
        rw [hS₀'] at this
        exact this
      exact localStopPath_eq_of_not_isLevelPause hr hWc hW0 (hSl.symm.trans hS₀') hSζ' (fun s hs => hW s hs) hnp
    -- the components
    have hstop : ∀ q : ℚ≥0, stopAt S (q : ℝ≥0) ω ≤ S₀ := fun q => by
      rw [stopAt_of_eq_coe hS₀']; exact min_le_right _ _
    refine Prod.ext (by simp only [twoSeedProj, stoppedHistory, hΦ, histOfCode, hloc]) (funext fun q => ?_)
    have hT : min (q : ℝ≥0) ((locStopCode r (stCode ζG Gw GVL GVR BG ω)).untopD (q : ℝ≥0)) =
        stopAt S (q : ℝ≥0) ω := by rw [hloc]; rfl
    simp only [twoSeedProj, stoppedHistory, drivingState, hΦ, histOfCode, hT, hdW]
    refine Prod.ext (hW _ (hstop q)).symm (Prod.ext (funext fun _ => ?_) (funext fun _ => ?_))
    · simp only
      rw [seedVal_eq_pick (fun i k hi hk => hcoL i k hi hk _ (by rw [hS₀']; exact WithTop.coe_le_coe.2 (hstop q)))
        (u := fun j => GVL j (stopAt S (q : ℝ≥0) ω) ω) fun j => hVLe j _ (hstop q)]
      cases seedPick (seedCount xL) with
      | some j => simp only [hdL]
      | none => simp only [hW _ (hstop q)]
    · simp only
      rw [seedVal_eq_pick (fun i k hi hk => hcoR i k hi hk _ (by rw [hS₀']; exact WithTop.coe_le_coe.2 (hstop q)))
        (u := fun j => GVR j (stopAt S (q : ℝ≥0) ω) ω) fun j => hVRe j _ (hstop q)]
      cases seedPick (seedCount xR) with
      | some j => simp only [hdR]
      | none => simp only [hW _ (hstop q)]
  -- claim B: the reference's history
  have hB : ∀ᵐ ω ∂Pr, refRecHist xL xR r Gr Wr VLr VRr ζr ω =
      Φ (stCode ζr Wr VLs VRs Br ω) := by
    have hGr : ∀ᵐ ω ∂Pr, ω ∈ Gr := ae_iff.2 (by exact hG0)
    filter_upwards [hGr, hζr, hEs.2.2.2.2] with ω hω hζω hp
    obtain ⟨hmem, hdW, hdL, hdR⟩ := stCode_decode_of_top hζω hp
    have hcap : capStop r Gr ζr Wr ω = locStopCode r (stCode ζr Wr VLs VRs Br ω) := by
      simp only [capStop, localStop_of_mem hω, hζω, locStopCode, hmem, ↓reduceIte, hdW]
      exact min_eq_left le_top
    have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζr ω := fun t => by rw [hζω]; exact ENNReal.coe_lt_top
    refine Prod.ext (by simp only [refRecHist, seedProj, stoppedHistory, hΦ, histOfCode, hcap]) (funext fun q => ?_)
    have hT : min (q : ℝ≥0) ((locStopCode r (stCode ζr Wr VLs VRs Br ω)).untopD
        (q : ℝ≥0)) = stopAt (capStop r Gr ζr Wr) (q : ℝ≥0) ω := by rw [← hcap]; rfl
    simp only [refRecHist, seedProj, stoppedHistory, completedState, hlt, ↓reduceIte, drivingState, hΦ, histOfCode,
      hT, hdW]
    refine Prod.ext rfl (Prod.ext (funext fun _ => ?_) (funext fun _ => ?_))
    · by_cases hs : ∃ i, xL i = 0
      · simp only [hs, ↓reduceIte, seedPick_of_pos ((exists_seed_iff_pos xL).1 hs)]
        rw [hdL]
      · simp only [hs, ↓reduceIte, seedPick_of_zero fun h => hs ((exists_seed_iff_pos xL).2 h)]
    · by_cases hs : ∃ j, xR j = 0
      · simp only [hs, ↓reduceIte, seedPick_of_pos ((exists_seed_iff_pos xR).1 hs)]
        rw [hdR]
      · simp only [hs, ↓reduceIte, seedPick_of_zero fun h => hs ((exists_seed_iff_pos xR).2 h)]
  -- the laws
  have hmG := measurable_stCode_of_evolution hEG
  have hmr := measurable_stCode_of_evolution hEs
  calc Q.map (fun ω => twoSeedProj xL xR (stoppedHistory (drivingState W VL VR) S ω))
      = (Q.map (stoppedHistory (drivingState W VL VR) S)).map (twoSeedProj xL xR) :=
        (AEMeasurable.map_map_of_aemeasurable (measurable_twoSeedProj xL xR).aemeasurable hY).symm
    _ = (Q'.map (stoppedHistory (drivingState W VL VR) S)).map (twoSeedProj xL xR) := by rw [hlaw]
    _ = Q'.map (fun ω => twoSeedProj xL xR (stoppedHistory (drivingState W VL VR) S ω)) :=
        AEMeasurable.map_map_of_aemeasurable (measurable_twoSeedProj xL xR).aemeasurable hY'
    _ = Q'.map (fun ω => Φ (stCode ζG Gw GVL GVR BG ω)) := Measure.map_congr hA
    _ = (Q'.map (stCode ζG Gw GVL GVR BG)).map Φ := (Measure.map_map hΦm hmG).symm
    _ = (Pr.map (stCode ζr Wr VLs VRs Br)).map Φ := by rw [hcode]
    _ = Pr.map (fun ω => Φ (stCode ζr Wr VLs VRs Br ω)) := Measure.map_map hΦm hmr
    _ = Pr.map (refRecHist xL xR r Gr Wr VLr VRr ζr) := (Measure.map_congr hB).symm

end LocalExt

end InteractingSLE
