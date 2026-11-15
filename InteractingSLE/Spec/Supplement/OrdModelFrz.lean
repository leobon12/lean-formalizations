/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.OrdAStopDrive
import InteractingSLE.Spec.Restart.StoppedK2ClauseFrz
import InteractingSLE.Spec.Restart.FCK2SourceCollision
import InteractingSLE.Spec.Sec7.PocketMartLife

/-!
# The original end of an A-stopped continuation is announced in the killed driving filtration

Packet PROVE-T15-ASTOP2. PROVE-T15-ASTOP's announcement of the A-stop (`OrdAStop.exists_isAnnouncingSeq_aStop`) needs,
besides the blowup of `1 / dist(γ, I_A)`, an announced time `ζ₂ ≥ V` that equals `V` when the continuation ends without
an A-contact (its original end, a threshold of its word). The driver is only observed before `V` in the killed driving
filtration, so its threshold is read through the **frozen driver** `frzDrv V W` (`StoppedK2.frz`, set to `0` on
`{V = 0}`), which is adapted to the killed driving filtration, continuous at every sample, and equal to `W` on `[0, V]`:

* `stronglyAdapted_frzDrv`, `continuous_frzDrv`, `frzDrv_eq`;
* `le_thr_frzDrv`: if `0 < V ≤ thr W`, then `V ≤ thr (frzDrv V W)`;
* `thr_frzDrv_eq`: if `0 < V = thr W`, then `thr (frzDrv V W) = V`;
* **`exists_isAnnouncingSeq_thr_frzDrv`**: `thr (frzDrv V W)` has an announcing sequence in the killed driving
  filtration enlarged by a code `e` (`OrdAStop.drivingSupCode`), as soon as the force positions are functions of the
  code and `0 < V ≤ thr W` almost surely (`FCDet.exists_isAnnouncingSeq_thr`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.RLC.OrdModel

open Restart Restart.StoppedK2 Restart.FCDet Sec7.PocketTraversal

variable {Ω : Type*} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **The driver frozen at a positive lifetime** (`StoppedK2.frz`), and `0` on `{V = 0}`. -/
def frzDrv (V : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if 0 < V ω then frz V W t ω else 0

theorem frzDrv_eq {V : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {ω : Ω} (hc : Continuous (W · ω)) (hV0 : 0 < V ω)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ V ω) : frzDrv V W t ω = W t ω := by
  simp only [frzDrv, hV0, ↓reduceIte]
  by_cases hVt : V ω = ⊤
  · exact frz_of_eq_top hVt t
  · rw [frz_eq_min hV0 hVt hc.continuousOn t, min_eq_left]
    simpa using ENNReal.toNNReal_mono hVt ht

theorem continuous_frzDrv {V : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} (hc : ∀ ω, Continuous (W · ω)) (ω : Ω) :
    Continuous (frzDrv V W · ω) := by
  by_cases hV0 : 0 < V ω
  · have e : (frzDrv V W · ω) = (frz V W · ω) := funext fun t => by simp only [frzDrv, hV0, ↓reduceIte]
    rw [e]
    by_cases hVt : V ω = ⊤
    · have e' : (frz V W · ω) = (W · ω) := funext fun t => frz_of_eq_top hVt t
      rw [e']
      exact hc ω
    · exact continuous_frz hV0 hVt (hc ω).continuousOn
  · have e : (frzDrv V W · ω) = fun _ => 0 := funext fun t => by simp only [frzDrv, hV0, ↓reduceIte]
    rw [e]
    exact continuous_const

theorem stronglyAdapted_frzDrv [MeasurableSpace Ω] {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} (hXP : IsMeasurableKilledDriving W VL VR V) :
    StronglyAdapted (killedDrivingFiltration hXP) (frzDrv V W) := fun t => by
  refine Measurable.stronglyMeasurable ?_
  have h1 : Measurable[killedDrivingFiltration hXP t] (frz V W t) :=
    measurable_frz (Coupling.adaptedBefore_killedDriving_W hXP) t
  have h0 : MeasurableSet[killedDrivingFiltration hXP t] {ω | 0 < V ω} := by
    have h := RetLeaf.measurableSet_live_killedDrivingSigma (W := W) (VL := VL) (VR := VR) (ζ := V) 0
    simp only [ENNReal.coe_zero] at h
    exact (killedDrivingFiltration hXP).mono (zero_le : (0 : ℝ≥0) ≤ t) _ h
  exact Measurable.ite h0 h1 measurable_const

/-- The geometric force images of two drivers agreeing on `[0, t]` agree at `t`. -/
theorem threshold_congr {W W' : ℝ≥0 → Ω → ℝ} {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {ω : Ω}
    (hc' : Continuous (W' · ω)) {t : ℝ≥0} (h : ∀ s ≤ t, W s ω = W' s ω) :
    ForceWord.ThresholdCondition ρL ρR (W t ω) (fun i => geomLW W xL i t ω) (fun j => geomRW W xR j t ω) ↔
      ForceWord.ThresholdCondition ρL ρR (W' t ω) (fun i => geomLW W' xL i t ω)
        (fun j => geomRW W' xR j t ω) := by
  have hL : (fun i => geomLW W xL i t ω) = fun i => geomLW W' xL i t ω :=
    funext fun i => Sec7.PocketMartLife.geomLW_congr hc' h xL i
  have hR : (fun j => geomRW W xR j t ω) = fun j => geomRW W' xR j t ω :=
    funext fun j => Sec7.PocketMartLife.geomRW_congr hc' h xR j
  rw [hL, hR, h t le_rfl]

/-- **Freezing at a lifetime before the threshold keeps the threshold beyond the lifetime.** -/
theorem le_thr_frzDrv {V : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} (hc : ∀ ω, Continuous (W · ω))
    (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ) {ω : Ω} (hV0 : 0 < V ω)
    (hV : V ω ≤ thr ρL ρR W xL xR ω) : V ω ≤ thr ρL ρR (frzDrv V W) xL xR ω := by
  have hfc := continuous_frzDrv (V := V) hc
  by_cases hVt : V ω = ⊤
  · have he : ∀ t, frzDrv V W t ω = W t ω := fun t => frzDrv_eq (hc ω) hV0 (by rw [hVt]; exact le_top)
    rw [FCDet.thr_congr (ρL := ρL) (ρR := ρR) (xL := xL) (xR := xR) (xL' := xL) (xR' := xR) he rfl rfl]
    exact hV
  · by_contra hlt
    rw [not_le] at hlt
    have hfin : thr ρL ρR (frzDrv V W) xL xR ω ≠ ⊤ := ne_top_of_lt hlt
    set T := (thr ρL ρR (frzDrv V W) xL xR ω).toNNReal with hT
    have hTe : thr ρL ρR (frzDrv V W) xL xR ω = T := (ENNReal.coe_toNNReal hfin).symm
    obtain ⟨t, htT, hcond⟩ := (MartChar.thresholdTime_le_iff (hfc ω)
      (fun i => (isForcePath_geomLW hfc xL ω i).1) (fun j => (isForcePath_geomRW hfc xR ω j).1)
      (fun i j s r hsr he => geomLW_merge hfc xL ω i j s r hsr he)
      (fun i j s r hsr he => geomRW_merge hfc xR ω i j s r hsr he) T).1 hTe.le
    have htV : (t : ℝ≥0∞) < V ω := lt_of_le_of_lt (by rw [hTe]; exact_mod_cast htT) hlt
    have hag : ∀ s ≤ t, frzDrv V W s ω = W s ω := fun s hs =>
      frzDrv_eq (hc ω) hV0 ((ENNReal.coe_le_coe.2 hs).trans htV.le)
    have hW : ForceWord.ThresholdCondition ρL ρR (W t ω) (fun i => geomLW W xL i t ω)
        (fun j => geomRW W xR j t ω) := (threshold_congr (hc ω) hag).1 hcond
    have := FCPlumb.thr_le_of_force_threshold hc hW
    exact absurd (hV.trans this) (not_le.2 htV)

/-- **At a lifetime equal to the threshold, the frozen driver has the same threshold.** -/
theorem thr_frzDrv_eq {V : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} (hc : ∀ ω, Continuous (W · ω))
    (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ) {ω : Ω} (hV0 : 0 < V ω)
    (hV : V ω = thr ρL ρR W xL xR ω) : thr ρL ρR (frzDrv V W) xL xR ω = V ω := by
  refine le_antisymm ?_ (le_thr_frzDrv hc xL xR hV0 hV.le)
  by_cases hVt : V ω = ⊤
  · rw [hVt]
    exact le_top
  · set v := (V ω).toNNReal with hv
    have hve : V ω = v := (ENNReal.coe_toNNReal hVt).symm
    have hmem := thr_mem_thresholdSet (ρL := ρL) (ρR := ρR) hc xL xR (T := v) (hv ▸ hve ▸ hV.symm)
    have hag : ∀ s ≤ v, W s ω = frzDrv V W s ω := fun s hs =>
      (frzDrv_eq (hc ω) hV0 (hve ▸ ENNReal.coe_le_coe.2 hs)).symm
    have hcond := (threshold_congr (continuous_frzDrv hc ω) hag).1 hmem
    rw [hve]
    exact FCPlumb.thr_le_of_force_threshold (continuous_frzDrv hc) hcond

/-- **The threshold of the frozen driver is announced in the killed driving filtration enlarged by a code** that
determines the force positions, as soon as `0 < V ≤ thr W` almost surely. -/
theorem exists_isAnnouncingSeq_thr_frzDrv [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hXP : IsMeasurableKilledDriving W VL VR V) {e : Ω → ℝ} (hem : Measurable e)
    (hc : ∀ ω, Continuous (W · ω)) {gL : ℝ → Fin nL → ℝ} {gR : ℝ → Fin nR → ℝ} (hgL : Measurable gL)
    (hgR : Measurable gR) (hgLa : ∀ c, Antitone (gL c)) (hgRm : ∀ c, Monotone (gR c))
    (hpos : ∀ᵐ ω ∂Q, 0 < V ω ∧ V ω ≤ thr ρL ρR W (fun ω => gL (e ω)) (fun ω => gR (e ω)) ω) :
    ∃ b : ℕ → Ω → ℝ≥0, Coupling.IsAnnouncingSeq (OrdAStop.drivingSupCode Q hXP hem) Q
      (thr ρL ρR (frzDrv V W) (fun ω => gL (e ω)) (fun ω => gR (e ω))) b := by
  set 𝓖 := OrdAStop.drivingSupCode Q hXP hem with h𝓖
  have hk : ∀ t, killedDrivingFiltration hXP t ≤ 𝓖 t := fun t =>
    (OrdAStop.le_supConst (killedDrivingFiltration hXP) _ hem.comap_le t).trans (Ito.le_usualAugmentation _ Q t)
  have he0 : Measurable[𝓖 0] e := (comap_measurable e).mono
    ((OrdAStop.le_supConst_const (killedDrivingFiltration hXP) _ hem.comap_le 0).trans
      (Ito.le_usualAugmentation _ Q 0)) le_rfl
  have hWa : StronglyAdapted 𝓖 (frzDrv V W) := fun t => (stronglyAdapted_frzDrv hXP t).mono (hk t)
  obtain ⟨b, hb, -⟩ := exists_isAnnouncingSeq_thr (𝓖 := 𝓖) (P := Q) (ρL := ρL) (ρR := ρR)
    (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0) (continuous_frzDrv hc) hWa
    (hgL.comp he0) (hgR.comp he0) (fun ω => hgLa (e ω)) (fun ω => hgRm (e ω))
    (hpos.mono fun ω h => lt_of_lt_of_le h.1 (le_thr_frzDrv hc _ _ h.1 h.2))
  exact ⟨b, hb⟩

end InteractingSLE.RLC.OrdModel
