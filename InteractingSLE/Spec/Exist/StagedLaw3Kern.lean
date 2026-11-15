/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedLaw3Path
import InteractingSLE.Spec.Coupling.WholeField4Birth

/-!
# The announced kernel at the stop, path by path

Packet PROVE-STAGEDLAW3. On one good path (an integrated `SLE_κ(ρ)` path with Aux. lemma 3's terminal limit, driven by
a regular driver whose record at the finite stop `T = min t ζ` is good):

* `IsGoodStopPath.tendsto_right`, `IsGoodStopPath.tendsto_left`: along stops `sₙ → T` (`sₙ < ζ`) the centred mark
  positions converge to the positions read from the record (`markPos`, `markPosL`);
* `IsGoodStopPath.eqOn_bheAt`: the bounded harmonic extension of the force data at time `s < ζ` is the force word's mean
  plus `θχ`;
* **`IsGoodStopPath.tendsto_integral_couplingMean`**: the tested coupling means `∫ 𝔥_{sₙ} φ` (with the frozen driver)
  converge to the tested mean at the stop with the record driver and the stop word, for `φ` supported off the hull at
  the stop;
* **`IsGoodStopPath.tendsto_zeroGFFTestCov`**: the same for the Green energies of the remaining domains.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Exist

namespace StagedLaw

open QuantumZipper Staged Restart LQGMetric

section PathMarks

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}

/-- **One good path at a finite stop.** -/
def IsGoodStopPath (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (t : ℝ≥0∞)
    (e : (ℝ≥0 → ℝ) × ℝ≥0∞) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (b : ℝ≥0 → ℝ) : Prop :=
  IsIntegratedSLEPath κ xL xR ρL ρR e.1 vL vR b e.2 ∧
    (∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = e.2 → ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
      Tendsto (fun s => (e.1 s, fun i => vL i s, fun i => vR i s)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀))) ∧
    IsRegularDriver e ∧ LocalExt.IsDrvGood (recHist (recOf t e)) ∧ min t e.2 ≠ ⊤ ∧ 0 < e.2

theorem IsGoodStopPath.stop_le (h : IsGoodStopPath κ xL xR ρL ρR t e vL vR b) :
    (((min t e.2).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ e.2 := by
  rw [ENNReal.coe_toNNReal h.2.2.2.2.1]
  exact min_le_right _ _

theorem IsGoodStopPath.rdrv_eq (h : IsGoodStopPath κ xL xR ρL ρR t e vL vR b) (s : ℝ≥0)
    (hs : s ≤ (min t e.2).toNNReal) : rdrv (recOf t e) s = e.1 s := by
  rw [rdrv_recOf_eq h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 (by rw [rtime_recOf_coe]; exact_mod_cast hs),
    Real.toNNReal_coe]

theorem IsGoodStopPath.stop_pos (h : IsGoodStopPath κ xL xR ρL ρR t e vL vR b) {T : ℝ≥0}
    (hT : (T : ℝ≥0∞) = e.2) : 0 < T := by
  have := h.2.2.2.2.2
  rw [← hT] at this
  exact_mod_cast this

/-- **The right marks converge to the positions read from the record.** -/
theorem IsGoodStopPath.tendsto_right (h : IsGoodStopPath κ xL xR ρL ρR t e vL vR b) (j : Fin nR)
    {s : ℕ → ℝ≥0} (hsζ : ∀ n, (s n : ℝ≥0∞) < e.2) (hsT : Tendsto s atTop (𝓝 (min t e.2).toNNReal)) :
    Tendsto (fun n => vR j (s n) - e.1 (s n)) atTop
      (𝓝 (markPos (rdrv (recOf t e)) (rtime (recOf t e)) (xR j))) := by
  have hthr := h.2.1
  obtain ⟨-, -, -, h4, -, h6, -, -, h9, -, -, h12, -, -, h15, -, h17, -⟩ := h.1
  refine tendsto_gap_markPos (continuous_rdrv _) (rdrv_zero _) h.stop_le
    (fun s hs _ => h.rdrv_eq s hs) h4 (h6 j) (fun t ht => h9 t ht j) (fun t ht => h15 t ht j)
    (fun t ht => h12 t ht j) (h17 j) (fun hT => ⟨h.stop_pos hT, ?_⟩) hsζ hsT
  obtain ⟨w₀, vL₀, vR₀, hlim⟩ := hthr _ (h.stop_pos hT) hT
  refine ⟨vR₀ j - w₀, ?_⟩
  have h1 : Tendsto (fun s => vR j s) (𝓝[<] (min t e.2).toNNReal) (𝓝 (vR₀ j)) :=
    ((continuous_apply j).tendsto _).comp ((continuous_snd.comp continuous_snd).tendsto _ |>.comp hlim)
  have h2 : Tendsto (fun s => e.1 s) (𝓝[<] (min t e.2).toNNReal) (𝓝 w₀) :=
    (continuous_fst.tendsto _).comp hlim
  exact h1.sub h2

/-- **The left marks converge to the positions read from the record** (by reflection). -/
theorem IsGoodStopPath.tendsto_left (h : IsGoodStopPath κ xL xR ρL ρR t e vL vR b) (i : Fin nL)
    {s : ℕ → ℝ≥0} (hsζ : ∀ n, (s n : ℝ≥0∞) < e.2) (hsT : Tendsto s atTop (𝓝 (min t e.2).toNNReal)) :
    Tendsto (fun n => vL i (s n) - e.1 (s n)) atTop
      (𝓝 (markPosL (rdrv (recOf t e)) (rtime (recOf t e)) (xL i))) := by
  have hthr := h.2.1
  obtain ⟨-, -, -, h4, h5, -, -, h8, -, -, h11, -, -, h14, -, h16, -, -⟩ := h.1
  have heq : ∀ t' : ℝ≥0, (t' : ℝ≥0∞) < e.2 → -vL i t' = -xL i +
      ∫ s in (0 : ℝ)..t', 2 / (-vL i s.toNNReal - -e.1 s.toNNReal) := by
    intro t' ht'
    rw [h14 t' ht' i]
    have : (∫ s in (0 : ℝ)..t', 2 / (-vL i s.toNNReal - -e.1 s.toNNReal)) =
        -∫ s in (0 : ℝ)..t', 2 / (vL i s.toNNReal - e.1 s.toNNReal) := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun s _ => ?_
      show 2 / (-vL i s.toNNReal - -e.1 s.toNNReal) = -(2 / (vL i s.toNNReal - e.1 s.toNNReal))
      rw [show -vL i s.toNNReal - -e.1 s.toNNReal = -(vL i s.toNNReal - e.1 s.toNNReal) by ring, div_neg]
    rw [this]
    ring
  have hint : ∀ t' : ℝ≥0, (t' : ℝ≥0∞) < e.2 →
      IntervalIntegrable (fun s : ℝ => (-e.1 s.toNNReal - -vL i s.toNNReal)⁻¹) volume 0 t' := by
    intro t' ht'
    refine (h11 t' ht' i).neg.congr fun s _ => ?_
    change -(e.1 s.toNNReal - vL i s.toNNReal)⁻¹ = (-e.1 s.toNNReal - -vL i s.toNNReal)⁻¹
    rw [show -e.1 s.toNNReal - -vL i s.toNNReal = -(e.1 s.toNNReal - vL i s.toNNReal) by ring, inv_neg]
  have hnull : volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < e.2 ∧ -e.1 s.toNNReal = -vL i s.toNNReal} = 0 := by
    refine measure_mono_null (fun s hs => ?_) (h16 i)
    exact ⟨hs.1, hs.2.1, neg_inj.1 hs.2.2⟩
  have hmain := tendsto_gap_markPos (w := fun s => -e.1 s) (v := fun s => -vL i s) (x := -xL i)
    (D := fun r => -rdrv (recOf t e) r) (continuous_rdrv _).neg (by simp [rdrv_zero]) h.stop_le
    (fun s hs _ => by show -rdrv (recOf t e) s = -e.1 s; rw [h.rdrv_eq s hs]) h4.neg (h5 i).neg
    (fun t' ht' => neg_le_neg (h8 t' ht' i)) heq
    hint hnull (fun hT => ⟨h.stop_pos hT, ?_⟩) hsζ hsT
  · have e' : (fun n => vL i (s n) - e.1 (s n)) = fun n => -((fun s => -vL i s) (s n) - (fun s => -e.1 s) (s n)) := by
      funext n; ring
    rw [e', markPosL]
    exact hmain.neg
  · obtain ⟨w₀, vL₀, vR₀, hlim⟩ := hthr _ (h.stop_pos hT) hT
    refine ⟨-vL₀ i - -w₀, ?_⟩
    have h1 : Tendsto (fun s => vL i s) (𝓝[<] (min t e.2).toNNReal) (𝓝 (vL₀ i)) :=
      ((continuous_apply i).tendsto _).comp ((continuous_fst.comp continuous_snd).tendsto _ |>.comp hlim)
    have h2 : Tendsto (fun s => e.1 s) (𝓝[<] (min t e.2).toNNReal) (𝓝 w₀) :=
      (continuous_fst.tendsto _).comp hlim
    exact h1.neg.sub h2.neg

end PathMarks

/-! ### Congruence of the coupling mean in the driver -/

theorem couplingMean_congr {W W' : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) (h : EqOn W W' (Icc 0 t)) (κ : ℝ) (u : ℂ → ℝ)
    (z : ℂ) : couplingMean κ W t u z = couplingMean κ W' t u z := by
  have hL : logDerivFwd W t z = logDerivFwd W' t z := by
    unfold logDerivFwd
    have : (∫ s in (0 : ℝ)..t, 2 / fwdMap W s z ^ 2) = ∫ s in (0 : ℝ)..t, 2 / fwdMap W' s z ^ 2 := by
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le ht] at hr
      simp only [Ito.fwdMap_congr_of_eqOn_of_le h hr.2]
    rw [this]
  unfold couplingMean
  rw [Ito.fwdMap_congr_of_eqOn h, hL]

/-! ### The word mean along a good path -/

section WordPath

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}

/-- The padded centred positions at time `s`, completed by the given limits. -/
def padPos {n : ℕ} (v : Fin n → ℝ≥0 → ℝ) (w : ℝ≥0 → ℝ) (s : ℝ≥0) (p : ℕ → ℝ) (i : ℕ) : ℝ :=
  if hi : i < n then v ⟨i, hi⟩ s - w s else p i

theorem padPos_fin {n : ℕ} (v : Fin n → ℝ≥0 → ℝ) (w : ℝ≥0 → ℝ) (s : ℝ≥0) (p : ℕ → ℝ) (i : Fin n) :
    padPos v w s p i = v i s - w s := by
  simp only [padPos, i.2, ↓reduceDIte, Fin.eta]

theorem isMarkOrder_padPos (hp : IsIntegratedSLEPath κ xL xR ρL ρR e.1 vL vR b e.2) {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) < e.2) (pL pR : ℕ → ℝ) : IsMarkOrder nL nR (padPos vL e.1 s pL) (padPos vR e.1 s pR) := by
  obtain ⟨-, -, -, -, -, -, h7, h8, h9, h10, -⟩ := hp
  refine ⟨fun i j hij hj => ?_, fun i hi => ?_, fun i j hij hj => ?_, fun i hi => ?_⟩
  · rw [padPos_fin vL e.1 s pL ⟨i, by omega⟩, padPos_fin vL e.1 s pL ⟨j, hj⟩]
    have := h7 s hs (show (⟨i, by omega⟩ : Fin nL) ≤ ⟨j, hj⟩ from hij)
    linarith
  · rw [padPos_fin vL e.1 s pL ⟨i, hi⟩]
    linarith [h8 s hs ⟨i, hi⟩]
  · rw [padPos_fin vR e.1 s pR ⟨i, by omega⟩, padPos_fin vR e.1 s pR ⟨j, hj⟩]
    have := h10 s hs (show (⟨i, by omega⟩ : Fin nR) ≤ ⟨j, hj⟩ from hij)
    linarith
  · rw [padPos_fin vR e.1 s pR ⟨i, hi⟩]
    linarith [h9 s hs ⟨i, hi⟩]

/-- **The bounded harmonic extension at time `s < ζ` is the force word's mean plus the shift.** -/
theorem eqOn_bheAt_forceWord (hp : IsIntegratedSLEPath κ xL xR ρL ρR e.1 vL vR b e.2) {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) < e.2) {ρLp ρRp : ℕ → ℝ} (hρL : ∀ i : Fin nL, ρLp i = ρL i) (hρR : ∀ j : Fin nR, ρRp j = ρR j)
    (pL pR : ℕ → ℝ) (θc : ℝ) :
    EqOn (WholeField.bheAt κ ρL ρR (e.1 s) (fun i => vL i s) (fun j => vR j s))
      (fun z => (forceWord κ nL nR (padPos vL e.1 s pL) (padPos vR e.1 s pR) ρLp ρRp θc).mean z + θc) H := by
  have hu := WholeField.bheAt_spec κ ρL ρR (e.1 s) (fun i => vL i s) (fun j => vR j s)
  have e1 : (fun i : Fin nL => ρLp i) = ρL := funext hρL
  have e2 : (fun j : Fin nR => ρRp j) = ρR := funext hρR
  have e3 : (fun i : Fin nL => padPos vL e.1 s pL i) = fun i => vL i s - e.1 s := funext (padPos_fin vL e.1 s pL)
  have e4 : (fun j : Fin nR => padPos vR e.1 s pR j) = fun j => vR j s - e.1 s := funext (padPos_fin vR e.1 s pR)
  refine eqOn_mean_forceWord κ ρLp ρRp θc (isMarkOrder_padPos hp hs pL pR) ?_
  rw [e1, e2, e3, e4]
  exact hu

end WordPath

/-! ### The limits of the announced kernel on a good path -/

section Limits

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}

/-- The frozen driver agrees with the record driver up to every time before the stop. -/
theorem IsGoodStopPath.eqOn_rpath (h : IsGoodStopPath κ xL xR ρL ρR t e vL vR b) {s : ℝ≥0}
    (hs : s ≤ (min t e.2).toNNReal) : EqOn (fun r : ℝ => e.1 r.toNNReal) (rdrv (recOf t e)) (Icc 0 (s : ℝ)) := by
  intro r hr
  have hrs : r.toNNReal ≤ (min t e.2).toNNReal := (Real.toNNReal_le_iff_le_coe.2 hr.2).trans hs
  have h1 := h.rdrv_eq r.toNNReal hrs
  rw [Real.coe_toNNReal r hr.1] at h1
  exact h1.symm

/-- The hulls of the frozen driver before the lifetime are those of the record driver. -/
theorem IsGoodStopPath.fwdHull_eq (h : IsGoodStopPath κ xL xR ρL ρR t e vL vR b) {s : ℝ≥0}
    (hs : s ≤ (min t e.2).toNNReal) (hsζ : (s : ℝ≥0∞) < e.2) :
    fwdHull (fun r : ℝ => e.1 r.toNNReal) s = fwdHull (rdrv (recOf t e)) s := by
  obtain ⟨T', hsT', hT'ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hsζ
  have hsT'' : (s : ℝ) < T' := by exact_mod_cast hsT'
  exact LocalExt.fwdHull_congr_of_continuousOn (Ito.continuousOn_rpath h.1.2.2.2.1 hT'ζ)
    (continuous_rdrv _).continuousOn s.coe_nonneg hsT'' (h.eqOn_rpath hs)

/-- **The Green energies of the remaining domains converge to the one at the stop.** -/
theorem IsGoodStopPath.tendsto_zeroGFFTestCov (h : IsGoodStopPath κ xL xR ρL ρR t e vL vR b) {s : ℕ → ℝ≥0}
    (hsζ : ∀ n, (s n : ℝ≥0∞) < e.2) (hsle : ∀ n, s n ≤ (min t e.2).toNNReal)
    (hsT : Tendsto s atTop (𝓝 (min t e.2).toNNReal)) (ψ : TestOn upperHalfPlaneOpens)
    (hψ : Disjoint (tsupport ψ) (fwdHull (rdrv (recOf t e)) (rtime (recOf t e)))) :
    Tendsto (fun n => zeroGFFTestCov (H \ fwdHull (fun r : ℝ => e.1 r.toNNReal) (s n)) ψ ψ) atTop
      (𝓝 (zeroGFFTestCov (H \ fwdHull (rdrv (recOf t e)) (rtime (recOf t e))) ψ ψ)) := by
  have hc := tendsto_zeroGFFTestCov_time (w := LocalExt.histDrv (recHist (recOf t e)))
    (LocalExt.continuous_histDrv _) (LocalExt.histDrv_zero _) hsle hsT ψ hψ
  refine hc.congr fun n => ?_
  change zeroGFFTestCov (H \ fwdHull (rdrv (recOf t e)) (s n)) ψ ψ = _
  rw [h.fwdHull_eq (hsle n) (hsζ n)]

/-- **The tested coupling means converge to the tested mean at the stop**, with the record driver and the force word
at the positions read from the record. -/
theorem IsGoodStopPath.tendsto_integral_couplingMean (h : IsGoodStopPath κ xL xR ρL ρR t e vL vR b)
    {ρLp ρRp xLp xRp : ℕ → ℝ} (hρL : ∀ i : Fin nL, ρLp i = ρL i) (hρR : ∀ j : Fin nR, ρRp j = ρR j)
    (hxL : ∀ i : Fin nL, xLp i = xL i) (hxR : ∀ j : Fin nR, xRp j = xR j) (θc : ℝ) {s : ℕ → ℝ≥0}
    (hsζ : ∀ n, (s n : ℝ≥0∞) < e.2) (hsle : ∀ n, s n ≤ (min t e.2).toNNReal)
    (hsT : Tendsto s atTop (𝓝 (min t e.2).toNNReal)) (ψ : TestOn upperHalfPlaneOpens)
    (hψ : tsupport ψ ⊆ H \ fwdHull (rdrv (recOf t e)) (rtime (recOf t e))) :
    Tendsto (fun n => ∫ z, couplingMean κ (fun r : ℝ => e.1 r.toNNReal) (s n)
        (WholeField.bheAt κ ρL ρR (e.1 (s n)) (fun i => vL i (s n)) (fun j => vR j (s n))) z * ψ z) atTop
      (𝓝 (∫ z, couplingMean κ (rdrv (recOf t e)) (rtime (recOf t e))
        (fun y => (forceWord κ nL nR (fun i => markPosL (rdrv (recOf t e)) (rtime (recOf t e)) (xLp i))
          (fun j => markPos (rdrv (recOf t e)) (rtime (recOf t e)) (xRp j)) ρLp ρRp θc).mean y + θc) z * ψ z)) := by
  set R := recOf t e with hRdef
  set D := rdrv R with hDdef
  set Tr := rtime R with hTrdef
  set pL : ℕ → ℝ := fun i => markPosL D Tr (xLp i) with hpLdef
  set pR : ℕ → ℝ := fun j => markPos D Tr (xRp j) with hpRdef
  set u : ℕ → ℂ → ℝ := fun n y =>
    (forceWord κ nL nR (padPos vL e.1 (s n) pL) (padPos vR e.1 (s n) pR) ρLp ρRp θc).mean y + θc with hudef
  have hTr : Tr = (((min t e.2).toNNReal : ℝ≥0) : ℝ) := rfl
  have hsI : ∀ n, ((s n : ℝ≥0) : ℝ) ∈ Icc 0 Tr := fun n => ⟨(s n).coe_nonneg, by rw [hTr]; exact_mod_cast hsle n⟩
  -- step 1: rewrite the frozen means with the record driver and the word mean
  have hstep : ∀ n, (∫ z, couplingMean κ (fun r : ℝ => e.1 r.toNNReal) (s n)
      (WholeField.bheAt κ ρL ρR (e.1 (s n)) (fun i => vL i (s n)) (fun j => vR j (s n))) z * ψ z) =
      ∫ z, couplingMean κ D (s n) (u n) z * ψ z := by
    intro n
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ tsupport ψ
    · have hzD : z ∈ H \ fwdHull D (s n) :=
        ⟨(hψ hz).1, fun hK => (hψ hz).2 (fwdHull_subset_of_le (hsI n).2 hK)⟩
      have him : 0 < (fwdMap D (s n) z).im :=
        (RS.im_fwdMap_le_of_le (continuous_rdrv R) (s n).coe_nonneg le_rfl hzD).2
      simp only
      rw [couplingMean_congr (s n).coe_nonneg (h.eqOn_rpath (hsle n))]
      unfold couplingMean
      rw [eqOn_bheAt_forceWord h.1 (hsζ n) hρL hρR pL pR θc him]
    · simp only [image_eq_zero_of_notMem_tsupport hz, mul_zero]
  simp only [hstep]
  -- step 2: dominated convergence
  have hsorted : ∀ n, (forceWord κ nL nR (padPos vL e.1 (s n) pL) (padPos vR e.1 (s n) pR) ρLp ρRp θc).IsSorted :=
    fun n => isSorted_forceWord _ _ _ _ _ _ _ _
  have huc : ∀ n, ContinuousOn (u n) H := fun n =>
    (LocalExt.continuousOn_of_isBoundedHarmonicExtension
      (BoundaryWord.isBoundedHarmonicExtension_mean _ (hsorted n))).add continuousOn_const
  have hub : ∀ n y, |u n y| ≤ wordBound κ nL nR ρLp ρRp θc + |θc| := fun n y =>
    (abs_add_le _ _).trans (add_le_add (abs_mean_forceWord_le _ _ _ _ _ _ _ _ _) le_rfl)
  have hsT' : Tendsto (fun n => ((s n : ℝ≥0) : ℝ)) atTop (𝓝 Tr) := by
    rw [hTr]; exact (NNReal.continuous_coe.tendsto _).comp hsT
  refine StagedLaw.tendsto_integral_couplingMean κ (continuous_rdrv R) (rtime_nonneg R) hsI hsT' huc hub ψ hψ
    fun z hz => ?_
  -- the word means converge along the flow
  have hL : ∀ i, Tendsto (fun n => padPos vL e.1 (s n) pL i) atTop (𝓝 (pL i)) := by
    intro i
    by_cases hi : i < nL
    · have := h.tendsto_left ⟨i, hi⟩ hsζ hsT
      simp only [padPos, hi, ↓reduceDIte, hpLdef, hxL ⟨i, hi⟩]
      exact this
    · simp only [padPos, hi, ↓reduceDIte]
      exact tendsto_const_nhds
  have hR : ∀ j, Tendsto (fun n => padPos vR e.1 (s n) pR j) atTop (𝓝 (pR j)) := by
    intro j
    by_cases hj : j < nR
    · have := h.tendsto_right ⟨j, hj⟩ hsζ hsT
      simp only [padPos, hj, ↓reduceDIte, hpRdef, hxR ⟨j, hj⟩]
      exact this
    · simp only [padPos, hj, ↓reduceDIte]
      exact tendsto_const_nhds
  have hcont := FwdHolo.continuousOn_fwdMap_time (continuous_rdrv R) (rtime_nonneg R) (hψ hz)
  have hsT'' : Tendsto (fun n => ((s n : ℝ≥0) : ℝ)) atTop (𝓝[Icc 0 Tr] Tr) :=
    tendsto_nhdsWithin_iff.2 ⟨hsT', Eventually.of_forall hsI⟩
  have hz' : Tendsto (fun n => fwdMap D (s n) z) atTop (𝓝 (fwdMap D Tr z)) :=
    (hcont Tr ⟨rtime_nonneg R, le_rfl⟩).tendsto.comp hsT''
  have hzH : 0 < (fwdMap D Tr z).im := (RS.im_fwdMap_le_of_le (continuous_rdrv R) (rtime_nonneg R) le_rfl (hψ hz)).2
  exact (tendsto_mean_forceWord κ ρLp ρRp θc hL hR hz' hzH).add_const θc

end Limits

end StagedLaw

end Exist

end InteractingSLE
