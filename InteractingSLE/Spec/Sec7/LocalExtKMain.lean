/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtKSeed

/-!
# Theorem 1.2's restart coupling: the stopped seed coupling after a restart

Packet PROVE-LOCEXT-K. Assembly of `RestartSeedCouplingStatement` (`LocalExtGStmt`) from the random-word Aux. lemma 55
(`LocalExtKJoint`, `LocalExtKDens`, `LocalExtKKer`), instantiated at the restart (`LocalExtKRestart`), with the `1 + 1`
seed word (`LocalExtKSeed`):

* `restartQ`: `Q = Z · P[·|D]` for the source of the restart word;
* `seedVal_restart_eq`: on the cell, before the restarted lifetime, the merged seed marks of the restarted path are the
  chosen seed marks;
* **`isStoppedSeedCoupling_restart_of`**: the stopped seed coupling of the `1 + 1` seed word under `Q`, given its driving
  law through the stop (clause (a)) and the locality of the restarted hulls under `Q` (first half of clause (e)); every
  other clause is proved here: (b) the local stop, (c) adaptedness, (d) the two-seed GFF law at time `0`, and the
  two-seed kernel of (e);
* `RestartDrivingLocalityInput κ` (**named input**, the two clauses above for the canonical objects);
* **`restartSeedCouplingStatement_of_input`**: `RestartDrivingLocalityInput κ → RestartSeedCouplingStatement κ` (`κ > 0`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open QuantumZipper (H fwdMap fwdHull greenH)
open LQGMetric (TestOn DistOn)
open Sec7 Sec5.Markov Sec2.Restart

/-! ### Merged seed marks after a restart -/

section Merge

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {T : Ω → ℝ≥0} {G : Set Ω} {SL : Finset (Fin nL)} {SR : Finset (Fin nR)} {ω : Ω}

/-- **The left merged seed value of the restarted path is the chosen seed mark** (or the default on an empty side). -/
theorem seedVal_restart_eqL (hg : IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) (hT : (T ω : ℝ≥0∞) < ζ ω) (hωG : ω ∈ G)
    (hpat : ∀ i, VL i (T ω) ω = W (T ω) ω ↔ i ∈ SL) {s : ℝ≥0} (hs : (s : ℝ≥0∞) < restartLife ζ T ω)
    (f : ℝ → ℝ) (w : ℝ) :
    seedVal (curL VL W T ω) (fun i => f (restartMark (VL i) W T s ω)) w =
      seedVal (oneSeedY SL) (fun k => f (r0VL G VL W T SL k s ω)) w := by
  have hpu := (isIntegratedSLEPath_restart (B := B) hg hT).isSLEPathUpTo le_rfl
  have hz : ∀ i, curL VL W T ω i = 0 ↔ i ∈ SL := fun i => by
    rw [curL, sub_eq_zero]; exact hpat i
  unfold seedVal
  by_cases hS : SL.Nonempty
  · have h1 : ∃ i, curL VL W T ω i = 0 := ⟨_, (hz _).2 (SL.min'_mem hS)⟩
    have hk : 0 < oneSeedCount SL := by rw [oneSeedCount_of_nonempty hS]; exact one_pos
    have h2 : ∃ k, oneSeedY SL k = 0 := ⟨⟨0, hk⟩, rfl⟩
    simp only [h1, h2, ↓reduceDIte]
    rw [r0VL_of_mem hωG]
    congr 1
    exact vL_eq_vL_of_xL_eq_zero hpu h1.choose_spec ((hz _).2 (oneSeedIdx_mem SL _)) hs
  · have h1 : ¬ ∃ i, curL VL W T ω i = 0 := fun ⟨i, hi⟩ => hS ⟨i, (hz i).1 hi⟩
    have h2 : ¬ ∃ k, oneSeedY SL k = 0 := fun ⟨k, _⟩ => hS (nonempty_of_oneSeedCount k)
    simp only [h1, h2, ↓reduceDIte]

/-- **The right merged seed value of the restarted path is the chosen seed mark.** -/
theorem seedVal_restart_eqR (hg : IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) (hT : (T ω : ℝ≥0∞) < ζ ω) (hωG : ω ∈ G)
    (hpat : ∀ j, VR j (T ω) ω = W (T ω) ω ↔ j ∈ SR) {s : ℝ≥0} (hs : (s : ℝ≥0∞) < restartLife ζ T ω)
    (f : ℝ → ℝ) (w : ℝ) :
    seedVal (curR VR W T ω) (fun j => f (restartMark (VR j) W T s ω)) w =
      seedVal (oneSeedY SR) (fun k => f (r0VR G VR W T SR k s ω)) w := by
  have hpu := (isIntegratedSLEPath_restart (B := B) hg hT).isSLEPathUpTo le_rfl
  have hz : ∀ j, curR VR W T ω j = 0 ↔ j ∈ SR := fun j => by
    rw [curR, sub_eq_zero]; exact hpat j
  unfold seedVal
  by_cases hS : SR.Nonempty
  · have h1 : ∃ j, curR VR W T ω j = 0 := ⟨_, (hz _).2 (SR.min'_mem hS)⟩
    have hk : 0 < oneSeedCount SR := by rw [oneSeedCount_of_nonempty hS]; exact one_pos
    have h2 : ∃ k, oneSeedY SR k = 0 := ⟨⟨0, hk⟩, rfl⟩
    simp only [h1, h2, ↓reduceDIte]
    rw [r0VR_of_mem hωG]
    congr 1
    exact vR_eq_vR_of_xR_eq_zero hpu h1.choose_spec ((hz _).2 (oneSeedIdx_mem SR _)) hs
  · have h1 : ¬ ∃ j, curR VR W T ω j = 0 := fun ⟨j, hj⟩ => hS ⟨j, (hz j).1 hj⟩
    have h2 : ¬ ∃ k, oneSeedY SR k = 0 := fun ⟨k, _⟩ => hS (nonempty_of_oneSeedCount k)
    simp only [h1, h2, ↓reduceDIte]

end Merge

/-! ### The stopped seed coupling after a restart -/

section Main

universe u

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens} {G : Set Ω} {T : Ω → ℝ≥0}
  {SL : Finset (Fin nL)} {SR : Finset (Fin nR)} {r : ℝ} {D : Set Ω}

variable (κ ρL ρR r) in
/-- **The measure `Q = Z · P[·|D]`** of the restart: the Cameron–Martin density of the source of the restart word. -/
def restartQ (P : Measure Ω) (D : Set Ω) (K : Ω → DrivingHist nL nR) (h : Ω → DistOn upperHalfPlaneOpens) :
    Measure Ω :=
  wordMeasure κ ρL ρR r (P[|D]) (restartWord r K) (fun ω => restartField κ (h ω, K ω))

/-- The recoded restarted field read from a recorded history agrees with the recoding of the restart word on the cell. -/
theorem restartRecode_eq_recode_restartWord {K K' : Ω → DrivingHist nL nR} {ω : Ω}
    (hK : K ω = stoppedHistory (completedState W VL VR ζ) (fun ω => (T ω : WithTop ℝ≥0)) ω)
    (hK' : K' ω = stoppedHistory (completedState W VL VR ζ) (fun ω => (T ω : WithTop ℝ≥0)) ω)
    (hTζ : (T ω : ℝ≥0∞) < ζ ω) (hadm : IsAdmWord r (curL VL W T ω, curR VR W T ω)) :
    restartRecode κ ρL ρR r (h ω, K' ω) =
      recode κ (restartWord r K ω).1 (restartWord r K ω).2 ρL ρR r (restartField κ (h ω, K ω)) := by
  have hs : histState (K' ω) = drivingState W VL VR (T ω) ω := by
    rw [hK']; exact histState_stoppedHistory_of_lt rfl hTζ
  have hKK : K' ω = K ω := hK'.trans hK.symm
  rw [restartWord_eq_cur hK hTζ hadm, restartRecode, hs, hKK]
  rfl

/-- **The stopped seed coupling after a restart, given its driving law and locality.** For the data of
`RestartSeedCouplingStatement` and a `𝓓_T`-measurable version `K` of `𝒳_T`, under `Q = restartQ` the `1 + 1` seed word
with the restarted driver and the restarted chosen seed marks, stopped at the capped local stop `S₀` of the restarted path,
with the recoded restarted field `F₀(h, K')`, is a stopped seed coupling — provided clause (a) (the driving law through
`S₀`) and the locality half of clause (e) hold. Clauses (b), (c), (d) and the kernel half of (e) are proved here
(random-word Aux. lemma 55 at the restart). -/
theorem isStoppedSeedCoupling_restart_of (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) (hF : IsOrderedForceWord xL xR) (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0)) (hGm : MeasurableSet G)
    (hG0 : P Gᶜ = 0) (hG : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω)
    (hD : MeasurableSet[hT.measurableSpace] D) (hPD : P D ≠ 0) (hDp : IsRestartCell W VL VR ζ G T SL SR r D)
    {K' : Ω → DrivingHist nL nR} (hK'm : Measurable K')
    (hK' : ∀ᵐ ω ∂P, ω ∈ D → K' ω = stoppedHistory (completedState W VL VR ζ) (fun ω => (T ω : WithTop ℝ≥0)) ω)
    {K : Ω → DrivingHist nL nR} (hKm : Measurable[hT.measurableSpace] K)
    (hK : ∀ ω, IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
      (fun t => B t ω) (ζ ω) → (T ω : ℝ≥0∞) < ζ ω →
        K ω = stoppedHistory (completedState W VL VR ζ) (fun ω => (T ω : WithTop ℝ≥0)) ω)
    (ha : ∃ (Q' : Measure Ω) (𝓕' : Filtration ℝ≥0 mΩ) (B' : ℝ≥0 → Ω → ℝ), IsProbabilityMeasure Q' ∧
      restartQ κ ρL ρR r P D K h ≪ Q' ∧ Q' ≪ restartQ κ ρL ρR r P D K h ∧
      restartFiltration (drivingFiltration P hX) T hT ≤ 𝓕' ∧
      Sec2.IsSLEEvolutionUpTo κ (oneSeedY SL) (oneSeedY SR) (seedWtL (oneSeedY SL) (oneSeedWts SL ρL))
        (seedWtR (oneSeedY SR) (oneSeedWts SR ρR)) Q' 𝓕' (r0W G W T) (r0VL G VL W T SL) (r0VR G VR W T SR) B'
        (fun ω => (capStop r G (restartLife ζ T) (restartDrv W T) ω : ℝ≥0∞)) ∧
      ∀ A, MeasurableSet[(isStoppingTime_capStop_restart hX hT hGm hG0 hG r).measurableSpace] A →
        restartQ κ ρL ρR r P D K h A = Q' A)
    (hloc : ∀ (τ : Ω → WithTop ℝ≥0) (_ : IsStoppingTime (restartFiltration (drivingFiltration P hX) T hT) τ),
      (∀ᵐ ω ∂(restartQ κ ρL ρR r P D K h), τ ω ≤ capStop r G (restartLife ζ T) (restartDrv W T) ω) →
      IsLocalSet (fun ω => fwdHull (fun s : ℝ => r0W G W T s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))
        (fun ω => restartRecode κ ρL ρR r (h ω, K' ω)) (restartQ κ ρL ρR r P D K h)) :
    IsStoppedSeedCoupling κ (oneSeedY SL) (oneSeedY SR) (oneSeedWts SL ρL) (oneSeedWts SR ρR) r (restartQ κ ρL ρR r P D K h)
      (r0W G W T) (r0VL G VL W T SL) (r0VR G VR W T SR) (capStop r G (restartLife ζ T) (restartDrv W T))
      (fun ω => restartRecode κ ρL ρR r (h ω, K' ω)) := by
  classical
  have hPDp : IsProbabilityMeasure (P[|D]) := cond_isProbabilityMeasure hPD
  have hDm : MeasurableSet D := hT.measurableSpace_le _ hD
  have hcf := isCouplingCharFun_restartWord hC hκ hX hT hG hD hPD hDp hKm hK
  have hhm := measurable_restartField_word hC hX hT hKm
  have hc := measurable_restartWord_zero hX hT hKm (r := r)
  have hcm : Measurable (restartWord r K) := measurable_restartWord r (hKm.mono hT.measurableSpace_le le_rfl)
  have hadm := isAdmWord_restartWord hPD hDp (K := K)
  have hgood := ae_isWordPath_restart (ρL := ρL) (ρR := ρR) hX hT hG hD hDp hK
  have hsum := ae_seedSum_restartWord (ρL := ρL) (ρR := ρR) hX hT hG hD hDp hK
  have hQ : IsProbabilityMeasure (restartQ κ ρL ρR r P D K h) :=
    isProbabilityMeasure_wordMeasure hcf hhm hc hadm hgood
  have hQP : restartQ κ ρL ρR r P D K h ≪ P[|D] := wordMeasure_absolutelyContinuous
  have hPQ : P[|D] ≪ restartQ κ ρL ρR r P D K h := absolutelyContinuous_wordMeasure hhm hcm
  have hDQ : ∀ᵐ ω ∂(restartQ κ ρL ρR r P D K h), ω ∈ D := hQP.ae_le (ae_cond_mem hDm)
  have hK'Q : ∀ᵐ ω ∂(restartQ κ ρL ρR r P D K h), ω ∈ D →
      K' ω = stoppedHistory (completedState W VL VR ζ) (fun ω => (T ω : WithTop ℝ≥0)) ω :=
    hQP.ae_le (cond_absolutelyContinuous.ae_le hK')
  -- the recoded field is the recoding of the restart word
  have hfield : ∀ᵐ ω ∂(restartQ κ ρL ρR r P D K h), restartRecode κ ρL ρR r (h ω, K' ω) =
      recode κ (restartWord r K ω).1 (restartWord r K ω).2 ρL ρR r (restartField κ (h ω, K ω)) := by
    filter_upwards [hDQ, hK'Q] with ω hω h2
    obtain ⟨hωG, hTζ, -, -, hr'⟩ := hDp ω hω
    have hg := hG ω hωG
    exact restartRecode_eq_recode_restartWord (hK ω hg.1 hTζ) (h2 hω) hTζ ⟨isOrderedForceWord_cur hg hTζ, hr'⟩
  have hS := isStoppingTime_capStop_restart hX hT hGm hG0 hG r
  refine ⟨restartFiltration (drivingFiltration P hX) T hT, hS, ha, ?_,
    adaptedBefore_r0W hX hT hGm hG0 hG r, fun k => adaptedBefore_r0VL hX hT hGm hG0 hG r k,
    fun k => adaptedBefore_r0VR hX hT hGm hG0 hG r k,
    (measurable_restartRecode κ ρL ρR r).comp (hC.2.1.prodMk hK'm), ?_, ?_⟩
  · -- (b) the local stop of a driving path continuous beyond it
    filter_upwards [hDQ] with ω hω
    obtain ⟨hωG, hTζ, -, -, hr'⟩ := hDp ω hω
    have hg := hG ω hωG
    have hp' := isIntegratedSLEPath_restart (B := B) hg hTζ
    refine ⟨restartLife ζ T ω, capStop_restart_lt hg hTζ hωG hr', ?_, ?_⟩
    · rw [capStop_restart_eq_localStopPath hg hTζ hωG hr']
      congr 1
      funext t
      exact (r0W_of_mem hωG t).symm
    · have hc1 : ContinuousOn (fun t => drivingState (restartDrv W T) (fun k => restartMark (VL (oneSeedIdx SL k)) W T)
          (fun k => restartMark (VR (oneSeedIdx SR k)) W T) t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < restartLife ζ T ω} :=
        hp'.2.2.2.1.prodMk ((continuousOn_pi.2 fun k => hp'.2.2.2.2.1 _).prodMk
          (continuousOn_pi.2 fun k => hp'.2.2.2.2.2.1 _))
      refine hc1.congr fun t _ => ?_
      simp only [drivingState, r0W_of_mem hωG, r0VL_of_mem hωG, r0VR_of_mem hωG]
  · -- (d) the two-seed GFF law at time `0`
    intro u₀ hu₀
    rw [seedSumL_oneSeedY, seedSumR_oneSeedY] at hu₀
    have hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR := by
      intro hth
      have h0 := ae_zeta_eq_zero_of_thresholdCondition hC.1 hκ hth
      apply hPD
      refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 h0)
      have hTζ := (hDp ω hω).2.1
      intro hz
      rw [hz] at hTζ
      exact not_lt_zero hTζ
    have hr0 := isSeedRadius_seedRadius xL xR
    have hu00 := isBoundedHarmonicExtension_bheAt κ ρL ρR xL xR
    have hu00c := continuousOn_of_isBoundedHarmonicExtension hu00
    have e₁ : ∀ (u : ℂ → ℝ), ContinuousOn u H → ∀ φ : TestOn upperHalfPlaneOpens,
        ∫ z, u z * φ z = SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u φ :=
      fun u hu φ => by
        rw [SupercriticalConformalCovariance.GM24.smoothDist_apply hu]
        exact integral_congr_ae (ae_of_all _ fun z => mul_comm _ _)
    have href := hC.2.2.1 (bheAt κ ρL ρR xL xR) hu00
    have eP : (fun φ ω => h ω φ - ∫ z, bheAt κ ρL ρR xL xR z * φ z) = fun φ ω =>
        h ω φ - SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens (bheAt κ ρL ρR xL xR) φ := by
      funext φ ω; rw [e₁ _ hu00c φ]
    rw [eP] at href
    have hrefcf : ∀ φ : TestOn upperHalfPlaneOpens, ∫ ω, Complex.exp (Complex.I * ((h ω φ -
        SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens (bheAt κ ρL ρR xL xR) φ : ℝ) : ℂ)) ∂P =
          ((Real.exp (-(1 / 2) * loewnerGreenEnergy (fun _ => 0) 0 φ) : ℝ) : ℂ) := fun φ => by
      rw [← e₁ _ hu00c φ]
      exact integral_cexp_sub_bheAt_eq hκ hC hF hr0 hseed φ
    have hZB := isZBGFFProcess_recode_wordMeasure hcf hhm hc hadm hgood hsum hu₀ _ href hrefcf
    have hu₀c := continuousOn_of_isBoundedHarmonicExtension hu₀
    have eQ : ∀ X : Ω → DistOn upperHalfPlaneOpens, (fun φ ω => X ω φ - ∫ z, u₀ z * φ z) = fun φ ω =>
        X ω φ - SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀ φ := fun X => by
      funext φ ω; rw [e₁ u₀ hu₀c φ]
    rw [eQ] at hZB
    rw [eQ]
    refine isZBGFFProcess_of_integral_cexp_eq ((measurable_restartRecode κ ρL ρR r).comp (hC.2.1.prodMk hK'm))
      _ _ hZB fun φ => integral_congr_ae ?_
    filter_upwards [hfield] with ω hω
    rw [Function.comp_apply, hω]
  · -- (e) locality (input) and the two-seed kernel
    intro τ hτ hτS
    refine ⟨hloc τ hτ hτS, fun u hu φ => ?_⟩
    have hτS' : ∀ᵐ ω ∂(P[|D]), τ ω ≤ localStopPath r (restartLife ζ T ω) fun t => restartDrv W T t ω := by
      filter_upwards [hPQ.ae_le hτS, ae_cond_mem hDm] with ω h1 hω
      obtain ⟨hωG, hTζ, -, -, hr'⟩ := hDp ω hω
      rw [← capStop_restart_eq_localStopPath (hG ω hωG) hTζ hωG hr']
      exact h1
    -- the data of the restart word and of the seed word
    set DE : Ω → Prop := fun ω => seedSumL (restartWord r K ω).1 ρL = seedSumL (oneSeedY SL) (oneSeedWts SL ρL) ∧
      seedSumR (restartWord r K ω).2 ρR = seedSumR (oneSeedY SR) (oneSeedWts SR ρR) ∧
      seedPosL (restartWord r K ω).1 (restartDrv W T) (fun i => restartMark (VL i) W T) τ ω =
        seedPosL (oneSeedY SL) (r0W G W T) (r0VL G VL W T SL) τ ω ∧
      seedPosR (restartWord r K ω).2 (restartDrv W T) (fun j => restartMark (VR j) W T) τ ω =
        seedPosR (oneSeedY SR) (r0W G W T) (r0VR G VR W T SR) τ ω with hDE
    set u₂ : Ω → ℂ → ℝ := fun ω => if DE ω then u ω else
      Impl.forceExt κ (Ito.weightWord (fun _ : Fin 1 => seedSumL (restartWord r K ω).1 ρL)
        (fun _ : Fin 1 => seedSumR (restartWord r K ω).2 ρR))
        (fun _ => seedPosL (restartWord r K ω).1 (restartDrv W T) (fun i => restartMark (VL i) W T) τ ω)
        (fun _ => seedPosR (restartWord r K ω).2 (restartDrv W T) (fun j => restartMark (VR j) W T) τ ω) with hu₂def
    have hu₂ : ∀ ω, IsBoundedHarmonicExtension
        (forceBoundaryData κ (fun _ : Fin 1 => seedSumL (restartWord r K ω).1 ρL)
          (fun _ : Fin 1 => seedSumR (restartWord r K ω).2 ρR)
          (fun _ => seedPosL (restartWord r K ω).1 (restartDrv W T) (fun i => restartMark (VL i) W T) τ ω)
          (fun _ => seedPosR (restartWord r K ω).2 (restartDrv W T) (fun j => restartMark (VR j) W T) τ ω))
        (forceJumpSet
          (fun _ : Fin 1 => seedPosL (restartWord r K ω).1 (restartDrv W T) (fun i => restartMark (VL i) W T) τ ω)
          (fun _ : Fin 1 => seedPosR (restartWord r K ω).2 (restartDrv W T) (fun j => restartMark (VR j) W T) τ ω))
        (u₂ ω) := fun ω => by
      by_cases hd : DE ω
      · simp only [hu₂def, hd, ↓reduceIte]
        obtain ⟨d1, d2, d3, d4⟩ := hd
        rw [d1, d2, d3, d4]
        exact hu ω
      · simp only [hu₂def, hd, ↓reduceIte]
        exact Impl.isBoundedHarmonicExtension_forceExt κ _ _ _
    have hk := condExp_recode_wordMeasure_eq_twoSeedKernel hcf hhm hc hadm hgood hτ hτS' hu₂ φ
    have hcond : (restartQ κ ρL ρR r P D K h)[fun ω' =>
        Complex.exp (Complex.I * (restartRecode κ ρL ρR r (h ω', K' ω') φ : ℂ)) | hτ.measurableSpace] =ᵐ[restartQ κ ρL ρR r P D K h]
        (restartQ κ ρL ρR r P D K h)[fun ω' => Complex.exp (Complex.I *
          (recode κ (restartWord r K ω').1 (restartWord r K ω').2 ρL ρR r (restartField κ (h ω', K ω')) φ : ℂ)) |
            hτ.measurableSpace] := by
      refine condExp_congr_ae ?_
      filter_upwards [hfield] with ω hω
      rw [hω]
    filter_upwards [hcond, hQP.ae_le hk, hDQ, hQP.ae_le hτS'] with ω h1 h2 hω h4 hdis
    obtain ⟨hωG, hTζ, hpL, hpR, hr'⟩ := hDp ω hω
    have hg := hG ω hωG
    have hrp := rpath_r0W_of_mem (W := W) (T := T) hωG
    rw [hrp] at hdis
    rw [h1, show restartQ κ ρL ρR r P D K h = wordMeasure κ ρL ρR r (P[|D]) (restartWord r K)
      (fun ω => restartField κ (h ω, K ω)) from rfl, h2 hdis, hrp]
    -- `u₂ = u` at `ω`
    have htζ : (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < restartLife ζ T ω := by
      have h5 := capStop_restart_lt (B := B) hg hTζ hωG hr'
      rw [capStop_restart_eq_localStopPath hg hTζ hωG hr'] at h5
      exact lt_of_le_of_lt (by exact_mod_cast coe_untopD_le_localStopPath h4) h5
    have hadmc : IsAdmWord r (curL VL W T ω, curR VR W T ω) := ⟨isOrderedForceWord_cur hg hTζ, hr'⟩
    have hw := restartWord_eq_cur (hK ω hg.1 hTζ) hTζ hadmc
    have hd : DE ω := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hw, seedSumL_oneSeedY]; exact seedSumL_curL hpL
      · rw [hw, seedSumR_oneSeedY]; exact seedSumR_curR hpR
      · rw [hw]
        have e := seedVal_restart_eqL (SL := SL) (G := G) hg hTζ hωG hpL htζ
          (fun v => v - restartDrv W T ((τ ω).untopD 0) ω) 0
        simp only [seedPosL]
        convert e using 3
        all_goals first | rfl | simp only [cposL, r0W_of_mem hωG]
      · rw [hw]
        have e := seedVal_restart_eqR (SR := SR) (G := G) hg hTζ hωG hpR htζ
          (fun v => v - restartDrv W T ((τ ω).untopD 0) ω) 0
        simp only [seedPosR]
        convert e using 3
        all_goals first | rfl | simp only [cposR, r0W_of_mem hωG]
    simp only [hu₂def, hd, ↓reduceIte]

end Main

/-! ### `RestartSeedCouplingStatement` from the remaining input -/

section Statement

universe u

/-- Locality is a property of the law of `(A, h)`: it passes to an almost surely equal field. -/
theorem IsLocalSet.congr_field {Ω : Type*} [MeasurableSpace Ω] {A : Ω → Set ℂ}
    {h h' : Ω → DistOn upperHalfPlaneOpens} {P : Measure Ω} (hA : IsLocalSet A h P) (hh : ∀ᵐ ω ∂P, h' ω = h ω) :
    IsLocalSet A h' P := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  obtain ⟨hm, hsub, Ω', mΩ', P', hP', A₀, h₁, h₂, hA₀, hh₁, hh₂, hA₀H, hharm, hcond, hlaw⟩ := hA
  have hpair : (fun ω => (A ω, h' ω)) =ᵐ[P] fun ω => (A ω, h ω) := hh.mono fun ω hω => Prod.ext rfl hω
  refine ⟨hm.congr hpair.symm, hsub, Ω', mΩ', P', hP', A₀, h₁, h₂, hA₀, hh₁, hh₂, hA₀H, hharm, hcond, ?_⟩
  rw [hlaw]
  exact Measure.map_congr hpair.symm

/-- **Named input: the driving law through the local stop and the locality of the hulls after a restart** (Aux. lemma
55, steps 3–5, the two parts not proved by the random-word Gaussian computations of this packet). For the data of
`RestartSeedCouplingStatement` and a `𝓓_T`-measurable version `K` of `𝒳_T`, under `Q = restartQ` (the Cameron–Martin
measure of the source of the restart word):

* (a) a probability measure `Q'` equivalent to `Q`, agreeing with `Q` on the stopped σ-algebra of the restarted local
  stop `S₀`, under which the restarted driver and the restarted chosen seed marks are a local evolution of the `1 + 1` seed
  word before `S₀` (Girsanov with the distant drift; the specification's identification of `Q` with the Girsanov
  measure on `𝓖'_{S₀}` is the bracket identity `∫ θ dB = −((𝔥_{·∧S₀}, v) − (𝔥₀, v))` with random positions);
* (e, locality) at every stop `τ ≤ S₀` of the restarted filtration, the restarted hull is a local set of the recoded
  restarted field under `Q`. -/
def RestartDrivingLocalityInput (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsOrderedForceWord xL xR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h →
      ∀ (hX : IsMeasurableKilledDriving W VL VR ζ) (T : Ω → ℝ≥0)
        (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0)) (G : Set Ω)
        (hGm : MeasurableSet G) (hG0 : P Gᶜ = 0) (hG : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω)
        (SL : Finset (Fin nL)) (SR : Finset (Fin nR)) (r : ℝ),
        -2 < ∑ i ∈ SL, ρL i → -2 < ∑ j ∈ SR, ρR j →
      ∀ D : Set Ω, MeasurableSet[hT.measurableSpace] D → P D ≠ 0 → IsRestartCell W VL VR ζ G T SL SR r D →
      ∀ K : Ω → DrivingHist nL nR, Measurable[hT.measurableSpace] K →
        (∀ ω, IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
          (fun t => B t ω) (ζ ω) → (T ω : ℝ≥0∞) < ζ ω →
            K ω = stoppedHistory (completedState W VL VR ζ) (fun ω => (T ω : WithTop ℝ≥0)) ω) →
        (∃ (Q' : Measure Ω) (𝓕' : Filtration ℝ≥0 mΩ) (B' : ℝ≥0 → Ω → ℝ), IsProbabilityMeasure Q' ∧
          restartQ κ ρL ρR r P D K h ≪ Q' ∧ Q' ≪ restartQ κ ρL ρR r P D K h ∧
          restartFiltration (drivingFiltration P hX) T hT ≤ 𝓕' ∧
          Sec2.IsSLEEvolutionUpTo κ (oneSeedY SL) (oneSeedY SR) (seedWtL (oneSeedY SL) (oneSeedWts SL ρL))
            (seedWtR (oneSeedY SR) (oneSeedWts SR ρR)) Q' 𝓕' (r0W G W T) (r0VL G VL W T SL) (r0VR G VR W T SR) B'
            (fun ω => (capStop r G (restartLife ζ T) (restartDrv W T) ω : ℝ≥0∞)) ∧
          ∀ A, MeasurableSet[(isStoppingTime_capStop_restart hX hT hGm hG0 hG r).measurableSpace] A →
            restartQ κ ρL ρR r P D K h A = Q' A) ∧
        ∀ (τ : Ω → WithTop ℝ≥0) (_ : IsStoppingTime (restartFiltration (drivingFiltration P hX) T hT) τ),
          (∀ᵐ ω ∂(restartQ κ ρL ρR r P D K h), τ ω ≤ capStop r G (restartLife ζ T) (restartDrv W T) ω) →
          IsLocalSet (fun ω => fwdHull (fun s : ℝ => r0W G W T s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))
            (fun ω => restartRecode κ ρL ρR r (h ω, K ω)) (restartQ κ ρL ρR r P D K h)

/-- **Theorem 1.2's restart coupling from the remaining input** (`κ > 0`): the random-word Aux. lemma 55 of this packet
(the source pairing's conditional law, the density `Z`, `Q = Z · P[·|D]`, the two-seed kernel, the two-seed GFF law),
the restart stops and adaptedness, and the recovery of the restarted two-seed history give
`RestartSeedCouplingStatement κ` from `RestartDrivingLocalityInput κ`. -/
theorem restartSeedCouplingStatement_of_input {κ : ℝ} (hκ : 0 < κ) (hin : RestartDrivingLocalityInput.{u} κ) :
    RestartSeedCouplingStatement.{u} κ := by
  intro nL nR xL xR ρL ρR hF Ω mΩ P _ 𝓕 W VL VR B ζ h hC hX T hT G hGm hG0 hG SL SR r hSL hSR D hD hPD hDp K' hK'm hK'
  classical
  obtain ⟨K, hKm, hK⟩ := exists_measurable_stoppedHistory_version (κ := κ) (xL := xL) (xR := xR) (ρL := ρL)
    (ρR := ρR) (B := B) hX hT
  have hDp' : IsRestartCell W VL VR ζ G T SL SR r D := hDp
  obtain ⟨ha, hloc⟩ := hin xL xR ρL ρR hF P 𝓕 W VL VR B ζ h hC hX T hT G hGm hG0 hG SL SR r hSL hSR D hD hPD hDp' K
    hKm hK
  have hPDp : IsProbabilityMeasure (P[|D]) := cond_isProbabilityMeasure hPD
  have hDm : MeasurableSet D := hT.measurableSpace_le _ hD
  have hcf := isCouplingCharFun_restartWord hC hκ hX hT hG hD hPD hDp' hKm hK
  have hhm := measurable_restartField_word hC hX hT hKm
  have hc := measurable_restartWord_zero hX hT hKm (r := r)
  have hcm : Measurable (restartWord r K) := measurable_restartWord r (hKm.mono hT.measurableSpace_le le_rfl)
  have hadm := isAdmWord_restartWord hPD hDp' (K := K)
  have hgood := ae_isWordPath_restart (ρL := ρL) (ρR := ρR) hX hT hG hD hDp' hK
  have hQ : IsProbabilityMeasure (restartQ κ ρL ρR r P D K h) :=
    isProbabilityMeasure_wordMeasure hcf hhm hc hadm hgood
  have hQP : restartQ κ ρL ρR r P D K h ≪ P[|D] := wordMeasure_absolutelyContinuous
  have hPQ : P[|D] ≪ restartQ κ ρL ρR r P D K h := absolutelyContinuous_wordMeasure hhm hcm
  have hcR : P[|D] = (P D)⁻¹ • P.restrict D := rfl
  have hcR1 : P[|D] ≪ P.restrict D := by rw [hcR]; exact Measure.smul_absolutelyContinuous
  have hcR2 : P.restrict D ≪ P[|D] := by
    rw [hcR]
    refine Measure.absolutelyContinuous_smul ?_
    exact ENNReal.inv_ne_zero.2 (measure_ne_top P D)
  have hDQ : ∀ᵐ ω ∂(restartQ κ ρL ρR r P D K h), ω ∈ D := hQP.ae_le (ae_cond_mem hDm)
  have hK'Q : ∀ᵐ ω ∂(restartQ κ ρL ρR r P D K h), ω ∈ D →
      K' ω = stoppedHistory (completedState W VL VR ζ) (fun ω => (T ω : WithTop ℝ≥0)) ω :=
    hQP.ae_le (cond_absolutelyContinuous.ae_le hK')
  have hKK' : ∀ᵐ ω ∂(restartQ κ ρL ρR r P D K h), K' ω = K ω := by
    filter_upwards [hDQ, hK'Q] with ω hω h2
    obtain ⟨hωG, hTζ, -⟩ := hDp ω hω
    exact (h2 hω).trans (hK ω (hG ω hωG).1 hTζ).symm
  refine ⟨restartQ κ ρL ρR r P D K h, hQ, hQP.trans hcR1, hcR2.trans hPQ, oneSeedCount SL, oneSeedCount SR, oneSeedY SL,
    oneSeedY SR, oneSeedWts SL ρL, oneSeedWts SR ρR, isOrderedForceWord_oneSeedY SL SR, seedSumL_oneSeedY SL ρL,
    seedSumR_oneSeedY SR ρR, r0W G W T, r0VL G VL W T SL, r0VR G VR W T SR,
    capStop r G (restartLife ζ T) (restartDrv W T), restartRecode κ ρL ρR r, fun p => p.2,
    measurable_restartRecode κ ρL ρR r, measurable_snd, ?_, ?_⟩
  · refine isStoppedSeedCoupling_restart_of hC hκ hF hX hT hGm hG0 hG hD hPD hDp' hK'm hK' hKm hK ha
      fun τ hτ hτS => IsLocalSet.congr_field (hloc τ hτ hτS) ?_
    filter_upwards [hKK'] with ω hω
    rw [hω]
  · -- the restarted two-seed history is recovered from the seed-word history
    filter_upwards [hDQ] with ω hω
    obtain ⟨hωG, hTζ, hpL, hpR, hr'⟩ := hDp ω hω
    have hg := hG ω hωG
    have hlt := capStop_restart_lt (B := B) hg hTζ hωG hr'
    refine Prod.ext rfl (funext fun q => ?_)
    simp only [stoppedHistory, twoSeedProj]
    have hs : ((stopAt (capStop r G (restartLife ζ T) (restartDrv W T)) q ω : ℝ≥0) : ℝ≥0∞) <
        restartLife ζ T ω :=
      lt_of_le_of_lt (by exact_mod_cast stopAt_le _ q ω) hlt
    have hcs : completedState (restartDrv W T) (fun i => restartMark (VL i) W T) (fun j => restartMark (VR j) W T)
        (restartLife ζ T) (stopAt (capStop r G (restartLife ζ T) (restartDrv W T)) q ω) ω =
        drivingState (restartDrv W T) (fun i => restartMark (VL i) W T) (fun j => restartMark (VR j) W T)
          (stopAt (capStop r G (restartLife ζ T) (restartDrv W T)) q ω) ω := ite_eq_left hs
    rw [hcs]
    simp only [drivingState, r0W_of_mem hωG]
    refine Prod.ext rfl (Prod.ext (funext fun _ => ?_) (funext fun _ => ?_))
    · exact seedVal_restart_eqL (SL := SL) (G := G) hg hTζ hωG hpL hs id _
    · exact seedVal_restart_eqR (SR := SR) (G := G) hg hTζ hωG hpR hs id _

end Statement

end LocalExt

end InteractingSLE
