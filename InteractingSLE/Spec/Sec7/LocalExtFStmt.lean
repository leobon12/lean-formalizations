/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtCTwoSeed
import InteractingSLE.Spec.Sec7.LocalExtDGFF
import InteractingSLE.Spec.Sec7.LocalExtA3Girsanov

/-!
# Step 6 of Aux. lemma 55 stated once: Aux. lemma 54 for a stopped seed coupling

Packet PROVE-LOCEXT-F. Aux. lemma 54 (specification p. 246) extends a coupling that is known only **through a stop**
`S` to a full coupling. In Aux. lemma 55 it is applied after the measure change (HL3): under `Q = Z·P`, through the local
stop `S` of radius `r`, the driver and the seed marks are a local evolution of the **seed-weight word** (every mark off the
seed has weight `0`), and the recoded field `h₀` of (HL8) has the **two-seed** kernel and locality at every driving stop
`τ ≤ S` (PROVE-LOCEXT-D, step 5) and the two-seed GFF law (PROVE-LOCEXT-D, (E3)).

This file states that situation once, independently of the original coupling (so that the time-`0` case of Theorem 1.2's
local extension and its restart at a stopping time share it):

* `IsStoppedSeedCoupling κ xL xR ρL ρR r Q W VL VR S h` — **a stopped seed coupling through the local stop `S`**:
  (a) the driving law through `S` (a local evolution of the seed-weight word before `S` under a measure `Q'` equivalent to `Q`
  that agrees with `Q` on the stopped σ-algebra `𝓓_S`), (b) `S` is the local stop of radius `r` of a driving path that is
  continuous beyond `S`, (c) the coordinates are `𝓓`-adapted before `S`, (d) the field is measurable and has the two-seed
  GFF law at time `0`, (e) locality and the two-seed kernel at every `𝓓`-stop `τ ≤ S`;
* `StoppedSeedExtensionStatement κ` (**named input: Aux. lemma 54** for the stopped seed coupling): every stopped seed
  coupling has an extended reference pair (`HasReferenceExtension`, weights the seed sums, radius `r`) over its own field
  recovering its two-seed history stopped at `S`;
* `HasReferenceExtension.comp`: an extended reference pair over `g ∘ H` (`g` measurable) is one over `H`;
* **`isStoppedSeedCoupling_srcMeasure`** (time `0`): for every coupling with an admissible seed, under `Q = srcMeasure`
  the original driving process, stopped at the capped local stop of a good event with continuous noise, with the recoded
  field, is a stopped seed coupling (PROVE-LOCEXT-A3's Girsanov identification, PROVE-LOCEXT-D's step 5 and (E3));
* **`twoSeedReferenceExtensionStatement_of_stoppedSeedExtension`**:
  `StoppedSeedExtensionStatement κ → TwoSeedReferenceExtensionStatement κ` (`0 < κ`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace LocalExt

open Sec7 Sec2

/-! ### The stopped seed coupling and Aux. lemma 54 -/

/-- **A stopped seed coupling through the local stop `S`** (the hypotheses of Aux. lemma 54, specification p. 246, for
the seed-weight word of an ordered force word: "`(h, W_{·∧S}, V_{·∧S})` is another stopped coupling with the same driving
law and the same original optional hull specification through `S`"). For a filtration `𝓓` of which `S` is a stopping
time:

* (a) **the driving law through `S`**: under a probability measure `Q'` equivalent to `Q` that agrees with `Q` on the stopped
  σ-algebra `𝓓_S`, the driver and the marks are a local evolution before `S` of the word with the seed weights
  (`seedWtL`, `seedWtR`: the marks off the seed have weight `0`) in a filtration containing `𝓓`;
* (b) `S` is the local stop of radius `r` of a driving path that is continuous beyond `S`;
* (c) the driving coordinates are `𝓓`-adapted before `S`;
* (d) the field is measurable, and `h − 𝔥⁰` is a zero-boundary GFF process, `𝔥⁰` the two-seed mean at time `0`
  (positions `0⁻, 0⁺`, weights the seed sums);
* (e) at every `𝓓`-stopping time `τ ≤ S` the hull `K_τ` is a local set of `h` and, off `K_τ`, the conditional law of `h`
  given `𝓓_τ` is the **two-seed** kernel (weights the seed sums, positions the merged seed positions `seedPosL`,
  `seedPosR`). -/
def IsStoppedSeedCoupling (κ : ℝ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) (r : ℝ) {Ω : Type u} {mΩ : MeasurableSpace Ω} (Q : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (S : Ω → WithTop ℝ≥0)
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) : Prop :=
  ∃ (𝓓 : Filtration ℝ≥0 mΩ) (hS : IsStoppingTime 𝓓 S),
    -- (a) the driving law through `S`
    (∃ (Q' : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (B : ℝ≥0 → Ω → ℝ), IsProbabilityMeasure Q' ∧ Q ≪ Q' ∧
      Q' ≪ Q ∧ 𝓓 ≤ 𝓕 ∧
      IsSLEEvolutionUpTo κ xL xR (seedWtL xL ρL) (seedWtR xR ρR) Q' 𝓕 W VL VR B (fun ω => (S ω : ℝ≥0∞)) ∧
      ∀ A, MeasurableSet[hS.measurableSpace] A → Q A = Q' A) ∧
    -- (b) the local stop of a driving path continuous beyond it
    (∀ᵐ ω ∂Q, ∃ ζ₀ : ℝ≥0∞, (S ω : ℝ≥0∞) < ζ₀ ∧ S ω = localStopPath r ζ₀ (fun t => W t ω) ∧
      ContinuousOn (fun t => drivingState W VL VR t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < ζ₀}) ∧
    -- (c) adaptedness before `S`
    AdaptedBefore 𝓓 (fun ω => (S ω : ℝ≥0∞)) W ∧ (∀ i, AdaptedBefore 𝓓 (fun ω => (S ω : ℝ≥0∞)) (VL i)) ∧
    (∀ j, AdaptedBefore 𝓓 (fun ω => (S ω : ℝ≥0∞)) (VR j)) ∧
    -- (d) the field and its law at time `0`
    Measurable h ∧
    (∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ (fun _ : Fin 1 => seedSumL xL ρL)
        (fun _ : Fin 1 => seedSumR xR ρR) LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀ →
      LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => h ω φ - ∫ z, u₀ z * φ z) Q) ∧
    -- (e) locality and the two-seed kernel at every stop `τ ≤ S`
    ∀ (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime 𝓓 τ), (∀ᵐ ω ∂Q, τ ω ≤ S ω) →
      IsLocalSet (fun ω => QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) h Q ∧
      ∀ u : Ω → ℂ → ℝ, (∀ ω, IsBoundedHarmonicExtension
          (forceBoundaryData κ (fun _ : Fin 1 => seedSumL xL ρL) (fun _ : Fin 1 => seedSumR xR ρR)
            (fun _ => seedPosL xL W VL τ ω) (fun _ => seedPosR xR W VR τ ω))
          (forceJumpSet (fun _ : Fin 1 => seedPosL xL W VL τ ω) (fun _ : Fin 1 => seedPosR xR W VR τ ω)) (u ω)) →
        ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂Q,
          Disjoint (tsupport φ) (QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) →
            Q[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | hτ.measurableSpace] ω =
              Complex.exp (Complex.I * ((∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)
                  (u ω) z * φ z : ℝ) : ℂ) -
                (((1 / 2 : ℝ) * loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) φ : ℝ) : ℂ))

/-- **Named input: Aux. lemma 54 for a stopped seed coupling** (specification p. 246: "Then the stopped coupling
extends to a full coupling with the original optional hull specification. The extension preserves the whole initial
field and uses only the stopped history and its active field when sampling the future"). For an ordered force word with
admissible seed sums (`> −2`) and a radius `r > 0`, every stopped seed coupling through its local stop `S` has an extended
reference pair over its own field, for the seed sums and the radius `r`, recovering its two-seed history stopped at `S`
(the driver and the merged seed marks, `twoSeedProj`). -/
def StoppedSeedExtensionStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (r : ℝ),
    IsOrderedForceWord xL xR → 0 < r → -2 < seedSumL xL ρL → -2 < seedSumR xR ρR →
    ∀ {Ω : Type u} {_ : MeasurableSpace Ω} (Q : Measure Ω) [IsProbabilityMeasure Q] (W : ℝ≥0 → Ω → ℝ)
      (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (S : Ω → WithTop ℝ≥0)
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsStoppedSeedCoupling κ xL xR ρL ρR r Q W VL VR S h →
      HasReferenceExtension.{u} κ (seedSumL xL ρL) (seedSumR xR ρR) r Q h
        (fun ω => twoSeedProj xL xR (stoppedHistory (drivingState W VL VR) S ω))

/-- **An extended reference pair over `g ∘ H` is one over `H`** (`g` measurable): the field map becomes `T ∘ g` and the
recovery map `F ∘ (g × id)`. -/
theorem HasReferenceExtension.comp {κ rL rR r : ℝ} {Ω : Type u} {_mΩ : MeasurableSpace Ω} {Q : Measure Ω}
    {γ γ' β : Type*} [MeasurableSpace γ] [MeasurableSpace γ'] [MeasurableSpace β] {H : Ω → γ} {g : γ → γ'}
    (hg : Measurable g) {Y : Ω → β} (hext : HasReferenceExtension.{u} κ rL rR r Q (fun ω => g (H ω)) Y) :
    HasReferenceExtension.{u} κ rL rR r Q H Y := by
  obtain ⟨T, hT, C, mC, E, hE, 𝓕', W', VL', VR', B', ζ', hEQ, hC', G', hG'm, hG'0, hG', F, hFm, hagree⟩ := hext
  exact ⟨fun x => T (g x), hT.comp hg, C, mC, E, hE, 𝓕', W', VL', VR', B', ζ', hEQ, hC', G', hG'm, hG'0, hG',
    fun p => F (g p.1, p.2), hFm.comp ((hg.comp measurable_fst).prodMk measurable_snd), hagree⟩

/-! ### Time `0`: the original coupling under `Q = Z·P` is a stopped seed coupling -/

section TimeZero

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {G : Set Ω}

/-- On a good path the capped local stop is the local stop of the path, strictly before the lifetime. -/
theorem capStop_eq_localStopPath (hG : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω)
    (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) {ω : Ω} (hω : ω ∈ G) :
    capStop r G ζ W ω = localStopPath r (ζ ω) (fun t => W t ω) ∧ (capStop r G ζ W ω : ℝ≥0∞) < ζ ω := by
  have h1 := capStop_eq_localStop hG hF hr hseed hω
  refine ⟨h1.trans (localStop_of_mem hω), ?_⟩
  rw [h1]
  exact localStop_lt hG hF hr hseed hω

/-- **Time `0` (Aux. lemma 55, steps 3–5): the original coupling under `Q = Z·P`, stopped at the capped local stop of a
good event with continuous noise, with the recoded field `h₀ = T(h)` of (HL8), is a stopped seed coupling.** (a) is
PROVE-LOCEXT-A3's Girsanov identification (`srcMeasure_girsanov`); (d)–(e) are PROVE-LOCEXT-D's GFF clause and step 5;
the filtration is the frozen driving filtration. -/
theorem isStoppedSeedCoupling_srcMeasure (hκ : 0 < κ) (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) (hGm : MeasurableSet G) (hGc : P Gᶜ = 0)
    (hG : ∀ ω ∈ G, IsGoodNoisePath κ xL xR ρL ρR W VL VR B ζ ω) :
    IsStoppedSeedCoupling κ xL xR ρL ρR r (srcMeasure κ ρL ρR P hF hr h) W VL VR (capStop r G ζ W)
      (fun ω => recode κ xL xR ρL ρR r (h ω)) := by
  obtain ⟨-, hPQ, hQP⟩ := srcMeasure_isEquiv hκ hC hF hr hseed
  have hX : IsMeasurableKilledDriving W VL VR ζ := Coupling.IsIntegratedSLEEvolution.isMeasurableKilledDriving hC.1
  have hGp : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω := fun ω hω => (hG ω hω).1
  have hS := isStoppingTime_capStop hX hGm hGc hGp r
  obtain ⟨hequiv, hevol, hagree⟩ := srcMeasure_girsanov hκ hC hF hr hseed hGm hGc hG hX
  have hGP : ∀ᵐ ω ∂P, ω ∈ G := ae_iff.2 hGc
  have hGQ : ∀ᵐ ω ∂(srcMeasure κ ρL ρR P hF hr h), ω ∈ G := hQP.ae_le hGP
  have hcap : (fun ω => (capTime r G ζ W ω : ℝ≥0∞)) = fun ω => ((capStop r G ζ W ω : WithTop ℝ≥0) : ℝ≥0∞) :=
    funext fun ω => coe_capTime ω
  have hdl : killedDrivingFiltration hX ≤ drivingFiltration P hX := Ito.le_usualAugmentation _ P
  have hSle : ∀ s : ℝ≥0, MeasurableSet[drivingFiltration P hX s]
      {ω | ((capStop r G ζ W ω : WithTop ℝ≥0) : ℝ≥0∞) ≤ (s : ℝ≥0∞)} := fun s => hS s
  have hSζ : ∀ ω, ((capStop r G ζ W ω : WithTop ℝ≥0) : ℝ≥0∞) ≤ ζ ω := fun ω => capStop_le r ω
  refine ⟨drivingFiltration P hX, hS, ⟨_, usualAugmentation 𝓕 P, _, hequiv.isProb, hQP.trans hequiv.ac',
    hequiv.ac.trans hPQ, Ito.drivingFiltration_le_usualAugmentation hC.1 hX, hcap ▸ hevol, hagree⟩, ?_,
    (Ito.adaptedBefore_mono hdl (Coupling.adaptedBefore_killedDriving_W hX)).of_le hSle hSζ,
    fun i => (Ito.adaptedBefore_mono hdl (Coupling.adaptedBefore_killedDriving_VL hX i)).of_le hSle hSζ,
    fun j => (Ito.adaptedBefore_mono hdl (Coupling.adaptedBefore_killedDriving_VR hX j)).of_le hSle hSζ,
    measurable_recode.comp hC.2.1, fun u₀ hu₀ => isZBGFFProcess_recode_srcMeasure hκ hC hF hr hseed hu₀, ?_⟩
  · filter_upwards [hGQ] with ω hω
    obtain ⟨h1, h2⟩ := capStop_eq_localStopPath hGp hF hr hseed hω
    have hp := (hGp ω hω).1
    refine ⟨ζ ω, h2, h1, ?_⟩
    exact hp.2.2.2.1.prodMk ((continuousOn_pi.2 fun i => hp.2.2.2.2.1 i).prodMk
      (continuousOn_pi.2 fun i => hp.2.2.2.2.2.1 i))
  · intro τ hτ hτS
    have hτP : ∀ᵐ ω ∂P, τ ω ≤ localStopPath r (ζ ω) fun t => W t ω := by
      filter_upwards [hPQ.ae_le hτS, hGP] with ω h1 h2
      rw [← (capStop_eq_localStopPath hGp hF hr hseed h2).1]
      exact h1
    exact ⟨isLocalSet_recode_srcMeasure hκ hC hF hr hseed hX hτ hτP, fun u hu φ =>
      condExp_recode_srcMeasure_eq_twoSeedKernel_of_pos hκ hC hF hr hseed hX hτ hτP hu φ⟩

end TimeZero

/-- **Aux. lemma 55 at time `0`, steps 3–6, from Aux. lemma 54**: the named input `StoppedSeedExtensionStatement κ`
(Aux. lemma 54 for stopped seed couplings) gives LOCEXT-C's `TwoSeedReferenceExtensionStatement κ`. The measure is
`Q = srcMeasure` ((HL3)); the stopped seed coupling is `isStoppedSeedCoupling_srcMeasure` on a good event with continuous
noise inside the given one; the field map is the recoding `T` of (HL8) (`HasReferenceExtension.comp`); on the good event
the two capped local stops agree and lie before the lifetime, where the completed state is the driving state. -/
theorem twoSeedReferenceExtensionStatement_of_stoppedSeedExtension {κ : ℝ} (hκ : 0 < κ)
    (hext : StoppedSeedExtensionStatement.{u} κ) : TwoSeedReferenceExtensionStatement.{u} κ := by
  intro nL nR xL xR ρL ρR hF hseed Ω mΩ P _ 𝓕 W VL VR B ζ h hC G hGm hG0 hG
  have hr : IsSeedRadius xL xR (seedRadius xL xR) := isSeedRadius_seedRadius xL xR
  obtain ⟨hQ, hPQ, hQP⟩ := srcMeasure_isEquiv hκ hC hF hr hseed
  obtain ⟨G', hG'G, hG'm, hG'0, hG'⟩ := exists_goodNoise_subset hC.1 hκ hGm hG0
  obtain ⟨hL, hR⟩ := seedSum_gt_of_not_thresholdCondition hseed
  have hmain := hext xL xR ρL ρR (seedRadius xL xR) hF hr.1 hL hR (srcMeasure κ ρL ρR P hF hr h) W VL VR
    (capStop (seedRadius xL xR) G' ζ W) _ (isStoppedSeedCoupling_srcMeasure hκ hC hF hr hseed hG'm hG'0 hG')
  refine ⟨srcMeasure κ ρL ρR P hF hr h, hQ, hPQ, hQP,
    (HasReferenceExtension.comp measurable_recode hmain).of_ae_eq (fun p => p.2) measurable_snd ?_⟩
  have hGP : ∀ᵐ ω ∂P, ω ∈ G' := ae_iff.2 hG'0
  filter_upwards [hQP.ae_le hGP] with ω hω
  have e1 := capStop_eq_localStopPath (fun ω hω => (hG' ω hω).1) hF hr hseed hω
  have e2 := capStop_eq_localStopPath hG hF hr hseed (hG'G hω)
  have heq : capStop (seedRadius xL xR) G ζ W ω = capStop (seedRadius xL xR) G' ζ W ω := e2.1.trans e1.1.symm
  show twoSeedProj xL xR (stoppedHistory (completedState W VL VR ζ) (capStop (seedRadius xL xR) G ζ W) ω) =
    twoSeedProj xL xR (stoppedHistory (drivingState W VL VR) (capStop (seedRadius xL xR) G' ζ W) ω)
  rw [stoppedHistory_congr (X := completedState W VL VR ζ) heq]
  congr 1
  refine Prod.ext rfl (funext fun q => ?_)
  have hlt : ((stopAt (capStop (seedRadius xL xR) G' ζ W) q ω : ℝ≥0) : ℝ≥0∞) < ζ ω :=
    lt_of_le_of_lt (stopAt_le _ q ω) e1.2
  simp only [stoppedHistory, completedState, hlt, ite_true]

end LocalExt

end InteractingSLE
