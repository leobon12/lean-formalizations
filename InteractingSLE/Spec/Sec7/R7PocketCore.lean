/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7PocketPhase
import InteractingSLE.Spec.Sec7.Lemma725RefSafeWord

/-!
# The two-seed pocket with its field for every seed weight `> −2`, the phase already zero

Packet PROVE-R7POCKET. Theorem R.7 (`source/spec/p433-480.md` L1051–L1070, pp. 477–478) with Lemma R.6
(L1024–L1048) and Aux. lemmas 122, 125 (`source/spec/p385-432.md` L104–L131, L197–L250).

PROVE-LEMMA725REF3's core (`Lemma725RefSafe.exists_pocketField_core`) produces (E), (S), (L) on one restricted space
from the pocket field's coupling clause `IsCouplingCharFun` — the clause with the **canonical** (zero-phase) coupling
means. Its two calls to Aux. lemma 122 (`ae_capLife_eq_top_of_hasPhaseMeans`, `aux122_isRandomWordEvolution`) carry
the upper seed-weight bound `< κ − 6` only for the phase selection, which is void here (`d = 0`). With the zero-phase
versions (`R7PocketPhase`) the core holds for all seed weights `> −2`:

* `PocketWord.aux122_isRandomWordEvolution_zeroPhase`: Aux. lemma 122's SDE conclusion with the phase already zero;
* **`exists_pocketField_core_zeroPhase`**: the core without the bound `< κ − 6`.

The proofs after the selection are PROVE-STRIPSYS6's and PROVE-LEMMA725REF3's, unchanged. Conditional helpers with
distinct names; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or a result taking them as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketWord

open MartChar Aux117 PhaseSel PhaseSelFull

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- **Aux. lemma 122's SDE conclusion with a random initial word, the phase already zero**
(`aux122_isRandomWordEvolution` with `d = 0`): no seed-weight bound; the time-zero event is `univ`. -/
theorem aux122_isRandomWordEvolution_zeroPhase [IsProbabilityMeasure P] {k : ℝ} (hk : 0 < k)
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ}
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
    (hmart : ∀ U : Ω → ℝ≥0 → ℂ → ℝ, (∀ ω t, IsBoundedHarmonicExtension
        (phaseData k ρL ρR (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω) 0)
        (forceJumpSet (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω)) (U ω t)) →
      ∀ z ∈ H, IsLocalMartingaleBefore 𝓕 P (fun ω => (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0))
        (fun t ω => couplingMean k (wpath W ω) t (U ω t) z)) :
    ∃ A : Set Ω, MeasurableSet[𝓕 0] A ∧ P A = 1 ∧
      ∃ B : ℝ≥0 → A → ℝ, Aux122Disint.IsRandomWordEvolution k (condSub P A) (subFilt 𝓕 A 0) univ
        (fun (ω : A) i => VL i 0 ω) (fun (ω : A) j => VR j 0 ω) ρL ρR (subFilt 𝓕 A) (fun t (ω : A) => W t ω)
        (fun i t (ω : A) => VL i t ω) (fun j t (ω : A) => VR j t ω) B
        (fun ω : A => thresholdTime ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω)) := by
  have hA0 : MeasurableSet[𝓕 0] (univ : Set Ω) := @MeasurableSet.univ _ (𝓕 0)
  have h0 : P univ ≠ 0 := by rw [measure_univ]; exact one_ne_zero
  have : IsProbabilityMeasure (condSub P univ) := isProbabilityMeasure_condSub MeasurableSet.univ h0
  -- the canonical extension extends the zero-phase data
  set U : Ω → ℝ≥0 → ℂ → ℝ := fun ω t => meanExt k ρL ρR (W t ω) (fun i => VL i t ω) (fun j => VR j t ω)
    with hUdef
  have hU : ∀ ω t, IsBoundedHarmonicExtension
      (phaseData k ρL ρR (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω) 0)
      (forceJumpSet (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω)) (U ω t) := by
    intro ω t
    have h := isBoundedHarmonicExtension_unshift (c := 0) hk (sub_nonpos.2 (hordL ω t 0))
      (sub_nonneg.2 (hordR ω t 0)) (isBoundedHarmonicExtension_meanExt k (shiftL k ρL 0) (shiftR k ρR 0) (W t ω)
        (fun i => VL i t ω) (fun j => VR j t ω))
    simp only [shiftL_zero_eq, shiftR_zero_eq, add_zero] at h
    exact h
  have hmA : ∀ z ∈ H, IsLocalMartingaleBefore (subFilt 𝓕 univ) (condSub P univ)
      (fun ω : (univ : Set Ω) => (QuantumZipper.swallowTime (wpath (fun t (ω : (univ : Set Ω)) => W t ω) ω) z :
        WithTop ℝ≥0))
      (coupProc k ρL ρR (fun t (ω : (univ : Set Ω)) => W t ω) (fun i t (ω : (univ : Set Ω)) => VL i t ω)
        (fun j t (ω : (univ : Set Ω)) => VR j t ω) z) :=
    fun z hz => isLocalMartingaleBefore_sub hA0 h0 (hmart U hU z hz)
  refine ⟨univ, hA0, measure_univ, _,
    isRandomWordEvolution_of_coupProc (P := condSub P univ) (𝓕 := subFilt 𝓕 univ) (ρL := ρL) (ρR := ρR)
      (W := fun t (ω : (univ : Set Ω)) => W t ω) (VL := fun i t (ω : (univ : Set Ω)) => VL i t ω)
      (VR := fun j t (ω : (univ : Set Ω)) => VR j t ω)
      hk (fun ω => hW0 ω) (fun ω => hWc ω) (stronglyAdapted_sub hWa)
      (fun i => stronglyAdapted_sub (hVLa i)) (fun i => stronglyAdapted_sub (hVRa i)) (fun ω => hordL ω)
      (fun ω => hordR ω) (fun ω => hpathL ω) (fun ω => hpathR ω) (fun ω => hantiL ω) (fun ω => hmonoR ω)
      (fun ω => hidxL ω) (fun ω => hidxR ω) (fun ω => hmergeL ω) (fun ω => hmergeR ω) (fun ω => hsep ω) hmA⟩

end InteractingSLE.Sec7.PocketWord

namespace InteractingSLE.Sec7.Lemma725RefSafe

open Restart.DomainMarkov Restart.DomainMarkov.K2 Aux122Disint PhaseSel PocketMartLife PocketCoupling LocalSets
  Coupling MartChar PocketTraversal Lemma71C PocketAdapt PocketWordLife LawUnique

section Word

universe u


/-- **The pocket evolution with its field on one restricted space, the phase already zero**
(`exists_pocketField_core` without the bound `< κ − 6`; the core of the pocket, Aux. lemmas
122 and 125, pp. 389–398). On a standard Borel probability space with initial information `𝓔` (the walls): a random
curve `γ`, driven for every `ω`, with points of `ℍ` of arbitrarily large modulus and measurable at fixed own times;
`𝓔`-measurable ordered marks with seeds at `0`; weights with all side partial sums `> −2` and **no upper bound on
the seed weights** (the phase is already zero in the clause, so Aux. lemma 122's selection is void); and a measurable
field `X` (the pocket field in the pocket chart) with the conditional-law clause of the word in
the usual augmentation of the relative history filtration (the input of the landed chain
`PocketAdapt.pocketWordEvolution_of_charFun_prefixFilt`) and K2's member identities (L) in the relative history
filtration. Then there are a standard Borel probability space `Ω₃` and a measurable map `π : Ω₃ → Ω` transporting
`P`-null sets to null sets, on which the relative lifetime is infinite, the driver, its geometric force coordinates and
a Brownian motion form an integrated evolution of the word `(x^L ∘ π, x^R ∘ π)` with lifetime `∞` and initial
information `π⁻¹𝓔` (Aux. lemma 122), and `X ∘ π` has K2's (S) and (L) in a filtration `𝓗'` with `π⁻¹𝓔 ≤ 𝓗'_0` in which
the driver and the coordinates are adapted. (E) is produced as in the landed chain (the restrictions to infinite
relative lifetime and to Aux. lemma 122's event of full measure), (S) is the clause at constant times
(`hasSafeLaw_of_isCouplingCharFun`), and (S), (L) are carried along the restrictions. -/
theorem exists_pocketField_core_zeroPhase {κ : ℝ} (hκ : 4 < κ) {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ}
    {ρR : Fin (nR + 1) → ℝ} (hsL : ∀ m : Fin (nL + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρL i)
    (hsR : ∀ m : Fin (nR + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρR i)
    {Ω : Type u} {𝓔 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (h𝓔 : 𝓔 ≤ mΩ) {γ : Ω → ℝ → ℂ} (hγ : ∀ ω, IsDrivenCurve (γ ω))
    (hγm : ∀ u, 0 ≤ u → Measurable[mΩ] fun ω => γ ω u)
    (hunb : ∀ ω (M : ℝ), ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} (hxLm : Measurable[𝓔] xL) (hxRm : Measurable[𝓔] xR)
    (hseedL : ∀ ω, xL ω 0 = 0) (hseedR : ∀ ω, xR ω 0 = 0)
    (hxLi : ∀ ω, Antitone (xL ω)) (hxRi : ∀ ω, Monotone (xR ω)) {X : Ω → DistOn upperHalfPlaneOpens}
    (hXm : Measurable X) (hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => X ω φ) P)
    (hcf : MartMeans.IsCouplingCharFun κ ρL ρR P
      (usualAugmentation (prefixFilt 𝓔 h𝓔 γ fun r n k => PocketMeas.measurableSet_prefixEvent hγ hγm r n k) P)
      (fun t ω => segDriver (γ ω) t) (geomLW (fun t ω => segDriver (γ ω) t) xL)
      (geomRW (fun t ω => segDriver (γ ω) t) xR) (fun ω => capLife (γ ω)) X)
    (hmem : HasSafeMembers P (prefixFilt 𝓔 h𝓔 γ fun r n k => PocketMeas.measurableSet_prefixEvent hγ hγm r n k)
      univ (fun ω => capLife (γ ω)) (fun t ω => segDriver (γ ω) t) X) :
    ∃ (Ω₃ : Type u) (m₃ : MeasurableSpace Ω₃) (_ : StandardBorelSpace Ω₃) (P₃ : Measure Ω₃)
      (_ : IsProbabilityMeasure P₃) (π : Ω₃ → Ω) (B : ℝ≥0 → Ω₃ → ℝ) (𝓗 𝓗' : Filtration ℝ≥0 m₃),
      Measurable π ∧ (∀ p : Ω → Prop, (∀ᵐ ω ∂P, p ω) → ∀ᵐ ω ∂P₃, p (π ω)) ∧
      (∀ ω, capLife (γ (π ω)) = ⊤) ∧
      IsRandomWordEvolution κ P₃ (MeasurableSpace.comap π 𝓔) univ (fun ω => xL (π ω)) (fun ω => xR (π ω)) ρL ρR
        𝓗 (fun t ω => segDriver (γ (π ω)) t) (fun i t ω => geomLW (fun t ω => segDriver (γ ω) t) xL i t (π ω))
        (fun j t ω => geomRW (fun t ω => segDriver (γ ω) t) xR j t (π ω)) B (fun _ => ⊤) ∧
      MeasurableSpace.comap π 𝓔 ≤ 𝓗' 0 ∧ AdaptedBefore 𝓗' (fun _ => ⊤) (fun t ω => segDriver (γ (π ω)) t) ∧
      (∀ i, AdaptedBefore 𝓗' (fun _ => ⊤) (fun t ω => geomLW (fun t ω => segDriver (γ ω) t) xL i t (π ω))) ∧
      (∀ j, AdaptedBefore 𝓗' (fun _ => ⊤) (fun t ω => geomRW (fun t ω => segDriver (γ ω) t) xR j t (π ω))) ∧
      HasSafeLaw κ ρL ρR P₃ 𝓗' univ (fun _ => ⊤) (fun t ω => segDriver (γ (π ω)) t)
        (fun i t ω => geomLW (fun t ω => segDriver (γ ω) t) xL i t (π ω))
        (fun j t ω => geomRW (fun t ω => segDriver (γ ω) t) xR j t (π ω)) (fun ω => X (π ω)) ∧
      HasSafeMembers P₃ 𝓗' univ (fun _ => ⊤) (fun t ω => segDriver (γ (π ω)) t) fun ω => X (π ω) := by
  classical
  have hm : ∀ r n k, MeasurableSet[mΩ] (prefixEvent γ r n k) := fun r n k =>
    PocketMeas.measurableSet_prefixEvent hγ hγm r n k
  set Fp := prefixFilt 𝓔 h𝓔 γ hm with hFp
  set 𝓕 := usualAugmentation Fp P with h𝓕
  have hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓕 0] s := fun s hs h0 =>
    Ito.measurableSet_usualAugmentation_of_null hs h0 0
  have hpre : IsPrefixAdapted 𝓕 γ := isPrefixAdapted_usualAugmentation_prefixFilt h𝓔 hm P
  have h0 : 𝓔 ≤ 𝓕 0 := (le_prefixFilt_zero h𝓔 hm).trans (Ito.le_usualAugmentation _ P 0)
  have hxLm' : Measurable[𝓕 0] xL := hxLm.mono h0 le_rfl
  have hxRm' : Measurable[𝓕 0] xR := hxRm.mono h0 le_rfl
  set W : ℝ≥0 → Ω → ℝ := fun t ω => segDriver (γ ω) t with hWdef
  have hM := PocketPhaseMeans.hasPhaseMeansBefore_zero_of_charFun hnull (fun ω => (hγ ω).segDriver_spec.1)
    (fun ω => PocketPhaseMeans.capLife_pos (hγ ω)) (fun ω => (hγ ω).segDriver_spec.2.1)
    (adaptedBefore_segDriver_of_isDrivenCurve hγ hpre)
    (Eventually.of_forall fun ω hfin C => PocketLife.exists_lt_abs_segDriver (hγ ω) (hunb ω) hfin C)
    hxLm' hxRm' hint hcf
  set d : ℝ≥0 → Ω → ℝ := fun _ _ => 0 with hd_def
  -- the event of infinite lifetime: a time-zero event of full measure
  set G : Set Ω := {ω | capLife (γ ω) = ⊤} with hGdef
  have hGm : MeasurableSet G := by
    have e : G = ⋂ n : ℕ, {ω | ((n : ℝ≥0) : ℝ≥0∞) < capLife (γ ω)} := by
      ext ω
      simp only [hGdef, mem_ofPred_eq, mem_iInter]
      constructor
      · intro h n; rw [h]; exact ENNReal.coe_lt_top
      · intro h
        by_contra hne
        obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hne
        exact absurd (h n) (not_lt.2 (by exact_mod_cast hn.le))
    rw [e]
    exact MeasurableSet.iInter fun n => 𝓕.le _ _ (measurableSet_lt_capLife hpre (fun ω => (hγ ω).zero) n)
  have hae := ae_capLife_eq_top_of_hasPhaseMeans_zeroPhase hκ hsL hsR hγ hunb hpre hxLm' hxRm' hseedL hseedR
    hxLi hxRi hM
  have hGc : P Gᶜ = 0 := by
    rw [ae_iff] at hae
    exact hae
  have hG0 : MeasurableSet[𝓕 0] G := by
    have h := (hnull Gᶜ hGm.compl hGc).compl
    rwa [compl_compl] at h
  have hPG : P G ≠ 0 := by
    intro h0
    have h1 : P (G ∪ Gᶜ) = 0 := measure_union_null h0 hGc
    rw [union_compl_self, measure_univ] at h1
    exact one_ne_zero h1
  have hSB : StandardBorelSpace G := hGm.standardBorel
  have hQ : IsProbabilityMeasure (condSub P G) := isProbabilityMeasure_condSub hGm hPG
  have hRC : (subFilt 𝓕 G).IsRightContinuous := isRightContinuous_subFilt G
  have hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < capLife (γ ω)} := fun ω =>
    (hγ ω).segDriver_spec.2.1
  -- the explicit extension of the data before the lifetime
  have hκ0 : 0 < κ := by linarith
  set U₀ : Ω → ℝ≥0 → ℂ → ℝ := fun ω t ξ => meanExt κ (shiftL κ ρL (d t ω)) (shiftR κ ρR (d t ω)) (W t ω)
    (fun i => geomLW W xL i t ω) (fun j => geomRW W xR j t ω) ξ + d t ω with hU₀def
  have hU₀ : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < capLife (γ ω) → IsBoundedHarmonicExtension
      (phaseData κ ρL ρR (fun i => geomLW W xL i t ω - W t ω) (fun j => geomRW W xR j t ω - W t ω) (d t ω))
      (forceJumpSet (fun i => geomLW W xL i t ω - W t ω) (fun j => geomRW W xR j t ω - W t ω)) (U₀ ω t) :=
    fun ω t ht => isBoundedHarmonicExtension_unshift hκ0 (sub_nonpos.2 (geomLW_le_of_lt (hWc ω) ht xL 0))
      (sub_nonneg.2 (le_geomRW_of_lt (hWc ω) ht xR 0)) (isBoundedHarmonicExtension_meanExt κ _ _ (W t ω) _ _)
  -- extensions on `G` extend to extensions before the lifetime on `Ω`
  have key : ∀ U' : G → ℝ≥0 → ℂ → ℝ, (∀ (ω : G) t, IsBoundedHarmonicExtension
      (phaseData κ ρL ρR (fun i => geomLW W xL i t ω - W t ω) (fun j => geomRW W xR j t ω - W t ω) (d t ω))
      (forceJumpSet (fun i => geomLW W xL i t ω - W t ω) (fun j => geomRW W xR j t ω - W t ω)) (U' ω t)) →
      ∃ U : Ω → ℝ≥0 → ℂ → ℝ, (∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < capLife (γ ω) → IsBoundedHarmonicExtension
        (phaseData κ ρL ρR (fun i => geomLW W xL i t ω - W t ω) (fun j => geomRW W xR j t ω - W t ω) (d t ω))
        (forceJumpSet (fun i => geomLW W xL i t ω - W t ω) (fun j => geomRW W xR j t ω - W t ω)) (U ω t)) ∧
        ∀ ω : G, U ω = U' ω := by
    intro U' hU'
    refine ⟨fun ω t => if h : ω ∈ G then U' ⟨ω, h⟩ t else U₀ ω t, fun ω t ht => ?_, fun ω => ?_⟩
    · by_cases h : ω ∈ G
      · simp only [h, ↓reduceDIte]; exact hU' ⟨ω, h⟩ t
      · simp only [h, ↓reduceDIte]; exact hU₀ ω t ht
    · funext t
      simp only [ω.2, ↓reduceDIte]
  have hlife : ∀ ω : G, capLife (γ ω) = ⊤ := fun ω => ω.2
  -- the restricted data on `G`
  set W₂ : ℝ≥0 → G → ℝ := fun t ω => W t ω with hW₂def
  set xL₂ : G → Fin (nL + 1) → ℝ := fun ω => xL ω with hxL₂def
  set xR₂ : G → Fin (nR + 1) → ℝ := fun ω => xR ω with hxR₂def
  have hW0₂ : ∀ ω, W₂ 0 ω = 0 := fun ω => (hγ ω).segDriver_spec.1
  have hWc₂ : ∀ ω, Continuous fun t => W₂ t ω := fun ω =>
    (hγ ω).continuous_segDriver_of_capLife_eq_top (hlife ω)
  have hWa₂ : StronglyAdapted (subFilt 𝓕 G) W₂ :=
    stronglyAdapted_segDriver_of_capLife_eq_top (fun ω : G => hγ ω) hlife (isPrefixAdapted_sub hpre G)
  have hxLm₂ : Measurable[subFilt 𝓕 G 0] xL₂ := hxLm'.comp (Measurable.of_comap_le le_rfl)
  have hxRm₂ : Measurable[subFilt 𝓕 G 0] xR₂ := hxRm'.comp (Measurable.of_comap_le le_rfl)
  have hmart₂ : ∀ U : G → ℝ≥0 → ℂ → ℝ, (∀ ω t, IsBoundedHarmonicExtension
      (phaseData κ ρL ρR (fun i => geomLW W₂ xL₂ i t ω - W₂ t ω) (fun j => geomRW W₂ xR₂ j t ω - W₂ t ω) (d t ω))
      (forceJumpSet (fun i => geomLW W₂ xL₂ i t ω - W₂ t ω) (fun j => geomRW W₂ xR₂ j t ω - W₂ t ω)) (U ω t)) →
      ∀ z ∈ H, IsLocalMartingaleBefore (subFilt 𝓕 G) (condSub P G)
        (fun ω => (QuantumZipper.swallowTime (wpath W₂ ω) z : WithTop ℝ≥0))
        (fun t ω => couplingMean κ (wpath W₂ ω) t (U ω t) z) := by
    intro U' hU' z hz
    obtain ⟨U, hU, hUU⟩ := key U' hU'
    have h1 := isLocalMartingaleBefore_sub hG0 hPG ((hM U hU).1 z hz)
    have h2 := PhaseSelAdapt.isLocalMartingaleBefore_congr_life
      (ζ' := fun ω : G => (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0))
      (fun ω => by simp only [hlife ω]; exact min_top_right _) h1
    have e : (fun (t : ℝ≥0) (ω : G) => couplingMean κ (wpath W ω) t (U ω t) z) =
        fun (t : ℝ≥0) (ω : G) => couplingMean κ (wpath W ω) t (U' ω t) z := by
      funext t ω
      rw [hUU ω]
    rw [e] at h2
    exact h2
  -- Aux. lemma 122 on `G` (the last step of `pocketWordEvolution_of_geom`)
  obtain ⟨A', hA'0, hP1, B, hE⟩ := PocketWord.aux122_isRandomWordEvolution_zeroPhase (P := condSub P G)
    (𝓕 := subFilt 𝓕 G) hκ0 (VL := geomLW W₂ xL₂) (VR := geomRW W₂ xR₂)
    hW0₂ hWc₂ hWa₂ (stronglyAdapted_geomLW hWa₂ hWc₂ hxLm₂) (stronglyAdapted_geomRW hWa₂ hWc₂ hxRm₂)
    (fun ω t i => geomLW_le hWc₂ xL₂ ω t i) (fun ω t j => le_geomRW hWc₂ xR₂ ω t j)
    (isForcePath_geomLW hWc₂ xL₂) (isForcePath_geomRW hWc₂ xR₂) (antitone_geomLW hWc₂ xL₂)
    (monotone_geomRW hWc₂ xR₂) (fun ω t => antitone_index_geomLW hWc₂ (hxLi ω) t)
    (fun ω t => monotone_index_geomRW hWc₂ (hxRi ω) t) (fun ω i j s t hst => geomLW_merge hWc₂ xL₂ ω i j s t hst)
    (fun ω i j s t hst => geomRW_merge hWc₂ xR₂ ω i j s t hst)
    (fun ω t ht i j => geom_sep hWc₂ xL₂ xR₂ ω t ht i j) hmart₂
  -- the restriction to Aux. lemma 122's event `A'` of full measure
  have hA'm : MeasurableSet A' := (subFilt 𝓕 G).le 0 _ hA'0
  have hPA' : condSub P G A' ≠ 0 := by rw [hP1]; exact one_ne_zero
  have hSB3 : StandardBorelSpace A' := hA'm.standardBorel
  have hQ3 : IsProbabilityMeasure (condSub (condSub P G) A') := isProbabilityMeasure_condSub hA'm hPA'
  have hA'ae : ∀ᵐ ω ∂(condSub P G), ω ∈ A' := ae_iff.2 ((prob_compl_eq_zero_iff hA'm).2 hP1)
  -- the lifetime of (E) is infinite
  have hζ₃ : ∀ ω : A', thresholdTime ρL ρR (fun t => W₂ t ω) (fun i t => geomLW W₂ xL₂ i t ω)
      (fun j t => geomRW W₂ xR₂ j t ω) = ⊤ := fun ω =>
    thresholdTime_eq_top_of_partialSums hsL hsR (fun t i => geomLW_le hWc₂ xL₂ ω t i)
      (fun t => antitone_index_geomLW hWc₂ (hxLi ω) t) (fun t j => le_geomRW hWc₂ xR₂ ω t j)
      (fun t => monotone_index_geomRW hWc₂ (hxRi ω) t)
  -- the word is the marks
  have hxLnp : ∀ ω i, xL ω i ≤ 0 := fun ω i => (hxLi ω (Fin.zero_le i)).trans_eq (hseedL ω)
  have hxRnn : ∀ ω j, 0 ≤ xR ω j := fun ω j => (hseedR ω).symm.trans_le (hxRi ω (Fin.zero_le j))
  have eΘL : (fun (ω : A') i => geomLW W₂ xL₂ i 0 (ω : G)) = fun (ω : A') => xL ((ω : G) : Ω) := funext fun ω =>
    funext fun i => geomLW_zero hWc₂ hW0₂ (hxLnp _ i)
  have eΘR : (fun (ω : A') j => geomRW W₂ xR₂ j 0 (ω : G)) = fun (ω : A') => xR ((ω : G) : Ω) := funext fun ω =>
    funext fun j => geomRW_zero hWc₂ hW0₂ (hxRnn _ j)
  rw [eΘL, eΘR] at hE
  have hE3 := hE.mono_sigma (𝓔' := MeasurableSpace.comap (Subtype.val : A' → G)
      (MeasurableSpace.comap (Subtype.val : G → Ω) 𝓔)) (MeasurableSpace.comap_mono (MeasurableSpace.comap_mono h0))
    MeasurableSet.univ (fun s hs => ⟨_, ⟨_, hxLm hs, rfl⟩, rfl⟩) (fun s hs => ⟨_, ⟨_, hxRm hs, rfl⟩, rfl⟩)
  -- (S), (L) and the determination on `A'`
  have hS1 : HasSafeLaw κ ρL ρR P Fp univ (fun ω => capLife (γ ω)) W (geomLW W xL) (geomRW W xR) X :=
    hasSafeLaw_of_isCouplingCharFun (fun q => Ito.le_usualAugmentation Fp P q) hXm hae hcf univ
  have hS3 := hasSafeLaw_subtype hA'm (subtype_cond_of_ae hA'ae) (hasSafeLaw_subtype hGm (subtype_cond_of_ae hae) hS1)
  have hL3 := hasSafeMembers_subtype hA'm (subtype_cond_of_ae hA'ae)
    (hasSafeMembers_subtype hGm (subtype_cond_of_ae hae) hmem)
  have hζle : ∀ ω : A', thresholdTime ρL ρR (fun t => W₂ t ω) (fun i t => geomLW W₂ xL₂ i t ω)
      (fun j t => geomRW W₂ xR₂ j t ω) ≤ capLife (γ ((ω : G) : Ω)) := fun ω => by
    rw [hlife ω]
    exact le_top
  have hWaP : AdaptedBefore Fp (fun ω => capLife (γ ω)) W :=
    adaptedBefore_segDriver_of_isDrivenCurve hγ (isPrefixAdapted_prefixFilt h𝓔 hm)
  have hxLP : Measurable[Fp 0] xL := hxLm.mono (le_prefixFilt_zero h𝓔 hm) le_rfl
  have hxRP : Measurable[Fp 0] xR := hxRm.mono (le_prefixFilt_zero h𝓔 hm) le_rfl
  have hζfun : (fun ω : A' => thresholdTime ρL ρR (fun t => W₂ t ω) (fun i t => geomLW W₂ xL₂ i t ω)
      (fun j t => geomRW W₂ xR₂ j t ω)) = fun _ => ⊤ := funext hζ₃
  have hGtop : ∀ ω ∈ G, capLife (γ ω) = ⊤ := fun _ hω => hω
  rw [hζfun] at hE3
  have e𝓔 : MeasurableSpace.comap (fun ω : A' => ((ω : G) : Ω)) 𝓔 =
      MeasurableSpace.comap (Subtype.val : A' → G) (MeasurableSpace.comap (Subtype.val : G → Ω) 𝓔) :=
    by rw [MeasurableSpace.comap_comp]; rfl
  refine ⟨A', inferInstance, hSB3, condSub (condSub P G) A', hQ3, fun ω => ((ω : G) : Ω), B,
    subFilt (subFilt 𝓕 G) A', subFilt (subFilt Fp G) A',
    measurable_subtype_coe.comp measurable_subtype_coe, fun p hp => ae_condSub_of_ae hA'm (ae_condSub_of_ae hGm hp),
    fun ω => hlife ω, ?_, e𝓔 ▸ MeasurableSpace.comap_mono (MeasurableSpace.comap_mono (le_prefixFilt_zero h𝓔 hm)),
    adaptedBefore_subtype (adaptedBefore_subtype_top hWaP hGtop) A',
    fun i => adaptedBefore_subtype (adaptedBefore_subtype_top
      (PocketPhaseMeans.adaptedBefore_geomLW hWc hWaP hxLP i) hGtop) A',
    fun j => adaptedBefore_subtype (adaptedBefore_subtype_top
      (PocketPhaseMeans.adaptedBefore_geomRW hWc hWaP hxRP j) hGtop) A',
    hasSafeLaw_mono_life (fun ω => le_top.trans_eq (hlife ω).symm) hS3,
    hasSafeMembers_mono_life (fun ω => le_top.trans_eq (hlife ω).symm) hL3⟩
  rw [e𝓔]
  exact hE3

end Word

end InteractingSLE.Sec7.Lemma725RefSafe
