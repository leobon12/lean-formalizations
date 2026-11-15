/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketMartLifeAe
import InteractingSLE.Spec.Sec7.PocketTraversalWord
import InteractingSLE.Spec.Sec7.Lemma71DUsual
import InteractingSLE.Spec.Coupling.CompactTransfer

/-!
# Lemma 7.25's pocket-word evolution with the lifetime only defined before it (hPW without `hγL`)

Packet PROVE-STRIPSYS14 (specification §7.4.1, proof of Lemma 7.25, `source/spec/p385-432.md` L490–L515, p. 414; Aux.
lemma 122, pp. 389–391; Aux. lemma 125, pp. 395–397).

PROVE-STRIPSYS10's `PocketTraversal.pocketWordEvolution_of_drivenCurve` assumes the relative curve driven for all
capacity times (`hγL : ∀ ω, capLife (γ ω) = ⊤`) and the martingale inputs for the globally defined driver. Here
both are replaced by Aux. lemma 122's hypotheses **before the terminal capacity time** (`HasPhaseMeansBefore`), the form
the field-level inputs (R.5, Aux. lemmas 27–29) can supply. Aux. lemma 125
(`PocketMartLife.ae_capLife_eq_top_of_hasPhaseMeans`) gives `capLife = ∞` almost surely; on that event (a time-zero
event when the time-zero σ-algebra contains the null sets, the usual conditions of R34) the hypotheses of
`pocketWordEvolution_of_drivenCurve` hold for every `ω` under the conditional law.

## Main results

* `isRightContinuous_subFilt`: the trace of a right-continuous filtration on a subset is right-continuous;
* `isPrefixAdapted_sub`: adapted filled prefixes stay adapted for the trace filtration;
* **`pocketWordEvolution_of_hasPhaseMeans`**: `Lemma725Ref.PocketWordEvolution κ r_L r_R` (hPW).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

universe v

namespace InteractingSLE.Sec7.PocketWordLife

open MartChar PocketTraversal PhaseSel PocketMartLife Lemma71C

section Sub

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- **The `limsup` of events of `𝓕` at the times `t + 1/(n+1)` is an event of `𝓕_t`**, for a right-continuous
filtration. -/
theorem measurableSet_limsup_of_isRightContinuous [𝓕.IsRightContinuous] {t : ℝ≥0} {B : ℕ → Set Ω}
    (hB : ∀ n : ℕ, MeasurableSet[𝓕 (t + 1 / ((n : ℝ≥0) + 1))] (B n)) :
    MeasurableSet[𝓕 t] (⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : N ≤ n), B n) := by
  set u : ℕ → ℝ≥0 := fun n => t + 1 / ((n : ℝ≥0) + 1) with hudef
  have hanti : Antitone u := fun n n' hnn' => by
    simp only [hudef]
    gcongr
  refine Filtration.IsRightContinuous.measurableSet ?_
  rw [Filtration.rightCont_eq_of_neBot_nhdsGT]
  refine MeasurableSpace.measurableSet_iInf.2 fun w => MeasurableSpace.measurableSet_iInf.2 fun hw => ?_
  obtain ⟨M, hM⟩ := exists_nat_one_div_lt (tsub_pos_of_lt hw)
  have huM : u M ≤ w := by
    have h := add_lt_add_left hM t
    rw [tsub_add_cancel_of_le hw.le, add_comm] at h
    exact h.le
  have e : (⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : N ≤ n), B n) = ⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : N + M ≤ n), B n := by
    ext ω
    simp only [mem_iInter, mem_iUnion, exists_prop]
    refine ⟨fun h N => h (N + M), fun h N => ?_⟩
    obtain ⟨n, hn, hω⟩ := h N
    exact ⟨n, le_trans (Nat.le_add_right N M) hn, hω⟩
  rw [e]
  refine MeasurableSet.iInter fun N => MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun hn => ?_
  exact 𝓕.mono ((hanti (le_trans (Nat.le_add_left M N) hn)).trans huM) _ (hB n)

theorem lt_add_one_div (t : ℝ≥0) (n : ℕ) : t < t + 1 / ((n : ℝ≥0) + 1) :=
  lt_add_of_pos_right t (by positivity)

/-- **The trace of a right-continuous filtration on a subset is right-continuous** (a set of `⨅_{u > t} 𝓕_u` on the
subset is the trace of the `limsup` of traces at times `t + 1/(n+1)`, which lies in `𝓕_{t+}= 𝓕_t`). -/
theorem isRightContinuous_subFilt [𝓕.IsRightContinuous] (A : Set Ω) : (subFilt 𝓕 A).IsRightContinuous := by
  refine ⟨fun t s hs => ?_⟩
  rw [Filtration.rightCont_eq_of_neBot_nhdsGT] at hs
  have hu : ∀ n : ℕ, MeasurableSet[subFilt 𝓕 A (t + 1 / ((n : ℝ≥0) + 1))] s := fun n =>
    MeasurableSpace.measurableSet_iInf.1 (MeasurableSpace.measurableSet_iInf.1 hs _) (lt_add_one_div t n)
  choose B hB hBs using hu
  refine ⟨_, measurableSet_limsup_of_isRightContinuous hB, ?_⟩
  ext ω
  simp only [mem_preimage, mem_iInter, mem_iUnion, exists_prop]
  constructor
  · intro h
    obtain ⟨n, -, hn⟩ := h 0
    have : ω ∈ (Subtype.val ⁻¹' B n : Set A) := hn
    rwa [hBs n] at this
  · intro h N
    refine ⟨N, le_rfl, ?_⟩
    have : ω ∈ (Subtype.val ⁻¹' B N : Set A) := by rw [hBs N]; exact h
    exact this

/-- **Adapted filled prefixes stay adapted for the trace filtration.** -/
theorem isPrefixAdapted_sub {γ : Ω → ℝ → ℂ} (hpre : IsPrefixAdapted 𝓕 γ) (A : Set Ω) :
    IsPrefixAdapted (subFilt 𝓕 A) (fun ω : A => γ ω) := fun r n k => ⟨_, hpre r n k, rfl⟩

end Sub

/-! ### The null augmentation of a right-continuous filtration -/

section Null

open Ito

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- **The null augmentation of a right-continuous filtration is right-continuous.** -/
theorem isRightContinuous_nullAugmented [𝓕.IsRightContinuous] : (nullAugmented 𝓕 P).IsRightContinuous := by
  refine ⟨fun t s hs => ?_⟩
  rw [Filtration.rightCont_eq_of_neBot_nhdsGT] at hs
  have hu : ∀ n : ℕ, MeasurableSet[nullAugmented 𝓕 P (t + 1 / ((n : ℝ≥0) + 1))] s := fun n =>
    MeasurableSpace.measurableSet_iInf.1 (MeasurableSpace.measurableSet_iInf.1 hs _) (lt_add_one_div t n)
  have hsm : MeasurableSet s := (nullAugmented 𝓕 P).le _ _ (hu 0)
  choose B hB hBs using fun n => exists_ae_eq_of_measurableSet_nullAugmented (hu n)
  refine Coupling.measurableSet_nullAugmented_of_ae_eq hsm (measurableSet_limsup_of_isRightContinuous hB) ?_
  have hall : ∀ᵐ ω ∂P, ∀ n, (ω ∈ s ↔ ω ∈ B n) := ae_all_iff.2 fun n => eventuallyEqSet_iff.1 (hBs n)
  refine eventuallyEqSet_iff.2 ?_
  filter_upwards [hall] with ω hω
  simp only [mem_iInter, mem_iUnion, exists_prop]
  constructor
  · intro h N
    exact ⟨N, le_rfl, (hω N).1 h⟩
  · intro h
    obtain ⟨n, -, hn⟩ := h 0
    exact (hω n).2 hn

/-- **A martingale stays a martingale for the null augmentation.** -/
theorem martingale_nullAugmented [IsProbabilityMeasure P] {X : ℝ≥0 → Ω → ℝ} (hX : Martingale X 𝓕 P) :
    Martingale X (nullAugmented 𝓕 P) P :=
  ⟨fun t => (hX.1 t).mono (le_nullAugmented 𝓕 P t), fun i j hij =>
    (Lemma71D.condExp_nullAugmented_ae_eq (hX.integrable j) i).trans (hX.2 i j hij)⟩

/-- **A local martingale before `ζ` stays one for the null augmentation.** -/
theorem isLocalMartingaleBefore_nullAugmented [IsProbabilityMeasure P] {ζ : Ω → WithTop ℝ≥0}
    {X : ℝ≥0 → Ω → ℝ} (hX : IsLocalMartingaleBefore 𝓕 P ζ X) :
    IsLocalMartingaleBefore (nullAugmented 𝓕 P) P ζ X := by
  obtain ⟨σ, hσ, hσζ, hae, hm⟩ := hX
  exact ⟨σ, fun n i => le_nullAugmented 𝓕 P i _ (hσ n i), hσζ, hae,
    fun n => martingale_nullAugmented (hm n)⟩

/-- The null augmentation contains the null sets at time zero. -/
theorem measurableSet_nullAugmented_zero {s : Set Ω} (hs : MeasurableSet s) (h0 : P s = 0) :
    MeasurableSet[nullAugmented 𝓕 P 0] s :=
  (le_sup_right : nullSets P ≤ 𝓕 0 ⊔ nullSets P) _ (MeasurableSpace.measurableSet_generateFrom ⟨hs, h0⟩)

end Null

/-- **Lemma 7.25's pocket-word evolution (hPW) from a random driven relative curve and Aux. lemma 122's hypotheses
before its lifetime** (specification pp. 389–397 and p. 414). On a standard Borel probability space with a
right-continuous filtration whose time-zero σ-algebra contains the null sets (the usual conditions, R34): a random
curve `γ ω`, driven for every `ω`, with points of `ℍ` of arbitrarily large modulus (for the erased pocket traversal,
PROVE-STRIPSYS13's `PocketLife.exists_relCurve_mem_H_lt_norm_of_isReversePocket(Inf)`) and filled prefixes adapted to
the filtration at capacity times; random `𝓕₀`-measurable marks with the seeds at `0`, the other left marks negative
and the other right marks positive, ordered in the index; weights with seed weights `r_L, r_R < κ/2 − 4` and all side
partial sums `> −2` (Aux. lemma 125: "All side partial sums are greater than `−2`"); a phase `d_t ∈ 2πχℤ` and Aux.
lemma 122's hypotheses before the lifetime (`HasPhaseMeansBefore`). No assumption on the lifetime: Aux. lemma 125
(`ae_capLife_eq_top_of_hasPhaseMeans`) makes it infinite almost surely. -/
theorem pocketWordEvolution_of_hasPhaseMeans_of_null {κ rL rR : ℝ} (hκ : 4 < κ) (hLd : rL < κ / 2 - 4)
    (hRd : rR < κ / 2 - 4) {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} (hρL : ρL 0 = rL)
    (hρR : ρR 0 = rR) (hsL : ∀ m : Fin (nL + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρL i)
    (hsR : ∀ m : Fin (nR + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρR i)
    {Ω : Type v} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsRightContinuous]
    (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓕 0] s)
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω, IsDrivenCurve (γ ω)) (hunb : ∀ ω (M : ℝ), ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    (hpre : IsPrefixAdapted 𝓕 γ) {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    (hxLm : Measurable[𝓕 0] xL) (hxRm : Measurable[𝓕 0] xR)
    (hseedL : ∀ ω, xL ω 0 = 0) (hseedR : ∀ ω, xR ω 0 = 0)
    (hxLd : ∀ ω (i : Fin nL), xL ω i.succ < 0) (hxRd : ∀ ω (j : Fin nR), 0 < xR ω j.succ)
    (hxLi : ∀ ω, Antitone (xL ω)) (hxRi : ∀ ω, Monotone (xR ω)) {d : ℝ≥0 → Ω → ℝ}
    (hd : ∀ (t : ℝ≥0) ω, 0 < t → (t : WithTop ℝ≥0) < capLife (γ ω) → ∃ n : ℤ, d t ω = n * phaseStep κ)
    (hM : HasPhaseMeansBefore κ ρL ρR P 𝓕 (fun t ω => segDriver (γ ω) t) xL xR d (fun ω => capLife (γ ω))) :
    Lemma725Ref.PocketWordEvolution.{v} κ rL rR := by
  classical
  have hκ0 : 0 < κ := by linarith
  have hL : -2 < rL := hρL ▸ neg_two_lt_zero_of_partialSums hsL
  have hR : -2 < rR := hρR ▸ neg_two_lt_zero_of_partialSums hsR
  have hrL' : ρL 0 < 2 * (κ / 2 - 2) - 2 := by rw [hρL]; linarith
  have hrR' : ρR 0 < 2 * (κ / 2 - 2) - 2 := by rw [hρR]; linarith
  set W : ℝ≥0 → Ω → ℝ := fun t ω => segDriver (γ ω) t with hWdef
  have hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < capLife (γ ω)} := fun ω =>
    (hγ ω).segDriver_spec.2.1
  -- the event of infinite lifetime is a time-zero event of full measure
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
  have hae := ae_capLife_eq_top_of_hasPhaseMeans hκ hsL hsR hrL' hrR' hγ hunb hpre hxLm hxRm hseedL hseedR hxLd
    hxRd hxLi hxRi hd hM
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
  -- the explicit phase-shifted extension of the data before the lifetime
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
  refine pocketWordEvolution_of_drivenCurve (Ω := G) (P := condSub P G) (𝓕 := subFilt 𝓕 G)
    (γ := fun ω : G => γ ω) (xL := fun ω : G => xL ω) (xR := fun ω : G => xR ω) (d := fun t (ω : G) => d t ω)
    hκ hL hLd hR hRd hρL hρR (fun ω => hγ ω) hlife (isPrefixAdapted_sub hpre G)
    (hxLm.comp (Measurable.of_comap_le le_rfl)) (hxRm.comp (Measurable.of_comap_le le_rfl))
    (fun ω => hseedL ω) (fun ω => hseedR ω) (fun ω i => hxLd ω i) (fun ω j => hxRd ω j) (fun ω => hxLi ω)
    (fun ω => hxRi ω) (fun t ω ht => hd t ω ht (by rw [hlife ω]; exact WithTop.coe_lt_top t)) ?_ ?_
  · intro U' hU' z hz
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
  · intro U' hU' ω z T' h0 hzK
    obtain ⟨U, hU, hUU⟩ := key U' hU'
    have h := (hM U hU).2 ω z T' h0 (by simp only [hlife ω]; exact WithTop.coe_lt_top _) hzK
    rw [hUU ω] at h
    exact h

/-- **Lemma 7.25's pocket-word evolution (hPW) from a random driven relative curve and Aux. lemma 122's hypotheses
before its lifetime**, in any right-continuous filtration (`pocketWordEvolution_of_hasPhaseMeans_of_null` applied to
the null augmentation, which is right-continuous, contains the null sets, and keeps the adaptedness and the local
martingales). See `pocketWordEvolution_of_hasPhaseMeans_of_null` for the hypotheses. -/
theorem pocketWordEvolution_of_hasPhaseMeans {κ rL rR : ℝ} (hκ : 4 < κ) (hLd : rL < κ / 2 - 4)
    (hRd : rR < κ / 2 - 4) {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} (hρL : ρL 0 = rL)
    (hρR : ρR 0 = rR) (hsL : ∀ m : Fin (nL + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρL i)
    (hsR : ∀ m : Fin (nR + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρR i)
    {Ω : Type v} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsRightContinuous]
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω, IsDrivenCurve (γ ω)) (hunb : ∀ ω (M : ℝ), ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    (hpre : IsPrefixAdapted 𝓕 γ) {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    (hxLm : Measurable[𝓕 0] xL) (hxRm : Measurable[𝓕 0] xR)
    (hseedL : ∀ ω, xL ω 0 = 0) (hseedR : ∀ ω, xR ω 0 = 0)
    (hxLd : ∀ ω (i : Fin nL), xL ω i.succ < 0) (hxRd : ∀ ω (j : Fin nR), 0 < xR ω j.succ)
    (hxLi : ∀ ω, Antitone (xL ω)) (hxRi : ∀ ω, Monotone (xR ω)) {d : ℝ≥0 → Ω → ℝ}
    (hd : ∀ (t : ℝ≥0) ω, 0 < t → (t : WithTop ℝ≥0) < capLife (γ ω) → ∃ n : ℤ, d t ω = n * phaseStep κ)
    (hM : HasPhaseMeansBefore κ ρL ρR P 𝓕 (fun t ω => segDriver (γ ω) t) xL xR d (fun ω => capLife (γ ω))) :
    Lemma725Ref.PocketWordEvolution.{v} κ rL rR := by
  have hRC : (Ito.nullAugmented 𝓕 P).IsRightContinuous := isRightContinuous_nullAugmented
  exact pocketWordEvolution_of_hasPhaseMeans_of_null (𝓕 := Ito.nullAugmented 𝓕 P) hκ hLd hRd hρL hρR hsL hsR
    (fun s hs h0 => measurableSet_nullAugmented_zero hs h0) hγ hunb
    (fun r n k => Ito.le_nullAugmented 𝓕 P r _ (hpre r n k))
    (hxLm.mono (Ito.le_nullAugmented 𝓕 P 0) le_rfl) (hxRm.mono (Ito.le_nullAugmented 𝓕 P 0) le_rfl) hseedL
    hseedR hxLd hxRd hxLi hxRi hd
    (fun U hU => ⟨fun z hz => isLocalMartingaleBefore_nullAugmented ((hM U hU).1 z hz), (hM U hU).2⟩)

end InteractingSLE.Sec7.PocketWordLife
