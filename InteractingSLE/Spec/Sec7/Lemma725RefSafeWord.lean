/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma725RefSafeTransfer
import InteractingSLE.Spec.Sec7.PocketWordLife
import InteractingSLE.Spec.Sec7.PocketMeas

/-!
# Lemma 7.25's pocket with its field: (E), (S), (L) and the determination on one probability space

Packet PROVE-LEMMA725REF3. Specification §7.4: Aux. lemma 125 (`source/spec/p385-432.md` L197–L250, pp. 395–398) and
Lemma 7.25's proof (L489–L515, pp. 413–414). The landed chain (`PocketAdapt.pocketWordEvolution_of_charFun_prefixFilt`
and below) derives the pocket evolution (E) from the coupling clause of the pocket field in the relative history
filtration, on successive restrictions of the probability space, and hides the field. Here the same construction is
carried out with the field kept, which gives the named input `Lemma725RefK2.PocketWordFieldStatement` of `href725`:

* **(S)** `hasSafeLaw_of_isCouplingCharFun`: K2's protected-kernel law in the relative history filtration is the
  conditional-law clause at constant stopping times ("The canonical law survives the exterior reveal", p. 396: the
  active Gaussian kernel in the relative filtration initially enlarged by `ℰ`);
* `adaptedBefore_subtype`, `adaptedBefore_subtype_top`: adaptedness on restrictions;
* **`pocketWordFieldStatement_of_charFun`**: from a random driven relative curve with the coupling clause of a field `X`
  in the usual augmentation of its relative history filtration (the input of the landed chain), K2's (L) for `X` in that
  filtration, and the determination of the killed relative history by `(E, X)` for an initial record `E`, the pocket
  word field statement holds. The restriction to infinite relative lifetime and to Aux. lemma 122's event are those of
  `PocketWordLife.pocketWordEvolution_of_hasPhaseMeans_of_null` and `PocketWordRef.pocketWordEvolution_of_aux122`;
  (S), (L) and the determination are transported along them (`Lemma725RefSafeTransfer`), and the lifetime of (E) is `∞`
  (`thresholdTime_eq_top_of_partialSums`: all side partial sums exceed `−2`).

Conditional helpers; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or a result taking them as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.Lemma725RefSafe

open Restart.DomainMarkov Restart.DomainMarkov.K2 Aux122Disint PhaseSel PocketMartLife PocketCoupling LocalSets
  Coupling MartChar PocketTraversal Lemma71C PocketAdapt PocketWordLife LawUnique

/-! ### (S) from the conditional-law clause -/

section Safe

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} {nL nR : ℕ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {X : Ω → DistOn upperHalfPlaneOpens}

/-- **(S) from the conditional-law clause**: if `X` satisfies the conditional-law clause of the optional hull
specification (`IsCouplingCharFun`) in a filtration `𝓕` and the lifetime is almost surely infinite, then K2's (S) holds
for every filtration `𝓗 ≤ 𝓕` (the clause at the constant stopping times). -/
theorem hasSafeLaw_of_isCouplingCharFun {𝓕 𝓗 : Filtration ℝ≥0 mΩ} (h𝓗 : ∀ q, 𝓗 q ≤ 𝓕 q) (hX : Measurable X)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hcf : MartMeans.IsCouplingCharFun κ ρL ρR P 𝓕 W VL VR ζ X) (F : Set Ω) :
    HasSafeLaw κ ρL ρR P 𝓗 F ζ W VL VR X := by
  refine Mean.hasSafeLaw_of_ae_condExp hX (fun _ q => 𝓕 q) (fun _ q => h𝓗 q) (fun _ q => 𝓕.le q) ?_
  intro ψ q D _ hDa
  have hτ := isStoppingTime_const 𝓕 q
  have hlt : ∀ᵐ ω ∂P, (((fun _ : Ω => (q : WithTop ℝ≥0)) ω : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := by
    filter_upwards [hζ] with ω hω
    rw [hω]
    exact WithTop.coe_lt_top q
  have hmain := hcf (fun _ => (q : WithTop ℝ≥0)) hτ hlt (fun ω => bheProc κ ρL ρR W VL VR ω q)
    (fun ω => by simp only [WithTop.untopD_coe]; exact isBoundedHarmonicExtension_bheProc ω q) ψ
  rw [IsStoppingTime.measurableSpace_const] at hmain
  simp only [WithTop.untopD_coe] at hmain
  filter_upwards [hmain, hDa] with ω h1 h2 hωD
  rw [h1 (h2 hωD).2.2]
  simp only [cfAt]
  congr 1
  push_cast
  ring

end Safe

/-! ### Adaptedness on restrictions -/

section Adapted

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓗 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞} {Y : ℝ≥0 → Ω → ℝ}

/-- Adaptedness before the lifetime restricts to a subevent. -/
theorem adaptedBefore_subtype (h : AdaptedBefore 𝓗 ζ Y) (S : Set Ω) :
    AdaptedBefore (subFilt 𝓗 S) (fun ω : S => ζ ω) fun t (ω : S) => Y t ω := fun t A hA =>
  ⟨_, h t A hA, rfl⟩

/-- On a subevent where the lifetime is infinite, adaptedness before the lifetime is adaptedness. -/
theorem adaptedBefore_subtype_top (h : AdaptedBefore 𝓗 ζ Y) {S : Set Ω} (hS : ∀ ω ∈ S, ζ ω = ⊤) :
    AdaptedBefore (subFilt 𝓗 S) (fun _ : S => ⊤) fun t (ω : S) => Y t ω := by
  intro t A hA
  refine ⟨_, h t A hA, ?_⟩
  ext ω
  simp only [mem_preimage, mem_ofPred_eq, hS ω ω.2, ENNReal.coe_lt_top, true_and]

end Adapted

/-! ### The pocket word field statement from the coupling clause -/

section Word

universe u

/-- **The pocket evolution with its field on one restricted space** (the core of Lemma 7.25's pocket, Aux. lemmas
122 and 125, pp. 389–398). On a standard Borel probability space with initial information `𝓔` (the walls): a random
curve `γ`, driven for every `ω`, with points of `ℍ` of arbitrarily large modulus and measurable at fixed own times;
`𝓔`-measurable marks (seeds at `0`, the other left marks negative and the other right marks positive, ordered); weights
with seed weights `r_L, r_R < κ − 6` (Aux. lemma 122's range `(−2, 2A − 2)`, `A = κ/2 − 2`) and all side partial sums
`> −2`; and a measurable field `X` (the pocket field in the pocket chart) with the conditional-law clause of the word in
the usual augmentation of the relative history filtration (the input of the landed chain
`PocketAdapt.pocketWordEvolution_of_charFun_prefixFilt`) and K2's member identities (L) in the relative history
filtration. Then there are a standard Borel probability space `Ω₃` and a measurable map `π : Ω₃ → Ω` transporting
`P`-null sets to null sets, on which the relative lifetime is infinite, the driver, its geometric force coordinates and
a Brownian motion form an integrated evolution of the word `(x^L ∘ π, x^R ∘ π)` with lifetime `∞` and initial
information `π⁻¹𝓔` (Aux. lemma 122), and `X ∘ π` has K2's (S) and (L) in a filtration `𝓗'` with `π⁻¹𝓔 ≤ 𝓗'_0` in which
the driver and the coordinates are adapted. (E) is produced as in the landed chain (the restrictions to infinite
relative lifetime and to Aux. lemma 122's event of full measure), (S) is the clause at constant times
(`hasSafeLaw_of_isCouplingCharFun`), and (S), (L) are carried along the restrictions. -/
theorem exists_pocketField_core {κ rL rR : ℝ} (hκ : 4 < κ) (hLd : rL < κ - 6)
    (hRd : rR < κ - 6) {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} (hρL : ρL 0 = rL)
    (hρR : ρR 0 = rR) (hsL : ∀ m : Fin (nL + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρL i)
    (hsR : ∀ m : Fin (nR + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρR i)
    {Ω : Type u} {𝓔 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (h𝓔 : 𝓔 ≤ mΩ) {γ : Ω → ℝ → ℂ} (hγ : ∀ ω, IsDrivenCurve (γ ω))
    (hγm : ∀ u, 0 ≤ u → Measurable[mΩ] fun ω => γ ω u)
    (hunb : ∀ ω (M : ℝ), ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} (hxLm : Measurable[𝓔] xL) (hxRm : Measurable[𝓔] xR)
    (hseedL : ∀ ω, xL ω 0 = 0) (hseedR : ∀ ω, xR ω 0 = 0)
    (hxLd : ∀ ω (i : Fin nL), xL ω i.succ < 0) (hxRd : ∀ ω (j : Fin nR), 0 < xR ω j.succ)
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
  have hL : -2 < rL := hρL ▸ neg_two_lt_zero_of_partialSums hsL
  have hR : -2 < rR := hρR ▸ neg_two_lt_zero_of_partialSums hsR
  have hrL' : ρL 0 < 2 * (κ / 2 - 2) - 2 := by rw [hρL]; linarith
  have hrR' : ρR 0 < 2 * (κ / 2 - 2) - 2 := by rw [hρR]; linarith
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
  have hd : ∀ (t : ℝ≥0) ω, 0 < t → (t : WithTop ℝ≥0) < capLife (γ ω) → ∃ n : ℤ, d t ω = n * phaseStep κ :=
    fun _ _ _ _ => ⟨0, by simp [hd_def]⟩
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
  have hae := ae_capLife_eq_top_of_hasPhaseMeans hκ hsL hsR hrL' hrR' hγ hunb hpre hxLm' hxRm' hseedL hseedR hxLd
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
  have hcont₂ : ∀ U : G → ℝ≥0 → ℂ → ℝ, (∀ ω t, IsBoundedHarmonicExtension
      (phaseData κ ρL ρR (fun i => geomLW W₂ xL₂ i t ω - W₂ t ω) (fun j => geomRW W₂ xR₂ j t ω - W₂ t ω) (d t ω))
      (forceJumpSet (fun i => geomLW W₂ xL₂ i t ω - W₂ t ω) (fun j => geomRW W₂ xR₂ j t ω - W₂ t ω)) (U ω t)) →
      ∀ ω (z : ℂ) (T' : ℝ), 0 ≤ T' → z ∈ H \ QuantumZipper.fwdHull (wpath W₂ ω) T' →
        ContinuousOn (fun t : ℝ => couplingMean κ (wpath W₂ ω) t (U ω t.toNNReal) z) (Icc 0 T') := by
    intro U' hU' ω z T' h0 hzK
    obtain ⟨U, hU, hUU⟩ := key U' hU'
    have h := (hM U hU).2 ω z T' h0 (by simp only [hlife ω]; exact WithTop.coe_lt_top _) hzK
    rw [hUU ω] at h
    exact h
  -- Aux. lemma 122 on `G` (the last step of `pocketWordEvolution_of_geom`)
  obtain ⟨A', hA'0, hP1, -, B, hE⟩ := PocketWord.aux122_isRandomWordEvolution (P := condSub P G)
    (𝓕 := subFilt 𝓕 G) hκ (hρL ▸ hL) hrL' (hρR ▸ hR) hrR' (VL := geomLW W₂ xL₂) (VR := geomRW W₂ xR₂)
    (fun ω => by rw [geomLW_zero hWc₂ hW0₂ (le_of_eq (hseedL ω))]; exact hseedL ω)
    (fun ω => by rw [geomRW_zero hWc₂ hW0₂ (le_of_eq (hseedR ω).symm)]; exact hseedR ω)
    (fun ω i => by rw [geomLW_zero hWc₂ hW0₂ (hxLd ω i).le]; exact hxLd ω i)
    (fun ω j => by rw [geomRW_zero hWc₂ hW0₂ (hxRd ω j).le]; exact hxRd ω j)
    hW0₂ hWc₂ hWa₂ (stronglyAdapted_geomLW hWa₂ hWc₂ hxLm₂) (stronglyAdapted_geomRW hWa₂ hWc₂ hxRm₂)
    (fun ω t i => geomLW_le hWc₂ xL₂ ω t i) (fun ω t j => le_geomRW hWc₂ xR₂ ω t j)
    (isForcePath_geomLW hWc₂ xL₂) (isForcePath_geomRW hWc₂ xR₂) (antitone_geomLW hWc₂ xL₂)
    (monotone_geomRW hWc₂ xR₂) (fun ω t => antitone_index_geomLW hWc₂ (hxLi ω) t)
    (fun ω t => monotone_index_geomRW hWc₂ (hxRi ω) t) (fun ω i j s t hst => geomLW_merge hWc₂ xL₂ ω i j s t hst)
    (fun ω i j s t hst => geomRW_merge hWc₂ xR₂ ω i j s t hst)
    (fun ω t ht i j => geom_sep hWc₂ xL₂ xR₂ ω t ht i j) (fun _ _ _ => ⟨0, by simp [hd_def]⟩) hmart₂ hcont₂
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

/-- **Lemma 7.25's pocket with its field from the coupling clause** (Aux. lemma 125 and Lemma 7.25's proof, pp.
395–398, 413–414): the core (`exists_pocketField_core`) with the determination of the killed relative history by
`(E, X)` for an `𝓔`-measurable record `E` with values in a standard Borel space ("the already established global field
determination, followed by the measurable selected-pocket erasure", p. 398) gives `PocketWordFieldStatement`. -/
theorem pocketWordFieldStatement_of_charFun {κ rL rR : ℝ} (hκ : 4 < κ) (hLd : rL < κ / 2 - 4)
    (hRd : rR < κ / 2 - 4) {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} (hρL : ρL 0 = rL)
    (hρR : ρR 0 = rR) (hsL : ∀ m : Fin (nL + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρL i)
    (hsR : ∀ m : Fin (nR + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρR i)
    {Ω : Type u} {𝓔 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (h𝓔 : 𝓔 ≤ mΩ) {γ : Ω → ℝ → ℂ} (hγ : ∀ ω, IsDrivenCurve (γ ω))
    (hγm : ∀ u, 0 ≤ u → Measurable[mΩ] fun ω => γ ω u)
    (hunb : ∀ ω (M : ℝ), ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} (hxLm : Measurable[𝓔] xL) (hxRm : Measurable[𝓔] xR)
    (hseedL : ∀ ω, xL ω 0 = 0) (hseedR : ∀ ω, xR ω 0 = 0)
    (hxLd : ∀ ω (i : Fin nL), xL ω i.succ < 0) (hxRd : ∀ ω (j : Fin nR), 0 < xR ω j.succ)
    (hxLi : ∀ ω, Antitone (xL ω)) (hxRi : ∀ ω, Monotone (xR ω)) {X : Ω → DistOn upperHalfPlaneOpens}
    (hXm : Measurable X) (hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => X ω φ) P)
    (hcf : MartMeans.IsCouplingCharFun κ ρL ρR P
      (usualAugmentation (prefixFilt 𝓔 h𝓔 γ fun r n k => PocketMeas.measurableSet_prefixEvent hγ hγm r n k) P)
      (fun t ω => segDriver (γ ω) t) (geomLW (fun t ω => segDriver (γ ω) t) xL)
      (geomRW (fun t ω => segDriver (γ ω) t) xR) (fun ω => capLife (γ ω)) X)
    (hmem : HasSafeMembers P (prefixFilt 𝓔 h𝓔 γ fun r n k => PocketMeas.measurableSet_prefixEvent hγ hγm r n k)
      univ (fun ω => capLife (γ ω)) (fun t ω => segDriver (γ ω) t) X)
    {ε : Type u} [MeasurableSpace ε] [StandardBorelSpace ε] {E : Ω → ε} (hEm : Measurable[𝓔] E)
    {g : ε × DistOn upperHalfPlaneOpens → HistorySpace (nL + 1) (nR + 1)} (hg : Measurable g)
    (hdet : ∀ᵐ ω ∂P, killedHistory (fun t ω => segDriver (γ ω) t) (geomLW (fun t ω => segDriver (γ ω) t) xL)
      (geomRW (fun t ω => segDriver (γ ω) t) xR) (fun ω => capLife (γ ω)) ω = g (E ω, X ω)) :
    Lemma725RefK2.PocketWordFieldStatement.{u} κ rL rR := by
  obtain ⟨Ω₃, m₃, hSB, P₃, hP₃, π, B, 𝓗, 𝓗', hπ, hae, hlife, hE, h𝓔', hWa, hVLa, hVRa, hS, hL⟩ :=
    exists_pocketField_core hκ (by linarith) (by linarith) hρL hρR hsL hsR h𝓔 hγ hγm hunb hxLm hxRm hseedL hseedR
      hxLd hxRd hxLi hxRi hXm hint hcf hmem
  have hxLnp : ∀ ω i, xL ω i ≤ 0 := fun ω i => (hxLi ω (Fin.zero_le i)).trans_eq (hseedL ω)
  have hxRnn : ∀ ω j, 0 ≤ xR ω j := fun ω j => (hseedR ω).symm.trans_le (hxRi ω (Fin.zero_le j))
  refine ⟨nL, nR, ρL, ρR, hρL, hρR, Ω₃, MeasurableSpace.comap π 𝓔, m₃, hSB, P₃, hP₃, univ,
    fun ω => xL (π ω), fun ω => xR (π ω), by rw [measure_univ]; exact one_ne_zero, fun ω _ => ?_, ε,
    inferInstance, inferInstance, fun ω => E (π ω), fun ω => X (π ω), fun t ω => segDriver (γ (π ω)) t,
    fun i t ω => geomLW (fun t ω => segDriver (γ ω) t) xL i t (π ω),
    fun j t ω => geomRW (fun t ω => segDriver (γ ω) t) xR j t (π ω), B, fun _ => ⊤, 𝓗, 𝓗', hE,
    ae_of_all _ fun ω _ T _ => ⟨capTrace (γ (π ω)), (hγ _).isGeneratingTrace_of_capLife_eq_top (hlife ω) T⟩,
    fun s hs => ⟨_, hEm hs, rfl⟩, hXm.comp hπ, h𝓔', hWa, hVLa, hVRa, hS, hL, g, hg, ?_⟩
  · refine ⟨⟨hxLi _, hxLnp _, hxRi _, hxRnn _⟩, hseedL _, hseedR _, fun i hi => ?_, fun j hj => ?_⟩
    · obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.2 hi
      exact hxLd _ i'
    · obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.2 hj
      exact hxRd _ j'
  · filter_upwards [hae _ hdet] with ω hω _
    have e : killedHistory (fun t ω => segDriver (γ (π ω)) t)
        (fun i t ω => geomLW (fun t ω => segDriver (γ ω) t) xL i t (π ω))
        (fun j t ω => geomRW (fun t ω => segDriver (γ ω) t) xR j t (π ω)) (fun _ => ⊤) ω =
        killedHistory (fun t ω => segDriver (γ ω) t) (geomLW (fun t ω => segDriver (γ ω) t) xL)
          (geomRW (fun t ω => segDriver (γ ω) t) xR) (fun ω => capLife (γ ω)) (π ω) := by
      simp only [killedHistory, hlife ω]
    rw [e]
    exact hω

/-- **The `P`-side pocket of a two-seed word with its field** (`Lemma725RefK2.PocketTwoSeedPSideStatement`, the
named input of `hR7`) from the core, for the constant two-seed word `SLE_κ(r_L; r_R)` with seed weights in Aux. lemma
122's range `(−2, κ − 6)`: the pathwise property `Good` of the relative driver with infinite lifetime, almost surely,
and the determination of the killed relative history by `(E, X)` for an `𝓔`-measurable record `E`. -/
theorem pocketTwoSeedPSideStatement_of_charFun {κ rL rR : ℝ} (hκ : 4 < κ) (hL : -2 < rL) (hLd : rL < κ - 6)
    (hR : -2 < rR) (hRd : rR < κ - 6) {Good : (ℝ≥0 → ℝ) → ℝ≥0∞ → Prop}
    {Ω : Type u} {𝓔 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (h𝓔 : 𝓔 ≤ mΩ) {γ : Ω → ℝ → ℂ} (hγ : ∀ ω, IsDrivenCurve (γ ω))
    (hγm : ∀ u, 0 ≤ u → Measurable[mΩ] fun ω => γ ω u)
    (hunb : ∀ ω (M : ℝ), ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖) {X : Ω → DistOn upperHalfPlaneOpens}
    (hXm : Measurable X) (hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => X ω φ) P)
    (hcf : MartMeans.IsCouplingCharFun κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P
      (usualAugmentation (prefixFilt 𝓔 h𝓔 γ fun r n k => PocketMeas.measurableSet_prefixEvent hγ hγm r n k) P)
      (fun t ω => segDriver (γ ω) t) (geomLW (fun t ω => segDriver (γ ω) t) fun _ => LP.twoSeedXL)
      (geomRW (fun t ω => segDriver (γ ω) t) fun _ => LP.twoSeedXR) (fun ω => capLife (γ ω)) X)
    (hmem : HasSafeMembers P (prefixFilt 𝓔 h𝓔 γ fun r n k => PocketMeas.measurableSet_prefixEvent hγ hγm r n k)
      univ (fun ω => capLife (γ ω)) (fun t ω => segDriver (γ ω) t) X)
    (hGood : ∀ᵐ ω ∂P, capLife (γ ω) = ⊤ → Good (fun t => segDriver (γ ω) t) ⊤)
    {ε : Type u} [MeasurableSpace ε] {E : Ω → ε} (hEm : Measurable[𝓔] E)
    {g : ε × DistOn upperHalfPlaneOpens → HistorySpace 1 1} (hg : Measurable g)
    (hdet : ∀ᵐ ω ∂P, killedHistory (fun t ω => segDriver (γ ω) t)
      (geomLW (fun t ω => segDriver (γ ω) t) fun _ => LP.twoSeedXL)
      (geomRW (fun t ω => segDriver (γ ω) t) fun _ => LP.twoSeedXR) (fun ω => capLife (γ ω)) ω = g (E ω, X ω)) :
    Lemma725RefK2.PocketTwoSeedPSideStatement.{u} κ rL rR Good := by
  have hsL : ∀ m : Fin 1, -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), (fun _ : Fin 1 => rL) i := by
    intro m
    rw [Subsingleton.elim m 0, Finset.filter_true_of_mem fun i _ => (Subsingleton.elim i 0).le]
    simpa using hL
  have hsR : ∀ m : Fin 1, -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), (fun _ : Fin 1 => rR) i := by
    intro m
    rw [Subsingleton.elim m 0, Finset.filter_true_of_mem fun i _ => (Subsingleton.elim i 0).le]
    simpa using hR
  obtain ⟨Ω₃, m₃, hSB, P₃, hP₃, π, B, 𝓗, 𝓗', hπ, hae, hlife, hE, h𝓔', hWa, hVLa, hVRa, hS, hL⟩ :=
    exists_pocketField_core (nL := 0) (nR := 0) hκ hLd hRd rfl rfl hsL hsR h𝓔 hγ hγm hunb
      (measurable_const (a := LP.twoSeedXL)) (measurable_const (a := LP.twoSeedXR)) (fun _ => rfl) (fun _ => rfl)
      (fun _ i => i.elim0) (fun _ j => j.elim0) (fun _ => fun i j _ => le_rfl) (fun _ => fun i j _ => le_rfl) hXm
      hint hcf hmem
  refine ⟨Ω₃, MeasurableSpace.comap π 𝓔, m₃, hSB, P₃, hP₃, univ, ε, inferInstance, fun ω => E (π ω),
    fun ω => X (π ω), fun t ω => segDriver (γ (π ω)) t,
    fun i t ω => geomLW (fun t ω => segDriver (γ ω) t) (fun _ => LP.twoSeedXL) i t (π ω),
    fun j t ω => geomRW (fun t ω => segDriver (γ ω) t) (fun _ => LP.twoSeedXR) j t (π ω), B, fun _ => ⊤, 𝓗, 𝓗',
    hE, by rw [measure_univ]; exact one_ne_zero, fun s hs => ⟨_, hEm hs, rfl⟩, hXm.comp hπ, h𝓔', hWa, hVLa, hVRa,
    hS, hL, ?_, g, hg, ?_⟩
  · filter_upwards [hae _ hGood] with ω hω _
    exact hω (hlife ω)
  · filter_upwards [hae _ hdet] with ω hω _
    have e : killedHistory (fun t ω => segDriver (γ (π ω)) t)
        (fun i t ω => geomLW (fun t ω => segDriver (γ ω) t) (fun _ => LP.twoSeedXL) i t (π ω))
        (fun j t ω => geomRW (fun t ω => segDriver (γ ω) t) (fun _ => LP.twoSeedXR) j t (π ω)) (fun _ => ⊤) ω =
        killedHistory (fun t ω => segDriver (γ ω) t) (geomLW (fun t ω => segDriver (γ ω) t) fun _ => LP.twoSeedXL)
          (geomRW (fun t ω => segDriver (γ ω) t) fun _ => LP.twoSeedXR) (fun ω => capLife (γ ω)) (π ω) := by
      simp only [killedHistory, hlife ω]
    rw [e]
    exact hω

end Word

end InteractingSLE.Sec7.Lemma725RefSafe
