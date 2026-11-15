/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.Assembly3Entr

/-!
# Aux. lemma 4, III: the two-seed cover with pathwise identities

Packet PROVE-T14-DS3. The landed `Sec2.Assembly3.exists_twoSeed_cover` (PROVE-SEC2-PATCH4, proof of Theorem 2.2's
uniqueness for the admissible entrances) constructs, under the Girsanov measure `Q` that removes the weights of the
non-seed marks up to the localization time `T = entT` (first time a non-seed mark is within `δ` of the driver, capped
at `1`), a two-seed evolution `G` of the merged seeds; it records that the *code* of `G` determines the observation up
to `T`. The restart of Lemma DS3 needs the pathwise content: `exists_twoSeed_cover_path` is the same construction
(the proof is the landed one) with the conclusion that, `Q`-almost surely, `G` has infinite lifetime, `T < ζ`, the
evolution's paths satisfy the integrated equations with the changed weights before `T` (the non-seed marks follow the
Loewner flow of the driver), and `G` *equals* the driver and the two seeds on `[0, T]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp12

namespace Aux4

open Sec2 Sec2.Assembly Sec2.Assembly2 Sec2.Assembly3 Girsanov

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ}

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓖 : Filtration ℝ≥0 mΩ} [𝓖.IsRightContinuous] {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The two-seed cover, pathwise.** -/
theorem exists_twoSeed_cover_path (ha : 0 < a) (hF : IsOrderedForceWord xL xR) {δ : ℝ} (hδ : 0 < δ)
    (hδL : ∀ i, xL i ≠ 0 → δ < -xL i) (hδR : ∀ j, xR j ≠ 0 → δ < xR j)
    {pL : Fin nL} {pR : Fin nR} (hpL : xL pL = 0) (hpR : xR pR = 0)
    (hthr : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR)
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓖 W VL VR B ζ)
    (hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hVLc : ∀ i ω, ContinuousOn (VL i · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hVRc : ∀ j ω, ContinuousOn (VR j · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hBc : ∀ ω, Continuous (B · ω)) (hW0 : ∀ ω, W 0 ω = 0) (hVL0 : ∀ i ω, VL i 0 ω = xL i)
    (hVR0 : ∀ j ω, VR j 0 ω = xR j) (hζ0 : ∀ ω, 0 < ζ ω)
    (hnull : ∀ N : Set Ω, MeasurableSet N → P N = 0 → ∀ t, MeasurableSet[𝓖 t] N) :
    ∃ (Gw : ℝ≥0 → Ω → ℝ) (Gl Gr : Fin 1 → ℝ≥0 → Ω → ℝ) (ζG : Ω → ℝ≥0∞),
      IsProbabilityMeasure (girsanovMeasure P 𝓖 B (weightDrift a δ ρL (seedW xL ρL) ρR
        (seedW xR ρR) (entT δ xL xR ζ W VL VR) ζ W VL VR) (1 + 1)) ∧
      IsIntegratedSLEEvolution a (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0)
        (fun _ => seedSum xL ρL) (fun _ => seedSum xR ρR)
        (girsanovMeasure P 𝓖 B (weightDrift a δ ρL (seedW xL ρL) ρR (seedW xR ρR)
          (entT δ xL xR ζ W VL VR) ζ W VL VR) (1 + 1)) 𝓖 Gw Gl Gr
        (girsanovProcess B (weightDrift a δ ρL (seedW xL ρL) ρR (seedW xR ρR)
          (entT δ xL xR ζ W VL VR) ζ W VL VR)) ζG ∧
      (∀ᵐ ω ∂(girsanovMeasure P 𝓖 B (weightDrift a δ ρL (seedW xL ρL) ρR (seedW xR ρR)
          (entT δ xL xR ζ W VL VR) ζ W VL VR) (1 + 1)),
        ζG ω = ⊤ ∧ entT δ xL xR ζ W VL VR ω < ζ ω ∧
        IsIntegratedSLEPath a xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) (ζ ω) ∧
        IsIntegratedSLEPath a (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0) (fun _ => seedSum xL ρL)
          (fun _ => seedSum xR ρR) (Gw · ω) (fun i t => Gl i t ω) (fun j t => Gr j t ω)
          (girsanovProcess B (weightDrift a δ ρL (seedW xL ρL) ρR (seedW xR ρR)
            (entT δ xL xR ζ W VL VR) ζ W VL VR) · ω) (ζG ω) ∧
        IsSLEPathUpTo a xL xR (seedW xL ρL) (seedW xR ρR) (W · ω) (fun i t => VL i t ω)
          (fun j t => VR j t ω) (girsanovProcess B (weightDrift a δ ρL (seedW xL ρL) ρR (seedW xR ρR)
            (entT δ xL xR ζ W VL VR) ζ W VL VR) · ω) (entT δ xL xR ζ W VL VR ω) ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ entT δ xL xR ζ W VL VR ω →
          Gw t ω = W t ω ∧ Gl 0 t ω = VL pL t ω ∧ Gr 0 t ω = VR pR t ω) := by
  classical
  have hne : Nonempty (Fin nL ⊕ Fin nR) := ⟨Sum.inl pL⟩
  obtain ⟨hsL, hsR⟩ := (not_thr_iff_seedSum xL xR ρL ρR).1 hthr
  set T := entT δ xL xR ζ W VL VR with hTdef
  set θ := weightDrift a δ ρL (seedW xL ρL) ρR (seedW xR ρR) T ζ W VL VR with hθdef
  set Q := girsanovMeasure P 𝓖 B θ (1 + 1) with hQdef
  set Bh := girsanovProcess B θ with hBhdef
  -- the localization time
  have hTle : ∀ s : ℝ≥0, MeasurableSet[𝓖 s] {ω | T ω ≤ s} :=
    measurableSet_entT_le hδ.le hE.2.1 hE.2.2.1 hE.2.2.2.1 hWc hVLc hVRc
  have hTζ : ∀ ω, T ω ≤ ζ ω := entT_le_lifetime hδ.le
  have hT1 : ∀ ω, T ω ≤ ((1 : ℝ≥0) : ℝ≥0∞) := fun ω => by
    rw [ENNReal.coe_one]; exact entT_le_one ω
  have h0gap : ∀ ω k, δ < gapFam δ xL xR W VL VR k 0 ω := by
    rintro ω (i | j)
    · simp only [gapFam, Sum.elim_inl]
      split_ifs with hi
      · linarith
      · rw [hW0, hVL0]; linarith [hδL i hi]
    · simp only [gapFam, Sum.elim_inr]
      split_ifs with hj
      · linarith
      · rw [hW0, hVR0]; linarith [hδR j hj]
  have hT0 : ∀ ω, 0 < T ω := fun ω =>
    entT_pos hδ.le (hWc ω) (fun i => hVLc i ω) (fun j => hVRc j ω) (hζ0 ω) (h0gap ω)
  -- Girsanov
  have hgap : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < T ω →
      (∀ i, seedW xL ρL i ≠ ρL i → δ ≤ |W t ω - VL i t ω|) ∧
        ∀ j, seedW xR ρR j ≠ ρR j → δ ≤ |W t ω - VR j t ω| := ae_of_all _ fun ω t ht => by
    have hk := (lt_of_lt_entT hδ.le ht).2
    refine ⟨fun i hi => ?_, fun j hj => ?_⟩
    · have hxi : xL i ≠ 0 := fun h => hi (seedW_of_eq h)
      have := hk (Sum.inl i)
      simp only [gapFam, Sum.elim_inl, hxi, ↓reduceIte] at this
      exact this.le.trans (le_abs_self _)
    · have hxj : xR j ≠ 0 := fun h => hj (seedW_of_eq h)
      have := hk (Sum.inr j)
      simp only [gapFam, Sum.elim_inr, hxj, ↓reduceIte] at this
      rw [abs_sub_comm]
      exact this.le.trans (le_abs_self _)
  have hEu := hE.isSLEEvolutionUpTo
  obtain ⟨hQ, hEQ⟩ := hEu.girsanov_changeWeights ha (seedW xL ρL) (seedW xR ρR) hTle hTζ hT1 hδ
    hgap
  have hQp : IsProbabilityMeasure Q := hQ.isProb
  have hQP : Q ≪ P := hQ.ac
  obtain ⟨hθp, hθb, -⟩ := hEu.weightDrift_props (seedW xL ρL) (seedW xR ρR) hTle hTζ hδ
  have hBhc : ∀ ω, Continuous (Bh · ω) := fun ω =>
    (hBc ω).add (Girsanov.continuous_drift hθp hθb ω)
  -- `T < ζ` almost surely
  have hTltP : ∀ᵐ ω ∂P, T ω < ζ ω := ae_entT_lt_lifetime ha hδ hpL hthr hE hpR
  -- the stopped processes
  set Tn : Ω → ℝ≥0 := fun ω => (T ω).toNNReal with hTndef
  have hTn : ∀ ω, (Tn ω : ℝ≥0∞) = T ω := fun ω => ENNReal.coe_toNNReal (entT_ne_top ω)
  have hTn0 : ∀ ω, 0 < Tn ω := fun ω => by
    have : (0 : ℝ≥0∞) < Tn ω := by rw [hTn]; exact hT0 ω
    exact_mod_cast this
  have hTst : IsStoppingTime 𝓖 fun ω => (Tn ω : WithTop ℝ≥0) := fun u => by
    have e : {ω | (Tn ω : WithTop ℝ≥0) ≤ u} = {ω | T ω ≤ u} := by
      ext ω
      simp only [mem_ofPred_eq]
      rw [← hTn ω]
      exact WithTop.coe_le_coe.trans ENNReal.coe_le_coe.symm
    rw [e]
    exact hTle u
  have hTm : Measurable T := by
    refine measurable_of_Iic fun x => ?_
    induction x using ENNReal.recTopCoe with
    | top => simp
    | coe s => exact 𝓖.le s _ (hTle s)
  have hζm : Measurable ζ := measurable_lifetime hE.2.1
  set N₂ : Set Ω := {ω | ¬ (T ω < ζ ω)} with hN₂
  have hN₂m : MeasurableSet N₂ := (measurableSet_lt hTm hζm).compl
  have hN₂0 : P N₂ = 0 := ae_iff.1 hTltP
  have hN₂Q : ∀ᵐ ω ∂Q, ω ∉ N₂ := hQP.ae_le (measure_eq_zero_iff_ae_notMem.1 hN₂0)
  set Ws : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ N₂ then 0 else stopK ζ Tn W t ω with hWs
  set Ls : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ N₂ then 0 else stopK ζ Tn (VL pL) t ω with hLs
  set Rs : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ N₂ then 0 else stopK ζ Tn (VR pR) t ω with hRs
  have hsm : ∀ {X : ℝ≥0 → Ω → ℝ}, AdaptedBefore 𝓖 ζ X →
      (∀ ω, ContinuousOn (X · ω) {t | (t : ℝ≥0∞) < ζ ω}) → ∀ t,
      Measurable[𝓖 t] (fun ω => if ω ∈ N₂ then 0 else stopK ζ Tn X t ω) := fun {X} hX hXc t => by
    let _ : MeasurableSpace Ω := 𝓖 t
    exact Measurable.ite (hnull N₂ hN₂m hN₂0 t) measurable_const (measurable_stopK hX hXc hTst t)
  have hsc : ∀ {X : ℝ≥0 → Ω → ℝ}, (∀ ω, ContinuousOn (X · ω) {t | (t : ℝ≥0∞) < ζ ω}) →
      ∀ ω, Continuous (fun t => if ω ∈ N₂ then 0 else stopK ζ Tn X t ω) := fun {X} hXc ω => by
    by_cases hω : ω ∈ N₂
    · simp only [hω, ↓reduceIte]; exact continuous_const
    · simp only [hω, ↓reduceIte]
      have : T ω < ζ ω := by simpa [hN₂] using hω
      exact continuous_stopK (hXc ω) (by rw [hTn]; exact this)
  have hsEq : ∀ {X : ℝ≥0 → Ω → ℝ} {ω : Ω}, ω ∉ N₂ → ∀ t : ℝ≥0, t ≤ Tn ω →
      (if ω ∈ N₂ then 0 else stopK ζ Tn X t ω) = X t ω := fun {X ω} hω t ht => by
    have : T ω < ζ ω := by simpa [hN₂] using hω
    simp only [hω, ↓reduceIte]
    exact stopK_of_le (by rw [hTn]; exact this) ht
  -- the merged two-seed path under `Q` up to `T`
  have hmerge : ∀ᵐ ω ∂Q, IsSLEPathUpTo a (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0)
      (fun _ => seedSum xL ρL) (fun _ => seedSum xR ρR) (Ws · ω) (fun _ t => Ls t ω)
      (fun _ t => Rs t ω) (Bh · ω) (Tn ω) := by
    filter_upwards [hEQ.ae_path, hN₂Q] with ω hp hω
    have hm := hp.mergeSeeds hpL hpR hsL hsR
    rw [← hTn ω] at hm
    refine isSLEPathUpTo_congr hm (hsEq hω 0 (zero_le)) (fun _ => hsEq hω 0 (zero_le))
      (fun _ => hsEq hω 0 (zero_le)) (fun t ht => hsEq hω t ?_) (fun t ht _ => hsEq hω t ?_)
      (fun t ht _ => hsEq hω t ?_) fun _ _ => rfl
    all_goals exact le_of_lt (by exact_mod_cast ht)
  -- the word at `T` is good
  have hgood : ∀ᵐ ω ∂Q, GoodWord (fun _ : Fin 1 => seedSum xL ρL) (fun _ : Fin 1 => seedSum xR ρR)
      (contWord Ws (fun _ : Fin 1 => Ls) (fun _ : Fin 1 => Rs) Tn ω) := by
    filter_upwards [hQP.ae_le hE.2.2.2.2, hQP.ae_le hTltP, hN₂Q] with ω hp hlt hω
    have hp' := hp.isSLEPathUpTo (le_refl (ζ ω))
    have hTlt : (Tn ω : ℝ≥0∞) < ζ ω := by rw [hTn]; exact hlt
    have hw : Ws (Tn ω) ω = W (Tn ω) ω := hsEq hω _ le_rfl
    have hl : Ls (Tn ω) ω = VL pL (Tn ω) ω := hsEq hω _ le_rfl
    have hr : Rs (Tn ω) ω = VR pR (Tn ω) ω := hsEq hω _ le_rfl
    refine ⟨fun _ _ => ?_, ⟨fun _ _ _ => le_rfl, fun _ => ?_, fun _ _ _ => le_rfl, fun _ => ?_⟩,
      not_thr_twoSeed hsL hsR _ _ _⟩
    · show Ls (Tn ω) ω - Ws (Tn ω) ω < Rs (Tn ω) ω - Ws (Tn ω) ω
      rw [hw, hl, hr]
      linarith [hp'.vL_lt_vR_of_pos hF (hTn0 ω) hTlt pL pR]
    · show Ls (Tn ω) ω - Ws (Tn ω) ω ≤ 0
      rw [hw, hl]
      linarith [hp'.vL_le_w hTlt pL]
    · show 0 ≤ Rs (Tn ω) ω - Ws (Tn ω) ω
      rw [hw, hr]
      linarith [hp'.w_le_vR hTlt pR]
  -- the continuation
  have hG := isIntegratedSLEEvolution_contClosed (P := Q) (𝓕 := 𝓖) ha hEQ.brownian hBhc
    (hsm hE.2.1 hWc) (fun _ t => hsm (hE.2.2.1 pL) (hVLc pL) t)
    (fun _ t => hsm (hE.2.2.2.1 pR) (hVRc pR) t) (hsc hWc) (fun _ => hsc (hVLc pL))
    (fun _ => hsc (hVRc pR)) hmerge hTst hTn0 hgood
  refine ⟨_, _, _, _, hQp, hG, ?_⟩
  filter_upwards [ae_lifetime_eq_top_twoSeed ha hG hsL hsR, hG.2.2.2.2, hQP.ae_le hE.2.2.2.2,
    hQP.ae_le hTltP, hN₂Q, hEQ.ae_path] with ω hζω hpG hp hlt hω hpQ
  have hpG' := hpG.isForcePath
  rw [hζω] at hpG'
  have huniv : {t : ℝ≥0 | (t : ℝ≥0∞) < ⊤} = univ := eq_univ_of_forall fun _ => ENNReal.coe_lt_top
  have hGwc := continuousOn_univ.1 (huniv ▸ hpG'.continuousOn_w)
  have hGlc := continuousOn_univ.1 (huniv ▸ hpG'.continuousOn_vL 0)
  have hGrc := continuousOn_univ.1 (huniv ▸ hpG'.continuousOn_vR 0)
  have hTlt : (Tn ω : ℝ≥0∞) < ζ ω := by rw [hTn]; exact hlt
  have hIic : Iic (Tn ω) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun t ht =>
    lt_of_le_of_lt (by exact_mod_cast ht) hTlt
  have hag : ∀ {f g : ℝ≥0 → ℝ}, Continuous f → ContinuousOn g {t | (t : ℝ≥0∞) < ζ ω} →
      (∀ s < Tn ω, f s = g s) → ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T ω → f t = g t := by
    intro f g hf hg hfg t ht
    have ht' : t ≤ Tn ω := by rw [← hTn ω] at ht; exact_mod_cast ht
    rcases lt_or_eq_of_le ht' with h | h
    · exact hfg t h
    · rw [h]
      exact eq_of_eqOn_Iio (hTn0 ω) hf.continuousOn (hg.mono hIic) hfg
  refine ⟨hζω, hlt, hp, hpG, hpQ, fun t ht => ⟨?_, ?_, ?_⟩⟩
  · refine hag hGwc (hWc ω) (fun s hs => ?_) t ht
    show concatAt (Tn ω) (Ws · ω) _ _ s = W s ω
    rw [concatAt_of_lt hs]; exact hsEq hω s hs.le
  · refine hag hGlc (hVLc pL ω) (fun s hs => ?_) t ht
    show concatAt (Tn ω) (Ls · ω) _ _ s = VL pL s ω
    rw [concatAt_of_lt hs]; exact hsEq hω s hs.le
  · refine hag hGrc (hVRc pR ω) (fun s hs => ?_) t ht
    show concatAt (Tn ω) (Rs · ω) _ _ s = VR pR s ω
    rw [concatAt_of_lt hs]; exact hsEq hω s hs.le

end Aux4

end Supp12

end InteractingSLE
