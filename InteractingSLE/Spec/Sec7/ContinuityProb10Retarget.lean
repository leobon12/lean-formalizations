/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.TargetChangeProcessBrownian

/-!
# The retargeted local evolution with its announcing stopping times

Packet PROVE-TRACECLOSE. `Zhan.Retarget.exists_retarget_evolution_of_seed` (PROVE-SEC7-C9) builds the local evolution
of LP9's transformed word on `Ω × Ω` through the localizing times `S_n = C(σ_n)` of the new clock, which are stopping
times of its filtration, lie before the new horizon and exhaust it (`newS_lt_horT`, `exists_le_newS`), but its
statement does not expose them. `exists_retarget_evolution_of_seed_stop` is the same construction (the proof is
PROVE-SEC7-C9's, unchanged) with this announcing sequence added to the conclusion. It is the input for a positive stop
before the horizon at a two-sided seed (`ContinuityProb10Seed`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Zhan

namespace Retarget

section Main

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} {nL j m : ℕ} {xL : Fin nL → ℝ} {xR : Fin (j + 1 + m) → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin (j + 1 + m) → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin (j + 1 + m) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The retargeted local evolution with an announcing sequence of its horizon** (admissible seed): the conclusion of
`exists_retarget_evolution_of_seed`, together with stopping times `S_n` of the filtration that lie almost surely before
the horizon and exhaust it. -/
theorem exists_retarget_evolution_of_seed_stop (hκ : 0 < κ) (hD : LP.IsDistinctForceWord xL xR) (hj : 1 ≤ j)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) :
    ∃ (𝓘 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × Ω))) (β : ℝ≥0 → Ω × Ω → ℝ)
      (τ : Ω → ℝ≥0∞),
      (∀ p, Continuous fun u => β u p) ∧
      (∀ᵐ ω ∂P, τ ω = newHorizon (LP.retargetPos xR) (fun t => W t ω) (fun t => VR (LP.retargetIdx j m) t ω)
        (sepTime (fun t => W t ω) (fun t => VR (LP.retargetIdx j m) t ω) (ζ ω))) ∧
      Sec2.IsSLEEvolutionUpTo κ (LP.retargetXL xL xR) (LP.retargetXR xR) (LP.retargetρL κ ρL ρR)
        (LP.retargetρR ρR) (P.prod P) 𝓘
        (fun u p => newW xR (fun t => W t p.1) (fun i t => VR i t p.1) u)
        (fun i u p => newVL xR (fun t => W t p.1) (fun i t => VL i t p.1) (fun i t => VR i t p.1) i u)
        (fun i u p => newVR xR (fun t => W t p.1) (fun i t => VR i t p.1) i u) β (fun p => τ p.1) ∧
      ∃ S : ℕ → Ω → ℝ≥0, (∀ n, IsStoppingTime 𝓘 fun p => (S n p.1 : WithTop ℝ≥0)) ∧
        ∀ᵐ ω ∂P, (∀ n, (S n ω : ℝ≥0∞) < τ ω) ∧ ∀ r : ℝ≥0, (r : ℝ≥0∞) < τ ω → ∃ n, r ≤ S n ω := by
  -- the independent Brownian motion
  obtain ⟨B₀, hB₀m, hB₀c, hB₀0, hB₀, -⟩ := QuantumZipper.RS.exists_good_version0 hE.1.1
  have hFB := hB₀.toIsPreBrownianReal.isFilteredPreBrownian hB₀m
  -- localization and the good event with the limit at the horizon
  obtain ⟨T, hT⟩ := Coupling.exists_isAnnouncingSeq hE hκ hseed
  obtain ⟨G₁, hG₁m, hG₁c, hgood₁⟩ := exists_good_r hE hT
  have hlim₁ := ae_tendsto_bv0 hE hG₁m hG₁c hgood₁ hT hD hj hκ
  set Bad : Set Ω := {ω | ¬ (ω ∈ G₁ → horT xR W VR ζ ω ≠ ⊤ → ∃ L, Tendsto
    (fun u => bv0 κ xL xR ρL ρR G₁ W VL VR B u ω) (𝓝[<] (horT xR W VR ζ ω).toNNReal) (𝓝 L))} with hBad
  have hBad0 : P Bad = 0 := ae_iff.1 hlim₁
  set G : Set Ω := G₁ ∩ (toMeasurable P Bad)ᶜ with hGdef
  have hGm : MeasurableSet G := hG₁m.inter (measurableSet_toMeasurable _ _).compl
  have hGc : P Gᶜ = 0 := by
    rw [hGdef, compl_inter, compl_compl]
    exact measure_union_null hG₁c (by rw [measure_toMeasurable]; exact hBad0)
  have hgood : ∀ ω ∈ G, IsRGood κ xL xR ρL ρR W VL VR B ζ T ω := fun ω hω => hgood₁ ω hω.1
  have hlim : ∀ ω ∈ G, horT xR W VR ζ ω ≠ ⊤ → ∃ L, Tendsto (fun u => bv0 κ xL xR ρL ρR G W VL VR B u ω)
      (𝓝[<] (horT xR W VR ζ ω).toNNReal) (𝓝 L) := by
    intro ω hω hfin
    have h1 : ω ∉ Bad := fun h => hω.2 (subset_toMeasurable _ _ h)
    simp only [hBad, mem_ofPred_eq, not_not] at h1
    obtain ⟨L, hL⟩ := h1 hω.1 hfin
    refine ⟨L, hL.congr fun u => ?_⟩
    simp only [bv0, rCoord, Sec2.TwoSeed.brownG, hω, hω.1, ↓reduceIte]
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hGc] with ω hω
    simpa using hω
  -- the exponential-martingale data of the frozen noise
  set H := filtH hE hGm hGc hgood hT hD hj with hHdef
  set S : ℕ → Ω → ℝ≥0 := fun n ω => newS xR G T W VL VR B ζ n ω with hSdef
  have hSm : ∀ (n : ℕ) (u : ℝ≥0), Measurable[H u] fun ω => min u (S n ω) := by
    intro n u
    have hσ := isStoppingTime_newS hE hGm hGc hgood hT hD hj n
    refine measurable_of_Iic (mδ := H u) fun x => ?_
    by_cases hx : u ≤ x
    · have : (fun ω => min u (S n ω)) ⁻¹' Iic x = univ := by
        ext ω; simp only [mem_preimage, mem_Iic, mem_univ, iff_true]; exact (min_le_left _ _).trans hx
      rw [this]; exact @MeasurableSet.univ _ (H u)
    · push Not at hx
      have : (fun ω => min u (S n ω)) ⁻¹' Iic x = {ω | ((S n ω : ℝ≥0) : WithTop ℝ≥0) ≤ x} := by
        ext ω
        simp only [mem_preimage, mem_Iic, min_le_iff, mem_ofPred_eq, WithTop.coe_le_coe]
        exact ⟨fun h => h.resolve_left (not_le.2 hx), Or.inr⟩
      rw [this]
      exact H.mono hx.le _ (hσ x)
  have hexp : ∀ (n : ℕ) (a : ℝ), Martingale (fun t ω => Real.exp (a * bvF κ xL xR ρL ρR G W VL VR B ζ
      (min t (S n ω)) ω - a ^ 2 * ((min t (S n ω) : ℝ≥0) : ℝ) / 2)) H P := by
    intro n a
    have h := martingale_exp_bv0_stopped hE hGm hGc hgood hT hD hj hκ a n
    convert h using 1
    funext t ω
    rw [bvF_min_newS hgood hD hj n t ω]
  have hTC := WholeField.isTCExpMartingale_annClock (𝒢 := fun _ : ℕ => H) (fun _ => monotone_const)
    (newS_mono hgood hD hj hT.2.1) hSm (continuous_bvF hgood hD hj hT.2.1 hlim) (bvF_zero hgood hD hj) hexp
  obtain ⟨hβ, hβc⟩ := WholeField.IsTCExpMartingale.isFilteredBrownianReal_complNoise hTC hFB hB₀c hB₀0
  set 𝓗' := WholeField.iSupFiltration (fun _ : ℕ => H) with h𝓗'
  have hle : ∀ t, H t ≤ 𝓗' t := fun t => WholeField.le_iSupFiltration (fun _ : ℕ => H) 0 t
  refine ⟨WholeField.prodFiltration 𝓗' (Filtration.natural B₀ fun t => (hB₀m t).stronglyMeasurable),
    WholeField.complNoise (fun u ω => bvF κ xL xR ρL ρR G W VL VR B ζ (WholeField.annClock S u ω) ω)
      (WholeField.annClock S) B₀, horG xR G W VR ζ, hβc, ?_, ?_, S, fun n u => ?_, ?_⟩
  · filter_upwards [hGae] with ω hω
    simp only [horG, hω, ↓reduceIte]
    rfl
  -- the local evolution
  have hlift : ∀ {X : ℝ≥0 → Ω → ℝ}, AdaptedBefore H (horG xR G W VR ζ) X →
      AdaptedBefore (WholeField.prodFiltration 𝓗' (Filtration.natural B₀ fun t => (hB₀m t).stronglyMeasurable))
        (fun p : Ω × Ω => horG xR G W VR ζ p.1) (fun t p => X t p.1) := by
    intro X hX t A hA
    exact WholeField.comap_fst_le_prodFiltration 𝓗' _ t _ ⟨_, hle t _ (hX t A hA), rfl⟩
  -- the path facts at a good `ω`
  have hpd : ∀ ω ∈ G, ∃ (hp : Sec2.IsSLEPathUpTo κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (B · ω) (sepTime (W · ω) (VR (LP.retargetIdx j m) · ω) (ζ ω))),
      RetargetData xL xR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
        (sepTime (W · ω) (VR (LP.retargetIdx j m) · ω) (ζ ω)) := fun ω hω => by
    have hp := (hgood ω hω).1.isSLEPathUpTo (sepTime_le (W · ω) (VR (LP.retargetIdx j m) · ω) (ζ ω))
    exact ⟨hp, retargetData_of_isSLEPathUpTo hp hD hj fun _ ht => lt_of_lt_sepTime ht⟩
  have hinv : ∀ ω ∈ G, ∀ t : ℝ≥0, (t : ℝ≥0∞) < horT xR W VR ζ ω →
      0 ≤ invClk (rate (LP.retargetPos xR) (W · ω) (VR (LP.retargetIdx j m) · ω)) t ∧
      (((invClk (rate (LP.retargetPos xR) (W · ω) (VR (LP.retargetIdx j m) · ω)) t).toNNReal : ℝ≥0) : ℝ≥0∞) <
        sepTime (W · ω) (VR (LP.retargetIdx j m) · ω) (ζ ω) := by
    intro ω hω t ht
    obtain ⟨hp, hd⟩ := hpd ω hω
    obtain ⟨S', _, _, _, hm, _⟩ := newTime_spec hd.sep hd.pos ht
    exact ⟨hm.1, invClk_lt hd.sep hd.pos ht⟩
  refine ⟨hβ, hlift (X := fun u ω => newW xR (W · ω) (fun i t => VR i t ω) u)
      (adaptedBefore_of_coords hE hGm hGc hgood hT hD hj (measurable_phiW κ xL xR ρL ρR) fun ω hω t ht => ?_),
    fun i => hlift (X := fun u ω => newVL xR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) i u)
      (adaptedBefore_of_coords hE hGm hGc hgood hT hD hj (measurable_phiVL i) fun ω hω t ht => ?_),
    fun i => hlift (X := fun u ω => newVR xR (W · ω) (fun i t => VR i t ω) i u)
      (adaptedBefore_of_coords hE hGm hGc hgood hT hD hj (measurable_phiVR i) fun ω hω t ht => ?_), ?_⟩
  · obtain ⟨hp, -⟩ := hpd ω hω
    have e := newW_eq_phiW (κ := κ) (xL := xL) (ρL := ρL) (ρR := ρR) hp (hinv ω hω t ht).1 (hinv ω hω t ht).2
    rw [show rateT xR W VR ω = rate (LP.retargetPos xR) (W · ω) (VR (LP.retargetIdx j m) · ω) from rfl]
    exact e
  · have e := newVL_eq_phiVL (xR := xR) (w := (W · ω)) (vR := fun i t => VR i t ω)
      (vL := fun i t => VL i t ω) (b := (B · ω)) (hinv ω hω t ht).1 i
    rw [show rateT xR W VR ω = rate (LP.retargetPos xR) (W · ω) (VR (LP.retargetIdx j m) · ω) from rfl]
    exact e
  · have e := newVR_eq_phiVR (xR := xR) (w := (W · ω)) (vR := fun i t => VR i t ω)
      (vL := fun i t => VL i t ω) (b := (B · ω)) (hinv ω hω t ht).1 i
    rw [show rateT xR W VR ω = rate (LP.retargetPos xR) (W · ω) (VR (LP.retargetIdx j m) · ω) from rfl]
    exact e
  · filter_upwards [Measure.quasiMeasurePreserving_fst.ae hGae] with p hp1
    obtain ⟨hp, hd⟩ := hpd p.1 hp1
    have h := isSLEPathUpTo_retarget hp hd hD hκ
    simp only [horG, hp1, ↓reduceIte]
    refine isSLEPathUpTo_congr_b h fun u hu => ?_
    have hu' : (u : ℝ≥0∞) < horT xR W VR ζ p.1 := hu
    obtain ⟨n, hn⟩ := exists_le_newS hgood hD hj hT.2.1 hp1 hu'
    have hℓ : WholeField.annClock S u p.1 = u := WholeField.annClock_eq_of_le hn
    rw [WholeField.complNoise_of_eq hℓ, hℓ]
    simp only [bvF, hp1, ↓reduceIte, hu']
    exact (bv0_eq_newB hκ hgood hD hj hp1 hu').symm
  · -- the new localizing times are stopping times of the product filtration
    exact WholeField.comap_fst_le_prodFiltration 𝓗' _ u _
      ⟨_, hle u _ (isStoppingTime_newS hE hGm hGc hgood hT hD hj n u), rfl⟩
  · filter_upwards [hGae] with ω hω
    simp only [horG, hω, ↓reduceIte]
    exact ⟨fun n => newS_lt_horT hgood hD hj hω n, fun r hr => exists_le_newS hgood hD hj hT.2.1 hω hr⟩


end Main

end Retarget

end Zhan

end InteractingSLE
