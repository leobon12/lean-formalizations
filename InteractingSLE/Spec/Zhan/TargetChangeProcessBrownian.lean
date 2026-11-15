/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.TargetChangeProcessBrownianAdapt
import InteractingSLE.Spec.Coupling.WholeField5Germ

/-!
# `b̃` is a Brownian motion: the proof of `RetargetEvolutionStatement`

Packet PROVE-SEC7-C9. **`retargetEvolutionStatement`**: for an integrated evolution of a retargeted distinct word,
the transformed paths of PROVE-SEC7-C8 form a local integrated `SLE_κ(ρ̃)` evolution of LP9's transformed word before
the new horizon, driven by a Brownian motion on `Ω × Ω`.

Proof (admissible seed). Localize (part 1–2), the localized Itô martingales (part 3), read them in the new clock
(parts 4–5), the a.s. limit of the noise at a finite horizon (part 6), freeze the noise there (part 7). Then
`WholeField.isTCExpMartingale_annClock` gives the exponential-martingale data `IsTCExpMartingale` of the frozen noise
`bvF` with the clock `u ∧ T̃`, and `IsTCExpMartingale.isFilteredBrownianReal_complNoise` continues it by an independent
Brownian motion on the second factor: `β = bvF(u ∧ T̃) + B₀(u) − B₀(u ∧ T̃)` is a Brownian motion of
`𝓗 ⊗ 𝓦`. Before `T̃`, `β = bv0 = b̃` (`bv0_eq_newB`), so the paths are those of `isSLEPathUpTo_retarget`; they
are adapted by part 8.

An inadmissible seed makes the lifetime, hence the horizon, `0` almost surely; then `β` is the independent Brownian
motion and the horizon is `0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Zhan

namespace Retarget

/-- A local path with its Brownian path changed after the horizon is still a local path. -/
theorem isSLEPathUpTo_congr_b {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b b' : ℝ≥0 → ℝ}
    {τ : ℝ≥0∞} (h : Sec2.IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ)
    (hb : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → b t = b' t) : Sec2.IsSLEPathUpTo a xL xR ρL ρR w vL vR b' τ :=
  { h with w_eq := fun ht => by rw [← hb _ ht]; exact h.w_eq ht }

/-- The new horizon of a zero time is zero. -/
theorem newHorizon_zero (xk : ℝ) (w vk : ℝ≥0 → ℝ) : newHorizon xk w vk 0 = 0 := by
  simp [newHorizon]

/-- The exponential-martingale data of the zero noise with the zero clock. -/
theorem isTCExpMartingale_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (𝓗 : Filtration ℝ≥0 ‹_›) :
    Sec6.Prop65.IsTCExpMartingale P 𝓗 (fun _ _ => 0) (fun _ _ => 0) :=
  ⟨fun _ => measurable_const, fun _ => measurable_const, fun _ _ => bot_le, fun _ _ _ _ => by simp,
    fun _ => continuous_const, fun _ => rfl, fun _ _ _ _ _ _ => rfl⟩

/-! ### The admissible seed -/

section Main

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} {nL j m : ℕ} {xL : Fin nL → ℝ} {xR : Fin (j + 1 + m) → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin (j + 1 + m) → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin (j + 1 + m) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **`b̃` is a Brownian motion, for an admissible seed.** -/
theorem exists_retarget_evolution_of_seed (hκ : 0 < κ) (hD : LP.IsDistinctForceWord xL xR) (hj : 1 ≤ j)
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
        (fun i u p => newVR xR (fun t => W t p.1) (fun i t => VR i t p.1) i u) β (fun p => τ p.1) := by
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
      (WholeField.annClock S) B₀, horG xR G W VR ζ, hβc, ?_, ?_⟩
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

/-- **`b̃` is a Brownian motion, for an inadmissible seed**: the lifetime and the horizon are `0`. -/
theorem exists_retarget_evolution_of_threshold (hκ : 0 < κ) (hD : LP.IsDistinctForceWord xL xR) (hj : 1 ≤ j)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR) :
    ∃ (𝓘 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × Ω))) (β : ℝ≥0 → Ω × Ω → ℝ)
      (τ : Ω → ℝ≥0∞),
      (∀ p, Continuous fun u => β u p) ∧
      (∀ᵐ ω ∂P, τ ω = newHorizon (LP.retargetPos xR) (fun t => W t ω) (fun t => VR (LP.retargetIdx j m) t ω)
        (sepTime (fun t => W t ω) (fun t => VR (LP.retargetIdx j m) t ω) (ζ ω))) ∧
      Sec2.IsSLEEvolutionUpTo κ (LP.retargetXL xL xR) (LP.retargetXR xR) (LP.retargetρL κ ρL ρR)
        (LP.retargetρR ρR) (P.prod P) 𝓘
        (fun u p => newW xR (fun t => W t p.1) (fun i t => VR i t p.1) u)
        (fun i u p => newVL xR (fun t => W t p.1) (fun i t => VL i t p.1) (fun i t => VR i t p.1) i u)
        (fun i u p => newVR xR (fun t => W t p.1) (fun i t => VR i t p.1) i u) β (fun p => τ p.1) := by
  obtain ⟨B₀, hB₀m, hB₀c, hB₀0, hB₀, -⟩ := QuantumZipper.RS.exists_good_version0 hE.1.1
  have hFB := hB₀.toIsPreBrownianReal.isFilteredPreBrownian hB₀m
  obtain ⟨hβ, hβc⟩ := WholeField.IsTCExpMartingale.isFilteredBrownianReal_complNoise
    (isTCExpMartingale_zero P 𝓕) hFB hB₀c hB₀0
  have hζ0 : ∀ᵐ ω ∂P, ζ ω = 0 := by
    filter_upwards [hE.2.2.2.2] with ω hp
    by_contra hne
    have hpos : ((0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by
      rw [ENNReal.coe_zero]; exact pos_iff_ne_zero.2 hne
    have hu := hp.isSLEPathUpTo le_rfl
    have h := hu.not_threshold hpos
    have e1 : (fun i => VL i 0 ω) = xL := funext hu.vL_zero
    have e2 : (fun i => VR i 0 ω) = xR := funext hu.vR_zero
    have e0 : W 0 ω = 0 := hu.w_zero
    simp only [e0] at h
    rw [e1, e2] at h
    exact h hseed
  refine ⟨WholeField.prodFiltration 𝓕 (Filtration.natural B₀ fun t => (hB₀m t).stronglyMeasurable),
    WholeField.complNoise (fun _ _ => 0) (fun _ _ => 0) B₀, fun _ => 0, hβc, ?_, ?_⟩
  · filter_upwards [hζ0] with ω hω
    simp only [sepTime, hω, zero_le, min_eq_left, newHorizon_zero]
  have hempty : ∀ (t : ℝ≥0) (X : Ω × Ω → ℝ) (A : Set ℝ),
      {p : Ω × Ω | (t : ℝ≥0∞) < (fun _ : Ω => (0 : ℝ≥0∞)) p.1 ∧ X p ∈ A} = ∅ := fun t X A => by
    ext p; simp
  refine ⟨hβ, fun t A _ => ?_, fun i t A _ => ?_, fun i t A _ => ?_, ?_⟩
  · rw [hempty]; exact (WholeField.prodFiltration 𝓕 _ t).measurableSet_empty
  · rw [hempty]; exact (WholeField.prodFiltration 𝓕 _ t).measurableSet_empty
  · rw [hempty]; exact (WholeField.prodFiltration 𝓕 _ t).measurableSet_empty
  · filter_upwards [Measure.quasiMeasurePreserving_fst.ae hE.2.2.2.2] with p hp
    have hu := hp.isSLEPathUpTo (bot_le : (0 : ℝ≥0∞) ≤ ζ p.1)
    have hd := retargetData_of_isSLEPathUpTo hu hD hj fun t ht => absurd ht (not_lt.2 bot_le)
    have h := (isSLEPathUpTo_retarget hu hd hD hκ).mono (bot_le : (0 : ℝ≥0∞) ≤ _)
    exact isSLEPathUpTo_congr_b h fun t ht => absurd ht (not_lt.2 bot_le)

end Main

/-- **`b̃` is a Brownian motion** (Specification pp. 378–379, supplement p. 485): the proof of the named statement
`RetargetEvolutionStatement`. -/
theorem retargetEvolutionStatement : RetargetEvolutionStatement.{u} := by
  intro Ω mΩ P hP 𝓕 κ nL j m xL xR ρL ρR W VL VR B ζ hκ hD hj hE
  by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · exact exists_retarget_evolution_of_threshold hκ hD hj hE hseed
  · exact exists_retarget_evolution_of_seed hκ hD hj hE hseed

end Retarget

end Zhan

end InteractingSLE
