/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtLLocQ

/-!
# Aux. lemma 54, (Loc) before the local stop: the projection identity on the extension

Packet PROVE-LOCEXT-L. On a record extension `E` of a stopped seed coupling `(Q, h)` by a time-adapted two-seed reference,
at a stop `s` of the reference's usual augmentation that is safe for a compact `C ⊆ ℍ` (`s < ζ̂`, `C ∩ K_s = ∅`), for an
open `U ⊆ C` and every event `A₀ ∈ 𝓖_s`, the centred original field `X = h(p.1) − T₀` satisfies the projection identity
of `Coupling.IsFamilyLocal` on `snd⁻¹(A₀ ∩ {s < Ŝ})`:

`∫ e^{iX(−Δf/2π + Ξ)} dE = projFactor U f Ξ · ∫ e^{iX(Ξ)} dE`.

Proof: as for (K-pre) (`LocalExtLPre`). Cut `A₀` along the dyadic grid; each piece, restricted to
`{t₁ < Ŝ, C ∩ K_{t₂} = ∅}` (`t₁ = (k+1)/2ⁿ`, `t₂ = (k+2)/2ⁿ`), is almost surely the reference history event
`preHistSet t₁ t₂ Γ C` (time-adapted generation at `t₁`); on `E` it is the same history event of the stopped coupling,
where the identity is `IsStoppedSeedCoupling.setIntegral_lapTest_pre`. Summation and dominated convergence (the pieces
increase to `A₀ ∩ {s < Ŝ}` by right-continuity of the hulls on `C`) conclude.

## Main results

* **`setIntegral_lapTest_preStop_of_tag`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace LocalExt

open Sec7 Sec4 LQGMetric LQGMetric.MarkovZB Coupling LocalSets

section Main

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {S : Ω → WithTop ℝ≥0}
  {h : Ω → DistOn upperHalfPlaneOpens}
  {Ωr : Type u} {mΩr : MeasurableSpace Ωr} {Pr : Measure Ωr} {𝓕r : Filtration ℝ≥0 mΩr}
  {Wr : ℝ≥0 → Ωr → ℝ} {VLr VRr : Fin 1 → ℝ≥0 → Ωr → ℝ} {Br : ℝ≥0 → Ωr → ℝ} {ζr : Ωr → ℝ≥0∞}
  {hr' : Ωr → DistOn upperHalfPlaneOpens} {Gr : Set Ωr}

/-- **On one history event before the stop, the projection identity transfers to the extension.** -/
theorem setIntegral_lapTest_hist_eq [IsProbabilityMeasure Q] [IsProbabilityMeasure Pr]
    (hr : 0 < r) (hL : -2 < seedSumL xL ρL) (hR : -2 < seedSumR xR ρR)
    (hc : IsStoppedSeedCoupling κ xL xR ρL ρR r Q W VL VR S h)
    (hC : IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => seedSumL xL ρL)
      (fun _ => seedSumR xR ρR) Pr 𝓕r Wr VLr VRr Br ζr hr')
    (hGm : MeasurableSet Gr) (hG0 : Pr Grᶜ = 0)
    (hG : ∀ ω ∈ Gr, IsGoodPath κ LP.twoSeedXL LP.twoSeedXR (fun _ => seedSumL xL ρL) (fun _ => seedSumR xR ρR)
      Wr VLr VRr Br ζr ω)
    {E : Measure (Ω × Ωr)}
    (hE : IsRecordExtension Q Pr h (stRecHist xL xR W VL VR S) hr' (refRecHist xL xR r Gr Wr VLr VRr ζr) E)
    {T₀ : DistOn upperHalfPlaneOpens} (hT₀ : IsHarmonicDistOn T₀ H) {t₁ t₂ : ℚ≥0} (ht : t₁ < t₂)
    {Γ : Set TwoSeedHist} (hΓ : MeasurableSet Γ) {C : Set ℂ} (hCc : IsCompact C) (hCH : C ⊆ H) {U : Opens ℂ}
    (hUC : (U : Set ℂ) ⊆ C) (f : zsSub (U : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) :
    ∫ p in Prod.snd ⁻¹' (refVer xL xR r Gr Wr VLr VRr ζr ⁻¹' preHistSet t₁ t₂ Γ C),
        Complex.exp (Complex.I * ((h p.1 - T₀) (lapTest U f + Ξ) : ℂ)) ∂E =
      Coupling.projFactor U f Ξ * ∫ p in Prod.snd ⁻¹' (refVer xL xR r Gr Wr VLr VRr ζr ⁻¹' preHistSet t₁ t₂ Γ C),
        Complex.exp (Complex.I * ((h p.1 - T₀) Ξ : ℂ)) ∂E := by
  have hRm := hc.measurable_stRecHist
  have hVm := measurable_refVer (r := r) hC hGm hG0 hG
  have hVe := ae_refVer_eq xL xR hL hR hr hG0 hG
  obtain ⟨-, -, -, -, -, -, -, hhm, -⟩ := id hc
  obtain ⟨hfst, hsnd, hhist, -, -⟩ := hE
  have hD' : MeasurableSet (preHistSet t₁ t₂ Γ C) := measurableSet_preHistSet t₁ t₂ hΓ hCc
  have hVeE : ∀ᵐ p ∂E, refVer xL xR r Gr Wr VLr VRr ζr p.2 = refRecHist xL xR r Gr Wr VLr VRr ζr p.2 := by
    rw [← hsnd] at hVe
    exact ae_of_ae_map measurable_snd.aemeasurable hVe
  have hset : (Prod.snd ⁻¹' (refVer xL xR r Gr Wr VLr VRr ζr ⁻¹' preHistSet t₁ t₂ Γ C) : Set (Ω × Ωr)) =ᵐ[E]
      (Prod.fst ⁻¹' (stRecHist xL xR W VL VR S ⁻¹' preHistSet t₁ t₂ Γ C) : Set (Ω × Ωr)) := by
    filter_upwards [hhist, hVeE] with p h1 h2
    simp only [mem_preimage, h1, h2]
  have hhm' : Measurable fun ω => h ω - T₀ := (WholeField.measurable_sub_dist T₀).comp hhm
  have hcm : ∀ χ : TestOn upperHalfPlaneOpens, Measurable fun ω => Complex.exp (Complex.I * ((h ω - T₀) χ : ℂ)) :=
    fun χ => Complex.continuous_exp.measurable.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp ((measurable_distOn_apply χ).comp hhm')))
  have hmap : ∀ χ : TestOn upperHalfPlaneOpens,
      ∫ p in Prod.snd ⁻¹' (refVer xL xR r Gr Wr VLr VRr ζr ⁻¹' preHistSet t₁ t₂ Γ C),
        Complex.exp (Complex.I * ((h p.1 - T₀) χ : ℂ)) ∂E =
      ∫ ω in stRecHist xL xR W VL VR S ⁻¹' preHistSet t₁ t₂ Γ C, Complex.exp (Complex.I * ((h ω - T₀) χ : ℂ)) ∂Q := by
    intro χ
    rw [setIntegral_congr_set hset, ← hfst]
    exact (setIntegral_map (hRm hD') (hcm χ).aestronglyMeasurable measurable_fst.aemeasurable).symm
  rw [hmap, hmap]
  exact hc.setIntegral_lapTest_pre hr hT₀ ht hΓ hCc hCH hUC f Ξ

/-- **(Loc) before the local stop**: the projection identity of `Coupling.IsFamilyLocal` for the centred original field on
`snd⁻¹(A₀ ∩ {s < Ŝ})`, `A₀ ∈ 𝓖_s`, for a time-adapted reference and a stop `s` safe for a compact `C ⊇ U`. -/
theorem setIntegral_lapTest_preStop_of_tag [IsProbabilityMeasure Q] [IsProbabilityMeasure Pr]
    (hr : 0 < r) (hL : -2 < seedSumL xL ρL) (hR : -2 < seedSumR xR ρR)
    (hc : IsStoppedSeedCoupling κ xL xR ρL ρR r Q W VL VR S h)
    (hC : IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => seedSumL xL ρL)
      (fun _ => seedSumR xR ρR) Pr 𝓕r Wr VLr VRr Br ζr hr')
    (hGm : MeasurableSet Gr) (hG0 : Pr Grᶜ = 0)
    (hG : ∀ ω ∈ Gr, IsGoodPath κ LP.twoSeedXL LP.twoSeedXR (fun _ => seedSumL xL ρL) (fun _ => seedSumR xR ρR)
      Wr VLr VRr Br ζr ω)
    (hTAG : IsTimeAdaptedRef xL xR r Gr Pr 𝓕r Wr VLr VRr ζr)
    {E : Measure (Ω × Ωr)}
    (hE : IsRecordExtension Q Pr h (stRecHist xL xR W VL VR S) hr' (refRecHist xL xR r Gr Wr VLr VRr ζr) E)
    {T₀ : DistOn upperHalfPlaneOpens} (hT₀ : IsHarmonicDistOn T₀ H)
    {C : Set ℂ} (hCc : IsCompact C) (hCH : C ⊆ H) {U : Opens ℂ} (hUC : (U : Set ℂ) ⊆ C)
    (s : Ωr → ℝ≥0) (hs : IsStoppingTime (usualAugmentation 𝓕r Pr) fun ω => (s ω : WithTop ℝ≥0))
    (hsafe : ∀ᵐ ω ∂Pr, (s ω : ℝ≥0∞) < ζr ω ∧ Disjoint C (fwdHull (fun r : ℝ => Wr r.toNNReal ω) (s ω)))
    (f : zsSub (U : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) (A₀ : Set Ωr)
    (hA₀ : MeasurableSet[hs.measurableSpace] A₀) :
    ∫ p in Prod.snd ⁻¹' (A₀ ∩ {ω | (s ω : WithTop ℝ≥0) < capStop r Gr ζr Wr ω}),
        Complex.exp (Complex.I * ((h p.1 - T₀) (lapTest U f + Ξ) : ℂ)) ∂E =
      Coupling.projFactor U f Ξ * ∫ p in Prod.snd ⁻¹' (A₀ ∩ {ω | (s ω : WithTop ℝ≥0) < capStop r Gr ζr Wr ω}),
        Complex.exp (Complex.I * ((h p.1 - T₀) Ξ : ℂ)) ∂E := by
  classical
  have hEp : IsProbabilityMeasure E := isProbabilityMeasure_of_map_fst hE.1
  have hsnd : E.map Prod.snd = Pr := hE.2.1
  obtain ⟨-, -, -, -, -, -, -, hhm, -⟩ := id hc
  obtain ⟨hXr, -⟩ := hC.2.2.2
  have hŜm : Measurable (capStop r Gr ζr Wr) := (isStoppingTime_capStop hXr hGm hG0 hG r).measurable'
  have hsm : Measurable fun ω => (s ω : WithTop ℝ≥0) := hs.measurable'
  have hVm := measurable_refVer (r := r) hC hGm hG0 hG
  have hVe := ae_refVer_eq xL xR hL hR hr hG0 hG
  set c : ℂ := Coupling.projFactor U f Ξ with hcdef
  set Iev : ℕ → ℕ → Set Ωr := fun n k => A₀ ∩ {ω | ⌈(2 : ℝ≥0) ^ n * s ω⌉₊ = k} with hIevdef
  have hIev : ∀ n k, MeasurableSet[usualAugmentation 𝓕r Pr ((dyadicQ (n, k) : ℚ≥0) : ℝ≥0)] (Iev n k) := by
    intro n k
    rw [coe_dyadicQ]
    exact measurableSet_inter_ceil_eq hs hA₀ n k
  have hq1 : ∀ n k, dyadicQ (n, k) < dyadicQ (n, k + 1) := by
    intro n k
    simp only [dyadicQ]
    gcongr
    exact_mod_cast Nat.lt_succ_self k
  have hq2 : ∀ n k, dyadicQ (n, k + 1) < dyadicQ (n, k + 2) := by
    intro n k
    simp only [dyadicQ]
    gcongr
    omega
  choose Γ hΓm hΓ using fun n k => hTAG (dyadicQ (n, k)) (dyadicQ (n, k + 1)) (hq1 n k) (Iev n k) (hIev n k)
  set Ev : ℕ → ℕ → Set Ωr := fun n k => refVer xL xR r Gr Wr VLr VRr ζr ⁻¹'
    {y | ((dyadicQ (n, k + 1) : ℝ≥0) : WithTop ℝ≥0) < y.1 ∧ Disjoint C (tsHull (truncH (dyadicQ (n, k + 2)) y))}
    with hEvdef
  set Hv : ℕ → ℕ → Set Ωr := fun n k => refVer xL xR r Gr Wr VLr VRr ζr ⁻¹'
    preHistSet (dyadicQ (n, k + 1)) (dyadicQ (n, k + 2)) (Γ n k) C with hHvdef
  set P : ℕ → ℕ → Set Ωr := fun n k => Iev n k ∩ Ev n k with hPdef
  have hEvm : ∀ n k, MeasurableSet (Ev n k) := fun n k =>
    hVm ((measurableSet_lt measurable_const measurable_fst).inter
      ((measurable_truncH _) (measurableSet_disjoint_tsHull hCc)))
  have hPm : ∀ n k, MeasurableSet (P n k) := fun n k =>
    ((usualAugmentation 𝓕r Pr).le _ _ (hIev n k)).inter (hEvm n k)
  have hPH : ∀ n k, ∀ᵐ ω ∂Pr, (ω ∈ P n k ↔ ω ∈ Hv n k) := by
    intro n k
    filter_upwards [hΓ n k, hVe] with ω hω hve
    simp only [hPdef, hHvdef, hEvdef, mem_inter_iff, mem_preimage, mem_ofPred_eq, preHistSet, hve]
    have hcap : (refRecHist xL xR r Gr Wr VLr VRr ζr ω).1 = capStop r Gr ζr Wr ω := rfl
    rw [hcap]
    constructor
    · rintro ⟨hI, ht, hD⟩
      exact ⟨ht, (hω ht).1 hI, hD⟩
    · rintro ⟨ht, hΓω, hD⟩
      exact ⟨(hω ht).2 hΓω, ht, hD⟩
  have hcexp : ∀ χ : TestOn upperHalfPlaneOpens,
      Measurable fun p : Ω × Ωr => Complex.exp (Complex.I * ((h p.1 - T₀) χ : ℂ)) := fun χ =>
    Complex.continuous_exp.measurable.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      ((measurable_distOn_apply χ).comp (((WholeField.measurable_sub_dist T₀).comp hhm).comp measurable_fst))))
  have hint : ∀ χ : TestOn upperHalfPlaneOpens,
      Integrable (fun p : Ω × Ωr => Complex.exp (Complex.I * ((h p.1 - T₀) χ : ℂ))) E := fun χ =>
    Integrable.of_bound (hcexp χ).aestronglyMeasurable 1
      (Eventually.of_forall fun p => (Complex.norm_exp_I_mul_ofReal _).le)
  -- the identity on each piece
  have hpiece : ∀ n k, ∫ p in Prod.snd ⁻¹' P n k, Complex.exp (Complex.I * ((h p.1 - T₀) (lapTest U f + Ξ) : ℂ)) ∂E =
      c * ∫ p in Prod.snd ⁻¹' P n k, Complex.exp (Complex.I * ((h p.1 - T₀) Ξ : ℂ)) ∂E := by
    intro n k
    have hset : (Prod.snd ⁻¹' P n k : Set (Ω × Ωr)) =ᵐ[E] (Prod.snd ⁻¹' Hv n k : Set (Ω × Ωr)) := by
      have h1 := hPH n k
      rw [← hsnd] at h1
      filter_upwards [ae_of_ae_map measurable_snd.aemeasurable h1] with p hp
      exact propext hp
    rw [setIntegral_congr_set hset, setIntegral_congr_set hset]
    exact setIntegral_lapTest_hist_eq hr hL hR hc hC hGm hG0 hG hE hT₀ (hq2 n k) (hΓm n k) hCc hCH hUC f Ξ
  -- the unions over `k`
  set B : ℕ → Set Ωr := fun n => ⋃ k, P n k with hBdef
  have hPdisj : ∀ n, Pairwise (Function.onFun Disjoint fun k => (Prod.snd ⁻¹' P n k : Set (Ω × Ωr))) := by
    intro n k k' hkk'
    refine Set.disjoint_left.2 fun p hp hp' => hkk' ?_
    exact hp.1.2.symm.trans hp'.1.2
  have hBint : ∀ n, ∫ p in Prod.snd ⁻¹' B n, Complex.exp (Complex.I * ((h p.1 - T₀) (lapTest U f + Ξ) : ℂ)) ∂E =
      c * ∫ p in Prod.snd ⁻¹' B n, Complex.exp (Complex.I * ((h p.1 - T₀) Ξ : ℂ)) ∂E := by
    intro n
    simp only [hBdef, preimage_iUnion]
    rw [integral_iUnion (fun k => measurable_snd (hPm n k)) (hPdisj n) (hint _).integrableOn,
      integral_iUnion (fun k => measurable_snd (hPm n k)) (hPdisj n) (hint _).integrableOn, ← tsum_mul_left]
    exact tsum_congr fun k => hpiece n k
  -- the target event
  set T : Set Ωr := A₀ ∩ {ω | (s ω : WithTop ℝ≥0) < capStop r Gr ζr Wr ω} with hTdef
  have hTm : MeasurableSet T := (hs.measurableSpace_le A₀ hA₀).inter (measurableSet_lt hsm hŜm)
  have hBT : ∀ n, B n ⊆ T := by
    intro n ω hω
    obtain ⟨k, hk⟩ := mem_iUnion.1 hω
    obtain ⟨⟨hA, hceil⟩, hev⟩ := hk
    have ht : ((dyadicQ (n, k + 1) : ℝ≥0) : WithTop ℝ≥0) < capStop r Gr ζr Wr ω := hev.1
    refine ⟨hA, lt_of_le_of_lt ?_ ht⟩
    have h1 : s ω ≤ LawUnique.dyadicTime (n, k) := (ceil_le_iff_le_dyadicTime (s ω) n k).1 hceil.le
    have h2 : LawUnique.dyadicTime (n, k) ≤ ((dyadicQ (n, k + 1) : ℚ≥0) : ℝ≥0) := by
      rw [coe_dyadicQ]
      simp only [LawUnique.dyadicTime]
      gcongr
      exact_mod_cast Nat.le_succ k
    exact WithTop.coe_le_coe.2 (h1.trans h2)
  have hGP : ∀ᵐ ω ∂Pr, ω ∈ Gr := ae_iff.2 (by exact hG0)
  have hconv : ∀ᵐ ω ∂Pr, ω ∈ T → ∀ᶠ n in atTop, ω ∈ B n := by
    filter_upwards [hGP, hsafe, hVe] with ω hω hsf hve hωT
    obtain ⟨hS, hSζ⟩ := capStop_ref hL hR hr hG hω
    set S₀ : ℝ≥0 := (capStop r Gr ζr Wr ω).untopD 0 with hS₀
    have hxS : s ω < S₀ := by
      have : (s ω : WithTop ℝ≥0) < capStop r Gr ζr Wr ω := hωT.2
      rw [hS] at this
      exact WithTop.coe_lt_coe.1 this
    set t1 : ℕ → ℝ≥0 := fun n => LawUnique.dyadicTime (n, ⌈(2 : ℝ≥0) ^ n * s ω⌉₊ + 1) with ht1
    set t2 : ℕ → ℝ≥0 := fun n => LawUnique.dyadicTime (n, ⌈(2 : ℝ≥0) ^ n * s ω⌉₊ + 2) with ht2
    have ht12 : ∀ n, t1 n ≤ t2 n := fun n => by
      simp only [ht1, ht2, LawUnique.dyadicTime]
      gcongr
      exact_mod_cast Nat.le_succ _
    have ht2s : ∀ n, s ω ≤ t2 n := fun n => (lt_dyadicTime_ceil_succ (s ω) n).le.trans (ht12 n)
    have ht2T : Tendsto t2 atTop (𝓝 (s ω)) := by
      have hup : Tendsto (fun n : ℕ => s ω + 3 * (1 / (2 : ℝ≥0) ^ n)) atTop (𝓝 (s ω)) := by
        have := (LawUnique.tendsto_one_div_two_pow.const_mul (3 : ℝ≥0)).const_add (s ω)
        simpa using this
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup ht2s fun n => ?_
      have hpos : (0 : ℝ≥0) < 2 ^ n := pow_pos two_pos n
      have hk : (⌈(2 : ℝ≥0) ^ n * s ω⌉₊ : ℝ≥0) < 2 ^ n * s ω + 1 := Nat.ceil_lt_add_one zero_le
      simp only [ht2, LawUnique.dyadicTime]
      rw [div_le_iff₀ hpos]
      have : (s ω + 3 * (1 / 2 ^ n)) * 2 ^ n = 2 ^ n * s ω + 3 := by field_simp
      rw [this]
      push_cast
      calc (⌈(2 : ℝ≥0) ^ n * s ω⌉₊ : ℝ≥0) + 2 ≤ (2 ^ n * s ω + 1) + 2 := by gcongr
        _ = 2 ^ n * s ω + 3 := by ring
    have hev1 : ∀ᶠ n in atTop, t2 n < S₀ := ht2T.eventually (gt_mem_nhds hxS)
    have hwc : ContinuousOn (fun t => Wr t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < ζr ω} := (hG ω hω).1.2.2.2.1
    have hev2 : ∀ᶠ n in atTop, Disjoint C (fwdHull (Ito.rpath fun t => Wr t ω) (t2 n : ℝ)) :=
      HullRightCont.eventually_disjoint_fwdHull_rpath_of_tendsto hwc hsf.1 hCc hCH hsf.2 ht2s ht2T
    filter_upwards [hev1, hev2] with n h1 h2
    have h1' : t1 n < S₀ := lt_of_le_of_lt (ht12 n) h1
    have hc1 : ((dyadicQ (n, ⌈(2 : ℝ≥0) ^ n * s ω⌉₊ + 1) : ℚ≥0) : ℝ≥0) = t1 n := by rw [coe_dyadicQ]
    have hc2 : ((dyadicQ (n, ⌈(2 : ℝ≥0) ^ n * s ω⌉₊ + 2) : ℚ≥0) : ℝ≥0) = t2 n := by rw [coe_dyadicQ]
    refine mem_iUnion.2 ⟨⌈(2 : ℝ≥0) ^ n * s ω⌉₊, ⟨hωT.1, rfl⟩, ?_, ?_⟩
    · show ((dyadicQ (n, ⌈(2 : ℝ≥0) ^ n * s ω⌉₊ + 1) : ℝ≥0) : WithTop ℝ≥0) <
        (refVer xL xR r Gr Wr VLr VRr ζr ω).1
      rw [hve, show (refRecHist xL xR r Gr Wr VLr VRr ζr ω).1 = capStop r Gr ζr Wr ω from rfl, hc1, hS]
      exact WithTop.coe_lt_coe.2 h1'
    · have htζ : ((t2 n : ℝ≥0) : ℝ≥0∞) < ζr ω := lt_trans (by exact_mod_cast h1) hSζ
      have htS : ((dyadicQ (n, ⌈(2 : ℝ≥0) ^ n * s ω⌉₊ + 2) : ℝ≥0) : WithTop ℝ≥0) < capStop r Gr ζr Wr ω := by
        rw [hc2, hS]
        exact WithTop.coe_lt_coe.2 h1
      show Disjoint C (tsHull (truncH (dyadicQ (n, ⌈(2 : ℝ≥0) ^ n * s ω⌉₊ + 2))
        (refVer xL xR r Gr Wr VLr VRr ζr ω)))
      rw [hve, truncH_refRecHist xL xR htS, hc2]
      exact disjoint_tsHull_tsOf (continuousOn_refState xL xR (hG ω hω) htζ) htζ hwc (fun _ _ => rfl) hCH h2
  -- dominated convergence on `E`
  have hconvE : ∀ᵐ p ∂E, p.2 ∈ T → ∀ᶠ n in atTop, p.2 ∈ B n := by
    rw [← hsnd] at hconv
    exact ae_of_ae_map measurable_snd.aemeasurable hconv
  have hBm : ∀ n, MeasurableSet (Prod.snd ⁻¹' B n : Set (Ω × Ωr)) := fun n =>
    measurable_snd (MeasurableSet.iUnion fun k => hPm n k)
  have hlim : ∀ g : Ω × Ωr → ℂ, Measurable g → (∀ p, ‖g p‖ ≤ 1) →
      Tendsto (fun n => ∫ p in Prod.snd ⁻¹' B n, g p ∂E) atTop (𝓝 (∫ p in Prod.snd ⁻¹' T, g p ∂E)) := by
    intro g hg hg1
    simp_rw [← integral_indicator (hBm _), ← integral_indicator (measurable_snd hTm)]
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun n => (hg.indicator (hBm n)).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun p => ?_) ?_
    · by_cases hp : p ∈ Prod.snd ⁻¹' B n
      · rw [indicator_of_mem hp]; exact hg1 p
      · rw [indicator_of_notMem hp, norm_zero]; exact zero_le_one
    · filter_upwards [hconvE] with p hp
      by_cases hpT : p.2 ∈ T
      · rw [indicator_of_mem (show p ∈ Prod.snd ⁻¹' T from hpT)]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hp hpT] with n hn
        rw [indicator_of_mem (show p ∈ Prod.snd ⁻¹' B n from hn)]
      · rw [indicator_of_notMem (show p ∉ Prod.snd ⁻¹' T from hpT)]
        refine tendsto_const_nhds.congr fun n => ?_
        rw [indicator_of_notMem (show p ∉ Prod.snd ⁻¹' B n from fun hn => hpT (hBT n hn))]
  have h1 := hlim _ (hcexp (lapTest U f + Ξ)) fun p => (Complex.norm_exp_I_mul_ofReal _).le
  have h2 := (hlim _ (hcexp Ξ) fun p => (Complex.norm_exp_I_mul_ofReal _).le).const_mul c
  exact tendsto_nhds_unique h1 (h2.congr fun n => (hBint n).symm)

end Main

end LocalExt

end InteractingSLE
