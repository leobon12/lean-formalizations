/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtLLocRef

/-!
# Aux. lemma 54, (Loc): locality on the extension from the post-stop identity

Packet PROVE-LOCEXT-L. On a record extension `E` of a stopped seed coupling by a time-adapted reference with a safe
locality family (`IsStdReferenceLS`), the centred original field `X = h(p.1) − 𝔥₀` is **family-local** for the reference
family read through `Prod.snd` (`Coupling.IsFamilyLocal`), provided the projection identity holds at each member on the
events after the reference's local stop (`ExtPostLocalStatement`, the remaining named input: "the new future kernel does
not read the old germ … successive local-set decompositions make the union of the old hull and each relative future hull
local"). Before the local stop the identity is proved (`setIntegral_lapTest_preStop_of_tag`). Hence every hull `K_τ` at a
stopping time of the extension's driving filtration is a local set of the original field
(`Coupling.isLocalSet_hull_of_isFamilyLocal`): PROVE-LOCEXT-H's (Loc) for these references.

## Main results

* `ExtPostLocalStatement κ`: the named input (post-stop identity at a safe member);
* **`isLocalSet_extension_of_post`**: (Loc) on a record extension;
* **`hasReferenceExtension_of_recordLaw_LS`**, **`stoppedSeedExtensionStatement_of_refLS`**: Aux. lemma 54 for stopped seed
  couplings from `StdTwoSeedReferenceLSStatement κ` and `ExtPostLocalStatement κ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper TopologicalSpace
open scoped NNReal ENNReal RealInnerProductSpace

universe u

namespace InteractingSLE

namespace LocalExt

open Sec7 Sec4 LQGMetric LQGMetric.MarkovZB Coupling LocalSets Ito QuantumZipper.K3 QuantumZipper.Thm11Asm
open SupercriticalConformalCovariance.GM24 (smoothDist)

/-! ### The named input: the identity after the local stop -/

/-- **Named input (Loc-post)**: on a record extension of a stopped seed coupling by a time-adapted reference, at a stop
`s` of the reference's usual augmentation that is safe for a compact `C ⊇ U` and at which the reference's centred field
satisfies the projection identity on every event of `𝓖_s`, the original centred field satisfies the projection identity
on the events of `𝓖_s` after the reference's capped local stop. -/
def ExtPostLocalStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (r : ℝ),
    IsOrderedForceWord xL xR → 0 < r → -2 < seedSumL xL ρL → -2 < seedSumR xR ρR →
    ∀ {Ω : Type u} {_ : MeasurableSpace Ω} (Q : Measure Ω) [IsProbabilityMeasure Q] (W : ℝ≥0 → Ω → ℝ)
      (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (S : Ω → WithTop ℝ≥0)
      (h : Ω → DistOn upperHalfPlaneOpens),
      IsStoppedSeedCoupling κ xL xR ρL ρR r Q W VL VR S h →
    ∀ {Ωr : Type u} {_ : MeasurableSpace Ωr} (Pr : Measure Ωr)
      (𝓕r : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ωr)) (Wr : ℝ≥0 → Ωr → ℝ) (VLr VRr : Fin 1 → ℝ≥0 → Ωr → ℝ)
      (Br : ℝ≥0 → Ωr → ℝ) (ζr : Ωr → ℝ≥0∞) (hr : Ωr → DistOn upperHalfPlaneOpens),
      IsStdReferenceL κ (seedSumL xL ρL) (seedSumR xR ρR) xL xR Pr 𝓕r Wr VLr VRr Br ζr hr →
    ∀ Gr : Set Ωr, MeasurableSet Gr → Pr Grᶜ = 0 →
      (∀ ωr ∈ Gr, IsGoodPath κ LP.twoSeedXL LP.twoSeedXR (fun _ => seedSumL xL ρL) (fun _ => seedSumR xR ρR)
        Wr VLr VRr Br ζr ωr) →
    ∀ E : Measure (Ω × Ωr),
      IsRecordExtension Q Pr h (stRecHist xL xR W VL VR S) hr (refRecHist xL xR r Gr Wr VLr VRr ζr) E →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ (fun _ : Fin 1 => seedSumL xL ρL)
        (fun _ : Fin 1 => seedSumR xR ρR) LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀ →
    ∀ (C : Set ℂ), IsCompact C → C ⊆ H → ∀ (U : Opens ℂ), (U : Set ℂ) ⊆ C →
    ∀ (s : Ωr → ℝ≥0) (hs : IsStoppingTime (usualAugmentation 𝓕r Pr) fun ω => (s ω : WithTop ℝ≥0)),
      (∀ᵐ ω ∂Pr, (s ω : ℝ≥0∞) < ζr ω ∧ Disjoint C (fwdHull (fun r : ℝ => Wr r.toNNReal ω) (s ω))) →
      (∀ (f : zsSub (U : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) (D : Set Ωr), MeasurableSet[hs.measurableSpace] D →
        ∫ ω in D, Complex.exp (Complex.I * ((hr ω - smoothDist upperHalfPlaneOpens u₀) (lapTest U f + Ξ) : ℂ)) ∂Pr =
          Coupling.projFactor U f Ξ *
            ∫ ω in D, Complex.exp (Complex.I * ((hr ω - smoothDist upperHalfPlaneOpens u₀) Ξ : ℂ)) ∂Pr) →
    ∀ (f : zsSub (U : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) (A₀ : Set Ωr), MeasurableSet[hs.measurableSpace] A₀ →
      ∫ p in Prod.snd ⁻¹' (A₀ ∩ {ω | capStop r Gr ζr Wr ω ≤ (s ω : WithTop ℝ≥0)}),
          Complex.exp (Complex.I * ((h p.1 - smoothDist upperHalfPlaneOpens u₀) (lapTest U f + Ξ) : ℂ)) ∂E =
        Coupling.projFactor U f Ξ * ∫ p in Prod.snd ⁻¹' (A₀ ∩ {ω | capStop r Gr ζr Wr ω ≤ (s ω : WithTop ℝ≥0)}),
          Complex.exp (Complex.I * ((h p.1 - smoothDist upperHalfPlaneOpens u₀) Ξ : ℂ)) ∂E

/-! ### Locality on the extension -/

section Loc

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {S : Ω → WithTop ℝ≥0}
  {h : Ω → DistOn upperHalfPlaneOpens}
  {Ωr : Type u} [mΩr : MeasurableSpace Ωr] {Pr : Measure Ωr} {𝓕r : Filtration ℝ≥0 mΩr}
  {Wr : ℝ≥0 → Ωr → ℝ} {VLr VRr : Fin 1 → ℝ≥0 → Ωr → ℝ} {Br : ℝ≥0 → Ωr → ℝ} {ζr : Ωr → ℝ≥0∞}
  {hr' : Ωr → DistOn upperHalfPlaneOpens} {Gr : Set Ωr}

/-- **(Loc) on a record extension** of a stopped seed coupling by a time-adapted reference with a safe locality family,
given the post-stop identity: every hull `K_τ` at a stopping time `τ < ζ̂` of the extension's driving filtration is a
local set of the original field. -/
theorem isLocalSet_extension_of_post [IsProbabilityMeasure Q] (hF : IsOrderedForceWord xL xR)
    (hr : 0 < r) (hL : -2 < seedSumL xL ρL) (hR : -2 < seedSumR xR ρR)
    (hc : IsStoppedSeedCoupling κ xL xR ρL ρR r Q W VL VR S h)
    (href : IsStdReferenceLS κ (seedSumL xL ρL) (seedSumR xR ρR) xL xR Pr 𝓕r Wr VLr VRr Br ζr hr')
    (hGm : MeasurableSet Gr) (hG0 : Pr Grᶜ = 0)
    (hG : ∀ ω ∈ Gr, IsGoodPath κ LP.twoSeedXL LP.twoSeedXR (fun _ => seedSumL xL ρL) (fun _ => seedSumR xR ρR)
      Wr VLr VRr Br ζr ω)
    {E : Measure (Ω × Ωr)}
    (hE : IsRecordExtension Q Pr h (stRecHist xL xR W VL VR S) hr' (refRecHist xL xR r Gr Wr VLr VRr ζr) E)
    (hPost : ExtPostLocalStatement.{u} κ)
    (hX : IsMeasurableKilledDriving (fun t (p : Ω × Ωr) => Wr t p.2) (fun i t p => VLr i t p.2)
      (fun i t p => VRr i t p.2) (fun p => ζr p.2)) {τ : Ω × Ωr → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration E hX) τ) (hτζ : ∀ᵐ p ∂E, (τ p : ℝ≥0∞) < ζr p.2) :
    IsLocalSet (fun p => fwdHull (fun s : ℝ => Wr s.toNNReal p.2) ((τ p).untopD 0 : ℝ≥0)) (fun p => h p.1) E := by
  classical
  obtain ⟨⟨⟨hSB, hPr, hC, -, -, -⟩, hTAGr⟩, hfamLS⟩ := id href
  have : IsProbabilityMeasure Pr := hPr
  have hEp : IsProbabilityMeasure E := isProbabilityMeasure_of_map_fst hE.1
  have hfst : E.map Prod.fst = Q := hE.1
  have hsnd : E.map Prod.snd = Pr := hE.2.1
  have hTAG : IsTimeAdaptedRef xL xR r Gr Pr 𝓕r Wr VLr VRr ζr := href.1.isTimeAdaptedRef
  obtain ⟨-, -, -, -, -, -, -, hhm, hgff, -⟩ := id hc
  -- the time-`0` mean
  set u₀ : ℂ → ℝ := Impl.forceExt κ (weightWord (fun _ : Fin 1 => seedSumL xL ρL) (fun _ : Fin 1 => seedSumR xR ρR))
    LP.twoSeedXL LP.twoSeedXR with hu₀def
  have hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ (fun _ : Fin 1 => seedSumL xL ρL)
      (fun _ : Fin 1 => seedSumR xR ρR) LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀ :=
    Impl.isBoundedHarmonicExtension_forceExt κ _ _ _
  have hu₀c : ContinuousOn u₀ H := fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt
  have hT₀ : IsHarmonicDistOn (smoothDist upperHalfPlaneOpens u₀) H := isHarmonicDistOn_smoothDist_of hu₀
  -- the centred field is a zero-boundary GFF on `E`
  have hhE : Measurable fun p : Ω × Ωr => h p.1 := hhm.comp measurable_fst
  have hZ : IsZeroBoundaryGFF upperHalfPlaneOpens
      (fun p : Ω × Ωr => h p.1 - smoothDist upperHalfPlaneOpens u₀) E := by
    have h1 := hgff u₀ hu₀
    rw [← hfst] at h1
    exact isZeroBoundaryGFF_sub_smoothDist hhE hu₀c (Restart.isZBGFFProcess_comp measurable_fst h1)
  -- the evolution on `E`
  have hE' := Coupling.IsIntegratedSLEEvolution.comap measurable_snd hsnd hC.1
  -- the family on `E`
  obtain ⟨ι, hι, U, C, s, hs, hCs, hsafe, hid, hexh⟩ := hfamLS u₀ hu₀
  obtain ⟨hXr, -⟩ := hC.2.2.2
  have hŜm : Measurable (capStop r Gr ζr Wr) := (isStoppingTime_capStop hXr hGm hG0 hG r).measurable'
  have hfamE : IsFamilyLocal E (filtrationComap 𝓕r measurable_snd) (fun t (p : Ω × Ωr) => Wr t p.2)
      (fun p => ζr p.2) (fun p => h p.1 - smoothDist upperHalfPlaneOpens u₀) := by
    refine ⟨ι, hι, U, fun i p => s i p.2, fun i => isStoppingTime_comap measurable_snd hsnd (hs i),
      fun i => (hCs i).2.2.trans (hCs i).2.1, fun i f Ξ D hD => ?_, ?_⟩
    · obtain ⟨D₀, hD₀, hDD₀⟩ := exists_comap_ae_eq_of_measurableSet_stopped measurable_snd hsnd (hs i) hD
      rw [setIntegral_congr_set hDD₀, setIntegral_congr_set hDD₀]
      have hD₀m : MeasurableSet D₀ := (hs i).measurableSpace_le D₀ hD₀
      have hsm : Measurable fun ω => (s i ω : WithTop ℝ≥0) := (hs i).measurable'
      set Pre : Set Ωr := D₀ ∩ {ω | (s i ω : WithTop ℝ≥0) < capStop r Gr ζr Wr ω} with hPre
      set Post : Set Ωr := D₀ ∩ {ω | capStop r Gr ζr Wr ω ≤ (s i ω : WithTop ℝ≥0)} with hPost'
      have hPrem : MeasurableSet Pre := hD₀m.inter (measurableSet_lt hsm hŜm)
      have hPostm : MeasurableSet Post := hD₀m.inter (measurableSet_le hŜm hsm)
      have hunion : (Prod.snd ⁻¹' D₀ : Set (Ω × Ωr)) = Prod.snd ⁻¹' Pre ∪ Prod.snd ⁻¹' Post := by
        ext p
        simp only [hPre, hPost', mem_preimage, mem_union, mem_inter_iff, mem_ofPred_eq]
        constructor
        · intro hp
          rcases lt_or_ge (s i p.2 : WithTop ℝ≥0) (capStop r Gr ζr Wr p.2) with h' | h'
          · exact Or.inl ⟨hp, h'⟩
          · exact Or.inr ⟨hp, h'⟩
        · rintro (⟨hp, -⟩ | ⟨hp, -⟩) <;> exact hp
      have hdisj : Disjoint (Prod.snd ⁻¹' Pre : Set (Ω × Ωr)) (Prod.snd ⁻¹' Post) := by
        refine Set.disjoint_left.2 fun p hp hp' => ?_
        have h1 : (s i p.2 : WithTop ℝ≥0) < capStop r Gr ζr Wr p.2 := hp.2
        have h2 : capStop r Gr ζr Wr p.2 ≤ (s i p.2 : WithTop ℝ≥0) := hp'.2
        exact absurd h1 (not_lt.2 h2)
      have hcexp : ∀ χ : TestOn upperHalfPlaneOpens,
          Integrable (fun p : Ω × Ωr => Complex.exp (Complex.I * ((h p.1 - smoothDist upperHalfPlaneOpens u₀) χ : ℂ)))
            E := fun χ =>
        Integrable.of_bound (Complex.continuous_exp.measurable.comp (measurable_const.mul (Complex.measurable_ofReal.comp
          ((measurable_distOn_apply χ).comp ((WholeField.measurable_sub_dist _).comp hhE))))).aestronglyMeasurable 1
          (Eventually.of_forall fun p => (Complex.norm_exp_I_mul_ofReal _).le)
      show ∫ p in Prod.snd ⁻¹' D₀,
          Complex.exp (Complex.I * ((h p.1 - smoothDist upperHalfPlaneOpens u₀) (lapTest (U i) f + Ξ) : ℂ)) ∂E =
        Coupling.projFactor (U i) f Ξ * ∫ p in Prod.snd ⁻¹' D₀,
          Complex.exp (Complex.I * ((h p.1 - smoothDist upperHalfPlaneOpens u₀) Ξ : ℂ)) ∂E
      rw [hunion, setIntegral_union hdisj (measurable_snd hPostm) (hcexp _).integrableOn (hcexp _).integrableOn,
        setIntegral_union hdisj (measurable_snd hPostm) (hcexp _).integrableOn (hcexp _).integrableOn, mul_add]
      congr 1
      · exact setIntegral_lapTest_preStop_of_tag hr hL hR hc hC hGm hG0 hG hTAG hE hT₀ (hCs i).1 (hCs i).2.1
          (hCs i).2.2 (s i) (hs i) (hsafe i) f Ξ D₀ hD₀
      · exact hPost xL xR ρL ρR r hF hr hL hR Q W VL VR S h hc Pr 𝓕r Wr VLr VRr Br ζr hr' href.1 Gr hGm hG0 hG E hE
          u₀ hu₀ (C i) (hCs i).1 (hCs i).2.1 (U i) (hCs i).2.2 (s i) (hs i) (hsafe i) (hid i) f Ξ D₀ hD₀
    · rw [← hsnd] at hexh
      exact ae_of_ae_map measurable_snd.aemeasurable hexh
  have hl := isLocalSet_hull_of_isFamilyLocal hE' hX hZ hfamE hτ hτζ
  have hl' := IsLocalSet.add_dist hl hT₀
  have e : (fun p : Ω × Ωr => h p.1 - smoothDist upperHalfPlaneOpens u₀ + smoothDist upperHalfPlaneOpens u₀) =
      fun p => h p.1 := funext fun p => sub_add_cancel _ _
  rw [e] at hl'
  exact hl'

end Loc

/-- **Named input: a time-adapted standard reference with a safe locality family exists** for the seed pattern of every
word and every pair of admissible seed weights (an empty seed side has weight `0`). -/
def StdTwoSeedReferenceLSStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (rL rR : ℝ), -2 < rL → -2 < rR →
    ((¬ ∃ i, xL i = 0) → rL = 0) → ((¬ ∃ j, xR j = 0) → rR = 0) →
    ∃ (Ωr : Type u) (_ : MeasurableSpace Ωr) (Pr : Measure Ωr) (𝓕r : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ωr))
      (Wr : ℝ≥0 → Ωr → ℝ) (VLr VRr : Fin 1 → ℝ≥0 → Ωr → ℝ) (Br : ℝ≥0 → Ωr → ℝ) (ζr : Ωr → ℝ≥0∞)
      (hr : Ωr → DistOn upperHalfPlaneOpens), IsStdReferenceLS κ rL rR xL xR Pr 𝓕r Wr VLr VRr Br ζr hr

/-! ### The extension and Aux. lemma 54 -/

section Extension

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} [IsProbabilityMeasure Q] {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {S : Ω → WithTop ℝ≥0}
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Aux. lemma 54 from a time-adapted standard reference with a safe locality family and the same record law**
((K-pre) proved; (Loc) from the post-stop identity `ExtPostLocalStatement`). PROVE-LOCEXT-H's `hasReferenceExtension_of_recordLaw` with the reference time-adapted. -/
theorem hasReferenceExtension_of_recordLaw_LS (hκ : 0 < κ) (hF : IsOrderedForceWord xL xR) (hr : 0 < r)
    (hL : -2 < seedSumL xL ρL) (hR : -2 < seedSumR xR ρR)
    (hc : IsStoppedSeedCoupling κ xL xR ρL ρR r Q W VL VR S h)
    {Ωr : Type u} [mΩr : MeasurableSpace Ωr] {Pr : Measure Ωr} {𝓕r : Filtration ℝ≥0 mΩr}
    {Wr : ℝ≥0 → Ωr → ℝ} {VLr VRr : Fin 1 → ℝ≥0 → Ωr → ℝ} {Br : ℝ≥0 → Ωr → ℝ} {ζr : Ωr → ℝ≥0∞}
    {hr' : Ωr → DistOn upperHalfPlaneOpens}
    (href : IsStdReferenceLS κ (seedSumL xL ρL) (seedSumR xR ρR) xL xR Pr 𝓕r Wr VLr VRr Br ζr hr')
    {Gr : Set Ωr} (hGm : MeasurableSet Gr) (hG0 : Pr Grᶜ = 0)
    (hG : ∀ ω ∈ Gr, IsGoodPath κ LP.twoSeedXL LP.twoSeedXR (fun _ => seedSumL xL ρL) (fun _ => seedSumR xR ρR)
      Wr VLr VRr Br ζr ω)
    {Rr : Ωr → RecSp} (hRrm : Measurable Rr)
    (hRr : ∀ᵐ ω ∂Pr, Rr ω = recOf (hr' ω) (refRecHist xL xR r Gr Wr VLr VRr ζr ω))
    (hlaw : Q.map (fun ω => recOf (h ω) (stRecHist xL xR W VL VR S ω)) = Pr.map Rr)
    (hPost : ExtPostLocalStatement.{u} κ) :
    HasReferenceExtension.{u} κ (seedSumL xL ρL) (seedSumR xR ρR) r Q h
      (fun ω => twoSeedProj xL xR (stoppedHistory (drivingState W VL VR) S ω)) := by
  classical
  obtain ⟨⟨⟨hSB, hPr, hC, hfam, -⟩, -⟩, -⟩ := id href
  have hTAG := href.1.isTimeAdaptedRef (r := r) (Gr := Gr)
  have : StandardBorelSpace Ωr := hSB
  have : IsProbabilityMeasure Pr := hPr
  have : Nonempty Ωr := nonempty_of_isProbabilityMeasure Pr
  have hRh := hc.measurable_stRecHist
  obtain ⟨𝓓, hS, -, -, -, -, -, hhm, hgff, -⟩ := id hc
  have hRecm : Measurable fun ω => recOf (h ω) (stRecHist xL xR W VL VR S ω) :=
    measurable_recOf.comp (hhm.prodMk hRh)
  obtain ⟨κ₀, hκ₀, hfst, hpair⟩ := Sec7.aux54_exists_extension (Fr := id) hRrm measurable_id hRecm hlaw
  set E : Measure (Ω × Ωr) := Q ⊗ₘ κ₀.comap (fun ω => recOf (h ω) (stRecHist xL xR W VL VR S ω)) hRecm
    with hEdef
  have hpm : Measurable fun p : Ω × Ωr => (recOf (h p.1) (stRecHist xL xR W VL VR S p.1), p.2) :=
    (hRecm.comp measurable_fst).prodMk measurable_snd
  have hsnd : E.map Prod.snd = Pr := by
    have e : (Prod.snd : Ω × Ωr → Ωr) =
        Prod.snd ∘ fun p : Ω × Ωr => (recOf (h p.1) (stRecHist xL xR W VL VR S p.1), p.2) := rfl
    rw [e, ← Measure.map_map measurable_snd hpm, hpair, Measure.map_map measurable_snd (hRrm.prodMk measurable_id)]
    exact Measure.map_id
  -- the two records agree almost surely on `E`
  have hRrE : ∀ᵐ p ∂E, Rr p.2 = recOf (hr' p.2) (refRecHist xL xR r Gr Wr VLr VRr ζr p.2) := by
    rw [← hsnd] at hRr
    exact ae_of_ae_map measurable_snd.aemeasurable hRr
  have hhist0 : ∀ᵐ p ∂E, stRecHist xL xR W VL VR S p.1 = (Rr p.2).1 := by
    have hD : MeasurableSet {q : RecSp × Ωr | q.1.1 = (Rr q.2).1} :=
      measurableSet_eq_twoSeedHist (measurable_fst.comp measurable_fst)
        (measurable_fst.comp (hRrm.comp measurable_snd))
    have h1 : ∀ᵐ q ∂(Pr.map fun ω => (Rr ω, id ω)), q.1.1 = (Rr q.2).1 :=
      (ae_map_iff (hRrm.prodMk measurable_id).aemeasurable hD).2 (Eventually.of_forall fun ω => rfl)
    rw [← hpair] at h1
    exact (ae_map_iff hpm.aemeasurable hD).1 h1
  have hfield0 : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ p ∂E,
      fieldRec (h p.1) (stRecHist xL xR W VL VR S p.1) ψ = (Rr p.2).2 ψ := fun ψ => by
    have hD : MeasurableSet {q : RecSp × Ωr | q.1.2 ψ = (Rr q.2).2 ψ} :=
      measurableSet_eq_fun ((measurable_pi_apply ψ).comp (measurable_snd.comp measurable_fst))
        ((measurable_pi_apply ψ).comp (measurable_snd.comp (hRrm.comp measurable_snd)))
    have h1 : ∀ᵐ q ∂(Pr.map fun ω => (Rr ω, id ω)), q.1.2 ψ = (Rr q.2).2 ψ :=
      (ae_map_iff (hRrm.prodMk measurable_id).aemeasurable hD).2 (Eventually.of_forall fun ω => rfl)
    rw [← hpair] at h1
    exact (ae_map_iff hpm.aemeasurable hD).1 h1
  have hhist : ∀ᵐ p ∂E, stRecHist xL xR W VL VR S p.1 = refRecHist xL xR r Gr Wr VLr VRr ζr p.2 := by
    filter_upwards [hhist0, hRrE] with p h1 h2
    rw [h1, h2]
    rfl
  have hfield : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ p ∂E,
      fieldRec (h p.1) (stRecHist xL xR W VL VR S p.1) ψ =
        fieldRec (hr' p.2) (refRecHist xL xR r Gr Wr VLr VRr ζr p.2) ψ := fun ψ => by
    filter_upwards [hfield0 ψ, hRrE] with p h1 h2
    rw [h1, h2]
    rfl
  have hrecext : IsRecordExtension Q Pr h (stRecHist xL xR W VL VR S) hr'
      (refRecHist xL xR r Gr Wr VLr VRr ζr) E :=
    ⟨hfst, hsnd, hhist, hfield, hRecm, κ₀, hκ₀, rfl⟩
  -- the evolution and the field at time `0`
  have hE' := Coupling.IsIntegratedSLEEvolution.comap measurable_snd hsnd hC.1
  have hgff' : ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension
      (forceBoundaryData κ (fun _ : Fin 1 => seedSumL xL ρL) (fun _ : Fin 1 => seedSumR xR ρR) LP.twoSeedXL
        LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀ →
      IsZBGFFProcess upperHalfPlaneOpens (fun φ (p : Ω × Ωr) => h p.1 φ - ∫ z, u₀ z * φ z) E := fun u₀ hu₀ => by
    have h1 := hgff u₀ hu₀
    rw [← hfst] at h1
    exact Restart.isZBGFFProcess_comp measurable_fst h1
  -- the family of the reference, pulled back
  obtain ⟨u, hu, ι, hι, U, s, hs, hsafe, hsamp, hexh⟩ := hfam
  obtain ⟨hXr, -⟩ := hC.2.2.2
  have hcapm : Measurable (capStop r Gr ζr Wr) := (isStoppingTime_capStop hXr hGm hG0 hG r).measurable'
  have hsafeE : ∀ i, ∀ᵐ p ∂E, ((s i p.2 : ℝ≥0) : ℝ≥0∞) < ζr p.2 ∧
      Disjoint (U i) (fwdHull (fun r : ℝ => Wr r.toNNReal p.2) (s i p.2)) := fun i => by
    have h1 := hsafe i
    rw [← hsnd] at h1
    exact ae_of_ae_map measurable_snd.aemeasurable h1
  have hGE : ∀ᵐ p ∂E, p.2 ∈ Gr := by
    have h1 : ∀ᵐ ω ∂Pr, ω ∈ Gr := ae_iff.2 (by exact hG0)
    rw [← hsnd] at h1
    exact ae_of_ae_map measurable_snd.aemeasurable h1
  have hexhE : ∀ᵐ p ∂E, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζr p.2 → ∀ K : Set ℂ, IsCompact K → K ⊆ H →
      Disjoint K (fwdHull (fun r : ℝ => Wr r.toNNReal p.2) t) → ∃ i, K ⊆ U i ∧ t ≤ s i p.2 := by
    have h1 := hexh
    rw [← hsnd] at h1
    exact ae_of_ae_map measurable_snd.aemeasurable h1
  have hsampE : ∀ i, IsSampledAt κ (fun t (p : Ω × Ωr) => Wr t p.2) (fun p => u p.2) E (fun p => h p.1) (U i)
      (isStoppingTime_comap measurable_snd hsnd (hs i)) := fun i => by
    refine isSampledAt_comap measurable_snd hsnd (hs i) fun ψ hψ A₀ hA₀ => ?_
    have hA₀m : MeasurableSet A₀ := (hs i).measurableSpace_le A₀ hA₀
    have hsm : Measurable fun ω => ((s i ω : ℝ≥0) : WithTop ℝ≥0) := (hs i).measurable'
    set C : Set Ωr := {ω | ((s i ω : ℝ≥0) : WithTop ℝ≥0) < capStop r Gr ζr Wr ω} with hCdef
    have hCm : MeasurableSet C := measurableSet_lt hsm hcapm
    have hmap : ∀ g : Ωr → ℂ, AEStronglyMeasurable g Pr → ∀ B : Set Ωr, MeasurableSet B →
        ∫ p in Prod.snd ⁻¹' B, g p.2 ∂E = ∫ ω in B, g ω ∂Pr := fun g hg B hB => by
      rw [← hsnd] at hg ⊢
      exact (setIntegral_map hB hg measurable_snd.aemeasurable).symm
    have hgm : Measurable fun ω => Complex.exp (Complex.I * (hr' ω ψ : ℂ)) :=
      Complex.continuous_exp.measurable.comp (measurable_const.mul
        (Complex.measurable_ofReal.comp ((measurable_distOn_apply ψ).comp hC.2.1)))
    have hfm : Measurable fun p : Ω × Ωr => Complex.exp (Complex.I * (h p.1 ψ : ℂ)) :=
      Complex.continuous_exp.measurable.comp (measurable_const.mul
        (Complex.measurable_ofReal.comp ((measurable_distOn_apply ψ).comp (hhm.comp measurable_fst))))
    have hcf : AEStronglyMeasurable (cfAt κ Wr u ψ 1 (s i)) Pr :=
      aestronglyMeasurable_cfAt_of_stoppingTime hC.1 hκ u hu ψ (hs i)
        (by filter_upwards [hsafe i] with ω hω using ⟨hω.1, hω.2.mono_left hψ⟩) 1
    -- the right-hand side is the reference field's integral
    rw [hmap _ hcf A₀ hA₀m, ← hsamp i ψ hψ A₀ hA₀, ← hmap _ hgm.aestronglyMeasurable A₀ hA₀m]
    -- split at the reference's local stop
    have hint : ∀ f : Ω × Ωr → ℂ, Measurable f → (∀ p, ‖f p‖ ≤ 1) → ∀ B : Set Ωr, MeasurableSet B →
        ∫ p in Prod.snd ⁻¹' B, f p ∂E =
          (∫ p in Prod.snd ⁻¹' (B ∩ C), f p ∂E) + ∫ p in Prod.snd ⁻¹' (B \ C), f p ∂E := by
      intro f hf hf1 B hB
      have hfi : Integrable f E := Integrable.of_bound hf.aestronglyMeasurable 1 (Eventually.of_forall hf1)
      rw [← setIntegral_union (Disjoint.preimage _ (disjoint_sdiff_inter.symm.mono_left
          (by rw [inter_comm]))) (measurable_snd (hB.diff hCm)) hfi.integrableOn hfi.integrableOn,
        ← preimage_union, inter_union_sdiff]
    have hf1 : ∀ p : Ω × Ωr, ‖Complex.exp (Complex.I * (h p.1 ψ : ℂ))‖ ≤ 1 := fun p =>
      (Complex.norm_exp_I_mul_ofReal _).le
    have hg1 : ∀ p : Ω × Ωr, ‖Complex.exp (Complex.I * (hr' p.2 ψ : ℂ))‖ ≤ 1 := fun p =>
      (Complex.norm_exp_I_mul_ofReal _).le
    rw [hint _ hfm hf1 A₀ hA₀m, hint (fun p => Complex.exp (Complex.I * (hr' p.2 ψ : ℂ))) (hgm.comp measurable_snd) hg1
      A₀ hA₀m]
    congr 1
    · -- (K-pre)
      exact setIntegral_preStop_eq_of_tag hr hL hR hc hC hGm hG0 hG hTAG hrecext (U i) (s i) (hs i) (hsafe i) ψ hψ
        A₀ hA₀
    · -- (K-post): after the local stop the two fields agree on `ψ`
      refine setIntegral_congr_ae (measurable_snd (hA₀m.diff hCm)) ?_
      filter_upwards [hhist, hfield ψ, hsafeE i, hGE] with p h1 h2 h3 h4 hp
      have hle : capStop r Gr ζr Wr p.2 ≤ ((s i p.2 : ℝ≥0) : WithTop ℝ≥0) := not_lt.1 hp.2
      have hdis : Disjoint (tsupport ψ) (tsHull (refRecHist xL xR r Gr Wr VLr VRr ζr p.2)) :=
        disjoint_tsHull_refRecHist xL xR hL hR hr hG h4 (tsupport_subset_H ψ) hle (h3.2.mono_left hψ)
      have e1 : fieldRec (hr' p.2) (refRecHist xL xR r Gr Wr VLr VRr ζr p.2) ψ = hr' p.2 ψ :=
        fieldRec_of_disjoint hdis
      have e2 : fieldRec (h p.1) (stRecHist xL xR W VL VR S p.1) ψ = h p.1 ψ :=
        fieldRec_of_disjoint (by rw [h1]; exact hdis)
      show Complex.exp (Complex.I * (h p.1 ψ : ℂ)) = Complex.exp (Complex.I * (hr' p.2 ψ : ℂ))
      rw [← e2, h2, e1]
  have hfamE : IsFamilySampled κ (fun _ : Fin 1 => seedSumL xL ρL) (fun _ : Fin 1 => seedSumR xR ρR) E
      (filtrationComap 𝓕r measurable_snd) (fun t (p : Ω × Ωr) => Wr t p.2) (fun i t p => VLr i t p.2)
      (fun i t p => VRr i t p.2) (fun p => ζr p.2) (fun p => h p.1) :=
    ⟨fun p => u p.2, fun p t => hu p.2 t, ι, hι, U, fun i p => s i p.2,
      fun i => isStoppingTime_comap measurable_snd hsnd (hs i), hsafeE, hsampE, hexhE⟩
  have hcoupE := Coupling.isOptionalHullCoupling_of_isFamilySampled hE' hκ (hhm.comp measurable_fst) hgff' hfamE
    fun hX τ hτ hτζ => isLocalSet_extension_of_post hF hr hL hR hc href hGm hG0 hG hrecext hPost hX hτ hτζ
  -- the good event and the recovery of the stopped history
  have hG'0 : E (Prod.snd ⁻¹' Gr)ᶜ = 0 := by
    rw [← preimage_compl, ← Measure.map_apply measurable_snd hGm.compl, hsnd]
    exact hG0
  have hQE : ∀ᵐ p ∂E, stRecHist xL xR W VL VR S p.1 =
      twoSeedProj xL xR (stoppedHistory (drivingState W VL VR) S p.1) := by
    have h1 := hc.ae_stRecHist_eq hr
    rw [← hfst] at h1
    exact ae_of_ae_map measurable_fst.aemeasurable h1
  refine ⟨id, measurable_id, Ωr, mΩr, E, inferInstance, filtrationComap 𝓕r measurable_snd,
    fun t p => Wr t p.2, fun i t p => VLr i t p.2, fun i t p => VRr i t p.2, fun t p => Br t p.2, fun p => ζr p.2,
    hfst, hcoupE, Prod.snd ⁻¹' Gr, measurable_snd hGm, hG'0, fun p hp => hG p.2 hp,
    fun q => seedProj xL xR q.2, (measurable_seedProj xL xR).comp measurable_snd, ?_⟩
  filter_upwards [hQE, hhist] with p h1 h2
  rw [← h1, h2]
  rfl

end Extension

/-- **Aux. lemma 54 for stopped seed couplings** (`StoppedSeedExtensionStatement κ`) from a time-adapted standard
reference for every seed pattern and (Loc) on the extension; (U) is PROVE-LOCEXT-J's `stoppedTwoSeedLawStatement` and
(K-pre) is `setIntegral_preStop_eq_of_tag`. -/
theorem stoppedSeedExtensionStatement_of_refLS {κ : ℝ} (hκ : 0 < κ) (hRef : StdTwoSeedReferenceLSStatement.{u} κ)
    (hPost : ExtPostLocalStatement.{u} κ) : StoppedSeedExtensionStatement.{u} κ := by
  intro nL nR xL xR ρL ρR r hF hr hL hR Ω mΩ Q hQ W VL VR S h hc
  obtain ⟨Ωr, mΩr, Pr, 𝓕r, Wr, VLr, VRr, Br, ζr, hr', href⟩ :=
    hRef xL xR _ _ hL hR seedSumL_eq_zero seedSumR_eq_zero
  obtain ⟨⟨⟨-, hPr, hC, -, -⟩, -⟩, -⟩ := id href
  have : IsProbabilityMeasure Pr := hPr
  obtain ⟨Gr, hGm, hG0, hG⟩ := exists_goodEvent hC.1 hκ
  have hlawU := stoppedTwoSeedLawStatement hκ xL xR ρL ρR r hF hr hL hR Q W VL VR S h hc Pr 𝓕r Wr VLr VRr Br ζr
    hC.1 Gr hGm hG0 hG
  have hver := ae_refVer_eq xL xR hL hR hr hG0 hG
  obtain ⟨-, -, -, -, -, -, -, hhm, -⟩ := id hc
  have hlaw : Q.map (stRecHist xL xR W VL VR S) = Pr.map (refVer xL xR r Gr Wr VLr VRr ζr) := by
    rw [Measure.map_congr (hc.ae_stRecHist_eq hr), hlawU, (Measure.map_congr hver).symm]
  have hY₂m : Measurable (refVer xL xR r Gr Wr VLr VRr ζr) := measurable_refVer hC hGm hG0 hG
  have hrec : Q.map (fun ω => recOf (h ω) (stRecHist xL xR W VL VR S ω)) =
      Pr.map (fun ω => recOf (hr' ω) (refVer xL xR r Gr Wr VLr VRr ζr ω)) := by
    obtain ⟨m₁, hm₁, hY₁, hk₁⟩ := hc.exists_hasHistKernel hr
    obtain ⟨m₂, hm₂, hY₂, hk₂⟩ := exists_hasHistKernel_ref xL xR hL hR hr hC hGm hG0 hG seedSumL_eq_zero
      seedSumR_eq_zero
    exact map_recOf_eq_of_hasHistKernel (mΩ₁ := mΩ) (mΩ₂ := mΩr) hm₁ hm₂ hY₁ hY₂ hhm hC.2.1
      (measurable_kerFun κ _ _) hk₁ hk₂ hlaw
  exact hasReferenceExtension_of_recordLaw_LS hκ hF hr hL hR hc href hGm hG0 hG
    (Rr := fun ω => recOf (hr' ω) (refVer xL xR r Gr Wr VLr VRr ζr ω))
    (measurable_recOf.comp (hC.2.1.prodMk hY₂m))
    (by filter_upwards [hver] with ω hω; rw [hω]) hrec hPost

/-! ### The reference for every seed pattern -/

/-- **Named input: time-adapted references with a safe locality family for seed patterns with an empty side** (an empty
seed side has weight `0`; with both sides present the reference is `exists_isStdReferenceLS_of_seeds`). What is missing
is the time-adapted generation when a seed side is empty: the reference's weight-`0` seed mark is then not recorded by
the normalized history, and must be shown to be almost surely a Borel function of the driver on `[0, t]` (uniqueness of
the singular flow `v' = 2/(v − w)`, `v₀ = w₀`, and a measurable solution map). -/
def EmptySideReferenceLSStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (rL rR : ℝ), -2 < rL → -2 < rR →
    ((¬ ∃ i, xL i = 0) → rL = 0) → ((¬ ∃ j, xR j = 0) → rR = 0) → ¬ ((∃ i, xL i = 0) ∧ ∃ j, xR j = 0) →
    ∃ (Ωr : Type u) (_ : MeasurableSpace Ωr) (Pr : Measure Ωr) (𝓕r : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ωr))
      (Wr : ℝ≥0 → Ωr → ℝ) (VLr VRr : Fin 1 → ℝ≥0 → Ωr → ℝ) (Br : ℝ≥0 → Ωr → ℝ) (ζr : Ωr → ℝ≥0∞)
      (hr : Ωr → DistOn upperHalfPlaneOpens), IsStdReferenceLS κ rL rR xL xR Pr 𝓕r Wr VLr VRr Br ζr hr

/-- **Time-adapted references with a safe locality family exist for every seed pattern**, given the empty-side case. -/
theorem stdTwoSeedReferenceLSStatement_of_emptySide {κ : ℝ} (hκ : 0 < κ)
    (hZ : EmptySideReferenceLSStatement.{u} κ) : StdTwoSeedReferenceLSStatement.{u} κ := by
  intro nL nR xL xR rL rR hL hR hrL hrR
  by_cases hseeds : (∃ i, xL i = 0) ∧ ∃ j, xR j = 0
  · exact exists_isStdReferenceLS_of_seeds hκ xL xR hseeds rL rR hL hR
  · exact hZ xL xR rL rR hL hR hrL hrR hseeds

/-- **Aux. lemma 54 for stopped seed couplings** (`StoppedSeedExtensionStatement κ`) from the two remaining named inputs:
the post-stop locality identity (`ExtPostLocalStatement κ`) and time-adapted references for seed patterns with an empty
side (`EmptySideReferenceLSStatement κ`). (U), (K-pre), (K-post), the pre-stop locality identity, the record law and
the construction for both seed sides present are proved. -/
theorem stoppedSeedExtensionStatement_of_post {κ : ℝ} (hκ : 0 < κ) (hZ : EmptySideReferenceLSStatement.{u} κ)
    (hPost : ExtPostLocalStatement.{u} κ) : StoppedSeedExtensionStatement.{u} κ :=
  stoppedSeedExtensionStatement_of_refLS hκ (stdTwoSeedReferenceLSStatement_of_emptySide hκ hZ) hPost

end LocalExt

end InteractingSLE
