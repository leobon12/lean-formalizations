/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtLPre
import InteractingSLE.Spec.Sec7.LocalExtJMain

/-!
# Aux. lemma 54 for stopped seed couplings: the extension with (K-pre) proved

Packet PROVE-LOCEXT-L. PROVE-LOCEXT-H's extension `E = Q ⊗ κ₀(record)` is an extended reference pair once the
protected kernel before the local stop (K-pre) and locality (Loc) hold on it. (K-pre) is proved here
(`setIntegral_preStop_eq_of_tag`) for a reference whose usual augmentation is **time-adapted** to its recorded history:

* `fullRefHist`: the reference's (normalized) two-seed history at all rational times;
* **`IsStdReferenceL`**: PROVE-LOCEXT-H's standard reference (`IsStdReference`) whose usual augmentation is generated, up to
  null sets and with time information, by that history: an event of `𝓖_q` is almost surely an event of the history
  truncated at any rational `t > q` (Theorem 1.1's construction on the coordinate filtration has this property, the
  noise being a function of the driving state, `WholeField.IsIntegratedSLEPath.eq_noiseOf`);
* `IsStdReferenceL.isTimeAdaptedRef`: the time-adapted generation by the history at the capped local stop;
* `ExtLocalityLStatement κ`: PROVE-LOCEXT-H's (Loc) for such references (a weaker requirement than `ExtLocalityStatement`);
* `StdTwoSeedReferenceLStatement κ`: such a reference exists for the seed pattern of every word;
* **`hasReferenceExtension_of_recordLaw_L`**: the extension theorem with (K-pre) proved;
* **`stoppedSeedExtensionStatement_of_refL`**: `StoppedSeedExtensionStatement κ` from `StdTwoSeedReferenceLStatement κ` and
  `ExtLocalityLStatement κ` ((U) is PROVE-LOCEXT-J's `stoppedTwoSeedLawStatement`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace LocalExt

open Sec7 Sec4 LQGMetric Coupling

/-! ### Time-adapted standard references -/

section RefL

variable {nL nR : ℕ} {Ωr : Type*} {mΩr : MeasurableSpace Ωr}

/-- **The reference's normalized two-seed history at all rational times** (empty seed sides read the driver). -/
def fullRefHist (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (Wr : ℝ≥0 → Ωr → ℝ) (VLr VRr : Fin 1 → ℝ≥0 → Ωr → ℝ)
    (ω : Ωr) : TwoSeedHist :=
  ((⊤ : WithTop ℝ≥0), fun q => refState xL xR Wr VLr VRr ω (q : ℝ≥0))

theorem truncH_fullRefHist (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (Wr : ℝ≥0 → Ωr → ℝ)
    (VLr VRr : Fin 1 → ℝ≥0 → Ωr → ℝ) (t : ℚ≥0) (ω : Ωr) :
    truncH t (fullRefHist xL xR Wr VLr VRr ω) = tsOf (t : ℝ≥0) (refState xL xR Wr VLr VRr ω) := by
  refine Prod.ext ?_ (funext fun q => ?_)
  · simp only [truncH, fullRefHist, tsOf, min_eq_right le_top]
  · simp only [truncH, fullRefHist, tsOf, coe_min_nnrat]

/-- **A time-adapted standard reference**: PROVE-LOCEXT-H's standard reference whose usual augmentation is generated,
with time information and up to null sets, by its normalized history: for rationals `q < t`, every event of `𝓖_q` is
almost surely an event of the history truncated at `t`. -/
def IsStdReferenceL (κ rL rR : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) {Ωr : Type u} [MeasurableSpace Ωr]
    (Pr : Measure Ωr) (𝓕r : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ωr)) (Wr : ℝ≥0 → Ωr → ℝ)
    (VLr VRr : Fin 1 → ℝ≥0 → Ωr → ℝ) (Br : ℝ≥0 → Ωr → ℝ) (ζr : Ωr → ℝ≥0∞)
    (hr : Ωr → DistOn upperHalfPlaneOpens) : Prop :=
  IsStdReference κ rL rR Pr 𝓕r Wr VLr VRr Br ζr hr ∧
    ∀ (q t : ℚ≥0), q < t → ∀ A : Set Ωr, MeasurableSet[usualAugmentation 𝓕r Pr (q : ℝ≥0)] A →
      ∃ Γ : Set TwoSeedHist, MeasurableSet Γ ∧
        ∀ᵐ ω ∂Pr, (ω ∈ A ↔ truncH t (fullRefHist xL xR Wr VLr VRr ω) ∈ Γ)

/-- **A time-adapted standard reference is time-adapted to its history at the capped local stop.** -/
theorem IsStdReferenceL.isTimeAdaptedRef {κ rL rR r : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {Ωr : Type u}
    [MeasurableSpace Ωr] {Pr : Measure Ωr} {𝓕r : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ωr)}
    {Wr : ℝ≥0 → Ωr → ℝ} {VLr VRr : Fin 1 → ℝ≥0 → Ωr → ℝ} {Br : ℝ≥0 → Ωr → ℝ} {ζr : Ωr → ℝ≥0∞}
    {hr : Ωr → DistOn upperHalfPlaneOpens} {Gr : Set Ωr}
    (href : IsStdReferenceL κ rL rR xL xR Pr 𝓕r Wr VLr VRr Br ζr hr) :
    IsTimeAdaptedRef xL xR r Gr Pr 𝓕r Wr VLr VRr ζr := by
  intro q t hqt A hA
  obtain ⟨Γ, hΓ, hAΓ⟩ := href.2 q t hqt A hA
  refine ⟨Γ, hΓ, ?_⟩
  filter_upwards [hAΓ] with ω hω htS
  rw [hω, truncH_refRecHist xL xR htS, truncH_fullRefHist]

/-- **Named input: a time-adapted standard reference exists** for the seed pattern of every word and every pair of
admissible seed weights (an empty seed side has weight `0`). -/
def StdTwoSeedReferenceLStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (rL rR : ℝ), -2 < rL → -2 < rR →
    ((¬ ∃ i, xL i = 0) → rL = 0) → ((¬ ∃ j, xR j = 0) → rR = 0) →
    ∃ (Ωr : Type u) (_ : MeasurableSpace Ωr) (Pr : Measure Ωr) (𝓕r : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ωr))
      (Wr : ℝ≥0 → Ωr → ℝ) (VLr VRr : Fin 1 → ℝ≥0 → Ωr → ℝ) (Br : ℝ≥0 → Ωr → ℝ) (ζr : Ωr → ℝ≥0∞)
      (hr : Ωr → DistOn upperHalfPlaneOpens), IsStdReferenceL κ rL rR xL xR Pr 𝓕r Wr VLr VRr Br ζr hr

/-- **Named input (Loc) for time-adapted references**: PROVE-LOCEXT-H's `ExtLocalityStatement` with the reference
assumed time-adapted (`IsStdReferenceL`). -/
def ExtLocalityLStatement (κ : ℝ) : Prop :=
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
    ∀ (hX : IsMeasurableKilledDriving (fun t (p : Ω × Ωr) => Wr t p.2) (fun i t p => VLr i t p.2)
        (fun i t p => VRr i t p.2) (fun p => ζr p.2)) (τ : Ω × Ωr → WithTop ℝ≥0),
      IsStoppingTime (drivingFiltration E hX) τ → (∀ᵐ p ∂E, (τ p : ℝ≥0∞) < ζr p.2) →
        IsLocalSet (fun p => fwdHull (fun s : ℝ => Wr s.toNNReal p.2) ((τ p).untopD 0 : ℝ≥0)) (fun p => h p.1) E

end RefL

/-! ### The extension -/

section Extension

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} [IsProbabilityMeasure Q] {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {S : Ω → WithTop ℝ≥0}
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Aux. lemma 54 from a time-adapted standard reference with the same record law** ((K-pre) proved; (Loc) from
`ExtLocalityLStatement`). PROVE-LOCEXT-H's `hasReferenceExtension_of_recordLaw` with the reference time-adapted. -/
theorem hasReferenceExtension_of_recordLaw_L (hκ : 0 < κ) (hF : IsOrderedForceWord xL xR) (hr : 0 < r)
    (hL : -2 < seedSumL xL ρL) (hR : -2 < seedSumR xR ρR)
    (hc : IsStoppedSeedCoupling κ xL xR ρL ρR r Q W VL VR S h)
    {Ωr : Type u} [mΩr : MeasurableSpace Ωr] {Pr : Measure Ωr} {𝓕r : Filtration ℝ≥0 mΩr}
    {Wr : ℝ≥0 → Ωr → ℝ} {VLr VRr : Fin 1 → ℝ≥0 → Ωr → ℝ} {Br : ℝ≥0 → Ωr → ℝ} {ζr : Ωr → ℝ≥0∞}
    {hr' : Ωr → DistOn upperHalfPlaneOpens}
    (href : IsStdReferenceL κ (seedSumL xL ρL) (seedSumR xR ρR) xL xR Pr 𝓕r Wr VLr VRr Br ζr hr')
    {Gr : Set Ωr} (hGm : MeasurableSet Gr) (hG0 : Pr Grᶜ = 0)
    (hG : ∀ ω ∈ Gr, IsGoodPath κ LP.twoSeedXL LP.twoSeedXR (fun _ => seedSumL xL ρL) (fun _ => seedSumR xR ρR)
      Wr VLr VRr Br ζr ω)
    {Rr : Ωr → RecSp} (hRrm : Measurable Rr)
    (hRr : ∀ᵐ ω ∂Pr, Rr ω = recOf (hr' ω) (refRecHist xL xR r Gr Wr VLr VRr ζr ω))
    (hlaw : Q.map (fun ω => recOf (h ω) (stRecHist xL xR W VL VR S ω)) = Pr.map Rr)
    (hLoc : ExtLocalityLStatement.{u} κ) :
    HasReferenceExtension.{u} κ (seedSumL xL ρL) (seedSumR xR ρR) r Q h
      (fun ω => twoSeedProj xL xR (stoppedHistory (drivingState W VL VR) S ω)) := by
  classical
  obtain ⟨⟨hSB, hPr, hC, hfam, -⟩, -⟩ := id href
  have hTAG := href.isTimeAdaptedRef (r := r) (Gr := Gr)
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
    fun hX τ hτ hτζ => hLoc xL xR ρL ρR r hF hr hL hR Q W VL VR S h hc Pr 𝓕r Wr VLr VRr Br ζr hr' href Gr hGm hG0
      hG E hrecext hX τ hτ hτζ
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

/-! ### Aux. lemma 54 for stopped seed couplings -/

/-- **Aux. lemma 54 for stopped seed couplings** (`StoppedSeedExtensionStatement κ`) from a time-adapted standard
reference for every seed pattern and (Loc) on the extension; (U) is PROVE-LOCEXT-J's `stoppedTwoSeedLawStatement` and
(K-pre) is `setIntegral_preStop_eq_of_tag`. -/
theorem stoppedSeedExtensionStatement_of_refL {κ : ℝ} (hκ : 0 < κ) (hRef : StdTwoSeedReferenceLStatement.{u} κ)
    (hLoc : ExtLocalityLStatement.{u} κ) : StoppedSeedExtensionStatement.{u} κ := by
  intro nL nR xL xR ρL ρR r hF hr hL hR Ω mΩ Q hQ W VL VR S h hc
  obtain ⟨Ωr, mΩr, Pr, 𝓕r, Wr, VLr, VRr, Br, ζr, hr', href⟩ :=
    hRef xL xR _ _ hL hR seedSumL_eq_zero seedSumR_eq_zero
  obtain ⟨⟨-, hPr, hC, -, -⟩, -⟩ := id href
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
  exact hasReferenceExtension_of_recordLaw_L hκ hF hr hL hR hc href hGm hG0 hG
    (Rr := fun ω => recOf (hr' ω) (refVer xL xR r Gr Wr VLr VRr ζr ω))
    (measurable_recOf.comp (hC.2.1.prodMk hY₂m))
    (by filter_upwards [hver] with ω hω; rw [hω]) hrec hLoc

end LocalExt

end InteractingSLE
