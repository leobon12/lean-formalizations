/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtHStmt
import InteractingSLE.Spec.Sec7.LocalExtFExt
import InteractingSLE.Spec.Restart.ChartGauss

/-!
# Aux. lemma 54 for a stopped seed coupling: the extension by one disintegration of a standard reference

Packet PROVE-LOCEXT-H. Given a stopped seed coupling on `(Ω, Q)` and a standard reference `R̂` on a standard Borel
`Ωr` (`IsStoppedSeedCoupling`, `IsStdReference`) whose records have the same law, the measure

  `E = Q ⊗ κ₀(record)`,  `κ₀` = the regular conditional law of the reference given its record

(`Sec7.aux54_exists_extension`, one disintegration) carries, on `Ω × Ωr`, the reference driving process read from the
second factor and the **original field** `h(p.1)` read from the first. This file proves that this is an extended
reference pair (`HasReferenceExtension`), using the named inputs (K-pre) and (Loc) of `LocalExtHStmt` for the two
parts of Aux. lemma 54 not proved here:

* `E` is a record extension (`isRecordExtension_compProd`): marginals `Q` and `P̂`, records equal almost surely;
* **(V)** the driving process of `E` is an integrated two-seed evolution (pulled back along `Prod.snd`);
* the field at time `0` has the two-seed GFF law (from (d), along `Prod.fst`);
* **(K-post)** at every member of the reference's family, on the events after the reference's local stop, the original
  field and the reference field agree on the protected test functions (`ae_field_eq_of_post`): the support avoids the
  hull at the member, hence the hull at the local stop, where the two records say the two fields agree; with (K-pre)
  the protected kernel of the reference transfers, so the coupling on `E` is family-sampled
  (`Coupling.isOptionalHullCoupling_of_isFamilySampled`, with (Loc) for locality);
* the good event is the reference's, and the stopped history at `S` is recovered from the reference's two-seed history
  at its capped local stop (the history record).

Main result: **`hasReferenceExtension_of_recordLaw`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace LocalExt

open Sec7 Sec4 LQGMetric Coupling

/-! ### The reference at its capped local stop -/

section RefStop

variable {κ rL rR r : ℝ} {nL nR : ℕ} {Ωr : Type*} {Wr : ℝ≥0 → Ωr → ℝ} {VLr VRr : Fin 1 → ℝ≥0 → Ωr → ℝ}
  {Br : ℝ≥0 → Ωr → ℝ} {ζr : Ωr → ℝ≥0∞} {Gr : Set Ωr}

theorem isSeedRadius_twoSeed (hr : 0 < r) : IsSeedRadius LP.twoSeedXL LP.twoSeedXR r :=
  ⟨hr, fun _ hi => absurd rfl hi, fun _ hj => absurd rfl hj⟩

/-- **On the good event the reference's capped local stop is finite and before the lifetime.** -/
theorem capStop_ref (hL : -2 < rL) (hR : -2 < rR) (hr : 0 < r)
    (hG : ∀ ω ∈ Gr, IsGoodPath κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) Wr VLr VRr Br ζr ω)
    {ω : Ωr} (hω : ω ∈ Gr) :
    capStop r Gr ζr Wr ω = (((capStop r Gr ζr Wr ω).untopD 0 : ℝ≥0) : WithTop ℝ≥0) ∧
      (((capStop r Gr ζr Wr ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < ζr ω := by
  have hthr : ¬ ForceWord.ThresholdCondition (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) 0 LP.twoSeedXL
      LP.twoSeedXR := Sec2.Assembly2.not_thr_twoSeed hL hR 0 _ _
  have h1 := capStop_eq_localStop hG isOrderedForceWord_twoSeed' (isSeedRadius_twoSeed hr) hthr hω
  have h2 := localStop_lt hG isOrderedForceWord_twoSeed' (isSeedRadius_twoSeed hr) hthr hω
  have hne : localStop r Gr ζr Wr ω ≠ ⊤ := localStop_ne_top
  obtain ⟨S₀, hS₀⟩ := WithTop.ne_top_iff_exists.1 hne
  rw [h1, ← hS₀, WithTop.untopD_coe]
  rw [← hS₀] at h2
  exact ⟨rfl, h2⟩

open Classical in
/-- The two-seed state of the reference with the empty seed sides normalized to the driver (as `seedProj`). -/
def refState (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (Wr : ℝ≥0 → Ωr → ℝ) (VLr VRr : Fin 1 → ℝ≥0 → Ωr → ℝ) (ω : Ωr) :
    ℝ≥0 → ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ) :=
  fun t => (Wr t ω, fun _ => if ∃ i, xL i = 0 then VLr 0 t ω else Wr t ω,
    fun _ => if ∃ j, xR j = 0 then VRr 0 t ω else Wr t ω)

/-- **The reference's two-seed history at a finite capped local stop before the lifetime** is the history of the
normalized state stopped there. -/
theorem refRecHist_eq_tsOf (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) {ω : Ωr} {S₀ : ℝ≥0}
    (hS : capStop r Gr ζr Wr ω = S₀) (hSζ : (S₀ : ℝ≥0∞) < ζr ω) :
    refRecHist xL xR r Gr Wr VLr VRr ζr ω = tsOf S₀ (refState xL xR Wr VLr VRr ω) := by
  classical
  refine Prod.ext hS (funext fun q => ?_)
  have hq : stopAt (capStop r Gr ζr Wr) q ω = min (q : ℝ≥0) S₀ := stopAt_of_eq_coe hS q
  have hlt : ((min (q : ℝ≥0) S₀ : ℝ≥0) : ℝ≥0∞) < ζr ω :=
    lt_of_le_of_lt (by exact_mod_cast min_le_right _ _) hSζ
  simp only [refRecHist, seedProj, stoppedHistory, hq, completedState, hlt, ↓reduceIte, drivingState, tsOf,
    refState]

theorem continuousOn_refState (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) {ω : Ωr}
    (hg : IsGoodPath κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) Wr VLr VRr Br ζr ω) {S₀ : ℝ≥0}
    (hSζ : (S₀ : ℝ≥0∞) < ζr ω) : ContinuousOn (refState xL xR Wr VLr VRr ω) (Iic S₀) := by
  classical
  have hsub : Iic S₀ ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζr ω} := fun t ht =>
    lt_of_le_of_lt (by exact_mod_cast ht) hSζ
  have hp := hg.1
  have hW : ContinuousOn (fun t => Wr t ω) (Iic S₀) := hp.2.2.2.1.mono hsub
  have hVL : ContinuousOn (fun t => VLr 0 t ω) (Iic S₀) := (hp.2.2.2.2.1 0).mono hsub
  have hVR : ContinuousOn (fun t => VRr 0 t ω) (Iic S₀) := (hp.2.2.2.2.2.1 0).mono hsub
  refine hW.prodMk ((continuousOn_pi.2 fun _ => ?_).prodMk (continuousOn_pi.2 fun _ => ?_))
  · by_cases h : ∃ i, xL i = 0
    · simpa only [refState, h, ↓reduceIte] using hVL
    · simpa only [refState, h, ↓reduceIte] using hW
  · by_cases h : ∃ j, xR j = 0
    · simpa only [refState, h, ↓reduceIte] using hVR
    · simpa only [refState, h, ↓reduceIte] using hW

/-- **After the local stop, a support that misses the hull at a later time misses the reference's recorded hull.** -/
theorem disjoint_tsHull_refRecHist (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (hL : -2 < rL) (hR : -2 < rR) (hr : 0 < r)
    (hG : ∀ ω ∈ Gr, IsGoodPath κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) Wr VLr VRr Br ζr ω)
    {ω : Ωr} (hω : ω ∈ Gr) {K : Set ℂ} (hKH : K ⊆ H) {t : ℝ≥0} (hSt : capStop r Gr ζr Wr ω ≤ t)
    (hK : Disjoint K (fwdHull (fun s : ℝ => Wr s.toNNReal ω) t)) :
    Disjoint K (tsHull (refRecHist xL xR r Gr Wr VLr VRr ζr ω)) := by
  obtain ⟨hS, hSζ⟩ := capStop_ref hL hR hr hG hω
  set S₀ : ℝ≥0 := (capStop r Gr ζr Wr ω).untopD 0 with hS₀
  rw [refRecHist_eq_tsOf xL xR hS hSζ]
  have hS₀t : S₀ ≤ t := by
    rw [hS] at hSt
    exact_mod_cast hSt
  refine disjoint_tsHull_tsOf (continuousOn_refState xL xR (hG ω hω) hSζ) hSζ (hG ω hω).1.2.2.2.1
    (fun _ _ => rfl) hKH (hK.mono_right ?_)
  exact (QuantumZipper.fwdHull_mono (W := fun s : ℝ => Wr s.toNNReal ω)).1 (by exact_mod_cast hS₀t)

end RefStop

/-! ### The stopped coupling's record -/

section StRec

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {S : Ω → WithTop ℝ≥0}
  {h : Ω → DistOn upperHalfPlaneOpens}

theorem IsStoppedSeedCoupling.measurable_stRecHist (hc : IsStoppedSeedCoupling κ xL xR ρL ρR r Q W VL VR S h) :
    Measurable (stRecHist xL xR W VL VR S) := by
  obtain ⟨𝓓, hS, -, -, hWa, hVLa, hVRa, -⟩ := hc
  exact (measurable_twoSeedProj xL xR).comp
    ((measurable_histVersion hS hWa hVLa hVRa).mono hS.measurableSpace_le le_rfl)

/-- On a stopped seed coupling, the record history is almost surely the merged stopped history. -/
theorem IsStoppedSeedCoupling.ae_stRecHist_eq (hr : 0 < r)
    (hc : IsStoppedSeedCoupling κ xL xR ρL ρR r Q W VL VR S h) :
    ∀ᵐ ω ∂Q, stRecHist xL xR W VL VR S ω = twoSeedProj xL xR (stoppedHistory (drivingState W VL VR) S ω) := by
  filter_upwards [hc.ae_isRegularStop hr] with ω hω
  rw [stRecHist, histVersion_eq hω.1 hω.2.1 hω.2.2]

end StRec

/-! ### The extension -/

section Extension

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} [IsProbabilityMeasure Q] {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {S : Ω → WithTop ℝ≥0}
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Aux. lemma 54 from a standard reference with the same record law** (conditional on (K-pre) and (Loc)). For a
stopped seed coupling and a standard reference for its seed sums, with a good event, whose record (history at the capped
local stop, field off its hull; any measurable version `Rr`) has the law of the stopped coupling's record, the
extension `Q ⊗ κ₀(record)` by the regular conditional law of the reference given its record is an extended reference
pair over the original field, recovering the merged stopped history. -/
theorem hasReferenceExtension_of_recordLaw (hκ : 0 < κ) (hF : IsOrderedForceWord xL xR) (hr : 0 < r)
    (hL : -2 < seedSumL xL ρL) (hR : -2 < seedSumR xR ρR)
    (hc : IsStoppedSeedCoupling κ xL xR ρL ρR r Q W VL VR S h)
    {Ωr : Type u} [mΩr : MeasurableSpace Ωr] {Pr : Measure Ωr} {𝓕r : Filtration ℝ≥0 mΩr}
    {Wr : ℝ≥0 → Ωr → ℝ} {VLr VRr : Fin 1 → ℝ≥0 → Ωr → ℝ} {Br : ℝ≥0 → Ωr → ℝ} {ζr : Ωr → ℝ≥0∞}
    {hr' : Ωr → DistOn upperHalfPlaneOpens}
    (href : IsStdReference κ (seedSumL xL ρL) (seedSumR xR ρR) Pr 𝓕r Wr VLr VRr Br ζr hr')
    {Gr : Set Ωr} (hGm : MeasurableSet Gr) (hG0 : Pr Grᶜ = 0)
    (hG : ∀ ω ∈ Gr, IsGoodPath κ LP.twoSeedXL LP.twoSeedXR (fun _ => seedSumL xL ρL) (fun _ => seedSumR xR ρR)
      Wr VLr VRr Br ζr ω)
    {Rr : Ωr → RecSp} (hRrm : Measurable Rr)
    (hRr : ∀ᵐ ω ∂Pr, Rr ω = recOf (hr' ω) (refRecHist xL xR r Gr Wr VLr VRr ζr ω))
    (hlaw : Q.map (fun ω => recOf (h ω) (stRecHist xL xR W VL VR S ω)) = Pr.map Rr)
    (hPre : ExtPreStopStatement.{u} κ) (hLoc : ExtLocalityStatement.{u} κ) :
    HasReferenceExtension.{u} κ (seedSumL xL ρL) (seedSumR xR ρR) r Q h
      (fun ω => twoSeedProj xL xR (stoppedHistory (drivingState W VL VR) S ω)) := by
  classical
  obtain ⟨hSB, hPr, hC, hfam, -⟩ := id href
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
      exact hPre xL xR ρL ρR r hF hr hL hR Q W VL VR S h hc Pr 𝓕r Wr VLr VRr Br ζr hr' href Gr hGm hG0 hG (U i)
        (s i) (hs i) (hsafe i) E hrecext ψ hψ A₀ hA₀
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

end LocalExt

end InteractingSLE
