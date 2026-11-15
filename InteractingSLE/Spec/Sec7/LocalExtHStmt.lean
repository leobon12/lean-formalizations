/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtHComap
import InteractingSLE.Spec.Sec7.LocalExtHRec
import InteractingSLE.Spec.Sec7.LocalExtFHist
import InteractingSLE.Spec.Coupling.Locality11

/-!
# Aux. lemma 54 for a stopped seed coupling: the record, the reference, and the remaining inputs

Packet PROVE-LOCEXT-H. Aux. lemma 54 (specification p. 246) extends a stopped coupling `(h, W_{·∧S}, V_{·∧S})` to a full
coupling by sampling its future from **one fixed reference coupling** conditionally on a record of the stopped history
and of the active field. This file fixes the objects and states the parts of the argument that are not proved here:

* `stRecHist`: the two-seed stopped history of the stopped coupling (through its measurable version `histVersion`);
  `refRecHist`: the two-seed history of a reference at its capped local stop, empty seed sides normalized (`seedProj`);
* `IsStdReference`: a full two-seed coupling on a standard Borel space, family-sampled (the protected kernel at a
  countable exhausting family of stops of the usual augmentation, `Coupling.IsFamilySampled`, Theorem 1.1's
  construction), whose usual augmentation is generated up to null sets by the driving coordinates
  (`Coupling.IsAeGen`, also from Theorem 1.1's construction);
* `IsRecordExtension`: a measure `E` on `Ω × Ωr` with marginals `Q` and `Pr`, in which the two records agree (history,
  and the field off the hull test function by test function) and which samples the second factor from the first only
  through the record (`E = Q ⊗ κ₀(record)`);
* the **named inputs** (each a statement of the specification's argument, stated for every such configuration):
  - `StdTwoSeedReferenceStatement κ` — a standard Borel reference exists for every admissible seed pair;
  - `StoppedTwoSeedLawStatement κ` — **(U)**: the stopped two-seed history of a stopped seed coupling has the law of the
    reference's at its local stop (uniqueness in law through the local stop; Theorem 2.2's entrance argument);
  - `ExtPreStopStatement κ` — **(K-pre)**: on a record extension, at a safe stop of the reference before its local stop,
    the original field and the reference field have the same tested characteristic functional on the events of the
    reference's stopped σ-algebra ("For a stop that may occur before … `S`, split into the two stopped-history-measurable
    events and apply the … pre-`S` … identity");
  - `ExtLocalityStatement κ` — **(Loc)**: on a record extension, every hull of the reference driving is a local set of
    the original field ("Successive local-set decompositions therefore make the union of the old hull and each relative
    future hull local for the original field").
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace LocalExt

open Sec7 Sec4 LQGMetric Coupling

/-! ### The two records -/

section Records

variable {nL nR : ℕ} {Ω : Type*}

/-- **The two-seed history of the stopped coupling**: the merged seed history (`twoSeedProj`) of the version of the
stopped history that is measurable for the stopped σ-algebra (`histVersion`, equal to the stopped history on regular
stops). -/
def stRecHist (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (S : Ω → WithTop ℝ≥0) (ω : Ω) : TwoSeedHist :=
  twoSeedProj xL xR (histVersion W VL VR S ω)

/-- **The two-seed history of a reference at its capped local stop**, with the empty seed sides normalized to the
driver (`seedProj`, as in `twoSeedProj`). -/
def refRecHist (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (r : ℝ) (G : Set Ω) (W : ℝ≥0 → Ω → ℝ)
    (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : TwoSeedHist :=
  seedProj xL xR (stoppedHistory (completedState W VL VR ζ) (capStop r G ζ W) ω)

end Records

/-! ### The reference -/

/-- **A standard reference** for the seed pair `(rL, rR)`: a full two-seed coupling with the frozen optional hull
specification on a standard Borel space, family-sampled (`Coupling.IsFamilySampled`), whose usual augmentation is
generated up to null sets by the rational-time driving coordinates (`Coupling.coordMap`), and family-local for the centred
field (`Coupling.IsFamilyLocal`). Theorem 1.1's construction
(`Coupling.exists_locCoupling_of_evolution`) on a standard Borel driving space has these properties. -/
def IsStdReference (κ rL rR : ℝ) {Ωr : Type u} [MeasurableSpace Ωr] (Pr : Measure Ωr)
    (𝓕r : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ωr)) (Wr : ℝ≥0 → Ωr → ℝ) (VLr VRr : Fin 1 → ℝ≥0 → Ωr → ℝ)
    (Br : ℝ≥0 → Ωr → ℝ) (ζr : Ωr → ℝ≥0∞) (hr : Ωr → DistOn upperHalfPlaneOpens) : Prop :=
  StandardBorelSpace Ωr ∧ IsProbabilityMeasure Pr ∧
    IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) Pr 𝓕r Wr VLr VRr Br ζr hr ∧
    IsFamilySampled κ (fun _ => rL) (fun _ => rR) Pr 𝓕r Wr VLr VRr ζr hr ∧
    (∀ t, IsAeGen Pr (coordMap Wr VLr VRr Br ζr) (usualAugmentation 𝓕r Pr t)) ∧
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
        LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀ →
      IsFamilyLocal Pr 𝓕r Wr ζr (fun ω => hr ω - SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀)

/-- **Named input: a standard reference exists** for every pair of admissible seed weights (Theorem 1.1's construction on
a standard Borel driving space; it follows from Theorem 2.2's existence on a standard Borel space). -/
def StdTwoSeedReferenceStatement (κ : ℝ) : Prop :=
  ∀ rL rR : ℝ, -2 < rL → -2 < rR →
    ∃ (Ωr : Type u) (_ : MeasurableSpace Ωr) (Pr : Measure Ωr) (𝓕r : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ωr))
      (Wr : ℝ≥0 → Ωr → ℝ) (VLr VRr : Fin 1 → ℝ≥0 → Ωr → ℝ) (Br : ℝ≥0 → Ωr → ℝ) (ζr : Ωr → ℝ≥0∞)
      (hr : Ωr → DistOn upperHalfPlaneOpens), IsStdReference κ rL rR Pr 𝓕r Wr VLr VRr Br ζr hr

/-! ### (U): the stopped two-seed law -/

/-- **Named input (U): uniqueness in law through the local stop.** For a stopped seed coupling through its local stop
`S` of radius `r` and every full two-seed evolution with the seed sums as weights and a good event, the merged two-seed
history stopped at `S` has the law of the reference's two-seed history (empty seed sides normalized) stopped at its
capped local stop of radius `r`. (Template: Theorem 2.2's entrance uniqueness, `Sec2.Assembly3Entr`, step 4.) -/
def StoppedTwoSeedLawStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (r : ℝ),
    IsOrderedForceWord xL xR → 0 < r → -2 < seedSumL xL ρL → -2 < seedSumR xR ρR →
    ∀ {Ω : Type u} {_ : MeasurableSpace Ω} (Q : Measure Ω) [IsProbabilityMeasure Q] (W : ℝ≥0 → Ω → ℝ)
      (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (S : Ω → WithTop ℝ≥0)
      (h : Ω → DistOn upperHalfPlaneOpens),
      IsStoppedSeedCoupling κ xL xR ρL ρR r Q W VL VR S h →
    ∀ {Ωr : Type u} {_ : MeasurableSpace Ωr} (Pr : Measure Ωr) [IsProbabilityMeasure Pr]
      (𝓕r : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ωr)) (Wr : ℝ≥0 → Ωr → ℝ) (VLr VRr : Fin 1 → ℝ≥0 → Ωr → ℝ)
      (Br : ℝ≥0 → Ωr → ℝ) (ζr : Ωr → ℝ≥0∞),
      IsIntegratedSLEEvolution κ LP.twoSeedXL LP.twoSeedXR (fun _ => seedSumL xL ρL) (fun _ => seedSumR xR ρR) Pr 𝓕r
        Wr VLr VRr Br ζr →
    ∀ Gr : Set Ωr, MeasurableSet Gr → Pr Grᶜ = 0 →
      (∀ ωr ∈ Gr, IsGoodPath κ LP.twoSeedXL LP.twoSeedXR (fun _ => seedSumL xL ρL) (fun _ => seedSumR xR ρR)
        Wr VLr VRr Br ζr ωr) →
      Q.map (fun ω => twoSeedProj xL xR (stoppedHistory (drivingState W VL VR) S ω)) =
        Pr.map (refRecHist xL xR r Gr Wr VLr VRr ζr)

/-! ### Record extensions -/

/-- **A record extension**: a measure `E` on `Ω × Ωr` with marginals `Q` and `Pr`, under which the stopped two-seed
history `Rh` of the first factor is the reference history `Rhr` of the second, the field off the hull agrees test
function by test function, and which samples the second factor from the first only through the record
(`E = Q ⊗ κ₀(record)`, Aux. lemma 54: "Use that kernel at `(𝓗_S, H_S)` to sample the new future"). -/
def IsRecordExtension {Ω Ωr : Type*} [MeasurableSpace Ω] [MeasurableSpace Ωr] (Q : Measure Ω) (Pr : Measure Ωr)
    (h : Ω → DistOn upperHalfPlaneOpens) (Rh : Ω → TwoSeedHist) (hr : Ωr → DistOn upperHalfPlaneOpens)
    (Rhr : Ωr → TwoSeedHist) (E : Measure (Ω × Ωr)) : Prop :=
  E.map Prod.fst = Q ∧ E.map Prod.snd = Pr ∧ (∀ᵐ p ∂E, Rh p.1 = Rhr p.2) ∧
    (∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ p ∂E, fieldRec (h p.1) (Rh p.1) ψ = fieldRec (hr p.2) (Rhr p.2) ψ) ∧
    ∃ (hm : Measurable fun ω => recOf (h ω) (Rh ω)) (κ₀ : Kernel RecSp Ωr), IsMarkovKernel κ₀ ∧
      E = Q ⊗ₘ κ₀.comap (fun ω => recOf (h ω) (Rh ω)) hm

/-! ### (K-pre) and (Loc) on a record extension -/

/-- **Named input (K-pre)**: the protected kernel before the local stop survives the extension. For a stopped seed
coupling, a standard reference with a good event, a stop `s` of the reference's usual augmentation that is safe for an
open set `U` (`s < ζr`, `U ∩ K_s = ∅`), and a record extension `E`, the original field `h(p.1)` and the reference field
`hr(p.2)` have the same integral of `exp(i ⟨·, ψ⟩)` (`supp ψ ⊆ U`) over every event of the reference's stopped
σ-algebra at `s` on which `s` precedes the reference's capped local stop. -/
def ExtPreStopStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (r : ℝ),
    IsOrderedForceWord xL xR → 0 < r → -2 < seedSumL xL ρL → -2 < seedSumR xR ρR →
    ∀ {Ω : Type u} {_ : MeasurableSpace Ω} (Q : Measure Ω) [IsProbabilityMeasure Q] (W : ℝ≥0 → Ω → ℝ)
      (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (S : Ω → WithTop ℝ≥0)
      (h : Ω → DistOn upperHalfPlaneOpens),
      IsStoppedSeedCoupling κ xL xR ρL ρR r Q W VL VR S h →
    ∀ {Ωr : Type u} {_ : MeasurableSpace Ωr} (Pr : Measure Ωr)
      (𝓕r : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ωr)) (Wr : ℝ≥0 → Ωr → ℝ) (VLr VRr : Fin 1 → ℝ≥0 → Ωr → ℝ)
      (Br : ℝ≥0 → Ωr → ℝ) (ζr : Ωr → ℝ≥0∞) (hr : Ωr → DistOn upperHalfPlaneOpens),
      IsStdReference κ (seedSumL xL ρL) (seedSumR xR ρR) Pr 𝓕r Wr VLr VRr Br ζr hr →
    ∀ Gr : Set Ωr, MeasurableSet Gr → Pr Grᶜ = 0 →
      (∀ ωr ∈ Gr, IsGoodPath κ LP.twoSeedXL LP.twoSeedXR (fun _ => seedSumL xL ρL) (fun _ => seedSumR xR ρR)
        Wr VLr VRr Br ζr ωr) →
    ∀ (U : Set ℂ) (s : Ωr → ℝ≥0) (hs : IsStoppingTime (usualAugmentation 𝓕r Pr) fun ωr => (s ωr : WithTop ℝ≥0)),
      (∀ᵐ ωr ∂Pr, (s ωr : ℝ≥0∞) < ζr ωr ∧ Disjoint U (fwdHull (fun r : ℝ => Wr r.toNNReal ωr) (s ωr))) →
    ∀ E : Measure (Ω × Ωr),
      IsRecordExtension Q Pr h (stRecHist xL xR W VL VR S) hr (refRecHist xL xR r Gr Wr VLr VRr ζr) E →
    ∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ U → ∀ A₀ : Set Ωr, MeasurableSet[hs.measurableSpace] A₀ →
      ∫ p in Prod.snd ⁻¹' (A₀ ∩ {ωr | (s ωr : WithTop ℝ≥0) < capStop r Gr ζr Wr ωr}),
          Complex.exp (Complex.I * (h p.1 ψ : ℂ)) ∂E =
        ∫ p in Prod.snd ⁻¹' (A₀ ∩ {ωr | (s ωr : WithTop ℝ≥0) < capStop r Gr ζr Wr ωr}),
          Complex.exp (Complex.I * (hr p.2 ψ : ℂ)) ∂E

/-- **Named input (Loc)**: locality survives the extension. For a stopped seed coupling, a standard reference with a
good event and a record extension `E`, at every stopping time `τ` of the frozen driving filtration of the reference
driving read on `E`, with `τ` before the lifetime, the hull `K_τ` is a local set of the original field `h(p.1)`. -/
def ExtLocalityStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (r : ℝ),
    IsOrderedForceWord xL xR → 0 < r → -2 < seedSumL xL ρL → -2 < seedSumR xR ρR →
    ∀ {Ω : Type u} {_ : MeasurableSpace Ω} (Q : Measure Ω) [IsProbabilityMeasure Q] (W : ℝ≥0 → Ω → ℝ)
      (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (S : Ω → WithTop ℝ≥0)
      (h : Ω → DistOn upperHalfPlaneOpens),
      IsStoppedSeedCoupling κ xL xR ρL ρR r Q W VL VR S h →
    ∀ {Ωr : Type u} {_ : MeasurableSpace Ωr} (Pr : Measure Ωr)
      (𝓕r : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ωr)) (Wr : ℝ≥0 → Ωr → ℝ) (VLr VRr : Fin 1 → ℝ≥0 → Ωr → ℝ)
      (Br : ℝ≥0 → Ωr → ℝ) (ζr : Ωr → ℝ≥0∞) (hr : Ωr → DistOn upperHalfPlaneOpens),
      IsStdReference κ (seedSumL xL ρL) (seedSumR xR ρR) Pr 𝓕r Wr VLr VRr Br ζr hr →
    ∀ Gr : Set Ωr, MeasurableSet Gr → Pr Grᶜ = 0 →
      (∀ ωr ∈ Gr, IsGoodPath κ LP.twoSeedXL LP.twoSeedXR (fun _ => seedSumL xL ρL) (fun _ => seedSumR xR ρR)
        Wr VLr VRr Br ζr ωr) →
    ∀ E : Measure (Ω × Ωr),
      IsRecordExtension Q Pr h (stRecHist xL xR W VL VR S) hr (refRecHist xL xR r Gr Wr VLr VRr ζr) E →
    ∀ (hX : IsMeasurableKilledDriving (fun t (p : Ω × Ωr) => Wr t p.2) (fun i t p => VLr i t p.2)
        (fun i t p => VRr i t p.2) (fun p => ζr p.2)) (τ : Ω × Ωr → WithTop ℝ≥0),
      IsStoppingTime (drivingFiltration E hX) τ → (∀ᵐ p ∂E, (τ p : ℝ≥0∞) < ζr p.2) →
        IsLocalSet (fun p => fwdHull (fun s : ℝ => Wr s.toNNReal p.2) ((τ p).untopD 0 : ℝ≥0)) (fun p => h p.1) E

end LocalExt

end InteractingSLE
