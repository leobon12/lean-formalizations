/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtLLocPre

/-!
# Aux. lemma 54, (Loc): references with a safe locality family

Packet PROVE-LOCEXT-L. Locality on the extension is proved through `Coupling.IsFamilyLocal` with the reference's own
countable family of regions `U_i` and stops `s_i`. The pre-stop part of each member's identity
(`setIntegral_lapTest_preStop_of_tag`) needs the member to be **safe**: `U_i ⊆ C_i` for a compact `C_i ⊆ ℍ` that avoids
`K_{s_i}`. Theorem 1.1's construction has such a family (rational balls with their closed balls, `exists_safeFamilyLoc`),
but `IsFamilyLocal` forgets the compact sets and the safety.

* `HasSafeLocalFamily`: `IsFamilyLocal` with the compacts and the safety retained;
* `exists_locCoupling_safe`: Theorem 1.1's coupling (`Coupling.exists_locCoupling_of_evolution`) with that family;
* **`IsStdReferenceLS`**: a time-adapted standard reference (`IsStdReferenceL`) with a safe locality family for the field
  centred at every time-`0` mean;
* **`exists_isStdReferenceLS_of_seeds`**: such references exist when both seed sides are present.
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

/-! ### Safe locality families -/

section Family

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **A safe locality family** of a field `X` over the evolution data `(𝓕, W, ζ)`: countably many open regions
`U i` inside compact sets `C i ⊆ ℍ`, stops `s i` of the usual augmentation with `s i < ζ` and `C i ∩ K_{s i} = ∅`, at which
the projection identity of `Coupling.IsFamilyLocal` holds on every event of the stopped σ-algebra, and which exhaust
avoidance locally. -/
def HasSafeLocalFamily (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (X : Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∃ (ι : Type) (_ : Countable ι) (U : ι → Opens ℂ) (C : ι → Set ℂ) (s : ι → Ω → ℝ≥0)
    (hs : ∀ i, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (s i ω : WithTop ℝ≥0)),
    (∀ i, IsCompact (C i) ∧ C i ⊆ H ∧ (U i : Set ℂ) ⊆ C i) ∧
    (∀ i, ∀ᵐ ω ∂P, (s i ω : ℝ≥0∞) < ζ ω ∧ Disjoint (C i) (fwdHull (fun r : ℝ => W r.toNNReal ω) (s i ω))) ∧
    (∀ i (f : zsSub (U i : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) (D : Set Ω),
      MeasurableSet[(hs i).measurableSpace] D →
        ∫ ω in D, Complex.exp (Complex.I * (X ω (lapTest (U i) f + Ξ) : ℂ)) ∂P =
          Coupling.projFactor (U i) f Ξ * ∫ ω in D, Complex.exp (Complex.I * (X ω Ξ : ℂ)) ∂P) ∧
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∀ K : Set ℂ, IsCompact K → K ⊆ H →
      Disjoint K (fwdHull (fun r : ℝ => W r.toNNReal ω) t) → ∀ O : Set ℂ, IsOpen O → K ⊆ O →
        ∃ i, K ⊆ U i ∧ (U i : Set ℂ) ⊆ O ∧ t ≤ s i ω

/-- A safe locality family is a locality family. -/
theorem HasSafeLocalFamily.isFamilyLocal {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} {X : Ω → DistOn upperHalfPlaneOpens} (h : HasSafeLocalFamily P 𝓕 W ζ X) :
    IsFamilyLocal P 𝓕 W ζ X := by
  obtain ⟨ι, hι, U, C, s, hs, hC, -, hid, hexh⟩ := h
  exact ⟨ι, hι, U, s, hs, fun i => (hC i).2.2.trans (hC i).2.1, hid, hexh⟩

end Family

/-! ### Theorem 1.1's coupling with its safe family -/

section Construction

variable {Ω₀ : Type u} {mΩ₀ : MeasurableSpace Ω₀} {P₀ : Measure Ω₀} {𝓕₀ : Filtration ℝ≥0 mΩ₀}
  {W : ℝ≥0 → Ω₀ → ℝ} {ζ : Ω₀ → ℝ≥0∞} {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {VL : Fin nL → ℝ≥0 → Ω₀ → ℝ} {VR : Fin nR → ℝ≥0 → Ω₀ → ℝ}
  {B : ℝ≥0 → Ω₀ → ℝ}

/-- **Theorem 1.1's coupling with its safe locality family** (admissible seed; `Coupling.exists_locCoupling_of_evolution`
with the rational-ball family kept). -/
theorem exists_locCoupling_safe [IsProbabilityMeasure P₀] (hκ : 0 < κ)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P₀ 𝓕₀ W VL VR B ζ)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR)
    {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] {G : Ω₀ → Y} (hG : Measurable G)
    (hgen : ∀ t, IsAeGen P₀ G (usualAugmentation 𝓕₀ P₀ t))
    (hI2 : FiniteFamilyProjStatement.{u} κ xL xR ρL ρR) :
    ∃ (α : Measure (DistOn upperHalfPlaneOpens)) (μ : Measure (Ω₀ × DistOn upperHalfPlaneOpens)),
      IsProbabilityMeasure α ∧ IsProbabilityMeasure μ ∧ μ.map Prod.fst = P₀ ∧ μ.map Prod.snd = α ∧
      (∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR)
          (forceJumpSet xL xR) u₀ →
        IsZBGFFProcess upperHalfPlaneOpens (fun φ x => x φ - ∫ z, u₀ z * φ z) α) ∧
      IsFamilySampled κ ρL ρR μ (filtrationFst 𝓕₀ (DistOn upperHalfPlaneOpens))
        (fun t p => W t p.1) (fun i t p => VL i t p.1) (fun i t p => VR i t p.1) (fun p => ζ p.1)
        (fun p => p.2) ∧
      ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR)
          (forceJumpSet xL xR) u₀ →
        HasSafeLocalFamily μ (filtrationFst 𝓕₀ (DistOn upperHalfPlaneOpens)) (fun t p => W t p.1)
          (fun p => ζ p.1) (fun p => p.2 - smoothDist upperHalfPlaneOpens u₀) := by
  set u : Ω₀ → ℝ≥0 → ℂ → ℝ := fun ω s => Impl.forceExt κ (weightWord ρL ρR)
    (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω) with hudef
  have hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s) := fun ω s =>
    Impl.isBoundedHarmonicExtension_forceExt κ (weightWord ρL ρR) _ _
  obtain ⟨T, hT⟩ := exists_isAnnouncingSeq hE hκ hseed
  obtain ⟨s, hs, hsafe, hexh⟩ := exists_safeFamilyLoc hE hT
  set U : RatBallSet × ℕ → Set ℂ := fun i => ballsU i.1.1 with hU
  have hUo : ∀ i, IsOpen (U i) := fun i => isOpen_ballsU _
  have hUH : ∀ i, U i ⊆ H := fun i => (ballsU_subset_ballsK _).trans i.1.2
  have hsafeU : ∀ i, ∀ᵐ ω ∂P₀, (s i ω : ℝ≥0∞) < ζ ω ∧
      Disjoint (U i) (fwdHull (fun r : ℝ => W r.toNNReal ω) (s i ω)) := fun i =>
    (hsafe i).mono fun ω h => ⟨h.1, h.2.mono_left (ballsU_subset_ballsK _)⟩
  have hK : ∀ i : RatBallSet × ℕ, IsCompact (ballsK i.1.1) ∧ ballsK i.1.1 ⊆ H ∧ U i ⊆ ballsK i.1.1 :=
    fun i => ⟨isCompact_ballsK _, i.1.2, ballsU_subset_ballsK _⟩
  obtain ⟨α, hαp, hαG, hfin⟩ := hI2 Ω₀ _ P₀ inferInstance 𝓕₀ W VL VR B ζ hE u hu (RatBallSet × ℕ)
    inferInstance U (fun i => ballsK i.1.1) hUo hK s hs hsafe
  obtain ⟨μ, hμp, hμ1, hμ2, hμs⟩ := exists_projCoupling_of_finite κ W u hG U hUo s hs
    (fun i => IsAeGen.stopped hgen (hs i)) α hfin
  have hexhOld : ∀ᵐ ω ∂P₀, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∀ K : Set ℂ, IsCompact K → K ⊆ H →
      Disjoint K (fwdHull (fun r : ℝ => W r.toNNReal ω) t) → ∃ i, K ⊆ U i ∧ t ≤ s i ω :=
    hexh.mono fun ω h t ht K hK hKH hdis => by
      obtain ⟨i, h1, -, h3⟩ := h t ht K hK hKH hdis univ isOpen_univ (subset_univ K)
      exact ⟨i, h1, h3⟩
  refine ⟨α, μ, hαp, hμp, hμ1, hμ2, hαG,
    isFamilySampled_of_isSampledCoupling hE hκ u hu U s hs hsafeU hexhOld hμ1 fun i => (hμs i).1,
    fun u₀ hu₀ => ?_⟩
  have hT₀ := isHarmonicDistOn_smoothDist_of hu₀
  refine ⟨RatBallSet × ℕ, inferInstance, fun i => ⟨U i, hUo i⟩, fun i => ballsK i.1.1, fun i p => s i p.1,
    fun i => isStoppingTime_fst hμ1 (hs i), hK, fun i => ?_, fun i f Ξ D hD => ?_, ?_⟩
  · have h1 := hsafe i
    rw [← hμ1] at h1
    exact ae_of_ae_map measurable_fst.aemeasurable h1
  · obtain ⟨A₀, hA₀, hDA⟩ := exists_fst_ae_eq_of_measurableSet_stopped hμ1 (hs i) hD
    have hUi : (⟨U i, hUo i⟩ : Opens ℂ) ≤ upperHalfPlaneOpens := hUH i
    have h0 : smoothDist upperHalfPlaneOpens u₀ (lapTest ⟨U i, hUo i⟩ f) = 0 :=
      IsHarmonicDistOn.apply_lapTest_eq_zero isOpen_H hT₀ hUi (hUH i) f
    have key := (hμs i).2 f Ξ A₀ hA₀
    rw [setIntegral_congr_set hDA, setIntegral_congr_set hDA]
    have e1 : ∀ p : Ω₀ × DistOn upperHalfPlaneOpens,
        Complex.exp (Complex.I * (((p.2 - smoothDist upperHalfPlaneOpens u₀) (lapTest ⟨U i, hUo i⟩ f + Ξ) : ℝ) : ℂ)) =
          Complex.exp (Complex.I * ((p.2 (lapTest ⟨U i, hUo i⟩ f + Ξ) : ℝ) : ℂ)) *
            Complex.exp (Complex.I * ((-(smoothDist upperHalfPlaneOpens u₀ Ξ) : ℝ) : ℂ)) := fun p => by
      rw [← Complex.exp_add, sub_apply, map_add (smoothDist upperHalfPlaneOpens u₀), h0, zero_add]
      congr 1
      push_cast
      ring
    have e2 : ∀ p : Ω₀ × DistOn upperHalfPlaneOpens,
        Complex.exp (Complex.I * (((p.2 - smoothDist upperHalfPlaneOpens u₀) Ξ : ℝ) : ℂ)) =
          Complex.exp (Complex.I * ((p.2 Ξ : ℝ) : ℂ)) *
            Complex.exp (Complex.I * ((-(smoothDist upperHalfPlaneOpens u₀ Ξ) : ℝ) : ℂ)) := fun p => by
      rw [← Complex.exp_add, sub_apply]
      congr 1
      push_cast
      ring
    simp_rw [e1, e2, integral_mul_const, key]
    rw [Coupling.projFactor]
    ring
  · have hexhL : ∀ᵐ ω ∂P₀, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∀ K : Set ℂ, IsCompact K → K ⊆ H →
        Disjoint K (fwdHull (fun r : ℝ => W r.toNNReal ω) t) → ∀ O : Set ℂ, IsOpen O → K ⊆ O →
          ∃ i, K ⊆ U i ∧ U i ⊆ O ∧ t ≤ s i ω :=
      hexh.mono fun ω h t ht K hK hKH hdis O hO hKO => by
        obtain ⟨i, h1, h2, h3⟩ := h t ht K hK hKH hdis O hO hKO
        exact ⟨i, h1, (ballsU_subset_ballsK _).trans h2, h3⟩
    rw [← hμ1] at hexhL
    exact ae_of_ae_map measurable_fst.aemeasurable hexhL

end Construction

/-! ### Time-adapted references with a safe locality family -/

/-- **A time-adapted standard reference with a safe locality family** for the field centred at every time-`0` mean. -/
def IsStdReferenceLS (κ rL rR : ℝ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) {Ωr : Type u} [MeasurableSpace Ωr]
    (Pr : Measure Ωr) (𝓕r : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ωr)) (Wr : ℝ≥0 → Ωr → ℝ)
    (VLr VRr : Fin 1 → ℝ≥0 → Ωr → ℝ) (Br : ℝ≥0 → Ωr → ℝ) (ζr : Ωr → ℝ≥0∞)
    (hr : Ωr → DistOn upperHalfPlaneOpens) : Prop :=
  IsStdReferenceL κ rL rR xL xR Pr 𝓕r Wr VLr VRr Br ζr hr ∧
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
        LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀ →
      HasSafeLocalFamily Pr 𝓕r Wr ζr (fun ω => hr ω - smoothDist upperHalfPlaneOpens u₀)

/-- **Theorem 1.1's construction on a standard Borel driving space is a time-adapted reference with a safe locality family** (both seed sides
present). -/
theorem isStdReferenceLS_of_stdBorel {κ rL rR : ℝ} (hκ : 0 < κ) (hL : -2 < rL) (hR : -2 < rR) {nL nR : ℕ}
    (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (hseeds : (∃ i, xL i = 0) ∧ ∃ j, xR j = 0)
    {Ω₀ : Type u} [mΩ₀ : MeasurableSpace Ω₀] [hSB : StandardBorelSpace Ω₀] {P₀ : Measure Ω₀}
    [IsProbabilityMeasure P₀] {𝓕₀ : Filtration ℝ≥0 mΩ₀} {W : ℝ≥0 → Ω₀ → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω₀ → ℝ}
    {B : ℝ≥0 → Ω₀ → ℝ} {ζ : Ω₀ → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P₀ 𝓕₀ W VL VR B ζ) :
    ∃ (Pr : Measure (Ω₀ × DistOn upperHalfPlaneOpens))
      (𝓕r : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω₀ × DistOn upperHalfPlaneOpens))),
      IsStdReferenceLS κ rL rR xL xR Pr 𝓕r (fun t p => W t p.1) (fun i t p => VL i t p.1)
        (fun i t p => VR i t p.1) (fun t p => B t p.1) (fun p => ζ p.1) (fun p => p.2) := by
  have hc := measurable_coordVal hE
  have hE₁ := isIntegratedSLEEvolution_coordFiltration hE
  have hgen := IsAeGen.usualAugmentation (IsAeGen.usualAugmentation (P₀ := P₀)
    (isAeGen_coordFiltration (P₀ := P₀) hc))
  obtain ⟨α, μ, -, hμp, hμ1, hμ2, hαG, hfamS, hfamLS⟩ :=
    exists_locCoupling_safe hκ hE₁ (Sec2.Assembly2.not_thr_twoSeed hL hR 0 _ _) (measurable_coordMap hc) hgen
      (finiteFamilyProjStatement hκ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR))
  have hfamL := fun u₀ hu₀ => (hfamLS u₀ hu₀).isFamilyLocal
  set u₀ : ℂ → ℝ := Impl.forceExt κ (weightWord (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR))
    LP.twoSeedXL LP.twoSeedXR with hu₀def
  have hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
      LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀ :=
    Impl.isBoundedHarmonicExtension_forceExt κ (weightWord (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)) _ _
  have hu₀c : ContinuousOn u₀ H := fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt
  have hEμ := IsIntegratedSLEEvolution.fst (X := DistOn upperHalfPlaneOpens) hμ1 hE₁
  have hZμ : IsZeroBoundaryGFF upperHalfPlaneOpens
      (fun p : Ω₀ × DistOn upperHalfPlaneOpens => p.2 - smoothDist upperHalfPlaneOpens u₀) μ :=
    isZeroBoundaryGFF_sub_smoothDist measurable_snd hu₀c (isZBGFFProcess_comp_snd hμ2 (hαG u₀ hu₀))
  have hharm : IsHarmonicDistOn (smoothDist upperHalfPlaneOpens u₀) H := isHarmonicDistOn_smoothDist_of hu₀
  have hC := isOptionalHullCoupling_of_isFamilySampled hEμ hκ measurable_snd
    (fun u₀' hu₀' => isZBGFFProcess_comp_snd hμ2 (hαG u₀' hu₀')) hfamS fun hX τ hτ hτζ => by
      have hl := isLocalSet_hull_of_isFamilyLocal hEμ hX hZμ (hfamL u₀ hu₀) hτ hτζ
      have hl' := IsLocalSet.add_dist hl hharm
      have e : (fun p : Ω₀ × DistOn upperHalfPlaneOpens =>
          p.2 - smoothDist upperHalfPlaneOpens u₀ + smoothDist upperHalfPlaneOpens u₀) = fun p => p.2 :=
        funext fun p => sub_add_cancel _ _
      rw [e] at hl'
      exact hl'
  -- the coordinates are read off the history almost surely
  have hζ := Sec2.Assembly2.ae_lifetime_eq_top_twoSeed hκ hE hL hR
  have hcoord : ∀ (q₂ t : ℚ≥0), q₂ ≤ t → ∀ᵐ ω ∂P₀,
      coordUpTo W VL VR B ζ q₂ ω = coordOfHist κ rL rR q₂ (truncH t (fullRefHist xL xR W VL VR ω)) := by
    intro q₂ t hq₂t
    filter_upwards [hζ, hE.2.2.2.2] with ω hζω hp
    exact coordUpTo_eq_coordOfHist hκ xL xR hseeds hζω hp hq₂t
  refine ⟨μ, filtrationFst (usualAugmentation (coordFiltration hc) P₀) (DistOn upperHalfPlaneOpens),
    ⟨⟨inferInstance, hμp, hC, hfamS, fun t A hA => ?_, fun u₀' hu₀' => hfamL u₀' hu₀'⟩, ?_⟩,
    fun u₀' hu₀' => hfamLS u₀' hu₀'⟩
  · obtain ⟨A₀, hA₀, hAA₀⟩ := exists_fst_ae_eq_of_measurableSet_usualAugmentation hμ1 hA
    obtain ⟨C, hC', hA₀C⟩ := hgen t A₀ hA₀
    exact ⟨C, hC', hAA₀.trans (preimage_fst_ae_eq hμ1 hA₀C)⟩
  · intro q t hqt A hA
    obtain ⟨q₁, h1, h1t⟩ := exists_between hqt
    obtain ⟨q₂, h12, h2t'⟩ := exists_between h1t
    have h2t : q₂ ≤ t := h2t'.le
    obtain ⟨A₀, hA₀, hAA₀⟩ := exists_fst_ae_eq_of_measurableSet_usualAugmentation hμ1 hA
    obtain ⟨A₁, hA₁, hA₀A₁⟩ :=
      exists_ae_eq_of_measurableSet_usualAugmentation (show (q : ℝ≥0) < q₁ by exact_mod_cast h1) hA₀
    obtain ⟨A₂, hA₂, hA₁A₂⟩ :=
      exists_ae_eq_of_measurableSet_usualAugmentation (show (q₁ : ℝ≥0) < q₂ by exact_mod_cast h12) hA₁
    obtain ⟨C, hCm, hC2⟩ := MeasurableSpace.measurableSet_comap.1 (coordFiltration_le_comap_coordUpTo hc q₂ _ hA₂)
    refine ⟨coordOfHist κ rL rR q₂ ⁻¹' C, measurable_coordOfHist κ rL rR q₂ hCm, ?_⟩
    have hAe : A =ᵐ[μ] Prod.fst ⁻¹' A₂ := hAA₀.trans (preimage_fst_ae_eq hμ1 (hA₀A₁.trans hA₁A₂))
    have hcμ : ∀ᵐ p ∂μ, coordUpTo W VL VR B ζ q₂ p.1 =
        coordOfHist κ rL rR q₂ (truncH t (fullRefHist xL xR W VL VR p.1)) := by
      have := hcoord q₂ t h2t
      rw [← hμ1] at this
      exact ae_of_ae_map measurable_fst.aemeasurable this
    filter_upwards [hAe, hcμ] with p hp1 hp2
    have hp1' : p ∈ A ↔ p.1 ∈ A₂ := iff_of_eq hp1
    rw [hp1', ← hC2]
    simp only [mem_preimage]
    rw [hp2]
    rfl

/-- **A time-adapted standard reference with a safe locality family exists** for every pair of admissible seed weights
and every seed pattern with both sides present. -/
theorem exists_isStdReferenceLS_of_seeds {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (hseeds : (∃ i, xL i = 0) ∧ ∃ j, xR j = 0) (rL rR : ℝ) (hL : -2 < rL) (hR : -2 < rR) :
    ∃ (Ωr : Type u) (_ : MeasurableSpace Ωr) (Pr : Measure Ωr) (𝓕r : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ωr))
      (Wr : ℝ≥0 → Ωr → ℝ) (VLr VRr : Fin 1 → ℝ≥0 → Ωr → ℝ) (Br : ℝ≥0 → Ωr → ℝ) (ζr : Ωr → ℝ≥0∞)
      (hr : Ωr → DistOn upperHalfPlaneOpens), IsStdReferenceLS κ rL rR xL xR Pr 𝓕r Wr VLr VRr Br ζr hr := by
  obtain ⟨Ω₀, mΩ₀, hSB, P₀, hP₀, 𝓕₀, W, VL, VR, B, ζ, hE⟩ :=
    thm22StdBorelStatement_of_ordered.{u} (ρL := fun _ : Fin 1 => rL) (ρR := fun _ : Fin 1 => rR) hκ
      isOrderedForceWord_twoSeed'
  obtain ⟨Pr, 𝓕r, href⟩ := isStdReferenceLS_of_stdBorel hκ hL hR xL xR hseeds hE
  exact ⟨Ω₀ × DistOn upperHalfPlaneOpens, inferInstance, Pr, 𝓕r, _, _, _, _, _, _, href⟩

end LocalExt

end InteractingSLE
