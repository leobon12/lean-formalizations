import InteractingSLE.Spec.Coupling.Assembly11B

/-!
# Theorem 1.1, conditional provider: the frozen Theorem 2.2 and projection-independent finite families

Packet PROVE-T11-LOC. The second assembly of the frozen Theorem 1.1:

* `isFamilyLocal_of_projCoupling`: a coupling projection-independent at every member of a locally exhausting family is
  family-local (`IsFamilyLocal`) for the centred field `p.2 − 𝔥₀` on `Ω₀ × 𝒟'(ℍ)`;
* `exists_locCoupling_of_evolution`: from an integrated evolution whose usual augmentation is almost surely generated
  by countably many coordinates and the named input `FiniteFamilyProjStatement`, a coupling on `Ω₀ × 𝒟'(ℍ)` that is
  family-sampled (the conditional-law clause) and family-local (locality);
* `exists_isOptionalHullCoupling_of_finiteFamilyProj` (**provider form**, every frozen argument implicit, every
  universe): the frozen statement of Theorem 1.1 from **exactly the frozen statement of Theorem 2.2** (an evolution on
  some `Ω : Type`) and the named input `FiniteFamilyProjStatement`. The evolution is lifted to `ULift Ω` and its
  filtration replaced by the usual augmentation of its rational-time coordinates (`Assembly11BCoord`), so no standard
  Borel assumption is made.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper TopologicalSpace
open scoped NNReal ENNReal Classical RealInnerProductSpace

universe u

namespace InteractingSLE

namespace Coupling

open Ito LQGMetric LQGMetric.MarkovZB LocalSets QuantumZipper.K3 QuantumZipper.Thm11Asm
open SupercriticalConformalCovariance.GM24 (smoothDist smoothDist_apply)

/-! ### The coupling is family-local -/

theorem smoothDist_apply_eq {u₀ : ℂ → ℝ} (hu₀c : ContinuousOn u₀ H) (φ : TestOn upperHalfPlaneOpens) :
    smoothDist upperHalfPlaneOpens u₀ φ = ∫ z, u₀ z * φ z := by
  rw [smoothDist_apply hu₀c]
  congr 1
  funext z
  ring

theorem isZeroBoundaryGFF_sub_smoothDist {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → DistOn upperHalfPlaneOpens} (hX : Measurable X) {u₀ : ℂ → ℝ} (hu₀c : ContinuousOn u₀ H)
    (hp : IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => X ω φ - ∫ z, u₀ z * φ z) P) :
    IsZeroBoundaryGFF upperHalfPlaneOpens (fun ω => X ω - smoothDist upperHalfPlaneOpens u₀) P := by
  refine ⟨(measurable_sub_distOnConst _).comp hX, ?_⟩
  have e : (fun φ ω => (X ω - smoothDist upperHalfPlaneOpens u₀) φ) =
      fun φ ω => X ω φ - ∫ z, u₀ z * φ z := by
    funext φ ω
    rw [sub_apply, smoothDist_apply_eq hu₀c]
  rw [e]
  exact hp

theorem isHarmonicDistOn_smoothDist_of {g : ℝ → ℝ} {S : Set ℝ} {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension g S u₀) :
    IsHarmonicDistOn (smoothDist upperHalfPlaneOpens u₀) H :=
  ⟨u₀, hu₀.1, fun φ _ => smoothDist_apply_eq (fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt) φ⟩

section Local

variable {Ω₀ : Type u} {mΩ₀ : MeasurableSpace Ω₀} {P₀ : Measure Ω₀} {𝓕₀ : Filtration ℝ≥0 mΩ₀}
  {W : ℝ≥0 → Ω₀ → ℝ} {ζ : Ω₀ → ℝ≥0∞}

/-- **A projection-independent coupling over a locally exhausting family is family-local** for the centred field
`p.2 − T₀` on `Ω₀ × 𝒟'(ℍ)`, `T₀` a deterministic distribution harmonic on `ℍ` (it annihilates the Dirichlet
directions, and its phase cancels). -/
theorem isFamilyLocal_of_projCoupling [IsProbabilityMeasure P₀]
    {ι : Type} [Countable ι] (U : ι → Set ℂ) (hUo : ∀ i, IsOpen (U i)) (hUH : ∀ i, U i ⊆ H)
    (s : ι → Ω₀ → ℝ≥0)
    (hs : ∀ i, IsStoppingTime (usualAugmentation 𝓕₀ P₀) fun ω => (s i ω : WithTop ℝ≥0))
    (hexh : ∀ᵐ ω ∂P₀, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∀ K : Set ℂ, IsCompact K → K ⊆ H →
      Disjoint K (fwdHull (fun r : ℝ => W r.toNNReal ω) t) → ∀ O : Set ℂ, IsOpen O → K ⊆ O →
        ∃ i, K ⊆ U i ∧ U i ⊆ O ∧ t ≤ s i ω)
    {μ : Measure (Ω₀ × DistOn upperHalfPlaneOpens)} (hμ1 : μ.map Prod.fst = P₀)
    {T₀ : DistOn upperHalfPlaneOpens} (hT₀ : IsHarmonicDistOn T₀ H)
    (hproj : ∀ i, IsProjIndepCoupling ⟨U i, hUo i⟩ (hs i) μ) :
    IsFamilyLocal μ (filtrationFst 𝓕₀ (DistOn upperHalfPlaneOpens)) (fun t p => W t p.1)
      (fun p => ζ p.1) (fun p => p.2 - T₀) := by
  refine ⟨ι, inferInstance, fun i => ⟨U i, hUo i⟩, fun i p => s i p.1,
    fun i => isStoppingTime_fst hμ1 (hs i), hUH, ?_, ?_⟩
  · intro i f Ξ D hD
    obtain ⟨A₀, hA₀, hDA⟩ := exists_fst_ae_eq_of_measurableSet_stopped hμ1 (hs i) hD
    have hUi : (⟨U i, hUo i⟩ : Opens ℂ) ≤ upperHalfPlaneOpens := hUH i
    have h0 : T₀ (lapTest ⟨U i, hUo i⟩ f) = 0 :=
      IsHarmonicDistOn.apply_lapTest_eq_zero isOpen_H hT₀ hUi (hUH i) f
    have key := hproj i f Ξ A₀ hA₀
    rw [setIntegral_congr_set hDA, setIntegral_congr_set hDA]
    have e1 : ∀ p : Ω₀ × DistOn upperHalfPlaneOpens,
        Complex.exp (Complex.I * (((p.2 - T₀) (lapTest ⟨U i, hUo i⟩ f + Ξ) : ℝ) : ℂ)) =
          Complex.exp (Complex.I * ((p.2 (lapTest ⟨U i, hUo i⟩ f + Ξ) : ℝ) : ℂ)) *
            Complex.exp (Complex.I * ((-(T₀ Ξ) : ℝ) : ℂ)) := fun p => by
      rw [← Complex.exp_add, sub_apply, map_add T₀, h0, zero_add]
      congr 1
      push_cast
      ring
    have e2 : ∀ p : Ω₀ × DistOn upperHalfPlaneOpens,
        Complex.exp (Complex.I * (((p.2 - T₀) Ξ : ℝ) : ℂ)) =
          Complex.exp (Complex.I * ((p.2 Ξ : ℝ) : ℂ)) *
            Complex.exp (Complex.I * ((-(T₀ Ξ) : ℝ) : ℂ)) := fun p => by
      rw [← Complex.exp_add, sub_apply]
      congr 1
      push_cast
      ring
    simp_rw [e1, e2, integral_mul_const, key]
    ring
  · rw [← hμ1] at hexh
    exact ae_of_ae_map measurable_fst.aemeasurable hexh

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω₀ → ℝ} {VR : Fin nR → ℝ≥0 → Ω₀ → ℝ} {B : ℝ≥0 → Ω₀ → ℝ}

/-- **The coupling of Theorem 1.1 with locality.** From an integrated evolution whose usual augmentation is almost
surely generated by countably many coordinates `G` and the named input `FiniteFamilyProjStatement`: a coupling on
`Ω₀ × 𝒟'(ℍ)` that is family-sampled and, for the centred field, family-local. -/
theorem exists_locCoupling_of_evolution [IsProbabilityMeasure P₀] (hκ : 0 < κ)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P₀ 𝓕₀ W VL VR B ζ)
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
        IsFamilyLocal μ (filtrationFst 𝓕₀ (DistOn upperHalfPlaneOpens)) (fun t p => W t p.1)
          (fun p => ζ p.1) (fun p => p.2 - smoothDist upperHalfPlaneOpens u₀) := by
  set u : Ω₀ → ℝ≥0 → ℂ → ℝ := fun ω s => Impl.forceExt κ (weightWord ρL ρR)
    (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω) with hudef
  have hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s) := fun ω s =>
    Impl.isBoundedHarmonicExtension_forceExt κ (weightWord ρL ρR) _ _
  have hcont : ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR)
      (forceJumpSet xL xR) u₀ → ContinuousOn u₀ H := fun u₀ hu₀ z hz =>
    (hu₀.1 z hz).1.continuousAt.continuousWithinAt
  by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · -- an inadmissible seed: `ζ = 0` almost surely and the family is empty
    have hζ0 := ae_zeta_eq_zero_of_threshold hE hseed
    set U0 : Empty → Set ℂ := fun i => i.elim
    set s0 : Empty → Ω₀ → ℝ≥0 := fun i => i.elim
    have hs0 : ∀ i, IsStoppingTime (usualAugmentation 𝓕₀ P₀) fun ω => (s0 i ω : WithTop ℝ≥0) :=
      fun i => i.elim
    have hU0o : ∀ i, IsOpen (U0 i) := fun i => i.elim
    obtain ⟨α, hαp, hαG, hfin⟩ := hI2 Ω₀ _ P₀ inferInstance 𝓕₀ W VL VR B ζ hE u hu Empty inferInstance
      U0 U0 hU0o (fun i => i.elim) s0 hs0 (fun i => i.elim)
    obtain ⟨μ, hμp, hμ1, hμ2, -⟩ := hfin ∅
    have hexh : ∀ᵐ ω ∂P₀, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∀ K : Set ℂ, IsCompact K → K ⊆ H →
        Disjoint K (fwdHull (fun r : ℝ => W r.toNNReal ω) t) → ∃ i, K ⊆ U0 i ∧ t ≤ s0 i ω := by
      filter_upwards [hζ0] with ω h t ht
      rw [h] at ht
      exact absurd ht not_lt_zero
    have hexhL : ∀ᵐ ω ∂P₀, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∀ K : Set ℂ, IsCompact K → K ⊆ H →
        Disjoint K (fwdHull (fun r : ℝ => W r.toNNReal ω) t) → ∀ O : Set ℂ, IsOpen O → K ⊆ O →
          ∃ i, K ⊆ U0 i ∧ U0 i ⊆ O ∧ t ≤ s0 i ω := by
      filter_upwards [hζ0] with ω h t ht
      rw [h] at ht
      exact absurd ht not_lt_zero
    exact ⟨α, μ, hαp, hμp, hμ1, hμ2, hαG,
      isFamilySampled_of_isSampledCoupling hE hκ u hu U0 s0 hs0 (fun i => i.elim) hexh hμ1
        (fun i => i.elim),
      fun u₀ hu₀ => isFamilyLocal_of_projCoupling U0 hU0o (fun i => i.elim) s0 hs0 hexhL hμ1
        (isHarmonicDistOn_smoothDist_of hu₀) fun i => i.elim⟩
  · -- an admissible seed: the announcing sequence and the locally exhausting rational-ball family
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
    have hexhL : ∀ᵐ ω ∂P₀, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∀ K : Set ℂ, IsCompact K → K ⊆ H →
        Disjoint K (fwdHull (fun r : ℝ => W r.toNNReal ω) t) → ∀ O : Set ℂ, IsOpen O → K ⊆ O →
          ∃ i, K ⊆ U i ∧ U i ⊆ O ∧ t ≤ s i ω :=
      hexh.mono fun ω h t ht K hK hKH hdis O hO hKO => by
        obtain ⟨i, h1, h2, h3⟩ := h t ht K hK hKH hdis O hO hKO
        exact ⟨i, h1, (ballsU_subset_ballsK _).trans h2, h3⟩
    exact ⟨α, μ, hαp, hμp, hμ1, hμ2, hαG,
      isFamilySampled_of_isSampledCoupling hE hκ u hu U s hs hsafeU hexhOld hμ1 fun i => (hμs i).1,
      fun u₀ hu₀ => isFamilyLocal_of_projCoupling U hUo hUH s hs hexhL hμ1
        (isHarmonicDistOn_smoothDist_of hu₀) fun i => (hμs i).2⟩

end Local

/-! ### The provider -/

/-- **Theorem 1.1, conditional provider form** (frozen arguments all implicit, every universe; PROVE-COMMON provider
convention). From **exactly the statement of the frozen Theorem 2.2** for this force word (`hI1`, an integrated
evolution on some `Ω : Type`) and the named input `FiniteFamilyProjStatement` (finite-family couplings sampled and
projection-independent at their members), the frozen statement of Theorem 1.1 holds. No standard Borel assumption:
the evolution is lifted to `ULift Ω` and read in the usual augmentation of its rational-time coordinates; locality is
`isLocalSet_hull_of_isFamilyLocal`. -/
theorem exists_isOptionalHullCoupling_of_finiteFamilyProj {κ : ℝ} (hκ : 0 < κ := by assumption)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (_hF : IsOrderedForceWord xL xR := by assumption)
    (hI1 : ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hI2 : FiniteFamilyProjStatement.{u} κ xL xR ρL ρR) :
    ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ := hI1
  set P₀ : Measure (ULift.{u} Ω) := P.map ULift.up with hP₀
  have hP₀p : IsProbabilityMeasure P₀ := inferInstance
  have hmap : P₀.map ULift.down = P := by
    rw [hP₀, Measure.map_map measurable_down measurable_up]
    exact Measure.map_id
  have hE₀ := IsIntegratedSLEEvolution.comap measurable_down hmap hE
  have hc := measurable_coordVal hE₀
  have hE₁ := isIntegratedSLEEvolution_coordFiltration hE₀
  have hgen := IsAeGen.usualAugmentation (IsAeGen.usualAugmentation (P₀ := P₀)
    (isAeGen_coordFiltration (P₀ := P₀) hc))
  obtain ⟨α, μ, hαp, hμp, hμ1, hμ2, hαG, hfamS, hfamL⟩ :=
    exists_locCoupling_of_evolution hκ hE₁ (measurable_coordMap hc) hgen hI2
  set u₀ : ℂ → ℝ := Impl.forceExt κ (weightWord ρL ρR) xL xR with hu₀def
  have hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀ :=
    Impl.isBoundedHarmonicExtension_forceExt κ (weightWord ρL ρR) xL xR
  have hu₀c : ContinuousOn u₀ H := fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt
  have hEμ := IsIntegratedSLEEvolution.fst (X := DistOn upperHalfPlaneOpens) hμ1 hE₁
  have hZμ : IsZeroBoundaryGFF upperHalfPlaneOpens
      (fun p : ULift.{u} Ω × DistOn upperHalfPlaneOpens => p.2 - smoothDist upperHalfPlaneOpens u₀) μ :=
    isZeroBoundaryGFF_sub_smoothDist measurable_snd hu₀c (isZBGFFProcess_comp_snd hμ2 (hαG u₀ hu₀))
  have hharm : IsHarmonicDistOn (smoothDist upperHalfPlaneOpens u₀) H :=
    isHarmonicDistOn_smoothDist_of hu₀
  refine ⟨ULift.{u} Ω × DistOn upperHalfPlaneOpens, inferInstance, μ, hμp, _, _, _, _, _, _,
    fun p => p.2, isOptionalHullCoupling_of_isFamilySampled hEμ hκ measurable_snd
      (fun u₀' hu₀' => isZBGFFProcess_comp_snd hμ2 (hαG u₀' hu₀')) hfamS fun hX τ hτ hτζ => ?_⟩
  have hl := isLocalSet_hull_of_isFamilyLocal hEμ hX hZμ (hfamL u₀ hu₀) hτ hτζ
  have hl' := IsLocalSet.add_dist hl hharm
  have e : (fun p : ULift.{u} Ω × DistOn upperHalfPlaneOpens =>
      p.2 - smoothDist upperHalfPlaneOpens u₀ + smoothDist upperHalfPlaneOpens u₀) = fun p => p.2 :=
    funext fun p => sub_add_cancel _ _
  rw [e] at hl'
  exact hl'

end Coupling

end InteractingSLE
