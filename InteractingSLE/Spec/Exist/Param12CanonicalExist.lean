/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.Param12CanonicalSuff
import InteractingSLE.Spec.Sec2.Assembly2Entr

/-!
# Every ordered word has a canonical coupling law (S4, non-emptiness)

Packet PROVE-PARAM12C. For an ordered word `θ` and `κ > 0`:

1. an integrated evolution of `θ` (the landed Theorem 2.2) has a code law that is an evolution law (S3 necessity), so
   the canonical processes on the code space form an evolution for the code filtration (S3 sufficiency);
2. Theorem 1.1's construction (`Coupling.exists_locCoupling_of_evolution`, with the finite-family input
   `finiteFamilyProjStatement`) on the code space gives a coupling `μ` of the code law and a field law, family-sampled
   and family-local;
3. `μ` satisfies `CanonCond κ θ`: the field law is `fieldLawW` (uniqueness of the zero-boundary GFF law); the dyadic
   sampling identities follow from the constraint at the stopping times `q ∧ T_m` (`T` announcing the lifetime) and
   monotone convergence in `m`; the dyadic projection-independence identities follow from the family-local constraint
   cut along the stops above `q` (`setIntegral_eq_mul_of_pieces`) and the resampling characterization.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal Classical RealInnerProductSpace

universe u

namespace InteractingSLE

namespace Exist

namespace Param12

open Sec2.Assembly Coupling Ito Staged LQGMetric Restart GFF

variable {nL nR : ℕ}

/-! ### The field law is determined by the zero-boundary GFF property -/

/-- A probability law of fields whose centred pairings form a zero-boundary GFF is `fieldLaw0 u₀`. -/
theorem eq_fieldLaw0_of_isZBGFFProcess {α : Measure (DistOn upperHalfPlaneOpens)} [IsProbabilityMeasure α]
    {u₀ : ℂ → ℝ} (hu₀c : ContinuousOn u₀ H)
    (g₁ : IsZBGFFProcess upperHalfPlaneOpens (fun φ x => x φ - ∫ z, u₀ z * φ z) α) :
    α = fieldLaw0 u₀ := by
  rw [fieldLaw0_eq_map]
  have g₂ : IsZBGFFProcess upperHalfPlaneOpens (fun φ (g : DistOn upperHalfPlaneOpens) => g φ)
      (zbLaw upperHalfPlaneOpens) := (isZeroBoundaryGFF_zbLaw (fun _ hz => hz)).process
  have e := g₁.map_eq g₂
  obtain ⟨c, hc⟩ : ∃ c : TestOn upperHalfPlaneOpens → ℝ, c = fun φ => ∫ z, u₀ z * φ z := ⟨_, rfl⟩
  have hadd : Measurable fun f : TestOn upperHalfPlaneOpens → ℝ => f + c := measurable_id.add_const c
  have hT : Measurable fun g : DistOn upperHalfPlaneOpens => g + meanH u₀ :=
    measurable_distOn_iff.2 fun φ => (measurable_distOn_apply φ).add_const _
  have hd₁ : distEval upperHalfPlaneOpens =
      (fun f => f + c) ∘ zbPath (fun φ (x : DistOn upperHalfPlaneOpens) => x φ - ∫ z, u₀ z * φ z) := by
    funext x φ; simp [zbPath, distEval, hc]
  have hd₂ : distEval upperHalfPlaneOpens ∘ (fun g => g + meanH u₀) =
      (fun f => f + c) ∘ zbPath (fun φ (g : DistOn upperHalfPlaneOpens) => g φ) := by
    funext g φ
    have := meanH_apply_eq hu₀c φ
    simp only [Function.comp_apply, distEval, zbPath, Pi.add_apply, hc]
    rw [← this]
    rfl
  have hz₁ : Measurable (zbPath (fun φ (x : DistOn upperHalfPlaneOpens) => x φ - ∫ z, u₀ z * φ z)) :=
    measurable_pi_iff.2 g₁.measurable
  have hz₂ : Measurable (zbPath fun φ (g : DistOn upperHalfPlaneOpens) => g φ) :=
    measurable_pi_iff.2 g₂.measurable
  have hD : α.map (distEval upperHalfPlaneOpens) =
      (zbLaw upperHalfPlaneOpens).map (distEval upperHalfPlaneOpens ∘ fun g => g + meanH u₀) := by
    rw [hd₂, hd₁, ← Measure.map_map hadd hz₁, ← Measure.map_map hadd hz₂, e]
  ext s hs
  obtain ⟨t, ht, rfl⟩ := hs
  have := congrArg (fun μ : Measure (TestOn upperHalfPlaneOpens → ℝ) => μ t) hD
  rw [Measure.map_apply (measurable_distEval _) ht,
    Measure.map_apply ((measurable_distEval _).comp hT) ht] at this
  change α (distEval upperHalfPlaneOpens ⁻¹' t) =
    ((zbLaw upperHalfPlaneOpens).map fun g => g + meanH u₀) (distEval upperHalfPlaneOpens ⁻¹' t)
  rw [Measure.map_apply hT (measurable_distEval _ ht)]
  exact this

/-! ### Helpers on the canonical space -/

section Helpers

/-- `cfAt` does not depend on the bounded harmonic extension off `ℍ`: at a time where `supp ψ` is alive, two
extensions agreeing on `ℍ` give the same value. -/
theorem cfAt_eq_of_eqOn {Ω : Type*} {κ : ℝ} {W : ℝ≥0 → Ω → ℝ} {u u' : Ω → ℝ≥0 → ℂ → ℝ} {ψ : ℂ → ℝ}
    {θ' : ℝ} {r : Ω → ℝ≥0} {ω : Ω} (hcont : ContinuousOn (rpath (W · ω)) (Icc 0 (r ω : ℝ)))
    (halive : ∀ z ∈ tsupport ψ, z ∈ H ∧ ∃ v, IsForwardSol (rpath (W · ω)) z (r ω) v)
    (heq : EqOn (u ω (r ω)) (u' ω (r ω)) H) :
    cfAt κ W u ψ θ' r ω = cfAt κ W u' ψ θ' r ω := by
  have hm : (∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) (r ω) (u ω (r ω)) z * ψ z) =
      ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) (r ω) (u' ω (r ω)) z * ψ z := by
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    by_cases hz : z ∈ tsupport ψ
    · obtain ⟨hzH, hsol⟩ := halive z hz
      have hpos := im_fwdMap_pos_of_continuousOn (r ω).coe_nonneg hcont hzH hsol
        ⟨(r ω).coe_nonneg, le_rfl⟩
      simp only [couplingMean]
      rw [show u ω (r ω) (fwdMap (fun s : ℝ => W s.toNNReal ω) (r ω) z) =
        u' ω (r ω) (fwdMap (fun s : ℝ => W s.toNNReal ω) (r ω) z) from heq hpos]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  simp only [cfAt, hm]

variable {π : Measure (XCode nL nR × DistOn upperHalfPlaneOpens)}

theorem integrable_cfAlive_of_ae {κ : ℝ} {θ : WordData nL nR}
    (hae : ∀ᵐ p ∂π, p.1 ∈ CRel κ θ.1.1 θ.1.2 θ.2.1 θ.2.2) [IsFiniteMeasure π] {K : Set ℂ} (hK : IsCompact K)
    (hKH : K ⊆ H) (ψ : TestOn upperHalfPlaneOpens) (hψK : tsupport (ψ : ℂ → ℝ) ⊆ K) (q : ℝ≥0) :
    Integrable (cfAlive κ θ K ψ q) π := by
  refine Integrable.of_bound (measurable_cfAlive κ θ hK hKH ψ hψK q).aestronglyMeasurable 1 ?_
  filter_upwards [hae] with p hp
  unfold cfAlive
  by_cases ha : (θ, p.1).2 ∈ codeAlive K q
  · rw [ite_eq_left_iff.2 fun h => absurd ha h]
    obtain ⟨hg, hq, hal⟩ := ha
    exact norm_cfAt_le_one (W := cwP) (uP κ) 1 ψ (r := fun _ => q) (ω := (θ, p.1))
      (continuousOn_rpath hg.continuousOn_w hq) hp.1.2.2.1 fun z hz => hal z (hψK hz)
  · rw [ite_eq_right_iff.2 fun h => absurd h ha, norm_zero]; exact zero_le_one

/-- Alive events are events of the usual augmentation of the lifted code filtration at their time. -/
theorem measurableSet_fst_codeAlive_aug [IsFiniteMeasure π] (hgood : ∀ᵐ p ∂π, Good p.1) {K : Set ℂ}
    (hK : IsCompact K) (hKH : K ⊆ H) (q : ℝ≥0) :
    MeasurableSet[usualAugmentation (filtrationFst (codeFilt (nL := nL) (nR := nR)) (DistOn upperHalfPlaneOpens)) π q]
      (Prod.fst ⁻¹' codeAlive K q) := by
  set 𝓖 := usualAugmentation (filtrationFst (codeFilt (nL := nL) (nR := nR)) (DistOn upperHalfPlaneOpens)) π
  have hle : filtrationFst (codeFilt (nL := nL) (nR := nR)) (DistOn upperHalfPlaneOpens) ≤ 𝓖 :=
    Ito.le_usualAugmentation _ _
  have hW : AdaptedBefore 𝓖 (fun p => cζ p.1) fun t p => cw p.1 t := fun t A hA =>
    hle t _ (MeasurableSpace.measurableSet_comap.2 ⟨_, adaptedBefore_cw t A hA, rfl⟩)
  set G : Set (XCode nL nR × DistOn upperHalfPlaneOpens) := Prod.fst ⁻¹' {x | Good x}
  have hGm : MeasurableSet G := measurable_fst measurableSet_good
  have hG0 : MeasurableSet[𝓖 0] G := by
    have h := measurableSet_usualAugmentation_of_null (𝓕 := filtrationFst (codeFilt (nL := nL) (nR := nR))
      (DistOn upperHalfPlaneOpens)) hGm.compl (ae_iff.1 hgood) 0
    have := h.compl
    rwa [compl_compl] at this
  have e : Prod.fst ⁻¹' codeAlive K q = ⋃ j : ℕ, {p : XCode nL nR × DistOn upperHalfPlaneOpens |
      p ∈ G ∧ IsSafeAt K (1 / ((j : ℝ) + 1)) q q (cζ p.1) (fun t => cw p.1 t) q} := by
    rw [codeAlive_eq_iUnion hK hKH q, preimage_iUnion]
    rfl
  rw [e]
  refine MeasurableSet.iUnion fun j => ?_
  obtain ⟨D, hDK, hDc, hKD⟩ := (TopologicalSpace.IsSeparable.of_separableSpace K).exists_countable_dense_subset
  have hδ : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
  have h := measurableSet_isSafeAt hW (fun p hp => Good.continuousOn_w hp) hG0 hDc (hDK.trans hKH)
    (σ₀ := fun _ => q) (isStoppingTime_const _ q) (1 / ((j : ℝ) + 1)) q q
  convert h using 1
  ext p
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨hg, hs⟩; exact ⟨hg, hs.subset hDK⟩
  · rintro ⟨hg, hs⟩; exact ⟨hg, hs.of_dense (Good.continuousOn_w hg) hKH hKD hDK hδ⟩

end Helpers

/-! ### The dyadic constraints of the landed coupling -/

section Dyadic

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {ν₀ : Measure (XCode nL nR)} [IsProbabilityMeasure ν₀]
  {μ : Measure (XCode nL nR × DistOn upperHalfPlaneOpens)} [IsProbabilityMeasure μ]

/-- An event of the filtration at `q` contained in `{q ≤ τ}` is an event of the stopped σ-algebra at `τ`. -/
theorem measurableSet_stopped_of_le_const {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ}
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ) {q : ℝ≥0} {D : Set Ω} (hD : MeasurableSet[𝓖 q] D)
    (hDle : ∀ ω ∈ D, (q : WithTop ℝ≥0) ≤ τ ω) : MeasurableSet[hτ.measurableSpace] D := by
  have hc := isStoppingTime_const 𝓖 q
  refine measurableSet_stopped_of_le hc hτ ?_ hDle
  rw [IsStoppingTime.measurableSpace_const]
  exact hD

theorem measurableSet_fst_condEv_aug (hgood : ∀ᵐ p ∂μ, Good p.1) (F : RatBallSet) (q : ℝ≥0)
    {A : Set (ObsY nL nR)} (hA : MeasurableSet A) :
    MeasurableSet[usualAugmentation (filtrationFst (codeFilt (nL := nL) (nR := nR)) (DistOn upperHalfPlaneOpens)) μ q]
      (Prod.fst ⁻¹' condEv F q A) := by
  have h1 : MeasurableSet[filtrationFst (codeFilt (nL := nL) (nR := nR)) (DistOn upperHalfPlaneOpens) q]
      (Prod.fst ⁻¹' (codeObs q ⁻¹' A)) :=
    MeasurableSpace.measurableSet_comap.2 ⟨_, MeasurableSpace.measurableSet_comap.2 ⟨A, hA, rfl⟩, rfl⟩
  exact (Ito.le_usualAugmentation _ _ q _ h1).inter
    (measurableSet_fst_codeAlive_aug hgood (isCompact_ballsK F.1) F.2 q)

/-- The constraint at every stopping time for a family-sampled coupling (`StopFamily`), with the extension `u` of
the family. -/
theorem setIntegral_cexp_eq_cfAt_of_isFamilySampled {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ)
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : ∀ ψ, Measurable fun ω => h ω ψ)
    (hfam : IsFamilySampled κ ρL ρR P 𝓕 W VL VR ζ h) (ψ : TestOn upperHalfPlaneOpens) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (τ ω : WithTop ℝ≥0))
    (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A)
    (hAE : A ⊆ {ω | Disjoint (tsupport ψ) (fwdHull (fun r : ℝ => W r.toNNReal ω) (τ ω))}) :
    ∃ u : Ω → ℝ≥0 → ℂ → ℝ, (∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s)) ∧
      ∫ ω in A, Complex.exp (Complex.I * (h ω ψ : ℂ)) ∂P = ∫ ω in A, cfAt κ W u ψ 1 τ ω ∂P := by
  obtain ⟨u, hu, ι, _, U, s, hs, hsafe, hsamp, hexh⟩ := hfam
  exact ⟨u, hu, setIntegral_cexp_eq_cfAt_of_family hE hκ u hu h hh U s hs hsafe hsamp hexh ψ hτ hτζ hA hAE⟩

/-- The alive-restricted protected characteristic function as `cfAt` on the canonical space. -/
theorem cfAlive_eq_cfAt (κ : ℝ) (θ : WordData nL nR) {K : Set ℂ} (ψ : TestOn upperHalfPlaneOpens) (q : ℝ≥0)
    {p : XCode nL nR × DistOn upperHalfPlaneOpens} (hp : p.1 ∈ codeAlive K q) :
    cfAlive κ θ K ψ q p =
      cfAt κ (fun t (p : XCode nL nR × DistOn upperHalfPlaneOpens) => cw p.1 t) (fun p t => uP κ (θ, p.1) t)
        ψ 1 (fun _ => q) p := by
  have hp2 : (θ, p.1).2 ∈ codeAlive K q := hp
  unfold cfAlive
  rw [ite_eq_left_iff.2 fun h => absurd hp2 h]
  rfl

/-- At a stop equal to `q` where `K ⊇ supp ψ` is alive, the protected characteristic function of any bounded harmonic
extension of the state is `cfAlive`. -/
theorem cfAt_eq_cfAlive {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {u' : XCode nL nR × DistOn upperHalfPlaneOpens → ℝ≥0 → ℂ → ℝ}
    (hu' : ∀ p s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => cvL p.1 i s - cw p.1 s) (fun j => cvR p.1 j s - cw p.1 s))
      (forceJumpSet (fun i => cvL p.1 i s - cw p.1 s) (fun j => cvR p.1 j s - cw p.1 s)) (u' p s))
    {K : Set ℂ} (hKH : K ⊆ H) (ψ : TestOn upperHalfPlaneOpens) (hψK : tsupport (ψ : ℂ → ℝ) ⊆ K) {q : ℝ≥0}
    {τ : XCode nL nR × DistOn upperHalfPlaneOpens → ℝ≥0} {p : XCode nL nR × DistOn upperHalfPlaneOpens}
    (hτp : τ p = q) (hp : p.1 ∈ codeAlive K q) :
    cfAt κ (fun t (p : XCode nL nR × DistOn upperHalfPlaneOpens) => cw p.1 t) u' ψ 1 τ p =
      cfAlive κ (((xL, xR), (ρL, ρR)) : WordData nL nR) K ψ q p := by
  obtain ⟨hg, hq, hal⟩ := hp
  rw [cfAlive_eq_cfAt κ _ ψ q ⟨hg, hq, hal⟩, cfAt_congr u' 1 (r' := fun _ => q) hτp]
  refine cfAt_eq_of_eqOn (continuousOn_rpath hg.continuousOn_w hq)
    (fun z hz => ⟨hKH (hψK hz), hal z (hψK hz)⟩) ?_
  exact Impl.eqOn_of_isBoundedHarmonicExtension (Impl.forceJumpSet_finite (weightWord ρL ρR) _ _)
    (isBoundedHarmonicExtension_uP κ (_, p.1) q) (hu' p q)

omit [IsProbabilityMeasure μ] in
/-- One piece of the dyadic sampling identities: on an event of the stopped σ-algebra at a stop `τ` that equals `q`
there and inside the alive event, the field's characteristic functional integrates to `cfAlive`. -/
theorem setIntegral_cexp_eq_cfAlive_of_family (hκ : 0 < κ)
    (hEμ : IsIntegratedSLEEvolution κ xL xR ρL ρR μ
      (filtrationFst (codeFilt (nL := nL) (nR := nR)) (DistOn upperHalfPlaneOpens)) (fun t p => cw p.1 t)
      (fun i t p => cvL p.1 i t) (fun j t p => cvR p.1 j t) (fun t p => cb p.1 t) (fun p => cζ p.1))
    (hfamS : IsFamilySampled κ ρL ρR μ (filtrationFst (codeFilt (nL := nL) (nR := nR)) (DistOn upperHalfPlaneOpens))
      (fun t p => cw p.1 t) (fun i t p => cvL p.1 i t) (fun j t p => cvR p.1 j t) (fun p => cζ p.1)
      (fun p => p.2))
    {K : Set ℂ} (hKH : K ⊆ H) (ψ : TestOn upperHalfPlaneOpens) (hψK : tsupport (ψ : ℂ → ℝ) ⊆ K) (q : ℝ≥0)
    {τ : XCode nL nR × DistOn upperHalfPlaneOpens → ℝ≥0}
    (hτ : IsStoppingTime (usualAugmentation (filtrationFst (codeFilt (nL := nL) (nR := nR))
      (DistOn upperHalfPlaneOpens)) μ) fun p => (τ p : WithTop ℝ≥0))
    (hτζ : ∀ᵐ p ∂μ, (τ p : ℝ≥0∞) < cζ p.1) {D : Set (XCode nL nR × DistOn upperHalfPlaneOpens)}
    (hD : MeasurableSet[hτ.measurableSpace] D) (hDq : ∀ p ∈ D, τ p = q)
    (hDK : D ⊆ Prod.fst ⁻¹' codeAlive K q) :
    ∫ p in D, Complex.exp (Complex.I * (p.2 ψ : ℂ)) ∂μ =
      ∫ p in D, cfAlive κ ((xL, xR), (ρL, ρR)) K ψ q p ∂μ := by
  have hAE : D ⊆ {p | Disjoint (tsupport (ψ : ℂ → ℝ)) (fwdHull (fun r : ℝ => cw p.1 r.toNNReal) (τ p))} := by
    intro p hp
    obtain ⟨hg, hq, hal⟩ := hDK hp
    show Disjoint _ (fwdHull _ ((τ p : ℝ≥0) : ℝ))
    rw [hDq p hp]
    exact Set.disjoint_left.2 fun z hz =>
      notMem_fwdHull_of_alive hg.continuousOn_w hq (hKH (hψK hz)) (hal z (hψK hz))
  obtain ⟨u', hu', h⟩ := setIntegral_cexp_eq_cfAt_of_isFamilySampled hEμ hκ
    (fun ψ' => (measurable_distOn_apply ψ').comp measurable_snd) hfamS ψ hτ hτζ hD hAE
  rw [h]
  exact setIntegral_congr_fun (hτ.measurableSpace_le _ hD) fun p hp =>
    cfAt_eq_cfAlive hu' hKH ψ hψK (hDq p hp) (hDK hp)

/-- **The dyadic sampling identities for the coupling of Theorem 1.1's construction** on the code space. -/
theorem sampled_of_family (hκ : 0 < κ) (hEv : IsEvoLaw κ ((xL, xR), (ρL, ρR)) ν₀) (hμ1 : μ.map Prod.fst = ν₀)
    (hfamS : IsFamilySampled κ ρL ρR μ (filtrationFst (codeFilt (nL := nL) (nR := nR)) (DistOn upperHalfPlaneOpens))
      (fun t p => cw p.1 t) (fun i t p => cvL p.1 i t) (fun j t p => cvR p.1 j t) (fun p => cζ p.1)
      (fun p => p.2))
    (F : RatBallSet) (n k : ℕ) {A : Set (ObsY nL nR)} (hA : MeasurableSet A) (j : RatComb) :
    sampL F (dyad n k) A j μ = sampR κ F (dyad n k) A j ((xL, xR), (ρL, ρR)) μ := by
  set θ : WordData nL nR := ((xL, xR), (ρL, ρR)) with hθ
  set q := dyad n k
  set ψ := sampTest F j
  have hK := isCompact_ballsK F.1
  have hKH := F.2
  have hψK := tsupport_sampTest_subset F j
  set S : Set (XCode nL nR × DistOn upperHalfPlaneOpens) := Prod.fst ⁻¹' condEv F q A with hS
  have hSm : MeasurableSet S := measurable_fst (measurableSet_condEv F q hA)
  have hE₁ := isIntegratedSLEEvolution_canon hEv
  have hEμ : IsIntegratedSLEEvolution κ xL xR ρL ρR μ
      (filtrationFst (codeFilt (nL := nL) (nR := nR)) (DistOn upperHalfPlaneOpens)) (fun t p => cw p.1 t)
      (fun i t p => cvL p.1 i t) (fun j t p => cvR p.1 j t) (fun t p => cb p.1 t) (fun p => cζ p.1) :=
    IsIntegratedSLEEvolution.fst (X := DistOn upperHalfPlaneOpens) hμ1 hE₁
  have hae : ∀ᵐ p ∂μ, p.1 ∈ CRel κ xL xR ρL ρR := by
    rw [← hμ1] at hEv; exact ae_of_ae_map measurable_fst.aemeasurable hEv.ae_mem
  rw [sampL, sampR, integral_ite_fst (measurableSet_condEv F q hA), integral_ite_fst (measurableSet_condEv F q hA)]
  have hRS : ∫ p in S, cfAt κ cwP (uP κ) ψ 1 (fun _ => q) (θ, p.1) ∂μ =
      ∫ p in S, cfAlive κ θ (ballsK F.1) ψ q p ∂μ :=
    setIntegral_congr_fun hSm fun p hp => by
      have hp2 : (θ, p.1).2 ∈ codeAlive (ballsK F.1) q := hp.2
      simp only [cfAlive, hp2, ↓reduceIte]
  rw [hRS]
  have hGi := integrable_cfAlive_of_ae (θ := θ) hae hK hKH ψ hψK q
  have hFi : Integrable (fun p : XCode nL nR × DistOn upperHalfPlaneOpens =>
      Complex.exp (Complex.I * (p.2 ψ : ℂ))) μ := integrable_cexp_snd ψ
  by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · have hζ0 := ae_zeta_eq_zero_of_threshold hEμ hseed
    have hS0 : μ S = 0 := by
      refine measure_mono_null (fun p hp => ?_) (ae_iff.1 hζ0)
      intro h0
      have h1 : (q : ℝ≥0∞) < cζ p.1 := hp.2.2.1
      rw [show cζ p.1 = 0 from h0] at h1
      exact not_lt_zero h1
    rw [setIntegral_measure_zero _ hS0, setIntegral_measure_zero _ hS0]
  · obtain ⟨T, hTst, hTmono, hTζ, hTex⟩ := exists_isAnnouncingSeq hEμ hκ hseed
    set 𝓖 := usualAugmentation (filtrationFst (codeFilt (nL := nL) (nR := nR)) (DistOn upperHalfPlaneOpens)) μ
    have hτ : ∀ m, IsStoppingTime 𝓖 fun p => ((min q (T m p) : ℝ≥0) : WithTop ℝ≥0) := fun m => by
      have h := (isStoppingTime_const 𝓖 q).min (hTst m)
      convert h using 2 with p
      rw [WithTop.coe_min]
    set Am : ℕ → Set (XCode nL nR × DistOn upperHalfPlaneOpens) := fun m => S ∩ {p | q ≤ T m p} with hAm_def
    have hgood : ∀ᵐ p ∂μ, Good p.1 := hae.mono fun p hp => hp.1.1
    have hS𝓖 : MeasurableSet[𝓖 q] S := measurableSet_fst_condEv_aug hgood F q hA
    have hAm𝓖 : ∀ m, MeasurableSet[𝓖 q] (Am m) := fun m => by
      have h := ((hTst m).measurableSet_lt q).compl
      refine hS𝓖.inter ?_
      convert h using 1
      ext p
      simp only [mem_ofPred_eq, mem_compl_iff, WithTop.coe_lt_coe, not_lt]
    have hAm : ∀ m, MeasurableSet[(hτ m).measurableSpace] (Am m) := fun m =>
      measurableSet_stopped_of_le_const (hτ m) (hAm𝓖 m) fun p hp => by
        rw [WithTop.coe_le_coe]; exact le_min le_rfl hp.2
    have hAmm : ∀ m, MeasurableSet (Am m) := fun m => 𝓖.le q _ (hAm𝓖 m)
    have hτζ : ∀ m, ∀ᵐ p ∂μ, ((min q (T m p) : ℝ≥0) : ℝ≥0∞) < cζ p.1 := fun m =>
      (hTζ m).mono fun p h => lt_of_le_of_lt (by exact_mod_cast min_le_right _ _) h
    have hid : ∀ m, ∫ p in Am m, Complex.exp (Complex.I * (p.2 ψ : ℂ)) ∂μ =
        ∫ p in Am m, cfAlive κ θ (ballsK F.1) ψ q p ∂μ := fun m =>
      setIntegral_cexp_eq_cfAlive_of_family hκ hEμ hfamS hKH ψ hψK q
        (hτ m) (hτζ m) (hAm m) (fun p hp => min_eq_left hp.2) fun p hp => hp.1.2
    have hmono : Monotone Am := fun m m' hmm' p hp => ⟨hp.1, hp.2.trans (hTmono p hmm')⟩
    have hUae : (⋃ m, Am m : Set (XCode nL nR × DistOn upperHalfPlaneOpens)) =ᵐ[μ] S := by
      have hsub : (⋃ m, Am m) ⊆ S := iUnion_subset fun m => inter_subset_left
      refine EventuallyLE.antisymm (Eventually.of_forall fun p (hp : p ∈ ⋃ m, Am m) => hsub hp) (ae_le_set.2 ?_)
      have : S \ ⋃ m, Am m ⊆ {p | ¬ ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ p.1 → ∃ m, t ≤ T m p} := by
        rintro p ⟨hpS, hpU⟩ hall
        obtain ⟨m, hm⟩ := hall q hpS.2.2.1
        exact hpU (mem_iUnion.2 ⟨m, hpS, hm⟩)
      exact measure_mono_null this (ae_iff.1 hTex)
    have hL := tendsto_setIntegral_of_monotone hAmm hmono hFi.integrableOn
    have hR := tendsto_setIntegral_of_monotone hAmm hmono hGi.integrableOn
    rw [setIntegral_congr_set hUae] at hL hR
    exact tendsto_nhds_unique (hL.congr hid) hR

end Dyadic

/-! ### Projection independence at deterministic times from the family-local constraint -/

section ProjTime

/-- The nesting of the projection constraint: a Dirichlet direction of `O ⊆ V` is one of `V` with the same factor. -/
theorem lapTest_projFactor_incl {O V : TopologicalSpace.Opens ℂ} (hVH : (V : Set ℂ) ⊆ H) (hOV : (O : Set ℂ) ⊆ V)
    (f : LQGMetric.MarkovZB.zsSub (O : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) :
    LocalSets.lapTest V (zsSubIncl hOV f) = LocalSets.lapTest O f ∧
      projFactor V (zsSubIncl hOV f) Ξ = projFactor O f Ξ := by
  have hf1 : (zsSubIncl hOV f).1 = f.1 := rfl
  refine ⟨?_, ?_⟩
  · ext z
    rw [LocalSets.coe_lapTest (show V ≤ upperHalfPlaneOpens from hVH),
      LocalSets.coe_lapTest (show O ≤ upperHalfPlaneOpens from fun z hz => hVH (hOV hz))]
    rfl
  · rw [projFactor, projFactor, hf1, LocalSets.norm_gradFeat_eq hOV f.2,
      LocalSets.inner_gradFeat_covVec_eq O.isOpen V.isOpen hVH hOV f.2]

/-- **Projection independence on an event of the filtration at a time `q`** inside the event that a compact `K ⊇ O`
is outside the hull at `q`, from the family-local constraint of the centred field `h − T₀` (`T₀` harmonic): cut the
event along the stops `s_i ≥ q` of the members `U_i ⊇ K`. -/
theorem setIntegral_projIndep_of_isFamilyLocal {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : ∀ ψ, Measurable fun ω => h ω ψ)
    {T₀ : DistOn upperHalfPlaneOpens} (hT₀ : IsHarmonicDistOn T₀ H)
    (hfam : IsFamilyLocal P 𝓕 W ζ fun ω => h ω - T₀) {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H)
    (O : TopologicalSpace.Opens ℂ) (hOK : (O : Set ℂ) ⊆ K) {q : ℝ≥0} {S : Set Ω}
    (hS : MeasurableSet[usualAugmentation 𝓕 P q] S)
    (hSK : ∀ᵐ ω ∂P, ω ∈ S → (q : ℝ≥0∞) < ζ ω ∧ Disjoint K (fwdHull (fun r : ℝ => W r.toNNReal ω) q))
    (f : LQGMetric.MarkovZB.zsSub (O : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) :
    ∫ ω in S, Complex.exp (Complex.I * (h ω (LocalSets.lapTest O f + Ξ) : ℂ)) ∂P =
      projFactor O f Ξ * ∫ ω in S, Complex.exp (Complex.I * (h ω Ξ : ℂ)) ∂P := by
  obtain ⟨ι, hι, U, s, hs, hUH, hind, hexh⟩ := hfam
  have hm : usualAugmentation 𝓕 P q ≤ mΩ := (usualAugmentation 𝓕 P).le q
  set C : ι → Set Ω := fun i => if K ⊆ U i then S ∩ {ω | q ≤ s i ω} else ∅ with hC
  have hb : ∀ Ψ : TestOn upperHalfPlaneOpens, Integrable (fun ω => Complex.exp (Complex.I * (h ω Ψ : ℂ))) P :=
    fun Ψ => Integrable.of_bound (GFF.measurable_exp_I_mul (hh Ψ)).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => (Complex.norm_exp_I_mul_ofReal _).le)
  refine setIntegral_eq_mul_of_pieces hm (hb _) (hb _) _ C (fun i => ?_) (fun i => ?_) ?_ (fun i D hD hDC => ?_)
  · by_cases hi : K ⊆ U i
    · simp only [hC, hi, ↓reduceIte]
      have h1 := ((hs i).measurableSet_lt q).compl
      refine @MeasurableSet.inter _ (usualAugmentation 𝓕 P q) _ _ hS ?_
      convert h1 using 1
      ext ω
      simp only [mem_ofPred_eq, mem_compl_iff, WithTop.coe_lt_coe, not_lt]
    · simp only [hC, hi, ↓reduceIte]; exact @MeasurableSet.empty _ (usualAugmentation 𝓕 P q)
  · by_cases hi : K ⊆ U i
    · simp only [hC, hi, ↓reduceIte]; exact inter_subset_left
    · simp only [hC, hi, ↓reduceIte]; exact empty_subset _
  · filter_upwards [hSK, hexh] with ω hω hex hωS
    obtain ⟨hq, hdis⟩ := hω hωS
    obtain ⟨i, hKU, -, hqs⟩ := hex q hq K hK hKH hdis univ isOpen_univ (subset_univ K)
    refine ⟨i, ?_⟩
    simp only [hC, hKU, ↓reduceIte]
    exact ⟨hωS, hqs⟩
  · by_cases hi : K ⊆ U i
    swap
    · have hD0 : D = ∅ := Set.subset_empty_iff.1 (by simpa only [hC, hi, ↓reduceIte] using hDC)
      simp [hD0]
    have hDC' : D ⊆ S ∩ {ω | q ≤ s i ω} := by simpa only [hC, hi, ↓reduceIte] using hDC
    have hDs : MeasurableSet[(hs i).measurableSpace] D :=
      measurableSet_stopped_of_le_const (hs i) hD fun ω hω => WithTop.coe_le_coe.2 (hDC' hω).2
    have hOU : (O : Set ℂ) ⊆ U i := hOK.trans hi
    obtain ⟨hL, hc⟩ := lapTest_projFactor_incl (hUH i) hOU f Ξ
    have key := hind i (zsSubIncl hOU f) Ξ D hDs
    rw [hL] at key
    have h0 : T₀ (LocalSets.lapTest O f) = 0 :=
      LocalSets.IsHarmonicDistOn.apply_lapTest_eq_zero isOpen_H hT₀
        (show O ≤ upperHalfPlaneOpens from fun z hz => hKH (hOK hz)) (fun z hz => hKH (hOK hz)) f
    set e₀ : ℂ := Complex.exp (Complex.I * ((-(T₀ Ξ) : ℝ) : ℂ)) with he₀
    have e1 : ∀ ω, Complex.exp (Complex.I * (((h ω - T₀) (LocalSets.lapTest O f + Ξ) : ℝ) : ℂ)) =
        Complex.exp (Complex.I * (h ω (LocalSets.lapTest O f + Ξ) : ℂ)) * e₀ := fun ω => by
      rw [he₀, ← Complex.exp_add, sub_apply, map_add T₀, h0, zero_add]
      congr 1; push_cast; ring
    have e2 : ∀ ω, Complex.exp (Complex.I * (((h ω - T₀) Ξ : ℝ) : ℂ)) =
        Complex.exp (Complex.I * (h ω Ξ : ℂ)) * e₀ := fun ω => by
      rw [he₀, ← Complex.exp_add, sub_apply]
      congr 1; push_cast; ring
    simp_rw [e1, e2, integral_mul_const] at key
    have hne : e₀ ≠ 0 := Complex.exp_ne_zero _
    change _ = projFactor (U i) (zsSubIncl hOU f) Ξ * _ at key
    rw [hc] at key
    rw [← mul_assoc] at key
    exact mul_right_cancel₀ hne key

end ProjTime

/-! ### The canonical conditions for the landed coupling, and non-emptiness -/

section Exists

open SupercriticalConformalCovariance.GM24 (smoothDist)

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {ν₀ : Measure (XCode nL nR)} [IsProbabilityMeasure ν₀]
  {μ : Measure (XCode nL nR × DistOn upperHalfPlaneOpens)} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure ν₀] in
/-- **The dyadic projection-independence identities for the coupling of Theorem 1.1's construction.** -/
theorem proj_of_family (hEv : IsEvoLaw κ ((xL, xR), (ρL, ρR)) ν₀) (hμ1 : μ.map Prod.fst = ν₀)
    (hμ2 : μ.map Prod.snd = fieldLawW κ (((xL, xR), (ρL, ρR)) : WordData nL nR))
    (hfamL : IsFamilyLocal μ (filtrationFst (codeFilt (nL := nL) (nR := nR)) (DistOn upperHalfPlaneOpens))
      (fun t p => cw p.1 t) (fun p => cζ p.1)
      (fun p => p.2 - smoothDist upperHalfPlaneOpens (wordExt κ (((xL, xR), (ρL, ρR)) : WordData nL nR))))
    (F : RatBallSet) (n k : ℕ) {A : Set (ObsY nL nR)} (hA : MeasurableSet A) (j : RatComb) :
    projL κ F (dyad n k) A j ((xL, xR), (ρL, ρR)) μ = projR F (dyad n k) A j μ := by
  set q := dyad n k
  -- `wordExt` is kept opaque: unfolding it in unification is very slow
  obtain ⟨u₀, hu₀def⟩ : ∃ u₀ : ℂ → ℝ, wordExt κ (((xL, xR), (ρL, ρR)) : WordData nL nR) = u₀ := ⟨_, rfl⟩
  rw [hu₀def] at hfamL
  have hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀ := by
    rw [← hu₀def]; exact isBoundedHarmonicExtension_wordExt κ xL xR ρL ρR
  have hK := isCompact_ballsK F.1
  have hKH := F.2
  set S : Set (XCode nL nR × DistOn upperHalfPlaneOpens) := Prod.fst ⁻¹' condEv F q A with hS
  have hSm : MeasurableSet S := measurable_fst (measurableSet_condEv F q hA)
  have hae : ∀ᵐ p ∂μ, p.1 ∈ CRel κ xL xR ρL ρR := by
    rw [← hμ1] at hEv; exact ae_of_ae_map measurable_fst.aemeasurable hEv.ae_mem
  have hgood : ∀ᵐ p ∂μ, Good p.1 := hae.mono fun p hp => hp.1.1
  have hS𝓖 := measurableSet_fst_condEv_aug hgood F q hA
  have hSK : ∀ᵐ p ∂μ, p ∈ S → (q : ℝ≥0∞) < cζ p.1 ∧
      Disjoint (ballsK F.1) (fwdHull (fun r : ℝ => cw p.1 r.toNNReal) q) := ae_of_all _ fun p hp => by
    obtain ⟨hg, hq, hal⟩ := hp.2
    exact ⟨hq, Set.disjoint_left.2 fun z hz => notMem_fwdHull_of_alive hg.continuousOn_w hq (hKH hz) (hal z hz)⟩
  set m := (μ.restrict S).map Prod.snd with hm
  have hmeas : ∀ Ψ : TestOn upperHalfPlaneOpens, Measurable fun x : DistOn upperHalfPlaneOpens =>
      Complex.exp (Complex.I * (x Ψ : ℂ)) := fun Ψ => GFF.measurable_exp_I_mul (measurable_distOn_apply Ψ)
  have hmS : ∀ Ψ : TestOn upperHalfPlaneOpens, ∫ x, Complex.exp (Complex.I * (x Ψ : ℂ)) ∂m =
      ∫ p in S, Complex.exp (Complex.I * (p.2 Ψ : ℂ)) ∂μ := fun Ψ => by
    rw [hm, integral_map measurable_snd.aemeasurable (hmeas Ψ).aestronglyMeasurable]
  have hPI : IsProjIndepMeasure (ballsOpens F) m := by
    intro f Ξ
    rw [hmS, hmS]
    have hT₀ : IsHarmonicDistOn (smoothDist upperHalfPlaneOpens u₀) H := isHarmonicDistOn_smoothDist_of hu₀
    have hfamL' : IsFamilyLocal μ (filtrationFst (codeFilt (nL := nL) (nR := nR)) (DistOn upperHalfPlaneOpens))
        (fun t p => cw p.1 t) (fun p => cζ p.1) fun p => Prod.snd p - smoothDist upperHalfPlaneOpens u₀ := hfamL
    exact setIntegral_projIndep_of_isFamilyLocal (h := Prod.snd)
      (fun Ψ => (measurable_distOn_apply Ψ).comp measurable_snd) hT₀ hfamL'
      hK hKH (ballsOpens F) (ballsU_subset_ballsK F.1) hS𝓖 hSK f Ξ
  obtain ⟨hGm, hGd⟩ := projMap_spec F
  have hac : m ≪ fieldLaw0 u₀ := by
    refine Measure.absolutelyContinuous_of_le ?_
    have h2 : μ.map Prod.snd = fieldLaw0 u₀ := by rw [← hu₀def]; exact hμ2
    rw [hm, ← h2]
    exact Measure.map_mono Measure.restrict_le_self measurable_snd
  have hres := resample_eq_of_isProjIndepMeasure hGm hGd (ballsOpens_subset_H F) hu₀.1 hac hPI
  set φ := ratComb upperHalfPlaneOpens j
  have hf1 : Measurable fun x : DistOn upperHalfPlaneOpens =>
      Complex.exp (Complex.I * ((x φ - projMap F (x - meanH u₀) φ : ℝ) : ℂ)) :=
    GFF.measurable_exp_I_mul ((measurable_distOn_apply φ).sub
      ((measurable_distOn_apply φ).comp (hGm.comp (measurable_sub_distOnConst _))))
  have key := integral_cexp_resample hGm (meanH u₀) m φ
  rw [hres, hm, integral_map measurable_snd.aemeasurable hf1.aestronglyMeasurable,
    integral_map measurable_snd.aemeasurable (hmeas φ).aestronglyMeasurable] at key
  rw [projL, projR, integral_ite_fst (measurableSet_condEv F q hA), integral_ite_fst (measurableSet_condEv F q hA),
    hu₀def]
  exact key.symm

/-- **Non-emptiness (S4).** Every ordered word has a canonical coupling law. -/
theorem exists_canonCond (hκ : 0 < κ) (hF : IsOrderedForceWord xL xR) :
    ∃ π : ProbabilityMeasure (XCode nL nR × DistOn upperHalfPlaneOpens),
      CanonCond κ (((xL, xR), (ρL, ρR)) : WordData nL nR) (π : Measure _) := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ :=
    exists_isIntegratedSLEEvolution_assembled (a := κ) (ρL := ρL) (ρR := ρR) hκ hF
  obtain ⟨B', hB'm, hB'c, hB'br, hae⟩ := Sec2.Restart.exists_continuous_version hE.1
  set ν₀ := P.map (codeOf xL xR B' W VL VR ζ)
  have hEv : IsEvoLaw κ ((xL, xR), (ρL, ρR)) ν₀ := isEvoLaw_map_codeOf hκ hE hB'm hB'c hB'br hae
  have hE₁ := isIntegratedSLEEvolution_canon hEv
  have hgen : ∀ t, IsAeGen ν₀ (id : XCode nL nR → XCode nL nR)
      (usualAugmentation (codeFilt (nL := nL) (nR := nR)) ν₀ t) := fun t A hA =>
    ⟨A, (usualAugmentation (codeFilt (nL := nL) (nR := nR)) ν₀).le t _ hA, EventuallyEq.rfl⟩
  obtain ⟨α, μ, hαp, hμp, hμ1, hμ2, hαG, hfamS, hfamL⟩ :=
    exists_locCoupling_of_evolution hκ hE₁ measurable_id hgen (finiteFamilyProjStatement hκ xL xR ρL ρR)
  have hu₀ := isBoundedHarmonicExtension_wordExt κ xL xR ρL ρR
  have hα : α = fieldLawW κ (((xL, xR), (ρL, ρR)) : WordData nL nR) :=
    eq_fieldLaw0_of_isZBGFFProcess (continuousOn_wordExt κ _) (hαG _ hu₀)
  have hμ2' : μ.map Prod.snd = fieldLawW κ (((xL, xR), (ρL, ρR)) : WordData nL nR) := hμ2.trans hα
  refine ⟨⟨μ, hμp⟩, ?_, hμ2', fun F n k A hA j => ?_, fun F n k A hA j => ?_⟩
  · show IsEvoLaw κ _ (μ.map Prod.fst)
    rw [hμ1]; exact hEv
  · exact sampled_of_family hκ hEv hμ1 hfamS F n k (measurableSet_obsPi hA) j
  · exact proj_of_family hEv hμ1 hμ2' (hfamL _ hu₀) F n k (measurableSet_obsPi hA) j

end Exists

end Param12

end Exist

end InteractingSLE
