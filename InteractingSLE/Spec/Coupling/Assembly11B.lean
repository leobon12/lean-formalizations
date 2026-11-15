import InteractingSLE.Spec.Coupling.Assembly11Provider
import InteractingSLE.Spec.Coupling.Locality11
import InteractingSLE.Spec.Coupling.Assembly11BCoord
import SupercriticalConformalCovariance.GM24.TVReduce

/-!
# Theorem 1.1: the finite-family input with projection independence, and the compactness step for it

Packet PROVE-T11-LOC (Astra §1 pp. 5–7). The second assembly of Theorem 1.1 (after PROVE-T11-ASM's
`Assembly11Provider`), in which locality is proved and the sample space is arbitrary:

* `IsProjIndepCoupling O hs μ` (Astra (1.10), second half, tested on `Ω₀`-events, free of projection versions and of
  the harmonic mean): for every `f ∈ C_c^∞(O)`, test function `Ξ` and event `A₀` of the stopped σ-algebra at `s`,
    `∫_{A₀ × 𝒟'} e^{i x(−Δf/2π + Ξ)} dμ = exp(−‖∇f‖²/2 − ⟪∇f, covVec_O Ξ⟫) ∫_{A₀ × 𝒟'} e^{i x(Ξ)} dμ`;
* `FiniteFamilyProjStatement` (**named input**): the conclusion of PROVE-T11-KER's `exists_fieldLaw_finiteFamily`
  (open regions inside compact protected sets, any sample space) with, in addition, projection independence at every
  member of every finite subfamily (Astra (1.9)–(1.10));
* `exists_safeFamilyLoc`: the rational-ball family of safe stops with **local** exhaustion: almost surely, for `t < ζ`,
  a compact `K ⊆ ℍ ∖ K_t` and an open `O ⊇ K`, some member has `K ⊆ U_i`, `K̄_i ⊆ O` and `t ≤ s_i` (Astra (1.12));
* `exists_projCoupling_of_finite` (compactness, `exists_limit_coupling` with countably many coordinates `G`): if every
  event of the stopped σ-algebras is almost surely a function of `G`, finite-family couplings sampled and
  projection-independent at their members give one coupling with both properties at every member.
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

theorem measurable_sub_distOnConst (T : DistOn upperHalfPlaneOpens) :
    Measurable fun x : DistOn upperHalfPlaneOpens => x - T :=
  measurable_distOn_iff.2 fun φ => by
    simp only [sub_apply]
    exact (measurable_distOn_apply φ).sub_const _

/-! ### Projection independence and the named input -/

section Defs

variable {Ω₀ : Type*} {mΩ₀ : MeasurableSpace Ω₀}

/-- **Projection independence of a coupling at a pair** (Astra (1.10), second half), in a form free of projection
versions and of the harmonic mean, tested on the events `A₀` of the stopped σ-algebra at `s` on `Ω₀`: every Dirichlet
direction `−Δf/2π`, `f ∈ C_c^∞(O)`, enters the characteristic functional of the field with the Gaussian factor of the
projection onto `H(O)`,
  `∫_{A₀ × 𝒟'} e^{i x(−Δf/2π + Ξ)} dμ = exp(−‖∇f‖²/2 − ⟪∇f, covVec_O Ξ⟫) ∫_{A₀ × 𝒟'} e^{i x(Ξ)} dμ`.
For a field `x = 𝔥₀ + h⁰` (`𝔥₀` harmonic, `h⁰` a zero-boundary GFF) this is equivalent to `P_O h⁰ ⫫ (h⁰ − P_O h⁰, 𝓕_s)`. -/
def IsProjIndepCoupling {𝓕₀ : Filtration ℝ≥0 mΩ₀} {P₀ : Measure Ω₀} (O : Opens ℂ) {s : Ω₀ → ℝ≥0}
    (hs : IsStoppingTime (usualAugmentation 𝓕₀ P₀) fun ω => (s ω : WithTop ℝ≥0))
    (μ : Measure (Ω₀ × DistOn upperHalfPlaneOpens)) : Prop :=
  ∀ (f : zsSub (O : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) (A₀ : Set Ω₀),
    MeasurableSet[hs.measurableSpace] A₀ →
      ∫ p in Prod.fst ⁻¹' A₀, Complex.exp (Complex.I * (p.2 (lapTest O f + Ξ) : ℂ)) ∂μ =
        Complex.exp (((-(1 / 2) * ‖gradFeat (O : Set ℂ) f.1‖ ^ 2 -
            ⟪gradFeat (O : Set ℂ) f.1, covVec (O : Set ℂ) Ξ⟫ : ℝ) : ℂ)) *
          ∫ p in Prod.fst ⁻¹' A₀, Complex.exp (Complex.I * (p.2 Ξ : ℂ)) ∂μ

end Defs

/-- **Named input: the finite-family step with projection independence** (Astra pp. 5–6, (1.9)–(1.10)). For an
integrated evolution on any probability space, bounded harmonic extensions `u`, and a countable family of open regions
`U i` inside compact sets `K i ⊆ ℍ` protected through stops `s i < ζ`, there is a field law `α` (a zero-boundary GFF
plus the time-zero harmonic mean) such that every finite subfamily admits a coupling of the driving law and `α`
sampled at all its members and projection-independent at all its members. Its first half is PROVE-T11-KER's
`exists_fieldLaw_finiteFamily` (for `0 < κ`). -/
def FiniteFamilyProjStatement (κ : ℝ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) : Prop :=
  ∀ (Ω₀ : Type u) (mΩ₀ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (_ : IsProbabilityMeasure P₀)
    (𝓕₀ : Filtration ℝ≥0 mΩ₀) (W : ℝ≥0 → Ω₀ → ℝ) (VL : Fin nL → ℝ≥0 → Ω₀ → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω₀ → ℝ) (B : ℝ≥0 → Ω₀ → ℝ) (ζ : Ω₀ → ℝ≥0∞),
    IsIntegratedSLEEvolution κ xL xR ρL ρR P₀ 𝓕₀ W VL VR B ζ →
    ∀ (u : Ω₀ → ℝ≥0 → ℂ → ℝ), (∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s)) →
    ∀ (ι : Type) (_ : Countable ι) (U K : ι → Set ℂ) (hUo : ∀ i, IsOpen (U i)),
    (∀ i, IsCompact (K i) ∧ K i ⊆ H ∧ U i ⊆ K i) →
    ∀ (s : ι → Ω₀ → ℝ≥0) (hs : ∀ i, IsStoppingTime (usualAugmentation 𝓕₀ P₀) fun ω => (s i ω : WithTop ℝ≥0)),
    (∀ i, ∀ᵐ ω ∂P₀, (s i ω : ℝ≥0∞) < ζ ω ∧
      Disjoint (K i) (fwdHull (fun r : ℝ => W r.toNNReal ω) (s i ω))) →
    ∃ α : Measure (DistOn upperHalfPlaneOpens), IsProbabilityMeasure α ∧
      (∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR)
          (forceJumpSet xL xR) u₀ →
        IsZBGFFProcess upperHalfPlaneOpens (fun φ x => x φ - ∫ z, u₀ z * φ z) α) ∧
      ∀ F : Finset ι, ∃ μ : Measure (Ω₀ × DistOn upperHalfPlaneOpens),
        IsProbabilityMeasure μ ∧ μ.map Prod.fst = P₀ ∧ μ.map Prod.snd = α ∧
          ∀ i ∈ F, IsSampledCoupling κ W u P₀ (U i) (hs i) μ ∧
            IsProjIndepCoupling ⟨U i, hUo i⟩ (hs i) μ

/-! ### The rational-ball family with local exhaustion -/

section Family

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}
  {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **The countable family of safe stops with local exhaustion** (Astra (1.11)–(1.13)): as `exists_safeFamily`, and
almost surely, for every `t < ζ`, compact `K ⊆ ℍ ∖ K_t` and open `O ⊇ K`, some member has `K ⊆ ⋃ F`, `⋃ F̄ ⊆ O`
and `t ≤ s_{F,n}`. -/
theorem exists_safeFamilyLoc (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {T : ℕ → Ω → ℝ≥0} (hT : IsAnnouncingSeq (usualAugmentation 𝓕 P) P ζ T) :
    ∃ s : RatBallSet × ℕ → Ω → ℝ≥0,
      (∀ i, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (s i ω : WithTop ℝ≥0)) ∧
      (∀ i, ∀ᵐ ω ∂P, (s i ω : ℝ≥0∞) < ζ ω ∧
        Disjoint (ballsK i.1.1) (fwdHull (fun r : ℝ => W r.toNNReal ω) (s i ω))) ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∀ K : Set ℂ, IsCompact K → K ⊆ H →
        Disjoint K (fwdHull (fun r : ℝ => W r.toNNReal ω) t) → ∀ O : Set ℂ, IsOpen O → K ⊆ O →
          ∃ i, K ⊆ ballsU i.1.1 ∧ ballsK i.1.1 ⊆ O ∧ t ≤ s i ω := by
  obtain ⟨hTst, hTm, hTζ, hTex⟩ := hT
  have hseq : ∀ F : RatBallSet, ∃ ρ : ℕ → Ω → ℝ≥0,
      (∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (ρ n ω : WithTop ℝ≥0)) ∧
      (∀ n : ℕ, ∀ᵐ ω ∂P, ∃ δ, IsSafeAt (ballsK F.1) δ n (T n ω) (ζ ω) (W · ω) (ρ n ω)) ∧
      ∀ᵐ ω ∂P, ∀ (j : ℕ) (t : ℝ≥0), t ≤ T j ω →
        (∀ z ∈ ballsK F.1, ∃ u, IsForwardSol (rpath (W · ω)) z t u) → ∀ᶠ n in atTop, t ≤ ρ n ω := by
    intro F
    obtain ⟨m, hm, hKm⟩ := exists_pos_le_im_of_isCompact (isCompact_ballsK F.1) F.2
    obtain ⟨ρ, h1, -, -, h4, h5⟩ := exists_safeSeq_of_seq hE (isCompact_ballsK F.1) F.2 hm hKm hTst
      hTm hTζ
    exact ⟨ρ, h1, fun n => (h4 n).mono fun ω h => ⟨_, h⟩, h5⟩
  choose ρ hρst hρsafe hρex using hseq
  refine ⟨fun i => ρ i.1 i.2, fun i => hρst i.1 i.2, fun i => ?_, ?_⟩
  · filter_upwards [hρsafe i.1 i.2, hE.2.2.2.2] with ω hS hP
    obtain ⟨δ, hS⟩ := hS
    exact ⟨hS.1, Set.disjoint_left.2 fun z hz =>
      notMem_fwdHull_of_alive hP.2.2.2.1 hS.1 (i.1.2 hz) (hS.2.2.2 z hz).1⟩
  · filter_upwards [ae_all_iff.2 hρex, hTex, hE.2.2.2.2] with ω hex hTω hP
    intro t ht K hK hKH hdis O hO hKO
    have hwt := continuousOn_rpath hP.2.2.2.1 ht
    set O' : Set ℂ := O ∩ (H \ fwdHull (clampDrv (rpath (W · ω)) t) t) with hO'_def
    have hO' : IsOpen O' := hO.inter
      (FwdHolo.isOpen_compl_fwdHull (continuous_clampDrv t.coe_nonneg hwt) t.coe_nonneg)
    have hKO' : K ⊆ O' := fun z hz => ⟨hKO hz,
      mem_diff_fwdHull_clampDrv t.coe_nonneg hwt (hKH hz)
        (exists_isForwardSol_of_mem t.coe_nonneg ⟨hKH hz, fun h' => hdis.ne_of_mem hz h' rfl⟩)⟩
    obtain ⟨F₀, hKF, hFO⟩ := exists_rationalBalls hK hO' hKO'
    set F : RatBallSet := ⟨F₀, hFO.trans (inter_subset_right.trans sdiff_subset)⟩
    have halive : ∀ z ∈ ballsK F.1, ∃ u, IsForwardSol (rpath (W · ω)) z t u := fun z hz => by
      obtain ⟨u, hu⟩ := exists_isForwardSol_of_mem t.coe_nonneg (hFO hz).2
      exact ⟨u, (isForwardSol_iff_of_eqOn (clampDrv_eqOn (W := rpath (W · ω))) u).1 hu⟩
    obtain ⟨j, hj⟩ := hTω t ht
    obtain ⟨n, hn⟩ := (hex F j t hj halive).exists
    exact ⟨(F, n), hKF, hFO.trans inter_subset_left, hn⟩

end Family

/-! ### Compactness with countably many coordinates -/

section Compact

variable {Ω₀ : Type*} {mΩ₀ : MeasurableSpace Ω₀} {P₀ : Measure Ω₀} {𝓕₀ : Filtration ℝ≥0 mΩ₀}

/-- A test on an event that is almost surely `G⁻¹ C` is a product-form test in the coordinates `G`. -/
theorem setIntegral_fst_preimage_eq_of_coord {Y : Type*} [MeasurableSpace Y] {G : Ω₀ → Y}
    (hG : Measurable G) {ν : Measure (Ω₀ × DistOn upperHalfPlaneOpens)} (hν : ν.map Prod.fst = P₀)
    {A₀ : Set Ω₀} {C : Set Y} (hC : MeasurableSet C) (hAC : A₀ =ᵐ[P₀] G ⁻¹' C)
    (f : DistOn upperHalfPlaneOpens → ℂ) :
    ∫ p in Prod.fst ⁻¹' A₀, f p.2 ∂ν = ∫ p, C.indicator (fun _ => (1 : ℂ)) (G p.1) * f p.2 ∂ν := by
  rw [setIntegral_congr_set (preimage_fst_ae_eq hν hAC),
    ← integral_indicator (measurable_fst (hG hC))]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  by_cases hp : G p.1 ∈ C
  · simp [indicator_of_mem hp, indicator_of_mem (show p ∈ Prod.fst ⁻¹' (G ⁻¹' C) from hp)]
  · simp [indicator_of_notMem hp, indicator_of_notMem (show p ∉ Prod.fst ⁻¹' (G ⁻¹' C) from hp)]

/-- **The compactness step for sampling and projection independence**, on an arbitrary sample space whose stopped
events are almost surely functions of countably many coordinates `G` (standard Borel). -/
theorem exists_projCoupling_of_finite [IsProbabilityMeasure P₀] (κ : ℝ) (W : ℝ≥0 → Ω₀ → ℝ)
    (u : Ω₀ → ℝ≥0 → ℂ → ℝ) {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] {G : Ω₀ → Y}
    (hG : Measurable G) {ι : Type*} [Countable ι] (U : ι → Set ℂ) (hUo : ∀ i, IsOpen (U i))
    (s : ι → Ω₀ → ℝ≥0)
    (hs : ∀ i, IsStoppingTime (usualAugmentation 𝓕₀ P₀) fun ω => (s i ω : WithTop ℝ≥0))
    (hgen : ∀ i, IsAeGen P₀ G (hs i).measurableSpace)
    (α : Measure (DistOn upperHalfPlaneOpens)) [IsProbabilityMeasure α]
    (hfin : ∀ F : Finset ι, ∃ μ : Measure (Ω₀ × DistOn upperHalfPlaneOpens),
      IsProbabilityMeasure μ ∧ μ.map Prod.fst = P₀ ∧ μ.map Prod.snd = α ∧
        ∀ i ∈ F, IsSampledCoupling κ W u P₀ (U i) (hs i) μ ∧
          IsProjIndepCoupling ⟨U i, hUo i⟩ (hs i) μ) :
    ∃ μ : Measure (Ω₀ × DistOn upperHalfPlaneOpens),
      IsProbabilityMeasure μ ∧ μ.map Prod.fst = P₀ ∧ μ.map Prod.snd = α ∧
        ∀ i, IsSampledCoupling κ W u P₀ (U i) (hs i) μ ∧
          IsProjIndepCoupling ⟨U i, hUo i⟩ (hs i) μ := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · obtain ⟨μ, h1, h2, h3, -⟩ := hfin ∅
    exact ⟨μ, h1, h2, h3, fun i => isEmptyElim i⟩
  obtain ⟨e, he⟩ := exists_surjective_nat ι
  set F : ℕ → Finset ι := fun n => (Finset.range n).image e with hF
  have hFmem : ∀ i, ∃ k, ∀ n, k < n → i ∈ F n := fun i => by
    obtain ⟨k, rfl⟩ := he i
    exact ⟨k, fun n hn => Finset.mem_image.2 ⟨k, Finset.mem_range.2 hn, rfl⟩⟩
  choose μ hμp hμ1 hμ2 hμs using fun n => hfin (F n)
  have : ∀ n, IsProbabilityMeasure (μ n) := hμp
  obtain ⟨μ', φ, hμ'p, hμ'1, hμ'2, hφ, hlim⟩ := exists_limit_coupling hG μ hμ1 hμ2
  have hpass : ∀ (i : ι) (A₀ : Set Ω₀), MeasurableSet[(hs i).measurableSpace] A₀ →
      ∀ (f : DistOn upperHalfPlaneOpens → ℂ), Measurable f → (∃ C, ∀ x, ‖f x‖ ≤ C) → ∀ c : ℂ,
      (∀ n, i ∈ F n → ∫ p in Prod.fst ⁻¹' A₀, f p.2 ∂(μ n) = c) →
      ∫ p in Prod.fst ⁻¹' A₀, f p.2 ∂μ' = c := by
    intro i A₀ hA₀ f hf hfb c hc
    obtain ⟨C, hC, hAC⟩ := hgen i A₀ hA₀
    obtain ⟨k, hk⟩ := hFmem i
    have hg : Measurable (C.indicator fun _ => (1 : ℂ)) := measurable_const.indicator hC
    have hL := hlim (C.indicator fun _ => (1 : ℂ)) f hg hf
      ⟨1, fun y => by by_cases hy : y ∈ C <;> simp [hy]⟩ hfb
    rw [setIntegral_fst_preimage_eq_of_coord hG hμ'1 hC hAC f]
    have hev : ∀ᶠ n in atTop, ∫ p, C.indicator (fun _ => (1 : ℂ)) (G p.1) * f p.2 ∂μ (φ n) = c := by
      filter_upwards [eventually_gt_atTop k] with n hn
      rw [← setIntegral_fst_preimage_eq_of_coord hG (hμ1 (φ n)) hC hAC f]
      exact hc (φ n) (hk (φ n) (hn.trans_le (hφ.id_le n)))
    exact tendsto_nhds_unique hL (tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm))
  have hnorm1 : ∀ x : ℝ, ‖Complex.exp (Complex.I * (x : ℂ))‖ ≤ 1 := fun x =>
    (Complex.norm_exp_I_mul_ofReal x).le
  refine ⟨μ', hμ'p, hμ'1, hμ'2, fun i => ⟨fun ψ hψ A₀ hA₀ => ?_, fun f Ξ A₀ hA₀ => ?_⟩⟩
  · exact hpass i A₀ hA₀ (fun x => Complex.exp (Complex.I * (x ψ : ℂ)))
      (GFF.measurable_exp_I_mul (measurable_distOn_apply ψ)) ⟨1, fun x => hnorm1 _⟩ _
      fun n hn => (hμs n i hn).1 ψ hψ A₀ hA₀
  · set c : ℂ := Complex.exp (((-(1 / 2) * ‖gradFeat (U i) f.1‖ ^ 2 -
      ⟪gradFeat (U i) f.1, covVec (U i) Ξ⟫ : ℝ) : ℂ)) with hc
    set Φ : TestOn upperHalfPlaneOpens := lapTest ⟨U i, hUo i⟩ f + Ξ with hΦ
    have he1 : Measurable fun x : DistOn upperHalfPlaneOpens => Complex.exp (Complex.I * (x Φ : ℂ)) :=
      GFF.measurable_exp_I_mul (measurable_distOn_apply Φ)
    have he2 : Measurable fun x : DistOn upperHalfPlaneOpens => Complex.exp (Complex.I * (x Ξ : ℂ)) :=
      GFF.measurable_exp_I_mul (measurable_distOn_apply Ξ)
    have hiff : ∀ ν : Measure (Ω₀ × DistOn upperHalfPlaneOpens), IsFiniteMeasure ν →
        (∫ p in Prod.fst ⁻¹' A₀, Complex.exp (Complex.I * (p.2 Φ : ℂ)) ∂ν =
            c * ∫ p in Prod.fst ⁻¹' A₀, Complex.exp (Complex.I * (p.2 Ξ : ℂ)) ∂ν ↔
          ∫ p in Prod.fst ⁻¹' A₀, (Complex.exp (Complex.I * (p.2 Φ : ℂ)) -
            c * Complex.exp (Complex.I * (p.2 Ξ : ℂ))) ∂ν = 0) := fun ν _ => by
      have i1 : Integrable (fun p : Ω₀ × DistOn upperHalfPlaneOpens =>
          Complex.exp (Complex.I * (p.2 Φ : ℂ))) (ν.restrict (Prod.fst ⁻¹' A₀)) :=
        Integrable.of_bound (he1.comp measurable_snd).aestronglyMeasurable 1
          (Eventually.of_forall fun p => hnorm1 _)
      have i2 : Integrable (fun p : Ω₀ × DistOn upperHalfPlaneOpens =>
          c * Complex.exp (Complex.I * (p.2 Ξ : ℂ))) (ν.restrict (Prod.fst ⁻¹' A₀)) :=
        (Integrable.of_bound (he2.comp measurable_snd).aestronglyMeasurable 1
          (Eventually.of_forall fun p => hnorm1 _)).const_mul c
      rw [integral_sub i1 i2, integral_const_mul, sub_eq_zero]
    refine (hiff μ' inferInstance).2 ?_
    refine hpass i A₀ hA₀ (fun x => Complex.exp (Complex.I * (x Φ : ℂ)) -
        c * Complex.exp (Complex.I * (x Ξ : ℂ))) (he1.sub (he2.const_mul c))
      ⟨1 + ‖c‖, fun x => ?_⟩ 0 fun n hn => (hiff (μ n) inferInstance).1
        ((hμs n i hn).2 f Ξ A₀ hA₀)
    calc _ ≤ ‖Complex.exp (Complex.I * (x Φ : ℂ))‖ + ‖c * Complex.exp (Complex.I * (x Ξ : ℂ))‖ :=
          norm_sub_le _ _
      _ ≤ 1 + ‖c‖ * 1 := by
          rw [norm_mul]
          exact add_le_add (hnorm1 _) (mul_le_mul_of_nonneg_left (hnorm1 _) (norm_nonneg _))
      _ = 1 + ‖c‖ := by rw [mul_one]

end Compact

end Coupling

end InteractingSLE
