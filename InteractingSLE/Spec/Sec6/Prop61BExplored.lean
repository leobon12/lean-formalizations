/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Prop61BMarked

/-!
# Proposition 6.1 for explored curves: the assembly

Packet PROVE-SEC6-D (specification §6.1, `source/spec/p145-192.md`, `#prop-6.1` p. 154,
`#prop-6.1-proof` pp. 166–169).

The proof of Proposition 6.1 works with `A(τ) = η_{θ₁}([0, τ]) ∪ η_{θ₂}` for a stopping time `τ` of
`𝓕_t = σ(η_{θ₁}(s) : s ≤ t, η_{θ₂})`, which is "a local set for `h` by Lemma 6.2 applied for the case
`k = 2`" (p. 167), compared with `A(∞)` and with `η_{θ₂}` (pp. 167–168). This file instantiates the
local-set lemmas of `Prop61BGlobal` and `Prop61BMarked` for explored sets of Lemma 6.2: from the
hypotheses of Lemma 6.2 (continuity, field determination, history-sensitive locality, Galmarino form of
the stopping times) it derives

* `comap_explored_le_aeSigma` : the explored set is almost surely determined by the field (so any two
  explored sets are conditionally independent given the field, the hypothesis of Proposition 3.8);
* `not_isBounded_lowerUnion_explored` : curves from real starting points in the closed half-plane have
  the unboundedness property of Proposition 3.8;
* `isOpen_H_diff_explored` : transient curves have relatively closed explored sets;

and assembles them in `ae_condExp_exp_eq_explored_of_tendsto`: the Gaussian law of Proposition 6.1 on
every component (bounded or not) of `ℍ ∖ A(τ)`, **given the germs and the ordered labeled stopped
curves**, as soon as the prime-end boundary values of the comparison means (of `A(∞)` and of `η_{θ₂}`)
are those of the explicit candidate `𝔥_C` in the chart of `C`. The two curves are `η 0 = η_{θ₂}` (run
in full, `τ 0 = ∞`) and `η 1 = η_{θ₁}` (stopped at `τ 1`, a Galmarino functional of the full first
curve and the past of the second: the source's `𝓕_t`-stopping time).

This is not Proposition 6.1 for the frozen `IsFlowLine`: the hypotheses of Lemma 6.2 for flow lines
(history-sensitive locality and field determination) and the prime-end boundary values (single-curve
laws in each component's chart, supplement §2.3 branch normalization, pocket topology) are its
remaining inputs (see the packet handoff).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal Real

namespace InteractingSLE.Sec6

open QuantumZipper (H)
open LQGMetric (DistOn TestOn CondIndepEv)
open SupercriticalConformalCovariance (IsConformalBijection)
open LocalSets

/-! ### Deterministic facts about explored sets -/

section Geometry

variable {Ω : Type*} {k : ℕ}

/-- The explored set grows with the stopping times. -/
theorem explored_mono {η : Fin k → Ω → ℝ≥0 → ℂ} {τ τ' : Fin k → Ω → ℝ≥0∞} {ω : Ω}
    (hle : ∀ i, τ i ω ≤ τ' i ω) : explored η τ ω ⊆ explored η τ' ω := by
  rintro z ⟨hz, hzH⟩
  obtain ⟨i, t, ht, rfl⟩ := mem_iUnion.1 hz
  exact ⟨mem_iUnion.2 ⟨i, t, (show (t : ℝ≥0∞) ≤ τ' i ω from ht.trans (hle i)), rfl⟩, hzH⟩

/-- **Unboundedness for curves from the real line** (the hypothesis of Proposition 3.8): if every
curve starts on `ℝ` and stays in the closed upper half-plane, every component of
`A ∪ {Im ≤ 0}` is unbounded, `A` the explored set. -/
theorem not_isBounded_lowerUnion_explored {η : Fin k → Ω → ℝ≥0 → ℂ} {τ : Fin k → Ω → ℝ≥0∞}
    {ω : Ω} (hc : ∀ i, Continuous (η i ω)) (h0 : ∀ i, (η i ω 0).im = 0)
    (him : ∀ i t, 0 ≤ (η i ω t).im) :
    ∀ z ∈ lowerUnion (explored η τ ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (explored η τ ω)) z) := by
  refine not_isBounded_of_isPreconnected_union_real ?_
  set R : Set ℂ := {w : ℂ | w.im = 0}
  set K : Fin k → Set ℂ := fun i => η i ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ τ i ω}
  have hR : IsPreconnected R := by
    have : R = Set.range (fun r : ℝ => (r : ℂ)) := by
      ext w
      simp only [R, mem_ofPred_eq, mem_range]
      refine ⟨fun hw => ⟨w.re, ?_⟩, ?_⟩
      · apply Complex.ext <;> simp [hw]
      · rintro ⟨r, rfl⟩; simp
    rw [this]
    exact isPreconnected_range Complex.continuous_ofReal
  have hK : ∀ i, IsPreconnected (K i ∪ R) := by
    intro i
    have hI : IsPreconnected {t : ℝ≥0 | (t : ℝ≥0∞) ≤ τ i ω} := by
      refine OrdConnected.isPreconnected ⟨fun a _ b hb t ht => ?_⟩
      exact (show (t : ℝ≥0∞) ≤ b from ENNReal.coe_le_coe.2 ht.2).trans hb
    refine (hI.image _ (hc i).continuousOn).union (η i ω 0) ⟨0, by simp, rfl⟩ (h0 i) hR
  have e : explored η τ ω ∪ R = R ∪ ⋃ i, (K i ∪ R) := by
    ext w
    simp only [explored, mem_union, mem_inter_iff, mem_iUnion]
    constructor
    · rintro (⟨⟨i, hi⟩, _⟩ | hw)
      · exact Or.inr ⟨i, Or.inl hi⟩
      · exact Or.inl hw
    · rintro (hw | ⟨i, hi | hw⟩)
      · exact Or.inr hw
      · obtain ⟨t, ht, rfl⟩ := hi
        rcases (him i t).lt_or_eq with hpos | hzero
        · exact Or.inl ⟨⟨i, t, ht, rfl⟩, hpos⟩
        · exact Or.inr hzero.symm
      · exact Or.inr hw
  rw [e]
  have hz : (0 : ℂ) ∈ R := by simp [R]
  have e2 : R ∪ ⋃ i, (K i ∪ R) = ⋃₀ insert R (range fun i => K i ∪ R) := by
    rw [sUnion_insert, sUnion_range]
  rw [e2]
  refine isPreconnected_sUnion 0 _ ?_ ?_
  · rintro s (rfl | ⟨i, rfl⟩)
    · exact hz
    · exact Or.inr hz
  · rintro s (rfl | ⟨i, rfl⟩)
    · exact hR
    · exact hK i

/-- A continuous path tending to `∞` has a closed image on every time set `{t ≤ T}` (`T ≤ ∞`). -/
theorem isClosed_image_le_of_tendsto_cobounded {γ : ℝ≥0 → ℂ} (hγ : Continuous γ)
    (htr : Tendsto γ atTop (Bornology.cobounded ℂ)) (T : ℝ≥0∞) :
    IsClosed (γ '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ T}) := by
  set I : Set ℝ≥0 := {t : ℝ≥0 | (t : ℝ≥0∞) ≤ T}
  have hIc : IsClosed I := isClosed_le ENNReal.continuous_coe continuous_const
  refine isClosed_of_closure_subset fun z hz => ?_
  have hn : Tendsto (fun t => ‖γ t‖) atTop atTop := tendsto_norm_cobounded_atTop.comp htr
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.1 (hn.eventually_gt_atTop (‖z‖ + 1))
  set J : Set ℝ≥0 := I ∩ Icc 0 t₀
  have hJ : IsCompact J := isCompact_Icc.inter_left hIc
  have hJc : IsClosed (γ '' J) := (hJ.image hγ).isClosed
  have hsub : ball z 1 ∩ γ '' I ⊆ γ '' J := by
    rintro w ⟨hw, t, ht, rfl⟩
    refine ⟨t, ⟨ht, zero_le, ?_⟩, rfl⟩
    by_contra hlt
    have h1 := ht₀ t (le_of_lt (not_le.1 hlt))
    have h2 : ‖γ t‖ < ‖z‖ + 1 := by
      have := mem_ball.1 hw
      rw [dist_eq_norm] at this
      linarith [norm_le_norm_add_norm_sub' (γ t) z, norm_sub_rev (γ t) z]
    linarith
  have hz' : z ∈ closure (ball z 1 ∩ γ '' I) :=
    isOpen_ball.inter_closure ⟨mem_ball_self one_pos, hz⟩
  exact image_mono inter_subset_left (hJc.closure_subset_iff.2 hsub hz')

/-- The explored set of transient curves is relatively closed in `ℍ`. -/
theorem isOpen_H_diff_explored {η : Fin k → Ω → ℝ≥0 → ℂ} {τ : Fin k → Ω → ℝ≥0∞} {ω : Ω}
    (hc : ∀ i, Continuous (η i ω)) (htr : ∀ i, Tendsto (η i ω) atTop (Bornology.cobounded ℂ)) :
    IsOpen (H \ explored η τ ω) := by
  have e : H \ explored η τ ω = H \ ⋃ i, η i ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ τ i ω} := by
    ext z
    simp only [explored, Set.mem_sdiff, mem_inter_iff, not_and]
    exact ⟨fun ⟨hz, h⟩ => ⟨hz, fun h' => h h' hz⟩, fun ⟨hz, h⟩ => ⟨hz, fun h' _ => h h'⟩⟩
  rw [e]
  exact QuantumZipper.isOpen_H.sdiff (isClosed_iUnion_of_finite fun i =>
    isClosed_image_le_of_tendsto_cobounded (hc i) (htr i) (τ i ω))

/-- The union of two explored sets is the explored set of the larger stopping times. -/
theorem explored_union_eq_max (η : Fin k → Ω → ℝ≥0 → ℂ) (τ₁ τ₂ : Fin k → Ω → ℝ≥0∞) (ω : Ω) :
    explored η τ₁ ω ∪ explored η τ₂ ω = explored η (fun i ω => max (τ₁ i ω) (τ₂ i ω)) ω := by
  ext z
  simp only [explored, mem_union, mem_inter_iff, mem_iUnion, mem_image, mem_ofPred_eq, le_max_iff]
  constructor
  · rintro (⟨⟨i, t, ht, rfl⟩, hz⟩ | ⟨⟨i, t, ht, rfl⟩, hz⟩)
    · exact ⟨⟨i, t, Or.inl ht, rfl⟩, hz⟩
    · exact ⟨⟨i, t, Or.inr ht, rfl⟩, hz⟩
  · rintro ⟨⟨i, t, ht | ht, rfl⟩, hz⟩
    · exact Or.inl ⟨⟨i, t, ht, rfl⟩, hz⟩
    · exact Or.inr ⟨⟨i, t, ht, rfl⟩, hz⟩

end Geometry

/-! ### Field determination of explored sets -/

section Determined

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}
  {k : ℕ} {η : Fin k → Ω → ℝ≥0 → ℂ} {τ : Fin k → Ω → ℝ≥0∞}
  {S : Fin k → (Fin k → Hist) → (ℚ≥0 → ℂ) → ℝ≥0∞}

/-- A random variable almost surely equal to a measurable function of the field is measurable for the
σ-algebra of events almost surely determined by the field. -/
theorem measurable_aeSigma_of_ae_eq {β : Type*} [MeasurableSpace β] {Y : Ω → β}
    {f : DistOn upperHalfPlaneOpens → β} (hf : Measurable f) (hY : Y =ᵐ[P] fun ω => f (h ω)) :
    Measurable[aeSigma (MeasurableSpace.comap h inferInstance) P] Y := by
  intro B hB
  refine ⟨h ⁻¹' (f ⁻¹' B), ⟨f ⁻¹' B, hf hB, rfl⟩, ?_⟩
  filter_upwards [hY] with ω hω
  simp only [mem_preimage, hω]

/-- **Explored sets are determined by the field** (proof of Proposition 6.1: "`η_{θ₁}` and `η_{θ₂}`
are both almost surely determined by `h`", p. 153; with stopping times in Galmarino path form, the
stopped union is then also determined). Every event of the explored set is almost surely an event of
the field. -/
theorem comap_explored_le_aeSigma (hc : ∀ i ω, Continuous (η i ω))
    (hdet : ∀ i (t : ℝ≥0), ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => η i ω t) =ᵐ[P] fun ω => f (h ω))
    (hSm : ∀ j, Measurable (Function.uncurry (S j))) (hSg : ∀ j, IsGalmarino (S j))
    (hτ : ∀ j ω, τ j ω = S j (prevHist (fun i => pathCoord (η i ω)) (fun i => τ i ω) j)
      (pathCoord (η j ω))) :
    MeasurableSpace.comap (explored η τ) hittingSigma ≤
      aeSigma (MeasurableSpace.comap h inferInstance) P := by
  have hηm : ∀ i t, Measurable[aeSigma (MeasurableSpace.comap h inferInstance) P] fun ω => η i ω t := fun i t => by
    obtain ⟨f, hf, he⟩ := hdet i t
    exact measurable_aeSigma_of_ae_eq hf he
  have hpc : Measurable[aeSigma (MeasurableSpace.comap h inferInstance) P] fun ω i => pathCoord (η i ω) :=
    @Measurable.of_eval _ _ _ (aeSigma (MeasurableSpace.comap h inferInstance) P) _ _ fun i => @Measurable.of_eval _ _ _ (aeSigma (MeasurableSpace.comap h inferInstance) P) _ _ fun q => hηm i q
  have hτeq : ∀ ω, (fun i => τ i ω) = recon S (fun i => histOf (pathCoord (η i ω)) ⊤) :=
    fun ω => ((forall_le_iff_recon hSg (fun j => hτ j ω)).2 (fun _ => le_top)).symm
  have hrm : Measurable[aeSigma (MeasurableSpace.comap h inferInstance) P] fun ω => recon S (fun i => histOf (pathCoord (η i ω)) ⊤) := by
    refine (measurable_recon hSm).comp (@Measurable.of_eval _ _ _ (aeSigma (MeasurableSpace.comap h inferInstance) P) _ _ fun i => ?_)
    exact measurable_histOf.comp ((@measurable_const _ _ _ (aeSigma (MeasurableSpace.comap h inferInstance) P) _).prodMk
      ((measurable_pi_apply i).comp hpc))
  have hτm : ∀ i, Measurable[aeSigma (MeasurableSpace.comap h inferInstance) P] (τ i) := fun i => by
    have e : τ i = fun ω => recon S (fun i => histOf (pathCoord (η i ω)) ⊤) i :=
      funext fun ω => congrFun (hτeq ω) i
    rw [e]
    exact (measurable_pi_apply i).comp hrm
  exact (@measurable_explored Ω (aeSigma (MeasurableSpace.comap h inferInstance) P) k η τ hc hηm hτm).comap_le

/-- Galmarino stopping times of measurable paths are measurable. -/
theorem measurable_of_galmarino (hηm : ∀ i t, Measurable fun ω => η i ω t)
    (hSm : ∀ j, Measurable (Function.uncurry (S j))) (hSg : ∀ j, IsGalmarino (S j))
    (hτ : ∀ j ω, τ j ω = S j (prevHist (fun i => pathCoord (η i ω)) (fun i => τ i ω) j)
      (pathCoord (η j ω))) (i : Fin k) : Measurable (τ i) := by
  have hpc : Measurable fun ω i => pathCoord (η i ω) :=
    Measurable.of_eval fun i => Measurable.of_eval fun q => hηm i q
  have hrm : Measurable fun ω => recon S (fun i => histOf (pathCoord (η i ω)) ⊤) := by
    refine (measurable_recon hSm).comp (Measurable.of_eval fun i => ?_)
    exact measurable_histOf.comp (measurable_const.prodMk ((measurable_pi_apply i).comp hpc))
  have e : τ i = fun ω => recon S (fun i => histOf (pathCoord (η i ω)) ⊤) i :=
    funext fun ω => congrFun ((forall_le_iff_recon hSg (fun j => hτ j ω)).2 (fun _ => le_top)).symm i
  rw [e]
  exact (measurable_pi_apply i).comp hrm

end Determined

/-! ### The assembly -/

section Assembly

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {k : ℕ} {η : Fin k → Ω → ℝ≥0 → ℂ} {x : Fin k → ℂ}
  {τ : Fin k → Ω → ℝ≥0∞} {S : Fin k → (Fin k → Hist) → (ℚ≥0 → ℂ) → ℝ≥0∞}

/-- Deterministic stopping times are Galmarino. -/
theorem isGalmarino_const (c : ℝ≥0∞) : IsGalmarino (k := k) fun _ _ => c := fun _ _ _ _ => rfl

/-- Lemma 6.2 for transient curves: the explored set is a local set. -/
theorem isLocalSet_explored_of_tendsto (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hc : ∀ i ω, Continuous (η i ω))
    (h0 : ∀ i ω, η i ω 0 = x i) (hηm : ∀ i t, Measurable fun ω => η i ω t)
    (hdet : ∀ i (t : ℝ≥0), ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => η i ω t) =ᵐ[P] fun ω => f (h ω))
    (hloc : ∀ i, IsEntranceHistoryLocal (η i) h P)
    (htr : ∀ᵐ ω ∂P, ∀ i, Tendsto (η i ω) atTop (Bornology.cobounded ℂ))
    (hSm : ∀ j, Measurable (Function.uncurry (S j))) (hSg : ∀ j, IsGalmarino (S j))
    (hτ : ∀ j ω, τ j ω = S j (prevHist (fun i => pathCoord (η i ω)) (fun i => τ i ω) j)
      (pathCoord (η j ω))) :
    IsLocalSet (explored η τ) h P :=
  isLocalSet_explored hh hc h0 hηm hdet hloc hSm hSg hτ
    (measurable_of_galmarino hηm hSm hSg hτ)
    (htr.mono fun ω hω => isOpen_H_diff_explored (fun i => hc i ω) hω)

/-- **Proposition 6.1 for explored curves: the identification of the mean** (pp. 167–169). Let
`h` be a zero-boundary GFF on `ℍ` and `F` a bounded harmonic function (the field is `h + F`); let
`η₀, …, η_{k−1}` be continuous transient curves from real points in the closed half-plane satisfying
the hypotheses of Lemma 6.2 (measurable, determined by `h`, history-sensitively local), with stopping
times `τ` in Galmarino path form; `A(τ)` their explored set, `A(∞)` the full explored set, and
`T = A(τT)` for deterministic `τT ≤ τ` (for Proposition 6.1: `η₀ = η_{θ₂}`, `τ₀ = ∞`, `η₁ = η_{θ₁}`,
`τT = (∞, 0)`, so `T = η_{θ₂}`). Let `gS, gL, gT` be versions of the local-set means. Almost surely,
for every component `C` of `ℍ ∖ A(τ)` (bounded or not), all harmonic representatives, and every
chart `(f, φ_C, G, L)` of Aux. lemma 28 with finite exceptional set: if every other prime end has an
impression `p` that either lies on `A(τ) ∪ ℝ` with `A(∞) ⊆ A(τ)` near `p` and there the mean of
`A(∞)` has the boundary values of `𝔥_C = G ∘ φ_C − χ L` (the stopped prefix and the active slit), or
lies on `T ∪ ℝ` with `A(τ) ⊆ T` near `p` and there the mean of `T` has those boundary values (the
suffix of `η_{θ₂}`), then `𝒞_{A(τ)} + F = 𝔥_C` on `C`. -/
theorem ae_eqOn_explored_of_tendsto
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hc : ∀ i ω, Continuous (η i ω)) (h0 : ∀ i ω, η i ω 0 = x i) (hx : ∀ i, (x i).im = 0)
    (him : ∀ i ω t, 0 ≤ (η i ω t).im) (hηm : ∀ i t, Measurable fun ω => η i ω t)
    (hdet : ∀ i (t : ℝ≥0), ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => η i ω t) =ᵐ[P] fun ω => f (h ω))
    (hloc : ∀ i, IsEntranceHistoryLocal (η i) h P)
    (htr : ∀ᵐ ω ∂P, ∀ i, Tendsto (η i ω) atTop (Bornology.cobounded ℂ))
    (hSm : ∀ j, Measurable (Function.uncurry (S j))) (hSg : ∀ j, IsGalmarino (S j))
    (hτ : ∀ j ω, τ j ω = S j (prevHist (fun i => pathCoord (η i ω)) (fun i => τ i ω) j)
      (pathCoord (η j ω)))
    (τT : Fin k → ℝ≥0∞) (hτT : ∀ i ω, τT i ≤ τ i ω)
    {gS gL gT : Ω → DistOn upperHalfPlaneOpens} (hgS : IsLocalSetMean (explored η τ) h P gS)
    (hgL : IsLocalSetMean (explored η fun _ _ => ⊤) h P gL)
    (hgT : IsLocalSetMean (explored η fun i _ => τT i) h P gT) {F : ℂ → ℝ}
    (hF : InnerProductSpace.HarmonicOnNhd F H) (hFb : ∃ M : ℝ, ∀ z ∈ H, |F z| ≤ M) (χ : ℝ) :
    ∀ᵐ ω ∂P, ∀ z₀ ∈ H \ explored η τ ω,
      ∀ v vL vT : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ explored η τ ω) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ explored η τ ω →
        gS ω ψ = ∫ x, v x * ψ x) →
      InnerProductSpace.HarmonicOnNhd vL (H \ explored η (fun _ _ => ⊤) ω) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ explored η (fun _ _ => ⊤) ω →
        gL ω ψ = ∫ x, vL x * ψ x) →
      InnerProductSpace.HarmonicOnNhd vT (H \ explored η (fun i _ => τT i) ω) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ explored η (fun i _ => τT i) ω →
        gT ω ψ = ∫ x, vT x * ψ x) →
      ∀ (f φc : ℂ → ℂ) (G Lc : ℂ → ℝ) (E : Set ℂ),
      IsConformalBijection f (ball 0 1) (connectedComponentIn (H \ explored η τ ω) z₀) →
      IsConformalBijection φc (connectedComponentIn (H \ explored η τ ω) z₀) {w : ℂ | 0 < w.im} →
      InnerProductSpace.HarmonicOnNhd G {w : ℂ | 0 < w.im} →
      (∃ M, ∀ w : ℂ, 0 < w.im → |G w| ≤ M) →
      ContinuousOn Lc (connectedComponentIn (H \ explored η τ ω) z₀) →
      (∀ z ∈ connectedComponentIn (H \ explored η τ ω) z₀,
        deriv φc z = ‖deriv φc z‖ * exp (Lc z * I)) →
      E.Finite →
      (∀ q ∈ sphere (0 : ℂ) 1, q ∉ E → ∃ p : ℂ, Tendsto f (𝓝[ball 0 1] q) (𝓝 p) ∧
        ((p ∈ explored η τ ω ∪ {z : ℂ | z.im = 0} ∧
            (∃ r > 0, explored η (fun _ _ => ⊤) ω ∩ ball p r ⊆ explored η τ ω) ∧
            Tendsto (fun ζ => (vL (f ζ) + F (f ζ)) - (G (φc (f ζ)) - χ * Lc (f ζ)))
              (𝓝[ball 0 1] q) (𝓝 0)) ∨
          (p ∈ explored η (fun i _ => τT i) ω ∪ {z : ℂ | z.im = 0} ∧
            (∃ r > 0, explored η τ ω ∩ ball p r ⊆ explored η (fun i _ => τT i) ω) ∧
            Tendsto (fun ζ => (vT (f ζ) + F (f ζ)) - (G (φc (f ζ)) - χ * Lc (f ζ)))
              (𝓝[ball 0 1] q) (𝓝 0)))) →
      ∀ z ∈ connectedComponentIn (H \ explored η τ ω) z₀, v z + F z = G (φc z) - χ * Lc z := by
  have hτm := measurable_of_galmarino hηm hSm hSg hτ
  have hSl : IsLocalSet (explored η τ) h P :=
    isLocalSet_explored_of_tendsto hh hc h0 hηm hdet hloc htr hSm hSg hτ
  have hLl : IsLocalSet (explored η fun _ _ => ⊤) h P :=
    isLocalSet_explored_of_tendsto (S := fun _ _ _ => ⊤) hh hc h0 hηm hdet hloc htr
      (fun _ => measurable_const) (fun _ => isGalmarino_const ⊤) (fun _ _ => rfl)
  have hTl : IsLocalSet (explored η fun i _ => τT i) h P :=
    isLocalSet_explored_of_tendsto (S := fun j _ _ => τT j) hh hc h0 hηm hdet hloc htr
      (fun _ => measurable_const) (fun j => isGalmarino_const (τT j)) (fun _ _ => rfl)
  have hSmeas : Measurable[mΩ, hittingSigma] (explored η τ) := measurable_explored hc hηm hτm
  have hLmeas : Measurable[mΩ, hittingSigma] (explored η fun _ _ => ⊤) :=
    measurable_explored hc hηm fun _ => measurable_const
  have hTmeas : Measurable[mΩ, hittingSigma] (explored η fun i _ => τT i) :=
    measurable_explored hc hηm fun _ => measurable_const
  have hdetL := comap_explored_le_aeSigma (P := P) (h := h) (S := fun _ _ _ => ⊤) (τ := fun _ _ => ⊤)
    hc hdet (fun _ => measurable_const) (fun _ => isGalmarino_const ⊤) (fun _ _ => rfl)
  have hdetS := comap_explored_le_aeSigma (P := P) hc hdet hSm hSg hτ
  have hci : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap (explored η fun _ _ => ⊤) hittingSigma)
      (MeasurableSpace.comap (explored η τ) hittingSigma) P :=
    condIndepEv_of_le_aeSigma hh.measurable.comap_le hSmeas.comap_le hdetL
  have hciT : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap (explored η τ) hittingSigma)
      (MeasurableSpace.comap (explored η fun i _ => τT i) hittingSigma) P :=
    condIndepEv_of_le_aeSigma hh.measurable.comap_le hTmeas.comap_le hdetS
  have h0im : ∀ i ω, (η i ω 0).im = 0 := fun i ω => by rw [h0]; exact hx i
  exact ae_eqOn_component_of_subset_of_tendsto_global hh hSmeas hLmeas hTmeas
    (fun _ => explored_mono fun _ => le_top) (fun ω => explored_mono fun i => hτT i ω) hci hciT
    hSl hLl hTl
    (Eventually.of_forall fun ω => not_isBounded_lowerUnion_explored (fun i => hc i ω)
      (fun i => h0im i ω) (fun i t => him i ω t))
    (Eventually.of_forall fun ω => not_isBounded_lowerUnion_explored (fun i => hc i ω)
      (fun i => h0im i ω) (fun i t => him i ω t))
    hgS hgL hgT hF hFb χ

/-- **Proposition 6.1 for explored curves: the conditional law given the labeled curves** (p. 154:
"Condition on the ordered labeled pair `(η_{θ₁}|_{[0,τ]}, η_{θ₂})` … Retain the canonical revealed
germs during the local-set argument … Then the law of `h̃|_C` is equal to that of the sum of a zero
boundary GFF in `C` plus `𝔥_C`"). Under the hypotheses of `ae_eqOn_explored_of_tendsto`, for a test
function `φ`: almost surely, for every component `C` of `ℍ ∖ A(τ)` containing the support of `φ` and
every chart satisfying the prime-end premise, given the germs of `A(τ)` **and the ordered stopped
curves** (`stoppedHistSigma η τ`), the field `h + F` paired with `φ` has the conditional characteristic
function of `(𝔥_C, φ) + GFF_C(φ)`, `𝔥_C = G ∘ φ_C − χ L`. (`ae_condExp_exp_eq_of_le_marked` then
forgets the germs, once the mean pairing and the variance are known to be measurable functions of the
labeled curves.) -/
theorem ae_condExp_exp_eq_explored_of_tendsto
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hc : ∀ i ω, Continuous (η i ω)) (h0 : ∀ i ω, η i ω 0 = x i) (hx : ∀ i, (x i).im = 0)
    (him : ∀ i ω t, 0 ≤ (η i ω t).im) (hηm : ∀ i t, Measurable fun ω => η i ω t)
    (hdet : ∀ i (t : ℝ≥0), ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => η i ω t) =ᵐ[P] fun ω => f (h ω))
    (hloc : ∀ i, IsEntranceHistoryLocal (η i) h P)
    (htr : ∀ᵐ ω ∂P, ∀ i, Tendsto (η i ω) atTop (Bornology.cobounded ℂ))
    (hSm : ∀ j, Measurable (Function.uncurry (S j))) (hSg : ∀ j, IsGalmarino (S j))
    (hτ : ∀ j ω, τ j ω = S j (prevHist (fun i => pathCoord (η i ω)) (fun i => τ i ω) j)
      (pathCoord (η j ω)))
    (τT : Fin k → ℝ≥0∞) (hτT : ∀ i ω, τT i ≤ τ i ω)
    {gS gL gT : Ω → DistOn upperHalfPlaneOpens} (hgS : IsLocalSetMean (explored η τ) h P gS)
    (hgL : IsLocalSetMean (explored η fun _ _ => ⊤) h P gL)
    (hgT : IsLocalSetMean (explored η fun i _ => τT i) h P gT) {F : ℂ → ℝ}
    (hF : InnerProductSpace.HarmonicOnNhd F H) (hFb : ∃ M : ℝ, ∀ z ∈ H, |F z| ≤ M) (χ : ℝ) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ∀ z₀ ∈ H \ explored η τ ω,
      tsupport φ ⊆ connectedComponentIn (H \ explored η τ ω) z₀ →
      ∀ v vL vT : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ explored η τ ω) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ explored η τ ω →
        gS ω ψ = ∫ x, v x * ψ x) →
      InnerProductSpace.HarmonicOnNhd vL (H \ explored η (fun _ _ => ⊤) ω) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ explored η (fun _ _ => ⊤) ω →
        gL ω ψ = ∫ x, vL x * ψ x) →
      InnerProductSpace.HarmonicOnNhd vT (H \ explored η (fun i _ => τT i) ω) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ explored η (fun i _ => τT i) ω →
        gT ω ψ = ∫ x, vT x * ψ x) →
      ∀ (f φc : ℂ → ℂ) (G Lc : ℂ → ℝ) (E : Set ℂ),
      IsConformalBijection f (ball 0 1) (connectedComponentIn (H \ explored η τ ω) z₀) →
      IsConformalBijection φc (connectedComponentIn (H \ explored η τ ω) z₀) {w : ℂ | 0 < w.im} →
      InnerProductSpace.HarmonicOnNhd G {w : ℂ | 0 < w.im} →
      (∃ M, ∀ w : ℂ, 0 < w.im → |G w| ≤ M) →
      ContinuousOn Lc (connectedComponentIn (H \ explored η τ ω) z₀) →
      (∀ z ∈ connectedComponentIn (H \ explored η τ ω) z₀,
        deriv φc z = ‖deriv φc z‖ * exp (Lc z * I)) →
      E.Finite →
      (∀ q ∈ sphere (0 : ℂ) 1, q ∉ E → ∃ p : ℂ, Tendsto f (𝓝[ball 0 1] q) (𝓝 p) ∧
        ((p ∈ explored η τ ω ∪ {z : ℂ | z.im = 0} ∧
            (∃ r > 0, explored η (fun _ _ => ⊤) ω ∩ ball p r ⊆ explored η τ ω) ∧
            Tendsto (fun ζ => (vL (f ζ) + F (f ζ)) - (G (φc (f ζ)) - χ * Lc (f ζ)))
              (𝓝[ball 0 1] q) (𝓝 0)) ∨
          (p ∈ explored η (fun i _ => τT i) ω ∪ {z : ℂ | z.im = 0} ∧
            (∃ r > 0, explored η τ ω ∩ ball p r ⊆ explored η (fun i _ => τT i) ω) ∧
            Tendsto (fun ζ => (vT (f ζ) + F (f ζ)) - (G (φc (f ζ)) - χ * Lc (f ζ)))
              (𝓝[ball 0 1] q) (𝓝 0)))) →
      P[fun ω' => cexp (I * ((h ω' φ + ∫ x, F x * φ x : ℝ) : ℂ)) |
          germSigma (explored η τ) h ⊔ stoppedHistSigma η τ] ω =
        cexp (I * ((∫ x, (G (φc x) - χ * Lc x) * φ x : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * QuantumZipper.zeroGFFTestCov
            (connectedComponentIn (H \ explored η τ ω) z₀) φ φ) : ℝ) : ℂ) := by
  have hτm := measurable_of_galmarino hηm hSm hSg hτ
  have hSl : IsLocalSet (explored η τ) h P :=
    isLocalSet_explored_of_tendsto hh hc h0 hηm hdet hloc htr hSm hSg hτ
  have hSmeas : Measurable[mΩ, hittingSigma] (explored η τ) := measurable_explored hc hηm hτm
  have hmark := isHistoryAvoidanceLocal_explored hh.measurable hc h0 hηm hdet hloc hSm hSg hτ
  have hFc : ContinuousOn F H := fun z hz => (hF z hz).1.continuousAt.continuousWithinAt
  filter_upwards [ae_condExp_exp_eq_of_eqOn_component_marked hh hSmeas hSl
      (stoppedHistSigma_le hηm hτm) hmark hgS hFc φ,
    ae_eqOn_explored_of_tendsto hh hc h0 hx him hηm hdet hloc htr hSm hSg hτ τT hτT hgS hgL hgT hF
      hFb χ]
    with ω hlaw hid z₀ hz₀ hφC v vL vT hv hvrep hvL hvLrep hvT hvTrep f φc G Lc E hf hφc hG hGb hLc
      hLd hE hbd
  exact hlaw z₀ hz₀ hφC v hv hvrep _ (hid z₀ hz₀ v vL vT hv hvrep hvL hvLrep hvT hvTrep f φc G Lc E
    hf hφc hG hGb hLc hLd hE hbd)

/-- **Proposition 6.1 for explored curves, the full union** (the case `τ = ∞`, p. 167: the pockets
between the two curves and the exterior components). For deterministic stopping times `τ₁, τ₂` (for
Proposition 6.1: `τ₁ = (0, ∞)`, so `A₁ = η_{θ₁}`, and `τ₂ = (∞, 0)`, so `A₂ = η_{θ₂}`), under the
curve hypotheses of `ae_eqOn_explored_of_tendsto`: almost surely, for every component `C` of
`ℍ ∖ (A₁ ∪ A₂)` (bounded or not) and every chart satisfying the prime-end premise of
`ae_eqOn_component_union_of_tendsto_global` (each prime end outside a finite set has an impression on
one curve, near which the other curve is contained in it, and there that curve's mean has the boundary
values of `𝔥_C`), `𝒞_{A₁ ∪ A₂} + F = 𝔥_C` on `C`. -/
theorem ae_eqOn_explored_union_of_tendsto
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hc : ∀ i ω, Continuous (η i ω)) (h0 : ∀ i ω, η i ω 0 = x i) (hx : ∀ i, (x i).im = 0)
    (him : ∀ i ω t, 0 ≤ (η i ω t).im) (hηm : ∀ i t, Measurable fun ω => η i ω t)
    (hdet : ∀ i (t : ℝ≥0), ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => η i ω t) =ᵐ[P] fun ω => f (h ω))
    (hloc : ∀ i, IsEntranceHistoryLocal (η i) h P)
    (htr : ∀ᵐ ω ∂P, ∀ i, Tendsto (η i ω) atTop (Bornology.cobounded ℂ))
    (τ₁ τ₂ : Fin k → ℝ≥0∞) {g g₁ g₂ : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (explored η fun i _ => max (τ₁ i) (τ₂ i)) h P g)
    (hg₁ : IsLocalSetMean (explored η fun i _ => τ₁ i) h P g₁)
    (hg₂ : IsLocalSetMean (explored η fun i _ => τ₂ i) h P g₂) {F : ℂ → ℝ}
    (hF : InnerProductSpace.HarmonicOnNhd F H) (hFb : ∃ M : ℝ, ∀ z ∈ H, |F z| ≤ M) (χ : ℝ) :
    ∀ᵐ ω ∂P, ∀ z₀ ∈ H \ explored η (fun i _ => max (τ₁ i) (τ₂ i)) ω,
      ∀ v v₁ v₂ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ explored η (fun i _ => max (τ₁ i) (τ₂ i)) ω) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ explored η (fun i _ => max (τ₁ i) (τ₂ i)) ω → g ω ψ = ∫ x, v x * ψ x) →
      InnerProductSpace.HarmonicOnNhd v₁ (H \ explored η (fun i _ => τ₁ i) ω) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ explored η (fun i _ => τ₁ i) ω → g₁ ω ψ = ∫ x, v₁ x * ψ x) →
      InnerProductSpace.HarmonicOnNhd v₂ (H \ explored η (fun i _ => τ₂ i) ω) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ explored η (fun i _ => τ₂ i) ω → g₂ ω ψ = ∫ x, v₂ x * ψ x) →
      ∀ (f φc : ℂ → ℂ) (G Lc : ℂ → ℝ) (E : Set ℂ),
      IsConformalBijection f (ball 0 1) (connectedComponentIn (H \ explored η (fun i _ => max (τ₁ i) (τ₂ i)) ω) z₀) →
      IsConformalBijection φc (connectedComponentIn (H \ explored η (fun i _ => max (τ₁ i) (τ₂ i)) ω) z₀) {w : ℂ | 0 < w.im} →
      InnerProductSpace.HarmonicOnNhd G {w : ℂ | 0 < w.im} →
      (∃ M, ∀ w : ℂ, 0 < w.im → |G w| ≤ M) →
      ContinuousOn Lc (connectedComponentIn (H \ explored η (fun i _ => max (τ₁ i) (τ₂ i)) ω) z₀) →
      (∀ z ∈ connectedComponentIn (H \ explored η (fun i _ => max (τ₁ i) (τ₂ i)) ω) z₀, deriv φc z = ‖deriv φc z‖ * exp (Lc z * I)) →
      E.Finite →
      (∀ q ∈ sphere (0 : ℂ) 1, q ∉ E → ∃ p : ℂ, Tendsto f (𝓝[ball 0 1] q) (𝓝 p) ∧
        ((p ∈ explored η (fun i _ => τ₂ i) ω ∪ {z : ℂ | z.im = 0} ∧ (∃ r > 0, explored η (fun i _ => τ₁ i) ω ∩ ball p r ⊆
              explored η (fun i _ => τ₂ i) ω) ∧
            Tendsto (fun ζ => (v₂ (f ζ) + F (f ζ)) - (G (φc (f ζ)) - χ * Lc (f ζ)))
              (𝓝[ball 0 1] q) (𝓝 0)) ∨
          (p ∈ explored η (fun i _ => τ₁ i) ω ∪ {z : ℂ | z.im = 0} ∧ (∃ r > 0, explored η (fun i _ => τ₂ i) ω ∩ ball p r ⊆
              explored η (fun i _ => τ₁ i) ω) ∧
            Tendsto (fun ζ => (v₁ (f ζ) + F (f ζ)) - (G (φc (f ζ)) - χ * Lc (f ζ)))
              (𝓝[ball 0 1] q) (𝓝 0)))) →
      ∀ z ∈ connectedComponentIn (H \ explored η (fun i _ => max (τ₁ i) (τ₂ i)) ω) z₀, v z + F z = G (φc z) - χ * Lc z := by
  have hl : ∀ τ' : Fin k → ℝ≥0∞, IsLocalSet (explored η fun i _ => τ' i) h P := fun τ' =>
    isLocalSet_explored_of_tendsto (S := fun j _ _ => τ' j) hh hc h0 hηm hdet hloc htr
      (fun _ => measurable_const) (fun j => isGalmarino_const (τ' j)) (fun _ _ => rfl)
  have hm : ∀ τ' : Fin k → ℝ≥0∞, Measurable[mΩ, hittingSigma] (explored η fun i _ => τ' i) :=
    fun τ' => measurable_explored hc hηm fun _ => measurable_const
  have hd : ∀ τ' : Fin k → ℝ≥0∞, MeasurableSpace.comap (explored η fun i _ => τ' i) hittingSigma ≤
      aeSigma (MeasurableSpace.comap h inferInstance) P := fun τ' =>
    comap_explored_le_aeSigma (S := fun j _ _ => τ' j) hc hdet (fun _ => measurable_const)
      (fun j => isGalmarino_const (τ' j)) (fun _ _ => rfl)
  have hci : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap (explored η fun i _ => τ₁ i) hittingSigma)
      (MeasurableSpace.comap (explored η fun i _ => τ₂ i) hittingSigma) P :=
    condIndepEv_of_le_aeSigma hh.measurable.comap_le (hm τ₂).comap_le (hd τ₁)
  have h0im : ∀ i ω, (η i ω 0).im = 0 := fun i ω => by rw [h0]; exact hx i
  have hunb : ∀ τ' : Fin k → ℝ≥0∞, ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (explored η (fun i _ => τ' i) ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (explored η (fun i _ => τ' i) ω)) z) :=
    fun τ' => Eventually.of_forall fun ω => not_isBounded_lowerUnion_explored (fun i => hc i ω)
      (fun i => h0im i ω) (fun i t => him i ω t)
  have hU : (fun ω => explored η (fun i _ => τ₁ i) ω ∪ explored η (fun i _ => τ₂ i) ω) =
      explored η fun i _ => max (τ₁ i) (τ₂ i) :=
    funext fun ω => explored_union_eq_max η _ _ ω
  have hg' : IsLocalSetMean (fun ω => explored η (fun i _ => τ₁ i) ω ∪
      explored η (fun i _ => τ₂ i) ω) h P g := by rw [hU]; exact hg
  have key := ae_eqOn_component_union_of_tendsto_global hh (hm τ₁) (hm τ₂) hci (hl τ₁) (hl τ₂)
    (hunb τ₁) (hunb τ₂) hg' hg₁ hg₂ hF hFb χ
  simp only [explored_union_eq_max] at key
  exact key

/-- **Proposition 6.1 for explored curves, the full union, the conditional law given the labeled
curves** (`τ = ∞`): under the hypotheses of `ae_eqOn_explored_union_of_tendsto` and for a test
function `φ` supported in the component `C`, given the germs of `A₁ ∪ A₂` and the ordered curves, the
field `h + F` paired with `φ` has the conditional characteristic function of `(𝔥_C, φ) + GFF_C(φ)`. -/
theorem ae_condExp_exp_eq_explored_union_of_tendsto
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hc : ∀ i ω, Continuous (η i ω)) (h0 : ∀ i ω, η i ω 0 = x i) (hx : ∀ i, (x i).im = 0)
    (him : ∀ i ω t, 0 ≤ (η i ω t).im) (hηm : ∀ i t, Measurable fun ω => η i ω t)
    (hdet : ∀ i (t : ℝ≥0), ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => η i ω t) =ᵐ[P] fun ω => f (h ω))
    (hloc : ∀ i, IsEntranceHistoryLocal (η i) h P)
    (htr : ∀ᵐ ω ∂P, ∀ i, Tendsto (η i ω) atTop (Bornology.cobounded ℂ))
    (τ₁ τ₂ : Fin k → ℝ≥0∞) {g g₁ g₂ : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (explored η fun i _ => max (τ₁ i) (τ₂ i)) h P g)
    (hg₁ : IsLocalSetMean (explored η fun i _ => τ₁ i) h P g₁)
    (hg₂ : IsLocalSetMean (explored η fun i _ => τ₂ i) h P g₂) {F : ℂ → ℝ}
    (hF : InnerProductSpace.HarmonicOnNhd F H) (hFb : ∃ M : ℝ, ∀ z ∈ H, |F z| ≤ M) (χ : ℝ) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ∀ z₀ ∈ H \ explored η (fun i _ => max (τ₁ i) (τ₂ i)) ω,
      tsupport φ ⊆ connectedComponentIn (H \ explored η (fun i _ => max (τ₁ i) (τ₂ i)) ω) z₀ →
      ∀ v v₁ v₂ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ explored η (fun i _ => max (τ₁ i) (τ₂ i)) ω) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ explored η (fun i _ => max (τ₁ i) (τ₂ i)) ω → g ω ψ = ∫ x, v x * ψ x) →
      InnerProductSpace.HarmonicOnNhd v₁ (H \ explored η (fun i _ => τ₁ i) ω) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ explored η (fun i _ => τ₁ i) ω → g₁ ω ψ = ∫ x, v₁ x * ψ x) →
      InnerProductSpace.HarmonicOnNhd v₂ (H \ explored η (fun i _ => τ₂ i) ω) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ explored η (fun i _ => τ₂ i) ω → g₂ ω ψ = ∫ x, v₂ x * ψ x) →
      ∀ (f φc : ℂ → ℂ) (G Lc : ℂ → ℝ) (E : Set ℂ),
      IsConformalBijection f (ball 0 1) (connectedComponentIn (H \ explored η (fun i _ => max (τ₁ i) (τ₂ i)) ω) z₀) →
      IsConformalBijection φc (connectedComponentIn (H \ explored η (fun i _ => max (τ₁ i) (τ₂ i)) ω) z₀) {w : ℂ | 0 < w.im} →
      InnerProductSpace.HarmonicOnNhd G {w : ℂ | 0 < w.im} →
      (∃ M, ∀ w : ℂ, 0 < w.im → |G w| ≤ M) →
      ContinuousOn Lc (connectedComponentIn (H \ explored η (fun i _ => max (τ₁ i) (τ₂ i)) ω) z₀) →
      (∀ z ∈ connectedComponentIn (H \ explored η (fun i _ => max (τ₁ i) (τ₂ i)) ω) z₀, deriv φc z = ‖deriv φc z‖ * exp (Lc z * I)) →
      E.Finite →
      (∀ q ∈ sphere (0 : ℂ) 1, q ∉ E → ∃ p : ℂ, Tendsto f (𝓝[ball 0 1] q) (𝓝 p) ∧
        ((p ∈ explored η (fun i _ => τ₂ i) ω ∪ {z : ℂ | z.im = 0} ∧ (∃ r > 0, explored η (fun i _ => τ₁ i) ω ∩ ball p r ⊆
              explored η (fun i _ => τ₂ i) ω) ∧
            Tendsto (fun ζ => (v₂ (f ζ) + F (f ζ)) - (G (φc (f ζ)) - χ * Lc (f ζ)))
              (𝓝[ball 0 1] q) (𝓝 0)) ∨
          (p ∈ explored η (fun i _ => τ₁ i) ω ∪ {z : ℂ | z.im = 0} ∧ (∃ r > 0, explored η (fun i _ => τ₂ i) ω ∩ ball p r ⊆
              explored η (fun i _ => τ₁ i) ω) ∧
            Tendsto (fun ζ => (v₁ (f ζ) + F (f ζ)) - (G (φc (f ζ)) - χ * Lc (f ζ)))
              (𝓝[ball 0 1] q) (𝓝 0)))) →
      P[fun ω' => cexp (I * ((h ω' φ + ∫ x, F x * φ x : ℝ) : ℂ)) |
          germSigma (explored η fun i _ => max (τ₁ i) (τ₂ i)) h ⊔
            stoppedHistSigma η fun i _ => max (τ₁ i) (τ₂ i)] ω =
        cexp (I * ((∫ x, (G (φc x) - χ * Lc x) * φ x : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * QuantumZipper.zeroGFFTestCov
            (connectedComponentIn (H \ explored η (fun i _ => max (τ₁ i) (τ₂ i)) ω) z₀) φ φ) : ℝ) : ℂ) := by
  have hSl : IsLocalSet (explored η fun i _ => max (τ₁ i) (τ₂ i)) h P :=
    isLocalSet_explored_of_tendsto (S := fun j _ _ => max (τ₁ j) (τ₂ j)) hh hc h0 hηm hdet hloc htr
      (fun _ => measurable_const) (fun j => isGalmarino_const _) (fun _ _ => rfl)
  have hSmeas : Measurable[mΩ, hittingSigma] (explored η fun i _ => max (τ₁ i) (τ₂ i)) :=
    measurable_explored hc hηm fun _ => measurable_const
  have hmark := isHistoryAvoidanceLocal_explored (S := fun j _ _ => max (τ₁ j) (τ₂ j))
    hh.measurable hc h0 hηm hdet hloc (fun _ => measurable_const) (fun j => isGalmarino_const _)
    (fun _ _ => rfl)
  have hFc : ContinuousOn F H := fun z hz => (hF z hz).1.continuousAt.continuousWithinAt
  filter_upwards [ae_condExp_exp_eq_of_eqOn_component_marked hh hSmeas hSl
      (stoppedHistSigma_le hηm fun _ => measurable_const) hmark hg hFc φ,
    ae_eqOn_explored_union_of_tendsto hh hc h0 hx him hηm hdet hloc htr τ₁ τ₂ hg hg₁ hg₂ hF hFb χ]
    with ω hlaw hid z₀ hz₀ hφC v v₁ v₂ hv hvrep hv₁ hv₁rep hv₂ hv₂rep f φc G Lc E hf hφc hG hGb hLc
      hLd hE hbd
  exact hlaw z₀ hz₀ hφC v hv hvrep _ (hid z₀ hz₀ v v₁ v₂ hv hvrep hv₁ hv₁rep hv₂ hv₂rep f φc G Lc E
    hf hφc hG hGb hLc hLd hE hbd)

end Assembly
