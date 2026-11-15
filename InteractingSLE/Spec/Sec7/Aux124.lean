/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.MarkedProp39

/-!
# Aux. lemma 124: preserving an interior kernel after retaining the exterior

Packet PROVE-STRIPSYS9. Specification §7.4, Aux. lemma 124 (`source/spec/p385-432.md#aux-124`, pp. 393–394):

> Let `A`, with its complete labels and canonical germ, be a field-determined marked local set, and let `C` be a
> Jordan component of `D ∖ A` selected measurably from those labels. Put `B = D ∖ C` … Retain the full canonical
> projection `h_B` … Let `R_t` be the stopped range of a continuous field-determined history-local exploration
> starting in `B`. Assume the marked optional union law for `A ∪ R_t`, with its stopped history and individual germs
> retained. … On each component of `C ∖ R_t`, its harmonic conditional mean is the same as the mean with only the
> marked `A ∪ R_t` initially retained. … In particular, an already established all-stop boundary-word formula in the
> active component of `C ∖ R_t` is preserved by the additional exterior reveal.

## Formalization

* `K` stands for the marked union `A ∪ R_t` (at a deterministic time, or at any stopping time at which the marked union
  law is available — the lemma's hypothesis), with its marks `ℋ` (the labels and germs of `A`, the stopped history of
  `R`). Its marked union law is `IsLocalSet K h P` together with the history-marked avoidance criterion
  `WholeField.IsHistoryAvoidanceLocal ℋ K h P` (Aux. lemma 18).
* `C` is a union of components of `ℍ ∖ A₀` (`A₀` the initial set `A`), `A₀ ⊆ K`, and `ℍ ∖ C` is measurable from the
  marks. Then `C ∖ K` is a union of components of `ℍ ∖ K` (`sdiff_isUnionComponents`): "every component of `D ∖ K_t`
  lies in one component of `D ∖ A`".
* The exterior information `h_B` is the field off `C` (`offSigma C h`, together with the germs of `A` and their
  harmonic extension, which the marks contain); the germ of `B ∪ R_t` is the germ σ-algebra of `(ℍ ∖ C) ∪ K`.

## Main results

* `ae_condExp_exp_exteriorReveal` (**Aux. lemma 124, the interior kernel**): for every σ-algebra `𝒥` between the
  marked `K` (`𝒦_K = 𝒜_K ∨ ℋ`) and `𝒦_K ∨ σ(h|_{ℍ∖C}) ∨ 𝒜_{B∪K}` (and more generally below
  `markedOffCoverSigma K (C ∖ K) ℋ h`), almost surely on `{supp φ ⊆ C ∖ K}`,
  `E[e^{i(h, φ)} | 𝒥] = e^{i(𝒞_K, φ)} e^{−σ²_{C∖K}(φ)/2}`: the conditional mean on `C ∖ K` is the mean `𝒞_K` with only
  the marked `K` retained, and the residual is the zero-boundary GFF of `C ∖ K`;
* `ae_condExp_exp_exteriorReveal_eq` : the two conditional characteristic functions (with and without the exterior
  reveal and the germ of `B ∪ K`) agree;
* `ae_condExp_exp_exteriorReveal_component` : the same in a single component of `ℍ ∖ K` inside `C`;
* `ae_condExp_exp_exteriorReveal_forget` : the law given any smaller σ-algebra (e.g. the exterior information `ℰ`
  together with a stopped history) when the mean and the variance are measurable from it ("an already established
  all-stop boundary-word formula … is preserved by the additional exterior reveal").

## Not formalized here

The optional clause "`B ∪ R_T` has the corresponding full marked local-set law at every stopping time `T` for the
filtration initially enlarged by `ℰ`" (exterior-dependent stopping times) is not proved. The consumers (Aux. 125's
relative clock) only use the stopping times `T(s)` of the relative clock at deterministic `s`, which are stopping times
of the un-enlarged exploration filtration (`RelClock.isStoppingTime_rightInv_const`); at those times the hypothesis of
the theorems below is the lemma's own assumption, and the enlarged conditioning is handled by
`ae_condExp_exp_exteriorReveal_forget` (exterior information as part of `𝒥`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace Metric
open scoped ENNReal

namespace InteractingSLE
namespace Sec7
namespace Aux124

open QuantumZipper LQGMetric LocalSets WholeField MarkedProp39

/-! ### Deterministic facts -/

/-- **Components of `ℍ ∖ K` inside `C`.** If `C ⊆ ℍ ∖ A₀` is a union of components of `ℍ ∖ A₀` and `A₀ ⊆ K`, then
`C ∖ K` is a union of components of `ℍ ∖ K`. -/
theorem sdiff_isUnionComponents {A₀ K C : Set ℂ} (hCs : C ⊆ H \ A₀)
    (hCc : ∀ z ∈ C, connectedComponentIn (H \ A₀) z ⊆ C) (hA₀K : A₀ ⊆ K) :
    C \ K ⊆ H \ K ∧ ∀ z ∈ C \ K, connectedComponentIn (H \ K) z ⊆ C \ K := by
  have hsub : H \ K ⊆ H \ A₀ := sdiff_subset_sdiff_right hA₀K
  refine ⟨fun z hz => ⟨(hCs hz.1).1, hz.2⟩, fun z hz w hw => ⟨?_, ?_⟩⟩
  · exact hCc z hz.1 (connectedComponentIn_mono z hsub hw)
  · exact (connectedComponentIn_subset _ _ hw).2

/-- `(ℍ ∖ (C ∖ K)) ∪ K = (ℍ ∖ C) ∪ K`: the set `S` of the marked cover argument for `C ∖ K` is `B ∪ K`. -/
theorem compl_sdiff_union_eq (C K : Set ℂ) : (H \ (C \ K)) ∪ K = (H \ C) ∪ K := by
  ext z
  simp only [mem_union, Set.mem_sdiff, not_and, not_not]
  tauto

/-- Measurability for the hitting σ-algebra only sees the trace on `ℍ`. -/
theorem measurable_hitting_of_inter_H_eq {Ω : Type*} {m : MeasurableSpace Ω} {f f' : Ω → Set ℂ}
    (hf : Measurable[m, hittingSigma] f) (he : ∀ ω, f' ω ∩ H = f ω ∩ H) : Measurable[m, hittingSigma] f' := by
  refine @measurable_generateFrom Ω (Set ℂ) m _ _ ?_
  rintro _ ⟨U, hU, hUH, rfl⟩
  have e : f' ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} = f ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq]
    have h1 : f' ω ∩ U = f' ω ∩ H ∩ U := by rw [inter_assoc, inter_eq_right.2 hUH]
    have h2 : f ω ∩ U = f ω ∩ H ∩ U := by rw [inter_assoc, inter_eq_right.2 hUH]
    rw [h1, h2, he ω]
  rw [e]
  exact hf (measurableSet_hitting hU hUH)

/-- `ℍ ∖ (C ∖ K)` is measurable from `σ(K) ∨ ℋ` when `ℍ ∖ C` is. -/
theorem measurable_compl_sdiff {Ω : Type*} {m : MeasurableSpace Ω} {C K : Ω → Set ℂ}
    (hC : Measurable[m, hittingSigma] fun ω => H \ C ω) (hK : Measurable[m, hittingSigma] K) :
    Measurable[m, hittingSigma] fun ω => H \ (C ω \ K ω) := by
  refine measurable_hitting_of_inter_H_eq (f := fun ω => (H \ C ω) ∪ K ω)
    (measurable_union_hitting hC hK) fun ω => ?_
  ext z
  simp only [mem_inter_iff, mem_union, Set.mem_sdiff, not_and, not_not]
  tauto

/-! ### The exterior reveal -/

section Reveal

variable {Ω : Type u} {ℋ 𝒥 : MeasurableSpace Ω} {K C : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}

/-- The exterior field `σ(h|_{ℍ∖C})` is part of the conditioning σ-algebra of the marked cover argument for
`C ∖ K`, when `ℍ ∖ C` is measurable from the marks. -/
theorem offSigma_le_markedOffCoverSigma_sdiff
    (hCm : Measurable[MeasurableSpace.comap K hittingSigma ⊔ ℋ, hittingSigma] fun ω => H \ C ω) :
    offSigma C h ≤ markedOffCoverSigma K (fun ω => C ω \ K ω) ℋ h := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro _ ⟨ψ, B, hB, rfl⟩
  have hsub : ∀ ω, relClosureH (H \ C ω) ⊆ relClosureH (H \ (C ω \ K ω)) := fun ω =>
    inter_subset_inter_right _ (closure_mono (inter_subset_inter_left _
      (sdiff_subset_sdiff_right sdiff_subset)))
  have e : {ω | tsupport ψ ⊆ relClosureH (H \ C ω)} ∩ (fun ω => h ω ψ) ⁻¹' B =
      {ω | tsupport ψ ⊆ relClosureH (H \ C ω)} ∩
        ({ω | tsupport ψ ⊆ relClosureH (H \ (C ω \ K ω))} ∩ (fun ω => h ω ψ) ⁻¹' B) := by
    ext ω
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h1.trans (hsub ω), h2⟩
    · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
  rw [e]
  have hE : MeasurableSet[MeasurableSpace.comap K hittingSigma ⊔ ℋ]
      {ω | tsupport ψ ⊆ relClosureH (H \ C ω)} :=
    hCm (measurableSet_subset_relClosureH ψ.hasCompactSupport ψ.tsupport_subset)
  refine MeasurableSet.inter ((le_sup_right.trans (le_sup_left.trans le_sup_left) :
    MeasurableSpace.comap K hittingSigma ⊔ ℋ ≤ markedOffCoverSigma K (fun ω => C ω \ K ω) ℋ h) _ hE) ?_
  exact offSigma_le_markedOffCoverSigma (A := K) (ℋ := ℋ) _ _
    (MeasurableSpace.measurableSet_generateFrom ⟨ψ, B, hB, rfl⟩)

/-- The germ σ-algebra of `B ∪ K = (ℍ ∖ C) ∪ K` is part of the conditioning σ-algebra of the marked cover argument
for `C ∖ K`. -/
theorem germSigma_compl_union_le_markedOffCoverSigma_sdiff :
    germSigma (fun ω => (H \ C ω) ∪ K ω) h ≤ markedOffCoverSigma K (fun ω => C ω \ K ω) ℋ h := by
  have e : (fun ω => (H \ C ω) ∪ K ω) = fun ω => (H \ (C ω \ K ω)) ∪ K ω :=
    funext fun ω => (compl_sdiff_union_eq (C ω) (K ω)).symm
  rw [e]
  exact germSigma_le_markedOffCoverSigma (A := K) (ℋ := ℋ) (h := h) fun ω => C ω \ K ω

/-- The exterior reveal σ-algebra of Aux. 124: the marked `K`, the field off `C`, and the germ of `B ∪ K`. -/
@[instance_reducible]
def revealSigma (K C : Ω → Set ℂ) (ℋ : MeasurableSpace Ω) (h : Ω → DistOn upperHalfPlaneOpens) :
    MeasurableSpace Ω :=
  germSigma K h ⊔ ℋ ⊔ offSigma C h ⊔ germSigma (fun ω => (H \ C ω) ∪ K ω) h

theorem le_revealSigma : germSigma K h ⊔ ℋ ≤ revealSigma K C ℋ h :=
  le_sup_left.trans le_sup_left

theorem revealSigma_le_markedOffCoverSigma
    (hCm : Measurable[MeasurableSpace.comap K hittingSigma ⊔ ℋ, hittingSigma] fun ω => H \ C ω) :
    revealSigma K C ℋ h ≤ markedOffCoverSigma K (fun ω => C ω \ K ω) ℋ h :=
  sup_le (sup_le (le_markedOffCoverSigma_germ _) (offSigma_le_markedOffCoverSigma_sdiff hCm))
    germSigma_compl_union_le_markedOffCoverSigma_sdiff

variable [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- The structural facts of `C ∖ K`, almost surely. -/
theorem ae_sdiff_isUnionComponents {A₀ : Ω → Set ℂ}
    (hC : ∀ᵐ ω ∂P, C ω ⊆ H \ A₀ ω ∧ ∀ z ∈ C ω, connectedComponentIn (H \ A₀ ω) z ⊆ C ω)
    (hA₀K : ∀ᵐ ω ∂P, A₀ ω ⊆ K ω) :
    ∀ᵐ ω ∂P, C ω \ K ω ⊆ H \ K ω ∧ ∀ z ∈ C ω \ K ω, connectedComponentIn (H \ K ω) z ⊆ C ω \ K ω := by
  filter_upwards [hC, hA₀K] with ω ⟨hCs, hCc⟩ hA
  exact sdiff_isUnionComponents hCs hCc hA

/-- **Aux. lemma 124: the interior kernel survives the exterior reveal.** Let `K` (the marked union `A ∪ R_t`) be a
local set of the zero-boundary GFF `h` with local-set mean `g`, satisfying the history-marked avoidance criterion for
the marks `ℋ`; let `C` be a union of components of `ℍ ∖ A₀` for a set `A₀ ⊆ K` (the initial marked set), with
`ℍ ∖ C` measurable from `σ(K) ∨ ℋ`. Then for every `𝒥` with `𝒜_K ∨ ℋ ≤ 𝒥 ≤ markedOffCoverSigma K (C ∖ K) ℋ h` (e.g.
`revealSigma K C ℋ h`, which retains `h|_{ℍ∖C}` and the germ of `B ∪ K`) and every test function `φ`, almost surely
on `{supp φ ⊆ C ∖ K}`, `E[e^{i(h, φ)} | 𝒥] = e^{i(g, φ)} e^{−σ²_{C∖K}(φ)/2}`. -/
theorem ae_condExp_exp_exteriorReveal (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hK : Measurable[mΩ, hittingSigma] K) (hℋ : ℋ ≤ mΩ) (hloc : IsLocalSet K h P)
    (hmark : IsHistoryAvoidanceLocal ℋ K h P) {A₀ : Ω → Set ℂ}
    (hCm : Measurable[MeasurableSpace.comap K hittingSigma ⊔ ℋ, hittingSigma] fun ω => H \ C ω)
    (hC : ∀ᵐ ω ∂P, C ω ⊆ H \ A₀ ω ∧ ∀ z ∈ C ω, connectedComponentIn (H \ A₀ ω) z ⊆ C ω)
    (hA₀K : ∀ᵐ ω ∂P, A₀ ω ⊆ K ω) {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean K h P g)
    (h𝒥 : germSigma K h ⊔ ℋ ≤ 𝒥) (h𝒥𝒦 : 𝒥 ≤ markedOffCoverSigma K (fun ω => C ω \ K ω) ℋ h)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, tsupport φ ⊆ C ω \ K ω →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒥] ω =
        Complex.exp (Complex.I * (g ω φ : ℂ)) *
          ((Real.exp (-(1 / 2) * zeroGFFTestCov (C ω \ K ω) φ φ) : ℝ) : ℂ) :=
  ae_condExp_exp_eq_of_le_markedOffCover hh hK hℋ hloc hmark
    (measurable_compl_sdiff hCm ((comap_measurable K).mono le_sup_left le_rfl))
    (ae_sdiff_isUnionComponents hC hA₀K) hg h𝒥 h𝒥𝒦 φ

/-- **Aux. lemma 124, comparison form**: revealing the field off `C` and the germ of `B ∪ K` does not change the
conditional characteristic function on `C ∖ K` given the marked `K`. -/
theorem ae_condExp_exp_exteriorReveal_eq (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hK : Measurable[mΩ, hittingSigma] K) (hℋ : ℋ ≤ mΩ) (hloc : IsLocalSet K h P)
    (hmark : IsHistoryAvoidanceLocal ℋ K h P) {A₀ : Ω → Set ℂ}
    (hCm : Measurable[MeasurableSpace.comap K hittingSigma ⊔ ℋ, hittingSigma] fun ω => H \ C ω)
    (hC : ∀ᵐ ω ∂P, C ω ⊆ H \ A₀ ω ∧ ∀ z ∈ C ω, connectedComponentIn (H \ A₀ ω) z ⊆ C ω)
    (hA₀K : ∀ᵐ ω ∂P, A₀ ω ⊆ K ω) {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean K h P g)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, tsupport φ ⊆ C ω \ K ω →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | revealSigma K C ℋ h] ω =
        P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | germSigma K h ⊔ ℋ] ω := by
  have h1 := ae_condExp_exp_exteriorReveal hh hK hℋ hloc hmark hCm hC hA₀K hg
    le_revealSigma (revealSigma_le_markedOffCoverSigma hCm) φ
  have h2 := ae_condExp_exp_exteriorReveal hh hK hℋ hloc hmark hCm hC hA₀K hg le_rfl
    (le_markedOffCoverSigma_germ _) φ
  filter_upwards [h1, h2] with ω h1 h2 hs
  rw [h1 hs, h2 hs]

/-- **Aux. lemma 124 on one component of `C ∖ K`**: almost surely, for a test function supported in the component of
`ℍ ∖ K` of a point of `C ∖ K`, the conditional characteristic function given `𝒥` is
`e^{i(g, φ)} e^{−σ²(φ)/2}` with the zero-boundary variance of that component. -/
theorem ae_condExp_exp_exteriorReveal_component (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hK : Measurable[mΩ, hittingSigma] K) (hℋ : ℋ ≤ mΩ) (hloc : IsLocalSet K h P)
    (hmark : IsHistoryAvoidanceLocal ℋ K h P) {A₀ : Ω → Set ℂ}
    (hCm : Measurable[MeasurableSpace.comap K hittingSigma ⊔ ℋ, hittingSigma] fun ω => H \ C ω)
    (hC : ∀ᵐ ω ∂P, C ω ⊆ H \ A₀ ω ∧ ∀ z ∈ C ω, connectedComponentIn (H \ A₀ ω) z ⊆ C ω)
    (hA₀K : ∀ᵐ ω ∂P, A₀ ω ⊆ K ω) {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean K h P g)
    (h𝒥 : germSigma K h ⊔ ℋ ≤ 𝒥) (h𝒥𝒦 : 𝒥 ≤ markedOffCoverSigma K (fun ω => C ω \ K ω) ℋ h)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ∀ z₀ ∈ C ω \ K ω, tsupport φ ⊆ connectedComponentIn (H \ K ω) z₀ →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒥] ω =
        Complex.exp (Complex.I * (g ω φ : ℂ)) *
          ((Real.exp (-(1 / 2) * zeroGFFTestCov (connectedComponentIn (H \ K ω) z₀) φ φ) : ℝ) : ℂ) := by
  filter_upwards [ae_condExp_exp_exteriorReveal hh hK hℋ hloc hmark hCm hC hA₀K hg h𝒥 h𝒥𝒦 φ,
    ae_sdiff_isUnionComponents hC hA₀K, hloc.2.1] with ω hω ⟨hs, hc⟩ ⟨_, ho⟩ z₀ hz₀ hφ
  have hzC := hc z₀ hz₀
  rw [hω (hφ.trans hzC)]
  have hCo : IsOpen (C ω \ K ω) := isOpen_of_forall_connectedComponentIn_subset ho hs hc
  have hcc : connectedComponentIn (H \ K ω) z₀ = connectedComponentIn (C ω \ K ω) z₀ := by
    refine subset_antisymm ?_ (connectedComponentIn_mono z₀ hs)
    exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn (hs hz₀)) hzC
  have hKo : IsOpen (connectedComponentIn (C ω \ K ω) z₀) := hCo.connectedComponentIn
  have hrest : IsOpen ((C ω \ K ω) \ connectedComponentIn (C ω \ K ω) z₀) :=
    isOpen_diff_of_forall_connectedComponentIn_subset hCo fun z hz => by
      rw [connectedComponentIn_eq hz]
  rw [hcc, zeroGFFTestCov_eq_of_isClopen hCo (hs.trans sdiff_subset) hKo (connectedComponentIn_subset _ _) hrest
    φ (hcc ▸ hφ)]

/-- **Aux. lemma 124, forgetting form** ("an already established all-stop boundary-word formula in the active
component of `C ∖ R_t` is preserved by the additional exterior reveal"): for any `𝒥 ≤ markedOffCoverSigma K (C ∖ K) ℋ h`
(e.g. the exterior information together with a stopped history), a `𝒥`-event `G` and `𝒥`-measurable `m, v` such that
almost surely on `G` the test function `φ` is supported in `C ∖ K` with `(𝒞_K, φ) = m` and `σ²_{C∖K}(φ) = v`: almost
surely on `G`, `E[e^{i(h, φ)} | 𝒥] = e^{i m} e^{−v/2}`. -/
theorem ae_condExp_exp_exteriorReveal_forget (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hK : Measurable[mΩ, hittingSigma] K) (hℋ : ℋ ≤ mΩ) (hloc : IsLocalSet K h P)
    (hmark : IsHistoryAvoidanceLocal ℋ K h P) {A₀ : Ω → Set ℂ}
    (hCm : Measurable[MeasurableSpace.comap K hittingSigma ⊔ ℋ, hittingSigma] fun ω => H \ C ω)
    (hC : ∀ᵐ ω ∂P, C ω ⊆ H \ A₀ ω ∧ ∀ z ∈ C ω, connectedComponentIn (H \ A₀ ω) z ⊆ C ω)
    (hA₀K : ∀ᵐ ω ∂P, A₀ ω ⊆ K ω) {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean K h P g)
    (h𝒥𝒦 : 𝒥 ≤ markedOffCoverSigma K (fun ω => C ω \ K ω) ℋ h) (φ : TestOn upperHalfPlaneOpens)
    {G : Set Ω} (hG : MeasurableSet[𝒥] G) {m v : Ω → ℝ} (hm : Measurable[𝒥] m) (hv : Measurable[𝒥] v)
    (hGC : ∀ᵐ ω ∂P, ω ∈ G → tsupport φ ⊆ C ω \ K ω ∧ g ω φ = m ω ∧ zeroGFFTestCov (C ω \ K ω) φ φ = v ω) :
    ∀ᵐ ω ∂P, ω ∈ G →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒥] ω =
        Complex.exp (Complex.I * (m ω : ℂ)) * ((Real.exp (-(1 / 2) * v ω) : ℝ) : ℂ) :=
  ae_condExp_exp_eq_of_le_markedOffCover_forget hh hK hℋ hloc hmark
    (measurable_compl_sdiff hCm ((comap_measurable K).mono le_sup_left le_rfl))
    (ae_sdiff_isUnionComponents hC hA₀K) hg h𝒥𝒦 φ hG hm hv hGC

/-- **Aux. lemma 124, forgetting form for the conditional mean**: under the hypotheses of
`ae_condExp_exp_exteriorReveal_forget`, with only the mean identified (`(𝒞_K, φ) = m` on `G`), almost surely on `G`,
`E[(h, φ) | 𝒥] = m`. -/
theorem ae_condExp_apply_exteriorReveal_forget (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hK : Measurable[mΩ, hittingSigma] K) (hℋ : ℋ ≤ mΩ) (hloc : IsLocalSet K h P)
    (hmark : IsHistoryAvoidanceLocal ℋ K h P) {A₀ : Ω → Set ℂ}
    (hCm : Measurable[MeasurableSpace.comap K hittingSigma ⊔ ℋ, hittingSigma] fun ω => H \ C ω)
    (hC : ∀ᵐ ω ∂P, C ω ⊆ H \ A₀ ω ∧ ∀ z ∈ C ω, connectedComponentIn (H \ A₀ ω) z ⊆ C ω)
    (hA₀K : ∀ᵐ ω ∂P, A₀ ω ⊆ K ω) {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean K h P g)
    (h𝒥𝒦 : 𝒥 ≤ markedOffCoverSigma K (fun ω => C ω \ K ω) ℋ h) (φ : TestOn upperHalfPlaneOpens)
    {G : Set Ω} (hG : MeasurableSet[𝒥] G) {m : Ω → ℝ} (hm : Measurable[𝒥] m)
    (hGC : ∀ᵐ ω ∂P, ω ∈ G → tsupport φ ⊆ C ω \ K ω ∧ g ω φ = m ω) :
    ∀ᵐ ω ∂P, ω ∈ G → P[fun ω => h ω φ | 𝒥] ω = m ω :=
  ae_condExp_apply_eq_of_le_markedOffCover_forget hh hK hℋ hloc hmark
    (measurable_compl_sdiff hCm ((comap_measurable K).mono le_sup_left le_rfl))
    (ae_sdiff_isUnionComponents hC hA₀K) hg h𝒥𝒦 φ hG hm hGC

end Reveal

end Aux124
end Sec7
end InteractingSLE
