import InteractingSLE.GFF.LocalSets.HittingSigma
import InteractingSLE.GFF.Markov
import LQGMetric.Prob.CondIndepEv
import LQGMetric.Field.Measurable

/-!
# Characterizations of local sets (specification Lemma 3.6, statement layer)

Source: `source/ig1-specification.pdf`, §3.2, Lemma 3.6 (pp. 51–52; transcription
`source/spec/p049-096.md#lem-3.6`), the restatement of [SS13, Lemma 3.9]. For a coupling `(A, h)` of
a zero-boundary GFF `h` on `ℍ` with a random relatively closed set `A ⊆ ℍ` (standing for
`A ∪ ∂ℍ ∈ Γ`, ruling R19 (5)), the following are equivalent:

* (i) `IsAvoidanceLocal` : for each deterministic open `U ⊆ ℍ`, `P[A ∩ U = ∅ | h]` is a measurable
  function of the projection of `h` onto `H^⊥(U)`;
* (ii) `IsMarkedAvoidanceLocal` : for each deterministic open `U ⊆ ℍ`, given the projection onto
  `H^⊥(U)`, the pair `(S, Ã)` (`S = {A ∩ U ≠ ∅}`, `Ã = A` on `Sᶜ` and `∅` on `S`) is independent of
  the projection onto `H(U)`;
* (iii) `IsGermConditionalLaw` : conditionally on the germ σ-algebra `𝒜` of `(A, h)`, `h = h₁ + h₂`
  with `h₁` an `𝒜`-measurable random distribution, almost surely harmonic on `ℍ \ A`, and `h₂` a
  zero-boundary GFF on `ℍ \ A`;
* (iv) `IsLocalSet` (frozen, `InteractingSLE/Frozen/Spec/IsLocalSet.lean`).

The projection of `h` onto `H(U)` is a Borel map `G` with `IsMarkovDecomposition U ℍ h (G ∘ h)`
(Proposition 3.1; such `G` exist, `exists_markovMap`), and the projection onto `H^⊥(U)` is `h − G h`
(the harmonic part `h_{U^c}`). Statements (i) and (ii) quantify over all such versions `G`.

## Main results

* `IsMarkedAvoidanceLocal.isAvoidanceLocal` : (ii) ⇒ (i) ("Trivially, (ii) implies (i)", p. 52);
* `IsGermConditionalLaw.isLocalSet` : (iii) ⇒ (iv) ("Now (iv) is immediate from (iii)", p. 54).

## Conventions

The germ σ-algebra (p. 50): `A_δ` is the closed `δ`-neighbourhood of `A ∪ ∂ℍ` and `𝒜_δ` is generated
by `A` and the restriction of `h` to the interior of `A_δ`; `𝒜 = ⋂_{δ>0} 𝒜_δ`. For the unbounded `ℍ`
the specification measures distances in the spherical metric (p. 49), so neighbourhoods of `∂ℍ`
include neighbourhoods of `∞`; here `germNbhd δ S = ℍ ∩ (thickening δ ((S ∩ ℍ) ∪ ℝ) ∪ {|z| > 1/δ})`,
a cofinal family of such neighbourhoods. The restriction of `h` to a random open set `O` is
recorded by the events `{tsupport φ ⊆ O} ∩ {h(φ) ∈ B}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace Metric
open scoped ENNReal

namespace InteractingSLE
namespace LocalSets

open QuantumZipper LQGMetric

/-! ### The projection onto `H(U)` -/

/-- The projection onto `H^⊥(U)` attached to a version `G` of the projection onto `H(U)`:
`T ↦ T − G T`. -/
def markovCompl (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens)
    (T : DistOn upperHalfPlaneOpens) : DistOn upperHalfPlaneOpens :=
  T - G T

theorem measurable_markovCompl {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens}
    (hG : Measurable G) : Measurable (markovCompl G) :=
  measurable_distOn_iff.2 fun φ =>
    (measurable_distOn_apply φ).sub ((measurable_distOn_apply φ).comp hG)

/-- Proposition 3.1 supplies a Borel version of the projection onto `H(U)` for every open
`U ⊆ ℍ`, the same for every zero-boundary GFF on `ℍ`; so the statements below, which quantify over
such versions, are not vacuous. -/
theorem exists_markovMap (U : Opens ℂ) (hU : (U : Set ℂ) ⊆ H) :
    ∃ G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens, Measurable G ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
        {h : Ω → DistOn upperHalfPlaneOpens}, IsZeroBoundaryGFF upperHalfPlaneOpens h P →
          GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P :=
  GFF.exists_markovMap_upperHalfPlane hU

/-! ### Statements (i) and (ii) -/

section Statements

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **Lemma 3.6 (i).** For every deterministic open `U ⊆ ℍ` and every Borel version `G` of the
projection onto `H(U)` (Proposition 3.1), the conditional probability of `{A ∩ U = ∅}` given `h` is
a measurable function of the projection `h − G h` of `h` onto `H^⊥(U)`. -/
def IsAvoidanceLocal (A : Ω → Set ℂ) (h : Ω → DistOn upperHalfPlaneOpens) (P : Measure Ω) :
    Prop :=
  ∀ (U : Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens),
    (U : Set ℂ) ⊆ H → Measurable G →
      GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P →
      ∃ g : DistOn upperHalfPlaneOpens → ℝ, Measurable g ∧
        P⟦{ω | Disjoint (A ω) U} | MeasurableSpace.comap h inferInstance⟧ =ᵐ[P]
          fun ω => g (markovCompl G (h ω))

/-- The recorded set `Ã` of Lemma 3.6 (ii): `S` if `S` avoids `U`, and `∅` otherwise. -/
def markedSet (U S : Set ℂ) : Set ℂ := {z | Disjoint S U ∧ z ∈ S}

/-- The σ-algebra of the pair `(S, Ã)` of Lemma 3.6 (ii): the hitting event `{A ∩ U ≠ ∅}` and the
recorded set `Ã`. -/
@[instance_reducible]
def markedSigma (A : Ω → Set ℂ) (U : Set ℂ) : MeasurableSpace Ω :=
  MeasurableSpace.generateFrom {{ω | Disjoint (A ω) U}} ⊔
    MeasurableSpace.comap (fun ω => markedSet U (A ω)) hittingSigma

/-- **Lemma 3.6 (ii).** For every deterministic open `U ⊆ ℍ` and every Borel version `G` of the
projection onto `H(U)`, given the projection `h − G h` of `h` onto `H^⊥(U)`, the pair `(S, Ã)` is
conditionally independent of the projection `G h` onto `H(U)`. -/
def IsMarkedAvoidanceLocal (A : Ω → Set ℂ) (h : Ω → DistOn upperHalfPlaneOpens)
    (P : Measure Ω) : Prop :=
  ∀ (U : Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens),
    (U : Set ℂ) ⊆ H → Measurable G →
      GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P →
      CondIndepEv (MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance)
        (markedSigma A U) (MeasurableSpace.comap (fun ω => G (h ω)) inferInstance) P

/-! ### Statement (iii) -/

/-- The open neighbourhood `int A_δ` of `A ∪ ∂ℍ` (including a neighbourhood of `∞`) in `ℍ`. -/
def germNbhd (δ : ℝ) (S : Set ℂ) : Set ℂ :=
  H ∩ (thickening δ ((S ∩ H) ∪ {z : ℂ | z.im = 0}) ∪ {z : ℂ | 1 / δ < ‖z‖})

/-- `𝒜_δ`: the σ-algebra generated by `A` and the restriction of `h` to `int A_δ`. -/
@[instance_reducible]
def germSigmaAt (A : Ω → Set ℂ) (h : Ω → DistOn upperHalfPlaneOpens) (δ : ℝ) :
    MeasurableSpace Ω :=
  MeasurableSpace.comap A hittingSigma ⊔ MeasurableSpace.generateFrom
    {E | ∃ (φ : TestOn upperHalfPlaneOpens) (B : Set ℝ), MeasurableSet B ∧
      E = {ω | tsupport φ ⊆ germNbhd δ (A ω)} ∩ (fun ω => h ω φ) ⁻¹' B}

/-- The germ σ-algebra `𝒜 = ⋂_{δ > 0} 𝒜_δ` of a random set `A` and a field `h` (p. 50). -/
@[instance_reducible]
def germSigma (A : Ω → Set ℂ) (h : Ω → DistOn upperHalfPlaneOpens) : MeasurableSpace Ω :=
  ⨅ n : ℕ, germSigmaAt A h (1 / ((n : ℝ) + 1))

omit mΩ in
lemma comap_le_germSigma (A : Ω → Set ℂ) (h : Ω → DistOn upperHalfPlaneOpens) :
    MeasurableSpace.comap A hittingSigma ≤ germSigma A h :=
  le_iInf fun _ => le_sup_left

/-- Membership of a set `K ⊆ ℍ` in the germ neighbourhood, reduced to a thickening of `S ∩ ℍ`. -/
lemma subset_germNbhd_iff {K : Set ℂ} (hKH : K ⊆ H) (δ : ℝ) (S : Set ℂ) :
    K ⊆ germNbhd δ S ↔
      K ∩ (thickening δ {z : ℂ | z.im = 0} ∪ {z : ℂ | 1 / δ < ‖z‖})ᶜ ⊆ thickening δ (S ∩ H) := by
  simp only [germNbhd, thickening_union]
  constructor
  · rintro hK z ⟨hzK, hz⟩
    simp only [mem_compl_iff, mem_union, not_or] at hz
    rcases (hK hzK).2 with (h1 | h1) | h1
    · exact h1
    · exact absurd h1 hz.1
    · exact absurd h1 hz.2
  · intro hK z hzK
    refine ⟨hKH hzK, ?_⟩
    by_cases hz : z ∈ thickening δ {z : ℂ | z.im = 0} ∪ {z : ℂ | 1 / δ < ‖z‖}
    · rcases hz with hz | hz
      · exact Or.inl (Or.inr hz)
      · exact Or.inr hz
    · exact Or.inl (Or.inl (hK ⟨hzK, hz⟩))

/-- For compact `K ⊆ ℍ` and `δ > 0`, `{S | K ⊆ germNbhd δ S}` is hitting-measurable. -/
theorem measurableSet_subset_germNbhd {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) {δ : ℝ}
    (hδ : 0 < δ) : MeasurableSet[hittingSigma] {S : Set ℂ | K ⊆ germNbhd δ S} := by
  have hK0 : IsCompact (K ∩ (thickening δ {z : ℂ | z.im = 0} ∪ {z : ℂ | 1 / δ < ‖z‖})ᶜ) :=
    hK.inter_right (isOpen_thickening.union (isOpen_lt continuous_const continuous_norm)).isClosed_compl
  have : {S : Set ℂ | K ⊆ germNbhd δ S} =
      {S : Set ℂ | K ∩ (thickening δ {z : ℂ | z.im = 0} ∪ {z : ℂ | 1 / δ < ‖z‖})ᶜ ⊆
        thickening δ (S ∩ H)} := by
    ext S
    exact subset_germNbhd_iff hKH δ S
  rw [this]
  exact measurableSet_subset_thickening hK0 hδ

/-- For measurable `A` and `h`, the germ σ-algebra is a sub-σ-algebra. -/
theorem germSigma_le {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h) : germSigma A h ≤ mΩ := by
  refine (iInf_le _ 0).trans (sup_le hA.comap_le (MeasurableSpace.generateFrom_le ?_))
  rintro _ ⟨φ, B, hB, rfl⟩
  have hδ : (0 : ℝ) < 1 / ((0 : ℕ) + 1) := by norm_num
  exact (hA (measurableSet_subset_germNbhd φ.hasCompactSupport φ.tsupport_subset hδ)).inter
    ((measurable_distOn_apply φ).comp hh hB)

/-- **Lemma 3.6 (iii).** Conditionally on the germ σ-algebra `𝒜`, the field is `h₁ + h₂` with `h₁`
an `𝒜`-measurable random distribution that is almost surely harmonic on `ℍ \ A` and `h₂` a
zero-boundary GFF on `ℍ \ A` (extended by zero). -/
def IsGermConditionalLaw (A : Ω → Set ℂ) (h : Ω → DistOn upperHalfPlaneOpens) (P : Measure Ω) :
    Prop :=
  ∃ h₁ : Ω → DistOn upperHalfPlaneOpens, Measurable[germSigma A h] h₁ ∧
    (∀ᵐ ω ∂P, IsHarmonicDistOn (h₁ ω) (H \ A ω)) ∧
    IsCondZeroBoundaryGFF P (germSigma A h) (fun ω => H \ A ω) (fun ω => h ω - h₁ ω)

end Statements

/-! ### Measurability of the recorded set -/

lemma markedSet_inter_nonempty_iff (U S V : Set ℂ) :
    (markedSet U S ∩ V).Nonempty ↔ Disjoint S U ∧ (S ∩ V).Nonempty := by
  constructor
  · rintro ⟨z, ⟨hd, hz⟩, hzV⟩
    exact ⟨hd, z, hz, hzV⟩
  · rintro ⟨hd, z, hz, hzV⟩
    exact ⟨z, ⟨hd, hz⟩, hzV⟩

theorem measurable_markedSet {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ H) :
    Measurable[hittingSigma, hittingSigma] (markedSet U) := by
  refine @measurable_generateFrom (Set ℂ) (Set ℂ) hittingSigma _ (markedSet U) ?_
  rintro _ ⟨V, hV, hVH, rfl⟩
  have : markedSet U ⁻¹' {S : Set ℂ | (S ∩ V).Nonempty} =
      {S : Set ℂ | Disjoint S U} ∩ {S : Set ℂ | (S ∩ V).Nonempty} := by
    ext S
    exact markedSet_inter_nonempty_iff U S V
  rw [this]
  exact (measurableSet_avoid hU hUH).inter (measurableSet_hitting hV hVH)

theorem markedSigma_le {Ω : Type*} [mΩ : MeasurableSpace Ω] {A : Ω → Set ℂ}
    (hA : Measurable[mΩ, hittingSigma] A) {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ H) :
    markedSigma A U ≤ mΩ := by
  refine sup_le ?_ ?_
  · refine MeasurableSpace.generateFrom_le ?_
    rintro _ rfl
    exact hA (measurableSet_avoid hU hUH)
  · exact ((measurable_markedSet hU hUH).comp hA).comap_le

theorem measurableSet_avoid_markedSigma {Ω : Type*} (A : Ω → Set ℂ) (U : Set ℂ) :
    MeasurableSet[markedSigma A U] {ω | Disjoint (A ω) U} :=
  (le_sup_left : _ ≤ markedSigma A U) _ (MeasurableSpace.measurableSet_generateFrom rfl)

/-! ### (ii) ⇒ (i) -/

section Implications

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

omit mΩ in
/-- `σ(h) = σ(G h) ⊔ σ(h − G h)`. -/
theorem comap_eq_sup_markov (h : Ω → DistOn upperHalfPlaneOpens)
    {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hG : Measurable G) :
    MeasurableSpace.comap h inferInstance =
      MeasurableSpace.comap (fun ω => G (h ω)) inferInstance ⊔
        MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · have hm : Measurable[MeasurableSpace.comap (fun ω => G (h ω)) inferInstance ⊔
        MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance] h := by
      refine (@measurable_distOn_iff _ _ (MeasurableSpace.comap (fun ω => G (h ω)) inferInstance ⊔
        MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance) _).2 fun φ => ?_
      have e : (fun ω => h ω φ) = fun ω => G (h ω) φ + markovCompl G (h ω) φ := by
        funext ω
        simp [markovCompl]
      rw [e]
      exact ((measurable_distOn_apply φ).comp (Measurable.of_comap_le le_sup_left)).add
        ((measurable_distOn_apply φ).comp (Measurable.of_comap_le le_sup_right))
    exact hm.comap_le
  · exact (hG.comp (comap_measurable h)).comap_le
  · exact ((measurable_markovCompl hG).comp (comap_measurable h)).comap_le

/-- **Lemma 3.6, (ii) ⇒ (i).** -/
theorem IsMarkedAvoidanceLocal.isAvoidanceLocal [IsProbabilityMeasure P] {A : Ω → Set ℂ}
    {h : Ω → DistOn upperHalfPlaneOpens} (hA : Measurable[mΩ, hittingSigma] A)
    (hh : Measurable h) (hii : IsMarkedAvoidanceLocal A h P) : IsAvoidanceLocal A h P := by
  intro U G hUH hG hMD
  have hci := (hii U G hUH hG hMD).symm
  have hYle : MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance ≤ mΩ :=
    ((measurable_markovCompl hG).comp hh).comap_le
  have hXle : MeasurableSpace.comap (fun ω => G (h ω)) inferInstance ≤ mΩ :=
    (hG.comp hh).comap_le
  have hmk := markedSigma_le hA U.isOpen hUH
  have key := LQGMetric.condExp_sup_eq_of_condIndepEv hYle hXle hmk hci
    (measurableSet_avoid_markedSigma A U)
  rw [← comap_eq_sup_markov h hG] at key
  obtain ⟨g, hg, hgeq⟩ :=
    (stronglyMeasurable_condExp (m := MeasurableSpace.comap
      (fun ω => markovCompl G (h ω)) inferInstance) (μ := P)
      (f := {ω | Disjoint (A ω) (U : Set ℂ)}.indicator fun _ => (1 : ℝ))).exists_eq_measurable_comp
  refine ⟨g, hg.measurable, key.trans ?_⟩
  rw [hgeq]
  rfl

/-! ### (iii) ⇒ (iv) -/

omit mΩ in
theorem comap_relClosureH_comp (A : Ω → Set ℂ) :
    MeasurableSpace.comap (fun ω => relClosureH (A ω)) hittingSigma =
      MeasurableSpace.comap A hittingSigma := by
  rw [show (fun ω => relClosureH (A ω)) = relClosureH ∘ A from rfl,
    ← MeasurableSpace.comap_comp, comap_relClosureH]

/-- If the germ σ-algebra is not a sub-σ-algebra, statement (iii) fails (its conditional
expectations vanish), so (iii) forces `𝒜 ≤ 𝓕`. -/
theorem IsGermConditionalLaw.germSigma_le [IsProbabilityMeasure P] {A : Ω → Set ℂ}
    {h : Ω → DistOn upperHalfPlaneOpens} (hiii : IsGermConditionalLaw A h P) :
    germSigma A h ≤ mΩ := by
  by_contra hne
  obtain ⟨h₁, -, -, hcond⟩ := hiii
  have h0 := hcond 0
  rw [condExp_of_not_le hne] at h0
  obtain ⟨ω, hω⟩ := h0.exists
  have hpos := Real.exp_pos (-(1 / 2) * zeroGFFTestCov (H \ A ω) (0 : TestOn upperHalfPlaneOpens)
    (0 : TestOn upperHalfPlaneOpens))
  have : ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ A ω) (0 : TestOn upperHalfPlaneOpens)
      (0 : TestOn upperHalfPlaneOpens)) : ℝ) : ℂ) = 0 := hω.symm
  exact hpos.ne' (Complex.ofReal_eq_zero.1 this)

/-- **Lemma 3.6, (iii) ⇒ (iv).** The two-step model is the original space: `A` (replaced by its
relative closure, almost surely equal), `h₁ = 𝒞_A`, `h₂ = h − 𝒞_A`. -/
theorem IsGermConditionalLaw.isLocalSet {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}
    (hA : Measurable[mΩ, hittingSigma] A) (hh : Measurable h)
    (hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω)) (hiii : IsGermConditionalLaw A h P) :
    IsLocalSet A h P := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  have hle := hiii.germSigma_le
  obtain ⟨h₁, hh₁, hharm, hcond⟩ := hiii
  have hh₁m : Measurable h₁ := hh₁.mono hle le_rfl
  have hAeq : ∀ᵐ ω ∂P, relClosureH (A ω) = A ω := by
    filter_upwards [hAc] with ω hω
    exact relClosureH_eq hω.1 hω.2
  refine ⟨(hA.prodMk hh).aemeasurable, hAc, Ω, mΩ, P, inferInstance,
    fun ω => relClosureH (A ω), h₁, fun ω => h ω - h₁ ω,
    measurable_relClosureH.comp hA, hh₁m,
    measurable_distOn_iff.2 fun φ =>
      ((measurable_distOn_apply φ).comp hh).sub ((measurable_distOn_apply φ).comp hh₁m),
    fun ω => ⟨relClosureH_subset _, isOpen_H_diff_relClosureH _⟩, ?_, ?_, ?_⟩
  · filter_upwards [hharm, hAeq] with ω h1 h2
    rw [h2]
    exact h1
  · intro φ
    set 𝒢 : MeasurableSpace Ω := MeasurableSpace.comap (fun ω => relClosureH (A ω)) hittingSigma ⊔
      MeasurableSpace.comap h₁ inferInstance with h𝒢def
    have h𝒢 : 𝒢 ≤ germSigma A h := by
      refine sup_le ?_ hh₁.comap_le
      rw [comap_relClosureH_comp]
      exact comap_le_germSigma A h
    have hcov : Measurable[𝒢] fun ω =>
        zeroGFFTestCov (H \ relClosureH (A ω)) φ φ := by
      refine (measurable_comap_zeroGFFTestCov_compl A φ φ).mono ?_ le_rfl
      rw [← comap_relClosureH_comp]
      exact le_sup_left
    set c' : Ω → ℂ := fun ω =>
      ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ relClosureH (A ω)) φ φ) : ℝ) : ℂ) with hc'def
    have hc'm : StronglyMeasurable[𝒢] c' :=
      (Complex.measurable_ofReal.comp
        (Real.measurable_exp.comp (hcov.const_mul _))).stronglyMeasurable
    have hcc' : (fun ω => ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ A ω) φ φ) : ℝ) : ℂ))
        =ᵐ[P] c' := by
      filter_upwards [hAeq] with ω hω
      simp only [c', hω]
    have hc'i : Integrable c' P := (integrable_condExp.congr (hcond φ)).congr hcc'
    calc P[(fun ω => Complex.exp (Complex.I * ((h ω - h₁ ω) φ : ℂ)))|𝒢]
        =ᵐ[P] P[P[(fun ω => Complex.exp (Complex.I * ((h ω - h₁ ω) φ : ℂ)))|germSigma A h]|𝒢] :=
          (condExp_condExp_of_le h𝒢 hle).symm
      _ =ᵐ[P] P[c'|𝒢] := condExp_congr_ae ((hcond φ).trans hcc')
      _ = c' := condExp_of_stronglyMeasurable (h𝒢.trans hle) hc'm hc'i
  · refine Measure.map_congr ?_
    filter_upwards [hAeq] with ω hω
    simp [hω]

/-! ### Deterministic sets are local -/

/-- A test function on `ℍ` supported in the open `U ⊆ ℍ`, as a test function on `U`. -/
def testOnOfSubset {U : Opens ℂ} (φ : TestOn upperHalfPlaneOpens) (hφ : tsupport φ ⊆ U) :
    TestOn U :=
  ⟨φ, φ.contDiff, φ.hasCompactSupport, hφ⟩

lemma testIncl_testOnOfSubset {U : Opens ℂ} (hU : U ≤ upperHalfPlaneOpens)
    (φ : TestOn upperHalfPlaneOpens) (hφ : tsupport φ ⊆ U) :
    GFF.testIncl U upperHalfPlaneOpens (testOnOfSubset φ hφ) = φ := by
  ext x
  rw [GFF.coe_testIncl hU]
  rfl

/-- The harmonic part of a Markov decomposition on `U ⊆ ℍ` is harmonic on `U` in the sense of
`IsHarmonicDistOn`. -/
theorem ae_isHarmonicDistOn_of_isMarkovDecomposition {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {U : Opens ℂ} (hU : U ≤ upperHalfPlaneOpens)
    {h hU' : Ω → DistOn upperHalfPlaneOpens}
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h hU' P) :
    ∀ᵐ ω ∂P, IsHarmonicDistOn (h ω - hU' ω) U := by
  filter_upwards [hd.ae_harmonic] with ω ⟨g, hg, hgeq⟩
  refine ⟨g, hg, fun φ hφ => ?_⟩
  have := hgeq (testOnOfSubset φ hφ)
  rw [GFF.restrictDist_apply, testIncl_testOnOfSubset hU] at this
  exact this

/-- **Deterministic closed sets are local** (specification p. 50, "Deterministic closed sets are
local"): for a zero-boundary GFF `h` on `ℍ` and a deterministic relatively closed `C ⊆ ℍ`, the
two-step decomposition is the Markov decomposition of Proposition 3.1 for `U = ℍ \ C`. -/
theorem isLocalSet_const {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {C : Set ℂ} (hC : C ⊆ H) (hCo : IsOpen (H \ C)) : IsLocalSet (fun _ => C) h P := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  let U : Opens ℂ := ⟨H \ C, hCo⟩
  have hUH : U ≤ upperHalfPlaneOpens := fun z hz => hz.1
  obtain ⟨G, hG, hMD⟩ := exists_markovMap U (fun z hz => hz.1)
  have hd := hMD hh
  have hhm := hh.measurable
  have hsub : Measurable fun ω => h ω - G (h ω) :=
    measurable_distOn_iff.2 fun φ =>
      ((measurable_distOn_apply φ).comp hhm).sub ((measurable_distOn_apply φ).comp (hG.comp hhm))
  refine ⟨(measurable_const.prodMk hhm).aemeasurable, ae_of_all _ fun _ => ⟨hC, hCo⟩, Ω, inferInstance,
    P, inferInstance, fun _ => C, fun ω => h ω - G (h ω), fun ω => G (h ω), measurable_const,
    hsub, hG.comp hhm, fun _ => ⟨hC, hCo⟩, ae_isHarmonicDistOn_of_isMarkovDecomposition hUH hd, ?_, ?_⟩
  · intro φ
    have hbot : MeasurableSpace.comap (fun _ : Ω => C) hittingSigma ⊔
        MeasurableSpace.comap (fun ω => h ω - G (h ω)) inferInstance =
          MeasurableSpace.comap (fun ω => h ω - G (h ω)) inferInstance := by
      rw [MeasurableSpace.comap_const, bot_sup_eq]
    rw [hbot]
    exact hd.condExp_exp_zbPart hsub φ
  · congr 1
    funext ω
    simp

end Implications

end LocalSets
end InteractingSLE
