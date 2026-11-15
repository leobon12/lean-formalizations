import InteractingSLE.GFF.LocalSets.SubdomainLaw

/-!
# Proposition 3.9: the union mean agrees with `𝒞_{A₁}` on components avoided by `A₂`

Specification §3.2, Proposition 3.9 (p. 71; transcription `source/spec/p049-096.md#prop-3.9`):

> Suppose that `D` is a bounded, simply connected domain and that `A₁, A₂` are connected local sets
> which are conditionally independent given `h`. Suppose that `C` is a `σ(A₁)`-measurable open
> subset of `D ∖ A₁` which can be written as a union of components of `D ∖ A₁` such that
> `C ∩ A₂ = ∅` almost surely. Then `𝒞_{A₁∪A₂}|_C = 𝒞_{A₁}|_C` almost surely.

Here `D = ℍ` (local sets are defined on `ℍ`, ruling R19 (5)); a relatively closed `A ⊆ ℍ` stands for
`A ∪ ∂ℍ`. The theorem below does not use the connectedness of `A₁, A₂`. "`C` is `σ(A₁)`-measurable"
is the measurability of the random relatively closed set `ℍ ∖ C` (the element `(ℍ ∖ C) ∪ ∂ℍ` of `Γ`)
for `σ(A₁)` and the hitting σ-algebra.

## Proof (own route on `ℍ`, ruling R34)

The specification conditions on `𝒜₁` and applies Lemma 3.6 (ii) in the conditional domain `D ∖ A₁`.
Here the two conditional laws are compared on `ℍ` directly. Given `𝒥 = σ(A₁, A₂, 𝒜, 𝒜₁, 𝒜₂)` the
field is `𝒞_A + GFF_{ℍ∖A}` (Proposition 3.7, `IsLocalSet.exists_condLaw_union_germs`), and given
`𝒜₁ ⊆ 𝒥` it is `𝒞_{A₁} + GFF_{ℍ∖A₁}`. For a test function `φ` supported in `C` the two Green
variances agree, `σ²_{ℍ∖A₁}(φ) = σ²_C(φ) = σ²_{ℍ∖A}(φ)`, because `C` is a union of components of both
`ℍ ∖ A₁` and `ℍ ∖ A` (`zeroGFFTestCov_eq_of_isClopen`). The tower property then forces the two
means to agree in the pairing with `φ` on `{supp φ ⊆ C} ∈ σ(A₁)`
(`ae_apply_eq_of_isCondZeroBoundaryGFF`), and harmonicity on `C` upgrades this to all test functions
simultaneously (`ae_forall_apply_eq_of_bump`).

## Main results

* `IsLocalSetMean.ae_eq_on_of_union` : **Proposition 3.9** (`𝒞_{A₁∪A₂}|_C = 𝒞_{A₁}|_C`), for any
  versions of the two local-set means;
* `IsHarmonicDistOn.mono`, `isOpen_diff_of_forall_connectedComponentIn_subset` : helpers.
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

/-- Harmonicity of a distribution on `U` passes to open subsets. -/
theorem IsHarmonicDistOn.mono {T : DistOn upperHalfPlaneOpens} {U V : Set ℂ}
    (hT : IsHarmonicDistOn T U) (hVU : V ⊆ U) : IsHarmonicDistOn T V := by
  obtain ⟨v, hv, hTv⟩ := hT
  exact ⟨v, fun z hz => hv z (hVU hz), fun φ hφ => hTv φ (hφ.trans hVU)⟩

/-- A union of connected components of an open set `V ⊆ ℂ` is relatively clopen in `V`. -/
theorem isOpen_diff_of_forall_connectedComponentIn_subset {V C : Set ℂ} (hV : IsOpen V)
    (hCc : ∀ z ∈ C, connectedComponentIn V z ⊆ C) : IsOpen (V \ C) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  refine Filter.mem_of_superset ((hV.connectedComponentIn).mem_nhds
    (mem_connectedComponentIn hz.1)) fun w hw => ⟨connectedComponentIn_subset V z hw, fun hwC => ?_⟩
  have e : connectedComponentIn V w = connectedComponentIn V z :=
    (connectedComponentIn_eq hw).symm
  exact hz.2 (hCc w hwC (e ▸ mem_connectedComponentIn hz.1))

theorem isOpen_of_forall_connectedComponentIn_subset {V C : Set ℂ} (hV : IsOpen V) (hCV : C ⊆ V)
    (hCc : ∀ z ∈ C, connectedComponentIn V z ⊆ C) : IsOpen C := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  exact Filter.mem_of_superset ((hV.connectedComponentIn).mem_nhds
    (mem_connectedComponentIn (hCV hz))) (hCc z hz)

section Prop39

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {A₁ A₂ : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Proposition 3.9.** Let `A₁, A₂` be local sets of a zero-boundary GFF `h` on `ℍ`, conditionally
independent given `h`, and let `C` be a random open set which is a union of components of
`ℍ ∖ A₁`, with `ℍ ∖ C` a `σ(A₁)`-measurable random relatively closed set and `C ∩ A₂ = ∅` almost
surely. Then, for any versions `g` of `𝒞_{A₁ ∪ A₂}` and `g₁` of `𝒞_{A₁}`, almost surely
`g = g₁` on `C`: `g(φ) = g₁(φ)` for every test function `φ` supported in `C`. -/
theorem IsLocalSetMean.ae_eq_on_of_union (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA₁ : Measurable[mΩ, hittingSigma] A₁) (hA₂ : Measurable[mΩ, hittingSigma] A₂)
    (hci : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap A₁ hittingSigma) (MeasurableSpace.comap A₂ hittingSigma) P)
    (h₁ : IsLocalSet A₁ h P) (h₂ : IsLocalSet A₂ h P) {C : Ω → Set ℂ}
    (hCm : Measurable[MeasurableSpace.comap A₁ hittingSigma, hittingSigma] fun ω => H \ C ω)
    (hC : ∀ᵐ ω ∂P, C ω ⊆ H \ A₁ ω ∧ ∀ z ∈ C ω, connectedComponentIn (H \ A₁ ω) z ⊆ C ω)
    (hCA₂ : ∀ᵐ ω ∂P, Disjoint (C ω) (A₂ ω))
    {g g₁ : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => A₁ ω ∪ A₂ ω) h P g) (hg₁ : IsLocalSetMean A₁ h P g₁) :
    ∀ᵐ ω ∂P, ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ C ω → g ω φ = g₁ ω φ := by
  have hhm := hh.measurable
  set A : Ω → Set ℂ := fun ω => A₁ ω ∪ A₂ ω with hAdef
  have hA : Measurable[mΩ, hittingSigma] A := measurable_union_hitting hA₁ hA₂
  obtain ⟨g₀, hg₀m, -, hg₀c⟩ := IsLocalSet.exists_condLaw_union_germs hh hA₁ hA₂ hci h₁ h₂
  have h𝒥le : germSigma A h ⊔
      (MeasurableSpace.comap A₁ hittingSigma ⊔ MeasurableSpace.comap A₂ hittingSigma) ⊔
        (germSigma A₁ h ⊔ germSigma A₂ h) ≤ mΩ :=
    sup_le (sup_le (germSigma_le hA hhm) (sup_le hA₁.comap_le hA₂.comap_le))
      (sup_le (germSigma_le hA₁ hhm) (germSigma_le hA₂ hhm))
  have hA𝒥 : germSigma A h ≤ germSigma A h ⊔
      (MeasurableSpace.comap A₁ hittingSigma ⊔ MeasurableSpace.comap A₂ hittingSigma) ⊔
        (germSigma A₁ h ⊔ germSigma A₂ h) := le_sup_left.trans le_sup_left
  have hA₁𝒥 : germSigma A₁ h ≤ germSigma A h ⊔
      (MeasurableSpace.comap A₁ hittingSigma ⊔ MeasurableSpace.comap A₂ hittingSigma) ⊔
        (germSigma A₁ h ⊔ germSigma A₂ h) := le_sup_left.trans le_sup_right
  -- the structural facts about `C`, almost surely
  have hgood : ∀ᵐ ω ∂P, IsOpen (H \ A₁ ω) ∧ IsOpen (H \ A ω) ∧ C ω ⊆ H \ A₁ ω ∧
      C ω ⊆ H \ A ω ∧ IsOpen (C ω) ∧ IsOpen ((H \ A₁ ω) \ C ω) ∧ IsOpen ((H \ A ω) \ C ω) := by
    filter_upwards [h₁.2.1, IsLocalSet.ae_relClosed_union h₁ h₂, hC, hCA₂] with ω ⟨_, ho₁⟩ ⟨_, ho⟩
      ⟨hCs, hCc⟩ hd
    have hCo := isOpen_of_forall_connectedComponentIn_subset ho₁ hCs hCc
    have hd₁ := isOpen_diff_of_forall_connectedComponentIn_subset ho₁ hCc
    have hCA : C ω ⊆ H \ A ω := fun z hz =>
      ⟨(hCs hz).1, fun h' => h'.elim (hCs hz).2 (Set.disjoint_left.1 hd hz)⟩
    refine ⟨ho₁, ho, hCs, hCA, hCo, hd₁, ?_⟩
    have e : (H \ A ω) \ C ω = ((H \ A₁ ω) \ C ω) ∩ (H \ A ω) := by
      ext z
      simp only [Set.mem_sdiff, mem_inter_iff, hAdef, mem_union]
      tauto
    rw [e]
    exact hd₁.inter ho
  -- the event `{supp φ ⊆ C}`, through the `σ(A₁)`-measurable closed set `ℍ ∖ C`
  set G : TestOn upperHalfPlaneOpens → Set Ω :=
    fun φ => {ω | Disjoint (tsupport φ) (relClosureH (H \ C ω))} with hGdef
  have hGm : ∀ φ : TestOn upperHalfPlaneOpens, MeasurableSet[germSigma A₁ h] (G φ) := fun φ =>
    comap_le_germSigma A₁ h _ (hCm (measurableSet_disjoint_relClosureH φ.hasCompactSupport
      φ.tsupport_subset))
  have hGsub : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
      (ω ∈ G φ ↔ tsupport φ ⊆ C ω) := fun φ => by
    filter_upwards [hgood] with ω ⟨_, _, hCs, _, hCo, _, _⟩
    have hrc : relClosureH (H \ C ω) = H \ C ω := by
      refine relClosureH_eq sdiff_subset ?_
      have : H \ (H \ C ω) = C ω := by
        ext z; constructor
        · rintro ⟨hz, hz'⟩; by_contra hzC; exact hz' ⟨hz, hzC⟩
        · intro hz; exact ⟨(hCs hz).1, fun h' => h'.2 hz⟩
      rw [this]; exact hCo
    simp only [hGdef, mem_ofPred_eq, hrc]
    constructor
    · intro hdis z hz
      by_contra hzC
      exact Set.disjoint_left.1 hdis hz ⟨φ.tsupport_subset hz, hzC⟩
    · intro hsub
      exact Set.disjoint_left.2 fun z hz hz' => hz'.2 (hsub hz)
  -- (1) `g = g₀` in every pairing
  have hgg₀ : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, g ω φ = g₀ ω φ := fun φ => by
    have := ae_apply_eq_of_isCondZeroBoundaryGFF (P := P) hA𝒥 h𝒥le hhm hg.1
      (hg₀m.mono hA𝒥 le_rfl) hg.2.2 hg₀c φ
      MeasurableSet.univ (fun c => Eventually.of_forall fun _ _ => rfl)
    filter_upwards [this] with ω hω using hω (mem_univ ω)
  -- (2) `g₁ = g₀` in the pairing with `φ` on `{supp φ ⊆ C}`
  have hg₁g₀ : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ G φ → g₁ ω φ = g₀ ω φ := by
    intro φ
    refine ae_apply_eq_of_isCondZeroBoundaryGFF (P := P) hA₁𝒥 h𝒥le hhm hg₁.1
      (hg₀m.mono hA𝒥 le_rfl) hg₁.2.2 hg₀c φ (hGm φ) fun c => ?_
    filter_upwards [hgood, hGsub φ] with ω ⟨ho₁, ho, hCs, hCA, hCo, hd₁, hd⟩ hG hωG
    have hsupp : tsupport ⇑(c • φ) ⊆ C ω :=
      (tsupport_smul_subset_right (fun _ => c) φ).trans (hG.1 hωG)
    rw [zeroGFFTestCov_eq_of_isClopen ho₁ sdiff_subset hCo hCs hd₁ (c • φ) hsupp,
      zeroGFFTestCov_eq_of_isClopen ho sdiff_subset hCo hCA hd (c • φ) hsupp]
  -- (3) all test functions at once
  have hO : ∀ᵐ ω ∂P, IsOpen (C ω) ∧ C ω ⊆ H := by
    filter_upwards [hgood] with ω ⟨_, _, hCs, _, hCo, _, _⟩
    exact ⟨hCo, hCs.trans sdiff_subset⟩
  have hgH : ∀ᵐ ω ∂P, IsHarmonicDistOn (g ω) (C ω) := by
    filter_upwards [hg.2.1, hgood] with ω hω ⟨_, _, _, hCA, _, _, _⟩
    exact IsHarmonicDistOn.mono hω hCA
  have hg₁H : ∀ᵐ ω ∂P, IsHarmonicDistOn (g₁ ω) (C ω) := by
    filter_upwards [hg₁.2.1, hgood] with ω hω ⟨_, _, hCs, _, _, _, _⟩
    exact IsHarmonicDistOn.mono hω hCs
  refine ae_forall_apply_eq_of_bump hO hgH hg₁H fun x δ hδ hB => ?_
  set ψ := GFF.bumpTest x hδ hB
  filter_upwards [hgg₀ ψ, hg₁g₀ ψ, hGsub ψ] with ω h1 h2 h3 hsub
  rw [h1, h2 (h3.2 ((GFF.tsupport_bumpFun_subset hδ).trans hsub))]

end Prop39

end LocalSets
end InteractingSLE
