/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Prop61Mean
import InteractingSLE.GFF.LocalSets.Prop39
import InteractingSLE.GFF.LocalSets.UnionLaw
import InteractingSLE.WangWu.Prop420Ext

/-!
# The all-contacts boundary comparison (Astra's post-contact note, §4.1 and §5), for abstract local sets

Packet PROVE-POSTCONTACT (ruling R77). Source: `source/external/AstraIG1/ig1_postcontact_finite_word.txt`, §4.1
(L218–L245) and §5 (L292–L312). This file proves the probabilistic part of the note's "new use" of its geometric
lemma: "the all-contacts boundary comparison followed by forgetting the auxiliary information" (L431–L432), in the
language of local sets of a zero-boundary GFF on `ℍ`, from the landed Propositions 3.7 (`isLocalSet_union`),
3.8 (`IsLocalSetMean.ae_tendsto_sub_of_union`) and 3.9 (`IsLocalSetMean.ae_eq_on_of_union`).

Notation (the note's): `A = α([0, t])` the flow prefix, `Aα` the complete available flow segment (`A ⊆ Aα`), `B = β`
the complete left boundary of the counterflow, `K` the stopped filled counterflow hull, `D` the component incident to
the current tip, `Eα` the exterior-left component of `ℍ ∖ Aα`.

* **The freeze (§5, L292–L297 and L306–L311)** (`ae_eq_on_union_swap`): if `D` lies in a union `C₁` of components of
  `ℍ ∖ (A ∪ K)` avoiding `B` and in a union `C₂` of components of `ℍ ∖ (A ∪ B)` avoiding `K` (each measurable from its
  own union), then the local-set means of `A ∪ K` and of `A ∪ B` agree on `D` ("Replacing `K` by the full `β` gives the
  same component", L203). Both are the mean of `A ∪ K ∪ B` there (Proposition 3.9, twice).
* **The old outer side (§4.1, L224–L236)** (`ae_tendsto_sub_old_side`): at every point `z₀` near which the complete
  segment adds nothing to `A ∪ B` (the future tail `α([t, a])` is at positive distance, "by simplicity"), and near which
  `D` lies in `Eα`, the harmonic mean of `A ∪ B` is asymptotic to the single-flow mean of `Aα` along `D` — including at
  every old mutual kiss and at their accumulation points, with no enumeration of contacts. Proposition 3.8 for the
  nested unions `A ∪ B ⊂ Aα ∪ B`, and Proposition 3.9 (`B` avoids `Eα`): `𝒞_{Aα ∪ B} = 𝒞_{Aα}` on `Eα` (4.1).
* **The far sides** (`ae_tendsto_sub_far`): at points of `B ∪ ℝ` away from `A` (the open `β`-suffix) the mean of
  `A ∪ B` is asymptotic to that of `B`, and at points of `A ∪ ℝ` away from `B` (the terminal slit, the original
  boundary) to that of `A` (Proposition 3.8).
* **Assembly** (`ae_germs_postContact`): the three germ statements for the actual mean of `A ∪ K` along `D`.

The geometric facts (`D ⊆ C₁ ∩ C₂`, the disjointness of `C₁` from `B` and of `C₂` from `K`, `D` locally inside `Eα`,
local inclusions) are hypotheses: they are the deterministic content of the note's Lemma 3.1 and are supplied per
sample by the geometry.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open QuantumZipper (H)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF CondIndepEv)

universe u

namespace InteractingSLE.Sec5.PostContact

open LocalSets

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

omit mΩ [IsProbabilityMeasure P] in
/-- Two random sets written as the same union up to reassociation and commutation. -/
theorem union_swap_eq (A K B : Ω → Set ℂ) :
    (fun ω => (A ω ∪ B ω) ∪ K ω) = fun ω => (A ω ∪ K ω) ∪ B ω := by
  funext ω
  ext z
  simp only [mem_union]
  tauto

/-- **The freeze (§5)**: the local-set means of `A ∪ K` and of `A ∪ B` agree on `D`, when `D` lies in a union `C₁`
of components of `ℍ ∖ (A ∪ K)` (measurable from `A ∪ K`) avoiding `B`, and in a union `C₂` of components of
`ℍ ∖ (A ∪ B)` (measurable from `A ∪ B`) avoiding `K`. Both agree with the mean of `A ∪ K ∪ B` there
(Proposition 3.9 twice; the union is a local set by Proposition 3.7). -/
theorem ae_eq_on_union_swap (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {A K B : Ω → Set ℂ}
    (hAm : Measurable[mΩ, hittingSigma] A) (hKm : Measurable[mΩ, hittingSigma] K)
    (hBm : Measurable[mΩ, hittingSigma] B)
    (hAK : IsLocalSet (fun ω => A ω ∪ K ω) h P) (hAB : IsLocalSet (fun ω => A ω ∪ B ω) h P)
    (hK : IsLocalSet K h P) (hB : IsLocalSet B h P)
    (hci₁ : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap (fun ω => A ω ∪ K ω) hittingSigma) (MeasurableSpace.comap B hittingSigma) P)
    (hci₂ : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap (fun ω => A ω ∪ B ω) hittingSigma) (MeasurableSpace.comap K hittingSigma) P)
    {C₁ C₂ D : Ω → Set ℂ}
    (hC₁m : Measurable[MeasurableSpace.comap (fun ω => A ω ∪ K ω) hittingSigma, hittingSigma]
      fun ω => H \ C₁ ω)
    (hC₁ : ∀ᵐ ω ∂P, C₁ ω ⊆ H \ (A ω ∪ K ω) ∧
      ∀ z ∈ C₁ ω, connectedComponentIn (H \ (A ω ∪ K ω)) z ⊆ C₁ ω)
    (hC₁B : ∀ᵐ ω ∂P, Disjoint (C₁ ω) (B ω))
    (hC₂m : Measurable[MeasurableSpace.comap (fun ω => A ω ∪ B ω) hittingSigma, hittingSigma]
      fun ω => H \ C₂ ω)
    (hC₂ : ∀ᵐ ω ∂P, C₂ ω ⊆ H \ (A ω ∪ B ω) ∧
      ∀ z ∈ C₂ ω, connectedComponentIn (H \ (A ω ∪ B ω)) z ⊆ C₂ ω)
    (hC₂K : ∀ᵐ ω ∂P, Disjoint (C₂ ω) (K ω))
    (hD : ∀ᵐ ω ∂P, D ω ⊆ C₁ ω ∩ C₂ ω)
    {gAK gAB : Ω → DistOn upperHalfPlaneOpens}
    (hgAK : IsLocalSetMean (fun ω => A ω ∪ K ω) h P gAK)
    (hgAB : IsLocalSetMean (fun ω => A ω ∪ B ω) h P gAB) :
    ∀ᵐ ω ∂P, ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ D ω → gAK ω φ = gAB ω φ := by
  have hAKm : Measurable[mΩ, hittingSigma] fun ω => A ω ∪ K ω := measurable_union_hitting hAm hKm
  have hABm : Measurable[mΩ, hittingSigma] fun ω => A ω ∪ B ω := measurable_union_hitting hAm hBm
  -- the triple union is a local set (Proposition 3.7) and has a mean
  have hS : IsLocalSet (fun ω => (A ω ∪ K ω) ∪ B ω) h P :=
    IsLocalSet.isLocalSet_union hh hAKm hBm hci₁ hAK hB
  have hSm : Measurable[mΩ, hittingSigma] fun ω => (A ω ∪ K ω) ∪ B ω :=
    measurable_union_hitting hAKm hBm
  obtain ⟨gS, hgS⟩ := IsLocalSet.exists_isLocalSetMean hh hSm hS
  -- Proposition 3.9 for `A₁ = A ∪ K`, `A₂ = B`, `C = C₁`
  have h1 := IsLocalSetMean.ae_eq_on_of_union hh hAKm hBm hci₁ hAK hB hC₁m hC₁ hC₁B hgS hgAK
  -- Proposition 3.9 for `A₁ = A ∪ B`, `A₂ = K`, `C = C₂`, with the same triple union
  have hgS' : IsLocalSetMean (fun ω => (A ω ∪ B ω) ∪ K ω) h P gS := by
    rw [union_swap_eq A K B]; exact hgS
  have h2 := IsLocalSetMean.ae_eq_on_of_union hh hABm hKm hci₂ hAB hK hC₂m hC₂ hC₂K hgS' hgAB
  filter_upwards [h1, h2, hD] with ω h1ω h2ω hDω φ hφ
  rw [← h1ω φ (hφ.trans fun z hz => (hDω hz).1), h2ω φ (hφ.trans fun z hz => (hDω hz).2)]

/-- **The old outer side (§4.1)**: Proposition 3.8 for the nested unions `A ∪ B ⊂ Aα ∪ B` and Proposition 3.9 for
`B` avoiding the exterior-left component `Eα` of the complete segment. Almost surely, for harmonic representatives
`vAB` of `𝒞_{A ∪ B}` on `ℍ ∖ (A ∪ B)` and `vα` of `𝒞_{Aα}` on `ℍ ∖ Aα`, at every `z₀ ∈ (A ∪ B) ∪ ℝ` near which
`Aα ⊆ A ∪ B`
(the future tail is away) the difference `vAB − vα` tends to `0` along `Eα ∖ (A ∪ B)`. -/
theorem ae_tendsto_sub_old_side (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {A Aα B : Ω → Set ℂ}
    (hsub : ∀ ω, A ω ⊆ Aα ω)
    (hAm : Measurable[mΩ, hittingSigma] A) (hAαm : Measurable[mΩ, hittingSigma] Aα)
    (hBm : Measurable[mΩ, hittingSigma] B)
    (hAα : IsLocalSet Aα h P) (hAB : IsLocalSet (fun ω => A ω ∪ B ω) h P) (hB : IsLocalSet B h P)
    (hci₃ : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap Aα hittingSigma) (MeasurableSpace.comap (fun ω => A ω ∪ B ω) hittingSigma) P)
    (hci₄ : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap Aα hittingSigma) (MeasurableSpace.comap B hittingSigma) P)
    (hunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A ω ∪ B ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A ω ∪ B ω)) z))
    {Eα : Ω → Set ℂ}
    (hEm : Measurable[MeasurableSpace.comap Aα hittingSigma, hittingSigma] fun ω => H \ Eα ω)
    (hE : ∀ᵐ ω ∂P, Eα ω ⊆ H \ Aα ω ∧ ∀ z ∈ Eα ω, connectedComponentIn (H \ Aα ω) z ⊆ Eα ω)
    (hEB : ∀ᵐ ω ∂P, Disjoint (Eα ω) (B ω))
    {gAB gα : Ω → DistOn upperHalfPlaneOpens}
    (hgAB : IsLocalSetMean (fun ω => A ω ∪ B ω) h P gAB) (hgα : IsLocalSetMean Aα h P gα) :
    ∀ᵐ ω ∂P, ∀ vAB vα : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd vAB (H \ (A ω ∪ B ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A ω ∪ B ω) → gAB ω φ = ∫ z, vAB z * φ z) →
      InnerProductSpace.HarmonicOnNhd vα (H \ Aα ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ Aα ω → gα ω φ = ∫ z, vα z * φ z) →
      ∀ z₀ ∈ (A ω ∪ B ω) ∪ {z : ℂ | z.im = 0}, (∃ r > 0, Aα ω ∩ ball z₀ r ⊆ A ω ∪ B ω) →
        Tendsto (fun z => vAB z - vα z) (𝓝[Eα ω \ (A ω ∪ B ω)] z₀) (𝓝 0) := by
  have hABm : Measurable[mΩ, hittingSigma] fun ω => A ω ∪ B ω := measurable_union_hitting hAm hBm
  -- the union `Aα ∪ (A ∪ B) = Aα ∪ B` is a local set with a mean
  have heq : (fun ω => Aα ω ∪ (A ω ∪ B ω)) = fun ω => Aα ω ∪ B ω := by
    funext ω
    ext z
    simp only [mem_union]
    constructor
    · rintro (h | (h | h))
      · exact Or.inl h
      · exact Or.inl (hsub ω h)
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
  have hS : IsLocalSet (fun ω => Aα ω ∪ B ω) h P := IsLocalSet.isLocalSet_union hh hAαm hBm hci₄ hAα hB
  obtain ⟨gS, hgS⟩ := IsLocalSet.exists_isLocalSetMean hh (measurable_union_hitting hAαm hBm) hS
  have hgS' : IsLocalSetMean (fun ω => Aα ω ∪ (A ω ∪ B ω)) h P gS := by rw [heq]; exact hgS
  -- Proposition 3.8: `𝒞_{Aα ∪ (A ∪ B)} − 𝒞_{A ∪ B}` is harmonic, with zero germs where `Aα ⊆ A ∪ B`
  have h38 := IsLocalSetMean.ae_tendsto_sub_of_union hh hAαm hABm hci₃ hAα hAB hunb hgS' hgAB
  -- Proposition 3.9: `𝒞_{Aα ∪ B} = 𝒞_{Aα}` on `Eα`
  have h39 := IsLocalSetMean.ae_eq_on_of_union hh hAαm hBm hci₄ hAα hB hEm hE hEB hgS hgα
  filter_upwards [h38, h39, hE, hAα.2.1, hAB.2.1] with ω ⟨u, hu, hurep, hulim⟩ h39ω ⟨hEsub, hEcomp⟩
    ⟨_, hAαo⟩ ⟨_, hABo⟩ vAB vα hvAB hvABrep hvα hvαrep z₀ hz₀ hloc
  -- the open set `O = Eα ∖ (A ∪ B)`
  have hEo : IsOpen (Eα ω) := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    exact Filter.mem_of_superset ((hAαo.connectedComponentIn).mem_nhds
      (mem_connectedComponentIn (hEsub hz))) (hEcomp z hz)
  have hO : IsOpen (Eα ω \ (A ω ∪ B ω)) := by
    have : Eα ω \ (A ω ∪ B ω) = Eα ω ∩ (H \ (A ω ∪ B ω)) := by
      ext z
      constructor
      · rintro ⟨hz, hzn⟩; exact ⟨hz, (hEsub hz).1, hzn⟩
      · rintro ⟨hz, -, hzn⟩; exact ⟨hz, hzn⟩
    rw [this]
    exact hEo.inter hABo
  have hOsub : Eα ω \ (A ω ∪ B ω) ⊆ H \ (Aα ω ∪ (A ω ∪ B ω)) := by
    rintro z ⟨hz, hzn⟩
    refine ⟨(hEsub hz).1, ?_⟩
    rintro (h' | h')
    · exact (hEsub hz).2 h'
    · exact hzn h'
  have hOH : Eα ω \ (A ω ∪ B ω) ⊆ H := fun z hz => (hOsub hz).1
  have hOAB : Eα ω \ (A ω ∪ B ω) ⊆ H \ (A ω ∪ B ω) := fun z hz => ⟨hOH hz, hz.2⟩
  have hOα : Eα ω \ (A ω ∪ B ω) ⊆ H \ Aα ω := fun z hz => hEsub hz.1
  -- on `O`: `vAB + u = vα`
  have hcont : ∀ {f : ℂ → ℝ} {V : Set ℂ}, InnerProductSpace.HarmonicOnNhd f V → ContinuousOn f V :=
    fun hf z hz => (hf z hz).1.continuousAt.continuousWithinAt
  have hEq : EqOn (fun z => vAB z + u z) vα (Eα ω \ (A ω ∪ B ω)) := by
    refine Sec6.eqOn_of_integral_mul_eq hO hOH (fun z hz => (hvAB z (hOAB hz)).add (hu z (hOsub hz)))
      (fun z hz => hvα z (hOα hz)) fun φ hφ => ?_
    have hi1 : Integrable (fun z => vAB z * φ z) :=
      LocalSets.integrable_mul_test hO ((hcont hvAB).mono hOAB) φ hφ
    have hi2 : Integrable (fun z => u z * φ z) :=
      LocalSets.integrable_mul_test hO ((hcont hu).mono hOsub) φ hφ
    have e1 : ∫ z, (vAB z + u z) * φ z = (∫ z, vAB z * φ z) + ∫ z, u z * φ z := by
      rw [← integral_add hi1 hi2]
      congr 1
      funext z
      ring
    rw [e1, ← hvABrep φ (hφ.trans hOAB), ← hurep φ (hφ.trans hOsub), ← hvαrep φ (hφ.trans hOα),
      ← h39ω φ (hφ.trans fun z hz => hz.1)]
    ring
  have hlim := (hulim z₀ hz₀ hloc).mono_left (nhdsWithin_mono z₀ hOsub)
  have hneg : Tendsto (fun z => -u z) (𝓝[Eα ω \ (A ω ∪ B ω)] z₀) (𝓝 0) := by
    simpa using hlim.neg
  refine hneg.congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
  have := hEq hz
  simp only at this
  linarith


/-- **Proposition 3.8 for harmonic representatives.** For conditionally independent local sets `A₁, A₂` (every
component of `A₂ ∪ {Im ≤ 0}` unbounded) and harmonic representatives `v` of `𝒞_{A₁ ∪ A₂}` on `ℍ ∖ (A₁ ∪ A₂)` and `v₂` of
`𝒞_{A₂}` on `ℍ ∖ A₂`, almost surely `v − v₂ → 0` at every `z₀ ∈ A₂ ∪ ℝ` near which `A₁ ⊆ A₂`. -/
theorem ae_tendsto_sub_rep (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {A₁ A₂ : Ω → Set ℂ}
    (hA₁m : Measurable[mΩ, hittingSigma] A₁) (hA₂m : Measurable[mΩ, hittingSigma] A₂)
    (hci : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap A₁ hittingSigma) (MeasurableSpace.comap A₂ hittingSigma) P)
    (h₁ : IsLocalSet A₁ h P) (h₂ : IsLocalSet A₂ h P)
    (hunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₂ ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₂ ω)) z))
    {g g₂ : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => A₁ ω ∪ A₂ ω) h P g) (hg₂ : IsLocalSetMean A₂ h P g₂) :
    ∀ᵐ ω ∂P, ∀ v v₂ : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ (A₁ ω ∪ A₂ ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A₁ ω ∪ A₂ ω) → g ω φ = ∫ z, v z * φ z) →
      InnerProductSpace.HarmonicOnNhd v₂ (H \ A₂ ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₂ ω → g₂ ω φ = ∫ z, v₂ z * φ z) →
      ∀ z₀ ∈ A₂ ω ∪ {z : ℂ | z.im = 0}, (∃ r > 0, A₁ ω ∩ ball z₀ r ⊆ A₂ ω) →
        Tendsto (fun z => v z - v₂ z) (𝓝[H \ (A₁ ω ∪ A₂ ω)] z₀) (𝓝 0) := by
  have h38 := IsLocalSetMean.ae_tendsto_sub_of_union hh hA₁m hA₂m hci h₁ h₂ hunb hg hg₂
  filter_upwards [h38, IsLocalSet.ae_relClosed_union h₁ h₂] with ω ⟨u, hu, hurep, hulim⟩ ⟨_, ho⟩
    v v₂ hv hvrep hv₂ hv₂rep z₀ hz₀ hloc
  have hcont : ∀ {f : ℂ → ℝ} {V : Set ℂ}, InnerProductSpace.HarmonicOnNhd f V → ContinuousOn f V :=
    fun hf z hz => (hf z hz).1.continuousAt.continuousWithinAt
  have hsub₂ : H \ (A₁ ω ∪ A₂ ω) ⊆ H \ A₂ ω := fun z hz => ⟨hz.1, fun h' => hz.2 (Or.inr h')⟩
  have hEq : EqOn (fun z => v z - v₂ z) u (H \ (A₁ ω ∪ A₂ ω)) := by
    refine Sec6.eqOn_of_integral_mul_eq ho sdiff_subset
      (fun z hz => (hv z hz).sub (hv₂ z (hsub₂ hz))) hu fun φ hφ => ?_
    have hi1 : Integrable (fun z => v z * φ z) := LocalSets.integrable_mul_test ho (hcont hv) φ hφ
    have hi2 : Integrable (fun z => v₂ z * φ z) :=
      LocalSets.integrable_mul_test ho ((hcont hv₂).mono hsub₂) φ hφ
    have e1 : ∫ z, (v z - v₂ z) * φ z = (∫ z, v z * φ z) - ∫ z, v₂ z * φ z := by
      rw [← integral_sub hi1 hi2]
      congr 1
      funext z
      ring
    rw [e1, ← hvrep φ hφ, ← hv₂rep φ (hφ.trans hsub₂), ← hurep φ hφ]
  exact (hulim z₀ hz₀ hloc).congr' (eventually_nhdsWithin_of_forall fun z hz => (hEq hz).symm)

/-- **The germs of the post-contact mean along the incident component** (§4.1 with the freeze of §5). Almost surely,
for harmonic representatives `vAK` of `𝒞_{A ∪ K}` (the actual stopped record's union), `vα` of `𝒞_{Aα}` (the complete
segment), `vB` of `𝒞_B` (the complete left boundary of the counterflow) and `vA` of `𝒞_A` (the flow prefix):

* (old outer side, including every old kiss) at `z₀ ∈ (A ∪ B) ∪ ℝ` near which `Aα ⊆ A ∪ B` and `D ⊆ Eα`:
  `vAK − vα → 0` along `D`;
* (open `β`-suffix) at `z₀ ∈ B ∪ ℝ` near which `A ⊆ B`: `vAK − vB → 0` along `D`;
* (terminal slit, original boundary) at `z₀ ∈ A ∪ ℝ` near which `B ⊆ A`: `vAK − vA → 0` along `D`. -/
theorem ae_germs_postContact (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {A Aα K B : Ω → Set ℂ}
    (hsub : ∀ ω, A ω ⊆ Aα ω)
    (hAm : Measurable[mΩ, hittingSigma] A) (hAαm : Measurable[mΩ, hittingSigma] Aα)
    (hKm : Measurable[mΩ, hittingSigma] K) (hBm : Measurable[mΩ, hittingSigma] B)
    (hA : IsLocalSet A h P) (hAα : IsLocalSet Aα h P) (hK : IsLocalSet K h P) (hB : IsLocalSet B h P)
    (hAK : IsLocalSet (fun ω => A ω ∪ K ω) h P) (hAB : IsLocalSet (fun ω => A ω ∪ B ω) h P)
    (hci₁ : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap (fun ω => A ω ∪ K ω) hittingSigma) (MeasurableSpace.comap B hittingSigma) P)
    (hci₂ : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap (fun ω => A ω ∪ B ω) hittingSigma) (MeasurableSpace.comap K hittingSigma) P)
    (hci₃ : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap Aα hittingSigma) (MeasurableSpace.comap (fun ω => A ω ∪ B ω) hittingSigma) P)
    (hci₄ : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap Aα hittingSigma) (MeasurableSpace.comap B hittingSigma) P)
    (hci₅ : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap A hittingSigma) (MeasurableSpace.comap B hittingSigma) P)
    (hci₆ : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap B hittingSigma) (MeasurableSpace.comap A hittingSigma) P)
    (hunbAB : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A ω ∪ B ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A ω ∪ B ω)) z))
    (hunbA : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A ω)) z))
    (hunbB : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (B ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (B ω)) z))
    {C₁ C₂ D Eα : Ω → Set ℂ}
    (hC₁m : Measurable[MeasurableSpace.comap (fun ω => A ω ∪ K ω) hittingSigma, hittingSigma]
      fun ω => H \ C₁ ω)
    (hC₁ : ∀ᵐ ω ∂P, C₁ ω ⊆ H \ (A ω ∪ K ω) ∧
      ∀ z ∈ C₁ ω, connectedComponentIn (H \ (A ω ∪ K ω)) z ⊆ C₁ ω)
    (hC₁B : ∀ᵐ ω ∂P, Disjoint (C₁ ω) (B ω))
    (hC₂m : Measurable[MeasurableSpace.comap (fun ω => A ω ∪ B ω) hittingSigma, hittingSigma]
      fun ω => H \ C₂ ω)
    (hC₂ : ∀ᵐ ω ∂P, C₂ ω ⊆ H \ (A ω ∪ B ω) ∧
      ∀ z ∈ C₂ ω, connectedComponentIn (H \ (A ω ∪ B ω)) z ⊆ C₂ ω)
    (hC₂K : ∀ᵐ ω ∂P, Disjoint (C₂ ω) (K ω))
    (hD : ∀ᵐ ω ∂P, IsOpen (D ω) ∧ D ω ⊆ C₁ ω ∩ C₂ ω)
    (hEm : Measurable[MeasurableSpace.comap Aα hittingSigma, hittingSigma] fun ω => H \ Eα ω)
    (hE : ∀ᵐ ω ∂P, Eα ω ⊆ H \ Aα ω ∧ ∀ z ∈ Eα ω, connectedComponentIn (H \ Aα ω) z ⊆ Eα ω)
    (hEB : ∀ᵐ ω ∂P, Disjoint (Eα ω) (B ω))
    {gAK gAB gα gB gA : Ω → DistOn upperHalfPlaneOpens}
    (hgAK : IsLocalSetMean (fun ω => A ω ∪ K ω) h P gAK)
    (hgAB : IsLocalSetMean (fun ω => A ω ∪ B ω) h P gAB)
    (hgα : IsLocalSetMean Aα h P gα) (hgB : IsLocalSetMean B h P gB) (hgA : IsLocalSetMean A h P gA) :
    ∀ᵐ ω ∂P, ∀ vAK vα vB vA : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd vAK (H \ (A ω ∪ K ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A ω ∪ K ω) → gAK ω φ = ∫ z, vAK z * φ z) →
      InnerProductSpace.HarmonicOnNhd vα (H \ Aα ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ Aα ω → gα ω φ = ∫ z, vα z * φ z) →
      InnerProductSpace.HarmonicOnNhd vB (H \ B ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ B ω → gB ω φ = ∫ z, vB z * φ z) →
      InnerProductSpace.HarmonicOnNhd vA (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → gA ω φ = ∫ z, vA z * φ z) →
      (∀ z₀ ∈ (A ω ∪ B ω) ∪ {z : ℂ | z.im = 0}, (∃ r > 0, Aα ω ∩ ball z₀ r ⊆ A ω ∪ B ω) →
        (∃ r > 0, D ω ∩ ball z₀ r ⊆ Eα ω) → Tendsto (fun z => vAK z - vα z) (𝓝[D ω] z₀) (𝓝 0)) ∧
      (∀ z₀ ∈ B ω ∪ {z : ℂ | z.im = 0}, (∃ r > 0, A ω ∩ ball z₀ r ⊆ B ω) →
        Tendsto (fun z => vAK z - vB z) (𝓝[D ω] z₀) (𝓝 0)) ∧
      (∀ z₀ ∈ A ω ∪ {z : ℂ | z.im = 0}, (∃ r > 0, B ω ∩ ball z₀ r ⊆ A ω) →
        Tendsto (fun z => vAK z - vA z) (𝓝[D ω] z₀) (𝓝 0)) := by
  have hfreeze := ae_eq_on_union_swap hh hAm hKm hBm hAK hAB hK hB hci₁ hci₂ hC₁m hC₁ hC₁B hC₂m hC₂ hC₂K
    (hD.mono fun _ h' => h'.2) hgAK hgAB
  have hold := ae_tendsto_sub_old_side hh hsub hAm hAαm hBm hAα hAB hB hci₃ hci₄ hunbAB hEm hE hEB hgAB hgα
  have hfarB := ae_tendsto_sub_rep hh hAm hBm hci₅ hA hB hunbB hgAB hgB
  have hBA : (fun ω => B ω ∪ A ω) = fun ω => A ω ∪ B ω := by funext ω; exact union_comm _ _
  have hgBA : IsLocalSetMean (fun ω => B ω ∪ A ω) h P gAB := by rw [hBA]; exact hgAB
  have hfarA := ae_tendsto_sub_rep hh hBm hAm hci₆ hB hA hunbA hgBA hgA
  filter_upwards [hfreeze, hold, hfarB, hfarA, hD, hC₁, hC₂, hgAB.2.1] with ω hfrω holdω hfarBω hfarAω
    ⟨hDo, hDC⟩ ⟨hC₁s, _⟩ ⟨hC₂s, _⟩ ⟨vAB, hvAB, hvABrep⟩ vAK vα vB vA hvAK hvAKrep hvα hvαrep hvB hvBrep
    hvA hvArep
  have hDAK : D ω ⊆ H \ (A ω ∪ K ω) := fun z hz => hC₁s (hDC hz).1
  have hDAB : D ω ⊆ H \ (A ω ∪ B ω) := fun z hz => hC₂s (hDC hz).2
  have hcont : ∀ {f : ℂ → ℝ} {V : Set ℂ}, InnerProductSpace.HarmonicOnNhd f V → ContinuousOn f V :=
    fun hf z hz => (hf z hz).1.continuousAt.continuousWithinAt
  -- the two harmonic representatives agree on `D`
  have hAKAB : EqOn vAK vAB (D ω) := by
    refine Sec6.eqOn_of_integral_mul_eq hDo (fun z hz => (hDAK hz).1) (fun z hz => hvAK z (hDAK hz))
      (fun z hz => hvAB z (hDAB hz)) fun φ hφ => ?_
    rw [← hvAKrep φ (hφ.trans hDAK), ← hvABrep φ (hφ.trans hDAB), hfrω φ hφ]
  have hcongr : ∀ (w : ℂ → ℝ) (z₀ : ℂ), Tendsto (fun z => vAB z - w z) (𝓝[D ω] z₀) (𝓝 0) →
      Tendsto (fun z => vAK z - w z) (𝓝[D ω] z₀) (𝓝 0) := fun w z₀ hlim =>
    hlim.congr' (eventually_nhdsWithin_of_forall fun z hz => by simp only [hAKAB hz])
  refine ⟨fun z₀ hz₀ hloc ⟨r, hr, hDr⟩ => hcongr vα z₀ ?_, fun z₀ hz₀ hloc => hcongr vB z₀ ?_,
    fun z₀ hz₀ hloc => hcongr vA z₀ ?_⟩
  · -- `𝓝[D] z₀ ≤ 𝓝[Eα ∖ (A ∪ B)] z₀`, since `D ∩ ball z₀ r ⊆ Eα ∖ (A ∪ B)`
    have hle : 𝓝[D ω] z₀ ≤ 𝓝[Eα ω \ (A ω ∪ B ω)] z₀ := by
      rw [← nhdsWithin_inter_of_mem (inter_mem_nhdsWithin (D ω) (ball_mem_nhds z₀ hr))]
      refine nhdsWithin_mono z₀ fun z hz => ?_
      exact ⟨hDr hz.1, (hDAB hz.1.1).2⟩
    exact (holdω vAB vα hvAB hvABrep hvα hvαrep z₀ hz₀ hloc).mono_left hle
  · have hle : 𝓝[D ω] z₀ ≤ 𝓝[H \ (A ω ∪ B ω)] z₀ := nhdsWithin_mono z₀ hDAB
    exact (hfarBω vAB vB hvAB hvABrep hvB hvBrep z₀ hz₀ hloc).mono_left hle
  · have hle : 𝓝[D ω] z₀ ≤ 𝓝[H \ (B ω ∪ A ω)] z₀ := nhdsWithin_mono z₀ fun z hz => by
      rw [union_comm]; exact hDAB hz
    have hvAB' : InnerProductSpace.HarmonicOnNhd vAB (H \ (B ω ∪ A ω)) := by rw [union_comm]; exact hvAB
    have hvABrep' : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (B ω ∪ A ω) →
        gAB ω φ = ∫ z, vAB z * φ z := by rw [union_comm]; exact hvABrep
    exact (hfarAω vAB vA hvAB' hvABrep' hvA hvArep z₀ hz₀ hloc).mono_left hle


/-! ### The freeze through the left sides -/

/-- The left side of `S` lies in `ℍ ∖ S` and is a union of components of `ℍ ∖ S`. -/
theorem leftSideOf_subset_and_comp (S : Set ℂ) :
    leftSideOf S ⊆ H \ S ∧ ∀ z ∈ leftSideOf S, connectedComponentIn (H \ S) z ⊆ leftSideOf S := by
  refine ⟨fun z hz => hz.1, fun z hz z' hz' => ?_⟩
  obtain ⟨_, x, hx, hxS, hxcl⟩ := hz
  refine ⟨connectedComponentIn_subset _ _ hz', x, hx, hxS, ?_⟩
  rw [← connectedComponentIn_eq hz']
  exact hxcl

omit mΩ in
/-- The complement of the left side of the relative closure is measurable from the set. -/
theorem measurable_compl_leftSideOf_comap (S : Ω → Set ℂ) :
    Measurable[MeasurableSpace.comap S hittingSigma, hittingSigma]
      fun ω => H \ leftSideOf (relClosureH (S ω)) :=
  WangWu.measurable_compl_leftSideOf_relClosureH.comp (comap_measurable S)

/-- **The germs of the post-contact mean along the incident component, with the left sides as the frozen
domains.** `ae_germs_postContact` with `C₁ = leftSideOf (A ∪ K)` and `C₂ = leftSideOf (A ∪ B)` (the components
of `ℍ ∖ (A ∪ K)`, resp. `ℍ ∖ (A ∪ B)`, reaching the negative real axis — §5's "union of all components … lying in
`Eβ`", measurable from the union alone). The remaining geometric hypotheses are intrinsic: `B` avoids the left side
of `A ∪ K`, `K` avoids the left side of `A ∪ B`, and `D` lies in both left sides. -/
theorem ae_germs_postContact_leftSide (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {A Aα K B : Ω → Set ℂ} (hsub : ∀ ω, A ω ⊆ Aα ω)
    (hAm : Measurable[mΩ, hittingSigma] A) (hAαm : Measurable[mΩ, hittingSigma] Aα)
    (hKm : Measurable[mΩ, hittingSigma] K) (hBm : Measurable[mΩ, hittingSigma] B)
    (hA : IsLocalSet A h P) (hAα : IsLocalSet Aα h P) (hK : IsLocalSet K h P) (hB : IsLocalSet B h P)
    (hAK : IsLocalSet (fun ω => A ω ∪ K ω) h P) (hAB : IsLocalSet (fun ω => A ω ∪ B ω) h P)
    (hci₁ : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap (fun ω => A ω ∪ K ω) hittingSigma) (MeasurableSpace.comap B hittingSigma) P)
    (hci₂ : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap (fun ω => A ω ∪ B ω) hittingSigma) (MeasurableSpace.comap K hittingSigma) P)
    (hci₃ : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap Aα hittingSigma) (MeasurableSpace.comap (fun ω => A ω ∪ B ω) hittingSigma) P)
    (hci₄ : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap Aα hittingSigma) (MeasurableSpace.comap B hittingSigma) P)
    (hci₅ : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap A hittingSigma) (MeasurableSpace.comap B hittingSigma) P)
    (hci₆ : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap B hittingSigma) (MeasurableSpace.comap A hittingSigma) P)
    (hunbAB : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A ω ∪ B ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A ω ∪ B ω)) z))
    (hunbA : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A ω)) z))
    (hunbB : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (B ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (B ω)) z))
    (hLB : ∀ᵐ ω ∂P, Disjoint (leftSideOf (A ω ∪ K ω)) (B ω))
    (hLK : ∀ᵐ ω ∂P, Disjoint (leftSideOf (A ω ∪ B ω)) (K ω))
    {D Eα : Ω → Set ℂ}
    (hD : ∀ᵐ ω ∂P, IsOpen (D ω) ∧ D ω ⊆ leftSideOf (A ω ∪ K ω) ∩ leftSideOf (A ω ∪ B ω))
    (hEm : Measurable[MeasurableSpace.comap Aα hittingSigma, hittingSigma] fun ω => H \ Eα ω)
    (hE : ∀ᵐ ω ∂P, Eα ω ⊆ H \ Aα ω ∧ ∀ z ∈ Eα ω, connectedComponentIn (H \ Aα ω) z ⊆ Eα ω)
    (hEB : ∀ᵐ ω ∂P, Disjoint (Eα ω) (B ω))
    {gAK gAB gα gB gA : Ω → DistOn upperHalfPlaneOpens}
    (hgAK : IsLocalSetMean (fun ω => A ω ∪ K ω) h P gAK)
    (hgAB : IsLocalSetMean (fun ω => A ω ∪ B ω) h P gAB)
    (hgα : IsLocalSetMean Aα h P gα) (hgB : IsLocalSetMean B h P gB) (hgA : IsLocalSetMean A h P gA) :
    ∀ᵐ ω ∂P, ∀ vAK vα vB vA : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd vAK (H \ (A ω ∪ K ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A ω ∪ K ω) → gAK ω φ = ∫ z, vAK z * φ z) →
      InnerProductSpace.HarmonicOnNhd vα (H \ Aα ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ Aα ω → gα ω φ = ∫ z, vα z * φ z) →
      InnerProductSpace.HarmonicOnNhd vB (H \ B ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ B ω → gB ω φ = ∫ z, vB z * φ z) →
      InnerProductSpace.HarmonicOnNhd vA (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → gA ω φ = ∫ z, vA z * φ z) →
      (∀ z₀ ∈ (A ω ∪ B ω) ∪ {z : ℂ | z.im = 0}, (∃ r > 0, Aα ω ∩ ball z₀ r ⊆ A ω ∪ B ω) →
        (∃ r > 0, D ω ∩ ball z₀ r ⊆ Eα ω) → Tendsto (fun z => vAK z - vα z) (𝓝[D ω] z₀) (𝓝 0)) ∧
      (∀ z₀ ∈ B ω ∪ {z : ℂ | z.im = 0}, (∃ r > 0, A ω ∩ ball z₀ r ⊆ B ω) →
        Tendsto (fun z => vAK z - vB z) (𝓝[D ω] z₀) (𝓝 0)) ∧
      (∀ z₀ ∈ A ω ∪ {z : ℂ | z.im = 0}, (∃ r > 0, B ω ∩ ball z₀ r ⊆ A ω) →
        Tendsto (fun z => vAK z - vA z) (𝓝[D ω] z₀) (𝓝 0)) := by
  -- on the almost sure event of relatively closed unions, the relative closures are the unions themselves
  have hrel : ∀ᵐ ω ∂P, relClosureH (A ω ∪ K ω) = A ω ∪ K ω ∧ relClosureH (A ω ∪ B ω) = A ω ∪ B ω := by
    filter_upwards [hAK.2.1, hAB.2.1] with ω ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨relClosureH_eq h1 h2, relClosureH_eq h3 h4⟩
  refine ae_germs_postContact hh hsub hAm hAαm hKm hBm hA hAα hK hB hAK hAB hci₁ hci₂ hci₃ hci₄ hci₅ hci₆
    hunbAB hunbA hunbB (C₁ := fun ω => leftSideOf (relClosureH (A ω ∪ K ω)))
    (C₂ := fun ω => leftSideOf (relClosureH (A ω ∪ B ω)))
    (measurable_compl_leftSideOf_comap (fun ω => A ω ∪ K ω)) ?_ ?_
    (measurable_compl_leftSideOf_comap (fun ω => A ω ∪ B ω)) ?_ ?_ ?_ hEm hE hEB hgAK hgAB hgα hgB hgA
  · filter_upwards [hrel] with ω ⟨e, _⟩
    simp only [e]
    exact leftSideOf_subset_and_comp _
  · filter_upwards [hrel, hLB] with ω ⟨e, _⟩ hω
    simp only [e]
    exact hω
  · filter_upwards [hrel] with ω ⟨_, e⟩
    simp only [e]
    exact leftSideOf_subset_and_comp _
  · filter_upwards [hrel, hLK] with ω ⟨_, e⟩ hω
    simp only [e]
    exact hω
  · filter_upwards [hrel, hD] with ω ⟨e₁, e₂⟩ hω
    simp only [e₁, e₂]
    exact hω


/-! ### Conditional independence for field-determined sets -/

section CondIndep

/-- **A σ-algebra almost surely inside the conditioning one is conditionally independent of every σ-algebra**: if every
event of `A` agrees almost surely with an event of `G`, then `A ⟂ B | G`. (For the boundary comparison: the flow
prefix, the complete segment and `β` are functions of the field, so they are conditionally independent given the field
of every set on the glued space.) -/
theorem condIndepEv_of_ae_measurableSet_left {Ω' : Type*} {G A B : MeasurableSpace Ω'} [mΩ' : MeasurableSpace Ω']
    {Q : Measure Ω'} [IsFiniteMeasure Q] (hG : G ≤ mΩ') (hB : B ≤ mΩ')
    (hA : ∀ a, MeasurableSet[A] a → ∃ a', MeasurableSet[G] a' ∧ a =ᵐ[Q] a') : CondIndepEv G A B Q := by
  intro a b ha hb
  obtain ⟨a', ha', haa'⟩ := hA a ha
  have hbm : MeasurableSet b := hB _ hb
  have hint : Integrable (b.indicator fun _ => (1 : ℝ)) Q := (integrable_const (1 : ℝ)).indicator hbm
  have e1 : Q[(a ∩ b).indicator fun _ => (1 : ℝ) | G] =ᵐ[Q] Q[(a' ∩ b).indicator fun _ => (1 : ℝ) | G] :=
    condExp_congr_ae (indicator_ae_eq_of_ae_eq_set (haa'.inter EventuallyEq.rfl))
  have e2 : ((a' ∩ b).indicator fun _ => (1 : ℝ)) = a'.indicator (b.indicator fun _ => (1 : ℝ)) :=
    (indicator_indicator a' b _).symm
  have e3 : Q[a'.indicator (b.indicator fun _ => (1 : ℝ)) | G] =ᵐ[Q]
      a'.indicator (Q[b.indicator fun _ => (1 : ℝ) | G]) := condExp_indicator hint ha'
  have e4 : Q[a.indicator fun _ => (1 : ℝ) | G] =ᵐ[Q] a'.indicator fun _ => (1 : ℝ) := by
    refine (condExp_congr_ae (indicator_ae_eq_of_ae_eq_set haa')).trans ?_
    rw [condExp_of_stronglyMeasurable hG
      (@StronglyMeasurable.indicator Ω' ℝ (fun _ => (1 : ℝ)) G _ _ stronglyMeasurable_const _ ha')
      ((integrable_const (1 : ℝ)).indicator (hG _ ha'))]
  filter_upwards [e1, e3, e4] with ω h1 h3 h4
  rw [h1, e2, h3, Pi.mul_apply, h4]
  by_cases hω : ω ∈ a'
  · simp [hω]
  · simp [hω]

/-- The symmetric form: a σ-algebra almost surely inside the conditioning one, on the right. -/
theorem condIndepEv_of_ae_measurableSet_right {Ω' : Type*} {G A B : MeasurableSpace Ω'} [mΩ' : MeasurableSpace Ω']
    {Q : Measure Ω'} [IsFiniteMeasure Q] (hG : G ≤ mΩ') (hA : A ≤ mΩ')
    (hB : ∀ b, MeasurableSet[B] b → ∃ b', MeasurableSet[G] b' ∧ b =ᵐ[Q] b') : CondIndepEv G A B Q := by
  intro a b ha hb
  have h := condIndepEv_of_ae_measurableSet_left (A := B) (B := A) hG hA hB b a hb ha
  rw [inter_comm] at h
  filter_upwards [h] with ω hω
  rw [hω, Pi.mul_apply, Pi.mul_apply, mul_comm]

/-- **Field-determined random sets**: if `A = F ∘ h` almost surely for a hitting-measurable `F`, every event of
`σ(A)` agrees almost surely with an event of `σ(h)`. -/
theorem ae_measurableSet_comap_of_ae_eq_comp {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'} {E : Type*}
    [MeasurableSpace E] {X : Ω' → E} {A : Ω' → Set ℂ}
    {F : E → Set ℂ} (hF : Measurable[_, hittingSigma] F) (hAF : ∀ᵐ ω ∂Q, A ω = F (X ω)) :
    ∀ a, MeasurableSet[MeasurableSpace.comap A hittingSigma] a →
      ∃ a', MeasurableSet[MeasurableSpace.comap X inferInstance] a' ∧ a =ᵐ[Q] a' := by
  rintro a ⟨S, hS, rfl⟩
  refine ⟨X ⁻¹' (F ⁻¹' S), ⟨F ⁻¹' S, hF hS, rfl⟩, ?_⟩
  filter_upwards [hAF] with ω hω
  simp only [mem_preimage, hω]

end CondIndep

end InteractingSLE.Sec5.PostContact
