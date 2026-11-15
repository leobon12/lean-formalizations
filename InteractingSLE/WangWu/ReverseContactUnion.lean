/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactRev
import InteractingSLE.GFF.LocalSets.Prop38
import InteractingSLE.Spec.Sec6.Prop61Mean

/-!
# The union boundary lemma on the glued space

Packet PROVE-WW-B12. Wang–Wu (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), proof of
Proposition 4.18 (text dump L1609–1612): "the independent-union lemma makes the two stopped slits a local set. The union
boundary lemma identifies its harmonic mean on every exposed open arc."

On the glued space `P ⊗ k(h)`, let `A(p.1)` be a local set read from the first coordinate and `G(p.2)` one read from
the second (both local for the same zero-boundary field `T(h p.1)`). They are conditionally independent given the field
(`condIndepEv_glue_fst`), so Proposition 3.8 (`LocalSets.IsLocalSetMean.ae_tendsto_sub_of_union`) applies twice, with
either slit as the comparison set.

* **`ae_union_boundary_glue`**: almost surely the union mean has one harmonic representative `w` on
  `ℍ \ (A ∪ G)` with `w − w_A → 0` at every point of `A ∪ ℝ` near which `G ⊆ A`, and `w − w_G → 0` at every point of
  `G ∪ ℝ` near which `A ⊆ G`, for any harmonic representatives `w_A`, `w_G` of the two slit means (each comparison set
  must have only unbounded components in `S ∪ {Im ≤ 0}`, the hypothesis of Proposition 3.8).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu

open QuantumZipper (H)
open LQGMetric (DistOn TestOn CondIndepEv)
open LocalSets (IsLocalSetMean lowerUnion)

universe u

section Glue

variable {Ω : Type u} {β : Type} {mΩ : MeasurableSpace Ω} [mβ : MeasurableSpace β] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
  (k : Kernel (DistOn upperHalfPlaneOpens) β) [IsMarkovKernel k]

include hh in
/-- **The two coordinates of the glued space are conditionally independent given a field read through an invertible
measurable map**, in the form of Proposition 3.8. -/
theorem condIndepEv_glue_sets {T : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hT : Measurable T)
    {T' : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hT' : Measurable T') (hTT : ∀ f, T' (T f) = f)
    {A : Ω → Set ℂ} (hAm : Measurable[mΩ, hittingSigma] A) {G : β → Set ℂ} (hG : Measurable[mβ, hittingSigma] G) :
    CondIndepEv (MeasurableSpace.comap (fun p : Ω × β => T (h p.1)) inferInstance)
      (MeasurableSpace.comap (fun p : Ω × β => A p.1) hittingSigma)
      (MeasurableSpace.comap (fun p : Ω × β => G p.2) hittingSigma) (glueMeasure P k h hh) := by
  have hci := condIndepEv_glue_fst (μ := P) k hh
  have hσ : MeasurableSpace.comap (fun p : Ω × β => T (h p.1)) inferInstance =
      MeasurableSpace.comap (fun p : Ω × β => h p.1) inferInstance := by
    refine le_antisymm ?_ ?_
    · change MeasurableSpace.comap (T ∘ fun p : Ω × β => h p.1) _ ≤ _
      rw [← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono hT.comap_le
    · calc MeasurableSpace.comap (fun p : Ω × β => h p.1) inferInstance
          = MeasurableSpace.comap (T' ∘ fun p : Ω × β => T (h p.1)) inferInstance := by
            congr 1; funext p; exact (hTT _).symm
        _ ≤ _ := by
            rw [← MeasurableSpace.comap_comp]
            exact MeasurableSpace.comap_mono hT'.comap_le
  rw [hσ]
  intro a b ha hb
  refine hci a b ?_ ?_
  · obtain ⟨s, hs, rfl⟩ := ha
    exact ⟨A ⁻¹' s, hAm hs, rfl⟩
  · obtain ⟨s, hs, rfl⟩ := hb
    exact ⟨G ⁻¹' s, hG hs, rfl⟩

include hh in
/-- **The union boundary lemma on the glued space** (Proposition 3.8 with either slit as comparison set). -/
theorem ae_union_boundary_glue {T : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hT : Measurable T)
    {T' : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hT' : Measurable T') (hTT : ∀ f, T' (T f) = f)
    (hF : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun ω => T (h ω)) P) {A : Ω → Set ℂ}
    (hAm : Measurable[mΩ, hittingSigma] A) {G : β → Set ℂ} (hG : Measurable[mβ, hittingSigma] G)
    (hA : IsLocalSet (fun p : Ω × β => A p.1) (fun p => T (h p.1)) (glueMeasure P k h hh))
    (hGl : IsLocalSet (fun p : Ω × β => G p.2) (fun p => T (h p.1)) (glueMeasure P k h hh))
    (hunbA : ∀ᵐ p ∂(glueMeasure P k h hh), ∀ z ∈ lowerUnion (A p.1),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A p.1)) z))
    (hunbG : ∀ᵐ p ∂(glueMeasure P k h hh), ∀ z ∈ lowerUnion (G p.2),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (G p.2)) z))
    {g gA gG : Ω × β → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun p : Ω × β => A p.1 ∪ G p.2) (fun p => T (h p.1)) (glueMeasure P k h hh) g)
    (hgA : IsLocalSetMean (fun p : Ω × β => A p.1) (fun p => T (h p.1)) (glueMeasure P k h hh) gA)
    (hgG : IsLocalSetMean (fun p : Ω × β => G p.2) (fun p => T (h p.1)) (glueMeasure P k h hh) gG) :
    ∀ᵐ p ∂(glueMeasure P k h hh), ∀ wA wG : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd wA (H \ A p.1) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A p.1 → gA p φ = ∫ z, wA z * φ z) →
      InnerProductSpace.HarmonicOnNhd wG (H \ G p.2) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ G p.2 → gG p φ = ∫ z, wG z * φ z) →
      ∃ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ (A p.1 ∪ G p.2)) ∧
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A p.1 ∪ G p.2) → g p φ = ∫ z, w z * φ z) ∧
        (∀ z₀ ∈ A p.1 ∪ {z : ℂ | z.im = 0}, (∃ r > 0, G p.2 ∩ ball z₀ r ⊆ A p.1) →
          Tendsto (fun z => w z - wA z) (𝓝[H \ (A p.1 ∪ G p.2)] z₀) (𝓝 0)) ∧
        (∀ z₀ ∈ G p.2 ∪ {z : ℂ | z.im = 0}, (∃ r > 0, A p.1 ∩ ball z₀ r ⊆ G p.2) →
          Tendsto (fun z => w z - wG z) (𝓝[H \ (A p.1 ∪ G p.2)] z₀) (𝓝 0)) := by
  have hF' : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun p : Ω × β => T (h p.1))
      (glueMeasure P k h hh) :=
    isZeroBoundaryGFF_comp_of_map_eq (g := fun ω => T (h ω)) (f := Prod.fst) measurable_fst
      (glueMeasure_fst (μ := P) k hh) hF
  have hAm' : Measurable[_, hittingSigma] fun p : Ω × β => A p.1 := hAm.comp measurable_fst
  have hGm' : Measurable[_, hittingSigma] fun p : Ω × β => G p.2 := hG.comp measurable_snd
  have hci := condIndepEv_glue_sets (P := P) hh k hT hT' hTT hAm hG
  -- comparison with the second slit
  have h1 := LocalSets.IsLocalSetMean.ae_tendsto_sub_of_union hF' hAm' hGm' hci hA hGl hunbG hg hgG
  -- comparison with the first slit
  have hg' : IsLocalSetMean (fun p : Ω × β => G p.2 ∪ A p.1) (fun p => T (h p.1)) (glueMeasure P k h hh) g := by
    have e : (fun p : Ω × β => G p.2 ∪ A p.1) = fun p => A p.1 ∪ G p.2 := funext fun p => union_comm _ _
    rw [e]; exact hg
  have h2 := LocalSets.IsLocalSetMean.ae_tendsto_sub_of_union hF' hGm' hAm' hci.symm hGl hA hunbA hg' hgA
  filter_upwards [h1, h2, hA.2.1, hGl.2.1] with p ⟨uG, huG, hrepG, hlimG⟩ ⟨uA, huA, hrepA, hlimA⟩ hAc hGc
  intro wA wG hwA hrepA' hwG hrepG'
  set O := H \ (A p.1 ∪ G p.2) with hO
  have hOo : IsOpen O := by
    have : O = (H \ A p.1) ∩ (H \ G p.2) := by
      ext z; simp only [hO, Set.mem_sdiff, mem_union, mem_inter_iff, not_or]; tauto
    rw [this]; exact hAc.2.inter hGc.2
  have hOA : O ⊆ H \ A p.1 := fun z hz => ⟨hz.1, fun h' => hz.2 (Or.inl h')⟩
  have hOG : O ⊆ H \ G p.2 := fun z hz => ⟨hz.1, fun h' => hz.2 (Or.inr h')⟩
  have hOH : O ⊆ H := fun z hz => hz.1
  have hGA : O = H \ (G p.2 ∪ A p.1) := by rw [hO, union_comm]
  have huA' : InnerProductSpace.HarmonicOnNhd uA O := by rw [hGA]; exact huA
  have hcont : ∀ {v : ℂ → ℝ} {U : Set ℂ}, InnerProductSpace.HarmonicOnNhd v U → ContinuousOn v U :=
    fun hv z hz => (hv z hz).1.continuousAt.continuousWithinAt
  -- the two candidate representatives of `g` agree on `O`
  have hsum : ∀ (u v : ℂ → ℝ) (U : Set ℂ), O ⊆ U → InnerProductSpace.HarmonicOnNhd u O →
      InnerProductSpace.HarmonicOnNhd v U → ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ O →
      ∫ z, (u z + v z) * φ z = (∫ z, u z * φ z) + ∫ z, v z * φ z := by
    intro u v U hOU hu hv φ hφ
    have i1 := LocalSets.integrable_mul_test hOo (hcont hu) φ hφ
    have i2 := LocalSets.integrable_mul_test hOo ((hcont hv).mono hOU) φ hφ
    rw [← integral_add i1 i2]
    congr 1; funext z; ring
  have heq : EqOn (fun z => uG z + wG z) (fun z => uA z + wA z) O := by
    refine Sec6.eqOn_of_integral_mul_eq hOo hOH (huG.add (fun z hz => hwG z (hOG hz)))
      (huA'.add (fun z hz => hwA z (hOA hz))) fun φ hφ => ?_
    rw [hsum uG wG _ hOG huG hwG φ hφ, hsum uA wA _ hOA huA' hwA φ hφ, ← hrepG φ hφ,
      ← hrepG' φ (hφ.trans hOG), ← hrepA φ (by rw [← hGA]; exact hφ), ← hrepA' φ (hφ.trans hOA)]
    ring
  refine ⟨fun z => uG z + wG z, huG.add (fun z hz => hwG z (hOG hz)), fun φ hφ => ?_, ?_, ?_⟩
  · rw [hsum uG wG _ hOG huG hwG φ hφ, ← hrepG φ hφ, ← hrepG' φ (hφ.trans hOG)]
    ring
  · intro z₀ hz₀ hloc
    have hl := hlimA z₀ hz₀ hloc
    rw [← hGA] at hl
    refine hl.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have := heq hz
    simp only at this
    rw [this]; ring
  · intro z₀ hz₀ hloc
    refine (hlimG z₀ hz₀ hloc).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    ring

end Glue

end InteractingSLE.WangWu
