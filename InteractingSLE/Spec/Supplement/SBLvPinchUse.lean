/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLvPinch
import InteractingSLE.Spec.Supplement.SBTail2EraseGlue

/-!
# Pinch-finiteness discharged in its consumers

Packet PROVE-T14-SBLEAVES (R87). The finite-fibre hypothesis `hgf` / `hfin` of Lemma S5's relative step
(`Erase.ErasureStep.relative`, `Erase.erasureStep_of_relative_clocks`) and of SB2(1)'s relative chain
(`FinRel.exists_relConfig_of_path`) is replaced by finite fibres of the path `p` parametrizing the retained set,
through `Lv.finite_fibre_of_isLeftEntryChart`. For a concatenation of finitely many simple pieces and real segments
this is a finite count of preimages (`Lv.finite_fibre_of_injOn_pieces`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lv

/-- **Finite fibres of a concatenation**: a path injective on each of finitely many sets covering `[0, 1]` (its simple
pieces and real segments) has finite fibres on `[0, 1]`, with at most one point per piece. -/
theorem finite_fibre_of_injOn_pieces {p : ℝ → ℂ} {n : ℕ} (I : Fin n → Set ℝ) (hcov : Icc (0 : ℝ) 1 ⊆ ⋃ i, I i)
    (hinj : ∀ i, InjOn p (I i)) (z : ℂ) : (p ⁻¹' {z} ∩ Icc 0 1).Finite := by
  have hsub : ∀ i, (p ⁻¹' {z} ∩ I i).Subsingleton := fun i a ha b hb =>
    hinj i ha.2 hb.2 (ha.1.trans hb.1.symm)
  refine (Set.finite_iUnion fun i => (hsub i).finite).subset ?_
  rintro t ⟨htz, ht⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov ht)
  exact Set.mem_iUnion.2 ⟨i, htz, hi⟩

/-- **S5's relative step without `hgf`**: the finite fibres of the boundary map come from finite fibres of the path. -/
theorem erasureStep_relative_of_finite {p : ℝ → ℂ} {β : ℝ≥0 → ℂ} {a : ℝ≥0} {c : Chart} {g : ℂ → ℂ}
    {tL a₁ : ℝ≥0} {aR bR : ℝ≥0 → ℂ} {w : ℝ}
    (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0) (hpf : ∀ z, (p ⁻¹' {z} ∩ Icc 0 1).Finite)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) (hβ0 : β 0 = 0)
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (ht : tL ≤ a) (hL : β tL = realMin (p '' Icc 0 1)) (hb0 : bR 0 = 0)
    (hrel : ∀ s : ℝ≥0, s ≤ a - tL → g (bR s) = β (tL + s))
    (hw : 0 ≤ w) (ha0 : aR 0 = w) (hord : HasOrderedProperCompletions aR a₁ bR (a - tL)) :
    Erase.ErasureStep β a (p '' Icc 0 1) (p '' Icc 0 1 ∪ g '' (aR '' Icc 0 a₁)) :=
  Erase.ErasureStep.relative hp hp0 hpH hβ0 hc hgc hgi
    (finite_fibre_of_isLeftEntryChart hp (by rw [hp0]; simp) hpf hc hgc hgi) ht hL hb0 hrel hw ha0 hord

/-- **S5's relative step with local clocks, without `hgf`.** -/
theorem erasureStep_of_relative_clocks_of_finite {p : ℝ → ℂ} {β : ℝ≥0 → ℂ} {a : ℝ≥0}
    {c : Chart} {g : ℂ → ℂ} {tL a₁ : ℝ≥0} {αR βR : ℝ≥0 → ℂ} {τ σ : ℝ≥0 → ℝ≥0} {w : ℝ}
    (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0) (hpf : ∀ z, (p ⁻¹' {z} ∩ Icc 0 1).Finite)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) (hβ0 : β 0 = 0)
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (ht : tL ≤ a) (hL : β tL = realMin (p '' Icc 0 1)) (hbR0 : βR 0 = 0)
    (hrel : ∀ s : ℝ≥0, s ≤ a - tL → g (βR (σ s)) = β (tL + s))
    (hw : 0 ≤ w) (haR0 : αR 0 = w)
    (hτc : ContinuousOn τ (Iic a₁)) (hτm : StrictMonoOn τ (Iic a₁)) (hτ0 : τ 0 = 0)
    (hσc : ContinuousOn σ (Iic (a - tL))) (hσm : StrictMonoOn σ (Iic (a - tL))) (hσ0 : σ 0 = 0)
    (hord : HasOrderedProperCompletions αR (τ a₁) βR (σ (a - tL))) :
    Erase.ErasureStep β a (p '' Icc 0 1) (p '' Icc 0 1 ∪ g '' ((αR ∘ τ) '' Icc 0 a₁)) :=
  Erase.erasureStep_of_relative_clocks hp hp0 hpH hβ0 hc hgc hgi
    (finite_fibre_of_isLeftEntryChart hp (by rw [hp0]; simp) hpf hc hgc hgi) ht hL hbR0 hrel hw haR0
    hτc hτm hτ0 hσc hσm hσ0 hord

/-- **SB2(1)'s relative chain without `hfin`** (`FinRel.exists_relConfig_of_path` with the finite fibres of `g`
supplied by pinch-finiteness). -/
theorem exists_relConfig_of_path_of_finite {p : ℝ → ℂ} {β' : ℝ≥0 → ℂ} {c : Chart} {g : ℂ → ℂ}
    (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0) (hpf : ∀ z, (p ⁻¹' {z} ∩ Icc 0 1).Finite)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) (hβ' : Supp9B.IsProperCurve β') (hβ'0 : β' 0 = 0)
    (hA : p '' Icc 0 1 ⊆ Supp9B.closedRightSide β')
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H) {S S₀ : ℝ} (hS₀ : 0 ≤ S₀) (hS₀S : S₀ < S)
    (hnA : ∀ t : ℝ≥0, β' t = realMin (p '' Icc 0 1) →
      interior {r ∈ Ioo (0 : ℝ) S | β' (t + r.toNNReal) ∈ closure (p '' Icc 0 1)} = ∅)
    (hnR : ∀ t : ℝ≥0, β' t = realMin (p '' Icc 0 1) →
      interior {r ∈ Ioo (0 : ℝ) S | β' (t + r.toNNReal) ∈ {z : ℂ | z.im = 0}} = ∅) :
    ∃ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ), β' tL = realMin (p '' Icc 0 1) ∧ β' '' Icc 0 tL ⊆ hullK (p '' Icc 0 1) ∧
      Supp9B.IsProperCurve γ ∧ γ 0 = 0 ∧ (∀ s, g (γ s) = β' (tL + s)) ∧
      ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ), FinRel.IsSB2RelChain (p '' Icc 0 1) c β' γ tL S₀ Wr ηr :=
  FinRel.exists_relConfig_of_path hp hp0 hpH hβ' hβ'0 hA hc hgc hgi
    (finite_fibre_of_isLeftEntryChart hp (by rw [hp0]; simp) hpf hc hgc hgi) hS₀ hS₀S hnA hnR

/-- **Pinch-finiteness for any domain chart of `ℍ ∖ fill A`, `A = p([0, 1])`** (e.g. SB2(2)'s right entry charts), with
properness of the boundary map at `∞` as a hypothesis. -/
theorem finite_fibre_of_isDomainChart {p : ℝ → ℂ} (hp : ContinuousOn p (Icc 0 1))
    (hpf : ∀ z, (p ⁻¹' {z} ∩ Icc 0 1).Finite) {c : Chart} (hD : IsDomainChart (H \ fillH (p '' Icc 0 1)) c)
    {g : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (hinf : Tendsto g (Bornology.cobounded ℂ ⊓ 𝓟 H) (Bornology.cobounded ℂ)) :
    ∀ z, (g ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite := by
  intro z
  have hAcpt : IsCompact (p '' Icc 0 1) := isCompact_Icc.image_of_continuousOn hp
  have hF := isBoundaryMap_of_isConformal hD.isConformal hgc hgi hinf
  have himg : g '' H = H \ fillH (p '' Icc 0 1) := by
    rw [image_congr fun w hw => hgi hw]; exact hD.image_eq
  refine finite_fibre_of_paths hF (p := fun _ : Fin 1 => p) (fun _ => hp) (fun _ => hpf) (fun _ => ?_) ?_ z
  · rw [himg]
    exact Set.disjoint_left.2 fun a ha haD => haD.2 ⟨haD.1, Or.inl (subset_closure ha)⟩
  · intro x
    rcases FinRel.g_ofReal_mem hD hgc hgi x with h | h
    · rw [hAcpt.isClosed.closure_eq] at h
      exact Or.inr ⟨0, h⟩
    · exact Or.inl h
