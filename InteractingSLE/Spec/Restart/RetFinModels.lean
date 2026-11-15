/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetFinBranch
import InteractingSLE.Spec.Restart.RetPlumbProofChart
import InteractingSLE.Spec.Restart.ChartMeasFlow
import InteractingSLE.Spec.Sec7.Lemma78MeanWordMeas

/-!
# Theorem 1.5's retained stopped models (leaf 1 of PROVE-T15-RET)

Packet PROVE-T15-RET3. **`RetAux79.RetStoppedModelsStatement` from Lemma 7.5**
(`retStoppedModelsStatement_of_lemma75`), and hence Lemma 7.6's retained determination
`Sec7.Lemma76DetRStatement` from Lemma 7.5, Theorem 1.3 and the stopped hull extension
(`lemma76DetRStatement_of_lemma75`).

The finite type partition: choose measurable versions of the flow lines, a retained family with good events
`G r'` (PROVE-RETPLUMB), and the explicit retained word `retWordAt` (LEMMA76G). Its force types range over a
fixed finite set (`hasBoundedForceType_wordM`). On the disjoint pairs, the given word `β` has the mean pairings of
`retWordAt` (`ae_mean_integrals_eq_retWordAt`), hence the same type (`mem_forceTypeSet_iff_of_mean_integrals`).
The parts are `(B ∩ G r) ∩ β⁻¹(type)` with `B` a retained-σ-algebra version of the pair event, disjointified
and with one measurable null set removed, so that all pathwise inputs hold at every point of every part. On each
part with positive probability `nonempty_stoppedModelTransfer_branch` gives the model.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.RetFin

open LQGMetric (DistOn TestOn)
open Supp7 Sec7 Sec7.Lemma76F RetAux79

universe v

/-- **Theorem 1.5's retained stopped models, from Lemma 7.5.** -/
theorem retStoppedModelsStatement_of_lemma75 (hL75 : Theorem15.Lemma75Statement.{v}) :
    RetStoppedModelsStatement.{v} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx _ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag u₀ hu₀ β hβ hmean
    hsort
  classical
  -- versions, the retained family and the explicit word
  obtain ⟨η₁', hm₁, ha₁⟩ := Restart.exists_measurable_version_of_isFlowLine hη₁
  obtain ⟨η₂', hm₂, ha₂⟩ := Restart.exists_measurable_version_of_isFlowLine hη₂
  obtain ⟨G, hG⟩ := exists_retG_family_with_live hκ hκ4 hη₁ hη₂ hm₁ hm₂ ha₁ ha₂ d.u
  have hdG : ∀ r', (retFam G η₁' η₂' d.u r').IsMeasGood := fun r' => (hG r').1
  have hGae : ∀ r' : ℝ≥0, ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (r' : ℝ≥0∞) < ζ₂ ω → ω ∈ G r' :=
    fun r' => (hG r').2.2.2
  obtain ⟨c₀, hc₀, hc₀J, hc₀b⟩ := Restart.BoundaryWord.exists_fn_eq_strictMonoOn hb
  obtain ⟨B, hBm, hBiff⟩ := exists_retSigma76_pairEvent hL75 hκ hκ4 hb hh hη₁ hη₂ u₀ d.u d.r
  have hW := ae_mean_integrals_eq_retWordAt (θ₁ := θ₁) hL75 hκ hκ4 hb hx hh hη₁ hη₂ hd hag hu₀ hmean hsort
    ha₁ ha₂ (hdG d.r) (hGae d.r) hc₀ hc₀J hc₀b
  -- every pathwise input, almost surely
  let Good : Ω → Prop := fun ω =>
    ((d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) ∧
    (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s) ∧
    (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s) ∧
    ((d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ G d.r) ∧
    IsPathGood (η₁ ω) (ζ₁ ω) x₁ ∧ IsPathGood (η₂ ω) (ζ₂ ω) x₂ ∧
    (Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
      (β ω).IsSorted ∧ (retWordAt G η₁' η₂' d.u κ θ₁ θ₂ c₀ d.r ω).IsSorted ∧
        ∀ φ : TestOn upperHalfPlaneOpens,
          ∫ z, (β ω).mean z * φ z = ∫ z, (retWordAt G η₁' η₂' d.u κ θ₁ θ₂ c₀ d.r ω).mean z * φ z) ∧
    (ω ∈ B ↔ Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r)
  have hGood : ∀ᵐ ω ∂P, Good ω := by
    filter_upwards [hag, ha₁, ha₂, hGae d.r,
      Restart.ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁,
      Restart.ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂, hW, hBiff]
      with ω h1 h2 h3 h4 h5 h6 h7 h8
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  set N := toMeasurable P {ω | ¬ Good ω} with hNdef
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : P N = 0 := by
    rw [hNdef, measure_toMeasurable]
    exact ae_iff.1 hGood
  have hNsub : ∀ ω, ω ∉ N → Good ω := fun ω hω => by
    by_contra hc
    exact hω (subset_toMeasurable P _ hc)
  -- the finite type partition
  let Nb := 3 * c₀.1 + 7
  let wts := flowWeightPalette κ θ₂ (retainedHeightPalette c₀
    (-sleLambda κ - θ₂ * QuantumZipper.chiC κ) (sleLambda κ - θ₂ * QuantumZipper.chiC κ)
    (-sleLambda κ - θ₁ * QuantumZipper.chiC κ) (sleLambda κ - θ₁ * QuantumZipper.chiC κ))
  let e := Fintype.equivFin (BoundedForceTypes Nb wts)
  let a : Fin (Fintype.card (BoundedForceTypes Nb wts)) → ForceWordType :=
    fun i => boundedForceType Nb wts (e.symm i)
  let S : Fin (Fintype.card (BoundedForceTypes Nb wts)) → Set Ω :=
    fun i => (B ∩ G d.r) ∩ β ⁻¹' forceTypeSet κ θ₂ (a i)
  have hSm : ∀ i, MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] (S i) := fun i =>
    (hBm.inter (hG d.r).2.2.1).inter (hβ (measurableSet_forceTypeSet κ θ₂ (a i)))
  obtain ⟨M', hM'm, hM'd, hM'U, hM'S⟩ :=
    @exists_measurable_finite_partition Ω (retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r) _ S (⋃ i, S i) hSm rfl
  have hR := retSigma76_le P η₁ η₂ ζ₁ ζ₂ d.u d.r
  refine ⟨Fintype.card (BoundedForceTypes Nb wts), fun i => M' i \ N,
    fun i => (hR _ (hM'm i)).diff hNm, fun i j hij => (hM'd hij).mono sdiff_subset sdiff_subset, ?_, ?_⟩
  · -- the parts cover the disjoint pairs almost surely
    filter_upwards [hGood, measure_eq_zero_iff_ae_notMem.1 hN0] with ω hg hωN hp
    obtain ⟨-, -, -, h4, -, -, h7, h8⟩ := hg
    obtain ⟨sβ, sW, heq⟩ := h7 hp
    obtain ⟨j, hj⟩ := exists_boundedForceType (hasBoundedForceType_wordM (retFam G η₁' η₂' d.u d.r) κ θ₂ c₀
      (-sleLambda κ - θ₂ * QuantumZipper.chiC κ) (sleLambda κ - θ₂ * QuantumZipper.chiC κ)
      (-sleLambda κ - θ₁ * QuantumZipper.chiC κ) (sleLambda κ - θ₁ * QuantumZipper.chiC κ) ω)
    have hj' : retWordAt G η₁' η₂' d.u κ θ₁ θ₂ c₀ d.r ω ∈ forceTypeSet κ θ₂ (boundedForceType Nb wts j) := hj
    have hβj := (mem_forceTypeSet_iff_of_mean_integrals _ sβ sW heq).2 hj'
    have hS : ω ∈ ⋃ i, S i := by
      refine mem_iUnion.2 ⟨e j, ⟨h8.2 hp, h4 hp.1 hp.2.1⟩, ?_⟩
      show β ω ∈ forceTypeSet κ θ₂ (boundedForceType Nb wts (e.symm (e j)))
      rw [Equiv.symm_apply_apply]
      exact hβj
    rw [← hM'U] at hS
    obtain ⟨i, hi⟩ := mem_iUnion.1 hS
    exact ⟨i, hi, hωN⟩
  · -- the model on each part
    intro i hPi
    have hfact : ∀ ω ∈ M' i \ N, ω ∈ G d.r ∧ β ω ∈ forceTypeSet κ θ₂ (a i) ∧ Good ω ∧
        Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r := by
      intro ω hω
      have hS := hM'S i hω.1
      have hg := hNsub ω hω.2
      exact ⟨hS.1.2, hS.2, hg, hg.2.2.2.2.2.2.2.1 hS.1.1⟩
    have hMa₁ : ∀ ω ∈ M' i \ N, ∀ s ≤ d.u, η₁' ω s = η₁ ω s := fun ω hω s hs =>
      (hfact ω hω).2.2.1.2.1 s ((ENNReal.coe_le_coe.2 hs).trans (hfact ω hω).2.2.2.1.le)
    have hMa₂ : ∀ ω ∈ M' i \ N, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s := fun ω hω =>
      (hfact ω hω).2.2.1.2.2.1
    have hMa₂' : ∀ ω ∈ M' i \ N, ∀ t ≤ d.r, η₂' ω t = η₂ ω t := fun ω hω t ht =>
      hMa₂ ω hω t ((ENNReal.coe_le_coe.2 ht).trans (hfact ω hω).2.2.2.2.1.le)
    have hMd : ∀ ω ∈ M' i \ N, ω ∈ d.G ∧ (∀ s ≤ d.u, d.η₁ ω s = η₁' ω s) ∧
        ∀ t ≤ d.r, d.η₂ ω t = η₂' ω t := by
      intro ω hω
      have hp := (hfact ω hω).2.2.2
      obtain ⟨hGd, a₁, a₂⟩ := (hfact ω hω).2.2.1.1 hp.1 hp.2.1
      exact ⟨hGd, fun s hs => (a₁ s hs).trans (hMa₁ ω hω s hs).symm,
        fun t ht => (a₂ t ht).trans (hMa₂' ω hω t ht).symm⟩
    have hMpair : ∀ ω ∈ M' i \ N, Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) d.u (η₂' ω) (ζ₂ ω) d.r :=
      fun ω hω => (isDisjointPair_congr (hMa₁ ω hω) (hMa₂' ω hω) Iff.rfl Iff.rfl).2 (hfact ω hω).2.2.2
    have hMmR : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] (M' i \ N) :=
      measurableSet_retSigma76_congr ((hR _ (hM'm i)).diff hNm) (hM'm i) (sdiff_null_ae_eq_self hN0)
    exact nonempty_stoppedModelTransfer_branch (θ₁ := θ₁) hL75 hκ hκ4 hb hx hh hη₁ hη₂ hd hag hu₀ hβ hmean
      hsort ha₁ ha₂ hdG hGae (hG d.r).2.1 hc₀ hc₀J hc₀b (a i) hMmR hPi (fun ω hω => (hfact ω hω).1) hMd
      hMpair (fun ω hω => (hfact ω hω).2.2.2)
      (fun ω hω => Supp7.IsPathGood.congr (hfact ω hω).2.2.1.2.2.2.2.1 (hfact ω hω).2.2.1.2.1)
      (fun ω hω => Supp7.IsPathGood.congr (hfact ω hω).2.2.1.2.2.2.2.2.1 (hMa₂ ω hω))
      hMa₁ hMa₂ (fun ω hω => (hfact ω hω).2.1) (fun ω hω => (hfact ω hω).2.2.1.2.2.2.2.2.2.1 (hfact ω hω).2.2.2)

/-- **Lemma 7.6's retained determination (R55 form) from Lemma 7.5**, Theorem 1.3 and the stopped hull
extension: `RetAux79.lemma76DetRStatement_of_stoppedModels` with its model input discharged. -/
theorem lemma76DetRStatement_of_lemma75
    (hext : ∀ κ : ℝ, 0 < κ → κ < 4 → StoppedExtend.StoppedHullExtendStatement.{0} κ)
    (h13 : Exist.Theorem13Statement.{0}) (hL75 : Theorem15.Lemma75Statement.{v}) :
    Sec7.Lemma76DetRStatement.{v} :=
  lemma76DetRStatement_of_stoppedModels hext h13 (retStoppedModelsStatement_of_lemma75 hL75)

end InteractingSLE.Restart.RetFin
