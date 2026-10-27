import MatedCRTHarmonic.MesoModel.Rec
import MatedCRTHarmonic.MesoModel.RecScaleCore
import MatedCRTHarmonic.MesoModel.CloseTransfer
import MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2Unique

/-!
# Transfer the family-scale recurrence estimate to Brownian path laws

The source estimate is an outer-measure bound on a coupled cell family. This module transfers that
bound through the measurable Brownian-path map using the same standard-Borel disintegration as
The Borel-free a.e. transfer needs no measurability of the path event. Brownian rescaling
from these mesh estimates to the unit-mesh recurrence conclusion is handled by Rec.lean using a
measurable equivalence.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.MesoModel

open MatedCRTHarmonic

universe u v

/-- Quantitative Borel-free transfer through a measurable path map. If membership of an arbitrary
path property forces the sample into a measurable set almost surely, then the pushforward outer
measure of that path event is bounded by the measure of the sample set. -/
private theorem matedCRT_outerMeasure_map_le_of_ae_imp
    {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {f : Ω → MatedCRT.Path2} (hf : Measurable f)
    {Q : MatedCRT.Path2 → Prop} {N : Set Ω} (hN : MeasurableSet N)
    (hQN : ∀ᵐ ω ∂P, Q (f ω) → ω ∈ N) :
    (P.map f) {x | Q x} ≤ P N := by
  classical
  let g : Ω → MatedCRT.Path2 × Ω := fun ω => (f ω, ω)
  have hg : Measurable g := hf.prodMk measurable_id
  let ρ : Measure (MatedCRT.Path2 × Ω) := P.map g
  letI : Nonempty Ω := MeasureTheory.nonempty_of_isProbabilityMeasure P
  have hρfinite : IsFiniteMeasure ρ := Measure.isFiniteMeasure_map P g
  letI : IsFiniteMeasure ρ := hρfinite
  let κ := ρ.condKernel
  have hcond : ρ.IsCondKernel κ := by
    simpa [κ] using (inferInstance : ρ.IsCondKernel ρ.condKernel)
  have hfst : ρ.fst = P.map f := by
    rw [Measure.fst, Measure.map_map measurable_fst hg]
    rfl
  have hgraph : MeasurableSet {p : MatedCRT.Path2 × Ω | p.1 = f p.2} :=
    closeMeasurableSet_graph_path2 hf
  have hρgraph : ∀ᵐ p ∂ρ, p.1 = f p.2 := by
    refine (ae_map_iff hg.aemeasurable hgraph).2 ?_
    filter_upwards with ω
    exact rfl
  have hbad : P {ω | Q (f ω) ∧ ω ∉ N} = 0 := by
    have h := ae_iff.mp hQN
    have hset : {ω | Q (f ω) ∧ ω ∉ N} =
        {ω | ¬ (Q (f ω) → ω ∈ N)} := by
      ext ω
      simp
    rw [hset]
    exact h
  obtain ⟨Nbad, hbadSub, hbadMeas, hbadMeasure⟩ :=
    exists_measurable_superset_of_null hbad
  have hρNbad : ρ {p | p.2 ∈ Nbad} = 0 := by
    calc
      ρ {p | p.2 ∈ Nbad} = P (g ⁻¹' {p | p.2 ∈ Nbad}) :=
        Measure.map_apply hg (measurable_snd hbadMeas)
      _ = P Nbad := by congr 1
      _ = 0 := hbadMeasure
  have hρgood : ∀ᵐ p ∂ρ, (Q p.1 → p.2 ∈ N) := by
    filter_upwards [hρgraph, measure_eq_zero_iff_ae_notMem.mp hρNbad] with p hpGraph hpNbad
    intro hpQ
    by_contra hpNotN
    have hpQ' : Q (f p.2) := hpGraph ▸ hpQ
    have hpBad : p.2 ∈ Nbad := hbadSub ⟨hpQ', hpNotN⟩
    exact hpNbad hpBad
  rw [← hcond.disintegrate] at hρgood
  have hfiber := Measure.ae_ae_of_ae_compProd hρgood
  let B : Set MatedCRT.Path2 := {x | κ x N = 1}
  have hB : MeasurableSet B := by
    exact measurableSet_eq_fun (κ.measurable_coe hN) measurable_const
  have hBbound : ρ.fst B ≤ P N := by
    have hsection : ∀ᵐ x ∂ρ.fst, ∀ᵐ ω ∂κ x, (x ∈ B → ω ∈ N) := by
      filter_upwards with x
      by_cases hx : x ∈ B
      · have hNae : ∀ᵐ ω ∂κ x, ω ∈ N :=
          (MeasureTheory.mem_ae_iff_prob_eq_one hN).2 hx
        filter_upwards [hNae] with ω hω
        exact fun _ => hω
      · exact ae_of_all _ fun ω hxB => (hx hxB).elim
    have hprodMeas : MeasurableSet
        {p : MatedCRT.Path2 × Ω | p.1 ∈ B → p.2 ∈ N} := by
      have hset :
          {p : MatedCRT.Path2 × Ω | p.1 ∈ B → p.2 ∈ N} =
            (Prod.fst ⁻¹' B)ᶜ ∪ Prod.snd ⁻¹' N := by
        ext p
        by_cases hpB : p.1 ∈ B <;> simp [hpB]
      rw [hset]
      exact (hB.preimage measurable_fst).compl.union
        (hN.preimage measurable_snd)
    have hprod : ∀ᵐ p ∂(ρ.fst ⊗ₘ κ), (p.1 ∈ B → p.2 ∈ N) :=
      Measure.ae_compProd_of_ae_ae (μ := ρ.fst) (κ := κ) hprodMeas hsection
    rw [hcond.disintegrate] at hprod
    have hprodRho : ∀ᵐ p ∂ρ, (p.1 ∈ B → p.2 ∈ N) := by
      simpa using hprod
    have haeBadProd : ∀ᵐ p ∂ρ, p ∉ {p | p.1 ∈ B ∧ p.2 ∉ N} := by
      filter_upwards [hprodRho] with p hp
      simp only [mem_setOf_eq, not_and]
      exact fun hpB hpN => hpN (hp hpB)
    have hbadProd : ρ {p | p.1 ∈ B ∧ p.2 ∉ N} = 0 := by
      exact measure_eq_zero_iff_ae_notMem.mpr haeBadProd
    have hsubset : {p : MatedCRT.Path2 × Ω | p.1 ∈ B} ⊆
        {p | p.2 ∈ N} ∪ {p | p.1 ∈ B ∧ p.2 ∉ N} := by
      intro p hp
      by_cases hpN : p.2 ∈ N
      · exact Or.inl hpN
      · exact Or.inr ⟨hp, hpN⟩
    calc
      ρ.fst B = ρ (Prod.fst ⁻¹' B) := Measure.fst_apply hB
      _ = ρ {p | p.1 ∈ B} := by rfl
      _ ≤ ρ ({p | p.2 ∈ N} ∪ {p | p.1 ∈ B ∧ p.2 ∉ N}) := measure_mono hsubset
      _ ≤ ρ {p | p.2 ∈ N} + ρ {p | p.1 ∈ B ∧ p.2 ∉ N} := measure_union_le _ _
      _ = P N := by
        rw [hbadProd, add_zero]
        change (P.map g) (Prod.snd ⁻¹' N) = P N
        rw [Measure.map_apply hg (measurable_snd hN)]
        rfl
  have hBmeas : (P.map f) B ≤ P N := by simpa only [← hfst] using hBbound
  have hAmod : {x : MatedCRT.Path2 | Q x} ⊆ B ∪
      {x | ¬ ∀ᵐ ω ∂κ x, Q x → ω ∈ N} := by
    intro x hxQ
    by_cases hx : ∀ᵐ ω ∂κ x, Q x → ω ∈ N
    · left
      have hNae : ∀ᵐ ω ∂κ x, ω ∈ N := hx.mono fun ω hω => hω hxQ
      have hmass : κ x N = 1 :=
        (MeasureTheory.mem_ae_iff_prob_eq_one hN).1 hNae
      exact hmass
    · exact Or.inr hx
  have hbadFiberZero : ρ.fst {x | ¬ ∀ᵐ ω ∂κ x, Q x → ω ∈ N} = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hfiber] with x hx
    by_contra hnot
    exact hnot hx
  obtain ⟨Z, hZsub, hZmeas, hZzero⟩ := exists_measurable_superset_of_null hbadFiberZero
  have hZmap : (P.map f) Z = 0 := by
    calc
      (P.map f) Z = ρ.fst Z := by rw [hfst]
      _ = 0 := hZzero
  have hA : (P.map f) {x | Q x} ≤ (P.map f) (B ∪ Z) :=
    measure_mono (fun x hx => by
      rcases hAmod hx with h | h
      · exact Or.inl h
      · exact Or.inr (hZsub h))
  calc
    (P.map f) {x | Q x} ≤ (P.map f) B + (P.map f) Z :=
      hA.trans (measure_union_le _ _)
    _ = (P.map f) B := by
      rw [hZmap, add_zero]
    _ ≤ P N := hBmeas

/-- A graph equality transports a cellular embedding across its multigraph cast. -/
private def matedCRT_cellularEmbedding_of_cast
    {V : Type v} {E E' : Type u} {G : LFMultigraph V E} {G' : LFMultigraph V E'} {o : V}
    (hE : E = E')
    (hG : cast (congrArg (LFMultigraph V) hE) G = G')
    (H : CellularEmbedding G o) : CellularEmbedding G' o := by
  cases hE
  change G = G' at hG
  subst G'
  exact H

private theorem matedCRT_theorem14Inputs_of_cast
    {V : Type v} {E E' : Type u} {G : LFMultigraph V E} {G' : LFMultigraph V E'}
    {o : V} {ε ρ ρ₁ q β β' α A : ℝ}
    (hE : E = E')
    (hG : cast (congrArg (LFMultigraph V) hE) G = G')
    (H : CellularEmbedding G o)
    (hinputs : GMS3.Theorem14Inputs H ε ρ ρ₁ q β β' α A) :
    GMS3.Theorem14Inputs
      (matedCRT_cellularEmbedding_of_cast hE hG H) ε ρ ρ₁ q β β' α A := by
  cases hE
  change G = G' at hG
  subst G'
  exact hinputs

/-- The family-level Lemma 2.7/G4 scale input yields the exact all-law path-scale estimate consumed by
the recurrence theorem. The outer-measure disintegration transfer retains its polynomial rate on
arbitrary path events. -/
theorem matedCRTRecurrencePathScaleInput_of_scaleInput
    {γ : ℝ} (hin : MatedCRTRecurrenceScaleInput γ) :
    MatedCRTRecurrencePathScaleInput γ := by
  rcases hin with ⟨Cpl, hstd, ρ, ρ₁, q, β, β', α, A, C27, Cfail,
    hρ, hρ₁, hβ, hq, hβ', hβ'q, hα, hA, hC27, hCfail, hbad⟩
  letI : StandardBorelSpace Cpl.family.Ω := hstd
  intro μ hμ
  have hlaw : Cpl.family.P.map Cpl.bm = μ :=
    MatedCRTHarmonic.isCorrelatedBM2_unique_holds γ _ _ Cpl.coupling.law hμ
  refine ⟨ρ, ρ₁, q, β, β', α, A, C27 + 3 * Cfail,
    hρ, hρ₁, hβ, hq, hβ', hβ'q, hα, hA, by positivity, ?_⟩
  intro k
  let Bfam : Set Cpl.family.Ω :=
    {ω | ¬ GMS3.Theorem14Inputs (Cpl.family.H k ω)
      (CellFamily.mesh k) ρ ρ₁ q β β' α A}
  obtain ⟨N, hBsub, hNmeas, hNmeasure⟩ :=
    exists_measurable_superset Cpl.family.P Bfam
  have hQimp : ∀ᵐ ω ∂Cpl.family.P,
      (¬ matedCRTTheorem14MeshGood (CellFamily.mesh k) ρ ρ₁ q β β' α A
        (Cpl.bm ω)) → ω ∈ N := by
    filter_upwards [Cpl.meshGraph_eq k] with ω hID
    rcases hID with ⟨hE, hlf, hG⟩
    intro hbadPath
    by_contra hωN
    have hinputs : GMS3.Theorem14Inputs (Cpl.family.H k ω)
        (CellFamily.mesh k) ρ ρ₁ q β β' α A := by
      by_contra hnot
      exact hωN (hBsub hnot)
    have Hpath : CellularEmbedding
        (MatedCRT.graph (CellFamily.mesh k) (Cpl.bm ω) hlf) 0 :=
      matedCRT_cellularEmbedding_of_cast hE hG (Cpl.family.H k ω)
    have hinputsPath := matedCRT_theorem14Inputs_of_cast hE hG
      (Cpl.family.H k ω) hinputs
    exact hbadPath ⟨hlf, matedCRT_cellularEmbedding_of_cast hE hG
      (Cpl.family.H k ω), hinputsPath⟩
  have hbound := matedCRT_outerMeasure_map_le_of_ae_imp
    (P := Cpl.family.P) (f := Cpl.bm)
    (Q := fun ω => ¬ matedCRTTheorem14MeshGood
      (CellFamily.mesh k) ρ ρ₁ q β β' α A ω) (N := N)
    Cpl.coupling.measurable_bm hNmeas hQimp
  have hrate := hbad k
  have hcombine :
      ENNReal.ofReal (C27 * CellFamily.mesh k ^ α) +
          ENNReal.ofReal (Cfail * CellFamily.mesh k ^ α) +
          ENNReal.ofReal (Cfail * CellFamily.mesh k ^ α) +
          ENNReal.ofReal (Cfail * CellFamily.mesh k ^ α) =
        ENNReal.ofReal ((C27 + 3 * Cfail) * CellFamily.mesh k ^ α) := by
    have hmesh : 0 ≤ CellFamily.mesh k ^ α := by
      unfold CellFamily.mesh
      positivity
    have hx27 : 0 ≤ C27 * CellFamily.mesh k ^ α := by positivity
    have hxf : 0 ≤ Cfail * CellFamily.mesh k ^ α := by positivity
    rw [← ENNReal.ofReal_add hx27 hxf,
      ← ENNReal.ofReal_add (by positivity :
        0 ≤ C27 * CellFamily.mesh k ^ α + Cfail * CellFamily.mesh k ^ α) hxf,
      ← ENNReal.ofReal_add (by positivity :
        0 ≤ C27 * CellFamily.mesh k ^ α + Cfail * CellFamily.mesh k ^ α +
          Cfail * CellFamily.mesh k ^ α) hxf]
    have _ := hmesh
    congr 1
    ring
  calc
    μ {ω | ¬ matedCRTTheorem14MeshGood (CellFamily.mesh k) ρ ρ₁ q β β' α A ω} =
        (Cpl.family.P.map Cpl.bm)
          {ω | ¬ matedCRTTheorem14MeshGood (CellFamily.mesh k) ρ ρ₁ q β β' α A ω} := by
            rw [← hlaw]
    _ ≤ Cpl.family.P N := hbound
    _ = Cpl.family.P Bfam := hNmeasure
    _ ≤ _ := hrate
    _ = ENNReal.ofReal ((C27 + 3 * Cfail) * CellFamily.mesh k ^ α) := hcombine

end MatedCRTHarmonic.MesoModel

