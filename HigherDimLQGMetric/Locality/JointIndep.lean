import HigherDimLQGMetric.Locality.JointMarginal
import LQGMetric.Papers.DFGPS.L2_17CoreC

/-! Finite-stage independence passes to the first coordinates of a joint
Skorokhod limit, even when extra metric coordinates are coupled with them. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped BoundedContinuousFunction

namespace HigherDimLQGMetric

theorem l7a_indep_of_joint_skorokhod
    {S T₁ T₂ C Ω E : Type}
    [MeasurableSpace Ω] [MeasurableSpace E]
    [TopologicalSpace S] [mS : MeasurableSpace S]
    [OpensMeasurableSpace S] [BorelSpace S] [PolishSpace S]
    [TopologicalSpace T₁] [MeasurableSpace T₁] [BorelSpace T₁]
    [SecondCountableTopology T₁] [PseudoMetrizableSpace T₁] [T2Space T₁]
    [TopologicalSpace T₂] [MeasurableSpace T₂] [BorelSpace T₂]
    [SecondCountableTopology T₂] [PseudoMetrizableSpace T₂] [T2Space T₂]
    [TopologicalSpace C] [MeasurableSpace C] [OpensMeasurableSpace C]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure E) [IsProbabilityMeasure Q]
    (X : Ω → S) (A : ℕ → Ω → T₁) (B : ℕ → Ω → T₂)
    (Cₙ : ℕ → Ω → C)
    (hX : Measurable X) (hA : ∀ n, Measurable (A n))
    (hB : ∀ n, Measurable (B n))
    (hC : ∀ n, AEMeasurable (Cₙ n) P)
    (ns : ℕ → ℕ)
    (Z : ℕ → E → (S × C) × (T₁ × T₂))
    (Zlim : E → (S × C) × (T₁ × T₂))
    (hZm : ∀ n, Measurable (Z n)) (hZlimm : Measurable Zlim)
    (hZlaw : ∀ n, Q.map (Z n) = P.map (fun ω =>
      ((X ω, Cₙ (ns n) ω), (A (ns n) ω, B (ns n) ω))))
    (hZconv : ∀ e, Tendsto (fun n => Z n e) atTop (𝓝 (Zlim e)))
    (𝒢 ℋ : {m : MeasurableSpace S // m ≤ mS})
    (hind : ∀ n, Indep
      (𝒢.1.comap X ⊔ MeasurableSpace.comap (A n) inferInstance)
      (ℋ.1.comap X ⊔ MeasurableSpace.comap (B n) inferInstance) P) :
    Indep
      (𝒢.1.comap (fun e => (Zlim e).1.1) ⊔
        MeasurableSpace.comap (fun e => (Zlim e).2.1) inferInstance)
      (ℋ.1.comap (fun e => (Zlim e).1.1) ⊔
        MeasurableSpace.comap (fun e => (Zlim e).2.2) inferInstance) Q := by
  let π : (S × C) × (T₁ × T₂) → S × (T₁ × T₂) :=
    fun q => (q.1.1, q.2)
  have hπ : Measurable π :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hcπ : Continuous π := by fun_prop
  let ρ : ProbabilityMeasure (S × (T₁ × T₂)) :=
    ⟨Q.map (π ∘ Zlim), inferInstance⟩
  have hProj (n : ℕ) : Q.map (π ∘ Z n) =
      P.map (fun ω => (X ω, (A (ns n) ω, B (ns n) ω))) := by
    calc
      Q.map (π ∘ Z n) = (Q.map (Z n)).map π :=
        (Measure.map_map hπ (hZm n)).symm
      _ = (P.map (fun ω =>
        ((X ω, Cₙ (ns n) ω), (A (ns n) ω, B (ns n) ω)))).map π := by
          rw [hZlaw n]
      _ = P.map (fun ω => (X ω, (A (ns n) ω, B (ns n) ω))) := by
          simpa only [Function.comp_def] using
            (AEMeasurable.map_map_of_aemeasurable hπ.aemeasurable
              ((hX.aemeasurable.prodMk (hC (ns n))).prodMk
                ((hA (ns n)).prodMk (hB (ns n))).aemeasurable))
  have hconvπ (e : E) : Tendsto (fun n => (π ∘ Z n) e) atTop
      (𝓝 ((π ∘ Zlim) e)) :=
    (hcπ.tendsto (Zlim e)).comp (hZconv e)
  have hν : Tendsto (β := ProbabilityMeasure (S × (T₁ × T₂)))
      (fun n => (⟨P.map (fun ω =>
        (X ω, (A (ns n) ω, B (ns n) ω))), inferInstance⟩ :
        ProbabilityMeasure (S × (T₁ × T₂)))) atTop (𝓝 ρ) := by
    have ht := LQGMetric.DFGPS.L217.tendsto_map_of_forall_tendsto
      (P := Q) (Z := fun n => π ∘ Z n) (Z₀ := π ∘ Zlim)
      (fun n => hπ.comp (hZm n))
      (hπ.comp hZlimm) hconvπ
    have heq (n : ℕ) :
        (⟨Q.map (π ∘ Z n), inferInstance⟩ :
          ProbabilityMeasure (S × (T₁ × T₂))) =
        (⟨P.map (fun ω =>
          (X ω, (A (ns n) ω, B (ns n) ω))), inferInstance⟩ :
          ProbabilityMeasure (S × (T₁ × T₂))) := Subtype.ext (hProj n)
    simpa only [← heq] using ht
  have hmarg : (ρ : Measure (S × (T₁ × T₂))).map Prod.fst = P.map X := by
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun g => ?_
    have key := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hν)
      (g.compContinuous ⟨Prod.fst, continuous_fst⟩)
    have hgm : Measurable fun x => g x := g.continuous.measurable
    have e : ∀ n, ∫ p, (g.compContinuous ⟨Prod.fst, continuous_fst⟩) p
        ∂(P.map fun ω => (X ω, (A (ns n) ω, B (ns n) ω))) =
        ∫ x, g x ∂(P.map X) := fun n => by
      show ∫ p, g p.1
        ∂(P.map fun ω => (X ω, (A (ns n) ω, B (ns n) ω))) = _
      rw [integral_map (hX.prodMk ((hA (ns n)).prodMk (hB (ns n)))).aemeasurable
        (f := fun p : S × (T₁ × T₂) => g p.1)
        (hgm.comp measurable_fst).aestronglyMeasurable,
        integral_map hX.aemeasurable hgm.aestronglyMeasurable]
    simp only [ProbabilityMeasure.coe_mk, e] at key
    rw [integral_map measurable_fst.aemeasurable hgm.aestronglyMeasurable]
    exact tendsto_nhds_unique key tendsto_const_nhds
  have hindρ := LQGMetric.DFGPS.L217.indep_of_tendsto_coupling
    hX (fun n => hA (ns n)) (fun n => hB (ns n)) hν hmarg 𝒢 ℋ
      (fun n => hind (ns n))
  have hπlim : Measurable (π ∘ Zlim) := hπ.comp hZlimm
  have htrans := LQGMetric.DFGPS.L217.indep_comap_of_map_eq
    (P := Q) (P' := (ρ : Measure _)) (X := π ∘ Zlim) (X' := id)
    hπlim measurable_id (by simp only [Measure.map_id]; rfl)
    (sup_le ((MeasurableSpace.comap_mono 𝒢.2).trans measurable_fst.comap_le)
      (measurable_fst.comp measurable_snd).comap_le)
    (sup_le ((MeasurableSpace.comap_mono ℋ.2).trans measurable_fst.comap_le)
      (measurable_snd.comp measurable_snd).comap_le)
    (by simpa only [MeasurableSpace.comap_id, Function.comp_id,
      Function.comp_def] using hindρ)
  simpa only [MeasurableSpace.comap_sup, MeasurableSpace.comap_comp,
    Function.comp_def] using htrans

end HigherDimLQGMetric
