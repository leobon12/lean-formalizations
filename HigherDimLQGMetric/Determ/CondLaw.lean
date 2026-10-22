import HigherDimLQGMetric.B3.Interfaces
import HigherDimLQGMetric.Field.StandardBorel
import HigherDimLQGMetric.Select.MetricBorel
import LQGMetric.Papers.DFGPS.L2_17Core3F

/-!
# Conditional joint law of metric copies

The event form of conditional independence is transferred to the standard
Borel law space, where mathlib's conditional-kernel factorization applies.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem determ_ci_triple_law {d : ℕ} [Nonempty (ContMetric d)]
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (D₁ D₂ : Ω → ContMetric d)
    (hh : Measurable h) (hD₁ : Measurable D₁) (hD₂ : Measurable D₂)
    (hci : LQGMetric.CondIndepEv (fullSigmaRd h)
      (MeasurableSpace.comap D₁ inferInstance)
      (MeasurableSpace.comap D₂ inferInstance) P) :
    P.map (fun ω => (h ω, D₁ ω, D₂ ω)) =
      P.map h ⊗ₘ (condDistrib D₁ h P ×ₖ condDistrib D₂ h P) := by
  let T := DistRd d × (ContMetric d × ContMetric d)
  let π : Ω → T := fun ω => (h ω, D₁ ω, D₂ ω)
  let k : T → DistRd d := Prod.fst
  let f : T → ContMetric d := fun t => t.2.1
  let g : T → ContMetric d := fun t => t.2.2
  have hπ : Measurable π := hh.prodMk (hD₁.prodMk hD₂)
  have hk : Measurable k := measurable_fst
  have hf : Measurable f := measurable_fst.comp measurable_snd
  have hg : Measurable g := measurable_snd.comp measurable_snd
  have hG : MeasurableSpace.comap k inferInstance ≤ (inferInstance : MeasurableSpace T) :=
    hk.comap_le
  have hA : MeasurableSpace.comap f inferInstance ≤ (inferInstance : MeasurableSpace T) :=
    hf.comap_le
  have hB : MeasurableSpace.comap g inferInstance ≤ (inferInstance : MeasurableSpace T) :=
    hg.comap_le
  have hci' : LQGMetric.CondIndepEv (MeasurableSpace.comap k inferInstance)
      (MeasurableSpace.comap f inferInstance)
      (MeasurableSpace.comap g inferInstance) (P.map π) := by
    apply LQGMetric.DFGPS.L217.condIndepEv_map hπ hG hA hB
    have hkπ : k ∘ π = h := rfl
    have hfπ : f ∘ π = D₁ := rfl
    have hgπ : g ∘ π = D₂ := rfl
    rw [MeasurableSpace.comap_comp, MeasurableSpace.comap_comp,
      MeasurableSpace.comap_comp, hkπ, hfπ, hgπ]
    exact hci
  have hmath : CondIndepFun (MeasurableSpace.comap k inferInstance) hG f g (P.map π) :=
    (condIndepFun_iff_condIndep (MeasurableSpace.comap k inferInstance) hG f g
      (P.map π)).2 ((LQGMetric.condIndep_iff_condIndepEv hG hA hB).2 hci')
  have hfact := (condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib
    (μ := P.map π) hf hg hk).1 hmath
  have hmapk : (P.map π).map k = P.map h := by
    rw [Measure.map_map hk hπ]
    rfl
  have hcond1 : condDistrib f k (P.map π) = condDistrib D₁ h P := by
    rw [condDistrib, condDistrib]
    simp only [Measure.map_map (hk.prodMk hf) hπ, Function.comp_def,
      k, f, π]
  have hcond2 : condDistrib g k (P.map π) = condDistrib D₂ h P := by
    rw [condDistrib, condDistrib]
    simp only [Measure.map_map (hk.prodMk hg) hπ, Function.comp_def,
      k, g, π]
  rw [hmapk, hcond1, hcond2, ← Measure.compProd_eq_comp_prod] at hfact
  have hmapπ : (P.map π).map (fun t => (k t, f t, g t)) = P.map π := by
    rw [Measure.map_map (hk.prodMk (hf.prodMk hg)) hπ]
    rfl
  rwa [hmapπ] at hfact

end HigherDimLQGMetric
