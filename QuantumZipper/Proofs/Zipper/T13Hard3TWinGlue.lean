import QuantumZipper.Proofs.Zipper.T13Hard3Heart

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# T13-HARD3-TWIN, glue: pair coupling and a product-measure identity

Own elementary glue for `T13Hard3TWin.lean`:
* `twin_tvDist_pair_le`: if two index-valued random variables agree coordinatewise a.s. on `G`,
  then pairing them with the same real variable costs at most `P Gᶜ` in TV (reduction to
  `tvDist_map_le_of_coord` on the index `Option ι`);
* `twin_map_prod_prod`: `(ν ⊗ (μT ⊗ μρ)).map (y,(t,p) ↦ (H (y,p), t)) = ((ν ⊗ μρ).map H) ⊗ μT`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-- Coupling inequality for pairs `(W, T)` vs `(F, T)` with coordinatewise a.s. agreement of `W`
and `F` on `G` (own elementary proof). -/
theorem twin_tvDist_pair_le {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {W F : Ω → ι → ℝ} {T : Ω → ℝ} (hW : AEMeasurable W P) (hF : AEMeasurable F P)
    (hT : AEMeasurable T P) (G : Set Ω) (h : ∀ i, ∀ᵐ ω ∂P, ω ∈ G → W ω i = F ω i) :
    TV.tvDist (P.map fun ω => (W ω, T ω)) (P.map fun ω => (F ω, T ω)) ≤ P Gᶜ := by
  let v : (ι → ℝ) × ℝ → (Option ι → ℝ) := fun p o => o.elim p.2 p.1
  let e : (Option ι → ℝ) → (ι → ℝ) × ℝ := fun w => (fun i => w (some i), w none)
  have hv : Measurable v := by
    refine Measurable.of_eval fun o => ?_
    cases o with
    | none => exact measurable_snd
    | some i => exact (measurable_pi_apply i).comp measurable_fst
  have he : Measurable e :=
    (Measurable.of_eval fun i => measurable_pi_apply (some i)).prodMk (measurable_pi_apply none)
  have hV : AEMeasurable (fun ω => v (W ω, T ω)) P := hv.comp_aemeasurable (hW.prodMk hT)
  have hV' : AEMeasurable (fun ω => v (F ω, T ω)) P := hv.comp_aemeasurable (hF.prodMk hT)
  have e1 : P.map (fun ω => (W ω, T ω)) = (P.map fun ω => v (W ω, T ω)).map e := by
    rw [AEMeasurable.map_map_of_aemeasurable he.aemeasurable hV]; rfl
  have e2 : P.map (fun ω => (F ω, T ω)) = (P.map fun ω => v (F ω, T ω)).map e := by
    rw [AEMeasurable.map_map_of_aemeasurable he.aemeasurable hV']; rfl
  rw [e1, e2]
  refine (TV.tvDist_map_le he).trans (tvDist_map_le_of_coord hV hV' G fun o => ?_)
  cases o with
  | none => exact Eventually.of_forall fun _ _ => rfl
  | some i => exact h i

/-- Rearranging a triple product (own elementary proof). -/
theorem twin_map_prod_prod {E A B C : Type*} [MeasurableSpace E] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (ν : Measure E) (μT : Measure A) (μρ : Measure B)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μT] [IsProbabilityMeasure μρ]
    {H : E × B → C} (hH : Measurable H) :
    (ν.prod (μT.prod μρ)).map (fun q => (H (q.1, q.2.2), q.2.1)) = ((ν.prod μρ).map H).prod μT := by
  have h1 : μT.prod μρ = (μρ.prod μT).map Prod.swap := Measure.prod_swap.symm
  have h2 : ν.prod ((μρ.prod μT).map Prod.swap) =
      (ν.prod (μρ.prod μT)).map (Prod.map id Prod.swap) := by
    rw [← Measure.map_prod_map ν (μρ.prod μT) measurable_id measurable_swap, Measure.map_id]
  have h3 : ν.prod (μρ.prod μT) = ((ν.prod μρ).prod μT).map MeasurableEquiv.prodAssoc :=
    Measure.prodAssoc_prod.symm
  have h4 : ((ν.prod μρ).map H).prod μT = ((ν.prod μρ).prod μT).map (Prod.map H id) := by
    rw [← Measure.map_prod_map (ν.prod μρ) μT hH measurable_id, Measure.map_id]
  have hq : Measurable fun q : E × (A × B) => (H (q.1, q.2.2), q.2.1) :=
    (hH.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))).prodMk
      (measurable_fst.comp measurable_snd)
  rw [h1, h2, h3, h4, Measure.map_map hq (measurable_id.prodMap measurable_swap),
    Measure.map_map (hq.comp (measurable_id.prodMap measurable_swap))
      MeasurableEquiv.prodAssoc.measurable]
  rfl

end D3Plus
end QuantumZipper
