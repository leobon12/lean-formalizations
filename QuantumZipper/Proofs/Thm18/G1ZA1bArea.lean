import QuantumZipper.Proofs.Thm18.G1ZSplitDefs
import QuantumZipper.Proofs.Thm18.G1Z2MeasScale
import QuantumZipper.Proofs.Thm18.G1Pair
import QuantumZipper.Proofs.Zipper.Cor15RezipRegGood
import QuantumZipper.Proofs.Zipper.WedgeCocycleCore
import QuantumZipper.Proofs.LQG.IndepParams

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-A1b, part 1: area-only choice independence and the translated field identity

Theorem 1.8, G1 zoom, node A1b `G1RerootRegStmt` (decision D66, handoff/G1-ZSPLIT.md item 2).
Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, proof of Theorem 1.8,
pp. 69–71 (the side surfaces after unzipping by a fixed quantum length are the old ones,
rerooted), and the definition (1.8) of the canonical description (rescaling by the unit-area
radius), which does not depend on the choice of the conformal map up to dilation.

* `g1za1b_scaleConsistent_of_core`: scale consistency of the pulled-back field from the PAIR-LIM
  clause of `G1.ChoiceRegularCore` (as in `G1.choiceRegular_of_continuum`, but with the regular
  sample of the core instead of the full `IsLQGGood`).
* `g1za1b_dataFull_canonical_rescale`: `dataFull H (canonical (rescale x Q b)) =
  dataFull H (canonical x)` from *area-only* goodness (regular sample + area limit), positive
  scale parameter and scale consistency. This is the variant of
  `G1.data_canonical_coordChange_eq` requested by the G1-ZSPLIT hazard note: it never uses the
  global boundary limit contained in `IsLQGGood` (it uses `g1z2_scaleParam_rescale`,
  `g1z2_canonical_rescale_apply` of G1Z2MeasScale).
* `g1za1b_regEq_translate`: deterministic change of variables: if the regularized folded-circle
  values of `X'` are those of the pullback of `y` by `Φ'`, and `Φ'(· + β) = G` on `ℍ` with `G`
  measurable, then `translate X' β` is `RegEq` to `coordChange y G Q`.

Own elementary bookkeeping (change of variables and the chain rule).
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G1ZA1b

/-- Scale consistency of `coordChange y ψ Q` at all dilated test measures, from the PAIR-LIM
clause of `ChoiceRegularCore` (no `IsLQGGood` needed). -/
theorem g1za1b_scaleConsistent_of_core {γ : ℝ} {y : FieldSample} {ψ : ℂ → ℂ}
    (hcore : G1.ChoiceRegularCore γ y ψ) {b : ℝ} (hb : 0 < b) {c : ℝ} (hc : 0 < c)
    (ρ : TestFun H) (σ : ℂ → ℝ) (hσ : σ = ρ.1 ∨ σ = fun z => -ρ.1 z) :
    G1.ScaleConsistentAt (coordChange y ψ (Qc γ)) (Qc γ) b
      ((G1.tmeas σ).map fun z => (c : ℂ) * z) := by
  obtain ⟨hreg, -, hpair⟩ := hcore
  obtain ⟨hsm, hsc, hsH⟩ := ρ.2
  have hσc : Continuous σ ∧ HasCompactSupport σ ∧ tsupport σ ⊆ H := by
    rcases hσ with rfl | rfl
    · exact ⟨hsm.continuous, hsc, hsH⟩
    · exact ⟨hsm.continuous.neg, hsc.neg, by
        rw [show (fun z => -ρ.1 z) = -ρ.1 from rfl, tsupport_neg]; exact hsH⟩
  obtain ⟨hσ1, hσ2, hσ3⟩ := hσc
  have := G1.isFiniteMeasure_tmeas hσ1 hσ2
  have hbc : 0 < b * c := mul_pos hb hc
  have hmap : ((G1.tmeas σ).map fun z => (c : ℂ) * z).map (fun z => (b : ℂ) * z) =
      (G1.tmeas σ).map fun z => ((b * c : ℝ) : ℂ) * z := by
    rw [Measure.map_map (measurable_const_mul _) (measurable_const_mul _)]
    congr 1
    funext z
    simp only [Function.comp, Complex.ofReal_mul]
    ring
  obtain ⟨hi, L, hL⟩ := hpair (b * c) hbc ρ σ hσ
  refine G1.scaleConsistentAt_of_continuum hreg (Qc γ) hb
    (G1.ae_tmeas_map_mem_Hbar hσ1 hσ3 hc) (L := L) (fun s hs' => ?_) ?_
  · rw [hmap]; exact hi s hs'
  · rw [hmap]; exact hL

/-- **Area-only choice independence of the canonical data.** -/
theorem g1za1b_dataFull_canonical_rescale {γ : ℝ} (hγ : 0 < γ) {x : FieldSample}
    (hx : IsRegularSample x) {μ : Measure ℂ} (hμ : HasAreaLimit γ x μ) {b : ℝ} (hb : 0 < b)
    (hs : 0 < scaleParam γ x)
    (hsc : ∀ ρ : TestFun H, ∀ σ : ℂ → ℝ, (σ = ρ.1 ∨ σ = fun z => -ρ.1 z) →
      G1.ScaleConsistentAt x (Qc γ) b
        ((G1.tmeas σ).map fun z => ((scaleParam γ x / b : ℝ) : ℂ) * z)) :
    WedgeMeas.dataFull H (canonical γ (rescale x (Qc γ) b)) =
      WedgeMeas.dataFull H (canonical γ x) := by
  have h1 : CoordsFull.coordsFull (canonical γ (rescale x (Qc γ) b)) =
      CoordsFull.coordsFull (canonical γ x) := by
    unfold canonical
    rw [g1z2_scaleParam_rescale hx hγ hμ hb]
    have := S5.FieldShift.coordsFull_rescale_rescale hx (Qc γ) hb (div_pos hs hb)
    rwa [mul_div_cancel₀ _ hb.ne'] at this
  have h2 : ∀ ρ : TestFun H, pairRaw (canonical γ (rescale x (Qc γ) b)) ρ.1 =
      pairRaw (canonical γ x) ρ.1 := fun ρ => by
    unfold pairRaw
    rw [g1z2_canonical_rescale_apply hγ hx hμ hb hs _ (hsc ρ ρ.1 (Or.inl rfl)),
      g1z2_canonical_rescale_apply hγ hx hμ hb hs _ (hsc ρ _ (Or.inr rfl))]
  simp only [WedgeMeas.dataFull]
  exact Prod.ext h1 (funext h2)

/-- Pulling back along `F` a measure translated by a real `β` is pulling back along `F(· + β)`. -/
theorem g1za1b_coordChange_map_add (y : FieldSample) {F : ℂ → ℂ} (hF : Measurable F) (Q : ℝ)
    (μ : Measure ℂ) (β : ℝ) :
    coordChange y F Q (μ.map fun u => u + (β : ℂ)) =
      coordChange y (fun u => F (u + (β : ℂ))) Q μ := by
  have hadd : Measurable fun u : ℂ => u + (β : ℂ) := measurable_id.add_const _
  unfold coordChange
  rw [Measure.map_map hF hadd,
    integral_map hadd.aemeasurable (measurable_deriv F).norm.log.aestronglyMeasurable]
  congr 2
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [deriv_comp_add_const]

/-- **The translated new field is the pullback along the translated map.** -/
theorem g1za1b_regEq_translate (y X' : FieldSample) (Q : ℝ) {Φ G : ℂ → ℂ} (β : ℝ)
    (hG : Measurable G) (hEq : EqOn (fun u => Φ (u + (β : ℂ))) G H)
    (hN : ∀ e ∈ Hbar, ∀ r : ℝ, 0 < r →
      evalReg X' (foldedCircle e r) = coordChange y Φ Q (foldedCircle e r)) :
    RegEq (translate X' (β : ℂ)) (coordChange y G Q) := by
  set G' : ℂ → ℂ := fun w => G (w - (β : ℂ)) with hG'
  have hG'm : Measurable G' := hG.comp (measurable_id.sub_const _)
  have hΦ : EqOn Φ G' H := fun w hw => by
    have hw' : w - (β : ℂ) ∈ H := by
      show 0 < (w - (β : ℂ)).im
      have : 0 < w.im := hw
      simpa using this
    have := hEq hw'
    simp only [sub_add_cancel] at this
    simp only [hG', this]
  refine F1.regEq_of_fc_Hbar fun d hd r hr => ?_
  have hdβ : d + (β : ℂ) ∈ Hbar := by
    show 0 ≤ (d + (β : ℂ)).im
    have : 0 ≤ d.im := hd
    simpa using this
  show evalReg X' ((foldedCircle d r).map (· + (β : ℂ))) = _
  rw [IndepParams.fc_map_add_real, hN _ hdβ r hr,
    Cor15Group.coordChange_congr_H y hΦ Q (TwoPoint.foldedCircle_ae_mem_H _ hr),
    ← IndepParams.fc_map_add_real, g1za1b_coordChange_map_add y hG'm Q _ β]
  congr 1
  funext u
  simp only [hG', add_sub_cancel_right]

end G1ZA1b
end Thm18Asm
end QuantumZipper
