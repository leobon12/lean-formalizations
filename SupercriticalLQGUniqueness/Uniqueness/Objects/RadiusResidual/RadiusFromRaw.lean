import SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusAssembly.RadiusAssembly
import SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusResidual.TargetRegularity
import SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusResidual.EnergyScale




 


set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusResidual
open LQGMetric (DistC)

 


def radiusInputs_of_raw
    {Ω : Type} [MeasurableSpace Ω] (Pμ : Measure Ω) (h : Ω → DistC)
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {cMinus cPlus : ℝ≥0∞}
    {Kann p0 : ℝ} (pbar : Set.Ioo (0 : ℝ) 1)
    (t : Objects.Density.T58Table ξ Q cMinus.toReal cPlus.toReal Kann p0 pbar)
    (r : Set.Ioi (0 : ℝ)) (D D' : DistC → LSCMetric)
    (Pt : Objects.Tube.TubeParams) (S : Objects.TubeMesh.TubeSelection (t.toConstants r) Pt)
    (ρ₀ : ℝ) (X : Finset ℂ)
    (hData : Objects.CorrectedEvent.DataMatch (t.toConstants r)
      (Objects.TubeBridge.tubeDataOf (t.toConstants r) Pt S.good
        (S.small (t.sup_lt_set.trans t.set_lt_nar)).1 ρ₀ X))
    (E : Set DistC)
    (hEvent : ∀ g ∈ E,
      Objects.CorrectedEvent.correctedEvent (t.toConstants r)
        (Objects.TubeBridge.tubeDataOf (t.toConstants r) Pt S.good
          (S.small (t.sup_lt_set.trans t.set_lt_nar)).1 ρ₀ X)
        hData
        (Objects.Excursions.blockEvent (t.toConstants r)
          (Objects.TubeBridge.tubeDataOf (t.toConstants r) Pt S.good
            (S.small (t.sup_lt_set.trans t.set_lt_nar)).1 ρ₀ X)
          t.K_sh (Objects.Density.Cmid0 cMinus.toReal cPlus.toReal) D D') D D' g)
    (hUnitEnergy : LQGMetric.gradEnergy
      (Pt.bumpTest 1 (t.toConstants r).A_max
        ⟨(t.toConstants r).A_sup, (t.toConstants r).supPos⟩ S.good
        (by norm_num) (S.small (t.sup_lt_set.trans t.set_lt_nar)).1) ≤ t.E_max)
    (L : ℂ → Set DistC)
    (L_local : ∀ z : ℂ, @MeasurableSet DistC
      (LQGMetric.Blueprint.fieldSigmaClosed0 (id : DistC → DistC)
        {x : ℂ | r ≤ dist x z ∧ dist x z ≤ 4 * (r : ℝ)}) (L z))
    (L_null : ∀ z : ℂ, (Pμ.map h)
      (L z \ Objects.Producer.centreTarget (regularizedTarget ξ D D'
        (Objects.TubeBridge.tubeDataOf (t.toConstants r) Pt S.good
          (S.small (t.sup_lt_set.trans t.set_lt_nar)).1 ρ₀ X)
        cPlus E) z) = 0)
    (L_prob : ∀ z : ℂ, ENNReal.ofReal (pbar : ℝ) ≤ (Pμ.map h) (L z)) :
    Objects.Producer.RadiusInputs Pμ h D D' ξ Q (EndSaving.Interfaces.midpoint cMinus cPlus) t.params pbar r := by
  let C := t.toConstants r
  let hSmall := (S.small (t.sup_lt_set.trans t.set_lt_nar)).1
  let T := Objects.TubeBridge.tubeDataOf C Pt S.good hSmall ρ₀ X
  let Target := regularizedTarget ξ D D' T cPlus E
  have hEvent' : ∀ g ∈ Target,
      Objects.CorrectedEvent.correctedEvent C T hData
        (Objects.Excursions.blockEvent C T t.K_sh
          (Objects.Density.Cmid0 cMinus.toReal cPlus.toReal) D D') D D' g := by
    intro g hg
    exact hEvent g (regularizedTarget_event hg)
  have hGood : ∀ g ∈ Target,
      Objects.Producer.LocalGood ξ D D' (range (Objects.CorrectedEvent.site T)) ∅ g := by
    intro g hg
    exact regularizedTarget_good hg
  have hComp : ∀ g ∈ Target, ∀ x y : ℂ,
      D' g (x, y) ≤ ENNReal.ofReal cPlus.toReal * D g (x, y) := by
    intro g hg
    exact regularizedTarget_comp hg
  have hInner : ∀ g ∈ Target,
      Objects.CorrectedEvent.ambientAcross (D g) 0 (r : ℝ) (1.5 * (r : ℝ)) =
        Objects.CorrectedEvent.acr (D g) 0 (r : ℝ) (1.5 * (r : ℝ)) := by
    intro g hg
    exact (regularizedTarget_crossings r hg).1
  have hOuter : ∀ g ∈ Target,
      Objects.CorrectedEvent.ambientAcross (D g) 0 (2.5 * (r : ℝ)) (3 * (r : ℝ)) =
        Objects.CorrectedEvent.acr (D g) 0 (2.5 * (r : ℝ)) (3 * (r : ℝ)) := by
    intro g hg
    exact (regularizedTarget_crossings r hg).2
  have hEnergy : LQGMetric.gradEnergy T.bump ≤ t.E_max := by
    rw [gradEnergy_tubeDataOf_eq_unit C Pt S.good hSmall ρ₀ X]
    exact hUnitEnergy
  exact Objects.RadiusAssembly.radiusInputs_of_mesh Pμ h pbar t r D D' Pt S ρ₀ X hData
    Target hEvent' hGood hComp hInner hOuter hEnergy L L_local L_null L_prob

end SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusResidual
