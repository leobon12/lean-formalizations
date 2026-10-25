import SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusAssembly.T57Assembly
import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.T58c
import SupercriticalLQGUniqueness.Uniqueness.Objects.CentreZero.Shape
import SupercriticalLQGUniqueness.Uniqueness.Objects.CentreZero.RN
import SupercriticalLQGUniqueness.Uniqueness.Objects.TubeBridge.ForwardTube




 
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusAssembly
open LQGMetric (DistC)

 



def radiusInputs_of_mesh
    {Ω : Type} [MeasurableSpace Ω] (Pμ : Measure Ω) (h : Ω → DistC)
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {cMinus cPlus : ℝ≥0∞}
    {Kann p0 : ℝ} (pbar : Set.Ioo (0 : ℝ) 1)
    (t : Objects.Density.T58Table ξ Q cMinus.toReal cPlus.toReal Kann p0 pbar)
    (r : Set.Ioi (0 : ℝ)) (D D' : DistC → LSCMetric)
    (Pt : Objects.Tube.TubeParams) (S : Objects.TubeMesh.TubeSelection (t.toConstants r) Pt)
    (ρ₀ : ℝ) (X : Finset ℂ)
    (hData : Objects.CorrectedEvent.DataMatch (t.toConstants r)
      (Objects.TubeBridge.tubeDataOf (t.toConstants r) Pt
        S.good
        (S.small (t.sup_lt_set.trans t.set_lt_nar)).1 ρ₀ X))
    (Target : Set DistC)
    (hEvent : ∀ g ∈ Target,
      Objects.CorrectedEvent.correctedEvent (t.toConstants r)
        (Objects.TubeBridge.tubeDataOf (t.toConstants r) Pt
          S.good
          (S.small (t.sup_lt_set.trans t.set_lt_nar)).1 ρ₀ X)
        hData
        (Objects.Excursions.blockEvent (t.toConstants r)
          (Objects.TubeBridge.tubeDataOf (t.toConstants r) Pt
            S.good
            (S.small (t.sup_lt_set.trans t.set_lt_nar)).1 ρ₀ X)
          t.K_sh (Objects.Density.Cmid0 cMinus.toReal cPlus.toReal) D D') D D' g)
    (hGood : ∀ g ∈ Target,
      Objects.Producer.LocalGood ξ D D'
        (range (Objects.CorrectedEvent.site (Objects.TubeBridge.tubeDataOf (t.toConstants r) Pt
          S.good
          (S.small (t.sup_lt_set.trans t.set_lt_nar)).1 ρ₀ X))) ∅ g)
    (hComp : ∀ g ∈ Target, ∀ x y : ℂ,
      D' g (x, y) ≤ ENNReal.ofReal cPlus.toReal * D g (x, y))
    (hInner : ∀ g ∈ Target,
      Objects.CorrectedEvent.ambientAcross (D g) 0 (r : ℝ) (1.5 * (r : ℝ)) =
        Objects.CorrectedEvent.acr (D g) 0 (r : ℝ) (1.5 * (r : ℝ)))
    (hOuter : ∀ g ∈ Target,
      Objects.CorrectedEvent.ambientAcross (D g) 0 (2.5 * (r : ℝ)) (3 * (r : ℝ)) =
        Objects.CorrectedEvent.acr (D g) 0 (2.5 * (r : ℝ)) (3 * (r : ℝ)))
    (hEnergy : LQGMetric.gradEnergy
      (Objects.TubeBridge.tubeDataOf (t.toConstants r) Pt
        S.good
        (S.small (t.sup_lt_set.trans t.set_lt_nar)).1 ρ₀ X).bump ≤ t.E_max)
    (L : ℂ → Set DistC)
    (L_local : ∀ z : ℂ, @MeasurableSet DistC
      (LQGMetric.Blueprint.fieldSigmaClosed0 (id : DistC → DistC)
        {x : ℂ | r ≤ dist x z ∧ dist x z ≤ 4 * (r : ℝ)}) (L z))
    (L_null : ∀ z : ℂ, (Pμ.map h) (L z \ Objects.Producer.centreTarget Target z) = 0)
    (L_prob : ∀ z : ℂ, ENNReal.ofReal (pbar : ℝ) ≤ (Pμ.map h) (L z)) :
    Objects.Producer.RadiusInputs Pμ h D D' ξ Q (EndSaving.Interfaces.midpoint cMinus cPlus) t.params pbar r := by
  let C := t.toConstants r
  let hSmall := (S.small (t.sup_lt_set.trans t.set_lt_nar)).1
  let T := Objects.TubeBridge.tubeDataOf C Pt S.good hSmall ρ₀ X
  let U₀ := Objects.CentreZero.uZero Pt S.good C.r C.A_sup C.rPos C.supPos hSmall
  let V₀ := Objects.CentreZero.vZero Pt S.good C.r C.A_sup C.rPos C.supPos hSmall
  let f₀ := Objects.CentreZero.fZero Pt S.good C.r C.A_sup C.A_max C.rPos C.supPos hSmall
  have hTube : Objects.CorrectedEvent.tubeSet T ⊆ (U₀ : Set ℂ) :=
    Objects.TubeBridge.tubeDataOf_tube_sub C Pt S.good hSmall ρ₀ X S.widthEq
  have hV : (V₀ : Set ℂ) = Objects.CorrectedEvent.tubeV T C.A_sup := by
    rw [Objects.TubeBridge.tubeDataOf_tubeV_eq C Pt S.good hSmall ρ₀ X S.widthEq]
    ext x
    change x ∈ Pt.nbhdAt C.r C.A_sup 0 ↔ x ∈ Pt.nbhd C.r C.A_sup
    rw [Objects.Tube.TubeParams.mem_nbhdAt, sub_zero]
  have hBump : f₀ = T.bump :=
    Objects.TubeBridge.fZero_eq_tubeDataOf_bump C Pt S.good hSmall ρ₀ X
  have hT57 : Objects.Producer.T57Inputs D D' ξ Q (EndSaving.Interfaces.midpoint cMinus cPlus) t.params r U₀ V₀
      (LQGMetric.testCont f₀) Target := by
    rw [hBump]
    exact t57Inputs_of_table t r D D' U₀ V₀ Target T hData hEvent hGood hComp hTube hV
  have hBounds : ∀ g ∈ Target, Objects.Producer.BoundsAt D ξ Q t.params 0 r U₀ V₀ g := by
    intro g hg
    have hMetric := (hGood g hg).1
    have hLength : (D g).IsLengthSpace := hMetric.1.1
    have hBarrier : BiLipschitz.Barrier.Barrier (D g) := hMetric.2
    have hForget := BiLipschitz.Barrier.continuous_forget_of_barrier (D g) hBarrier hLength
    exact Objects.TubeMesh.boundsAt_of_selected_mesh C Pt S (t.sup_lt_set.trans t.set_lt_nar)
      ρ₀ X hData (hEvent g hg) hLength hForget (hInner g hg) (hOuter g hg)
      (fun γ a b hγ _ => BiLipschitz.Barrier.continuousOn_of_barrier_of_length (D g) hBarrier hLength hγ)
      rfl rfl rfl
  have hRN : ∀ g ∈ Target,
      t.params.Crn⁻¹ ≤ LQGMetric.cmDensity f₀ (LQGMetric.pair0 g) ∧
      LQGMetric.cmDensity f₀ (LQGMetric.pair0 g) ≤ t.params.Crn :=
    by
      intro g hg
      rw [hBump]
      exact Objects.CentreZero.rn_of_corrected_event (hEvent g hg) hEnergy rfl
  exact {
    U₀ := U₀
    V₀ := V₀
    f₀ := f₀
    U_annular := Objects.CentreZero.uZero_annular Pt S.good C.r C.A_sup C.rPos C.supPos hSmall
    V_annular := Objects.CentreZero.vZero_annular Pt S.good C.r C.A_sup C.rPos C.supPos hSmall
    closure_U_V := Objects.CentreZero.closure_uZero_vZero Pt S.good C.r C.A_sup C.rPos C.supPos hSmall
    closure_V_annulus := Objects.CentreZero.closure_vZero_annulus Pt S.good C.r C.A_sup C.rPos C.supPos hSmall
    f_nonneg := Objects.CentreZero.fZero_nonneg Pt S.good C.r C.A_sup C.A_max C.rPos C.supPos hSmall C.maxPos.le
    f_le := Objects.CentreZero.fZero_le Pt S.good C.r C.A_sup C.A_max C.rPos C.supPos hSmall C.maxPos.le
    f_on_U := fun x hx => Objects.CentreZero.fZero_on_uZero Pt S.good C.r C.A_sup C.A_max C.rPos C.supPos hSmall hx
    f_off_V := fun x hx => Objects.CentreZero.fZero_off_vZero Pt S.good C.r C.A_sup C.A_max C.rPos C.supPos hSmall hx
    Target := Target
    bounds := hBounds
    rn := hRN
    t57 := hT57
    L := L
    L_local := L_local
    L_null := L_null
    L_prob := L_prob }

end SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusAssembly
