import SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusAssembly.TubeData
import SupercriticalLQGUniqueness.Uniqueness.Objects.Density.T57
import SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions.Witness




 
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusAssembly
open LQGMetric (DistC)

 


def t57Inputs_of_table
    {ξ : Set.Ioi (0 : ℝ)} {Q cm cp Kann p0 pbar : ℝ}
    (t : Objects.Density.T58Table ξ Q cm cp Kann p0 pbar) (r : Set.Ioi (0 : ℝ))
    (D D' : DistC → LSCMetric) (U₀ V₀ : TopologicalSpace.Opens ℂ)
    (Target : Set DistC) (T : Objects.CorrectedEvent.TubeData)
    (hData : Objects.CorrectedEvent.DataMatch (t.toConstants r) T)
    (hEvent : ∀ g ∈ Target,
      Objects.CorrectedEvent.correctedEvent (t.toConstants r) T hData
        (Objects.Excursions.blockEvent (t.toConstants r) T t.K_sh (Objects.Density.Cmid0 cm cp) D D') D D' g)
    (hGood : ∀ g ∈ Target,
      Objects.Producer.LocalGood ξ D D' (range (Objects.CorrectedEvent.site T)) ∅ g)
    (hComp : ∀ g ∈ Target, ∀ x y : ℂ,
      D' g (x, y) ≤ ENNReal.ofReal cp * D g (x, y))
    (hTube : Objects.CorrectedEvent.tubeSet T ⊆ (U₀ : Set ℂ))
    (hV : (V₀ : Set ℂ) = Objects.CorrectedEvent.tubeV T (t.toConstants r).A_sup) :
    Objects.Producer.T57Inputs D D' ξ Q (Objects.Density.Cmid cm cp) t.params r U₀ V₀ (LQGMetric.testCont T.bump) Target := by
  have hTiny : (t.toConstants r).lamConst < 1 / 10 ^ 100 := by
    change t.lam < 1 / 10 ^ 100
    have h := t.lam_lt_tiny
    norm_num at h ⊢
    exact h
  have hLoc : 3 < (t.toConstants r).A_loc := (tubeSelection t r).locGt
  have hReg : (t.toConstants r).c_reg⁻¹ ^ 2 *
      (1 + (t.toConstants r).c_reg) ^ 3 * (2 : ℝ) ^ (2 * Objects.Excursions.theta (t.toConstants r)) *
      ((2 : ℝ) ^ (-((t.toConstants r).k0 : ℝ))) ^ Objects.Excursions.theta (t.toConstants r) ≤ 1 := by
    simpa only [Objects.Excursions.theta, Objects.Density.T58Table.toConstants, Objects.Density.regExp, Objects.Density.epScale, inv_pow] using t.reg_ep
  have hSp : 4 * (t.toConstants r).A_sp ^ Objects.Excursions.theta (t.toConstants r) *
      (t.toConstants r).A_around <
      (t.toConstants r).A_across ^ 2 / (16 * (t.toConstants r).A_around) := by
    simpa only [Objects.Excursions.theta, Objects.Density.T58Table.toConstants, Objects.Density.regExp] using t.sp_loop
  have hSet : 4 * (2 * (t.toConstants r).A_set) ^ Objects.Excursions.theta (t.toConstants r) *
      (t.toConstants r).A_around ≤
      (t.toConstants r).lamConst * (t.toConstants r).A_nar ^
        ((t.toConstants r).ξ * ((t.toConstants r).Q + 3)) := by
    simpa only [Objects.Excursions.theta, Objects.Density.T58Table.toConstants, Objects.Density.regExp] using t.set_loop
  exact Objects.Excursions.mkT57Inputs (t.toConstants r) T hData t.K_sh (Objects.Density.Cmid0 cm cp)
    rfl rfl rfl rfl rfl hEvent hGood cp (t.cm_pos.trans t.cm_lt_cp) hComp
    (Objects.Density.Cmid0_pos t.cm_pos t.cm_lt_cp).le
    ((Objects.Density.Cmid0_pos t.cm_pos t.cm_lt_cp).trans (Objects.Density.Cmid0_lt_Cmid t.cm_lt_cp)).le
    t.ratio t.Kann_nonneg t.endpt_le_one t.lam_le
    (t.toConstants_count r (Objects.Density.blockRadius_ge_of_dataMatch hData))
    hTube (t.toConstants_relations r).2.2.2.1 hV hTiny hLoc t.Kann_gt t.endpt_a t.ρ_tube
    hReg hSp hSet t.max_across t.max_nar (le_of_eq t.params_Ctime.symm)

end SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusAssembly
