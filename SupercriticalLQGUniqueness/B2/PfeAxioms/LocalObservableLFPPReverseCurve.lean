import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableLFPPBudget
import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaUnitSpeed

 

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped ENNReal
open LQGMetric LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem lfppDOn_le_len_of_lfpp_curve
    (ξ : ℝ) (φ : C(ℂ, ℝ)) {U : Set ℂ} (hU : IsOpen U)
    {P : ℝ → ℂ} {a b : ℝ}
    (hP : (PfeWeyl.lfppLSCMetric ξ φ).IsCurve P a b)
    (htrace : ∀ t ∈ Icc a b, P t ∈ U) :
    lfppDOn ξ φ U (P a) (P b) ≤
      (PfeWeyl.lfppLSCMetric ξ φ).len P a b := by
  let E := PfeWeyl.lfppLSCMetric ξ φ
  let C := lfppContMetric ξ φ φ.continuous
  by_cases hfinite : E.len P a b = ∞
  · change lfppDOn ξ φ U (P a) (P b) ≤ E.len P a b
    rw [hfinite]
    exact le_top
  have hfinite' : E.len P a b ≠ ∞ := hfinite
  obtain ⟨Q, hQ, hunit, hQ0, hQL, hQU, hQlen⟩ :=
    exists_unit_speed_buffered_curve E hP htrace hfinite'
  let L := (E.len P a b).toReal
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  let f : E.Space → C.Space := id
  have hf : Isometry f := by
    intro x y
    exact (PfeWeyl.edist_lfppLSCMetric_eq_cont ξ φ x y).symm
  have hQc : ContinuousOn Q (Icc 0 L) := by
    exact (continuous_weylToC C).comp_continuousOn
      (hf.continuous.comp_continuousOn hQ.2)
  let K : Set ℂ := Q '' Icc 0 L
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hQc
  have hKne : K.Nonempty := ⟨Q 0, 0, ⟨le_rfl, hL⟩, rfl⟩
  have hKU : K ⊆ U := by
    rintro z ⟨t, ht, rfl⟩
    exact hQU t ht
  obtain ⟨r, hr, m, hm, hball⟩ :=
    exists_uniform_lfpp_ball_data φ.continuous hK hKne hU hKU
  have hmain : ∀ η : ℝ, 0 < η →
      lfppDOn ξ φ U (Q 0) (Q L) ≤ ENNReal.ofReal (L + η) := by
    intro η hη
    obtain ⟨N, hδ, hbudget⟩ := exists_lfpp_mesh_budget hL hm hr hη
    have hmesh := lfppDOn_le_of_unitSpeed_mesh ξ φ hL hunit
      (show ∀ t ∈ Icc 0 L, Q t ∈ K from
        fun t ht => ⟨t, ht, rfl⟩) hr hm.le hδ hball N hbudget.le
    exact hmesh.trans_eq (lfpp_mesh_total_eq N hL hη.le)
  rw [← hQ0, ← hQL]
  have hlen : ENNReal.ofReal L = E.len P a b := ENNReal.ofReal_toReal hfinite'
  calc
    lfppDOn ξ φ U (Q 0) (Q L) ≤ ENNReal.ofReal L := by
      refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
      have h := hmain (ε : ℝ) (by exact_mod_cast hε)
      rwa [ENNReal.ofReal_add hL (by exact_mod_cast hε.le),
        ENNReal.ofReal_coe_nnreal] at h
    _ = E.len P a b := hlen

end SupercriticalLQGUniqueness.B2.PfeAxioms
