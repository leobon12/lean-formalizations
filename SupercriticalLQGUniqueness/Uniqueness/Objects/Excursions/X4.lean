import SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions.X3
import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.L5
import SupercriticalLQGUniqueness.Uniqueness.Objects.Splice.C6Continuum




 











set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions

variable {C : Objects.CorrectedEvent.Constants} {T : Objects.CorrectedEvent.TubeData} {hData : Objects.CorrectedEvent.DataMatch C T}
  {F : ℂ → LQGMetric.DistC → Prop} {D D' : LQGMetric.DistC → LSCMetric} {g : LQGMetric.DistC}
  {Db : LSCMetric} {f : C(ℂ, ℝ)} {V : TopologicalSpace.Opens ℂ} {P : ℝ → ℂ} {L τ' τ σ σ' : ℝ}

 
def midAnn (C : Objects.CorrectedEvent.Constants) : Set ℂ := {x : ℂ | 3 / 2 * C.r < ‖x‖ ∧ ‖x‖ < 3 * C.r}

theorem mem_ann_of_midAnn {x : ℂ} (hx : x ∈ midAnn C) : x ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r) := by
  change 1.5 * C.r < dist x 0 ∧ dist x 0 < 3 * C.r
  rw [dist_zero_right]
  exact ⟨by have := hx.1; norm_num at this ⊢; linarith, hx.2⟩

 
theorem c6_time (S : ExcSetting C (D g) Db f V P L τ' τ σ σ')
    (hev : Objects.CorrectedEvent.correctedEvent C T hData F D D' g) {N : ℝ}
    (hNe : Objects.CorrectedEvent.normalizer C g C.r 0 = ENNReal.ofReal N) :
    ∀ s t, τ ≤ s → s ≤ t → t ≤ σ → (∀ u ∈ Icc s t, P u ∉ (V : Set ℂ)) →
      (∀ u ∈ Icc s t, P u ∈ midAnn C) →
      dist (P s) (P t) ≤ C.lamConst⁻¹ * (C.A_nar * C.r) →
      (dist (P s) (P t) / C.r) ^ (C.ξ * (C.Q + 3)) * N ≤ t - s := by
  intro s t hs hst ht hoff hW hwin
  have hr := C.rPos
  have hz := mem_ann_of_midAnn (hW s ⟨le_rfl, hst⟩)
  have hw := mem_ann_of_midAnn (hW t ⟨hst, le_rfl⟩)
  have hwindow : dist (P s) (P t) ≤ C.A_nar / C.lamConst * C.r := by
    have : C.A_nar / C.lamConst * C.r = C.lamConst⁻¹ * (C.A_nar * C.r) := by ring
    rw [this]; exact hwin
  have h6 := Objects.Splice.event_narrow_continuum hev hz hw hwindow
  have h0s : 0 ≤ s := S.τ'_nonneg.trans (S.τ'_le_τ.trans hs)
  have htL : t ≤ L := ht.trans (S.σ_le_σ'.trans S.σ'_le_L)
  have hcurve : (D g).IsCurve P s t := S.isCurve h0s hst htL
  have hint := BiLipschitz.Barrier.internal_le_len' (D g) hcurve
    (fun u hu => Objects.Splice.large_ann_subset C (mem_ann_of_midAnn (hW u hu)))
  have hlen := S.len_eq_of_off h0s hst htL hoff
  have hchain := h6.trans (hint.trans_eq hlen)
  rw [hNe, ← ENNReal.ofReal_mul (by positivity)] at hchain
  exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp hchain

 
theorem x4_tube (S : ExcSetting C (D g) Db f V P L τ' τ σ σ')
    (hev : Objects.CorrectedEvent.correctedEvent C T hData F D D' g) {N : ℝ} (hN : 0 < N)
    (hNe : Objects.CorrectedEvent.normalizer C g C.r 0 = ENNReal.ofReal N)
    (hloc : ∀ x y, y ∈ closure (V : Set ℂ) → dist x y ≤ C.A_nar * C.r → x ∈ midAnn C)
    (hlam3 : 3 * C.lamConst < 1)
    (hL3 : σ - τ ≤ 3 * C.lamConst * C.A_nar ^ (C.ξ * (C.Q + 3)) * N) :
    ∀ x ∈ Icc τ σ, P x ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r) := by
  have ha : 0 < C.ξ * (C.Q + 3) := mul_pos C.ξPos (by linarith [C.QPos])
  have hL4 := Objects.Tube.L4_of_L3_C6 (S.cont_sub S.τ'_le_τ S.σ_le_σ') V.isOpen S.τ_mem_cl C.rPos C.narPos
    hN ha C.lamPos hlam3 hloc (c6_time S hev hNe) hL3
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hL4.1 x hx
  exact mem_ann_of_midAnn (hloc _ y hy hxy.le)

end SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions
