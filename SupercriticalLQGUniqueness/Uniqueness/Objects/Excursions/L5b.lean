import SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions.L5




 









set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Real
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions

open SupercriticalLQGUniqueness.Uniqueness.Objects.Tube

 
def WindowAt (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (V : Set ℂ) (P : ℝ → ℂ) (τ σ : ℝ) (c : ℂ)
    (a b : ℝ) : Prop :=
  τ ≤ a ∧ a < b ∧ b ≤ σ ∧ ‖P a - c‖ = T.blockRadius + C.A_sup * C.r ∧
    ‖P b - c‖ = T.blockRadius + C.A_sup * C.r ∧ T.blockRadius / 8 ≤ dist (P a) (P b) ∧
    (∀ t ∈ Icc a b, P t ∈ ball c (T.blockRadius + C.A_sup * C.r + C.A_nar * C.r)) ∧
    (∀ t ∈ Ioo a b, P t ∈ V → P t ∈ ball c (T.blockRadius + C.A_sup * C.r))

variable {C : Objects.CorrectedEvent.Constants} {T : Objects.CorrectedEvent.TubeData} {hData : Objects.CorrectedEvent.DataMatch C T}
  {F : ℂ → LQGMetric.DistC → Prop} {D D' : LQGMetric.DistC → LSCMetric} {g : LQGMetric.DistC}
  {Db : LSCMetric} {f : C(ℂ, ℝ)} {V : TopologicalSpace.Opens ℂ} {P : ℝ → ℂ} {L τ' τ σ σ' : ℝ}

 
theorem l5_windows (S : ExcSetting C (D g) Db f V P L τ' τ σ σ')
    (hev : Objects.CorrectedEvent.correctedEvent C T hData F D D' g)
    (hV : (V : Set ℂ) = Objects.CorrectedEvent.tubeV T C.A_sup)
    {N : ℝ} (hN : 0 < N) (hNe : Objects.CorrectedEvent.normalizer C g C.r 0 = ENNReal.ofReal N)
    (hlam : C.lamConst < 1 / 10 ^ 100) (hAloc : 3 < C.A_loc) (hKann : 3 / 4 < C.K_ann)
    (hendpt : C.A_endpt ≤ C.lamConst * (1 - C.K_ann) ^ 2)
    (hrho2 : C.ρ ≤ 10 * C.lamConst ^ 2 / (Real.pi ^ 2 * C.A_loc ^ 2))
    (hsep : C.A_sp * C.r ≤ dist (P τ) (P σ))
    (hL3 : σ - τ ≤ 3 * C.lamConst * C.A_nar ^ (C.ξ * (C.Q + 3)) * N) :
    ∃ k : Fin T.K, F (Objects.CorrectedEvent.site T k) g ∧
      (∃ a b, WindowAt C T V P τ σ (Objects.CorrectedEvent.innerCenter T k) a b) ∧
      (∃ a b, WindowAt C T V P τ σ (Objects.CorrectedEvent.outerCenter T k) a b) := by
  obtain ⟨hr, hρ, hl, hE, hα, hK, hn4, -, -, hlo, -⟩ := dataMatch_basic hData
  have hbr0 : 0 ≤ T.blockRadius :=
    le_trans (mul_nonneg (mul_nonneg C.endptPos.le C.rhoPos.le) C.rPos.le) hlo
  have hGood := good_toParams hData hlam hAloc hKann hendpt hrho2
  set Pm := toParams T with hPm
  have hr0 : 0 < T.r := hr ▸ C.rPos
  have hρr : T.rho * T.r ≠ 0 := by rw [hρ, hr]; exact (mul_pos C.rhoPos C.rPos).ne'
  have hn : ‖T.orientation‖ = 1 := Objects.Producer.norm_orientation hn4
  have hsp23 : Objects.CorrectedEvent.sPrime T ≤ 2 / 3 := by
    have h1 := hGood.sp_le; have h2 := hGood.α_gt
    change 100 * Objects.CorrectedEvent.sPrime T ≤ 1 - T.alpha at h1
    change 3 / 4 < T.alpha at h2
    linarith
  have hpos : 0 ≤ T.alpha - 3 * Objects.CorrectedEvent.sPrime T / 4 := by
    have h1 := hGood.sp_le; have h2 := hGood.α_gt; have h3 := hGood.sp_pos
    change 100 * Objects.CorrectedEvent.sPrime T ≤ 1 - T.alpha at h1
    change 3 / 4 < T.alpha at h2
    linarith
  have hVn : (V : Set ℂ) = Pm.nbhd T.r C.A_sup := by
    rw [hV, tubeV_eq T hn hsp23 hpos hρr]
  
  have hsmall := TubeParams.small_of_DG Pm (lam := C.lamConst) (Aendpt := C.A_endpt)
    (Anar := C.A_nar) (Asup := C.A_sup) C.lamPos hlam hGood.α_gt C.endptPos
    (sPrime_bounds hData).1 hGood.ρ_pos C.supPos (C.supLtSet.trans C.setLtNar)
    (by simp only [hPm, toParams]; rw [hα, hρ]; exact C.narLe)
  have hρAsp : 10 ^ 4 * Pm.ρ ≤ C.A_sp :=
    TubeParams.rho_Asp_of_DG hlam C.spPos (by simp only [hPm, toParams]; rw [hρ]; exact C.rhoLt)
  have hEv := eevent_of_S4 hData (Objects.CorrectedEvent.event_block_arcs hev)
  have hlam3 : 3 * C.lamConst < 1 := by linarith [C.lamPos]
  have ha : 0 < C.ξ * (C.Q + 3) := mul_pos C.ξPos (by linarith [C.QPos])
  have hτcl : P τ ∈ closure (Pm.nbhd T.r C.A_sup) := hVn ▸ S.τ_mem_cl
  have hσcl : P σ ∈ closure (Pm.nbhd T.r C.A_sup) := hVn ▸ S.σ_mem_cl
  have hC6 : ∀ s t, τ ≤ s → s ≤ t → t ≤ σ → (∀ u ∈ Icc s t, P u ∉ Pm.nbhd T.r C.A_sup) →
      (∀ u ∈ Icc s t, P u ∈ {x : ℂ | 3 / 2 * T.r < ‖x‖ ∧ ‖x‖ < 3 * T.r}) →
      dist (P s) (P t) ≤ C.lamConst⁻¹ * (C.A_nar * T.r) →
      (dist (P s) (P t) / T.r) ^ (C.ξ * (C.Q + 3)) * N ≤ t - s := by
    intro s t hs hst ht hoff hW hwin
    rw [hr] at hW hwin ⊢
    exact c6_time S hev hNe s t hs hst ht (fun u hu => hVn ▸ hoff u hu) hW hwin
  obtain ⟨k, hFk, hwin⟩ := TubeParams.T55_conditional (P := Pm) (r := T.r) (Asup := C.A_sup)
    hGood hr0 C.supPos hsmall.1 hρAsp hEv (Q := P) S.τ_le_σ
    (S.cont_sub S.τ'_le_τ S.σ_le_σ') hτcl hσcl (by rw [hr]; exact hsep) C.narPos hsmall.2 hN ha
    C.lamPos hlam3 hC6 hL3
  
  obtain ⟨kf, m, hkm⟩ := exists_fin_of_int T k
  have hKne : (Pm.K : ℝ) ≠ 0 := by simp only [hPm, toParams]; exact_mod_cast T.Kpos.ne'
  have hsite : Pm.site T.r k = Objects.CorrectedEvent.site T kf := by
    rw [hkm, site_add_K_mul Pm T.r hKne, site_eq]
  have huC : Pm.uC T.r k = Objects.CorrectedEvent.innerCenter T kf := by
    rw [innerCenter_eq, TubeParams.uC, TubeParams.uC, hkm, modMap_add_K_mul Pm T.r hKne]
  have hvC : Pm.vC T.r k = Objects.CorrectedEvent.outerCenter T kf := by
    rw [outerCenter_eq, TubeParams.vC, TubeParams.vC, hkm, modMap_add_K_mul Pm T.r hKne]
  have hs : Pm.s T.r = T.blockRadius := s_eq T hρr
  refine ⟨kf, hsite ▸ hFk, ?_, ?_⟩
  · obtain ⟨a, b, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hwin (Pm.uC T.r k) (by simp)
    rw [huC, hs] at h4 h5 h7 h8
    rw [hr] at h4 h5 h7
    rw [hs] at h6
    refine ⟨a, b, h1, h2, h3, by rw [← dist_eq_norm]; exact h4, by rw [← dist_eq_norm]; exact h5,
      by linarith [h6, hbr0], ?_, ?_⟩
    · intro t ht
      rw [mem_ball]
      have := h7 t ht
      linarith
    · intro t ht hVt
      have := h8 t ht (hVn ▸ hVt)
      rwa [hr] at this
  · obtain ⟨a, b, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hwin (Pm.vC T.r k) (by simp)
    rw [hvC, hs] at h4 h5 h7 h8
    rw [hr] at h4 h5 h7
    rw [hs] at h6
    refine ⟨a, b, h1, h2, h3, by rw [← dist_eq_norm]; exact h4, by rw [← dist_eq_norm]; exact h5,
      by linarith [h6, hbr0], ?_, ?_⟩
    · intro t ht
      rw [mem_ball]
      have := h7 t ht
      linarith
    · intro t ht hVt
      have := h8 t ht (hVn ▸ hVt)
      rwa [hr] at this

end SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions
