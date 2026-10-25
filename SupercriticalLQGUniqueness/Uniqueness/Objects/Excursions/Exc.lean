import SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions.Base




 


















set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions

 
structure ExcSetting (C : Objects.CorrectedEvent.Constants) (D Db : LSCMetric) (f : C(ℂ, ℝ))
    (V : TopologicalSpace.Opens ℂ) (P : ℝ → ℂ) (L τ' τ σ σ' : ℝ) : Prop where
  forget : Continuous (BiLipschitz.Barrier.forget D)
  length : D.IsLengthSpace
  weyl : ∀ x y : ℂ, Db (x, y) = weylScale C.ξ (-f) D (x, y)
  f_bd : ∀ x : ℂ, 0 ≤ f x ∧ f x ≤ C.A_max
  f_off : ∀ x ∉ (V : Set ℂ), f x = 0
  V_loc : closure (V : Set ℂ) ⊆ {x : ℂ | 3 / 2 * C.r < ‖x‖ ∧ ‖x‖ < 5 / 2 * C.r}
  geo : EndSaving.Interfaces.BumpedGeodesic Db P L
  exc : EndSaving.Interfaces.Excursion P L (ball (0 : ℂ) (4 * C.r)) V τ' τ σ σ'

namespace ExcSetting

variable {C : Objects.CorrectedEvent.Constants} {D Db : LSCMetric} {f : C(ℂ, ℝ)} {V : TopologicalSpace.Opens ℂ}
  {P : ℝ → ℂ} {L τ' τ σ σ' : ℝ}

theorem r_pos (_S : ExcSetting C D Db f V P L τ' τ σ σ') : 0 < C.r := C.rPos

theorem frontier_ball4 : frontier (ball (0 : ℂ) (4 * C.r)) = sphere 0 (4 * C.r) :=
  frontier_ball 0 (by linarith [C.rPos])

theorem norm_τ' (S : ExcSetting C D Db f V P L τ' τ σ σ') : ‖P τ'‖ = 4 * C.r := by
  have h := S.exc.2.2.2.2.2.1
  rw [frontier_ball4] at h
  simpa only [mem_sphere, dist_zero_right] using h

theorem norm_σ' (S : ExcSetting C D Db f V P L τ' τ σ σ') : ‖P σ'‖ = 4 * C.r := by
  have h := S.exc.2.2.2.2.2.2.1
  rw [frontier_ball4] at h
  simpa only [mem_sphere, dist_zero_right] using h

theorem τ'_nonneg (S : ExcSetting C D Db f V P L τ' τ σ σ') : 0 ≤ τ' := S.exc.1
theorem τ'_le_τ (S : ExcSetting C D Db f V P L τ' τ σ σ') : τ' ≤ τ := S.exc.2.1
theorem τ_le_σ (S : ExcSetting C D Db f V P L τ' τ σ σ') : τ ≤ σ := S.exc.2.2.1
theorem σ_le_σ' (S : ExcSetting C D Db f V P L τ' τ σ σ') : σ ≤ σ' := S.exc.2.2.2.1
theorem σ'_le_L (S : ExcSetting C D Db f V P L τ' τ σ σ') : σ' ≤ L := S.exc.2.2.2.2.1

theorem τ_mem_cl (S : ExcSetting C D Db f V P L τ' τ σ σ') : P τ ∈ closure (V : Set ℂ) :=
  S.exc.2.2.2.2.2.2.2.2.1

theorem σ_mem_cl (S : ExcSetting C D Db f V P L τ' τ σ σ') : P σ ∈ closure (V : Set ℂ) :=
  S.exc.2.2.2.2.2.2.2.2.2.1

theorem norm_τ (S : ExcSetting C D Db f V P L τ' τ σ σ') :
    3 / 2 * C.r < ‖P τ‖ ∧ ‖P τ‖ < 5 / 2 * C.r := S.V_loc S.τ_mem_cl

theorem norm_σ (S : ExcSetting C D Db f V P L τ' τ σ σ') :
    3 / 2 * C.r < ‖P σ‖ ∧ ‖P σ‖ < 5 / 2 * C.r := S.V_loc S.σ_mem_cl

 
theorem norm_le (S : ExcSetting C D Db f V P L τ' τ σ σ') {t : ℝ} (ht : t ∈ Icc τ' σ') :
    ‖P t‖ ≤ 4 * C.r := by
  rcases eq_or_lt_of_le ht.1 with h | h
  · rw [← h, S.norm_τ']
  rcases eq_or_lt_of_le ht.2 with h' | h'
  · rw [h', S.norm_σ']
  have := S.exc.2.2.2.2.2.2.2.1 t ⟨h, h'⟩
  rw [mem_ball, dist_zero_right] at this
  exact this.le

 
theorem isCurve_b (S : ExcSetting C D Db f V P L τ' τ σ σ') {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ L) : Db.IsCurve P a b := bumped_isCurve S.geo ha hab hb

 
theorem isCurve (S : ExcSetting C D Db f V P L τ' τ σ σ') {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ L) : D.IsCurve P a b :=
  Objects.Splice.bumped_curve_transfer_back C D Db f S.forget S.weyl S.f_bd (S.isCurve_b ha hab hb)

 

theorem cont (S : ExcSetting C D Db f V P L τ' τ σ σ') : ContinuousOn P (Icc τ' σ') := by
  have hP := S.isCurve_b S.τ'_nonneg (S.τ'_le_τ.trans (S.τ_le_σ.trans S.σ_le_σ')) S.σ'_le_L
  refine hP.continuousOn_of_mapsTo (isCompact_closedBall (0 : ℂ) (4 * C.r)) ?_
  intro t ht
  rw [mem_closedBall, dist_zero_right]
  exact S.norm_le ht

theorem cont_sub (S : ExcSetting C D Db f V P L τ' τ σ σ') {a b : ℝ} (ha : τ' ≤ a) (hb : b ≤ σ') :
    ContinuousOn P (Icc a b) := S.cont.mono (Icc_subset_Icc ha hb)

theorem τ'_lt_τ (S : ExcSetting C D Db f V P L τ' τ σ σ') : τ' < τ := by
  refine lt_of_le_of_ne S.τ'_le_τ (fun h => ?_)
  have h1 := S.norm_τ.2
  rw [← h, S.norm_τ'] at h1
  linarith [C.rPos]

theorem σ_lt_σ' (S : ExcSetting C D Db f V P L τ' τ σ σ') : σ < σ' := by
  refine lt_of_le_of_ne S.σ_le_σ' (fun h => ?_)
  have h1 := S.norm_σ.2
  rw [h, S.norm_σ'] at h1
  linarith [C.rPos]

 
theorem τ_not_mem (S : ExcSetting C D Db f V P L τ' τ σ σ') : P τ ∉ (V : Set ℂ) := by
  intro hτV
  have hcw : ContinuousWithinAt P (Ioo τ' τ) τ :=
    (S.cont τ ⟨S.τ'_le_τ, S.τ_le_σ.trans S.σ_le_σ'⟩).mono
      (fun t ht => ⟨ht.1.le, ht.2.le.trans (S.τ_le_σ.trans S.σ_le_σ')⟩)
  have hev : ∀ᶠ t in 𝓝[Ioo τ' τ] τ, P t ∈ (V : Set ℂ) :=
    hcw.tendsto.eventually (V.isOpen.mem_nhds hτV)
  have hne : (𝓝[Ioo τ' τ] τ).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo S.τ'_lt_τ.ne]
    exact right_mem_Icc.mpr S.τ'_le_τ
  obtain ⟨t, htV, htI⟩ := (hev.and self_mem_nhdsWithin).exists
  exact S.exc.2.2.2.2.2.2.2.2.2.2.1 t htI (subset_closure htV)

 
theorem σ_not_mem (S : ExcSetting C D Db f V P L τ' τ σ σ') : P σ ∉ (V : Set ℂ) := by
  intro hσV
  have hcw : ContinuousWithinAt P (Ioo σ σ') σ :=
    (S.cont σ ⟨S.τ'_le_τ.trans S.τ_le_σ, S.σ_le_σ'⟩).mono
      (fun t ht => ⟨S.τ'_le_τ.trans (S.τ_le_σ.trans ht.1.le), ht.2.le⟩)
  have hev : ∀ᶠ t in 𝓝[Ioo σ σ'] σ, P t ∈ (V : Set ℂ) :=
    hcw.tendsto.eventually (V.isOpen.mem_nhds hσV)
  have hne : (𝓝[Ioo σ σ'] σ).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo S.σ_lt_σ'.ne]
    exact left_mem_Icc.mpr S.σ_le_σ'
  obtain ⟨t, htV, htI⟩ := (hev.and self_mem_nhdsWithin).exists
  exact S.exc.2.2.2.2.2.2.2.2.2.2.2 t htI (subset_closure htV)

theorem norm_lt_of_mem_V (S : ExcSetting C D Db f V P L τ' τ σ σ') {x : ℂ} (hx : x ∈ (V : Set ℂ)) :
    ‖x‖ < 5 / 2 * C.r := (S.V_loc (subset_closure hx)).2

 
theorem not_mem_before (S : ExcSetting C D Db f V P L τ' τ σ σ') {t : ℝ} (ht : t ∈ Icc τ' τ) :
    P t ∉ (V : Set ℂ) := by
  rcases eq_or_lt_of_le ht.1 with h | h
  · intro hV
    have := S.norm_lt_of_mem_V hV
    rw [← h, S.norm_τ'] at this
    linarith [C.rPos]
  rcases eq_or_lt_of_le ht.2 with h' | h'
  · rw [h']; exact S.τ_not_mem
  exact fun hV => S.exc.2.2.2.2.2.2.2.2.2.2.1 t ⟨h, h'⟩ (subset_closure hV)

 
theorem not_mem_after (S : ExcSetting C D Db f V P L τ' τ σ σ') {t : ℝ} (ht : t ∈ Icc σ σ') :
    P t ∉ (V : Set ℂ) := by
  rcases eq_or_lt_of_le ht.2 with h | h
  · intro hV
    have := S.norm_lt_of_mem_V hV
    rw [h, S.norm_σ'] at this
    linarith [C.rPos]
  rcases eq_or_lt_of_le ht.1 with h' | h'
  · rw [← h']; exact S.σ_not_mem
  exact fun hV => S.exc.2.2.2.2.2.2.2.2.2.2.2 t ⟨h', h⟩ (subset_closure hV)

 
theorem len_eq_of_off (S : ExcSetting C D Db f V P L τ' τ σ σ') {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ L) (hoff : ∀ t ∈ Icc a b, P t ∉ (V : Set ℂ)) :
    D.len P a b = ENNReal.ofReal (b - a) := by
  rw [← bumped_len_eq_of_zero C D Db f S.forget S.weyl (S.isCurve ha hab hb)
    (fun t ht => S.f_off _ (hoff t ht))]
  exact bumped_len_eq S.geo ha hab hb

theorem len_eq_before (S : ExcSetting C D Db f V P L τ' τ σ σ') {a b : ℝ} (ha : τ' ≤ a) (hab : a ≤ b)
    (hb : b ≤ τ) : D.len P a b = ENNReal.ofReal (b - a) :=
  S.len_eq_of_off (S.τ'_nonneg.trans ha) hab
    (hb.trans (S.τ_le_σ.trans (S.σ_le_σ'.trans S.σ'_le_L)))
    (fun _ ht => S.not_mem_before ⟨ha.trans ht.1, ht.2.trans hb⟩)

theorem len_eq_after (S : ExcSetting C D Db f V P L τ' τ σ σ') {a b : ℝ} (ha : σ ≤ a) (hab : a ≤ b)
    (hb : b ≤ σ') : D.len P a b = ENNReal.ofReal (b - a) :=
  S.len_eq_of_off ((S.τ'_nonneg.trans (S.τ'_le_τ.trans S.τ_le_σ)).trans ha) hab (hb.trans S.σ'_le_L)
    (fun _ ht => S.not_mem_after ⟨ha.trans ht.1, ht.2.trans hb⟩)

 
theorem dist_eq (S : ExcSetting C D Db f V P L τ' τ σ σ') {s t : ℝ} (hs : τ' ≤ s) (hst : s ≤ t)
    (ht : t ≤ σ') : Db (P s, P t) = ENNReal.ofReal (t - s) :=
  bumped_dist_eq S.geo (S.τ'_nonneg.trans hs) hst (ht.trans S.σ'_le_L)

end ExcSetting

 

 


theorem x2a_times {C : Objects.CorrectedEvent.Constants} {D Db : LSCMetric} {f : C(ℂ, ℝ)} {V : TopologicalSpace.Opens ℂ}
    {P : ℝ → ℂ} {L τ' τ σ σ' : ℝ} (S : ExcSetting C D Db f V P L τ' τ σ σ') {N : ℝ} (hN : 0 < N)
    (hS2 : Objects.CorrectedEvent.around D 0 (3 * C.r) (4 * C.r) ≤ ENNReal.ofReal C.A_around * ENNReal.ofReal N) :
    ∃ τ₀ σ₀ : ℝ, τ' ≤ τ₀ ∧ τ₀ ≤ τ ∧ σ ≤ σ₀ ∧ σ₀ ≤ σ' ∧ ‖P τ₀‖ = 3 * C.r ∧ ‖P σ₀‖ = 3 * C.r ∧
      σ₀ - τ₀ < 2 * C.A_around * N := by
  have hr := C.rPos
  have hAr : 0 < C.A_around := lt_trans one_pos C.aroundGtOne
  
  have hcτ : ContinuousOn (fun t => ‖P t‖) (Icc τ' τ) :=
    (S.cont_sub le_rfl (S.τ_le_σ.trans S.σ_le_σ')).norm
  obtain ⟨τ₀, hτ₀, hτ₀n⟩ : ∃ τ₀ ∈ Icc τ' τ, ‖P τ₀‖ = 3 * C.r := by
    have := intermediate_value_Icc' S.τ'_le_τ hcτ
    exact this ⟨by linarith [S.norm_τ.2], by rw [S.norm_τ']; linarith⟩
  have hcσ : ContinuousOn (fun t => ‖P t‖) (Icc σ σ') :=
    (S.cont_sub (S.τ'_le_τ.trans S.τ_le_σ) le_rfl).norm
  obtain ⟨σ₀, hσ₀, hσ₀n⟩ : ∃ σ₀ ∈ Icc σ σ', ‖P σ₀‖ = 3 * C.r := by
    have := intermediate_value_Icc S.σ_le_σ' hcσ
    exact this ⟨by linarith [S.norm_σ.2], by rw [S.norm_σ']; linarith⟩
  
  have hB : Objects.CorrectedEvent.around D 0 (3 * C.r) (4 * C.r) < ENNReal.ofReal (2 * C.A_around * N) := by
    refine hS2.trans_lt ?_
    rw [← ENNReal.ofReal_mul hAr.le]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by nlinarith)
  obtain ⟨π, s, t, hπ, hπann, hπsep, hπlen⟩ := EndpointAttachment.exists_corrected_loop_lt D 0 _ _ hB
  have hsep := LQGMetric.Disconnects.closedBall_compl_ball (by linarith : 3 * C.r ≤ 4 * C.r) hπsep
  
  obtain ⟨u, hu, huK⟩ := exists_hit hτ₀.1 (S.cont_sub le_rfl (hτ₀.2.trans (S.τ_le_σ.trans S.σ_le_σ')))
    hsep.symm (by simp only [mem_compl_iff, mem_ball, dist_zero_right, S.norm_τ', lt_irrefl,
      not_false_eq_true]) (by simp only [mem_closedBall, dist_zero_right, hτ₀n, le_refl])
  obtain ⟨v, hv, hvK⟩ := exists_hit hσ₀.2 (S.cont_sub (S.τ'_le_τ.trans (S.τ_le_σ.trans hσ₀.1)) le_rfl)
    hsep (by simp only [mem_closedBall, dist_zero_right, hσ₀n, le_refl])
    (by simp only [mem_compl_iff, mem_ball, dist_zero_right, S.norm_σ', lt_irrefl,
      not_false_eq_true])
  obtain ⟨p, hp, hpu⟩ := huK
  obtain ⟨q, hq, hqv⟩ := hvK
  have huv : u ≤ v := hu.2.trans (hτ₀.2.trans (S.τ_le_σ.trans (hσ₀.1.trans hv.1)))
  have hdist := S.dist_eq hu.1 huv hv.2
  have hle : Db (P u, P v) ≤ D.len π s t := by
    rw [← hpu, ← hqv]
    exact bumped_dist_le_len C D Db f S.forget S.weyl S.f_bd hπ hp hq
  have hlt : ENNReal.ofReal (v - u) < ENNReal.ofReal (2 * C.A_around * N) :=
    hdist ▸ hle.trans_lt hπlen
  have hvu : v - u < 2 * C.A_around * N :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hlt
  refine ⟨τ₀, σ₀, hτ₀.1, hτ₀.2, hσ₀.1, hσ₀.2, hτ₀n, hσ₀n, ?_⟩
  linarith [hu.2, hv.1]

end SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions
