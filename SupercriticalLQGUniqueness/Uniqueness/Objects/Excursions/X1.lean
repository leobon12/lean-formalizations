import SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions.Net




 










set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions

namespace NetData

variable {C : Objects.CorrectedEvent.Constants} {T : Objects.CorrectedEvent.TubeData} {D : LSCMetric} {Ne : ℝ≥0∞}
  {π : ℂ → ℝ → ℂ} {ts us : ℂ → ℝ}

 
theorem cost_lt (net : NetData C T D Ne π ts us) (Db : LSCMetric) (f : C(ℂ, ℝ))
    (hforget : Continuous (BiLipschitz.Barrier.forget D))
    (hWeyl : ∀ x y : ℂ, Db (x, y) = weylScale C.ξ (-f) D (x, y))
    (hfmax : ∀ x ∈ Objects.CorrectedEvent.tubeSet T, f x = C.A_max)
    {p q : ℂ} (hp : p ∈ Γ π ts us T) (hq : q ∈ Γ π ts us T) :
    Db (p, q) < ENNReal.ofReal (Real.exp (-C.ξ * C.A_max)) * (ENNReal.ofReal (C.A_internal / 2) * Ne) := by
  classical
  obtain ⟨x, hx, hpx⟩ := mem_iUnion₂.mp hp
  obtain ⟨y, hy, hqy⟩ := mem_iUnion₂.mp hq
  set e := ENNReal.ofReal (Real.exp (-C.ξ * C.A_max)) with he
  have hchain := chain_bound Db T.netSites (fun x => π x '' Icc (ts x) (us x))
    (fun z => Db.len (π z) (ts z) (us z)) _
    (fun a b hab => ⟨hab.2.1, net.contact a b hab.1 hab.2.1 hab.2.2.1 hab.2.2.2⟩)
    (fun z _ p' hp' q' hq' => by
      obtain ⟨u, hu, rfl⟩ := hp'
      obtain ⟨v, hv, rfl⟩ := hq'
      exact edist_le_len Db (π z) hu hv)
    hx hpx (net.conn x hx y hy) hqy
  have hweyl : ∀ z ∈ T.netSites, Db.len (π z) (ts z) (us z) ≤ e * D.len (π z) (ts z) (us z) :=
    fun z hz => bumped_len_le_of_max C D Db f hforget hWeyl (net.curve z hz)
      (fun t ht => hfmax _ (net.tube z hz ⟨t, ht, rfl⟩))
  have hsum : ∑ z ∈ T.netSites, D.len (π z) (ts z) (us z) <
      ∑ _z ∈ T.netSites, ENNReal.ofReal (C.A_internal / (2 * T.netSites.card)) * Ne :=
    ENNReal.sum_lt_sum_of_nonempty net.nonempty net.len
  have hconst : ∑ _z ∈ T.netSites, ENNReal.ofReal (C.A_internal / (2 * T.netSites.card)) * Ne =
      ENNReal.ofReal (C.A_internal / 2) * Ne := by
    rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc]
    congr 1
    have hn : (0 : ℝ) < T.netSites.card := by exact_mod_cast Finset.card_pos.mpr net.nonempty
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hn.le]
    congr 1
    field_simp
  have he0 : e ≠ 0 := by rw [he]; exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have het : e ≠ ⊤ := ENNReal.ofReal_ne_top
  calc Db (p, q) ≤ ∑ z ∈ T.netSites, Db.len (π z) (ts z) (us z) := hchain
    _ ≤ ∑ z ∈ T.netSites, e * D.len (π z) (ts z) (us z) := Finset.sum_le_sum hweyl
    _ = e * ∑ z ∈ T.netSites, D.len (π z) (ts z) (us z) := by rw [Finset.mul_sum]
    _ < e * (ENNReal.ofReal (C.A_internal / 2) * Ne) := by
        rw [← hconst]
        exact ENNReal.mul_lt_mul_right he0 het hsum

end NetData

variable {C : Objects.CorrectedEvent.Constants} {T : Objects.CorrectedEvent.TubeData} {D Db : LSCMetric} {f : C(ℂ, ℝ)}
  {V : TopologicalSpace.Opens ℂ} {P : ℝ → ℂ} {L τ' τ σ σ' : ℝ}

 
theorem x1_carrier (S : ExcSetting C D Db f V P L τ' τ σ σ') {N : ℝ} (hN : 0 < N)
    {π : ℂ → ℝ → ℂ} {ts us : ℂ → ℝ} (net : NetData C T D (ENNReal.ofReal N) π ts us)
    (hS1 : ENNReal.ofReal C.A_across * ENNReal.ofReal N ≤ Objects.CorrectedEvent.acr D 0 C.r (1.5 * C.r))
    (hmaxint : Real.exp (-C.ξ * C.A_max) * C.A_internal ≤ C.lamConst * C.A_across)
    (hlam : C.lamConst ≤ 1)
    (htube : ∀ x ∈ Objects.CorrectedEvent.tubeSet T, 3 / 2 * C.r < ‖x‖)
    (hfmax : ∀ x ∈ Objects.CorrectedEvent.tubeSet T, f x = C.A_max)
    {t : ℝ} (ht : t ∈ Icc τ' σ') : P t ∈ Objects.CorrectedEvent.cann 0 C.r (4 * C.r) := by
  have hr := C.rPos
  refine ⟨?_, by rw [dist_zero_right]; exact S.norm_le ht⟩
  rw [dist_zero_right]
  by_contra hlt
  push Not at hlt
  have hAc := C.acrossPos
  
  obtain ⟨a, ha, haΓ⟩ := exists_hit ht.1 (S.cont_sub le_rfl ht.2) net.barrier.symm
    (by simp only [mem_compl_iff, mem_ball, dist_zero_right, S.norm_τ', not_lt]; linarith)
    (by rw [mem_closedBall, dist_zero_right]; linarith)
  obtain ⟨b, hb, hbΓ⟩ := exists_hit ht.2 (S.cont_sub ht.1 le_rfl) net.barrier
    (by rw [mem_closedBall, dist_zero_right]; linarith)
    (by simp only [mem_compl_iff, mem_ball, dist_zero_right, S.norm_σ', not_lt]; linarith)
  have hbnorm : 3 / 2 * C.r < ‖P b‖ := by
    obtain ⟨x, hx, hbx⟩ := mem_iUnion₂.mp hbΓ
    exact htube _ (net.tube x hx hbx)
  
  have hrad : ContinuousOn (fun u => ‖P u‖) (Icc t b) :=
    (S.cont_sub ht.1 hb.2).norm
  obtain ⟨c', d', htc, hcd, hdb, hc', hd', hbetween⟩ :=
    LQGMetric.RectCross.exists_sub_crossing hb.1 hrad (by linarith : C.r ≤ 1.5 * C.r) hlt.le
      (by linarith)
  have h0c : 0 ≤ c' := S.τ'_nonneg.trans (ht.1.trans htc)
  have hdL : d' ≤ L := hdb.trans (hb.2.trans S.σ'_le_L)
  have hP : D.IsCurve P c' d' := S.isCurve h0c hcd hdL
  have htrace : P '' Icc c' d' ⊆ Objects.CorrectedEvent.cann 0 C.r (1.5 * C.r) := by
    rintro x ⟨u, hu, rfl⟩
    have := hbetween u hu
    exact ⟨by rw [dist_zero_right]; exact this.1, by rw [dist_zero_right]; exact this.2⟩
  have hoff : ∀ u ∈ Icc c' d', P u ∉ (V : Set ℂ) := by
    intro u hu hV
    have h1 := (S.V_loc (subset_closure hV)).1
    have h2 := (hbetween u hu).2
    linarith
  have hacr : Objects.CorrectedEvent.acr D 0 C.r (1.5 * C.r) ≤ D.len P c' d' :=
    EndpointAttachment.corrected_acr_le_crossing_length D hP htrace
      (by rw [mem_sphere, dist_zero_right]; exact hc')
      (by rw [mem_sphere, dist_zero_right]; exact hd')
  rw [S.len_eq_of_off h0c hcd hdL hoff] at hacr
  
  have hab : a ≤ b := ha.2.trans hb.1
  have hdist := S.dist_eq ha.1 hab hb.2
  have hcost := net.cost_lt Db f S.forget S.weyl hfmax haΓ hbΓ
  rw [hdist, ← ENNReal.ofReal_mul (div_nonneg C.internalPos.le two_pos.le),
    ← ENNReal.ofReal_mul (Real.exp_pos _).le] at hcost
  have hlt2 : b - a < Real.exp (-C.ξ * C.A_max) * (C.A_internal / 2 * N) :=
    (ENNReal.ofReal_lt_ofReal_iff
      (mul_pos (Real.exp_pos _) (mul_pos (div_pos C.internalPos two_pos) hN))).mp hcost
  have hS1' : C.A_across * N ≤ d' - c' := by
    have := hS1.trans hacr
    rw [← ENNReal.ofReal_mul hAc.le] at this
    exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp this
  have hdc : d' - c' ≤ b - a := by linarith [ha.2, htc]
  have hmax' : Real.exp (-C.ξ * C.A_max) * (C.A_internal / 2 * N) ≤ C.lamConst * C.A_across * N / 2 := by
    have := mul_le_mul_of_nonneg_right hmaxint hN.le
    nlinarith
  have hfin : C.lamConst * C.A_across * N / 2 < C.A_across * N := by
    have h1 : 0 < C.A_across * N := mul_pos hAc hN
    nlinarith
  linarith

 
theorem x1_geo (S : ExcSetting C D Db f V P L τ' τ σ σ')
    (hcar : ∀ t ∈ Icc τ' σ', P t ∈ Objects.CorrectedEvent.cann 0 C.r (4 * C.r))
    (ha : P τ' ∈ Objects.CorrectedEvent.cann 0 C.r (4 * C.r)) (hb : P σ' ∈ Objects.CorrectedEvent.cann 0 C.r (4 * C.r)) :
    Db.len P τ' σ' = Db.internal (Objects.CorrectedEvent.cann 0 C.r (4 * C.r)) (⟨P τ', ha⟩, ⟨P σ', hb⟩) := by
  have hτσ : τ' ≤ σ' := S.τ'_le_τ.trans (S.τ_le_σ.trans S.σ_le_σ')
  have hP : Db.IsCurve P τ' σ' := S.isCurve_b S.τ'_nonneg hτσ S.σ'_le_L
  refine le_antisymm ?_ (BiLipschitz.Barrier.internal_le_len' Db hP hcar)
  rw [bumped_len_eq S.geo S.τ'_nonneg hτσ S.σ'_le_L, ← S.dist_eq le_rfl hτσ le_rfl,
    LSCMetric.internal_eq_internalEDist]
  exact LQGMetric.MetricGeometry.edist_le_internalEDist (X := Db.Space) _ _ _

end SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions
