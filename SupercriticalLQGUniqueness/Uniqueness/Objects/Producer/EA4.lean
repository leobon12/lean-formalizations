import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.EA3
import SupercriticalLQGUniqueness.Uniqueness.Objects.EndpointAttachmentCore.TimeBins
import SupercriticalLQGUniqueness.Uniqueness.Objects.EndpointAttachment.LoopHit




 














set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Complex
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Producer

 

 

theorem narrow_time_lower (C : Objects.CorrectedEvent.Constants) (D Db : LSCMetric) (f : C(ℂ, ℝ))
    (hforget : Continuous (BiLipschitz.Barrier.forget D))
    (hWeyl : ∀ x y : ℂ, Db (x, y) = weylScale C.ξ (-f) D (x, y))
    {P : ℝ → ℂ} {L : ℝ} (hPD : D.IsCurve P 0 L) (hunit : HasUnitSpeedOn (Db.pt ∘ P) (Icc 0 L))
    {N : ℝ}
    (hnarrow : ∀ (z w : ℂ) (hz : z ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r))
      (hw : w ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r)), dist z w ≤ C.A_nar / C.lamConst * C.r →
      ENNReal.ofReal ((dist z w / C.r) ^ (C.ξ * (C.Q + 3))) * ENNReal.ofReal N ≤
        D.internal (Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (⟨z, mid_ann_subset C hz⟩, ⟨w, mid_ann_subset C hw⟩))
    {p q : ℝ} (h0p : 0 ≤ p) (hpq : p ≤ q) (hqL : q ≤ L)
    (hoff : ∀ t ∈ Icc p q, f (P t) = 0)
    (hloc : ∀ t ∈ Icc p q, P t ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r))
    (hwin : dist (P p) (P q) ≤ C.A_nar / C.lamConst * C.r) :
    (dist (P p) (P q) / C.r) ^ (C.ξ * (C.Q + 3)) * N ≤ q - p := by
  have hp := hloc p ⟨le_rfl, hpq⟩
  have hq := hloc q ⟨hpq, le_rfl⟩
  have hE := hnarrow (P p) (P q) hp hq hwin
  have hsub : D.IsCurve P p q := ⟨hpq, hPD.2.mono (Icc_subset_Icc h0p hqL)⟩
  have hint := internal_le_len_pts D (Y := Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) hsub
    (fun x hx => mid_ann_subset C (hloc x hx)) (mid_ann_subset C hp) (mid_ann_subset C hq) rfl rfl
  have hlenD : D.len P p q = ENNReal.ofReal (q - p) := by
    rw [← bumped_len_zero_trace C D Db f hforget hWeyl hsub hoff]
    exact unit_len hunit ⟨h0p, hpq.trans hqL⟩ ⟨h0p.trans hpq, hqL⟩ hpq
  have hchain := hE.trans (hint.trans hlenD.le)
  have hnn : 0 ≤ (dist (P p) (P q) / C.r) ^ (C.ξ * (C.Q + 3)) :=
    Real.rpow_nonneg (div_nonneg dist_nonneg C.rPos.le) _
  rw [← ENNReal.ofReal_mul hnn] at hchain
  exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 hchain

 

 
def excReach (P : ℝ → ℂ) (e : ℝ × ℝ) : ℝ := sSup ((fun t => ‖P t - P e.1‖) '' Icc e.1 e.2)

theorem excReach_ge {P : ℝ → ℂ} {e : ℝ × ℝ} (hcont : ContinuousOn P (Icc e.1 e.2))
    {t : ℝ} (ht : t ∈ Icc e.1 e.2) : ‖P t - P e.1‖ ≤ excReach P e := by
  have hc : IsCompact ((fun t => ‖P t - P e.1‖) '' Icc e.1 e.2) :=
    isCompact_Icc.image_of_continuousOn ((hcont.sub continuousOn_const).norm)
  exact le_csSup hc.bddAbove ⟨t, ht, rfl⟩

theorem excReach_attained {P : ℝ → ℂ} {e : ℝ × ℝ} (hcont : ContinuousOn P (Icc e.1 e.2))
    (hle : e.1 ≤ e.2) : ∃ t ∈ Icc e.1 e.2, ‖P t - P e.1‖ = excReach P e := by
  have hc : IsCompact ((fun t => ‖P t - P e.1‖) '' Icc e.1 e.2) :=
    isCompact_Icc.image_of_continuousOn ((hcont.sub continuousOn_const).norm)
  have hne : ((fun t => ‖P t - P e.1‖) '' Icc e.1 e.2).Nonempty := ⟨_, e.1, left_mem_Icc.2 hle, rfl⟩
  obtain ⟨t, ht, heq⟩ := hc.sSup_mem hne
  exact ⟨t, ht, heq⟩

 

def chargedExc (P : ℝ → ℂ) (c : ℂ) (R₁ ε a b : ℝ) (W' : Set ℂ) : Set (ℝ × ℝ) :=
  {e | a ≤ e.1 ∧ e.1 < e.2 ∧ e.2 ≤ b ∧ ‖P e.1 - c‖ = R₁ ∧ ‖P e.2 - c‖ = R₁ ∧
    (∀ t ∈ Ioo e.1 e.2, R₁ < ‖P t - c‖) ∧
    ∃ s ∈ Icc e.1 e.2, R₁ + ε ≤ ‖P s - c‖ ∧ ∃ w ∈ W', w = LQGMetric.Topo.Crosscut.rproj c R₁ (P s)}

 
theorem chargedExc_off {P : ℝ → ℂ} {c : ℂ} {R₁ ε a b : ℝ} {W' : Set ℂ} {V : Set ℂ} (hV : IsOpen V)
    (hcont : ContinuousOn P (Icc a b)) (hwin : ∀ t ∈ Ioo a b, P t ∈ V → P t ∈ ball c R₁)
    {e : ℝ × ℝ} (he : e ∈ chargedExc P c R₁ ε a b W') : ∀ t ∈ Icc e.1 e.2, P t ∉ V := by
  obtain ⟨hae, hlt, heb, -, -, hext, -⟩ := he
  exact Objects.TubeChecks.excursion_endpoints_off hV hcont hae hlt heb
    (fun t ht => by rw [dist_eq_norm]; exact hext t ht) hwin

 
theorem chargedExc_reach (C : Objects.CorrectedEvent.Constants) (D Db : LSCMetric) (f : C(ℂ, ℝ))
    (hforget : Continuous (BiLipschitz.Barrier.forget D))
    (hWeyl : ∀ x y : ℂ, Db (x, y) = weylScale C.ξ (-f) D (x, y))
    {P : ℝ → ℂ} {L : ℝ} (hPD : D.IsCurve P 0 L) (hunit : HasUnitSpeedOn (Db.pt ∘ P) (Icc 0 L))
    (hcont : ContinuousOn P (Icc 0 L)) {N : ℝ}
    (hnarrow : ∀ (z w : ℂ) (hz : z ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r))
      (hw : w ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r)), dist z w ≤ C.A_nar / C.lamConst * C.r →
      ENNReal.ofReal ((dist z w / C.r) ^ (C.ξ * (C.Q + 3))) * ENNReal.ofReal N ≤
        D.internal (Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (⟨z, mid_ann_subset C hz⟩, ⟨w, mid_ann_subset C hw⟩))
    (hlam : C.lamConst ≤ 1)
    {c : ℂ} {R₁ ε a b : ℝ} {W' V : Set ℂ} (hV : IsOpen V) (hfV : ∀ x ∉ V, f x = 0)
    (h0a : 0 ≤ a) (hbL : b ≤ L)
    (hshort : b - a < C.A_nar ^ (C.ξ * (C.Q + 3)) * N)
    (hwin : ∀ t ∈ Ioo a b, P t ∈ V → P t ∈ ball c R₁)
    (hloc : ∀ t ∈ Icc a b, P t ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r))
    {e : ℝ × ℝ} (he : e ∈ chargedExc P c R₁ ε a b W') :
    ε ≤ excReach P e ∧ excReach P e < C.A_nar * C.r := by
  have hcab : ContinuousOn P (Icc a b) := hcont.mono (Icc_subset_Icc h0a hbL)
  have hoff := chargedExc_off hV hcab hwin he
  obtain ⟨hae, hlt, heb, he1, -, -, s, hs, hsfar, -⟩ := he
  have hce : ContinuousOn P (Icc e.1 e.2) := hcab.mono (Icc_subset_Icc hae heb)
  constructor
  · refine le_trans ?_ (excReach_ge hce hs)
    have := norm_sub_norm_le (P s - c) (P e.1 - c)
    rw [sub_sub_sub_cancel_right] at this
    linarith
  · obtain ⟨t, ht, hteq⟩ := excReach_attained hce hlt.le
    rw [← hteq, ← dist_eq_norm, dist_comm]
    exact offbump_diam_lt C D Db f hforget hWeyl hPD hunit hcont hnarrow hlam
      (h0a.trans hae) (heb.trans hbL) (by linarith)
      (fun x hx => hfV _ (hoff x hx)) (fun x hx => hloc x ⟨hae.trans hx.1, hx.2.trans heb⟩)
      e.1 (left_mem_Icc.2 hlt.le) t ht

 
theorem chargedExc_time (C : Objects.CorrectedEvent.Constants) (D Db : LSCMetric) (f : C(ℂ, ℝ))
    (hforget : Continuous (BiLipschitz.Barrier.forget D))
    (hWeyl : ∀ x y : ℂ, Db (x, y) = weylScale C.ξ (-f) D (x, y))
    {P : ℝ → ℂ} {L : ℝ} (hPD : D.IsCurve P 0 L) (hunit : HasUnitSpeedOn (Db.pt ∘ P) (Icc 0 L))
    (hcont : ContinuousOn P (Icc 0 L)) {N : ℝ}
    (hnarrow : ∀ (z w : ℂ) (hz : z ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r))
      (hw : w ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r)), dist z w ≤ C.A_nar / C.lamConst * C.r →
      ENNReal.ofReal ((dist z w / C.r) ^ (C.ξ * (C.Q + 3))) * ENNReal.ofReal N ≤
        D.internal (Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (⟨z, mid_ann_subset C hz⟩, ⟨w, mid_ann_subset C hw⟩))
    {c : ℂ} {R₁ ε a b : ℝ} {W' V : Set ℂ} (hV : IsOpen V) (hfV : ∀ x ∉ V, f x = 0)
    (hε : 0 < ε) (hεwin : ε ≤ C.A_nar / C.lamConst * C.r)
    (h0a : 0 ≤ a) (hbL : b ≤ L)
    (hwin : ∀ t ∈ Ioo a b, P t ∈ V → P t ∈ ball c R₁)
    (hloc : ∀ t ∈ Icc a b, P t ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r))
    {e : ℝ × ℝ} (he : e ∈ chargedExc P c R₁ ε a b W') :
    (ε / C.r) ^ (C.ξ * (C.Q + 3)) * N ≤ e.2 - e.1 := by
  have hcab : ContinuousOn P (Icc a b) := hcont.mono (Icc_subset_Icc h0a hbL)
  have hoff := chargedExc_off hV hcab hwin he
  obtain ⟨hae, hlt, heb, he1, -, -, s, hs, hsfar, -⟩ := he
  have hce : ContinuousOn P (Icc e.1 e.2) := hcab.mono (Icc_subset_Icc hae heb)
  
  have hfar : ε ≤ dist (P e.1) (P s) := by
    rw [dist_comm, dist_eq_norm]
    have := norm_sub_norm_le (P s - c) (P e.1 - c)
    rw [sub_sub_sub_cancel_right] at this
    linarith
  have hcs : ContinuousOn (fun x => dist (P e.1) (P x)) (Icc e.1 s) :=
    (continuous_const.dist continuous_id).comp_continuousOn (hce.mono (Icc_subset_Icc le_rfl hs.2))
  obtain ⟨t, ht, hdt⟩ := intermediate_value_Icc hs.1 hcs
    (show ε ∈ Icc (dist (P e.1) (P e.1)) (dist (P e.1) (P s)) by
      rw [dist_self]; exact ⟨hε.le, hfar⟩)
  simp only at hdt
  have htmem : t ∈ Icc e.1 e.2 := ⟨ht.1, ht.2.trans hs.2⟩
  have hbound := narrow_time_lower C D Db f hforget hWeyl hPD hunit hnarrow
    (h0a.trans hae) ht.1 (htmem.2.trans (heb.trans hbL))
    (fun x hx => hfV _ (hoff x ⟨hx.1, hx.2.trans htmem.2⟩))
    (fun x hx => hloc x ⟨hae.trans hx.1, hx.2.trans (htmem.2.trans heb)⟩) (by rw [hdt]; exact hεwin)
  rw [hdt] at hbound
  linarith [htmem.2]

 
theorem chargedExc_finite {P : ℝ → ℂ} {c : ℂ} {R₁ ε a b : ℝ} {W' : Set ℂ} {δ : ℝ} (hδ : 0 < δ)
    (htime : ∀ e ∈ chargedExc P c R₁ ε a b W', δ ≤ e.2 - e.1) :
    (chargedExc P c R₁ ε a b W').Finite := by
  apply Objects.Shadow.finite_maximal_exterior_excursions (f := fun t => ‖P t - c‖) (R := R₁) (a := a)
    (b := b) hδ
  intro e he
  have ht := htime e he
  obtain ⟨hae, -, heb, he1, he2, hext, -⟩ := he
  exact ⟨hae, ht, heb, he1, he2, hext⟩

end SupercriticalLQGUniqueness.Uniqueness.Objects.Producer
