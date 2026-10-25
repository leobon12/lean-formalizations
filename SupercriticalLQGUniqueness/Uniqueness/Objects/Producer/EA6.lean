import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.EA5




 
















set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Complex
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Producer

theorem dist_radial_aux (c x : ℂ) {R₀ R₁ : ℝ} (hR₀ : 0 < R₀) (hR : R₀ ≤ R₁) (hx : ‖x - c‖ = R₀) :
    dist x (c + ((R₁ : ℂ) / (R₀ : ℂ)) * (x - c)) = R₁ - R₀ := by
  rw [dist_eq_norm]
  have h0 : (R₀ : ℂ) ≠ 0 := by exact_mod_cast hR₀.ne'
  have : x - (c + ((R₁ : ℂ) / (R₀ : ℂ)) * (x - c)) = ((((R₀ - R₁) / R₀ : ℝ)) : ℂ) * (x - c) := by
    push_cast
    field_simp
    ring
  rw [this, norm_mul, Complex.norm_real, hx, Real.norm_eq_abs]
  rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hR₀.le)]
  field_simp
  ring

theorem internal_symm (D : LSCMetric) (Y : Set ℂ) (p q : Y) :
    D.internal Y (p, q) = D.internal Y (q, p) :=
  (LSCMetric.isExtMetric_internal D Y).2.2.1 p q

theorem internal_triangle (D : LSCMetric) (Y : Set ℂ) (p q w : Y) :
    D.internal Y (p, w) ≤ D.internal Y (p, q) + D.internal Y (q, w) :=
  (LSCMetric.isExtMetric_internal D Y).2.2.2 p q w

 
theorem paid_attachment (C : Objects.CorrectedEvent.Constants) (D Db : LSCMetric) (f : C(ℂ, ℝ))
    (hforget : Continuous (BiLipschitz.Barrier.forget D)) (hL : D.IsLengthSpace)
    (hWeyl : ∀ x y : ℂ, Db (x, y) = weylScale C.ξ (-f) D (x, y))
    (hf : ∀ x : ℂ, 0 ≤ f x ∧ f x ≤ C.A_max)
    {V : Set ℂ} (hV : IsOpen V) (hfV : ∀ x ∉ V, f x = 0)
    {c u : ℂ} {R₀ R₁ : NNReal} {dt N : ℝ} (hR₀ : 0 < R₀)
    (hR₁def : (R₁ : ℝ) = R₀ + C.A_sup * C.r) (hdt : 0 < C.lamConst * dt) (hN : 0 ≤ N)
    (hfB : ∀ x ∈ closedBall c (R₀ : ℝ), f x = C.A_max)
    (hu : u ∈ closedBall c (R₀ : ℝ)) (hu2 : dist u c < (R₀ : ℝ) / 2)
    (hAnn : ball c ((R₁ : ℝ) + 3 * C.A_nar * C.r) ⊆ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r))
    (hBinA : closedBall c (R₀ : ℝ) ⊆ Objects.CorrectedEvent.ann 0 C.r (4 * C.r))
    (hnar_s : 3 * C.A_nar * C.r ≤ (R₀ : ℝ) / 2)
    {P : ℝ → ℂ} {L : ℝ} (hPD : D.IsCurve P 0 L) (hunit : HasUnitSpeedOn (Db.pt ∘ P) (Icc 0 L))
    (hcont : ContinuousOn P (Icc 0 L))
    (hnarrow : ∀ (z w : ℂ) (hz : z ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r))
      (hw : w ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r)), dist z w ≤ C.A_nar / C.lamConst * C.r →
      ENNReal.ofReal ((dist z w / C.r) ^ (C.ξ * (C.Q + 3))) * ENNReal.ofReal N ≤
        D.internal (Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (⟨z, mid_ann_subset C hz⟩, ⟨w, mid_ann_subset C hw⟩))
    (hcompare : ∀ y ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r), ∀ δ : ℝ, 0 < δ → δ ≤ C.A_nar →
      Objects.CorrectedEvent.around D y (2 * δ * C.r) (3 * δ * C.r) ≤
        ENNReal.ofReal (δ ^ (-(1 : ℝ) / 4)) * Objects.CorrectedEvent.acr D y (δ * C.r / 4) (δ * C.r / 2))
    (hlam : C.lamConst ≤ 1)
    {a b τ' σ' σ₀ : ℝ} (h0a : 0 ≤ a) (hbσ₀ : b ≤ σ₀) (hσ₀L : σ₀ ≤ L) (hσ₀ : ‖P σ₀‖ = 3 * C.r)
    (hshort : b - a < C.A_nar ^ (C.ξ * (C.Q + 3)) * N)
    (hwin : ∀ t ∈ Ioo a b, P t ∈ V → P t ∈ ball c (R₁ : ℝ))
    (hmid : ∀ t ∈ Icc a b, P t ∈ ball c ((R₁ : ℝ) + C.A_nar * C.r))
    (hnohit : ∀ t ∈ Icc a b, P t ∉ cheapSet D c u (R₀ : ℝ) (2 * C.lamConst * dt))
    {W' : Set ℂ}
    (hW' : ∀ w ∈ W', ∃ x, x ∈ goodSet D c u (R₀ : ℝ) (C.lamConst * dt) hu ∧
      x ∉ hitSet P τ' σ' (2 * C.A_sup * C.r) ∧ w = c + ((R₁ : ℂ) / (R₀ : ℂ)) * (x - c))
    {e : ℝ × ℝ} (he : e ∈ chargedExc P c (R₁ : ℝ) (C.A_sup * C.r) a b W') :
    ∃ s t : ℝ, e.1 ≤ s ∧ s ≤ e.2 ∧ e.2 < t ∧ t ≤ σ₀ ∧
      MapsTo P (Icc s t) (ball (P e.1) (3 * excReach P e)) ∧
      (excReach P e / (4 * C.r)) ^ (C.ξ * (C.Q + 3)) * N ≤ t - s ∧
      ∃ (hPt : P t ∈ Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (huA : u ∈ Objects.CorrectedEvent.ann 0 C.r (4 * C.r)),
        Db.internal (Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (⟨P t, hPt⟩, ⟨u, huA⟩) ≤
          ENNReal.ofReal (2 * C.lamConst * (Real.exp (-C.ξ * C.A_max) * dt) +
            2 * (excReach P e / C.r) ^ (-(1 : ℝ) / 4) * (t - s)) := by
  have hr := C.rPos
  have hsup := C.supPos
  have hnar := C.narPos
  have hR0r : (0 : ℝ) < R₀ := by exact_mod_cast hR₀
  have hsr : 0 < C.A_sup * C.r := mul_pos hsup hr
  have h3nar : 3 * C.A_nar * C.r = 3 * (C.A_nar * C.r) := by ring
  have hR1r : (0 : ℝ) < R₁ := by rw [hR₁def]; positivity
  have hbL : b ≤ L := hbσ₀.trans hσ₀L
  have hcab : ContinuousOn P (Icc a b) := hcont.mono (Icc_subset_Icc h0a hbL)
  have hlocab : ∀ t ∈ Icc a b, P t ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r) := fun t ht =>
    hAnn (ball_subset_ball (by nlinarith) (hmid t ht))
  
  have hoff := chargedExc_off hV hcab hwin he
  obtain ⟨hreach1, hreach2⟩ := chargedExc_reach C D Db f hforget hWeyl hPD hunit hcont hnarrow hlam
    hV hfV h0a hbL hshort hwin hlocab he
  have he' := he
  obtain ⟨hae, hlt, heb, he1, he2, hext, sw, hsw, hswfar, w, hwW', hwproj⟩ := he'
  set α := e.1
  set β := e.2
  set y := P α with hy
  set H := excReach P e with hH
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) hreach1
  have hce : ContinuousOn P (Icc α β) := hcab.mono (Icc_subset_Icc hae heb)
  have hαL : 0 ≤ α := h0a.trans hae
  have hβL : β ≤ L := heb.trans hbL
  
  obtain ⟨tm, htm, htmH⟩ := excReach_attained (P := P) (e := e) hce hlt.le
  have hHge : ∀ t ∈ Icc α β, ‖P t - y‖ ≤ H := fun t ht => excReach_ge (P := P) (e := e) hce ht
  have htmH' : ‖P tm - y‖ = H := htmH
  have htm' : tm ∈ Icc α β := htm
  clear_value H y α β
  clear htm htmH
  have hfc : ContinuousOn (fun t => ‖P t - y‖) (Icc α tm) :=
    ((hce.mono (Icc_subset_Icc le_rfl htm'.2)).sub continuousOn_const).norm
  obtain ⟨s, s', hαs, hss', hs'tm, hfs, hfs', hcoll⟩ := LQGMetric.RectCross.exists_sub_crossing
    htm'.1 hfc (by linarith : H / 4 ≤ H / 2)
    (by show ‖P α - y‖ ≤ H / 4; rw [hy, sub_self, norm_zero]; linarith)
    (by show H / 2 ≤ ‖P tm - y‖; rw [htmH']; linarith)
  have hss'lt : s < s' := by
    rcases eq_or_lt_of_le hss' with h | h
    · rw [h] at hfs; linarith
    · exact h
  have hsβ : s ≤ β := hss'.trans (hs'tm.trans htm'.2)
  have hs'β : s' ≤ β := hs'tm.trans htm'.2
  have hsub_s : Icc s s' ⊆ Icc α β := Icc_subset_Icc hαs hs'β
  
  have hDcross : D.IsCurve P s s' := ⟨hss', hPD.2.mono (Icc_subset_Icc (hαL.trans hαs) (hs'β.trans hβL))⟩
  have hlen_cross : D.len P s s' = ENNReal.ofReal (s' - s) := by
    rw [← bumped_len_zero_trace C D Db f hforget hWeyl hDcross
      (fun x hx => hfV _ (hoff x (hsub_s hx)))]
    exact unit_len hunit ⟨hαL.trans hαs, hss'.trans (hs'β.trans hβL)⟩
      ⟨hαL.trans (hαs.trans hss'), hs'β.trans hβL⟩ hss'
  have hacr : Objects.CorrectedEvent.acr D y (H / 4) (H / 2) ≤ ENNReal.ofReal (s' - s) := by
    rw [← hlen_cross]
    refine EndpointAttachment.corrected_acr_le_crossing_length D hDcross ?_ ?_ ?_
    · rintro z ⟨x, hx, rfl⟩
      have := hcoll x hx
      exact ⟨by rw [dist_eq_norm]; exact this.1, by rw [dist_eq_norm]; exact this.2⟩
    · rw [mem_sphere, dist_eq_norm]; exact hfs
    · rw [mem_sphere, dist_eq_norm]; exact hfs'
  
  have hdisp : H / 4 ≤ dist (P s) (P s') := by
    rw [dist_comm, dist_eq_norm]
    have := norm_sub_norm_le (P s' - y) (P s - y)
    rw [sub_sub_sub_cancel_right] at this
    linarith
  have hdisp2 : dist (P s) (P s') ≤ C.A_nar / C.lamConst * C.r := by
    have h1 : dist (P s) (P s') ≤ H / 2 + H / 4 := by
      calc dist (P s) (P s') ≤ dist (P s) y + dist y (P s') := dist_triangle _ _ _
        _ = H / 4 + H / 2 := by rw [dist_eq_norm, hfs, dist_comm, dist_eq_norm, hfs']
        _ = H / 2 + H / 4 := by ring
    have h2 : C.A_nar * C.r ≤ C.A_nar / C.lamConst * C.r := by
      have : C.A_nar ≤ C.A_nar / C.lamConst := by
        rw [le_div_iff₀ C.lamPos]; nlinarith
      nlinarith
    linarith
  have hnt := narrow_time_lower C D Db f hforget hWeyl hPD hunit hnarrow (hαL.trans hαs) hss'
    (hs'β.trans hβL) (fun x hx => hfV _ (hoff x (hsub_s hx)))
    (fun x hx => hlocab x ⟨hae.trans (hαs.trans hx.1), hx.2.trans (hs'β.trans heb)⟩) hdisp2
  have hexp : 0 < C.ξ * (C.Q + 3) := mul_pos C.ξPos (by linarith [C.QPos])
  have htime_low : (H / (4 * C.r)) ^ (C.ξ * (C.Q + 3)) * N ≤ s' - s := by
    refine le_trans ?_ hnt
    have hratio : H / (4 * C.r) ≤ dist (P s) (P s') / C.r := by
      rw [div_le_div_iff₀ (by positivity) hr]
      nlinarith
    have hmono : (H / (4 * C.r)) ^ (C.ξ * (C.Q + 3)) ≤ (dist (P s) (P s') / C.r) ^ (C.ξ * (C.Q + 3)) :=
      Real.rpow_le_rpow (by positivity) hratio hexp.le
    exact mul_le_mul_of_nonneg_right hmono hN
  
  have hy_mid : y ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r) := by
    rw [hy]; exact hlocab α ⟨hae, hlt.le.trans heb⟩
  have hδ : 0 < H / C.r := div_pos hH0 hr
  have hδnar : H / C.r ≤ C.A_nar := by rw [div_le_iff₀ hr]; exact hreach2.le
  have hcmp := hcompare y hy_mid (H / C.r) hδ hδnar
  have e1 : 2 * (H / C.r) * C.r = 2 * H := by field_simp
  have e2 : 3 * (H / C.r) * C.r = 3 * H := by field_simp
  have e3 : H / C.r * C.r / 4 = H / 4 := by field_simp
  have e4 : H / C.r * C.r / 2 = H / 2 := by field_simp
  rw [e1, e2, e3, e4] at hcmp
  have hd : 0 < s' - s := by linarith
  have hcoeff : 0 < (H / C.r) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos hδ _
  obtain ⟨π, u₁, v₁, hπ, hπc, hπann, hπsep, hπlen⟩ :=
    EndpointAttachment.exists_corrected_paid_loop_continuous D y (H / 4) (2 * H) (H / 2) (3 * H) hcoeff hd hcmp hacr
  have hu₁v₁ : u₁ ≤ v₁ := hπ.1
  set K := π '' Icc u₁ v₁ with hK
  have hKcl : IsClosed K := (isCompact_Icc.image_of_continuousOn hπc).isClosed
  have hKball : K ⊆ ball y (3 * H) := fun z hz => by
    have := hπann hz
    rw [mem_ball]; exact this.2
  
  have hyc : ‖y - c‖ = R₁ := he1
  have hball3 : ball y (3 * H) ⊆ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r) := by
    intro z hz
    apply hAnn
    rw [mem_ball] at hz ⊢
    calc dist z c ≤ dist z y + dist y c := dist_triangle _ _ _
      _ < 3 * H + R₁ := by rw [dist_eq_norm y c, hyc]; linarith only [hz]
      _ ≤ (R₁ : ℝ) + 3 * C.A_nar * C.r := by linarith only [hreach2, h3nar]
  
  have hβσ₀ : β ≤ σ₀ := heb.trans hbσ₀
  have hPβ : P β ∈ closedBall y (2 * H) := by
    rw [mem_closedBall, dist_eq_norm]
    have := hHge β (right_mem_Icc.2 hlt.le)
    linarith only [this, hH0]
  have hPσ₀ : P σ₀ ∈ (ball y (3 * H))ᶜ := by
    intro hin
    have := (hball3 hin).2
    rw [dist_zero_right, hσ₀] at this
    exact lt_irrefl _ this
  have hPβK : P β ∉ K := by
    intro hin
    have h1 := (hπann hin).1
    have h2 := hHge β (right_mem_Icc.2 hlt.le)
    rw [dist_eq_norm] at h1
    linarith only [h1, h2, hH0]
  obtain ⟨t, ht, hPtK, hβt, -, hmaps⟩ := Objects.Shadow.first_separator_hit_inside_collar hβσ₀
    (by linarith only [hH0] : 2 * H ≤ 3 * H) (hcont.mono (Icc_subset_Icc (hαL.trans hlt.le) hσ₀L)) hKcl hπsep
    hKball hPβ hPσ₀ hPβK
  
  have hmapsst : MapsTo P (Icc s t) (ball y (3 * H)) := by
    intro x hx
    rcases le_total x β with hxβ | hxβ
    · rw [mem_ball, dist_eq_norm]
      have := hHge x ⟨hαs.trans hx.1, hxβ⟩
      linarith only [this, hH0]
    · exact hmaps ⟨hxβ, hx.2⟩
  
  obtain ⟨x, hxG, hxN, hwx⟩ := hW' w hwW'
  have hxs : x ∈ sphere c (R₀ : ℝ) := hxG.1
  have hxy : x ∈ closedBall y (2 * H) := by
    rw [mem_closedBall]
    have hwy : dist w y ≤ H := by
      rw [hwproj, dist_eq_norm]
      have hyS : y ∈ sphere c (R₁ : ℝ) := by rw [mem_sphere, dist_eq_norm]; exact hyc
      refine (Objects.Shadow.norm_rproj_sub_le hR1r hyS (by linarith only [hswfar, hsr])).trans ?_
      exact hHge sw hsw
    have hxw : dist x w = C.A_sup * C.r := by
      have hxc : ‖x - c‖ = R₀ := by rw [← dist_eq_norm]; exact hxs
      have hR01 : (R₀ : ℝ) ≤ R₁ := by rw [hR₁def]; exact le_add_of_nonneg_right hsr.le
      have h := dist_radial_aux c x hR0r hR01 hxc
      calc dist x w = dist x (c + (((R₁ : ℝ) : ℂ) / ((R₀ : ℝ) : ℂ)) * (x - c)) := by rw [hwx]
        _ = (R₁ : ℝ) - R₀ := h
        _ = C.A_sup * C.r := by rw [hR₁def]; ring
    calc dist x y ≤ dist x w + dist w y := dist_triangle _ _ _
      _ ≤ C.A_sup * C.r + H := by rw [hxw]; linarith only [hwy]
      _ ≤ 2 * H := by linarith only [hreach1]
  have hu3 : u ∈ (ball y (3 * H))ᶜ := by
    intro hin
    rw [mem_ball] at hin
    have h1 : dist y c ≤ dist y u + dist u c := dist_triangle _ _ _
    rw [dist_eq_norm y c, hyc, dist_comm] at h1
    rw [hR₁def] at h1
    linarith only [h1, hin, hu2, hreach2, hnar_s, h3nar, hsr]
  obtain ⟨Lp, hLB, -, hLcheap⟩ := cheap_path_avoiding C D hforget hdt hu hnohit hxG
  have hsep' := LQGMetric.Disconnects.closedBall_compl_ball (by linarith only [hH0] : 2 * H ≤ 3 * H) hπsep
  obtain ⟨z, ⟨τ₁, hτ₁⟩, hzK⟩ := hsep' x u Lp.symm hxy hu3
  have hzcheap : z ∈ cheapSet D c u (R₀ : ℝ) (2 * C.lamConst * dt) := by
    rw [← hτ₁]; exact hLcheap _
  
  have hA : ∀ q ∈ ball y (3 * H), q ∈ Objects.CorrectedEvent.ann 0 C.r (4 * C.r) := fun q hq =>
    mid_ann_subset C (hball3 hq)
  have hPtA : P t ∈ Objects.CorrectedEvent.ann 0 C.r (4 * C.r) := hA _ (hKball hPtK)
  have hzA : z ∈ Objects.CorrectedEvent.ann 0 C.r (4 * C.r) := hA _ (hKball hzK)
  have huA : u ∈ Objects.CorrectedEvent.ann 0 C.r (4 * C.r) := hBinA hu
  have hcheapcost := attach_of_cheap C D Db f hforget hL hWeyl hf hfB hBinA hzcheap hzA huA
  
  obtain ⟨p₁, hp₁, hp₁eq⟩ := hPtK
  obtain ⟨p₂, hp₂, hp₂eq⟩ := hzK
  have hloopcost : Db.internal (Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (⟨P t, hPtA⟩, ⟨z, hzA⟩) ≤ D.len π u₁ v₁ := by
    have hπA : ∀ q ∈ Icc u₁ v₁, π q ∈ Objects.CorrectedEvent.ann 0 C.r (4 * C.r) := fun q hq =>
      hA _ (hKball ⟨q, hq, rfl⟩)
    rcases le_total p₁ p₂ with h12 | h21
    · have hsub : D.IsCurve π p₁ p₂ := ⟨h12, hπ.2.mono (Icc_subset_Icc hp₁.1 hp₂.2)⟩
      have hsubb := Objects.Splice.bumped_curve_transfer C D Db f hforget hWeyl hf hL hsub
      have h1 := internal_le_len_pts Db hsubb (fun q hq => hπA q ⟨hp₁.1.trans hq.1, hq.2.trans hp₂.2⟩)
        hPtA hzA hp₁eq hp₂eq
      have h2 := (Objects.Splice.bumped_length_bounds C D Db f hforget hWeyl hf hsub).2
      have h3 : D.len π p₁ p₂ ≤ D.len π u₁ v₁ :=
        LQGMetric.MetricGeometry.curveLength_mono _ hp₁.1 hp₂.2
      exact h1.trans (h2.trans h3)
    · have hsub : D.IsCurve π p₂ p₁ := ⟨h21, hπ.2.mono (Icc_subset_Icc hp₂.1 hp₁.2)⟩
      have hsubb := Objects.Splice.bumped_curve_transfer C D Db f hforget hWeyl hf hL hsub
      have h1 := internal_le_len_pts Db hsubb (fun q hq => hπA q ⟨hp₂.1.trans hq.1, hq.2.trans hp₁.2⟩)
        hzA hPtA hp₂eq hp₁eq
      have h2 := (Objects.Splice.bumped_length_bounds C D Db f hforget hWeyl hf hsub).2
      have h3 : D.len π p₂ p₁ ≤ D.len π u₁ v₁ :=
        LQGMetric.MetricGeometry.curveLength_mono _ hp₂.1 hp₁.2
      rw [internal_symm]
      exact h1.trans (h2.trans h3)
  refine ⟨s, t, hαs, hsβ, hβt, ht.2, ?_, ?_, hPtA, huA, ?_⟩
  · exact hmapsst
  · linarith only [htime_low, hs'β, hβt.le]
  · 
    have htri := internal_triangle Db (Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) ⟨P t, hPtA⟩ ⟨z, hzA⟩ ⟨u, huA⟩
    have hst' : s' - s ≤ t - s := by linarith only [hs'β, hβt]
    have hloop2 : D.len π u₁ v₁ ≤ ENNReal.ofReal (2 * (H / C.r) ^ (-(1 : ℝ) / 4) * (t - s)) := by
      refine hπlen.le.trans (ENNReal.ofReal_le_ofReal ?_)
      have := mul_le_mul_of_nonneg_left hst' hcoeff.le
      linarith only [this]
    calc Db.internal (Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (⟨P t, hPtA⟩, ⟨u, huA⟩)
        ≤ Db.internal (Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (⟨P t, hPtA⟩, ⟨z, hzA⟩) +
          Db.internal (Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (⟨z, hzA⟩, ⟨u, huA⟩) := htri
      _ ≤ ENNReal.ofReal (2 * (H / C.r) ^ (-(1 : ℝ) / 4) * (t - s)) +
          ENNReal.ofReal (2 * C.lamConst * (Real.exp (-C.ξ * C.A_max) * dt)) :=
          add_le_add (hloopcost.trans hloop2) hcheapcost.le
      _ = ENNReal.ofReal (2 * C.lamConst * (Real.exp (-C.ξ * C.A_max) * dt) +
            2 * (H / C.r) ^ (-(1 : ℝ) / 4) * (t - s)) := by
          have hdt0 : 0 < dt := pos_of_mul_pos_right hdt C.lamPos.le
          have hA : 0 ≤ 2 * C.lamConst * (Real.exp (-C.ξ * C.A_max) * dt) :=
            mul_nonneg (mul_nonneg zero_le_two C.lamPos.le) (mul_nonneg (Real.exp_pos _).le hdt0.le)
          have hts : 0 ≤ t - s := by linarith only [hs'β, hβt, hss']
          have hB : 0 ≤ 2 * (H / C.r) ^ (-(1 : ℝ) / 4) * (t - s) :=
            mul_nonneg (mul_nonneg zero_le_two hcoeff.le) hts
          rw [add_comm, ← ENNReal.ofReal_add hA hB]

end SupercriticalLQGUniqueness.Uniqueness.Objects.Producer
