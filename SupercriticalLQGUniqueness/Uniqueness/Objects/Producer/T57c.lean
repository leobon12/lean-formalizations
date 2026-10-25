import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.T57




 



















set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Producer

 
theorem t57_centre0 (C : Objects.CorrectedEvent.Constants) (D Dt Db Dtb : LSCMetric) (f : C(ℂ, ℝ))
    (hLD : D.IsLengthSpace) (hforgetD : Continuous (BiLipschitz.Barrier.forget D)) (hLDt : Dt.IsLengthSpace)
    (hforgetDt : Continuous (BiLipschitz.Barrier.forget Dt))
    (hWD : ∀ x y : ℂ, Db (x, y) = weylScale C.ξ (-f) D (x, y))
    (hWDt : ∀ x y : ℂ, Dtb (x, y) = weylScale C.ξ (-f) Dt (x, y))
    (hf : ∀ x : ℂ, 0 ≤ f x ∧ f x ≤ C.A_max)
    {V : Set ℂ} (hV : IsOpen V) (hfV : ∀ x ∉ V, f x = 0)
    {Cp Cmid0 Cmid : ℝ} (hCp : 0 < Cp) (hCmid0 : 0 ≤ Cmid0) (hCmid : 0 ≤ Cmid)
    (hle : ∀ x y : ℂ, Dt (x, y) ≤ ENNReal.ofReal Cp * D (x, y))
    (hratio : (1 + 10 * Cp * C.lamConst) * Cmid0 ≤ Cmid * (1 - 10 * Cp * C.lamConst))
    {R₀ : NNReal} {dt N : ℝ} (hR₀ : 0 < R₀) (hdt : 0 < dt) (hN : 0 < N)
    (hlam : C.lamConst ≤ 1 / 48) (hsup_s : C.A_sup * C.r ≤ R₀)
    (hnar_s : 3 * C.A_nar * C.r ≤ (R₀ : ℝ) / 2) (hnar1 : C.A_nar < 1)
    (hcount : ∀ k : ℕ, (1 / 2 : ℝ) ^ (k + 1) < C.A_nar →
      21 * (((k : ℝ) + 3) * (C.ξ * (C.Q + 3)) + Real.logb 2 (2 * C.A_around) + 2) ≤
        cSel * ((R₀ : ℝ) / C.r) * (2 : ℝ) ^ ((k : ℝ) / 4))
    (hnarrow : ∀ (z w : ℂ) (hz : z ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r))
      (hw : w ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r)), dist z w ≤ C.A_nar / C.lamConst * C.r →
      ENNReal.ofReal ((dist z w / C.r) ^ (C.ξ * (C.Q + 3))) * ENNReal.ofReal N ≤
        D.internal (Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (⟨z, mid_ann_subset C hz⟩, ⟨w, mid_ann_subset C hw⟩))
    (hcompare : ∀ y ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r), ∀ δ : ℝ, 0 < δ → δ ≤ C.A_nar →
      Objects.CorrectedEvent.around D y (2 * δ * C.r) (3 * δ * C.r) ≤
        ENNReal.ofReal (δ ^ (-(1 : ℝ) / 4)) * Objects.CorrectedEvent.acr D y (δ * C.r / 4) (δ * C.r / 2))
    
    {P : ℝ → ℂ} {L : ℝ} (hPb : Db.IsCurve P 0 L) (hunit : HasUnitSpeedOn (Db.pt ∘ P) (Icc 0 L))
    (hgeoP : Db.len P 0 L = Db (P 0, P L))
    {τ' σ' τ σ τ₀ σ₀ : ℝ} (h0τ₀ : 0 ≤ τ₀) (hτ₀τ : τ₀ ≤ τ) (hσσ₀ : σ ≤ σ₀) (hσ₀L : σ₀ ≤ L)
    (hτ'τ : τ' ≤ τ) (hσσ' : σ ≤ σ') (hσ₀ : ‖P σ₀‖ = 3 * C.r)
    (hσ₀τ₀ : σ₀ - τ₀ ≤ 2 * C.A_around * N)
    (hloc : ∀ x ∈ Icc τ σ, P x ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r))
    
    {cu cv u v : ℂ}
    (hfB_u : ∀ x ∈ closedBall cu (R₀ : ℝ), f x = C.A_max)
    (hfB_v : ∀ x ∈ closedBall cv (R₀ : ℝ), f x = C.A_max)
    (hu : u ∈ closedBall cu (R₀ : ℝ)) (hu2 : dist u cu < (R₀ : ℝ) / 2)
    (hv : v ∈ closedBall cv (R₀ : ℝ)) (hv2 : dist v cv < (R₀ : ℝ) / 2)
    (hAnn_u : ball cu ((R₀ : ℝ) + C.A_sup * C.r + 3 * C.A_nar * C.r) ⊆
      Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r))
    (hAnn_v : ball cv ((R₀ : ℝ) + C.A_sup * C.r + 3 * C.A_nar * C.r) ⊆
      Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r))
    (hBinA_u : closedBall cu (R₀ : ℝ) ⊆ Objects.CorrectedEvent.ann 0 C.r (4 * C.r))
    (hBinA_v : closedBall cv (R₀ : ℝ) ⊆ Objects.CorrectedEvent.ann 0 C.r (4 * C.r))
    (hsepB : ∀ x ∈ ball cu ((R₀ : ℝ) + (C.A_sup + C.A_nar) * C.r),
      ∀ y ∈ ball cv ((R₀ : ℝ) + (C.A_sup + C.A_nar) * C.r), C.A_nar * C.r ≤ dist x y)
    (hdtu : Dt (u, v) = ENNReal.ofReal dt)
    (hF1 : ENNReal.ofReal dt ≤ ENNReal.ofReal Cmid0 * D (u, v))
    (hblock : Dtb.internal (Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (⟨u, hBinA_u hu⟩, ⟨v, hBinA_v hv⟩) ≤
      ENNReal.ofReal (Real.exp (-C.ξ * C.A_max) * dt))
    (hbad_u : Objects.Shadow.circleOuter cu R₀ 0
      (sphere cu (R₀ : ℝ) \ goodSet D cu u (R₀ : ℝ) (C.lamConst * dt) hu) ≤
        ENNReal.ofReal (C.lamConst * R₀ / 2))
    (hbad_v : Objects.Shadow.circleOuter cv R₀ 0
      (sphere cv (R₀ : ℝ) \ goodSet D cv v (R₀ : ℝ) (C.lamConst * dt) hv) ≤
        ENNReal.ofReal (C.lamConst * R₀ / 2))
    (hnear_u : Objects.Shadow.circleOuter cu R₀ 0 (hitSet P τ' σ' (2 * C.A_sup * C.r)) ≤
      ENNReal.ofReal (C.lamConst * R₀))
    (hnear_v : Objects.Shadow.circleOuter cv R₀ 0 (hitSet P τ' σ' (2 * C.A_sup * C.r)) ≤
      ENNReal.ofReal (C.lamConst * R₀))
    
    {au bu av bv : ℝ} (hτau : τ ≤ au) (habu : au < bu) (hbuσ : bu ≤ σ)
    (hτav : τ ≤ av) (habv : av < bv) (hbvσ : bv ≤ σ)
    (hPau : ‖P au - cu‖ = (R₀ : ℝ) + C.A_sup * C.r) (hPbu : ‖P bu - cu‖ = (R₀ : ℝ) + C.A_sup * C.r)
    (hPav : ‖P av - cv‖ = (R₀ : ℝ) + C.A_sup * C.r) (hPbv : ‖P bv - cv‖ = (R₀ : ℝ) + C.A_sup * C.r)
    (hfar_u : (R₀ : ℝ) / 8 ≤ dist (P au) (P bu)) (hfar_v : (R₀ : ℝ) / 8 ≤ dist (P av) (P bv))
    (hmid_u : ∀ t ∈ Icc au bu, P t ∈ ball cu ((R₀ : ℝ) + C.A_sup * C.r + C.A_nar * C.r))
    (hmid_v : ∀ t ∈ Icc av bv, P t ∈ ball cv ((R₀ : ℝ) + C.A_sup * C.r + C.A_nar * C.r))
    (hwin_u : ∀ t ∈ Ioo au bu, P t ∈ V → P t ∈ ball cu ((R₀ : ℝ) + C.A_sup * C.r))
    (hwin_v : ∀ t ∈ Ioo av bv, P t ∈ V → P t ∈ ball cv ((R₀ : ℝ) + C.A_sup * C.r))
    (hshort : σ - τ < C.A_nar ^ (C.ξ * (C.Q + 3)) * N) :
    ∃ s t : ℝ, τ ≤ s ∧ s < t ∧ t ≤ σ ∧
      Real.exp (-C.ξ * C.A_max) * (C.A_nar ^ (C.ξ * (C.Q + 3)) * N) ≤ t - s ∧
      ∃ (hs : P s ∈ Metric.ball (0 : ℂ) (4 * C.r)) (ht : P t ∈ Metric.ball (0 : ℂ) (4 * C.r)),
        Dtb.internal (Metric.ball (0 : ℂ) (4 * C.r)) (⟨P s, hs⟩, ⟨P t, ht⟩) ≤
          ENNReal.ofReal (Cmid * (t - s)) := by
  have hlam1 : C.lamConst ≤ 1 := by linarith only [hlam]
  have h0τ : 0 ≤ τ := h0τ₀.trans hτ₀τ
  have hσL : σ ≤ L := hσσ₀.trans hσ₀L
  
  obtain ⟨tu, htu, hPtu, hattu⟩ := lem_endpt_close' C D Db f hLD hforgetD hWD hf hV hfV hR₀ hdt hN
    hfB_u hu hu2 hAnn_u hBinA_u hlam hsup_s hnar_s hnar1 hPb hunit hgeoP h0τ₀ (hτ₀τ.trans hτau) habu
    (hτ'τ.trans hτau) (hbuσ.trans hσσ') (hbuσ.trans hσσ₀) hσ₀L hσ₀ hσ₀τ₀ hPau hPbu hfar_u hmid_u
    hwin_u (by linarith only [hshort, hτau, hbuσ]) hnarrow hcompare hbad_u hnear_u hcount
  
  obtain ⟨tv, htv, hPtv, hattv⟩ := lem_endpt_close' C D Db f hLD hforgetD hWD hf hV hfV hR₀ hdt hN
    hfB_v hv hv2 hAnn_v hBinA_v hlam hsup_s hnar_s hnar1 hPb hunit hgeoP h0τ₀ (hτ₀τ.trans hτav) habv
    (hτ'τ.trans hτav) (hbvσ.trans hσσ') (hbvσ.trans hσσ₀) hσ₀L hσ₀ hσ₀τ₀ hPav hPbv hfar_v hmid_v
    hwin_v (by linarith only [hshort, hτav, hbvσ]) hnarrow hcompare hbad_v hnear_v hcount
  obtain ⟨hPu, huA, hu5⟩ := hattu
  obtain ⟨hPv, hvA, hv5⟩ := hattv
  exact t57_from_attachments C D Dt Db Dtb f hforgetD hLDt hforgetDt hWD hWDt hf hCp hCmid0 hCmid hle
    hratio hlam1 hnarrow hPb hunit hgeoP hdt hdtu hF1 (hBinA_u hu) (hBinA_v hv) hblock h0τ hσL
    ⟨hτau.trans htu.1, htu.2.trans hbuσ⟩ ⟨hτav.trans htv.1, htv.2.trans hbvσ⟩ hloc
    (hsepB _ hPtu _ hPtv) ⟨hPu, hu5⟩ ⟨hPv, hv5⟩

end SupercriticalLQGUniqueness.Uniqueness.Objects.Producer
