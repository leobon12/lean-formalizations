import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.EA7




 





















set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Complex
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Producer

 
theorem lem_endpt_close' (C : Objects.CorrectedEvent.Constants) (D Db : LSCMetric) (f : C(ℂ, ℝ))
    (hL : D.IsLengthSpace) (hforget : Continuous (BiLipschitz.Barrier.forget D))
    (hWeyl : ∀ x y : ℂ, Db (x, y) = weylScale C.ξ (-f) D (x, y))
    (hf : ∀ x : ℂ, 0 ≤ f x ∧ f x ≤ C.A_max)
    {V : Set ℂ} (hV : IsOpen V) (hfV : ∀ x ∉ V, f x = 0)
    {c u : ℂ} {R₀ : NNReal} {dt N : ℝ} (hR₀ : 0 < R₀) (hdt : 0 < dt) (hN : 0 < N)
    (hfB : ∀ x ∈ closedBall c (R₀ : ℝ), f x = C.A_max)
    (hu : u ∈ closedBall c (R₀ : ℝ)) (hu2 : dist u c < (R₀ : ℝ) / 2)
    (hAnn : ball c ((R₀ : ℝ) + C.A_sup * C.r + 3 * C.A_nar * C.r) ⊆
      Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r))
    (hBinA : closedBall c (R₀ : ℝ) ⊆ Objects.CorrectedEvent.ann 0 C.r (4 * C.r))
    (hlam : C.lamConst ≤ 1 / 48) (hsup_s : C.A_sup * C.r ≤ R₀)
    (hnar_s : 3 * C.A_nar * C.r ≤ (R₀ : ℝ) / 2) (hnar1 : C.A_nar < 1)
    {P : ℝ → ℂ} {L : ℝ} (hPb : Db.IsCurve P 0 L) (hunit : HasUnitSpeedOn (Db.pt ∘ P) (Icc 0 L))
    (hgeoP : Db.len P 0 L = Db (P 0, P L))
    {a b τ' σ' τ₀ σ₀ : ℝ} (h0τ₀ : 0 ≤ τ₀) (hτ₀a : τ₀ ≤ a) (hab : a < b) (hτ'a : τ' ≤ a)
    (hbσ' : b ≤ σ') (hbσ₀ : b ≤ σ₀) (hσ₀L : σ₀ ≤ L) (hσ₀ : ‖P σ₀‖ = 3 * C.r)
    (hσ₀τ₀ : σ₀ - τ₀ ≤ 2 * C.A_around * N)
    (hPa : ‖P a - c‖ = (R₀ : ℝ) + C.A_sup * C.r) (hPb' : ‖P b - c‖ = (R₀ : ℝ) + C.A_sup * C.r)
    (hfar : (R₀ : ℝ) / 8 ≤ dist (P a) (P b))
    (hmid : ∀ t ∈ Icc a b, P t ∈ ball c ((R₀ : ℝ) + C.A_sup * C.r + C.A_nar * C.r))
    (hwin : ∀ t ∈ Ioo a b, P t ∈ V → P t ∈ ball c ((R₀ : ℝ) + C.A_sup * C.r))
    (hshort : b - a < C.A_nar ^ (C.ξ * (C.Q + 3)) * N)
    (hnarrow : ∀ (z w : ℂ) (hz : z ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r))
      (hw : w ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r)), dist z w ≤ C.A_nar / C.lamConst * C.r →
      ENNReal.ofReal ((dist z w / C.r) ^ (C.ξ * (C.Q + 3))) * ENNReal.ofReal N ≤
        D.internal (Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (⟨z, mid_ann_subset C hz⟩, ⟨w, mid_ann_subset C hw⟩))
    (hcompare : ∀ y ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r), ∀ δ : ℝ, 0 < δ → δ ≤ C.A_nar →
      Objects.CorrectedEvent.around D y (2 * δ * C.r) (3 * δ * C.r) ≤
        ENNReal.ofReal (δ ^ (-(1 : ℝ) / 4)) * Objects.CorrectedEvent.acr D y (δ * C.r / 4) (δ * C.r / 2))
    (hbad : Objects.Shadow.circleOuter c R₀ 0
      (sphere c (R₀ : ℝ) \ goodSet D c u (R₀ : ℝ) (C.lamConst * dt) hu) ≤
        ENNReal.ofReal (C.lamConst * R₀ / 2))
    (hnear : Objects.Shadow.circleOuter c R₀ 0 (hitSet P τ' σ' (2 * C.A_sup * C.r)) ≤
      ENNReal.ofReal (C.lamConst * R₀))
    (hcount : ∀ k : ℕ, (1 / 2 : ℝ) ^ (k + 1) < C.A_nar →
      21 * (((k : ℝ) + 3) * (C.ξ * (C.Q + 3)) + Real.logb 2 (2 * C.A_around) + 2) ≤
        cSel * ((R₀ : ℝ) / C.r) * (2 : ℝ) ^ ((k : ℝ) / 4)) :
    ∃ t ∈ Icc a b, P t ∈ ball c ((R₀ : ℝ) + (C.A_sup + C.A_nar) * C.r) ∧
      ∃ (hPt : P t ∈ Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (huA : u ∈ Objects.CorrectedEvent.ann 0 C.r (4 * C.r)),
        Db.internal (Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (⟨P t, hPt⟩, ⟨u, huA⟩) ≤
          ENNReal.ofReal (5 * C.lamConst * (Real.exp (-C.ξ * C.A_max) * dt)) := by
  classical
  have hr := C.rPos
  have hsup := C.supPos
  have hnar := C.narPos
  have hlampos := C.lamPos
  have hsr : 0 < C.A_sup * C.r := mul_pos hsup hr
  have hnr : 0 < C.A_nar * C.r := mul_pos hnar hr
  have hR0r : (0 : ℝ) < R₀ := by exact_mod_cast hR₀
  have hlam1 : C.lamConst ≤ 1 := by linarith only [hlam]
  have hPD : D.IsCurve P 0 L := Objects.Splice.bumped_curve_transfer_back C D Db f hforget hWeyl hf hPb
  have hcont : ContinuousOn P (Icc 0 L) := hforget.comp_continuousOn hPD.2
  have h0a : 0 ≤ a := h0τ₀.trans hτ₀a
  have hbL : b ≤ L := hbσ₀.trans hσ₀L
  have hX0 : 0 < Real.exp (-C.ξ * C.A_max) * dt := mul_pos (Real.exp_pos _) hdt
  have hloc : ∀ t ∈ Icc a b, P t ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r) := fun t ht =>
    hAnn (ball_subset_ball (by linarith only [hnr]) (hmid t ht))
  have hlocA : ∀ t ∈ Icc a b, P t ∈ Objects.CorrectedEvent.ann 0 C.r (4 * C.r) := fun t ht =>
    mid_ann_subset C (hloc t ht)
  have huA : u ∈ Objects.CorrectedEvent.ann 0 C.r (4 * C.r) := hBinA hu
  have hmid' : ∀ t ∈ Icc a b, P t ∈ ball c ((R₀ : ℝ) + (C.A_sup + C.A_nar) * C.r) := by
    intro t ht
    have h := hmid t ht
    have e : (R₀ : ℝ) + (C.A_sup + C.A_nar) * C.r = (R₀ : ℝ) + C.A_sup * C.r + C.A_nar * C.r := by ring
    rw [e]; exact h
  
  by_cases hhit : ∃ t ∈ Icc a b, P t ∈ cheapSet D c u (R₀ : ℝ) (2 * C.lamConst * dt)
  · obtain ⟨t, ht, hcheap⟩ := hhit
    refine ⟨t, ht, hmid' t ht, hlocA t ht, huA, ?_⟩
    have h := attach_of_cheap C D Db f hforget hL hWeyl hf hfB hBinA hcheap (hlocA t ht) huA
    refine h.le.trans (ENNReal.ofReal_le_ofReal ?_)
    have : 0 < C.lamConst * (Real.exp (-C.ξ * C.A_max) * dt) := mul_pos hlampos hX0
    linarith only [this]
  push Not at hhit
  
  set R₁ : NNReal := ⟨(R₀ : ℝ) + C.A_sup * C.r, by positivity⟩ with hR₁
  set R₂ : NNReal := ⟨(R₀ : ℝ) + C.A_sup * C.r + C.A_nar * C.r, by positivity⟩ with hR₂
  have hR₁def : (R₁ : ℝ) = R₀ + C.A_sup * C.r := rfl
  have hR₂def : (R₂ : ℝ) = R₀ + C.A_sup * C.r + C.A_nar * C.r := rfl
  have hR1r : (0 : ℝ) < R₁ := by rw [hR₁def]; positivity
  have hR₀₁ : (R₀ : ℝ) ≤ R₁ := by rw [hR₁def]; linarith only [hsr]
  have hR₁₀ : R₁ ≤ 2 * R₀ := by
    rw [← NNReal.coe_le_coe, NNReal.coe_mul, hR₁def]
    push_cast
    linarith only [hsup_s]
  have hgap : (R₁ : ℝ) - R₀ < 2 * C.A_sup * C.r := by rw [hR₁def]; linarith only [hsr]
  have hR₁le : (R₁ : ℝ) + C.A_sup * C.r ≤ R₀ + 2 * C.A_sup * C.r := by rw [hR₁def]; linarith only
  have hR₁₂ : (R₁ : ℝ) < R₂ := by rw [hR₁def, hR₂def]; linarith only [hnr]
  have hdtlam : 0 < C.lamConst * dt := mul_pos hlampos hdt
  have hsub : Icc a b ⊆ Icc τ' σ' := Icc_subset_Icc hτ'a hbσ'
  have hcab : ContinuousOn P (Icc a b) := hcont.mono (Icc_subset_Icc h0a hbL)
  have hPDab : MapsTo P (Icc a b) (closedBall c (R₂ : ℝ)) := fun t ht =>
    ball_subset_closedBall (by rw [hR₂def]; exact hmid t ht)
  have hPa' : P a ∈ sphere c (R₁ : ℝ) := by rw [mem_sphere, dist_eq_norm, hR₁def]; exact hPa
  have hPb'' : P b ∈ sphere c (R₁ : ℝ) := by rw [mem_sphere, dist_eq_norm, hR₁def]; exact hPb'
  
  obtain ⟨θ₀, W', hW's, hmass, hW'⟩ := shadow_mass C D hforget hR₀ hR₀₁ hR₁₀ hgap hR₁le hR₁₂ hdtlam
    hlam hu hab.le hsub hcab hPDab hPa' hPb'' hfar hhit hbad hnear
  
  set S := chargedExc P c (R₁ : ℝ) (C.A_sup * C.r) a b W' with hS
  have hwin' : ∀ t ∈ Ioo a b, P t ∈ V → P t ∈ ball c (R₁ : ℝ) := by
    intro t ht hV'; rw [hR₁def]; exact hwin t ht hV'
  have hreachS : ∀ e ∈ S, C.A_sup * C.r ≤ excReach P e ∧ excReach P e < C.A_nar * C.r :=
    fun e he => chargedExc_reach C D Db f hforget hWeyl hPD hunit hcont hnarrow hlam1 hV hfV h0a hbL
      hshort hwin' hloc he
  have hεwin : C.A_sup * C.r ≤ C.A_nar / C.lamConst * C.r := by
    have h1 : C.A_sup ≤ C.A_nar := by
      have := C.supLtSet; have := C.setLtNar; linarith only [C.supLtSet, C.setLtNar]
    have h2 : C.A_nar ≤ C.A_nar / C.lamConst := by
      rw [le_div_iff₀ hlampos]
      calc C.A_nar * C.lamConst ≤ C.A_nar * 1 := mul_le_mul_of_nonneg_left hlam1 hnar.le
        _ = C.A_nar := mul_one _
    exact mul_le_mul_of_nonneg_right (h1.trans h2) hr.le
  have htimeS : ∀ e ∈ S, (C.A_sup * C.r / C.r) ^ (C.ξ * (C.Q + 3)) * N ≤ e.2 - e.1 :=
    fun e he => chargedExc_time C D Db f hforget hWeyl hPD hunit hcont hnarrow hV hfV hsr hεwin h0a
      hbL hwin' hloc he
  have hδ : 0 < (C.A_sup * C.r / C.r) ^ (C.ξ * (C.Q + 3)) * N :=
    mul_pos (Real.rpow_pos_of_pos (div_pos hsr hr) _) hN
  have hSfin : S.Finite := chargedExc_finite hδ htimeS
  have hcov := cover_by_caps (P := P) (W' := W') hR1r hsr hcab (by rw [hR₁def]; exact hPa)
    (by rw [hR₁def]; exact hPb') (fun w hw => (hW' w hw).2) hW's
  
  have hcen : ∀ e ∈ S, P e.1 ∈ sphere c (R₁ : ℝ) := by
    intro e he; rw [mem_sphere, dist_eq_norm]; exact he.2.2.2.1
  obtain ⟨k, T, hTS, hTbin, hTdisj, hTcard, hknar⟩ := dyadic_selection (P := P) (S := S)
    (R₁ := R₁) (θ₀ := θ₀) hR₀ (by exact_mod_cast hR1r) hr hsup hnar1 hSfin hreachS hcen hcov hmass
  
  have hAnn' : ball c ((R₁ : ℝ) + 3 * C.A_nar * C.r) ⊆ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r) := by
    rw [hR₁def]; exact hAnn
  have hmid'' : ∀ t ∈ Icc a b, P t ∈ ball c ((R₁ : ℝ) + C.A_nar * C.r) := by
    intro t ht; rw [hR₁def]; exact hmid t ht
  have hpa : ∀ e ∈ T, ∃ s t : ℝ, e.1 ≤ s ∧ s ≤ e.2 ∧ e.2 < t ∧ t ≤ σ₀ ∧
      MapsTo P (Icc s t) (ball (P e.1) (3 * excReach P e)) ∧
      (excReach P e / (4 * C.r)) ^ (C.ξ * (C.Q + 3)) * N ≤ t - s ∧
      ∃ (hPt : P t ∈ Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (huA : u ∈ Objects.CorrectedEvent.ann 0 C.r (4 * C.r)),
        Db.internal (Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (⟨P t, hPt⟩, ⟨u, huA⟩) ≤
          ENNReal.ofReal (2 * C.lamConst * (Real.exp (-C.ξ * C.A_max) * dt) +
            2 * (excReach P e / C.r) ^ (-(1 : ℝ) / 4) * (t - s)) :=
    fun e he => paid_attachment C D Db f hforget hL hWeyl hf hV hfV hR₀ hR₁def hdtlam hN.le hfB hu hu2
      hAnn' hBinA hnar_s hPD hunit hcont hnarrow hcompare hlam1 h0a hbσ₀ hσ₀L hσ₀ hshort hwin' hmid''
      hhit (fun w hw => (hW' w hw).1) (hTS he)
  obtain ⟨st, fn, hst⟩ : ∃ st fn : ℝ × ℝ → ℝ, ∀ e ∈ T, e.1 ≤ st e ∧ st e ≤ e.2 ∧ e.2 < fn e ∧
      fn e ≤ σ₀ ∧ MapsTo P (Icc (st e) (fn e)) (ball (P e.1) (3 * excReach P e)) ∧
      (excReach P e / (4 * C.r)) ^ (C.ξ * (C.Q + 3)) * N ≤ fn e - st e ∧
      ∃ (hPt : P (fn e) ∈ Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (huA : u ∈ Objects.CorrectedEvent.ann 0 C.r (4 * C.r)),
        Db.internal (Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (⟨P (fn e), hPt⟩, ⟨u, huA⟩) ≤
          ENNReal.ofReal (2 * C.lamConst * (Real.exp (-C.ξ * C.A_max) * dt) +
            2 * (excReach P e / C.r) ^ (-(1 : ℝ) / 4) * (fn e - st e)) := by
    choose! st fn hst using hpa
    exact ⟨st, fn, hst⟩
  clear hpa
  
  have has0 : 0 < C.ξ * (C.Q + 3) := mul_pos C.ξPos (by linarith only [C.QPos])
  obtain ⟨Lk, hLk⟩ : ∃ Lk : ℝ, Lk = (2 : ℝ) ^ (-((k : ℝ) + 3) * (C.ξ * (C.Q + 3))) * N := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = 2 * C.A_around * N := ⟨_, rfl⟩
  have hLk0 : 0 < Lk := by rw [hLk]; exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hN
  have haround := C.aroundGtOne
  have hLkU : Lk ≤ U := by
    have h1 : (2 : ℝ) ^ (-((k : ℝ) + 3) * (C.ξ * (C.Q + 3))) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (by positivity)) has0.le)
    have h2 : (1 : ℝ) ≤ 2 * C.A_around := by linarith only [haround]
    rw [hLk, hU]
    calc (2 : ℝ) ^ (-((k : ℝ) + 3) * (C.ξ * (C.Q + 3))) * N ≤ 1 * N :=
          mul_le_mul_of_nonneg_right h1 hN.le
      _ ≤ 2 * C.A_around * N := mul_le_mul_of_nonneg_right h2 hN.le
  obtain ⟨d, hd⟩ : ∃ d : ℝ × ℝ → ℝ, d = fun e => fn e - st e := ⟨_, rfl⟩
  have hdval : ∀ e, d e = fn e - st e := fun e => by rw [hd]
  have hdT : ∀ e ∈ T, d e ∈ Icc Lk U := by
    intro e he
    obtain ⟨h1, h2, h3, h4, -, h6, -⟩ := hst e he
    have heS := hTS he
    rw [hdval]
    refine ⟨?_, ?_⟩
    · have hlow := time_low_k (H := excReach P e) hr has0.le (hTbin e he).1
      rw [hLk]
      exact le_trans (mul_le_mul_of_nonneg_right hlow hN.le) h6
    · have ha1 : a ≤ e.1 := heS.1
      rw [hU]
      linarith only [hσ₀τ₀, hτ₀a, ha1, h1, h4]
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (2 : ℝ) ^ (((k : ℝ) + 1) / 4) := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by rw [hK]; exact Real.one_le_rpow (by norm_num) (by positivity)
  have hBdef := _root_.SupercriticalLQGUniqueness.Uniqueness.Objects.EndpointAttachmentCore.endpoint_time_bin_log_ratio (k := k) (a := C.ξ * (C.Q + 3)) hN
    (by linarith only [haround] : (0 : ℝ) < C.A_around)
  have hquota : ∀ M : ℕ, (M : ℝ) ≤ Real.logb 2 (U / Lk) + 2 → (M : ℝ) * (1 + 16 * K) ≤ T.card := by
    intro M hM
    obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (2 : ℝ) ^ ((k : ℝ) / 4) := ⟨_, rfl⟩
    have hx1 : 1 ≤ x := by rw [hx]; exact Real.one_le_rpow (by norm_num) (by positivity)
    have hB : Real.logb 2 (U / Lk) + 2 =
        ((k : ℝ) + 3) * (C.ξ * (C.Q + 3)) + Real.logb 2 (2 * C.A_around) + 2 := by
      rw [hU, hLk]; exact hBdef
    have hlog : 0 < Real.logb 2 (2 * C.A_around) :=
      Real.logb_pos (by norm_num) (by linarith only [haround])
    have hBpos : 0 < Real.logb 2 (U / Lk) + 2 := by
      rw [hB]
      have : 0 ≤ ((k : ℝ) + 3) * (C.ξ * (C.Q + 3)) := by positivity
      linarith only [this, hlog]
    have hlarge : 21 * (Real.logb 2 (U / Lk) + 2) ≤ cSel * ((R₀ : ℝ) / C.r) * x := by
      rw [hB, hx]; exact hcount k hknar
    have hcard : cSel * ((R₀ : ℝ) / C.r) * x ^ 2 ≤ (T.card : ℝ) := by
      have hx2 : x ^ 2 = Real.sqrt 2 ^ k := by
        rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        congr 1; push_cast; ring
      rw [hx2]; exact hTcard
    have hfin := _root_.SupercriticalLQGUniqueness.Uniqueness.Objects.EndpointAttachmentCore.source_count_quota hx1 hBpos hM hlarge hcard
    have hKx : (2 : ℝ) ^ ((1 : ℝ) / 4) * x = K := by
      rw [hx, hK, ← Real.rpow_add (by norm_num)]
      congr 1; ring
    rw [hKx] at hfin
    exact hfin
  obtain ⟨M, j, hM, hj, hbin⟩ :=
    _root_.SupercriticalLQGUniqueness.Uniqueness.Objects.EndpointAttachmentCore.many_in_one_dyadic_bin_real T d hLk0 hLkU hdT (1 + 16 * K) hquota
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = Lk * (2 : ℝ) ^ j := ⟨_, rfl⟩
  have hq0 : 0 < q := by rw [hq]; exact mul_pos hLk0 (by positivity)
  rw [← hq] at hbin
  obtain ⟨Tj, hTj⟩ : ∃ Tj : Finset (ℝ × ℝ), Tj = T.filter (fun e => q ≤ d e ∧ d e < 2 * q) :=
    ⟨_, rfl⟩
  rw [← hTj] at hbin
  have hTjmem : ∀ e ∈ Tj, e ∈ T ∧ q ≤ d e ∧ d e < 2 * q := fun e he => by
    rw [hTj, Finset.mem_filter] at he; exact he
  have hTjne : Tj.Nonempty := by
    rw [← Finset.card_pos]
    have : (1 : ℝ) ≤ Tj.card := le_trans (by linarith only [hK1]) hbin
    exact_mod_cast (show (0 : ℝ) < Tj.card by linarith only [this])
  
  have hballA : ∀ e ∈ T, ball (P e.1) (3 * excReach P e) ⊆ Objects.CorrectedEvent.ann 0 C.r (4 * C.r) := by
    intro e he z hz
    apply mid_ann_subset C
    apply hAnn'
    have hyc : ‖P e.1 - c‖ = R₁ := (hTS he).2.2.2.1
    have hH := (hreachS e (hTS he)).2
    rw [mem_ball] at hz ⊢
    calc dist z c ≤ dist z (P e.1) + dist (P e.1) c := dist_triangle _ _ _
      _ < 3 * excReach P e + R₁ := by rw [dist_eq_norm (P e.1) c, hyc]; linarith only [hz]
      _ ≤ (R₁ : ℝ) + 3 * C.A_nar * C.r := by linarith only [hH]
  obtain ⟨cost, hcost⟩ : ∃ cost : ℝ × ℝ → ℝ, cost = fun e =>
      2 * C.lamConst * (Real.exp (-C.ξ * C.A_max) * dt) +
        2 * (excReach P e / C.r) ^ (-(1 : ℝ) / 4) * d e := ⟨_, rfl⟩
  have hcostval : ∀ e, cost e = 2 * C.lamConst * (Real.exp (-C.ξ * C.A_max) * dt) +
      2 * (excReach P e / C.r) ^ (-(1 : ℝ) / 4) * d e := fun e => by rw [hcost]
  have hgeo : LQGMetric.MetricGeometry.IsGeodesicCurve (Db.pt ∘ P) 0 L := by
    refine ⟨h0a.trans (hab.le.trans hbL), hPb.2, ?_⟩
    show LQGMetric.MetricGeometry.curveLength (Db.pt ∘ P) 0 L = edist (Db.pt (P 0)) (Db.pt (P L))
    rw [← Db.len_eq_curveLength]; exact hgeoP
  have hsepT : ∀ e ∈ Tj, ∀ e' ∈ Tj, e ≠ e' → q ≤ |fn e - fn e'| := by
    intro e he e' he' hne
    obtain ⟨heT, hqe, -⟩ := hTjmem e he
    obtain ⟨heT', hqe', -⟩ := hTjmem e' he'
    obtain ⟨-, -, -, -, hm, -, -⟩ := hst e heT
    obtain ⟨-, -, -, -, hm', -, -⟩ := hst e' heT'
    have hdisj := hTdisj e heT e' heT' hne
    have hdisj' : Disjoint (ball (P e.1) (3 * excReach P e)) (ball (P e'.1) (3 * excReach P e')) :=
      Disjoint.mono ball_subset_closedBall ball_subset_closedBall hdisj
    rw [hdval] at hqe hqe'
    have hle : st e ≤ fn e := by linarith only [hqe, hq0]
    have hle' : st e' ≤ fn e' := by linarith only [hqe', hq0]
    rcases order_of_disjoint_images hdisj' hle hle' hm hm' with h | h
    · rw [abs_sub_comm, abs_of_pos (by linarith only [h, hqe', hq0])]
      linarith only [h, hqe']
    · rw [abs_of_pos (by linarith only [h, hqe, hq0])]
      linarith only [h, hqe]
  have hstartT : ∀ e ∈ Tj, a ≤ st e ∧ st e ≤ b ∧ 0 ≤ st e ∧ st e < fn e ∧ fn e ≤ L ∧
      fn e - st e < 2 * q := by
    intro e he
    obtain ⟨heT, hqe, hqe2⟩ := hTjmem e he
    obtain ⟨h1, h2, h3, h4, -, -, -⟩ := hst e heT
    have heS := hTS heT
    rw [hdval] at hqe hqe2
    exact ⟨heS.1.trans h1, h2.trans heS.2.2.1, h0a.trans (heS.1.trans h1),
      by linarith only [hqe, hq0], h4.trans hσ₀L, hqe2⟩
  have hcontT : ∀ e ∈ Tj, ContinuousOn (Db.pt ∘ P) (Icc (st e) (fn e)) := by
    intro e he
    obtain ⟨-, -, h0, -, hfL, -⟩ := hstartT e he
    exact hPb.2.mono (Icc_subset_Icc h0 hfL)
  have hmapsT : ∀ e ∈ Tj, MapsTo (Db.pt ∘ P) (Icc (st e) (fn e)) (Db.pt '' Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) := by
    intro e he x hx
    obtain ⟨heT, -, -⟩ := hTjmem e he
    obtain ⟨-, -, -, -, hm, -, -⟩ := hst e heT
    exact ⟨P x, hballA e heT (hm hx), rfl⟩
  have hcost0T : ∀ e ∈ Tj, 0 ≤ cost e := by
    intro e he
    obtain ⟨heT, hqe, -⟩ := hTjmem e he
    rw [hcostval]
    have hcoeff : 0 ≤ (excReach P e / C.r) ^ (-(1 : ℝ) / 4) :=
      Real.rpow_nonneg (div_nonneg (le_trans hsr.le (hreachS e (hTS heT)).1) hr.le) _
    have hde : 0 ≤ d e := le_trans hq0.le hqe
    have : 0 ≤ 2 * C.lamConst * (Real.exp (-C.ξ * C.A_max) * dt) :=
      mul_nonneg (mul_nonneg zero_le_two hlampos.le) hX0.le
    exact add_nonneg this (mul_nonneg (mul_nonneg zero_le_two hcoeff) hde)
  have hattachT : ∀ e ∈ Tj, LQGMetric.MetricGeometry.internalEDist (Db.pt '' Objects.CorrectedEvent.ann 0 C.r (4 * C.r))
      ((Db.pt ∘ P) (fn e)) (Db.pt u) ≤ ENNReal.ofReal (cost e) := by
    intro e he
    obtain ⟨heT, -, -⟩ := hTjmem e he
    obtain ⟨-, -, -, -, -, -, hPt, huA', hint⟩ := hst e heT
    rw [LSCMetric.internal_eq_internalEDist] at hint
    rw [hcostval, hdval]
    exact hint
  have hpaidT : ∀ e ∈ Tj, cost e ≤ 2 * C.lamConst * (Real.exp (-C.ξ * C.A_max) * dt) + 4 * K * q := by
    intro e he
    obtain ⟨heT, hqe, hqe2⟩ := hTjmem e he
    have hcoeff := coeff_le_K (H := excReach P e) hr (hTbin e heT).1
    rw [← hK] at hcoeff
    have hde0 : 0 ≤ d e := le_trans hq0.le hqe
    have h1 : (excReach P e / C.r) ^ (-(1 : ℝ) / 4) * d e ≤ K * d e :=
      mul_le_mul_of_nonneg_right hcoeff hde0
    have h2 : K * d e ≤ K * (2 * q) := mul_le_mul_of_nonneg_left hqe2.le (by linarith only [hK1])
    rw [hcostval]
    linarith only [h1, h2]
  have hcountT : 16 * K ≤ (Tj.card : ℝ) - 1 := by linarith only [hbin]
  obtain ⟨t, ht, hfinal⟩ := _root_.SupercriticalLQGUniqueness.Uniqueness.Objects.EndpointAttachmentCore.endpoint_attachment_of_separated_returns
    (Y := Db.Space) Tj hTjne (U := Db.pt '' Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (P := Db.pt ∘ P)
    (u := Db.pt u) (a := a) (b := b) (L := L) (q := q) (lam := C.lamConst)
    (X := Real.exp (-C.ξ * C.A_max) * dt) (K := K) st fn cost hq0 hK1 hsepT hstartT hcontT hmapsT
    hgeo hunit hcost0T hattachT hpaidT hcountT
  refine ⟨t, ht, hmid' t ht, hlocA t ht, huA, ?_⟩
  rw [LSCMetric.internal_eq_internalEDist]
  exact hfinal

end SupercriticalLQGUniqueness.Uniqueness.Objects.Producer
