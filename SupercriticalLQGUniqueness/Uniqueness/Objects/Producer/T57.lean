import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.BLb




 













set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Producer

 

theorem narrow_time_bumped (C : Objects.CorrectedEvent.Constants) (D Db : LSCMetric) (f : C(ℂ, ℝ))
    (hforget : Continuous (BiLipschitz.Barrier.forget D))
    (hWeyl : ∀ x y : ℂ, Db (x, y) = weylScale C.ξ (-f) D (x, y))
    (hf : ∀ x : ℂ, 0 ≤ f x ∧ f x ≤ C.A_max)
    {P : ℝ → ℂ} {L : ℝ} (hPD : D.IsCurve P 0 L) (hunit : HasUnitSpeedOn (Db.pt ∘ P) (Icc 0 L))
    (hcont : ContinuousOn P (Icc 0 L)) {N : ℝ}
    (hnarrow : ∀ (z w : ℂ) (hz : z ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r))
      (hw : w ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r)), dist z w ≤ C.A_nar / C.lamConst * C.r →
      ENNReal.ofReal ((dist z w / C.r) ^ (C.ξ * (C.Q + 3))) * ENNReal.ofReal N ≤
        D.internal (Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (⟨z, mid_ann_subset C hz⟩, ⟨w, mid_ann_subset C hw⟩))
    (hlam : C.lamConst ≤ 1)
    {s t : ℝ} (h0s : 0 ≤ s) (hst : s ≤ t) (htL : t ≤ L)
    (hloc : ∀ x ∈ Icc s t, P x ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r))
    (hsep : C.A_nar * C.r ≤ dist (P s) (P t)) :
    Real.exp (-C.ξ * C.A_max) * (C.A_nar ^ (C.ξ * (C.Q + 3)) * N) ≤ t - s := by
  have hr := C.rPos
  have hnar := C.narPos
  have hlampos := C.lamPos
  have hcst : ContinuousOn (fun x => dist (P s) (P x)) (Icc s t) :=
    (continuous_const.dist continuous_id).comp_continuousOn (hcont.mono (Icc_subset_Icc h0s htL))
  obtain ⟨t', ht', hdt'⟩ := intermediate_value_Icc hst hcst
    (show C.A_nar * C.r ∈ Icc (dist (P s) (P s)) (dist (P s) (P t)) by
      rw [dist_self]; exact ⟨(mul_pos hnar hr).le, hsep⟩)
  simp only at hdt'
  have hzs := hloc s ⟨le_rfl, hst⟩
  have hzt := hloc t' ht'
  have hwin : dist (P s) (P t') ≤ C.A_nar / C.lamConst * C.r := by
    rw [hdt']
    have h2 : C.A_nar ≤ C.A_nar / C.lamConst := by
      rw [le_div_iff₀ hlampos]
      calc C.A_nar * C.lamConst ≤ C.A_nar * 1 := mul_le_mul_of_nonneg_left hlam hnar.le
        _ = C.A_nar := mul_one _
    exact mul_le_mul_of_nonneg_right h2 hr.le
  have hE := hnarrow (P s) (P t') hzs hzt hwin
  rw [hdt', mul_div_assoc, div_self hr.ne', mul_one] at hE
  have hsub : D.IsCurve P s t' := ⟨ht'.1, hPD.2.mono (Icc_subset_Icc h0s (ht'.2.trans htL))⟩
  have hint := internal_le_len_pts D (Y := Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) hsub
    (fun x hx => mid_ann_subset C (hloc x ⟨hx.1, hx.2.trans ht'.2⟩))
    (mid_ann_subset C hzs) (mid_ann_subset C hzt) rfl rfl
  have hlow := (Objects.Splice.bumped_length_bounds C D Db f hforget hWeyl hf hsub).1
  have hunitlen : Db.len P s t' = ENNReal.ofReal (t' - s) :=
    unit_len hunit ⟨h0s, ht'.1.trans (ht'.2.trans htL)⟩ ⟨h0s.trans ht'.1, ht'.2.trans htL⟩ ht'.1
  have hchain : ENNReal.ofReal (Real.exp (-C.ξ * C.A_max)) *
      (ENNReal.ofReal (C.A_nar ^ (C.ξ * (C.Q + 3))) * ENNReal.ofReal N) ≤ ENNReal.ofReal (t' - s) := by
    calc ENNReal.ofReal (Real.exp (-C.ξ * C.A_max)) *
          (ENNReal.ofReal (C.A_nar ^ (C.ξ * (C.Q + 3))) * ENNReal.ofReal N)
        ≤ ENNReal.ofReal (Real.exp (-C.ξ * C.A_max)) * D.len P s t' := by gcongr; exact hE.trans hint
      _ ≤ Db.len P s t' := hlow
      _ = ENNReal.ofReal (t' - s) := hunitlen
  have hnn : 0 ≤ C.A_nar ^ (C.ξ * (C.Q + 3)) := Real.rpow_nonneg hnar.le _
  rw [← ENNReal.ofReal_mul hnn, ← ENNReal.ofReal_mul (Real.exp_pos _).le] at hchain
  have := (ENNReal.ofReal_le_ofReal_iff (by linarith only [ht'.1])).1 hchain
  linarith only [this, ht'.2]

 
theorem t57_final (C : Objects.CorrectedEvent.Constants) (D Dt Db Dtb : LSCMetric) (f : C(ℂ, ℝ))
    (hforgetD : Continuous (BiLipschitz.Barrier.forget D)) (hLDt : Dt.IsLengthSpace)
    (hforgetDt : Continuous (BiLipschitz.Barrier.forget Dt))
    (hWD : ∀ x y : ℂ, Db (x, y) = weylScale C.ξ (-f) D (x, y))
    (hWDt : ∀ x y : ℂ, Dtb (x, y) = weylScale C.ξ (-f) Dt (x, y))
    (hf : ∀ x : ℂ, 0 ≤ f x ∧ f x ≤ C.A_max)
    {Cp Cmid0 Cmid : ℝ} (hCp : 0 < Cp) (hCmid0 : 0 ≤ Cmid0) (hCmid : 0 ≤ Cmid)
    (hle : ∀ x y : ℂ, Dt (x, y) ≤ ENNReal.ofReal Cp * D (x, y))
    (hratio : (1 + 10 * Cp * C.lamConst) * Cmid0 ≤ Cmid * (1 - 10 * Cp * C.lamConst))
    {P : ℝ → ℂ} {L : ℝ} (hPb : Db.IsCurve P 0 L) (hunit : HasUnitSpeedOn (Db.pt ∘ P) (Icc 0 L))
    (hgeoP : Db.len P 0 L = Db (P 0, P L))
    {A W : Set ℂ} (hAW : A ⊆ W)
    {u v : ℂ} {dt : ℝ} (hdt : 0 < dt) (hdtu : Dt (u, v) = ENNReal.ofReal dt)
    (hF1 : ENNReal.ofReal dt ≤ ENNReal.ofReal Cmid0 * D (u, v))
    (huA : u ∈ A) (hvA : v ∈ A)
    (hblock : Dtb.internal A (⟨u, huA⟩, ⟨v, hvA⟩) ≤
      ENNReal.ofReal (Real.exp (-C.ξ * C.A_max) * dt))
    {s t : ℝ} (hs : s ∈ Icc 0 L) (ht : t ∈ Icc 0 L) (hst : s ≤ t)
    (hsA : P s ∈ A) (htA : P t ∈ A)
    (hatt_u : Db.internal A (⟨P s, hsA⟩, ⟨u, huA⟩) ≤
      ENNReal.ofReal (5 * C.lamConst * (Real.exp (-C.ξ * C.A_max) * dt)))
    (hatt_v : Db.internal A (⟨P t, htA⟩, ⟨v, hvA⟩) ≤
      ENNReal.ofReal (5 * C.lamConst * (Real.exp (-C.ξ * C.A_max) * dt))) :
    Dtb.internal W (⟨P s, hAW hsA⟩, ⟨P t, hAW htA⟩) ≤ ENNReal.ofReal (Cmid * (t - s)) := by
  have hlampos := C.lamPos
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp (-C.ξ * C.A_max) := ⟨_, rfl⟩
  have hE0 : 0 < E := by rw [hE]; exact Real.exp_pos _
  rw [← hE] at hblock hatt_u hatt_v
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = E * dt := ⟨_, rfl⟩
  have hX0 : 0 < X := by rw [hX]; exact mul_pos hE0 hdt
  rw [← hX] at hblock hatt_u hatt_v
  
  have hKne0 : ENNReal.ofReal Cp ≠ 0 := by simpa using hCp
  have hblb := blb C D Dt Db Dtb f hLDt hforgetD hforgetDt hWD hWDt hf hKne0 ENNReal.ofReal_ne_top hle A
  have h1 : Dtb.internal A (⟨P s, hsA⟩, ⟨u, huA⟩) ≤ ENNReal.ofReal (5 * Cp * C.lamConst * X) := by
    refine (hblb _).trans ?_
    calc ENNReal.ofReal Cp * Db.internal A (⟨P s, hsA⟩, ⟨u, huA⟩)
        ≤ ENNReal.ofReal Cp * ENNReal.ofReal (5 * C.lamConst * X) := by gcongr
      _ = ENNReal.ofReal (5 * Cp * C.lamConst * X) := by
          rw [← ENNReal.ofReal_mul hCp.le]; congr 1; ring
  have h2 : Dtb.internal A (⟨v, hvA⟩, ⟨P t, htA⟩) ≤ ENNReal.ofReal (5 * Cp * C.lamConst * X) := by
    rw [internal_symm]
    refine (hblb _).trans ?_
    calc ENNReal.ofReal Cp * Db.internal A (⟨P t, htA⟩, ⟨v, hvA⟩)
        ≤ ENNReal.ofReal Cp * ENNReal.ofReal (5 * C.lamConst * X) := by gcongr
      _ = ENNReal.ofReal (5 * Cp * C.lamConst * X) := by
          rw [← ENNReal.ofReal_mul hCp.le]; congr 1; ring
  have hupper : Dtb.internal A (⟨P s, hsA⟩, ⟨P t, htA⟩) ≤
      ENNReal.ofReal ((1 + 10 * Cp * C.lamConst) * X) := by
    have t1 := internal_triangle Dtb A ⟨P s, hsA⟩ ⟨u, huA⟩ ⟨P t, htA⟩
    have t2 := internal_triangle Dtb A ⟨u, huA⟩ ⟨v, hvA⟩ ⟨P t, htA⟩
    have hnn : 0 ≤ 5 * Cp * C.lamConst * X := by positivity
    calc Dtb.internal A (⟨P s, hsA⟩, ⟨P t, htA⟩)
        ≤ Dtb.internal A (⟨P s, hsA⟩, ⟨u, huA⟩) +
          (Dtb.internal A (⟨u, huA⟩, ⟨v, hvA⟩) + Dtb.internal A (⟨v, hvA⟩, ⟨P t, htA⟩)) :=
          t1.trans (add_le_add le_rfl t2)
      _ ≤ ENNReal.ofReal (5 * Cp * C.lamConst * X) +
          (ENNReal.ofReal X + ENNReal.ofReal (5 * Cp * C.lamConst * X)) :=
          add_le_add h1 (add_le_add hblock h2)
      _ = ENNReal.ofReal ((1 + 10 * Cp * C.lamConst) * X) := by
          rw [← ENNReal.ofReal_add hX0.le hnn, ← ENNReal.ofReal_add hnn (by positivity)]
          congr 1; ring
  
  have hgeo : LQGMetric.MetricGeometry.IsGeodesicCurve (Db.pt ∘ P) 0 L := by
    refine ⟨hs.1.trans hs.2, hPb.2, ?_⟩
    show LQGMetric.MetricGeometry.curveLength (Db.pt ∘ P) 0 L = edist (Db.pt (P 0)) (Db.pt (P L))
    rw [← Db.len_eq_curveLength]; exact hgeoP
  have hdist : Db (P s, P t) = ENNReal.ofReal (t - s) :=
    LQGMetric.MetricGeometry.IsGeodesicCurve.edist_eq_of_hasUnitSpeedOn hgeo hunit hs ht hst
  have hus : Db (u, P s) ≤ ENNReal.ofReal (5 * C.lamConst * X) := by
    have := BiLipschitz.Barrier.edist_le_internal' Db A (⟨P s, hsA⟩, ⟨u, huA⟩)
    rw [(LSCMetric.isExtMetric Db).2.2.1]
    exact this.trans hatt_u
  have htv : Db (P t, v) ≤ ENNReal.ofReal (5 * C.lamConst * X) :=
    (BiLipschitz.Barrier.edist_le_internal' Db A (⟨P t, htA⟩, ⟨v, hvA⟩)).trans hatt_v
  have hDbuv : Db (u, v) ≤ ENNReal.ofReal (10 * C.lamConst * X + (t - s)) := by
    have tri := (LSCMetric.isExtMetric Db).2.2.2
    have hnn : 0 ≤ 5 * C.lamConst * X := by positivity
    calc Db (u, v) ≤ Db (u, P s) + Db (P s, v) := tri _ _ _
      _ ≤ Db (u, P s) + (Db (P s, P t) + Db (P t, v)) := add_le_add le_rfl (tri _ _ _)
      _ ≤ ENNReal.ofReal (5 * C.lamConst * X) +
          (ENNReal.ofReal (t - s) + ENNReal.ofReal (5 * C.lamConst * X)) := by
          rw [hdist]; exact add_le_add hus (add_le_add le_rfl htv)
      _ = ENNReal.ofReal (10 * C.lamConst * X + (t - s)) := by
          rw [← ENNReal.ofReal_add (by linarith only [hst]) hnn,
            ← ENNReal.ofReal_add hnn (by linarith only [hst, hnn])]
          congr 1; ring
  have hlowDb := Objects.Splice.bumped_distance_lower C D Db f hforgetD hWD hf u v
  rw [← hE] at hlowDb
  
  have hDfin : D (u, v) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top (by simpa using hE0)] at hlowDb
    exact ENNReal.ofReal_ne_top (top_le_iff.1 (hlowDb.trans hDbuv))
  obtain ⟨Du, hDu⟩ : ∃ Du : ℝ, D (u, v) = ENNReal.ofReal Du ∧ 0 ≤ Du :=
    ⟨(D (u, v)).toReal, (ENNReal.ofReal_toReal hDfin).symm, ENNReal.toReal_nonneg⟩
  rw [hDu.1] at hlowDb hF1
  have hle_uv := hle u v
  rw [hdtu, hDu.1] at hle_uv
  
  have r1 : E * Du ≤ 10 * C.lamConst * X + (t - s) := by
    have h := hlowDb.trans hDbuv
    rw [← ENNReal.ofReal_mul hE0.le] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by nlinarith [hX0, hlampos, hst])).1 h
  have r2 : dt ≤ Cmid0 * Du := by
    rw [← ENNReal.ofReal_mul hCmid0] at hF1
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hCmid0 hDu.2)).1 hF1
  have r3 : dt ≤ Cp * Du := by
    rw [← ENNReal.ofReal_mul hCp.le] at hle_uv
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hCp.le hDu.2)).1 hle_uv
  have hEDu : 0 ≤ E * Du := mul_nonneg hE0.le hDu.2
  have r4 : (1 - 10 * Cp * C.lamConst) * (E * Du) ≤ t - s := by
    have : 10 * C.lamConst * X ≤ 10 * Cp * C.lamConst * (E * Du) := by
      rw [hX]
      have hl : 0 ≤ 10 * C.lamConst * E := by positivity
      calc 10 * C.lamConst * (E * dt) = (10 * C.lamConst * E) * dt := by ring
        _ ≤ (10 * C.lamConst * E) * (Cp * Du) := mul_le_mul_of_nonneg_left r3 hl
        _ = 10 * Cp * C.lamConst * (E * Du) := by ring
    linarith only [r1, this]
  have r5 : (1 + 10 * Cp * C.lamConst) * X ≤ Cmid * (t - s) := by
    have hX' : X ≤ Cmid0 * (E * Du) := by
      rw [hX]
      calc E * dt ≤ E * (Cmid0 * Du) := mul_le_mul_of_nonneg_left r2 hE0.le
        _ = Cmid0 * (E * Du) := by ring
    have hpos : 0 ≤ 1 + 10 * Cp * C.lamConst := by positivity
    calc (1 + 10 * Cp * C.lamConst) * X ≤ (1 + 10 * Cp * C.lamConst) * (Cmid0 * (E * Du)) :=
          mul_le_mul_of_nonneg_left hX' hpos
      _ = ((1 + 10 * Cp * C.lamConst) * Cmid0) * (E * Du) := by ring
      _ ≤ (Cmid * (1 - 10 * Cp * C.lamConst)) * (E * Du) := mul_le_mul_of_nonneg_right hratio hEDu
      _ = Cmid * ((1 - 10 * Cp * C.lamConst) * (E * Du)) := by ring
      _ ≤ Cmid * (t - s) := mul_le_mul_of_nonneg_left r4 hCmid
  calc Dtb.internal W (⟨P s, hAW hsA⟩, ⟨P t, hAW htA⟩)
      ≤ Dtb.internal A (⟨P s, hsA⟩, ⟨P t, htA⟩) := internal_anti Dtb hAW hsA htA
    _ ≤ ENNReal.ofReal ((1 + 10 * Cp * C.lamConst) * X) := hupper
    _ ≤ ENNReal.ofReal (Cmid * (t - s)) := ENNReal.ofReal_le_ofReal r5

 



theorem t57_from_attachments (C : Objects.CorrectedEvent.Constants) (D Dt Db Dtb : LSCMetric) (f : C(ℂ, ℝ))
    (hforgetD : Continuous (BiLipschitz.Barrier.forget D)) (hLDt : Dt.IsLengthSpace)
    (hforgetDt : Continuous (BiLipschitz.Barrier.forget Dt))
    (hWD : ∀ x y : ℂ, Db (x, y) = weylScale C.ξ (-f) D (x, y))
    (hWDt : ∀ x y : ℂ, Dtb (x, y) = weylScale C.ξ (-f) Dt (x, y))
    (hf : ∀ x : ℂ, 0 ≤ f x ∧ f x ≤ C.A_max)
    {Cp Cmid0 Cmid : ℝ} (hCp : 0 < Cp) (hCmid0 : 0 ≤ Cmid0) (hCmid : 0 ≤ Cmid)
    (hle : ∀ x y : ℂ, Dt (x, y) ≤ ENNReal.ofReal Cp * D (x, y))
    (hratio : (1 + 10 * Cp * C.lamConst) * Cmid0 ≤ Cmid * (1 - 10 * Cp * C.lamConst))
    (hlam : C.lamConst ≤ 1)
    {N : ℝ}
    (hnarrow : ∀ (z w : ℂ) (hz : z ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r))
      (hw : w ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r)), dist z w ≤ C.A_nar / C.lamConst * C.r →
      ENNReal.ofReal ((dist z w / C.r) ^ (C.ξ * (C.Q + 3))) * ENNReal.ofReal N ≤
        D.internal (Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (⟨z, mid_ann_subset C hz⟩, ⟨w, mid_ann_subset C hw⟩))
    {P : ℝ → ℂ} {L : ℝ} (hPb : Db.IsCurve P 0 L) (hunit : HasUnitSpeedOn (Db.pt ∘ P) (Icc 0 L))
    (hgeoP : Db.len P 0 L = Db (P 0, P L))
    {u v : ℂ} {dt : ℝ} (hdt : 0 < dt) (hdtu : Dt (u, v) = ENNReal.ofReal dt)
    (hF1 : ENNReal.ofReal dt ≤ ENNReal.ofReal Cmid0 * D (u, v))
    (huA : u ∈ Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (hvA : v ∈ Objects.CorrectedEvent.ann 0 C.r (4 * C.r))
    (hblock : Dtb.internal (Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (⟨u, huA⟩, ⟨v, hvA⟩) ≤
      ENNReal.ofReal (Real.exp (-C.ξ * C.A_max) * dt))
    {τ σ tu tv : ℝ} (h0τ : 0 ≤ τ) (hσL : σ ≤ L) (htu : tu ∈ Icc τ σ) (htv : tv ∈ Icc τ σ)
    (hloc : ∀ x ∈ Icc τ σ, P x ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r))
    (hsep : C.A_nar * C.r ≤ dist (P tu) (P tv))
    (huAtt : ∃ (h1 : P tu ∈ Objects.CorrectedEvent.ann 0 C.r (4 * C.r)),
      Db.internal (Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (⟨P tu, h1⟩, ⟨u, huA⟩) ≤
        ENNReal.ofReal (5 * C.lamConst * (Real.exp (-C.ξ * C.A_max) * dt)))
    (hvAtt : ∃ (h1 : P tv ∈ Objects.CorrectedEvent.ann 0 C.r (4 * C.r)),
      Db.internal (Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (⟨P tv, h1⟩, ⟨v, hvA⟩) ≤
        ENNReal.ofReal (5 * C.lamConst * (Real.exp (-C.ξ * C.A_max) * dt))) :
    ∃ s t : ℝ, τ ≤ s ∧ s < t ∧ t ≤ σ ∧
      Real.exp (-C.ξ * C.A_max) * (C.A_nar ^ (C.ξ * (C.Q + 3)) * N) ≤ t - s ∧
      ∃ (hs : P s ∈ Metric.ball (0 : ℂ) (4 * C.r)) (ht : P t ∈ Metric.ball (0 : ℂ) (4 * C.r)),
        Dtb.internal (Metric.ball (0 : ℂ) (4 * C.r)) (⟨P s, hs⟩, ⟨P t, ht⟩) ≤
          ENNReal.ofReal (Cmid * (t - s)) := by
  have hr := C.rPos
  have hnar := C.narPos
  have hPD : D.IsCurve P 0 L := Objects.Splice.bumped_curve_transfer_back C D Db f hforgetD hWD hf hPb
  have hcont : ContinuousOn P (Icc 0 L) := hforgetD.comp_continuousOn hPD.2
  have hAW : Objects.CorrectedEvent.ann 0 C.r (4 * C.r) ⊆ Metric.ball (0 : ℂ) (4 * C.r) := fun x hx => by
    rw [mem_ball]; exact hx.2
  obtain ⟨hPu, hattu⟩ := huAtt
  obtain ⟨hPv, hattv⟩ := hvAtt
  have hne : tu ≠ tv := by
    intro h
    rw [h, dist_self] at hsep
    have : 0 < C.A_nar * C.r := mul_pos hnar hr
    linarith only [hsep, this]
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · 
    refine ⟨tu, tv, htu.1, hlt, htv.2, ?_, hAW hPu, hAW hPv, ?_⟩
    · exact narrow_time_bumped C D Db f hforgetD hWD hf hPD hunit hcont hnarrow hlam
        (h0τ.trans htu.1) hlt.le (htv.2.trans hσL)
        (fun x hx => hloc x ⟨htu.1.trans hx.1, hx.2.trans htv.2⟩) hsep
    · exact t57_final C D Dt Db Dtb f hforgetD hLDt hforgetDt hWD hWDt hf hCp hCmid0 hCmid hle hratio hPb
        hunit hgeoP hAW hdt hdtu hF1 huA hvA hblock ⟨h0τ.trans htu.1, htu.2.trans hσL⟩
        ⟨h0τ.trans htv.1, htv.2.trans hσL⟩ hlt.le hPu hPv hattu hattv
  · 
    have hdtv : Dt (v, u) = ENNReal.ofReal dt := by rw [(LSCMetric.isExtMetric Dt).2.2.1]; exact hdtu
    have hF1' : ENNReal.ofReal dt ≤ ENNReal.ofReal Cmid0 * D (v, u) := by
      rw [(LSCMetric.isExtMetric D).2.2.1]; exact hF1
    have hblock' : Dtb.internal (Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (⟨v, hvA⟩, ⟨u, huA⟩) ≤
        ENNReal.ofReal (Real.exp (-C.ξ * C.A_max) * dt) := by
      rw [internal_symm]; exact hblock
    refine ⟨tv, tu, htv.1, hlt, htu.2, ?_, hAW hPv, hAW hPu, ?_⟩
    · rw [dist_comm] at hsep
      exact narrow_time_bumped C D Db f hforgetD hWD hf hPD hunit hcont hnarrow hlam
        (h0τ.trans htv.1) hlt.le (htu.2.trans hσL)
        (fun x hx => hloc x ⟨htv.1.trans hx.1, hx.2.trans htu.2⟩) hsep
    · exact t57_final C D Dt Db Dtb f hforgetD hLDt hforgetDt hWD hWDt hf hCp hCmid0 hCmid hle hratio hPb
        hunit hgeoP hAW hdt hdtv hF1' hvA huA hblock' ⟨h0τ.trans htv.1, htv.2.trans hσL⟩
        ⟨h0τ.trans htu.1, htu.2.trans hσL⟩ hlt.le hPv hPu hattv hattu

end SupercriticalLQGUniqueness.Uniqueness.Objects.Producer
