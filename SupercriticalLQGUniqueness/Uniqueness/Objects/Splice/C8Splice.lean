import SupercriticalLQGUniqueness.Uniqueness.Objects.Splice.C8Weyl
import SupercriticalLQGUniqueness.Uniqueness.Objects.Compare.CompareGeometry



 
set_option autoImplicit false
noncomputable section
open Set Metric
namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Splice

private def euclidForget (D : LSCMetric) : D.Space → ℂ := id

 


theorem internal_geodesic_segment_le_competitor
    (D : LSCMetric) (U : Set ℂ) {P π : ℝ → ℂ}
    {t₁ t₂ u v : ℝ} (h₁ : P t₁ ∈ U) (h₂ : P t₂ ∈ U)
    (hgeo : D.len P t₁ t₂ = D.internal U (⟨P t₁, h₁⟩, ⟨P t₂, h₂⟩))
    (hπ : D.IsCurve π u v)
    (hπU : ∀ x ∈ Icc u v, π x ∈ U)
    (hu : π u = P t₁) (hv : π v = P t₂) :
    D.len P t₁ t₂ ≤ D.len π u v := by
  rw [hgeo]
  unfold LSCMetric.internal
  exact iInf_le_of_le π <| iInf_le_of_le u <| iInf_le_of_le v <|
    iInf_le_of_le hπ <| iInf_le_of_le hπU <|
      iInf_le_of_le hu <| iInf_le_of_le hv le_rfl

 

theorem internal_geodesic_segment_le_loop_of_two_hits
    (D : LSCMetric) (U : Set ℂ) {P π : ℝ → ℂ}
    {t₁ t₂ u v : ℝ} (h₁ : P t₁ ∈ U) (h₂ : P t₂ ∈ U)
    (hgeo : D.len P t₁ t₂ = D.internal U (⟨P t₁, h₁⟩, ⟨P t₂, h₂⟩))
    (hπ : D.IsCurve π u v)
    (hπU : ∀ x ∈ Icc u v, π x ∈ U)
    (hhit₁ : P t₁ ∈ π '' Icc u v)
    (hhit₂ : P t₂ ∈ π '' Icc u v) :
    D.len P t₁ t₂ ≤ D.len π u v := by
  obtain ⟨p, hp, hpu⟩ := hhit₁
  obtain ⟨q, hq, hqv⟩ := hhit₂
  let V : Set D.Space := D.pt '' U
  have hmaps : MapsTo (D.pt ∘ π) (Icc u v) V := by
    intro x hx
    exact ⟨π x, hπU x hx, rfl⟩
  have hbound : LQGMetric.MetricGeometry.internalEDist V
      (D.pt (P t₁)) (D.pt (P t₂)) ≤ D.len π u v := by
    rcases le_total p q with hpq | hqp
    · have hsmall := LQGMetric.MetricGeometry.internalEDist_le_curveLength
        hpq (hπ.2.mono (Icc_subset_Icc hp.1 hq.2))
        (hmaps.mono_left (Icc_subset_Icc hp.1 hq.2))
      have hsmall' : LQGMetric.MetricGeometry.internalEDist V
          (D.pt (P t₁)) (D.pt (P t₂)) ≤
          LQGMetric.MetricGeometry.curveLength (D.pt ∘ π) p q := by
        simpa only [Function.comp_apply, hpu, hqv] using hsmall
      exact hsmall'.trans (LQGMetric.MetricGeometry.curveLength_mono _ hp.1 hq.2)
    · have hsmall := LQGMetric.MetricGeometry.internalEDist_le_curveLength
        hqp (hπ.2.mono (Icc_subset_Icc hq.1 hp.2))
        (hmaps.mono_left (Icc_subset_Icc hq.1 hp.2))
      have hsmall' : LQGMetric.MetricGeometry.internalEDist V
          (D.pt (P t₂)) (D.pt (P t₁)) ≤
          LQGMetric.MetricGeometry.curveLength (D.pt ∘ π) q p := by
        simpa only [Function.comp_apply, hpu, hqv] using hsmall
      calc
        _ = LQGMetric.MetricGeometry.internalEDist V
            (D.pt (P t₂)) (D.pt (P t₁)) :=
          LQGMetric.MetricGeometry.internalEDist_comm _ _ _
        _ ≤ LQGMetric.MetricGeometry.curveLength (D.pt ∘ π) q p := hsmall'
        _ ≤ D.len π u v := LQGMetric.MetricGeometry.curveLength_mono _ hq.1 hp.2
  rw [hgeo, D.internal_eq_internalEDist]
  exact hbound

 

theorem good_cell_two_hits_crossing
    (C : Objects.CorrectedEvent.Constants) (D : LSCMetric) (c : ℂ) (s : ℝ)
    (l : Objects.CorrectedEvent.Cell) (k : ℕ) (hR : 0 < Objects.CorrectedEvent.supRadius C k)
    (hgood : Objects.CorrectedEvent.supGood C D c s l k)
    {P : ℝ → ℂ} {a t b : ℝ} (hat : a < t) (htb : t < b)
    (hP : D.IsCurve P a b) (hcont : ContinuousOn P (Icc a b))
    (hends : P a ∈ (ball (Objects.CorrectedEvent.cellCenter c s l)
      ((3-1/20)*Objects.CorrectedEvent.supRadius C k))ᶜ ∧
      P b ∈ (ball (Objects.CorrectedEvent.cellCenter c s l)
      ((3-1/20)*Objects.CorrectedEvent.supRadius C k))ᶜ)
    (hvisit : dist (P t) (Objects.CorrectedEvent.cellCenter c s l) ≤
      (1+1/20)*Objects.CorrectedEvent.supRadius C k) :
    ∃ (π : ℝ → ℂ) (u v t₁ t₂ : ℝ),
      D.IsCurve π u v ∧
      π '' Icc u v ⊆ Objects.CorrectedEvent.ann (Objects.CorrectedEvent.cellCenter c s l)
        ((2+1/20)*Objects.CorrectedEvent.supRadius C k)
        ((3-1/20)*Objects.CorrectedEvent.supRadius C k) ∧
      a ≤ t₁ ∧ t₁ < t ∧ t < t₂ ∧ t₂ ≤ b ∧
      P t₁ ∈ π '' Icc u v ∧ P t₂ ∈ π '' Icc u v ∧
      Objects.CorrectedEvent.acr D (Objects.CorrectedEvent.cellCenter c s l)
        ((1+1/20)*Objects.CorrectedEvent.supRadius C k)
        ((2-1/20)*Objects.CorrectedEvent.supRadius C k) ≤ D.len P t t₂ ∧
      D.len π u v < ENNReal.ofReal (Real.exp (-C.ξ*C.A_max)) *
        Objects.CorrectedEvent.acr D (Objects.CorrectedEvent.cellCenter c s l)
          ((1+1/20)*Objects.CorrectedEvent.supRadius C k)
          ((2-1/20)*Objects.CorrectedEvent.supRadius C k) := by
  obtain ⟨π, u, v, hπ, hπann, hsep, hπcost⟩ :=
    Objects.Compare.sup_good_separator C D c s l k hgood
  have hnot : P t ∉ π '' Icc u v := by
    intro hmem
    have hrad := (hπann hmem).1
    have hvisit' : dist (Objects.CorrectedEvent.cellCenter c s l) (P t) ≤
        (1+1/20)*Objects.CorrectedEvent.supRadius C k := by simpa only [dist_comm] using hvisit
    nlinarith [hvisit']
  have htle : P t ∈ closedBall (Objects.CorrectedEvent.cellCenter c s l)
      ((2+1/20)*Objects.CorrectedEvent.supRadius C k) := by
    rw [mem_closedBall]
    have hvisit' : dist (Objects.CorrectedEvent.cellCenter c s l) (P t) ≤
        (1+1/20)*Objects.CorrectedEvent.supRadius C k := by simpa only [dist_comm] using hvisit
    nlinarith [hvisit']
  have hrR : (2+1/20)*Objects.CorrectedEvent.supRadius C k ≤
      (3-1/20)*Objects.CorrectedEvent.supRadius C k := by nlinarith
  obtain ⟨t₁, t₂, hat₁, ht₁t, htt₂, ht₂b, hhit₁, hhit₂⟩ :=
    separator_two_hits hat htb hrR hcont hsep hends.1 hends.2 htle hnot
  have hrad₂ : (2-1/20)*Objects.CorrectedEvent.supRadius C k ≤
      dist (P t₂) (Objects.CorrectedEvent.cellCenter c s l) := by
    have h := (hπann hhit₂).1
    have h' : (2+1/20)*Objects.CorrectedEvent.supRadius C k <
        dist (P t₂) (Objects.CorrectedEvent.cellCenter c s l) := by simpa only [dist_comm] using h
    nlinarith [h']
  have hcross : Objects.CorrectedEvent.acr D (Objects.CorrectedEvent.cellCenter c s l)
        ((1+1/20)*Objects.CorrectedEvent.supRadius C k)
        ((2-1/20)*Objects.CorrectedEvent.supRadius C k) ≤ D.len P t t₂ := by
    exact Objects.Compare.acr_le_curve_of_endpoint_order D
      ⟨htt₂.le, hP.2.mono (Icc_subset_Icc hat.le ht₂b)⟩
      (hcont.mono (Icc_subset_Icc hat.le ht₂b))
      (by nlinarith) hvisit hrad₂
  exact ⟨π, u, v, t₁, t₂, hπ, hπann, hat₁, ht₁t, htt₂, ht₂b,
    hhit₁, hhit₂, hcross, hπcost⟩

 


theorem good_cell_visit_impossible_of_metric_adapters
    (C : Objects.CorrectedEvent.Constants) (D Db : LSCMetric) (U : Set ℂ)
    (c : ℂ) (s : ℝ) (l : Objects.CorrectedEvent.Cell) (k : ℕ)
    (hR : 0 < Objects.CorrectedEvent.supRadius C k)
    (hgood : Objects.CorrectedEvent.supGood C D c s l k)
    {P : ℝ → ℂ} {a t b : ℝ} (hat : a < t) (htb : t < b)
    (hP : D.IsCurve P a b) (hcont : ContinuousOn P (Icc a b))
    (hPcarrier : ∀ x ∈ Icc a b, P x ∈ U)
    (hends : P a ∈ (ball (Objects.CorrectedEvent.cellCenter c s l)
      ((3-1/20)*Objects.CorrectedEvent.supRadius C k))ᶜ ∧
      P b ∈ (ball (Objects.CorrectedEvent.cellCenter c s l)
      ((3-1/20)*Objects.CorrectedEvent.supRadius C k))ᶜ)
    (hvisit : dist (P t) (Objects.CorrectedEvent.cellCenter c s l) ≤
      (1+1/20)*Objects.CorrectedEvent.supRadius C k)
    (hcarrier : Objects.CorrectedEvent.ann (Objects.CorrectedEvent.cellCenter c s l)
      ((2+1/20)*Objects.CorrectedEvent.supRadius C k)
      ((3-1/20)*Objects.CorrectedEvent.supRadius C k) ⊆ U)
    (hgeo : ∀ (t₁ t₂ : ℝ) (h₁ : t₁ ∈ Icc a b)
      (h₂ : t₂ ∈ Icc a b), t₁ ≤ t₂ →
      Db.len P t₁ t₂ = Db.internal U
        (⟨P t₁, hPcarrier t₁ h₁⟩, ⟨P t₂, hPcarrier t₂ h₂⟩))
    (hloopCurve : ∀ (π : ℝ → ℂ) (u v : ℝ), D.IsCurve π u v →
      (∀ x ∈ Icc u v, π x ∈ U) → Db.IsCurve π u v)
    (hloopWeyl : ∀ (π : ℝ → ℂ) (u v : ℝ), D.IsCurve π u v →
      Db.len π u v ≤ D.len π u v)
    (hcrossWeyl : ∀ (u v : ℝ), a ≤ u → u ≤ v → v ≤ b →
      ENNReal.ofReal (Real.exp (-C.ξ*C.A_max)) * D.len P u v ≤ Db.len P u v) :
    False := by
  obtain ⟨π, u, v, t₁, t₂, hπ, hπann, hat₁, ht₁t, htt₂, ht₂b,
    hhit₁, hhit₂, hcross, hπcost⟩ :=
    good_cell_two_hits_crossing C D c s l k hR hgood hat htb hP hcont hends hvisit
  have hπU : ∀ x ∈ Icc u v, π x ∈ U := by
    intro x hx
    exact hcarrier (hπann ⟨x, hx, rfl⟩)
  have ht₁mem : t₁ ∈ Icc a b := ⟨hat₁, ht₁t.le.trans htb.le⟩
  have ht₂mem : t₂ ∈ Icc a b := ⟨hat.le.trans htt₂.le, ht₂b⟩
  have hseg := internal_geodesic_segment_le_loop_of_two_hits Db U
    (hPcarrier t₁ ht₁mem) (hPcarrier t₂ ht₂mem)
    (hgeo t₁ t₂ ht₁mem ht₂mem (ht₁t.trans htt₂).le)
    (hloopCurve π u v hπ hπU) hπU hhit₁ hhit₂
  have hmono : Db.len P t t₂ ≤ Db.len P t₁ t₂ := by
    exact LQGMetric.MetricGeometry.curveLength_mono _ ht₁t.le le_rfl
  have hbound : D.len π u v < Db.len π u v := by
    calc
      D.len π u v < ENNReal.ofReal (Real.exp (-C.ξ*C.A_max)) *
          Objects.CorrectedEvent.acr D (Objects.CorrectedEvent.cellCenter c s l)
            ((1+1/20)*Objects.CorrectedEvent.supRadius C k)
            ((2-1/20)*Objects.CorrectedEvent.supRadius C k) := hπcost
      _ ≤ ENNReal.ofReal (Real.exp (-C.ξ*C.A_max)) * D.len P t t₂ :=
        by gcongr
      _ ≤ Db.len P t t₂ := hcrossWeyl t t₂ hat.le htt₂.le ht₂b
      _ ≤ Db.len P t₁ t₂ := hmono
      _ ≤ Db.len π u v := hseg
  exact (not_lt_of_ge (hloopWeyl π u v hπ)) hbound

 


theorem good_cell_visit_impossible_of_weyl
    (C : Objects.CorrectedEvent.Constants) (D Db : LSCMetric) (U : Set ℂ)
    (f : C(ℂ, ℝ))
    (hforget : Continuous (euclidForget D))
    (hWeyl : ∀ x y : ℂ, Db (x, y) = weylScale C.ξ (-f) D (x, y))
    (hf : ∀ x : ℂ, 0 ≤ f x ∧ f x ≤ C.A_max)
    (hLength : D.IsLengthSpace)
    (c : ℂ) (s : ℝ) (l : Objects.CorrectedEvent.Cell) (k : ℕ)
    (hR : 0 < Objects.CorrectedEvent.supRadius C k)
    (hgood : Objects.CorrectedEvent.supGood C D c s l k)
    {P : ℝ → ℂ} {a t b : ℝ} (hat : a < t) (htb : t < b)
    (hPb : Db.IsCurve P a b) (hUcompact : IsCompact U)
    (hPcarrier : ∀ x ∈ Icc a b, P x ∈ U)
    (hends : P a ∈ (ball (Objects.CorrectedEvent.cellCenter c s l)
      ((3-1/20)*Objects.CorrectedEvent.supRadius C k))ᶜ ∧
      P b ∈ (ball (Objects.CorrectedEvent.cellCenter c s l)
      ((3-1/20)*Objects.CorrectedEvent.supRadius C k))ᶜ)
    (hvisit : dist (P t) (Objects.CorrectedEvent.cellCenter c s l) ≤
      (1+1/20)*Objects.CorrectedEvent.supRadius C k)
    (hcarrier : Objects.CorrectedEvent.ann (Objects.CorrectedEvent.cellCenter c s l)
      ((2+1/20)*Objects.CorrectedEvent.supRadius C k)
      ((3-1/20)*Objects.CorrectedEvent.supRadius C k) ⊆ U)
    (hgeo : ∀ (t₁ t₂ : ℝ) (h₁ : t₁ ∈ Icc a b)
      (h₂ : t₂ ∈ Icc a b), t₁ ≤ t₂ →
      Db.len P t₁ t₂ = Db.internal U
        (⟨P t₁, hPcarrier t₁ h₁⟩, ⟨P t₂, hPcarrier t₂ h₂⟩)) :
    False := by
  have hP : D.IsCurve P a b :=
    bumped_curve_transfer_back C D Db f hforget hWeyl hf hPb
  have hcont : ContinuousOn P (Icc a b) :=
    hP.continuousOn_of_mapsTo hUcompact hPcarrier
  apply good_cell_visit_impossible_of_metric_adapters C D Db U c s l k hR hgood
    hat htb hP hcont hPcarrier hends hvisit hcarrier hgeo
  · intro π u v hπ hπU
    exact bumped_curve_transfer C D Db f hforget hWeyl hf hLength hπ
  · intro π u v hπ
    exact (bumped_length_bounds C D Db f hforget hWeyl hf hπ).2
  · intro u v hau huv hvb
    have hPuv : D.IsCurve P u v :=
      ⟨huv, hP.2.mono (Icc_subset_Icc hau hvb)⟩
    exact (bumped_length_bounds C D Db f hforget hWeyl hf hPuv).1

end SupercriticalLQGUniqueness.Uniqueness.Objects.Splice
