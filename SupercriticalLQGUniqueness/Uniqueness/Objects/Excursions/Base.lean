import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.T57w
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Interfaces.Section4Interfaces




 















set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions

 

 
theorem bumped_len_eq {D : LSCMetric} {P : ℝ → ℂ} {L : ℝ} (h : EndSaving.Interfaces.BumpedGeodesic D P L)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htL : t ≤ L) :
    D.len P s t = ENNReal.ofReal (t - s) :=
  LQGMetric.MetricGeometry.curveLength_of_hasUnitSpeedOn h.2.1 ⟨hs, hst.trans htL⟩
    ⟨hs.trans hst, htL⟩

 
theorem bumped_dist_eq {D : LSCMetric} {P : ℝ → ℂ} {L : ℝ} (h : EndSaving.Interfaces.BumpedGeodesic D P L)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htL : t ≤ L) :
    D (P s, P t) = ENNReal.ofReal (t - s) := by
  have hL : 0 ≤ L := hs.trans (hst.trans htL)
  have hgeo : LQGMetric.MetricGeometry.IsGeodesicCurve (D.pt ∘ P) 0 L :=
    ⟨hL, h.1.2, h.2.2.1⟩
  exact LQGMetric.MetricGeometry.IsGeodesicCurve.edist_eq_of_hasUnitSpeedOn hgeo h.2.1
    ⟨hs, hst.trans htL⟩ ⟨hs.trans hst, htL⟩ hst

 
theorem bumped_dist_eq' {D : LSCMetric} {P : ℝ → ℂ} {L : ℝ} (h : EndSaving.Interfaces.BumpedGeodesic D P L)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htL : t ≤ L) :
    D (P t, P s) = ENNReal.ofReal (t - s) := by
  rw [show D (P t, P s) = D (P s, P t) from D.isExtMetric.2.2.1 _ _]
  exact bumped_dist_eq h hs hst htL

 
theorem bumped_isCurve {D : LSCMetric} {P : ℝ → ℂ} {L : ℝ} (h : EndSaving.Interfaces.BumpedGeodesic D P L)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htL : t ≤ L) : D.IsCurve P s t :=
  ⟨hst, h.1.2.mono (Icc_subset_Icc hs htL)⟩

 

 

theorem edist_le_len (D : LSCMetric) (P : ℝ → ℂ) {a b p q : ℝ} (hp : p ∈ Icc a b) (hq : q ∈ Icc a b) :
    D (P p, P q) ≤ D.len P a b :=
  eVariationOn.edist_le (D.pt ∘ P) hp hq

 

section Weyl

variable (C : Objects.CorrectedEvent.Constants) (D Db : LSCMetric) (f : C(ℂ, ℝ))

 
private theorem len_eq_with (hWeyl : ∀ x y : ℂ, Db (x, y) = weylScale C.ξ (-f) D (x, y))
    (P : ℝ → ℂ) (a b : ℝ) :
    Db.len P a b = HigherDimLQGMetric.curveLengthWith
      (fun x y : D.Space => weylScale C.ξ (-f) D (x, y)) (D.pt ∘ P) a b := by
  have hδ : (fun x y : D.Space => weylScale C.ξ (-f) D (x, y)) =
      (fun x y : D.Space => Db (x, y)) := by
    funext x y
    exact (hWeyl x y).symm
  rw [hδ, Db.len_eq_curveLength]
  exact (HigherDimLQGMetric.curveLengthWith_edist (Db.pt ∘ P) a b).symm

 

theorem bumped_len_eq_of_zero (hforget : Continuous (BiLipschitz.Barrier.forget D))
    (hWeyl : ∀ x y : ℂ, Db (x, y) = weylScale C.ξ (-f) D (x, y))
    {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b) (h0 : ∀ t ∈ Icc a b, f (P t) = 0) :
    Db.len P a b = D.len P a b := by
  have h0' : ∀ s ∈ Icc a b, (-f) (P s) = 0 := by
    intro s hs
    simp only [ContinuousMap.neg_apply, h0 s hs, neg_zero]
  have h := Toolkit.WeylLength.weylCurveLength_eq_of_zero_on_trace D C.ξ (-f) hforget hP h0'
  rw [len_eq_with C D Db f hWeyl]
  exact h

 

theorem bumped_len_le_of_max (hforget : Continuous (BiLipschitz.Barrier.forget D))
    (hWeyl : ∀ x y : ℂ, Db (x, y) = weylScale C.ξ (-f) D (x, y))
    {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b) (hmax : ∀ t ∈ Icc a b, f (P t) = C.A_max) :
    Db.len P a b ≤ ENNReal.ofReal (Real.exp (-C.ξ * C.A_max)) * D.len P a b := by
  have hlo : ∀ s ∈ Icc a b, -C.A_max ≤ (-f) (P s) := by
    intro s hs
    simp only [ContinuousMap.neg_apply, hmax s hs, le_refl]
  have hhi : ∀ s ∈ Icc a b, (-f) (P s) ≤ -C.A_max := by
    intro s hs
    simp only [ContinuousMap.neg_apply, hmax s hs, le_refl]
  have h := (Toolkit.WeylLength.weylCurveLength_factor_bounds D C.ξ C.ξPos.le (-f) hforget hP
    (-C.A_max) (-C.A_max) hlo hhi).2
  rw [len_eq_with C D Db f hWeyl]
  have hexp : C.ξ * -C.A_max = -C.ξ * C.A_max := by ring
  rw [hexp] at h
  exact h

 
theorem bumped_len_le (hforget : Continuous (BiLipschitz.Barrier.forget D))
    (hWeyl : ∀ x y : ℂ, Db (x, y) = weylScale C.ξ (-f) D (x, y))
    (hf : ∀ x : ℂ, 0 ≤ f x ∧ f x ≤ C.A_max)
    {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b) : Db.len P a b ≤ D.len P a b :=
  (Objects.Splice.bumped_length_bounds C D Db f hforget hWeyl hf hP).2

 
theorem bumped_dist_le_len (hforget : Continuous (BiLipschitz.Barrier.forget D))
    (hWeyl : ∀ x y : ℂ, Db (x, y) = weylScale C.ξ (-f) D (x, y))
    (hf : ∀ x : ℂ, 0 ≤ f x ∧ f x ≤ C.A_max)
    {π : ℝ → ℂ} {a b p q : ℝ} (hπ : D.IsCurve π a b) (hp : p ∈ Icc a b) (hq : q ∈ Icc a b) :
    Db (π p, π q) ≤ D.len π a b :=
  (edist_le_len Db π hp hq).trans (bumped_len_le C D Db f hforget hWeyl hf hπ)

end Weyl

 

 
theorem exists_hit {P : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hP : ContinuousOn P (Icc a b))
    {K E F : Set ℂ} (hK : LQGMetric.Disconnects K E F) (ha : P a ∈ E) (hb : P b ∈ F) :
    ∃ t ∈ Icc a b, P t ∈ K := by
  obtain ⟨w, hw, hwK⟩ := hK (P a) (P b) (LQGMetric.pathOfIcc P hab hP) ha hb
  obtain ⟨t, ht, rfl⟩ := LQGMetric.range_pathOfIcc_subset P hab hP hw
  exact ⟨t, ht, hwK⟩

 

theorem exists_last_mem {P : ℝ → ℂ} {a b : ℝ} (hP : ContinuousOn P (Icc a b)) {K : Set ℂ}
    (hK : IsClosed K) (hne : ∃ t ∈ Icc a b, P t ∈ K) :
    ∃ t₀ ∈ Icc a b, P t₀ ∈ K ∧ ∀ t ∈ Icc a b, P t ∈ K → t ≤ t₀ := by
  set S := Icc a b ∩ P ⁻¹' K with hS
  have hSc : IsClosed S := hP.preimage_isClosed_of_isClosed isClosed_Icc hK
  have hSne : S.Nonempty := by
    obtain ⟨t, ht, htK⟩ := hne
    exact ⟨t, ht, htK⟩
  have hSb : BddAbove S := ⟨b, fun t ht => ht.1.2⟩
  have hmem : sSup S ∈ S := hSc.csSup_mem hSne hSb
  exact ⟨sSup S, hmem.1, hmem.2, fun t ht htK => le_csSup hSb ⟨ht, htK⟩⟩

 
theorem exists_first_mem {P : ℝ → ℂ} {a b : ℝ} (hP : ContinuousOn P (Icc a b)) {K : Set ℂ}
    (hK : IsClosed K) (hne : ∃ t ∈ Icc a b, P t ∈ K) :
    ∃ t₀ ∈ Icc a b, P t₀ ∈ K ∧ ∀ t ∈ Icc a b, P t ∈ K → t₀ ≤ t := by
  set S := Icc a b ∩ P ⁻¹' K with hS
  have hSc : IsClosed S := hP.preimage_isClosed_of_isClosed isClosed_Icc hK
  have hSne : S.Nonempty := by
    obtain ⟨t, ht, htK⟩ := hne
    exact ⟨t, ht, htK⟩
  have hSb : BddBelow S := ⟨a, fun t ht => ht.1.1⟩
  have hmem : sInf S ∈ S := hSc.csInf_mem hSne hSb
  exact ⟨sInf S, hmem.1, hmem.2, fun t ht htK => csInf_le hSb ⟨ht, htK⟩⟩

 



theorem exists_last_hit {P : ℝ → ℂ} {a s : ℝ} (has : a ≤ s) (hP : ContinuousOn P (Icc a s))
    {K : Set ℂ} {y : ℂ} {ρ R : ℝ} (hρR : ρ ≤ R) (hKc : IsClosed K)
    (hK : LQGMetric.Disconnects K (sphere y ρ) (sphere y R))
    (hKann : K ⊆ {x | ρ < dist x y ∧ dist x y < R})
    (ha : R ≤ dist (P a) y) (hs : dist (P s) y ≤ ρ) :
    ∃ t₀ ∈ Icc a s, t₀ < s ∧ P t₀ ∈ K ∧ ∀ t ∈ Icc t₀ s, dist (P t) y < R := by
  have hsep := (LQGMetric.Disconnects.closedBall_compl_ball hρR hK).symm
  have hhit : ∃ t ∈ Icc a s, P t ∈ K :=
    exists_hit has hP hsep (by simpa only [mem_compl_iff, mem_ball, not_lt] using ha)
      (mem_closedBall.mpr hs)
  obtain ⟨t₀, ht₀, ht₀K, hlast⟩ := exists_last_mem hP hKc hhit
  have hsK : P s ∉ K := fun h => (lt_irrefl _ ((hKann h).1.trans_le hs))
  have ht₀s : t₀ < s := lt_of_le_of_ne ht₀.2 (fun h => hsK (h ▸ ht₀K))
  refine ⟨t₀, ht₀, ht₀s, ht₀K, ?_⟩
  intro t ht
  by_contra hfar
  push Not at hfar
  
  have hPt : ContinuousOn P (Icc t s) := hP.mono (Icc_subset_Icc (ht₀.1.trans ht.1) le_rfl)
  obtain ⟨t₁, ht₁, ht₁K⟩ := exists_hit ht.2 hPt hsep
    (by simpa only [mem_compl_iff, mem_ball, not_lt] using hfar) (mem_closedBall.mpr hs)
  have hle := hlast t₁ ⟨(ht₀.1.trans ht.1).trans ht₁.1, ht₁.2⟩ ht₁K
  have ht₁t₀ : t₁ = t₀ := le_antisymm hle (ht.1.trans ht₁.1)
  have htt₀ : t = t₀ := le_antisymm (ht₁t₀ ▸ ht₁.1) ht.1
  have hfar' := hfar
  rw [htt₀] at hfar'
  exact absurd (hKann ht₀K).2 (not_lt.mpr hfar')

 
theorem exists_first_hit {P : ℝ → ℂ} {s b : ℝ} (hsb : s ≤ b) (hP : ContinuousOn P (Icc s b))
    {K : Set ℂ} {y : ℂ} {ρ R : ℝ} (hρR : ρ ≤ R) (hKc : IsClosed K)
    (hK : LQGMetric.Disconnects K (sphere y ρ) (sphere y R))
    (hKann : K ⊆ {x | ρ < dist x y ∧ dist x y < R})
    (hs : dist (P s) y ≤ ρ) (hb : R ≤ dist (P b) y) :
    ∃ t₀ ∈ Icc s b, s < t₀ ∧ P t₀ ∈ K ∧ ∀ t ∈ Icc s t₀, dist (P t) y < R := by
  have hsep := LQGMetric.Disconnects.closedBall_compl_ball hρR hK
  have hhit : ∃ t ∈ Icc s b, P t ∈ K :=
    exists_hit hsb hP hsep (mem_closedBall.mpr hs)
      (by simpa only [mem_compl_iff, mem_ball, not_lt] using hb)
  obtain ⟨t₀, ht₀, ht₀K, hfirst⟩ := exists_first_mem hP hKc hhit
  have hsK : P s ∉ K := fun h => (lt_irrefl _ ((hKann h).1.trans_le hs))
  have hst₀ : s < t₀ := lt_of_le_of_ne ht₀.1 (fun h => hsK (h ▸ ht₀K))
  refine ⟨t₀, ht₀, hst₀, ht₀K, ?_⟩
  intro t ht
  by_contra hfar
  push Not at hfar
  have hPt : ContinuousOn P (Icc s t) := hP.mono (Icc_subset_Icc le_rfl (ht.2.trans ht₀.2))
  obtain ⟨t₁, ht₁, ht₁K⟩ := exists_hit ht.1 hPt hsep (mem_closedBall.mpr hs)
    (by simpa only [mem_compl_iff, mem_ball, not_lt] using hfar)
  have hle := hfirst t₁ ⟨ht₁.1, ht₁.2.trans (ht.2.trans ht₀.2)⟩ ht₁K
  have ht₁t₀ : t₁ = t₀ := le_antisymm (ht₁.2.trans ht.2) hle
  have htt₀ : t = t₀ := le_antisymm ht.2 (ht₁t₀ ▸ ht₁.2)
  have hfar' := hfar
  rw [htt₀] at hfar'
  exact absurd (hKann ht₀K).2 (not_lt.mpr hfar')

end SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions
