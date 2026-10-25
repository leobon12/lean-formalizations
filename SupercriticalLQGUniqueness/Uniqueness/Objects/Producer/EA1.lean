import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.C8
import SupercriticalLQGUniqueness.Uniqueness.Objects.Compare.ExcursionWeyl




 

















set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Complex
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Producer

 

section bridges

variable (C : Objects.CorrectedEvent.Constants) (D Db : LSCMetric) (f : C(ℂ, ℝ))

 
theorem weyl_len_eq (hWeyl : ∀ x y : ℂ, Db (x, y) = weylScale C.ξ (-f) D (x, y))
    (Q : ℝ → ℂ) (a b : ℝ) :
    HigherDimLQGMetric.curveLengthWith
        (fun x y : D.Space => weylScale C.ξ (-f) D (BiLipschitz.Barrier.forget D x, BiLipschitz.Barrier.forget D y))
        (D.pt ∘ Q) a b = Db.len Q a b := by
  have hδ : (fun x y : D.Space => weylScale C.ξ (-f) D (BiLipschitz.Barrier.forget D x, BiLipschitz.Barrier.forget D y)) =
      (fun x y : D.Space => Db (x, y)) := by
    funext x y
    exact (hWeyl x y).symm
  rw [hδ, Db.len_eq_curveLength]
  exact HigherDimLQGMetric.curveLengthWith_edist (Db.pt ∘ Q) a b

 
theorem bumped_len_zero_trace (hforget : Continuous (BiLipschitz.Barrier.forget D))
    (hWeyl : ∀ x y : ℂ, Db (x, y) = weylScale C.ξ (-f) D (x, y))
    {Q : ℝ → ℂ} {a b : ℝ} (hQ : D.IsCurve Q a b) (h0 : ∀ x ∈ Icc a b, f (Q x) = 0) :
    Db.len Q a b = D.len Q a b := by
  have h := Toolkit.WeylLength.weylCurveLength_eq_of_zero_on_trace D C.ξ (-f) hforget hQ
    (fun s hs => by simp [h0 s hs])
  rw [← weyl_len_eq C D Db f hWeyl Q a b]
  exact h

 
theorem bumped_len_max_trace (hforget : Continuous (BiLipschitz.Barrier.forget D))
    (hWeyl : ∀ x y : ℂ, Db (x, y) = weylScale C.ξ (-f) D (x, y))
    {Q : ℝ → ℂ} {a b : ℝ} (hQ : D.IsCurve Q a b) (hmax : ∀ x ∈ Icc a b, f (Q x) = C.A_max) :
    Db.len Q a b ≤ ENNReal.ofReal (Real.exp (-C.ξ * C.A_max)) * D.len Q a b := by
  have h := (Toolkit.WeylLength.weylCurveLength_factor_bounds D C.ξ C.ξPos.le (-f) hforget hQ (-C.A_max)
    (-C.A_max) (fun s hs => by simp [hmax s hs]) (fun s hs => by simp [hmax s hs])).2
  have h' : Db.len Q a b ≤ ENNReal.ofReal (Real.exp (C.ξ * -C.A_max)) * D.len Q a b := by
    rw [← weyl_len_eq C D Db f hWeyl Q a b]
    exact h
  calc Db.len Q a b ≤ ENNReal.ofReal (Real.exp (C.ξ * -C.A_max)) * D.len Q a b := h'
    _ = ENNReal.ofReal (Real.exp (-C.ξ * C.A_max)) * D.len Q a b := by ring_nf

end bridges

 

 
theorem ennreal_mul_lt_mul_left {a b c : ℝ≥0∞} (ha0 : a ≠ 0) (hat : a ≠ ⊤) (h : b < c) :
    a * b < a * c := by
  have := ENNReal.mul_lt_mul_left ha0 hat h
  rwa [mul_comm b, mul_comm c] at this

theorem unit_len {Db : LSCMetric} {P : ℝ → ℂ} {L : ℝ} (hunit : HasUnitSpeedOn (Db.pt ∘ P) (Icc 0 L))
    {s t : ℝ} (hs : s ∈ Icc 0 L) (ht : t ∈ Icc 0 L) (hst : s ≤ t) :
    Db.len P s t = ENNReal.ofReal (t - s) :=
  (hasUnitSpeedOn_iff Db P L).1 hunit s hs t ht hst

 
theorem internal_le_len_pts (D : LSCMetric) {Y : Set ℂ} {Q : ℝ → ℂ} {a b : ℝ}
    (hQ : D.IsCurve Q a b) (hY : ∀ t ∈ Icc a b, Q t ∈ Y) {x y : ℂ} (hx : x ∈ Y) (hy : y ∈ Y)
    (hxa : Q a = x) (hyb : Q b = y) : D.internal Y (⟨x, hx⟩, ⟨y, hy⟩) ≤ D.len Q a b :=
  iInf_le_of_le Q (iInf_le_of_le a (iInf_le_of_le b (iInf_le_of_le hQ (iInf_le_of_le hY
    (iInf_le_of_le hxa (iInf_le _ hyb))))))

 
theorem exists_curve_of_internal_lt (D : LSCMetric) {Y : Set ℂ} {x y : ℂ} (hx : x ∈ Y)
    (hy : y ∈ Y) {B : ℝ≥0∞} (h : D.internal Y (⟨x, hx⟩, ⟨y, hy⟩) < B) :
    ∃ (Q : ℝ → ℂ) (a b : ℝ), D.IsCurve Q a b ∧ (∀ t ∈ Icc a b, Q t ∈ Y) ∧ Q a = x ∧ Q b = y ∧
      D.len Q a b < B := by
  unfold LSCMetric.internal at h
  simp only [iInf_lt_iff] at h
  obtain ⟨Q, a, b, hQ, hY, ha, hb, hlen⟩ := h
  exact ⟨Q, a, b, hQ, hY, ha, hb, hlen⟩

 

 
theorem mid_ann_subset (C : Objects.CorrectedEvent.Constants) :
    Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r) ⊆ Objects.CorrectedEvent.ann 0 C.r (4 * C.r) := by
  intro x hx
  have hr := C.rPos
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

 


theorem offbump_diam_lt (C : Objects.CorrectedEvent.Constants) (D Db : LSCMetric) (f : C(ℂ, ℝ))
    (hforget : Continuous (BiLipschitz.Barrier.forget D))
    (hWeyl : ∀ x y : ℂ, Db (x, y) = weylScale C.ξ (-f) D (x, y))
    {P : ℝ → ℂ} {L : ℝ} (hPD : D.IsCurve P 0 L) (hunit : HasUnitSpeedOn (Db.pt ∘ P) (Icc 0 L))
    (hcont : ContinuousOn P (Icc 0 L)) {N : ℝ}
    (hnarrow : ∀ (z w : ℂ) (hz : z ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r))
      (hw : w ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r)), dist z w ≤ C.A_nar / C.lamConst * C.r →
      ENNReal.ofReal ((dist z w / C.r) ^ (C.ξ * (C.Q + 3))) * ENNReal.ofReal N ≤
        D.internal (Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) (⟨z, mid_ann_subset C hz⟩, ⟨w, mid_ann_subset C hw⟩))
    (hlam : C.lamConst ≤ 1)
    {p q : ℝ} (h0p : 0 ≤ p) (hqL : q ≤ L)
    (hshort : q - p < C.A_nar ^ (C.ξ * (C.Q + 3)) * N)
    (hoff : ∀ t ∈ Icc p q, f (P t) = 0)
    (hloc : ∀ t ∈ Icc p q, P t ∈ Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r)) :
    ∀ s ∈ Icc p q, ∀ t ∈ Icc p q, dist (P s) (P t) < C.A_nar * C.r := by
  have hr := C.rPos
  have hnar := C.narPos
  have hlampos := C.lamPos
  
  suffices key : ∀ s ∈ Icc p q, ∀ t ∈ Icc p q, s ≤ t → dist (P s) (P t) < C.A_nar * C.r by
    intro s hs t ht
    rcases le_total s t with h | h
    · exact key s hs t ht h
    · rw [dist_comm]; exact key t ht s hs h
  intro s hs t ht hst
  by_contra hcon
  push Not at hcon
  
  have hcst : ContinuousOn (fun x => dist (P s) (P x)) (Icc s t) :=
    (continuous_const.dist continuous_id).comp_continuousOn
      (hcont.mono (Icc_subset_Icc (h0p.trans hs.1) (ht.2.trans hqL)))
  obtain ⟨t', ht', hdt'⟩ := intermediate_value_Icc hst hcst
    (show C.A_nar * C.r ∈ Icc (dist (P s) (P s)) (dist (P s) (P t)) by
      rw [dist_self]; exact ⟨by positivity, hcon⟩)
  simp only at hdt'
  have hst' : s < t' := by
    rcases eq_or_lt_of_le ht'.1 with h | h
    · rw [← h, dist_self] at hdt'
      exfalso
      have : 0 < C.A_nar * C.r := by positivity
      linarith
    · exact h
  have ht'pq : t' ∈ Icc p q := ⟨hs.1.trans ht'.1, ht'.2.trans ht.2⟩
  
  have hzs := hloc s hs
  have hzt := hloc t' ht'pq
  have hwin : dist (P s) (P t') ≤ C.A_nar / C.lamConst * C.r := by
    rw [hdt']
    have : C.A_nar ≤ C.A_nar / C.lamConst := by
      rw [le_div_iff₀ hlampos]
      nlinarith
    nlinarith
  have hE := hnarrow (P s) (P t') hzs hzt hwin
  rw [hdt', mul_div_assoc, div_self hr.ne', mul_one] at hE
  
  have hsub : D.IsCurve P s t' := ⟨hst'.le, hPD.2.mono (Icc_subset_Icc (h0p.trans hs.1)
    (ht'.2.trans (ht.2.trans hqL)))⟩
  have hint := internal_le_len_pts D (Y := Objects.CorrectedEvent.ann 0 C.r (4 * C.r)) hsub
    (fun x hx => mid_ann_subset C (hloc x ⟨hs.1.trans hx.1, hx.2.trans ht'pq.2⟩))
    (mid_ann_subset C hzs) (mid_ann_subset C hzt) rfl rfl
  have hzero : ∀ x ∈ Icc s t', f (P x) = 0 := fun x hx => hoff x ⟨hs.1.trans hx.1, hx.2.trans ht'pq.2⟩
  have hlenD : D.len P s t' = ENNReal.ofReal (t' - s) := by
    rw [← bumped_len_zero_trace C D Db f hforget hWeyl hsub hzero]
    exact unit_len hunit ⟨h0p.trans hs.1, hs.2.trans hqL⟩ ⟨h0p.trans ht'pq.1, ht'pq.2.trans hqL⟩ hst'.le
  have hchain := hE.trans (hint.trans hlenD.le)
  rw [← ENNReal.ofReal_mul (by positivity)] at hchain
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 hchain
  have : t' - s ≤ q - p := by linarith [ht'pq.2, hs.1]
  linarith

 

 
def cheapSet (D : LSCMetric) (c u : ℂ) (s₀ B : ℝ) : Set ℂ :=
  {w | ∃ (Q : ℝ → ℂ) (a b : ℝ), D.IsCurve Q a b ∧ (∀ t ∈ Icc a b, Q t ∈ closedBall c s₀) ∧
    Q a = w ∧ Q b = u ∧ D.len Q a b < ENNReal.ofReal B}

 
def goodSet (D : LSCMetric) (c u : ℂ) (s₀ B : ℝ) (hu : u ∈ closedBall c s₀) : Set ℂ :=
  {x | x ∈ sphere c s₀ ∧ ∃ hx : x ∈ closedBall c s₀,
    D.internal (closedBall c s₀) (⟨x, hx⟩, ⟨u, hu⟩) ≤ ENNReal.ofReal B}

 
theorem cheapSet_of_curve (D : LSCMetric) {c u : ℂ} {s₀ B : ℝ} {Q : ℝ → ℂ} {a b : ℝ}
    (hQ : D.IsCurve Q a b) (hY : ∀ t ∈ Icc a b, Q t ∈ closedBall c s₀) (hb : Q b = u)
    (hlen : D.len Q a b < ENNReal.ofReal B) : ∀ t ∈ Icc a b, Q t ∈ cheapSet D c u s₀ B := by
  intro t ht
  refine ⟨Q, t, b, ⟨ht.2, hQ.2.mono (Icc_subset_Icc ht.1 le_rfl)⟩,
    fun x hx => hY x ⟨ht.1.trans hx.1, hx.2⟩, rfl, hb, lt_of_le_of_lt ?_ hlen⟩
  exact LQGMetric.MetricGeometry.curveLength_mono _ ht.1 le_rfl

 
theorem attach_of_cheap (C : Objects.CorrectedEvent.Constants) (D Db : LSCMetric) (f : C(ℂ, ℝ))
    (hforget : Continuous (BiLipschitz.Barrier.forget D)) (hL : D.IsLengthSpace)
    (hWeyl : ∀ x y : ℂ, Db (x, y) = weylScale C.ξ (-f) D (x, y))
    (hf : ∀ x : ℂ, 0 ≤ f x ∧ f x ≤ C.A_max)
    {c u : ℂ} {s₀ dt : ℝ} (hfB : ∀ x ∈ closedBall c s₀, f x = C.A_max)
    {Y : Set ℂ} (hBY : closedBall c s₀ ⊆ Y) {w : ℂ} (hw : w ∈ cheapSet D c u s₀ (2 * C.lamConst * dt))
    (hwY : w ∈ Y) (huY : u ∈ Y) :
    Db.internal Y (⟨w, hwY⟩, ⟨u, huY⟩) <
      ENNReal.ofReal (2 * C.lamConst * (Real.exp (-C.ξ * C.A_max) * dt)) := by
  obtain ⟨Q, a, b, hQ, hY, ha, hb, hlen⟩ := hw
  have hQb : Db.IsCurve Q a b := Objects.Splice.bumped_curve_transfer C D Db f hforget hWeyl hf hL hQ
  have h1 := internal_le_len_pts Db hQb (fun t ht => hBY (hY t ht)) hwY huY ha hb
  have h2 := bumped_len_max_trace C D Db f hforget hWeyl hQ (fun t ht => hfB (Q t) (hY t ht))
  have hexp : 0 < Real.exp (-C.ξ * C.A_max) := Real.exp_pos _
  have hfin : D.len Q a b ≠ ⊤ := ne_top_of_lt hlen
  calc Db.internal Y (⟨w, hwY⟩, ⟨u, huY⟩) ≤ Db.len Q a b := h1
    _ ≤ ENNReal.ofReal (Real.exp (-C.ξ * C.A_max)) * D.len Q a b := h2
    _ < ENNReal.ofReal (Real.exp (-C.ξ * C.A_max)) * ENNReal.ofReal (2 * C.lamConst * dt) :=
        ennreal_mul_lt_mul_left (by simpa using hexp) ENNReal.ofReal_ne_top hlen
    _ = ENNReal.ofReal (2 * C.lamConst * (Real.exp (-C.ξ * C.A_max) * dt)) := by
        rw [← ENNReal.ofReal_mul hexp.le]
        congr 1
        ring

 

theorem cheap_path_avoiding (C : Objects.CorrectedEvent.Constants) (D : LSCMetric)
    (hforget : Continuous (BiLipschitz.Barrier.forget D))
    {c u : ℂ} {s₀ dt : ℝ} (hdt : 0 < C.lamConst * dt) (hu : u ∈ closedBall c s₀)
    {P : ℝ → ℂ} {a b : ℝ}
    (hnohit : ∀ t ∈ Icc a b, P t ∉ cheapSet D c u s₀ (2 * C.lamConst * dt))
    {x : ℂ} (hx : x ∈ goodSet D c u s₀ (C.lamConst * dt) hu) :
    ∃ γ : Path u x, (∀ τ, γ τ ∈ closedBall c s₀) ∧ (∀ τ, ∀ t ∈ Icc a b, γ τ ≠ P t) ∧
      ∀ τ, γ τ ∈ cheapSet D c u s₀ (2 * C.lamConst * dt) := by
  obtain ⟨-, hxB, hxint⟩ := hx
  have hlt : D.internal (closedBall c s₀) (⟨x, hxB⟩, ⟨u, hu⟩) <
      ENNReal.ofReal (2 * C.lamConst * dt) := by
    refine hxint.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith))
  obtain ⟨Q, a', b', hQ, hY, ha, hb, hlen⟩ := exists_curve_of_internal_lt D hxB hu hlt
  have hcheap := cheapSet_of_curve D hQ hY hb hlen
  have hQc : ContinuousOn Q (Icc a' b') := hforget.comp_continuousOn hQ.2
  let p₀ : Path (Q a') (Q b') := LQGMetric.pathOfIcc Q hQ.1 hQc
  let p₁ : Path x u := p₀.cast ha.symm hb.symm
  have hrange : ∀ τ : unitInterval, ∃ σ ∈ Icc a' b', Q σ = p₁.symm τ := fun τ =>
    LQGMetric.range_pathOfIcc_subset Q hQ.1 hQc ⟨unitInterval.symm τ, rfl⟩
  refine ⟨p₁.symm, fun τ => ?_, fun τ t ht hEq => ?_, fun τ => ?_⟩
  · obtain ⟨σ, hσ, hσeq⟩ := hrange τ
    exact hσeq ▸ hY σ hσ
  · obtain ⟨σ, hσ, hσeq⟩ := hrange τ
    have := hcheap σ hσ
    rw [hσeq, hEq] at this
    exact hnohit t ht this
  · obtain ⟨σ, hσ, hσeq⟩ := hrange τ
    have := hcheap σ hσ
    rwa [hσeq] at this

end SupercriticalLQGUniqueness.Uniqueness.Objects.Producer
