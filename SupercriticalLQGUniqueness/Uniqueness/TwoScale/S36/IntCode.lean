import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.HProjection
import LQGMetric.Metric.CurveNatural




 

















set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal NNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

 

 

def intExt (D : LSCMetric) (Y : Set ℂ) (x y : ℂ) : ℝ≥0∞ :=
  ⨅ (P : ℝ → ℂ) (a : ℝ) (b : ℝ) (_ : D.IsCurve P a b) (_ : ∀ t ∈ Icc a b, P t ∈ Y)
    (_ : P a = x) (_ : P b = y), D.len P a b

theorem internal_eq_intExt (D : LSCMetric) (Y : Set ℂ) (p : Y × Y) :
    D.internal Y p = intExt D Y p.1 p.2 :=
  rfl

theorem intExt_le_len {D : LSCMetric} {Y : Set ℂ} {P : ℝ → ℂ} {a b : ℝ}
    (hP : D.IsCurve P a b) (hY : ∀ t ∈ Icc a b, P t ∈ Y) :
    intExt D Y (P a) (P b) ≤ D.len P a b :=
  iInf_le_of_le P (iInf_le_of_le a (iInf_le_of_le b (iInf_le_of_le hP
    (iInf_le_of_le hY (iInf_le_of_le rfl (iInf_le (fun _ : P b = P b => D.len P a b) rfl))))))

theorem intExt_eq_top_of_not_mem_left {D : LSCMetric} {Y : Set ℂ} {x : ℂ} (y : ℂ)
    (hx : x ∉ Y) : intExt D Y x y = ⊤ := by
  refine top_unique (le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hc =>
    le_iInf fun hY => le_iInf fun hPa => le_iInf fun _ => ?_)
  exact absurd (hPa ▸ hY a ⟨le_rfl, hc.1⟩) hx

theorem intExt_eq_top_of_not_mem_right {D : LSCMetric} {Y : Set ℂ} (x : ℂ) {y : ℂ}
    (hy : y ∉ Y) : intExt D Y x y = ⊤ := by
  refine top_unique (le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hc =>
    le_iInf fun hY => le_iInf fun _ => le_iInf fun hPb => ?_)
  exact absurd (hPb ▸ hY b ⟨hc.1, le_rfl⟩) hy

 
theorem measurable_intExt_code {Y : Set ℂ} (hY : IsCompact Y) :
    Measurable fun p : LSCMetric × PathCode => intExt p.1 Y (p.2 0) (p.2 1) := by
  set S : Set (LSCMetric × PathCode) := {p | p.2 0 ∈ Y ∧ p.2 1 ∈ Y} with hSdef
  have hS : MeasurableSet S := by
    have h0 : MeasurableSet {p : LSCMetric × PathCode | p.2 0 ∈ Y} :=
      ((continuous_eval_const (0 : unitInterval)).measurable.comp measurable_snd)
        hY.isClosed.measurableSet
    have h1 : MeasurableSet {p : LSCMetric × PathCode | p.2 1 ∈ Y} :=
      ((continuous_eval_const (1 : unitInterval)).measurable.comp measurable_snd)
        hY.isClosed.measurableSet
    exact h0.inter h1
  refine measurable_of_restrict_of_restrict_compl hS ?_ ?_
  · 
    let φ : S → LSCMetric × (Y × Y) := fun p =>
      (p.1.1, (⟨p.1.2 0, p.2.1⟩, ⟨p.1.2 1, p.2.2⟩))
    have hφ : Measurable φ := by
      have hb : Measurable fun p : S => p.1 := measurable_subtype_coe
      refine (measurable_fst.comp hb).prodMk (Measurable.prodMk ?_ ?_)
      · exact (((continuous_eval_const (0 : unitInterval)).measurable.comp
          measurable_snd).comp hb).subtype_mk
      · exact (((continuous_eval_const (1 : unitInterval)).measurable.comp
          measurable_snd).comp hb).subtype_mk
    have hint := (TwoScale.S36Events.internal_compact_joint_lsc hY).measurable
    have h2 := hint.comp hφ
    have heq : S.domRestrict (fun p : LSCMetric × PathCode => intExt p.1 Y (p.2 0) (p.2 1)) =
        (fun q : LSCMetric × (Y × Y) => q.1.internal Y (q.2.1, q.2.2)) ∘ φ := by
      funext p
      rfl
    rw [heq]
    exact h2
  · have heq : Sᶜ.domRestrict (fun p : LSCMetric × PathCode => intExt p.1 Y (p.2 0) (p.2 1)) =
        fun _ => ⊤ := by
      funext p
      have hp : ¬ (p.1.2 0 ∈ Y ∧ p.1.2 1 ∈ Y) := p.2
      by_cases h0 : p.1.2 0 ∈ Y
      · have h1 : p.1.2 1 ∉ Y := fun h1 => hp ⟨h0, h1⟩
        exact intExt_eq_top_of_not_mem_right _ h1
      · exact intExt_eq_top_of_not_mem_left _ h0
    rw [heq]
    exact measurable_const

 

 
theorem lipCode_iff_rat (D : LSCMetric) (γ : PathCode) {L : ℝ≥0∞} (hL : L ≠ ⊤) :
    (∀ s t : unitInterval, (s : ℝ) ≤ t → D (γ s, γ t) ≤ ENNReal.ofReal ((t : ℝ) - s) * L) ↔
      ∀ q : RatTimes, D (γ q.lo, γ q.hi) ≤ ENNReal.ofReal ((q.hi : ℝ) - q.lo) * L := by
  constructor
  · intro hall q
    exact hall q.lo q.hi q.2.2.1
  · intro hrat s t hst
    by_contra hbad
    rw [not_le] at hbad
    let F : unitInterval × unitInterval → ℝ≥0∞ := fun p => D (γ p.1, γ p.2)
    let G : unitInterval × unitInterval → ℝ≥0∞ :=
      fun p => ENNReal.ofReal ((p.2 : ℝ) - p.1) * L
    have hFl : LowerSemicontinuous F := by
      have hc : Continuous fun p : unitInterval × unitInterval => (γ p.1, γ p.2) :=
        (γ.continuous.comp continuous_fst).prodMk (γ.continuous.comp continuous_snd)
      exact D.lowerSemicontinuous.comp hc
    have hGc : Continuous G := by
      have h1 : Continuous fun p : unitInterval × unitInterval =>
          ENNReal.ofReal ((p.2 : ℝ) - p.1) :=
        ENNReal.continuous_ofReal.comp
          ((continuous_subtype_val.comp continuous_snd).sub
            (continuous_subtype_val.comp continuous_fst))
      exact (ENNReal.continuous_mul_const hL).comp h1
    have hO : IsOpen {p | G p < F p} := isOpen_lt_of_continuous_lsc hGc hFl
    have hmem : (s, t) ∈ {p | G p < F p} := hbad
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO (s, t) hmem
    obtain ⟨q₁, hq₁0, hq₁s, hq₁ε⟩ := exists_rat_below s hε
    obtain ⟨q₂, hq₂1, hq₂t, hq₂ε⟩ := exists_rat_above t hε
    let q : RatTimes := ⟨(q₁, q₂), hq₁0, hq₁s.trans (hst.trans hq₂t), hq₂1⟩
    have hqball : (q.lo, q.hi) ∈ Metric.ball (s, t) ε := by
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      constructor
      · rw [Subtype.dist_eq, Real.dist_eq, abs_lt]
        change -ε < (q₁ : ℝ) - s ∧ (q₁ : ℝ) - s < ε
        constructor <;> linarith
      · rw [Subtype.dist_eq, Real.dist_eq, abs_lt]
        change -ε < (q₂ : ℝ) - t ∧ (q₂ : ℝ) - t < ε
        constructor <;> linarith
    exact (not_lt_of_ge (hrat q)) (hball hqball)

 
theorem codeExt_dist_le_of_lip {D : LSCMetric} {γ : PathCode} {L : ℝ≥0∞} (hL : L ≠ ⊤)
    (hlip : ∀ s t : unitInterval, (s : ℝ) ≤ t →
      D (γ s, γ t) ≤ ENNReal.ofReal ((t : ℝ) - s) * L)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    D (codeExt γ x, codeExt γ y) ≤ L.toNNReal * edist x y := by
  rw [ENNReal.coe_toNNReal hL, codeExt_of_mem γ hx, codeExt_of_mem γ hy]
  rcases le_total x y with hxy | hyx
  · have h := hlip ⟨x, hx⟩ ⟨y, hy⟩ hxy
    rw [edist_dist, Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hxy), mul_comm]
    exact h
  · have h := hlip ⟨y, hy⟩ ⟨x, hx⟩ hyx
    rw [D.isExtMetric.2.2.1, edist_dist, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hyx),
      mul_comm]
    exact h

 
theorem curve_len_of_lip {D : LSCMetric} {γ : PathCode} {L : ℝ≥0∞} (hL : L ≠ ⊤)
    (hlip : ∀ s t : unitInterval, (s : ℝ) ≤ t →
      D (γ s, γ t) ≤ ENNReal.ofReal ((t : ℝ) - s) * L) :
    D.IsCurve (codeExt γ) 0 1 ∧ D.len (codeExt γ) 0 1 ≤ L := by
  have hLip : LipschitzOnWith L.toNNReal (D.pt ∘ codeExt γ) (Icc 0 1) :=
    fun x hx y hy => codeExt_dist_le_of_lip hL hlip hx hy
  refine ⟨⟨zero_le_one, hLip.continuousOn⟩, ?_⟩
  have h1 : eVariationOn (D.pt ∘ codeExt γ ∘ id) (Icc (0 : ℝ) 1) ≤
      L.toNNReal * eVariationOn (id : ℝ → ℝ) (Icc 0 1) :=
    hLip.comp_eVariationOn_le (mapsTo_id _)
  have h2 : eVariationOn (id : ℝ → ℝ) (Icc (0 : ℝ) 1) ≤ ENNReal.ofReal (1 - 0) := by
    have h := (monotone_id.monotoneOn (Icc (0 : ℝ) 1)).eVariationOn_eq
      (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
    simp only [inter_self, id] at h
    exact h.le
  calc
    D.len (codeExt γ) 0 1 = eVariationOn (D.pt ∘ codeExt γ ∘ id) (Icc (0 : ℝ) 1) := rfl
    _ ≤ L.toNNReal * eVariationOn (id : ℝ → ℝ) (Icc 0 1) := h1
    _ ≤ L.toNNReal * ENNReal.ofReal (1 - 0) := mul_le_mul' le_rfl h2
    _ = L := by rw [ENNReal.coe_toNNReal hL]; norm_num

 

 

def IsIntGeod (D : LSCMetric) (Y : Set ℂ) (P : ℝ → ℂ) (s t : ℝ) : Prop :=
  D.IsCurve P s t ∧ (∀ v ∈ Icc s t, P v ∈ Y) ∧
    D.len P s t = intExt D Y (P s) (P t) ∧ D.len P s t < ⊤

 
def IsIntCode (D : LSCMetric) (Y : Set ℂ) (γ : PathCode) : Prop :=
  (∀ τ, γ τ ∈ Y) ∧ intExt D Y (γ 0) (γ 1) < ⊤ ∧
    ∀ s t : unitInterval, (s : ℝ) ≤ t →
      D (γ s, γ t) ≤ ENNReal.ofReal ((t : ℝ) - s) * intExt D Y (γ 0) (γ 1)

 
theorem intGeod_of_intCode {D : LSCMetric} {Y : Set ℂ} {γ : PathCode}
    (hγ : IsIntCode D Y γ) : IsIntGeod D Y (codeExt γ) 0 1 := by
  obtain ⟨hY, hfin, hlip⟩ := hγ
  obtain ⟨hcurve, hle⟩ := curve_len_of_lip hfin.ne hlip
  have htr : ∀ v ∈ Icc (0 : ℝ) 1, codeExt γ v ∈ Y := fun v hv => by
    rw [codeExt_of_mem γ hv]
    exact hY _
  have hge : intExt D Y (codeExt γ 0) (codeExt γ 1) ≤ D.len (codeExt γ) 0 1 :=
    intExt_le_len hcurve htr
  rw [codeExt_zero, codeExt_one] at hge
  refine ⟨hcurve, htr, ?_, ?_⟩
  · rw [codeExt_zero, codeExt_one]
    exact le_antisymm hle hge
  · exact hle.trans_lt hfin

 
theorem IsIntGeod.shift {D : LSCMetric} {Y : Set ℂ} {P : ℝ → ℂ} {s t : ℝ}
    (hP : IsIntGeod D Y P s t) (c : ℝ) :
    IsIntGeod D Y (fun τ => P (τ - c)) (s + c) (t + c) := by
  obtain ⟨⟨hst, hcont⟩, htr, hlen, hfin⟩ := hP
  have himg : (fun τ : ℝ => τ - c) '' Icc (s + c) (t + c) = Icc s t := by
    rw [image_sub_const_Icc]
    simp only [add_sub_cancel_right]
  have hmono : MonotoneOn (fun τ : ℝ => τ - c) (Icc (s + c) (t + c)) :=
    fun x _ y _ hxy => sub_le_sub_right hxy c
  have hlen' : D.len (fun τ => P (τ - c)) (s + c) (t + c) = D.len P s t := by
    have h := eVariationOn.comp_eq_of_monotoneOn (D.pt ∘ P) (fun τ : ℝ => τ - c) hmono
    rw [himg] at h
    exact h
  have hmaps : MapsTo (fun τ : ℝ => τ - c) (Icc (s + c) (t + c)) (Icc s t) := by
    intro τ hτ
    rw [← himg]
    exact mem_image_of_mem _ hτ
  refine ⟨⟨by linarith, ?_⟩, ?_, ?_, ?_⟩
  · exact hcont.comp ((continuous_id.sub continuous_const).continuousOn) hmaps
  · intro v hv
    exact htr _ (hmaps hv)
  · rw [hlen']
    simp only [add_sub_cancel_right]
    exact hlen
  · rw [hlen']
    exact hfin

 
theorem intGeod_shift_of_intCode {D : LSCMetric} {Y : Set ℂ} {γ : PathCode}
    (hγ : IsIntCode D Y γ) : IsIntGeod D Y (fun τ => codeExt γ (τ - 1)) 1 2 := by
  have h := (intGeod_of_intCode hγ).shift 1
  norm_num at h
  exact h

 

theorem exists_intCode_of_intGeod {D : LSCMetric} {Y : Set ℂ} (hY : IsCompact Y)
    {P : ℝ → ℂ} {s t : ℝ} (hP : IsIntGeod D Y P s t) :
    ∃ γ : PathCode, IsIntCode D Y γ ∧ γ 0 = P s ∧ γ 1 = P t ∧
      (∀ τ, ∃ x ∈ Icc s t, γ τ = P x) ∧
      ∀ v ∈ Icc s t, ∀ w ∈ Icc s t, v ≤ w →
        ∃ σ σ' : unitInterval, (σ : ℝ) ≤ σ' ∧ γ σ = P v ∧ γ σ' = P w ∧
          ∀ τ : unitInterval, (σ : ℝ) ≤ τ → (τ : ℝ) ≤ σ' → ∃ x ∈ Icc v w, γ τ = P x := by
  obtain ⟨hcurve, htr, hlen, hfin⟩ := hP
  have hst : s ≤ t := hcurve.1
  set f : ℝ → D.Space := D.pt ∘ P with hf
  have hfc : ContinuousOn f (Icc s t) := hcurve.2
  have hL' : LQGMetric.MetricGeometry.curveLength f s t ≠ ⊤ := hfin.ne
  set Lr : ℝ := (D.len P s t).toReal with hLr
  have hLr0 : 0 ≤ Lr := ENNReal.toReal_nonneg
  have hLofReal : ENNReal.ofReal Lr = D.len P s t := ENNReal.ofReal_toReal hfin.ne
  set Q : ℝ → D.Space := LQGMetric.MetricGeometry.lengthParam f s t with hQ
  set φ : ℝ → ℝ := variationOnFromTo f (Icc s t) s with hφ
  have hBV : BoundedVariationOn f (Icc s t) := hL'
  have hsmem : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have hφcont : ContinuousOn φ (Icc s t) := fun x hx =>
    (hBV.continuousWithinAt_variationOnFromTo_iff hsmem hx).2 (hfc x hx)
  have hφmono : MonotoneOn φ (Icc s t) :=
    variationOnFromTo.monotoneOn hBV.locallyBoundedVariationOn hsmem
  have hφs : φ s = 0 := variationOnFromTo.self f (Icc s t) s
  have hφt : φ t = Lr := by
    rw [hφ, variationOnFromTo.eq_of_le _ _ hst, inter_self]
    rfl
  have hQφ : ∀ x ∈ Icc s t, Q (φ x) = f x := fun x hx =>
    LQGMetric.MetricGeometry.lengthParam_variationOnFromTo hL' hx
  have hφrange : ∀ x ∈ Icc s t, φ x ∈ Icc 0 Lr := fun x hx =>
    ⟨hφs ▸ hφmono hsmem hx hx.1, hφt ▸ hφmono hx ⟨hst, le_rfl⟩ hx.2⟩
  have himg : φ '' Icc s t = Icc 0 Lr := by
    have h := LQGMetric.MetricGeometry.variationOnFromTo_image_Icc hst hfc hL'
    exact h
  have hQlip : LipschitzOnWith 1 Q (Icc 0 Lr) :=
    LQGMetric.MetricGeometry.lipschitzOnWith_lengthParam hst hfc hL'
  
  let g : unitInterval → ℂ := fun τ => (Q ((τ : ℝ) * Lr) : ℂ)
  have hτL : ∀ τ : unitInterval, (τ : ℝ) * Lr ∈ Icc 0 Lr := fun τ =>
    ⟨mul_nonneg τ.2.1 hLr0, mul_le_of_le_one_left hLr0 τ.2.2⟩
  have hgP : ∀ τ : unitInterval, ∃ x ∈ Icc s t, g τ = P x := by
    intro τ
    have hmem : (τ : ℝ) * Lr ∈ φ '' Icc s t := himg ▸ hτL τ
    obtain ⟨x, hx, hxeq⟩ := hmem
    refine ⟨x, hx, ?_⟩
    change (Q ((τ : ℝ) * Lr) : ℂ) = P x
    rw [← hxeq, hQφ x hx]
    rfl
  have hgD : Continuous (D.pt ∘ g) := by
    have hm : Continuous fun τ : unitInterval => (τ : ℝ) * Lr :=
      continuous_subtype_val.mul continuous_const
    have hQc : ContinuousOn Q (Icc 0 Lr) := hQlip.continuousOn
    exact hQc.comp_continuous hm hτL
  have hKP : IsCompact (P '' Icc s t) :=
    isCompact_Icc.image_of_continuousOn (hcurve.continuousOn_of_mapsTo hY fun v hv => htr v hv)
  have hgK : ∀ τ, g τ ∈ P '' Icc s t := fun τ => by
    obtain ⟨x, hx, hxeq⟩ := hgP τ
    exact ⟨x, hx, hxeq.symm⟩
  have hgc : Continuous g := Toolkit.CompactPathInfimum.continuous_euclidean_of_metric_on_compact D hKP hgK hgD
  let γ : PathCode := ⟨g, hgc⟩
  have hγapp : ∀ τ : unitInterval, γ τ = (Q ((τ : ℝ) * Lr) : ℂ) := fun τ => rfl
  
  have hdivmul : ∀ x ∈ Icc s t, φ x / Lr * Lr = φ x := by
    intro x hx
    rcases eq_or_ne Lr 0 with h0 | h0
    · have hφx : φ x = 0 := by
        have h := hφrange x hx
        rw [h0] at h
        exact le_antisymm h.2 h.1
      rw [h0, hφx]
      simp
    · exact div_mul_cancel₀ (φ x) h0
  have htm_mem : ∀ x ∈ Icc s t, φ x / Lr ∈ Icc (0 : ℝ) 1 := by
    intro x hx
    refine ⟨div_nonneg (hφrange x hx).1 hLr0, ?_⟩
    rcases eq_or_ne Lr 0 with h0 | h0
    · rw [h0, div_zero]
      exact zero_le_one
    · exact (div_le_one (lt_of_le_of_ne hLr0 (Ne.symm h0))).mpr (hφrange x hx).2
  have hγtm : ∀ x (hx : x ∈ Icc s t), γ ⟨φ x / Lr, htm_mem x hx⟩ = P x := by
    intro x hx
    rw [hγapp]
    change (Q (φ x / Lr * Lr) : ℂ) = P x
    rw [hdivmul x hx, hQφ x hx]
    rfl
  have hγ0 : γ 0 = P s := by
    have h := hγtm s hsmem
    have he : (⟨φ s / Lr, htm_mem s hsmem⟩ : unitInterval) = 0 := by
      apply Subtype.ext
      change φ s / Lr = 0
      rw [hφs, zero_div]
    rw [he] at h
    exact h
  have htmem : t ∈ Icc s t := ⟨hst, le_rfl⟩
  have hγ1 : γ 1 = P t := by
    rw [hγapp]
    change (Q (1 * Lr) : ℂ) = P t
    rw [one_mul, ← hφt, hQφ t htmem]
    rfl
  refine ⟨γ, ⟨fun τ => ?_, ?_, ?_⟩, hγ0, hγ1, hgP, ?_⟩
  · obtain ⟨x, hx, hxeq⟩ := hgP τ
    change g τ ∈ Y
    rw [hxeq]
    exact htr x hx
  · rw [hγ0, hγ1, ← hlen]
    exact hfin
  · intro σ σ' hσσ'
    have h := hQlip (hτL σ) (hτL σ')
    rw [hγ0, hγ1, ← hlen, ← hLofReal]
    change edist (Q ((σ : ℝ) * Lr)) (Q ((σ' : ℝ) * Lr)) ≤ _
    refine h.trans ?_
    rw [ENNReal.coe_one, one_mul, edist_dist, Real.dist_eq, abs_sub_comm,
      ← sub_mul, abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hσσ') hLr0),
      ENNReal.ofReal_mul (sub_nonneg.mpr hσσ')]
  · intro v hv w hw hvw
    refine ⟨⟨φ v / Lr, htm_mem v hv⟩, ⟨φ w / Lr, htm_mem w hw⟩, ?_, hγtm v hv, hγtm w hw, ?_⟩
    · exact div_le_div_of_nonneg_right (hφmono hv hw hvw) hLr0
    · intro τ hτ1 hτ2
      have hlo : φ v ≤ (τ : ℝ) * Lr := by
        rw [← hdivmul v hv]
        exact mul_le_mul_of_nonneg_right hτ1 hLr0
      have hhi : (τ : ℝ) * Lr ≤ φ w := by
        rw [← hdivmul w hw]
        exact mul_le_mul_of_nonneg_right hτ2 hLr0
      have hsub : Icc v w ⊆ Icc s t := Icc_subset_Icc hv.1 hw.2
      obtain ⟨x, hx, hxeq⟩ :=
        intermediate_value_Icc hvw (hφcont.mono hsub) ⟨hlo, hhi⟩
      refine ⟨x, hx, ?_⟩
      rw [hγapp, ← hxeq, hQφ x (hsub hx)]
      rfl

 
theorem measurable_code_eval (x y : unitInterval) :
    Measurable fun p : LSCMetric × PathCode => p.1 (p.2 x, p.2 y) := by
  have hc : Measurable fun p : LSCMetric × PathCode =>
      ((p.1, (p.2 x, p.2 y)) : LSCMetric × (ℂ × ℂ)) := by
    refine measurable_fst.prodMk (Measurable.prodMk ?_ ?_)
    · exact (continuous_eval_const x).measurable.comp measurable_snd
    · exact (continuous_eval_const y).measurable.comp measurable_snd
  have h := TwoScale.S36Events.jointEval_lsc.measurable.comp hc
  simpa only [Function.comp_def] using h

 
theorem measurableSet_isIntCode {Y : Set ℂ} (hY : IsCompact Y) :
    MeasurableSet {p : LSCMetric × PathCode | IsIntCode p.1 Y p.2} := by
  have hint := measurable_intExt_code hY
  have htr : MeasurableSet {p : LSCMetric × PathCode | ∀ τ, p.2 τ ∈ Y} :=
    measurable_snd (isClosed_trace Y hY.isClosed).measurableSet
  have hfin : MeasurableSet {p : LSCMetric × PathCode | intExt p.1 Y (p.2 0) (p.2 1) < ⊤} :=
    measurableSet_lt hint measurable_const
  have hq : ∀ q : RatTimes, MeasurableSet {p : LSCMetric × PathCode |
      p.1 (p.2 q.lo, p.2 q.hi) ≤
        ENNReal.ofReal ((q.hi : ℝ) - q.lo) * intExt p.1 Y (p.2 0) (p.2 1)} := fun q =>
    measurableSet_le (measurable_code_eval q.lo q.hi) (measurable_const.mul hint)
  have hall : MeasurableSet (⋂ q : RatTimes, {p : LSCMetric × PathCode |
      p.1 (p.2 q.lo, p.2 q.hi) ≤
        ENNReal.ofReal ((q.hi : ℝ) - q.lo) * intExt p.1 Y (p.2 0) (p.2 1)}) :=
    MeasurableSet.iInter hq
  have heq : {p : LSCMetric × PathCode | IsIntCode p.1 Y p.2} =
      {p : LSCMetric × PathCode | ∀ τ, p.2 τ ∈ Y} ∩
        ({p : LSCMetric × PathCode | intExt p.1 Y (p.2 0) (p.2 1) < ⊤} ∩
          ⋂ q : RatTimes, {p : LSCMetric × PathCode |
            p.1 (p.2 q.lo, p.2 q.hi) ≤
              ENNReal.ofReal ((q.hi : ℝ) - q.lo) * intExt p.1 Y (p.2 0) (p.2 1)}) := by
    ext p
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, mem_iInter.mpr ((lipCode_iff_rat p.1 p.2 h2.ne).mp h3)⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, (lipCode_iff_rat p.1 p.2 h2.ne).mpr (mem_iInter.mp h3)⟩
  rw [heq]
  exact htr.inter (hfin.inter hall)

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
