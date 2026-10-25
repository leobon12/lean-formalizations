import SupercriticalLQGUniqueness.B2.Median.MedianUniqueness
import SupercriticalLQGUniqueness.B2.Median.Inputs
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.MetricLemmas
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.Bridge

 






set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Median


open Uniqueness.Toolkit.CompactPathInfimum

 


theorem exists_crossing_const_lsc (D : LSCMetric) :
    ∃ c₀ : ℝ≥0∞, 0 < c₀ ∧
      ∀ u ∈ LQGMetric.leftSide, ∀ v,
        Metric.infDist v LQGMetric.leftSide = 4⁻¹ → c₀ ≤ D (u, v) := by
  let K : Set ℂ := {v | Metric.infDist v LQGMetric.leftSide = 4⁻¹}
  have hLne : LQGMetric.leftSide.Nonempty :=
    ⟨0, LQGMetric.GM.zero_mem_leftSide⟩
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded
      (isClosed_eq (Metric.continuous_infDist_pt _) continuous_const)
      ((Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 3)).subset fun v hv => ?_)
    obtain ⟨u, hu, hd⟩ := (Metric.infDist_lt_iff hLne).mp
      (show Metric.infDist v LQGMetric.leftSide < 1 by rw [hv]; norm_num)
    have hnorm := LQGMetric.GM.norm_le_two_of_mem_leftSide hu
    rw [mem_closedBall_zero_iff]
    have htri : ‖v‖ ≤ ‖u‖ + dist v u := by
      rw [dist_eq_norm]
      linarith [norm_le_norm_add_norm_sub' v u]
    linarith
  rcases (LQGMetric.leftSide ×ˢ K).eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun u hu v hv => ?_⟩
    have hmem : (u, v) ∈ LQGMetric.leftSide ×ˢ K := ⟨hu, hv⟩
    rw [he] at hmem
    exact absurd hmem (Set.notMem_empty _)
  · obtain ⟨p, hp, hmin⟩ :=
      (D.lowerSemicontinuous.lowerSemicontinuousOn
        (LQGMetric.leftSide ×ˢ K)).exists_isMinOn hne
        (LQGMetric.GM.isCompact_leftSide.prod hKc)
    have hDp : D p ≠ 0 := by
      intro hz
      have heq : p.1 = p.2 := D.isExtMetric.2.1 p.1 p.2 hz
      have hzero : Metric.infDist p.2 LQGMetric.leftSide = 0 := by
        rw [← heq]
        exact Metric.infDist_zero_of_mem hp.1
      have hquarter : Metric.infDist p.2 LQGMetric.leftSide = 4⁻¹ := hp.2
      rw [hzero] at hquarter
      norm_num at hquarter
    exact ⟨D p, pos_iff_ne_zero.mpr hDp,
      fun u hu v hv => hmin ⟨hu, hv⟩⟩

 



theorem compactPathInf_le_mul_of_dist_le
    (D E : LSCMetric) (κ : NNReal) (hκ : 0 < κ)
    (hcomp : ∀ x y : ℂ, E (x, y) ≤ (κ : ℝ≥0∞) * D (x, y))
    (K A B : Set ℂ) :
    compactPathInf E K A B ≤ (κ : ℝ≥0∞) * compactPathInf D K A B := by
  let F : D.Space → E.Space := id
  have hLip : LipschitzWith κ F := by
    intro x y
    change E (x, y) ≤ (κ : ℝ≥0∞) * D (x, y)
    exact hcomp x y
  unfold compactPathInf
  have hκ0 : (κ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hκ.ne'
  have hκTop : (κ : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  simp only [ENNReal.mul_iInf_of_ne hκ0 hκTop]
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b =>
    le_iInf fun hP => le_iInf fun hK => le_iInf fun hA =>
      le_iInf fun hB => ?_
  have hEP : E.IsCurve P a b := by
    refine ⟨hP.1, ?_⟩
    change ContinuousOn (F ∘ (D.pt ∘ P)) (Icc a b)
    exact hLip.continuous.comp_continuousOn hP.2
  have hlen : E.len P a b ≤ (κ : ℝ≥0∞) * D.len P a b := by
    change eVariationOn (F ∘ (D.pt ∘ P)) (Icc a b) ≤
      (κ : ℝ≥0∞) * eVariationOn (D.pt ∘ P) (Icc a b)
    exact hLip.lipschitzOnWith.comp_eVariationOn_le (fun _ _ => mem_univ _)
  exact (iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <|
    iInf_le_of_le hEP <| iInf_le_of_le hK <|
    iInf_le_of_le hA <| iInf_le_of_le hB hlen)

 


theorem weylScale_le_exp_mul_lsc
    {ξ c : ℝ} {f g : C(ℂ, ℝ)} {D : LSCMetric}
    (hfg : ∀ x, ξ * f x ≤ ξ * g x + c) (z w : ℂ) :
    weylScale ξ f D (z, w) ≤
      ENNReal.ofReal (Real.exp c) * weylScale ξ g D (z, w) := by
  have hc0 : ENNReal.ofReal (Real.exp c) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.exp_pos c)).ne'
  have hct : ENNReal.ofReal (Real.exp c) ≠ ∞ := ENNReal.ofReal_ne_top
  simp only [weylScale, ENNReal.mul_iInf_of_ne hc0 hct]
  refine iInf_mono fun P => iInf_mono fun L => iInf_mono fun _ =>
    iInf_mono fun _ => iInf_mono fun _ => iInf_mono fun _ =>
      ?_
  rw [← lintegral_const_mul' _ _ hct]
  refine setLIntegral_mono' measurableSet_Icc fun t _ => ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith [hfg (P t)]))

 



theorem compactPathInf_weyl_le_exp_mul
    (D E F : LSCMetric) (ξ c : ℝ) (f g : C(ℂ, ℝ))
    (hE : ∀ p : ℂ × ℂ, E p = weylScale ξ f D p)
    (hF : ∀ p : ℂ × ℂ, F p = weylScale ξ g D p)
    (hfg : ∀ x, ξ * f x ≤ ξ * g x + c)
    (K A B : Set ℂ) :
    compactPathInf E K A B ≤
      ENNReal.ofReal (Real.exp c) * compactPathInf F K A B := by
  let κ : NNReal := ⟨Real.exp c, (Real.exp_pos c).le⟩
  have hκ : 0 < κ := Real.exp_pos c
  have hκeq : (κ : ℝ≥0∞) = ENNReal.ofReal (Real.exp c) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    rfl
  have hpoint : ∀ x y : ℂ, E (x, y) ≤ (κ : ℝ≥0∞) * F (x, y) := by
    intro x y
    rw [hE (x, y), hF (x, y)]
    rw [hκeq]
    exact weylScale_le_exp_mul_lsc (D := D) hfg x y
  simpa only [hκeq] using
    compactPathInf_le_mul_of_dist_le F E κ hκ hpoint K A B

 


theorem crossingInf_weyl_le
    (D₀ : LSCMetric) (D' : ℝ → LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (f : C(ℂ, ℝ)) {M : ℝ} (hM : ∀ x, |f x| ≤ M)
    (hW : ∀ t p, D' t p = weylScale ξ (t • f) D₀ p)
    (s t : ℝ) :
    crossingInf (D' t) ≤
      ENNReal.ofReal (Real.exp (ξ * |t - s| * M)) * crossingInf (D' s) := by
  have hfx : ∀ x, ξ * (t • f) x ≤ ξ * (s • f) x + ξ * |t - s| * M := by
    intro x
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    have h2 : |t - s| * |f x| ≤ |t - s| * M :=
      mul_le_mul_of_nonneg_left (hM x) (abs_nonneg _)
    have h1 : (t - s) * f x ≤ |t - s| * M :=
      (le_abs_self _).trans (by rw [abs_mul]; exact h2)
    nlinarith [mul_le_mul_of_nonneg_left h1 hξ]
  exact compactPathInf_weyl_le_exp_mul D₀ (D' t) (D' s)
    ξ (ξ * |t - s| * M) (t • f) (s • f)
    (hW t) (hW s) hfx unitSquare LQGMetric.leftSide LQGMetric.rightSide

 




theorem continuousAt_crossingInf_weyl_of_finite
    (D₀ : LSCMetric) (D' : ℝ → LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (f : C(ℂ, ℝ)) {M : ℝ} (hM : ∀ x, |f x| ≤ M)
    (hW : ∀ t p, D' t p = weylScale ξ (t • f) D₀ p)
    (s : ℝ) (hfin : crossingInf (D' s) ≠ ∞) :
    ContinuousAt (fun t => crossingInf (D' t)) s := by
  let θ : ℝ → ℝ≥0∞ := fun t => crossingInf (D' t)
  let k : ℝ → ℝ := fun t => ξ * |t - s| * M
  have hkc : Continuous k := by
    dsimp [k]
    fun_prop
  have hks : k s = 0 := by simp [k]
  have hkp : Tendsto (fun t => ENNReal.ofReal (Real.exp (k t))) (𝓝 s)
      (𝓝 (1 : ℝ≥0∞)) := by
    have hc := ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp hkc)
    simpa [Function.comp_def, hks] using hc.tendsto s
  have hkm : Tendsto (fun t => ENNReal.ofReal (Real.exp (-(k t)))) (𝓝 s)
      (𝓝 (1 : ℝ≥0∞)) := by
    have hc := ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp hkc.neg)
    simpa [Function.comp_def, hks] using hc.tendsto s
  have hup : Tendsto (fun t => ENNReal.ofReal (Real.exp (k t)) * θ s)
      (𝓝 s) (𝓝 (θ s)) := by
    simpa only [one_mul] using ENNReal.Tendsto.mul_const hkp (Or.inr hfin)
  have hlo : Tendsto (fun t => ENNReal.ofReal (Real.exp (-(k t))) * θ s)
      (𝓝 s) (𝓝 (θ s)) := by
    simpa only [one_mul] using ENNReal.Tendsto.mul_const hkm (Or.inr hfin)
  have hle (t : ℝ) : θ t ≤ ENNReal.ofReal (Real.exp (k t)) * θ s :=
    crossingInf_weyl_le D₀ D' ξ hξ f hM hW s t
  have hge (t : ℝ) :
      ENNReal.ofReal (Real.exp (-(k t))) * θ s ≤ θ t := by
    have hrev := crossingInf_weyl_le D₀ D' ξ hξ f hM hW t s
    rw [abs_sub_comm] at hrev
    have hcancel : ENNReal.ofReal (Real.exp (-(k t))) *
        ENNReal.ofReal (Real.exp (k t)) = 1 := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      simp
    calc
      ENNReal.ofReal (Real.exp (-(k t))) * θ s
          ≤ ENNReal.ofReal (Real.exp (-(k t))) *
              (ENNReal.ofReal (Real.exp (k t)) * θ t) := by gcongr
      _ = θ t := by rw [← mul_assoc, hcancel, one_mul]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hup hge hle

theorem continuous_toReal_crossingInf_weyl_of_finite_at_zero
    (D₀ : LSCMetric) (D' : ℝ → LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (f : C(ℂ, ℝ)) {M : ℝ} (hM : ∀ x, |f x| ≤ M)
    (hW : ∀ t p, D' t p = weylScale ξ (t • f) D₀ p)
    (hfin0 : crossingInf (D' 0) ≠ ∞) :
    Continuous (fun t => (crossingInf (D' t)).toReal) := by
  have hfin (t : ℝ) : crossingInf (D' t) ≠ ∞ := by
    have hle := crossingInf_weyl_le D₀ D' ξ hξ f hM hW 0 t
    have htop : ENNReal.ofReal (Real.exp (ξ * |t - 0| * M)) *
        crossingInf (D' 0) ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin0
    exact ne_top_of_le_ne_top htop hle
  apply continuous_iff_continuousAt.mpr
  intro t
  change ContinuousAt (ENNReal.toReal ∘ fun u : ℝ => crossingInf (D' u)) t
  exact (ENNReal.continuousAt_toReal (hfin t)).comp
    (f := fun u : ℝ => crossingInf (D' u))
    (continuousAt_crossingInf_weyl_of_finite D₀ D' ξ hξ f hM hW t (hfin t))

theorem measure_Ioo_pos_of_shift_ennreal
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z : Ω → ℝ≥0∞} {Zq : ℚ → Ω → ℝ≥0∞} {a b : ℝ≥0∞}
    (hpath : ∀ᵐ ω ∂P, Z ω ≤ a → ∃ q : ℚ, 0 < q ∧ Zq q ω ∈ Ioo a b)
    (htr : ∀ q : ℚ, 0 < q →
      0 < P {ω | Zq q ω ∈ Ioo a b} → 0 < P {ω | Z ω ∈ Ioo a b})
    (hpos : 0 < P {ω | Z ω ≤ a}) :
    0 < P {ω | Z ω ∈ Ioo a b} := by
  by_contra hcon
  have hnull : ∀ q : ℚ, P {ω | 0 < q ∧ Zq q ω ∈ Ioo a b} = 0 := by
    intro q
    by_cases hq : 0 < q
    · by_contra hne
      refine hcon (htr q hq (pos_iff_ne_zero.2 fun h0 => hne ?_))
      exact measure_mono_null (fun ω hω => hω.2) h0
    · exact measure_mono_null (fun ω hω => absurd hω.1 hq) (measure_empty (μ := P))
  have hsub : {ω | Z ω ≤ a} ⊆
      {ω | ¬ (Z ω ≤ a → ∃ q : ℚ, 0 < q ∧ Zq q ω ∈ Ioo a b)} ∪
        ⋃ q : ℚ, {ω | 0 < q ∧ Zq q ω ∈ Ioo a b} := by
    intro ω hω
    by_cases h : Z ω ≤ a → ∃ q : ℚ, 0 < q ∧ Zq q ω ∈ Ioo a b
    · obtain ⟨q, hq⟩ := h hω
      exact Or.inr (mem_iUnion.2 ⟨q, hq⟩)
    · exact Or.inl h
  have hzero : P {ω | Z ω ≤ a} = 0 :=
    measure_mono_null hsub (measure_union_null (ae_iff.1 hpath) (measure_iUnion_null hnull))
  exact hpos.ne' hzero

 





theorem le_weylScale_of_exit_of_forget
    {ξ a : ℝ} {c₀ : ℝ≥0∞} {f : C(ℂ, ℝ)} {D : LSCMetric}
    (hforget : Continuous (Inputs.euclideanForget D))
    (hf : ∀ x, Metric.infDist x LQGMetric.leftSide ≤ 4⁻¹ → a ≤ ξ * f x)
    (hc₀ : ∀ u ∈ LQGMetric.leftSide, ∀ v,
      Metric.infDist v LQGMetric.leftSide = 4⁻¹ → c₀ ≤ D (u, v))
    {z w : ℂ} (hz : z ∈ LQGMetric.leftSide)
    (hw : 4⁻¹ ≤ Metric.infDist w LQGMetric.leftSide) :
    ENNReal.ofReal (Real.exp a) * c₀ ≤ weylScale ξ f D (z, w) := by
  unfold weylScale
  refine le_iInf fun P => le_iInf fun L => le_iInf fun hP =>
    le_iInf fun hu => le_iInf fun h0 => le_iInf fun h1 => ?_
  have hPc : ContinuousOn P (Icc 0 L) :=
    hforget.comp_continuousOn hP.2
  let g : ℝ → ℝ := fun s => Metric.infDist (P s) LQGMetric.leftSide
  have hg : ContinuousOn g (Icc 0 L) :=
    (Metric.continuous_infDist_pt LQGMetric.leftSide).comp_continuousOn hPc
  let S : Set ℝ := Icc 0 L ∩ g ⁻¹' Ici 4⁻¹
  have hS : IsClosed S := hg.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hbdd : BddBelow S := ⟨0, fun s hs => hs.1.1⟩
  have hSne : S.Nonempty :=
    ⟨L, ⟨⟨hP.1, le_rfl⟩, by
      simp only [mem_preimage, g, h1]
      exact hw⟩⟩
  let s₀ := sInf S
  have hs₀ : s₀ ∈ S := hS.csInf_mem hSne hbdd
  have hg0 : g 0 = 0 := by
    simp only [g, h0]
    exact Metric.infDist_zero_of_mem hz
  obtain ⟨s₁, hs₁, hgs₁⟩ : ∃ s₁ ∈ Icc 0 s₀, g s₁ = 4⁻¹ :=
    intermediate_value_Icc hs₀.1.1
      (hg.mono (Icc_subset_Icc_right hs₀.1.2))
      ⟨by rw [hg0]; norm_num, hs₀.2⟩
  have hs₁S : s₁ ∈ S := ⟨⟨hs₁.1, hs₁.2.trans hs₀.1.2⟩, hgs₁.ge⟩
  have hs₁eq : s₁ = s₀ := le_antisymm hs₁.2 (csInf_le hbdd hs₁S)
  have hle : ∀ s ∈ Icc 0 s₀, g s ≤ 4⁻¹ := by
    intro s hs
    rcases eq_or_lt_of_le hs.2 with heq | hlt
    · rw [heq, ← hs₁eq, hgs₁]
    · by_contra hcon
      have hsS : s ∈ S :=
        ⟨⟨hs.1, hs.2.trans hs₀.1.2⟩, (not_le.mp hcon).le⟩
      exact absurd (csInf_le hbdd hsS) (not_le.mpr hlt)
  have hd : D (P 0, P s₀) ≤ ENNReal.ofReal s₀ := by
    have hunit := (LQGMetric.MetricGeometry.lipschitzOnWith_of_hasUnitSpeedOn hu)
      ⟨le_rfl, hP.1⟩ hs₀.1
    change D (P 0, P s₀) ≤ (1 : ℝ≥0∞) * edist (0 : ℝ) s₀ at hunit
    simpa only [one_mul, edist_dist,
      Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hs₀.1.1] using hunit
  have hc : c₀ ≤ D (P 0, P s₀) :=
    hc₀ _ (h0 ▸ hz) _ (hs₁eq ▸ hgs₁)
  calc
    ENNReal.ofReal (Real.exp a) * c₀
        ≤ ENNReal.ofReal (Real.exp a) * ENNReal.ofReal s₀ :=
          mul_le_mul_of_nonneg_left (hc.trans hd) zero_le
    _ = ∫⁻ _ in Icc (0 : ℝ) s₀, ENNReal.ofReal (Real.exp a) := by
      have hvol : volume (Icc (0 : ℝ) s₀) = ENNReal.ofReal s₀ := by
        rw [Real.volume_Icc, sub_zero]
      rw [← hvol]
      exact (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ t in Icc (0 : ℝ) s₀,
          ENNReal.ofReal (Real.exp (ξ * f (P t))) :=
      setLIntegral_mono' measurableSet_Icc fun t ht =>
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hf _ (hle t ht)))
    _ ≤ ∫⁻ t in Icc (0 : ℝ) L,
          ENNReal.ofReal (Real.exp (ξ * f (P t))) :=
      lintegral_mono_set (Icc_subset_Icc_right hs₀.1.2)

 


theorem exp_mul_le_crossingInf_weyl_of_forget
    (D E : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (hforget : Continuous (Inputs.euclideanForget D))
    (f : C(ℂ, ℝ))
    (hf1 : ∀ x, Metric.infDist x LQGMetric.leftSide ≤ 4⁻¹ → 1 ≤ f x)
    (t : ℝ) (ht : 0 ≤ t)
    (hW : ∀ p, E p = weylScale ξ (t • f) D p)
    (c₀ : ℝ≥0∞)
    (hc₀ : ∀ u ∈ LQGMetric.leftSide, ∀ v,
      Metric.infDist v LQGMetric.leftSide = 4⁻¹ → c₀ ≤ D (u, v)) :
    ENNReal.ofReal (Real.exp (ξ * t)) * c₀ ≤ crossingInf E := by
  unfold crossingInf compactPathInf
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b =>
    le_iInf fun hP => le_iInf fun hK => le_iInf fun hA =>
      le_iInf fun hB => ?_
  have hbar : ∀ x, Metric.infDist x LQGMetric.leftSide ≤ 4⁻¹ →
      ξ * t ≤ ξ * (t • f) x := by
    intro x hx
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    nlinarith [hf1 x hx, mul_nonneg hξ ht]
  have hdist := le_weylScale_of_exit_of_forget
    (ξ := ξ) (a := ξ * t) (c₀ := c₀) (f := t • f) (D := D)
    hforget hbar hc₀ hA
    (LQGMetric.GM.quarter_le_infDist_of_mem_rightSide hB)
  rw [← hW] at hdist
  exact hdist.trans (E.edist_le_len P hP.1)

 



theorem exists_rat_crossingInf_weyl_mem_of_forget
    (D₀ : LSCMetric) (D' : ℝ → LSCMetric)
    (ξ : ℝ) (hξ : 0 < ξ)
    (hforget : Continuous (Inputs.euclideanForget D₀))
    (f : C(ℂ, ℝ))
    (hf1 : ∀ x, Metric.infDist x LQGMetric.leftSide ≤ 4⁻¹ → 1 ≤ f x)
    {M : ℝ} (hM : ∀ x, |f x| ≤ M)
    (hW : ∀ t p, D' t p = weylScale ξ (t • f) D₀ p)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (h0 : crossingInf (D' 0) ≤ ENNReal.ofReal a) :
    ∃ q : ℚ, 0 < q ∧ crossingInf (D' q) ∈
      Ioo (ENNReal.ofReal a) (ENNReal.ofReal b) := by
  let θ : ℝ → ℝ := fun t => (crossingInf (D' t)).toReal
  have hfin0 : crossingInf (D' 0) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top h0
  have hθ : Continuous θ :=
    continuous_toReal_crossingInf_weyl_of_finite_at_zero
      D₀ D' ξ hξ.le f hM hW hfin0
  have hfin (t : ℝ) : crossingInf (D' t) ≠ ∞ := by
    have hle := crossingInf_weyl_le D₀ D' ξ hξ.le f hM hW 0 t
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin0) hle
  obtain ⟨c₀, hc₀, hc⟩ := exists_crossing_const_lsc D₀
  have hc₀fin : c₀ ≠ ∞ := by
    have hlow := exp_mul_le_crossingInf_weyl_of_forget
      D₀ (D' 0) ξ hξ.le hforget f hf1 0 le_rfl (hW 0)
      c₀ hc
    simpa using ne_top_of_le_ne_top hfin0 (by simpa using hlow : c₀ ≤ crossingInf (D' 0))
  have hc₀real : 0 < c₀.toReal := ENNReal.toReal_pos hc₀.ne' hc₀fin
  have hlarge (t : ℝ) (ht : 0 ≤ t) :
      Real.exp (ξ * t) * c₀.toReal ≤ θ t := by
    have hlow := exp_mul_le_crossingInf_weyl_of_forget
      D₀ (D' t) ξ hξ.le hforget f hf1 t ht (hW t) c₀ hc
    have hleftfin : ENNReal.ofReal (Real.exp (ξ * t)) * c₀ ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hc₀fin
    have hreal := (ENNReal.toReal_le_toReal hleftfin (hfin t)).mpr hlow
    simpa only [θ, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_pos _).le] using hreal
  have h0real : θ 0 ≤ a := by
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h0
    simpa only [θ, ENNReal.toReal_ofReal ha] using hreal
  obtain ⟨T, hT0, hTb⟩ : ∃ T : ℝ, 0 < T ∧ b < θ T := by
    have htend : Tendsto (fun t : ℝ => Real.exp (ξ * t) * c₀.toReal)
        atTop atTop :=
      (Real.tendsto_exp_atTop.comp
        (tendsto_id.const_mul_atTop hξ)).atTop_mul_const hc₀real
    obtain ⟨T, hT⟩ :=
      ((htend.eventually_gt_atTop b).and (eventually_gt_atTop 0)).exists
    exact ⟨T, hT.2, hT.1.trans_le (hlarge T hT.2.le)⟩
  obtain ⟨s, hs, hθs⟩ := intermediate_value_Icc hT0.le hθ.continuousOn
    (show (a + b) / 2 ∈ Icc (θ 0) (θ T) from ⟨by linarith, by linarith⟩)
  have hs0 : s ≠ 0 := fun heq => by rw [heq] at hθs; linarith
  have hsT : s ≠ T := fun heq => by rw [heq] at hθs; linarith
  have hU : IsOpen (Ioo 0 T ∩ θ ⁻¹' Ioo a b) :=
    isOpen_Ioo.inter (isOpen_Ioo.preimage hθ)
  have hsU : s ∈ Ioo 0 T ∩ θ ⁻¹' Ioo a b :=
    ⟨⟨lt_of_le_of_ne hs.1 (Ne.symm hs0),
      lt_of_le_of_ne hs.2 hsT⟩,
      by simp only [mem_preimage, hθs, mem_Ioo]; constructor <;> linarith⟩
  obtain ⟨q, hq1, hq2⟩ := Rat.denseRange_cast.exists_mem_open hU ⟨s, hsU⟩
  refine ⟨q, by exact_mod_cast hq1.1, ?_⟩
  have hqfin : crossingInf (D' q) ≠ ∞ := hfin q
  have hqeq : ENNReal.ofReal (θ q) = crossingInf (D' q) := by
    exact ENNReal.ofReal_toReal hqfin
  change a < θ q ∧ θ q < b at hq2
  rw [← hqeq]
  exact ⟨(ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < θ q)).mpr hq2.1,
    (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < b)).mpr hq2.2⟩

 




theorem noGap_crossingInf_of_ae_euclideanForget
    (ξ : Set.Ioi (0 : ℝ))
    (D : LQGMetric.DistC → LSCMetric)
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hweak : B2.Iface.IsPfeWeakMetric ξ D c)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (hforget : ∀ᵐ ω ∂P, Continuous (Inputs.euclideanForget (D (h ω))))
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hpos : 0 < P {ω | crossingInf (D (h ω)) ≤ ENNReal.ofReal a}) :
    0 < P {ω | crossingInf (D (h ω)) ∈
      Ioo (ENNReal.ofReal a) (ENNReal.ofReal b)} := by
  let Z : Ω → ℝ≥0∞ := fun ω => crossingInf (D (h ω))
  have hDm : Measurable (fun g : LQGMetric.DistC => crossingInf (D g)) :=
    measurable_crossingInf.comp hweak.1
  obtain ⟨f₀, hf1, hf0⟩ := LQGMetric.GM.exists_noGap_test
  obtain ⟨M, hM⟩ : ∃ M, ∀ x, |LQGMetric.testCont f₀ x| ≤ M := by
    obtain ⟨C, hC⟩ := (LQGMetric.testCont f₀).continuous.bounded_above_of_compact_support
      f₀.hasCompactSupport
    exact ⟨C, fun x => by simpa [Real.norm_eq_abs] using hC x⟩
  have hold : LQGMetric.IsNormalizedWPGFF h P :=
    Uniqueness.Toolkit.AnnulusIteration.normalized_old_of_new hh
  have hcont : LQGMetric.IsGFFPlusCont h P :=
    LQGMetric.GM.isGFFPlusCont_of_normalized hold
  obtain ⟨_, _, _, hweyl, _, _, _⟩ := hweak
  have hW := hweyl P h hcont
  refine measure_Ioo_pos_of_shift_ennreal
    (Z := Z)
    (Zq := fun (q : ℚ) ω => crossingInf
      (D (LQGMetric.addFun (h ω) ((q : ℝ) • LQGMetric.testCont f₀))))
    ?_ ?_ hpos
  · filter_upwards [hW, hforget] with ω hw hfg hZ
    change Continuous (Inputs.euclideanForget (D (h ω))) at hfg
    have hweq (t : ℝ) (p : ℂ × ℂ) :
        D (LQGMetric.addFun (h ω) (t • LQGMetric.testCont f₀)) p =
          weylScale (ξ : ℝ) (t • LQGMetric.testCont f₀) (D (h ω)) p := by
      exact congrFun (hw (t • LQGMetric.testCont f₀)) p |>.symm
    exact exists_rat_crossingInf_weyl_mem_of_forget
      (D (h ω))
      (fun t => D (LQGMetric.addFun (h ω) (t • LQGMetric.testCont f₀)))
      (ξ : ℝ) ξ.property hfg (LQGMetric.testCont f₀) hf1 hM
      hweq ha hab (by simpa [LQGMetric.GM.addFun_zero_eq] using hZ)
  · intro q _ hq
    by_contra hcon
    have h0 : P (h ⁻¹' {g | crossingInf (D g) ∈
        Ioo (ENNReal.ofReal a) (ENNReal.ofReal b)}) = 0 :=
      nonpos_iff_eq_zero.mp (not_lt.mp hcon)
    have hφ : Real.circleAverage
        (LQGMetric.testCont ((q : ℝ) • f₀)) 0 1 = 0 := by
      have he : (LQGMetric.testCont ((q : ℝ) • f₀) : ℂ → ℝ) =
          fun x => (q : ℝ) • LQGMetric.testCont f₀ x := rfl
      rw [he, Real.circleAverage_fun_smul, hf0, smul_zero]
    have hnull := LQGMetric.GM.measure_addFun_preimage_eq_zero
      hold hφ (hDm measurableSet_Ioo) h0
    have he : LQGMetric.testCont ((q : ℝ) • f₀) =
        (q : ℝ) • LQGMetric.testCont f₀ := rfl
    rw [he] at hnull
    exact hq.ne' hnull

 

theorem noGap_crossingInf_finite_of_ae_euclideanForget
    (ξ : Set.Ioi (0 : ℝ))
    (D : LQGMetric.DistC → LSCMetric)
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hweak : B2.Iface.IsPfeWeakMetric ξ D c)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (hforget : ∀ᵐ ω ∂P, Continuous (Inputs.euclideanForget (D (h ω))))
    (x y : ℝ≥0∞) (hxy : x < y) (hyfin : y ≠ ∞)
    (hpos : 0 < P {ω | crossingInf (D (h ω)) ≤ x}) :
    0 < P {ω | x < crossingInf (D (h ω)) ∧ crossingInf (D (h ω)) < y} := by
  have hxfin : x ≠ ∞ := ne_top_of_lt hxy
  have ha : 0 ≤ x.toReal := ENNReal.toReal_nonneg
  have hab : x.toReal < y.toReal :=
    (ENNReal.toReal_lt_toReal hxfin hyfin).mpr hxy
  have hxeq : ENNReal.ofReal x.toReal = x := ENNReal.ofReal_toReal hxfin
  have hyeq : ENNReal.ofReal y.toReal = y := ENNReal.ofReal_toReal hyfin
  have hng := noGap_crossingInf_of_ae_euclideanForget
    ξ D c hweak P h hh hforget x.toReal y.toReal ha hab
  rw [hxeq, hyeq] at hng
  exact hng hpos

end SupercriticalLQGUniqueness.B2.Median
