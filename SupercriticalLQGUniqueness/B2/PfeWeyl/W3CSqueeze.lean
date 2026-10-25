import SupercriticalLQGUniqueness.B2.PfeWeyl.W3Sample
import SupercriticalLQGUniqueness.B2.PfeWeyl.W1Crossing
import SupercriticalLQGUniqueness.B2.PfeWeyl.W2Chain
import SupercriticalLQGUniqueness.B2.LscTop.Dilate
import SupercriticalLQGUniqueness.B2.PfeAxioms.FiniteConstantScale

 































set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 

 

theorem weylScale_le_exp_mul_of_le {ξ c : ℝ} {f g : C(ℂ, ℝ)} {D : LSCMetric}
    (hfg : ∀ x, ξ * f x ≤ ξ * g x + c) (p : ℂ × ℂ) :
    weylScale ξ f D p ≤ ENNReal.ofReal (Real.exp c) * weylScale ξ g D p := by
  have hc0 : ENNReal.ofReal (Real.exp c) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.exp_pos c)).ne'
  have hct : ENNReal.ofReal (Real.exp c) ≠ ∞ := ENNReal.ofReal_ne_top
  simp only [weylScale, ENNReal.mul_iInf_of_ne hc0 hct]
  refine iInf_mono fun P => iInf_mono fun L => iInf_mono fun _ =>
    iInf_mono fun _ => iInf_mono fun _ => iInf_mono fun _ => ?_
  rw [← lintegral_const_mul' _ _ hct]
  refine setLIntegral_mono' measurableSet_Icc fun t _ => ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith [hfg (P t)]))

 
theorem weylScale_mono_weight {ξ : ℝ} (hξ : 0 ≤ ξ) {f g : C(ℂ, ℝ)} {D : LSCMetric}
    (hfg : ∀ x, f x ≤ g x) (p : ℂ × ℂ) : weylScale ξ f D p ≤ weylScale ξ g D p := by
  have h := weylScale_le_exp_mul_of_le (ξ := ξ) (c := 0) (f := f) (g := g) (D := D)
    (fun x => by nlinarith [hfg x]) p
  simpa using h

 
theorem weylScale_add_const (ξ c : ℝ) (f : C(ℂ, ℝ)) (D : LSCMetric) (p : ℂ × ℂ) :
    weylScale ξ (f + ContinuousMap.const ℂ c) D p =
      ENNReal.ofReal (Real.exp (ξ * c)) * weylScale ξ f D p := by
  apply le_antisymm
  · exact weylScale_le_exp_mul_of_le (fun x => by simp [mul_add]) p
  · have h := weylScale_le_exp_mul_of_le (ξ := ξ) (c := -(ξ * c)) (f := f)
      (g := f + ContinuousMap.const ℂ c) (D := D) (fun x => by simp [mul_add]) p
    have hpos : ENNReal.ofReal (Real.exp (ξ * c)) * ENNReal.ofReal (Real.exp (-(ξ * c))) = 1 := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_neg_cancel,
        Real.exp_zero, ENNReal.ofReal_one]
    calc ENNReal.ofReal (Real.exp (ξ * c)) * weylScale ξ f D p
        ≤ ENNReal.ofReal (Real.exp (ξ * c)) * (ENNReal.ofReal (Real.exp (-(ξ * c))) *
            weylScale ξ (f + ContinuousMap.const ℂ c) D p) := mul_le_mul' le_rfl h
      _ = weylScale ξ (f + ContinuousMap.const ℂ c) D p := by
          rw [← mul_assoc, hpos, one_mul]

 
theorem mollCont_apply_eq_integral {ε : ℝ} (hε : ε ≠ 0) (f : C(ℂ, ℝ)) (M : ℝ)
    (hM : ∀ z, |f z| ≤ M) (z : ℂ) :
    LQGMetric.LFPP.mollCont ε hε f M hM z =
      ∫ w, f w * LQGMetric.heatKernel (ε ^ 2 / 2) z w :=
  LQGMetric.heatMollify_ofCont f M hM ε hε z

theorem integrable_mul_heatKernel_of_bdd (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ z, |f z| ≤ M)
    {s : ℝ} (hs : 0 < s) (z : ℂ) :
    Integrable (fun w => f w * LQGMetric.heatKernel s z w) := by
  simpa only [mul_comm] using LQGMetric.integrable_heatKernel_mul_of_bdd f M hM s hs z

 
theorem mollCont_mono {ε : ℝ} (hε : ε ≠ 0) {f g : C(ℂ, ℝ)} {M M' : ℝ}
    (hM : ∀ z, |f z| ≤ M) (hM' : ∀ z, |g z| ≤ M') (hfg : ∀ z, f z ≤ g z) (z : ℂ) :
    LQGMetric.LFPP.mollCont ε hε f M hM z ≤ LQGMetric.LFPP.mollCont ε hε g M' hM' z := by
  have hs : 0 < ε ^ 2 / 2 := by positivity
  rw [mollCont_apply_eq_integral, mollCont_apply_eq_integral]
  exact integral_mono (integrable_mul_heatKernel_of_bdd f M hM hs z)
    (integrable_mul_heatKernel_of_bdd g M' hM' hs z)
    fun w => mul_le_mul_of_nonneg_right (hfg w) (LQGMetric.heatKernel_nonneg _ hs.le z w)

 
theorem mollCont_add_const {ε : ℝ} (hε : ε ≠ 0) (f : C(ℂ, ℝ)) (c : ℝ) {M M' : ℝ}
    (hM : ∀ z, |f z| ≤ M) (hM' : ∀ z, |(f + ContinuousMap.const ℂ c) z| ≤ M') :
    LQGMetric.LFPP.mollCont ε hε (f + ContinuousMap.const ℂ c) M' hM' =
      LQGMetric.LFPP.mollCont ε hε f M hM + ContinuousMap.const ℂ c := by
  have hs : 0 < ε ^ 2 / 2 := by positivity
  ext z
  rw [ContinuousMap.add_apply, mollCont_apply_eq_integral, mollCont_apply_eq_integral]
  simp only [ContinuousMap.add_apply, ContinuousMap.const_apply, add_mul]
  rw [integral_add (integrable_mul_heatKernel_of_bdd f M hM hs z)
    ((LQGMetric.integrable_heatKernel _ hs z).const_mul c), integral_const_mul,
    LQGMetric.integral_heatKernel _ hs z, mul_one]

 
theorem normalizedLFPPMetric_add_mollCont_mono {ξ : ℝ} (hξ : 0 ≤ ξ) (a : Set.Ioi (0 : ℝ))
    (φ : C(ℂ, ℝ)) {ε : ℝ} (hε : ε ≠ 0) {f g : C(ℂ, ℝ)} {M M' : ℝ}
    (hM : ∀ z, |f z| ≤ M) (hM' : ∀ z, |g z| ≤ M') (hfg : ∀ z, f z ≤ g z) (p : ℂ × ℂ) :
    normalizedLFPPMetric ξ a (φ + LQGMetric.LFPP.mollCont ε hε f M hM) p ≤
      normalizedLFPPMetric ξ a (φ + LQGMetric.LFPP.mollCont ε hε g M' hM') p := by
  rw [normalizedLFPPMetric_add_eq_weylScale, normalizedLFPPMetric_add_eq_weylScale]
  exact weylScale_mono_weight hξ (mollCont_mono hε hM hM' hfg) p

 
theorem weyl_add_const_of_tendsto (ξ : ℝ) (a : ℕ → Set.Ioi (0 : ℝ)) (φ : ℕ → C(ℂ, ℝ))
    (D : LSCMetric) (ε : ℕ → ℝ) (hε : ∀ n, ε n ≠ 0) (f : C(ℂ, ℝ)) (M : ℝ)
    (hM : ∀ z, |f z| ≤ M) (E : LSCMetric) (hE : ∀ p, E p = weylScale ξ f D p)
    (hconv : Tendsto (fun n => normalizedLFPPMetric ξ (a n)
      (φ n + LQGMetric.LFPP.mollCont (ε n) (hε n) f M hM)) atTop (𝓝 E))
    (c : ℝ) (M' : ℝ) (hM' : ∀ z, |(f + ContinuousMap.const ℂ c) z| ≤ M') :
    ∃ E' : LSCMetric, (∀ p, E' p = weylScale ξ (f + ContinuousMap.const ℂ c) D p) ∧
      Tendsto (fun n => normalizedLFPPMetric ξ (a n)
        (φ n + LQGMetric.LFPP.mollCont (ε n) (hε n) (f + ContinuousMap.const ℂ c) M' hM'))
        atTop (𝓝 E') := by
  let k : Set.Ioi (0 : ℝ) := ⟨Real.exp (ξ * c), Real.exp_pos _⟩
  refine ⟨B2.LscTop.smulMetric k E, fun p => ?_, ?_⟩
  · rw [B2.LscTop.smulMetric_apply, hE p, weylScale_add_const]
  · have heq : (fun n => normalizedLFPPMetric ξ (a n)
        (φ n + LQGMetric.LFPP.mollCont (ε n) (hε n) (f + ContinuousMap.const ℂ c) M' hM')) =
        fun n => B2.LscTop.smulMetric k (normalizedLFPPMetric ξ (a n)
          (φ n + LQGMetric.LFPP.mollCont (ε n) (hε n) f M hM)) := by
      funext n
      apply LSCMetric.ext
      intro p
      rw [B2.LscTop.smulMetric_apply]
      refine PfeAxioms.normalizedLFPPMetric_add_const ξ (a n) _ _ c (fun u => ?_) p
      rw [mollCont_add_const (hε n) f c hM hM']
      simp only [ContinuousMap.add_apply, ContinuousMap.const_apply]
      ring
    rw [heq]
    exact B2.LscTop.tendsto_smulMetric tendsto_const_nhds hconv

 

 
theorem weylScale_le_integral {ξ : ℝ} {f : C(ℂ, ℝ)} {D : LSCMetric} {P : ℝ → ℂ} {L : ℝ}
    (hc : D.IsCurve P 0 L) (hu : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L)) {p : ℂ × ℂ}
    (h0 : P 0 = p.1) (hL : P L = p.2) :
    weylScale ξ f D p ≤ ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t))) :=
  iInf_le_of_le P <| iInf_le_of_le L <| iInf_le_of_le hc <| iInf_le_of_le hu <|
    iInf_le_of_le h0 <| iInf_le_of_le hL le_rfl

 
theorem integral_exp_le_exp_mul {ξ c : ℝ} {f g : C(ℂ, ℝ)} {P : ℝ → ℂ} {L : ℝ}
    (hfg : ∀ t ∈ Icc 0 L, ξ * f (P t) ≤ ξ * g (P t) + c) :
    ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t))) ≤
      ENNReal.ofReal (Real.exp c) * ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * g (P t))) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith [hfg t ht]))

 
theorem len_eq_of_hasUnitSpeedOn {D : LSCMetric} {P : ℝ → ℂ} {L : ℝ} (hL : 0 ≤ L)
    (hu : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L)) : D.len P 0 L = ENNReal.ofReal L := by
  have h := hu ⟨le_rfl, hL⟩ ⟨hL, le_rfl⟩
  rw [Set.inter_self, sub_zero] at h
  simp only [NNReal.coe_one, one_mul] at h
  exact h

 


theorem limsup_weylScale_le_of_upper {ξ : ℝ} (hξ : 0 ≤ ξ) {D : LSCMetric}
    (hforget : Continuous (euclidForget D)) (f : C(ℂ, ℝ)) (g : ℕ → C(ℂ, ℝ))
    (η : ℕ → ℝ) (hη : Tendsto η atTop (𝓝 0))
    (hup : ∀ j : ℕ, ∀ z ∈ Metric.closedBall (0 : ℂ) j, g j z ≤ f z + η j) (p : ℂ × ℂ) :
    limsup (fun j => weylScale ξ (g j) D p) atTop ≤ weylScale ξ f D p := by
  refine le_of_forall_gt_imp_ge_of_dense fun T hT => le_of_lt ?_
  obtain ⟨T₁, hT₁, hT₁T⟩ := exists_between hT
  have hT₁top : T₁ ≠ ⊤ := ne_top_of_lt hT₁T
  obtain ⟨P, L, hc, hu, h0, hL, hint⟩ : ∃ (P : ℝ → ℂ) (L : ℝ) (_ : D.IsCurve P 0 L)
      (_ : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L)) (_ : P 0 = p.1) (_ : P L = p.2),
      ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t))) < T₁ := by
    have h := hT₁
    simp only [weylScale, iInf_lt_iff] at h
    exact h
  have hPc : ContinuousOn P (Icc 0 L) := continuousOn_of_isCurve_of_forget D hforget hc
  obtain ⟨R, hR⟩ := ((isCompact_Icc.image_of_continuousOn hPc).isBounded).subset_closedBall 0
  obtain ⟨N, hN⟩ := exists_nat_ge R
  have hbound : ∀ᶠ j : ℕ in atTop, weylScale ξ (g j) D p ≤
      ENNReal.ofReal (Real.exp (ξ * η j)) * T₁ := by
    filter_upwards [eventually_ge_atTop N] with j hj
    have htr : ∀ t ∈ Icc 0 L, ξ * g j (P t) ≤ ξ * f (P t) + ξ * η j := by
      intro t ht
      have hmem : P t ∈ Metric.closedBall (0 : ℂ) j :=
        Metric.closedBall_subset_closedBall (hN.trans (by exact_mod_cast hj)) (hR ⟨t, ht, rfl⟩)
      have := hup j (P t) hmem
      nlinarith
    calc weylScale ξ (g j) D p
        ≤ ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * g j (P t))) :=
          weylScale_le_integral hc hu h0 hL
      _ ≤ ENNReal.ofReal (Real.exp (ξ * η j)) *
          ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t))) := integral_exp_le_exp_mul htr
      _ ≤ ENNReal.ofReal (Real.exp (ξ * η j)) * T₁ := mul_le_mul' le_rfl hint.le
  have hlim : Tendsto (fun j => ENNReal.ofReal (Real.exp (ξ * η j)) * T₁) atTop (𝓝 T₁) := by
    have h1 : Tendsto (fun j => ENNReal.ofReal (Real.exp (ξ * η j))) atTop (𝓝 1) := by
      have h2 := hη.const_mul ξ
      rw [mul_zero] at h2
      have := (Real.continuous_exp.tendsto 0).comp h2
      simp only [Real.exp_zero] at this
      simpa using ENNReal.tendsto_ofReal this
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hT₁top)
  calc limsup (fun j => weylScale ξ (g j) D p) atTop
      ≤ limsup (fun j => ENNReal.ofReal (Real.exp (ξ * η j)) * T₁) atTop :=
        limsup_le_limsup hbound (by isBoundedDefault) (by isBoundedDefault)
    _ = T₁ := hlim.limsup_eq
    _ < T := hT₁T

 



theorem weylScale_le_liminf_of_lower {ξ : ℝ} (hξ : 0 ≤ ξ) {D : LSCMetric}
    (hforget : Continuous (euclidForget D)) (hacross : AcrossUnbounded D)
    (f : C(ℂ, ℝ)) (g : ℕ → C(ℂ, ℝ)) (η : ℕ → ℝ) (hη : Tendsto η atTop (𝓝 0)) (B : ℝ)
    (hB : ∀ j z, -B ≤ g j z)
    (hlow : ∀ j : ℕ, ∀ z ∈ Metric.closedBall (0 : ℂ) j, f z - η j ≤ g j z) (p : ℂ × ℂ) :
    weylScale ξ f D p ≤ liminf (fun j => weylScale ξ (g j) D p) atTop := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨T, hT1, hT2⟩ := exists_between hcon
  have hTtop : T ≠ ⊤ := ne_top_of_lt hT2
  have hfreq : ∃ᶠ j in atTop, weylScale ξ (g j) D p < T :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) hT1
  
  have hkey : ∀ δ : ℝ, 0 < δ → weylScale ξ f D p ≤ ENNReal.ofReal (Real.exp δ) * T := by
    intro δ hδ
    set Λ : ℝ≥0∞ := ENNReal.ofReal (Real.exp (ξ * B)) * T with hΛ
    have hΛtop : Λ ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hTtop
    obtain ⟨k, hk⟩ := exists_nat_ge ‖p.1‖
    obtain ⟨R, hR⟩ := hacross k Λ hΛtop
    obtain ⟨N, hN⟩ := exists_nat_ge (R : ℝ)
    have hξη : ∀ᶠ j in atTop, ξ * η j ≤ δ := by
      have := hη.const_mul ξ
      rw [mul_zero] at this
      exact this.eventually (ge_mem_nhds hδ)
    obtain ⟨j, hjT, hjN, hjδ⟩ :=
      (hfreq.and_eventually ((eventually_ge_atTop N).and hξη)).exists
    obtain ⟨P, L, hc, hu, h0, hL, hint⟩ : ∃ (P : ℝ → ℂ) (L : ℝ) (_ : D.IsCurve P 0 L)
        (_ : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L)) (_ : P 0 = p.1) (_ : P L = p.2),
        ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * g j (P t))) < T := by
      have h := hjT
      simp only [weylScale, iInf_lt_iff] at h
      exact h
    have hL0 : 0 ≤ L := hc.1
    
    have hlenT : ENNReal.ofReal (Real.exp (-(ξ * B))) * ENNReal.ofReal L < T := by
      refine lt_of_le_of_lt ?_ hint
      calc ENNReal.ofReal (Real.exp (-(ξ * B))) * ENNReal.ofReal L
          = ∫⁻ _ in Icc (0 : ℝ) L, ENNReal.ofReal (Real.exp (-(ξ * B))) := by
            rw [setLIntegral_const, Real.volume_Icc, sub_zero, mul_comm]
        _ ≤ ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * g j (P t))) := by
            refine setLIntegral_mono' measurableSet_Icc fun t _ => ?_
            refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
            nlinarith [hB j (P t)]
    have hlen : D.len P 0 L < Λ := by
      rw [len_eq_of_hasUnitSpeedOn hL0 hu]
      have hprod : ENNReal.ofReal (Real.exp (ξ * B)) *
          ENNReal.ofReal (Real.exp (-(ξ * B))) = 1 := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_neg_cancel,
          Real.exp_zero, ENNReal.ofReal_one]
      calc ENNReal.ofReal L
          = ENNReal.ofReal (Real.exp (ξ * B)) *
            (ENNReal.ofReal (Real.exp (-(ξ * B))) * ENNReal.ofReal L) := by
            rw [← mul_assoc, hprod, one_mul]
        _ = (ENNReal.ofReal (Real.exp (-(ξ * B))) * ENNReal.ofReal L) *
            ENNReal.ofReal (Real.exp (ξ * B)) := mul_comm _ _
        _ < T * ENNReal.ofReal (Real.exp (ξ * B)) :=
            ENNReal.mul_lt_mul_left (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
              ENNReal.ofReal_ne_top hlenT
        _ = Λ := by rw [hΛ, mul_comm]
    have hPc : ContinuousOn P (Icc 0 L) := continuousOn_of_isCurve_of_forget D hforget hc
    have hin := curve_mem_ball_of_len_lt_acrossDist D
      (outerAnnulus ((k : ℝ) + 1) (Nat.cast_add_one_pos k) R) hPc
      (by
        change dist (P 0) 0 ≤ 2 * ((k : ℝ) + 1)
        rw [h0, dist_zero_right]
        linarith)
      (hlen.trans hR)
    have htr : ∀ t ∈ Icc 0 L, ξ * f (P t) ≤ ξ * g j (P t) + δ := by
      intro t ht
      have hball : P t ∈ Metric.ball (0 : ℂ) R := hin t ht
      have hmem : P t ∈ Metric.closedBall (0 : ℂ) j := by
        rw [Metric.mem_closedBall]
        rw [Metric.mem_ball] at hball
        have : (R : ℝ) ≤ j := hN.trans (by exact_mod_cast hjN)
        linarith
      have := hlow j (P t) hmem
      nlinarith
    calc weylScale ξ f D p
        ≤ ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t))) :=
          weylScale_le_integral hc hu h0 hL
      _ ≤ ENNReal.ofReal (Real.exp δ) *
          ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * g j (P t))) :=
          integral_exp_le_exp_mul htr
      _ ≤ ENNReal.ofReal (Real.exp δ) * T := mul_le_mul' le_rfl hint.le
  have hlim : Tendsto (fun k : ℕ => ENNReal.ofReal (Real.exp (1 / ((k : ℝ) + 1))) * T)
      atTop (𝓝 T) := by
    have h1 : Tendsto (fun k : ℕ => ENNReal.ofReal (Real.exp (1 / ((k : ℝ) + 1)))) atTop
        (𝓝 1) := by
      have := (Real.continuous_exp.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
      simp only [Real.exp_zero] at this
      simpa using ENNReal.tendsto_ofReal this
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hTtop)
  have hle : weylScale ξ f D p ≤ T :=
    ge_of_tendsto' hlim fun k => hkey _ (by positivity)
  exact absurd (lt_of_lt_of_le hT2 hle) (lt_irrefl _)

 

 


theorem weyl_all_bounded_of_squeeze (ξ : ℝ) (hξ : 0 ≤ ξ) (a : ℕ → Set.Ioi (0 : ℝ))
    (φ : ℕ → C(ℂ, ℝ)) (D : LSCMetric) (hforget : Continuous (euclidForget D))
    (hacross : AcrossUnbounded D) (ε : ℕ → ℝ) (hε : ∀ n, ε n ≠ 0) (S : Set C(ℂ, ℝ))
    (hS : ∀ g ∈ S, ∀ (M : ℝ) (hM : ∀ z, |g z| ≤ M), ∃ E : LSCMetric,
      (∀ p, E p = weylScale ξ g D p) ∧
      Tendsto (fun n => normalizedLFPPMetric ξ (a n)
        (φ n + LQGMetric.LFPP.mollCont (ε n) (hε n) g M hM)) atTop (𝓝 E))
    (happrox : ∀ (f : C(ℂ, ℝ)) (M : ℝ), (∀ z, |f z| ≤ M) → ∀ j : ℕ,
      ∃ gp ∈ S, ∃ gm ∈ S, (∃ Mp : ℝ, ∀ z, |gp z| ≤ Mp) ∧ (∃ Mm : ℝ, ∀ z, |gm z| ≤ Mm) ∧
        (∀ z, f z ≤ gp z) ∧ (∀ z, gm z ≤ f z) ∧
        (∀ z ∈ Metric.closedBall (0 : ℂ) j, gp z ≤ f z + 1 / ((j : ℝ) + 1)) ∧
        (∀ z ∈ Metric.closedBall (0 : ℂ) j, f z - 1 / ((j : ℝ) + 1) ≤ gm z) ∧
        (∀ z, -(3 * M + 3) ≤ gm z))
    (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ z, |f z| ≤ M) :
    ∃ E : LSCMetric, (∀ p, E p = weylScale ξ f D p) ∧
      Tendsto (fun n => normalizedLFPPMetric ξ (a n)
        (φ n + LQGMetric.LFPP.mollCont (ε n) (hε n) f M hM)) atTop (𝓝 E) := by
  choose gp hgpS gm hgmS hMp hMm hfgp hgmf hup hlow hBm using happrox f M hM
  choose Mp hMp using hMp
  choose Mm hMm using hMm
  choose Ep hEp hEpc using fun j => hS (gp j) (hgpS j) (Mp j) (hMp j)
  choose Em hEm hEmc using fun j => hS (gm j) (hgmS j) (Mm j) (hMm j)
  set W : ℂ × ℂ → ℝ≥0∞ := fun p => weylScale ξ f D p with hWdef
  set G : ℕ → LSCMetric := fun n => normalizedLFPPMetric ξ (a n)
    (φ n + LQGMetric.LFPP.mollCont (ε n) (hε n) f M hM) with hGdef
  have hη : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hupper : ∀ p, limsup (fun j => Ep j p) atTop ≤ W p := by
    intro p
    simp only [hEp]
    exact limsup_weylScale_le_of_upper hξ hforget f gp _ hη hup p
  have hlower : ∀ p, W p ≤ liminf (fun j => Em j p) atTop := by
    intro p
    simp only [hEm]
    exact weylScale_le_liminf_of_lower hξ hforget hacross f gm _ hη (3 * M + 3) hBm hlow p
  have hEmle : ∀ j p, Em j p ≤ W p := fun j p => by
    rw [hEm]
    exact weylScale_mono_weight hξ (hgmf j) p
  have hWsup : ∀ p, W p = ⨆ j, Em j p := fun p =>
    le_antisymm ((hlower p).trans ((liminf_le_limsup (by isBoundedDefault)
      (by isBoundedDefault)).trans limsup_le_iSup)) (iSup_le fun j => hEmle j p)
  have hlsc : LowerSemicontinuous W := by
    have hW : W = fun p => ⨆ j, Em j p := funext hWsup
    rw [hW]
    exact lowerSemicontinuous_iSup fun j => (Em j).2.2
  have hext : IsExtMetric W :=
    Uniqueness.Toolkit.WeylLength.weylScale_isExtMetric D ξ f hforget
  let E : LSCMetric := ⟨W, hext, hlsc⟩
  have hEW : ∀ p, E p = W p := fun _ => rfl
  
  have hlim : ∀ (pseq : ℕ → ℂ × ℂ) (q : ℂ × ℂ), Tendsto pseq atTop (𝓝 q) →
      W q ≤ liminf (fun n => G n (pseq n)) atTop := by
    intro pseq q hq
    rw [hWsup q]
    refine iSup_le fun j => ?_
    calc Em j q ≤ liminf (fun n => normalizedLFPPMetric ξ (a n)
          (φ n + LQGMetric.LFPP.mollCont (ε n) (hε n) (gm j) (Mm j) (hMm j)) (pseq n)) atTop :=
          (LSCMetric.tendsto_iff.1 (hEmc j)).1 pseq q hq
      _ ≤ liminf (fun n => G n (pseq n)) atTop :=
          liminf_le_liminf (Eventually.of_forall fun n =>
            normalizedLFPPMetric_add_mollCont_mono hξ (a n) (φ n) (hε n) (hMm j) hM
              (hgmf j) (pseq n)) (by isBoundedDefault) (by isBoundedDefault)
  refine ⟨E, hEW, LSCMetric.tendsto_iff.2 ⟨hlim, fun q => ?_⟩⟩
  change ∃ pseq : ℕ → ℂ × ℂ, Tendsto pseq atTop (𝓝 q) ∧
    Tendsto (fun n => G n (pseq n)) atTop (𝓝 (W q))
  by_cases htop : W q = ⊤
  · refine ⟨fun _ => q, tendsto_const_nhds, ?_⟩
    rw [htop]
    have h := hlim (fun _ => q) q tendsto_const_nhds
    rw [htop] at h
    exact tendsto_of_le_liminf_of_limsup_le h le_top (by isBoundedDefault) (by isBoundedDefault)
  
  have hδ : ∀ δ : ℝ, 0 < δ → ∃ pseq : ℕ → ℂ × ℂ, Tendsto pseq atTop (𝓝 q) ∧
      ∀ᶠ n in atTop, G n (pseq n) ≤ W q + ENNReal.ofReal δ := by
    intro δ hδ
    have hδ2 : (0 : ℝ≥0∞) < ENNReal.ofReal (δ / 2) := ENNReal.ofReal_pos.2 (half_pos hδ)
    have hlt : limsup (fun j => Ep j q) atTop < W q + ENNReal.ofReal (δ / 2) :=
      lt_of_le_of_lt (hupper q) (ENNReal.lt_add_right htop hδ2.ne')
    obtain ⟨j, hj⟩ := (eventually_lt_of_limsup_lt hlt (by isBoundedDefault)).exists
    have hEptop : Ep j q ≠ ⊤ :=
      ne_top_of_lt (hj.trans (ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 htop,
        ENNReal.ofReal_lt_top⟩))
    obtain ⟨pseq, hpq, hconv⟩ := (LSCMetric.tendsto_iff.1 (hEpc j)).2 q
    refine ⟨pseq, hpq, ?_⟩
    have hev := (tendsto_order.1 hconv).2 _ (ENNReal.lt_add_right hEptop hδ2.ne')
    filter_upwards [hev] with n hn
    calc G n (pseq n)
        ≤ normalizedLFPPMetric ξ (a n)
          (φ n + LQGMetric.LFPP.mollCont (ε n) (hε n) (gp j) (Mp j) (hMp j)) (pseq n) :=
          normalizedLFPPMetric_add_mollCont_mono hξ (a n) (φ n) (hε n) hM (hMp j)
            (hfgp j) (pseq n)
      _ ≤ Ep j q + ENNReal.ofReal (δ / 2) := hn.le
      _ ≤ (W q + ENNReal.ofReal (δ / 2)) + ENNReal.ofReal (δ / 2) := add_le_add hj.le le_rfl
      _ = W q + ENNReal.ofReal δ := by
          rw [add_assoc, ← ENNReal.ofReal_add (half_pos hδ).le (half_pos hδ).le, add_halves]
  obtain ⟨pseq, hpq, hev⟩ := exists_diagonal_upper (fun n x => G n x) q (W q) hδ
  refine ⟨pseq, hpq, tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩⟩
  · exact eventually_lt_of_lt_liminf (lt_of_lt_of_le hb (hlim pseq q hpq))
      (by isBoundedDefault)
  · obtain ⟨r, hr0, hrb⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hb
    filter_upwards [hev (r : ℝ) (by exact_mod_cast hr0)] with n hn
    refine lt_of_le_of_lt hn ?_
    rwa [ENNReal.ofReal_coe_nnreal]

end SupercriticalLQGUniqueness.B2.PfeWeyl
