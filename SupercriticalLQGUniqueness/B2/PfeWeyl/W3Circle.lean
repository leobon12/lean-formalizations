import SupercriticalLQGUniqueness.B2.PfeWeyl.W3CircleUpper
import SupercriticalLQGUniqueness.B2.PfeWeyl.W3Stochastic

 











set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric (DistC addFun IsGFFPlusBddCont)
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 
theorem weyl_rationalCircle_tendsto
    {G : ℕ → LSCMetric} {D : LSCMetric} (hG : Tendsto G atTop (𝓝 D))
    (hGlen : ∀ n, (G n).IsLengthSpace)
    (hGforget : ∀ n, Continuous (euclidForget (G n)))
    (ξ : ℝ) (hξ : 0 ≤ ξ) (f : C(ℂ, ℝ)) (fn : ℕ → C(ℂ, ℝ))
    (hfn : ∀ K : Set ℂ, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ x ∈ K, |fn n x - f x| < ε)
    (M : ℝ) (hfM : ∀ z, |f z| ≤ M) (hfnM : ∀ n z, |fn n z| ≤ M)
    (hDlen : D.IsLengthSpace) (hDforget : Continuous (euclidForget D))
    (hacross : AcrossUnbounded D)
    (W : ℕ → LSCMetric)
    (hW : ∀ n x y, W n (x, y) = weylScale ξ (fn n) (G n) (x, y))
    (hWforget : ∀ n, Continuous (euclidForget (W n)))
    (hsmall : ∀ k : ℕ,
      SmallAnnulusCosts G D (Metric.closedBall 0 k) (Metric.ball 0 ((k : ℝ) + 1)))
    (hcirc : ∀ O O' : Set ℂ, IsRationalCircle O → IsRationalCircle O' →
      Tendsto (fun n => setDistance (G n) O O') atTop (𝓝 (setDistance D O O')))
    {O O' : Set ℂ} (hO : IsRationalCircle O) (hO' : IsRationalCircle O') :
    Tendsto (fun n => setDistance (W n) O O') atTop
      (𝓝 (setDistance (weylScale ξ f D) O O')) := by
  obtain ⟨E, hE, hWE⟩ := weyl_tendsto_lscMetric hG hGlen hGforget ξ hξ f fn hfn M hfM
    hfnM hDlen hDforget hacross W hW hWforget hsmall
  have hEfun : (fun p => E p) = weylScale ξ f D := funext hE
  have hlow : setDistance (weylScale ξ f D) O O' ≤
      liminf (fun n => setDistance (W n) O O') atTop := by
    have h := rationalCircle_liminf hWE hO hO'
    have heq : setDistance (fun p => E p) O O' = setDistance (weylScale ξ f D) O O' := by
      rw [hEfun]
    rw [← heq]
    exact h
  set S := setDistance (weylScale ξ f D) O O' with hSdef
  by_cases hS : S = ⊤
  · refine tendsto_of_le_liminf_of_limsup_le hlow ?_
    rw [hS]
    exact le_top
  refine tendsto_of_le_liminf_of_limsup_le hlow ?_
  refine ENNReal.le_of_forall_pos_le_add fun ε' hε' _ => ?_
  set s₀ : ℝ := S.toReal with hs₀
  have hSeq : S = ENNReal.ofReal s₀ := (ENNReal.ofReal_toReal hS).symm
  have hs₀0 : 0 ≤ s₀ := ENNReal.toReal_nonneg
  let F : ℝ → ℝ := fun t =>
    Real.exp (4 * ξ * t) * (s₀ + t + t) + t * (Real.exp (ξ * (M + t + t + t)) + 1)
  have hFc : Continuous F := by fun_prop
  have hF0 : F 0 = s₀ := by simp [F]
  have hε'r : (0 : ℝ) < ε' := by exact_mod_cast hε'
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), F t < s₀ + ε' :=
    hFc.continuousAt.eventually_lt continuousAt_const (by rw [hF0]; linarith)
  obtain ⟨t, ht1, ht2⟩ :=
    ((hev.filter_mono (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))).and
      self_mem_nhdsWithin).exists
  have ht : 0 < t := ht2
  have hup := weyl_rationalCircle_upper hG hGlen hGforget ξ hξ f fn hfn M hfM hfnM hDlen
    hDforget W hW hWforget hsmall hcirc hO hO' ht ht hS
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [hup] with n hn
  refine hn.trans ?_
  rw [← hSdef, hSeq, ← ENNReal.ofReal_add hs₀0 ht.le, ← ENNReal.ofReal_add (by positivity) ht.le,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul ht.le,
    ← ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_coe_nnreal.symm,
    ← ENNReal.ofReal_add hs₀0 hε'r.le]
  exact ENNReal.ofReal_le_ofReal ht1.le

 
theorem setDistance_normalizedLFPPMetric (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ))
    (O O' : Set ℂ) :
    setDistance (normalizedLFPPMetric ξ a φ) O O' =
      ENNReal.ofReal ((a : ℝ)⁻¹) * setDistance (lfppDistance ξ φ) O O' := by
  have h0 : ENNReal.ofReal ((a : ℝ)⁻¹) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (inv_pos.2 a.property)).ne'
  simp only [setDistance, ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top,
    normalizedLFPPMetric_apply]

 

theorem ae_rationalCircle_tendsto_of_subseqLimit
    (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ)) (hX : ∀ δ, IsHeatSmoothing P h δ (X δ)) :
    ∀ᵐ ω ∂P, ∀ O O' : Set ℂ, IsRationalCircle O → IsRationalCircle O' →
      Tendsto (fun n => setDistance (normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (X (ε n) ω)) O O')
        atTop (𝓝 (setDistance (D (h ω)) O O')) := by
  have hbase := (hD P h (LQGMetric.DFGPS.isGFFPlusBddCont_of_wp hh.1) X hX).2
  let circ : ℚ × ℚ × ℚ → Set ℂ := fun c =>
    Metric.sphere (Complex.mk (c.1 : ℝ) (c.2.1 : ℝ)) (c.2.2 : ℝ)
  have hpair : ∀ c c' : ℚ × ℚ × ℚ, ∀ᵐ ω ∂P, 0 ≤ c.2.2 → 0 ≤ c'.2.2 →
      Tendsto (fun n => ENNReal.ofReal ((m (ε n) : ℝ)⁻¹) *
        setDistance (lfppDistance (ξ : ℝ) (X (ε n) ω)) (circ c) (circ c')) atTop
        (𝓝 (setDistance (D (h ω)).1 (circ c) (circ c'))) := by
    intro c c'
    by_cases hc : 0 ≤ c.2.2
    · by_cases hc' : 0 ≤ c'.2.2
      · filter_upwards [hbase (circ c) (circ c') ⟨c.1, c.2.1, c.2.2, hc, rfl⟩
          ⟨c'.1, c'.2.1, c'.2.2, hc', rfl⟩] with ω hω _ _
        exact hω
      · exact Eventually.of_forall fun ω _ h' => absurd h' hc'
    · exact Eventually.of_forall fun ω h' _ => absurd h' hc
  filter_upwards [ae_all_iff.2 fun c => ae_all_iff.2 fun c' => hpair c c'] with ω hω
    O O' hO hO'
  obtain ⟨x, y, r, hr, rfl⟩ := hO
  obtain ⟨x', y', r', hr', rfl⟩ := hO'
  have := hω (x, y, r) (x', y', r') hr hr'
  simp only [setDistance_normalizedLFPPMetric]
  exact this

 

theorem ae_weyl_rationalCircle_all_bounded_of_tendsto
    (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Dω : Ω → LSCMetric) (X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n =>
      normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (X (ε n) ω)) atTop (𝓝 (Dω ω)))
    (hcircω : ∀ᵐ ω ∂P, ∀ O O' : Set ℂ, IsRationalCircle O → IsRationalCircle O' →
      Tendsto (fun n => setDistance (normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (X (ε n) ω)) O O')
        atTop (𝓝 (setDistance (Dω ω) O O')))
    (hlen : ∀ᵐ ω ∂P, (Dω ω).IsLengthSpace)
    (hctrl : ∀ᵐ ω ∂P, ∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
      ∀ v : ℂ, (Dω ω).1 (u, v) < ENNReal.ofReal η → dist u v < δ)
    (hgeo : ∀ k : ℕ, AcrossTailInput P Dω ((k : ℝ) + 1) (Nat.cast_add_one_pos k))
    (hsmall : ∀ k : ℕ, ∀ᵐ ω ∂P,
      SmallAnnulusCosts (fun n => normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (X (ε n) ω))
        (Dω ω) (Metric.closedBall 0 k) (Metric.ball 0 ((k : ℝ) + 1))) :
    ∀ᵐ ω ∂P, ∀ (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ z, |f z| ≤ M) (O O' : Set ℂ),
      IsRationalCircle O → IsRationalCircle O' →
        Tendsto (fun n => setDistance (normalizedLFPPMetric (ξ : ℝ) (m (ε n))
          (X (ε n) ω + LQGMetric.LFPP.mollCont (ε n : ℝ) (ε n).property.ne' f M hM)) O O')
          atTop (𝓝 (setDistance (weylScale (ξ : ℝ) f (Dω ω)) O O')) := by
  filter_upwards [hconv, hlen, hctrl, ae_acrossUnbounded_of_acrossTail P _ hgeo,
    ae_all_iff.2 hsmall, hcircω] with ω hG hL hC hA hS hcirc f M hM O O' hO hO'
  have hε0 : ∀ n, (ε n : ℝ) ≠ 0 := fun n => (ε n).property.ne'
  exact weyl_rationalCircle_tendsto hG
    (fun n => isLengthSpace_normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (X (ε n) ω))
    (fun n => PfeAxioms.continuous_euclidForget_normalizedLFPPMetric (ξ : ℝ) (m (ε n)) _)
    (ξ : ℝ) (le_of_lt ξ.property) f
    (fun n => LQGMetric.LFPP.mollCont (ε n : ℝ) (hε0 n) f M hM)
    (fun K hK η hη => mollCont_fixed_tendsto_compact hε0 hε f M hM K hK η hη)
    M hM (fun n z => abs_mollCont_le (hε0 n) f M hM z) hL
    (B2.PfeLocal.continuous_euclidForget_of_small_metric _ hC) hA
    (fun n => normalizedLFPPMetric (ξ : ℝ) (m (ε n))
      (X (ε n) ω + LQGMetric.LFPP.mollCont (ε n : ℝ) (hε0 n) f M hM))
    (fun n x y => normalizedLFPPMetric_add_eq_weylScale (ξ : ℝ) (m (ε n)) _ _ (x, y))
    (fun n => PfeAxioms.continuous_euclidForget_normalizedLFPPMetric (ξ : ℝ) (m (ε n)) _)
    hS hcirc hO hO'

 

theorem ae_weyl_rationalCircle_all_bounded
    (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ)) (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (hlen : ∀ᵐ ω ∂P, (D (h ω)).IsLengthSpace)
    (hctrl : ∀ᵐ ω ∂P, ∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
      ∀ v : ℂ, (D (h ω)).1 (u, v) < ENNReal.ofReal η → dist u v < δ)
    (hgeo : ∀ k : ℕ, AcrossTailInput P (fun ω => D (h ω)) ((k : ℝ) + 1)
      (Nat.cast_add_one_pos k))
    (hsmall : ∀ k : ℕ, ∀ᵐ ω ∂P,
      SmallAnnulusCosts (fun n => normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (X (ε n) ω))
        (D (h ω)) (Metric.closedBall 0 k) (Metric.ball 0 ((k : ℝ) + 1))) :
    ∀ᵐ ω ∂P, ∀ (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ z, |f z| ≤ M) (O O' : Set ℂ),
      IsRationalCircle O → IsRationalCircle O' →
        Tendsto (fun n => setDistance (normalizedLFPPMetric (ξ : ℝ) (m (ε n))
          (X (ε n) ω + LQGMetric.LFPP.mollCont (ε n : ℝ) (ε n).property.ne' f M hM)) O O')
          atTop (𝓝 (setDistance (weylScale (ξ : ℝ) f (D (h ω))) O O')) :=
  ae_weyl_rationalCircle_all_bounded_of_tendsto ξ m ε hε P (fun ω => D (h ω)) X
    (PfeAxioms.ae_normalizedLFPPMetric_tendsto ξ m ε D hD P h hh X hX)
    (ae_rationalCircle_tendsto_of_subseqLimit ξ m ε D hD P h hh X hX)
    hlen hctrl hgeo hsmall

end SupercriticalLQGUniqueness.B2.PfeWeyl
