import SupercriticalLQGUniqueness.B2.PfeWeyl.W2ApproxRecovery

 














set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 

theorem ofReal_exp_mul_le_weylScale (ξ : ℝ) (hξ : 0 ≤ ξ) (g : C(ℂ, ℝ))
    (E : LSCMetric) (hforget : Continuous (euclidForget E)) (M : ℝ)
    (hg : ∀ z, |g z| ≤ M) (x y : ℂ) :
    ENNReal.ofReal (Real.exp (ξ * -M)) * E (x, y) ≤ weylScale ξ g E (x, y) := by
  unfold weylScale
  refine le_iInf fun P => le_iInf fun L => le_iInf fun hP => le_iInf fun hu =>
    le_iInf fun hx => le_iInf fun hy => ?_
  have hb := (unitSpeed_weyl_cost_bounds E ξ hξ g hforget hP hu (-M) M
    (fun t _ => (abs_le.1 (hg (P t))).1) (fun t _ => (abs_le.1 (hg (P t))).2)).1
  refine le_trans ?_ hb
  gcongr
  have h := LSCMetric.apply_le_len E P hP.1
  rwa [hx, hy] at h

 
theorem weyl_lsc_convergence
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
      SmallAnnulusCosts G D (Metric.closedBall 0 k) (Metric.ball 0 ((k : ℝ) + 1))) :
    (∀ (p : ℕ → ℂ × ℂ) (q : ℂ × ℂ), Tendsto p atTop (𝓝 q) →
        weylScale ξ f D q ≤ liminf (fun n => W n (p n)) atTop) ∧
      ∀ q : ℂ × ℂ, ∃ p : ℕ → ℂ × ℂ, Tendsto p atTop (𝓝 q) ∧
        Tendsto (fun n => W n (p n)) atTop (𝓝 (weylScale ξ f D q)) := by
  have hWp : ∀ n p, W n p = weylScale ξ (fn n) (G n) p := fun n p => by
    simpa only [Prod.mk.eta] using hW n p.1 p.2
  have hlow : ∀ (p : ℕ → ℂ × ℂ) (q : ℂ × ℂ), Tendsto p atTop (𝓝 q) →
      weylScale ξ f D q ≤ liminf (fun n => W n (p n)) atTop := by
    intro p q hp
    simp only [hWp]
    exact weyl_gamma_liminf hG ξ hξ f fn hfn M hfnM hGforget hDlen hDforget hacross hp
  refine ⟨hlow, fun q => ?_⟩
  by_cases htop : weylScale ξ f D q = ⊤
  · 
    have hDtop : D q = ⊤ := by
      by_contra hne
      have hlt : D (q.1, q.2) < ⊤ := by rw [Prod.mk.eta]; exact lt_top_iff_ne_top.2 hne
      have hb := weylScale_le_exp_mul_of_local ξ hξ f D hDlen hlt one_pos (M' := M)
        (fun x _ => (abs_le.1 (hfM x)).2)
      rw [Prod.mk.eta] at hb hlt
      have hfin : weylScale ξ f D q < ⊤ := hb.trans_lt (ENNReal.mul_lt_top
        ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2 ⟨hlt, ENNReal.ofReal_lt_top⟩))
      exact hfin.ne htop
    obtain ⟨p, hp, hGp⟩ := (LSCMetric.tendsto_iff.1 hG).2 q
    refine ⟨p, hp, ?_⟩
    rw [htop]
    have hc0 : ENNReal.ofReal (Real.exp (ξ * -M)) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
    have hlim : Tendsto (fun n => ENNReal.ofReal (Real.exp (ξ * -M)) * G n (p n)) atTop
        (𝓝 ⊤) := by
      have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (Real.exp (ξ * -M))) hGp
        (Or.inr ENNReal.ofReal_ne_top)
      rwa [hDtop, ENNReal.mul_top hc0] at this
    refine tendsto_nhds_top_mono hlim (Eventually.of_forall fun n => ?_)
    show ENNReal.ofReal (Real.exp (ξ * -M)) * G n (p n) ≤ W n (p n)
    rw [hWp]
    simpa only [Prod.mk.eta] using
      ofReal_exp_mul_le_weylScale ξ hξ (fn n) (G n) (hGforget n) M (hfnM n) (p n).1 (p n).2
  · 
    set e : ℝ≥0∞ := weylScale ξ f D q with hedef
    have happrox : ∀ ε : ℝ, 0 < ε → ∃ p : ℕ → ℂ × ℂ, Tendsto p atTop (𝓝 q) ∧
        ∀ᶠ n in atTop, W n (p n) ≤ e + ENNReal.ofReal ε := by
      intro ε hε
      set e₀ : ℝ := e.toReal with he₀
      have he : e = ENNReal.ofReal e₀ := (ENNReal.ofReal_toReal htop).symm
      have he₀0 : 0 ≤ e₀ := ENNReal.toReal_nonneg
      let F : ℝ → ℝ := fun t =>
        Real.exp (3 * ξ * t) * (e₀ + t) + t * (Real.exp (ξ * (M + t + t)) + 1)
      have hFc : Continuous F := by fun_prop
      have hF0 : F 0 = e₀ := by simp [F]
      have hev : ∀ᶠ t in 𝓝 (0 : ℝ), F t < e₀ + ε :=
        hFc.continuousAt.eventually_lt continuousAt_const (by rw [hF0]; linarith)
      obtain ⟨t, ht1, ht2⟩ :=
        ((hev.filter_mono (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))).and
          self_mem_nhdsWithin).exists
      have ht : 0 < t := ht2
      have hqf : weylScale ξ f D (q.1, q.2) ≠ ⊤ := by rw [Prod.mk.eta]; exact htop
      obtain ⟨x, y, hx, hy, hxy⟩ := weyl_approx_recovery hG hGlen hGforget ξ hξ f fn hfn M
        hfM hfnM hDforget W hW hWforget hsmall hqf ht ht
      refine ⟨fun n => (x n, y n), by simpa only [Prod.mk.eta] using hx.prodMk_nhds hy, ?_⟩
      filter_upwards [hxy] with n hn
      refine hn.trans ?_
      rw [Prod.mk.eta, ← hedef, he, ← ENNReal.ofReal_add he₀0 ht.le,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← ENNReal.ofReal_mul ht.le, ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add he₀0 hε.le]
      exact ENNReal.ofReal_le_ofReal ht1.le
    obtain ⟨p, hp, hpF⟩ := exists_diagonal_upper (fun n p => W n p) q e happrox
    refine ⟨p, hp, tendsto_of_le_liminf_of_limsup_le (hlow p q hp) ?_⟩
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have h := hpF ε (by exact_mod_cast hε)
    simp only [ENNReal.ofReal_coe_nnreal] at h
    exact limsup_le_of_le (by isBoundedDefault) h

end SupercriticalLQGUniqueness.B2.PfeWeyl
