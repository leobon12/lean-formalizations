import SupercriticalLQGUniqueness.B2.PfeLocal.L6Path

 














set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeLocal

open LQGMetric LQGMetric.DFGPS LQGMetric.DFGPS.L217 LQGMetric.LFPP PfeWeyl

 
def l6Λ (S : L6Geo) (ξ : ℝ) (g₀ : L6S → DistC) {Ω' : Type} (h' : Ω' → DistC)
    (L : Ω' → LSCMetric) (ω : Ω') : L6Lam S.R :=
  (pairJ ⊤ (h' ω), (fun d => l5Obs (L ω) d,
    (fun d => ENNReal.ofReal (Real.exp (-(ξ * S.cA (h' ω)))) * l5Obs (L ω) d, S.u g₀ (h' ω))))

theorem measurable_l6Λ (S : L6Geo) (ξ : ℝ) {g₀ : L6S → DistC} (hg₀ : Measurable g₀)
    {Ω' : Type} [MeasurableSpace Ω'] {h' : Ω' → DistC} (hh'm : Measurable h')
    {L : Ω' → LSCMetric} (hL : Measurable L) : Measurable (l6Λ S ξ g₀ h' L) := by
  have hobs : Measurable fun ω => fun d => l5Obs (L ω) d :=
    measurable_pi_iff.2 fun d => (measurable_l5Obs d).comp hL
  have hc : Measurable fun ω => ENNReal.ofReal (Real.exp (-(ξ * S.cA (h' ω)))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((S.measurable_cA.comp hh'm).const_mul ξ).neg)
  refine ((measurable_pairJ ⊤).comp hh'm).prodMk (hobs.prodMk ?_)
  refine (measurable_pi_iff.2 fun d => hc.mul ((measurable_l5Obs d).comp hL)).prodMk ?_
  exact (S.measurable_u hg₀).comp hh'm

 
def l6GoodA (S : L6Geo) (p : L6Lam S.R × L6Y) : Prop :=
  (∀ d : L5Code, l5Rect d.1 ⊆ (S.V₁ : Set ℂ) → p.1.2.2.1 d ≤ p.2.2.1 d) ∧
    ∀ (c : L5Code) (k : ℕ), l5Rect (l6Enlarge c k).1 ⊆ (S.V₁ : Set ℂ) →
      p.2.2.1 (l6Enlarge c k) ≤ p.1.2.2.1 (l6Enlarge c (k + 1))

 
def l6GoodB (S : L6Geo) (ξ : ℝ) (p : L6Lam S.R × L6Y) : Prop :=
  (∀ (d : L5Code) (j : ℕ) (q : ℚ), l5Rect d.1 ⊆ (S.U₁ : Set ℂ) →
      ‖l6Res S.R (l6W S.R j) - p.1.2.2.2‖ < q →
        ENNReal.ofReal (Real.exp (-(ξ * q))) * p.1.2.1 d ≤ p.2.2.2 (d, j)) ∧
    ∀ (c : L5Code) (k j : ℕ) (q : ℚ), l5Rect (l6Enlarge c k).1 ⊆ (S.U₁ : Set ℂ) →
      ‖l6Res S.R (l6W S.R j) - p.1.2.2.2‖ < q →
        p.2.2.2 (l6Enlarge c k, j) ≤ ENNReal.ofReal (Real.exp (ξ * q)) * p.1.2.1 (l6Enlarge c (k + 1))

 
theorem l6_smallAnnulusCosts_comp {G : ℕ → LSCMetric} {D : LSCMetric} {K K' : Set ℂ}
    (h : SmallAnnulusCosts G D K K') {ψ : ℕ → ℕ} (hψ : Tendsto ψ atTop atTop) :
    SmallAnnulusCosts (fun n => G (ψ n)) D K K' := by
  intro z hz hns δ hδ ρ hρ
  obtain ⟨A, h1, h2, h3, h4, h5⟩ := h z hz hns δ hδ ρ hρ
  exact ⟨A, h1, h2, h3, h4, hψ.eventually h5⟩

 
theorem l6_ae_tendsto_pairJ {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {h' : Ω' → DistC} {hN : ℕ → Ω' → DistC}
    (hpair : ∀ φ : TestC, ∀ᵐ ω ∂P', Tendsto (fun n => hN n ω φ) atTop (𝓝 (h' ω φ))) :
    ∀ᵐ ω ∂P', Tendsto (fun n => pairJ ⊤ (hN n ω)) atTop (𝓝 (pairJ ⊤ (h' ω))) := by
  have h : ∀ᵐ ω ∂P', ∀ c : CoordJ, Tendsto (fun n => hN n ω (comb ⊤ c)) atTop
      (𝓝 (h' ω (comb ⊤ c))) := ae_all_iff.2 fun c => hpair _
  filter_upwards [h] with ω hω
  exact tendsto_pi_nhds.2 fun c => hω c

 
theorem l6_stage_rel {ξ : ℝ} (hξ : 0 ≤ ξ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (e : ℕ → Set.Ioi (0 : ℝ)) (he : Tendsto (fun n => (e n : ℝ)) atTop (𝓝 0))
    {V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)} (hVm : ∀ δ, Measurable (V δ))
    {μ : Measure DistC} [IsProbabilityMeasure μ] (hμ : IsNormalizedWPGFF id μ)
    (hV : ∀ δ : Set.Ioi (0 : ℝ), ∀ᵐ g ∂μ, ∀ z, V δ g z = heatMollify (δ : ℝ) g z)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {h' : Ω' → DistC} (hh'm : Measurable h') (hh'law : P'.map h' = μ)
    {hN : ℕ → Ω' → DistC} (hNm : ∀ n, Measurable (hN n)) (hNlaw : ∀ n, P'.map (hN n) = μ)
    (hpair : ∀ φ : TestC, ∀ᵐ ω ∂P', Tendsto (fun n => hN n ω φ) atTop (𝓝 (h' ω φ)))
    {L : Ω' → LSCMetric} (hL : Measurable L)
    (hconv : ∀ᵐ ω ∂P', Tendsto (fun n => normalizedLFPPMetric ξ (m (e n)) (V (e n) (hN n ω)))
      atTop (𝓝 (L ω)))
    (hsmall : ∀ k : ℕ, ∀ᵐ ω ∂P', SmallAnnulusCosts
      (fun n => normalizedLFPPMetric ξ (m (e n)) (V (e n) (hN n ω))) (L ω) (closedBall 0 k)
      (ball 0 ((k : ℝ) + 1)))
    (S : L6Geo) {g₀ : L6S → DistC} (hg₀ : Measurable g₀)
    (hind : ∀ n, Indep ((l6G S).comap (pairJ ⊤) ⊔
        MeasurableSpace.comap (l6An ξ m e S n) inferInstance)
      ((l6H S g₀).comap (pairJ ⊤) ⊔ MeasurableSpace.comap (l6Bn ξ m e S g₀ n) inferInstance)
      μ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (μs : ℕ → ProbabilityMeasure (L6Lam S.R × L6Y))
      (ρ : ProbabilityMeasure (L6Lam S.R × L6Y)),
      (∀ n, (μs n : Measure (L6Lam S.R × L6Y)) = P'.map fun ω =>
        (l6Λ S ξ g₀ h' L ω, l6Yn hN (l6An ξ m e S) (l6Bn ξ m e S g₀) (ψ n) ω)) ∧
      Tendsto μs atTop (𝓝 ρ) ∧
      (ρ : Measure (L6Lam S.R × L6Y)).map Prod.fst = P'.map (l6Λ S ξ g₀ h' L) ∧
      Indep ((l6G S).comap (fun p : L6Lam S.R × L6Y => p.2.1) ⊔
          MeasurableSpace.comap (fun p : L6Lam S.R × L6Y => p.2.2.1) inferInstance)
        ((l6H S g₀).comap (fun p : L6Lam S.R × L6Y => p.2.1) ⊔
          MeasurableSpace.comap (fun p : L6Lam S.R × L6Y => p.2.2.2) inferInstance)
        (ρ : Measure (L6Lam S.R × L6Y)) ∧
      ∀ᵐ p ∂(ρ : Measure (L6Lam S.R × L6Y)), l6GoodA S p ∧ l6GoodB S ξ p ∧ p.2.1 = p.1.1 := by
  
  have hpairJ := l6_ae_tendsto_pairJ hpair
  have hrecwp := (isNormalizedAt_recenter hμ.1 S.hr S.z).1
  have hN2m : Measurable (S.N2 g₀) :=
    (isGFFPlusBddCont_sub_ofCont hrecwp (S.measurable_Fb hg₀) (S.bound_Fb g₀)).1
  have hA := l6_prob_of_ae (E := fun n g => l6ErrA S V (e n) g)
    (fun n => measurable_l6ErrA S hVm (e n)) (l6_errA_ae hμ S hV he) hNm hNlaw
  have hB := l6_prob_of_ae (E := fun n g => l6ErrB S V (e n) g₀ g)
    (fun n => measurable_l6ErrB S hVm (e n) hg₀ hN2m) (l6_errB_ae hμ S hV he hg₀) hNm hNlaw
  have hC := l6_prob_comp hh'm hh'law hNm hNlaw hpairJ S.cA S.measurable_cA
  have hU := l6_prob_comp hh'm hh'law hNm hNlaw hpairJ (S.u g₀) (S.measurable_u hg₀)
  have hE := l6_tendsto_measure_add (l6_tendsto_measure_add (l6_tendsto_measure_add hA hB) hC) hU
  obtain ⟨ψ₀, hψ₀, hE0⟩ := l6_exists_subseq_ae hE
  
  have hΛ := measurable_l6Λ S ξ hg₀ hh'm hL
  obtain ⟨ψ₁, hψ₁, μs, ρ, hμs, hlim, hmarg, hindρ⟩ := l6_exists_coupling hΛ
    (hN := fun n => hN (ψ₀ n)) (fun n => hNm _) (fun n => hNlaw _)
    (An := fun n => l6An ξ m e S (ψ₀ n)) (Bn := fun n => l6Bn ξ m e S g₀ (ψ₀ n))
    (fun n => measurable_l6An _ _ _ _ _)
    (fun n => (measurable_l6ObsFn _ _ _ _ _).comp hN2m)
    ⟨l6G S, l6G_le S⟩ ⟨l6H S g₀, l6H_le S hg₀⟩ (fun n => hind (ψ₀ n))
  set ψ : ℕ → ℕ := fun n => ψ₀ (ψ₁ n) with hψdef
  have hψ : StrictMono ψ := hψ₀.comp hψ₁
  refine ⟨ψ, hψ, μs, ρ, hμs, hlim, hmarg, hindρ, ?_⟩
  
  have hYm : ∀ n, Measurable fun ω =>
      (l6Λ S ξ g₀ h' L ω, l6Yn hN (l6An ξ m e S) (l6Bn ξ m e S g₀) (ψ n) ω) := fun n =>
    hΛ.prodMk (((measurable_pairJ ⊤).comp (hNm _)).prodMk
      (((measurable_l6An _ _ _ _ _).comp (hNm _)).prodMk
        (((measurable_l6ObsFn _ _ _ _ _).comp hN2m).comp (hNm _))))
  
  have hsmall' : ∀ᵐ ω ∂P', ∀ k : ℕ, SmallAnnulusCosts
      (fun n => normalizedLFPPMetric ξ (m (e n)) (V (e n) (hN n ω))) (L ω) (closedBall 0 k)
      (ball 0 ((k : ℝ) + 1)) := ae_all_iff.2 hsmall
  have hgood : ∀ᵐ ω ∂P',
      Tendsto (fun n => normalizedLFPPMetric ξ (m (e (ψ n))) (V (e (ψ n)) (hN (ψ n) ω))) atTop
        (𝓝 (L ω)) ∧
      (∀ k : ℕ, SmallAnnulusCosts
        (fun n => normalizedLFPPMetric ξ (m (e (ψ n))) (V (e (ψ n)) (hN (ψ n) ω))) (L ω)
        (closedBall 0 k) (ball 0 ((k : ℝ) + 1))) ∧
      Tendsto (fun n => l6ErrA S V (e (ψ n)) (hN (ψ n) ω)) atTop (𝓝 0) ∧
      Tendsto (fun n => l6ErrB S V (e (ψ n)) g₀ (hN (ψ n) ω)) atTop (𝓝 0) ∧
      Tendsto (fun n => S.cA (hN (ψ n) ω)) atTop (𝓝 (S.cA (h' ω))) ∧
      Tendsto (fun n => S.u g₀ (hN (ψ n) ω)) atTop (𝓝 (S.u g₀ (h' ω))) ∧
      Tendsto (fun n => pairJ ⊤ (hN (ψ n) ω)) atTop (𝓝 (pairJ ⊤ (h' ω))) := by
    filter_upwards [hconv, hsmall', hE0, hpairJ] with ω h1 h2 h3 h4
    have hψt : Tendsto ψ atTop atTop := hψ.tendsto_atTop
    have hψ₁t : Tendsto ψ₁ atTop atTop := hψ₁.tendsto_atTop
    have h3' := h3.comp hψ₁t
    have hsq : ∀ {a b c d' : ℕ → ℝ}, (∀ n, 0 ≤ a n) → (∀ n, 0 ≤ b n) → (∀ n, 0 ≤ c n) →
        (∀ n, 0 ≤ d' n) → Tendsto (fun n => a n + b n + c n + d' n) atTop (𝓝 0) →
        Tendsto a atTop (𝓝 0) ∧ Tendsto b atTop (𝓝 0) ∧ Tendsto c atTop (𝓝 0) ∧
          Tendsto d' atTop (𝓝 0) := by
      intro a b c d' ha hb hc hd h
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun n => ?_)
          (fun n => ?_) <;> simp only [] <;>
        linarith [ha n, hb n, hc n, hd n]
    obtain ⟨hA', hB', hC', hU'⟩ := hsq (fun n => norm_nonneg _) (fun n => norm_nonneg _)
      (fun n => norm_nonneg _) (fun n => norm_nonneg _) h3'
    refine ⟨h1.comp hψt, fun k => l6_smallAnnulusCosts_comp (h2 k) hψt, hA', hB', ?_, ?_,
      h4.comp hψt⟩
    · exact tendsto_iff_norm_sub_tendsto_zero.2 hC'
    · exact tendsto_iff_norm_sub_tendsto_zero.2 hU'
  have heψ : Tendsto (fun n => (e (ψ n) : ℝ)) atTop (𝓝 0) := he.comp hψ.tendsto_atTop
  
  have hR0 : ∀ c : CoordJ, ∀ᵐ p ∂(ρ : Measure (L6Lam S.R × L6Y)), p.2.1 c - p.1.1 c = 0 :=
    fun c => l6_ae_eq_zero_of_tendsto hYm hμs hlim
      ((continuous_apply c).comp (continuous_fst.comp continuous_snd) |>.sub
        ((continuous_apply c).comp (continuous_fst.comp continuous_fst)))
      (by
        filter_upwards [hgood] with ω hω
        have := (continuous_apply c).continuousAt.tendsto.comp hω.2.2.2.2.2.2
        simpa [l6Yn, l6Λ] using this.sub_const (pairJ ⊤ (h' ω) c))
  
  have hA1 : ∀ d : L5Code, l5Rect d.1 ⊆ (S.V₁ : Set ℂ) →
      ∀ᵐ p ∂(ρ : Measure (L6Lam S.R × L6Y)), p.1 ∈ univ → p.1.2.2.1 d ≤ p.2.2.1 d := by
    intro d hd
    refine l6_ae_ge_of_liminf hYm hμs hlim
      ((continuous_apply d).comp (continuous_fst.comp (continuous_snd.comp continuous_snd)))
      ((continuous_apply d).comp (continuous_fst.comp (continuous_snd.comp continuous_snd)))
      isOpen_univ ?_
    filter_upwards [hgood] with ω hω _
    exact l6_pathA_lower hξ heψ S hω.1 hω.2.2.1 hω.2.2.2.2.1 hd
  have hA2 : ∀ (c : L5Code) (k : ℕ), l5Rect (l6Enlarge c k).1 ⊆ (S.V₁ : Set ℂ) →
      ∀ᵐ p ∂(ρ : Measure (L6Lam S.R × L6Y)), p.1 ∈ univ →
        p.2.2.1 (l6Enlarge c k) ≤ p.1.2.2.1 (l6Enlarge c (k + 1)) := by
    intro c k hd
    refine l6_ae_le_of_limsup hYm hμs hlim
      ((continuous_apply _).comp (continuous_fst.comp (continuous_snd.comp continuous_snd)))
      ((continuous_apply _).comp (continuous_fst.comp (continuous_snd.comp continuous_snd)))
      isOpen_univ ?_
    filter_upwards [hgood] with ω hω _
    exact l6_pathA_upper hξ heψ S hω.1 hω.2.1 hω.2.2.1 hω.2.2.2.2.1 c hd
  
  have hB1 : ∀ (d : L5Code) (j : ℕ) (q : ℚ), l5Rect d.1 ⊆ (S.U₁ : Set ℂ) →
      ∀ᵐ p ∂(ρ : Measure (L6Lam S.R × L6Y)),
        p.1 ∈ {l : L6Lam S.R | ‖l6Res S.R (l6W S.R j) - l.2.2.2‖ < q} →
          ENNReal.ofReal (Real.exp (-(ξ * q))) * p.1.2.1 d ≤ p.2.2.2 (d, j) := by
    intro d j q hd
    refine l6_ae_ge_of_liminf hYm hμs hlim
      ((continuous_apply (d, j)).comp (continuous_snd.comp (continuous_snd.comp continuous_snd)))
      (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top |>.comp
        ((continuous_apply d).comp (continuous_fst.comp continuous_snd)))
      (isOpen_lt (continuous_const.sub (continuous_snd.comp (continuous_snd.comp
        continuous_snd))).norm continuous_const) ?_
    filter_upwards [hgood] with ω hω hq
    exact l6_pathB_lower hξ heψ S hω.1 hω.2.2.2.1 hω.2.2.2.2.2.1 hd j hq
  have hB2 : ∀ (c : L5Code) (k j : ℕ) (q : ℚ), l5Rect (l6Enlarge c k).1 ⊆ (S.U₁ : Set ℂ) →
      ∀ᵐ p ∂(ρ : Measure (L6Lam S.R × L6Y)),
        p.1 ∈ {l : L6Lam S.R | ‖l6Res S.R (l6W S.R j) - l.2.2.2‖ < q} →
          p.2.2.2 (l6Enlarge c k, j) ≤
            ENNReal.ofReal (Real.exp (ξ * q)) * p.1.2.1 (l6Enlarge c (k + 1)) := by
    intro c k j q hd
    refine l6_ae_le_of_limsup hYm hμs hlim
      ((continuous_apply (l6Enlarge c k, j)).comp
        (continuous_snd.comp (continuous_snd.comp continuous_snd)))
      (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top |>.comp
        ((continuous_apply _).comp (continuous_fst.comp continuous_snd)))
      (isOpen_lt (continuous_const.sub (continuous_snd.comp (continuous_snd.comp
        continuous_snd))).norm continuous_const) ?_
    filter_upwards [hgood] with ω hω hq
    exact l6_pathB_upper hξ heψ S hω.1 hω.2.1 hω.2.2.2.1 hω.2.2.2.2.2.1 c hd j hq
  
  have hR0' : ∀ᵐ p ∂(ρ : Measure (L6Lam S.R × L6Y)), ∀ c : CoordJ, p.2.1 c - p.1.1 c = 0 :=
    ae_all_iff.2 hR0
  have hA1' : ∀ᵐ p ∂(ρ : Measure (L6Lam S.R × L6Y)), ∀ d : L5Code,
      l5Rect d.1 ⊆ (S.V₁ : Set ℂ) → p.1.2.2.1 d ≤ p.2.2.1 d := by
    refine ae_all_iff.2 fun d => ?_
    by_cases hd : l5Rect d.1 ⊆ (S.V₁ : Set ℂ)
    · filter_upwards [hA1 d hd] with p hp _ using hp (mem_univ _)
    · exact Eventually.of_forall fun p h => absurd h hd
  have hA2' : ∀ᵐ p ∂(ρ : Measure (L6Lam S.R × L6Y)), ∀ (c : L5Code) (k : ℕ),
      l5Rect (l6Enlarge c k).1 ⊆ (S.V₁ : Set ℂ) →
        p.2.2.1 (l6Enlarge c k) ≤ p.1.2.2.1 (l6Enlarge c (k + 1)) := by
    refine ae_all_iff.2 fun c => ae_all_iff.2 fun k => ?_
    by_cases hd : l5Rect (l6Enlarge c k).1 ⊆ (S.V₁ : Set ℂ)
    · filter_upwards [hA2 c k hd] with p hp _ using hp (mem_univ _)
    · exact Eventually.of_forall fun p h => absurd h hd
  have hB1' : ∀ᵐ p ∂(ρ : Measure (L6Lam S.R × L6Y)), ∀ (d : L5Code) (j : ℕ) (q : ℚ),
      l5Rect d.1 ⊆ (S.U₁ : Set ℂ) → ‖l6Res S.R (l6W S.R j) - p.1.2.2.2‖ < q →
        ENNReal.ofReal (Real.exp (-(ξ * q))) * p.1.2.1 d ≤ p.2.2.2 (d, j) := by
    refine ae_all_iff.2 fun d => ae_all_iff.2 fun j => ae_all_iff.2 fun q => ?_
    by_cases hd : l5Rect d.1 ⊆ (S.U₁ : Set ℂ)
    · filter_upwards [hB1 d j q hd] with p hp _ hq using hp hq
    · exact Eventually.of_forall fun p h => absurd h hd
  have hB2' : ∀ᵐ p ∂(ρ : Measure (L6Lam S.R × L6Y)), ∀ (c : L5Code) (k j : ℕ) (q : ℚ),
      l5Rect (l6Enlarge c k).1 ⊆ (S.U₁ : Set ℂ) → ‖l6Res S.R (l6W S.R j) - p.1.2.2.2‖ < q →
        p.2.2.2 (l6Enlarge c k, j) ≤
          ENNReal.ofReal (Real.exp (ξ * q)) * p.1.2.1 (l6Enlarge c (k + 1)) := by
    refine ae_all_iff.2 fun c => ae_all_iff.2 fun k => ae_all_iff.2 fun j =>
      ae_all_iff.2 fun q => ?_
    by_cases hd : l5Rect (l6Enlarge c k).1 ⊆ (S.U₁ : Set ℂ)
    · filter_upwards [hB2 c k j q hd] with p hp _ hq using hp hq
    · exact Eventually.of_forall fun p h => absurd h hd
  filter_upwards [hR0', hA1', hA2', hB1', hB2'] with p h0 h1 h2 h3 h4
  exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩, funext fun c => sub_eq_zero.1 (h0 c)⟩

end SupercriticalLQGUniqueness.B2.PfeLocal
