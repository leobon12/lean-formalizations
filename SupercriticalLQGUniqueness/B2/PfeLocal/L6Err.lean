import SupercriticalLQGUniqueness.B2.PfeLocal.L6Canon
import SupercriticalLQGUniqueness.B2.PfeLocal.L6Lusin
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalizedLFPP
import LQGMetric.Papers.DFGPS.T12P0
import LQGMetric.Papers.DFGPS.L2_12Moll
import LQGMetric.Papers.DFGPS.L2_6

 



















set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeLocal

open LQGMetric LQGMetric.DFGPS LQGMetric.DFGPS.L217 LQGMetric.LFPP

 
def l6ErrA (S : L6Geo) (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)) (ε : Set.Ioi (0 : ℝ))
    (g : DistC) : ℝ :=
  ‖l6Res S.R (locMollifyC ε ε.2 (S.ren g) - (V ε g - ContinuousMap.const ℂ (S.cA g)))‖

 
def l6ErrB (S : L6Geo) (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)) (ε : Set.Ioi (0 : ℝ))
    (g₀ : L6S → DistC) (g : DistC) : ℝ :=
  ‖l6Res S.R (locMollifyC ε ε.2 (S.N2 g₀ g) -
    (V ε g - ContinuousMap.const ℂ (S.cA g) - S.Fb g₀ g))‖

theorem measurable_const_cA (S : L6Geo) :
    Measurable fun g : DistC => ContinuousMap.const ℂ (S.cA g) :=
  ContinuousMap.measurable_iff_eval.2 fun _ => S.measurable_cA

theorem measurable_l6ErrA (S : L6Geo) {V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
    (hVm : ∀ δ, Measurable (V δ)) (ε : Set.Ioi (0 : ℝ)) : Measurable (l6ErrA S V ε) := by
  have hF : Measurable fun g => locMollifyC ε ε.2 (S.ren g) -
      (V ε g - ContinuousMap.const ℂ (S.cA g)) :=
    ContinuousMap.measurable_iff_eval.2 fun z => by
      simp only [ContinuousMap.sub_apply, ContinuousMap.const_apply]
      exact ((continuous_eval_const z).measurable.comp
        ((measurable_locMollifyC ε ε.2).comp S.measurable_ren)).sub
        (((continuous_eval_const z).measurable.comp (hVm ε)).sub S.measurable_cA)
  exact continuous_norm.measurable.comp ((continuous_l6Res S.R).measurable.comp hF)

theorem measurable_l6ErrB (S : L6Geo) {V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
    (hVm : ∀ δ, Measurable (V δ)) (ε : Set.Ioi (0 : ℝ)) {g₀ : L6S → DistC}
    (hg₀ : Measurable g₀) (hN2 : Measurable (S.N2 g₀)) : Measurable (l6ErrB S V ε g₀) := by
  have hF : Measurable fun g => locMollifyC ε ε.2 (S.N2 g₀ g) -
      (V ε g - ContinuousMap.const ℂ (S.cA g) - S.Fb g₀ g) :=
    ContinuousMap.measurable_iff_eval.2 fun z => by
      simp only [ContinuousMap.sub_apply, ContinuousMap.const_apply]
      exact ((continuous_eval_const z).measurable.comp
        ((measurable_locMollifyC ε ε.2).comp hN2)).sub
        ((((continuous_eval_const z).measurable.comp (hVm ε)).sub S.measurable_cA).sub
          ((continuous_eval_const z).measurable.comp (S.measurable_Fb hg₀)))
  exact continuous_norm.measurable.comp ((continuous_l6Res S.R).measurable.comp hF)

 
theorem l6_tendsto_nhdsGT {e : ℕ → Set.Ioi (0 : ℝ)} (he : Tendsto (fun n => (e n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => (e n : ℝ)) atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.2 ⟨he, Eventually.of_forall fun n => (e n).2⟩

 

theorem l6_heatMollify_sub_ofCont {ε : ℝ} (hε : ε ≠ 0) {h : DistC} {z : ℂ}
    (hh : Tendsto (fun n : ℕ => h (heatTrunc (ε ^ 2 / 2) z n)) atTop (𝓝 (heatMollify ε h z)))
    (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ w, |f w| ≤ M) :
    heatMollify ε (h - ofCont f) z = heatMollify ε h z - heatMollify ε (ofCont f) z :=
  (hh.sub (tendsto_heatMollify_ofCont f M hM hε z)).limUnder_eq

 
theorem l6_errA_ae {μ : Measure DistC} [IsProbabilityMeasure μ] (hμ : IsNormalizedWPGFF id μ)
    (S : L6Geo) {V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
    (hV : ∀ δ : Set.Ioi (0 : ℝ), ∀ᵐ g ∂μ, ∀ z, V δ g z = heatMollify (δ : ℝ) g z)
    {e : ℕ → Set.Ioi (0 : ℝ)} (he : Tendsto (fun n => (e n : ℝ)) atTop (𝓝 0)) :
    ∀ᵐ g ∂μ, Tendsto (fun n => l6ErrA S V (e n) g) atTop (𝓝 0) := by
  have hrenB : IsGFFPlusBddCont S.ren μ := isGFFPlusBddCont_normField hμ S.hr S.z
  have hcomp := PfeAxioms.localizedLFPP_compare hrenB (U := ball (0 : ℂ) (S.R + 1))
    isBounded_ball ⟨1, Set.mem_Ioi.2 one_pos⟩
  have hraw : IsGFFPlusBddCont (id : DistC → DistC) μ := T12.isGFFPlusBddCont_of_wp hμ.1
  have htr : ∀ᵐ g ∂μ, ∀ n, TendstoLocallyUniformly
      (fun (k : ℕ) (z : ℂ) => g (heatTrunc ((e n : ℝ) ^ 2 / 2) z k))
      (heatMollify (e n) g) atTop ∧ Continuous (heatMollify (e n) g) :=
    ae_all_iff.2 fun n => hraw.ae_tendstoLocallyUniformly_heatMollify (e n) (e n).2.ne'
  have hVn : ∀ᵐ g ∂μ, ∀ n z, V (e n) g z = heatMollify (e n) g z :=
    ae_all_iff.2 fun n => hV (e n)
  filter_upwards [hcomp, htr, hVn] with g hc ht hv
  have hge : ∀ n, 0 ≤ l6ErrA S V (e n) g := fun n => norm_nonneg _
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun n => ha.trans_le (hge n),
    fun a ha => ?_⟩
  have ha2 : 0 < a / 2 := half_pos ha
  have hev := (l6_tendsto_nhdsGT he).eventually (hc.1 (a / 2) ha2)
  filter_upwards [hev] with n hn
  refine lt_of_le_of_lt ?_ (half_lt_self ha)
  refine (ContinuousMap.norm_le _ ha2.le).2 fun x => ?_
  have hx : (x : ℂ) ∈ closure (ball (0 : ℂ) (S.R + 1)) :=
    subset_closure (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 x.2) (by linarith)))
  have key := hn (e n).2 x hx
  have hren : heatMollify (e n) (S.ren g) x = heatMollify (e n) g x + -S.cA g :=
    heatMollify_addConst_of_tendsto (e n).2.ne' ((tendstoLocallyUniformlyOn_univ.2 (ht n).1).tendsto_at (mem_univ (x : ℂ))) _
  simp only [l6Res_apply, ContinuousMap.sub_apply, ContinuousMap.const_apply, Real.norm_eq_abs]
  change |locMollify (e n) (e n).2 (S.ren g) x - (V (e n) g x - S.cA g)| ≤ a / 2
  rw [hv n x, abs_sub_comm]
  convert key using 2
  rw [hren]; ring

 
theorem l6_errB_ae {μ : Measure DistC} [IsProbabilityMeasure μ] (hμ : IsNormalizedWPGFF id μ)
    (S : L6Geo) {V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
    (hV : ∀ δ : Set.Ioi (0 : ℝ), ∀ᵐ g ∂μ, ∀ z, V δ g z = heatMollify (δ : ℝ) g z)
    {e : ℕ → Set.Ioi (0 : ℝ)} (he : Tendsto (fun n => (e n : ℝ)) atTop (𝓝 0))
    {g₀ : L6S → DistC} (hg₀ : Measurable g₀) :
    ∀ᵐ g ∂μ, Tendsto (fun n => l6ErrB S V (e n) g₀ g) atTop (𝓝 0) := by
  have hrecwp := (isNormalizedAt_recenter hμ.1 S.hr S.z).1
  have hN2B : IsGFFPlusBddCont (S.N2 g₀) μ :=
    isGFFPlusBddCont_sub_ofCont hrecwp (S.measurable_Fb hg₀) (S.bound_Fb g₀)
  have hcomp := PfeAxioms.localizedLFPP_compare hN2B (U := ball (0 : ℂ) (S.R + 1))
    isBounded_ball ⟨1, Set.mem_Ioi.2 one_pos⟩
  have hrenB : IsGFFPlusBddCont S.ren μ := isGFFPlusBddCont_normField hμ S.hr S.z
  have hraw : IsGFFPlusBddCont (id : DistC → DistC) μ := T12.isGFFPlusBddCont_of_wp hμ.1
  have htr : ∀ᵐ g ∂μ, ∀ n, TendstoLocallyUniformly
      (fun (k : ℕ) (z : ℂ) => g (heatTrunc ((e n : ℝ) ^ 2 / 2) z k))
      (heatMollify (e n) g) atTop ∧ Continuous (heatMollify (e n) g) :=
    ae_all_iff.2 fun n => hraw.ae_tendstoLocallyUniformly_heatMollify (e n) (e n).2.ne'
  have htr' : ∀ᵐ g ∂μ, ∀ n, TendstoLocallyUniformly
      (fun (k : ℕ) (z : ℂ) => S.ren g (heatTrunc ((e n : ℝ) ^ 2 / 2) z k))
      (heatMollify (e n) (S.ren g)) atTop ∧ Continuous (heatMollify (e n) (S.ren g)) :=
    ae_all_iff.2 fun n => hrenB.ae_tendstoLocallyUniformly_heatMollify (e n) (e n).2.ne'
  have hVn : ∀ᵐ g ∂μ, ∀ n z, V (e n) g z = heatMollify (e n) g z :=
    ae_all_iff.2 fun n => hV (e n)
  filter_upwards [hcomp, htr, htr', hVn] with g hc ht ht' hv
  obtain ⟨M, hM⟩ := S.bound_Fb g₀ g
  
  have hR1 : 0 < |S.R| + 1 := by positivity
  have hmoll := tendstoUniformlyOn_heatMollify_seq (εn := fun n => (e n : ℝ))
    (fun n => (e n).2.ne') he (fn := fun _ => S.Fb g₀ g) (f := S.Fb g₀ g) (fun _ => hM) hM
    (fun R _ => Metric.tendstoUniformlyOn_iff.2 fun η hη =>
      Eventually.of_forall fun n x _ => by simpa using hη) hR1
  have hge : ∀ n, 0 ≤ l6ErrB S V (e n) g₀ g := fun n => norm_nonneg _
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun n => ha.trans_le (hge n),
    fun a ha => ?_⟩
  have ha2 : 0 < a / 2 := half_pos ha
  have hev := (l6_tendsto_nhdsGT he).eventually (hc.1 (a / 4) (by positivity))
  have hev2 := Metric.tendstoUniformlyOn_iff.1 hmoll (a / 4) (by positivity)
  filter_upwards [hev, hev2] with n hn hn2
  refine lt_of_le_of_lt ?_ (half_lt_self ha)
  refine (ContinuousMap.norm_le _ ha2.le).2 fun x => ?_
  have hxR : ‖(x : ℂ)‖ ≤ S.R := by simpa using mem_closedBall.1 x.2
  have hx : (x : ℂ) ∈ closure (ball (0 : ℂ) (S.R + 1)) :=
    subset_closure (mem_ball.2 (by simpa using (lt_of_le_of_lt hxR (by linarith))))
  have hxR' : (x : ℂ) ∈ closedBall (0 : ℂ) (|S.R| + 1) := by
    rw [mem_closedBall, dist_zero_right]; linarith [le_abs_self S.R]
  have key := hn (e n).2 x hx
  have key2 := hn2 x hxR'
  have hren : heatMollify (e n) (S.ren g) x = heatMollify (e n) g x + -S.cA g :=
    heatMollify_addConst_of_tendsto (e n).2.ne' ((tendstoLocallyUniformlyOn_univ.2 (ht n).1).tendsto_at (mem_univ (x : ℂ))) _
  have hN2 : heatMollify (e n) (S.N2 g₀ g) x =
      heatMollify (e n) (S.ren g) x - heatMollify (e n) (ofCont (S.Fb g₀ g)) x :=
    l6_heatMollify_sub_ofCont (e n).2.ne' ((tendstoLocallyUniformlyOn_univ.2 (ht' n).1).tendsto_at (mem_univ (x : ℂ))) _ M hM
  simp only [l6Res_apply, ContinuousMap.sub_apply, ContinuousMap.const_apply, Real.norm_eq_abs]
  change |locMollify (e n) (e n).2 (S.N2 g₀ g) x - (V (e n) g x - S.cA g - S.Fb g₀ g x)| ≤ a / 2
  rw [hv n x]
  rw [Real.dist_eq] at key2
  have e1 : locMollify (e n) (e n).2 (S.N2 g₀ g) x - (heatMollify (e n) g x - S.cA g -
      S.Fb g₀ g x) = (locMollify (e n) (e n).2 (S.N2 g₀ g) x - heatMollify (e n) (S.N2 g₀ g) x) +
        (S.Fb g₀ g x - heatMollify (e n) (ofCont (S.Fb g₀ g)) x) := by
    rw [hN2, hren]; ring
  rw [e1]
  refine (abs_add_le _ _).trans ?_
  rw [abs_sub_comm] at key
  have : a / 4 + a / 4 = a / 2 := by ring
  linarith [key2.le]

 
theorem l6_prob_of_ae {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {μ : Measure DistC} [IsProbabilityMeasure μ]
    {E : ℕ → DistC → ℝ} (hEm : ∀ n, Measurable (E n))
    (h : ∀ᵐ g ∂μ, Tendsto (fun n => E n g) atTop (𝓝 0)) {hN : ℕ → Ω' → DistC}
    (hNm : ∀ n, Measurable (hN n)) (hNlaw : ∀ n, P'.map (hN n) = μ) :
    ∀ δ : ℝ, 0 < δ → Tendsto (fun n => P' {ω | δ ≤ |E n (hN n ω)|}) atTop (𝓝 0) := by
  intro δ hδ
  have hT := tendstoInMeasure_of_tendsto_ae (fun n => (hEm n).aestronglyMeasurable) h
  have h1 := hT (ENNReal.ofReal δ) (ENNReal.ofReal_pos.2 hδ)
  refine h1.congr fun n => ?_
  have hs : MeasurableSet {g : DistC | δ ≤ |E n g|} :=
    measurableSet_le measurable_const (hEm n).abs
  have e1 : {g : DistC | ENNReal.ofReal δ ≤ edist (E n g) 0} = {g | δ ≤ |E n g|} := by
    ext g
    simp only [mem_ofPred_eq, edist_dist, Real.dist_eq, sub_zero]
    exact ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)
  rw [e1, ← hNlaw n, Measure.map_apply (hNm n) hs]
  rfl

 
theorem l6_prob_comp {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {μ : Measure DistC} [IsProbabilityMeasure μ]
    {h' : Ω' → DistC} (hh'm : Measurable h') (hh'law : P'.map h' = μ)
    {hN : ℕ → Ω' → DistC} (hNm : ∀ n, Measurable (hN n)) (hNlaw : ∀ n, P'.map (hN n) = μ)
    (hpair : ∀ᵐ ω ∂P', Tendsto (fun n => pairJ ⊤ (hN n ω)) atTop (𝓝 (pairJ ⊤ (h' ω))))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (T : DistC → E) (hT : Measurable T) :
    ∀ δ : ℝ, 0 < δ → Tendsto (fun n => P' {ω | δ ≤ |‖T (hN n ω) - T (h' ω)‖|}) atTop (𝓝 0) := by
  intro δ hδ
  have hX : Measurable (pairJ ⊤ : DistC → L6S) := measurable_pairJ ⊤
  have hlaw : ∀ n, P'.map (fun ω => pairJ ⊤ (hN n ω)) = μ.map (pairJ ⊤) := fun n => by
    rw [← hNlaw n, Measure.map_map hX (hNm n)]; rfl
  have hlaw₀ : P'.map (fun ω => pairJ ⊤ (h' ω)) = μ.map (pairJ ⊤) := by
    rw [← hh'law, Measure.map_map hX hh'm]; rfl
  have H := l6_tendstoInMeasure_comp (μ := μ.map (pairJ ⊤)) P' (fun n ω => pairJ ⊤ (hN n ω))
    (fun ω => pairJ ⊤ (h' ω)) (fun n => hX.comp (hNm n)) (hX.comp hh'm) hlaw hlaw₀ hpair
    (fun x => T (pairJInv ⊤ x)) (hT.comp (measurable_pairJInv ⊤)) δ hδ
  refine H.congr fun n => ?_
  congr 1; ext ω
  simp only [mem_ofPred_eq, pairJInv_pairJ, abs_norm]
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)

end SupercriticalLQGUniqueness.B2.PfeLocal
