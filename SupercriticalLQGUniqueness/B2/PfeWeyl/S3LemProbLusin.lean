import SupercriticalLQGUniqueness.B2.PfeWeyl.S3LemProb
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Topology.UniformSpace.UniformConvergence

 














set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal NNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

variable {S T : Type*} [PseudoMetricSpace S] [PseudoMetricSpace T]

 
def lusinInf (K : Set S) (Φ : S → T) (C : ℝ) (x : S) (y : T) : ℝ :=
  ⨅ x' : K, (min (dist y (Φ x')) 1 + C * dist x x')

 
def lusinTest (K : Set S) (Φ : S → T) (C : ℝ) (x : S) (y : T) : ℝ :=
  min 1 (lusinInf K Φ C x y)

theorem lusinInf_term_nonneg {K : Set S} {Φ : S → T} {C : ℝ} (hC : 0 ≤ C) (x : S) (y : T)
    (x' : K) : 0 ≤ min (dist y (Φ x')) 1 + C * dist x x' :=
  add_nonneg (le_min dist_nonneg zero_le_one) (mul_nonneg hC dist_nonneg)

theorem lusinInf_bddBelow {K : Set S} {Φ : S → T} {C : ℝ} (hC : 0 ≤ C) (x : S) (y : T) :
    BddBelow (range fun x' : K => min (dist y (Φ x')) 1 + C * dist x x') :=
  ⟨0, by rintro _ ⟨x', rfl⟩; exact lusinInf_term_nonneg hC x y x'⟩

theorem lusinInf_nonneg {K : Set S} {Φ : S → T} {C : ℝ} (hC : 0 ≤ C) (x : S) (y : T) :
    0 ≤ lusinInf K Φ C x y := by
  rcases isEmpty_or_nonempty K with hK | hK
  · simp [lusinInf]
  · exact le_ciInf fun x' => lusinInf_term_nonneg hC x y x'

theorem lusinTest_nonneg {K : Set S} {Φ : S → T} {C : ℝ} (hC : 0 ≤ C) (x : S) (y : T) :
    0 ≤ lusinTest K Φ C x y :=
  le_min zero_le_one (lusinInf_nonneg hC x y)

theorem lusinTest_le_one {K : Set S} {Φ : S → T} {C : ℝ} (x : S) (y : T) :
    lusinTest K Φ C x y ≤ 1 := min_le_left _ _

 
theorem lusinTest_graph {K : Set S} {Φ : S → T} {C : ℝ} (hC : 0 ≤ C) {x : S} (hx : x ∈ K) :
    lusinTest K Φ C x (Φ x) = 0 := by
  have hle : lusinInf K Φ C x (Φ x) ≤ 0 := by
    have := ciInf_le (lusinInf_bddBelow (K := K) (Φ := Φ) hC x (Φ x)) ⟨x, hx⟩
    simpa [lusinInf] using this
  exact le_antisymm ((min_le_right _ _).trans hle) (lusinTest_nonneg hC x (Φ x))

 
theorem lusinInf_le_add {K : Set S} {Φ : S → T} {C : ℝ} (hC : 0 ≤ C) (hK : K.Nonempty)
    (x₁ x₂ : S) (y₁ y₂ : T) :
    lusinInf K Φ C x₁ y₁ ≤ lusinInf K Φ C x₂ y₂ + (dist y₁ y₂ + C * dist x₁ x₂) := by
  have : Nonempty K := hK.to_subtype
  rw [← sub_le_iff_le_add]
  refine le_ciInf fun x' => ?_
  rw [sub_le_iff_le_add]
  refine (ciInf_le (lusinInf_bddBelow hC x₁ y₁) x').trans ?_
  have h1 : min (dist y₁ (Φ x')) 1 ≤ min (dist y₂ (Φ x')) 1 + dist y₁ y₂ := by
    have := dist_triangle y₁ y₂ (Φ x')
    rcases le_total (dist y₂ (Φ x')) 1 with h | h
    · rw [min_eq_left h]
      exact (min_le_left _ _).trans (by linarith)
    · rw [min_eq_right h]
      exact (min_le_right _ _).trans (by linarith [dist_nonneg (x := y₁) (y := y₂)])
  have h2 : C * dist x₁ x' ≤ C * dist x₂ x' + C * dist x₁ x₂ := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (by linarith [dist_triangle x₁ x₂ x', dist_comm x₁ x₂]) hC
  linarith

 
theorem continuous_lusinTest {K : Set S} {Φ : S → T} {C : ℝ} (hC : 0 ≤ C) (hK : K.Nonempty) :
    Continuous (fun p : S × T => lusinTest K Φ C p.1 p.2) := by
  refine continuous_const.min ?_
  refine Metric.continuous_iff.2 fun p ε hε => ⟨ε / (1 + C), by positivity, fun q hq => ?_⟩
  have hd1 : dist q.1 p.1 ≤ dist q p := by rw [Prod.dist_eq]; exact le_max_left _ _
  have hd2 : dist q.2 p.2 ≤ dist q p := by rw [Prod.dist_eq]; exact le_max_right _ _
  have hbound : dist q.2 p.2 + C * dist q.1 p.1 ≤ (1 + C) * dist q p := by
    have := mul_le_mul_of_nonneg_left hd1 hC
    nlinarith
  have hsmall : (1 + C) * dist q p < ε := by
    rw [lt_div_iff₀ (by positivity)] at hq
    linarith
  rw [Real.dist_eq, abs_lt]
  have a1 := lusinInf_le_add (Φ := Φ) hC hK q.1 p.1 q.2 p.2
  have a2 := lusinInf_le_add (Φ := Φ) hC hK p.1 q.1 p.2 q.2
  rw [dist_comm p.2 q.2, dist_comm p.1 q.1] at a2
  constructor <;> linarith

 

theorem lusinTest_ge_of_far {K : Set S} {Φ : S → T} {a η : ℝ} (ha1 : a ≤ 1)
    (hη : 0 < η) (hunif : ∀ x ∈ K, ∀ x' ∈ K, dist x x' < η → dist (Φ x) (Φ x') < a / 2)
    {x : S} (hx : x ∈ K) {y : T} (hy : a ≤ dist y (Φ x)) :
    a / 2 ≤ lusinTest K Φ (1 / η) x y := by
  have hC : 0 ≤ 1 / η := by positivity
  refine le_min (by linarith) ?_
  have : Nonempty K := ⟨⟨x, hx⟩⟩
  refine le_ciInf fun x' => ?_
  by_cases hxx : dist x x' < η
  · have hΦ := hunif x hx x' x'.property hxx
    have htri := dist_triangle y (Φ x') (Φ x)
    rw [dist_comm (Φ x') (Φ x)] at htri
    have hmin : a / 2 ≤ min (dist y (Φ x')) 1 := le_min (by linarith) (by linarith)
    linarith [mul_nonneg hC (dist_nonneg (x := x) (y := x'))]
  · push Not at hxx
    have hge : 1 ≤ 1 / η * dist x x' := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hη]
      linarith
    linarith [le_min (dist_nonneg (x := y) (y := Φ x')) zero_le_one]

 
theorem tendstoInMeasure_of_coupling_lusin
    [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
    [MeasurableSpace T] [BorelSpace T] [SecondCountableTopology T]
    (μ : Measure S) [IsProbabilityMeasure μ] (R : ℕ → S → T) (Φ : S → T)
    (hR : ∀ n, Measurable (R n))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : ℕ → Ω' → S) (Xl : Ω' → S) (hXm : ∀ n, Measurable (X n)) (hXlm : Measurable Xl)
    (hXlaw : ∀ n, P'.map (X n) = μ) (hXllaw : P'.map Xl = μ)
    (Y : ℕ → Ω' → T) (hYm : ∀ n, Measurable (Y n)) (hY : ∀ n, Y n =ᵐ[P'] R n ∘ X n)
    (hXconv : ∀ᵐ ω ∂P', Tendsto (fun n => X n ω) atTop (𝓝 (Xl ω)))
    (hYconv : ∀ᵐ ω ∂P', Tendsto (fun n => Y n ω) atTop (𝓝 (Φ (Xl ω))))
    (hlusin : ∀ κ : ℝ≥0∞, 0 < κ → ∃ K : Set S, IsClosed K ∧ μ Kᶜ < κ ∧
      ∀ a : ℝ, 0 < a → ∃ η : ℝ, 0 < η ∧
        ∀ x ∈ K, ∀ x' ∈ K, dist x x' < η → dist (Φ x) (Φ x') < a) :
    TendstoInMeasure μ R atTop Φ := by
  refine tendstoInMeasure_of_ne_top fun ε hε hεtop => ?_
  rw [ENNReal.tendsto_nhds_zero]
  intro κ hκ
  set a : ℝ := min ε.toReal 1 with hadef
  have ha : 0 < a := lt_min (ENNReal.toReal_pos hε.ne' hεtop) one_pos
  have ha1 : a ≤ 1 := min_le_right _ _
  set b : ℝ≥0∞ := ENNReal.ofReal (a / 2) with hbdef
  have hb0 : b ≠ 0 := (ENNReal.ofReal_pos.2 (half_pos ha)).ne'
  have hbtop : b ≠ ⊤ := ENNReal.ofReal_ne_top
  set κ₂ : ℝ≥0∞ := b * (κ / 2 / 2) with hκ₂def
  have hκ₂ : 0 < κ₂ := ENNReal.mul_pos hb0 (ENNReal.half_pos (ENNReal.half_pos hκ.ne').ne').ne'
  obtain ⟨K, hKc, hKμ, hunif⟩ := hlusin (min (κ / 2) κ₂)
    (lt_min (ENNReal.half_pos hκ.ne') hκ₂)
  have hKμ1 : μ Kᶜ ≤ κ / 2 := hKμ.le.trans (min_le_left _ _)
  have hKμ2 : μ Kᶜ ≤ κ₂ := hKμ.le.trans (min_le_right _ _)
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine Eventually.of_forall fun n => ?_
    have h1 : μ Kᶜ = 1 := by rw [hKe, compl_empty, measure_univ]
    calc μ {x | ε ≤ edist (R n x) (Φ x)} ≤ 1 := prob_le_one
      _ = μ Kᶜ := h1.symm
      _ ≤ κ / 2 := hKμ1
      _ ≤ κ := ENNReal.half_le_self
  obtain ⟨η, hη, hηK⟩ := hunif (a / 2) (half_pos ha)
  have hC : (0 : ℝ) ≤ 1 / η := by positivity
  set F : S → T → ℝ := lusinTest K Φ (1 / η) with hFdef
  have hFc : Continuous (fun p : S × T => F p.1 p.2) := continuous_lusinTest hC hKne
  have hF1 : ∀ x y, F x y ≤ 1 := fun x y => lusinTest_le_one x y
  have hF0 : ∀ x ∈ K, F x (Φ x) = 0 := fun x hx => lusinTest_graph hC hx
  have hFfar : ∀ x ∈ K, ∀ y, a ≤ dist y (Φ x) → a / 2 ≤ F x y := fun x hx y hy =>
    lusinTest_ge_of_far ha1 hη hηK hx hy
  clear_value F
  have hFm : Measurable (fun p : S × T => F p.1 p.2) := hFc.measurable
  have hFmn : ∀ n, Measurable (fun ω => ENNReal.ofReal (F (X n ω) (Y n ω))) := fun n =>
    (hFm.comp ((hXm n).prodMk (hYm n))).ennreal_ofReal
  have hFmR : ∀ n, Measurable (fun x => ENNReal.ofReal (F x (R n x))) := fun n =>
    (hFm.comp (measurable_id.prodMk (hR n))).ennreal_ofReal
  
  have hdom : Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal (F (X n ω) (Y n ω)) ∂P') atTop
      (𝓝 (∫⁻ ω, ENNReal.ofReal (F (Xl ω) (Φ (Xl ω))) ∂P')) := by
    refine tendsto_lintegral_of_dominated_convergence (fun _ => 1) (fun n => ?_)
      (fun n => Eventually.of_forall fun ω => ?_) (by simp) ?_
    · exact hFmn n
    · exact ENNReal.ofReal_le_one.2 (hF1 _ _)
    · filter_upwards [hXconv, hYconv] with ω h1 h2
      exact (ENNReal.continuous_ofReal.tendsto _).comp
        ((hFc.tendsto (Xl ω, Φ (Xl ω))).comp (h1.prodMk_nhds h2))
  have hlimle : (∫⁻ ω, ENNReal.ofReal (F (Xl ω) (Φ (Xl ω))) ∂P') ≤ μ Kᶜ := by
    have hmeasK : MeasurableSet Kᶜ := hKc.measurableSet.compl
    calc (∫⁻ ω, ENNReal.ofReal (F (Xl ω) (Φ (Xl ω))) ∂P')
        ≤ ∫⁻ ω, (Xl ⁻¹' Kᶜ).indicator 1 ω ∂P' := by
          refine lintegral_mono fun ω => ?_
          by_cases hω : Xl ω ∈ K
          · rw [hF0 _ hω, ENNReal.ofReal_zero]
            exact zero_le
          · have hmem : ω ∈ Xl ⁻¹' Kᶜ := hω
            rw [Set.indicator_of_mem hmem]
            exact ENNReal.ofReal_le_one.2 (hF1 _ _)
      _ = P' (Xl ⁻¹' Kᶜ) := lintegral_indicator_one (hXlm hmeasK)
      _ = μ Kᶜ := by rw [← Measure.map_apply hXlm hmeasK, hXllaw]
  have hev : ∀ᶠ n in atTop, (∫⁻ ω, ENNReal.ofReal (F (X n ω) (Y n ω)) ∂P') < μ Kᶜ + κ₂ :=
    (tendsto_order.1 hdom).2 _ (lt_of_le_of_lt hlimle (ENNReal.lt_add_right
      (measure_ne_top μ _) hκ₂.ne'))
  filter_upwards [hev] with n hn
  
  have hint : (∫⁻ x, ENNReal.ofReal (F x (R n x)) ∂μ) =
      ∫⁻ ω, ENNReal.ofReal (F (X n ω) (Y n ω)) ∂P' := by
    rw [← hXlaw n, lintegral_map (hFmR n) (hXm n)]
    refine lintegral_congr_ae ?_
    filter_upwards [hY n] with ω hω
    rw [hω]
    rfl
  
  have hmarkov : μ {x | b ≤ ENNReal.ofReal (F x (R n x))} ≤
      (∫⁻ x, ENNReal.ofReal (F x (R n x)) ∂μ) / b :=
    meas_ge_le_lintegral_div (hFmR n).aemeasurable hb0 hbtop
  have hsub : {x | ε ≤ edist (R n x) (Φ x)} ⊆ Kᶜ ∪ {x | b ≤ ENNReal.ofReal (F x (R n x))} := by
    intro x hx
    by_cases hxK : x ∈ K
    · right
      have hdist : a ≤ dist (R n x) (Φ x) := by
        have h1 : ε ≤ ENNReal.ofReal (dist (R n x) (Φ x)) := by
          rw [← edist_dist]
          exact hx
        have h2 : ε.toReal ≤ dist (R n x) (Φ x) :=
          (ENNReal.toReal_le_toReal hεtop ENNReal.ofReal_ne_top).2 h1 |>.trans_eq
            (ENNReal.toReal_ofReal dist_nonneg)
        exact (min_le_left _ _).trans h2
      exact ENNReal.ofReal_le_ofReal (hFfar x hxK _ hdist)
    · exact Or.inl hxK
  calc μ {x | ε ≤ edist (R n x) (Φ x)}
      ≤ μ Kᶜ + μ {x | b ≤ ENNReal.ofReal (F x (R n x))} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ κ / 2 + (μ Kᶜ + κ₂) / b := by
        gcongr
        rw [← hint] at hn
        exact hmarkov.trans (ENNReal.div_le_div_right hn.le b)
    _ ≤ κ / 2 + (κ₂ + κ₂) / b := by gcongr
    _ = κ := by
        rw [hκ₂def, ← mul_add, ENNReal.add_halves, mul_comm b,
          ENNReal.mul_div_cancel_right hb0 hbtop, ENNReal.add_halves]

 

theorem exists_subseq_ae_of_coupling_lusin
    [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
    [MeasurableSpace T] [BorelSpace T] [SecondCountableTopology T]
    (μ : Measure S) [IsProbabilityMeasure μ] (R : ℕ → S → T) (Φ : S → T)
    (hR : ∀ n, Measurable (R n))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : ℕ → Ω' → S) (Xl : Ω' → S) (hXm : ∀ n, Measurable (X n)) (hXlm : Measurable Xl)
    (hXlaw : ∀ n, P'.map (X n) = μ) (hXllaw : P'.map Xl = μ)
    (Y : ℕ → Ω' → T) (hYm : ∀ n, Measurable (Y n)) (hY : ∀ n, Y n =ᵐ[P'] R n ∘ X n)
    (hXconv : ∀ᵐ ω ∂P', Tendsto (fun n => X n ω) atTop (𝓝 (Xl ω)))
    (hYconv : ∀ᵐ ω ∂P', Tendsto (fun n => Y n ω) atTop (𝓝 (Φ (Xl ω))))
    (hlusin : ∀ κ : ℝ≥0∞, 0 < κ → ∃ K : Set S, IsClosed K ∧ μ Kᶜ < κ ∧
      ∀ a : ℝ, 0 < a → ∃ η : ℝ, 0 < η ∧
        ∀ x ∈ K, ∀ x' ∈ K, dist x x' < η → dist (Φ x) (Φ x') < a) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → S), AEMeasurable h P →
        P.map h = μ → ∀ᵐ ω ∂P, Tendsto (fun k => R (ns k) (h ω)) atTop (𝓝 (Φ (h ω))) := by
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_coupling_lusin μ R Φ hR P' X Xl hXm hXlm
    hXlaw hXllaw Y hYm hY hXconv hYconv hlusin).exists_seq_tendsto_ae
  refine ⟨ns, hns, fun P h hh hlaw => ?_⟩
  rw [← hlaw] at hae
  exact ae_of_ae_map hh hae

end SupercriticalLQGUniqueness.B2.PfeWeyl
