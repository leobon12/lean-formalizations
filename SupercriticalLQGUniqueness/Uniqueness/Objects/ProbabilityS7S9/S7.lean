import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS1S2.Bridges
import SLUFieldSupport
import SLUMetricAPI2
import NV1Evidence
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.CountableBase.Annulus




 




















set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS7S9

open LQGMetric (DistC circleAvg)

 

 



theorem around_eq_aroundDist (D : LSCMetric) (w : ℂ) (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    Objects.CorrectedEvent.around D w a b = aroundDist D ⟨(w, a, b), ha, hab⟩ := by
  refine le_antisymm (Objects.ProbabilityS1S2.around_le_aroundDist D w a b ha hab) ?_
  unfold Objects.CorrectedEvent.around
  refine le_iInf fun P => le_iInf fun t => le_iInf fun u =>
    le_iInf fun hcurve => le_iInf fun htrace => le_iInf fun hsep => ?_
  set A : EuclideanAnnulus := ⟨(w, a, b), ha, hab⟩ with hAdef
  have htrace' : ∀ s ∈ Icc t u, P s ∈ A.toSet := by
    intro s hs
    have hmem : P s ∈ Objects.CorrectedEvent.ann w a b := htrace ⟨s, hs, rfl⟩
    change P s ∈ ball w b \ closure (ball w a)
    rw [closure_ball _ ha.ne']
    simp only [Objects.CorrectedEvent.ann, mem_ofPred_eq] at hmem
    exact ⟨mem_ball.mpr hmem.2, fun h => absurd (mem_closedBall.mp h) (not_le.mpr hmem.1)⟩
  have hsep' : Disconnects (P '' Icc t u) A.innerBoundary A.outerBoundary :=
    (disconnects_iff_lqgMetric_disconnects hcurve.isClosed_image).mpr hsep
  unfold aroundDist
  exact iInf_le_of_le P (iInf_le_of_le t (iInf_le_of_le u (iInf_le_of_le hcurve
    (iInf_le_of_le htrace' (iInf_le_of_le hsep' le_rfl)))))

 
theorem measurable_around_comp {D : DistC → LSCMetric} (hD : Measurable D) (w : ℂ) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    Measurable fun g => Objects.CorrectedEvent.around (D g) w a b := by
  have heq : (fun g => Objects.CorrectedEvent.around (D g) w a b) =
      fun g => aroundDist (D g) ⟨(w, a, b), ha, hab⟩ := by
    funext g
    exact around_eq_aroundDist (D g) w a b ha hab
  rw [heq]
  exact (Toolkit.CountableBase.aroundBoundedAnnulus_borel _).comp hD

 
theorem measurable_normalizer (C : Objects.CorrectedEvent.Constants) (s : ℝ) (w : ℂ) :
    Measurable fun g : DistC => Objects.CorrectedEvent.normalizer C g s w := by
  unfold Objects.CorrectedEvent.normalizer
  exact ENNReal.measurable_ofReal.comp (measurable_const.mul
    (Real.measurable_exp.comp (measurable_const.mul (LQGMetric.measurable_circleAvg_left s w))))

 
theorem measurableSet_S7 {D : DistC → LSCMetric} (hD : Measurable D) (C : Objects.CorrectedEvent.Constants)
    (T : Objects.CorrectedEvent.TubeData) (hT : 0 < T.netRadius) :
    MeasurableSet {g : DistC | Objects.CorrectedEvent.S7 C T (D g) g} := by
  have hset : {g : DistC | Objects.CorrectedEvent.S7 C T (D g) g} = ⋂ x ∈ T.netSites,
      {g : DistC | Objects.CorrectedEvent.around (D g) x T.netRadius (2 * T.netRadius) <
        ENNReal.ofReal (C.A_internal / (2 * T.netSites.card)) * Objects.CorrectedEvent.normalizer C g C.r 0} := by
    ext g
    simp only [Objects.CorrectedEvent.S7, mem_ofPred_eq, mem_iInter]
  rw [hset]
  refine Finset.measurableSet_biInter _ fun x _ => ?_
  exact measurableSet_lt (measurable_around_comp hD x hT (by linarith))
    (measurable_const.mul (measurable_normalizer C C.r 0))

 

 
theorem normalizer_mul_inv (ξ Q r c : ℝ) (hr : 0 < r) :
    ENNReal.ofReal (r ^ (ξ * Q) * Real.exp (ξ * c)) *
      ENNReal.ofReal (r ^ (-(ξ * Q)) * Real.exp (-(ξ * c))) = 1 := by
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one]
  congr 1
  rw [Real.rpow_neg hr.le, Real.exp_neg]
  have h1 : r ^ (ξ * Q) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
  have h2 : Real.exp (ξ * c) ≠ 0 := (Real.exp_pos _).ne'
  field_simp

 

 
def netShape (ρ' : ℝ) (hρ : 0 < ρ') (x' : ℂ) : EuclideanAnnulus :=
  ⟨(x', ρ', 2 * ρ'), hρ, by linarith⟩

 
theorem netShape_dilate (ρ' : ℝ) (hρ : 0 < ρ') (x' : ℂ) {r : ℝ} (hr : 0 < r) :
    (netShape ρ' hρ x').dilate r hr =
      (⟨((r : ℂ) * x', ρ' * r, 2 * (ρ' * r)), mul_pos hρ hr, by nlinarith⟩ : EuclideanAnnulus) := by
  apply Subtype.ext
  change (r • x', r * ρ', r * (2 * ρ')) = ((r : ℂ) * x', ρ' * r, 2 * (ρ' * r))
  rw [Complex.real_smul]
  congr 1
  congr 1 <;> ring

 
theorem around_le_netShape (D : LSCMetric) (ρ' : ℝ) (hρ : 0 < ρ') (x' : ℂ) {r : ℝ}
    (hr : 0 < r) :
    Objects.CorrectedEvent.around D ((r : ℂ) * x') (ρ' * r) (2 * (ρ' * r)) ≤
      aroundDist D ((netShape ρ' hρ x').dilate r hr) := by
  rw [netShape_dilate ρ' hρ x' hr]
  exact Objects.ProbabilityS1S2.around_le_aroundDist D _ _ _ (mul_pos hρ hr) (by nlinarith)

 

 




theorem exists_s7_shape_budget (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (ε : ℝ) (hε : 0 < ε) (ρ' : ℝ) (hρ : 0 < ρ') (X' : Finset ℂ) :
    ∃ A : ℝ, 0 < A ∧ ∀ C : Objects.CorrectedEvent.Constants, ∀ T : Objects.CorrectedEvent.TubeData, C.ξ = ξ → C.Q = Q →
      T.netRadius = ρ' * C.r → T.netSites = X'.image (fun x => (C.r : ℂ) * x) →
      A ≤ C.A_internal → μ {g | ¬ Objects.CorrectedEvent.S7 C T (D g) g} ≤ ENNReal.ofReal ε := by
  classical
  
  let Y : ℂ → Ioi (0 : ℝ) → DistC → ℝ≥0∞ := fun x' r g =>
    ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) * Real.exp (-((ξ : ℝ) * circleAvg g r 0))) *
      aroundDist (D g) ((netShape ρ' hρ x').dilate r r.2)
  have hY : ∀ x' : ℂ, IsTwoSidedTight μ (Y x') := fun x' =>
    (hD.tightness μ id hμ (fun r g => circleAvg g r 0)
      (fun r => ae_isCircleAverage_old hμ.1 r 0) (netShape ρ' hρ x')).2
  set n : ℕ := X'.card with hndef
  have hε' : 0 < ε / ((n : ℝ) + 1) := by positivity
  have hM : ∀ x' : ℂ, ∃ M : ℝ, 0 < M ∧ ∀ r : Ioi (0 : ℝ),
      μ {g | ENNReal.ofReal M < Y x' r g} ≤ ENNReal.ofReal (ε / ((n : ℝ) + 1)) := by
    intro x'
    obtain ⟨M, hM0, hMr⟩ := (hY x').2 _ hε'
    exact ⟨M, hM0, fun r => (hMr r).1⟩
  choose M hM0 hMr using hM
  set Msum : ℝ := ∑ x' ∈ X', M x' with hMsum
  have hMsum0 : 0 ≤ Msum := Finset.sum_nonneg fun x' _ => (hM0 x').le
  have hMle : ∀ x' ∈ X', M x' ≤ Msum := fun x' hx' =>
    Finset.single_le_sum (fun y _ => (hM0 y).le) hx'
  refine ⟨2 * ((n : ℝ) + 1) * (Msum + 1), by positivity, ?_⟩
  intro C T hξ hQ hrad hsites hA
  have hr : 0 < C.r := C.rPos
  set r : Ioi (0 : ℝ) := ⟨C.r, hr⟩ with hrdef
  
  have hinj : Function.Injective (fun x : ℂ => (C.r : ℂ) * x) := by
    intro x y hxy
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne') hxy
  have hcard : T.netSites.card = n := by
    rw [hsites, Finset.card_image_of_injective _ hinj]
  
  have hsub : {g : DistC | ¬ Objects.CorrectedEvent.S7 C T (D g) g} ⊆
      ⋃ x' ∈ X', {g | ENNReal.ofReal (M x') < Y x' r g} := by
    intro g hg
    simp only [Objects.CorrectedEvent.S7, mem_ofPred_eq, not_forall, not_lt] at hg
    obtain ⟨x, hx, hbad⟩ := hg
    rw [hsites, Finset.mem_image] at hx
    obtain ⟨x', hx', rfl⟩ := hx
    simp only [mem_iUnion, mem_ofPred_eq]
    refine ⟨x', hx', ?_⟩
    have hn0 : 0 < n := by
      rw [hndef]
      exact Finset.card_pos.mpr ⟨x', hx'⟩
    rw [hcard] at hbad
    rw [hrad] at hbad
    set N : ℝ≥0∞ := Objects.CorrectedEvent.normalizer C g C.r 0 with hNdef
    set ninv : ℝ≥0∞ := ENNReal.ofReal ((C.r : ℝ) ^ (-((ξ : ℝ) * Q)) *
      Real.exp (-((ξ : ℝ) * circleAvg g C.r 0))) with hninv
    have hNn : N * ninv = 1 := by
      rw [hNdef, hninv]
      unfold Objects.CorrectedEvent.normalizer
      rw [hξ, hQ]
      exact normalizer_mul_inv (ξ : ℝ) Q C.r (circleAvg g C.r 0) hr
    
    have hthr : M x' < C.A_internal / (2 * (n : ℝ)) := by
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
      rw [lt_div_iff₀ (by positivity)]
      have hMx := hMle x' hx'
      nlinarith
    have hYge : ENNReal.ofReal (C.A_internal / (2 * (n : ℝ))) ≤ Y x' r g := by
      have h1 : Objects.CorrectedEvent.around (D g) ((C.r : ℂ) * x') (ρ' * C.r) (2 * (ρ' * C.r)) ≤
          aroundDist (D g) ((netShape ρ' hρ x').dilate r r.2) :=
        around_le_netShape (D g) ρ' hρ x' hr
      calc ENNReal.ofReal (C.A_internal / (2 * (n : ℝ)))
          = ENNReal.ofReal (C.A_internal / (2 * (n : ℝ))) * N * ninv := by
            rw [mul_assoc, hNn, mul_one]
        _ ≤ Objects.CorrectedEvent.around (D g) ((C.r : ℂ) * x') (ρ' * C.r) (2 * (ρ' * C.r)) * ninv := by
            gcongr
        _ ≤ aroundDist (D g) ((netShape ρ' hρ x').dilate r r.2) * ninv := by gcongr
        _ = Y x' r g := by
            rw [mul_comm]
    exact lt_of_lt_of_le (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (hM0 x').le |>.mpr hthr) hYge
  calc μ {g : DistC | ¬ Objects.CorrectedEvent.S7 C T (D g) g}
      ≤ μ (⋃ x' ∈ X', {g | ENNReal.ofReal (M x') < Y x' r g}) := measure_mono hsub
    _ ≤ ∑ x' ∈ X', μ {g | ENNReal.ofReal (M x') < Y x' r g} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _x' ∈ X', ENNReal.ofReal (ε / ((n : ℝ) + 1)) :=
        Finset.sum_le_sum fun x' _ => hMr x' r
    _ = (n : ℝ≥0∞) * ENNReal.ofReal (ε / ((n : ℝ) + 1)) := by
        rw [Finset.sum_const, nsmul_eq_mul, hndef]
    _ ≤ ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        rw [mul_div_assoc']
        rw [div_le_iff₀ (by positivity)]
        nlinarith

 






theorem exists_s7_budget (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (pbar : Ioo (0 : ℝ) 1) (𝒩 : Finset (ℝ × Finset ℂ)) (h𝒩 : ∀ s ∈ 𝒩, 0 < s.1) :
    ∃ A : ℝ, 0 < A ∧ ∀ C : Objects.CorrectedEvent.Constants, ∀ T : Objects.CorrectedEvent.TubeData, C.ξ = ξ → C.Q = Q →
      (∃ s ∈ 𝒩, T.netRadius = s.1 * C.r ∧
        T.netSites = s.2.image (fun x => (C.r : ℂ) * x)) →
      A ≤ C.A_internal →
      μ {g | ¬ Objects.CorrectedEvent.S7 C T (D g) g} ≤ ENNReal.ofReal ((1 - (pbar : ℝ)) / 10) := by
  classical
  have hε : 0 < (1 - (pbar : ℝ)) / 10 := by linarith [pbar.2.2]
  have key : ∀ s : ℝ × Finset ℂ, ∃ A : ℝ, 0 < A ∧ ∀ hs : 0 < s.1, ∀ C : Objects.CorrectedEvent.Constants,
      ∀ T : Objects.CorrectedEvent.TubeData, C.ξ = ξ → C.Q = Q →
      T.netRadius = s.1 * C.r → T.netSites = s.2.image (fun x => (C.r : ℂ) * x) →
      A ≤ C.A_internal →
      μ {g | ¬ Objects.CorrectedEvent.S7 C T (D g) g} ≤ ENNReal.ofReal ((1 - (pbar : ℝ)) / 10) := by
    intro s
    by_cases hs : 0 < s.1
    · obtain ⟨A, hA0, hA⟩ := exists_s7_shape_budget μ hμ ξ Q D hD _ hε s.1 hs s.2
      exact ⟨A, hA0, fun _ => hA⟩
    · exact ⟨1, one_pos, fun h => absurd h hs⟩
  choose A hA0 hA using key
  refine ⟨∑ s ∈ 𝒩, A s + 1, by
    have := Finset.sum_nonneg fun s (_ : s ∈ 𝒩) => (hA0 s).le
    linarith, ?_⟩
  intro C T hξ hQ ⟨s, hs𝒩, hrad, hsites⟩ hAint
  have hle : A s ≤ C.A_internal := by
    have h1 : A s ≤ ∑ s ∈ 𝒩, A s := Finset.single_le_sum (fun t _ => (hA0 t).le) hs𝒩
    linarith
  exact hA s (h𝒩 s hs𝒩) C T hξ hQ hrad hsites hle


end SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS7S9
