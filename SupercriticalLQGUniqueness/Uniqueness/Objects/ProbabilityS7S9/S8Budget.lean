import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS7S9.S8Cell




 





















set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS7S9

open LQGMetric (DistC)

 

theorem numCells_pos (C : Objects.CorrectedEvent.Constants) {s : ℝ} (hs : 0 < s) : 0 < Objects.CorrectedEvent.numCells C s := by
  unfold Objects.CorrectedEvent.numCells
  have hR : 0 < Objects.CorrectedEvent.supRadius C 1 := by
    unfold Objects.CorrectedEvent.supRadius
    have := C.supPos
    have := C.rPos
    positivity
  have harg : 0 < 2 * Real.pi / ((1 / 20 : ℝ) * Objects.CorrectedEvent.supRadius C 1 / (4 * s)) := by
    have := Real.pi_pos
    positivity
  exact Nat.ceil_pos.mpr harg

theorem circleCell_width (C : Objects.CorrectedEvent.Constants) (s : ℝ) (l : ℕ) :
    (Objects.CorrectedEvent.circleCell C s l).hi - (Objects.CorrectedEvent.circleCell C s l).lo =
      2 * Real.pi / (Objects.CorrectedEvent.numCells C s : ℝ) := by
  simp only [Objects.CorrectedEvent.circleCell]
  push_cast
  ring

 
theorem cell_widths_sum (C : Objects.CorrectedEvent.Constants) {s : ℝ} (hs : 0 < s) :
    ∑ l ∈ Finset.range (Objects.CorrectedEvent.numCells C s),
      s * ((Objects.CorrectedEvent.circleCell C s l).hi - (Objects.CorrectedEvent.circleCell C s l).lo) = 2 * Real.pi * s := by
  have hn : (0 : ℝ) < Objects.CorrectedEvent.numCells C s := by exact_mod_cast numCells_pos C hs
  simp only [circleCell_width, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

theorem circleCell_width_nonneg (C : Objects.CorrectedEvent.Constants) (s : ℝ) (l : ℕ) :
    0 ≤ (Objects.CorrectedEvent.circleCell C s l).hi - (Objects.CorrectedEvent.circleCell C s l).lo := by
  rw [circleCell_width]
  have := Real.pi_pos
  positivity

 

 


theorem exists_badLength_tail (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (Amax : ℝ) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ ∀ C : Objects.CorrectedEvent.Constants, C.ξ = ξ → C.Q = Q → C.A_max = Amax →
      1 ≤ Objects.CorrectedEvent.supK C → ∀ (c₀ : ℂ) (s t : ℝ), 0 < s → 0 < t →
        μ {g | t < Objects.CorrectedEvent.badLength C (D g) c₀ s} ≤
          ENNReal.ofReal (2 * Real.pi * s * (c * Real.exp (-a * (Objects.CorrectedEvent.supK C : ℝ))) / t) := by
  obtain ⟨a, c, ha, hc, H⟩ := badCell_subset_measurable μ hμ ξ Q D hD Amax
  refine ⟨a, c, ha, hc, ?_⟩
  intro C hξ hQ hA hK c₀ s t hs ht
  set n := Objects.CorrectedEvent.numCells C s with hndef
  set q : ℝ := c * Real.exp (-a * (Objects.CorrectedEvent.supK C : ℝ)) with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hB : ∀ l : ℕ, ∃ B : Set DistC, MeasurableSet B ∧
      {g | Objects.CorrectedEvent.badCell C (D g) c₀ s (Objects.CorrectedEvent.circleCell C s l)} ⊆ B ∧
      μ B ≤ ENNReal.ofReal q := fun l => H C hξ hQ hA c₀ s (Objects.CorrectedEvent.circleCell C s l) hK
  choose B hBm hBsub hBμ using hB
  set wt : ℕ → ℝ := fun l => s * ((Objects.CorrectedEvent.circleCell C s l).hi - (Objects.CorrectedEvent.circleCell C s l).lo)
    with hwtdef
  have hwt0 : ∀ l, 0 ≤ wt l := fun l => mul_nonneg hs.le (circleCell_width_nonneg C s l)
  set F : DistC → ℝ≥0∞ := fun g =>
    ∑ l ∈ Finset.range n, (B l).indicator (fun _ => ENNReal.ofReal (wt l)) g with hFdef
  have hFm : Measurable F :=
    Finset.measurable_sum _ fun l _ => measurable_const.indicator (hBm l)
  have hFint : ∫⁻ g, F g ∂μ ≤ ENNReal.ofReal (2 * Real.pi * s * q) := by
    calc ∫⁻ g, F g ∂μ
        = ∑ l ∈ Finset.range n, ∫⁻ g, (B l).indicator (fun _ => ENNReal.ofReal (wt l)) g ∂μ :=
          lintegral_finsetSum _ fun l _ => measurable_const.indicator (hBm l)
      _ = ∑ l ∈ Finset.range n, ENNReal.ofReal (wt l) * μ (B l) := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [lintegral_indicator_const (hBm l)]
      _ ≤ ∑ l ∈ Finset.range n, ENNReal.ofReal (wt l) * ENNReal.ofReal q :=
          Finset.sum_le_sum fun l _ => mul_le_mul' le_rfl (hBμ l)
      _ = ENNReal.ofReal (∑ l ∈ Finset.range n, wt l) * ENNReal.ofReal q := by
          rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun l _ => hwt0 l]
      _ = ENNReal.ofReal (2 * Real.pi * s * q) := by
          rw [show (∑ l ∈ Finset.range n, wt l) = 2 * Real.pi * s from cell_widths_sum C hs,
            ← ENNReal.ofReal_mul (by positivity)]
  have hpt : ∀ g, ENNReal.ofReal (Objects.CorrectedEvent.badLength C (D g) c₀ s) ≤ F g := by
    intro g
    classical
    unfold Objects.CorrectedEvent.badLength
    rw [ENNReal.ofReal_sum_of_nonneg (fun l _ => by
      split_ifs
      · exact hwt0 l
      · exact le_rfl)]
    refine Finset.sum_le_sum fun l _ => ?_
    split_ifs with hbad
    · have hgB : g ∈ B l := hBsub l hbad
      rw [Set.indicator_of_mem hgB]
    · rw [ENNReal.ofReal_zero]
      exact zero_le
  have hsub : {g | t < Objects.CorrectedEvent.badLength C (D g) c₀ s} ⊆ {g | ENNReal.ofReal t ≤ F g} := by
    intro g hg
    exact (ENNReal.ofReal_le_ofReal (le_of_lt hg)).trans (hpt g)
  have ht0 : ENNReal.ofReal t ≠ 0 := (ENNReal.ofReal_pos.mpr ht).ne'
  calc μ {g | t < Objects.CorrectedEvent.badLength C (D g) c₀ s}
      ≤ μ {g | ENNReal.ofReal t ≤ F g} := measure_mono hsub
    _ ≤ (∫⁻ g, F g ∂μ) / ENNReal.ofReal t :=
        meas_ge_le_lintegral_div hFm.aemeasurable ht0 ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2 * Real.pi * s * q) / ENNReal.ofReal t := by gcongr
    _ = ENNReal.ofReal (2 * Real.pi * s * q / t) := (ENNReal.ofReal_div_of_pos ht).symm

 

 


theorem exists_s8_failure_le (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (Amax : ℝ) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ ∀ C : Objects.CorrectedEvent.Constants, ∀ T : Objects.CorrectedEvent.TubeData,
      Objects.CorrectedEvent.DataMatch C T → C.ξ = ξ → C.Q = Q → C.A_max = Amax → 1 ≤ Objects.CorrectedEvent.supK C →
        μ {g | ¬ Objects.CorrectedEvent.S8 C T (D g)} ≤
          ENNReal.ofReal (2 * (T.K : ℝ) * (2 * Real.pi * (c * Real.exp (-a * (Objects.CorrectedEvent.supK C : ℝ))))
            / (C.lamConst * Real.sqrt C.A_endpt)) := by
  obtain ⟨a, c, ha, hc, H⟩ := exists_badLength_tail μ hμ ξ Q D hD Amax
  refine ⟨a, c, ha, hc, ?_⟩
  intro C T hData hξ hQ hA hK
  obtain ⟨_, _, _, _, _, _, _, _, _, hb1, hb2, -⟩ := hData
  set s := T.blockRadius with hsdef
  set t := C.lamConst * C.A_endpt * C.ρ * C.r with htdef
  set q : ℝ := c * Real.exp (-a * (Objects.CorrectedEvent.supK C : ℝ)) with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hlamP := C.lamPos
  have he := C.endptPos
  have hρ := C.rhoPos
  have hr := C.rPos
  have ht : 0 < t := by positivity
  have hs : 0 < s := lt_of_lt_of_le (by positivity) hb1
  
  have hone : ∀ c₀ : ℂ, μ {g | t < Objects.CorrectedEvent.badLength C (D g) c₀ s} ≤
      ENNReal.ofReal (2 * Real.pi * q / (C.lamConst * Real.sqrt C.A_endpt)) := by
    intro c₀
    refine (H C hξ hQ hA hK c₀ s t hs ht).trans (ENNReal.ofReal_le_ofReal ?_)
    have hsq : 0 < Real.sqrt C.A_endpt := Real.sqrt_pos.mpr he
    have hsqsq : Real.sqrt C.A_endpt * Real.sqrt C.A_endpt = C.A_endpt :=
      Real.mul_self_sqrt he.le
    rw [div_le_div_iff₀ ht (by positivity)]
    have hs' : s ≤ Real.sqrt C.A_endpt * C.ρ * C.r := hb2
    have hpq : 0 ≤ 2 * Real.pi * q := by have := Real.pi_pos; positivity
    calc 2 * Real.pi * s * q * (C.lamConst * Real.sqrt C.A_endpt)
        = (2 * Real.pi * q) * (C.lamConst * Real.sqrt C.A_endpt) * s := by ring
      _ ≤ (2 * Real.pi * q) * (C.lamConst * Real.sqrt C.A_endpt) *
            (Real.sqrt C.A_endpt * C.ρ * C.r) := by
          apply mul_le_mul_of_nonneg_left hs'
          positivity
      _ = 2 * Real.pi * q * t := by
          rw [htdef]
          have : (2 * Real.pi * q) * (C.lamConst * Real.sqrt C.A_endpt) *
              (Real.sqrt C.A_endpt * C.ρ * C.r) =
              2 * Real.pi * q * (C.lamConst * (Real.sqrt C.A_endpt * Real.sqrt C.A_endpt) *
                C.ρ * C.r) := by ring
          rw [this, hsqsq]
  have hsub : {g : DistC | ¬ Objects.CorrectedEvent.S8 C T (D g)} ⊆
      ⋃ k : Fin T.K, ({g | t < Objects.CorrectedEvent.badLength C (D g) (Objects.CorrectedEvent.innerCenter T k) s} ∪
        {g | t < Objects.CorrectedEvent.badLength C (D g) (Objects.CorrectedEvent.outerCenter T k) s}) := by
    intro g hg
    simp only [Objects.CorrectedEvent.S8, mem_ofPred_eq, not_forall, not_and_or, not_le] at hg
    obtain ⟨k, hk⟩ := hg
    simp only [mem_iUnion, mem_union, mem_ofPred_eq]
    exact ⟨k, hk⟩
  set e : ℝ := 2 * Real.pi * q / (C.lamConst * Real.sqrt C.A_endpt) with hedef
  have he0 : 0 ≤ e := by
    have := Real.pi_pos
    have := Real.sqrt_nonneg C.A_endpt
    positivity
  calc μ {g : DistC | ¬ Objects.CorrectedEvent.S8 C T (D g)}
      ≤ μ (⋃ k : Fin T.K, ({g | t < Objects.CorrectedEvent.badLength C (D g) (Objects.CorrectedEvent.innerCenter T k) s} ∪
          {g | t < Objects.CorrectedEvent.badLength C (D g) (Objects.CorrectedEvent.outerCenter T k) s})) := measure_mono hsub
    _ ≤ ∑ k : Fin T.K, μ ({g | t < Objects.CorrectedEvent.badLength C (D g) (Objects.CorrectedEvent.innerCenter T k) s} ∪
          {g | t < Objects.CorrectedEvent.badLength C (D g) (Objects.CorrectedEvent.outerCenter T k) s}) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _k : Fin T.K, (ENNReal.ofReal e + ENNReal.ofReal e) :=
        Finset.sum_le_sum fun k _ =>
          (measure_union_le _ _).trans (add_le_add (hone _) (hone _))
    _ = ENNReal.ofReal (2 * (T.K : ℝ) * (2 * Real.pi * q) /
          (C.lamConst * Real.sqrt C.A_endpt)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_add he0 he0, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [hedef]
        ring

 

 
theorem exp_neg_supK_le (C : Objects.CorrectedEvent.Constants) {a : ℝ} (ha : 0 < a) :
    Real.exp (-a * (Objects.CorrectedEvent.supK C : ℝ)) ≤
      Real.exp a * (16 * C.A_sup) ^ (a / Real.log 4) := by
  have hA := C.supPos
  set y : ℝ := Real.logb 4 (1 / (16 * C.A_sup)) with hydef
  have hK : y - 1 ≤ (Objects.CorrectedEvent.supK C : ℝ) := by
    unfold Objects.CorrectedEvent.supK
    rw [← hydef]
    rcases le_or_gt 0 y with hy | hy
    · have := Nat.lt_floor_add_one y
      linarith
    · have : (0 : ℝ) ≤ (Nat.floor y : ℝ) := Nat.cast_nonneg _
      linarith
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hpow : (16 * C.A_sup) ^ (a / Real.log 4) = Real.exp (-a * y) := by
    rw [Real.rpow_def_of_pos (by positivity), hydef, Real.logb, one_div, Real.log_inv]
    congr 1
    field_simp
  rw [hpow, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

 
theorem le_supK (C : Objects.CorrectedEvent.Constants) (N : ℕ) (hA : C.A_sup ≤ (1 / 4 : ℝ) ^ N / 16) :
    N ≤ Objects.CorrectedEvent.supK C := by
  have hA0 := C.supPos
  unfold Objects.CorrectedEvent.supK
  apply Nat.le_floor
  have h16 : (4 : ℝ) ^ N ≤ 1 / (16 * C.A_sup) := by
    rw [le_div_iff₀ (by positivity)]
    have h4 : (4 : ℝ) ^ N * (1 / 4) ^ N = 1 := by rw [← mul_pow]; norm_num
    calc (4 : ℝ) ^ N * (16 * C.A_sup) ≤ 4 ^ N * (16 * ((1 / 4) ^ N / 16)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
      _ = 4 ^ N * (1 / 4) ^ N := by ring
      _ = 1 := h4
  have : (N : ℝ) = Real.logb 4 ((4 : ℝ) ^ N) := by
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  rw [this]
  exact Real.logb_le_logb_of_le (by norm_num) (by positivity) h16

 




theorem exists_s8_budget (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (pbar : Ioo (0 : ℝ) 1) (lam Aloc ρ Aendpt Amax : ℝ) (hlam : 0 < lam) (hAendpt : 0 < Aendpt) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ C : Objects.CorrectedEvent.Constants, ∀ T : Objects.CorrectedEvent.TubeData, Objects.CorrectedEvent.DataMatch C T →
      C.ξ = ξ → C.Q = Q → C.lamConst = lam → C.A_loc = Aloc → C.ρ = ρ →
      C.A_endpt = Aendpt → C.A_max = Amax → C.A_sup ≤ A₀ →
        μ {g | ¬ Objects.CorrectedEvent.S8 C T (D g)} ≤ ENNReal.ofReal ((1 - (pbar : ℝ)) / 10) := by
  obtain ⟨a, c, ha, hc, H⟩ := exists_s8_failure_le μ hμ ξ Q D hD Amax
  set Kρ : ℝ := (Nat.ceil (lam / (Aloc * ρ)) : ℝ) with hKρdef
  set Bc : ℝ := 2 * Kρ * (2 * Real.pi * c) / (lam * Real.sqrt Aendpt) with hBcdef
  have hBc0 : 0 ≤ Bc := by
    have := Real.pi_pos
    have := Real.sqrt_nonneg Aendpt
    positivity
  have hε : 0 < (1 - (pbar : ℝ)) / 10 := by linarith [pbar.2.2]
  
  obtain ⟨N, hN⟩ : ∃ N : ℕ, Bc * Real.exp (-a * N) ≤ (1 - (pbar : ℝ)) / 10 := by
    have htend : Filter.Tendsto (fun N : ℕ => Bc * Real.exp (-a * N)) Filter.atTop
        (nhds (Bc * 0)) := by
      apply Filter.Tendsto.const_mul
      have : Filter.Tendsto (fun N : ℕ => -a * (N : ℝ)) Filter.atTop Filter.atBot :=
        Filter.Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_natCast_atTop_atTop
      exact Real.tendsto_exp_atBot.comp this
    rw [mul_zero] at htend
    obtain ⟨N, hN⟩ := (htend.eventually (ge_mem_nhds hε)).exists
    exact ⟨N, hN⟩
  set N' : ℕ := max N 1 with hN'def
  have hN'1 : 1 ≤ N' := le_max_right _ _
  have hN'N : (N : ℝ) ≤ N' := by exact_mod_cast le_max_left N 1
  refine ⟨(1 / 4 : ℝ) ^ N' / 16, by positivity, ?_⟩
  intro C T hData hξ hQ hlamC hAlocC hρC hAendptC hAmaxC hA
  have hK : N' ≤ Objects.CorrectedEvent.supK C := le_supK C N' hA
  have hK1 : 1 ≤ Objects.CorrectedEvent.supK C := hN'1.trans hK
  have hTK : (T.K : ℝ) = Kρ := by
    obtain ⟨_, _, _, _, _, hTK, -⟩ := hData
    rw [hTK, hKρdef, hlamC, hAlocC, hρC]
  refine (H C T hData hξ hQ hAmaxC hK1).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [hTK, hlamC, hAendptC]
  have hKr : (N : ℝ) ≤ (Objects.CorrectedEvent.supK C : ℝ) := hN'N.trans (by exact_mod_cast hK)
  have hexp : Real.exp (-a * (Objects.CorrectedEvent.supK C : ℝ)) ≤ Real.exp (-a * N) :=
    Real.exp_le_exp.mpr (by nlinarith)
  calc 2 * Kρ * (2 * Real.pi * (c * Real.exp (-a * (Objects.CorrectedEvent.supK C : ℝ)))) /
        (lam * Real.sqrt Aendpt)
      = Bc * Real.exp (-a * (Objects.CorrectedEvent.supK C : ℝ)) := by rw [hBcdef]; ring
    _ ≤ Bc * Real.exp (-a * N) := mul_le_mul_of_nonneg_left hexp hBc0
    _ ≤ (1 - (pbar : ℝ)) / 10 := hN


end SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS7S9
