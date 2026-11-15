import InteractingSLE.Spec.Sec2.MartingaleFinalImage
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

/-!
# Geometric force-point images have Lebesgue-null collision sets

Packet PROVE-SEC2-MART2 (step R4). The specification derives `|{t : V_t = W_t}| = 0` from Lemma 2.5
(the times a generating curve spends on `ℝ` are null) and the identification of collisions with
boundary times of the curve (`source/spec/p001-048.md`, L842). Here it is proved for the geometric
images of **every** continuous driver, by a one-dimensional argument added by this packet:

* for alive `y < y'`, `g_t(y') − g_t(y) ≤ y' − y` (`cflow_lt_and_sub_le`), so at a collision time `t`
  (`V_t = w_t`) every alive `y` above the extreme alive point `y₀(t)` has
  `g_t(y) − w_t = g_t(y) − V_t ≤ y − y₀(t)`, hence `∫_{y₀(t)}^{Y} 2/(g_t(y) − w_t) dy = ∞`;
* on the other hand, by Tonelli,
  `∫₀ᵀ ∫_x^Y 1{y alive at t} 2/(g_t(y) − w_t) dy dt = ∫_x^Y (g_{τ_y ∧ T}(y) − y) dy < ∞`
  (`∂ₜ g_t(y) = 2/(g_t(y) − w_t)` and `g_t(y)` is bounded on bounded sets).

So almost every time is not a collision time (`volume_rightImg_eq_zero`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace MartChar

namespace RealFlow

variable {w : ℝ → ℝ}

/-! ### Continuity of the regularized flow in the starting point -/

/-- **Forward Grönwall**: `|X^{y'}_t − X^{y}_t| ≤ |y' − y| e^{2t/ε²}`. -/
lemma abs_regFlow_sub_le (hw : Continuous w) {ε : ℝ} (hε : 0 < ε) (y y' : ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    |regFlow w ε y' t - regFlow w ε y t| ≤ |y' - y| * Real.exp (2 / ε ^ 2 * t) := by
  set D : ℝ → ℝ := fun s => regFlow w ε y' s - regFlow w ε y s with hD
  have hDc : ContinuousOn D (Icc 0 t) :=
    ((continuousOn_regFlow hw hε y').sub (continuousOn_regFlow hw hε y)).mono fun s hs => hs.1
  have hD0 : D 0 = y' - y := by
    simp only [hD, regFlow_eq hw hε _ le_rfl, intervalIntegral.integral_same]
    ring
  have h := norm_le_gronwallBound_of_norm_deriv_right_le (f := D)
    (f' := fun u => Bessel.regDrift 2 ε (regFlow w ε y' u) - Bessel.regDrift 2 ε (regFlow w ε y u))
    (δ := |y' - y|) (K := 2 / ε ^ 2) (ε := 0) hDc (fun u hu => ?_) (by simp [hD0])
    (fun u _ => ?_) t ⟨ht, le_rfl⟩
  · rw [gronwallBound_ε0, sub_zero] at h
    simpa [hD, Real.norm_eq_abs] using h
  · rcases hu.1.eq_or_lt with h0 | hpos
    · -- at `u = 0` use the one-sided derivative of `lipUnc`
      have hdat := lipData_regDrift_two hw hε
      have h1 := OneForce.lipUnc_hasDerivWithinAt hdat (T := t) ht y' u ⟨hu.1, hu.2.le⟩
      have h2 := OneForce.lipUnc_hasDerivWithinAt hdat (T := t) ht y u ⟨hu.1, hu.2.le⟩
      have heq : D = fun s => OneForce.lipUnc (Bessel.regDrift 2 ε) y' (fun t => -w t) s
          - OneForce.lipUnc (Bessel.regDrift 2 ε) y (fun t => -w t) s := by
        funext s
        simp only [hD, regFlow, OneForce.lipSol]
        ring
      rw [heq]
      exact Bessel.hasDerivWithinAt_Ici_of_Icc (h1.sub h2) hu
    · exact (hasDerivAt_regFlow_sub hw hε y y' hpos).hasDerivWithinAt
  · have hL := (Bessel.lipschitzWith_regDrift zero_le_two hε).dist_le_mul
      (regFlow w ε y' u) (regFlow w ε y u)
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)] at hL
    simpa [hD, Real.norm_eq_abs] using hL

lemma continuous_regFlow_start (hw : Continuous w) {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : 0 ≤ t) :
    Continuous fun y => regFlow w ε y t := by
  refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal (Real.exp (2 / ε ^ 2 * t)))
    fun y y' => ?_).continuous
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (Real.exp_pos _).le, mul_comm]
  exact abs_regFlow_sub_le hw hε y' y ht

/-- `(y, t) ↦ X^y_{t ∨ 0}` is jointly measurable. -/
lemma measurable_regFlow_uncurry (hw : Continuous w) {ε : ℝ} (hε : 0 < ε) :
    Measurable (Function.uncurry fun y t => regFlow w ε y (max t 0)) := by
  refine measurable_uncurry_of_continuous_of_measurable (fun t => ?_) (fun y => ?_)
  · exact continuous_regFlow_start hw hε (le_max_right t 0)
  · exact ((continuousOn_regFlow hw hε y).comp_continuous (continuous_id.max continuous_const)
      fun t => le_max_right t 0).measurable

/-! ### A growth bound for alive points -/

/-- A point whose image exceeds the driver's running bound `M` stays alive and grows at most like
`2√t`. -/
lemma Alive.gImg_le_of_lt (hw : Continuous w) {y s t M : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hy : Alive w y s) (hM : M < gImg w y s) (hM2 : ∀ u ∈ Icc s t, w u ≤ M) :
    Alive w y t ∧ gImg w y t ≤ gImg w y s + 2 * Real.sqrt (t - s) := by
  have hc : 0 < gImg w y s - M := by linarith
  have hyt : Alive w y t := hy.of_forall_le_cflow hw hs hc fun u hu hyu => by
    have h1 := hyu.gImg_mono hw hs hu.1 le_rfl
    have h2 := hM2 u hu
    simp only [gImg] at h1 ⊢
    linarith
  refine ⟨hyt, ?_⟩
  have hgc : ContinuousOn (fun u => gImg w y u) (Icc 0 t) :=
    hw.continuousOn.add (hyt.isPosSol hw).1
  have hanti : AntitoneOn (fun u => (gImg w y u - M) ^ 2 - 4 * u) (Icc s t) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc s t)
      (((hgc.mono (Icc_subset_Icc_left hs)).sub continuousOn_const).pow 2 |>.sub
        (continuousOn_const.mul continuousOn_id))
      (f' := fun u => 2 * (gImg w y u - M) * (2 / cflow w y u) - 4) (fun u hu => ?_)
      (fun u hu => ?_)
    · rw [interior_Icc] at hu
      have hd := hyt.hasDerivAt_gImg hw ⟨hs.trans_lt hu.1, hu.2⟩
      have := ((hd.sub_const M).pow 2).fun_sub ((hasDerivAt_id' u).const_mul 4)
      exact (this.congr_deriv (by ring)).hasDerivWithinAt
    · rw [interior_Icc] at hu
      have hu' : u ∈ Icc 0 t := ⟨hs.trans hu.1.le, hu.2.le⟩
      have hpos := hyt.cflow_pos hw hu'
      have hgm : gImg w y s ≤ gImg w y u := hyt.gImg_mono hw hs hu.1.le hu.2.le
      have hwu := hM2 u ⟨hu.1.le, hu.2.le⟩
      have hle : gImg w y u - M ≤ cflow w y u := by simp only [gImg] at hgm ⊢; linarith
      have he : 2 * (gImg w y u - M) * (2 / cflow w y u) = 4 * ((gImg w y u - M) / cflow w y u) :=
        by ring
      have : (gImg w y u - M) / cflow w y u ≤ 1 := (div_le_one hpos).2 hle
      rw [he]
      linarith
  have hst' := hanti ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst
  simp only at hst'
  have hgt : M ≤ gImg w y t := by linarith [hyt.gImg_mono hw hs hst le_rfl]
  have hsq : (gImg w y t - M) ^ 2 ≤ (gImg w y s - M + 2 * Real.sqrt (t - s)) ^ 2 := by
    have hd : 0 ≤ t - s := by linarith
    have h2 := Real.sq_sqrt hd
    have h3 := Real.sqrt_nonneg (t - s)
    nlinarith
  have := (pow_le_pow_iff_left₀ (by linarith) (by positivity) two_ne_zero).1 hsq
  linarith

/-! ### The inner time integral -/

lemma measurableSet_alive (y : ℝ) : MeasurableSet {t | Alive w y t} :=
  Set.OrdConnected.measurableSet ⟨fun _ _ _ hb _ hc => (show Alive w y _ from hb).mono hc.2⟩

/-- `∫₀ᵀ 1{y alive at t} 2/(g_t(y) − w_t) dt ≤ C` if `g_s(y) − y ≤ C` at every alive `s ≤ T`. -/
lemma lintegral_alive_le (hw : Continuous w) {y T C : ℝ}
    (hC : ∀ s ∈ Icc 0 T, Alive w y s → gImg w y s - y ≤ C) :
    ∫⁻ t in Icc 0 T, {t | Alive w y t}.indicator (fun t => ENNReal.ofReal (2 / cflow w y t)) t
      ≤ ENNReal.ofReal C := by
  set f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (2 / cflow w y t) with hf
  rw [lintegral_indicator (measurableSet_alive y), Measure.restrict_restrict (measurableSet_alive y)]
  set J := {t | Alive w y t} ∩ Icc 0 T with hJ
  have hpiece : ∀ s ∈ J, ∫⁻ t in Icc 0 s, f t ≤ ENNReal.ofReal C := by
    intro s hs
    have hs0 : 0 ≤ s := hs.2.1
    have hint : IntegrableOn (fun r => 2 / cflow w y r) (Icc 0 s) :=
      (hs.1.continuousOn_inv hw).integrableOn_Icc
    have hnn : 0 ≤ᵐ[volume.restrict (Icc 0 s)] fun r => 2 / cflow w y r := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact (div_pos two_pos (hs.1.cflow_pos hw hr)).le
    rw [hf, ← ofReal_integral_eq_lintegral_ofReal hint hnn]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs0]
    have := hs.1.gImg_eq hw ⟨hs0, le_rfl⟩
    linarith [hC s hs.2 hs.1]
  by_cases hJne : J.Nonempty
  · have hJbdd : BddAbove J := ⟨T, fun t ht => ht.2.2⟩
    set τ := sSup J with hτ
    set K : ℕ → Set ℝ := fun n => J ∩ Iic (τ - 1 / ((n : ℝ) + 1)) with hK
    have hKmono : Monotone K := fun n m hnm t ht => by
      refine ⟨ht.1, (mem_Iic.1 ht.2).trans ?_⟩
      have : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
      linarith
    have hsub : J ⊆ (⋃ n, K n) ∪ {τ} := by
      intro t ht
      rcases (le_csSup hJbdd ht).lt_or_eq with hlt | heq
      · left
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
        exact mem_iUnion.2 ⟨n, ht, by rw [mem_Iic]; linarith⟩
      · right
        exact heq
    calc ∫⁻ t in J, f t ≤ ∫⁻ t in (⋃ n, K n) ∪ {τ}, f t := lintegral_mono_set hsub
      _ ≤ (∫⁻ t in ⋃ n, K n, f t) + ∫⁻ t in {τ}, f t := lintegral_union_le _ _ _
      _ = ⨆ n, ∫⁻ t in K n, f t := by
          rw [setLIntegral_measure_zero _ _ (Real.volume_singleton), add_zero]
          exact setLIntegral_iUnion_of_directed _ hKmono.directed_le
      _ ≤ ENNReal.ofReal C := iSup_le fun n => by
          have hlt : τ - 1 / ((n : ℝ) + 1) < τ := by
            have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
            linarith
          obtain ⟨s, hs, hst⟩ := exists_lt_of_lt_csSup hJne hlt
          calc ∫⁻ t in K n, f t ≤ ∫⁻ t in Icc 0 s, f t :=
                lintegral_mono_set fun t ht => ⟨ht.1.2.1, (mem_Iic.1 ht.2).trans hst.le⟩
            _ ≤ ENNReal.ofReal C := hpiece s hs
  · rw [not_nonempty_iff_eq_empty.1 hJne, Measure.restrict_empty, lintegral_zero_measure]
    exact zero_le

/-! ### The collision set is null -/

/-- `∫_{y₀}^{Y} 2/(y − y₀) dy = ∞`. -/
lemma lintegral_two_div_sub_eq_top {y₀ Y : ℝ} (h : y₀ < Y) :
    ∫⁻ y in Ioo y₀ Y, ENNReal.ofReal (2 / (y - y₀)) = ∞ := by
  by_contra hfin
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo y₀ Y)] fun y => 2 / (y - y₀) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact (div_pos two_pos (sub_pos.2 hy.1)).le
  have hcont : ContinuousOn (fun y => 2 / (y - y₀)) (Ioo y₀ Y) :=
    continuousOn_const.div (continuousOn_id.sub continuousOn_const) fun y hy =>
      (sub_pos.2 hy.1).ne'
  have hint : IntegrableOn (fun y => 2 / (y - y₀)) (Ioo y₀ Y) :=
    ⟨hcont.aestronglyMeasurable measurableSet_Ioo,
      (hasFiniteIntegral_iff_ofReal hnn).2 (lt_top_iff_ne_top.2 hfin)⟩
  have hint' : IntegrableOn (fun y => (1 / 2) * (2 / (y - y₀))) (Ioc y₀ Y) :=
    ((integrableOn_Ioc_iff_integrableOn_Ioo (by simp)).2 hint).const_mul _
  have hII : IntervalIntegrable (fun y => (y - y₀)⁻¹) volume y₀ Y := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le h.le).2 (hint'.congr_fun ?_
      measurableSet_Ioc)
    intro y hy
    have : y - y₀ ≠ 0 := (sub_pos.2 hy.1).ne'
    field_simp
  rcases intervalIntegrable_sub_inv_iff.1 hII with h1 | h1
  · exact absurd h1 h.ne
  · exact h1 left_mem_uIcc

/-- A lower bound on `[0, t]` for a continuous function is checked at rational times and at `t`. -/
lemma forall_Icc_iff_rat {f : ℝ → ℝ} {t c : ℝ} (hf : ContinuousOn f (Icc 0 t)) :
    (∀ s ∈ Icc 0 t, c ≤ f s) ↔
      (∀ q : ℚ, (0 : ℝ) ≤ q → (q : ℝ) ≤ t → c ≤ f q) ∧ (0 ≤ t → c ≤ f t) := by
  refine ⟨fun h => ⟨fun q h0 hq => h q ⟨h0, hq⟩, fun ht => h t ⟨ht, le_rfl⟩⟩, ?_⟩
  rintro ⟨hq, ht⟩ s hs
  rcases hs.2.eq_or_lt with heq | hlt
  · rw [heq]; exact ht (hs.1.trans hs.2)
  have hcl : IsClosed (Icc 0 t ∩ f ⁻¹' Ici c) :=
    hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hsub : Ioo 0 t ∩ range ((↑) : ℚ → ℝ) ⊆ Icc 0 t ∩ f ⁻¹' Ici c := by
    rintro r ⟨hr, q, rfl⟩
    exact ⟨Ioo_subset_Icc_self hr, hq q hr.1.le hr.2.le⟩
  have ht0 : (0 : ℝ) < t := hs.1.trans_lt hlt
  have h1 : Ioo 0 t ⊆ closure (Ioo 0 t ∩ range ((↑) : ℚ → ℝ)) :=
    Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo
  have h2 : s ∈ closure (Ioo (0 : ℝ) t) := by rw [closure_Ioo ht0.ne]; exact hs
  have h3 : closure (Ioo (0 : ℝ) t) ⊆ closure (Ioo 0 t ∩ range ((↑) : ℚ → ℝ)) :=
    closure_minimal h1 isClosed_closure
  exact (closure_minimal hsub hcl (h3 h2)).2

/-- **The collision set of a geometric image on `[0, T]` is null.** -/
theorem volume_collision_Icc (hw : Continuous w) (x : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    volume {t | t ∈ Icc 0 T ∧ rightImg w x t = w t} = 0 := by
  -- the upper cutoff `Y` above the extreme alive point at time `T`
  set AT := {y | x < y ∧ Alive w y T} with hAT
  have hATne : AT.Nonempty := by
    obtain ⟨_, ⟨y, hxy, hy, -⟩⟩ := imgSet_nonempty hw x hT
    exact ⟨y, hxy, hy⟩
  have hATbdd : BddBelow AT := ⟨x, fun y hy => hy.1.le⟩
  set Y := sInf AT + 1 with hY
  -- a large alive point bounding every image below `Y`
  obtain ⟨s₀, hs₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hT) hw.continuousOn
  set Y₁ := max Y (w s₀) + 1 with hY₁
  have hwY₁ : ∀ s ∈ Icc 0 T, w s ≤ w s₀ := fun s hs => hmax hs
  have hY₁alive : Alive w Y₁ T := alive_of_forall_lt hw hT fun s hs => by
    linarith [hwY₁ s hs, le_max_right Y (w s₀)]
  have hY₁0 : Alive w Y₁ 0 := hY₁alive.mono hT
  have hg0 : gImg w Y₁ 0 = Y₁ := gImg_zero hw hY₁0
  have hgY₁ : ∀ s ∈ Icc 0 T, gImg w Y₁ s ≤ Y₁ + 2 * Real.sqrt T := fun s hs => by
    have h := (hY₁0.gImg_le_of_lt hw le_rfl hs.1 (M := w s₀)
      (by rw [hg0]; linarith [le_max_right Y (w s₀)])
      (fun u hu => hwY₁ u ⟨hu.1, hu.2.trans hs.2⟩)).2
    rw [hg0, sub_zero] at h
    have hsq : Real.sqrt s ≤ Real.sqrt T := Real.sqrt_le_sqrt hs.2
    linarith
  set C := Y₁ + 2 * Real.sqrt T - x with hCdef
  have hC : ∀ y, x < y → y < Y → ∀ s ∈ Icc 0 T, Alive w y s → gImg w y s - y ≤ C :=
    fun y hxy hyY s hs hys => by
      have hlt : y < Y₁ := by linarith [le_max_left Y (w s₀)]
      have h1 := (cflow_lt_and_sub_le hw hys hlt hs.1 ⟨hs.1, le_rfl⟩).1
      have h2 := hgY₁ s hs
      simp only [gImg] at h1 h2 ⊢
      linarith
  -- the jointly measurable integrand `F(y, t)`
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hε
  have hε0 : ∀ n, 0 < ε n := fun n => by simp only [hε]; positivity
  set S : ℕ → Set (ℝ × ℝ) := fun n => {p | x < p.1 ∧ p.1 < Y ∧ 0 ≤ p.2 ∧
    ∀ s ∈ Icc 0 p.2, ε n ≤ regFlow w (ε n) p.1 s} with hS
  set F : ℝ × ℝ → ℝ≥0∞ := fun p => ⨆ n, (S n).indicator
    (fun q => ENNReal.ofReal (2 / regFlow w (ε n) q.1 (max q.2 0))) p with hF
  have hSm : ∀ n, MeasurableSet (S n) := by
    intro n
    have hset : S n = {p : ℝ × ℝ | x < p.1} ∩ {p | p.1 < Y} ∩ {p | 0 ≤ p.2} ∩
        (⋂ q : ℚ, {p | ¬ ((0 : ℝ) ≤ q ∧ (q : ℝ) ≤ p.2) ∨
          ε n ≤ regFlow w (ε n) p.1 (max (q : ℝ) 0)}) ∩
        {p | ε n ≤ regFlow w (ε n) p.1 (max p.2 0)} := by
      ext p
      simp only [hS, mem_ofPred_eq, mem_inter_iff, mem_iInter]
      have hcont : ContinuousOn (regFlow w (ε n) p.1) (Icc 0 p.2) :=
        (continuousOn_regFlow hw (hε0 n) p.1).mono fun s hs => hs.1
      rw [forall_Icc_iff_rat hcont]
      constructor
      · rintro ⟨h1, h2, h3, h4, h5⟩
        refine ⟨⟨⟨⟨h1, h2⟩, h3⟩, fun q => ?_⟩, by rw [max_eq_left h3]; exact h5 h3⟩
        by_cases hq : (0 : ℝ) ≤ q ∧ (q : ℝ) ≤ p.2
        · exact Or.inr (by rw [max_eq_left hq.1]; exact h4 q hq.1 hq.2)
        · exact Or.inl hq
      · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
        refine ⟨h1, h2, h3, fun q hq0 hq => ?_, fun _ => by rwa [max_eq_left h3] at h5⟩
        rcases h4 q with h | h
        · exact absurd ⟨hq0, hq⟩ h
        · rwa [max_eq_left hq0] at h
    rw [hset]
    have hR : ∀ r : ℝ, Measurable fun p : ℝ × ℝ => regFlow w (ε n) p.1 (max r 0) := fun r =>
      (continuous_regFlow_start hw (hε0 n) (le_max_right r 0)).measurable.comp measurable_fst
    refine ((((measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_const)).inter
      (measurableSet_le measurable_const measurable_snd)).inter
      (MeasurableSet.iInter fun q => ?_)).inter ?_
    · refine MeasurableSet.union ?_ (measurableSet_le measurable_const (hR q))
      exact ((MeasurableSet.const _).inter (measurableSet_le measurable_const measurable_snd)).compl
    · exact measurableSet_le measurable_const (measurable_regFlow_uncurry hw (hε0 n))
  have hFm : Measurable F := Measurable.iSup fun n => Measurable.indicator
    (ENNReal.measurable_ofReal.comp (measurable_const.div (measurable_regFlow_uncurry hw (hε0 n))))
    (hSm n)
  -- `F` is the alive indicator
  have hFle : ∀ y t, F (y, t) ≤ (Ioo x Y).indicator (fun y =>
      {t | Alive w y t}.indicator (fun t => ENNReal.ofReal (2 / cflow w y t)) t) y := by
    intro y t
    refine iSup_le fun n => ?_
    by_cases hp : (y, t) ∈ S n
    · obtain ⟨h1, h2, h3, h4⟩ := hp
      have hA : Alive w y t := ⟨_, isPosSol_regFlow hw (hε0 n) h4⟩
      rw [indicator_of_mem (show (y, t) ∈ S n from ⟨h1, h2, h3, h4⟩),
        indicator_of_mem (show y ∈ Ioo x Y from ⟨h1, h2⟩),
        indicator_of_mem (show t ∈ {t | Alive w y t} from hA),
        max_eq_left h3, cflow_eq_regFlow hw (hε0 n) h4 ⟨h3, le_rfl⟩]
    · rw [indicator_of_notMem hp]
      exact zero_le
  have hFge : ∀ y t, 0 ≤ t → x < y → y < Y → Alive w y t →
      ENNReal.ofReal (2 / cflow w y t) ≤ F (y, t) := by
    intro y t ht hxy hyY hA
    obtain ⟨n, hn⟩ := (alive_iff_regFlow hw ht).1 hA
    refine le_iSup_of_le n ?_
    rw [indicator_of_mem (show (y, t) ∈ S n from ⟨hxy, hyY, ht, hn⟩), max_eq_left ht,
      cflow_eq_regFlow hw (hε0 n) hn ⟨ht, le_rfl⟩]
  -- Tonelli: the double integral is finite
  have hswap := lintegral_lintegral_swap (μ := volume.restrict (Icc 0 T)) (ν := volume)
    (f := fun t y => F (y, t)) (hFm.comp measurable_swap).aemeasurable
  have hfin : ∫⁻ t in Icc 0 T, ∫⁻ y, F (y, t) ≠ ∞ := by
    rw [hswap]
    refine ne_top_of_le_ne_top (b := ∫⁻ y, (Ioo x Y).indicator (fun _ => ENNReal.ofReal C) y)
      ?_ (lintegral_mono fun y => ?_)
    · rw [lintegral_indicator_const measurableSet_Ioo, Real.volume_Ioo]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    · calc ∫⁻ t in Icc 0 T, F (y, t) ≤ ∫⁻ t in Icc 0 T, (Ioo x Y).indicator (fun y =>
            {t | Alive w y t}.indicator (fun t => ENNReal.ofReal (2 / cflow w y t)) t) y :=
            lintegral_mono fun t => hFle y t
        _ ≤ (Ioo x Y).indicator (fun _ => ENNReal.ofReal C) y := by
            by_cases hy : y ∈ Ioo x Y
            · simp only [indicator_of_mem hy]
              exact lintegral_alive_le hw (hC y hy.1 hy.2)
            · simp only [indicator_of_notMem hy, lintegral_zero, le_refl]
  have hmeasF : Measurable fun t => ∫⁻ y, F (y, t) :=
    (hFm.comp measurable_swap).lintegral_prod_right'
  have hae := ae_lt_top hmeasF hfin
  -- at a collision time the inner integral diverges
  have hdiv : ∀ t ∈ Icc 0 T, rightImg w x t = w t → ∫⁻ y, F (y, t) = ∞ := by
    intro t ht hcol
    set At := {y | x < y ∧ Alive w y t} with hAt
    have hAtbdd : BddBelow At := ⟨x, fun y hy => hy.1.le⟩
    have hAtne : At.Nonempty := hATne.mono fun y hy => ⟨hy.1, hy.2.mono ht.2⟩
    set y₀ := sInf At with hy₀
    have hy₀Y : y₀ < Y := by
      have : y₀ ≤ sInf AT := csInf_le_csInf hAtbdd hATne fun y hy => ⟨hy.1, hy.2.mono ht.2⟩
      linarith
    have hxy₀ : x ≤ y₀ := le_csInf hAtne fun y hy => hy.1.le
    have hlow : ∀ y ∈ Ioo y₀ Y, ENNReal.ofReal (2 / (y - y₀)) ≤ F (y, t) := by
      intro y hy
      obtain ⟨y', hy'At, hy'y⟩ := exists_lt_of_csInf_lt hAtne hy.1
      have hxy : x < y := hy'At.1.trans hy'y
      have hA : Alive w y t := hy'At.2.of_le hw hy'y.le ht.1
      have hle := gImg_sub_rightImg_le hw ht.1 hxy hA fun y'' hxy'' hy'' =>
        csInf_le hAtbdd ⟨hxy'', hy''⟩
      rw [hcol] at hle
      have hpos := hA.cflow_pos hw ⟨ht.1, le_rfl⟩
      have hcf : cflow w y t ≤ y - y₀ := by simp only [gImg] at hle; linarith
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hFge y t ht.1 hxy hy.2 hA)
      exact div_le_div_of_nonneg_left zero_le_two hpos hcf
    refine top_le_iff.1 ?_
    calc (∞ : ℝ≥0∞) = ∫⁻ y in Ioo y₀ Y, ENNReal.ofReal (2 / (y - y₀)) :=
          (lintegral_two_div_sub_eq_top hy₀Y).symm
      _ ≤ ∫⁻ y in Ioo y₀ Y, F (y, t) := setLIntegral_mono' measurableSet_Ioo fun y hy => hlow y hy
      _ ≤ ∫⁻ y, F (y, t) := setLIntegral_le_lintegral _ _
  -- conclusion
  have hnull : volume.restrict (Icc 0 T) {t | ¬ ∫⁻ y, F (y, t) < ∞} = 0 := by
    rw [← ae_iff]
    exact hae
  refine measure_mono_null (t := {t | ¬ ∫⁻ y, F (y, t) < ∞} ∩ Icc 0 T) ?_ ?_
  · rintro t ⟨ht, hcol⟩
    exact ⟨by rw [mem_ofPred_eq, hdiv t ht hcol]; exact lt_irrefl _, ht⟩
  · rwa [Measure.restrict_apply' measurableSet_Icc] at hnull

/-- **Geometric images have Lebesgue-null collision sets** (for every continuous driver). -/
theorem volume_rightImg_eq_zero (hw : Continuous w) (x : ℝ) :
    volume {t : ℝ | 0 ≤ t ∧ rightImg w x t = w t} = 0 := by
  refine measure_mono_null (t := ⋃ N : ℕ, {t | t ∈ Icc 0 (N : ℝ) ∧ rightImg w x t = w t})
    (fun t ht => mem_iUnion.2 ⟨⌈t⌉₊, ⟨ht.1, Nat.le_ceil t⟩, ht.2⟩)
    (measure_iUnion_null fun N => volume_collision_Icc hw x (Nat.cast_nonneg N))

end RealFlow

end MartChar

end InteractingSLE
