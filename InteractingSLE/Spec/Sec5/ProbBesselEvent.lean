/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.ProbSmallBall
import InteractingSLE.Stochastic.Bessel.Existence
import QuantumZipper.Proofs.RS.TransienceCanon
import InteractingSLE.Spec.Sec5.Grid

/-!
# Lemma 5.10: the reference events on the space of continuous paths

Packet PROVE-SEC5-B (specification §5.2, proof of Lemma 5.10, `source/spec/p097-144.md` L947–L959, and the
corrected crossing lemma, `source/spec/p433-480.md` §2.2, "Proof of uniform positivity for the reference").

The uniform positivity of the one-force reference probability is reduced to two events of a Brownian path
`β` on the canonical space `CPath` (QuantumZipper), both independent of the starting point `x ≥ 0` and of the
weight `ρ` in a compact `J ⊂ (−2, ∞)`:

* `pastEvent c a b g s`: on `[0, s]` the path stays in `[−a, a]`, the zero-start Bessel path `Y` of drift
  coefficient `c = c_*` (dimension `δ_* = 1 + 2c_*`, the minimal dimension over `J`) driven by `−β` has
  `Y_s + β_s = c ∫₀ˢ 1/Y ≤ b`, and `Y_s ≥ g` (every one-force gap dominates `Y` by Bessel comparison);
* `incrEvent s T a`: the increment `β_{s+u} − β_s` stays in `[−a, a]` for `u ≤ T`.

`exists_pos_measureReal_pastEvent`: for every `a, b > 0` and every `s₁ > 0` there are `s ∈ (0, s₁]` and `g > 0`
with `ℙ(pastEvent) > 0` (continuity at time `0`, a fixed time at which `Y` is almost surely positive, from the
null zero set of `Y` and Fubini, and continuity of the measure from above).
`measureReal_pastEvent_inter_incrEvent`: the two events are independent (weak Markov property), and
`incrEvent` has probability at least `exp(−π² T/(8a²))` (`ProbSmallBall`).
-/

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper.RS
open scoped NNReal ENNReal

noncomputable section

namespace InteractingSLE

namespace Sec5

/-! ### Closed conditions on `[0, s]` through countably many times -/

/-- A closed condition holds on `[0, s]` iff it holds on the countable dense set `ratTimesLE s`. -/
theorem forall_le_iff_ratTimesLE {γ : ℝ≥0 → ℝ} (hγ : Continuous γ) {S : Set ℝ} (hS : IsClosed S)
    (s : ℝ≥0) : (∀ t ≤ s, γ t ∈ S) ↔ ∀ q ∈ ratTimesLE s, γ q ∈ S := by
  refine ⟨fun h q hq => h q (le_of_mem_ratTimesLE hq), fun h t ht => ?_⟩
  by_contra hns
  obtain ⟨δ, hδ, hδγ⟩ := Metric.continuous_iff.1 hγ t _
    (show 0 < Metric.infDist (γ t) S from (hS.notMem_iff_infDist_pos ⟨_, h s
      (Set.mem_insert _ _)⟩).1 hns)
  obtain ⟨q, hq, hqt⟩ := exists_mem_ratTimesLE_near ht hδ
  have h1 := hδγ q hqt
  have h2 : Metric.infDist (γ t) S ≤ dist (γ t) (γ q) := Metric.infDist_le_dist_of_mem (h q hq)
  rw [dist_comm] at h1
  linarith

/-! ### The Bessel path of the canonical Brownian motion -/

/-- The zero-start Bessel path of drift coefficient `c` driven by `−β`, for a path `β ∈ CPath`. -/
def besY (c : ℝ) (f : CPath) (t : ℝ≥0) : ℝ := Bessel.besselProc c 0 (-canonBM) t f

theorem continuous_negCanonBM (f : CPath) : Continuous fun t => (-canonBM) t f :=
  (continuous_canonBM f).neg

theorem measurable_negCanonBM (t : ℝ≥0) : Measurable ((-canonBM) t) :=
  (measurable_canonBM t).neg

/-- The natural filtration of the canonical path. -/
def canonFilt : Filtration ℝ≥0 (inferInstance : MeasurableSpace CPath) :=
  Bessel.natFilt measurable_canonBM

theorem measurable_canonBM_canonFilt (t : ℝ≥0) : Measurable[canonFilt t] (canonBM t) :=
  Bessel.natFilt_adapted measurable_canonBM t

theorem measurable_besY (hc : 0 < c) (t : ℝ≥0) : Measurable[canonFilt t] fun f => besY c f t :=
  Bessel.besselProc_measurable canonFilt (fun t => (measurable_canonBM_canonFilt t).neg)
    continuous_negCanonBM hc t

theorem measurable_besY' (hc : 0 < c) (t : ℝ≥0) : Measurable fun f => besY c f t :=
  (measurable_besY hc t).mono (canonFilt.le t) le_rfl

/-- Joint measurability in time and path (a supremum of continuous-in-time regularized solutions). -/
theorem measurable_besY_uncurry (hc : 0 < c) : Measurable fun p : ℝ≥0 × CPath => besY c p.2 p.1 := by
  have h : ∀ n, Measurable fun p : ℝ≥0 × CPath =>
      Bessel.regProc c (Bessel.besselEps c n) 0 (-canonBM) p.1 p.2 := fun n =>
    measurable_uncurry_of_continuous_of_measurable
      (fun f => Bessel.continuous_regProc continuous_negCanonBM hc.le (Bessel.besselEps_pos c n) f)
      (fun t => Bessel.regProc_measurable' measurable_negCanonBM continuous_negCanonBM hc.le
        (Bessel.besselEps_pos c n) t)
  exact Measurable.iSup h

variable {μ₀ : Measure CPath} [IsProbabilityMeasure μ₀]

omit [IsProbabilityMeasure μ₀] in
/-- Almost surely `besY c` is a Bessel path driven by `−β` started at `0`. -/
theorem ae_isBesselPath_besY (hμ : IsPreBrownianReal canonBM μ₀) (hc : 0 < c) :
    ∀ᵐ f ∂μ₀, Bessel.IsBesselPath c 0 (fun t => -f.1 t) (fun t => besY c f t) :=
  Bessel.ae_isBesselPath hμ.neg continuous_negCanonBM measurable_negCanonBM hc le_rfl

/-! ### The two events -/

/-- The past event on `[0, s]`. -/
def pastEvent (c a b g : ℝ) (s : ℝ≥0) : Set CPath :=
  {f | (∀ t ≤ s, |f.1 t| ≤ a) ∧ besY c f s + f.1 s ≤ b ∧ g ≤ besY c f s}

/-- The increment event after `s`. -/
def incrEvent (s T : ℝ≥0) (a : ℝ) : Set CPath := {f | ∀ u ≤ T, |f.1 (s + u) - f.1 s| ≤ a}

theorem measurableSet_forall_le_abs (s : ℝ≥0) (a : ℝ) :
    MeasurableSet[canonFilt s] {f : CPath | ∀ t ≤ s, |f.1 t| ≤ a} := by
  have hS : IsClosed {x : ℝ | |x| ≤ a} := isClosed_le continuous_abs continuous_const
  have h : {f : CPath | ∀ t ≤ s, |f.1 t| ≤ a} = ⋂ q ∈ ratTimesLE s, {f : CPath | |f.1 q| ≤ a} := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact forall_le_iff_ratTimesLE (S := {x : ℝ | |x| ≤ a}) f.2 hS s
  rw [h]
  refine MeasurableSet.biInter (countable_ratTimesLE s) fun q hq => ?_
  exact measurableSet_le (continuous_abs.measurable.comp
    ((measurable_canonBM_canonFilt q).mono (canonFilt.mono (le_of_mem_ratTimesLE hq)) le_rfl))
    measurable_const

theorem measurableSet_pastEvent (hc : 0 < c) (a b g : ℝ) (s : ℝ≥0) :
    MeasurableSet[canonFilt s] (pastEvent c a b g s) := by
  have h : pastEvent c a b g s = {f : CPath | ∀ t ≤ s, |f.1 t| ≤ a} ∩
      ({f | besY c f s + canonBM s f ≤ b} ∩ {f | g ≤ besY c f s}) := rfl
  rw [h]
  exact (measurableSet_forall_le_abs s a).inter ((measurableSet_le
    ((measurable_besY hc s).add (measurable_canonBM_canonFilt s)) measurable_const).inter
    (measurableSet_le measurable_const (measurable_besY hc s)))

/-- The increment path after `s`. -/
def shiftPath (s : ℝ≥0) (f : CPath) : ℝ≥0 → ℝ := fun u => f.1 (s + u) - f.1 s

theorem measurableSet_incrEvent (s T : ℝ≥0) (a : ℝ) :
    MeasurableSet[MeasurableSpace.comap (fun f : CPath => shiftPath s f) MeasurableSpace.pi]
      (incrEvent s T a) := by
  have hS : IsClosed {x : ℝ | |x| ≤ a} := isClosed_le continuous_abs continuous_const
  have h : incrEvent s T a = (fun f : CPath => shiftPath s f) ⁻¹'
      (⋂ q ∈ ratTimesLE T, {g : ℝ≥0 → ℝ | |g q| ≤ a}) := by
    ext f
    simp only [incrEvent, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_iInter, shiftPath]
    exact forall_le_iff_ratTimesLE (S := {x : ℝ | |x| ≤ a})
      ((f.2.comp (continuous_const.add continuous_id)).sub continuous_const) hS T
  rw [h]
  refine ⟨_, ?_, rfl⟩
  refine MeasurableSet.biInter (countable_ratTimesLE T) fun q _ => ?_
  exact measurableSet_le (continuous_abs.measurable.comp (measurable_pi_apply q)) measurable_const

/-! ### Independence of the two events, and the small ball after `s` -/

omit [IsProbabilityMeasure μ₀] in
/-- **The two events are independent** (weak Markov property at the deterministic time `s`). -/
theorem measureReal_pastEvent_inter_incrEvent (hμ : IsPreBrownianReal canonBM μ₀) (hc : 0 < c)
    (a b g : ℝ) (s T : ℝ≥0) (a' : ℝ) :
    μ₀.real (pastEvent c a b g s ∩ incrEvent s T a')
      = μ₀.real (pastEvent c a b g s) * μ₀.real (incrEvent s T a') := by
  have h := hμ.indepFun_shift s
  rw [IndepFun_iff_Indep] at h
  have h1 : MeasurableSet[MeasurableSpace.comap (fun f (u : Set.Iic s) => canonBM u f)
      MeasurableSpace.pi] (pastEvent c a b g s) :=
    Bessel.natFilt_le_past measurable_canonBM s _ (measurableSet_pastEvent hc a b g s)
  have h2 := measurableSet_incrEvent s T a'
  have := (Indep_iff _ _ _).1 h _ _ h2 h1
  rw [measureReal_def, measureReal_def, measureReal_def, Set.inter_comm, this,
    ENNReal.toReal_mul, mul_comm]

/-- **Small-ball positivity after `s`**: `ℙ[∀ u ≤ T, |β_{s+u} − β_s| ≤ a] ≥ exp(−π² T/(8a²))`. -/
theorem exp_le_measureReal_incrEvent (hμ : IsPreBrownianReal canonBM μ₀) (s T : ℝ≥0) {a : ℝ}
    (ha : 0 < a) : Real.exp (-(Real.pi ^ 2 * T / (8 * a ^ 2))) ≤ μ₀.real (incrEvent s T a) := by
  have hβ := hμ.shift s
  have h := exp_le_measureReal_forall_abs_lt hβ
    (fun u => (measurable_canonBM _).sub (measurable_canonBM s))
    (fun f => ((continuous_canonBM f).comp (continuous_const.add continuous_id)).sub continuous_const)
    (fun f => by simp) ha T
  refine h.trans (measureReal_mono fun f hf u hu => (hf u hu).le)

/-! ### Positivity of the past event -/

omit [IsProbabilityMeasure μ₀] in
theorem add_eq_integral_of_isBesselPath {f : CPath} {Y : ℝ≥0 → ℝ}
    (hY : Bessel.IsBesselPath c 0 (fun t => -f.1 t) Y) (t : ℝ≥0) :
    Y t + f.1 t = ∫ s in (0 : ℝ)..t, c / Y s.toNNReal := by
  have := hY.2.2.2.2 t
  simp only [zero_add] at this
  linarith

omit [IsProbabilityMeasure μ₀] in
theorem add_le_add_of_isBesselPath (hc : 0 < c) {f : CPath} {Y : ℝ≥0 → ℝ}
    (hY : Bessel.IsBesselPath c 0 (fun t => -f.1 t) Y) {s t : ℝ≥0} (hst : s ≤ t) :
    Y s + f.1 s ≤ Y t + f.1 t := by
  rw [add_eq_integral_of_isBesselPath hY, add_eq_integral_of_isBesselPath hY]
  refine intervalIntegral.integral_mono_interval le_rfl (NNReal.coe_nonneg s)
    (by exact_mod_cast hst) (ae_of_all _ fun u => div_nonneg hc.le (hY.2.1 _))
    (hY.intervalIntegrable_div t)

/-- The past event without the gap condition. -/
def pastEvent₀ (c a b : ℝ) (s : ℝ≥0) : Set CPath :=
  {f | (∀ t ≤ s, |f.1 t| ≤ a) ∧ besY c f s + f.1 s ≤ b}

/-- **Positivity of the past event**: for `a, b > 0` and `s₁ > 0` there are `s ∈ (0, s₁]` and `g > 0` with
`ℙ(pastEvent c a b g s) > 0`. -/
theorem exists_pos_measureReal_pastEvent (hμ : IsPreBrownianReal canonBM μ₀) (hc : 0 < c) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) {s₁ : ℝ≥0} (hs₁ : 0 < s₁) :
    ∃ s : ℝ≥0, 0 < s ∧ s ≤ s₁ ∧ ∃ g : ℝ, 0 < g ∧ 0 < μ₀.real (pastEvent c a b g s) := by
  -- the good set
  set G : Set CPath := {f | Bessel.IsBesselPath c 0 (fun t => -f.1 t) (fun t => besY c f t) ∧
    f.1 0 = 0} with hG
  have hGae : ∀ᵐ f ∂μ₀, f ∈ G := by
    filter_upwards [ae_isBesselPath_besY hμ hc, hμ.eval_zero_ae_eq_zero] with f h1 h2
    exact ⟨h1, h2⟩
  have hμG : μ₀ G = 1 := by
    rw [← measure_univ (μ := μ₀)]
    exact measure_congr (ae_eq_univ.2 (by
      filter_upwards [hGae] with f hf using hf))
  -- step 1: a small time with `ℙ(pastEvent₀) ≥ 3/4`
  set sn : ℕ → ℝ≥0 := fun n => s₁ / (n + 1) with hsn
  have hsn0 : Tendsto (fun n => (sn n : ℝ)) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (s₁ : ℝ)
    rw [mul_zero] at this
    refine this.congr fun n => ?_
    simp only [hsn, NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
    ring
  have hlim : G ⊆ {f | ∀ᶠ n in atTop, f ∈ pastEvent₀ c a b (sn n)} := by
    intro f ⟨hY, hf0⟩
    have hY0 : besY c f 0 = 0 := by
      have := hY.2.2.2.2 0
      simp only [NNReal.coe_zero, intervalIntegral.integral_same, add_zero, zero_add] at this
      rw [this, hf0, neg_zero]
    have hc1 : ContinuousAt (fun t => f.1 t) 0 := f.2.continuousAt
    have hc2 : ContinuousAt (fun t => besY c f t + f.1 t) 0 := (hY.1.add f.2).continuousAt
    obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.continuousAt_iff.1 hc1 a ha
    obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.continuousAt_iff.1 hc2 b hb
    have hev : ∀ᶠ n in atTop, sn n < min δ₁ δ₂ := by
      have hm : (0 : ℝ) < min δ₁ δ₂ := lt_min hδ₁ hδ₂
      exact hsn0.eventually (gt_mem_nhds hm)
    refine hev.mono fun n hn => ⟨fun t ht => ?_, ?_⟩
    · have hd : dist t 0 < δ₁ := by
        rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg (NNReal.coe_nonneg t)]
        exact lt_of_le_of_lt (by exact_mod_cast ht) (hn.trans_le (min_le_left _ _))
      have := h₁ hd
      rw [Real.dist_eq, hf0, sub_zero] at this
      exact this.le
    · have hd : dist (sn n) 0 < δ₂ := by
        rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg (NNReal.coe_nonneg (sn n))]
        exact hn.trans_le (min_le_right _ _)
      have := h₂ hd
      rw [Real.dist_eq, hY0, hf0, add_zero, sub_zero] at this
      exact (le_abs_self _).trans this.le
  obtain ⟨n, hn⟩ := exists_measure_le_add_of_subset_liminf μ₀ hlim
    (show (0 : ℝ≥0∞) < 1 / 4 by norm_num)
  rw [hμG] at hn
  -- step 2: a time `s ∈ (0, sn n]` at which `Y` is almost surely positive (Fubini)
  have hsnpos : 0 < sn n := by
    simp only [hsn]; positivity
  set Z : Set (ℝ × CPath) := {p | p.1 ∈ Set.Ioc 0 (sn n : ℝ) ∧ besY c p.2 p.1.toNNReal = 0}
    with hZ
  have hZm : MeasurableSet Z := by
    refine (measurable_fst measurableSet_Ioc).inter ?_
    exact measurableSet_eq_fun ((measurable_besY_uncurry hc).comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)) measurable_const
  have hZ0 : (volume.prod μ₀) Z = 0 := by
    rw [Measure.prod_apply_symm hZm]
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    · filter_upwards [hGae] with f hf
      refine measure_mono_null (fun t ht => ?_) hf.1.2.2.1
      exact ⟨ht.1.1.le, ht.2⟩
  have hae := (Measure.measure_prod_null hZm).1 hZ0
  have hpos : (volume : Measure ℝ) (Set.Ioc 0 (sn n : ℝ)) ≠ 0 := by
    rw [Real.volume_Ioc]; simpa using hsnpos.ne'
  have : (ae ((volume : Measure ℝ).restrict (Set.Ioc 0 (sn n : ℝ)))).NeBot :=
    ae_restrict_neBot.2 hpos
  obtain ⟨t, ht0, htI⟩ := ((ae_restrict_of_ae (s := Set.Ioc 0 (sn n : ℝ)) hae).and
    (ae_restrict_mem (s := Set.Ioc 0 (sn n : ℝ)) (μ := volume) measurableSet_Ioc)).exists
  set s : ℝ≥0 := t.toNNReal with hs
  have hst : (s : ℝ) = t := Real.coe_toNNReal _ htI.1.le
  have hspos : 0 < s := by rw [← NNReal.coe_pos, hst]; exact htI.1
  have hsle : s ≤ sn n := by rw [← NNReal.coe_le_coe, hst]; exact htI.2
  have hY0null : μ₀ {f | besY c f s = 0} = 0 := by
    have hpre : Prod.mk t ⁻¹' Z = {f | besY c f s = 0} := by
      ext f
      simp only [hZ, Set.mem_preimage, Set.mem_ofPred_eq, hs]
      exact ⟨fun h => h.2, fun h => ⟨htI, h⟩⟩
    rw [← hpre]
    exact ht0
  -- step 3: a gap level `g`
  set A : ℕ → Set CPath := fun k => {f | besY c f s < 1 / ((k : ℝ) + 1)} with hA
  have hAm : ∀ k, MeasurableSet (A k) := fun k => measurableSet_lt (measurable_besY' hc s)
    measurable_const
  have hAanti : Antitone A := fun k l hkl f hf => by
    simp only [hA, Set.mem_ofPred_eq] at hf ⊢
    refine hf.trans_le ?_
    gcongr
  have hAinter : μ₀ (⋂ k, A k) = 0 := by
    refine measure_mono_null_ae ?_ hY0null
    filter_upwards [hGae] with f hf hfA
    simp only [hA, Set.mem_iInter, Set.mem_ofPred_eq] at hfA ⊢
    refine le_antisymm ?_ (hf.1.2.1 s)
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    linarith [hfA k]
  have htend := tendsto_measure_iInter_atTop (μ := μ₀) (fun k => (hAm k).nullMeasurableSet) hAanti
    ⟨0, measure_ne_top _ _⟩
  rw [hAinter] at htend
  obtain ⟨k, hk⟩ := (htend.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < 1 / 4 by norm_num))).exists
  refine ⟨s, hspos, hsle.trans ?_, 1 / ((k : ℝ) + 1), by positivity, ?_⟩
  · simp only [hsn]
    exact div_le_self s₁.2 (by simp)
  -- step 4: combine
  have h1 : μ₀ (pastEvent₀ c a b (sn n)) ≤ μ₀ (pastEvent₀ c a b s) := by
    refine measure_mono_ae ?_
    filter_upwards [hGae] with f hf hfE
    exact ⟨fun t ht => hfE.1 t (ht.trans hsle),
      (add_le_add_of_isBesselPath hc hf.1 hsle).trans hfE.2⟩
  have h2 : μ₀ (pastEvent₀ c a b s) ≤ μ₀ (pastEvent c a b (1 / ((k : ℝ) + 1)) s) + μ₀ (A k) := by
    refine (measure_mono fun f hf => ?_).trans (measure_union_le _ _)
    by_cases hfk : f ∈ A k
    · exact Or.inr hfk
    · exact Or.inl ⟨hf.1, hf.2, not_lt.1 hfk⟩
  have h3 : (1 : ℝ≥0∞) ≤ μ₀ (pastEvent c a b (1 / ((k : ℝ) + 1)) s) + 1 / 4 + 1 / 4 := by
    calc (1 : ℝ≥0∞) ≤ μ₀ (pastEvent₀ c a b (sn n)) + 1 / 4 := hn
      _ ≤ μ₀ (pastEvent c a b (1 / ((k : ℝ) + 1)) s) + μ₀ (A k) + 1 / 4 := by
          gcongr; exact h1.trans h2
      _ ≤ μ₀ (pastEvent c a b (1 / ((k : ℝ) + 1)) s) + 1 / 4 + 1 / 4 := by
          gcongr; exact hk.le
  have h4 : 0 < μ₀ (pastEvent c a b (1 / ((k : ℝ) + 1)) s) := by
    by_contra h0
    rw [not_lt, nonpos_iff_eq_zero] at h0
    rw [h0, zero_add] at h3
    have : (1 / 4 + 1 / 4 : ℝ≥0∞) < 1 := by
      rw [ENNReal.div_add_div_same, ENNReal.div_lt_iff (by norm_num) (by norm_num)]
      norm_num
    exact absurd h3 (not_le.2 this)
  exact ENNReal.toReal_pos h4.ne' (measure_ne_top _ _)

end Sec5

end InteractingSLE
