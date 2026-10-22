import HigherDimLQGMetric.Metric.Lemma21
import LQGMetric.Metric.CurveNatural

/-!
# Weighted lengths along length-parametrized curves; the chain rule

Packet M1 (Phase A, block A2). Generic tools connecting the partition definition of the weighted
length `∫_P w ds` (Lemma 2.1, `weightedLength`) with the frozen definition of Weyl scaling, which
integrates `e^{ξ f}` along curves parametrized by length.

* `weightedLength_eq_lengthParam`: a continuous curve of finite length has the weighted length of
  its parametrization by length (mathlib's natural parametrization, LQGMetric's `lengthParam`).
* `weylDistOn_eq_iInf_unitSpeed`: for a positive continuous weight, `(w·D)(x, y; S)` is the
  infimum of `∫_0^L w(P t) dt` over unit-speed curves `P : [0, L] → S` from `x` to `y` (the shape
  of the frozen `weylScale`).
* `weightedLength_eq_lintegral_of_curveLength` (**chain rule**): if the length of `Q` on every
  subinterval `[u, t]` is `∫_u^t h`, then `∫_Q v ds = ∫ v(Q τ) h(τ) dτ`.

Elementary partition arguments; own proofs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open LQGMetric.MetricGeometry

section EMetric

variable {X : Type*} [EMetricSpace X] {w : X → ℝ}

/-- The length function `σ t = len(Q; [a, t])` of a continuous curve of finite length is
continuous on `[a, b]`. -/
theorem continuousOn_variationOnFromTo {Q : ℝ → X} {a b : ℝ} (hab : a ≤ b)
    (hQ : ContinuousOn Q (Icc a b)) (hL : curveLength Q a b ≠ ⊤) :
    ContinuousOn (variationOnFromTo Q (Icc a b) a) (Icc a b) := fun x hx =>
  ((boundedVariationOn_of_curveLength_ne_top hL).continuousWithinAt_variationOnFromTo_iff
    ⟨le_rfl, hab⟩ hx).2 (hQ x hx)

/-- **Reduction to unit speed**: the weighted length of a continuous curve of finite length `ℓ` is
that of its parametrization by length on `[0, ℓ]`. -/
theorem weightedLength_eq_lengthParam {Q : ℝ → X} {a b : ℝ} (hab : a ≤ b)
    (hQ : ContinuousOn Q (Icc a b)) (hL : curveLength Q a b ≠ ⊤) :
    weightedLength w Q a b =
      weightedLength w (lengthParam Q a b) 0 (curveLength Q a b).toReal := by
  set σ := variationOnFromTo Q (Icc a b) a with hσ
  have hbv : BoundedVariationOn Q (Icc a b) := hL
  have hσm : MonotoneOn σ (Icc a b) :=
    variationOnFromTo.monotoneOn hbv.locallyBoundedVariationOn ⟨le_rfl, hab⟩
  have hσc : ContinuousOn σ (Icc a b) := continuousOn_variationOnFromTo hab hQ hL
  have hσa : σ a = 0 := variationOnFromTo.self _ _ _
  have hσb : σ b = (curveLength Q a b).toReal := by
    rw [hσ, variationOnFromTo.eq_of_le _ _ hab, inter_self]; rfl
  rw [← hσa, ← hσb, ← weightedLength_comp_monotoneOn hab hσc hσm]
  exact weightedLength_congr fun t ht => (lengthParam_variationOnFromTo hL ht).symm

/-- The parametrization by length of a curve in `S` stays in `S`, with the same endpoints. -/
theorem lengthParam_props {Q : ℝ → X} {a b : ℝ} (hab : a ≤ b) (hQ : ContinuousOn Q (Icc a b))
    (hL : curveLength Q a b ≠ ⊤) {S : Set X} (hS : MapsTo Q (Icc a b) S) :
    HasUnitSpeedOn (lengthParam Q a b) (Icc 0 (curveLength Q a b).toReal) ∧
      ContinuousOn (lengthParam Q a b) (Icc 0 (curveLength Q a b).toReal) ∧
      lengthParam Q a b 0 = Q a ∧ lengthParam Q a b (curveLength Q a b).toReal = Q b ∧
      MapsTo (lengthParam Q a b) (Icc 0 (curveLength Q a b).toReal) S := by
  have himg := variationOnFromTo_image_Icc hab hQ hL
  refine ⟨hasUnitSpeedOn_lengthParam hab hQ hL,
    (lipschitzOnWith_lengthParam hab hQ hL).continuousOn, ?_, ?_, ?_⟩
  · have := lengthParam_variationOnFromTo hL (⟨le_rfl, hab⟩ : a ∈ Icc a b)
    rwa [variationOnFromTo.self] at this
  · have := lengthParam_variationOnFromTo hL (⟨hab, le_rfl⟩ : b ∈ Icc a b)
    rwa [variationOnFromTo.eq_of_le _ _ hab, inter_self] at this
  · intro u hu
    rw [← himg] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    rw [lengthParam_variationOnFromTo hL ht]
    exact hS ht

/-- **Unit-speed form** of `(w·D)(x, y; S)` for a positive continuous weight: the infimum of
`∫_0^L w(P t) dt` over unit-speed curves `P : [0, L] → S` from `x` to `y` (the shape of the frozen
`weylScale`). -/
theorem weylDistOn_eq_iInf_unitSpeed {S : Set X} (hw : ContinuousOn w S)
    (hpos : ∀ x ∈ S, 0 < w x) (x y : X) :
    weylDistOn w S x y = ⨅ (L : ℝ) (P : ℝ → X) (_ : 0 ≤ L) (_ : ContinuousOn P (Icc 0 L))
      (_ : HasUnitSpeedOn P (Icc 0 L)) (_ : P 0 = x) (_ : P L = y)
      (_ : ∀ t ∈ Icc 0 L, P t ∈ S), ∫⁻ t in Icc 0 L, ENNReal.ofReal (w (P t)) := by
  apply le_antisymm
  · simp only [le_iInf_iff]
    intro L P hL hc hu h0 h1 hS
    rw [← weightedLength_of_hasUnitSpeedOn hL hu (hw.comp hc fun t ht => hS t ht), ← h0, ← h1]
    exact weylDistOn_le_of_curve hL hc fun t ht => hS t ht
  · refine le_weylDistOn fun Q hc h0 h1 hS => ?_
    by_cases hL : curveLength Q 0 1 = ⊤
    · obtain ⟨m, M, hm, hmM⟩ := exists_bounds_along hw hpos zero_le_one hc hS
      rw [weightedLength_eq_top hm zero_le_one (fun s hs => (hmM s hs).1) hL]
      exact le_top
    obtain ⟨hu, hcP, hP0, hPL, hPS⟩ := lengthParam_props zero_le_one hc hL hS
    rw [weightedLength_eq_lengthParam zero_le_one hc hL,
      weightedLength_of_hasUnitSpeedOn ENNReal.toReal_nonneg hu (hw.comp hcP hPS)]
    exact iInf_le_of_le _ <| iInf_le_of_le _ <| iInf_le_of_le ENNReal.toReal_nonneg <|
      iInf_le_of_le hcP <| iInf_le_of_le hu <| iInf_le_of_le (hP0.trans h0) <|
      iInf_le_of_le (hPL.trans h1) <| iInf_le_of_le (fun t ht => hPS ht) le_rfl

end EMetric

section Chain

variable {Y : Type*} [PseudoEMetricSpace Y] {v : Y → ℝ} {Q : ℝ → Y} {h : ℝ → ℝ} {a b : ℝ}

/-- **Chain rule** for weighted lengths: if `len(Q; [u, t]) = ∫_u^t h` for `a ≤ u ≤ t ≤ b` and the
total is finite, then `∫_Q v ds = ∫_a^b v(Q τ) h(τ) dτ` (`v ∘ Q` continuous on `[a, b]`). -/
theorem weightedLength_eq_lintegral_of_curveLength (hab : a ≤ b)
    (hlen : ∀ u t, a ≤ u → u ≤ t → t ≤ b →
      curveLength Q u t = ∫⁻ τ in Icc u t, ENNReal.ofReal (h τ))
    (hfin : curveLength Q a b ≠ ⊤) (hv : ContinuousOn (fun t => v (Q t)) (Icc a b)) :
    weightedLength v Q a b =
      ∫⁻ τ in Icc a b, ENNReal.ofReal (v (Q τ)) * ENNReal.ofReal (h τ) := by
  set F : ℝ → ℝ≥0∞ := fun τ => ENNReal.ofReal (v (Q τ)) * ENNReal.ofReal (h τ) with hF
  have hIoc : ∀ u t, a ≤ u → u ≤ t → t ≤ b →
      curveLength Q u t = ∫⁻ τ in Ioc u t, ENNReal.ofReal (h τ) := fun u t h1 h2 h3 => by
    rw [hlen u t h1 h2 h3, setLIntegral_congr Ioc_ae_eq_Icc]
  apply le_antisymm
  · refine partitionSup_le fun p => ?_
    have hmono : Monotone fun i => p.t (min i p.n) := fun i j hij =>
      p.le_t (min_le_min_right p.n hij) (min_le_right _ _)
    calc p.sum (fun u v' => infAlong v Q u v' * curveLength Q u v')
        ≤ ∑ i ∈ Finset.range p.n, ∫⁻ τ in Ioc (p.t (min i p.n)) (p.t (min (i + 1) p.n)), F τ := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' := Finset.mem_range.1 hi
          rw [min_eq_left hi'.le, min_eq_left (by omega)]
          obtain ⟨h1, h2, h3⟩ := p.step hi'
          show infAlong v Q (p.t i) (p.t (i + 1)) * curveLength Q (p.t i) (p.t (i + 1)) ≤ _
          rw [hIoc _ _ h1 h2 h3, ← lintegral_const_mul' _ _ (infAlong_ne_top h2)]
          exact setLIntegral_mono' measurableSet_Ioc fun τ hτ =>
            mul_le_mul' (infAlong_le ⟨hτ.1.le, hτ.2⟩) le_rfl
      _ = ∫⁻ τ in Ioc (p.t 0) (p.t p.n), F τ := by
          rw [sum_setLIntegral_Ioc F hmono p.n]
          simp only [Nat.zero_min, min_self]
      _ ≤ ∫⁻ τ in Icc a b, F τ := by
          rw [p.zero, p.last]
          exact lintegral_mono_set Ioc_subset_Icc_self
  · refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
    set L := curveLength Q a b with hLdef
    set ε : ℝ := η / (L.toReal + 1) with hεdef
    have hεpos : 0 < ε := div_pos (by exact_mod_cast hη) (by positivity)
    obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1
      (isCompact_Icc.uniformContinuousOn_of_continuous hv) ε hεpos
    obtain ⟨N, hN, hNδ⟩ := exists_uniform_fine hab hδ
    set p := IccPartition.uniform hab N hN with hp
    have hstep : ∀ k, p.t (k + 1) - p.t k = (b - a) / N := IccPartition.uniform_step hab N hN
    have hmono : Monotone p.t := fun i j hij => by
      show a + (i : ℝ) * ((b - a) / N) ≤ a + (j : ℝ) * ((b - a) / N)
      have : 0 ≤ (b - a) / N := div_nonneg (sub_nonneg.2 hab) (Nat.cast_nonneg N)
      gcongr
    have hpiece : ∀ k < N, ∀ τ ∈ Icc (p.t k) (p.t (k + 1)),
        ENNReal.ofReal (v (Q τ)) ≤ infAlong v Q (p.t k) (p.t (k + 1)) + ENNReal.ofReal ε := by
      intro k hk τ hτ
      have hsub : Icc (p.t k) (p.t (k + 1)) ⊆ Icc a b :=
        Icc_subset_Icc (p.mem_Icc hk.le).1 (p.mem_Icc (Nat.succ_le_of_lt hk)).2
      rw [← tsub_le_iff_right]
      refine le_infAlong fun σ hσ => ?_
      rw [tsub_le_iff_right]
      have hdist : dist τ σ < δ := by
        rw [Real.dist_eq, abs_lt]
        have := hstep k
        constructor <;> linarith [hτ.1, hτ.2, hσ.1, hσ.2]
      have h1 := hδ' τ (hsub hτ) σ (hsub hσ) hdist
      rw [Real.dist_eq, abs_lt] at h1
      calc ENNReal.ofReal (v (Q τ)) ≤ ENNReal.ofReal (v (Q σ) + ε) :=
            ENNReal.ofReal_le_ofReal (by linarith [h1.2])
        _ ≤ ENNReal.ofReal (v (Q σ)) + ENNReal.ofReal ε := ENNReal.ofReal_add_le
    have hp0 : p.t 0 = a := p.zero
    have hpN : p.t N = b := p.last
    have hlenk : ∀ k < N, curveLength Q (p.t k) (p.t (k + 1)) =
        ∫⁻ τ in Ioc (p.t k) (p.t (k + 1)), ENNReal.ofReal (h τ) := fun k hk =>
      hIoc _ _ (p.mem_Icc hk.le).1 (hmono (Nat.le_succ k)) (p.mem_Icc (Nat.succ_le_of_lt hk)).2
    have hsumlen : ∑ k ∈ Finset.range N, curveLength Q (p.t k) (p.t (k + 1)) = L := by
      rw [sum_curveLength_eq Q hmono N, hp0, hpN]
    calc ∫⁻ τ in Icc a b, F τ = ∫⁻ τ in Ioc a b, F τ := (setLIntegral_congr Ioc_ae_eq_Icc).symm
      _ = ∑ k ∈ Finset.range N, ∫⁻ τ in Ioc (p.t k) (p.t (k + 1)), F τ := by
          rw [sum_setLIntegral_Ioc F hmono N, hp0, hpN]
      _ ≤ ∑ k ∈ Finset.range N, (infAlong v Q (p.t k) (p.t (k + 1)) + ENNReal.ofReal ε) *
            curveLength Q (p.t k) (p.t (k + 1)) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' := Finset.mem_range.1 hk
          rw [hlenk k hk', ← lintegral_const_mul' _ _
            (ENNReal.add_ne_top.2 ⟨infAlong_ne_top (hmono (Nat.le_succ k)), ENNReal.ofReal_ne_top⟩)]
          exact setLIntegral_mono' measurableSet_Ioc fun τ hτ =>
            mul_le_mul' (hpiece k hk' τ ⟨hτ.1.le, hτ.2⟩) le_rfl
      _ = p.sum (fun u v' => infAlong v Q u v' * curveLength Q u v') + ENNReal.ofReal ε * L := by
          simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hsumlen]
          rfl
      _ ≤ weightedLength v Q a b + η := by
          refine add_le_add (le_partitionSup p) ?_
          rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul hεpos.le,
            ← ENNReal.ofReal_coe_nnreal]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hεdef, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith [η.coe_nonneg, (ENNReal.toReal_nonneg : 0 ≤ L.toReal)]

end Chain

end HigherDimLQGMetric
