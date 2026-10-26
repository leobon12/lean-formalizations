import SupercriticalConformalCovariance.BiLip.L51.Meas
import SupercriticalConformalCovariance.BiLip.Local
import SupercriticalLQGUniqueness.Uniqueness.Positivity.FromAxioms.AXPOSComplete
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Prob

/-!
# Lemma 5.1: the literal event as an event of the centred fields

For an instance and `c = h_{3r}(z)`, let `h_c = h − c`, `k_c = k − c` (so `(g₀, k_c)` realizes `h_c^φ`,
`isDomainRealization_forward_add_const`) and `G_c = g₀ + χ_m k_c` with `φ(cl A_{r/2,2r}(z)) ⊆ W_m`.

`ae_goodEvent_iff`: almost surely

  `ω ∈ F_{z,r}  ↔  (h_c ω, G_c ω) ∈ Bset`,

where `Bset` uses `ehat(G_c) = D_{G_c}(φ ·, φ ·; φ(cl A))` in place of `e`. The ingredients are:
* Weyl scaling by the constant `c`: `D_h = e^{ξ c} D_{h_c}` (Axiom III) and
  `e = e^{ξ c} e_c` (`domainMetric_add_const`), with the circle average shifted by `c`;
* homogeneity of the event (`good_scale_iff`);
* the shield for the centred instance (`good_congr_ehat`), whose comparison follows from the given one by
  the same scaling.

Sample properties used: Barrier and length space for `D_h` (SLU `ae_barrier`, Axiom I), finiteness of
`D_h(M, ∂A)` (`ae_acrossDist_dilate_lt_top`), and the `g₀` sample event.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set Metric Filter Topology MeasureTheory TopologicalSpace
open scoped ENNReal

namespace SupercriticalConformalCovariance.BiLip.L51

open SupercriticalLQGUniqueness (LSCMetric IsStrongLQGMetric IsCircleAverage acrossDist)
open SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events (eventCarrier eventMiddle eventBoundary)
open SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios (setDist)
open SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier (Barrier dyadicAnnulus)
open SupercriticalConformalCovariance (IsConformalBijection domainMetric)
open LQGMetric (DistC addFun addConst IsGFFPlusCont)
open SupercriticalConformalCovariance.Domain (exW cutF)

/-- the barrier event is scale invariant -/
theorem barrier_of_scale {d₁ d₂ : LSCMetric} {k : ℝ≥0∞} (hk0 : k ≠ 0) (hkt : k ≠ ⊤)
    (hd : ∀ x y, d₂ (x, y) = k * d₁ (x, y)) (hB : Barrier d₁) : Barrier d₂ := by
  intro n₀ M
  have hMk : (M : ℝ≥0∞) / k ≠ ⊤ := ENNReal.div_ne_top (by simp) hk0
  obtain ⟨M', hM'⟩ := ENNReal.exists_nat_gt hMk
  obtain ⟨n, hn, hlt⟩ := hB n₀ M'
  refine ⟨n, hn, ?_⟩
  rw [SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.acrossDist_eq_mul_of_dist_scale
    d₁ d₂ k hk0 hkt hd]
  calc (M : ℝ≥0∞) ≤ k * M' := by
        rw [ENNReal.div_lt_iff (Or.inl hk0) (Or.inl hkt)] at hM'
        rw [mul_comm]; exact hM'.le
    _ < k * acrossDist d₁ (dyadicAnnulus n) := (ENNReal.mul_lt_mul_iff_right hk0 hkt).2 hlt

theorem barrier_measurableSet {D : DistC → LSCMetric} (hD : Measurable D) :
    MeasurableSet {g : DistC | Barrier (D g)} := by
  have e : {g : DistC | Barrier (D g)} = ⋂ n₀ : ℕ, ⋂ M : ℕ, ⋃ n : ℕ,
      {g : DistC | n₀ ≤ n ∧ (M : ℝ≥0∞) < acrossDist (D g) (dyadicAnnulus n)} := by
    ext g; simp only [mem_setOf_eq, mem_iInter, mem_iUnion, Barrier]
  rw [e]
  refine MeasurableSet.iInter fun n₀ => MeasurableSet.iInter fun M => MeasurableSet.iUnion fun n => ?_
  by_cases hn : n₀ ≤ n
  · simp only [hn, true_and]
    exact measurableSet_lt measurable_const
      ((SupercriticalLQGUniqueness.measurable_acrossDist (dyadicAnnulus n)).comp hD)
  · simp only [hn, false_and, setOf_false, MeasurableSet.empty]

/-- constant shift of the domain weight (as `SupercriticalConformalCovariance.Transport.domainMetric_add_const`) -/
theorem domainMetric_add_const' (ξ : ℝ) (hξ : 0 ≤ ξ) (D : DistC → LSCMetric) (V : Opens ℂ)
    (h₀ : DistC) (f : C(V, ℝ)) (c : ℝ) (p : V × V) :
    domainMetric ξ D V h₀ (f + ContinuousMap.const V c) p =
      ENNReal.ofReal (Real.exp (ξ * c)) * domainMetric ξ D V h₀ f p :=
  le_antisymm (SupercriticalConformalCovariance.Domain.weylScaleOn_add_le hξ f (ContinuousMap.const V c) (fun _ => le_rfl) p)
    (SupercriticalConformalCovariance.Domain.le_weylScaleOn_add hξ f (ContinuousMap.const V c) (fun _ => le_rfl) p)

section Event

variable {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}

/-- **The literal event is a.s. the event of the centred fields.** -/
theorem ae_goodEvent_iff (hD : IsStrongLQGMetric ξ Q D) {U V : Opens ℂ} {φ : ℂ → ℂ}
    (hφ : IsConformalBijection φ U V) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h g₀ : Ω → DistC} {f : Ω → C(V, ℝ)}
    (hI : SupercriticalConformalCovariance.BiLip.IsInstance Q U V hφ P h g₀ f) {C : ℝ} (hC : 1 ≤ C)
    (hcmp : ∀ᵐ ω ∂P, ∀ u v : U,
      ENNReal.ofReal C⁻¹ * (D (h ω)).internal U (u, v) ≤
          domainMetric (ξ : ℝ) D V (g₀ ω) (f ω) (⟨φ u, hφ.2.mapsTo u.2⟩, ⟨φ v, hφ.2.mapsTo v.2⟩) ∧
        domainMetric (ξ : ℝ) D V (g₀ ω) (f ω) (⟨φ u, hφ.2.mapsTo u.2⟩, ⟨φ v, hφ.2.mapsTo v.2⟩) ≤
          ENNReal.ofReal C * (D (h ω)).internal U (u, v))
    (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ)) (θ : Ioi (0 : ℝ))
    (η : ℝ) {z : ℂ} {r : ℝ} (hr : 0 < r) (hYU : eventCarrier z r ⊆ U) {m : ℕ}
    (hm : φ '' eventCarrier z r ⊆ exW V m) :
    ∀ᵐ ω ∂P,
      (ω ∈ SupercriticalConformalCovariance.Good.GoodEvent h (D ∘ h) (fun ω => SupercriticalConformalCovariance.Good.transportedE (ξ : ℝ) D hφ (g₀ ω) (f ω))
          ξ Q q a K θ (SupercriticalConformalCovariance.Good.shieldK C) η z r ↔
        ((addConst (h ω) (-SupercriticalConformalCovariance.BiLip.ctr (h ω) z r)),
          addFun (g₀ ω) (cutF V m (f ω + ContinuousMap.const V (-SupercriticalConformalCovariance.BiLip.ctr (h ω) z r)))) ∈
          Bset D (eventCarrier z r) φ ξ Q z ⟨r, hr⟩ q a K θ (SupercriticalConformalCovariance.Good.shieldK C) η) := by
  set rr : Ioi (0 : ℝ) := ⟨r, hr⟩ with hrr
  obtain ⟨hhn, hR⟩ := hI
  have hh := hhn.1
  set c : Ω → ℝ := fun ω => SupercriticalConformalCovariance.BiLip.ctr (h ω) z r with hcdef
  have hcm : Measurable c := (LQGMetric.measurable_circleAvg_left (3 * r) z).comp hh.measurable
  have hhc : IsGFFPlusCont (fun ω => addConst (h ω) (-c ω)) P :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp (hh.addConst hcm.neg)
  have hW := SupercriticalLQGUniqueness.B2.Strong.isWeakLQGMetric_of_isStrongLQGMetric hD
  have hQ0 : 0 < Q := SupercriticalLQGUniqueness.Uniqueness.Positivity.FromAxioms.axpos ξ Q D hW
  have hξ0 : (0 : ℝ) ≤ ξ := le_of_lt ξ.2
  filter_upwards [hcmp, SupercriticalConformalCovariance.Domain.ae_sample_of_isGFFPlusCont hD P g₀ hR.2.1,
    SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.ae_barrier hW hQ0 P h hhn,
    hD.2.1 P (fun ω => addConst (h ω) (-c ω)) hhc,
    SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.ae_addConst_eq_mul P _ hhc ξ Q D hW c,
    SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.ae_acrossDist_dilate_lt_top ξ Q D hW P h hhn
      (SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.halfAnnShape z rr) rr]
    with ω hcω hs hBh hLc hsc hfin
  obtain ⟨hf₀, hL₀, hWeyl⟩ := hs
  set hc := addConst (h ω) (-c ω) with hhcdef
  set lam : ℝ≥0∞ := ENNReal.ofReal (Real.exp (ξ * c ω)) with hlam
  have hl0 : lam ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hlt : lam ≠ ⊤ := ENNReal.ofReal_ne_top
  have hhω : addConst hc (c ω) = h ω := SupercriticalConformalCovariance.BiLip.addConst_ctr_eq (h ω) (c ω)
  -- the source scaling
  have hscale : ∀ x y : ℂ, D (h ω) (x, y) = lam * D hc (x, y) := by
    intro x y; have := hsc (x, y); rwa [hhω] at this
  have hlinv : lam⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hlt
  have hlinvt : lam⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hl0
  have hscale' : ∀ x y : ℂ, D hc (x, y) = lam⁻¹ * D (h ω) (x, y) := by
    intro x y
    rw [hscale, ← mul_assoc, ENNReal.inv_mul_cancel hl0 hlt, one_mul]
  have hBc : Barrier (D hc) := barrier_of_scale hlinv hlinvt hscale' hBh
  have hSt : setDist (D hc) (eventMiddle z r) (eventBoundary z r) < ⊤ := by
    have h1 := (SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.setDist_middle_le_across
      (D (h ω)) z rr).trans_lt hfin
    rw [SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.setDist_eq_mul_of_scale hl0 hlt hscale] at h1
    exact (SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.mul_lt_top_iff_of_ne hl0 hlt _).1 h1
  -- the target scaling
  set kc : C(V, ℝ) := f ω + ContinuousMap.const V (-c ω) with hkcdef
  have hdm : ∀ p, domainMetric (ξ : ℝ) D V (g₀ ω) (f ω) p =
      lam * domainMetric (ξ : ℝ) D V (g₀ ω) kc p := by
    intro p
    have e := domainMetric_add_const' (ξ : ℝ) hξ0 D V (g₀ ω) (f ω) (-c ω) p
    rw [e, ← mul_assoc, hlam, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    simp
  have htE : ∀ p, SupercriticalConformalCovariance.Good.transportedE (ξ : ℝ) D hφ (g₀ ω) (f ω) p =
      lam * SupercriticalConformalCovariance.Good.transportedE (ξ : ℝ) D hφ (g₀ ω) kc p := by
    intro p
    unfold SupercriticalConformalCovariance.Good.transportedE
    split_ifs with hp
    · exact hdm _
    · exact (ENNReal.mul_top hl0).symm
  -- the comparison for the centred instance
  have hint : ∀ u v : U, (D (h ω)).internal U (u, v) = lam * (D hc).internal U (u, v) :=
    fun u v => SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.internal_eq_mul_of_dist_scale
      (D hc) (D (h ω)) lam hl0 hlt hscale U (u, v)
  have hcmpc : ∀ u v : U,
      ENNReal.ofReal C⁻¹ * (D hc).internal U (u, v) ≤
          domainMetric (ξ : ℝ) D V (g₀ ω) kc (⟨φ u, hφ.2.mapsTo u.2⟩, ⟨φ v, hφ.2.mapsTo v.2⟩) ∧
        domainMetric (ξ : ℝ) D V (g₀ ω) kc (⟨φ u, hφ.2.mapsTo u.2⟩, ⟨φ v, hφ.2.mapsTo v.2⟩) ≤
          ENNReal.ofReal C * (D hc).internal U (u, v) := by
    intro u v
    obtain ⟨h1, h2⟩ := hcω u v
    rw [hint, hdm] at h1 h2
    refine ⟨?_, ?_⟩
    · rw [mul_left_comm] at h1
      exact (SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.scale_le_iff hl0 hlt _ _).1 h1
    · rw [mul_left_comm (ENNReal.ofReal C)] at h2
      exact (SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.scale_le_iff hl0 hlt _ _).1 h2
  -- the cut-off target field and the shield
  have hFk : ∀ y (hy : y ∈ (V : Set ℂ)), y ∈ φ '' eventCarrier z r →
      cutF V m kc y = kc ⟨y, hy⟩ := fun y hy hyK => SupercriticalConformalCovariance.Domain.cutF_eq V m kc y (hm hyK)
  have hcongr := fun c' => good_congr_ehat (ξ : ℝ) hξ0 D hφ hc (g₀ ω) kc hf₀ hL₀ hWeyl hBc
    hLc hC hcmpc (r := rr) hYU (cutF V m kc) hFk hSt Q q a K θ c' η
  -- the circle average
  have hCA : ∀ c', IsCircleAverage (h ω) rr z c' ↔ IsCircleAverage hc rr z (c' - c ω) := by
    intro c'
    have := SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.isCircleAverage_addConst hc (c ω)
      rr z (c' - c ω)
    rw [sub_add_cancel, hhω] at this
    exact this
  -- the chain
  have hD₁ : ∀ x y, D (h ω) (x, y) = ENNReal.ofReal (Real.exp ((ξ : ℝ) * c ω)) * D hc (x, y) :=
    hscale
  have hgs := fun c'' => good_scale_iff (d₁ := D hc) (d₂ := D (h ω))
    (e₁ := SupercriticalConformalCovariance.Good.transportedE (ξ : ℝ) D hφ (g₀ ω) kc)
    (e₂ := SupercriticalConformalCovariance.Good.transportedE (ξ : ℝ) D hφ (g₀ ω) (f ω)) (c ω) hD₁ htE Q z rr q a K θ
    (SupercriticalConformalCovariance.Good.shieldK C) c'' η
  constructor
  · rintro ⟨hr', c', hc', hG⟩
    refine ⟨c' - c ω, (hCA c').1 hc', ?_⟩
    have hG' : SupercriticalConformalCovariance.Improve.Good (D (h ω)) (SupercriticalConformalCovariance.Good.transportedE (ξ : ℝ) D hφ (g₀ ω) (f ω)) ξ Q z rr
        q a K θ (SupercriticalConformalCovariance.Good.shieldK C) (c' - c ω + c ω) η := by rw [sub_add_cancel]; exact hG
    exact (hcongr _).1 ((hgs _).1 hG')
  · rintro ⟨c'', hc'', hG⟩
    refine ⟨hr, c'' + c ω, (hCA _).2 (by rw [add_sub_cancel_right]; exact hc''), ?_⟩
    exact (hgs c'').2 ((hcongr _).2 hG)

end Event

end SupercriticalConformalCovariance.BiLip.L51
