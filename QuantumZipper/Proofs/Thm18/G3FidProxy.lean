import QuantumZipper.Proofs.Thm18.G3ConcreteMaps
import QuantumZipper.Proofs.Section5.Prop16LocalRule

/-!
# G3 fidelity, fact F1: the proxies of the concrete scheme agree with the true objects

`handoff/G3.md` §G3-M123 lists the fidelity facts (F1)–(F4) still needed for G2 / G3-Transfer on
the concrete scheme of `G3ConcreteMaps.lean`. This file proves **F1**, deterministically and
pathwise (no probability):

* **F1 (a)** `scaleProxy_eq_scaleParam`: whenever the area approximations `areaApprox γ y` have a
  vague limit on `ℍ` — the hypothesis `∃ μ, IsVagueLimitOn H (areaApprox γ y) μ` used to pick out
  `qAreaMeasure`/`scaleParam` (Sheffield §1; `LQGMeas.measurable_qAreaMeasure_open`'s `key`) —
  the measurable proxy `scaleProxy γ y` (an infimum over rational radii of the pre-limit
  functionals `areaFun`) equals the true scale parameter `scaleParam γ y` (the infimum of the
  radii `a` with `qAreaMeasure γ y (B_a(0) ∩ ℍ) ≥ 1`). Consequently the measurable canonical
  description `canonProxy γ y` is the canonical description (1.8) `canonical γ y`
  (`canonProxy_eq_canonical`).
* **F1 (b)** `bdryM_of_bCert`: on the countable certificate `E1.M4.BCert γ y` the G3 boundary
  measure `bdryM γ y` is the true boundary length measure `qBoundaryMeasure γ y`
  (`bdryM_of_not_bCert`: off the certificate it is the junk measure `0`).

The route of (a): on a field with a vague limit, `areaFun γ (openBump U n) y` is the integral of
`openBump U n` against the limit (`areaFun_eq_of_isVagueLimitOn`), so `areaProxy γ y a` is the
true area `qAreaMeasure γ y (B_a(0) ∩ ℍ)` of the half-disc (`areaProxy_eq_qAreaMeasure`). The two
`scale` infima then agree because each set of admissible radii contains the other's radii
arbitrarily from above (`sInf_rat_le_eq_sInf`, a rational-density argument).

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §5.4, pp. 70–71 and
Figure 1.7 (the canonical description and the boundary measure of a quantum surface). The
rounding of the scale parameter to rational radii and the rational-density bookkeeping are our
own elementary arguments (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace Thm18Asm

open LQGMeas

/-! ## F1 (b): the boundary measure on its existence certificate -/

/-- **F1 (b).** On the boundary certificate, the G3 boundary measure `bdryM` is the true
boundary length measure of the field. -/
theorem bdryM_of_bCert (γ : ℝ) {y : FieldSample} (h : E1.M4.BCert γ y) :
    bdryM γ y = qBoundaryMeasure γ y := by
  rw [bdryM]
  exact ite_eq_left h

/-! ## F1 (a): the area proxy computes the true area of a half-disc -/

/-- On the existence of the vague limit, the measurable pre-limit functional `areaFun` computes
the integral of a test function against the true area measure. -/
theorem areaFun_eq_of_isVagueLimitOn {γ : ℝ} {y : FieldSample} {μ : Measure ℂ}
    (hμ : IsVagueLimitOn H (areaApprox γ y) μ) {f : ℂ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfH : tsupport f ⊆ H) :
    areaFun γ f y = ∫ z, f z ∂qAreaMeasure γ y := by
  rw [qAreaMeasure_eq hμ]
  exact (hμ.2.2 f hf hfc hfH).liminf_eq

/-- The supremum of the `areaFun` integrals against the cut-offs of an open `U ⊆ ℍ` is the true
area of `U`, when the vague limit exists. -/
theorem sup_openBump_areaFun_eq_measure_open {γ : ℝ} {y : FieldSample} {μ : Measure ℂ}
    (hμ : IsVagueLimitOn H (areaApprox γ y) μ) {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUH : U ⊆ H) (hUc : Uᶜ.Nonempty) :
    (⨆ n : ℕ, ENNReal.ofReal (areaFun γ (openBump U n) y)) = qAreaMeasure γ y U := by
  rw [measure_open_eq_iSup _ hU hUc]
  congr 1
  funext n
  have hsupp : tsupport (openBump U n) ⊆ H := (tsupport_openBump_subset U n).trans hUH
  rw [areaFun_eq_of_isVagueLimitOn hμ (continuous_openBump U n)
      (hasCompactSupport_openBump hUb n) hsupp,
    ofReal_integral_eq_lintegral_ofReal _ (ae_of_all _ fun z => openBump_nonneg U n z)]
  rw [qAreaMeasure_eq hμ]
  exact GoodSample.integrable_of_tsupport hμ.2.1 (continuous_openBump U n)
    (hasCompactSupport_openBump hUb n) hsupp

/-- **The undiscounted area proxy is the true area of a half-disc**: given the vague limit,
`areaProxy γ y a` is `qAreaMeasure γ y (B_a(0) ∩ ℍ)`. -/
theorem areaProxy_eq_qAreaMeasure {γ : ℝ} {y : FieldSample} {μ : Measure ℂ}
    (hμ : IsVagueLimitOn H (areaApprox γ y) μ) (a : ℝ) :
    areaProxy γ y a = qAreaMeasure γ y (Metric.ball (0 : ℂ) a ∩ H) := by
  have hU : IsOpen (Metric.ball (0 : ℂ) a ∩ H) := Metric.isOpen_ball.inter isOpen_H
  have hUb : Bornology.IsBounded (Metric.ball (0 : ℂ) a ∩ H) :=
    Metric.isBounded_ball.subset inter_subset_left
  have hUc : (Metric.ball (0 : ℂ) a ∩ H)ᶜ.Nonempty :=
    ⟨0, fun h => by simpa [H] using (inter_subset_right h : (0 : ℂ) ∈ H)⟩
  exact sup_openBump_areaFun_eq_measure_open hμ hU hUb inter_subset_right hUc

/-! ## F1 (a): the two scale infima -/

/-- **Rational-density bookkeeping for the scale parameter.** If a function `P` agrees with a
monotone `A` at every positive rational, then
`inf{a > 0 | ∃ q ∈ ℚ, 0 < q ≤ a, 1 ≤ P q} = inf{a > 0 | 1 ≤ A a}`:
every radius allowed by the rational condition is allowed by the second set (`A a ≥ A q ≥ 1`),
and conversely each `b` allowed by the second set is approached from above by rationals `q > b`,
which are allowed by the first set (with `a := q`). Own elementary argument. -/
theorem sInf_rat_le_eq_sInf {P A : ℝ → ℝ≥0∞}
    (hPA : ∀ q : ℚ, 0 < (q : ℝ) → P q = A q) (hmono : Monotone A) :
    sInf {a : ℝ | 0 < a ∧ ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) ≤ a ∧ 1 ≤ P q} =
      sInf {a : ℝ | 0 < a ∧ 1 ≤ A a} := by
  set S : Set ℝ := {a : ℝ | 0 < a ∧ ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) ≤ a ∧ 1 ≤ P q} with hS
  set T : Set ℝ := {a : ℝ | 0 < a ∧ 1 ≤ A a} with hT
  have hST : ∀ a ∈ S, a ∈ T := by
    intro a ha
    rw [hS] at ha
    rw [hT]
    obtain ⟨ha0, q, hq0, hqa, h1⟩ := ha
    exact ⟨ha0, (h1.trans (le_of_eq (hPA q hq0))).trans (hmono hqa)⟩
  have hbddS : BddBelow S := ⟨0, fun a ha => by rw [hS] at ha; exact ha.1.le⟩
  have hbddT : BddBelow T := ⟨0, fun a ha => by rw [hT] at ha; exact ha.1.le⟩
  have hqS : ∀ q : ℚ, 0 < (q : ℝ) → 1 ≤ P q → (q : ℝ) ∈ S := by
    intro q hq0 h1
    rw [hS]
    exact ⟨hq0, q, hq0, le_rfl, h1⟩
  have hqT : ∀ q : ℚ, 0 < (q : ℝ) → 1 ≤ P q → (q : ℝ) ∈ T := by
    intro q hq0 h1
    rw [hT]
    exact ⟨hq0, by rw [hPA q hq0] at h1; exact h1⟩
  by_cases hne : T.Nonempty
  · have hneT : T.Nonempty := hne
    obtain ⟨b, hb⟩ := hne
    rw [hT] at hb
    have hneS : S.Nonempty := by
      obtain ⟨q₀, hbq₀, -⟩ := exists_rat_btwn (show b < b + 1 by linarith)
      have hq₀0 : 0 < (q₀ : ℝ) := hb.1.trans hbq₀
      refine ⟨q₀, hqS q₀ hq₀0 ?_⟩
      rw [hPA q₀ hq₀0]
      exact hb.2.trans (hmono hbq₀.le)
    refine le_antisymm ?_ (le_csInf hneS fun a ha => ?_)
    · refine le_csInf hneT fun b' hb' => ?_
      rw [hT] at hb'
      by_contra hlt
      rw [not_le] at hlt
      obtain ⟨q, hb'q, hqs⟩ := exists_rat_btwn hlt
      have h1 : 1 ≤ P q := by
        rw [hPA q (hb'.1.trans hb'q)]
        exact hb'.2.trans (hmono hb'q.le)
      exact absurd (csInf_le hbddS (hqS q (hb'.1.trans hb'q) h1)) (not_le.2 hqs)
    · rw [hS] at ha
      obtain ⟨-, q, hq0, hqa, h1⟩ := ha
      exact (csInf_le hbddT (hqT q hq0 h1)).trans hqa
  · have hSe : S = ∅ := eq_empty_iff_forall_notMem.2 fun a ha => hne ⟨a, hST a ha⟩
    rw [hSe, not_nonempty_iff_eq_empty.1 hne]

/-- **F1 (a).** Whenever the area approximations of `y` have a vague limit on `ℍ`, the measurable
scale proxy `scaleProxy γ y` is the true scale parameter `scaleParam γ y`. -/
theorem scaleProxy_eq_scaleParam (γ : ℝ) (y : FieldSample)
    (h : ∃ μ, IsVagueLimitOn H (areaApprox γ y) μ) :
    scaleProxy γ y = scaleParam γ y := by
  obtain ⟨μ, hμ⟩ := h
  exact sInf_rat_le_eq_sInf (P := areaProxy γ y)
    (A := fun a : ℝ => qAreaMeasure γ y (Metric.ball (0 : ℂ) a ∩ H))
    (fun q _ => areaProxy_eq_qAreaMeasure hμ (q : ℝ))
    (fun a b hab => measure_mono (inter_subset_inter_left _ (Metric.ball_subset_ball hab)))

/-- **F1 (a), good samples.** Good samples have the area limit (`Prop16Area.G`), so the scale
proxy is the scale parameter there. -/
theorem scaleProxy_eq_scaleParam_of_good {γ : ℝ} {y : FieldSample} (hy : IsLQGGood γ y) :
    scaleProxy γ y = scaleParam γ y :=
  scaleProxy_eq_scaleParam γ y ⟨_, Prop16Area.G.isVagueLimitOn_H_of_good hy⟩

/-- **F1 (a), canonical description.** Under the vague limit, the measurable canonical proxy is
the canonical description (1.8) of `y`. -/
theorem canonProxy_eq_canonical {γ : ℝ} {y : FieldSample}
    (h : ∃ μ, IsVagueLimitOn H (areaApprox γ y) μ) :
    canonProxy γ y = canonical γ y := by
  rw [canonProxy, canonical, scaleProxy_eq_scaleParam γ y h]

/-- **F1 (a), canonical description on good samples.** -/
theorem canonProxy_eq_canonical_of_good {γ : ℝ} {y : FieldSample} (hy : IsLQGGood γ y) :
    canonProxy γ y = canonical γ y :=
  canonProxy_eq_canonical ⟨_, Prop16Area.G.isVagueLimitOn_H_of_good hy⟩

end Thm18Asm
end QuantumZipper
