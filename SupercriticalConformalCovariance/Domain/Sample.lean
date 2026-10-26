import SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylShift.WeylSample
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylShift.WeylLocalTopology
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.GapChecks.Gapc2
import SupercriticalLQGUniqueness.B2.Strong.WeakOfStrong

/-!
# The common sample event of a whole-plane GFF plus a continuous function

For a strong LQG metric `D` and a whole-plane GFF plus a continuous
function `h` (`LQGMetric.IsGFFPlusCont`, not necessarily normalized, the continuous part unbounded),
almost surely:
* the identity `(ℂ, D_h) → ℂ` is continuous (every `D_h`-curve is Euclidean-continuous);
* `(ℂ, D_h)` is a length space (Axiom I);
* `e^{ξ g} · D_h = D_{h + g}` for every continuous `g` (Axiom III).

The first item is proved from the normalized decomposition `h = k + F'`
(`Uniqueness.TwoScale.GapChecks.exists_normalized_decomposition`), the escape barrier for the
normalized field (`Uniqueness.Toolkit.WeylShift.ae_common_weyl_sample`) and the local topology
comparison for unbounded continuous Weyl shifts (`Uniqueness.Toolkit.WeylShift.continuous_forget_of_weyl`).

Also: `isGFFPlusCont_addFun_of_measurable`, a whole-plane GFF plus a continuous function plus a
measurable random continuous function is again one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalConformalCovariance.Domain

open LQGMetric (DistC DistOn restrictTo IsGFFPlusCont IsWholePlaneGFF ofCont addFun)
open SupercriticalLQGUniqueness (LSCMetric IsStrongLQGMetric weylScale)

/-- The identity map `(ℂ, D) → ℂ` (the sealed `Barrier.forget`). -/
abbrev forget (D : LSCMetric) : D.Space → ℂ :=
  SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.forget D

theorem ofCont_add (f g : C(ℂ, ℝ)) : ofCont (f + g) = ofCont f + ofCont g := by
  ext φ
  rw [add_apply, LQGMetric.ofCont_apply, LQGMetric.ofCont_apply,
    LQGMetric.ofCont_apply]
  simp only [ContinuousMap.add_apply, mul_add]
  exact integral_add
    ((φ.continuous.mul f.continuous).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_right)
    ((φ.continuous.mul g.continuous).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_right)

/-- A whole-plane GFF plus a continuous function, plus a measurable random continuous function, is a
whole-plane GFF plus a continuous function. -/
theorem isGFFPlusCont_addFun_of_measurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsGFFPlusCont h P) {F : Ω → C(ℂ, ℝ)} (hF : Measurable F) :
    IsGFFPlusCont (fun ω => addFun (h ω) (F ω)) P := by
  obtain ⟨hm, g, hg, hgff⟩ := hh
  refine ⟨LQGMetric.measurable_addFun.comp (hm.prodMk hF), fun ω => g ω + F ω, ?_, ?_⟩
  · rw [ContinuousMap.measurable_iff_eval]
    intro x
    simp only [ContinuousMap.add_apply]
    exact ((ContinuousMap.measurable_eval x).comp hg).add
      ((ContinuousMap.measurable_eval x).comp hF)
  · have e : (fun ω => addFun (h ω) (F ω) - ofCont (g ω + F ω)) = fun ω => h ω - ofCont (g ω) := by
      funext ω
      rw [addFun, ofCont_add]
      abel
    rw [e]
    exact hgff

/-- **The common sample event.** For a strong LQG metric and a whole-plane GFF plus a continuous
function `h`, almost surely `(ℂ, D_h) → ℂ` is continuous, `D_h` is a length space, and Axiom III
holds for every continuous shift. -/
theorem ae_sample_of_isGFFPlusCont {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsGFFPlusCont h P) :
    ∀ᵐ ω ∂P, Continuous (forget (D (h ω))) ∧ (D (h ω)).IsLengthSpace ∧
      ∀ g : C(ℂ, ℝ), weylScale (ξ : ℝ) g (D (h ω)) = (D (addFun (h ω) g)).1 := by
  have hW := SupercriticalLQGUniqueness.B2.Strong.isWeakLQGMetric_of_isStrongLQGMetric hD
  obtain ⟨k, F', hkn, -, -, hrep⟩ :=
    SupercriticalLQGUniqueness.Uniqueness.TwoScale.GapChecks.exists_normalized_decomposition hh
  filter_upwards [SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylShift.ae_common_weyl_sample
      hW P k hkn, hD.2.1 P h hh, hD.2.2.2.1 P h hh] with ω hk hL hWh
  obtain ⟨hfk, -, hwk⟩ := hk
  refine ⟨?_, hL, hWh⟩
  have hE : ∀ q : ℂ × ℂ, (D (h ω)) q = weylScale (ξ : ℝ) (F' ω) (D (k ω)) q := by
    intro q
    rw [hwk (F' ω), ← hrep ω]
  exact SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylShift.continuous_forget_of_weyl
    (D (k ω)) (D (h ω)) (ξ : ℝ) (le_of_lt ξ.2) (F' ω) hfk hE

end SupercriticalConformalCovariance.Domain
