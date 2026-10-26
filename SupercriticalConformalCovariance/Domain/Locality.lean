import SupercriticalLQGUniqueness.Frozen.IsStrongLQGMetric
import SmallGammaGeodesics.CC.UniversalLocality

/-!
# Universal locality for the strong (supercritical) LQG metric, by coin mixture

Port of
`SmallGammaGeodesics.CC.universalLocality` (`CC/UniversalLocality.lean:160`, continuous metrics) to
the sealed `SupercriticalLQGUniqueness.IsStrongLQGMetric` (lower semicontinuous metrics,
`LSCMetric.internal`).

Axiom II (locality, conjunct 3 of `IsStrongLQGMetric`) gives, for **one** whole-plane GFF plus a
continuous function `g` and an open `U`, a measurable `F` with `D_g(·,·;U) = F(g|_U)` a.s.; `F` is only
determined up to null sets of the law of `g|_U`. The coin mixture produces **one** functional for
countably many such fields, on possibly different probability spaces (the mixture-measure and law
lemmas are reused from `SmallGammaGeodesics.CC`; they do not involve the metric).

* `universalLocality_lsc`: one functional for countably many fields;
* `ae_internal_eq_of_ae_restrictTo_eq_lsc` (**pathwise locality**): if two whole-plane GFFs plus
  continuous functions on one probability space agree on `U` a.s., their internal metrics on `U`
  agree a.s.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalConformalCovariance.Domain

open LQGMetric (DistC DistOn restrictTo IsGFFPlusCont IsWholePlaneGFF ofCont)
open SupercriticalLQGUniqueness (LSCMetric IsStrongLQGMetric)
open SmallGammaGeodesics.CC (mixMeasure exists_pos_weights isProbabilityMeasure_mixMeasure
  measurable_of_sigma map_mixMeasure sum_smul_eq_of_tsum_eq_one ae_of_ae_mixMeasure
  isWholePlaneGFF_of_map_pairProc_eq)

/-- **Universal locality** for a strong LQG metric (port of `SmallGammaGeodesics.CC.universalLocality`):
countably many whole-plane GFFs plus continuous functions, on possibly different probability spaces,
share one measurable locality functional on each open set. -/
theorem universalLocality_lsc {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D) (U : TopologicalSpace.Opens ℂ)
    (ι : Type) [Countable ι] (Ω : ι → Type) [∀ i, MeasurableSpace (Ω i)]
    (P : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (P i)]
    (g : ∀ i, Ω i → DistC) (hg : ∀ i, IsGFFPlusCont (g i) (P i)) :
    ∃ F : DistOn U → (↥(U : Set ℂ) × ↥(U : Set ℂ) → ℝ≥0∞), Measurable F ∧
      ∀ i, ∀ᵐ ω ∂P i, (D (g i ω)).internal (U : Set ℂ) = F (restrictTo U (g i ω)) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨fun _ _ => 0, measurable_const, fun i => (IsEmpty.false i).elim⟩
  obtain ⟨w, hw0, hw1⟩ := exists_pos_weights ι
  choose f hfm hfg using fun i => (hg i).2
  have : IsProbabilityMeasure (mixMeasure w P) := isProbabilityMeasure_mixMeasure hw1
  set Y : Sigma Ω → DistC := fun p => g p.1 p.2 with hYdef
  set fY : Sigma Ω → C(ℂ, ℝ) := fun p => f p.1 p.2 with hfYdef
  have hYm : Measurable Y := measurable_of_sigma fun i => (hg i).1
  have hfYm : Measurable fY := measurable_of_sigma fun i => hfm i
  have hXm : Measurable fun p => Y p - ofCont (fY p) :=
    measurable_of_sigma fun i => (hfg i).measurable
  obtain ⟨i₀⟩ := hι
  have hX : IsWholePlaneGFF (fun p => Y p - ofCont (fY p)) (mixMeasure w P) := by
    refine isWholePlaneGFF_of_map_pairProc_eq hXm (hfg i₀) ?_
    rw [map_mixMeasure (LQGMetric.GFFLaw.measurable_pairProc hXm)]
    have e : ∀ i, (P i).map (fun ω => LQGMetric.GFFLaw.pairProc
        (fun p => Y p - ofCont (fY p)) ⟨i, ω⟩) =
        (P i₀).map (LQGMetric.GFFLaw.pairProc fun ω => g i₀ ω - ofCont (f i₀ ω)) :=
      fun i => LQGMetric.GFFLaw.map_pairProc_eq (hfg i) (hfg i₀)
    simp only [e]
    exact sum_smul_eq_of_tsum_eq_one hw1 _
  have hYc : IsGFFPlusCont Y (mixMeasure w P) := ⟨hYm, fY, hfYm, hX⟩
  obtain ⟨F, hF, hFae⟩ := hD.2.2.1 (mixMeasure w P) Y hYc U
  exact ⟨F, hF, fun i => ae_of_ae_mixMeasure hw0 hFae i⟩

/-- **Pathwise locality** for a strong LQG metric: if two whole-plane GFFs plus continuous
functions on one probability space agree on the open set `U` a.s., then a.s. their internal
metrics on `U` agree (as functions on `U × U`, values `∞` included). -/
theorem ae_internal_eq_of_ae_restrictTo_eq_lsc {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {D : DistC → LSCMetric} (hD : IsStrongLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {g₁ g₂ : Ω → DistC} (h₁ : IsGFFPlusCont g₁ P) (h₂ : IsGFFPlusCont g₂ P)
    (U : TopologicalSpace.Opens ℂ)
    (hU : ∀ᵐ ω ∂P, restrictTo U (g₁ ω) = restrictTo U (g₂ ω)) :
    ∀ᵐ ω ∂P, (D (g₁ ω)).internal (U : Set ℂ) = (D (g₂ ω)).internal (U : Set ℂ) := by
  obtain ⟨F, -, hF⟩ := universalLocality_lsc hD U Bool (fun _ => Ω) (fun _ => P)
    (fun b => cond b g₁ g₂) (fun b => by cases b <;> assumption)
  filter_upwards [hF true, hF false, hU] with ω e1 e2 e3
  have e1' : (D (g₁ ω)).internal (U : Set ℂ) = F (restrictTo U (g₁ ω)) := e1
  have e2' : (D (g₂ ω)).internal (U : Set ℂ) = F (restrictTo U (g₂ ω)) := e2
  rw [e1', e2', e3]

end SupercriticalConformalCovariance.Domain
