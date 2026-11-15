import InteractingSLE.Spec.Sec5.Aux61RestartFinComparison
import InteractingSLE.Spec.Sec7.ReverseArcLift

/-!
# The actual additional hydrodynamic logarithm

Packet PROVE-AUX61-R1. For the nested own and retained hulls in the original
target coordinate, the additional hull and its canonical logarithm are actual
constructed objects. Canonical uniqueness proves the exact chain rule, and
Aux. 57 fixes the additional phase to zero on every untouched real collar.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open QuantumZipper (H)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Sec5.Aux61Restart

open Restart

/-- The filled additional hull after mapping out the original own prefix. -/
def restartAdditionalHull (A B : Set ℂ) : Set ℂ := ConformalImage.mapOut A '' (B \ A)

/-- Its derivative logarithm with the inherited hydrodynamic normalization. -/
def restartAdditionalLog (A B : Set ℂ) : ℂ → ℂ := canonDerivLog (restartAdditionalHull A B)

theorem isHPHull_restartAdditionalHull {A B : Set ℂ} (hA : IsHPHull A)
    (hB : IsHPHull B) (hAB : A ⊆ B) : IsHPHull (restartAdditionalHull A B) :=
  (ConformalImage.isMapOut_mapOut hA).isHPHull_image hA hB hAB

theorem isCanonicalDerivLog_restartAdditionalLog {A B : Set ℂ} (hA : IsHPHull A)
    (hB : IsHPHull B) (hAB : A ⊆ B) :
    IsCanonicalDerivLog (restartAdditionalHull A B)
      (ConformalImage.mapOut (restartAdditionalHull A B)) (restartAdditionalLog A B) :=
  isCanonicalDerivLog_canonDerivLog (isHPHull_restartAdditionalHull hA hB hAB)

/-- The total map is literally the additional map after the own map on the
retained component; this uses uniqueness of hydrodynamic mapping-out functions. -/
theorem restart_mapOut_chain {A B : Set ℂ} (hA : IsHPHull A) (hB : IsHPHull B)
    (hAB : A ⊆ B) : EqOn (ConformalImage.mapOut B)
      (ConformalImage.mapOut (restartAdditionalHull A B) ∘ ConformalImage.mapOut A) (H \ B) := by
  exact (ConformalImage.isMapOut_mapOut hB).eqOn hB
    ((ConformalImage.isMapOut_mapOut hA).comp hA hB hAB
      (ConformalImage.isMapOut_mapOut (isHPHull_restartAdditionalHull hA hB hAB)))

/-- The canonical total logarithm equals the actual additional logarithm plus
the canonical own logarithm, exactly rather than modulo an integer. -/
theorem restart_canonicalLog_chain {A B : Set ℂ} (hA : IsHPHull A) (hB : IsHPHull B)
    (hAB : A ⊆ B) : EqOn (canonDerivLog B)
      (fun z => restartAdditionalLog A B (ConformalImage.mapOut A z) + canonDerivLog A z)
      (H \ B) := by
  have hgA := ConformalImage.isMapOut_mapOut hA
  have hgE := ConformalImage.isMapOut_mapOut (isHPHull_restartAdditionalHull hA hB hAB)
  have hcomp := IsCanonicalDerivLog.comp hA hB hAB hgA hgE
    (isCanonicalDerivLog_canonDerivLog hA) (isCanonicalDerivLog_restartAdditionalLog hA hB hAB)
  exact IsCanonicalDerivLog.eqOn
    ((isCanonicalDerivLog_canonDerivLog hB).congr hB (restart_mapOut_chain hA hB hAB))
    hcomp hB (hgA.comp hA hB hAB hgE)

/-- Aux. 57 supplies zero additional phase at an untouched current collar.
The logarithm is the constructed canonical logarithm of the filled additional
hull; no unspecified branch is supplied as an assumption. -/
theorem tendsto_restartAdditionalLog_im_zero {A B : Set ℂ} (hA : IsHPHull A)
    (hB : IsHPHull B) (hAB : A ⊆ B) {u ρ : ℝ} (hρ : 0 < ρ)
    (hfree : Disjoint (ball (u : ℂ) ρ) (restartAdditionalHull A B)) :
    Tendsto (fun z => (restartAdditionalLog A B z).im) (𝓝[H] (u : ℂ)) (𝓝 0) :=
  (isCanonicalDerivLog_restartAdditionalLog hA hB hAB).tendsto_im_nhdsWithin_zero
    (isHPHull_restartAdditionalHull hA hB hAB)
    (ConformalImage.isMapOut_mapOut (isHPHull_restartAdditionalHull hA hB hAB)) hρ hfree

/-- The current inverse-chart collar proves the canonical additional phase
zero, including existence of the required free real ball. -/
theorem exists_restartAdditionalLog_phase_zero {A B : Set ℂ} (hA : IsHPHull A)
    (hB : IsHPHull B) (hAB : A ⊆ B) {F : ℂ → ℂ}
    (hF : IsConformalBijection F H (H \ A)) {z₀ : ℂ}
    (hF₀ : Tendsto F (𝓝[H] 0) (𝓝 z₀))
    (hcurrent : ∃ δ > 0, MapsTo F (ball 0 δ ∩ H) (H \ B)) :
    ∃ u ρ : ℝ, 0 < ρ ∧ Disjoint (ball (u : ℂ) ρ) (restartAdditionalHull A B) ∧
      Tendsto (ConformalImage.mapOut A ∘ F) (𝓝[H] 0) (𝓝[H] (u : ℂ)) ∧
      Tendsto (fun w => (restartAdditionalLog A B (ConformalImage.mapOut A (F w))).im)
        (𝓝[H] 0) (𝓝 0) := by
  obtain ⟨u, ρ, hρ, hf, hlim⟩ := exists_current_transition_collar hA hB
    (ConformalImage.isMapOut_mapOut hA) hF hF₀ hcurrent
  exact ⟨u, ρ, hρ, hf, hlim,
    (tendsto_restartAdditionalLog_im_zero hA hB hAB hρ hf).comp hlim⟩

/-- On physical points of the retained domain, the additional log evaluation
is the difference of the two canonical log evaluations. Hence its measurable
anchor follows from the two history charts; it is not a new measurability input. -/
theorem measurable_restartAdditionalLog_comp
    {Ω : Type*} [MeasurableSpace Ω] {A B : Ω → Set ℂ}
    (hA : ∀ ω, IsHPHull (A ω)) (hB : ∀ ω, IsHPHull (B ω))
    (hAB : ∀ ω, A ω ⊆ B ω) {z : Ω → ℂ} (hz : ∀ ω, z ω ∈ H \ B ω)
    (hLA : Measurable fun ω => canonDerivLog (A ω) (z ω))
    (hLB : Measurable fun ω => canonDerivLog (B ω) (z ω)) :
    Measurable fun ω => restartAdditionalLog (A ω) (B ω) (ConformalImage.mapOut (A ω) (z ω)) := by
  have heq : (fun ω => restartAdditionalLog (A ω) (B ω)
      (ConformalImage.mapOut (A ω) (z ω))) =
      fun ω => canonDerivLog (B ω) (z ω) - canonDerivLog (A ω) (z ω) := by
    funext ω
    rw [restart_canonicalLog_chain (hA ω) (hB ω) (hAB ω) (hz ω), add_sub_cancel_right]
  rw [heq]
  exact hLB.sub hLA

/-- For actual compact filled-hull records, the additional inherited anchor is
measurable from the existing dyadic-hit record API. Both canonical chart logs
are constructed from those records, rather than assumed measurable separately. -/
theorem measurable_additionalLog_of_compact_records
    {Ω : Type*} [MeasurableSpace Ω] {K₀ K : Ω → Set ℂ}
    (hm₀ : IsDyadicHitMeasurable K₀) (hm : IsDyadicHitMeasurable K)
    (hc₀ : ∀ ω, IsCompact (K₀ ω)) (hc : ∀ ω, IsCompact (K ω))
    (hp₀ : ∀ ω, IsPreconnected (K₀ ω ∪ lowerHalf))
    (hp : ∀ ω, IsPreconnected (K ω ∪ lowerHalf))
    (hsub : ∀ ω, fillH (K₀ ω) ⊆ fillH (K ω))
    {e : ℕ → ℂ} {N : Ω → ℕ} (hN : Measurable N)
    (hz : ∀ ω, e (N ω) ∈ H \ fillH (K ω)) :
    Measurable fun ω => restartAdditionalLog (fillH (K₀ ω)) (fillH (K ω))
      (ConformalImage.mapOut (fillH (K₀ ω)) (e (N ω))) := by
  have hA := fun ω => isHPHull_fillH_of_compact (hc₀ ω) (hp₀ ω)
  have hB := fun ω => isHPHull_fillH_of_compact (hc ω) (hp ω)
  have hz₀ : ∀ ω, e (N ω) ∈ H \ fillH (K₀ ω) :=
    fun ω => ⟨(hz ω).1, fun ha => (hz ω).2 (hsub ω ha)⟩
  have hLA := Sec7.Lemma71E.measurable_at_seq hN hz₀
    (measurable_indicator_canonDerivLog hm₀ hc₀ hp₀)
  have hLB := Sec7.Lemma71E.measurable_at_seq hN hz
    (measurable_indicator_canonDerivLog hm hc hp)
  exact measurable_restartAdditionalLog_comp hA hB hsub hz hLA hLB

end InteractingSLE.Sec5.Aux61Restart
