import SupercriticalConformalCovariance.Good.Specialized
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Prob

/-!
# Theorem 1.1, step 1: `e ≤ d` for the whole-plane-restricted field

Paper §§2–6 (l. 38–40, forward convention; Proposition 6.1, l. 453–515). For an instance of
`SupercriticalConformalCovariance.BiLip.IsInstance` (source `h` a normalized whole-plane GFF on `U`, target realization `(g₀, k)`
of `h^φ` on `V`), almost surely `e(u, v) = D_{h^φ}(φ u, φ v; V) ≤ D_h(u, v; U) = d(u, v)` for all
`u, v ∈ U` (`forward_wholePlane`).

Proved here from the proved providers
* `SupercriticalConformalCovariance.Improve.almost_everywhere_internal_bound` (Proposition 6.1, C* closure),
* `SupercriticalConformalCovariance.Good.ae_goodCover_of_locality_and_prop43_transport` (Lemma 5.1 probability, display
  (10) and Borel–Cantelli, with the covering lemma for display (10)'s covers and the good events (G1)–(G4)'s source events),
* `SupercriticalConformalCovariance.BiLip.lemma21_of_inputs` (Lemma 2.1),
* the sealed barrier (`ae_barrier`), the length axiom, and the domain-metric layer's domain triangle inequality,

and four **in-progress** inputs, each a named `Prop` stated in the exact consumption form:
* `SupercriticalConformalCovariance.BiLip.TargetTightUniform` and `SupercriticalConformalCovariance.BiLip.GoodEventsLocal` (the two inputs this module takes as hypotheses: Lemma 2.1
  steps 2 and 4; step 2 consumes Lemma 3.3);
* `Prop43Input` (Proposition 4.3, l. 333–370);
* `Lemma51LocalInput` (Lemma 5.1's locality, l. 416–438), with `k = 1/(4C²)` for every
  constant `C` of Lemma 2.1 (paper l. 375–380: "Fix the constant `C` from Lemma 2.1").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace
open scoped ENNReal

namespace SupercriticalConformalCovariance.Root

open LQGMetric (DistC)
open LQGMetric.Blueprint (AEEventIn)
open SupercriticalLQGUniqueness (LSCMetric IsStrongLQGMetric IsLFPPExponent)
open SupercriticalConformalCovariance (IsConformalBijection domainMetric)
open SupercriticalConformalCovariance.Good (transportedE transportedE_on shieldK shieldK_pos GoodEvent RegularBadEvent)

/-- **Proposition 4.3** (paper l. 333–370), in the consumption form of the Lemma 5.1 proof
(`SupercriticalConformalCovariance.Good.RegularBadEvent` with the transported domain metric `e`): for every instance, every
compact `L ⊆ U`, every dyadic geometry `(q, α)`, every `θ > 0` and `η > 0`, the probability that some
dyadically regular pair at `(z, r)` has `e(u, v) ≥ (1 + η) D_h(u, v)` tends to `0` as `r ↓ 0`,
uniformly in `z ∈ L`. -/
def Prop43Input (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) : Prop :=
  ∀ (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1) (θ : Ioi (0 : ℝ)) (η : ℝ), 0 < η →
  ∀ {U V : Opens ℂ} (φ : ℂ → ℂ) (hφ : IsConformalBijection φ U V)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h g₀ : Ω → DistC) (f : Ω → C(V, ℝ)) (hI : SupercriticalConformalCovariance.BiLip.IsInstance Q U V hφ P h g₀ f),
  ∀ L : Set ℂ, IsCompact L → L ⊆ U → ∀ ε : ℝ, 0 < ε → ∃ r₀ : ℝ, 0 < r₀ ∧
    ∀ z ∈ L, ∀ r : Ioi (0 : ℝ), (r : ℝ) ≤ r₀ →
      P (RegularBadEvent h (D ∘ h) (fun ω => transportedE (ξ : ℝ) D hφ (g₀ ω) (f ω))
        ξ Q q a θ η z r) ≤ ENNReal.ofReal ε

/-- **Lemma 5.1, locality** (paper l. 416–417, 425–438; with SOURCE_GAP `lem-5.1#locality`'s closed-annulus
σ-algebra `SupercriticalConformalCovariance.Cover.localSigma`): for every instance and every constant `C ≥ 1` for which Lemma 2.1's
two-sided comparison holds almost surely, with `k = shieldK C = 1/(4C²)`, the good event `F_{z,r}`
(G1–G5) is almost surely an event of the field near the annulus modulo its circle average, for all
small `r`, around every compact `L ⊆ U`. -/
def Lemma51LocalInput (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) : Prop :=
  ∀ (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ)) (θ : Ioi (0 : ℝ))
    (η : ℝ), 0 < η →
  ∀ {U V : Opens ℂ} (φ : ℂ → ℂ) (hφ : IsConformalBijection φ U V)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h g₀ : Ω → DistC) (f : Ω → C(V, ℝ)) (hI : SupercriticalConformalCovariance.BiLip.IsInstance Q U V hφ P h g₀ f),
  ∀ C : ℝ, 1 ≤ C →
    (∀ᵐ ω ∂P, ∀ u v : U,
      ENNReal.ofReal C⁻¹ * (D (h ω)).internal U (u, v) ≤
          domainMetric (ξ : ℝ) D V (g₀ ω) (f ω)
            (⟨φ u, hφ.2.mapsTo u.2⟩, ⟨φ v, hφ.2.mapsTo v.2⟩) ∧
        domainMetric (ξ : ℝ) D V (g₀ ω) (f ω)
            (⟨φ u, hφ.2.mapsTo u.2⟩, ⟨φ v, hφ.2.mapsTo v.2⟩) ≤
          ENNReal.ofReal C * (D (h ω)).internal U (u, v)) →
  ∀ L : Set ℂ, IsCompact L → L ⊆ U → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ z ∈ L, ∀ r ∈ Ioc (0 : ℝ) r₀,
    AEEventIn P (SupercriticalConformalCovariance.Cover.localSigma h z r)
      (GoodEvent h (D ∘ h) (fun ω => transportedE (ξ : ℝ) D hφ (g₀ ω) (f ω))
        ξ Q q a K θ (shieldK C) η z r)

/-- The transported metric satisfies the triangle inequality on `U` (on the sample event of `g₀`). -/
theorem transportedE_triangle (ξ : ℝ) (D : DistC → LSCMetric) {U V : Opens ℂ} {φ : ℂ → ℂ}
    (hφ : IsConformalBijection φ U V) (g₀ : DistC) (k : C(V, ℝ))
    (hf : Continuous (SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.forget (D g₀)))
    {x y z : ℂ} (hx : x ∈ (U : Set ℂ)) (hy : y ∈ (U : Set ℂ)) (hz : z ∈ (U : Set ℂ)) :
    transportedE ξ D hφ g₀ k (x, z) ≤
      transportedE ξ D hφ g₀ k (x, y) + transportedE ξ D hφ g₀ k (y, z) := by
  have e1 := transportedE_on ξ D hφ g₀ k ⟨x, hx⟩ ⟨z, hz⟩
  have e2 := transportedE_on ξ D hφ g₀ k ⟨x, hx⟩ ⟨y, hy⟩
  have e3 := transportedE_on ξ D hφ g₀ k ⟨y, hy⟩ ⟨z, hz⟩
  simp only at e1 e2 e3
  rw [e1, e2, e3]
  exact SupercriticalConformalCovariance.Domain.weylScaleOn_triangle hf k _ _ _

/-- **Step 1: `e ≤ d` for the whole-plane-restricted field** (Proposition 6.1 with its inputs). -/
theorem forward_wholePlane (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D)
    (hT : SupercriticalConformalCovariance.BiLip.TargetTightUniform ξ Q D) (hloc : SupercriticalConformalCovariance.BiLip.GoodEventsLocal ξ Q D)
    (hP43 : Prop43Input ξ Q D) (hL51 : Lemma51LocalInput ξ Q D) :
    ∀ (U V : Opens ℂ) (φ : ℂ → ℂ) (hφ : IsConformalBijection φ U V)
      {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h g₀ : Ω → DistC) (k : Ω → C(V, ℝ)) (hI : SupercriticalConformalCovariance.BiLip.IsInstance Q U V hφ P h g₀ k),
      ∀ᵐ ω ∂P, ∀ u v : U,
        domainMetric (ξ : ℝ) D V (g₀ ω) (k ω)
            (⟨φ u, hφ.2.mapsTo u.2⟩, ⟨φ v, hφ.2.mapsTo v.2⟩) ≤
          (D (h ω)).internal U (u, v) := by
  have hQpos : 0 < Q := SupercriticalLQGUniqueness.B2.QPos.dg20ExponentPositive_proved ξ Q hQ
  have hW := SupercriticalLQGUniqueness.B2.Strong.isWeakLQGMetric_of_isStrongLQGMetric hD
  obtain ⟨C, hC1, H21⟩ := SupercriticalConformalCovariance.BiLip.lemma21_of_inputs ξ Q hQ D hD hT hloc
  obtain ⟨p, θ, n, q, a, K, hp0, hp1, hqd, HG⟩ :=
    SupercriticalConformalCovariance.Good.ae_goodCover_of_locality_and_prop43_transport ξ Q hQpos D hD (shieldK C)
      (shieldK_pos hC1)
  intro U V φ hφ Ω _ P _ h g₀ k hI
  obtain ⟨E, hEc, hEU, hEcof⟩ := SupercriticalConformalCovariance.Good.exists_compact_exhaustion U U.isOpen
  set e : Ω → ℂ × ℂ → ℝ≥0∞ := fun ω => transportedE (ξ : ℝ) D hφ (g₀ ω) (k ω) with he
  have h21 := H21 U V φ hφ P h g₀ k hI
  have hInitial : ∃ c, SupercriticalConformalCovariance.Improve.Admissible P U (fun ω => D (h ω)) e c := by
    refine ⟨C, hC1, ?_⟩
    filter_upwards [h21] with ω hω u v
    have := (hω u v).2
    rw [he]
    simp only
    rw [transportedE_on]
    exact this
  have hhc : LQGMetric.IsGFFPlusCont h P := LQGMetric.GM.Tight.isGFFPlusCont_of_wp hI.1.1
  have hSample : ∀ᵐ ω ∂P,
      SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Barrier (D (h ω)) ∧
      (D (h ω)).IsLengthSpace ∧
      (∀ x ∈ (U : Set ℂ), ∀ y ∈ (U : Set ℂ), ∀ z ∈ (U : Set ℂ),
        e ω (x, z) ≤ e ω (x, y) + e ω (y, z)) := by
    filter_upwards [SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.ae_barrier hW hQpos
        P h hI.1, hD.2.1 P h hhc,
      SupercriticalConformalCovariance.Domain.ae_sample_of_isGFFPlusCont hD P g₀ hI.2.2.1] with ω hB hL hs
    exact ⟨hB, hL, fun x hx y hy z hz =>
      transportedE_triangle (ξ : ℝ) D hφ (g₀ ω) (k ω) hs.1 hx hy hz⟩
  have hCover : ∀ η : ℝ, 0 < η →
      η < SupercriticalConformalCovariance.Improve.optimalConstant P U (fun ω => D (h ω)) e - 1 →
      ∀ᵐ ω ∂P, SupercriticalConformalCovariance.Improve.GoodCover (D (h ω)) (e ω) ξ Q q a K θ (shieldK C) η E
        SupercriticalConformalCovariance.Good.coverScale := fun η hη _ =>
    HG φ hφ P h g₀ k hI E hEc hEU η hη
      (hL51 q a K θ η hη φ hφ P h g₀ k hI C hC1 h21)
      (fun L hL hLU => hP43 q a θ η hη φ hφ P h g₀ k hI L hL hLU ((1 - p) / 2)
        (by linarith))
  have hfin := SupercriticalConformalCovariance.Improve.almost_everywhere_internal_bound P U (fun ω => D (h ω)) e U.isOpen
    ξ Q q a K θ (shieldK C) n hqd E SupercriticalConformalCovariance.Good.coverScale hEcof hInitial hSample hCover
  filter_upwards [hfin] with ω hω u v
  have := hω u v
  rw [he] at this
  simp only at this
  rwa [transportedE_on] at this

end SupercriticalConformalCovariance.Root
