import GaussianLQG
import LQGMetric.Assembly.MainFinal
import LQGMetric.Papers.GM.S1.Subseq
import SmallGammaGeodesics.Geodesic.Basic

/-!
# Core setup (packet K0)

The coordinate realization of the normalized whole-plane GFF bundled with a canonical metric family
(GaussianLQG `Setup` together with the field-level objects), and the reductions used everywhere
downstream (planning audit GA5, Details (c); rulings G6, G8, G11):

* `exists_canonical_family`: every strong γ-LQG metric family is a.s. a positive multiple of a
  canonical one (GM Theorem 1.2), so it has the same geodesics;
* `uniformMomentInput_canonical`: the uniform moment input (S6) of GaussianLQG, hypothesis-free
  (replaces Kavvadias, Lemma 5.4);
* `GSetup.exists_of`;
* `dimension_input`: source (1.12).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace SmallGammaGeodesics

open LQGMetric GaussianLQG

/-- Constant-speed geodesics are unchanged when the metric is multiplied by a positive constant. -/
theorem isGeod01_iff_of_eq_smul {D D' : ContMetric} {C : ℝ} (hC : 0 < C)
    (hDD : ∀ u v : ℂ, D.1 (u, v) = C * D'.1 (u, v)) (z w : ℂ) (η : C(unitInterval, ℂ)) :
    Blueprint.IsGeod01 D z w η ↔ Blueprint.IsGeod01 D' z w η := by
  unfold Blueprint.IsGeod01
  refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun s =>
    forall_congr' fun t => ?_
  rw [hDD, hDD, mul_left_comm]
  exact ⟨fun h => mul_left_cancel₀ hC.ne' h, fun h => by rw [h]⟩

/-- Every strong γ-LQG metric is a.s. a deterministic positive multiple of a canonical one
(GM Theorem 1.2, `theorem12_proved`). -/
theorem exists_canonical_smul {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric}
    (hD : IsStrongLQGMetric γ D) :
    ∃ D' : DistC → ContMetric, IsCanonicalLQGMetric γ D' ∧ ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsGFFPlusCont h P →
        ∀ᵐ ω ∂P, ∀ u v : ℂ, (D (h ω)).1 (u, v) = C * (D' (h ω)).1 (u, v) := by
  obtain ⟨D', hD'⟩ := exists_isCanonicalLQGMetric hγ hγ2
  obtain ⟨C, hC, hDC⟩ := (theorem12_proved γ hγ hγ2).2 D D' hD hD'.1
  exact ⟨D', hD', C, hC, hDC⟩

/-- A strong γ-LQG metric family has a.s. the same constant-speed geodesics as a canonical family. -/
theorem exists_canonical_family (D : ℝ → DistC → ContMetric)
    (hD : ∀ γ, 0 < γ → γ < 2 → IsStrongLQGMetric γ (D γ)) :
    ∃ D' : ℝ → DistC → ContMetric, (∀ γ, 0 < γ → γ < 2 → IsCanonicalLQGMetric γ (D' γ)) ∧
      ∀ γ, 0 < γ → γ < 2 → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistC), IsGFFPlusCont h P →
        ∀ᵐ ω ∂P, ∀ (z w : ℂ) (η : C(unitInterval, ℂ)),
          Blueprint.IsGeod01 (D γ (h ω)) z w η ↔ Blueprint.IsGeod01 (D' γ (h ω)) z w η := by
  classical
  have hex : ∀ γ : ℝ, ∃ D' : DistC → ContMetric, (0 < γ → γ < 2 → IsCanonicalLQGMetric γ D' ∧
      ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsGFFPlusCont h P →
        ∀ᵐ ω ∂P, ∀ u v : ℂ, (D γ (h ω)).1 (u, v) = C * (D' (h ω)).1 (u, v)) := by
    intro γ
    by_cases hγ : 0 < γ ∧ γ < 2
    · obtain ⟨D', hD', hC⟩ := exists_canonical_smul hγ.1 hγ.2 (hD γ hγ.1 hγ.2)
      exact ⟨D', fun _ _ => ⟨hD', hC⟩⟩
    · exact ⟨D γ, fun h1 h2 => absurd ⟨h1, h2⟩ hγ⟩
  choose D' hD' using hex
  refine ⟨D', fun γ hγ hγ2 => (hD' γ hγ hγ2).1, ?_⟩
  intro γ hγ hγ2 Ω _ P _ h hh
  obtain ⟨C, hC, hDC⟩ := (hD' γ hγ hγ2).2
  filter_upwards [hDC P h hh] with ω hω z w η
  exact isGeod01_iff_of_eq_smul hC hω z w η

/-- (S6) for the canonical metric, hypothesis-free (replaces Kavvadias, Lemma 5.4; ruling G6). -/
theorem uniformMomentInput_canonical (D : ℝ → DistC → ContMetric)
    (hD : ∀ γ, 0 < γ → γ < 2 → IsCanonicalLQGMetric γ (D γ)) : UniformMomentInput D := by
  obtain ⟨c, hc, hstar⟩ := StarBound.exists_lfppUniformMoments Uniform.ifaceHolderMomentU_holds
  exact uniformMomentInput_of_lfppUniformMoments c hc hstar D hD

/-- The coordinate realization of the normalized GFF bundled with a canonical metric family: the
GaussianLQG coordinate calculus and the field-level axioms on one probability space. -/
structure GSetup where
  S : Setup
  Dfam : ℝ → DistC → ContMetric
  hD : ∀ γ, 0 < γ → γ < 2 → IsCanonicalLQGMetric γ (Dfam γ)
  h₀ : Coord → DistC
  measurable_h₀ : Measurable h₀
  normalized : IsNormalizedWPGFF h₀ stdP
  compat : ∀ γ ∈ Ioo (0 : ℝ) 2, S.ξ γ = xiGamma γ ∧ ∀ ω, S.D γ ω = Dfam γ (h₀ ω)
  /-- the frame pairing with the uniform measure on `[0,1]` is the field's `measPairing` (BP2: needed by
  the field-level residual variance of §5) -/
  pairSeg : pairing S.e (segMeasure 0 1) =ᵐ[stdP] fun ω => measPairing (h₀ ω) (segMeasure 0 1)

theorem GSetup.exists_of (Dfam : ℝ → DistC → ContMetric)
    (hD : ∀ γ, 0 < γ → γ < 2 → IsCanonicalLQGMetric γ (Dfam γ)) :
    ∃ G : GSetup, G.Dfam = Dfam := by
  obtain ⟨S, h₀, hm, hn, hc, hH, -⟩ := exists_setup Dfam hD (uniformMomentInput_canonical Dfam hD)
  have hps : pairing S.e (segMeasure 0 1) =ᵐ[stdP] fun ω => measPairing (h₀ ω) (segMeasure 0 1) := by
    have h00 := hH 0 ⟨le_rfl, zero_le_one⟩ 0 ⟨le_rfl, zero_le_one⟩
    rw [S.H_zero_zero] at h00
    filter_upwards [h00] with ω hω
    rw [hω]
    simp [segPairing]
  exact ⟨⟨S, Dfam, hD, h₀, hm, hn, hc, hps⟩, rfl⟩

/-- Source (1.12): `|ξQ − 1| ≤ Cξ` and `γ/3 ≤ ξ ≤ γ` for small `γ`. -/
theorem dimension_input :
    ∃ γ₀ C : ℝ, 0 < γ₀ ∧ ∀ γ ∈ Ioc (0 : ℝ) γ₀,
      |xiGamma γ * Q γ - 1| ≤ C * xiGamma γ ∧ γ / 3 ≤ xiGamma γ ∧ xiGamma γ ≤ γ := by
  obtain ⟨Dfam, hD⟩ : ∃ Dfam : ℝ → DistC → ContMetric,
      ∀ γ, 0 < γ → γ < 2 → IsCanonicalLQGMetric γ (Dfam γ) := by
    classical
    refine ⟨fun γ => if h : 0 < γ ∧ γ < 2 then (exists_isCanonicalLQGMetric h.1 h.2).choose
      else (exists_isCanonicalLQGMetric (γ := 1) one_pos one_lt_two).choose, ?_⟩
    intro γ hγ hγ2
    simp only [hγ, hγ2, and_self, dite_true]
    exact (exists_isCanonicalLQGMetric hγ hγ2).choose_spec
  obtain ⟨S, h₀, -, -, hS, -⟩ := exists_setup Dfam hD (uniformMomentInput_canonical Dfam hD)
  obtain ⟨⟨γe, C₁, hγe, hγe2, hb⟩, -, -⟩ := S.exponents
  refine ⟨γe, C₁, hγe, fun γ hγ => ?_⟩
  have hξ : S.ξ γ = xiGamma γ := (hS γ ⟨hγ.1, hγ.2.trans_lt hγe2⟩).1
  obtain ⟨h1, h2, -, h4⟩ := hb γ hγ
  rw [hξ] at h1 h2 h4
  exact ⟨h4, h1, h2⟩

end SmallGammaGeodesics
