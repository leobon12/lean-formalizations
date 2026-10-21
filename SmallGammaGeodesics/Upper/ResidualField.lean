import SmallGammaGeodesics.Upper.Transfer
import SmallGammaGeodesics.Variance.Residual

/-!
# The residual variance on every realization of the field (packet P-U1)

Blueprint `s5-upper.tex`, Lemma `lem:residual-field` (BP2 detail D6, Remark `rem:pairseg`).

`residualVariance_field`: there are `γ₀ > 0` and `C` such that for `γ ∈ (0, γ₀]` and every
measurable a.s. geodesic `η` of the coordinate setup `G`, `M(η)` is integrable and, for **every**
whole-plane GFF `h` on any probability space,
`∫⁻ Z_{b_γ}(h)² ≤ C ξ² (E M(η) + ξ^{99/100} log(1/ξ))`.

Proof. Lemma 3.2′ (`residualVariance`, packet P-A5) for `G.S` gives the bound for
`Z = ξ · S.firstOrderErr γ 0 1 = log S.D^γ(0,1) − b_γ − ξ · pairing S.e λ` (since `log|0 − 1| = 0`).
The field `pairSeg` of `GSetup` identifies `pairing S.e λ` with `(h₀, λ)` a.s., and the field
`compat` identifies `S.D^γ` with `D^γ_{h₀}` and `S.ξ` with `xiGamma`; so `Z = Z_{b_γ}(h₀)` a.s.
For a general whole-plane GFF `h`: `Z_b(h) = Z_b(nrm h)` a.s. (`ae_Zf_nrmF`), `g ↦ Z_b(g)²` is
Borel, and `nrm h` has the law of `h₀` (both are normalized).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace SmallGammaGeodesics

open GaussianLQG LQGMetric LQGMetric.Blueprint

/-- `g ↦ Z_b(g)` is Borel for a canonical metric. -/
theorem measurable_Zf {γ b : ℝ} {D : DistC → ContMetric} (hD : IsCanonicalLQGMetric γ D) :
    Measurable fun g : DistC => Zf γ b D g :=
  (((hD.measurable_dist_comp 0 1).log.sub_const b).sub
    ((measurable_measPairing (segMeasure 0 1)).const_mul _))

/-- On the coordinate setup, the residual `ξ F` of Lemma 3.2′ is `Z_{b_γ}(h₀)` almost surely. -/
theorem ae_firstOrderErr_eq_Zf (G : GSetup) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    (fun ω => G.S.ξ γ * G.S.firstOrderErr γ 0 1 ω) =ᵐ[stdP]
      fun ω => Zf γ (G.S.b γ) (G.Dfam γ) (G.h₀ ω) := by
  obtain ⟨hξ, hDeq⟩ := G.compat γ hγ
  have hξ0 : G.S.ξ γ ≠ 0 := (G.S.ξ_pos γ hγ.1 hγ.2).ne'
  filter_upwards [G.pairSeg] with ω hω
  have hlog : Real.log ‖(0 : ℂ) - 1‖ = 0 := by simp
  simp only [Setup.firstOrderErr, Zf, hlog, mul_zero, sub_zero, hω, hDeq ω]
  rw [mul_sub, mul_div_cancel₀ _ hξ0, hξ]

/-- **The residual variance on every realization** (`lem:residual-field`). -/
theorem residualVariance_field (G : GSetup) : ∃ γ₀ C : ℝ, 0 < γ₀ ∧ ∀ γ ∈ Ioc 0 γ₀,
    ∀ η : Coord → C(unitInterval, ℂ), Measurable η →
      (∀ᵐ ω ∂stdP, IsGeod01 (G.Dfam γ (G.h₀ ω)) 0 1 (η ω)) →
      Integrable (fun ω => maxDev (η ω)) stdP ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
        IsWholePlaneGFF h P →
        ∫⁻ ω, ENNReal.ofReal (Zf γ (G.S.b γ) (G.Dfam γ) (h ω) ^ 2) ∂P ≤
          ENNReal.ofReal (C * xiGamma γ ^ 2 *
            ((∫ ω, maxDev (η ω) ∂stdP) + xiGamma γ ^ (99 / 100 : ℝ) * Lg γ)) := by
  obtain ⟨γ₁, C, hγ₁, hres⟩ := residualVariance G.S
  refine ⟨min γ₁ 1, C, lt_min hγ₁ one_pos, fun γ hγ η hηm hη => ?_⟩
  have hγ0 : 0 < γ := hγ.1
  have hγ1 : γ ≤ γ₁ := hγ.2.trans (min_le_left _ _)
  have hγ2 : γ < 2 := by linarith [hγ.2.trans (min_le_right _ _)]
  have hγI : γ ∈ Ioo (0 : ℝ) 2 := ⟨hγ0, hγ2⟩
  obtain ⟨hξ, hDeq⟩ := G.compat γ hγI
  have hη' : ∀ᵐ ω ∂stdP, IsGeod01 (G.S.D γ ω) 0 1 (η ω) := by
    filter_upwards [hη] with ω hω
    rw [hDeq ω]
    exact hω
  obtain ⟨hMint, hmem, hbound⟩ := hres γ ⟨hγ0, hγ1⟩ η hηm hη'
  refine ⟨hMint, fun {Ω} _ P _ h hh => ?_⟩
  set F : DistC → ℝ≥0∞ := fun g => ENNReal.ofReal (Zf γ (G.S.b γ) (G.Dfam γ) g ^ 2) with hF_def
  have hF : Measurable F :=
    ((measurable_Zf (G.hD γ hγ0 hγ2)).pow_const 2).ennreal_ofReal
  -- the coordinate bound
  have hcoord : ∫⁻ ω, F (G.h₀ ω) ∂stdP ≤
      ENNReal.ofReal (C * xiGamma γ ^ 2 *
        ((∫ ω, maxDev (η ω) ∂stdP) + xiGamma γ ^ (99 / 100 : ℝ) * Lg γ)) := by
    have hZ := ae_firstOrderErr_eq_Zf G hγI
    have e1 : ∫⁻ ω, F (G.h₀ ω) ∂stdP =
        ∫⁻ ω, ENNReal.ofReal ((G.S.ξ γ * G.S.firstOrderErr γ 0 1 ω) ^ 2) ∂stdP := by
      refine lintegral_congr_ae ?_
      filter_upwards [hZ] with ω hω
      simp only [hF_def, hω]
    rw [e1, ← ofReal_integral_eq_lintegral_ofReal hmem.integrable_sq
      (ae_of_all _ fun ω => sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal (hbound.trans (le_of_eq ?_))
    rw [hξ, Lg, one_div]
  -- transfer to `h` through `nrm h`
  have h1 : ∫⁻ ω, F (h ω) ∂P = ∫⁻ ω, F (nrmF (h ω)) ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_Zf_nrmF (b := G.S.b γ) (G.hD γ hγ0 hγ2).1 hh] with ω hω
    simp only [hF_def, hω]
  have h2 : ∫⁻ ω, F (nrmF (h ω)) ∂P = ∫⁻ ω, F (G.h₀ ω) ∂stdP := by
    have hm : Measurable fun ω => nrmF (h ω) := measurable_nrmF.comp hh.measurable
    rw [← lintegral_map hF hm, ← lintegral_map hF G.measurable_h₀,
      map_eq_map_of_isNormalizedWPGFF (isNormalizedWPGFF_nrmF hh) G.normalized]
  calc ∫⁻ ω, F (h ω) ∂P = ∫⁻ ω, F (G.h₀ ω) ∂stdP := h1.trans h2
    _ ≤ _ := hcoord

end SmallGammaGeodesics
