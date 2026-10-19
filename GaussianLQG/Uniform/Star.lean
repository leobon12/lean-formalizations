import GaussianLQG.Uniform.Star.Inverse
import GaussianLQG.Core.InterfacesS6
import LQGMetric.Papers.DG.BallMass

/-!
# Route U, step U15: the uniform LFPP moment bounds (★)

The ledger statement U15 (`blueprint/phaseB/uniform-ledger.tex`, `star_bound`), delivered as the
interface `LFPPUniformMoments c` (`GaussianLQG/Core/InterfacesS6.lean`; (★) under `normGFFLaw`,
`ε = 2⁻ⁿ`) with the normalization `c γ n := λ_n(ξ_γ) = lambdaN (xiGamma γ) W P n` of the white
noise `W` from which the field is built (on `(ℕ → ℝ, stdP)`: `DG.exists_wn_wholePlaneGFF`, the
construction of U14, `FieldCmp.exists_heatMollify_phiMN_tail'`).

* `star_bound`: (★) on the probability space of the noise, for the normalized whole-plane GFF
  `h = h₀ − (h₀)_1(0)` built from a white noise `W` (`h₀(φ) = W(testL2 φ)` a.s.): the two halves
  `holder_half` (from U12) and `inv_half` (from U13, proved) at `ξ = ξ_γ ≤ γ`.
* `lfppUniformMoments_lambda`: the same bounds under `normGFFLaw` (`GM.normGFFLaw_eq` and
  `lintegral_map_le`; no measurability of the functionals is needed), i.e.
  `LFPPUniformMoments (fun γ n => lambdaN (xiGamma γ) W P n)`.
* `lambdaN_xiGamma_pos`: `c γ n > 0` for **all** `γ ∈ ℝ` and `n` (`DDDF.lambdaN_pos`; audit
  B-0b, M-3).
* `exists_lfppUniformMoments_lambda` (on `(ℕ → ℝ, stdP)` with the noise of U14) and
  `exists_lfppUniformMoments` (`∃ c > 0, LFPPUniformMoments c`, the form consumed by U16/U17).

The exponent: `γ_p = min(ξ_{U12}(2p), ξ_{U13}(2p))` (also `≤ 1`), where `ξ_{U12}`, `ξ_{U13}` are the
existential thresholds of U12 and U13 at order `2p` (audit B-0b, C-5); `ξ_γ = γ/d_γ ≤ γ` by
`d_γ ≥ 1` (`DG.one_le_dGamma`, with the proved `DG.chiLeTwo`). The bounds hold for every `n ≥ 0`.

The only hypothesis is U12 (`Uniform.IfaceHolderMomentU`, packet PB-U12). U13 is the proved
`Uniform.inv_moment_unif_holds` (packet PB-U13, ENNReal form of audit B-0b, S-1/M-4), U14 the
proved `FieldCmp.heatMollify_phiMN_tail_unif`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace GaussianLQG
namespace StarBound

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

/-- `ξ_γ ∈ (0, γ]` for `γ ∈ (0, 2)`: `d_γ ≥ 1` (`DG.one_le_dGamma`, `DG.chiLeTwo`). -/
theorem xiGamma_mem_Ioc {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : xiGamma γ ∈ Set.Ioc 0 γ :=
  ⟨DG.xiGamma_pos hγ, div_le_self hγ.le (DG.one_le_dGamma DG.chiLeTwo hγ hγ2)⟩

/-- **Moving to `normGFFLaw`**: for a normalized whole-plane GFF `h` on a probability space,
`∫ F d(normGFFLaw) ≤ E[F(h)]` for every `F : 𝒟'(ℂ) → [0, ∞]` (no measurability of `F`). -/
theorem lintegral_normGFFLaw_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsNormalizedWPGFF h P) (F : DistC → ℝ≥0∞) :
    ∫⁻ g, F g ∂normGFFLaw ≤ ∫⁻ ω, F (h ω) ∂P := by
  rw [GM.normGFFLaw_eq hh]
  exact lintegral_map_le F hh.1.measurable.aemeasurable

/-- `c γ n = λ_n(ξ_γ) > 0` for every `γ ∈ ℝ` and `n` (audit B-0b, M-3). -/
theorem lambdaN_xiGamma_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (γ : ℝ) (n : ℕ) :
    0 < lambdaN (xiGamma γ) W P n :=
  lambdaN_pos hW n

/-- **(★) on the probability space of the noise** (ledger U15, `star_bound`). For every white
noise `W` on a probability space and the normalized whole-plane GFF `h = h₀ − (h₀)_1(0)` built
from it: for `p ≥ 1` there is `γ_p > 0` such that for every compact `K` and `δ > 0` there is
`C < ∞` with `E[A_X(K)^p] ≤ C` and `E[I_X(K, δ)^{-p}] ≤ C` for `X = λ_n⁻¹ D^{2⁻ⁿ}_h`,
`λ_n = lambdaN ξ_γ W P n`, every `γ ∈ (0, γ_p]` and every `n`. The constants do not depend on the
noise. -/
theorem star_bound (hU12 : Uniform.IfaceHolderMomentU) (p : ℝ) (hp : 1 ≤ p) :
    ∃ γp : ℝ, 0 < γp ∧ γp ≤ 1 ∧ ∀ K : Set ℂ, IsCompact K → ∀ δ : ℝ, 0 < δ →
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {h₀ : Ω → DistC},
        IsWhiteNoise P W → IsWholePlaneGFF h₀ P →
        (∀ φ : TestC, (fun ω => h₀ ω φ) =ᵐ[P] W (GFFExist.testL2 φ)) →
        ∀ γ ∈ Set.Ioc (0 : ℝ) γp, ∀ n : ℕ,
          (∫⁻ ω, holderConst (fun z => (lambdaN (xiGamma γ) W P n)⁻¹ *
              lfppDist (xiGamma γ) ((2 : ℝ)⁻¹ ^ n)
                (addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)) z) K ^ p ∂P) ≤ C ∧
          (∫⁻ ω, (sepInf (fun z => (lambdaN (xiGamma γ) W P n)⁻¹ *
              lfppDist (xiGamma γ) ((2 : ℝ)⁻¹ ^ n)
                (addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)) z) K δ)⁻¹ ^ p ∂P) ≤ C := by
  obtain ⟨ξ₁, hξ₁, hξ₁1, hH⟩ := holder_half hU12 hp
  obtain ⟨ξ₂, hξ₂, -, hI⟩ := inv_half hp
  refine ⟨min ξ₁ ξ₂, lt_min hξ₁ hξ₂, (min_le_left _ _).trans hξ₁1, fun K hK δ hδ => ?_⟩
  obtain ⟨C₁, hC₁, hH'⟩ := hH K hK
  obtain ⟨C₂, hC₂, hI'⟩ := hI K hK δ hδ
  refine ⟨C₁ + C₂, ENNReal.add_ne_top.2 ⟨hC₁, hC₂⟩,
    fun {Ω} _ {P} {W} {h₀} hW hh hae γ hγ n => ?_⟩
  have hγ2 : γ < 2 :=
    (hγ.2.trans ((min_le_left _ _).trans hξ₁1)).trans_lt one_lt_two
  obtain ⟨hξ0, hξγ⟩ := xiGamma_mem_Ioc hγ.1 hγ2
  exact ⟨(hH' hW hh hae _ ⟨hξ0, hξγ.trans (hγ.2.trans (min_le_left _ _))⟩ n).trans le_self_add,
    (hI' hW hh hae _ ⟨hξ0, hξγ.trans (hγ.2.trans (min_le_right _ _))⟩ n).trans le_add_self⟩

/-- **(★) under `normGFFLaw`** (ledger U15 delivered as the interface of U16): for every white
noise `W` on a probability space from which a whole-plane GFF `h₀` is built
(`h₀(φ) = W(testL2 φ)` a.s.), `LFPPUniformMoments (fun γ n => λ_n(ξ_γ))` holds with
`λ_n(ξ) = lambdaN ξ W P n`. -/
theorem lfppUniformMoments_lambda (hU12 : Uniform.IfaceHolderMomentU)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {h₀ : Ω → DistC}
    (hW : IsWhiteNoise P W) (hh : IsWholePlaneGFF h₀ P)
    (hae : ∀ φ : TestC, (fun ω => h₀ ω φ) =ᵐ[P] W (GFFExist.testL2 φ)) :
    LFPPUniformMoments (fun γ n => lambdaN (xiGamma γ) W P n) := by
  have hP := hW.isProbabilityMeasure
  have hN := FieldCmp.isNormalizedWPGFF_norm hh
  intro p hp
  obtain ⟨γp, hγp, -, hS⟩ := star_bound hU12 p hp
  refine ⟨γp, hγp, fun K hK δ hδ => ?_⟩
  obtain ⟨C, hC, hS'⟩ := hS K hK δ hδ
  refine ⟨C, hC, fun γ hγ n _ => ?_⟩
  obtain ⟨h1, h2⟩ := hS' hW hh hae γ hγ n
  exact ⟨(lintegral_normGFFLaw_le hN _).trans h1, (lintegral_normGFFLaw_le hN _).trans h2⟩

/-- **(★) for the noise of U14 on `(ℕ → ℝ, stdP)`**: there is a white noise `W` on the coordinate
space with `λ_n(ξ_γ) > 0` for all `γ, n` and
`LFPPUniformMoments (fun γ n => lambdaN (xiGamma γ) W stdP n)`. -/
theorem exists_lfppUniformMoments_lambda (hU12 : Uniform.IfaceHolderMomentU) :
    ∃ W : WNSpace → Coord → ℝ, IsWhiteNoise stdP W ∧
      (∀ γ n, 0 < lambdaN (xiGamma γ) W stdP n) ∧
      LFPPUniformMoments (fun γ n => lambdaN (xiGamma γ) W stdP n) := by
  obtain ⟨W, h₀, hW, hh, hae⟩ := DG.exists_wn_wholePlaneGFF
  exact ⟨W, hW, lambdaN_xiGamma_pos hW, lfppUniformMoments_lambda hU12 hW hh hae⟩

/-- **(★) for some positive normalization** (the form consumed by U16/U17; audit B-0b, C-3). -/
theorem exists_lfppUniformMoments (hU12 : Uniform.IfaceHolderMomentU) :
    ∃ c : ℝ → ℕ → ℝ, (∀ γ n, 0 < c γ n) ∧ LFPPUniformMoments c := by
  obtain ⟨W, -, hpos, hstar⟩ := exists_lfppUniformMoments_lambda hU12
  exact ⟨_, hpos, hstar⟩

end StarBound
end GaussianLQG
