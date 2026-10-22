import HigherDimLQGMetric.Thm13.Decomp
import HigherDimLQGMetric.Metric.WeylAxioms
import HigherDimLQGMetric.Limits.TranslatePrelimit

/-! Translation covariance of the patched metric. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The exact statement of L6c's prelimit translation result. -/
def L8TranslatePrelimitInput : Prop :=
  ∀ {d : ℕ} (_hd : 2 ≤ d) (κ : Rd d → ℝ)
    (_hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (_hεs : ∀ n, 0 < εs n)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (_hh : IsNormalizedLGF h P) (z : Rd d),
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ u v : Rd d,
      lfppSeq κ ξ εs (h ω) n (z + u, z + v) =
        Real.exp (ξ * sphereAvg (h ω) 1 z) *
          lfppSeq κ ξ εs
            (addConst (affineComp 1 z (h ω))
              (-sphereAvg (affineComp 1 z (h ω)) 1 0)) n (u, v)

theorem l8_translate_prelimit_input : L8TranslatePrelimitInput := by
  intro d hd κ hκ ξ εs hεs Ω _ P _ h hh z
  exact l6c_ae_lfppSeq_translate hd κ hκ ξ εs hεs P h hh z

theorem l8_translation_normalized
    (hTr : L8TranslatePrelimitInput)
    {d : ℕ} (hd : 2 ≤ d) (κ : Rd d → ℝ)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hN : L8NormalizedGood hd hκ ξ εs hεs)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hh : IsNormalizedLGF h P) (z : Rd d) :
    ∀ᵐ ω ∂P, ∀ u v : Rd d,
      (l8_patch hd hκ ξ εs hεs (affineComp 1 z (h ω))).1 (u, v) =
        (l8_patch hd hκ ξ εs hεs (h ω)).1 (u + z, v + z) := by
  let k : Ω → DistRd d := fun ω => affineComp 1 z (h ω)
  let g : Ω → DistRd d := fun ω =>
    addConst (k ω) (-sphereAvg (k ω) 1 0)
  have hk : IsWholeSpaceLGF k P := hh.1.affineComp one_pos z
  have hg : IsNormalizedLGF g P :=
    hk.isNormalizedLGF_normalize (by omega)
      (hk.ae_exists_tendsto_sphereAvgSeq hd one_pos 0)
  obtain ⟨_, hconvH, _⟩ := hN P h hh
  obtain ⟨_, hconvG, hWg⟩ := hN P g hg
  filter_upwards [hTr hd κ hκ ξ εs hεs P h hh z,
    hh.1.ae_sphereAvg_affineComp hd one_pos z one_pos 0,
    hconvH, hconvG, hWg] with ω hpre hsph hH hG hW u v
  let c : ℝ := sphereAvg (k ω) 1 0
  have hc : c = sphereAvg (h ω) 1 z := by
    simpa only [c, k, one_mul, one_smul, zero_add] using hsph
  have hk_eq : addConst (g ω) c = k ω := by
    dsimp [g, c]
    rw [addConst_addConst, neg_add_cancel, addConst_zero]
  obtain ⟨hDg, hWg⟩ := hW
  have hconst :
      (l8_patch hd hκ ξ εs hεs (k ω)).1 (u, v) =
        Real.exp (ξ * c) *
          (l8_patch hd hκ ξ εs hεs (g ω)).1 (u, v) := by
    rw [← hk_eq, ← addFun_const, hWg]
    exact apply_eq_exp_mul_of_weyl_const hDg
      (fun x y => weylMetric_spec hDg x y) u v
  have htH : Tendsto
      (fun n => lfppSeq κ ξ εs (h ω) n (z + u, z + v))
      atTop (𝓝 ((l8_patch hd hκ ξ εs hεs (h ω)).1
        (z + u, z + v))) :=
    (continuous_eval_const _).continuousAt.tendsto.comp hH
  have htG : Tendsto
      (fun n => Real.exp (ξ * c) *
        lfppSeq κ ξ εs (g ω) n (u, v))
      atTop (𝓝 (Real.exp (ξ * c) *
        (l8_patch hd hκ ξ εs hεs (g ω)).1 (u, v))) :=
    (continuous_const.mul (continuous_eval_const _)).continuousAt.tendsto.comp hG
  have heq :
      (l8_patch hd hκ ξ εs hεs (h ω)).1 (z + u, z + v) =
        Real.exp (ξ * c) *
          (l8_patch hd hκ ξ εs hεs (g ω)).1 (u, v) := by
    apply tendsto_nhds_unique htH
    exact htG.congr' (Eventually.of_forall fun n => by
      rw [hc]
      exact (hpre n u v).symm)
  rw [hconst, ← heq]
  congr 1
  all_goals abel_nf

theorem l8_normalizedWeyl_of_good
    {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hN : L8NormalizedGood hd hκ ξ εs hεs) :
    L8NormalizedWeyl ξ (l8_patch hd hκ ξ εs hεs) := by
  intro Ω _ P _ h hh
  exact (hN P h hh).2.2

theorem l8_translation_of_normalized_good
    (hTr : L8TranslatePrelimitInput)
    {d : ℕ} (hd : 2 ≤ d) (κ : Rd d → ℝ)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hN : L8NormalizedGood hd hκ ξ εs hεs)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hh : IsLGFPlusCont h P) (z : Rd d) :
    ∀ᵐ ω ∂P, ∀ u v : Rd d,
      (l8_patch hd hκ ξ εs hεs (affineComp 1 z (h ω))).1 (u, v) =
        (l8_patch hd hκ ξ εs hεs (h ω)).1 (u + z, v + z) := by
  let D : DistRd d → ContMetric d := l8_patch hd hκ ξ εs hεs
  obtain ⟨h₀, g, hh₀, _, hdec⟩ := l8_lgfPlusCont_decomp hd P h hh
  let k : Ω → DistRd d := fun ω => affineComp 1 z (h₀ ω)
  have hk : IsWholeSpaceLGF k P := hh₀.1.affineComp one_pos z
  have hwk := (l8_length_weyl_of_normalized hd ξ D
    (l8_normalizedWeyl_of_good hd hκ ξ εs hεs hN) P k
    hk.isLGFPlusCont).2
  have hw0 := (l8_length_weyl_of_normalized hd ξ D
    (l8_normalizedWeyl_of_good hd hκ ξ εs hεs hN) P h₀
    hh₀.1.isLGFPlusCont).2
  filter_upwards [l8_translation_normalized hTr hd κ hκ ξ εs hεs
    hN P h₀ hh₀ z, hwk, hw0] with ω htr hwk hw0 u v
  have hA : D (k ω) = (D (h₀ ω)).affine 1 one_ne_zero z := by
    apply Subtype.ext
    apply ContinuousMap.ext
    rintro ⟨x, y⟩
    simpa only [D, k, ContMetric.affine_apply, one_smul,
      add_comm z x, add_comm z y] using htr x y
  have he := hwk ((g ω).comp (affinePt 1 z)) u v
  rw [hA, show affinePt 1 z = ContMetric.affineMap 1 z from rfl,
    weylScale_affine] at he
  simp only [ContMetric.affineMap_apply, one_smul] at he
  rw [hw0 (g ω) (u + z) (v + z)] at he
  have he' :
      (D (addFun (k ω) ((g ω).comp (affinePt 1 z)))).1 (u, v) =
        (D (addFun (h₀ ω) (g ω))).1 (u + z, v + z) :=
    (ENNReal.ofReal_eq_ofReal_iff
      ((D _).nonneg u v) ((D _).nonneg _ _)).1 he.symm
  rw [hdec ω, affineComp_addFun one_pos]
  simpa only [D, k, affinePt_apply, one_smul] using he'

end HigherDimLQGMetric
