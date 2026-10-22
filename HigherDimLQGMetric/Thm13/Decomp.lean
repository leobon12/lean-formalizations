import HigherDimLQGMetric.Thm13.NormalizedGood
import HigherDimLQGMetric.Metric.WeylCompose

/-! Decomposition of an LGF plus a continuous function into a normalized LGF
and one random continuous perturbation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l8_lgfPlusCont_decomp
    {d : ℕ} (hd : 2 ≤ d) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsLGFPlusCont h P) :
    ∃ (h₀ : Ω → DistRd d) (g : Ω → C(Rd d, ℝ)),
      IsNormalizedLGF h₀ P ∧ Measurable g ∧
      ∀ ω, h ω = addFun (h₀ ω) (g ω) := by
  obtain ⟨_, f₀, hf₀, hk⟩ := hh
  let k : Ω → DistRd d := fun ω => h ω - ofCont (f₀ ω)
  let c : Ω → ℝ := fun ω => sphereAvg (k ω) 1 0
  have hcm : Measurable c :=
    (measurable_sphereAvg_left 1 0).comp hk.measurable
  let h₀ : Ω → DistRd d := fun ω => addConst (k ω) (-c ω)
  let g : Ω → C(Rd d, ℝ) :=
    fun ω => f₀ ω + ContinuousMap.const (Rd d) (c ω)
  have hnorm : IsNormalizedLGF h₀ P :=
    hk.isNormalizedLGF_normalize (by omega)
      ((sphereConvAS_of_sphereAvg_spec (sphereAvg_spec_holds d hd)) P k hk)
  have hgm : Measurable g := hf₀.add
    (measurable_const_continuousMap.comp hcm)
  refine ⟨h₀, g, hnorm, hgm, fun ω => ?_⟩
  have hcancel :
      ContinuousMap.const (Rd d) (-c ω) +
          (f₀ ω + ContinuousMap.const (Rd d) (c ω)) = f₀ ω := by
    ext z
    simp only [ContinuousMap.add_apply, ContinuousMap.const_apply]
    ring
  calc
    h ω = addFun (k ω) (f₀ ω) := by
      rw [addFun_def]
      exact (sub_add_cancel (h ω) (ofCont (f₀ ω))).symm
    _ = addFun (k ω) (ContinuousMap.const (Rd d) (-c ω) +
          (f₀ ω + ContinuousMap.const (Rd d) (c ω))) := by rw [hcancel]
    _ = addFun (addFun (k ω) (ContinuousMap.const (Rd d) (-c ω)))
          (f₀ ω + ContinuousMap.const (Rd d) (c ω)) :=
      (addFun_addFun _ _ _).symm
    _ = addFun (h₀ ω) (g ω) := by rw [addFun_const]

theorem l8_lgfPlusBddCont_decomp
    {d : ℕ} (hd : 2 ≤ d) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsLGFPlusBddCont h P) :
    ∃ (h₀ : Ω → DistRd d) (g : Ω → C(Rd d, ℝ)),
      IsNormalizedLGF h₀ P ∧ Measurable g ∧
      (∀ ω, ∃ M : ℝ, ∀ z, |g ω z| ≤ M) ∧
      ∀ ω, h ω = addFun (h₀ ω) (g ω) := by
  obtain ⟨_, f₀, hf₀, hfb, hk⟩ := hh
  let k : Ω → DistRd d := fun ω => h ω - ofCont (f₀ ω)
  let c : Ω → ℝ := fun ω => sphereAvg (k ω) 1 0
  have hcm : Measurable c :=
    (measurable_sphereAvg_left 1 0).comp hk.measurable
  let h₀ : Ω → DistRd d := fun ω => addConst (k ω) (-c ω)
  let g : Ω → C(Rd d, ℝ) :=
    fun ω => f₀ ω + ContinuousMap.const (Rd d) (c ω)
  have hnorm : IsNormalizedLGF h₀ P :=
    hk.isNormalizedLGF_normalize (by omega)
      ((sphereConvAS_of_sphereAvg_spec (sphereAvg_spec_holds d hd)) P k hk)
  have hgm : Measurable g := hf₀.add
    (measurable_const_continuousMap.comp hcm)
  have hgb (ω : Ω) : ∃ M : ℝ, ∀ z, |g ω z| ≤ M := by
    obtain ⟨M, hM⟩ := hfb ω
    refine ⟨M + |c ω|, fun z => ?_⟩
    exact (abs_add_le _ _).trans (add_le_add (hM z) le_rfl)
  refine ⟨h₀, g, hnorm, hgm, hgb, fun ω => ?_⟩
  have hcancel :
      ContinuousMap.const (Rd d) (-c ω) +
          (f₀ ω + ContinuousMap.const (Rd d) (c ω)) = f₀ ω := by
    ext z
    simp only [ContinuousMap.add_apply, ContinuousMap.const_apply]
    ring
  calc
    h ω = addFun (k ω) (f₀ ω) := by
      rw [addFun_def]
      exact (sub_add_cancel (h ω) (ofCont (f₀ ω))).symm
    _ = addFun (k ω) (ContinuousMap.const (Rd d) (-c ω) +
          (f₀ ω + ContinuousMap.const (Rd d) (c ω))) := by rw [hcancel]
    _ = addFun (addFun (k ω) (ContinuousMap.const (Rd d) (-c ω)))
          (f₀ ω + ContinuousMap.const (Rd d) (c ω)) :=
      (addFun_addFun _ _ _).symm
    _ = addFun (h₀ ω) (g ω) := by rw [addFun_const]

/-- The simultaneous normalized-field form of the Weyl identity. -/
def L8NormalizedWeyl {d : ℕ} (ξ : ℝ)
    (D : DistRd d → ContMetric d) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistRd d),
    IsNormalizedLGF h P →
    ∀ᵐ ω ∂P, ∃ hD : (D (h ω)).IsLength,
      ∀ f : C(Rd d, ℝ),
        D (addFun (h ω) f) = weylMetric ξ f (D (h ω)) hD

/-- The normalized identity and the random-continuous decomposition prove
Axioms I and III for the full input class. -/
theorem l8_length_weyl_of_normalized
    {d : ℕ} (hd : 2 ≤ d) (ξ : ℝ)
    (D : DistRd d → ContMetric d) (hN : L8NormalizedWeyl ξ D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hh : IsLGFPlusCont h P) :
    (∀ᵐ ω ∂P, (D (h ω)).IsLength) ∧
      (∀ᵐ ω ∂P, ∀ f : C(Rd d, ℝ), ∀ z w : Rd d,
        weylScale ξ f (D (h ω)) z w =
          ENNReal.ofReal ((D (addFun (h ω) f)).1 (z, w))) := by
  obtain ⟨h₀, g, hh₀, _hgm, hdec⟩ := l8_lgfPlusCont_decomp hd P h hh
  have hW := hN P h₀ hh₀
  refine ⟨hW.mono (fun ω hω => ?_),
    hW.mono (fun ω hω f z w => ?_)⟩
  · obtain ⟨hD, hω⟩ := hω
    rw [hdec ω, hω (g ω)]
    exact weylMetric_isLength hD
  · obtain ⟨hD, hω⟩ := hω
    calc
      weylScale ξ f (D (h ω)) z w =
          weylScale ξ f (weylMetric ξ (g ω) (D (h₀ ω)) hD) z w := by
        rw [hdec ω, hω (g ω)]
      _ = weylScale ξ (f + g ω) (D (h₀ ω)) z w :=
        weylScale_weylMetric hD f z w
      _ = ENNReal.ofReal ((D (addFun (h ω) f)).1 (z, w)) := by
        rw [hdec ω, addFun_addFun, hω (g ω + f), weylMetric_spec]
        rw [add_comm]

end HigherDimLQGMetric
