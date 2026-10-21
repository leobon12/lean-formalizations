import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Compact modulus sets and the path modulus of Corollary 6.0′ (packet P-T0, targets T2 and T3)

Source: `source/small-parameter-lqg-geodesics.pdf`, §6.3 and Theorem 1.2, as corrected by planning
audit GA3 (`planning/audits/GA3-sections-5-6.md`, Details A11, A12 and (c4)(i); ruling G12). Both
results are deterministic and use Mathlib only.

* `modulusSet w`: the paths `f ∈ C([0,1], ℂ)` with `f 0 = 0` and modulus of continuity `w`, i.e.
  `‖f s - f t‖ ≤ w |s - t|`.
* `isCompact_modulusSet` (**T3**, Arzelà–Ascoli for a fixed modulus): if `w(r) → 0` as `r → 0⁺`,
  then `modulusSet w` is compact. Ported verbatim from GA3's compiled scratch proof (c4)(i).
* `path_modulus_of_smallScale` (**T2**, Corollary 6.0′, deterministic form): let `d` satisfy the
  small-scale lower bound `d(z,w) ≥ |z-w|^{5/4}` on `B̄₂` for `0 < |z-w| ≤ 2^{-n}`, and let `η` be a
  path in `B̄₂` with the constant-speed identity `d(η s, η t) = |t - s| d(0,1)` and `d(0,1) ≤ 2`.
  Then `|η(s) - η(t)| ≤ (2|s-t|)^{4/5}` whenever `|s - t| < 2^{-5n/4}/2`. It is applied with
  `d = e^{-b_γ} D` (ruling G8), which keeps the constant-speed identity of a `D`-geodesic.

Proof of T2 (GA3 A11). Put `ρ = |η(s) - η(t)|` and `δ = 2^{-n}`. If `0 < ρ ≤ δ`, then
`ρ^{5/4} ≤ d(η s, η t) = |s-t| d(0,1) ≤ 2|s-t|`. If `ρ > δ`, the intermediate value theorem gives
`u` between `s` and `t` with `|η(s) - η(u)| = δ`, whence `δ^{5/4} ≤ 2|s-u| ≤ 2|s-t| < δ^{5/4}`,
which is absurd. The hypotheses `η 0 = 0` and `η 1 = 1` of the packet statement are not needed by
this argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology Set

namespace SmallGammaGeodesics

/-! ## T3: compactness of a modulus set (GA3 (c4)(i), verbatim) -/

/-- Paths vanishing at `0` with modulus of continuity `w`. -/
def modulusSet (w : ℝ → ℝ) : Set C(unitInterval, ℂ) :=
  {f | f 0 = 0 ∧ ∀ s t : unitInterval, ‖f s - f t‖ ≤ w |(s : ℝ) - t|}

/-- **Arzelà–Ascoli for a fixed modulus**: if `w(r) → 0` as `r → 0⁺`, `modulusSet w` is compact. -/
theorem isCompact_modulusSet (w : ℝ → ℝ) (hw : Tendsto w (𝓝[≥] 0) (𝓝 0)) :
    IsCompact (modulusSet w) := by
  set T : Set (unitInterval → ℂ) :=
    {f | f 0 = 0 ∧ ∀ s t : unitInterval, ‖f s - f t‖ ≤ w |(s : ℝ) - t|} with hT
  -- a uniform `δ` for each `ε`
  have hδ : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 ≤ r → r < δ → w r < ε := by
    intro ε hε
    have h1 : ∀ᶠ r in 𝓝[≥] (0 : ℝ), w r < ε := hw.eventually (gt_mem_nhds hε)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h1
    obtain ⟨δ, hδ0, hδ⟩ := h1
    refine ⟨δ, hδ0, fun r hr0 hrδ => hδ ?_ hr0⟩
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg hr0]
  -- every element of `T` is continuous
  have hcont : ∀ f ∈ T, Continuous f := by
    intro f hf
    rw [Metric.continuous_iff]
    intro b ε hε
    obtain ⟨δ, hδ0, hδw⟩ := hδ ε hε
    refine ⟨δ, hδ0, fun a ha => ?_⟩
    rw [dist_eq_norm]
    refine (hf.2 a b).trans_lt (hδw _ (abs_nonneg _) ?_)
    rwa [Subtype.dist_eq, Real.dist_eq] at ha
  have himg : ContinuousMap.toFun '' modulusSet w = T := by
    ext f
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hf
      exact ⟨⟨f, hcont f hf⟩, hf, rfl⟩
  -- `T` is closed and contained in a product of closed balls
  have hTc : IsClosed T := by
    have h1 : IsClosed {f : unitInterval → ℂ | f 0 = 0} :=
      isClosed_eq (continuous_apply 0) continuous_const
    have h2 : IsClosed {f : unitInterval → ℂ |
        ∀ s t : unitInterval, ‖f s - f t‖ ≤ w |(s : ℝ) - t|} := by
      have e : {f : unitInterval → ℂ | ∀ s t : unitInterval, ‖f s - f t‖ ≤ w |(s : ℝ) - t|} =
          ⋂ s : unitInterval, ⋂ t : unitInterval, {f | ‖f s - f t‖ ≤ w |(s : ℝ) - t|} := by
        ext f
        simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      rw [e]
      exact isClosed_iInter fun s => isClosed_iInter fun t =>
        isClosed_le ((continuous_apply s).sub (continuous_apply t)).norm continuous_const
    exact h1.inter h2
  have hsub : T ⊆ Set.pi univ fun t : unitInterval => Metric.closedBall (0 : ℂ) (w |(t : ℝ) - 0|) := by
    intro f hf t _
    have h := hf.2 t 0
    rw [hf.1, sub_zero] at h
    simpa [Metric.mem_closedBall, dist_zero_right] using h
  have hTk : IsCompact T :=
    (isCompact_univ_pi fun t => isCompact_closedBall (0 : ℂ) _).of_isClosed_subset hTc hsub
  refine ArzelaAscoli.isCompact_of_equicontinuous (modulusSet w) (himg ▸ hTk) ?_
  intro p
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  obtain ⟨δ, hδ0, hδw⟩ := hδ ε hε
  filter_upwards [Metric.ball_mem_nhds p hδ0] with q hq
  intro f
  rw [dist_eq_norm]
  refine (f.2.2 p q).trans_lt (hδw _ (abs_nonneg _) ?_)
  rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] at hq
  rwa [abs_sub_comm]

/-! ## T2: the path modulus of Corollary 6.0′ (GA3 A11) -/

/-- `ρ ≤ x^{4/5}` from `ρ^{5/4} ≤ x`, for `ρ ≥ 0`. -/
theorem le_rpow_four_fifths_of_rpow_five_fourths_le {ρ x : ℝ} (hρ : 0 ≤ ρ)
    (h : ρ ^ (5 / 4 : ℝ) ≤ x) : ρ ≤ x ^ (4 / 5 : ℝ) := by
  calc ρ = (ρ ^ (5 / 4 : ℝ)) ^ (4 / 5 : ℝ) := by
        rw [← Real.rpow_mul hρ]
        norm_num
    _ ≤ x ^ (4 / 5 : ℝ) := Real.rpow_le_rpow (Real.rpow_nonneg hρ _) h (by norm_num)

set_option linter.unusedVariables false in
/-- **Corollary 6.0′ (deterministic path modulus; GA3 A11).** If `d(z,w) ≥ |z-w|^{5/4}` for all
`z, w ∈ B̄₂` with `0 < |z-w| ≤ 2^{-n}`, and `η` is a path in `B̄₂` with
`d(η s, η t) = |t-s| d(0,1)` and `d(0,1) ≤ 2`, then `|η(s) - η(t)| ≤ (2|s-t|)^{4/5}` whenever
`|s-t| < (2^{-n})^{5/4}/2`.

The signature is the packet's verbatim. The endpoint hypotheses `h0`, `h1` are part of the setting
(a geodesic from `0` to `1`) but the argument does not use them, so the unused-variable linter is
silenced here. -/
theorem path_modulus_of_smallScale (d : ℂ × ℂ → ℝ) (η : C(unitInterval, ℂ)) (n : ℕ)
    (h0 : η 0 = 0) (h1 : η 1 = 1)
    (hgeo : ∀ s t : unitInterval, d (η s, η t) = |(t : ℝ) - s| * d (0, 1))
    (hd01 : d (0, 1) ≤ 2) (hball : ∀ t, η t ∈ Metric.closedBall (0 : ℂ) 2)
    (hsmall : ∀ z ∈ Metric.closedBall (0 : ℂ) 2, ∀ w ∈ Metric.closedBall (0 : ℂ) 2,
      0 < ‖z - w‖ → ‖z - w‖ ≤ (2 : ℝ)⁻¹ ^ n → ‖z - w‖ ^ (5 / 4 : ℝ) ≤ d (z, w)) :
    ∀ s t : unitInterval, |(s : ℝ) - t| < ((2 : ℝ)⁻¹ ^ n) ^ (5 / 4 : ℝ) / 2 →
      ‖η s - η t‖ ≤ (2 * |(s : ℝ) - t|) ^ (4 / 5 : ℝ) := by
  intro s t hst
  set δ : ℝ := (2 : ℝ)⁻¹ ^ n with hδ
  have hδ0 : 0 < δ := pow_pos (by norm_num) n
  -- the small-scale bound along the path, measured from `η s`
  have hkey : ∀ u : unitInterval, 0 < ‖η s - η u‖ → ‖η s - η u‖ ≤ δ →
      ‖η s - η u‖ ^ (5 / 4 : ℝ) ≤ 2 * |(s : ℝ) - u| := by
    intro u hpos hle
    calc ‖η s - η u‖ ^ (5 / 4 : ℝ) ≤ d (η s, η u) := hsmall _ (hball s) _ (hball u) hpos hle
      _ = |(u : ℝ) - s| * d (0, 1) := hgeo s u
      _ ≤ |(u : ℝ) - s| * 2 := mul_le_mul_of_nonneg_left hd01 (abs_nonneg _)
      _ = 2 * |(s : ℝ) - u| := by rw [abs_sub_comm]; ring
  by_cases hρ : ‖η s - η t‖ ≤ δ
  · rcases (norm_nonneg (η s - η t)).eq_or_lt with h | h
    · rw [← h]
      exact Real.rpow_nonneg (by positivity) _
    · exact le_rpow_four_fifths_of_rpow_five_fourths_le (norm_nonneg _) (hkey t h hρ)
  · exfalso
    replace hρ : δ < ‖η s - η t‖ := not_le.mp hρ
    -- intermediate value theorem for `x ↦ |η(s) - η(x)|` on the segment between `s` and `t`
    set f : ℝ → ℝ := fun x => ‖η s - η (Set.projIcc 0 1 zero_le_one x)‖ with hf_def
    have hf : Continuous f :=
      (continuous_const.sub (η.continuous.comp continuous_projIcc)).norm
    have hfs : f s = 0 := by
      simp only [hf_def, Set.projIcc_val, sub_self, norm_zero]
    have hft : f t = ‖η s - η t‖ := by
      simp only [hf_def, Set.projIcc_val]
    have hmem : δ ∈ Set.uIcc (f s) (f t) := by
      rw [hfs, hft]
      exact Set.mem_uIcc_of_le hδ0.le hρ.le
    obtain ⟨x, hx, hfx⟩ := intermediate_value_uIcc hf.continuousOn hmem
    have hx01 : x ∈ Set.Icc (0 : ℝ) 1 := Set.uIcc_subset_Icc s.2 t.2 hx
    set u : unitInterval := Set.projIcc 0 1 zero_le_one x with hu_def
    have hu : (u : ℝ) = x := by
      rw [hu_def, Set.projIcc_of_mem zero_le_one hx01]
    have hfu : ‖η s - η u‖ = δ := hfx
    have hδu := hkey u (hfu ▸ hδ0) hfu.le
    rw [hfu] at hδu
    have hsu : |(s : ℝ) - u| ≤ |(s : ℝ) - t| := by
      rw [hu, abs_sub_comm, abs_sub_comm (s : ℝ)]
      exact Set.abs_sub_left_of_mem_uIcc hx
    linarith

end SmallGammaGeodesics
