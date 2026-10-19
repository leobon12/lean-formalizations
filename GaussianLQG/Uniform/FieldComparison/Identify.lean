import GaussianLQG.Uniform.FieldComparison.Kernel

/-!
# OP-4: the heat-mollified normalized GFF as a white-noise integral (Route U, U14)

Let `W` be a white noise and `h₀` the whole-plane GFF built from it, `h₀(φ) = W(testL2 φ)` a.s.
for every test function (`LQGMetric.DG.exists_wn_wholePlaneGFF`), and let
`h̊₀ = h₀ − (h₀)_1(0)` be the field normalized by its unit-circle average. Blueprint A.6 /
audit A5, Lemma A6.2: `h̊₀*_ε(z)` is the white-noise integral of the kernel
`p_{(t+ε²)/2}(z − w) − b_t(w)`, `b_t = σ * p_{t/2}` (source (A.20) after the semigroup
property). In Lean:

* `ae_heatMollify_eq_wn`: `h₀*_ε(z) = W(molKerL2 ε z)` a.s., for each `z` and `ε ≠ 0`
  (`heatMollify` is the a.s. limit of the truncated pairings `h₀(p_{ε²/2}(z,·) χ_m)`, which equal
  `W(testL2 (p_{ε²/2}(z,·) χ_m))` a.s. and converge in `L²(P)` to `W(molKerL2 ε z)`);
* `ae_circleAvg_eq_wn_circKer`: the normalization constant `(h₀)_1(0) = W(circKerL2)` a.s.;
* `ae_heatMollify_norm_eq_wn`: `h̊₀*_ε(z) = W(molKerL2 ε z − circKerL2)` a.s., where
  `molKerL2 ε z − circKerL2` is a.e. `normMolKer ε z`
  `= √π 1_{t>0} (p_{ε²/2+t/2}(z, y) − ∫ p_{t/2}(u, y) σ(du))` (`coeFn_molKerL2_sub_circKerL2`);
* `ae_continuous_heatMollify_norm`: a.s. `z ↦ h̊₀*_ε(z)` is continuous (and the truncations converge
  locally uniformly), so `h̊₀*_ε` is a continuous version of the white-noise process
  `z ↦ W(molKerL2 ε z − circKerL2)`; any other version that is a.s. continuous on a set `S`
  agrees with it a.s. simultaneously for all `z ∈ S` (`ae_eqOn_of_ae_eq`);
  packaged: `heatMollify_norm_continuous_version`.

Own elementary arguments (the pattern of `LQGMetric.DG.ae_circleAvg_eq_wn_lim`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace GaussianLQG
namespace FieldCmp

open LQGMetric LQGMetric.WhiteNoise LQGMetric.GFFExist

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
  {h₀ : Ω → DistC}

/-! ### Elementary facts -/

/-- `W (f − g) = W f − W g` almost surely. -/
lemma wn_sub_ae (hW : IsWhiteNoise P W) (f g : WNSpace) :
    W (f - g) =ᵐ[P] fun ω => W f ω - W g ω := by
  filter_upwards [hW.add_ae (f - g) g] with ω hω
  rw [sub_add_cancel] at hω
  linarith

/-- `(g + c)*_ε = g*_ε + c` where the truncations of `g` converge. -/
lemma heatMollify_addConst {ε : ℝ} (hε : ε ≠ 0) {g : DistC} {z : ℂ}
    (hg : Tendsto (fun n : ℕ => g (heatTrunc (ε ^ 2 / 2) z n)) atTop (𝓝 (heatMollify ε g z)))
    (c : ℝ) : heatMollify ε (addConst g c) z = heatMollify ε g z + c := by
  have hs : 0 < ε ^ 2 / 2 := by positivity
  have h2 := tendsto_ofCont_heatTrunc (ContinuousMap.const ℂ c) (ε ^ 2 / 2) hs z
    (integrable_heatKernel_mul_of_bdd _ |c| (fun _ => le_rfl) _ hs z)
  have hc : ∫ w, heatKernel (ε ^ 2 / 2) z w * (ContinuousMap.const ℂ c) w = c := by
    simp only [ContinuousMap.const_apply]
    rw [integral_mul_const, integral_heatKernel _ hs z, one_mul]
  rw [hc] at h2
  have h3 := hg.add h2
  show limUnder atTop (fun n : ℕ => g (heatTrunc (ε ^ 2 / 2) z n) +
    ofCont (ContinuousMap.const ℂ c) (heatTrunc (ε ^ 2 / 2) z n)) = _
  exact h3.limUnder_eq

/-- Two processes that are a.s. continuous on `S` and agree a.s. at each point of `S` agree a.s.
simultaneously on `S` (countable dense subset). -/
lemma ae_eqOn_of_ae_eq {S : Set ℂ} {X Y : ℂ → Ω → ℝ}
    (hX : ∀ᵐ ω ∂P, ContinuousOn (fun z => X z ω) S) (hY : ∀ᵐ ω ∂P, ContinuousOn (fun z => Y z ω) S)
    (h : ∀ z ∈ S, X z =ᵐ[P] Y z) : ∀ᵐ ω ∂P, ∀ z ∈ S, X z ω = Y z ω := by
  obtain ⟨D, hDc, hDs, hDd⟩ := TopologicalSpace.exists_countable_dense_subset S
  have hD : ∀ᵐ ω ∂P, ∀ q ∈ D, X q ω = Y q ω := by
    rw [ae_ball_iff hDc]
    exact fun q hq => h q (hDs hq)
  filter_upwards [hD, hX, hY] with ω hω h1 h2
  exact Set.EqOn.of_subset_closure hω h1 h2 hDs hDd

/-! ### The identification -/

section Ident

variable (hW : IsWhiteNoise P W) (hh : IsWholePlaneGFF h₀ P)
  (hae : ∀ φ : TestC, (fun ω => h₀ ω φ) =ᵐ[P] W (testL2 φ))
include hW hh hae

/-- **OP-4, unnormalized field**: `h₀*_ε(z) = W(molKerL2 ε z)` almost surely. -/
theorem ae_heatMollify_eq_wn {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) :
    (fun ω => heatMollify ε (h₀ ω) z) =ᵐ[P] W (molKerL2 ε z) := by
  have := hW.isProbabilityMeasure
  set φ : ℕ → TestC := fun m => heatTrunc (ε ^ 2 / 2) z m with hφ
  have hmo : ∀ m, W (testL2 (φ m)) =ᵐ[P] fun ω => h₀ ω (φ m) := fun m => (hae (φ m)).symm
  have h1 : TendstoInMeasure P (fun m ω => W (testL2 (φ m)) ω) atTop (W (molKerL2 ε z)) := by
    refine tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero
      (fun m => (hW.measurable _).aestronglyMeasurable) (hW.measurable _).aestronglyMeasurable ?_
    have e : ∀ m, eLpNorm (W (testL2 (φ m)) - W (molKerL2 ε z)) 2 P =
        ENNReal.ofReal ‖testL2 (φ m) - molKerL2 ε z‖ := fun m => DG.eLpNorm_wn_sub hW _ _
    simp_rw [e]
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal
      (tendsto_iff_norm_sub_tendsto_zero.1 (tendsto_testL2_heatTrunc hε z))
  have h2 : TendstoInMeasure P (fun m ω => h₀ ω (φ m)) atTop (W (molKerL2 ε z)) :=
    h1.congr' (Eventually.of_forall hmo) EventuallyEq.rfl
  have h3 : TendstoInMeasure P (fun m ω => h₀ ω (φ m)) atTop
      (fun ω => heatMollify ε (h₀ ω) z) := by
    refine tendstoInMeasure_of_tendsto_ae (fun m => ?_) ?_
    · exact (hW.measurable _).aestronglyMeasurable.congr (hmo m)
    · exact hh.ae_tendsto_heatMollify ε hε z
  exact tendstoInMeasure_ae_unique h3 h2

/-- The normalization constant: `(h₀)_1(0) = W(circKerL2)` almost surely. -/
theorem ae_circleAvg_eq_wn_circKer :
    (fun ω => circleAvg (h₀ ω) 1 0) =ᵐ[P] W circKerL2 :=
  DG.ae_circleAvg_eq_wn_lim hW hh hae 0 one_pos tendsto_testL2_circBump

/-- **OP-4**: the heat mollification of the normalized field `h̊₀ = h₀ − (h₀)_1(0)` is the
white-noise integral `W(molKerL2 ε z) − (h₀)_1(0)`, almost surely. -/
theorem ae_heatMollify_norm_eq_wn_sub {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) :
    (fun ω => heatMollify ε (addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)) z) =ᵐ[P]
      fun ω => W (molKerL2 ε z) ω - circleAvg (h₀ ω) 1 0 := by
  filter_upwards [hh.ae_tendsto_heatMollify ε hε z, ae_heatMollify_eq_wn hW hh hae hε z]
    with ω h1 h2
  rw [heatMollify_addConst hε h1, h2]
  ring

/-- **OP-4, kernel form**: `h̊₀*_ε(z) = W(molKerL2 ε z − circKerL2)` almost surely. -/
theorem ae_heatMollify_norm_eq_wn {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) :
    (fun ω => heatMollify ε (addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)) z) =ᵐ[P]
      W (molKerL2 ε z - circKerL2) := by
  filter_upwards [ae_heatMollify_norm_eq_wn_sub hW hh hae hε z, ae_circleAvg_eq_wn_circKer hW hh hae,
    wn_sub_ae hW (molKerL2 ε z) circKerL2] with ω h1 h2 h3
  rw [h1, h2, h3]

end Ident

/-- The normalized field is a whole-plane GFF. -/
lemma isWholePlaneGFF_norm (hh : IsWholePlaneGFF h₀ P) :
    IsWholePlaneGFF (fun ω => addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)) P :=
  hh.addConst ((measurable_circleAvg_left 1 0).comp hh.measurable).neg

/-- **Continuity**: almost surely the truncations of `h̊₀` converge locally uniformly and
`z ↦ h̊₀*_ε(z)` is continuous. -/
theorem ae_continuous_heatMollify_norm (hh : IsWholePlaneGFF h₀ P) {ε : ℝ} (hε : ε ≠ 0) :
    ∀ᵐ ω ∂P, TendstoLocallyUniformly (fun (n : ℕ) (z : ℂ) =>
        addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0) (heatTrunc (ε ^ 2 / 2) z n))
      (heatMollify ε (addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0))) atTop ∧
      Continuous (heatMollify ε (addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0))) :=
  (isWholePlaneGFF_norm hh).ae_tendstoLocallyUniformly_heatMollify ε hε

/-- **OP-4, packaged**: `z ↦ h̊₀*_ε(z)` is a continuous version of the white-noise process
`z ↦ W(molKerL2 ε z − circKerL2)`: for each `z` the two agree a.s., `h̊₀*_ε` is a.s. continuous,
and every other version that is a.s. continuous agrees with `h̊₀*_ε` a.s. simultaneously for all
`z ∈ ℂ` (in particular on every compact). -/
theorem heatMollify_norm_continuous_version (hW : IsWhiteNoise P W) (hh : IsWholePlaneGFF h₀ P)
    (hae : ∀ φ : TestC, (fun ω => h₀ ω φ) =ᵐ[P] W (testL2 φ)) {ε : ℝ} (hε : ε ≠ 0) :
    (∀ z : ℂ, (fun ω => heatMollify ε (addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)) z) =ᵐ[P]
      W (molKerL2 ε z - circKerL2)) ∧
    (∀ᵐ ω ∂P, Continuous (heatMollify ε (addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)))) ∧
    ∀ Y : ℂ → Ω → ℝ, (∀ᵐ ω ∂P, Continuous fun z => Y z ω) →
      (∀ z, Y z =ᵐ[P] W (molKerL2 ε z - circKerL2)) →
      ∀ᵐ ω ∂P, ∀ z, Y z ω = heatMollify ε (addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)) z := by
  refine ⟨ae_heatMollify_norm_eq_wn hW hh hae hε,
    (ae_continuous_heatMollify_norm hh hε).mono fun ω hω => hω.2, fun Y hYc hY => ?_⟩
  have h := ae_eqOn_of_ae_eq (S := univ) (X := Y)
    (Y := fun z ω => heatMollify ε (addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)) z)
    (hYc.mono fun ω hω => hω.continuousOn)
    ((ae_continuous_heatMollify_norm hh hε).mono fun ω hω => hω.2.continuousOn)
    (fun z _ => (hY z).trans (ae_heatMollify_norm_eq_wn hW hh hae hε z).symm)
  filter_upwards [h] with ω hω z
  exact hω z (mem_univ z)

/-! ### The kernel of the normalized field (source (A.20), mollified) -/

/-- The kernel of `h̊₀*_ε(z)`: `√π 1_{t>0} (p_{ε²/2 + t/2}(z, y) − b_t(y))`,
`b_t(y) = ∫ p_{t/2}(u, y) σ(du)` with `σ` the uniform measure on the unit circle. -/
def normMolKer (ε : ℝ) (z : ℂ) (q : ℝ × ℂ) : ℝ :=
  Real.sqrt Real.pi * (Ioi (0 : ℝ)).indicator (fun t => heatKernel (ε ^ 2 / 2 + t / 2) z q.2 -
    ∫ u, heatKernel (t / 2) u q.2 ∂QuantumZipper.circleUnif 0 1) q.1

theorem coeFn_molKerL2_sub_circKerL2 {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) :
    ((molKerL2 ε z - circKerL2 : WNSpace) : ℝ × ℂ → ℝ) =ᵐ[volume] normMolKer ε z := by
  filter_upwards [Lp.coeFn_sub (molKerL2 ε z) circKerL2, coeFn_molKerL2 hε z, coeFn_circKerL2]
    with q h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3]
  unfold molKer DG.circKerLim normMolKer
  by_cases hq : q.1 ∈ Ioi (0 : ℝ)
  · simp only [indicator_of_mem hq]
    ring
  · simp only [indicator_of_notMem hq, mul_zero, sub_zero]

end FieldCmp
end GaussianLQG
