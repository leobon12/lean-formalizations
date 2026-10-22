import HigherDimLQGMetric.Markov.LogPot

/-!
# Changing the normalization of the Gaussian projection

The projection space is conveniently defined using a smooth probability test `ρ`. The statement
of D-M uses a sphere average. These identities relate the two on the event where the sphere
average converges.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ}

/-- Recentering at a mean-one test is invariant under any constant shift, including the sphere
normalization. This identity holds for every distribution, even when the sphere average diverges. -/
theorem markov_recenter_sphereCentered {ρ : TestRd d} (hρ : ∫ x, ρ x = 1)
    (g : DistRd d) (r : ℝ) (z : Rd d) :
    recenter ρ (addConst g (-sphereAvg g r z)) = recenter ρ g :=
  recenter_addConst hρ g _

/-- On the convergence event, sphere normalization can be performed after smooth-test
recentering. This removes the unknown additive constant exactly. -/
theorem markov_sphereCentered_recenter (hd : 1 ≤ d) {ρ : TestRd d}
    (g : DistRd d) (r : ℝ) (z : Rd d)
    (hconv : ∃ a, Tendsto (sphereAvgSeq g r z) atTop (𝓝 a)) :
    addConst (recenter ρ g) (-sphereAvg (recenter ρ g) r z) =
      addConst g (-sphereAvg g r z) := by
  obtain ⟨a, ha⟩ := hconv
  rw [recenter, sphereAvg_addConst_of_tendsto hd ha, addConst_addConst]
  congr 1
  ring

/-- The change of normalization holds almost surely for every whole-space LGF. -/
theorem markov_sphereCentered_recenter_ae {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistRd d} (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    {ρ : TestRd d} {r : ℝ} (hr : 0 < r) (z : Rd d) :
    (fun ω => addConst (recenter ρ (h ω))
      (-sphereAvg (recenter ρ (h ω)) r z)) =ᵐ[P]
      (fun ω => addConst (h ω) (-sphereAvg (h ω) r z)) := by
  filter_upwards [hh.ae_exists_tendsto_sphereAvgSeq hd hr z] with ω hω
  exact markov_sphereCentered_recenter (by omega) (h ω) r z hω

/-- Add a constant to a distribution on an open set. -/
def markovShiftOn (V : Opens (Rd d)) (u : DistOn V) (c : ℝ) : DistOn V :=
  u + c • restrictTo V (ofCont (ContinuousMap.const (Rd d) 1))

theorem markovShiftOn_apply (V : Opens (Rd d)) (u : DistOn V) (c : ℝ)
    (φ : TestOn V) : markovShiftOn V u c φ = u φ + c * ∫ x, φ x := by
  simp [markovShiftOn, restrictTo_ofCont_apply]

theorem markov_measurableShiftOn (V : Opens (Rd d)) :
    Measurable fun p : DistOn V × ℝ => markovShiftOn V p.1 p.2 := by
  unfold markovShiftOn
  fun_prop

theorem markov_restrictTo_addConst (V : Opens (Rd d)) (g : DistRd d) (c : ℝ) :
    restrictTo V (addConst g c) = markovShiftOn V (restrictTo V g) c := by
  ext φ
  rw [restrictTo_addConst_apply, markovShiftOn_apply]

/-- Sphere normalization of an open-set restriction, obtained from locality of sphere averages. -/
def markovSphereCenterMap (V : Opens (Rd d)) (z : Rd d) (r : ℝ)
    (hV : Metric.sphere z |r| ⊆ V) : DistOn V → DistOn V :=
  fun u => markovShiftOn V u
    (-(Classical.choose (exists_measurable_sphereAvg_eq_restrictTo hV)) u)

theorem markov_measurableSphereCenterMap (V : Opens (Rd d)) (z : Rd d) (r : ℝ)
    (hV : Metric.sphere z |r| ⊆ V) :
    Measurable (markovSphereCenterMap V z r hV) := by
  unfold markovSphereCenterMap
  exact (markov_measurableShiftOn V).comp (measurable_id.prodMk
    ((Classical.choose_spec (exists_measurable_sphereAvg_eq_restrictTo hV)).1.neg))

theorem markov_restrictTo_sphereCentered (V : Opens (Rd d)) (z : Rd d) (r : ℝ)
    (hV : Metric.sphere z |r| ⊆ V) (g : DistRd d) :
    restrictTo V (addConst g (-sphereAvg g r z)) =
      markovSphereCenterMap V z r hV (restrictTo V g) := by
  rw [markovSphereCenterMap, ← (Classical.choose_spec
    (exists_measurable_sphereAvg_eq_restrictTo hV)).2 g,
    markov_restrictTo_addConst]

/-- Orthogonal residuals remain independent after changing from smooth-test recentering to the
sphere normalization in the D-M statement. -/
theorem markov_indep_residual_sphere_field {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P) (V : Opens (Rd d))
    (z : Rd d) {r : ℝ} (hr : 0 < r) (hV : Metric.sphere z r ⊆ V)
    {ρ : TestRd d} (hρ : ∫ x, ρ x = 1)
    (R : Ω → DistOn (extOpen V)) (hR : Measurable R)
    (hpair : ∀ ψ : TestOn (extOpen V),
      (fun ω => R ω ψ) =ᵐ[P] (fun ω => (markovResidualVec hh V hρ ψ : Ω → ℝ) ω)) :
    ProbabilityTheory.Indep (MeasurableSpace.comap R inferInstance)
      (fieldSigmaRd (fun ω => addConst (h ω) (-sphereAvg (h ω) r z)) V) P := by
  let X : Ω → DistOn V := fun ω => restrictTo V (recenter ρ (h ω))
  let Y : Ω → DistOn V := fun ω =>
    restrictTo V (addConst (h ω) (-sphereAvg (h ω) r z))
  have hV' : Metric.sphere z |r| ⊆ V := by simpa [abs_of_pos hr] using hV
  let T := markovSphereCenterMap V z r hV'
  have hY : Y =ᵐ[P] T ∘ X := by
    filter_upwards [markov_sphereCentered_recenter_ae hd hh hr z] with ω hω
    dsimp [Y, X, T]
    rw [← hω, markov_restrictTo_sphereCentered]
  have hind : ProbabilityTheory.IndepFun R X P := by
    exact (IndepFun_iff_Indep _ _ P).mpr
      (markov_indep_residual_dist hh V hρ R hR hpair)
  have hind' : ProbabilityTheory.IndepFun R (T ∘ X) P := by
    simpa only [Function.id_comp] using hind.comp measurable_id
      (markov_measurableSphereCenterMap V z r hV')
  have hindY : ProbabilityTheory.IndepFun R Y P := hind'.congr Filter.EventuallyEq.rfl hY.symm
  exact (IndepFun_iff_Indep _ _ P).mp hindY

/-- A sphere contained in `V` supplies a smooth, mean-one test supported in `V`. This allows
all recentered pairings in the Gaussian Hilbert space to be supported in the interior. -/
theorem markov_exists_inner_normalizer (hd : 1 ≤ d) (V : Opens (Rd d))
    (z : Rd d) (r : ℝ) (hV : Metric.sphere z |r| ⊆ V) :
    ∃ ρ : TestRd d, (∫ x, ρ x = 1) ∧ tsupport (ρ : Rd d → ℝ) ⊆ V := by
  obtain ⟨N, hN⟩ := exists_tsupport_sphBump_subset hV
  exact ⟨sphBump N z r, integral_sphBump hd N z r, hN N le_rfl⟩

end HigherDimLQGMetric
