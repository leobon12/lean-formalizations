import HigherDimLQGMetric.B3.Interfaces
import HigherDimLQGMetric.Sphere.Conv
import HigherDimLQGMetric.Field.SphereBump
import HigherDimLQGMetric.Field.LGFPlusCont
import HigherDimLQGMetric.Local.CopiesSigma

/-! Normalization identities and local observability of a second sphere average. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- After normalizing at one sphere, the average at another sphere is the
difference of the original averages, almost surely. -/
theorem l7a_ae_sphereAvg_addConst {d : ℕ} (hd : 2 ≤ d)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistRd d} (hh : IsWholeSpaceLGF h P)
    {r₀ : ℝ} (hr₀ : 0 < r₀) (z₀ : Rd d)
    (r : ℝ) (z : Rd d) :
    ∀ᵐ ω ∂P,
      sphereAvg (addConst (h ω) (-sphereAvg (h ω) r z)) r₀ z₀ =
        sphereAvg (h ω) r₀ z₀ - sphereAvg (h ω) r z := by
  filter_upwards [hh.ae_exists_tendsto_sphereAvgSeq hd hr₀ z₀] with ω hω
  obtain ⟨a, ha⟩ := hω
  simpa only [sub_eq_add_neg] using
    sphereAvg_addConst_of_tendsto (by omega : 1 ≤ d) ha (-sphereAvg (h ω) r z)

/-- The average over a sphere strictly inside an open set is measurable from
the distribution restricted to that set. -/
theorem l7a_measurable_sphereAvg_fieldSigma {d : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (g : Ω → DistRd d)
    (V : TopologicalSpace.Opens (Rd d))
    (z : Rd d) (r : ℝ) (hsph : sphere z |r| ⊆ V) :
    Measurable[fieldSigmaRd g V] (fun ω => sphereAvg (g ω) r z) := by
  obtain ⟨F, hFm, hFeq⟩ := exists_measurable_sphereAvg_eq_restrictTo hsph
  letI : MeasurableSpace Ω := fieldSigmaRd g V
  have hm : Measurable (fun ω => F (restrictTo V (g ω))) :=
    hFm.comp (comap_measurable _)
  convert hm using 1
  funext ω
  exact hFeq (g ω)

/-- Distribution restriction commutes measurably with a random constant
shift when both the restriction and the shift are observable. -/
theorem l7a_measurable_restrictTo_addConst {d : ℕ}
    {Ω : Type*} {M : MeasurableSpace Ω}
    (V : TopologicalSpace.Opens (Rd d)) {g : Ω → DistRd d} {c : Ω → ℝ}
    (hg : Measurable[M] (fun ω => restrictTo V (g ω)))
    (hc : Measurable[M] c) :
    Measurable[M] (fun ω => restrictTo V (addConst (g ω) (c ω))) := by
  letI : MeasurableSpace Ω := M
  apply measurable_distOn_iff.mpr
  intro ψ
  have hm : Measurable (fun ω => restrictTo V (g ω) ψ + c ω * ∫ x, ψ x) :=
    ((measurable_distOn_apply ψ).comp hg).add (hc.mul_const _)
  convert hm using 1
  funext ω
  exact restrictTo_addConst_apply V (g ω) (c ω) ψ

/-- Recentring at a sphere inside `V` makes the first recentered
restriction observable from the second one, modulo null events. -/
theorem l7a_recenter_fieldSigma_le_aeClosure {d : ℕ} (hd : 2 ≤ d)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistRd d} (hh : IsWholeSpaceLGF h P)
    (V : TopologicalSpace.Opens (Rd d))
    {r₀ : ℝ} (hr₀ : 0 < r₀) (z₀ : Rd d)
    (hsph : sphere z₀ r₀ ⊆ V) (r : ℝ) (z : Rd d) :
    fieldSigmaRd (fun ω => l7b_recenter (h ω) r₀ z₀) V ≤
      LQGMetric.GM.Bilip.aeClosure P
        (fieldSigmaRd (fun ω => l7b_recenter (h ω) r z) V) := by
  let g₀ : Ω → DistRd d := fun ω => l7b_recenter (h ω) r₀ z₀
  let g₁ : Ω → DistRd d := fun ω => l7b_recenter (h ω) r z
  let a : Ω → ℝ := fun ω => sphereAvg (g₁ ω) r₀ z₀
  have ham : Measurable[fieldSigmaRd g₁ V] a :=
    l7a_measurable_sphereAvg_fieldSigma g₁ V z₀ r₀ (by simpa [abs_of_pos hr₀] using hsph)
  have hm : Measurable[fieldSigmaRd g₁ V]
      (fun ω => restrictTo V (addConst (g₁ ω) (-a ω))) :=
    l7a_measurable_restrictTo_addConst V (comap_measurable _) ham.neg
  have hae : ∀ᵐ ω ∂P, g₀ ω = addConst (g₁ ω) (-a ω) := by
    filter_upwards [l7a_ae_sphereAvg_addConst hd hh hr₀ z₀ r z] with ω hω
    dsimp [g₀, g₁, l7b_recenter, a] at hω ⊢
    rw [hω, addConst_addConst]
    congr 1
    ring
  rintro s ⟨S, hS, rfl⟩
  refine ⟨(fun ω => restrictTo V (addConst (g₁ ω) (-a ω))) ⁻¹' S,
    hm hS, ?_⟩
  filter_upwards [hae] with ω hω
  change (restrictTo V (g₀ ω) ∈ S) =
    (restrictTo V (addConst (g₁ ω) (-a ω)) ∈ S)
  rw [hω]

/-- Any second recentering is a measurable function of the first
recentered whole field modulo null events. -/
theorem l7a_recenter_fullSigma_le_aeClosure {d : ℕ} (hd : 2 ≤ d)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistRd d} (hh : IsWholeSpaceLGF h P)
    (r₀ : ℝ) (z₀ : Rd d)
    {r : ℝ} (hr : 0 < r) (z : Rd d) :
    fullSigmaRd (fun ω => l7b_recenter (h ω) r z) ≤
      LQGMetric.GM.Bilip.aeClosure P
        (fullSigmaRd (fun ω => l7b_recenter (h ω) r₀ z₀)) := by
  let g₀ : Ω → DistRd d := fun ω => l7b_recenter (h ω) r₀ z₀
  let g₁ : Ω → DistRd d := fun ω => l7b_recenter (h ω) r z
  let b : Ω → ℝ := fun ω => sphereAvg (g₀ ω) r z
  have hm : Measurable[fullSigmaRd g₀] (fun ω => addConst (g₀ ω) (-b ω)) := by
    letI : MeasurableSpace Ω := fullSigmaRd g₀
    exact Measurable.addConst (comap_measurable _)
      ((measurable_sphereAvg_left r z).comp (comap_measurable _)).neg
  have hae : ∀ᵐ ω ∂P, g₁ ω = addConst (g₀ ω) (-b ω) := by
    filter_upwards [l7a_ae_sphereAvg_addConst hd hh hr z r₀ z₀] with ω hω
    dsimp [g₀, g₁, l7b_recenter, b] at hω ⊢
    rw [hω, addConst_addConst]
    congr 1
    ring
  rintro s ⟨S, hS, rfl⟩
  refine ⟨(fun ω => addConst (g₀ ω) (-b ω)) ⁻¹' S, hm hS, ?_⟩
  filter_upwards [hae] with ω hω
  change (g₁ ω ∈ S) = (addConst (g₀ ω) (-b ω) ∈ S)
  rw [hω]

/-- The rescaled internal-metric family for a second recentering is the
first family multiplied by the exponential of a locally observable average. -/
theorem l7a_recenter_fam_scale_ae {d : ℕ} (hd : 2 ≤ d)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistRd d} (hh : IsWholeSpaceLGF h P)
    (D : Ω → ContMetric d) (ξ : ℝ)
    {r₀ : ℝ} (hr₀ : 0 < r₀) (z₀ : Rd d)
    (r : ℝ) (z : Rd d) :
    ∀ᵐ ω ∂P, ∀ W : Set (Rd d), ∀ u v : Rd d,
      rescFam ξ h D z r ω W u v =
        ENNReal.ofReal (Real.exp
          (ξ * sphereAvg (l7b_recenter (h ω) r z) r₀ z₀)) *
          rescFam ξ h D z₀ r₀ ω W u v := by
  filter_upwards [l7a_ae_sphereAvg_addConst hd hh hr₀ z₀ r z] with ω hω
  intro W u v
  dsimp [rescFam, l7b_recenter]
  rw [hω, ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring_nf

end HigherDimLQGMetric
