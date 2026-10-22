import HigherDimLQGMetric.Local.CopiesLaw
import HigherDimLQGMetric.Sphere.Conv
import LQGMetric.Papers.GM.S2.BilipLocal

/-!
# Sigma algebras of a normalized field and its sphere recentering

For `d ≥ 2` the fixed-scale sphere averages converge almost surely. Unit-sphere
normalization then makes the original field reconstructible from its recentering.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open LQGMetric.GM.Bilip
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ}

def l7b_recenter (h : DistRd d) (r : ℝ) (z : Rd d) : DistRd d :=
  addConst h (-sphereAvg h r z)

def l7b_unrecenter (g : DistRd d) : DistRd d :=
  addConst g (-sphereAvg g 1 0)

theorem l7b_measurable_recenter (r : ℝ) (z : Rd d) :
    Measurable (l7b_recenter (d := d) · r z) :=
  Measurable.addConst measurable_id (measurable_sphereAvg_left r z).neg

private theorem l7b_measurable_unrecenter : Measurable (l7b_unrecenter (d := d)) :=
  Measurable.addConst measurable_id (measurable_sphereAvg_left 1 0).neg

/-- Almost-sure reconstruction of a normalized LGF from its recentered field. -/
theorem l7b_unrecenter_recenter_ae {d : ℕ} (hd : 2 ≤ d) {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P) {r : ℝ} (hr : 0 < r) (z : Rd d) :
    (fun ω => l7b_unrecenter (l7b_recenter (h ω) r z)) =ᵐ[P] h := by
  have hd1 : 1 ≤ d := by omega
  filter_upwards [hh.1.ae_exists_tendsto_sphereAvgSeq hd hr z,
    hh.1.ae_exists_tendsto_sphereAvgSeq hd one_pos 0, hh.2] with ω hconv hconv1 hnorm
  obtain ⟨a, ha⟩ := hconv1
  have hs : sphereAvg (l7b_recenter (h ω) r z) 1 0 = -sphereAvg (h ω) r z := by
    dsimp [l7b_recenter]
    rw [sphereAvg_addConst_of_tendsto hd1 ha, hnorm, zero_add]
  dsimp [l7b_unrecenter]
  rw [hs, neg_neg]
  simpa only [l7b_recenter, neg_neg] using
    (addConst_neg (h ω) (-sphereAvg (h ω) r z))

/-- The recentered field contains the original normalized LGF modulo null events. -/
theorem l7b_fullSigma_le_aeClosure_recenter {d : ℕ} (hd : 2 ≤ d)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P) {r : ℝ} (hr : 0 < r) (z : Rd d) :
    fullSigmaRd h ≤ aeClosure P (fullSigmaRd (fun ω => l7b_recenter (h ω) r z)) := by
  let k : Ω → DistRd d := fun ω => l7b_recenter (h ω) r z
  have hm : Measurable[fullSigmaRd k] (fun ω => l7b_unrecenter (k ω)) :=
    (l7b_measurable_unrecenter (d := d)).comp (comap_measurable k)
  rintro s ⟨S, hS, rfl⟩
  refine ⟨(fun ω => l7b_unrecenter (k ω)) ⁻¹' S, hm hS, ?_⟩
  filter_upwards [l7b_unrecenter_recenter_ae hd hh hr z] with ω hω
  change (h ω ∈ S) = (l7b_unrecenter (k ω) ∈ S)
  rw [hω]

/-- The recentered field is a measurable function of the original field. -/
theorem l7b_recenterSigma_le_fullSigma {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (h : Ω → DistRd d) (r : ℝ) (z : Rd d) :
    fullSigmaRd (fun ω => l7b_recenter (h ω) r z) ≤ fullSigmaRd h := by
  exact ((l7b_measurable_recenter r z).comp (comap_measurable h)).comap_le

end HigherDimLQGMetric
