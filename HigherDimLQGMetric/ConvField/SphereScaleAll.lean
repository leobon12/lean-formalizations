import HigherDimLQGMetric.ConvField.WholeSpaceRadial
import HigherDimLQGMetric.Sphere.Scaling

/-! A simultaneous version of sphere-average scaling at a fixed dilation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

set_option maxHeartbeats 1000000 in
theorem l2b_ae_sphereAvg_scale_all (d : ℕ) (hd : 2 ≤ d)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → ∀ z : Rd d,
      sphereAvg (affineComp ρ 0 (h ω)) r z =
        sphereAvg (h ω) (ρ * r) (ρ • z) := by
  let Q : Set (ℝ × Rd d) := Ioi 0 ×ˢ univ
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense Q
  let _ : Countable S := hSc.to_subtype
  have hfix : ∀ᵐ ω ∂P, ∀ p : S,
      sphereAvg (affineComp ρ 0 (h ω)) p.1.1.1 p.1.1.2 =
        sphereAvg (h ω) (ρ * p.1.1.1) (ρ • p.1.1.2) := by
    apply ae_all_iff.mpr
    intro p
    have hp : 0 < p.1.1.1 := p.1.2.1
    filter_upwards [hh.ae_sphereAvg_affineComp hd hρ 0 hp p.1.1.2] with ω hω
    simpa using hω
  have hh' : IsWholeSpaceLGF (fun ω => affineComp ρ 0 (h ω)) P := hh.affineComp hρ 0
  filter_upwards [hfix, hh.ae_continuousOn_sphereAvg hd,
    hh'.ae_continuousOn_sphereAvg hd] with ω hfix hcont hcont'
  let map : Q → Q := fun q =>
    ⟨(ρ * q.1.1, ρ • q.1.2), ⟨mul_pos hρ q.2.1, trivial⟩⟩
  have hmap : Continuous map := by
    apply Continuous.subtype_mk
    exact (continuous_const.mul (continuous_fst.comp continuous_subtype_val)).prodMk
      ((continuous_const : Continuous fun _ : Q => ρ).smul
        (continuous_snd.comp continuous_subtype_val))
  have hleft : Continuous (fun q : Q =>
      sphereAvg (affineComp ρ 0 (h ω)) q.1.1 q.1.2) := hcont'.2.domRestrict
  have hright : Continuous (fun q : Q =>
      sphereAvg (h ω) (ρ * q.1.1) (ρ • q.1.2)) := by
    change Continuous ((fun q : Q => sphereAvg (h ω) q.1.1 q.1.2) ∘ map)
    exact hcont.2.domRestrict.comp hmap
  have heq : (fun q : Q => sphereAvg (affineComp ρ 0 (h ω)) q.1.1 q.1.2) =
      (fun q : Q => sphereAvg (h ω) (ρ * q.1.1) (ρ • q.1.2)) :=
    Continuous.ext_on hSd hleft hright (fun p hp => hfix ⟨p, hp⟩)
  intro r hr z
  exact congrFun heq ⟨(r, z), ⟨hr, trivial⟩⟩

end HigherDimLQGMetric
