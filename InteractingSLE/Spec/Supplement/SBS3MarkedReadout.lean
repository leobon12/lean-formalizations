/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3MarkedMean
import InteractingSLE.Spec.Supplement.SBS3AssemblyWord

/-!
# S3: the identified marked mean supplies the exact comparison readout
-/

set_option autoImplicit false

noncomputable section

open Filter Set Topology
open QuantumZipper (H chiC)

namespace InteractingSLE.Theorem14.SB.S3

open Restart

/-- Turn the physical marked-mean identity into the readout used by S3's
comparison. The complex log must have the inherited chart lift on the approach. -/
theorem isChartWordMean_of_corrected_eqOn {κ : ℝ} {word : BoundaryWord}
    (hs : word.IsSorted) {c : Chart} {v u₀ : ℂ → ℝ} {L : ℂ → ℂ}
    (hmean : EqOn (fun z => v z + u₀ z + chiC κ * c.2.2 z)
      (fun z => word.mean (c.1 z)) c.dom)
    (hlog : EqOn (fun z => (L z).im) c.2.2 c.dom)
    {F : Filter ℂ} (hF : F ≤ 𝓟 (c.dom : Set ℂ)) {x : ℝ}
    (hx : x ∉ word.jumps) (hq : Tendsto c.1 F (𝓝[H] (x : ℂ))) :
    IsChartWordMean κ word x F v u₀ L := by
  refine ⟨hs, hx, c.1, hq, ?_⟩
  filter_upwards [le_principal_iff.1 hF] with z hz
  have he : (L z).im = c.2.2 z := hlog hz
  rw [he]
  exact hmean hz

/-- The marked-mean identification yields the unmarked physical side limit
with its precise background and argument correction. -/
theorem tendsto_corrected_mean_of_eqOn {κ : ℝ} {word : BoundaryWord}
    (hs : word.IsSorted) {c : Chart} {v u₀ : ℂ → ℝ} {L : ℂ → ℂ}
    (hmean : EqOn (fun z => v z + u₀ z + chiC κ * c.2.2 z)
      (fun z => word.mean (c.1 z)) c.dom)
    (hlog : EqOn (fun z => (L z).im) c.2.2 c.dom)
    {F : Filter ℂ} (hF : F ≤ 𝓟 (c.dom : Set ℂ)) {x : ℝ}
    (hx : x ∉ word.jumps) (hq : Tendsto c.1 F (𝓝[H] (x : ℂ))) :
    Tendsto (fun z => v z + u₀ z + chiC κ * (L z).im) F (𝓝 (word.fn x)) :=
  (isChartWordMean_of_corrected_eqOn hs hmean hlog hF hx hq).tendsto

end InteractingSLE.Theorem14.SB.S3
