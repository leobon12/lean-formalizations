/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PsmPairP
import InteractingSLE.Spec.Supplement.GW2SsmMean

/-!
# GW2's open lines: the explicit stage mean is harmonic off the stage hull

Packet PROVE-GW2-STAGEMEAN, R121 round (deterministic):

* **`harmonicOnNhd_stgMeanR`**: `stgMeanR` is harmonic on the stage chart's inverse image of the complement of the
  stage hull at the clock (the proof of `GW2Ssm.harmonicOnNhd_stageMean` for the stage chart of `relChart`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.GW2Psm

open Exist.StagedLaw GW2Rd Supp8

/-- **The explicit stage mean is harmonic off the stage hull.** -/
theorem harmonicOnNhd_stgMeanR (κ : ℝ) (rec : RecData) {R : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R 0 = 0)
    (a₀ : ℝ≥0) {Q : ℝ} (hQ : 0 ≤ Q) {U u₀ : ℂ → ℝ} (hU : InnerProductSpace.HarmonicOnNhd U H)
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (σa : ℝ) :
    InnerProductSpace.HarmonicOnNhd (stgMeanR κ rec R a₀ Q U u₀ σa)
      ((stgChart (RelSafeS.relChart rec) R a₀).2.1 '' (H \ fwdHull (Ito.rpath (stgDrv R a₀)) Q)) := by
  set cs := stgChart (RelSafeS.relChart rec) R a₀ with hcsdef
  have hcsD := isDomainChart_stgChart_relChart rec hR hR0 a₀
  have hcs : cs.IsConformal := hcsD.isConformal
  have hlh : InnerProductSpace.HarmonicOnNhd cs.2.2 cs.dom := by
    have h := GW2Rd.harmonicOnNhd_lift_of_isDomainChart hcsD
    exact h
  rintro x ⟨z, hz, rfl⟩
  have hdom : cs.2.1 z ∈ cs.dom := hcs.inv_mem_dom hz.1
  have hSc : Continuous (Ito.rpath (stgDrv R a₀)) := (continuous_stgDrv hR a₀).comp continuous_real_toNNReal
  have hf := hcs.differentiableOn_fwd.analyticAt (cs.dom.isOpen.mem_nhds hdom)
  have hcm := Sec7.SideHeight.harmonicOnNhd_couplingMean (κ := κ) hSc hQ hU z hz
  rw [← hcs.2.2 z hz.1] at hcm
  have hm := QuantumZipper.FieldLawler.fl_harmonicAt_comp hf hcm
  have harg : InnerProductSpace.HarmonicAt (fun x => QuantumZipper.chiC κ * cs.2.2 x) (cs.2.1 z) := by
    have he : (QuantumZipper.chiC κ • cs.2.2) = (fun x => QuantumZipper.chiC κ * cs.2.2 x) := by
      funext x
      rfl
    simpa only [he] using (hlh _ hdom).const_smul (c := QuantumZipper.chiC κ)
  have hu := hu₀ _ (hcs.2.1 hz.1)
  exact ((hm.sub hu).sub (InnerProductSpace.harmonicAt_const σa)).sub harg

end InteractingSLE.Theorem14.GW2Psm
