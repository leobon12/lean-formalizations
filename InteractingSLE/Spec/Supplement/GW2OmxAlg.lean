/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OmxDrv
import InteractingSLE.Spec.Supplement.GW2SdlScale
import InteractingSLE.Spec.Exist.StagedLaw3Kern

/-!
# GW2's open lines: the kernel's harmonic form at stage time `t` is the stage mean's form

Packet PROVE-GW2-STAGEMEAN, R120 round (per-sample algebra). At one physical point `y` off the union: with the
stage-start dilation `relMap (Uk, t₀) (cL.1 y) = λ · cs.1 y`, the driver relation `S = Rk(λ²·)/λ` on `[0, Q]`, the
flowed harmonic extensions related by `G(λ v) = U v + cst`, and the stage-start constant
`χ(Im relLog (cL.1 y) + cL.lift y − cs.lift y) + θχ − σa = cst`, the kernel union's harmonic form at `t` (through the
launch chart, with `uθ − u' = θχ`) is the canonical stage-chart coupling mean:

* **`kernel_form_eq_stage_form`**: `wP y + u₀ y + σa + χ · cs.lift y = couplingMean κ S Q U (cs.1 y)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd chiC)

namespace InteractingSLE.Theorem14.GW2Omx

open Supp8.GB6 (relMap)
open Supp8.Q3Rel (relLog)

/-- **The kernel's harmonic form at `t` is the stage mean's form** (one point, deterministic). -/
theorem kernel_form_eq_stage_form {κ σa θχ : ℝ} {cL cs : Chart} {Uk : ℝ → ℝ} {t₀ : ℝ} {lam : ℝ} (hlam : 0 < lam)
    {S Rk : ℝ → ℝ} {Q : ℝ} (hQ : 0 ≤ Q) (hdrv : EqOn S (fun s => Rk (lam ^ 2 * s) / lam) (Icc 0 Q))
    {G U : ℂ → ℝ} {cst : ℝ} {wP u₀ u' uθ : ℂ → ℝ} {y : ℂ}
    (hGU : G ((lam : ℂ) * fwdMap (fun s => Rk (lam ^ 2 * s) / lam) Q (cs.1 y)) =
      U (fwdMap (fun s => Rk (lam ^ 2 * s) / lam) Q (cs.1 y)) + cst)
    (hdil : relMap Uk t₀ (cL.1 y) = (lam : ℂ) * cs.1 y)
    (hE : chiC κ * ((relLog Uk t₀ (cL.1 y)).im + cL.2.2 y - cs.2.2 y) + θχ - σa = cst)
    (hθ : uθ (cL.1 y) - u' (cL.1 y) = θχ) (hinv : cL.2.1 (cL.1 y) = y)
    (hK : wP (cL.2.1 (cL.1 y)) + u₀ (cL.2.1 (cL.1 y)) + chiC κ * cL.2.2 (cL.2.1 (cL.1 y)) - u' (cL.1 y) +
        uθ (cL.1 y) =
      G (fwdMap Rk (lam ^ 2 * Q) (relMap Uk t₀ (cL.1 y))) -
        chiC κ * ((logDerivFwd Rk (lam ^ 2 * Q) (relMap Uk t₀ (cL.1 y))).im + (relLog Uk t₀ (cL.1 y)).im)) :
    wP y + u₀ y + σa + chiC κ * cs.2.2 y = couplingMean κ S Q U (cs.1 y) := by
  set S' : ℝ → ℝ := fun s => Rk (lam ^ 2 * s) / lam with hS'
  set w := cs.1 y with hw
  have hne : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  have hf : fwdMap Rk (lam ^ 2 * Q) ((lam : ℂ) * w) = (lam : ℂ) * fwdMap S' Q w := by
    rw [QuantumZipper.B3d.fwdMap_scale_of Rk hlam hQ w]
    field_simp
  have hL : logDerivFwd Rk (lam ^ 2 * Q) ((lam : ℂ) * w) = logDerivFwd S' Q w :=
    (GW2Sdl.logDerivFwd_scale_of Rk hlam hQ w).symm
  rw [hinv, hdil, hf, hL, hGU] at hK
  have hcm : couplingMean κ S Q U w = couplingMean κ S' Q U w := Exist.StagedLaw.couplingMean_congr hQ hdrv κ U w
  rw [hcm]
  unfold couplingMean
  linarith

end InteractingSLE.Theorem14.GW2Omx
