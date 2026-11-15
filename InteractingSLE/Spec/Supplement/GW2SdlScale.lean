/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SpmPhys

/-!
# GW2's stage mean, clause (G2): the stage-chart reading from the dilation of the kernel-route chart

Packet PROVE-GW2-STAGEMEAN, dilation round. Clause (G2) of `GW2Spm.StagePhysLawAt` reads the physical mean `M` in the
instance's stage chart `cs`. On the conditional-kernel route `M` is DEFINED by the chart `ca` in which the route
computes it (the launch chart followed by the relative chart of the conditional counterflow): `M_ca x =
couplingMean κ R_n q' U_ca (ca.1 x) − u₀ x − σa − kc · ca.lift x`. The two charts differ by a positive dilation `λ`
(`GW2Spm.exists_realMobius_of_same_dom`), so (G2) for `M_ca` is Brownian scaling:

* **`logDerivFwd_scale_of`**, **`couplingMean_scale`**: Brownian scaling of the logarithmic derivative and of the
  coupling mean, `couplingMean κ (W(λ² ·)/λ) t (U(λ ·)) z = couplingMean κ W (λ² t) U (λ z)` (no hypothesis on `W`);
* `realMobius_eq_dilation`: a real Möbius map with `b = e = 0` is the dilation by `a / f`;
* **`read_of_dilation`** (per sample): if `ca.1 = λ · cs.1` and `ca.lift = cs.lift` on the physical domain, the stage
  driver is the Brownian rescaling of the kernel-route driver and the kernel-route harmonic extension rescaled is the
  stage one, then `M_ca` read in `cs` is the stage coupling mean;
* **`StageDilationAt`** (named input: the dilation data, a.s. on `G`) and **`stagePhysLawAt_of_dilation`**:
  `StagePhysLawAt` from (G1) for `M_ca` (what the kernel route delivers) and the dilation data.

Deterministic except for the packaging. Conditional helper with distinct names; it replaces no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H fwdHull fwdMap fwdMapInv logDerivFwd chiC zeroGFFTestCov)

universe u

namespace InteractingSLE.Theorem14.GW2Sdl

open GW2KM2 Restart Restart.DomainMarkov Restart.FCDet Exist.StagedLaw Sec7.PocketTraversal Supp8.GB6
  Supp8.GB6.RelDrv Supp8.Q3Stop Supp8.GB6.HullId Supp8.RelSafe GW2Rd GW2Sde GW2TipSystem GW2TipSystem.RootC24
  LocalSets WholeField Supp8.RelSafeS GW2Stl GW2Scl GW2Spm

/-! ### Brownian scaling -/

/-- **Brownian scaling of the logarithmic derivative of the Loewner map.** -/
theorem logDerivFwd_scale_of (W : ℝ → ℝ) {a : ℝ} (ha : 0 < a) {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    logDerivFwd (fun s => W (a ^ 2 * s) / a) t z = logDerivFwd W (a ^ 2 * t) (a * z) := by
  have ha2 : (a ^ 2 : ℝ) ≠ 0 := by positivity
  unfold logDerivFwd
  congr 1
  have hc : ∀ s ∈ uIcc (0 : ℝ) t, 2 / (fwdMap (fun s => W (a ^ 2 * s) / a) s z) ^ 2 =
      (a ^ 2 : ℝ) • (2 / (fwdMap W (a ^ 2 * s) (a * z)) ^ 2) := by
    intro s hs
    rw [uIcc_of_le ht] at hs
    rw [QuantumZipper.B3d.fwdMap_scale_of W ha hs.1 z, div_pow, div_div_eq_mul_div, Complex.real_smul]
    push_cast
    ring
  rw [intervalIntegral.integral_congr hc, intervalIntegral.integral_smul,
    intervalIntegral.integral_comp_mul_left (fun s => 2 / (fwdMap W s (a * z)) ^ 2) ha2, smul_smul,
    mul_inv_cancel₀ ha2, one_smul, mul_zero]

/-- **Brownian scaling of the coupling mean**: `𝔥^{W(λ²·)/λ}_t(z)` with the harmonic function `U(λ ·)` is
`𝔥^W_{λ² t}(λ z)` with `U`. -/
theorem couplingMean_scale (κ : ℝ) (W : ℝ → ℝ) {a : ℝ} (ha : 0 < a) {t : ℝ} (ht : 0 ≤ t) (U : ℂ → ℝ) (z : ℂ) :
    couplingMean κ (fun s => W (a ^ 2 * s) / a) t (fun w => U (a * w)) z =
      couplingMean κ W (a ^ 2 * t) U (a * z) := by
  unfold couplingMean
  have hne : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [logDerivFwd_scale_of W ha ht z, QuantumZipper.B3d.fwdMap_scale_of W ha ht z]
  simp only [mul_div_cancel₀ _ hne]

/-- A real Möbius map with `b = e = 0` is a dilation. -/
theorem realMobius_eq_dilation {a f : ℝ} (hf : f ≠ 0) (w : ℂ) :
    QuantumZipper.CA.realMobius a 0 0 f w = ((a / f : ℝ) : ℂ) * w := by
  unfold QuantumZipper.CA.realMobius
  have hf' : (f : ℂ) ≠ 0 := by exact_mod_cast hf
  simp only [Complex.ofReal_zero, zero_mul, add_zero, zero_add, Complex.ofReal_div]
  field_simp

/-! ### The reading in the stage chart -/

/-- **The kernel-route mean read in the stage chart, per sample.** -/
theorem read_of_dilation {κ σa kc : ℝ} {cs ca : Chart} (hcs : cs.IsConformal) {D : Set ℂ} {S Sn : ℝ → ℝ}
    {q lam : ℝ} (hlam : 0 < lam) (hq : 0 ≤ q) {U Uca u₀ : ℂ → ℝ}
    (hD : ∀ z ∈ H \ fwdHull S q, cs.2.1 z ∈ D)
    (hfwd : ∀ x ∈ D, ca.1 x = (lam : ℂ) * cs.1 x) (hlift : ∀ x ∈ D, ca.2.2 x = cs.2.2 x)
    (hS : S = fun s => Sn (lam ^ 2 * s) / lam) (hSc : Continuous S) (hU : EqOn (fun w => Uca (lam * w)) U H) :
    ∀ z ∈ H \ fwdHull S q,
      (couplingMean κ Sn (lam ^ 2 * q) Uca (ca.1 (cs.2.1 z)) - u₀ (cs.2.1 z) - σa - kc * ca.2.2 (cs.2.1 z)) +
          u₀ (cs.2.1 z) + σa + kc * cs.2.2 (cs.2.1 z) = couplingMean κ S q U z := by
  intro z hz
  have hx := hD z hz
  rw [hfwd _ hx, hlift _ hx, hcs.2.2 z hz.1]
  have hfH : fwdMap S q z ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hSc hq hz
  have e1 : couplingMean κ Sn (lam ^ 2 * q) Uca ((lam : ℂ) * z) = couplingMean κ S q U z := by
    rw [← couplingMean_scale κ Sn hlam hq Uca z, ← hS]
    unfold couplingMean
    rw [hU hfH]
  rw [e1]
  ring

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}
  {l : List (EntryIdx c.Θ c.Q)}

/-- The physical mean computed in the kernel-route chart `ca` (definition of `M_ca`). -/
def caMean (I : StageInst Ω) (c : SourceData Ω) (ca : Ω → Chart) (Sn : Ω → ℝ → ℝ) (lam : Ω → ℝ) (Uca : Ω → ℂ → ℝ)
    (t : ℝ≥0) (ω : Ω) (x : ℂ) : ℝ :=
  couplingMean c.κ (Sn ω) (lam ω ^ 2 * ((I.clock c t ω).toNNReal : ℝ)) (Uca ω) ((ca ω).1 x) - I.u₀ x - I.σa -
    I.kc * (ca ω).2.2 x

/-- **Named input: the dilation data of a stage at time `t`** (almost surely on `G`): the kernel-route chart `ca` is
the instance's stage chart dilated by `λ > 0` on `ℍ ∖ B t` (same lift), the stage driver is the Brownian rescaling of
the kernel-route driver `Sn` by `λ`, and the kernel-route harmonic extension rescaled by `λ` is the canonical bounded
harmonic extension of the typed stage word flowed to the stage clock. -/
def StageDilationAt (I : StageInst Ω) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (w : WordType) (t : ℝ≥0) (G : Set Ω) (ca : Ω → Chart) (Sn : Ω → ℝ → ℝ) (lam : Ω → ℝ) (Uca : Ω → ℂ → ℝ) :
    Prop :=
  ∀ᵐ ω ∂c.P, ω ∈ G → 0 < lam ω ∧
    (∀ x ∈ H \ I.B t ω, (ca ω).1 x = (lam ω : ℂ) * (I.chart c ω).1 x ∧ (ca ω).2.2 x = (I.chart c ω).2.2 x) ∧
    (fun s : ℝ => I.drv c s.toNNReal ω) = (fun s => Sn ω (lam ω ^ 2 * s) / lam ω) ∧
    EqOn (fun w => Uca ω (lam ω * w))
      (bheProc c.κ (typedRhoL w) (typedRhoR w) (I.drv c)
        (fun i t ω => geomLW canonDrv (fun y => typedXL c.κ w (I.β y.1)) i t
          (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω))
        (fun j t ω => geomRW canonDrv (fun y => typedXR c.κ w (I.β y.1)) j t
          (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω)) ω
        (I.clock c t ω).toNNReal) H

/-- **`StagePhysLawAt` from the kernel route**: (G1) for the kernel-route mean `M_ca` (harmonic on `ℍ ∖ B t`), the
stage shape on `G` and the dilation data give the physical stage law at time `t` (its clause (G2) is
`read_of_dilation`). -/
theorem stagePhysLawAt_of_dilation (I : StageInst Ω) (hv : IsGB6RelVersion c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V)
    (hpre : Measurable (stgPreRec c.s I.W c.W c.ζ I.GT I.V I.T I.R)) (w : WordType) (t : ℝ≥0)
    {G : Set Ω} (hG : MeasurableSet[I.ℋ t] G)
    (hlive : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w I.β I.E (I.srec c r l) → I.clock c t ω < I.cap c ω → ω ∈ G)
    {ca : Ω → Chart} {Sn : Ω → ℝ → ℝ} {lam : Ω → ℝ} {Uca : Ω → ℂ → ℝ}
    (hMh : ∀ ω, InnerProductSpace.HarmonicOnNhd (caMean I c ca Sn lam Uca t ω) (H \ I.B t ω))
    (hlaw : ∀ (φ : TestOn upperHalfPlaneOpens) (ρ : ℝ), ∀ᵐ ω ∂c.P, ω ∈ G → tsupport φ ⊆ H \ I.B t ω →
      (c.P[fun ω' => Complex.exp (Complex.I * ((ρ * centredField c.h I.u₀ ω' φ : ℝ) : ℂ)) | I.ℋ t]) ω =
        Complex.exp (Complex.I * ((ρ * ∫ z, caMean I c ca Sn lam Uca t ω z * φ z : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (ρ ^ 2 * zeroGFFTestCov (H \ I.B t ω) φ φ)) : ℝ) : ℂ))
    (hshape : ∀ᵐ ω ∂c.P, ω ∈ G → H \ I.B t ω = (I.chart c ω).2.1 ''
      (H \ fwdHull (fun s : ℝ => I.drv c s.toNNReal ω) ((I.clock c t ω).toNNReal : ℝ)))
    (hdil : StageDilationAt I c r l w t G ca Sn lam Uca) :
    StagePhysLawAt I c r l w t := by
  have hmc := isMeasChart_stgChart (measurable_gb6Rec_src c) hv.2.1 hv.2.2.1 hpre
  refine ⟨G, caMean I c ca Sn lam Uca t, hG, hlive, hMh, hlaw, ?_⟩
  filter_upwards [hshape, hdil] with ω hsh hd hωG
  obtain ⟨hlam, hch, hS, hU⟩ := hd hωG
  have hSc : Continuous fun s : ℝ => I.drv c s.toNNReal ω :=
    (continuous_stgDrv (hv.2.1 ω) _).comp continuous_real_toNNReal
  intro z hz
  have h := read_of_dilation (κ := c.κ) (σa := I.σa) (kc := I.kc) (u₀ := I.u₀) (hmc.1 ω) hlam
    (NNReal.coe_nonneg _) (D := H \ I.B t ω)
    (fun z hz => by rw [hsh hωG]; exact mem_image_of_mem _ hz)
    (fun x hx => (hch x hx).1) (fun x hx => (hch x hx).2) hS hSc hU z hz
  exact h

end InteractingSLE.Theorem14.GW2Sdl
