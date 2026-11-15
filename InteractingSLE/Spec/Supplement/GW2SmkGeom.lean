/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SmkMarks

/-!
# GW2's stage mean, clause (G2): the dilation data from the geometry of the two charts

Packet PROVE-GW2-STAGEMEAN, marks round. `GW2Sdm.StageDilationOnAt` (the dilation data of a stage at time `t`) is
DERIVED here from per-sample geometric facts about the instance's stage chart `cs` and the kernel-route chart `ca`,
with the CANONICAL factor `λ = GW2Sdl.dilationFactor cs ca`, the kernel-route driver `Sn = R` and the kernel-route
harmonic function `Uca = GW2Smk.kernelBhe` of the stage typing with marks multiplied by `λ`:

* the chart dilation `ca.1 = λ · cs.1` from the same domain and the two tip normalizations
  (`GW2Sdl.eq_dilationFactor`);
* the driver clause on `[0, clock]` from the domain identities at every stage time (`GW2Sdm.driver_scale_of_domains`);
* `q = λ² · clock` from the domain identity at the clock (`GW2Sdm.mem_fwdHull_iff_of_chart_dilation`,
  `GW2Sdm.time_eq_of_mem_iff`);
* the word clause (`StageInst.word_clause_of_kernel`).

`StageGeomAt` (named input) lists the geometric facts; **`StageInst.stageDilationOnAt_of_geom`** derives the dilation
data. `GW2Spm.StagePhysLawAt` asks the mean to be harmonic off `B t` at EVERY sample, which `caMean` is only almost
surely; **`stagePhysLawAt_of_ae_harmonic`** patches the mean to `0` off the harmonicity event (`harmPatch`), so
harmonicity is needed only almost surely on `G`. **`StageInst.stagePhysLawAt_of_geom_ae`** combines: the physical law
from (G1) for `caMean` (with its almost-sure harmonicity), the stage shape and `StageGeomAt`.

Conditional helper with distinct names; it replaces no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology Complex
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H fwdHull zeroGFFTestCov)

universe u

namespace InteractingSLE.Theorem14.GW2Smk

open GW2KM2 Restart Restart.DomainMarkov Restart.FCDet Exist.StagedLaw Sec7.PocketTraversal Supp8.GB6
  Supp8.GB6.RelDrv Supp8.Q3Stop GW2Rd GW2Sde GW2TipSystem GW2TipSystem.RootC24 LocalSets WholeField GW2Spm GW2Sdl
  GW2Sdm

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}
  {l : List (EntryIdx c.Θ c.Q)}

/-- **Named input: the geometry of the stage chart and the kernel-route chart at time `t`** (almost surely on `G`):
`ca` is conformal; the kernel relative driver `R` is continuous from `0`; `ca` and the stage chart `cs` have the same
domain; `ca ∘ cs⁻¹` sends the explored tip to `0` and the counterflow tip to `∞`; the lifts agree on `ℍ ∖ B t`; at
every stage time `u ≤ clock` the two charts map the complements of their own Loewner hulls to the same set, at the
clock with the kernel-route time `q`. -/
def StageGeomAt (I : StageInst Ω) (c : SourceData Ω) (t : ℝ≥0) (G : Set Ω) (ca : Ω → Chart) (R : Ω → ℝ≥0 → ℝ)
    (q : Ω → ℝ≥0) : Prop :=
  ∀ᵐ ω ∂c.P, ω ∈ G → (ca ω).IsConformal ∧ Continuous (fun s : ℝ => R ω s.toNNReal) ∧ R ω 0 = 0 ∧
    ((I.chart c ω).dom : Set ℂ) = (ca ω).dom ∧
    Tendsto (fun z => (ca ω).1 ((I.chart c ω).2.1 z)) (𝓝[H] 0) (𝓝 0) ∧
    Tendsto (fun y : ℝ => ‖(ca ω).1 ((I.chart c ω).2.1 ((y : ℂ) * Complex.I))‖) atTop atTop ∧
    (∀ x ∈ H \ I.B t ω, (ca ω).2.2 x = (I.chart c ω).2.2 x) ∧
    (∀ u ∈ Icc (0 : ℝ) ((I.clock c t ω).toNNReal : ℝ), ∃ u' : ℝ, 0 ≤ u' ∧
      (I.chart c ω).2.1 '' (H \ fwdHull (fun s : ℝ => I.drv c s.toNNReal ω) u) =
        (ca ω).2.1 '' (H \ fwdHull (fun s : ℝ => R ω s.toNNReal) u')) ∧
    (I.chart c ω).2.1 '' (H \ fwdHull (fun s : ℝ => I.drv c s.toNNReal ω) ((I.clock c t ω).toNNReal : ℝ)) =
      (ca ω).2.1 '' (H \ fwdHull (fun s : ℝ => R ω s.toNNReal) (q ω : ℝ))

/-- The canonical dilation factor of the kernel-route chart against the stage chart. -/
abbrev kLam (I : StageInst Ω) (c : SourceData Ω) (ca : Ω → Chart) (ω : Ω) : ℝ :=
  dilationFactor (I.chart c ω) (ca ω)

/-- The kernel-route harmonic function of the stage typing with marks multiplied by the canonical factor. -/
abbrev kUca (I : StageInst Ω) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (w : WordType) (ca : Ω → Chart) (R : Ω → ℝ≥0 → ℝ) (q : Ω → ℝ≥0) (ω : Ω) : ℂ → ℝ :=
  kernelBhe c.κ w (R ω) (fun i => kLam I c ca ω * typedXL c.κ w (I.β (I.srec c r l ω)) i)
    (fun j => kLam I c ca ω * typedXR c.κ w (I.β (I.srec c r l ω)) j) (q ω)

/-- **The dilation data from the geometry of the two charts.** -/
theorem StageInst.stageDilationOnAt_of_geom (I : StageInst Ω)
    (hv : IsGB6RelVersion c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V)
    (hpre : Measurable (stgPreRec c.s I.W c.W c.ζ I.GT I.V I.T I.R)) (w : WordType) (t : ℝ≥0) {G : Set Ω}
    {ca : Ω → Chart} {R : Ω → ℝ≥0 → ℝ} {q : Ω → ℝ≥0}
    (hshape : ∀ᵐ ω ∂c.P, ω ∈ G → H \ I.B t ω = (I.chart c ω).2.1 ''
      (H \ fwdHull (fun s : ℝ => I.drv c s.toNNReal ω) ((I.clock c t ω).toNNReal : ℝ)))
    (hgeom : StageGeomAt I c t G ca R q) :
    StageDilationOnAt I c r l w t G ca (fun ω s => R ω s.toNNReal) (kLam I c ca) (kUca I c r l w ca R q) := by
  have hmc := isMeasChart_stgChart (measurable_gb6Rec_src c) hv.2.1 hv.2.2.1 hpre
  have hkey : ∀ᵐ ω ∂c.P, ω ∈ G → 0 < kLam I c ca ω ∧
      (∀ x ∈ (I.chart c ω).2.1 '' H, (ca ω).1 x = (kLam I c ca ω : ℂ) * (I.chart c ω).1 x) ∧
      Continuous (fun s : ℝ => R ω s.toNNReal) ∧
      (q ω : ℝ) = kLam I c ca ω ^ 2 * ((I.clock c t ω).toNNReal : ℝ) ∧
      EqOn (fun s : ℝ => I.drv c s.toNNReal ω) (fun s => R ω (kLam I c ca ω ^ 2 * s).toNNReal / kLam I c ca ω)
        (Icc 0 ((I.clock c t ω).toNNReal : ℝ)) := by
    filter_upwards [hgeom] with ω hg hωG
    obtain ⟨hca, hRc, hR0, hdom, h0, hinf, -, hD, hDq⟩ := hg hωG
    have hcs := hmc.1 ω
    obtain ⟨hlam, hdil⟩ := eq_dilationFactor hcs hca hdom h0 hinf
    have hfwd : ∀ x ∈ (I.chart c ω).2.1 '' H, (ca ω).1 x = (kLam I c ca ω : ℂ) * (I.chart c ω).1 x :=
      fun x hx => hdil x (by rw [hcs.coe_dom]; exact hx)
    have hSc : Continuous fun s : ℝ => I.drv c s.toNNReal ω :=
      (continuous_stgDrv (hv.2.1 ω) _).comp continuous_real_toNNReal
    have hS0 : (fun s : ℝ => I.drv c s.toNNReal ω) 0 = 0 := by
      simp only [Real.toNNReal_zero]
      exact stgDrv_zero (fun t => I.R t ω) _
    have hRn0 : (fun s : ℝ => R ω s.toNNReal) 0 = 0 := by
      simp only [Real.toNNReal_zero]
      exact hR0
    have hQ : (0 : ℝ) ≤ ((I.clock c t ω).toNNReal : ℝ) := NNReal.coe_nonneg _
    refine ⟨hlam, hfwd, hRc, ?_, driver_scale_of_domains hcs hca hlam hfwd hSc hS0 hRc hRn0 hQ hD⟩
    exact time_eq_of_mem_iff hSc hS0 hRc hRn0 hlam hQ (NNReal.coe_nonneg _)
      (mem_fwdHull_iff_of_chart_dilation hcs hca hlam hfwd hDq)
  have hword := StageInst.word_clause_of_kernel (r := r) (l := l) I hv w t (G := G) (lam := kLam I c ca) (R := R)
    (q := q) (by
      filter_upwards [hkey] with ω hk hωG
      obtain ⟨h1, -, h3, h4, h5⟩ := hk hωG
      exact ⟨h1, h3, h4, h5⟩)
  filter_upwards [hkey, hgeom, hshape, hword] with ω hk hg hsh hwd hωG
  obtain ⟨hlam, hfwd, -, -, hS⟩ := hk hωG
  obtain ⟨-, -, -, -, -, -, hlift, -, -⟩ := hg hωG
  refine ⟨hlam, fun x hx => ⟨hfwd x ?_, hlift x hx⟩, hS, hwd hωG⟩
  rw [hsh hωG] at hx
  exact image_mono sdiff_subset hx

/-! ### Harmonicity of the mean only almost surely -/

open Classical in
/-- The mean patched to `0` on the samples where it is not harmonic off `B`. -/
def harmPatch (B : Ω → Set ℂ) (M : Ω → ℂ → ℝ) (ω : Ω) : ℂ → ℝ :=
  if InnerProductSpace.HarmonicOnNhd (M ω) (H \ B ω) then M ω else 0

omit mΩ in
theorem harmonicOnNhd_harmPatch (B : Ω → Set ℂ) (M : Ω → ℂ → ℝ) (ω : Ω) :
    InnerProductSpace.HarmonicOnNhd (harmPatch B M ω) (H \ B ω) := by
  unfold harmPatch
  split_ifs with h
  · exact h
  · exact InnerProductSpace.harmonicOnNhd_const (0 : ℝ)

/-- **`GW2Spm.StagePhysLawAt` with the harmonicity of the mean only almost surely on `G`** (the mean is patched to `0`
off the harmonicity event, which changes neither (G1) nor (G2) on `G`). -/
theorem stagePhysLawAt_of_ae_harmonic (I : StageInst Ω) (w : WordType) (t : ℝ≥0) {G : Set Ω} {M : Ω → ℂ → ℝ}
    (hG : MeasurableSet[I.ℋ t] G)
    (hlive : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w I.β I.E (I.srec c r l) → I.clock c t ω < I.cap c ω → ω ∈ G)
    (hMh : ∀ᵐ ω ∂c.P, ω ∈ G → InnerProductSpace.HarmonicOnNhd (M ω) (H \ I.B t ω))
    (hlaw : ∀ (φ : TestOn upperHalfPlaneOpens) (ρ : ℝ), ∀ᵐ ω ∂c.P, ω ∈ G → tsupport φ ⊆ H \ I.B t ω →
      (c.P[fun ω' => Complex.exp (Complex.I * ((ρ * centredField c.h I.u₀ ω' φ : ℝ) : ℂ)) | I.ℋ t]) ω =
        Complex.exp (Complex.I * ((ρ * ∫ z, M ω z * φ z : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (ρ ^ 2 * zeroGFFTestCov (H \ I.B t ω) φ φ)) : ℝ) : ℂ))
    (hread : ∀ᵐ ω ∂c.P, ω ∈ G → ∀ z ∈ H \ fwdHull (fun s : ℝ => I.drv c s.toNNReal ω) ((I.clock c t ω).toNNReal : ℝ),
      M ω ((I.chart c ω).2.1 z) + I.u₀ ((I.chart c ω).2.1 z) + I.σa +
          I.kc * (I.chart c ω).2.2 ((I.chart c ω).2.1 z) =
        couplingMean c.κ (fun s : ℝ => I.drv c s.toNNReal ω) (I.clock c t ω).toNNReal
          (bheProc c.κ (typedRhoL w) (typedRhoR w) (I.drv c)
            (fun i t ω => geomLW canonDrv (fun y => typedXL c.κ w (I.β y.1)) i t
              (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω))
            (fun j t ω => geomRW canonDrv (fun y => typedXR c.κ w (I.β y.1)) j t
              (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω)) ω
            (I.clock c t ω).toNNReal) z) :
    StagePhysLawAt I c r l w t := by
  refine ⟨G, harmPatch (I.B t) M, hG, hlive, harmonicOnNhd_harmPatch _ _, fun φ ρ => ?_, ?_⟩
  · filter_upwards [hlaw φ ρ, hMh] with ω h hh hωG hsupp
    simp only [harmPatch, hh hωG, ↓reduceIte]
    exact h hωG hsupp
  · filter_upwards [hread, hMh] with ω h hh hωG z hz
    simp only [harmPatch, hh hωG, ↓reduceIte]
    exact h hωG z hz

/-- **The physical law of a stage at time `t` from (G1) and the geometry, harmonicity almost surely on `G`.** -/
theorem StageInst.stagePhysLawAt_of_geom_ae (I : StageInst Ω)
    (hv : IsGB6RelVersion c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V)
    (hpre : Measurable (stgPreRec c.s I.W c.W c.ζ I.GT I.V I.T I.R)) (w : WordType) (t : ℝ≥0) {G : Set Ω}
    (hG : MeasurableSet[I.ℋ t] G)
    (hlive : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w I.β I.E (I.srec c r l) → I.clock c t ω < I.cap c ω → ω ∈ G)
    {ca : Ω → Chart} {R : Ω → ℝ≥0 → ℝ} {q : Ω → ℝ≥0}
    (hMh : ∀ᵐ ω ∂c.P, ω ∈ G → InnerProductSpace.HarmonicOnNhd
      (caMean I c ca (fun ω s => R ω s.toNNReal) (kLam I c ca) (kUca I c r l w ca R q) t ω) (H \ I.B t ω))
    (hlaw : ∀ (φ : TestOn upperHalfPlaneOpens) (ρ : ℝ), ∀ᵐ ω ∂c.P, ω ∈ G → tsupport φ ⊆ H \ I.B t ω →
      (c.P[fun ω' => Complex.exp (Complex.I * ((ρ * centredField c.h I.u₀ ω' φ : ℝ) : ℂ)) | I.ℋ t]) ω =
        Complex.exp (Complex.I * ((ρ * ∫ z, caMean I c ca (fun ω s => R ω s.toNNReal) (kLam I c ca)
          (kUca I c r l w ca R q) t ω z * φ z : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (ρ ^ 2 * zeroGFFTestCov (H \ I.B t ω) φ φ)) : ℝ) : ℂ))
    (hshape : ∀ᵐ ω ∂c.P, ω ∈ G → H \ I.B t ω = (I.chart c ω).2.1 ''
      (H \ fwdHull (fun s : ℝ => I.drv c s.toNNReal ω) ((I.clock c t ω).toNNReal : ℝ)))
    (hgeom : StageGeomAt I c t G ca R q) :
    StagePhysLawAt I c r l w t := by
  have hdil := StageInst.stageDilationOnAt_of_geom (r := r) (l := l) I hv hpre w t hshape hgeom
  have hmc := isMeasChart_stgChart (measurable_gb6Rec_src c) hv.2.1 hv.2.2.1 hpre
  refine stagePhysLawAt_of_ae_harmonic I w t hG hlive hMh hlaw ?_
  filter_upwards [hshape, hdil] with ω hsh hd hωG
  obtain ⟨hlam, hch, hS, hU⟩ := hd hωG
  have hSc : Continuous fun s : ℝ => I.drv c s.toNNReal ω :=
    (continuous_stgDrv (hv.2.1 ω) _).comp continuous_real_toNNReal
  intro z hz
  exact read_of_dilation_eqOn (κ := c.κ) (σa := I.σa) (kc := I.kc) (u₀ := I.u₀) (hmc.1 ω) hlam
    (NNReal.coe_nonneg _) (D := H \ I.B t ω)
    (fun z hz => by rw [hsh hωG]; exact mem_image_of_mem _ hz)
    (fun x hx => (hch x hx).1) (fun x hx => (hch x hx).2) hS hSc hU z hz

end InteractingSLE.Theorem14.GW2Smk
