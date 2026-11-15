/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12DawnFibres

/-!
# (K-b) for the canonical candidate mean: (PC1) holds deterministically

Packet PROVE-AUX61-FIBK. Specification Aux. lemma 61 (`source/spec/p241-288.md` L427–L470, pp. 261–262) and Astra's
follow-up 4 §1.2 (`source/external/AstraIG1/ig1_followup4_audited.txt` L150–L176, ruling R71).

The GlueK interface (`Aux61GlueK.hint_of_chartKernel`, wired in `Wire.Dawn.FibrePC1`) asks for a chart mean `M`
satisfying (PC1) relative to the canonical reference extension. The explicit (PC1) mean read through ONE cutoff,
`meanF κ u q F₀ w t`, does not depend on the cutoff off the hull (`Aux61Act.integral_meanF_congr_cut`), so it satisfies
(PC1) for EVERY cutoff. Hence:

* **`isPC1_canonMean`**: at a code with the path facts and a time before its lifetime, the canonical candidate
  `canonMean d F₀ s t = meanF d.κ (canonExt d s t) d.q F₀ (rpath (fibW · s)) t` satisfies `IsPC1` for the data's `q`
  and window `O₀`, whenever `F₀` is a cutoff of `q` on a neighbourhood of the data's buffer;
* **`canonKernelData`**, **`fibrePC1_canon`**: on any cover satisfying `Night.FibreGeometry`, the kernel data whose
  candidate means are the canonical ones satisfy `Dawn.FibrePC1` (no probability is involved);
* **`integral_eq_canonMean_of_isPC1`**: conversely every (PC1) mean pairs like the canonical one, so a chart law with
  a (PC1) mean is the chart law with the canonical mean (`fibreChart_canon_of_pc1`).

So the two leaves `FibreChart` + `FibrePC1` are equivalent to the single leaf `FibreChart` for the canonical means:
the whole content of Aux. lemma 61 (the identification of the ACTUAL conditional mean) sits in that chart law.

Conditional helpers with distinct names; they replace no source theorem. R48/R77: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement`, any `*_of_param` result, or Astra's post-contact kernel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61UnionK

open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open LocalExt (cfVal)
open Restart.FlowStopIdentCMI (CMCut)
open Restart.DomainMarkov (RatIdx dyT)
open Aux61Win (meanF IsCutoffOn IsPC1)
open Aux61Fib (FibCode FibData PathGood fibW fibΓ fibU fibField)
open Aux61FibK (canonExt refExt_canonExt ratAvoid ratψ)

universe u

/-! ### The canonical candidate mean at one code -/

/-- **The canonical (PC1) candidate mean** of a code `s` at fibre time `t`, read through the cutoff `F₀` of the data's
correction: `M⁰_t + G_{ℍ∖K_t}(1_ℍ gD F₀.f) + (q − F₀.f)` (`Aux61Win.meanF`), with the canonical reference
extension `canonExt d s t` of the data's word. -/
def canonMean (d : FibData) (F₀ : CMCut) (s : ULift.{u} FibCode) (t : ℝ≥0) : ℂ → ℝ :=
  meanF d.κ (canonExt d s t) d.q F₀ (Ito.rpath (fibW · s)) t

/-- The canonical reference extension is the bounded harmonic extension of the data's word at the geometric images
of the marks under the decoded driver (the `geomL`/`geomR` form of `refExt_canonExt`). -/
theorem bhe_canonExt (d : FibData) (s : ULift.{u} FibCode) (t : ℝ≥0) :
    IsBoundedHarmonicExtension
      (forceBoundaryData d.κ (flowLineRhoL d.κ d.bR d.JR 0 0) (flowLineRhoR d.κ d.bR d.JR 0 0)
        (fun i => Restart.FlowStopIdentCMI.geomL (Ito.rpath (fibW · s)) t (flowLineXL d.bR d.JR 0 i))
        (fun j => Restart.FlowStopIdentCMI.geomR (Ito.rpath (fibW · s)) t (flowLineXR d.bR d.JR 0 j)))
      (forceJumpSet (fun i => Restart.FlowStopIdentCMI.geomL (Ito.rpath (fibW · s)) t (flowLineXL d.bR d.JR 0 i))
        (fun j => Restart.FlowStopIdentCMI.geomR (Ito.rpath (fibW · s)) t (flowLineXR d.bR d.JR 0 j)))
      (canonExt d s t) := by
  have e1 : (fun i => Restart.FlowStopIdentCMI.geomL (Ito.rpath (fibW · s)) t (flowLineXL d.bR d.JR 0 i)) =
      fun i => Sec7.PocketTraversal.geomLW fibW (fun _ => flowLineXL d.bR d.JR 0) i t s - fibW t s :=
    funext fun i => Restart.FlowStopIdentCMI.geomL_rpath_eq_geomLW_sub fibW _ i t s
  have e2 : (fun j => Restart.FlowStopIdentCMI.geomR (Ito.rpath (fibW · s)) t (flowLineXR d.bR d.JR 0 j)) =
      fun j => Sec7.PocketTraversal.geomRW fibW (fun _ => flowLineXR d.bR d.JR 0) j t s - fibW t s :=
    funext fun j => Restart.FlowStopIdentCMI.geomR_rpath_eq_geomRW_sub fibW _ j t s
  rw [e1, e2]
  exact refExt_canonExt d s t

/-- **(PC1) for the canonical candidate** (Aux. lemma 61 in cutoff form, for the explicit mean): at a code with the
path facts, before its lifetime, the canonical candidate read through a cutoff `F₀` of `q` on a neighbourhood `N₀` of
the buffer satisfies (PC1) for every cutoff — the explicit mean does not depend on the cutoff off the hull. -/
theorem isPC1_canonMean {d : FibData} {F₀ : CMCut} {N₀ : Set ℂ} (hF₀ : IsCutoffOn F₀ d.q N₀ d.O₀)
    (hbN : d.buffer ⊆ N₀) {s : ULift.{u} FibCode} (hgood : PathGood d s.down) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < fibU s) :
    IsPC1 d.κ (canonExt d s t) (Ito.rpath (fibW · s)) t d.q d.O₀ (canonMean d F₀ s t) := by
  intro F N hF h0 hKN φ hφ
  have hKb := Aux61GlueK.closure_fwdHull_subset_buffer hgood ht
  have htr : IsGeneratingTrace (fibW · s) (fibU s) (fibΓ s) := hgood.1
  have hqc : ContinuousOn d.q H := d.q_harm.contDiffOn.continuousOn
  rw [canonMean, Aux61Act.integral_meanF_congr_cut d.κ_pos d.bR_pc (FibCode.continuous_driver s.down)
    (FibCode.driver_zero s.down) (fun _ => Aux61Act.exists_trace_real htr ht) (bhe_canonExt d s t) hqc hF₀ hF
    ⟨hbN d.zero_mem, h0⟩ (subset_inter (hKb.trans hbN) hKN) φ hφ]
  exact Aux61Win.integral_meanF_eq (bhe_canonExt d s t).1 hqc (FibCode.continuous_driver s.down)
    (hF.isGreenTest_src hKN) φ hφ

/-- **Every (PC1) mean pairs like the canonical candidate** off the hull, at a code with the path facts before its
lifetime. -/
theorem integral_eq_canonMean_of_isPC1 {d : FibData} {F₀ : CMCut} {N₀ : Set ℂ} (hF₀ : IsCutoffOn F₀ d.q N₀ d.O₀)
    (hbN : d.buffer ⊆ N₀) {s : ULift.{u} FibCode} (hgood : PathGood d s.down) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < fibU s) {M : ℂ → ℝ}
    (hPC : IsPC1 d.κ (canonExt d s t) (Ito.rpath (fibW · s)) t d.q d.O₀ M) (ψ : TestOn upperHalfPlaneOpens)
    (hψ : Disjoint (tsupport ψ) (fwdHull (Ito.rpath (fibW · s)) t)) :
    ∫ z, M z * ψ z = ∫ z, canonMean d F₀ s t z * ψ z := by
  have hKb := Aux61GlueK.closure_fwdHull_subset_buffer hgood ht
  exact Aux61GlueK.integral_eq_meanF_of_isPC1 (bhe_canonExt d s t).1 d.q_harm.contDiffOn.continuousOn
    (FibCode.continuous_driver s.down) hPC hF₀ (hbN d.zero_mem) (hKb.trans hbN) ψ hψ

/-! ### The canonical candidate means of a cover -/

section Cover

variable {X : Type u} [MeasurableSpace X]

/-- **The kernel data with the canonical candidate means**: the reference words and conditioning σ-algebras are
given; the candidate mean of index `i` at the dyadic fibre time `k/2ⁿ` is the canonical one of the code `Y i x`, read
through the cover's cutoff. -/
def canonKernelData (D : Wire.Night.FibreRecords X) (kappa : D.ι → ℝ) (boundary : D.ι → ℝ → ℝ)
    (jumps : D.ι → Finset ℝ) (sigma : D.ι → ℕ → ℕ → MeasurableSpace X) : Wire.Dawn.FibreKernelData D where
  kappa := kappa
  boundary := boundary
  jumps := jumps
  sigma := sigma
  mean := fun i n k x => canonMean (D.data i (D.Z i x)) (D.cutoff i (D.Z i x)) (ULift.up.{u} (D.Y i x)) (dyT n k)

/-- **`FibrePC1` for the canonical candidate means** on every cover with the path facts and the cutoff clause of
`Night.FibreGeometry` (deterministic). -/
theorem fibrePC1_canon {μ : Measure X} {E : X → Prop} (D : Wire.Night.FibreRecords X)
    (hg : Wire.Night.FibreGeometry μ E D) (kappa : D.ι → ℝ) (boundary : D.ι → ℝ → ℝ) (jumps : D.ι → Finset ℝ)
    (sigma : D.ι → ℕ → ℕ → MeasurableSpace X) :
    Wire.Dawn.FibrePC1 μ D (canonKernelData D kappa boundary jumps sigma) := by
  obtain ⟨-, -, -, -, -, -, -, hGgood, hYG, -, -, hcut⟩ := hg
  intro i n k
  filter_upwards [hYG i] with x hx hxB hlt
  exact isPC1_canonMean (hcut i _ hxB).1 (hcut i _ hxB).2 (hGgood i _ _ hxB (hx hxB)) hlt

/-- **A chart law with (PC1) means is the chart law with the canonical means**: if `K`'s means satisfy `FibrePC1`
and its chart law `FibreChart` holds, then so does the chart law of the canonical kernel data with the same words and
σ-algebras. -/
theorem fibreChart_canon_of_pc1 {μ : Measure X} {E : X → Prop} (D : Wire.Night.FibreRecords X)
    (hg : Wire.Night.FibreGeometry μ E D) (K : Wire.Dawn.FibreKernelData D) (hc : Wire.Dawn.FibreChart μ D K)
    (hp : Wire.Dawn.FibrePC1 μ D K) :
    Wire.Dawn.FibreChart μ D (canonKernelData D K.kappa K.boundary K.jumps K.sigma) := by
  obtain ⟨-, -, -, -, -, -, -, hGgood, hYG, -, -, hcut⟩ := hg
  intro i n k p
  filter_upwards [hc i n k p, hp i n k, hYG i] with x hx hpc hxG hxB hxA
  refine (hx hxB hxA).trans ?_
  have hlt : ((dyT n k : ℝ≥0) : ℝ≥0∞) < fibU (ULift.up.{u} (D.Y i x)) := hxA.1
  have hψ : Disjoint (tsupport (ratψ p))
      (fwdHull (Ito.rpath fun r => fibW r (ULift.up.{u} (D.Y i x))) (dyT n k : ℝ≥0)) := hxA.2
  congr 1
  exact integral_eq_canonMean_of_isPC1 (hcut i _ hxB).1 (hcut i _ hxB).2 (hGgood i _ _ hxB (hxG hxB)) hlt
    (hpc hxB hlt) (ratψ p) hψ

end Cover

end InteractingSLE.Sec5.Aux61UnionK
