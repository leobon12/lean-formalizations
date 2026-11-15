/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61FibKTilt
import InteractingSLE.Spec.Sec5.Aux61FibAssembly
import InteractingSLE.Spec.Sec7.PocketPhaseMeans

/-!
# The code fibres need the kernel only at deterministic dyadic times

Packet PROVE-AUX61-FIB2, on the code space `ULift FibCode` of PROVE-AUX61-FIB (`Aux61FibCode`, `Aux61FibAssembly`):

* **`FibKernelRaw d P`**: the kernel of a fibre law `P` at the deterministic dyadic times `q = k/2ⁿ`, on the pre-clock
  event `{q < life}` with the test off the hull, given the null-augmented σ-algebra of the decoded driver killed at the
  lifetime at time `q` (a σ-algebra on the codes that does not depend on the data `d`);
* `rawFibre`: a law with the path facts, `FibKernelRaw` and `FibMembers` is a `RawActFibre` (clock source `fibSource`,
  reference clock `dataClock`, `𝓜 q` the null-augmented raw σ-algebra of the decoded driver);
* **`fibKernel_of_raw`**: `FibKernelRaw` (with the path facts and `FibMembers`) gives PROVE-AUX61-FIB's `FibKernel` —
  the kernel at the stops `min(T_N, k/2ⁿ)` of the completed filtration;
* **`exists_dyActFibre_of_raw`**, **`hasDyActFibreCover_of_fibRaw`**: PROVE-AUX61-FIB's assembly with `FibKernelRaw` in
  place of `FibKernel`.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param` result; R77: no post-contact kernel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61FibK

open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open LocalExt (cfVal)
open Restart.FlowStopIdentCMI (CMCut)
open Aux61Win (meanF IsCutoffOn)
open Aux61R2 (RefExt)
open Aux61Fib (FibCode FibData PathGood FibKernel FibMembers fibW fibΓ fibU fibField fibSource dataClock
  isMeasurableKilledDriving_fib ae_goodTrace_of_pathGood)
open Sec7.PocketTraversal

universe u

/-- The raw filtration of the codes: the decoded driver killed at the lifetime. -/
abbrev codeFiltration : Filtration ℝ≥0 (inferInstance : MeasurableSpace (ULift.{u} FibCode)) :=
  killedDrivingFiltration isMeasurableKilledDriving_fib.{u}

/-- **The kernel of a fibre law at the deterministic dyadic times** (pieces (F2) and (F3) without stops): for every
cutoff `(F, N)` of `q` on `O₀` with `buffer ⊆ N`, at each dyadic time `q = k/2ⁿ`, for every reference extension `u`
at `q` and every test `ψ`, almost surely on `{q < life}` with `ψ` off the hull at `q`, the conditional characteristic
functional of the field given the null-augmented raw σ-algebra of the decoded driver at `q` is the `meanF` Gaussian
kernel. -/
def FibKernelRaw (d : FibData) (P : Measure (ULift.{u} FibCode)) : Prop :=
  ∀ (F : CMCut) (N : Set ℂ), IsCutoffOn F d.q N d.O₀ → d.buffer ⊆ N → ∀ n k : ℕ,
    ∀ u : ULift.{u} FibCode → ℂ → ℝ, (∀ ω, RefExt d.κ d.bR d.JR fibW (Restart.DomainMarkov.dyT n k) ω (u ω)) →
    ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
      ((Restart.DomainMarkov.dyT n k : ℝ≥0) : ℝ≥0∞) < fibU ω →
      Disjoint (tsupport ψ) (fwdHull (Ito.rpath (fibW · ω)) (Restart.DomainMarkov.dyT n k : ℝ≥0)) →
      P[fun ω' => Complex.exp (Complex.I * (fibField ω' ψ : ℂ)) |
          Ito.nullAugmented codeFiltration.{u} P (Restart.DomainMarkov.dyT n k)] ω =
        cfVal (∫ z, meanF d.κ (u ω) d.q F (Ito.rpath (fibW · ω)) (Restart.DomainMarkov.dyT n k : ℝ≥0) z * ψ z)
          (loewnerGreenEnergy (Ito.rpath (fibW · ω)) (Restart.DomainMarkov.dyT n k : ℝ≥0) ψ)

section Fibre

variable (d : FibData) (P : Measure (ULift.{u} FibCode)) [IsProbabilityMeasure P]
  (hgood : ∀ᵐ s ∂P, PathGood d s.down)

include hgood in
/-- The reference word's killed driver generates (up to null sets) no more than the decoded driver: its marks are
functions of the driver. -/
theorem nullAugmented_dataClock_le (t : ℝ≥0) :
    Ito.nullAugmented (killedDrivingFiltration (dataClock d P hgood).killed) P t ≤
      Ito.nullAugmented codeFiltration.{u} P t := by
  have hWa := Coupling.adaptedBefore_killedDriving_W isMeasurableKilledDriving_fib.{u}
  have hc : ∀ ω : ULift.{u} FibCode, ContinuousOn (fun s => fibW s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < fibU ω} :=
    fun ω => (Aux61Fib.FibCode.continuous_driver ω.down).continuousOn
  have hle : killedDrivingFiltration (dataClock d P hgood).killed ≤ codeFiltration.{u} :=
    Ito.killedDrivingFiltration_le hWa
      (fun i => Sec7.PocketPhaseMeans.adaptedBefore_geomLW hc hWa measurable_const i)
      (fun j => Sec7.PocketPhaseMeans.adaptedBefore_geomRW hc hWa measurable_const j) _
  rw [Ito.nullAugmented_apply, Ito.nullAugmented_apply]
  exact sup_le_sup_right (hle t) _

/-- **The code fibre with the kernel at the dyadic times** (a `RawActFibre`). -/
def rawFibre (hraw : FibKernelRaw d P) (hmem : FibMembers d P) : RawActFibre (ULift.{u} FibCode) where
  κ := d.κ
  κ_pos := d.κ_pos
  bR := d.bR
  JR := d.JR
  bR_pc := d.bR_pc
  CS := fibSource P (ae_goodTrace_of_pathGood d P hgood)
  y_zero := rfl
  V := d.V
  RC := dataClock d P hgood
  driving_eq := Aux61Fib.driving_eq_self (dataClock d P hgood) fun _ => rfl
  field := fibField
  measurable_field := Aux61Fib.FibCode.measurable_field.comp measurable_down
  q := d.q
  q_harm := d.q_harm
  O₀ := d.O₀
  O₀_open := d.O₀_open
  q_zero := d.q_zero
  buffer := d.buffer
  buffer_open := d.buffer_open
  zero_mem := d.zero_mem
  buffer_compact := d.buffer_compact
  buffer_real := d.buffer_real
  hull_buffer := Aux61Cov.ae_hull_buffer_of_exit rfl (dataClock d P hgood) d.V_sub
    (hgood.mono fun _ h => h.2.2.2.2.2) (hgood.mono fun _ h => h.2.2.2.2.1)
  𝓜 := fun t => Ito.nullAugmented codeFiltration.{u} P t
  𝓜_le := fun t => (Ito.nullAugmented codeFiltration.{u} P).le t
  raw_le := nullAugmented_dataClock_le d P hgood
  rawKernel := hraw
  members := hmem _
  injective := hgood.mono fun _ h => h.2.2.2.2.2

include hgood in
/-- **`FibKernelRaw` gives `FibKernel`** (the kernel at the stops `min(T_N, k/2ⁿ)` of the completed filtration), for a
law with the path facts and the member identities. -/
theorem fibKernel_of_raw (hraw : FibKernelRaw d P) (hmem : FibMembers d P) : FibKernel d P := by
  intro F N hF hbN n k N' hτ u hu ψ
  exact (rawFibre d P hgood hraw hmem).toDyActFibre.dyKernel F N hF hbN _ hτ ⟨n, k, N', rfl⟩ u hu ψ

include hgood in
/-- **A law on the codes with the path facts, the kernel at the dyadic times and the member identities is a
`DyActFibre`** with that law, the data's reference word, the decoded path and the lifetime as its clock. -/
theorem exists_dyActFibre_of_raw (hraw : FibKernelRaw d P) (hmem : FibMembers d P) :
    ∃ D : Aux61Act.DyActFibre (ULift.{u} FibCode), D.CS.P = P ∧ D.κ = d.κ ∧ D.bR = d.bR ∧ D.JR = d.JR ∧
      D.CS.Γ = fibΓ ∧ D.RC.e = fibU :=
  Aux61Fib.exists_dyActFibre d P hgood (fibKernel_of_raw d P hgood hraw hmem) hmem

end Fibre

/-! ### The member identities on the raw code events -/

/-- The field of a code fibre centred by the reference mean plus the correction (the field of `FibMembers`). -/
def centredFib (d : FibData) : ULift.{u} FibCode → DistOn upperHalfPlaneOpens :=
  WholeField.centredField fibField fun z =>
    MartChar.meanExt d.κ (flowLineRhoL d.κ d.bR d.JR 0 0) (flowLineRhoR d.κ d.bR d.JR 0 0) 0
      (flowLineXL d.bR d.JR 0) (flowLineXR d.bR d.JR 0) z + d.q z

/-- **The member identities on the raw events of the decoded driver** (piece (F4) without completion and without the
reference marks): for rational `r < s` and every finite family `F` of rational balls in `ℍ`, a measurable version `S`
of the safe event at `s` such that the law of the centred field integrated over `D ∩ S` is projection-independent at
`⋃ F` for every event `D` of the raw code σ-algebra at `r` (a σ-algebra that does not depend on the data). -/
def FibMembersRaw (d : FibData) (P : Measure (ULift.{u} FibCode)) : Prop :=
  ∀ r s : ℚ≥0, r < s → ∀ F : Finset (ℚ × ℚ × ℚ), Coupling.ballsK F ⊆ H →
    ∃ S : Set (ULift.{u} FibCode), MeasurableSet S ∧ S =ᵐ[P] Restart.DomainMarkov.safeEv fibW fibU F (s : ℝ≥0) ∧
      ∀ D : Set (ULift.{u} FibCode), MeasurableSet[codeFiltration.{u} (r : ℝ≥0)] D →
        Coupling.IsProjIndepMeasure (Restart.DomainMarkov.ballsOpen F) ((P.restrict (D ∩ S)).map (centredFib d))

/-- The killed driving filtration of the decoded driver with any marks that are geometric images of fixed points is
below the raw code filtration. -/
theorem killedDrivingFiltration_marks_le {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (hX : IsMeasurableKilledDriving fibW.{u} (geomLW fibW fun _ => xL) (geomRW fibW fun _ => xR) fibU) :
    killedDrivingFiltration hX ≤ codeFiltration.{u} := by
  have hWa := Coupling.adaptedBefore_killedDriving_W isMeasurableKilledDriving_fib.{u}
  have hc : ∀ ω : ULift.{u} FibCode, ContinuousOn (fun s => fibW s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < fibU ω} :=
    fun ω => (Aux61Fib.FibCode.continuous_driver ω.down).continuousOn
  exact Ito.killedDrivingFiltration_le hWa
    (fun i => Sec7.PocketPhaseMeans.adaptedBefore_geomLW hc hWa measurable_const i)
    (fun j => Sec7.PocketPhaseMeans.adaptedBefore_geomRW hc hWa measurable_const j) _

/-- **`FibMembersRaw` gives `FibMembers`** (PROVE-AUX61-ACT's `hasRatMembers_of_raw` and the comparison of the
filtrations). -/
theorem fibMembers_of_raw (d : FibData) (P : Measure (ULift.{u} FibCode)) (h : FibMembersRaw d P) :
    FibMembers d P := by
  intro hX
  refine Aux61Act.hasRatMembers_of_raw fun r s hrs F hF => ?_
  obtain ⟨S, hSm, hSae, hS⟩ := h r s hrs F hF
  exact ⟨S, hSm, hSae, fun D hD => hS D (killedDrivingFiltration_marks_le _ _ hX (r : ℝ≥0) _ hD)⟩

end InteractingSLE.Sec5.Aux61FibK
