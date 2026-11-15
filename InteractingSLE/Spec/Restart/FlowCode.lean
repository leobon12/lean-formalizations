/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowCodeWord
import InteractingSLE.Spec.Restart.KernelFlow
import InteractingSLE.Spec.Restart.KernelDriver
import InteractingSLE.Spec.Sec7.Lemma75Bridge

/-!
# Canonical flow codes and driver codes from Theorems 1.2–1.3

Packet PROVE-CONDDET. PROVE-RESTARTKERNEL's restart kernels use a Borel *canonical flow code* (`Restart.IsFlowCode`)
and a Borel *canonical driver code* (`Restart.IsDriverCode`), named inputs `FlowCodeStatement` and
`DriverCodeStatement`.

**Defect of the landed predicates.** `IsFlowCode` (resp. `IsDriverCode`) quantifies over *every* lifetime `ζ`
(resp. `L`) that almost surely equals the coded one, measurable or not; but `IsFlowLine` (resp. `IsFlowLineDriver`)
contains `IsMeasurableKilledDriving`, which forces `{r < ζ}` to be measurable for every `r`
(`Restart.measurable_lifetime_of_isFlowLine`). On a probability space with a null measurable set that has a
non-measurable subset, a lifetime equal to the coded one off that null set and non-measurable on it matches the code
almost surely and is no flow line. So no `F` satisfies `IsFlowCode`, and `FlowCodeStatement`, `DriverCodeStatement` are
false as stated (and the reductions `KernelG7`, `KernelFC` that assume them are vacuous). Every consumer
(`ae_isFlowLine_of_codeMatch`, `ae_isFlowLineDriver_of_codeMatch`) has a measurable lifetime coordinate, so the fix is
to add `Measurable ζ` (resp. `Measurable L`) to the predicates.

This file proves the corrected statements, together with the converse (determination) direction that the
"lift back" of the conditional determination identity needs:

* `isOptionalHullCoupling_of_detAgree`: a measurable driver with a measurable lifetime that agree almost surely with
  the field-determined driver of `Theorem12ParamStatement` (before the lifetime and at time `0`) form, with the field,
  an optional hull coupling (a variant of `Exist.Staged.isOptionalHullCoupling_drv` whose lifetime and driver may
  differ from the determined ones on a null set);
* **`flowCode`**, **`driverCode`**: the canonical codes, jointly measurable in the word, the seed and the field
  (`measurable_flowCode`, `measurable_driverCode`), built from the measurable flow-line word (`FlowCodeWord.lean`);
* **`IsCanonicalFlowCode`**, **`IsCanonicalDriverCode`**: the corrected `IsFlowCode`/`IsDriverCode` (with a measurable
  lifetime), together with determination (every flow line, resp. driver, matches the code almost surely);
* **`isCanonicalFlowCode_flowCode`**, **`isCanonicalDriverCode_driverCode`**, **`canonicalFlowCodeStatement_of_param`**,
  **`canonicalDriverCodeStatement_of_param`**: both from `Theorem12ParamStatement` and `Theorem13Statement` (exactly the
  frozen Theorem 1.3's type) at universe `0`.

**R43.** These are inputs of the restart kernels of Theorems 1.4–1.5 (G7, first contact, GB6, the §5 counterflow
restart), which are downstream of Theorem 1.2; they use Theorem 1.2 (in R44's word-measurable form) and Theorem 1.3 as
inputs, which is not circular. They must not be fed into Lemma 7.1's chain.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Restart

open LQGMetric Sec2.Assembly Exist.Staged

/-! ### The field-determined coupling, moved to an almost surely equal driver and lifetime -/

/-- **The field-determined driver realizes an optional hull coupling, up to null modifications.** For an ordered word
and a measurable GFF `h₀` with its data, a measurable driver `W` and a measurable lifetime `ζ` that almost surely agree
with the field-determined driver `drvOf (detCode (paramΦ …) (w, h₀))` (equal lifetimes, equal values at `0` and before
the lifetime) form with `h₀` an optional hull coupling. -/
theorem isOptionalHullCoupling_of_detAgree (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) {Ω : Type u} [mΩ : MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hh₀ : IsGFFWithBoundaryData Q h₀ (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR))
    {W : ℝ≥0 → Ω → ℝ} (hW : ∀ t, Measurable (W t)) {ζ : Ω → ℝ≥0∞} (hζ : Measurable ζ)
    (hagree : ∀ᵐ ω ∂Q, ζ ω = (drvOf (detCode (paramΦ h12p hκ nL nR) (((xL, xR), (ρL, ρR)), h₀ ω))).2 ∧
      W 0 ω = (drvOf (detCode (paramΦ h12p hκ nL nR) (((xL, xR), (ρL, ρR)), h₀ ω))).1 0 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω →
        W t ω = (drvOf (detCode (paramΦ h12p hκ nL nR) (((xL, xR), (ρL, ρR)), h₀ ω))).1 t) :
    ∃ (𝓕 : Filtration ℝ≥0 mΩ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ), IsOptionalHullCoupling κ xL xR ρL ρR Q 𝓕 W VL VR B ζ h₀ := by
  set Φ := paramΦ h12p hκ nL nR with hΦdef
  have hΦm : Measurable Φ := measurable_paramΦ h12p hκ nL nR
  have h12 : Exist.Theorem12Statement.{u} := theorem12Statement_of_param h12p
  -- the reference coupling (sealed Theorem 1.1) and its field-determined realization
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, hr, hcoup⟩ :=
    Spec.Provider.exists_isOptionalHullCoupling.{u} (κ := κ) (xL := xL) (xR := xR) (ρL := ρL) (ρR := ρR) hκ hF
  obtain ⟨Ψ, S, ηf, hΨm, hSm, hae, hSdet, -, hreal⟩ :=
    exists_fieldDetermination_realization_det h12 h13 hκ hF hcoup
  obtain ⟨u, hu, -⟩ := Spec.Provider.existsUnique_isBoundedHarmonicExtension_forceBoundaryData (κ := κ)
    (ρL := ρL) (ρR := ρR) (vL := xL) (vR := xR)
  have hr' : IsGFFWithBoundaryData P₀ hr (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) :=
    ⟨hcoup.2.1, hcoup.2.2.1⟩
  have hlaw : Q.map h₀ = P₀.map hr := Exist.map_eq_of_isGFFWithBoundaryData hh₀ hr' hu
  -- the realization on `(Ω, Q)`, on the usual augmentation
  obtain ⟨𝓕, B, hEv⟩ := hreal Q h₀ hh₀.1 hlaw
  have hEa := Ito.isIntegratedSLEEvolution_usualAugmentation hEv
  have hdet : ∀ᵐ ω ∂P₀, (Exist.pathsOfCode (Ψ (hr ω))).1 = ζ₀ ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₀ ω →
      (Exist.pathsOfCode (Ψ (hr ω))).2.1 t = W₀ t ω ∧
        (∀ i, (Exist.pathsOfCode (Ψ (hr ω))).2.2.1 i t = VL₀ i t ω) ∧
        ∀ j, (Exist.pathsOfCode (Ψ (hr ω))).2.2.2 j t = VR₀ j t ω := by
    filter_upwards [hae] with ω hω
    exact ⟨hω.2.1, hω.2.2⟩
  have hdatum : Exist.IsFieldRealizationDatum κ xL xR ρL ρR (Exist.pathsOfCode ∘ Ψ) Q h₀ :=
    ⟨hκ, hF, Exist.measurable_pathsOfCode.comp hΨm, hh₀.1, Ω₀, mΩ₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, hr,
      hcoup, hdet, hlaw⟩
  have hC := Exist.hullClauseTransferStatement κ _ _ _ _ (Exist.pathsOfCode ∘ Ψ) Q h₀ hdatum _ B hEa
  -- the determined driver code is the realized one almost everywhere for the reference law
  have hdetm : Measurable fun f : DistOn upperHalfPlaneOpens => detCode Φ (((xL, xR), (ρL, ρR)), f) :=
    (measurable_detCode hΦm).comp (measurable_const.prodMk measurable_id)
  have hAm : MeasurableSet {f : DistOn upperHalfPlaneOpens |
      detCode Φ (((xL, xR), (ρL, ρR)), f) = dOf (Ψ f)} :=
    measurableSet_eq_dCode hdetm (measurable_dOf.comp hΨm)
  have href : ∀ᵐ f ∂(P₀.map hr), detCode Φ (((xL, xR), (ρL, ρR)), f) = dOf (Ψ f) := by
    refine (ae_map_iff hcoup.2.1.aemeasurable hAm).2 ?_
    filter_upwards [ae_detCode_eq hκ hF h13 hcoup ((h12p κ hκ nL nR).choose_spec.2 xL xR ρL ρR hF hcoup), hae]
      with ω ⟨x₀, hx₀, hζx, hwx, hcode⟩ hω
    have hcode' : detCode Φ (((xL, xR), (ρL, ρR)), hr ω) = dOf x₀ := hcode
    rw [hcode']
    refine dOf_eq_of_agree hx₀ (hSdet _ hω.1) (hζx.trans hω.2.1.symm) fun t ht => ?_
    rw [hζx] at ht
    exact ((hwx t ht).1).trans ((hω.2.2 t ht).1).symm
  rw [← hlaw] at href
  have hQ : ∀ᵐ ω ∂Q, detCode Φ (((xL, xR), (ρL, ρR)), h₀ ω) = dOf (Ψ (h₀ ω)) :=
    (ae_map_iff hh₀.1.aemeasurable hAm).1 href
  -- move the coupling to `(W, ζ)`
  have hX' : IsMeasurableKilledDriving W (fun i t ω => cvL (Ψ (h₀ ω)) i t) (fun j t ω => cvR (Ψ (h₀ ω)) j t) ζ := by
    intro t A hA
    refine (measurableSet_lt measurable_const hζ).inter (hA.preimage ?_)
    refine (hW t).prodMk
      ((measurable_pi_iff.2 fun i => (measurable_cvL_at i t).comp (hΨm.comp hh₀.1)).prodMk
        (measurable_pi_iff.2 fun j => (measurable_cvR_at j t).comp (hΨm.comp hh₀.1)))
  refine ⟨_, _, _, B, IsOptionalHullCoupling.congr_ae hC
    (fun t N hN h0 => Ito.measurableSet_usualAugmentation_of_null hN h0 t) hX' ?_⟩
  have hSQ : ∀ᵐ ω ∂Q, h₀ ω ∈ S := by
    have h1 : ∀ᵐ f ∂(P₀.map hr), f ∈ S :=
      (ae_map_iff hcoup.2.1.aemeasurable hSm).2 (hae.mono fun ω hω => hω.1)
    rw [← hlaw] at h1
    exact (ae_map_iff hh₀.1.aemeasurable hSm).1 h1
  filter_upwards [hagree, hQ, hSQ] with ω ⟨hζω, h0ω, hWω⟩ hQω hSω
  have hd : drvOf (detCode Φ (((xL, xR), (ρL, ρR)), h₀ ω)) = (drvPath (dOf (Ψ (h₀ ω))), cζ (Ψ (h₀ ω))) := by
    rw [hQω, drvOf_of_mem (dOf_mem_DSet (hSdet _ hSω))]
    rfl
  have hζ' : ζ ω = cζ (Ψ (h₀ ω)) := by rw [hζω, hd]
  have h0' : W 0 ω = drvPath (dOf (Ψ (h₀ ω))) 0 := by rw [h0ω, hd]
  refine ⟨hζ', h0'.trans (drvPath_dOf_agree _).1, fun t ht => ?_⟩
  have ht' : (t : ℝ≥0∞) < cζ (Ψ (h₀ ω)) := ht
  have hWt : W t ω = drvPath (dOf (Ψ (h₀ ω))) t := by
    rw [hWω t (by rw [hζ']; exact ht'), hd]
  exact hWt.trans ((drvPath_dOf_agree _).2 t ht')

/-! ### The canonical codes -/

section Codes

variable (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (θ : ℝ)

/-- The arguments of the determination map at word sizes `mn`: the truncated padded flow-line word of `(c, x)` and
the flow field. -/
def flowArg (mn : ℕ × ℕ) (q : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens) :
    WordData mn.1 mn.2 × DistOn upperHalfPlaneOpens :=
  (truncWord mn.1 mn.2 (flowPad κ θ q.1), Exist.flowField q.1.2 (θ * QuantumZipper.chiC κ) q.2)

theorem measurable_flowArg (mn : ℕ × ℕ) : Measurable (flowArg (κ := κ) θ mn) := by
  have h1 : Measurable fun q : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens =>
      truncWord mn.1 mn.2 (flowPad κ θ q.1) :=
    (measurable_truncWord mn.1 mn.2).comp ((measurable_flowPad κ θ).comp measurable_fst)
  have hg : Measurable fun q : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens => (q.1.2, q.2) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have h2 := (measurable_flowField_uncurry (θ * QuantumZipper.chiC κ)).comp hg
  exact h1.prodMk h2

/-- The determination output at word sizes `r.2`. -/
def flowTraceAt (r : ((BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens) × (ℕ × ℕ)) : ℝ≥0∞ × (ℝ≥0 → ℂ) :=
  paramΦ h12p hκ r.2.1 r.2.2 (flowArg (κ := κ) θ r.2 r.1)

theorem measurable_flowTraceAt : Measurable (flowTraceAt h12p hκ θ) :=
  measurable_from_prod_countable_left fun mn =>
    (measurable_paramΦ h12p hκ mn.1 mn.2).comp (measurable_flowArg θ mn)

/-- The word-glued determination output at the flow-line word of `(c, x)` and the flow field of `f`. -/
def flowTrace (q : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens) : ℝ≥0∞ × (ℝ≥0 → ℂ) :=
  flowTraceAt h12p hκ θ (q, (flowLineNL q.1.1.fn q.1.1.jumps q.1.2, flowLineNR q.1.1.fn q.1.1.jumps q.1.2))

theorem measurable_flowTrace : Measurable (flowTrace h12p hκ θ) := by
  have hg : Measurable fun q : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens =>
      (q, (flowLineNL q.1.1.fn q.1.1.jumps q.1.2, flowLineNR q.1.1.fn q.1.1.jumps q.1.2)) :=
    measurable_id.prodMk ((measurable_flowLineNL.comp measurable_fst).prodMk
      (measurable_flowLineNR.comp measurable_fst))
  have h2 := (measurable_flowTraceAt h12p hκ θ).comp hg
  exact h2

theorem flowTrace_mk (c : BoundaryWord) (x : ℝ) (f : DistOn upperHalfPlaneOpens) :
    flowTrace h12p hκ θ ((c, x), f) = paramΦ h12p hκ (flowLineNL c.fn c.jumps x) (flowLineNR c.fn c.jumps x)
      (((flowLineXL c.fn c.jumps x, flowLineXR c.fn c.jumps x),
        (flowLineRhoL κ c.fn c.jumps x θ, flowLineRhoR κ c.fn c.jumps x θ)),
        Exist.flowField x (θ * QuantumZipper.chiC κ) f) := by
  have e := truncWord_flowPad κ θ (c, x)
  simp only [flowTrace, flowTraceAt, flowArg]
  rw [e]

/-- **The canonical flow code**: the seed plus the determined trace of the flow-line word, coded with the determined
lifetime. -/
def flowCode (q : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens) : (PCode × PCode) × ℝ≥0∞ :=
  encPath (fun t => (q.1.2 : ℂ) + (flowTrace h12p hκ θ q).2 t) (flowTrace h12p hκ θ q).1

theorem measurable_flowCode : Measurable (flowCode h12p hκ θ) := by
  have hT := measurable_flowTrace h12p hκ θ
  refine measurable_encPath (fun t => ?_) (measurable_fst.comp hT)
  exact (Complex.measurable_ofReal.comp (measurable_snd.comp measurable_fst)).add
    ((measurable_pi_apply t).comp (measurable_snd.comp hT))

/-- The field-determined driver of the flow line from `0` of a field with data `c`. -/
def driverOf (q : BoundaryWord × DistOn upperHalfPlaneOpens) : (ℝ≥0 → ℝ) × ℝ≥0∞ :=
  stagedDrv h12p hκ (fun a : BoundaryWord × ℝ => flowLineNL a.1.fn a.1.jumps a.2)
    (fun a : BoundaryWord × ℝ => flowLineNR a.1.fn a.1.jumps a.2) (flowPad κ θ) (q.1, 0)
    (Exist.flowField 0 (θ * QuantumZipper.chiC κ) q.2)

theorem measurable_driverOf : Measurable (driverOf h12p hκ θ) := by
  have h := measurable_stagedDrv h12p hκ measurable_flowLineNL measurable_flowLineNR (measurable_flowPad κ θ)
  have hg : Measurable fun q : BoundaryWord × DistOn upperHalfPlaneOpens =>
      ((q.1, (0 : ℝ)), Exist.flowField 0 (θ * QuantumZipper.chiC κ) q.2) :=
    (measurable_fst.prodMk measurable_const).prodMk ((Exist.measurable_flowField 0 _).comp measurable_snd)
  have h2 := h.comp hg
  exact h2

theorem driverOf_mk (c : BoundaryWord) (f : DistOn upperHalfPlaneOpens) :
    driverOf h12p hκ θ (c, f) = drvOf (detCode (paramΦ h12p hκ (flowLineNL c.fn c.jumps 0) (flowLineNR c.fn c.jumps 0))
      (((flowLineXL c.fn c.jumps 0, flowLineXR c.fn c.jumps 0),
        (flowLineRhoL κ c.fn c.jumps 0 θ, flowLineRhoR κ c.fn c.jumps 0 θ)),
        Exist.flowField 0 (θ * QuantumZipper.chiC κ) f)) := by
  have e := truncWord_flowPad κ θ (c, 0)
  simp only [driverOf, stagedDrv]
  rw [e]

/-- **The canonical driver code**: the dyadic code of the determined driver of the flow line from `0`, with its
lifetime. -/
def driverCode (q : BoundaryWord × DistOn upperHalfPlaneOpens) : PCode × ℝ≥0∞ :=
  (enc (driverOf h12p hκ θ q).1, (driverOf h12p hκ θ q).2)

theorem measurable_driverCode : Measurable (driverCode h12p hκ θ) := by
  have hD := measurable_driverOf h12p hκ θ
  refine (measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k => ?_).prodMk (measurable_snd.comp hD)
  exact (measurable_pi_apply _).comp (measurable_fst.comp hD)

end Codes

end Restart

end InteractingSLE
