/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdeBridge
import InteractingSLE.Spec.Supplement.GW2RdStgEngine
import InteractingSLE.Spec.Exist.StagedLawKernel
import InteractingSLE.Spec.Exist.StagedKernel
import InteractingSLE.Spec.Sec7.Aux122Disint

/-!
# GW2's retained stopped SDE under the regular conditional law given a record

Packet PROVE-GW2-SDE. The key observation of the packet (PROVE-GW2-RELDET, round 8): at stage `n` the GB6 engine
conditions on the encoded stage-start history `GW2Rd.stageEncRec c r l`, and that record generates EXACTLY the
retained σ-algebra `c.sigma r l` of JOINTDET's R11 (`GW2Rd.comap_stageEncRec_sigma`). So K2's relative safe law of the
stage (`HasRelSafe` on every word type) gives the conditional SDE of the PHYSICAL relative piece under R11's kernel
directly, with no detour through the canonical stages of the joint-chart field.

* **`ae_exists_isStopped_of_relSafe`**: for an arbitrary measurable record `rec`, word map `β`, record event `E` and
  relative variable `(Hr, R, V)` with K2's inputs on every word type (`HasRelSafe`), the engine's stop conditions
  (the stop a path rule, announced by finite path rules), the conditional Gaussian law of `Hr` given `rec` with the data
  of `β rec` (the time-`0` field law of the stage), and a physical stop `τ` that is a protected stopping rule of the
  killed path `(R, V)`: for `P`-a.e. `ω₀` with `rec ω₀ ∈ E`, for EVERY presentation of the angle-`0` flow-line word of
  `β (rec ω₀)`, there are local dynamics with driver `R` and stop `τ` satisfying `LocalDynamics.IsStopped` under
  `condExpKernel P (comap rec) ω₀`.
* **`ae_exists_isStopped_sigma`**: the same at ROOT2's encoded record, under R11's literal kernel
  `condExpKernel c.P (c.sigma r l) ω₀`.

Route: `GW2Rd.ae_isStopDrvMatch_rec` (the engine on every word type) gives the stopped driver match `P`-a.s.;
disintegration (`Aux122Disint.ae_ae_condExpKernel`) and the constancy of the record under its own conditional law
(`Exist.Staged.ae_ae_eq_of_comap`) move it, the stop rule and the protection under the kernel at a.e. `ω₀`;
`Exist.StagedLaw.ae_isGFFWithBoundaryData_condExpKernel` gives the GFF under the kernel; then
`GW2Sde.exists_isStopped_of_stopDrvMatch`. Conditional helper with a distinct name.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2Sde

open GW2KM2 Restart Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop Supp8.GB6.HullId

/-- **The stopped SDE of the physical relative piece under the regular conditional law given its record**
(conditional helper: K2's inputs, the engine's stop conditions, the time-`0` conditional field law and the
protected stop rule are hypotheses; the local dynamics are constructed). -/
theorem ae_exists_isStopped_of_relSafe (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ)
    {Fd : BoundaryWord × DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞}
    (hFd : IsCanonicalDriverCode κ 0 Fd)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {β : RecData → BoundaryWord} (hβ : Measurable β) {E : Set RecData} (hE : MeasurableSet E)
    (hcount : (range fun r : RecData => wordType κ (β r)).Countable) (hsort : ∀ r ∈ E, (β r).IsSorted)
    {rec : Ω → RecData} (hrecm : Measurable rec) {Hr : Ω → DistOn upperHalfPlaneOpens} (hHr : Measurable Hr)
    {R : ℝ≥0 → Ω → ℝ} (hRm : ∀ t, Measurable (R t)) (hRc : ∀ ω, Continuous fun t => R t ω)
    (hR0 : ∀ ω, R 0 ω = 0) {V : Ω → ℝ≥0∞} (hVm : Measurable V)
    (hS : ∀ w : WordType, HasRelSafe κ w β E (P.map fun ω => (rec ω, relVar Hr R V ω)))
    (hV0 : ∀ᵐ ω ∂P, rec ω ∈ E → 0 < V ω)
    {ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρm : Measurable ρ) (hρ : IsPathRule ρ)
    (hVρ : ∀ᵐ ω ∂P, V ω = ρ (rec ω, fun u => R u ω))
    {ρs : ℕ → RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρsm : ∀ n, Measurable (ρs n)) (hρs : ∀ n, IsPathRule (ρs n))
    (hρsfin : ∀ n x, ρs n x ≠ ⊤) (hρsmono : ∀ x, Monotone fun n => ρs n x)
    (hρslt : ∀ᵐ ω ∂P, rec ω ∈ E → ∀ n, ρs n (rec ω, fun u => R u ω) < V ω)
    (hρssup : ∀ᵐ ω ∂P, rec ω ∈ E → ⨆ n, ρs n (rec ω, fun u => R u ω) = V ω)
    (hG : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, rec ω ∈ E →
      P[fun ω' => Complex.exp (Complex.I * (Hr ω' φ : ℂ)) | MeasurableSpace.comap rec inferInstance] ω =
        gaussCF (β (rec ω)) φ)
    (τ₀ : RecData → (ℝ≥0 → ℝ) × ℝ≥0∞ → ℝ≥0∞)
    (hτ₀ : ∀ (x : RecData) (t : ℝ≥0), MeasurableSet[pathKilledSigma t] {e | τ₀ x e ≤ (t : ℝ≥0∞)})
    {τ : Ω → ℝ≥0∞} (hτm : Measurable τ) (hτ : ∀ᵐ ω ∂P, τ ω = τ₀ (rec ω) ((fun t => R t ω), V ω))
    (hτV : ∀ᵐ ω ∂P, rec ω ∈ E → τ ω ≤ V ω) (hprot : ∀ᵐ ω ∂P, rec ω ∈ E → τ ω ≠ ⊤ → τ ω < V ω) :
    ∀ᵐ ω₀ ∂P, rec ω₀ ∈ E → ∀ {nL nR : ℕ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ},
      FCDet.IsFlowType κ 0 (β (rec ω₀)) xL xR ρL ρR →
      ∃ d : GW2JDetR11.LocalDynamics Ω nL nR, d.W = R ∧ d.stop = τ ∧
        d.IsStopped (condExpKernel P (MeasurableSpace.comap rec inferInstance) ω₀) κ xL ρL xR ρR := by
  have h𝒢 : MeasurableSpace.comap rec inferInstance ≤ mΩ := hrecm.comap_le
  -- the engine: the stopped driver match, `P`-almost surely on the record event
  have hmatch := GW2Rd.ae_isStopDrvMatch_rec hκ hFd hβ hE hcount hrecm hHr hRm hRc hR0 hVm hS hV0 hρm hρ hVρ
    hρsm hρs hρsfin hρsmono hρslt hρssup
  -- everything under the kernel
  have hall : ∀ᵐ ω ∂P, (rec ω ∈ E → IsStopDrvMatch (Fd (β (rec ω), Hr ω)) (fun t => R t ω) (V ω)) ∧
      τ ω = τ₀ (rec ω) ((fun t => R t ω), V ω) ∧ (rec ω ∈ E → τ ω ≤ V ω) ∧
      (rec ω ∈ E → τ ω ≠ ⊤ → τ ω < V ω) := by
    filter_upwards [hmatch, hτ, hτV, hprot] with ω h1 h2 h3 h4 using ⟨h1, h2, h3, h4⟩
  have hker := Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 hall
  have hconst := Exist.Staged.ae_ae_eq_of_comap (P := P) hrecm
  -- the conditional field law
  have hgff := ae_isGFFWithBoundaryData_condExpKernel (P := P) h𝒢 (M := rec ⁻¹' E) (β := fun ω => β (rec ω))
    (Eventually.of_forall fun ω hω => hsort _ hω) hHr hG
  filter_upwards [hker, hconst, hgff] with ω₀ hk hc hX hω₀ nL nR xL ρL xR ρR hw
  have hX' := hX hω₀
  refine exists_isStopped_of_stopDrvMatch h12p h13 hκ hFd (hsort _ hω₀) hX' hRm hRc hR0 (V := V) ?_ (τ₀ (rec ω₀))
    (hτ₀ (rec ω₀)) hτm ?_ ?_ ?_ hw
  · filter_upwards [hk, hc] with ξ h1 h2
    rw [← h2]
    exact h1.1 (h2 ▸ hω₀)
  · filter_upwards [hk, hc] with ξ h1 h2
    rw [← h2]
    exact h1.2.1
  · filter_upwards [hk, hc] with ξ h1 h2
    exact h1.2.2.1 (h2 ▸ hω₀)
  · filter_upwards [hk, hc] with ξ h1 h2
    exact h1.2.2.2 (h2 ▸ hω₀)

end InteractingSLE.Theorem14.GW2Sde
