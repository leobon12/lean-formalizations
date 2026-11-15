/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61FibKGlued

/-!
# (M): the explicit fibre kernel is jointly measurable in the history and the raw code

Packet PROVE-AUX61-GLUEK (Theorem 1.2's Prop 5.1 (E1); `planning/handoffs/PROVE-AUX61-FIB2.md`, "What remains" (M)).
`Aux61FibK.hasDyActFibreCover_of_glued` needs, for every dyadic time `q = k/2ⁿ` and rational test `ψ_p`, that
`(z, s) ↦ 1_{ratAvoid}(s) · ratKer (d z) (F₀ z) n k p s` be measurable for the product of the history σ-algebra and
the raw code σ-algebra at `q`. Here this is proved for every family of fibre data whose reference word is fixed and
whose correction `q`, cutoff function and cutoff source are jointly measurable in `(history, point)`
(**`measurable_ratAvoid_ratKer`**), with no integrability needed (the Bochner integral of a jointly measurable
integrand is measurable in the parameter whatever the integrability of its sections):

* `frozenW q s r`: the decoded driver frozen at `q` (and `0` if the lifetime is at most `q`): continuous, from `0`,
  measurable for the raw code σ-algebra at `q`; it has the forward map of the decoded driver at `q` before the
  lifetime;
* `measurable_fwdMap_frozenW`: its forward map at `q` is jointly measurable in `(code, point)` at **every** point
  (the landed `Exist.StagedLaw.measurable_fwdMap_param`), hence the Green potential term of `meanF`;
* the reference part `couplingMean κ w q (canonExt …)` on the safe sets `safeSet δ × tsupport ψ` through the landed
  `fwdSafe`/`logSafe` measurability and `couplingMean_eq_meanCan` (as `Coupling.measurable_meanK`);
* the energy through the landed `Coupling.measurable_energyK`; the safe union by monotone exhaustion.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param` result; R77: no post-contact kernel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GlueK

open QuantumZipper (H fwdHull fwdMap greenH)
open LQGMetric (TestOn DistOn)
open LocalExt (cfVal)
open Restart.FlowStopIdentCMI (CMCut)
open Restart.DomainMarkov (RatIdx dyT)
open Aux61Win (meanF IsCutoffOn)
open Aux61Fib (FibCode FibData PathGood fibW fibΓ fibU fibField)
open Aux61FibK (codeSigma codeFiltration ratKer ratAvoid ratψ canonExt)

universe u

/-! ### The decoded driver frozen at a fixed time -/

/-- **The decoded driver frozen at `q`**, set to `0` when the lifetime is at most `q`. -/
def frozenW (q : ℝ≥0) (s : ULift.{u} FibCode) (r : ℝ≥0) : ℝ :=
  if (q : ℝ≥0∞) < fibU s then fibW (min r q) s else 0

theorem continuous_frozenW (q : ℝ≥0) (s : ULift.{u} FibCode) : Continuous (frozenW q s) := by
  unfold frozenW
  split_ifs
  · exact (Aux61Fib.FibCode.continuous_driver s.down).comp (continuous_id.min continuous_const)
  · exact continuous_const

theorem frozenW_zero (q : ℝ≥0) (s : ULift.{u} FibCode) : frozenW q s 0 = 0 := by
  unfold frozenW
  split_ifs
  · rw [min_eq_left (zero_le (a := q))]; exact Aux61Fib.FibCode.driver_zero s.down
  · rfl

theorem frozenW_eq {q : ℝ≥0} {s : ULift.{u} FibCode} (hs : (q : ℝ≥0∞) < fibU s) {r : ℝ≥0} (hr : r ≤ q) :
    frozenW q s r = fibW r s := by
  simp only [frozenW, hs, ite_true, min_eq_left hr]

/-- The frozen driver is measurable for the raw code σ-algebra at `q`. -/
theorem measurable_frozenW (q r : ℝ≥0) : Measurable[codeFiltration.{u} q] fun s => frozenW q s r := by
  have hX := Aux61Fib.isMeasurableKilledDriving_fib.{u}
  have hlt : MeasurableSet[codeFiltration.{u} q] {s : ULift.{u} FibCode | (q : ℝ≥0∞) < fibU s} :=
    by simpa only [mem_univ, true_and, and_true] using
      Coupling.adaptedBefore_killedDriving_W hX q univ MeasurableSet.univ
  have hk : Measurable[codeFiltration.{u} q] fun s => Girsanov.killed fibU fibW (min r q) s :=
    (Girsanov.measurable_killed (Coupling.adaptedBefore_killedDriving_W hX) (min r q)).mono
      (codeFiltration.mono (min_le_right r q)) le_rfl
  have e : (fun s => frozenW q s r) = fun s =>
      if (q : ℝ≥0∞) < fibU s then Girsanov.killed fibU fibW (min r q) s else 0 := by
    funext s
    simp only [frozenW]
    split_ifs with h
    · rw [Girsanov.killed_of_lt (lt_of_le_of_lt (by exact_mod_cast min_le_right r q) h)]
    · rfl
  rw [e]
  exact Measurable.ite hlt hk measurable_const

/-- Before the lifetime the frozen driver has the forward map of the decoded driver at `q`. -/
theorem fwdMap_frozenW {q : ℝ≥0} {s : ULift.{u} FibCode} (hs : (q : ℝ≥0∞) < fibU s) (x : ℂ) :
    fwdMap (Ito.rpath (frozenW q s ·)) q x = fwdMap (Ito.rpath (fibW · s)) q x := by
  refine Ito.fwdMap_congr_of_eqOn fun r hr => ?_
  simp only [Ito.rpath]
  exact frozenW_eq hs (Real.toNNReal_le_iff_le_coe.2 hr.2)

/-- **The forward map of the frozen driver at `q` is jointly measurable in the code and the point**, for the raw
code σ-algebra at `q`. -/
theorem measurable_fwdMap_frozenW (q : ℝ≥0) :
    Measurable[(codeFiltration.{u} q).prod (inferInstance : MeasurableSpace ℂ)]
      fun a : ULift.{u} FibCode × ℂ => fwdMap (Ito.rpath (frozenW q a.1 ·)) q a.2 := by
  let _ : MeasurableSpace (ULift.{u} FibCode × ℂ) := (codeFiltration.{u} q).prod inferInstance
  refine (Exist.StagedLaw.measurable_fwdMap_param (W := fun a : ULift.{u} FibCode × ℂ => Ito.rpath (frozenW q a.1 ·))
    (fun a => (continuous_frozenW q a.1).comp continuous_real_toNNReal) (fun t => ?_)
    (fun a => by simp [Ito.rpath, frozenW_zero]) (τ := fun _ => (q : ℝ)) measurable_const (fun _ => q.coe_nonneg)
    (y := Prod.snd) measurable_snd).1
  exact (measurable_frozenW q t.toNNReal).comp measurable_fst

/-! ### The integrand of the explicit mean on a safe set -/

section Integrand

open Sec7.PocketTraversal (geomLW geomRW)

variable {β : Type*} [mβ : MeasurableSpace β]

/-- The Green potential term of `meanF` with the frozen driver: `∫ G_{ℍ∖K_q}(x, y) v_z(y) dy`. -/
def gpotF (v : β → ℂ → ℝ) (q : ℝ≥0) (z : β) (s : ULift.{u} FibCode) (x : ℂ) : ℝ :=
  ∫ y, greenH (fwdMap (Ito.rpath (frozenW q s ·)) q x) (fwdMap (Ito.rpath (frozenW q s ·)) q y) * v z y

/-- **The Green potential term is jointly measurable** in `(history, code, point)`. -/
theorem measurable_gpotF {v : β → ℂ → ℝ} (hv : Measurable fun p : β × ℂ => v p.1 p.2) (q : ℝ≥0) :
    Measurable[(mβ.prod (codeFiltration.{u} q)).prod (inferInstance : MeasurableSpace ℂ)]
      fun a : (β × ULift.{u} FibCode) × ℂ => gpotF v q a.1.1 a.1.2 a.2 := by
  let _ : MeasurableSpace (ULift.{u} FibCode) := codeFiltration.{u} q
  have hF : Measurable fun a : ULift.{u} FibCode × ℂ => fwdMap (Ito.rpath (frozenW q a.1 ·)) q a.2 :=
    measurable_fwdMap_frozenW q
  refine Coupling.measurable_integral_param (μ := (volume : Measure ℂ))
    (f := fun y (a : (β × ULift.{u} FibCode) × ℂ) =>
      greenH (fwdMap (Ito.rpath (frozenW q a.1.2 ·)) q a.2) (fwdMap (Ito.rpath (frozenW q a.1.2 ·)) q y) *
        v a.1.1 y) ?_
  have h1 : Measurable fun p : ℂ × ((β × ULift.{u} FibCode) × ℂ) =>
      fwdMap (Ito.rpath (frozenW q p.2.1.2 ·)) q p.2.2 :=
    hF.comp (measurable_snd.fst.snd.prodMk measurable_snd.snd)
  have h2 : Measurable fun p : ℂ × ((β × ULift.{u} FibCode) × ℂ) =>
      fwdMap (Ito.rpath (frozenW q p.2.1.2 ·)) q p.1 :=
    hF.comp (measurable_snd.fst.snd.prodMk measurable_fst)
  exact (QuantumZipper.measurable_greenH.comp (h1.prodMk h2)).mul
    (hv.comp (measurable_snd.fst.fst.prodMk measurable_fst))

/-- **The integrand of the explicit mean on `safeSet δ`** (zero off it): the reference part through the safe forward
map and logarithmic derivative, the Green potential term with the frozen driver, and the correction `r = q − F.f`,
times the test. -/
def meanInt (κ₀ : ℝ) (bR₀ : ℝ → ℝ) (JR₀ : Finset ℝ) (v r : β → ℂ → ℝ) (ψ : ℂ → ℝ) (δ : ℝ) (q : ℝ≥0)
    (a : (β × ULift.{u} FibCode) × ℂ) : ℝ :=
  haveI := Classical.dec
  if a.1.2 ∈ Coupling.safeSet fibW fibU univ ψ δ q then
    (Ito.meanHarmonic κ₀ (flowLineRhoL κ₀ bR₀ JR₀ 0 0) (flowLineRhoR κ₀ bR₀ JR₀ 0 0)
        (fun i => Girsanov.killed fibU (geomLW fibW (fun _ => flowLineXL bR₀ JR₀ 0) i) q a.1.2 -
          Girsanov.killed fibU fibW q a.1.2)
        (fun j => Girsanov.killed fibU (geomRW fibW (fun _ => flowLineXR bR₀ JR₀ 0) j) q a.1.2 -
          Girsanov.killed fibU fibW q a.1.2)
        (Coupling.fwdSafe fibW fibU univ ψ δ q a.2 a.1.2) -
      QuantumZipper.chiC κ₀ * (Coupling.logSafe fibW fibU univ ψ δ q a.2 a.1.2).im +
      gpotF v q a.1.1 a.1.2 a.2 + r a.1.1 a.2) * ψ a.2
  else 0

/-- **The integrand of the explicit mean is jointly measurable.** -/
theorem measurable_meanInt (κ₀ : ℝ) (bR₀ : ℝ → ℝ) (JR₀ : Finset ℝ) {v r : β → ℂ → ℝ}
    (hv : Measurable fun p : β × ℂ => v p.1 p.2) (hr : Measurable fun p : β × ℂ => r p.1 p.2)
    {ψ : TestOn upperHalfPlaneOpens} {δ : ℝ} (hδ : 0 < δ) (q : ℝ≥0) :
    Measurable[(mβ.prod (codeFiltration.{u} q)).prod (inferInstance : MeasurableSpace ℂ)]
      (meanInt.{u} κ₀ bR₀ JR₀ v r ψ δ q) := by
  have hX := Aux61Fib.isMeasurableKilledDriving_fib.{u}
  have hWa := Coupling.adaptedBefore_killedDriving_W hX
  have hc : ∀ ω : ULift.{u} FibCode, ContinuousOn (fun s => fibW s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < fibU ω} :=
    fun ω => (Aux61Fib.FibCode.continuous_driver ω.down).continuousOn
  have hGc : ∀ ω ∈ (univ : Set (ULift.{u} FibCode)),
      ContinuousOn (fun t => fibW t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < fibU ω} := fun ω _ => hc ω
  have hψH : tsupport (ψ : ℂ → ℝ) ⊆ H := Coupling.tsupport_subset_H ψ
  have hS := Coupling.measurableSet_safeSet hWa hGc MeasurableSet.univ hψH hδ q
  have hfs := Coupling.measurable_fwdSafe hWa hGc MeasurableSet.univ hψH hδ q
  have hls := Coupling.measurable_logSafe hWa hGc MeasurableSet.univ hψH hδ q
  have hVLa := fun i => Sec7.PocketPhaseMeans.adaptedBefore_geomLW hc hWa
    (measurable_const (a := flowLineXL bR₀ JR₀ 0)) i
  have hVRa := fun j => Sec7.PocketPhaseMeans.adaptedBefore_geomRW hc hWa
    (measurable_const (a := flowLineXR bR₀ JR₀ 0)) j
  have hgp := measurable_gpotF hv q
  let _ : MeasurableSpace (ULift.{u} FibCode) := codeFiltration.{u} q
  have hK : ∀ X : ℝ≥0 → ULift.{u} FibCode → ℝ, AdaptedBefore codeFiltration.{u} fibU X →
      Measurable fun a : (β × ULift.{u} FibCode) × ℂ => Girsanov.killed fibU X q a.1.2 := fun X hX' =>
    (Girsanov.measurable_killed hX' q).comp measurable_fst.snd
  have ha : Measurable fun a : (β × ULift.{u} FibCode) × ℂ => fun i =>
      Girsanov.killed fibU (geomLW fibW (fun _ => flowLineXL bR₀ JR₀ 0) i) q a.1.2 -
        Girsanov.killed fibU fibW q a.1.2 :=
    Measurable.of_eval fun i => (hK _ (hVLa i)).sub (hK _ hWa)
  have hb : Measurable fun a : (β × ULift.{u} FibCode) × ℂ => fun j =>
      Girsanov.killed fibU (geomRW fibW (fun _ => flowLineXR bR₀ JR₀ 0) j) q a.1.2 -
        Girsanov.killed fibU fibW q a.1.2 :=
    Measurable.of_eval fun j => (hK _ (hVRa j)).sub (hK _ hWa)
  have hf : Measurable fun a : (β × ULift.{u} FibCode) × ℂ => Coupling.fwdSafe fibW fibU univ ψ δ q a.2 a.1.2 :=
    hfs.comp (measurable_snd.prodMk measurable_fst.snd)
  have hl : Measurable fun a : (β × ULift.{u} FibCode) × ℂ => Coupling.logSafe fibW fibU univ ψ δ q a.2 a.1.2 :=
    hls.comp (measurable_snd.prodMk measurable_fst.snd)
  unfold meanInt
  refine Measurable.ite (measurable_fst.snd hS) ?_ measurable_const
  refine Measurable.mul ?_ (ψ.continuous.measurable.comp measurable_snd)
  refine (((Coupling.measurable_meanHarmonic_prod κ₀ _ _).comp (ha.prodMk (hb.prodMk hf))).sub
    (measurable_const.mul (Complex.measurable_im.comp hl))).add hgp |>.add ?_
  exact hr.comp (measurable_fst.fst.prodMk measurable_snd)

end Integrand

/-! ### The explicit mean on a safe set, and the kernel -/

section Kernel

open Sec7.PocketTraversal (geomLW geomRW)

variable {β : Type*} [mβ : MeasurableSpace β]

omit mβ in
/-- **On `safeSet δ` the integral of `meanInt` is the `meanF` pairing** of the data (reference word fixed). -/
theorem integral_meanInt_eq {d : FibData} {F₀ : CMCut} {κ₀ : ℝ} {bR₀ : ℝ → ℝ} {JR₀ : Finset ℝ}
    (hword : d.κ = κ₀ ∧ d.bR = bR₀ ∧ d.JR = JR₀) {v r : β → ℂ → ℝ} {z : β}
    (hv : v z = H.indicator (QuantumZipper.K3.greenDensity F₀.f)) (hr : ∀ x, r z x = d.q x - F₀.f x)
    {ψ : TestOn upperHalfPlaneOpens} {δ : ℝ} (hδ : 0 < δ) {q : ℝ≥0} {s : ULift.{u} FibCode}
    (hs : s ∈ Coupling.safeSet fibW fibU univ ψ δ q) :
    ∫ x, meanInt.{u} κ₀ bR₀ JR₀ v r ψ δ q ((z, s), x) =
      ∫ x, meanF d.κ (canonExt d s q) d.q F₀ (Ito.rpath (fibW · s)) q x * ψ x := by
  obtain ⟨h1, h2, h3⟩ := hword
  have hψH : tsupport (ψ : ℂ → ℝ) ⊆ H := Coupling.tsupport_subset_H ψ
  have hlt : (q : ℝ≥0∞) < fibU s := hs.2.1
  have hw : ContinuousOn (fun t => fibW t s) {t : ℝ≥0 | (t : ℝ≥0∞) < fibU s} :=
    (Aux61Fib.FibCode.continuous_driver s.down).continuousOn
  have hWc : ∀ ω : ULift.{u} FibCode, Continuous (fibW · ω) := fun ω =>
    Aux61Fib.FibCode.continuous_driver ω.down
  have hu := Aux61FibK.refExt_canonExt d s q
  unfold Aux61R2.RefExt at hu
  rw [h1, h2, h3] at hu
  rw [h1]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  by_cases hx : x ∈ tsupport (ψ : ℂ → ℝ)
  · have hcm := Coupling.couplingMean_eq_meanCan (κ := κ₀) (ρL := flowLineRhoL κ₀ bR₀ JR₀ 0 0)
      (ρR := flowLineRhoR κ₀ bR₀ JR₀ 0 0) (vL := fun i t => geomLW fibW (fun _ => flowLineXL bR₀ JR₀ 0) i t s)
      (vR := fun j t => geomRW fibW (fun _ => flowLineXR bR₀ JR₀ 0) j t s) hw hψH hs.2 hδ le_rfl hx
      (fun i => Sec7.PocketTraversal.geomLW_le hWc _ s q i) (fun j => Sec7.PocketTraversal.le_geomRW hWc _ s q j) hu
    have hgp : gpotF v q z s x = GB7a.greenPot (Ito.rpath (fibW · s)) (v z) q x := by
      simp only [gpotF, GB7a.greenPot, fwdMap_frozenW hlt]
    simp only [meanInt, meanF, hcm, Coupling.meanCan, Coupling.fwdSafe, Coupling.logSafe, hs, hx,
      and_self, ite_true, Girsanov.killed_of_lt hlt, hgp, hv, hr]
  · simp [meanInt, image_eq_zero_of_notMem_tsupport hx]

/-- On the codes the avoidance event of `ψ_p` at `k/2ⁿ` is the safe union. -/
theorem ratAvoid_eq_safeU (n k : ℕ) (p : RatIdx) :
    ratAvoid.{u} n k p = Restart.DomainMarkov.safeU fibW fibU univ (ratψ p) (dyT n k) :=
  Subset.antisymm (fun ω hω => Restart.DomainMarkov.mem_safeU_of_mem_avoidSet Aux61FibK.isWeakPath_fib (ratψ p)
      (mem_univ ω) hω)
    (Restart.DomainMarkov.safeU_subset_avoidSet_of_weak Aux61FibK.isWeakPath_fib univ (ratψ p) (dyT n k))

/-- **(M): the explicit kernel is jointly measurable** in the history and the raw code at `k/2ⁿ`, for fibre data with
a fixed reference word whose correction, cutoff and cutoff source are jointly measurable in `(history, point)`. -/
theorem measurable_ratAvoid_ratKer (d : β → FibData) (F₀ : β → CMCut) (κ₀ : ℝ) (bR₀ : ℝ → ℝ) (JR₀ : Finset ℝ)
    (hword : ∀ z, (d z).κ = κ₀ ∧ (d z).bR = bR₀ ∧ (d z).JR = JR₀)
    (hq : Measurable fun p : β × ℂ => (d p.1).q p.2) (hf : Measurable fun p : β × ℂ => (F₀ p.1).f p.2)
    (hsrc : Measurable fun p : β × ℂ => QuantumZipper.K3.greenDensity (F₀ p.1).f p.2) (n k : ℕ) (p : RatIdx) :
    Measurable[mβ.prod (codeSigma.{u} n k)]
      (fun zs : β × ULift.{u} FibCode => (ratAvoid n k p).indicator (ratKer (d zs.1) (F₀ zs.1) n k p) zs.2) := by
  set q : ℝ≥0 := dyT n k with hqdef
  set ψ : TestOn upperHalfPlaneOpens := ratψ p with hψdef
  set v : β → ℂ → ℝ := fun z => H.indicator (QuantumZipper.K3.greenDensity (F₀ z).f) with hvdef
  set r : β → ℂ → ℝ := fun z x => (d z).q x - (F₀ z).f x with hrdef
  have hvm : Measurable fun p : β × ℂ => v p.1 p.2 := by
    have e : (fun p : β × ℂ => v p.1 p.2) = (Prod.snd ⁻¹' H).indicator fun p : β × ℂ =>
        QuantumZipper.K3.greenDensity (F₀ p.1).f p.2 := by
      funext p; by_cases h : p.2 ∈ H <;> simp [hvdef, h]
    rw [e]
    exact hsrc.indicator (measurable_snd QuantumZipper.isOpen_H.measurableSet)
  have hrm : Measurable fun p : β × ℂ => r p.1 p.2 := hq.sub hf
  have hX := Aux61Fib.isMeasurableKilledDriving_fib.{u}
  have hWa := Coupling.adaptedBefore_killedDriving_W hX
  have hGc : ∀ ω ∈ (univ : Set (ULift.{u} FibCode)),
      ContinuousOn (fun t => fibW t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < fibU ω} := fun ω _ =>
    (Aux61Fib.FibCode.continuous_driver ω.down).continuousOn
  have hψH : tsupport (ψ : ℂ → ℝ) ⊆ H := Coupling.tsupport_subset_H ψ
  set δ : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1) with hδdef
  have hδ : ∀ m, 0 < δ m := fun m => by positivity
  -- the approximations on the safe sets
  set K : ℕ → β × ULift.{u} FibCode → ℂ := fun m zs =>
    (Coupling.safeSet fibW fibU univ ψ (δ m) q).indicator (fun s =>
      cfVal (∫ x, meanInt.{u} κ₀ bR₀ JR₀ v r ψ (δ m) q ((zs.1, s), x))
        (Coupling.energyK fibW fibU univ ψ (δ m) q s)) zs.2 with hKdef
  let _ : MeasurableSpace (ULift.{u} FibCode) := codeFiltration.{u} q
  have hKm : ∀ m, Measurable (K m) := by
    intro m
    have hS := Coupling.measurableSet_safeSet hWa hGc MeasurableSet.univ hψH (hδ m) q
    have hI : Measurable fun zs : β × ULift.{u} FibCode => ∫ x, meanInt.{u} κ₀ bR₀ JR₀ v r ψ (δ m) q (zs, x) :=
      Coupling.measurable_integral_param (μ := (volume : Measure ℂ))
        (f := fun x (zs : β × ULift.{u} FibCode) => meanInt.{u} κ₀ bR₀ JR₀ v r ψ (δ m) q (zs, x))
        ((measurable_meanInt κ₀ bR₀ JR₀ hvm hrm (hδ m) q).comp (measurable_snd.prodMk measurable_fst))
    have hE : Measurable fun zs : β × ULift.{u} FibCode => Coupling.energyK fibW fibU univ ψ (δ m) q zs.2 :=
      (Coupling.measurable_energyK hWa hGc MeasurableSet.univ hψH (hδ m) ψ.continuous.measurable q).comp
        measurable_snd
    have hc := LocalExt.continuous_cfVal.measurable.comp (hI.prodMk hE)
    have e : K m = (Prod.snd ⁻¹' Coupling.safeSet fibW fibU univ ψ (δ m) q).indicator fun zs =>
        cfVal (∫ x, meanInt.{u} κ₀ bR₀ JR₀ v r ψ (δ m) q (zs, x))
          (Coupling.energyK fibW fibU univ ψ (δ m) q zs.2) := by
      funext zs
      by_cases h : zs.2 ∈ Coupling.safeSet fibW fibU univ ψ (δ m) q <;> simp [hKdef, h]
    rw [e]
    exact hc.indicator (measurable_snd hS)
  refine measurable_of_tendsto_metrizable hKm ?_
  rw [tendsto_pi_nhds]
  intro zs
  by_cases hω : zs.2 ∈ ratAvoid.{u} n k p
  · have hω' := hω
    rw [ratAvoid_eq_safeU] at hω'
    obtain ⟨m₀, hm₀⟩ := mem_iUnion.1 hω'
    rw [indicator_of_mem hω]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop m₀] with m hm
    have hle : δ m ≤ δ m₀ := by simp only [hδdef]; gcongr
    have hsm : zs.2 ∈ Coupling.safeSet fibW fibU univ ψ (δ m) q := ⟨hm₀.1, hm₀.2.mono hle le_rfl le_rfl⟩
    simp only [hKdef, indicator_of_mem hsm]
    rw [integral_meanInt_eq (v := v) (r := r) (z := zs.1) (hword zs.1) rfl (fun x => rfl) (hδ m) hsm]
    simp only [Coupling.energyK, hsm, ite_true, ratKer]
    rfl
  · rw [indicator_of_notMem hω]
    refine tendsto_const_nhds.congr fun m => (indicator_of_notMem (fun h' => hω ?_) _).symm
    rw [ratAvoid_eq_safeU]
    exact mem_iUnion.2 ⟨m, h'⟩

end Kernel

end InteractingSLE.Sec5.Aux61GlueK
