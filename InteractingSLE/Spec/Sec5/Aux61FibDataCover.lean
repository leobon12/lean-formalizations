/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61FibDataCode
import InteractingSLE.Spec.Sec5.Aux61FibDataMeas
import InteractingSLE.Spec.Sec5.Aux61GlueKCover

/-!
# The glued-space fibre objects, VII: the fibre cover from the restart codes

Packet PROVE-AUX61-FIBDATA. **`hasDyActFibreCover_of_restart`** is `Aux61GlueK.hasDyActFibreCover_of_chartKernel`
with the glued-space code `Y i` taken to be the **restart code killed at its window exit**
(`exitCode (Er i) (c i) (ρ i) (T i) (V i) a k h`, `Aux61FibDataCode`), and with every code-side hypothesis discharged:

* `hY` (measurability of the code): `IsRestartSpec.measurable_exitCode`;
* the path-fact set `G i = {(z, s) | PathGood (d i z) s}` is measurable (`measurableSet_pathGood`, the data share the
  window `V i` and its clearance), `hGgood` holds by definition, and `hYG` holds on the window-exit event
  (`IsRestartSpec.pathGood_exitCode`);
* the visit sets `L i = {s | the decoded path visits the open interval I i before its lifetime}` are measurable
  (`Aux61Fib.measurableSet_visitIoo`) and `hLv` holds by definition.

What remains are the hypotheses about the glued space itself: the restart data (`IsRestartSpec`, landing, injectivity,
lift continuity), the history events and the a.s. inclusion of the history events in the window-exit events, the cover
and event clauses, the data's reference words, and the analytic statements (the cutoffs, data measurability, the union
kernel in the chart `hchart`, Aux. lemma 61's (PC1) `hPC1`, and the marked locality `hloc`) — all stated about these
explicit codes. Conditional helper with a distinct name; it replaces no source theorem. R48: nothing here uses Theorem
1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`; R77: no post-contact kernel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61FibData

open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open LocalExt (cfVal)
open Restart.FlowStopIdentCMI (CMCut)
open Restart.DomainMarkov (RatIdx dyT safeEv ballsOpen)
open Aux61Win (meanF IsCutoffOn IsPC1)
open Aux61Fib (FibCode FibData PathGood fibW fibΓ fibU fibField)
open Aux61FibK (codeSigma ratKer ratAvoid ratψ ratPi canonExt)

universe u

/-- **The visit set of an open interval**: codes whose decoded path is at a point of `(p, q)` at some time before
its lifetime. -/
def visitSet (p q : ℝ) : Set FibCode :=
  {s | ∃ v : ℝ≥0, (v : ℝ≥0∞) ≤ s.life ∧ ∃ y ∈ Ioo p q, FibCode.trace s v = (y : ℂ)}

theorem measurableSet_visitSet (p q : ℝ) : MeasurableSet (visitSet p q) :=
  Aux61Fib.measurableSet_visitIoo FibCode.measurable_trace FibCode.continuous_trace FibCode.measurable_life p q

/-- `PathGood` only reads the window and the clearance of the data. -/
theorem pathGood_congr {d d' : FibData} (hV : d.V = d'.V) (hℓ : d.ℓ = d'.ℓ) (s : FibCode) :
    PathGood d s ↔ PathGood d' s := by
  simp only [PathGood, hV, hℓ]

/-- The path-fact set of a family of data sharing one window and its clearance is measurable. -/
theorem measurableSet_pathGood_family {β : Type*} [MeasurableSpace β] (d : β → FibData) {V : Set ℂ}
    (hdV : ∀ z, (d z).V = V) (hdℓ : ∀ z, (d z).ℓ = clr V) (hVo : IsOpen V) :
    MeasurableSet {p : β × FibCode | PathGood (d p.1) p.2} := by
  rcases isEmpty_or_nonempty β with hβ | ⟨⟨z₀⟩⟩
  · have : {p : β × FibCode | PathGood (d p.1) p.2} = ∅ := by
      ext p; exact isEmptyElim p.1
    rw [this]; exact MeasurableSet.empty
  · have hne : (d z₀).Vᶜ.Nonempty := by
      by_contra hemp
      rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hemp
      have hb := (d z₀).buffer_compact.isBounded.subset ((d z₀).V_sub.trans subset_closure)
      rw [hemp] at hb
      exact NormedSpace.unbounded_univ ℝ ℂ hb
    have hS := measurableSet_pathGood (d z₀) ((hdℓ z₀).trans (by rw [hdV z₀])) (by rw [hdV z₀]; exact hVo) hne
    have e : {p : β × FibCode | PathGood (d p.1) p.2} = univ ×ˢ {s | PathGood (d z₀) s} := by
      ext p
      simp only [mem_ofPred_eq, mem_prod, mem_univ, true_and]
      exact pathGood_congr ((hdV p.1).trans (hdV z₀).symm) ((hdℓ p.1).trans (hdℓ z₀).symm) p.2
    rw [e]
    exact MeasurableSet.univ.prod hS

/-- **The fibre cover of the glued space from the restart codes** (see the module docstring): the hypotheses of
`Aux61GlueK.hasDyActFibreCover_of_chartKernel`, with the code `Y i` the restart code killed at its window exit and its
measurability, path facts and visit sets discharged. -/
theorem hasDyActFibreCover_of_restart {X : Type u} [mX : MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {E : X → Prop} {Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop} {ι : Type} [Countable ι]
    {β : ι → Type*} [mβ : ∀ i, MeasurableSpace (β i)]
    (Z : ∀ i, X → β i) (hZ : ∀ i, Measurable (Z i)) (B : ∀ i, Set (β i)) (hB : ∀ i, MeasurableSet (B i))
    -- the restart data
    (Er : ι → Set X) (c : ι → X → Chart) (ρ : ι → X → ℝ≥0 → ℂ) (T : ι → X → ℝ≥0∞)
    (hs : ∀ i, IsRestartSpec (Er i) (c i) (ρ i) (T i)) (V : ι → Set ℂ) (hVo : ∀ i, IsOpen (V i))
    (hV0 : ∀ i, (0 : ℂ) ∈ V i) (hland : ∀ i, IsLanding (Er i) (c i) (ρ i) (T i) (V i))
    (hinj : ∀ i, ∀ x ∈ Er i, InjOn (ρ i x) {u | (u : ℝ≥0∞) < T i x})
    (hliftc : ∀ i, ∀ x ∈ Er i, ContinuousOn (c i x).2.2 (c i x).dom)
    (h : X → DistOn upperHalfPlaneOpens) (hh : Measurable h) (a k : ℝ)
    -- the data and the events
    (d : ∀ i, β i → FibData) (hdV : ∀ i z, (d i z).V = V i) (hdℓ : ∀ i z, (d i z).ℓ = clr (V i))
    (p q : ι → ℝ) (hRef : ∀ i, ∀ z ∈ B i, Ref (d i z).κ (d i z).bR (d i z).JR (Ioo (p i) (q i)))
    (hexit : ∀ i, ∀ᵐ x ∂μ, Z i x ∈ B i → x ∈ exitEv (Er i) (c i) (ρ i) (T i) (V i))
    (hcover : ∀ᵐ x ∂μ, E x → ∃ i, Z i x ∈ B i)
    (hE : ∀ i, ∀ᵐ x ∂μ, Z i x ∈ B i → E x →
      exitCode (Er i) (c i) (ρ i) (T i) (V i) a k h x ∈ visitSet (p i) (q i))
    -- the cutoffs and the data measurability
    (F₀ : ∀ i, β i → CMCut) (N₀ : ∀ i, β i → Set ℂ)
    (hcut : ∀ i, ∀ z ∈ B i, IsCutoffOn (F₀ i z) (d i z).q (N₀ i z) (d i z).O₀ ∧ (d i z).buffer ⊆ N₀ i z)
    (κ₀ : ι → ℝ) (bR₀ : ι → ℝ → ℝ) (JR₀ : ι → Finset ℝ)
    (hword : ∀ i z, (d i z).κ = κ₀ i ∧ (d i z).bR = bR₀ i ∧ (d i z).JR = JR₀ i)
    (hqm : ∀ i, Measurable fun p : β i × ℂ => (d i p.1).q p.2)
    (hfm : ∀ i, Measurable fun p : β i × ℂ => (F₀ i p.1).f p.2)
    (hsrc : ∀ i, Measurable fun p : β i × ℂ => QuantumZipper.K3.greenDensity (F₀ i p.1).f p.2)
    -- (K) the union kernel in the chart and (PC1)
    (𝓜 : ι → ℕ → ℕ → MeasurableSpace X) (h𝓜 : ∀ i n k, 𝓜 i n k ≤ mX)
    (hZ𝓜 : ∀ i n k, (mβ i).comap (Z i) ≤ 𝓜 i n k)
    (hY𝓜 : ∀ i n k', (codeSigma.{u} n k').comap
      (fun x => ULift.up.{u} (exitCode (Er i) (c i) (ρ i) (T i) (V i) a k h x)) ≤ 𝓜 i n k')
    (M : ι → ℕ → ℕ → X → ℂ → ℝ)
    (hchart : ∀ i (n k' : ℕ) (r : RatIdx), ∀ᵐ x ∂μ, Z i x ∈ B i →
      ULift.up.{u} (exitCode (Er i) (c i) (ρ i) (T i) (V i) a k h x) ∈ ratAvoid n k' r →
      μ[fun x' => Complex.exp (Complex.I *
          (fibField (ULift.up.{u} (exitCode (Er i) (c i) (ρ i) (T i) (V i) a k h x')) (ratψ r) : ℂ)) | 𝓜 i n k'] x =
        cfVal (∫ z, M i n k' x z * ratψ r z)
          (loewnerGreenEnergy (Ito.rpath (fibW · (ULift.up.{u} (exitCode (Er i) (c i) (ρ i) (T i) (V i) a k h x))))
            (dyT n k' : ℝ≥0) (ratψ r)))
    (hPC1 : ∀ i (n k' : ℕ), ∀ᵐ x ∂μ, Z i x ∈ B i →
      ((dyT n k' : ℝ≥0) : ℝ≥0∞) < fibU (ULift.up.{u} (exitCode (Er i) (c i) (ρ i) (T i) (V i) a k h x)) →
      IsPC1 (d i (Z i x)).κ (canonExt (d i (Z i x)) (ULift.up.{u} (exitCode (Er i) (c i) (ρ i) (T i) (V i) a k h x))
          (dyT n k'))
        (Ito.rpath (fibW · (ULift.up.{u} (exitCode (Er i) (c i) (ρ i) (T i) (V i) a k h x)))) (dyT n k')
        (d i (Z i x)).q (d i (Z i x)).O₀ (M i n k' x))
    -- (F4) the marked locality over the glued rectangles
    (hloc : ∀ i (r s : ℚ≥0), r < s → ∀ F : Finset (ℚ × ℚ × ℚ), Coupling.ballsK F ⊆ H →
      ∀ (Tf : Finset (ℚ × ℚ × ℚ)) (B' : Set (β i)), MeasurableSet B' → B' ⊆ B i →
        Coupling.IsProjIndepMeasure (ballsOpen F)
          ((μ.restrict (Z i ⁻¹' B' ∩ (fun x => ULift.up.{u} (exitCode (Er i) (c i) (ρ i) (T i) (V i) a k h x)) ⁻¹'
            (ratPi fibW fibU (r : ℝ≥0) Tf ∩ safeEv fibW fibU F (s : ℝ≥0)))).map
              fun x => fibField (ULift.up.{u} (exitCode (Er i) (c i) (ρ i) (T i) (V i) a k h x)))) :
    Aux61Act.HasDyActFibreCover μ E Ref := by
  set Y : ι → X → FibCode := fun i => exitCode (Er i) (c i) (ρ i) (T i) (V i) a k h with hYdef
  have hY : ∀ i, Measurable (Y i) := fun i =>
    (hs i).measurable_exitCode (hVo i) (hV0 i) (hland i) (hinj i) (hliftc i) hh a k
  refine Aux61GlueK.hasDyActFibreCover_of_chartKernel Z hZ Y hY B hB d (fun i => Ioo (p i) (q i))
    (fun i => visitSet (p i) (q i)) (fun i => measurableSet_visitSet _ _) (fun i s hs' => hs') hRef
    (fun i => {p : β i × FibCode | PathGood (d i p.1) p.2})
    (fun i => measurableSet_pathGood_family (d i) (hdV i) (hdℓ i) (hVo i)) (fun i z s _ hzs => hzs)
    (fun i => ?_) hcover hE F₀ N₀ hcut κ₀ bR₀ JR₀ hword hqm hfm hsrc 𝓜 h𝓜 hZ𝓜 hY𝓜 M hchart hPC1 hloc
  filter_upwards [hexit i] with x hx hxB
  exact (hs i).pathGood_exitCode (hVo i) (hV0 i) (hland i) (hinj i) (d i (Z i x)) (hdV i _) (hdℓ i _) (hx hxB)

end InteractingSLE.Sec5.Aux61FibData
