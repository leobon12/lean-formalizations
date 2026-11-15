/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GlueKMem
import InteractingSLE.Spec.Sec5.Aux61GlueKCond
import InteractingSLE.Spec.Sec5.Aux61GlueKMeas

/-!
# The fibre cover from the chart kernel, (PC1) and glued projection independence

Packet PROVE-AUX61-GLUEK. **`hasDyActFibreCover_of_chartKernel`** is `Aux61FibK.hasDyActFibreCover_of_glued` with its
three glued-space hypotheses replaced by this packet's reductions:

* `hmeas` (M) by joint measurability of the data (`measurable_ratAvoid_ratKer`: a fixed reference word per index, and
  the correction, cutoff and cutoff source jointly measurable in `(history, point)`);
* `hint` (K) by the union kernel in the chart with some mean `M` and Aux. lemma 61's identity (PC1) for `M`
  (`hint_of_chartKernel`);
* `hmem` (F4) by projection independence of the chart field's law over the glued rectangles
  (`ae_fibMembersRaw_of_glued`, then `Aux61FibK.fibMembers_of_raw`).

Conditional helper with a distinct name; it replaces no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param` result; R77: no post-contact kernel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GlueK

open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open LocalExt (cfVal)
open Restart.FlowStopIdentCMI (CMCut)
open Restart.DomainMarkov (RatIdx dyT safeEv ballsOpen)
open Aux61Win (meanF IsCutoffOn IsPC1)
open Aux61Fib (FibCode FibData PathGood fibW fibΓ fibU fibField)
open Aux61FibK (codeSigma ratKer ratAvoid ratψ ratPi canonExt)

universe u

/-- **The fibre cover of the glued space from the chart kernel, (PC1) and glued projection independence** (see the
module docstring): the hypotheses of `Aux61FibK.hasDyActFibreCover_of_glued` with `hmeas`, `hint` and `hmem` replaced
by data measurability, the union kernel in the chart with a (PC1) mean, and the marked locality of the chart field
over the glued rectangles. -/
theorem hasDyActFibreCover_of_chartKernel {X : Type u} [mX : MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {E : X → Prop} {Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop} {ι : Type} [Countable ι]
    {β : ι → Type*} [mβ : ∀ i, MeasurableSpace (β i)]
    (Z : ∀ i, X → β i) (hZ : ∀ i, Measurable (Z i)) (Y : ι → X → FibCode) (hY : ∀ i, Measurable (Y i))
    (B : ∀ i, Set (β i)) (hB : ∀ i, MeasurableSet (B i)) (d : ∀ i, β i → FibData) (I : ι → Set ℝ)
    (L : ι → Set FibCode) (hL : ∀ i, MeasurableSet (L i))
    (hLv : ∀ i, ∀ s ∈ L i, ∃ v : ℝ≥0, (v : ℝ≥0∞) ≤ s.life ∧ ∃ y ∈ I i, s.trace v = (y : ℂ))
    (hRef : ∀ i, ∀ z ∈ B i, Ref (d i z).κ (d i z).bR (d i z).JR (I i))
    (G : ∀ i, Set (β i × FibCode)) (hG : ∀ i, MeasurableSet (G i))
    (hGgood : ∀ i z s, z ∈ B i → (z, s) ∈ G i → PathGood (d i z) s)
    (hYG : ∀ i, ∀ᵐ x ∂μ, Z i x ∈ B i → (Z i x, Y i x) ∈ G i)
    (hcover : ∀ᵐ x ∂μ, E x → ∃ i, Z i x ∈ B i) (hE : ∀ i, ∀ᵐ x ∂μ, Z i x ∈ B i → E x → Y i x ∈ L i)
    (F₀ : ∀ i, β i → CMCut) (N₀ : ∀ i, β i → Set ℂ)
    (hcut : ∀ i, ∀ z ∈ B i, IsCutoffOn (F₀ i z) (d i z).q (N₀ i z) (d i z).O₀ ∧ (d i z).buffer ⊆ N₀ i z)
    -- (M) the data
    (κ₀ : ι → ℝ) (bR₀ : ι → ℝ → ℝ) (JR₀ : ι → Finset ℝ)
    (hword : ∀ i z, (d i z).κ = κ₀ i ∧ (d i z).bR = bR₀ i ∧ (d i z).JR = JR₀ i)
    (hqm : ∀ i, Measurable fun p : β i × ℂ => (d i p.1).q p.2)
    (hfm : ∀ i, Measurable fun p : β i × ℂ => (F₀ i p.1).f p.2)
    (hsrc : ∀ i, Measurable fun p : β i × ℂ => QuantumZipper.K3.greenDensity (F₀ i p.1).f p.2)
    -- (K) the union kernel in the chart and (PC1)
    (𝓜 : ι → ℕ → ℕ → MeasurableSpace X) (h𝓜 : ∀ i n k, 𝓜 i n k ≤ mX)
    (hZ𝓜 : ∀ i n k, (mβ i).comap (Z i) ≤ 𝓜 i n k)
    (hY𝓜 : ∀ i n k, (codeSigma.{u} n k).comap (fun x => ULift.up.{u} (Y i x)) ≤ 𝓜 i n k)
    (M : ι → ℕ → ℕ → X → ℂ → ℝ)
    (hchart : ∀ i (n k : ℕ) (p : RatIdx), ∀ᵐ x ∂μ, Z i x ∈ B i → ULift.up.{u} (Y i x) ∈ ratAvoid n k p →
      μ[fun x' => Complex.exp (Complex.I * (fibField (ULift.up.{u} (Y i x')) (ratψ p) : ℂ)) | 𝓜 i n k] x =
        cfVal (∫ z, M i n k x z * ratψ p z)
          (loewnerGreenEnergy (Ito.rpath (fibW · (ULift.up.{u} (Y i x)))) (dyT n k : ℝ≥0) (ratψ p)))
    (hPC1 : ∀ i (n k : ℕ), ∀ᵐ x ∂μ, Z i x ∈ B i → ((dyT n k : ℝ≥0) : ℝ≥0∞) < fibU (ULift.up.{u} (Y i x)) →
      IsPC1 (d i (Z i x)).κ (canonExt (d i (Z i x)) (ULift.up.{u} (Y i x)) (dyT n k))
        (Ito.rpath (fibW · (ULift.up.{u} (Y i x)))) (dyT n k) (d i (Z i x)).q (d i (Z i x)).O₀ (M i n k x))
    -- (F4) the marked locality over the glued rectangles
    (hloc : ∀ i (r s : ℚ≥0), r < s → ∀ F : Finset (ℚ × ℚ × ℚ), Coupling.ballsK F ⊆ H →
      ∀ (T : Finset (ℚ × ℚ × ℚ)) (B' : Set (β i)), MeasurableSet B' → B' ⊆ B i →
        Coupling.IsProjIndepMeasure (ballsOpen F)
          ((μ.restrict (Z i ⁻¹' B' ∩ (fun x => ULift.up.{u} (Y i x)) ⁻¹'
            (ratPi fibW fibU (r : ℝ≥0) T ∩ safeEv fibW fibU F (s : ℝ≥0)))).map
              fun x => fibField (ULift.up.{u} (Y i x)))) :
    Aux61Act.HasDyActFibreCover μ E Ref := by
  have hmeas : ∀ i (n k : ℕ) (p : RatIdx), Measurable[(mβ i).prod (codeSigma.{u} n k)]
      (fun zs : β i × ULift.{u} FibCode => (ratAvoid n k p).indicator (ratKer (d i zs.1) (F₀ i zs.1) n k p) zs.2) :=
    fun i n k p => measurable_ratAvoid_ratKer (d i) (F₀ i) (κ₀ i) (bR₀ i) (JR₀ i) (hword i) (hqm i) (hfm i)
      (hsrc i) n k p
  have hgood : ∀ i, ∀ᵐ x ∂μ, Z i x ∈ B i → PathGood (d i (Z i x)) (Y i x) := fun i =>
    (hYG i).mono fun x hx hxB => hGgood i _ _ hxB (hx hxB)
  have hint : ∀ i (n k : ℕ) (p : RatIdx) (T : Finset (ℚ × ℚ × ℚ)) (B' : Set (β i)), MeasurableSet B' → B' ⊆ B i →
      ∫ x in Z i ⁻¹' B' ∩ (fun x => ULift.up.{u} (Y i x)) ⁻¹' ratPi fibW.{u} fibU.{u} (dyT n k) T,
        Aux61FibK.gluedInt.{u} (B i) (d i) (F₀ i) n k p (Z i x, ULift.up (Y i x)) ∂μ = 0 := fun i =>
    hint_of_chartKernel (hZ i) (hY i) (hB i) (d i) (F₀ i) (N₀ i) (hcut i) (hgood i) (hmeas i)
    (𝓜 i) (h𝓜 i) (hZ𝓜 i) (hY𝓜 i) (M i) (hchart i) (hPC1 i)
  refine Aux61FibK.hasDyActFibreCover_of_glued Z hZ Y hY B hB d I L hL hLv hRef G hG hGgood hYG hcover hE F₀ N₀
    hcut hmeas hint fun i => ?_
  have hraw := Aux61FibK.ae_fibKernelRaw_of_glued (hZ i) (hY i) (hB i) (d i) (F₀ i) (N₀ i) (hcut i) (G i) (hG i)
    (hGgood i) (hYG i) (hmeas i) (hint i)
  have hpg := Aux61FibK.ae_pathGood_condDistrib (hZ i) (hY i) (hB i) (d i) (G i) (hG i) (hGgood i) (hYG i)
  filter_upwards [ae_fibMembersRaw_of_glued (hZ i) (hY i) (hB i) (d i) hpg hraw (hloc i)] with x hx hxB
  exact Aux61FibK.fibMembers_of_raw _ _ (hx hxB)

end InteractingSLE.Sec5.Aux61GlueK
