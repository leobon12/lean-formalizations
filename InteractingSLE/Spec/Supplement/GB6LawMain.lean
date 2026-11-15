/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6TraceLaw
import InteractingSLE.Spec.Supplement.GB6Life
import InteractingSLE.Spec.Supplement.GB6MeasChart

/-!
# Proposition GB6: the hull form of its conditional-law half from (d)

Packet PROVE-GB6D. **`gb6RelativeLawStatement_of_condDet`**: PROVE-GB6C's `GB6RelativeLawStatement` follows from

* `Restart.CanonicalDriverCodeStatement` (canonical driver codes; proved by PROVE-CONDDET from Theorem 1.2 in R44's
  word-measurable form and Theorem 1.3, `Restart.canonicalDriverCodeStatement_of_param`);
* `CompleteSixteenDivStatement` (Theorem 1.3 at `16/κ` in its landed form);
* `GB6EndpointStatement` (the deterministic half of step (e), `GB6Life.lean`);
* `GB6CondDetStatement` (step (d), named in the general restart kernel's form, `GB6Law.lean`).

Proof. The chart field has a measurable version (`exists_measurable_chartField`); with the canonical driver code `F` of
the counterflow at `16/κ`, (d) gives `𝒢, M, β, jL, jR`. The restart variable is
`X = (Hc, F (β, Hc), jL, jR) : GB6Space` (measurable: every component is). PROVE-RESTARTKERNEL's general kernel
(`Restart.restartKernel_isFlowLineDriver_of_codeMatch_canonical`, with the code decoded before its lifetime) gives:
for a disintegrating kernel `K` (`Restart.exists_isMarkovKernel_map_eq_compProd`) under which the chart field is a GFF
with the word and the decoded code drives its counterflow. Under
almost every `K c`, `gb6_kernel` gives (f) — the conditional counterflow with infinite lifetime and complete transient
trace — and the good event `IsGB6KernelGood` (code with infinite lifetime, generating trace, avoidance of the closed
tails), which is measurable and integrates back to almost every `ω ∈ M` (`Restart.ae_mem_of_compProd_eq`). Pathwise, on
`{s < ζα, α(s) ∈ ℍ}`: the decoded chart driver is the canonical one of (d)'s hull identity, the chart path is its
generating trace, and since it avoids the closed tails at the geometric junctions, `relClock_unbounded_of_endpoint`
(step (e)) makes the relative clock unbounded before the first contact.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Supp8

namespace GB6

open Restart Sec2.Assembly LQGMetric

/-- **The pathwise clause of `GB6RelativeLawStatement` at one realization**, from the good event of the canonical space
and the hull identity of (d). -/
theorem gb6_pathwise (hEnd : GB6EndpointStatement) {κ : ℝ} {hω Hω : DistOn upperHalfPlaneOpens}
    {wα w : ℝ≥0 → ℝ} {Tα : ℝ≥0∞} {α γ : ℝ≥0 → ℂ} {s : ℝ≥0} {x : GB6Space}
    (hα : IsGeneratingTrace wα Tα α) (hwα : ContinuousOn wα {t | (t : ℝ≥0∞) < Tα}) (hwα0 : wα 0 = 0)
    (hs : (s : ℝ≥0∞) < Tα) (hsH : α s ∈ H) (hγ : IsGeneratingTrace w ⊤ γ) (hw : Continuous w) (hw0 : w 0 = 0)
    (htrγ : Tendsto (fun t => ‖γ t‖) atTop atTop)
    (htr : IsChartTransport (ownComponentChart (fun r : ℝ => wα r.toNNReal) s) (-1)
      (-(Real.pi * QuantumZipper.chiC κ)) (QuantumZipper.chiC (16 / κ)) hω Hω) (hHx : gb6Field x = Hω)
    (hgood : IsGB6KernelGood x) (hcode : IsGoodDrvCode (gb6Code x))
    (hjL : gb6JL x = junctionL (fun r : ℝ => wα r.toNNReal) s)
    (hjR : gb6JR x = junctionR (fun r : ℝ => wα r.toNNReal) s)
    (hK : ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
        ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s) →
      QuantumZipper.fwdHull (fun r : ℝ => drvDec (gb6Code x) r.toNNReal)
          (relClock (fun r : ℝ => wα r.toNNReal) s (fun r : ℝ => w r.toNNReal) t) =
        relMap (fun r : ℝ => wα r.toNNReal) s '' QuantumZipper.fwdHull (fun r : ℝ => w r.toNNReal) t) :
    IsChartTransport (ownComponentChart (fun r : ℝ => wα r.toNNReal) s) (-1)
        (-(Real.pi * QuantumZipper.chiC κ)) (QuantumZipper.chiC (16 / κ)) hω (gb6Field x) ∧
      Continuous (fun t => gb6WC t x) ∧ gb6WC 0 x = 0 ∧ IsGeneratingTrace (fun t => gb6WC t x) ⊤ (gb6Γ x) ∧
      (∀ u : ℝ, ∃ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
          ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s) ∧
        u ≤ relClock (fun r : ℝ => wα r.toNNReal) s (fun r : ℝ => w r.toNNReal) t) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
          ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s) →
        QuantumZipper.fwdHull (fun r : ℝ => gb6WC r.toNNReal x)
            (relClock (fun r : ℝ => wα r.toNNReal) s (fun r : ℝ => w r.toNNReal) t) =
          relMap (fun r : ℝ => wα r.toNNReal) s '' QuantumZipper.fwdHull (fun r : ℝ => w r.toNNReal) t := by
  obtain ⟨hL, -, htg, hav⟩ := hgood
  have hdrv : (fun t => gb6WC t x) = drvDec (gb6Code x) := drvDecTop_eq_drvDec hcode hL
  have hgen := isGeneratingTrace_gb6Γ htg
  have e : (fun r : ℝ => gb6WC r.toNNReal x) = fun r : ℝ => drvDec (gb6Code x) r.toNNReal := by
    funext r; exact congrFun hdrv r.toNNReal
  have hK' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
        ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s) →
      QuantumZipper.fwdHull (fun r : ℝ => gb6WC r.toNNReal x)
          (relClock (fun r : ℝ => wα r.toNNReal) s (fun r : ℝ => w r.toNNReal) t) =
        relMap (fun r : ℝ => wα r.toNNReal) s '' QuantumZipper.fwdHull (fun r : ℝ => w r.toNNReal) t := by
    rw [e]; exact hK
  have hav' : ∀ u, 0 < tailGap (junctionL (fun r : ℝ => wα r.toNNReal) s)
      (junctionR (fun r : ℝ => wα r.toNNReal) s) (gb6Γ x u) := by
    rw [← hjL, ← hjR]; exact hav
  refine ⟨hHx ▸ htr, continuous_gb6WC x, htg.2, hgen.1, ?_, hK'⟩
  exact relClock_unbounded_of_endpoint hEnd hα hwα hwα0 hs hsH hγ hw hw0 htrγ hgen.1 (continuous_gb6WC x) htg.2
    hgen.2 hK' hav'

/-- **GB6's conditional-law half (hull form) from (d)** (conditional helper with a distinct name). -/
theorem gb6RelativeLawStatement_of_condDet (hcode : CanonicalDriverCodeStatement) (hC : CompleteSixteenDivStatement)
    (hEnd : GB6EndpointStatement) (hD : GB6CondDetStatement.{u}) : GB6RelativeLawStatement.{u} := by
  intro κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' htr hcf hadmL hadmR hcomp hfl hα s
  -- the chart field and the canonical driver code
  obtain ⟨Hc, hHcm, hHc⟩ := exists_measurable_chartField hfl hG.1 s (-1) (-(Real.pi * QuantumZipper.chiC κ))
    (QuantumZipper.chiC (16 / κ))
  have hHc' : ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      IsChartTransport (ownComponentChart (fun r : ℝ => Wα r.toNNReal ω) s) (-1)
        (-(Real.pi * QuantumZipper.chiC κ)) (QuantumZipper.chiC (16 / κ)) (h ω) (Hc ω) := by
    filter_upwards [hHc] with ω hω hs _ using hω hs
  obtain ⟨F, hF⟩ := hcode (16 / κ) 0 (by positivity)
  -- step (d)
  obtain ⟨𝒢, M, β, jL, jR, hM, hβ, hjL, hjR, hword, hR1, hdet⟩ :=
    hD κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' htr hcf hadmL hadmR hcomp hfl hα s Hc
      hHcm hHc' F hF
  have hβm : Measurable β := hβ.mono 𝒢.2 le_rfl
  have hMm : MeasurableSet M := 𝒢.2 _ hM
  -- the restart variable
  set X : Ω → GB6Space := fun ω => (Hc ω, F (β ω, Hc ω), (jL ω, jR ω)) with hXdef
  have hXm : Measurable X :=
    hHcm.prodMk ((hF.1.comp (hβm.prodMk hHcm)).prodMk ((hjL.mono 𝒢.2 le_rfl).prodMk (hjR.mono 𝒢.2 le_rfl)))
  -- the general restart kernel
  obtain ⟨K, hK, hlaw⟩ := exists_isMarkovKernel_map_eq_compProd P M hβm hXm
  have hker := restartKernel_isFlowLineDriver_of_codeMatch_canonical (ι := Unit) (P := P) (S := GB6Space)
    (w := id) (θ := fun _ => 0) (WC := fun _ => gb6WCl) (L := fun _ => gb6L) (F := fun _ => F)
    𝒢.2 hM hβ measurable_id hXm measurable_gb6Field
    (by filter_upwards [hword] with ω hω hωM using (hω hωM).1) hR1 (fun _ => measurable_gb6WCl)
    (fun _ => measurable_gb6L) (fun _ => continuousOn_gb6WCl) (fun _ => hF)
    (fun _ => by filter_upwards [hword] with ω hω hωM using isDriverCodeMatch_drvDec (hω hωM).2.2.2) K hlaw
  -- transfers to almost every conditional law
  have hadm : ∀ᵐ c ∂(P.restrict M).map β, IsGB6AdmData κ c :=
    (ae_map_iff hβm.aemeasurable (measurableSet_isGB6AdmData κ)).2
      ((ae_restrict_iff' hMm).2 (by filter_upwards [hword] with ω hω hωM using (hω hωM).2.1))
  have hgoodK : ∀ᵐ c ∂(P.restrict M).map β, ∀ᵐ x ∂(K c), IsGoodDrvCode (gb6Code x) := by
    have h := ae_ae_of_map_eq_compProd hMm hβm hXm hlaw (E := {p : BoundaryWord × GB6Space |
      IsGoodDrvCode (gb6Code p.2)}) (measurable_gb6Code.comp measurable_snd measurableSet_isGoodDrvCode)
      (by filter_upwards [hword] with ω hω hωM using (hω hωM).2.2.2)
    filter_upwards [h] with c hc using hc
  have hmatchK : ∀ᵐ c ∂(P.restrict M).map β, ∀ᵐ x ∂(K c),
      IsDriverCodeMatch (F (c, gb6Field x)) (fun t => gb6WCl t x) (gb6L x) := by
    have hE := measurableSet_driverCodeMatch (G := fun p : BoundaryWord × GB6Space => F (p.1, gb6Field p.2))
      (hF.1.comp (measurable_fst.prodMk (measurable_gb6Field.comp measurable_snd))) measurable_gb6WCl
      measurable_gb6L
    have h := ae_ae_of_map_eq_compProd hMm hβm hXm hlaw hE
      (by filter_upwards [hword] with ω hω hωM using isDriverCodeMatch_drvDec (hω hωM).2.2.2)
    filter_upwards [h] with c hc using hc
  have htailK : ∀ᵐ c ∂(P.restrict M).map β, ∀ᵐ x ∂(K c), IsGB6TailData κ c (gb6JL x) (gb6JR x) := by
    have hm : Measurable fun p : BoundaryWord × GB6Space => (p.1, gb6JL p.2, gb6JR p.2) :=
      measurable_fst.prodMk ((measurable_gb6JL.comp measurable_snd).prodMk (measurable_gb6JR.comp measurable_snd))
    have h := ae_ae_of_map_eq_compProd hMm hβm hXm hlaw (hm (measurableSet_isGB6TailData κ))
      (by filter_upwards [hword] with ω hω hωM using (hω hωM).2.2.1)
    filter_upwards [h] with c hc using hc
  have hall : ∀ᵐ c ∂(P.restrict M).map β, IsGB6ConditionalCounterflow κ c (K c) gb6Field gb6WC gb6Γ ∧
      ∀ᵐ x ∂(K c), IsGB6KernelGood x := by
    filter_upwards [hker, hadm, hgoodK, hmatchK, htailK] with c ⟨hcs, hcg, hcfl⟩ hca hcg' hcm hct
    exact gb6_kernel hκ hκ4 hC hF hcs hca hcg (hcfl ()) hcg' hcm hct
  -- the good event integrates back
  have hXgood : ∀ᵐ ω ∂P, ω ∈ M → IsGB6KernelGood (X ω) :=
    ae_mem_of_compProd_eq hMm hβm hXm hlaw measurableSet_isGB6KernelGood (by
      filter_upwards [hall] with c hc using hc.2)
  refine ⟨GB6Space, inferInstance, gb6Field, gb6WC, gb6Γ, M, β, X, K, isGB6RestartCoordinates, hMm, hβm, hXm, hK,
    hlaw, by filter_upwards [hall] with c hc using hc.1, ?_⟩
  -- the pathwise clause
  filter_upwards [hdet, hXgood, hword, hα, ae_driver_zero_continuousOn hfl, hcomp, ae_driver_zero_continuousOn hcf,
    hHc] with ω hdω hXω hwω hαω hpα hcω hpc hHcω hsζ hsH
  obtain ⟨hωM, hjLω, hjRω, hK'⟩ := hdω hsζ hsH
  have hWc : Continuous fun t => W t ω := by
    have := hpc.2
    rw [hcω.1] at this
    simp only [ENNReal.coe_lt_top, ofPred_true] at this
    exact continuousOn_univ.1 this
  have h := gb6_pathwise (x := X ω) hEnd hαω hpα.2 hpα.1 hsζ hsH hcω.2.1 hWc hpc.1 hcω.2.2 (hHcω hsζ) rfl
    (hXω hωM) (hwω hωM).2.2.2 hjLω hjRω hK'
  exact ⟨hωM, h⟩

/-- **GB6's conditional-law half** (`GB6RestartStatement`) from (d) (conditional helper). -/
theorem gb6RestartStatement_of_condDet (hcode : CanonicalDriverCodeStatement) (hC : CompleteSixteenDivStatement)
    (hEnd : GB6EndpointStatement) (hD : GB6CondDetStatement.{u}) : GB6RestartStatement.{u} :=
  gb6RestartStatement_of_relativeLaw (gb6RelativeLawStatement_of_condDet hcode hC hEnd hD)

/-- **GB6's first-contact assertion** from (d) (conditional helper). -/
theorem gb6FirstContactStatement_of_condDet (hcode : CanonicalDriverCodeStatement) (hC : CompleteSixteenDivStatement)
    (hEnd : GB6EndpointStatement) (hD : GB6CondDetStatement.{u}) : GB6FirstContactStatement.{u} :=
  gb6FirstContactStatement_of_relativeLaw (gb6RelativeLawStatement_of_condDet hcode hC hEnd hD)

/-- **GB6's conditional-law half (hull form)** from Theorem 1.2 (R44's word-measurable form), Theorem 1.3, Theorem 1.3
at
`16/κ`, the deterministic endpoint statement and (d) (conditional helper; the canonical driver codes are
PROVE-CONDDET's `Restart.canonicalDriverCodeStatement_of_param`). -/
theorem gb6RelativeLawStatement_of_param (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hC : CompleteSixteenDivStatement) (hEnd : GB6EndpointStatement)
    (hD : GB6CondDetStatement.{u}) : GB6RelativeLawStatement.{u} :=
  gb6RelativeLawStatement_of_condDet (canonicalDriverCodeStatement_of_param h12p h13) hC hEnd hD

end GB6

end Supp8

end InteractingSLE
