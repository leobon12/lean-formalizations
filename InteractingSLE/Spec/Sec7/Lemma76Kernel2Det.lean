/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma76Kernel2
import InteractingSLE.Spec.Restart.CondDet
import InteractingSLE.Spec.Supplement.G7Restart

/-!
# Lemma 7.6's restart kernel from the conditional-determination input

Packet PROVE-LEMMA76D, part (a). Specification §7.2, proof of Lemma 7.6 (pp. 267–270): "Retain the two labelled
histories and their canonical germs … The stopping-time local-set theorem gives their joint Gaussian conditional law
in each complementary component … Aux. lemma 59 consequently makes `p` an active tip in the joint unbounded component
`D` … After this coordinate change and addition of `θ₂χ`, the conditional field has the form `h⁰_D + M` … the
canonical-seed hypothesis of Aux. lemma 61" (the continuation is the flow line of the conditional field), and the
right-side heights `b_* = λ + (θ₂ − θ₁)χ`, `R = c + θ₂χ` (p. 269).

The restart kernel is a specialization of PROVE-RESTARTKERNEL's general restart kernel with PROVE-CONDDET's canonical
flow codes (`Restart.IsCanonicalFlowCode`, in-flight form): the restart variable is
`X = (chart field, F₂((β, 0), chart field), F₂((β, 0), chart field))`, so the continuation coordinate is a flow line
under every conditional law by construction (`ae_isFlowLine_of_codeMatch_canonical`), and the pathwise identity (Det)
ties it to the actual continuation read in G7's retained chart.

* `Lemma76CondDetStatement` (named input, **not proved**): the P-side content at a deterministic pair of stops — (R1)
  the conditional characteristic functional of the retained chart field, the right-side word (`IsRightSideWord`) and
  (Det) for the second continuation's canonical retained clock (`Supp7.canonRetPath`), in the in-flight form of
  PROVE-CONDDET's `RetainedCanonCondDetStatement` (one continuation, `θ₁ < θ₂ + π`, the right side identified);
* `mem_E_of_isDisjointPair`: a good configuration lies in G7's chart event;
* **`lemma76KernelLtStatement_of_condDet`**: `Lemma76KernelLtStatement` from `CanonicalFlowCodeStatement` and
  `Lemma76CondDetStatement` (the second continuation's clock relation from `isRetCont_snd`, the chart visit from
  `Lemma76Exit.exists_chartVisit_of_isForbiddenExit`, the admissibility from the word);
* **`lemma76Statement_of_condDet`**, `lemma76Statement_of_param`: Lemma 7.6 (both halves);
  `lemma76KernelStatement_of_condDet`: PROVE-LEMMA76C's named input.

**R43.** Canonical codes use Theorems 1.2–1.3. Lemma 7.6 feeds Lemma 7.7, W8's first contact and Aux. 70, i.e.
Theorem 1.5; none of Lemma 7.1, Proposition 7.3 or Lemma 7.5 uses it.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace Sec7

open LQGMetric Restart Supp7

/-- **Named input: the conditional law at a good disjoint pair, the right-side word and the determination
identity** (proof of Lemma 7.6, pp. 267–269; Lemma G7's retained conditional law, Aux. 59–61, Aux. 60 and the nested
comparison for the heights; Theorem W8's (Det), p. 541), in the form of PROVE-CONDDET's
`Restart.RetainedCanonCondDetStatement` for one continuation. Binders: those of `Lemma76KernelLtStatement` with
retained data `d` (deterministic stops `d.u`, `d.r`) agreeing almost surely with the two flow lines, and any canonical
flow code `F₂` for the angle `θ₂`. There are a sub-σ-algebra `𝒢`, a `𝒢`-event `M` and a `𝒢`-measurable datum `β` such
that:
* on `M` the datum is sorted;
* (R1) on `M`, conditionally on `𝒢`, the retained chart field `hd.chartField κ h` has the Gaussian characteristic
  functional of the datum;
* almost surely at a good configuration (`Lemma76Exit.IsDisjointPair`): `ω ∈ M`, the datum has the right-side heights
  in the retained chart (`IsRightSideWord` with the chart inverse `d.inv ω`), and (Det) the second continuation's
  canonical retained clock agrees, up to its lifetime, with the decoded canonical flow code of the chart field from
  `0`, whose lifetime is at least that of the clock. **Not proved in Lean.** -/
def Lemma76CondDetStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : RetData Ω) (hd : d.IsMeasGood),
      (∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
        (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) →
    ∀ F₂ : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (Sec2.Assembly.PCode × Sec2.Assembly.PCode) × ℝ≥0∞,
      IsCanonicalFlowCode κ θ₂ F₂ →
    ∃ (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ}) (M : Set Ω) (β : Ω → BoundaryWord),
      MeasurableSet[𝒢.1] M ∧ Measurable[𝒢.1] β ∧
      (∀ᵐ ω ∂P, ω ∈ M → (β ω).IsSorted) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
        P[fun ω' => Complex.exp (Complex.I * (hd.chartField κ h ω' φ : ℂ)) | 𝒢.1] ω = gaussCF (β ω) φ) ∧
      ∀ᵐ ω ∂P, Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        ω ∈ M ∧ IsRightSideWord κ θ₁ (η₁ ω) d.u (d.inv ω) (β ω) ∧
        canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 ≤
          (F₂ ((β ω, 0), hd.chartField κ h ω)).2 ∧
        ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤
            canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 →
          canonRetPath (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 s =
            decPath (F₂ ((β ω, 0), hd.chartField κ h ω)) s

/-- **A good configuration lies in G7's chart event** (as `RetData.IsMeasGood.mem_E_of_ordinary`, from the fields of
`IsDisjointPair`). -/
theorem mem_E_of_isDisjointPair {Ω : Type*} [MeasurableSpace Ω] {d : RetData Ω} (hd : d.IsMeasGood) {ω : Ω}
    (hG : ω ∈ d.G) {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} (ha₁ : ∀ s ≤ d.u, d.η₁ ω s = α s)
    (ha₂ : ∀ t ≤ d.r, d.η₂ ω t = β t) (hp : Lemma76Exit.IsDisjointPair α ζ₁ d.u β ζ₂ d.r) : ω ∈ d.E := by
  have e₁ : EqOn (d.η₁ ω) α (Icc 0 d.u) := fun s hs => ha₁ s hs.2
  have e₂ : EqOn (d.η₂ ω) β (Icc 0 d.r) := fun t ht => ha₂ t ht.2
  have htip : d.η₂ ω d.r = β d.r := ha₂ d.r le_rfl
  have hβα : β d.r ∉ α '' Icc 0 d.u := fun h =>
    Set.disjoint_left.1 hp.2.2.2.1 h ⟨d.r, ⟨zero_le, le_rfl⟩, rfl⟩
  have hE₀ : ω ∈ d.E₀ := ⟨⟨hG, by rw [mem_ofPred_eq, htip]; exact hp.2.2.1⟩, by
    rw [mem_ofPred_eq, htip, e₁.image_eq]; exact hβα⟩
  refine ⟨hE₀, ?_⟩
  show d.η₂ ω d.r ∈ closure (d.DOf d.E₀ ω)
  rw [hd.DOf_of_mem RetData.E₀_subset_G hE₀, activeDomain_congr_Icc e₁ e₂, htip]
  exact hp.2.2.2.2.1

/-- **Lemma 7.6's restart kernel at good configurations from the conditional-determination input.** The retained
data `d` at the stops `(a, r)` (`exists_retData_of_isFlowLine`), a canonical flow code `F₂`, the restart variable
`X = (Hc, F₂((β, 0), Hc), F₂((β, 0), Hc))` with `Hc` the retained chart field, and `K = condDistrib X β (P|M)`:
(R1) gives the GFF clause, the construction of `X` the flow-line clause; pathwise, at a good configuration with a
forbidden exit, `isRetCont_snd` and `isRetainedClock_canon` give the second continuation's clock relation, (Det) moves
it to the kernel's path coordinate, `Lemma76Exit.exists_chartVisit_of_isForbiddenExit` gives the chart visit beyond
the first tip, and the right-side word makes the visited point admissible. -/
theorem lemma76KernelLtStatement_of_condDet (hF : CanonicalFlowCodeStatement)
    (hD : Lemma76CondDetStatement.{u}) : Lemma76KernelLtStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ a r
  obtain ⟨d, hd, hdu, hdr, hag⟩ := exists_retData_of_isFlowLine hκ hκ4 hη₁ hη₂ a r
  subst hdu hdr
  obtain ⟨F₂, hF₂⟩ := hF κ θ₂ hκ hκ4
  obtain ⟨𝒢, M, β, hM, hβ, hsort, hR1, hpath⟩ :=
    hD κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag F₂ hF₂
  have hβm : Measurable β := hβ.mono 𝒢.2 le_rfl
  have hMm : MeasurableSet M := 𝒢.2 _ hM
  set Hc := hd.chartField κ h with hHc
  have hHcm : Measurable Hc := hd.measurable_chartField κ hh.1
  have hFm : Measurable fun ω => F₂ ((β ω, (0 : ℝ)), Hc ω) :=
    hF₂.1.comp ((hβm.prodMk measurable_const).prodMk hHcm)
  set X : Ω → RestartSpace := fun ω => (Hc ω, F₂ ((β ω, 0), Hc ω), F₂ ((β ω, 0), Hc ω)) with hXdef
  have hXm : Measurable X := hHcm.prodMk (hFm.prodMk hFm)
  obtain ⟨K, hK, hlaw⟩ := exists_isMarkovKernel_map_eq_compProd P M hβm hXm
  have hco := isRestartCoordinates_restartSpace
  -- (R1) under the kernel
  have hgff := ae_isGFFWithBoundaryData_of_condExp_word 𝒢.2 hM hβ measurable_id
    (by filter_upwards [hsort] with ω hω hωM; exact hω hωM) hXm (H := RestartSpace.field)
    measurable_fst hlaw hR1
  -- the continuation coordinate is the canonical flow of the chart field, by construction
  have hfl := ae_isFlowLine_of_codeMatch_canonical hMm hβm hXm hlaw measurable_id (x := fun _ => (0 : ℝ))
    measurable_const (H := RestartSpace.field) measurable_fst (Γ := RestartSpace.path₂) hco.2.2.2.2.1
    hco.2.2.1 hco.2.2.2.2.2.2 hF₂ hgff (Eventually.of_forall fun ω _ => ⟨rfl, fun t _ => rfl⟩)
  refine ⟨RestartSpace, inferInstance, RestartSpace.field, RestartSpace.path₂, RestartSpace.life₂, M, β, X, K,
    hco.1, hco.2.2.1, hco.2.2.2.2.1, hco.2.2.2.2.2.2, hMm, hβm, hXm, hK, hlaw, ?_, ?_⟩
  · filter_upwards [hgff, hfl] with c hc1 hc2
    exact ⟨hc1.2, hc2⟩
  · filter_upwards [hpath, hag, ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁,
      ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂] with ω hω hagω hp₁ hp₂ hpair hexit
    obtain ⟨hωM, hW, hlife, hdet⟩ := hω hpair
    obtain ⟨hG, a₁, a₂⟩ := hagω hpair.1 hpair.2.1
    have hωE := mem_E_of_isDisjointPair hd hG a₁ a₂ hpair
    obtain ⟨⟨x₀, hx₀⟩, hC⟩ := hd.isRetChart hωE
    have hφ : ∃ x₀ : ℝ, ∀ z, d.fwd ω z =
        ConformalImage.mapOut (fillH (prefixSet (d.η₁ ω) d.u (d.η₂ ω) d.r)) z - x₀ :=
      ⟨x₀, fun z => by
        show d.g ω z - d.shift ω = _
        rw [hx₀, RetData.g, RetData.K_of_mem hωE]⟩
    have e₁ : EqOn (d.η₁ ω) (η₁ ω) (Icc 0 d.u) := fun s hs => a₁ s hs.2
    have e₂ : EqOn (d.η₂ ω) (η₂ ω) (Icc 0 d.r) := fun t ht => a₂ t ht.2
    have hi₁ : d.η₁ ω '' Icc 0 d.u = η₁ ω '' Icc 0 d.u := e₁.image_eq
    have hdom : activeDomain (d.η₁ ω) d.u (d.η₂ ω) d.r = activeDomain (η₁ ω) d.u (η₂ ω) d.r :=
      activeDomain_congr_Icc e₁ e₂
    have htip : d.η₂ ω d.r = η₂ ω d.r := a₂ d.r le_rfl
    have hR₂ := isRetCont_snd (hd.good ω (RetData.E_subset_G hωE)) hC hφ hp₂ a₂ hpair.2.1
      (by rw [htip]; exact hpair.2.2.1)
      (by
        rw [htip, hi₁]
        exact fun h' => Set.disjoint_left.1 hpair.2.2.2.1 h' ⟨d.r, ⟨zero_le, le_rfl⟩, rfl⟩)
      (by rw [htip, hdom]; exact hpair.2.2.2.2.1)
    rw [hi₁] at hR₂
    set A := η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r with hA
    have hKc : IsCompact A := (Sec7.IsPathGood.isCompact_image_Icc hp₁ hpair.1.le).union
      (Sec7.IsPathGood.isCompact_image_Icc hp₂ hpair.2.1.le)
    have hDeq : d.D ω = H \ fillH A := by
      rw [hd.D_of_mem hωE, hdom]
      exact Lemma76Exit.unboundedPart_eq hKc.isClosed
    have hclk := isRetainedClock_canon hR₂.shift_zero rfl hDeq
    have hclk' : IsRetainedClock (η₂ ω) (ζ₂ ω) d.r A (d.inv ω) (RestartSpace.path₂ (X ω))
        (RestartSpace.life₂ (X ω)) :=
      hclk.mono hlife fun s hs => (hdet s hs).symm
    obtain ⟨e, v, he, hex⟩ := hexit
    obtain ⟨s, hsU, y, hΓy, hψy, w, hψw, hwy⟩ := Lemma76Exit.exists_chartVisit_of_isForbiddenExit hR₂ hclk'
      (hco.2.2.2.2.2.2 (X ω)) (Sec7.IsPathGood.continuousOn_Icc hp₁ hpair.1.le)
      (Sec7.IsPathGood.injOn_Icc hp₁ hpair.1.le) isCompact_lowerArc.isClosed
      (Set.disjoint_left.2 fun z hz hzH => notMem_lowerArc_of_mem_H hzH hz) hex he
      (by rw [← Lemma76Exit.unboundedPart_eq hKc.isClosed]; exact hpair.2.2.2.2.2)
    obtain ⟨hy0, hadm⟩ := isAdmissibleRight_of_isRightSideWord hκ hκ4 hθ hW hψw hwy hex.2.1 hψy
    exact ⟨hωM, s, hsU, y, hy0, hΓy, hadm⟩

/-- **Lemma 7.6 (`Lemma76Statement`, both halves) from canonical flow codes and the conditional-determination
input.** -/
theorem lemma76Statement_of_condDet (hF : CanonicalFlowCodeStatement) (hD : Lemma76CondDetStatement.{u}) :
    Lemma76Statement.{u} :=
  lemma76Statement_of_kernelLt (lemma76KernelLtStatement_of_condDet hF hD)

/-- **Lemma 7.6 from Theorems 1.2 (measurable in the word) and 1.3 and the conditional-determination input**
(the canonical flow codes by `canonicalFlowCodeStatement_of_param`). -/
theorem lemma76Statement_of_param (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hD : Lemma76CondDetStatement.{u}) : Lemma76Statement.{u} :=
  lemma76Statement_of_condDet (canonicalFlowCodeStatement_of_param h12p h13) hD

/-- **PROVE-LEMMA76C's `Lemma76KernelStatement` from canonical flow codes and the conditional-determination
input.** -/
theorem lemma76KernelStatement_of_condDet (hF : CanonicalFlowCodeStatement) (hD : Lemma76CondDetStatement.{u}) :
    Lemma76KernelStatement.{u} :=
  lemma76KernelStatement_of_kernelLt (lemma76KernelLtStatement_of_condDet hF hD)

end Sec7

end InteractingSLE
