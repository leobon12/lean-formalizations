/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSeedOpen
import InteractingSLE.Spec.Restart.DomainMarkovMean
import InteractingSLE.Spec.Restart.DomainMarkovAux79Stop
import InteractingSLE.Spec.Sec7.PocketTraversalMeas
import InteractingSLE.WangWu.ReverseContactMartFilt2

/-!
# Theorem 1.3's pocket word: the coupling clause of the pocket traversal from the field in the pocket chart

Packet PROVE-STRIPSYS26. Specification §7.4, Aux. lemma 125's proof (`source/spec/p385-432.md` L234–L250, p. 396:
"*The canonical law survives the exterior reveal.* Condition on `ℰ`. … Aux. lemma 124 preserves the actual canonical
active mean at `T(S)`. The marked local-set law gives its active Dirichlet covariance. Both the mean and that covariance
depend only on `Θ` and the relative stopped history. The tower property therefore leaves exactly this Gaussian kernel
when the extra ambient history and germs are forgotten."), Aux. lemma 130's proof (p. 412: "restricting to its
measurable event `F_r` does not change that conditional law") and Lemma 7.25's proof (pp. 413–414).

STRIPSYS20's named input `PocketWordAssembly.PocketCouplingInput` asks, on every walls-measurable word-shape event `A`
and for every walls-measurable Jordan coordinate `ψ` of the change pocket, for a random field on the subtype `A`
(under `condSub P A`) satisfying the conditional-law clause `IsCouplingCharFun` of the pocket word along the traversal,
at every stopping time of the usual augmentation of its relative history filtration. This file derives it from the
field-level statement in the **physical frame on the ambient space** (`PocketChartInput`): a pocket chart with forward
map `ψ` (Aux. lemma 119's measurable lift), and at every fixed relative capacity time `q`

* the **physical kernel** (`PocketKernel`, Aux. lemma 124 / R.5): given σ-algebras `𝓜_q` containing the walls and the
  traversal's prefix events, the field is Gaussian on the active pocket domain `inv(ℍ ∖ K_q)` with some mean `M_q` and
  the zero-boundary covariance of that domain;
* the **mean identification** (`PocketMeanIdent`, Aux. lemmas 119–122): the chart transport of `M_q` is the canonical
  coupling mean of the pocket word at the geometric force coordinates.

## Main results

* `condExp_condSub_ae_eq`: conditional expectations under `condSub P A` for `A ∈ 𝓜` are those under `P`, on `A`;
* `isForceReg_segDriver`, **`isCouplingCharFun_chartTransport`**: the coupling clause of the field transported into a
  random chart from the kernel and the mean identification at fixed times (tower step and fixed times to stopping
  times, through `Restart.DomainMarkov.Mean.hasSafeLaw_chartTransport` and
  `Restart.DomainMarkov.Aux79.isCouplingCharFun_of_hasSafeLaw`);
* `locPrefixSigma`, `comap_locPrefixSigma`: the relative history σ-algebras on the ambient space;
* `IsPocketChartOn`, `PocketKernel`, `PocketMeanIdent`, `PocketChartLaw` (definitions of the inputs);
* **`pocketCouplingClause_of_chartLaw`**: `PocketCouplingClause` on the subtype from the chart law on the ambient space;
* `travAll`, `marksRAll`, `marksL2All`, `marksL1All`, `PocketChartInput`; `measurable_marks`,
  `measurable_indicator_apply` (the marks and the fixed-point values of any walls-measurable Jordan coordinate);
* **`pocketCouplingInput_of_chartInput`**: `PocketCouplingInput` from `PocketChartInput` (bounded change pocket).

The pocket opening at the flow seed and the assembly of hPW are in `PocketCouplingInf`. Conditional helpers; they
replace no source theorem. Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`,
`Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketCoupling

open PocketTraversal PocketAdapt PhaseSel Lemma71C

section Sub

variable {Ω : Type*} {𝓜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {A : Set Ω}

omit 𝓜 in
/-- Set integrals over a trace event under the conditional law `condSub P A`. -/
theorem setIntegral_condSub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (hA : MeasurableSet A)
    {s : Set Ω} (hs : MeasurableSet s) (g : Ω → E) :
    ∫ ω in (Subtype.val ⁻¹' s : Set A), g ω ∂(condSub P A) = (P A)⁻¹.toReal • ∫ ω in s ∩ A, g ω ∂P := by
  rw [condSub, Measure.restrict_smul, integral_smul_measure]
  congr 1
  rw [← integral_indicator (measurable_subtype_coe hs), ← integral_indicator (hs.inter hA)]
  have e : (Subtype.val ⁻¹' s).indicator (fun ω : A => g (ω : Ω)) = fun ω : A => s.indicator g (ω : Ω) := by
    funext ω
    by_cases h : (ω : Ω) ∈ s <;> simp [h]
  rw [e, integral_subtype_comap hA, ← integral_indicator hA]
  congr 1
  funext ω
  by_cases h1 : ω ∈ s <;> by_cases h2 : ω ∈ A <;> simp [h1, h2]

omit 𝓜 in
/-- An integrable function stays integrable under the conditional law given an event. -/
theorem integrable_condSub {E : Type*} [NormedAddCommGroup E] (hA : MeasurableSet A) (h0 : P A ≠ 0)
    {X : Ω → E} (hX : Integrable X P) : Integrable (fun ω : A => X ω) (condSub P A) := by
  have h := (integrableOn_iff_comap_subtypeVal hA).1 (hX.integrableOn (s := A))
  exact h.smul_measure (ENNReal.inv_ne_top.2 h0)

/-- **Conditional expectations under the conditional law given an event of the conditioning σ-algebra**: for
`A ∈ 𝓜` of positive probability, `E_{P(·|A)}[X | 𝓜 ∩ A] = E_P[X | 𝓜]` almost surely on `A` (spec p. 412: "restricting
to its measurable event `F_r` does not change that conditional law"). -/
theorem condExp_condSub_ae_eq [IsFiniteMeasure P] (h𝓜 : 𝓜 ≤ mΩ)
    (hA : MeasurableSet[𝓜] A) (h0 : P A ≠ 0) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {X : Ω → E} (hX : Integrable X P) :
    (condSub P A)[(fun ω : A => X ω) | MeasurableSpace.comap Subtype.val 𝓜] =ᵐ[condSub P A]
      fun ω : A => (P[X | 𝓜]) ω := by
  have hAm : MeasurableSet A := h𝓜 _ hA
  have hle : MeasurableSpace.comap Subtype.val 𝓜 ≤ (inferInstance : MeasurableSpace A) :=
    MeasurableSpace.comap_mono h𝓜
  have : IsProbabilityMeasure (condSub P A) := isProbabilityMeasure_condSub hAm h0
  have : SigmaFinite ((condSub P A).trim hle) := inferInstance
  have hint : Integrable (fun ω : A => X ω) (condSub P A) := integrable_condSub hAm h0 hX
  have hintc : Integrable (fun ω : A => (P[X | 𝓜]) ω) (condSub P A) :=
    integrable_condSub hAm h0 integrable_condExp
  refine (ae_eq_condExp_of_forall_setIntegral_eq hle hint (fun s _ _ => hintc.integrableOn)
    (fun s hs _ => ?_) ?_).symm
  · obtain ⟨s', hs', rfl⟩ := hs
    rw [setIntegral_condSub hAm (h𝓜 _ hs'), setIntegral_condSub hAm (h𝓜 _ hs'),
      setIntegral_condExp h𝓜 hX (hs'.inter hA)]
  · exact (stronglyMeasurable_condExp.comp_measurable (comap_measurable Subtype.val)).aestronglyMeasurable

end Sub


section Bridge

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {nL nR : ℕ}

omit mΩ in
/-- The pathwise regularity of the canonical driver of a driven curve and its geometric force coordinates. -/
theorem isForceReg_segDriver {γ : Ω → ℝ → ℂ} (hγ : ∀ ω, IsDrivenCurve (γ ω)) (xL : Ω → Fin nL → ℝ)
    (xR : Ω → Fin nR → ℝ) (ω : Ω) :
    Restart.DomainMarkov.Aux79.IsForceReg (fun t ω => segDriver (γ ω) t)
      (PocketTraversal.geomLW (fun t ω => segDriver (γ ω) t) xL)
      (PocketTraversal.geomRW (fun t ω => segDriver (γ ω) t) xR) (fun ω => capLife (γ ω)) ω := by
  have hc : ∀ ω, ContinuousOn (fun t => segDriver (γ ω) t) {t : ℝ≥0 | (t : WithTop ℝ≥0) < capLife (γ ω)} :=
    fun ω => (hγ ω).segDriver_spec.2.1
  refine ⟨(hγ ω).segDriver_spec.1, (hγ ω).segDriver_spec.2.1, fun i => ?_, fun j => ?_, fun t ht => ⟨fun i => ?_,
    fun j => ?_⟩⟩
  · exact PocketMartLife.continuousOn_geomLW_of_lt (T := fun ω => capLife (γ ω)) hc xL i ω
  · exact PocketMartLife.continuousOn_geomRW_of_lt (T := fun ω => capLife (γ ω)) hc xR j ω
  · exact PocketMartLife.geomLW_le_of_lt (W := fun t ω => segDriver (γ ω) t) (ω := ω) (hc ω) ht xL i
  · exact PocketMartLife.le_geomRW_of_lt (W := fun t ω => segDriver (γ ω) t) (ω := ω) (hc ω) ht xR j

/-- **The coupling clause of the field transported into a random chart, from the physical kernel and the mean
identification at fixed capacity times** (Aux. lemma 125's proof, p. 396: "Aux. lemma 124 preserves the actual
canonical active mean at `T(S)`. The marked local-set law gives its active Dirichlet covariance. Both the mean and that
covariance depend only on `Θ` and the relative stopped history. The tower property therefore leaves exactly this
Gaussian kernel when the extra ambient history and germs are forgotten."). Let `γ` be a random driven curve whose
prefixes are adapted to `𝓗`, with `𝓗₀`-measurable marks, and `c` a random conformal chart known at time `0`. If at
every fixed capacity time `q`, given some `𝓜_q ⊇ 𝓗_q`, the physical field `h` is Gaussian on the chart preimage
`inv(ℍ ∖ K_q)` of the active domain with mean `M_q` and the zero-boundary covariance of that domain, and the chart
transport of `M_q` is the canonical coupling mean of the word at the geometric force coordinates, then the transported
field `chartTransport c 1 a k h` satisfies the conditional-law clause (`IsCouplingCharFun`) at every stopping time of
the usual augmentation of `𝓗`. Route: `Mean.hasSafeLaw_chartTransport` (the tower step in set-integral form) and
`Aux79.isCouplingCharFun_of_hasSafeLaw` (fixed times to stopping times, from pathwise regularity). -/
theorem isCouplingCharFun_chartTransport (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {𝓗 : Filtration ℝ≥0 mΩ}
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω, IsDrivenCurve (γ ω)) (hpre : IsPrefixAdapted 𝓗 γ)
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} (hxL : Measurable[𝓗 0] xL) (hxR : Measurable[𝓗 0] xR)
    {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝓗 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓗 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓗 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (a k : ℝ) (𝓜 : ℝ≥0 → MeasurableSpace Ω) (h𝓗𝓜 : ∀ q, 𝓗 q ≤ 𝓜 q) (h𝓜 : ∀ q, 𝓜 q ≤ mΩ)
    (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (hcond : ∀ (q : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, (q : ℝ≥0∞) < capLife (γ ω) →
      tsupport φ ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q) →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝓜 q] ω =
        Complex.exp (Complex.I * (M q ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q))
            φ φ : ℝ) : ℂ)))
    (hmean : ∀ (q : ℝ≥0) (ψ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P,
      ω ∈ Restart.DomainMarkov.avoidSet (fun t ω => segDriver (γ ω) t) (fun ω => capLife (γ ω)) ψ q →
      Chart.chartTransport (hc ω) 1 a k (M q ω) ψ =
        ∫ z, couplingMean κ (fun s : ℝ => segDriver (γ ω) s.toNNReal) q
          (Restart.DomainMarkov.bheProc κ ρL ρR (fun t ω => segDriver (γ ω) t)
            (PocketTraversal.geomLW (fun t ω => segDriver (γ ω) t) xL)
            (PocketTraversal.geomRW (fun t ω => segDriver (γ ω) t) xR) ω q) z * ψ z) :
    Coupling.MartMeans.IsCouplingCharFun κ ρL ρR P (usualAugmentation 𝓗 P) (fun t ω => segDriver (γ ω) t)
      (PocketTraversal.geomLW (fun t ω => segDriver (γ ω) t) xL)
      (PocketTraversal.geomRW (fun t ω => segDriver (γ ω) t) xR) (fun ω => capLife (γ ω))
      (fun ω => Chart.chartTransport (hc ω) 1 a k (h ω)) := by
  have hWa := PocketTraversal.adaptedBefore_segDriver_of_isDrivenCurve hγ hpre
  have hlaw := Restart.DomainMarkov.Mean.hasSafeLaw_chartTransport (𝒢 := 𝓗 0) (P := P) (κ := κ) (ρL := ρL)
    (ρR := ρR) (W := fun t ω => segDriver (γ ω) t) (VL := PocketTraversal.geomLW (fun t ω => segDriver (γ ω) t) xL)
    (VR := PocketTraversal.geomRW (fun t ω => segDriver (γ ω) t) xR) (ζ := fun ω => capLife (γ ω))
    (𝓗 := 𝓗) (F := univ) le_rfl hc hdom hfwd hliftm hliftc hh a k 𝓜 h𝓗𝓜 h𝓜 M
    (fun q φ => by filter_upwards [hcond q φ] with ω hω _ using hω)
    (fun q ψ => by filter_upwards [hmean q ψ] with ω hω _ using hω)
    (ae_of_all _ fun ω _ => ⟨(hγ ω).segDriver_spec.2.1, (hγ ω).segDriver_spec.1⟩)
  have hX : Measurable fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) :=
    Chart.measurable_chartTransport_random' hc (fun z => 𝓗.le 0 _ (hdom z))
      (fun z => (hfwd z).mono (𝓗.le 0) le_rfl) (fun z => (hliftm z).mono (𝓗.le 0) le_rfl) hliftc hh 1 a k
  exact Restart.DomainMarkov.Aux79.isCouplingCharFun_of_hasSafeLaw _
    (fun ψ => (LQGMetric.measurable_distOn_apply ψ).comp hX) hlaw
    (ae_of_all _ (isForceReg_segDriver hγ xL xR)) (ae_of_all _ fun ω hω => absurd (mem_univ ω) hω) hWa
    (fun i => PocketPhaseMeans.adaptedBefore_geomLW (fun ω => (hγ ω).segDriver_spec.2.1) hWa hxL i)
    (fun j => PocketPhaseMeans.adaptedBefore_geomRW (fun ω => (hγ ω).segDriver_spec.2.1) hWa hxR j)

end Bridge


/-! ### The named inputs on the ambient space -/

section Inputs

variable {Ω : Type*}

/-- **The walls' information and the prefix events of `γ` on `A`** up to capacity time `s`: the trace on `A` of
this σ-algebra is the relative history σ-algebra `prefixSigma` of the traversal on the subtype `A`
(`comap_locPrefixSigma`). -/
@[instance_reducible] def locPrefixSigma (𝓦 : MeasurableSpace Ω) (A : Set Ω) (γ : Ω → ℝ → ℂ) (s : ℝ≥0) :
    MeasurableSpace Ω :=
  𝓦 ⊔ MeasurableSpace.generateFrom {E | ∃ r ≤ s, ∃ n k, E = A ∩ prefixEvent γ r n k}

theorem comap_locPrefixSigma (𝓦 : MeasurableSpace Ω) (A : Set Ω) (γ : Ω → ℝ → ℂ) (s : ℝ≥0) :
    MeasurableSpace.comap (Subtype.val : A → Ω) (locPrefixSigma 𝓦 A γ s) =
      prefixSigma (MeasurableSpace.comap Subtype.val 𝓦) (fun ω : A => γ ω) s := by
  rw [locPrefixSigma, prefixSigma, MeasurableSpace.comap_sup, MeasurableSpace.comap_generateFrom]
  congr 2
  ext E
  constructor
  · rintro ⟨_, ⟨r, hr, n, k, rfl⟩, rfl⟩
    refine ⟨r, hr, n, k, ?_⟩
    ext ω
    simp only [mem_preimage, mem_inter_iff, Subtype.coe_prop, true_and]
    rfl
  · rintro ⟨r, hr, n, k, rfl⟩
    refine ⟨_, ⟨r, hr, n, k, rfl⟩, ?_⟩
    ext ω
    simp only [mem_preimage, mem_inter_iff, Subtype.coe_prop, true_and]
    rfl

/-- **The pocket chart** on `A` (Aux. lemma 119: "There is a measurably selected derivative-logarithm lift for a
conformal chart `φ : C → ℍ`"): on `A`, a conformal chart of the pocket `C` whose forward map is the Jordan
coordinate `ψ`, with a lift continuous on `C` and measurable for the walls' σ-algebra at every fixed point. -/
def IsPocketChartOn (𝓦 : MeasurableSpace Ω) (A : Set Ω) (C : Ω → Set ℂ) (ψ : Ω → ℂ → ℂ) (c : Ω → Chart) :
    Prop :=
  (∀ ω ∈ A, (c ω).IsConformal ∧ ((c ω).dom : Set ℂ) = C ω ∧ EqOn (c ω).1 (ψ ω) (C ω) ∧
    ContinuousOn (c ω).2.2 (c ω).dom) ∧
  ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => (c ω).2.2 z)

/-- **The physical pocket kernel** (Aux. lemma 124 at the relative capacity times; R.5; Aux. lemma 125's proof,
p. 396): there are σ-algebras `𝓜_q ≤ mΩ` containing the walls' information and the traversal's prefix events on `A`
up to relative capacity time `q` (in the source: the marked union of the walls and the counterflow stopped at the
ambient stopping time `T(q)`, with its germ and stopped histories), and random distributions `M_q`, such that almost
surely on `A ∩ {q < capLife γ}`, for every test function `φ` supported in the chart preimage `inv(ℍ ∖ K_q)` of the
active domain (the active component of `C ∖ η[0, T(q)]`), the conditional characteristic function of `h(φ)` given
`𝓜_q` is Gaussian with mean `M_q(φ)` and the zero-boundary variance of that domain. -/
def PocketKernel (𝓦 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (γ : Ω → ℝ → ℂ) (c : Ω → Chart) (h : Ω → DistOn upperHalfPlaneOpens) (𝓜 : ℝ≥0 → MeasurableSpace Ω)
    (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens) : Prop :=
  (∀ q, 𝓜 q ≤ mΩ) ∧ (∀ q, locPrefixSigma 𝓦 A γ q ≤ 𝓜 q) ∧
  ∀ (q : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
    tsupport φ ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q) →
    P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝓜 q] ω =
      Complex.exp (Complex.I * (M q ω φ : ℂ) -
        (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q))
          φ φ : ℝ) : ℂ))

/-- **The pocket mean identification** (Aux. lemmas 119–122, Lemma 7.25's proof, pp. 413–414: "The contained
two-arc mean theorem applies at all enlarged stopping times with the exact inherited lifts … the exposed-side
discrepancies have the one common even-lattice form required by Aux. lemma 122 … that lemma identifies the canonical
stopped driving equation"): almost surely on `A`, at every fixed relative capacity time `q` and for every test
function `ψ` off the relative hull, the chart transport `chartTransport c 1 a k M_q` (the mean read in the pocket
coordinate with the coordinate rule (1.4)) is the canonical coupling mean of the word `(ρL; ρR)` at the geometric force
coordinates of the marks `xL`, `xR` along the canonical driver of `γ`. -/
def PocketMeanIdent (κ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) [MeasurableSpace Ω] (P : Measure Ω)
    (A : Set Ω) (γ : Ω → ℝ → ℂ) (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ) (c : Ω → Chart) (a k : ℝ)
    (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∀ (q : ℝ≥0) (ψ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ A →
    ω ∈ Restart.DomainMarkov.avoidSet (fun t ω => segDriver (γ ω) t) (fun ω => capLife (γ ω)) ψ q →
    ∀ hc : (c ω).IsConformal, Chart.chartTransport hc 1 a k (M q ω) ψ =
      ∫ z, couplingMean κ (fun s : ℝ => segDriver (γ ω) s.toNNReal) q
        (Restart.DomainMarkov.bheProc κ ρL ρR (fun t ω => segDriver (γ ω) t)
          (PocketTraversal.geomLW (fun t ω => segDriver (γ ω) t) xL)
          (PocketTraversal.geomRW (fun t ω => segDriver (γ ω) t) xR) ω q) z * ψ z

/-- **The pocket chart law** (the field-level content of `PocketCouplingClause`, in the physical frame): a pocket
chart of `C` with forward map `ψ` (`IsPocketChartOn`), frame constants `a`, `k`, the physical kernel (`PocketKernel`)
and the mean identification (`PocketMeanIdent`). -/
def PocketChartLaw (κ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (𝓦 : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω) (γ : Ω → ℝ → ℂ) (xL : Ω → Fin nL → ℝ)
    (xR : Ω → Fin nR → ℝ) (C : Ω → Set ℂ) (ψ : Ω → ℂ → ℂ) (h : Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∃ (c : Ω → Chart) (a k : ℝ) (𝓜 : ℝ≥0 → MeasurableSpace Ω) (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens),
    IsPocketChartOn 𝓦 A C ψ c ∧ PocketKernel 𝓦 P A γ c h 𝓜 M ∧ PocketMeanIdent κ ρL ρR P A γ xL xR c a k M

end Inputs


/-! ### The coupling clause on the subtype -/

section Clause

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {nL nR : ℕ}

/-- **The pocket coupling clause from the pocket chart law**: on a walls-measurable event `A` of positive
probability, for a random curve `γ` driven on `A`, walls-measurable marks on `A`, and a Jordan coordinate `ψ` of
the random pocket `C` measurable for the walls at fixed points, the pocket chart law on the ambient space gives the
coupling clause `PocketCouplingClause` of the traversal under the conditional law `condSub P A`, for the field
`chartTransport c 1 a k h`. -/
theorem pocketCouplingClause_of_chartLaw {κ : ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} (h𝓦 : 𝓦 ≤ mΩ)
    {A : Set Ω} (hA : MeasurableSet[𝓦] A) (hPA : 0 < P A) {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω))
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    (hxL : Measurable[MeasurableSpace.comap Subtype.val 𝓦] fun ω : A => xL ω)
    (hxR : Measurable[MeasurableSpace.comap Subtype.val 𝓦] fun ω : A => xR ω)
    {C : Ω → Set ℂ} (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    {ψ : Ω → ℂ → ℂ} (hψm : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => ψ ω z))
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (hlaw : PocketChartLaw κ ρL ρR 𝓦 P A γ xL xR C ψ h) :
    PocketWordAssembly.PocketCouplingClause κ ρL ρR (MeasurableSpace.comap Subtype.val 𝓦) (condSub P A)
      (fun ω : A => γ ω) (fun ω : A => xL ω) (fun ω : A => xR ω) := by
  intro h𝓔 hm
  obtain ⟨c, a, k, 𝓜, M, ⟨hcA, hlm⟩, ⟨h𝓜, h𝓜pre, hK⟩, hmean⟩ := hlaw
  have hAm : MeasurableSet A := h𝓦 _ hA
  have : IsProbabilityMeasure (condSub P A) := isProbabilityMeasure_condSub hAm hPA.ne'
  set 𝓗 := prefixFilt (MeasurableSpace.comap Subtype.val 𝓦) h𝓔 (fun ω : A => γ ω) hm with h𝓗def
  have hpre : IsPrefixAdapted 𝓗 (fun ω : A => γ ω) := isPrefixAdapted_prefixFilt h𝓔 hm
  have h0 : MeasurableSpace.comap Subtype.val 𝓦 ≤ 𝓗 0 := le_prefixFilt_zero h𝓔 hm
  have hcA' : ∀ ω : A, (c ω).IsConformal := fun ω => (hcA ω ω.2).1
  have h𝓗𝓜 : ∀ q, 𝓗 q ≤ MeasurableSpace.comap Subtype.val (𝓜 q) := fun q => by
    show prefixSigma _ (fun ω : A => γ ω) q ≤ _
    rw [← comap_locPrefixSigma]
    exact MeasurableSpace.comap_mono (h𝓜pre q)
  have h𝓜' : ∀ q, MeasurableSpace.comap (Subtype.val : A → Ω) (𝓜 q) ≤ (inferInstance : MeasurableSpace A) :=
    fun q => MeasurableSpace.comap_mono (h𝓜 q)
  have hA𝓜 : ∀ q, MeasurableSet[𝓜 q] A := fun q =>
    h𝓜pre q _ ((le_sup_left : 𝓦 ≤ locPrefixSigma 𝓦 A γ q) _ hA)
  have hdomeq : ∀ ω : A, ∀ z, z ∈ (c ω).dom ↔ z ∈ C ω := fun ω z => by
    rw [← SetLike.mem_coe, (hcA ω ω.2).2.1]
  have hset : ∀ z, {ω : A | z ∈ (c ω).dom} = Subtype.val ⁻¹' {ω | ω ∈ A ∧ z ∈ C ω} := fun z => by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage, hdomeq ω z, ω.2, true_and]
  have hdom : ∀ z, MeasurableSet[𝓗 0] {ω : A | z ∈ (c ω).dom} := fun z => by
    rw [hset z]
    exact h0 _ ⟨_, hCm z, rfl⟩
  have hind : ∀ {β : Type} [Zero β] [MeasurableSpace β] (z : ℂ) (f : Ω → ℂ → β),
      Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => f ω z) →
      Measurable[𝓗 0] ({ω : A | z ∈ (c ω).dom}.indicator fun ω => f ω z) := fun z f hf => by
    have e : ({ω : A | z ∈ (c ω).dom}.indicator fun ω => f ω z) =
        ({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => f ω z) ∘ Subtype.val := by
      rw [hset z]
      rfl
    rw [e]
    exact (hf.comp (comap_measurable Subtype.val)).mono h0 le_rfl
  have hfwd : ∀ z, Measurable[𝓗 0] ({ω : A | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z) := fun z => by
    have e : ({ω : A | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z) =
        ({ω : A | z ∈ (c ω).dom}.indicator fun ω => ψ ω z) := by
      funext ω
      by_cases hz : ω ∈ {ω : A | z ∈ (c ω).dom}
      · rw [indicator_of_mem hz, indicator_of_mem hz, (hcA ω ω.2).2.2.1 ((hdomeq ω z).1 hz)]
      · rw [indicator_of_notMem hz, indicator_of_notMem hz]
    rw [e]
    exact hind z ψ (hψm z)
  have hliftm : ∀ z, Measurable[𝓗 0] ({ω : A | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z) := fun z =>
    hind z (fun ω => (c ω).2.2) (hlm z)
  have hliftc : ∀ ω : A, ContinuousOn (c ω).2.2 (c ω).dom := fun ω => (hcA ω ω.2).2.2.2
  have hh' : Measurable fun ω : A => h ω := hh.comp measurable_subtype_coe
  have hcond : ∀ (q : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ (ω : A) ∂(condSub P A),
      (q : ℝ≥0∞) < capLife (γ ω) →
      tsupport φ ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q) →
      condExp (MeasurableSpace.comap Subtype.val (𝓜 q)) (condSub P A)
          (fun ω : A => Complex.exp (Complex.I * (h ω φ : ℂ))) ω =
        Complex.exp (Complex.I * (M q ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q))
            φ φ : ℝ) : ℂ)) := fun q φ => by
    have hint : Integrable (fun ω => Complex.exp (Complex.I * (h ω φ : ℂ))) P :=
      GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp hh)
    filter_upwards [condExp_condSub_ae_eq (h𝓜 q) (hA𝓜 q) hPA.ne' hint, ae_condSub_of_ae hAm (hK q φ)]
      with ω h1 h2 hq hs
    rw [h1]
    exact h2 ω.2 hq hs
  have hmean' : ∀ (q : ℝ≥0) (ψ' : TestOn upperHalfPlaneOpens), ∀ᵐ (ω : A) ∂(condSub P A),
      ω ∈ Restart.DomainMarkov.avoidSet (fun t (ω : A) => segDriver (γ ω) t) (fun ω : A => capLife (γ ω)) ψ' q →
      Chart.chartTransport (hcA' ω) 1 a k (M q ω) ψ' =
        ∫ z, couplingMean κ (fun s : ℝ => segDriver (γ ω) s.toNNReal) q
          (Restart.DomainMarkov.bheProc κ ρL ρR (fun t (ω : A) => segDriver (γ ω) t)
            (PocketTraversal.geomLW (fun t (ω : A) => segDriver (γ ω) t) fun ω : A => xL ω)
            (PocketTraversal.geomRW (fun t (ω : A) => segDriver (γ ω) t) fun ω : A => xR ω) ω q) z * ψ' z :=
    fun q ψ' => by
      filter_upwards [ae_condSub_of_ae hAm (hmean q ψ')] with ω hω hav
      exact hω ω.2 hav (hcA' ω)
  have hcf := isCouplingCharFun_chartTransport κ ρL ρR (fun ω : A => hγ ω ω.2) hpre (hxL.mono h0 le_rfl)
    (hxR.mono h0 le_rfl) hcA' hdom hfwd hliftm hliftc hh' a k (fun q => MeasurableSpace.comap Subtype.val (𝓜 q))
    h𝓗𝓜 h𝓜' (fun q ω => M q ω) hcond hmean'
  have hX : Measurable fun ω : A => Chart.chartTransport (hcA' ω) 1 a k (h ω) :=
    Chart.measurable_chartTransport_random' hcA' (fun z => 𝓗.le 0 _ (hdom z))
      (fun z => (hfwd z).mono (𝓗.le 0) le_rfl) (fun z => (hliftm z).mono (𝓗.le 0) le_rfl) hliftc hh' 1 a k
  refine ⟨fun ω => Chart.chartTransport (hcA' ω) 1 a k (h ω), fun φ => ?_, hcf⟩
  exact WangWu.integrable_apply_of_isCouplingCharFun_of_bounded hcf
    (ae_of_all _ fun ω => ⟨PocketPhaseMeans.capLife_pos (hγ ω ω.2), (hγ ω ω.2).segDriver_spec.2.1,
      (hγ ω ω.2).segDriver_spec.1⟩) φ ((LQGMetric.measurable_distOn_apply φ).comp hX)

end Clause


/-! ### The change pocket -/

section PocketDefs

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks

variable {Ω : Type*}

/-- The erased counterflow traversal of the change pocket in the Jordan coordinate `ψ`, read on all of `Ω`. -/
def travAll (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) : Ω → ℝ → ℂ :=
  fun ω => cfTraversal (R ω) (L ω) r (η ω) (ψ ω)

/-- The right marks, read on all of `Ω`. -/
def marksRAll (L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (ψ : Ω → ℂ → ℂ) : Ω → Fin 2 → ℝ :=
  fun ω => ![0, (ψ ω (cfPt (toDisc (realPath (L ω)) (discTime r)))).re]

/-- The left marks with the right wall's change point, read on all of `Ω`. -/
def marksL2All (R : Ω → ℝ≥0 → ℂ) (ψ : Ω → ℂ → ℂ) : Ω → Fin 2 → ℝ :=
  fun ω => ![0, (ψ ω (cfPt (toDisc (realPath (R ω)) (discTime 1)))).re]

/-- The left marks without the right wall's change point (the seed only). -/
def marksL1All : Ω → Fin 1 → ℝ := fun _ => ![0]

theorem travSub_eq (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (A : Set Ω) :
    PocketWordAssembly.travSub R L r η ψ A = fun ω : A => travAll R L r η ψ ω := rfl

theorem marksR_eq (L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (ψ : Ω → ℂ → ℂ) (A : Set Ω) :
    PocketWordAssembly.marksR L r ψ A = fun ω : A => marksRAll L r ψ ω := rfl

theorem marksL2_eq (R : Ω → ℝ≥0 → ℂ) (ψ : Ω → ℂ → ℂ) (A : Set Ω) :
    PocketWordAssembly.marksL2 R ψ A = fun ω : A => marksL2All R ψ ω := rfl

theorem marksL1_eq (A : Set Ω) : PocketWordAssembly.marksL1 A = fun ω : A => marksL1All (Ω := Ω) ω := rfl

/-- **The pocket inputs on every word-shape event** (the field-level form of `PocketWordAssembly.PocketCouplingInput`):
for every walls-measurable event `A ⊆ G` of positive probability and every Jordan coordinate family `ψ` of the change
pocket measurable for the walls at its measurable points, the pocket chart law holds for the traversal `travAll` in
`ψ`, with the four-mark word `(wordL2; wordR2)` when the right wall's change point is on the selected right arc
throughout `A` and with `(wordL1; wordR2)` when it is off that arc throughout `A`. -/
def PocketChartInput (κ rL rR : ℝ) (𝓦 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω) (h : Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, PocketWordAssembly.IsCfJordan (R ω) (L ω) r (ψ ω)) →
    @PocketWordAssembly.IsPointMeasurable Ω 𝓦 R L r G ψ →
    ((∀ ω ∈ A, discTime 1 ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketChartLaw (16 / κ) (wordL2 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR)) 𝓦 P A
        (travAll R L r η ψ) (marksL2All R ψ) (marksRAll L r ψ) (fun ω => cfPocket (R ω) (L ω) r) ψ h) ∧
    ((∀ ω ∈ A, discTime 1 ∉ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketChartLaw (16 / κ) (wordL1 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR)) 𝓦 P A
        (travAll R L r η ψ) marksL1All (marksRAll L r ψ) (fun ω => cfPocket (R ω) (L ω) r) ψ h)

end PocketDefs

section Arcs

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0}

/-- The interior points of the selected right arc of a bounded change pocket lie in its closure, off the opening
point. -/
theorem mem_closure_cfArcR (hG : IsChangeConfigInc R L r) (hpos : 0 < rightLo R L r) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) : cfArcR R L r s ∈ closure (cfPocket R L r) \ {cfPt (openPt R L r)} := by
  have hP := hG.isCfPocket (zero_notMem_closure_of_rightLo_pos hG hpos)
  refine ⟨frontier_subset_closure (hP.frontier_eq ▸ Or.inl ⟨s, Ioo_subset_Icc_self hs, rfl⟩), fun he => ?_⟩
  have h0 : cfArcR R L r 0 = cfPt (openPt R L r) := by
    simp only [cfArcR, zero_mul, add_zero, openPt]
  rw [← h0] at he
  exact hs.1.ne' (hP.inj₁ (Ioo_subset_Icc_self hs) ⟨le_rfl, zero_le_one⟩ he)

/-- The interior points of the selected left arc of a bounded change pocket lie in its closure, off the opening
point. -/
theorem mem_closure_cfArcL (hG : IsChangeConfigInc R L r) (hpos : 0 < rightLo R L r) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) : cfArcL R L r s ∈ closure (cfPocket R L r) \ {cfPt (openPt R L r)} := by
  have hP := hG.isCfPocket (zero_notMem_closure_of_rightLo_pos hG hpos)
  refine ⟨frontier_subset_closure (hP.frontier_eq ▸ Or.inr ⟨s, Ioo_subset_Icc_self hs, rfl⟩), fun he => ?_⟩
  have h0 : cfArcR R L r 0 = cfPt (openPt R L r) := by
    simp only [cfArcR, zero_mul, add_zero, openPt]
  rw [← h0, ← hP.junction] at he
  exact hs.1.ne' (hP.inj₂ (Ioo_subset_Icc_self hs) ⟨le_rfl, zero_le_one⟩ he)

/-- The left wall's change point lies on the selected left arc. -/
theorem changePtL_mem (hG : IsChangeConfigInc R L r) (hpos : 0 < rightLo R L r) :
    cfPt (toDisc (realPath L) (discTime r)) ∈ closure (cfPocket R L r) \ {cfPt (openPt R L r)} := by
  obtain ⟨s, hs, he⟩ := exists_affine_eq hG.changeCorners.2.2.2.2.1
  have e : cfArcL R L r s = cfPt (toDisc (realPath L) (discTime r)) := by rw [cfArcL, he]
  exact e ▸ mem_closure_cfArcL hG hpos hs

/-- The right wall's point at disc time `c₁` lies on the selected right arc when `c₁` is between its ends. -/
theorem changePtR_mem (hG : IsChangeConfigInc R L r) (hpos : 0 < rightLo R L r) {c₁ : ℝ}
    (hc : c₁ ∈ Ioo (rightLo R L r) (rightHi R L r)) :
    cfPt (toDisc (realPath R) c₁) ∈ closure (cfPocket R L r) \ {cfPt (openPt R L r)} := by
  obtain ⟨s, hs, he⟩ := exists_affine_eq hc
  have e : cfArcR R L r s = cfPt (toDisc (realPath R) c₁) := by rw [cfArcR, he]
  exact e ▸ mem_closure_cfArcR hG hpos hs

/-- A point of the open pocket is not its opening point. -/
theorem mem_closure_diff_of_mem (hG : IsChangeConfigInc R L r) {z : ℂ} (hz : z ∈ cfPocket R L r) :
    z ∈ closure (cfPocket R L r) \ {cfPt (openPt R L r)} :=
  ⟨subset_closure hz, fun h => hG.cfPt_openPt_notMem (h ▸ hz)⟩

end Arcs

section PocketMarks

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketWordAssembly

variable {Ω : Type*} [m : MeasurableSpace Ω] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {G : Set Ω}

/-- A measurable indicator of a real part is measurable on the subtype. -/
theorem measurable_sub_re {A : Set Ω} {g : Ω → ℂ} (hg : Measurable (A.indicator g)) :
    Measurable[MeasurableSpace.comap Subtype.val m] fun ω : A => (g ω).re := by
  have h := Complex.measurable_re.comp (hg.comp (comap_measurable (Subtype.val : A → Ω)))
  convert h using 1
  funext ω
  simp only [Function.comp_apply, indicator_of_mem ω.2]

/-- **The marks of a measurable Jordan coordinate are measurable for the walls** (bounded change pocket). -/
theorem measurable_marks (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hG0 : ∀ ω ∈ G, 0 < rightLo (R ω) (L ω) r)
    {ψ : Ω → ℂ → ℂ} (hψm : IsPointMeasurable R L r G ψ) {A : Set Ω} (hA : MeasurableSet A) (hAG : A ⊆ G) :
    Measurable[MeasurableSpace.comap Subtype.val m] (fun ω : A => marksRAll L r ψ ω) ∧
      ((∀ ω ∈ A, discTime 1 ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
        Measurable[MeasurableSpace.comap Subtype.val m] (fun ω : A => marksL2All R ψ ω)) := by
  have hpL : Measurable fun ω => cfPt (toDisc (realPath (L ω)) (discTime r)) :=
    measurable_cfPt.comp (measurable_toDisc_apply hLm _)
  have hpR : Measurable fun ω => cfPt (toDisc (realPath (R ω)) (discTime 1)) :=
    measurable_cfPt.comp (measurable_toDisc_apply hRm _)
  refine ⟨?_, fun hs => ?_⟩
  · exact PocketWordAssembly.measurable_vec_two (measurable_sub_re (hψm A hA hAG _ hpL fun ω hω =>
      changePtL_mem (hG ω (hAG hω)) (hG0 ω (hAG hω))))
  · exact PocketWordAssembly.measurable_vec_two (measurable_sub_re (hψm A hA hAG _ hpR fun ω hω =>
      changePtR_mem (hG ω (hAG hω)) (hG0 ω (hAG hω)) (hs ω hω)))

/-- **The Jordan coordinate at fixed points of the pocket is measurable for the walls.** -/
theorem measurable_indicator_apply (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hGm : MeasurableSet G) (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) {ψ : Ω → ℂ → ℂ}
    (hψm : IsPointMeasurable R L r G ψ) {A : Set Ω} (hA : MeasurableSet A) (hAG : A ⊆ G) (z : ℂ) :
    MeasurableSet {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} ∧
      Measurable ({ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z) := by
  have hE : {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} = A ∩ {ω | ω ∈ G ∧ z ∈ cfPocket (R ω) (L ω) r} := by
    ext ω
    exact ⟨fun h => ⟨h.1, hAG h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  have hEm : MeasurableSet {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := by
    rw [hE]
    exact hA.inter (PocketTraversalMeasRand.measurableSet_mem_cfPocket hRm hLm hGm hG z)
  exact ⟨hEm, hψm _ hEm (fun ω hω => hAG hω.1) (fun _ => z) measurable_const fun ω hω =>
    mem_closure_diff_of_mem (hG ω (hAG hω.1)) hω.2⟩

end PocketMarks


/-! ### The coupling input of a bounded change pocket -/

section Input

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketWordAssembly

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **`PocketCouplingInput` from the pocket chart inputs** (packet PROVE-STRIPSYS26): for a random bounded change
pocket traversed by the counterflow on `G` (`IsCfPocketConfig`), with walls measurable for `𝓦 ≤ mΩ`, and a measurable
physical field `h`, the pocket chart inputs give STRIPSYS20's coupling input. -/
theorem pocketCouplingInput_of_chartInput {κ rL rR : ℝ} (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
    (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t)
    {G : Set Ω} (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (hin : PocketChartInput κ rL rR 𝓦 P R L r η G h) :
    PocketCouplingInput κ rL rR 𝓦 P R L r η G := by
  intro A hA hAG hPA ψ hψ hψm
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hG0 : ∀ ω ∈ G, 0 < rightLo (R ω) (L ω) r := fun ω hω => (hcfg ω hω).bounded
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAll R L r η ψ ω) := fun ω hω =>
    ((hcfg ω (hAG hω)).isDrivenCurve (hψ ω hω)).1
  have hmk := measurable_marks (m := 𝓦) hRm hLm hG hG0 hψm hA hAG
  have hpt := fun z => measurable_indicator_apply (m := 𝓦) hRm hLm hGm hG hψm hA hAG z
  rw [travSub_eq, marksR_eq, marksL2_eq, marksL1_eq]
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · exact pocketCouplingClause_of_chartLaw h𝓦 hA hPA hγ (hmk.2 hs) hmk.1 (fun z => (hpt z).1)
      (fun z => (hpt z).2) hh ((hin A hA hAG hPA ψ hψ hψm).1 hs)
  · exact pocketCouplingClause_of_chartLaw h𝓦 hA hPA hγ measurable_const hmk.1 (fun z => (hpt z).1)
      (fun z => (hpt z).2) hh ((hin A hA hAG hPA ψ hψ hψm).2 hs)

end Input

end InteractingSLE.Sec7.PocketCoupling
