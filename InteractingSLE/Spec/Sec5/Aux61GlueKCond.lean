/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61FibKGlued

/-!
# (K): the glued rectangle identities from the chart kernel and Aux. 61's identity (PC1)

Packet PROVE-AUX61-GLUEK (Theorem 1.2's Prop 5.1 (E1); `planning/handoffs/PROVE-AUX61-FIB2.md`, "What remains" (K)).
`Aux61FibK.hasDyActFibreCover_of_glued` needs the rectangle identities `hint`:
`∫_{Z ∈ B', Y ∈ ratPi q T} 1_B(Z) 1_{ratAvoid}(Y) (e^{i h_chart(ψ_p)} − ratKer) dμ = 0` at every dyadic fibre time `q`.
This file reduces them to the two genuinely probabilistic statements of Astra's follow-up 4 §§1.1–1.2 (R71):

* **`hint_of_condExp`**: `hint` from the conditional characteristic functional of the chart field given any
  σ-algebra `𝓜` containing the history and the raw code σ-algebra at `q`
  (`E[e^{i h_chart(ψ_p)} | 𝓜] = ratKer` on `{Z ∈ B, Y ∈ ratAvoid}`); the kernel only needs to be jointly measurable
  (`hmeas`, see `Aux61GlueKMeas`);
* `closure_fwdHull_subset_buffer`: the path facts put the hull before the lifetime into the buffer;
* **`integral_eq_meanF_of_isPC1`**, **`cfVal_eq_ratKer_of_isPC1`**: a mean satisfying Aux. lemma 61's identity
  (PC1) (`Aux61Win.IsPC1`, relative to the reference extension `canonExt`) pairs like `meanF` with the data's cutoff,
  so the Gaussian kernel with that mean is `ratKer`;
* **`hint_of_chartKernel`**: `hint` from (i) the union kernel in the chart — the conditional characteristic
  functional given `𝓜` is Gaussian with some mean `M` and the Green covariance of `ℍ ∖ K_q` (§1.1) — and (ii) (PC1)
  for `M` (§1.2, Aux. lemma 61).

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param` result; R77: no post-contact kernel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GlueK

open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open LocalExt (cfVal)
open Restart.FlowStopIdentCMI (CMCut)
open Restart.DomainMarkov (RatIdx dyT)
open Aux61Win (meanF IsCutoffOn IsPC1)
open Aux61Fib (FibCode FibData PathGood fibW fibΓ fibU fibField)
open Aux61FibK (codeSigma ratKer ratAvoid ratψ ratPi gluedInt canonExt)

universe u

/-! ### The rectangle identities from a conditional expectation -/

/-- **(K) from the glued conditional kernel.** If `𝓜 n k` is a σ-algebra on the glued space containing the history
σ-algebra and the raw code σ-algebra at the dyadic time `k/2ⁿ`, and almost surely on `{Z ∈ B, Y ∈ ratAvoid}` the
conditional characteristic functional of the chart field at `ψ_p` given `𝓜 n k` is the explicit kernel `ratKer`
(jointly measurable), then the rectangle identities `hint` of `Aux61FibK.hasDyActFibreCover_of_glued` hold. -/
theorem hint_of_condExp {X : Type*} [mX : MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {β : Type*} [mβ : MeasurableSpace β] {Z : X → β} (hZ : Measurable Z) {Y : X → FibCode} (hY : Measurable Y)
    {B : Set β} (hB : MeasurableSet B) (d : β → FibData) (F₀ : β → CMCut)
    (hmeas : ∀ (n k : ℕ) (p : RatIdx), Measurable[mβ.prod (codeSigma.{u} n k)]
      (fun zs : β × ULift.{u} FibCode => (ratAvoid n k p).indicator (ratKer (d zs.1) (F₀ zs.1) n k p) zs.2))
    (𝓜 : ℕ → ℕ → MeasurableSpace X) (h𝓜 : ∀ n k, 𝓜 n k ≤ mX)
    (hZ𝓜 : ∀ n k, mβ.comap Z ≤ 𝓜 n k)
    (hY𝓜 : ∀ n k, (codeSigma.{u} n k).comap (fun x => ULift.up.{u} (Y x)) ≤ 𝓜 n k)
    (hker : ∀ (n k : ℕ) (p : RatIdx), ∀ᵐ x ∂μ, Z x ∈ B → ULift.up.{u} (Y x) ∈ ratAvoid n k p →
      μ[fun x' => Complex.exp (Complex.I * (fibField (ULift.up.{u} (Y x')) (ratψ p) : ℂ)) | 𝓜 n k] x =
        ratKer (d (Z x)) (F₀ (Z x)) n k p (ULift.up.{u} (Y x))) :
    ∀ (n k : ℕ) (p : RatIdx) (T : Finset (ℚ × ℚ × ℚ)) (B' : Set β), MeasurableSet B' → B' ⊆ B →
      ∫ x in Z ⁻¹' B' ∩ (fun x => ULift.up.{u} (Y x)) ⁻¹' ratPi fibW fibU (dyT n k) T,
        gluedInt B d F₀ n k p (Z x, ULift.up (Y x)) ∂μ = 0 := by
  intro n k p T B' hB' _
  set Y' : X → ULift.{u} FibCode := fun x => ULift.up (Y x) with hY'def
  have hY' : Measurable Y' := measurable_up.comp hY
  have hsig : codeSigma.{u} n k ≤ (inferInstance : MeasurableSpace (ULift.{u} FibCode)) :=
    Aux61FibK.codeFiltration.le _
  -- the events are events of `𝓜`
  have hZm : ∀ C : Set β, MeasurableSet C → MeasurableSet[𝓜 n k] (Z ⁻¹' C) := fun C hC =>
    hZ𝓜 n k _ ⟨C, hC, rfl⟩
  have hYm : ∀ A : Set (ULift.{u} FibCode), MeasurableSet[codeSigma.{u} n k] A →
      MeasurableSet[𝓜 n k] (Y' ⁻¹' A) := fun A hA => hY𝓜 n k _ ⟨A, hA, rfl⟩
  have hPi : MeasurableSet[codeSigma.{u} n k] (ratPi fibW fibU (dyT n k) T) := by
    have h : MeasurableSet[Aux61FibK.ratSigma fibW.{u} fibU (dyT n k)] (ratPi fibW fibU (dyT n k) T) :=
      MeasurableSpace.measurableSet_generateFrom ⟨T, rfl⟩
    rwa [Aux61FibK.generateFrom_ratPi fibW fibU (fun s => Aux61Fib.FibCode.continuous_driver s.down)
      (Aux61FibK.exists_rat_dyT n k)] at h
  set E : Set X := Z ⁻¹' B ∩ Y' ⁻¹' ratAvoid n k p with hEdef
  set A : Set X := Z ⁻¹' B' ∩ Y' ⁻¹' ratPi fibW fibU (dyT n k) T with hAdef
  have hAE : MeasurableSet[𝓜 n k] (A ∩ E) :=
    ((hZm B' hB').inter (hYm _ hPi)).inter ((hZm B hB).inter (hYm _ (Aux61FibK.measurableSet_ratAvoid n k p)))
  -- the integrands
  set f : X → ℂ := fun x => Complex.exp (Complex.I * (fibField (Y' x) (ratψ p) : ℂ)) with hfdef
  set g : X → ℂ := fun x => (ratAvoid n k p).indicator (ratKer (d (Z x)) (F₀ (Z x)) n k p) (Y' x) with hgdef
  have hfm : Measurable f := Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
    ((LQGMetric.measurable_distOn_apply (ratψ p)).comp
      ((Aux61Fib.FibCode.measurable_field.comp measurable_down).comp hY'))))
  have hfi : Integrable f μ := Integrable.of_bound hfm.aestronglyMeasurable 1
    (ae_of_all _ fun x => (Complex.norm_exp_I_mul_ofReal _).le)
  have hgm : Measurable g := by
    have h := (hmeas n k p).mono (sup_le_sup le_rfl (MeasurableSpace.comap_mono hsig)) le_rfl
    exact h.comp (hZ.prodMk hY')
  have hgi : Integrable g μ := Integrable.of_bound hgm.aestronglyMeasurable 1
    (ae_of_all _ fun x => Aux61FibK.norm_indicator_ratKer_le_one _ _ n k p _)
  have e : (fun x => gluedInt.{u} B d F₀ n k p (Z x, Y' x)) = E.indicator fun x => f x - g x := by
    funext x
    simp only [gluedInt, hEdef, hfdef, hgdef, Set.indicator, mem_inter_iff, mem_preimage]
    split_ifs <;> simp_all
  show ∫ x in A, gluedInt.{u} B d F₀ n k p (Z x, Y' x) ∂μ = 0
  rw [e, setIntegral_indicator (h𝓜 n k _ ((hZm B hB).inter (hYm _ (Aux61FibK.measurableSet_ratAvoid n k p)))),
    integral_sub hfi.integrableOn hgi.integrableOn, ← setIntegral_condExp (h𝓜 n k) hfi hAE, sub_eq_zero]
  refine setIntegral_congr_ae (h𝓜 n k _ hAE) ?_
  filter_upwards [hker n k p] with x hx hxA
  rw [hx hxA.2.1 hxA.2.2, hgdef]
  exact (Set.indicator_of_mem (s := ratAvoid n k p) hxA.2.2 _).symm

/-! ### Aux. lemma 61's identity (PC1) gives the explicit kernel -/

/-- **The path facts put the hull before the lifetime into the buffer.** -/
theorem closure_fwdHull_subset_buffer {d : FibData} {s : FibCode} (hs : PathGood d s) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < s.life) :
    closure (fwdHull (Ito.rpath (Aux61Fib.FibCode.driver · s)) t) ⊆ d.buffer :=
  (Aux61Cov.closure_fwdHull_subset_of_exit hs.1 hs.2.2.2.2.2 hs.2.2.2.2.1 hs.2.2.2.1 ht).trans d.V_sub

/-- **A mean satisfying (PC1) pairs like `meanF`**: for a cutoff `F` of `q` on `N` containing the seed and the closed
hull, `∫ M ψ = ∫ meanF κ u₀ q F w t ψ` at every test `ψ` off the hull. -/
theorem integral_eq_meanF_of_isPC1 {κ : ℝ} {u₀ q : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hq : ContinuousOn q H) {w' : ℝ≥0 → ℝ} (hw' : Continuous w') {t : ℝ≥0} {O₀ : Set ℝ} {M : ℂ → ℝ}
    (hPC : IsPC1 κ u₀ (Ito.rpath w') t q O₀ M) {F : CMCut} {N : Set ℂ} (hF : IsCutoffOn F q N O₀)
    (h0N : (0 : ℂ) ∈ N) (hKN : closure (fwdHull (Ito.rpath w') t) ⊆ N) (ψ : TestOn upperHalfPlaneOpens)
    (hψ : Disjoint (tsupport ψ) (fwdHull (Ito.rpath w') t)) :
    ∫ z, M z * ψ z = ∫ z, meanF κ u₀ q F (Ito.rpath w') t z * ψ z := by
  rw [hPC F N hF h0N hKN ψ hψ, Aux61Win.integral_meanF_eq hu₀ hq hw' (hF.isGreenTest_src hKN) ψ hψ]

/-- **The Gaussian kernel with a (PC1) mean is `ratKer`** on the avoidance event of a code with the path facts, for a
cutoff of the data's `q` on a neighbourhood of the buffer. -/
theorem cfVal_eq_ratKer_of_isPC1 {d : FibData} {F₀ : CMCut} {N₀ : Set ℂ} (hF₀ : IsCutoffOn F₀ d.q N₀ d.O₀)
    (hbN : d.buffer ⊆ N₀) {n k : ℕ} {p : RatIdx} {s : ULift.{u} FibCode} (hgood : PathGood d s.down)
    (hs : s ∈ ratAvoid n k p) {M : ℂ → ℝ}
    (hPC : IsPC1 d.κ (canonExt d s (dyT n k)) (Ito.rpath (fibW · s)) (dyT n k) d.q d.O₀ M) :
    cfVal (∫ z, M z * ratψ p z) (loewnerGreenEnergy (Ito.rpath (fibW · s)) (dyT n k : ℝ≥0) (ratψ p)) =
      ratKer d F₀ n k p s := by
  have hlt : ((dyT n k : ℝ≥0) : ℝ≥0∞) < fibU s := hs.1
  have hψ : Disjoint (tsupport (ratψ p)) (fwdHull (Ito.rpath (fibW · s)) (dyT n k : ℝ≥0)) := hs.2
  have hKb := closure_fwdHull_subset_buffer hgood hlt
  have hu := Aux61FibK.refExt_canonExt d s (dyT n k)
  rw [ratKer, integral_eq_meanF_of_isPC1 hu.1 d.q_harm.contDiffOn.continuousOn
    (Aux61Fib.FibCode.continuous_driver s.down) hPC hF₀ (hbN d.zero_mem) (hKb.trans hbN) (ratψ p) hψ]

/-! ### The rectangle identities from the chart kernel and (PC1) -/

/-- **(K) from the union kernel in the chart and Aux. lemma 61.** On the glued space, let `𝓜 n k` contain the
history and the raw code σ-algebra at the dyadic fibre time `q = k/2ⁿ`. Suppose that almost surely on
`{Z ∈ B, Y ∈ ratAvoid}`

* (§1.1, the union kernel) the conditional characteristic functional of the chart field at `ψ_p` given `𝓜 n k` is
  Gaussian, `cfVal(∫ M ψ_p, E_{ℍ∖K_q}(ψ_p))`, with some mean `M n k x`, and
* (§1.2, Aux. lemma 61) `M n k x` satisfies (PC1) relative to the reference extension `canonExt` at `q`, the data's
  correction `q` and window `O₀`;

and that the path facts hold on `{Z ∈ B}` and `F₀` is a cutoff of the data's `q` near its buffer. Then the rectangle
identities `hint` of `Aux61FibK.hasDyActFibreCover_of_glued` hold. -/
theorem hint_of_chartKernel {X : Type*} [mX : MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {β : Type*} [mβ : MeasurableSpace β] {Z : X → β} (hZ : Measurable Z) {Y : X → FibCode} (hY : Measurable Y)
    {B : Set β} (hB : MeasurableSet B) (d : β → FibData) (F₀ : β → CMCut) (N₀ : β → Set ℂ)
    (hcut : ∀ z ∈ B, IsCutoffOn (F₀ z) (d z).q (N₀ z) (d z).O₀ ∧ (d z).buffer ⊆ N₀ z)
    (hgood : ∀ᵐ x ∂μ, Z x ∈ B → PathGood (d (Z x)) (Y x))
    (hmeas : ∀ (n k : ℕ) (p : RatIdx), Measurable[mβ.prod (codeSigma.{u} n k)]
      (fun zs : β × ULift.{u} FibCode => (ratAvoid n k p).indicator (ratKer (d zs.1) (F₀ zs.1) n k p) zs.2))
    (𝓜 : ℕ → ℕ → MeasurableSpace X) (h𝓜 : ∀ n k, 𝓜 n k ≤ mX)
    (hZ𝓜 : ∀ n k, mβ.comap Z ≤ 𝓜 n k)
    (hY𝓜 : ∀ n k, (codeSigma.{u} n k).comap (fun x => ULift.up.{u} (Y x)) ≤ 𝓜 n k)
    (M : ℕ → ℕ → X → ℂ → ℝ)
    (hchart : ∀ (n k : ℕ) (p : RatIdx), ∀ᵐ x ∂μ, Z x ∈ B → ULift.up.{u} (Y x) ∈ ratAvoid n k p →
      μ[fun x' => Complex.exp (Complex.I * (fibField (ULift.up.{u} (Y x')) (ratψ p) : ℂ)) | 𝓜 n k] x =
        cfVal (∫ z, M n k x z * ratψ p z)
          (loewnerGreenEnergy (Ito.rpath (fibW · (ULift.up.{u} (Y x)))) (dyT n k : ℝ≥0) (ratψ p)))
    (hPC1 : ∀ n k : ℕ, ∀ᵐ x ∂μ, Z x ∈ B → ((dyT n k : ℝ≥0) : ℝ≥0∞) < fibU (ULift.up.{u} (Y x)) →
      IsPC1 (d (Z x)).κ (canonExt (d (Z x)) (ULift.up.{u} (Y x)) (dyT n k))
        (Ito.rpath (fibW · (ULift.up.{u} (Y x)))) (dyT n k) (d (Z x)).q (d (Z x)).O₀ (M n k x)) :
    ∀ (n k : ℕ) (p : RatIdx) (T : Finset (ℚ × ℚ × ℚ)) (B' : Set β), MeasurableSet B' → B' ⊆ B →
      ∫ x in Z ⁻¹' B' ∩ (fun x => ULift.up.{u} (Y x)) ⁻¹' ratPi fibW fibU (dyT n k) T,
        gluedInt B d F₀ n k p (Z x, ULift.up (Y x)) ∂μ = 0 := by
  refine hint_of_condExp hZ hY hB d F₀ hmeas 𝓜 h𝓜 hZ𝓜 hY𝓜 fun n k p => ?_
  filter_upwards [hchart n k p, hPC1 n k, hgood] with x hx hpc hg hxB hxA
  rw [hx hxB hxA]
  exact cfVal_eq_ratKer_of_isPC1 (hcut _ hxB).1 (hcut _ hxB).2 (s := ULift.up.{u} (Y x)) (hg hxB) hxA
    (hpc hxB hxA.1)

end InteractingSLE.Sec5.Aux61GlueK
