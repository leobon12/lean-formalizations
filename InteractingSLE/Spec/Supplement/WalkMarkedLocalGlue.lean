/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkMarkedLocalKernel
import InteractingSLE.Spec.Coupling.Locality11Gauss

/-!
# One more stage: a marked local set and a conditionally local new piece

Packet PROVE-T14-WALKLAW2 (Part D.2 of the follow-up note, `source/external/AstraIG1/ig1_followup_a_e_audited.txt`
L771–L832: "Given the old marked datum, a new ordinary stage is the canonical finite-word flow of that conditional
field. […] Iterating the conditional Gaussian identities proves the asserted full joined-history law").

The induction step of the per-walk locality, in the local-set calculus of the project. Let `A` be a history-marked
local set of a zero-boundary GFF `h` for the marks `𝒢` (the retained past), and let `B` be a random set (the next
piece) with marks `ℋ` (its record). Suppose that the marks are almost surely events of `σ(h)` (field determination)
and that, **under the regular conditional law given `𝒢`**, `B` satisfies the history-marked avoidance criterion for
`ℋ`, for the open sets `U` that the old set avoids (`IsHistoryAvoidanceLocalOff (A ω₀) ℋ B h (condExpKernel P 𝒢 ω₀)`).
Then `A ∪ B` is a history-marked local set of `h` for `𝒢 ⊔ ℋ` (**`isHistoryAvoidanceLocal_union_of_kernel`**).

Proof. Fix `U`, the Markov decomposition `h = Z + X` along `U` (`Z = G h`), marks `F ∈ 𝒢`, `F' ∈ ℋ`, and put
`C = {A ∩ U = ∅} ∩ F`, `S = {B ∩ U = ∅} ∩ F'`. Almost surely on `C` the decomposition survives under the conditional
law `ν` (`ae_isMarkovDecomposition_condExpKernel`, with the law of `Z` unchanged); there the conditional criterion for
`B` gives `∫_S e^{iZ(Φ)} e^{iX(Ψ)} dν = E[e^{iZ(Φ)}] ∫_S e^{iX(Ψ)} dν` (`setIntegral_exp_markov_of_condExp_self`).
Integrating over `C ∈ 𝒢` gives the same identity for `C ∩ S` under `P`; so `P[C ∩ S | h]` is a function of `X`
(`exists_condExp_eq_comp_of_setIntegral_exp`, Lemma 3.6 (ii) ⇒ (i) for one event), and since `C ∩ S` is determined by
`h`, it is almost surely an event of `σ(X)` (`mem_complSigma_of_condExp_eq_comp`). The marks `F'' ∈ 𝒢 ⊔ ℋ` for which
`{(A ∪ B) ∩ U = ∅} ∩ F''` has this property form a σ-algebra containing `𝒢` and `ℋ` (`WalkLaw.traceSigma`), and the
criterion follows (`WalkLaw.isHistoryAvoidanceLocal_of_mem_aeSigma`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE

namespace Theorem14

namespace WalkLaw

open LocalSets

/-! ### The criterion restricted to open sets off a given set -/

section Off

variable {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]

variable (ℋ) in
/-- **The history-marked avoidance criterion for the open sets off `K`**: as `WholeField.IsHistoryAvoidanceLocal`, but
only for the open `U ⊆ ℍ` with `K ∩ U = ∅`. Used under a regular conditional law that freezes an old history `K`
(the criterion is only asked where the field is unconstrained by `K`). -/
def IsHistoryAvoidanceLocalOff (K : Set ℂ) (B : Ω → Set ℂ) (h : Ω → DistOn upperHalfPlaneOpens)
    (Q : Measure Ω) : Prop :=
  ∀ (U : Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens),
    (U : Set ℂ) ⊆ H → Disjoint K U → Measurable G →
      GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) Q →
      ∀ F : Set Ω, MeasurableSet[ℋ] F →
        ∃ g : DistOn upperHalfPlaneOpens → ℝ, Measurable g ∧
          Q⟦{ω | Disjoint (B ω) U} ∩ F | MeasurableSpace.comap h inferInstance⟧ =ᵐ[Q]
            fun ω => g (markovCompl G (h ω))

/-- The full criterion gives the criterion off every set. -/
theorem _root_.InteractingSLE.WholeField.IsHistoryAvoidanceLocal.off {B : Ω → Set ℂ}
    {h : Ω → DistOn upperHalfPlaneOpens} {Q : Measure Ω} (hloc : WholeField.IsHistoryAvoidanceLocal ℋ B h Q)
    (K : Set ℂ) : IsHistoryAvoidanceLocalOff ℋ K B h Q :=
  fun U G hUH _ hG hd F hF => hloc U G hUH hG hd F hF

end Off

/-! ### Characteristic-function identities -/

section CharFun

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **The basic identity for a marked event, along the decomposition itself**: if, under a probability measure `Q`,
`G` gives the Markov decomposition of `h` along `U` and the conditional probability of `E` given `h` is a function of
`h − G h`, then `∫_E e^{iX(Φ)} e^{iY(Ψ)} dQ = E[e^{iX(Φ)}] ∫_E e^{iY(Ψ)} dQ` (`X = G h`, `Y = h − G h`). No law of `h`
is assumed beyond the decomposition (unlike `WholeField.setIntegral_exp_markov_of_condExp`). -/
theorem setIntegral_exp_markov_of_condExp_self {Q : Measure Ω} [IsProbabilityMeasure Q]
    {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {U : Opens ℂ}
    {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) Q)
    {E : Set Ω} (hE : MeasurableSet E) {g : DistOn upperHalfPlaneOpens → ℝ} (hg : Measurable g)
    (hge : Q⟦E | MeasurableSpace.comap h inferInstance⟧ =ᵐ[Q] fun ω => g (markovCompl G (h ω)))
    (Φ Ψ : TestOn upperHalfPlaneOpens) :
    ∫ ω in E, Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) *
        Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ)) ∂Q =
      (∫ ω, Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) ∂Q) *
        ∫ ω in E, Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ)) ∂Q := by
  have hm : MeasurableSpace.comap h inferInstance ≤ mΩ := hhm.comap_le
  set k : DistOn upperHalfPlaneOpens → ℂ := fun T => ((g T : ℝ) : ℂ)
  have hk : Measurable k := Complex.measurable_ofReal.comp hg
  have hXm : Measurable[MeasurableSpace.comap h inferInstance] fun ω => G (h ω) :=
    hG.comp (comap_measurable h)
  have hYm : Measurable[MeasurableSpace.comap h inferInstance] fun ω => markovCompl G (h ω) :=
    (measurable_markovCompl hG).comp (comap_measurable h)
  have hexp : ∀ (Z : Ω → DistOn upperHalfPlaneOpens) (χ : TestOn upperHalfPlaneOpens),
      Measurable[MeasurableSpace.comap h inferInstance] Z →
        StronglyMeasurable[MeasurableSpace.comap h inferInstance]
          fun ω => Complex.exp (Complex.I * (Z ω χ : ℂ)) :=
    fun Z χ hZ => (@GFF.measurable_exp_I_mul Ω (MeasurableSpace.comap h inferInstance) _
      ((LQGMetric.measurable_distOn_apply χ).comp hZ)).stronglyMeasurable
  have hnorm : ∀ x : ℝ, ‖Complex.exp (Complex.I * (x : ℂ))‖ ≤ 1 := fun x =>
    (Complex.norm_exp_I_mul_ofReal x).le
  have hL := setIntegral_eq_integral_condExp_mul (P := Q) hm hE
    (W := fun ω => Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) *
      Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ)))
    ((hexp _ Φ hXm).mul (hexp _ Ψ hYm)) (C := 1) fun ω => by
      rw [norm_mul]
      exact (mul_le_mul (hnorm _) (hnorm _) (norm_nonneg _) zero_le_one).trans (by norm_num)
  have hR := setIntegral_eq_integral_condExp_mul (P := Q) hm hE (hexp _ Ψ hYm) (C := 1)
    fun ω => hnorm _
  rw [hL, hR]
  have e1 : ∫ ω, ((Q⟦E|MeasurableSpace.comap h inferInstance⟧) ω : ℂ) *
      (Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) *
        Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ))) ∂Q =
      ∫ ω, Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) *
        (k (markovCompl G (h ω)) * Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ))) ∂Q := by
    refine integral_congr_ae ?_
    filter_upwards [hge] with ω hω
    simp only [k, hω]; ring
  have e2 : ∫ ω, ((Q⟦E|MeasurableSpace.comap h inferInstance⟧) ω : ℂ) *
      Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ)) ∂Q =
      ∫ ω, k (markovCompl G (h ω)) * Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ)) ∂Q := by
    refine integral_congr_ae ?_
    filter_upwards [hge] with ω hω
    simp only [k, hω]
  rw [e1, e2]
  have := hd.indepFun.integral_fun_comp_mul_comp (f := fun T : DistOn upperHalfPlaneOpens =>
      Complex.exp (Complex.I * (T Φ : ℂ)))
    (g := fun T : DistOn upperHalfPlaneOpens => k T * Complex.exp (Complex.I * (T Ψ : ℂ)))
    (hG.comp hhm).aemeasurable ((measurable_markovCompl hG).comp hhm).aemeasurable
    (GFF.measurable_exp_I_mul (LQGMetric.measurable_distOn_apply Φ)).aestronglyMeasurable
    (hk.mul (GFF.measurable_exp_I_mul (LQGMetric.measurable_distOn_apply Ψ))).aestronglyMeasurable
  simpa [markovCompl] using this

end CharFun

/-! ### From the identity to the conditional probability -/

section Event

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Lemma 3.6, (ii) ⇒ (i), for one event.** If `G` gives the Markov decomposition `h = X + Y` along `U` under `P`
and an event `E` satisfies `∫_E e^{iX(Φ)} e^{iY(Ψ)} = E[e^{iX(Φ)}] ∫_E e^{iY(Ψ)}` for all test functions, then the
conditional probability of `E` given `h` is a measurable function of `Y = h − G h` (the second and third steps of
`Coupling.isAvoidanceLocal_of_setIntegral_lapTest`). -/
theorem exists_condExp_eq_comp_of_setIntegral_exp {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h)
    {U : Opens ℂ} {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P) {E : Set Ω}
    (hEm : MeasurableSet E)
    (hstep : ∀ Φ Ψ : TestOn upperHalfPlaneOpens,
      ∫ ω in E, Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) *
          Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ)) ∂P =
        (∫ ω, Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) ∂P) *
          ∫ ω in E, Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ)) ∂P) :
    ∃ g : DistOn upperHalfPlaneOpens → ℝ, Measurable g ∧
      P⟦E | MeasurableSpace.comap h inferInstance⟧ =ᵐ[P] fun ω => g (markovCompl G (h ω)) := by
  have hXm : Measurable fun ω => G (h ω) := hG.comp hhm
  have hQm : Measurable fun ω => markovCompl G (h ω) := (measurable_markovCompl hG).comp hhm
  have hcexp : ∀ c : Ω → ℝ, Measurable c → Measurable fun ω => Complex.exp (Complex.I * (c ω : ℂ)) :=
    fun c hc => GFF.measurable_exp_I_mul hc
  have hcexpX : ∀ Φ : TestOn upperHalfPlaneOpens,
      Measurable fun ω => Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) := fun Φ =>
    hcexp _ ((LQGMetric.measurable_distOn_apply Φ).comp hXm)
  have hcexpQ : ∀ Ψ : TestOn upperHalfPlaneOpens,
      Measurable fun ω => Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ)) := fun Ψ =>
    hcexp _ ((LQGMetric.measurable_distOn_apply Ψ).comp hQm)
  have hintb : ∀ F : Ω → ℂ, Measurable F → (∀ ω, ‖F ω‖ ≤ 1) → Integrable F P := fun F hF hFb =>
    Integrable.of_bound hF.aestronglyMeasurable 1 (Eventually.of_forall hFb)
  have hnorm1 : ∀ x : ℝ, ‖Complex.exp (Complex.I * (x : ℂ))‖ ≤ 1 := fun x =>
    (Complex.norm_exp_I_mul_ofReal x).le
  have huniv : ∀ Φ Ψ : TestOn upperHalfPlaneOpens,
      ∫ ω, Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) *
          Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ)) ∂P =
        (∫ ω, Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) ∂P) *
          ∫ ω, Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ)) ∂P := fun Φ Ψ =>
    hd.indepFun.integral_fun_comp_mul_comp (f := fun T : DistOn upperHalfPlaneOpens =>
        Complex.exp (Complex.I * (T Φ : ℂ)))
      (g := fun T : DistOn upperHalfPlaneOpens => Complex.exp (Complex.I * (T Ψ : ℂ)))
      hXm.aemeasurable hQm.aemeasurable
      (GFF.measurable_exp_I_mul (LQGMetric.measurable_distOn_apply Φ)).aestronglyMeasurable
      (GFF.measurable_exp_I_mul (LQGMetric.measurable_distOn_apply Ψ)).aestronglyMeasurable
  have h𝓜 : MeasurableSpace.generateFrom {E} ≤ mΩ := MeasurableSpace.generateFrom_singleton_le hEm
  have hindep := indep_comap_sup_of_setIntegral_exp (𝓜 := MeasurableSpace.generateFrom {E}) hXm hQm h𝓜
      fun Φ Ψ m hm => by
    have hE' := hstep Φ Ψ
    rcases measurableSet_generateFrom_singleton_iff.1 hm with rfl | rfl | rfl | rfl
    · simp
    · exact hE'
    · have hi1 := hintb (fun ω => Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) *
          Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ))) ((hcexpX Φ).mul (hcexpQ Ψ))
          fun ω => by
        rw [norm_mul, Complex.norm_exp_I_mul_ofReal, Complex.norm_exp_I_mul_ofReal, one_mul]
      have hi2 := hintb _ (hcexpQ Ψ) fun ω => hnorm1 _
      rw [setIntegral_compl hEm hi1, setIntegral_compl hEm hi2, huniv Φ Ψ, hE', mul_sub]
    · simp only [Measure.restrict_univ]
      exact huniv Φ Ψ
  have hXle := hXm.comap_le
  have hQle := hQm.comap_le
  have hci : LQGMetric.CondIndepEv (MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance)
      (MeasurableSpace.comap (fun ω => G (h ω)) inferInstance) (MeasurableSpace.generateFrom {E}) P := by
    refine LQGMetric.condIndepEv_of_condExp_sup_eq hQle hXle h𝓜 fun a ha => ?_
    have hfa : StronglyMeasurable[MeasurableSpace.comap (fun ω => G (h ω)) inferInstance]
        (a.indicator fun _ => (1 : ℝ)) := stronglyMeasurable_const.indicator ha
    have hind1 : Indep (MeasurableSpace.comap (fun ω => G (h ω)) inferInstance)
        (MeasurableSpace.generateFrom {E} ⊔
          MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance) P := by
      rw [sup_comm]; exact hindep
    have hind2 : Indep (MeasurableSpace.comap (fun ω => G (h ω)) inferInstance)
        (MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance) P :=
      indep_of_indep_of_le_right hindep le_sup_left
    have e1 := condExp_indep_eq (m₁ := MeasurableSpace.comap (fun ω => G (h ω)) inferInstance)
      (m₂ := MeasurableSpace.generateFrom {E} ⊔
        MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance)
      hXle (sup_le h𝓜 hQle) hfa hind1
    have e2 := condExp_indep_eq (m₁ := MeasurableSpace.comap (fun ω => G (h ω)) inferInstance)
      (m₂ := MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance)
      hXle hQle hfa hind2
    exact e1.trans e2.symm
  have key := LQGMetric.condExp_sup_eq_of_condIndepEv hQle hXle h𝓜 hci
    (b := E) (MeasurableSpace.measurableSet_generateFrom rfl)
  rw [← comap_eq_sup_markov h hG] at key
  obtain ⟨g, hg, hgeq⟩ :=
    (stronglyMeasurable_condExp (m := MeasurableSpace.comap
      (fun ω => markovCompl G (h ω)) inferInstance) (μ := P)
      (f := E.indicator fun _ => (1 : ℝ))).exists_eq_measurable_comp
  refine ⟨g, hg.measurable, key.trans ?_⟩
  rw [hgeq]
  rfl

omit [IsProbabilityMeasure P] in
/-- **A field-determined event whose conditional probability is a function of `h − G h` is almost surely an event of
`h − G h`.** -/
theorem mem_complSigma_of_condExp_eq_comp [IsFiniteMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hhm : Measurable h) {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} {E : Set Ω}
    {g : DistOn upperHalfPlaneOpens → ℝ} (hg : Measurable g)
    (hge : P⟦E | MeasurableSpace.comap h inferInstance⟧ =ᵐ[P] fun ω => g (markovCompl G (h ω)))
    (hEh : MeasurableSet[aeSigma (MeasurableSpace.comap h inferInstance) P] E) :
    MeasurableSet[complSigma P G h] E := by
  obtain ⟨K, hK, hEK⟩ := hEh
  have hle : MeasurableSpace.comap h inferInstance ≤ mΩ := hhm.comap_le
  have hKm : MeasurableSet K := hle K hK
  have h1 : P⟦E | MeasurableSpace.comap h inferInstance⟧ =ᵐ[P] K.indicator fun _ => (1 : ℝ) := by
    refine (condExp_congr_ae (indicator_ae_eq_of_ae_eq_set hEK)).trans ?_
    rw [condExp_of_stronglyMeasurable hle ((measurable_const.indicator hK).stronglyMeasurable)
      ((integrable_const (1 : ℝ)).indicator hKm)]
  have h2 : (K.indicator fun _ => (1 : ℝ)) =ᵐ[P] fun ω => g (markovCompl G (h ω)) := h1.symm.trans hge
  set K' : Set Ω := (fun ω => markovCompl G (h ω)) ⁻¹' (g ⁻¹' {1}) with hK'
  refine ⟨K', ⟨g ⁻¹' {1}, hg (measurableSet_singleton 1), rfl⟩, hEK.trans ?_⟩
  filter_upwards [h2] with ω hω
  simp only [hK', mem_preimage, mem_singleton_iff, ← hω]
  by_cases hωK : ω ∈ K
  · simp [hωK]
  · simp [hωK]

end Event

/-! ### Integrating a kernel identity over an event of the conditioning σ-algebra -/

section KernelInt

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- For `C ∈ 𝒢` and a bounded measurable `f`, `∫_{C ∩ S} f dP = ∫_C (∫_S f dκ_𝒢(ω₀)) dP(ω₀)`. -/
theorem setIntegral_inter_eq_setIntegral_condExpKernel (h𝒢 : 𝒢 ≤ mΩ) {C S : Set Ω} (hC : MeasurableSet[𝒢] C)
    (hS : MeasurableSet S) {f : Ω → ℂ} (hf : Measurable f) (hfb : ∀ ω, ‖f ω‖ ≤ 1) :
    ∫ ω in C ∩ S, f ω ∂P = ∫ ω₀ in C, (∫ ω in S, f ω ∂(condExpKernel P 𝒢 ω₀)) ∂P := by
  have hfi : Integrable (S.indicator f) P :=
    (Integrable.of_bound hf.aestronglyMeasurable 1 (Eventually.of_forall hfb)).indicator hS
  have e1 : ∫ ω in C ∩ S, f ω ∂P = ∫ ω in C, S.indicator f ω ∂P := by
    rw [setIntegral_indicator hS]
  rw [e1, ← setIntegral_condExp h𝒢 hfi hC]
  refine setIntegral_congr_ae (h𝒢 _ hC) ?_
  filter_upwards [condExp_ae_eq_integral_condExpKernel h𝒢 hfi] with ω₀ hω₀ _
  rw [hω₀, integral_indicator hS]

end KernelInt

/-! ### The glue -/

section Glue

variable {Ω : Type*} {𝒢 ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **One more stage of a marked local set.** Let `h` be a zero-boundary GFF on `ℍ`, `A` a history-marked local set
for the marks `𝒢` (avoidance events in `𝒢`), and `B` a random set with marks `ℋ` whose avoidance events are events of
`𝒢 ⊔ ℋ`. If all marks are almost surely events of `σ(h)`, and under almost every regular conditional law given `𝒢`
the set `B` satisfies the history-marked criterion for `ℋ` on the open sets off `A`, then `A ∪ B` is a history-marked
local set for `𝒢 ⊔ ℋ`. -/
theorem isHistoryAvoidanceLocal_union_of_kernel {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P) (h𝒢 : 𝒢 ≤ mΩ) (hℋ : ℋ ≤ mΩ)
    {A B : Ω → Set ℂ}
    (hA : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[𝒢] {ω | Disjoint (A ω) U})
    (hB : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[𝒢 ⊔ ℋ] {ω | Disjoint (B ω) U})
    (hdet : 𝒢 ⊔ ℋ ≤ aeSigma (MeasurableSpace.comap h inferInstance) P)
    (hlocA : WholeField.IsHistoryAvoidanceLocal 𝒢 A h P)
    (hlocB : ∀ᵐ ω₀ ∂P, IsHistoryAvoidanceLocalOff ℋ (A ω₀) B h (condExpKernel P 𝒢 ω₀)) :
    WholeField.IsHistoryAvoidanceLocal (𝒢 ⊔ ℋ) (fun ω => A ω ∪ B ω) h P := by
  have hhm := hh.measurable
  refine isHistoryAvoidanceLocal_of_mem_aeSigma hhm fun U G hUH hG hd F hF => ?_
  set E₁ : Set Ω := {ω | Disjoint (A ω) U} with hE₁
  set E₂ : Set Ω := {ω | Disjoint (B ω) U} with hE₂
  have hE₁m : MeasurableSet[𝒢] E₁ := hA U hUH
  have hE₂m : MeasurableSet[𝒢 ⊔ ℋ] E₂ := hB U hUH
  have hG1 := ae_isMarkovDecomposition_condExpKernel hh h𝒢 hA hlocA hUH hG hd
  have hcexp : ∀ (Y : Ω → DistOn upperHalfPlaneOpens) (χ : TestOn upperHalfPlaneOpens), Measurable Y →
      Measurable fun ω => Complex.exp (Complex.I * (Y ω χ : ℂ)) :=
    fun Y χ hY => GFF.measurable_exp_I_mul ((LQGMetric.measurable_distOn_apply χ).comp hY)
  have hZm : Measurable fun ω => G (h ω) := hG.comp hhm
  have hXm : Measurable fun ω => markovCompl G (h ω) := (measurable_markovCompl hG).comp hhm
  have hn : ∀ x : ℝ, ‖Complex.exp (Complex.I * (x : ℂ))‖ ≤ 1 := fun x => (Complex.norm_exp_I_mul_ofReal x).le
  -- the core: the doubly marked avoidance events are almost surely events of `h − G h`
  have core : ∀ F₁, MeasurableSet[𝒢] F₁ → ∀ F₂, MeasurableSet[ℋ] F₂ →
      MeasurableSet[complSigma P G h] ((E₁ ∩ F₁) ∩ (E₂ ∩ F₂)) := by
    intro F₁ hF₁ F₂ hF₂
    have hCm : MeasurableSet[𝒢] (E₁ ∩ F₁) := hE₁m.inter hF₁
    have hSm : MeasurableSet (E₂ ∩ F₂) := (sup_le h𝒢 hℋ _ hE₂m).inter (hℋ _ hF₂)
    -- under the conditional law, on the avoidance event of `A`
    have hker : ∀ Φ Ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω₀ ∂P, ω₀ ∈ E₁ ∩ F₁ →
        ∫ ω in E₂ ∩ F₂, Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) *
            Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ)) ∂(condExpKernel P 𝒢 ω₀) =
          (∫ ω, Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) ∂P) *
            ∫ ω in E₂ ∩ F₂, Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ)) ∂(condExpKernel P 𝒢 ω₀) := by
      intro Φ Ψ
      filter_upwards [hG1, hlocB] with ω₀ h1 h2 hω₀
      obtain ⟨hdν, hlaw⟩ := h1 hω₀.1
      obtain ⟨g, hg, hge⟩ := h2 U G hUH hω₀.1 hG hdν F₂ hF₂
      rw [setIntegral_exp_markov_of_condExp_self hhm hG hdν hSm hg hge Φ Ψ]
      congr 1
      have hf : Measurable fun T : DistOn upperHalfPlaneOpens => Complex.exp (Complex.I * (T Φ : ℂ)) :=
        GFF.measurable_exp_I_mul (LQGMetric.measurable_distOn_apply Φ)
      rw [← integral_map hZm.aemeasurable hf.aestronglyMeasurable, hlaw,
        integral_map hZm.aemeasurable hf.aestronglyMeasurable]
    have hstep : ∀ Φ Ψ : TestOn upperHalfPlaneOpens,
        ∫ ω in (E₁ ∩ F₁) ∩ (E₂ ∩ F₂), Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) *
            Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ)) ∂P =
          (∫ ω, Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) ∂P) *
            ∫ ω in (E₁ ∩ F₁) ∩ (E₂ ∩ F₂), Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ)) ∂P := by
      intro Φ Ψ
      have hpm : Measurable fun ω => Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) *
          Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ)) := (hcexp _ Φ hZm).mul (hcexp _ Ψ hXm)
      have hpb : ∀ ω, ‖Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) *
          Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ))‖ ≤ 1 := fun ω => by
        rw [norm_mul]
        exact (mul_le_mul (hn _) (hn _) (norm_nonneg _) zero_le_one).trans (by norm_num)
      rw [setIntegral_inter_eq_setIntegral_condExpKernel h𝒢 hCm hSm hpm hpb,
        setIntegral_inter_eq_setIntegral_condExpKernel h𝒢 hCm hSm (hcexp _ Ψ hXm) (fun ω => hn _),
        ← integral_const_mul]
      refine setIntegral_congr_ae (h𝒢 _ hCm) ?_
      filter_upwards [hker Φ Ψ] with ω₀ hω₀ hmem using hω₀ hmem
    obtain ⟨g, hg, hge⟩ :=
      exists_condExp_eq_comp_of_setIntegral_exp hhm hG hd ((h𝒢 _ hCm).inter hSm) hstep
    refine mem_complSigma_of_condExp_eq_comp hhm hg hge ?_
    exact hdet _ (((le_sup_left : 𝒢 ≤ 𝒢 ⊔ ℋ) _ hCm).inter
      (hE₂m.inter ((le_sup_right : ℋ ≤ 𝒢 ⊔ ℋ) _ hF₂)))
  have hE𝒦 : MeasurableSet[complSigma P G h] (E₁ ∩ E₂) := by
    simpa using core univ (@MeasurableSet.univ _ 𝒢) univ (@MeasurableSet.univ _ ℋ)
  have hE : {ω | Disjoint (A ω ∪ B ω) U} = E₁ ∩ E₂ := by
    ext ω
    simp only [mem_ofPred_eq, disjoint_union_left, hE₁, hE₂, mem_inter_iff]
  rw [hE]
  have hle₁ : 𝒢 ≤ traceSigma (complSigma P G h) (E₁ ∩ E₂) hE𝒦 := fun F₁ hF₁ => by
    change MeasurableSet[complSigma P G h] ((E₁ ∩ E₂) ∩ F₁)
    have e : (E₁ ∩ E₂) ∩ F₁ = (E₁ ∩ F₁) ∩ (E₂ ∩ univ) := by
      ext ω; simp only [mem_inter_iff, mem_univ]; tauto
    rw [e]
    exact core F₁ hF₁ univ (@MeasurableSet.univ _ ℋ)
  have hle₂ : ℋ ≤ traceSigma (complSigma P G h) (E₁ ∩ E₂) hE𝒦 := fun F₂ hF₂ => by
    change MeasurableSet[complSigma P G h] ((E₁ ∩ E₂) ∩ F₂)
    have e : (E₁ ∩ E₂) ∩ F₂ = (E₁ ∩ univ) ∩ (E₂ ∩ F₂) := by
      ext ω; simp only [mem_inter_iff, mem_univ]; tauto
    rw [e]
    exact core univ (@MeasurableSet.univ _ 𝒢) F₂ hF₂
  exact sup_le hle₁ hle₂ F hF

end Glue

/-! ### Iterating the step -/

section Stages

variable {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **Marked locality along increasing stages.** Let `𝒢 0 ≤ 𝒢 1 ≤ ⋯` be marks, almost surely events of `σ(h)`, and
`A 0 ⊆ A 1 ⊆ ⋯` random sets whose avoidance events are marks of their stage. If `A 0` is a marked local set for
`𝒢 0`, and for every `k`, under almost every regular conditional law given `𝒢 k`, the next set `A (k + 1)` satisfies
the marked criterion for `𝒢 (k + 1)` on the open sets off the current `A k`, then every `A k` is a marked local set
for `𝒢 k`. -/
theorem isHistoryAvoidanceLocal_of_stages {𝒢 : ℕ → MeasurableSpace Ω} {A : ℕ → Ω → Set ℂ}
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hle : ∀ k, 𝒢 k ≤ mΩ) (hmono : ∀ k, 𝒢 k ≤ 𝒢 (k + 1)) (hsub : ∀ k ω, A k ω ⊆ A (k + 1) ω)
    (hA : ∀ k (U : Opens ℂ), (U : Set ℂ) ⊆ H → MeasurableSet[𝒢 k] {ω | Disjoint (A k ω) U})
    (hdet : ∀ k, 𝒢 k ≤ aeSigma (MeasurableSpace.comap h inferInstance) P)
    (h0 : WholeField.IsHistoryAvoidanceLocal (𝒢 0) (A 0) h P)
    (hstep : ∀ k, ∀ᵐ ω₀ ∂P,
      IsHistoryAvoidanceLocalOff (𝒢 (k + 1)) (A k ω₀) (A (k + 1)) h (condExpKernel P (𝒢 k) ω₀)) :
    ∀ k, WholeField.IsHistoryAvoidanceLocal (𝒢 k) (A k) h P := by
  intro k
  induction k with
  | zero => exact h0
  | succ k ih =>
    have hB : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H →
        MeasurableSet[𝒢 k ⊔ 𝒢 (k + 1)] {ω | Disjoint (A (k + 1) ω) U} := fun U hU =>
      (le_sup_right : 𝒢 (k + 1) ≤ 𝒢 k ⊔ 𝒢 (k + 1)) _ (hA (k + 1) U hU)
    have := isHistoryAvoidanceLocal_union_of_kernel hh (hle k) (hle (k + 1)) (hA k) hB
      (sup_le (hdet k) (hdet (k + 1))) ih (hstep k)
    have e1 : 𝒢 k ⊔ 𝒢 (k + 1) = 𝒢 (k + 1) := sup_eq_right.2 (hmono k)
    have e2 : (fun ω => A k ω ∪ A (k + 1) ω) = A (k + 1) :=
      funext fun ω => union_eq_right.2 (hsub k ω)
    rw [e1, e2] at this
    exact this

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **Adding a frozen old set.** If, under `Q`, the old set `A₀` is almost surely the fixed `K`, and the new piece `B`
satisfies the marked criterion off `K`, so does `A₀ ∪ B`. -/
theorem IsHistoryAvoidanceLocalOff.union_frozen {K : Set ℂ} {A₀ B : Ω → Set ℂ}
    {h : Ω → DistOn upperHalfPlaneOpens} {Q : Measure Ω} (hfr : ∀ᵐ ω ∂Q, A₀ ω = K)
    (hB : IsHistoryAvoidanceLocalOff ℋ K B h Q) :
    IsHistoryAvoidanceLocalOff ℋ K (fun ω => A₀ ω ∪ B ω) h Q := by
  intro U G hUH hKU hG hd F hF
  obtain ⟨g, hg, hge⟩ := hB U G hUH hKU hG hd F hF
  refine ⟨g, hg, Filter.EventuallyEq.trans ?_ hge⟩
  refine condExp_congr_ae (indicator_ae_eq_of_ae_eq_set ?_)
  filter_upwards [hfr] with ω hω
  simp only [mem_inter_iff, mem_ofPred_eq, disjoint_union_left, hω, hKU, true_and]

end Stages

end WalkLaw

end Theorem14

end InteractingSLE
