import InteractingSLE.Spec.Coupling.WholeFieldMarked

/-!
# History marking by coding: the reduction of Aux. lemma 18's first conclusion

Packet PROVE-WHOLEFIELD (ruling R36). Specification Aux. lemma 18, proof (`source/spec/p097-144.md#aux-18-proof`,
p. 97): "Fix `H ∈ 𝓕_τ` and a deterministic `b > 0`, and define `S = τ` on `H ∩ {τ ≤ b}`, `b + 1` otherwise. …
Capacity is a measurable function of a hull and distinguishes the two branches: `{hcap(K_S) ≤ 2b} = H ∩ {τ ≤ b}`.
Apply the marked avoidance criterion of Lemma 3.6(ii) to the local set `K_S`. It shows that
`P[H ∩ {τ ≤ b} ∩ E_U | h]` is measurable with respect to `h − P_U h`. Let `b → ∞`. Conditional monotone convergence
proves the same assertion with `{τ ≤ b}` omitted." (Aux. lemma 19 does the same before a finite lifetime, with the
coded stopping times capped by an announcing sequence.)

The probabilistic skeleton of this argument is proved here for arbitrary random sets:

* `IsMarkedAvoidanceLocal.exists_condExp_eq_comp` (Lemma 3.6 (ii), every recorded event): for a set satisfying (ii)
  and an event `E` of its marked σ-algebra `σ(1_{A∩U=∅}, A 1_{A∩U=∅})`, `P[E | h]` is a measurable function of
  `h − G h`;
* `exists_condExp_eq_comp_of_tendsto` (the limit step): if `P(E_k Δ E) → 0` and each `P[E_k | m]` is a measurable
  function of `Y`, so is `P[E | m]`;
* `isHistoryAvoidanceLocal_of_coding` (**the coding reduction**): if every marked avoidance event
  `F ∩ {A ∩ U = ∅}` (`F ∈ ℋ`) is approximated in probability by recorded events of sets satisfying Lemma 3.6 (ii),
  then `A` satisfies the history-marked avoidance criterion for `ℋ`.

For the optional hull coupling the recorded sets are the hulls `K_S` of coded stopping times `S < T_*` (local sets
by the frozen predicate, hence (ii) by `GFF/LocalSets/MarkedAvoidance.lean`), and the recorded events are
`{hcap(K_S) ∈ I} ∩ {K_S ∩ U = ∅}`; this needs the measurability of the half-plane capacity for the hitting
σ-algebra (the remaining input, see the handoff).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped ENNReal

namespace InteractingSLE

namespace WholeField

open LocalSets QuantumZipper LQGMetric

variable {Ω : Type*} {m ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **Lemma 3.6 (ii), every recorded event.** For a set satisfying (ii) and an event `E` of the marked σ-algebra of
`U`, the conditional probability of `E` given `h` is a measurable function of the projection `h − G h`. -/
theorem IsMarkedAvoidanceLocal.exists_condExp_eq_comp {A : Ω → Set ℂ}
    {h : Ω → DistOn upperHalfPlaneOpens} (hA : Measurable[mΩ, hittingSigma] A) (hh : Measurable h)
    (hii : IsMarkedAvoidanceLocal A h P) (U : Opens ℂ)
    {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hUH : (U : Set ℂ) ⊆ H)
    (hG : Measurable G) (hMD : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P)
    {E : Set Ω} (hE : MeasurableSet[markedSigma A U] E) :
    ∃ g : DistOn upperHalfPlaneOpens → ℝ, Measurable g ∧
      P⟦E | MeasurableSpace.comap h inferInstance⟧ =ᵐ[P] fun ω => g (markovCompl G (h ω)) := by
  have hci := (hii U G hUH hG hMD).symm
  have hYle : MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance ≤ mΩ :=
    ((measurable_markovCompl hG).comp hh).comap_le
  have hXle : MeasurableSpace.comap (fun ω => G (h ω)) inferInstance ≤ mΩ :=
    (hG.comp hh).comap_le
  have hmk := markedSigma_le hA U.isOpen hUH
  have key := LQGMetric.condExp_sup_eq_of_condIndepEv hYle hXle hmk hci hE
  rw [← comap_eq_sup_markov h hG] at key
  obtain ⟨g, hg, hgeq⟩ :=
    (stronglyMeasurable_condExp (m := MeasurableSpace.comap
      (fun ω => markovCompl G (h ω)) inferInstance) (μ := P)
      (f := E.indicator fun _ => (1 : ℝ))).exists_eq_measurable_comp
  refine ⟨g, hg.measurable, key.trans ?_⟩
  rw [hgeq]
  rfl

/-- `‖P[E | m] − P[E' | m]‖₁ ≤ P(E Δ E')`. -/
theorem eLpNorm_condExp_indicator_sub_le {E E' : Set Ω}
    (hE : MeasurableSet E) (hE' : MeasurableSet E') :
    eLpNorm (P⟦E' | m⟧ - P⟦E | m⟧) 1 P ≤ P (symmDiff E' E) := by
  have hi : ∀ {S : Set Ω}, MeasurableSet S → Integrable (S.indicator fun _ => (1 : ℝ)) P :=
    fun hS => (integrable_const (1 : ℝ)).indicator hS
  have hsub := condExp_sub (m := m) (μ := P) (hi hE') (hi hE)
  rw [eLpNorm_congr_ae hsub.symm]
  refine (eLpNorm_condExp_le_eLpNorm _ le_rfl).trans (le_of_eq ?_)
  have e2 : eLpNorm (E'.indicator (fun _ => (1 : ℝ)) - E.indicator fun _ => (1 : ℝ)) 1 P =
      eLpNorm ((symmDiff E' E).indicator fun _ => (1 : ℝ)) 1 P := by
    refine eLpNorm_congr_norm_ae (Eventually.of_forall fun ω => ?_)
    by_cases h1 : ω ∈ E' <;> by_cases h2 : ω ∈ E <;> simp [h1, h2, Set.mem_symmDiff]
  rw [e2, eLpNorm_indicator_const (hE'.symmDiff hE) one_ne_zero ENNReal.one_ne_top]
  simp

/-- **The limit step.** If `P(E_k Δ E) → 0` and every `P[E_k | m]` is almost surely a measurable function of `Y`,
then so is `P[E | m]`. -/
theorem exists_condExp_eq_comp_of_tendsto {β : Type*} [MeasurableSpace β]
    {Y : Ω → β} {E : Set Ω} (hE : MeasurableSet E) {Es : ℕ → Set Ω} (hEs : ∀ k, MeasurableSet (Es k))
    (hlim : Tendsto (fun k => P (symmDiff (Es k) E)) atTop (𝓝 0))
    (hg : ∀ k, ∃ g : β → ℝ, Measurable g ∧ P⟦Es k | m⟧ =ᵐ[P] fun ω => g (Y ω)) :
    ∃ g : β → ℝ, Measurable g ∧ P⟦E | m⟧ =ᵐ[P] fun ω => g (Y ω) := by
  choose gs hgs hgse using hg
  have hmeas : ∀ {S : Set Ω}, AEStronglyMeasurable (P⟦S | m⟧) P := fun {S} =>
    integrable_condExp.aestronglyMeasurable
  have hin : TendstoInMeasure P (fun k => P⟦Es k | m⟧) atTop (P⟦E | m⟧) := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero (fun _ => hmeas) hmeas ?_
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
      fun k => eLpNorm_condExp_indicator_sub_le hE (hEs k)
  obtain ⟨ns, -, hns⟩ := hin.exists_seq_tendsto_ae
  set g : β → ℝ := fun y => limUnder atTop fun i => gs (ns i) y
  have hgm : Measurable g :=
    (StronglyMeasurable.limUnder fun i => (hgs (ns i)).stronglyMeasurable).measurable
  refine ⟨g, hgm, ?_⟩
  have hall := ae_all_iff.2 fun i => hgse (ns i)
  filter_upwards [hns, hall] with ω h1 h2
  have h3 : Tendsto (fun i => gs (ns i) (Y ω)) atTop (𝓝 ((P⟦E | m⟧) ω)) := by
    refine h1.congr fun i => ?_
    exact h2 i
  exact h3.limUnder_eq.symm

/-- **The coding reduction of Aux. lemma 18.** Suppose that for every deterministic open `U ⊆ ℍ` and every mark
`F ∈ ℋ`, the marked avoidance event `F ∩ {A ∩ U = ∅}` is the limit in probability of events `E_k` recorded by sets
`A_k` satisfying Lemma 3.6 (ii) (`E_k ∈ σ(1_{A_k∩U=∅}, A_k 1_{A_k∩U=∅})`). Then `A` satisfies the history-marked
avoidance criterion for `ℋ`. -/
theorem isHistoryAvoidanceLocal_of_coding {A : Ω → Set ℂ}
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h) (hA : Measurable[mΩ, hittingSigma] A)
    (hℋ : ℋ ≤ mΩ)
    (hcode : ∀ (U : Opens ℂ), (U : Set ℂ) ⊆ H → ∀ F : Set Ω, MeasurableSet[ℋ] F →
      ∃ (As : ℕ → Ω → Set ℂ) (Es : ℕ → Set Ω), (∀ k, Measurable[mΩ, hittingSigma] (As k)) ∧
        (∀ k, IsMarkedAvoidanceLocal (As k) h P) ∧ (∀ k, MeasurableSet[markedSigma (As k) U] (Es k)) ∧
        Tendsto (fun k => P (symmDiff (Es k) ({ω | Disjoint (A ω) U} ∩ F))) atTop (𝓝 0)) :
    IsHistoryAvoidanceLocal ℋ A h P := by
  intro U G hUH hG hMD F hF
  obtain ⟨As, Es, hAs, hii, hEs, hlim⟩ := hcode U hUH F hF
  refine exists_condExp_eq_comp_of_tendsto ((hA (measurableSet_avoid U.isOpen hUH)).inter (hℋ F hF))
    (fun k => markedSigma_le (hAs k) U.isOpen hUH _ (hEs k)) hlim fun k => ?_
  exact IsMarkedAvoidanceLocal.exists_condExp_eq_comp (hAs k) hh (hii k) U hUH hG hMD (hEs k)

end WholeField

end InteractingSLE
