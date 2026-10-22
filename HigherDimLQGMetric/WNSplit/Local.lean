import HigherDimLQGMetric.WNSplit.Split

/-!
# Field σ-algebras and a.s. events for the consumers of D-WN′ (packet S5a)

Small interface lemmas for packet S5b (MA3 D-6.1 (b)–(c)): the trial events of Lemma 6.1 are a.s.
events of `σ(F|_J)` modulo constants (`fieldSigma0`, packet S4a's locality D-LOC) for annuli
`J = A_{s/2,5s}(w) ⊆ B_{5s}(w)`, and D-WN′ (2)–(3) give independence over disjoint noise
neighbourhoods.

* `wns_fieldSigma0_le_fieldSigmaOn`: `fieldSigma0 h V ≤ fieldSigmaOn h V`;
* `wns_fieldSigmaOn_mono`: `V ⊆ V' → fieldSigmaOn h V ≤ fieldSigmaOn h V'`;
* `wns_aeEventIn_mono`: `AEEventIn` is monotone in the σ-algebra;
* `wns_measure_biInter_of_aeEventIn`: for mutually independent σ-algebras `m i` and events `E i`
  that are a.s. equal to `m i`-events, `P(⋂_{i ∈ s} E i) = ∏_{i ∈ s} P(E i)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {Ω : Type*}

/-- `σ(h|_V)` modulo constants is contained in `σ(h|_V)`. -/
theorem wns_fieldSigma0_le_fieldSigmaOn (h : Ω → DistRd d) (V : Set (Rd d)) :
    fieldSigma0 h V ≤ fieldSigmaOn h V := by
  set r : ({φ : TestRd d // tsupport (φ : Rd d → ℝ) ⊆ V} → ℝ) →
      ({φ : TestRd0 d // tsupport (φ.1 : Rd d → ℝ) ⊆ V} → ℝ) :=
    fun F ψ => F ⟨ψ.1.1, ψ.2⟩ with hr
  have hrm : Measurable r := Measurable.of_eval fun ψ => measurable_pi_apply _
  have e : (fun ω (ψ : {φ : TestRd0 d // tsupport (φ.1 : Rd d → ℝ) ⊆ V}) => h ω ψ.1.1) =
      r ∘ fun ω (ψ : {φ : TestRd d // tsupport (φ : Rd d → ℝ) ⊆ V}) => h ω ψ.1 := rfl
  rw [fieldSigma0, fieldSigmaOn, e, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hrm.comap_le

/-- `σ(h|_V)` is monotone in `V`. -/
theorem wns_fieldSigmaOn_mono (h : Ω → DistRd d) {V V' : Set (Rd d)} (hVV' : V ⊆ V') :
    fieldSigmaOn h V ≤ fieldSigmaOn h V' := by
  set r : ({φ : TestRd d // tsupport (φ : Rd d → ℝ) ⊆ V'} → ℝ) →
      ({φ : TestRd d // tsupport (φ : Rd d → ℝ) ⊆ V} → ℝ) :=
    fun F ψ => F ⟨ψ.1, ψ.2.trans hVV'⟩ with hr
  have hrm : Measurable r := Measurable.of_eval fun ψ => measurable_pi_apply _
  have e : (fun ω (ψ : {φ : TestRd d // tsupport (φ : Rd d → ℝ) ⊆ V}) => h ω ψ.1) =
      r ∘ fun ω (ψ : {φ : TestRd d // tsupport (φ : Rd d → ℝ) ⊆ V'}) => h ω ψ.1 := rfl
  rw [fieldSigmaOn, fieldSigmaOn, e, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hrm.comap_le

/-! The sub-σ-algebras are bound before the ambient σ-algebra `mΩ`, so that instance resolution
for `P` picks the ambient one. -/

/-- `AEEventIn` is monotone in the σ-algebra. -/
theorem wns_aeEventIn_mono {m m' : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    (hmm' : m ≤ m') {E : Set Ω} (hE : AEEventIn P m E) : AEEventIn P m' E := by
  obtain ⟨F, hF, hEF⟩ := hE
  exact ⟨F, hmm' F hF, hEF⟩

/-- **Product rule for a.s. events of independent σ-algebras**. -/
theorem wns_measure_biInter_of_aeEventIn {ι : Type*} {m : ι → MeasurableSpace Ω}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} (hm : iIndep m P) {E : ι → Set Ω} (s : Finset ι)
    (hE : ∀ i ∈ s, AEEventIn P (m i) (E i)) :
    P (⋂ i ∈ s, E i) = ∏ i ∈ s, P (E i) := by
  choose! F hF hEF using hE
  have e1 : (⋂ i ∈ s, E i) =ᵐ[P] ⋂ i ∈ s, F i :=
    EventuallyEqSet.biInter s.finite_toSet fun i hi => hEF i hi
  rw [measure_congr e1, hm.meas_biInter fun i hi => hF i hi]
  exact Finset.prod_congr rfl fun i hi => (measure_congr (hEF i hi)).symm

/-- Complements of a.s. events are a.s. events. -/
theorem wns_aeEventIn_compl {m : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {E : Set Ω} (hE : AEEventIn P m E) : AEEventIn P m Eᶜ := by
  obtain ⟨F, hF, hEF⟩ := hE
  exact ⟨Fᶜ, hF.compl, hEF.compl⟩

end HigherDimLQGMetric
