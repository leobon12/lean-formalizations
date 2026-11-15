/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Zhan's A.1.5: a single compactness step produces the full coupling

Packet PROVE-ZHAN-GT4-A12. Astra, *Follow-up proofs*, §A.1.5 (`source/external/AstraIG1/ig1_followup_proofs.txt`
L409–L425, R38): "Enumerate a countable cofinal family of separated polygonal enclosure pairs. For its first `n` pairs
use (D11) to obtain a coupling of the two fixed complete marginal path laws. Enlarge each path coordinate by the stopped
path and countable generators of the actual augmented stopped sigma-algebra for every enclosure in the enumeration.
These are Borel functions of that marginal path, modulo its fixed null sets. Regard the resulting coordinates as
elements of a countable product of real standard Borel spaces. Their marginal laws are fixed and tight; hence the
family of couplings is tight. A weak limit has the two required marginal laws. For each fixed enclosure pair, all
sufficiently late couplings have exactly the same joint law of its two recorded stopped histories, namely the density
from (D6). This equality passes to the limit by continuous cylinder tests. Because the augmented marginal laws were
fixed, the recorded coordinates are still the stated Borel functions of the original marginal paths."

The measure-theoretic content, for Polish coordinate spaces `X`, `Y` (a countable product of standard Borel spaces,
with a Polish topology generating the σ-algebra):

* `isTightMeasureSet_couplings`: probability measures on `X × Y` with fixed marginals form a tight set;
* **`exists_coupling_of_eventually_map_eq`**: for any sequence of couplings of `ν₁` and `ν₂` and any family of
  continuous "cylinder tests" `f i : X × Y → Z i` whose push-forwards are eventually equal to fixed laws `λ i`, some
  cluster point in the topology of convergence in distribution is a coupling of `ν₁` and `ν₂` with every push-forward
  `f i` equal to `λ i` (Prokhorov: `isCompact_closure_of_isTightMeasureSet`);
* **`ae_eq_comp_of_map_fst_eq`**: a coordinate that is a fixed Borel function `g` of another coordinate under the
  marginal law (the "recorded coordinates") is still `g` of it almost surely under every coupling with that marginal.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace InteractingSLE.ZhanGT4

section Coupling

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [PolishSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [PolishSpace Y]

/-- **Couplings with fixed marginals form a tight set.** -/
theorem isTightMeasureSet_couplings (ν₁ : Measure X) (ν₂ : Measure Y) [IsFiniteMeasure ν₁]
    [IsFiniteMeasure ν₂] :
    IsTightMeasureSet {μ : Measure (X × Y) | μ.map Prod.fst = ν₁ ∧ μ.map Prod.snd = ν₂} := by
  refine IsTightMeasureSet.prodMk ((isTightMeasureSet_singleton (μ := ν₁)).subset ?_)
    ((isTightMeasureSet_singleton (μ := ν₂)).subset ?_)
  · rintro _ ⟨μ, hμ, rfl⟩
    exact hμ.1
  · rintro _ ⟨μ, hμ, rfl⟩
    exact hμ.2

/-- The probability measures on `X × Y` with marginals `ν₁`, `ν₂` (as a set of `ProbabilityMeasure`s). -/
def couplingSet (ν₁ : Measure X) (ν₂ : Measure Y) : Set (ProbabilityMeasure (X × Y)) :=
  {μ | (μ : Measure (X × Y)).map Prod.fst = ν₁ ∧ (μ : Measure (X × Y)).map Prod.snd = ν₂}

/-- The set of couplings is closed in the topology of convergence in distribution. -/
theorem isClosed_couplingSet (ν₁ : Measure X) (ν₂ : Measure Y) : IsClosed (couplingSet ν₁ ν₂) := by
  by_cases h₁ : IsProbabilityMeasure ν₁
  · by_cases h₂ : IsProbabilityMeasure ν₂
    · have e : couplingSet ν₁ ν₂ = (fun μ : ProbabilityMeasure (X × Y) => μ.map Prod.fst) ⁻¹' {⟨ν₁, h₁⟩} ∩
          (fun μ : ProbabilityMeasure (X × Y) => μ.map Prod.snd) ⁻¹' {⟨ν₂, h₂⟩} := by
        ext μ
        simp only [couplingSet, mem_ofPred_eq, mem_inter_iff, mem_preimage]
        constructor
        · rintro ⟨e1, e2⟩
          exact ⟨Subtype.ext e1, Subtype.ext e2⟩
        · rintro ⟨e1, e2⟩
          exact ⟨congrArg Subtype.val e1, congrArg Subtype.val e2⟩
      rw [e]
      exact (isClosed_singleton.preimage (ProbabilityMeasure.continuous_map continuous_fst)).inter
        (isClosed_singleton.preimage (ProbabilityMeasure.continuous_map continuous_snd))
    · convert isClosed_empty
      refine eq_empty_of_forall_notMem fun μ hμ => h₂ ?_
      rw [← hμ.2]
      infer_instance
  · convert isClosed_empty
    refine eq_empty_of_forall_notMem fun μ hμ => h₁ ?_
    rw [← hμ.1]
    infer_instance

/-- **Prokhorov for couplings**: the set of couplings of two laws on Polish spaces is compact. -/
theorem isCompact_couplingSet (ν₁ : Measure X) (ν₂ : Measure Y) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] :
    IsCompact (couplingSet ν₁ ν₂) := by
  have hT : IsTightMeasureSet {((μ : ProbabilityMeasure (X × Y)) : Measure (X × Y)) | μ ∈ couplingSet ν₁ ν₂} :=
    (isTightMeasureSet_couplings ν₁ ν₂).subset fun _ ⟨μ, hμ, e⟩ => e ▸ hμ
  have h := isCompact_closure_of_isTightMeasureSet hT
  rwa [(isClosed_couplingSet ν₁ ν₂).closure_eq] at h

/-- **A.1.5, the compactness step.** Let `μ n` be couplings of `ν₁` and `ν₂` (probability measures on `X × Y` with
marginals `ν₁`, `ν₂`), and let `f i : X × Y → Z i` be continuous maps ("cylinder tests") whose push-forwards under
`μ n` are, for each `i`, eventually equal to a fixed law `λ i`. Then some probability measure `μ∞` on `X × Y` is a
cluster point of `μ n` in the topology of convergence in distribution, is a coupling of `ν₁` and `ν₂`, and has
push-forward `λ i` under every `f i`. -/
theorem exists_coupling_of_eventually_map_eq (ν₁ : Measure X) (ν₂ : Measure Y) [IsFiniteMeasure ν₁]
    [IsFiniteMeasure ν₂] (μ : ℕ → ProbabilityMeasure (X × Y))
    (h₁ : ∀ n, (μ n : Measure (X × Y)).map Prod.fst = ν₁) (h₂ : ∀ n, (μ n : Measure (X × Y)).map Prod.snd = ν₂)
    {ι : Type*} {Z : ι → Type*} [∀ i, TopologicalSpace (Z i)] [∀ i, MeasurableSpace (Z i)]
    [∀ i, BorelSpace (Z i)] [∀ i, HasOuterApproxClosed (Z i)] (f : ∀ i, X × Y → Z i)
    (hf : ∀ i, Continuous (f i)) (lam : ∀ i, Measure (Z i))
    (hev : ∀ i, ∀ᶠ n in atTop, (μ n : Measure (X × Y)).map (f i) = lam i) :
    ∃ μ' : ProbabilityMeasure (X × Y), MapClusterPt μ' atTop μ ∧
      (μ' : Measure (X × Y)).map Prod.fst = ν₁ ∧ (μ' : Measure (X × Y)).map Prod.snd = ν₂ ∧
      ∀ i, (μ' : Measure (X × Y)).map (f i) = lam i := by
  obtain ⟨μ', hμ'S, hcl⟩ := (isCompact_couplingSet ν₁ ν₂).exists_mapClusterPt (f := atTop) (u := μ)
    (le_principal_iff.2 (mem_map.2 (univ_mem' fun n => ⟨h₁ n, h₂ n⟩)))
  refine ⟨μ', hcl, hμ'S.1, hμ'S.2, fun i => ?_⟩
  -- the law `λ i` is a probability measure (it is eventually a push-forward of one)
  obtain ⟨n, hn⟩ := (hev i).exists
  have hP : IsProbabilityMeasure (lam i) := by
    rw [← hn]
    infer_instance
  have hC : IsClosed ((fun ν : ProbabilityMeasure (X × Y) => ν.map (f i)) ⁻¹' {⟨lam i, hP⟩}) :=
    isClosed_singleton.preimage (ProbabilityMeasure.continuous_map (hf i))
  have hmem := hC.mem_of_mapClusterPt hcl ((hev i).mono fun n hn => by
    show (μ n).map (f i) = ⟨lam i, hP⟩
    exact Subtype.ext hn)
  exact congrArg Subtype.val (show (μ'.map (f i) : ProbabilityMeasure (Z i)) = ⟨lam i, hP⟩ from hmem)

end Coupling

section Recorded

variable {X₀ X₁ Y : Type*} [MeasurableSpace X₀] [MeasurableSpace X₁] [MeasurableSpace Y]

/-- **The recorded coordinates stay Borel functions of the path.** If under the marginal law `ν₁` of `X₀ × X₁` the
second coordinate is almost surely a measurable function `g` of the first (`X₁` with measurable diagonal), then under
every measure `μ` on `(X₀ × X₁) × Y` with first marginal `ν₁` the same holds almost surely. -/
theorem ae_eq_comp_of_map_fst_eq [MeasurableEq X₁]
    {g : X₀ → X₁} (hg : Measurable g) {ν₁ : Measure (X₀ × X₁)} (hν : ∀ᵐ p ∂ν₁, p.2 = g p.1)
    {μ : Measure ((X₀ × X₁) × Y)} (hμ : μ.map Prod.fst = ν₁) :
    ∀ᵐ q ∂μ, q.1.2 = g q.1.1 := by
  have hm : MeasurableSet {p : X₀ × X₁ | p.2 = g p.1} := measurableSet_eq_fun measurable_snd (hg.comp measurable_fst)
  have h := (ae_map_iff measurable_fst.aemeasurable hm).1 (by rwa [hμ])
  exact h

end Recorded

end InteractingSLE.ZhanGT4
