/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootReg

/-!
# GW2's root stages from per-candidate tests (follow-up 5 §4.1; follow-up note A.2–A.5)

Packet PROVE-GW2-ROOT. Follow-up 5 §4.1 (`source/external/AstraIG1/ig1_followup5.txt` L559–L640): "At stage `j`,
choose the desired direction `e` and error `εⱼ > 0` … `K_z(S < F) > 1 − εⱼ/2` … define, on the canonical next-piece
space, `E_m = ⋃_{n ≤ m} {S < qₙ < F, qₙ strictly available, γ(qₙ) ∈ D, X_{qₙ} ∈ I_e}` … `E_m ↑ {S < F}` …
`m(z) = min{m : K_z(E_m) > 1 − εⱼ}` … Proposition 4.1 (Actual stage rule). Inspect the finite set
`{q₁, …, q_{m(Z)}}` in chronological order. Stop at its first member satisfying the conditions in (4.2) … Summable error
allowances give total failure probability at most `Σⱼ εⱼ`".

This file removes the encodings of `GW2TipSystem.CandClaimsR` (rules `Nat.pair (a, m)`, the candidate enumeration, the
tolerances `εⱼ`): the remaining content is stated **per candidate time `q ∈ Q`** and **per rule parameter `a`**:

* `rootSigma`, `capR`: the stage-start σ-algebra and the relative capacity (regularized record) of a schedule;
* **`TestClaims`**: alive events `A`, parameter angles, tests `T l a q` ("the stage from `l` with parameter `a`
  passes the test at the candidate `q`"), unit events `V`, and the claims: measurability at the stage start (the test
  at `q` known once the new piece reached any `q' ≥ q`), a passed test from an alive schedule gives an alive extension,
  **the crossing claim** (`hcross`: for every `ε > 0`, almost surely on `A l`, some parameter's tests succeed with
  conditional probability `> 1 − ε`; follow-up 5 (4.1) with `E_m ↑ {S < F}`), **the no-unit claim** (`hnounit`: at
  even depths `≥ 4` the conditional probability of a success without a unit is at most `1 − p₀`, for every parameter;
  the uniform Lemma 5.10), and the unit bookkeeping;
* **`candClaimsR_of_testClaims`**: the finite-candidate data (`GW2CandData`, enumeration of `Q` by `ℕ`, tolerances
  `min ε₀ 1 · 2^{-(j+1)}`) satisfying `CandClaimsR` (Lemma A.1: a finite count suffices; Proposition 4.1);
* **`GW2RootTestStatement`** (named) and **`gw2RootCandRStatement_of_test`**,
  **`gw2TipExhaustionCanonStatement_of_test`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2TipSystem

open GW2Schedule GW2Cone GW2Later GW2Tip GW2TipStage Exist Staged StagedLaw Restart LQGMetric

/-- A dense subset of `ℝ≥0` is infinite. -/
theorem infinite_of_dense {Q : Set ℝ≥0} (hQ : Dense Q) : Q.Infinite := by
  intro hfin
  have h1 : Q = univ := by rw [← hfin.isClosed.closure_eq, hQ.closure_eq]
  exact Set.infinite_univ (h1 ▸ hfin)

/-- The tolerances `min ε₀ 1 · 2^{-(j+1)}` sum to at most `ε₀`. -/
theorem tsum_tol_le (ε₀ : ℝ≥0∞) : ∑' j : ℕ, min ε₀ 1 * 2⁻¹ ^ (j + 1) ≤ ε₀ := by
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv,
    ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]
  exact min_le_left _ _

theorem tol_pos {ε₀ : ℝ≥0∞} (hε₀ : 0 < ε₀) (j : ℕ) : 0 < min ε₀ 1 * 2⁻¹ ^ (j + 1) :=
  ENNReal.mul_pos (lt_min hε₀ one_pos).ne' (ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) _).ne'

section Test

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u}) (βA : BoundaryWord × ℝ × RecData → BoundaryWord)
  (b : ℝ → ℝ) (jumps : Finset ℝ) (c₀ : BoundaryWord) {Ω : Type u} [mΩ : MeasurableSpace Ω]
  (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) {Θ : Set ℝ} {Q : Set ℝ≥0} (s : ℝ≥0)

/-- **The stage-start σ-algebra of the schedule `l` from the root `r`** (the counterflow record at `s` and the
canonical pieces stopped at their switching times; the σ-algebra of `gw2RootRule` and `gw2RootRuleR`). -/
abbrev rootSigma (r : ScaledRootIdx Θ Q) (l : List (EntryIdx Θ Q)) : MeasurableSpace Ω :=
  stageSigma hκ h12p βA c₀ h s W' ζ' (schedSpecOf r.1 l) ((entryList l).length + 1)

/-- **The relative capacity of the schedule `l` from the root `r`**, in the joint chart of the regularized counterflow
record, scaled by `4^k` (the capacity of `gw2RootRuleR`). -/
def capR (r : ScaledRootIdx Θ Q) (l : List (EntryIdx Θ Q)) (ω : Ω) : ℝ :=
  4 ^ r.2 * schedCap hκ h12p βA b jumps c₀ h (regW s W' ζ') s Θ Q (rootPt r.1) (rootEntry r.1) (entryList l) ω

/-- **The per-candidate claims of GW2's stages from the root `r`** with initial event `G` (follow-up 5 §4.1; follow-up
note A.2–A.5): alive events `A`, the angle of each rule parameter, the tests `T l a q` at the candidate times `q ∈ Q`,
the unit events `V` and the unit probability `p₀`. -/
structure TestClaims [StandardBorelSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] (r : ScaledRootIdx Θ Q) (G : Set Ω)
    (A : List (EntryIdx Θ Q) → Set Ω) (ang : ℕ → Θ) (T : List (EntryIdx Θ Q) → ℕ → Q → Set Ω)
    (V : List (EntryIdx Θ Q) → Set Ω) (p₀ : ℝ) : Prop where
  /-- The initial event is known at the root. -/
  hG : MeasurableSet[rootSigma hκ h12p βA c₀ h W' ζ' s r []] G
  hGA : G ⊆ A []
  hA : ∀ l, MeasurableSet[rootSigma hκ h12p βA c₀ h W' ζ' s r l] (A l)
  /-- The test at `q` is known once the new piece has reached any candidate `q' ≥ q`. -/
  hT : ∀ l a (q q' : Q), q ≤ q' → MeasurableSet[rootSigma hκ h12p βA c₀ h W' ζ' s r ((ang a, q') :: l)] (T l a q)
  /-- A passed test from an alive schedule gives an alive extension. -/
  hTA : ∀ l a q, A l ∩ T l a q ⊆ A ((ang a, q) :: l)
  hV : ∀ l, MeasurableSet[rootSigma hκ h12p βA c₀ h W' ζ' s r l] (V l)
  /-- **The crossing claim** (follow-up 5 (4.1)–(4.2); A.3–A.4). -/
  hcross : ∀ l (ε : ℝ≥0∞), 0 < ε → ∀ᵐ ω ∂P, ω ∈ A l → ∃ a,
    1 - ε < condExpKernel P (rootSigma hκ h12p βA c₀ h W' ζ' s r l) ω (⋃ q, T l a q)
  hp₀ : 0 < p₀
  hp₀1 : p₀ ≤ 1
  /-- **The no-unit claim** (the uniform Lemma 5.10 at even depths `≥ 4`; A.5). -/
  hnounit : ∀ (k : ℕ) l, l.length = 2 * k + 4 → ∀ᵐ ω ∂P, ω ∈ A l → ∀ a,
    condExpKernel P (rootSigma hκ h12p βA c₀ h W' ζ' s r l) ω (⋃ q, (T l a q \ V ((ang a, q) :: l))) ≤
      ENNReal.ofReal (1 - p₀)
  /-- The unit clause. -/
  hcapU : ∀ l x, ∀ ω ∈ A (x :: l), ω ∈ V (x :: l) →
    capR hκ h12p βA b jumps c₀ h W' ζ' s r l ω + 1 ≤ capR hκ h12p βA b jumps c₀ h W' ζ' s r (x :: l) ω

/-- The finite-candidate data of per-candidate tests, for an enumeration `e` of the candidate times and tolerances
`ε`. -/
def testCandData (A : List (EntryIdx Θ Q) → Set Ω) (ang : ℕ → Θ) (T : List (EntryIdx Θ Q) → ℕ → Q → Set Ω)
    (V : List (EntryIdx Θ Q) → Set Ω) (p₀ : ℝ) (e : ℕ → Q) (ε : ℕ → ℝ≥0∞) : GW2CandData Θ Q Ω where
  A n := A n.2
  ang := ang
  qe := e
  Tst n a i := T n.2 a (e i)
  V n := V n.2
  ε := ε
  p₀ := p₀

variable {hκ h12p βA b jumps c₀ h W' ζ' s}

/-- **The finite-candidate claims from the per-candidate claims** (Lemma A.1, Proposition 4.1 of follow-up 5): with an
enumeration of `Q` and the tolerances `min ε₀ 1 · 2^{-(j+1)}`, a parameter whose tests succeed with conditional
probability `> 1 − εⱼ` gives a finite candidate count with probability `≥ 1 − εⱼ` (`exists_candE_of_lt`; the alive
event has conditional probability one on itself); a rule's no-unit successes are no-unit successes of its parameter. -/
theorem candClaimsR_of_testClaims [StandardBorelSpace Ω] (hβA : Measurable βA) (hh : Measurable h)
    {P : Measure Ω} [IsFiniteMeasure P] (hcf : IsCenteredCounterflowDriver κ P h W' ζ') {hΘc : Θ.Countable}
    {hQc : Q.Countable} {r : ScaledRootIdx Θ Q} {G : Set Ω} {A : List (EntryIdx Θ Q) → Set Ω} {ang : ℕ → Θ}
    {T : List (EntryIdx Θ Q) → ℕ → Q → Set Ω} {V : List (EntryIdx Θ Q) → Set Ω} {p₀ : ℝ}
    (hc : TestClaims hκ h12p βA b jumps c₀ h W' ζ' s P r G A ang T V p₀) (e : ℕ ≃ Q) {ε₀ : ℝ≥0∞} (hε₀ : 0 < ε₀) :
    CandClaimsR hκ h12p βA b jumps c₀ h W' ζ' hΘc hQc s r G P ε₀
      (testCandData A ang T V p₀ e fun j => min ε₀ 1 * 2⁻¹ ^ (j + 1)) := by
  set cd := testCandData A ang T V p₀ e fun j => min ε₀ 1 * 2⁻¹ ^ (j + 1) with hcd
  have hle : ∀ l, rootSigma hκ h12p βA c₀ h W' ζ' s r l ≤ mΩ := fun l =>
    stageSigma_le hβA hh hcf s _ _
  refine
    { hqe := e.injective
      hG := hc.hG
      hGA := hc.hGA
      hA := fun l => hc.hA l
      hTst := fun l a n n' hnn' => hc.hT l a (e n) (e n') hnn'
      hTstA := fun l a n => hc.hTA l a (e n)
      hV := fun l => hc.hV l
      hstep := ?_
      hp₀ := hc.hp₀
      hp₀1 := hc.hp₀1
      hunit := ?_
      hε := tsum_tol_le ε₀
      hcapU := fun l x => hc.hcapU l x }
  · intro l
    filter_upwards [hc.hcross l _ (tol_pos hε₀ l.length),
      KernelTower.ae_condExpKernel_compl_eq_zero (P := P) (hle l) (hc.hA l)] with ω h1 h2 hAω
    obtain ⟨a, ha⟩ := h1 hAω
    have hU : (⋃ n, cd.Tst ((), l) a n) = ⋃ q, T l a q := e.surjective.iUnion_comp fun q => T l a q
    have hconull : condExpKernel P (rootSigma hκ h12p βA c₀ h W' ζ' s r l) ω
        (cd.A ((), l) ∩ ⋃ n, cd.Tst ((), l) a n) =
        condExpKernel P (rootSigma hκ h12p βA c₀ h W' ζ' s r l) ω (⋃ q, T l a q) := by
      rw [inter_comm, hU]
      exact measure_inter_conull (h2.1 hAω)
    exact cd.exists_candE_of_lt _ ((), l) a (hconull ▸ ha)
  · intro k l hl
    filter_upwards [hc.hnounit k l hl] with ω h1 hAω i
    refine le_trans (measure_mono ?_) (h1 hAω (Nat.unpair i).1)
    intro x hx
    obtain ⟨o, ho⟩ := mem_iUnion.1 hx
    have hO := (cd.candO_subset ((), l) i o) ho.1
    exact mem_iUnion.2 ⟨e o, hO.2, ho.2⟩

end Test

/-! ### The named statement and the reduction -/

/-- **Named statement: GW2's initial cover and the per-candidate claims of the root stages** (follow-up 5 §4.1;
follow-up note A.2–A.5; GB9, pp. 525–526). Binders of `GW2RootCandRStatement`; conclusion: initial events `G₀ r`
covering `{γ(s) ∈ ℍ}` almost surely, and for every root `r` alive events, parameter angles, tests at the candidate
times, unit events and a unit probability satisfying `TestClaims` (no tolerance: the crossing claim holds for every
`ε > 0`). -/
def GW2RootTestStatement : Prop :=
  ∀ κ : ℝ, ∀ hκ : 0 < κ, κ < 4 → ∀ (h12p : Theorem12ParamStatement.{u})
    (βA : BoundaryWord × ℝ × RecData → BoundaryWord), IsStopLaw.{u} κ βA →
    ∀ (b : ℝ → ℝ) (jumps : Finset ℝ) (c₀ : BoundaryWord), IsPiecewiseConstantBoundaryData b jumps →
      c₀.jumps = jumps → (∀ y ∉ jumps, c₀.fn y = b y) →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ Θ : Set ℝ, Θ ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2) → Θ.Countable →
      Ioo (-(Real.pi / 2)) (Real.pi / 2) ⊆ closure Θ →
    ∀ Q : Set ℝ≥0, Q.Countable → Dense Q → (∀ q ∈ Q, 0 < q) →
      ∀ γ : Ω → ℝ≥0 → ℂ, (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (γ ω)) →
        ∀ s : ℝ≥0, ∃ G₀ : ScaledRootIdx Θ Q → Set Ω, (∀ᵐ ω ∂P, γ ω s ∈ H → ∃ r, ω ∈ G₀ r) ∧
          ∀ r, ∃ (A : List (EntryIdx Θ Q) → Set Ω) (ang : ℕ → Θ) (T : List (EntryIdx Θ Q) → ℕ → Q → Set Ω)
            (V : List (EntryIdx Θ Q) → Set Ω) (p₀ : ℝ),
            TestClaims hκ h12p βA b jumps c₀ h W' ζ' s P r (G₀ r) A ang T V p₀

/-- **The repaired root stages from the per-candidate claims.** -/
theorem gw2RootCandRStatement_of_test (hS : GW2RootTestStatement.{u}) : GW2RootCandRStatement.{u} := by
  intro κ hκ hκ4 h12p βA hβA b jumps c₀ hb hc₀J hc₀ Ω _ _ P _ h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd Q hQc hQd hQpos
    γ hγ s
  obtain ⟨G₀, hcov, hroot⟩ :=
    hS κ hκ hκ4 h12p βA hβA b jumps c₀ hb hc₀J hc₀ P h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd Q hQc hQd hQpos γ hγ s
  have : Countable Q := hQc.to_subtype
  have : Infinite Q := (infinite_of_dense hQd).to_subtype
  obtain ⟨hden⟩ := nonempty_denumerable Q
  refine ⟨G₀, hcov, fun r ε₀ hε₀ => ?_⟩
  obtain ⟨A, ang, T, V, p₀, hc⟩ := hroot r
  exact ⟨_, candClaimsR_of_testClaims hβA.1 hh.1 hcf hc (Denumerable.eqv Q).symm hε₀⟩

/-- **The canonical tip exhaustion from the per-candidate claims** (TIP9's chain through the repaired rule). -/
theorem gw2TipExhaustionCanonStatement_of_test (hS : GW2RootTestStatement.{u}) :
    GW2TipExhaustionCanonStatement.{u} :=
  gw2TipExhaustionCanonStatement_of_candR (gw2RootCandRStatement_of_test hS)

end GW2TipSystem

end Theorem14

end InteractingSLE
