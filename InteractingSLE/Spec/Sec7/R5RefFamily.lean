/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5RefCollar
import InteractingSLE.Spec.Sec7.SideC6Heights

/-!
# Lemma R.5 on an R.7 test: the reference family, its charts (clause 3) and the pathwise cover (clause 5)

Packet PROVE-R5-REFCHART. Proof of Lemma R.5 (spec p. 475): "Implement the simultaneous comparison with a countable
family of rational original times and rational chart half-discs … Intersect these countably many probability-one
statements before choosing the suitable member from the realized geometry." For the change pocket of an R.7 test
(`travAll R L r η ψ`, base chart `c` with `c = ψ` on `C = cfPocket R L r`) and references `F i` (the counterflow hull
at the `i`-th rational original time, `R5Phase.refHull`):

* `refChart` (def): the `i`-th reference chart, the relative chart at the capacity reached at the original time
  `rationalOriginalTime i` (independent of `q`);
* `refEvent` (def): the pair event at relative capacity `q` — `ω` in the test, `q` live, the reference time an
  interior visit OR zero, its capacity at most `q`, and `F i ω` the hull at that time;
* `refExc` (def): the exceptional physical set `{η(T⁰(q)), outgoing corner}` (finite: `refExc_finite`);
* **`refEvent_spec`**: CLAUSE 3 of `R5Phase.R5Clauses` with `M := refEvent … q`, `old := refChart …`, at every `q`;
* **`refCover`** (pathwise), **`ae_refCover`**: the GEOMETRIC PART of clause 5 — every real current coordinate whose
  landing avoids `refExc` has a reference `i` with `ω ∈ refEvent … q i` and an unfilled collar
  (`IsRefCollar`: half-disc inclusion, transition limit, old-inverse landing, contact and transition-domain facts).
  At `q = 0` the zero reference is the current chart itself (`isRefCollar_self`); at `q > 0` the reference is a
  rational interior visit before the left stop (`R5Ref.exists_visit_collar`);
* `ae_refHull_eq`: under the original coupling with infinite lifetime the hull identity holds a.s. at every
  rational time; `shiftChart_cfPocket_facts`: the shifted pocket chart of `TwoSeedR5Input` satisfies the chart
  hypotheses;
* the same for the pocket opening at the flow seed (`…Inf`; `refExcInf = {η(T⁰(q))}`).

The heights `b` and the lift differences `d` of clause 5, the lattice phase (clause 2) and the increment laws
(clause 4) are not addressed here (packets PROVE-R5-SAMETIME, -LIFT, -ENLARGED). Ruling R48: nothing here uses
Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open QuantumZipper (H Hbar fwdHull)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Ref

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt Lemma71C PocketCoupling
  PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopField PocketStopSide PocketStopMarked
  PocketStopWallsFin Sec6 R5Phase
open Wire.Current.SideTest (rationalOriginalTime rationalOriginalTime_eqv)

variable {Ω : Type*}

/-! ### The reference family -/

section Defs

/-- **R.5's `i`-th reference chart** (bounded change pocket): the relative chart at the capacity reached at the
rational original time `rationalOriginalTime i`. -/
def refChart (c : Ω → Chart) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (i : ℕ)
    (ω : Ω) : Chart :=
  relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω (rationalOriginalTime i)).toNNReal ω

/-- **R.5's `i`-th reference chart** (change pocket opening at the flow seed). -/
def refChartInf (c : Ω → Chart) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (i : ℕ)
    (ω : Ω) : Chart :=
  relChart c (travAllInf R L r η ψ) (visitCapInf R L r η ψ ω (rationalOriginalTime i)).toNNReal ω

/-- **R.5's pair event of the `i`-th reference at relative capacity `q`** (bounded change pocket): `ω` is in the
test, `q` is live, the reference time is an interior visit or zero, its capacity is at most `q`, and the reference
set `F i ω` is the counterflow hull at the reference time. -/
def refEvent (A : Set Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (W : Ω → ℝ → ℝ) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ)
    (F : ℕ → Ω → Set ℂ) (q : ℝ≥0) (i : ℕ) : Set Ω :=
  {ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) ∧
    (η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r ∨ rationalOriginalTime i = 0) ∧
    (visitCap R L r η ψ ω (rationalOriginalTime i)).toNNReal ≤ q ∧
    F i ω = fwdHull (W ω) (rationalOriginalTime i)}

/-- **R.5's pair event of the `i`-th reference at relative capacity `q`** (change pocket opening at the flow
seed). -/
def refEventInf (A : Set Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (W : Ω → ℝ → ℝ) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ)
    (F : ℕ → Ω → Set ℂ) (q : ℝ≥0) (i : ℕ) : Set Ω :=
  {ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) ∧
    (η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r ∨ rationalOriginalTime i = 0) ∧
    (visitCapInf R L r η ψ ω (rationalOriginalTime i)).toNNReal ≤ q ∧
    F i ω = fwdHull (W ω) (rationalOriginalTime i)}

/-- **R.5's exceptional physical set at relative capacity `q`** (bounded change pocket): the current tip
`η(T⁰(q))` and the outgoing corner (the pole of the Jordan coordinate). -/
def refExc (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (q : ℝ≥0) (ω : Ω) : Set ℂ :=
  {η ω (leftStop R L r η ψ q ω), cfPt (openPt (R ω) (L ω) r)}

/-- **R.5's exceptional physical set at relative capacity `q`** (change pocket opening at the flow seed): the
current tip `η(T⁰(q))`. -/
def refExcInf (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (q : ℝ≥0) (ω : Ω) : Set ℂ :=
  {η ω (leftStopInf R L r η ψ q ω)}

theorem refExc_finite (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (q : ℝ≥0) (ω : Ω) :
    (refExc R L r η ψ q ω).Finite :=
  (Set.finite_singleton _).insert _

theorem refExcInf_finite (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (q : ℝ≥0) (ω : Ω) :
    (refExcInf R L r η ψ q ω).Finite :=
  Set.finite_singleton _

end Defs

/-- The zero reference time is in the family. -/
theorem rationalOriginalTime_eqv_zero : rationalOriginalTime (Denumerable.eqv ℚ 0) = 0 := by
  rw [rationalOriginalTime_eqv, Rat.cast_zero, Real.toNNReal_zero]

/-- A nonnegative rational reference time is in the family. -/
theorem coe_rationalOriginalTime_eqv {s : ℚ} (hs : 0 ≤ (s : ℝ)) :
    ((rationalOriginalTime (Denumerable.eqv ℚ s) : ℝ≥0) : ℝ) = s := by
  rw [rationalOriginalTime_eqv, Real.coe_toNNReal _ hs]

/-- The relative chart at capacity `0` has the base chart's domain. -/
theorem relChart_zero_dom {c : Ω → Chart} {γ : Ω → ℝ → ℂ} {ω : Ω} (hγ : IsDrivenCurve (γ ω)) :
    ((relChart c γ 0 ω).dom : Set ℂ) = (c ω).dom := by
  change interior ((relChart c γ 0 ω).2.1 '' H) = interior ((c ω).2.1 '' H)
  rw [Set.EqOn.image_eq fun z hz => relChart_zero_inv_of_driven hγ hz]

/-! ### The bounded change pocket -/

section Bounded

variable {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}
  {A : Set Ω} {c : Ω → Chart}

/-- The relative capacity reached at time `0` is `0` (bounded change pocket). -/
theorem visitCap_zero {ω : Ω} (hcfg : IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) : visitCap R L r η ψ ω 0 = 0 := by
  obtain ⟨hP, hψ'⟩ := pocket_of_cfg hcfg hψ
  exact relCap_eq_zero_of_le hP hcfg.attach hψ' hP.nonneg

/-- **Clause 3 of `R5Clauses` for the reference family** (bounded change pocket): on the pair event the reference
chart is conformal, contains the current domain and has domain the reference complement `ℍ ∖ liveExt(F i, 0)`. -/
theorem refEvent_spec (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) (F : ℕ → Ω → Set ℂ) (q : ℝ≥0) :
    ∀ i, ∀ ω ∈ refEvent A R L r W η ψ F q i, ω ∈ A ∧ (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) ∧
      (refChart c R L r η ψ i ω).IsConformal ∧
      ((relChart c (travAll R L r η ψ) q ω).dom : Set ℂ) ⊆ (refChart c R L r η ψ i ω).dom ∧
      ((refChart c R L r η ψ i ω).dom : Set ℂ) =
        H \ liveExt A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) (F i) 0 ω := by
  rintro i ω ⟨hω, hq, hv | hz, hQ, hF⟩
  · exact ⟨hω, hq, reference_chart_at_visit hω (hcfg ω hω) (hψ ω hω) (hc ω hω) (hdom ω hω) (heq ω hω) hv hF hq hQ⟩
  · have hγ := ((hcfg ω hω).isDrivenCurve (hψ ω hω)).1
    have h0 : (visitCap R L r η ψ ω (rationalOriginalTime i)).toNNReal = 0 := by
      rw [hz, NNReal.coe_zero, visitCap_zero (hcfg ω hω) (hψ ω hω), Real.toNNReal_zero]
    have hCH : cfPocket (R ω) (L ω) r ⊆ H := by
      rw [← hdom ω hω, (hc ω hω).coe_dom]
      exact (hc ω hω).2.1.image_subset
    have hlive : ((0 : ℝ≥0) : ℝ≥0∞) < capLife (travAll R L r η ψ ω) := by
      rw [ENNReal.coe_zero]
      exact PocketPhaseMeans.capLife_pos hγ
    simp only [refChart, h0]
    refine ⟨hω, hq, isConformal_relChart_of_driven (c := c) (γ := travAll R L r η ψ) hγ hlive (hc ω hω),
      relChart_dom_antitone (hc ω hω) hγ hq (show (0 : ℝ≥0) ≤ q from zero_le), ?_⟩
    rw [relChart_zero_dom (c := c) (γ := travAll R L r η ψ) hγ, hdom ω hω, H_diff_liveExt_zero hω hγ, hF, hz,
      NNReal.coe_zero, QuantumZipper.RS.fwdHull_zero_eq_empty (hcfg ω hω).continuous_W, sdiff_empty]
    exact (inter_eq_left.2 hCH).symm

/-- **The geometric part of clause 5 of `R5Clauses`, pathwise** (bounded change pocket): on the event where every
reference set is the hull at its time, every real current coordinate whose landing avoids `refExc` has a reference
`i` with `ω ∈ refEvent … q i` and an unfilled R.5 collar. -/
theorem refCover {ω : Ω} (hω : ω ∈ A) (hcfg : IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {F : ℕ → Ω → Set ℂ} (hHull : ∀ i, F i ω = fwdHull (W ω) (rationalOriginalTime i)) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω)) (ξ : ℝ)
    (hX : extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∉ refExc R L r η ψ q ω) :
    ∃ (i : ℕ) (x ε : ℝ), ω ∈ refEvent A R L r W η ψ F q i ∧
        (η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r ∨ q = 0) ∧
      IsRefCollar (refChart c R L r η ψ i ω) (relChart c (travAll R L r η ψ) q ω) ξ
        (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ) x ε := by
  have hγ := (hcfg.isDrivenCurve hψ).1
  have hNow := isConformal_relChart_of_driven (c := c) (γ := travAll R L r η ψ) hγ hq hc
  obtain ⟨hLanding, -, -⟩ := current_landing hω hcfg hψ hc hdom heq hq ξ
  rcases (show (0 : ℝ≥0) ≤ q from zero_le).eq_or_lt with hq0 | hq0
  · subst hq0
    have h0 : (visitCap R L r η ψ ω (rationalOriginalTime (Denumerable.eqv ℚ 0))).toNNReal = 0 := by
      rw [rationalOriginalTime_eqv_zero, NNReal.coe_zero, visitCap_zero hcfg hψ, Real.toNNReal_zero]
    refine ⟨Denumerable.eqv ℚ 0, ξ, 1, ⟨hω, hq, Or.inr rationalOriginalTime_eqv_zero, h0.le, hHull _⟩,
      Or.inr rfl, ?_⟩
    simp only [refChart, h0]
    exact isRefCollar_self hNow hLanding
  · simp only [refExc, mem_insert_iff, mem_singleton_iff, not_or] at hX
    obtain ⟨s, hs0, hv, hQ, -, x, ε, hcol⟩ := exists_visit_collar hω hcfg hψ hc hdom heq hq0 hq ξ hX.1 hX.2
    have hti := coe_rationalOriginalTime_eqv hs0
    refine ⟨Denumerable.eqv ℚ s, x, ε, ⟨hω, hq, Or.inl (by rw [hti]; exact hv), by rw [hti]; exact hQ,
      hHull _⟩, Or.inl (by rw [hti]; exact hv), ?_⟩
    simp only [refChart, hti]
    exact hcol

/-- **A collar landing inside the pocket is a point of the reference set** (bounded change pocket): on the pair event,
the landing of an unfilled collar of the reference chart lies in `F i ω` whenever it lies in `C`. -/
theorem mem_ref_of_collar (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) {F : ℕ → Ω → Set ℂ} {q : ℝ≥0} {i : ℕ}
    {ω : Ω} (hM : ω ∈ refEvent A R L r W η ψ F q i) {ξ : ℝ} {p : ℂ} {x ε : ℝ}
    (hcol : IsRefCollar (refChart c R L r η ψ i ω) (relChart c (travAll R L r η ψ) q ω) ξ p x ε)
    (hp : p ∈ cfPocket (R ω) (L ω) r) : p ∈ F i ω := by
  obtain ⟨hω, -, hOld, -, hOldDom⟩ := refEvent_spec hcfg hψ hc hdom heq F q i ω hM
  have hγ := ((hcfg ω hω).isDrivenCurve (hψ ω hω)).1
  have hn : p ∉ ((refChart c R L r η ψ i ω).dom : Set ℂ) := hcol.notMem_dom hOld
  rw [hOldDom, H_diff_liveExt_zero hω hγ] at hn
  have hCH : cfPocket (R ω) (L ω) r ⊆ H := by
    rw [← hdom ω hω, (hc ω hω).coe_dom]
    exact (hc ω hω).2.1.image_subset
  by_contra hF
  exact hn ⟨hp, hCH hp, hF⟩

/-- **The geometric part of clause 5 of `R5Clauses`** (bounded change pocket), in the clause's almost-sure form: the
hull identities at all rational times are intersected before the realized geometry selects the reference. -/
theorem ae_refCover {_ : MeasurableSpace Ω} {P : Measure Ω}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) {F : ℕ → Ω → Set ℂ}
    (hHull : ∀ᵐ ω ∂P, ω ∈ A → ∀ i, F i ω = fwdHull (W ω) (rationalOriginalTime i)) (q : ℝ≥0) :
    ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) → ∀ ξ : ℝ,
      extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∉ refExc R L r η ψ q ω →
      ∃ (i : ℕ) (x ε : ℝ), ω ∈ refEvent A R L r W η ψ F q i ∧
          (η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r ∨ q = 0) ∧
        IsRefCollar (refChart c R L r η ψ i ω) (relChart c (travAll R L r η ψ) q ω) ξ
          (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ) x ε := by
  filter_upwards [hHull] with ω hH hω hq ξ hX
  exact refCover hω (hcfg ω hω) (hψ ω hω) (hc ω hω) (hdom ω hω) (heq ω hω) (hH hω) hq ξ hX

/-- **The shifted pocket chart of an R.7 test satisfies the chart hypotheses** (bounded change pocket). -/
theorem shiftChart_cfPocket_facts (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (n : Ω → ℤ) :
    ∀ ω ∈ A, (shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)).IsConformal ∧
      ((shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)).dom : Set ℂ) =
        cfPocket (R ω) (L ω) r ∧
      EqOn (shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)).1 (ψ ω)
        (cfPocket (R ω) (L ω) r) :=
  shiftChart_dom_facts (fun ω hω => (pocket_of_cfg (hcfg ω hω) (hψ ω hω)).1.isOpen)
    (fun ω hω => WangWu.image_negInv_subset_H (hcfg ω hω).conf.changePocket_subset_H) (fun ω hω => (hψ ω hω).2.2.2.1) n

end Bounded

/-! ### The change pocket opening at the flow seed -/

section Inf

variable {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}
  {A : Set Ω} {c : Ω → Chart}

/-- The relative capacity reached at time `0` is `0` (pocket opening at the flow seed). -/
theorem visitCapInf_zero {ω : Ω} (hcfg : IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) : visitCapInf R L r η ψ ω 0 = 0 := by
  obtain ⟨hP, hψ'⟩ := pocket_of_cfgInf hcfg hψ
  exact relCapInf_eq_zero_of_le hP hcfg.attach hψ' hP.nonneg

/-- **Clause 3 of `R5Clauses` for the reference family** (pocket opening at the flow seed). -/
theorem refEventInf_spec (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) (F : ℕ → Ω → Set ℂ) (q : ℝ≥0) :
    ∀ i, ∀ ω ∈ refEventInf A R L r W η ψ F q i, ω ∈ A ∧ (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) ∧
      (refChartInf c R L r η ψ i ω).IsConformal ∧
      ((relChart c (travAllInf R L r η ψ) q ω).dom : Set ℂ) ⊆ (refChartInf c R L r η ψ i ω).dom ∧
      ((refChartInf c R L r η ψ i ω).dom : Set ℂ) =
        H \ liveExt A (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) (F i) 0 ω := by
  rintro i ω ⟨hω, hq, hv | hz, hQ, hF⟩
  · exact ⟨hω, hq,
      reference_chart_at_visitInf hω (hcfg ω hω) (hψ ω hω) (hc ω hω) (hdom ω hω) (heq ω hω) hv hF hq hQ⟩
  · have hγ := ((hcfg ω hω).isDrivenCurve (hψ ω hω)).1
    have h0 : (visitCapInf R L r η ψ ω (rationalOriginalTime i)).toNNReal = 0 := by
      rw [hz, NNReal.coe_zero, visitCapInf_zero (hcfg ω hω) (hψ ω hω), Real.toNNReal_zero]
    have hCH : cfPocket (R ω) (L ω) r ⊆ H := by
      rw [← hdom ω hω, (hc ω hω).coe_dom]
      exact (hc ω hω).2.1.image_subset
    have hlive : ((0 : ℝ≥0) : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) := by
      rw [ENNReal.coe_zero]
      exact PocketPhaseMeans.capLife_pos hγ
    simp only [refChartInf, h0]
    refine ⟨hω, hq, isConformal_relChart_of_driven (c := c) (γ := travAllInf R L r η ψ) hγ hlive (hc ω hω),
      relChart_dom_antitone (hc ω hω) hγ hq (show (0 : ℝ≥0) ≤ q from zero_le), ?_⟩
    rw [relChart_zero_dom (c := c) (γ := travAllInf R L r η ψ) hγ, hdom ω hω, H_diff_liveExt_zero hω hγ, hF, hz,
      NNReal.coe_zero, QuantumZipper.RS.fwdHull_zero_eq_empty (hcfg ω hω).continuous_W, sdiff_empty]
    exact (inter_eq_left.2 hCH).symm

/-- **The geometric part of clause 5 of `R5Clauses`, pathwise** (pocket opening at the flow seed). -/
theorem refCoverInf {ω : Ω} (hω : ω ∈ A) (hcfg : IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {F : ℕ → Ω → Set ℂ} (hHull : ∀ i, F i ω = fwdHull (W ω) (rationalOriginalTime i)) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)) (ξ : ℝ)
    (hX : extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∉ refExcInf R L r η ψ q ω) :
    ∃ (i : ℕ) (x ε : ℝ), ω ∈ refEventInf A R L r W η ψ F q i ∧
        (η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r ∨ q = 0) ∧
      IsRefCollar (refChartInf c R L r η ψ i ω) (relChart c (travAllInf R L r η ψ) q ω) ξ
        (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ) x ε := by
  have hγ := (hcfg.isDrivenCurve hψ).1
  have hNow := isConformal_relChart_of_driven (c := c) (γ := travAllInf R L r η ψ) hγ hq hc
  obtain ⟨hLanding, -, -⟩ := current_landingInf hω hcfg hψ hc hdom heq hq ξ
  rcases (show (0 : ℝ≥0) ≤ q from zero_le).eq_or_lt with hq0 | hq0
  · subst hq0
    have h0 : (visitCapInf R L r η ψ ω (rationalOriginalTime (Denumerable.eqv ℚ 0))).toNNReal = 0 := by
      rw [rationalOriginalTime_eqv_zero, NNReal.coe_zero, visitCapInf_zero hcfg hψ, Real.toNNReal_zero]
    refine ⟨Denumerable.eqv ℚ 0, ξ, 1, ⟨hω, hq, Or.inr rationalOriginalTime_eqv_zero, h0.le, hHull _⟩,
      Or.inr rfl, ?_⟩
    simp only [refChartInf, h0]
    exact isRefCollar_self hNow hLanding
  · simp only [refExcInf, mem_singleton_iff] at hX
    obtain ⟨s, hs0, hv, hQ, -, x, ε, hcol⟩ := exists_visit_collarInf hω hcfg hψ hc hdom heq hq0 hq ξ hX
    have hti := coe_rationalOriginalTime_eqv hs0
    refine ⟨Denumerable.eqv ℚ s, x, ε, ⟨hω, hq, Or.inl (by rw [hti]; exact hv), by rw [hti]; exact hQ,
      hHull _⟩, Or.inl (by rw [hti]; exact hv), ?_⟩
    simp only [refChartInf, hti]
    exact hcol

/-- **A collar landing inside the pocket is a point of the reference set** (pocket opening at the flow seed): on the
pair event, the landing of an unfilled collar of the reference chart lies in `F i ω` whenever it lies in `C`. -/
theorem mem_ref_of_collarInf (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) {F : ℕ → Ω → Set ℂ} {q : ℝ≥0} {i : ℕ}
    {ω : Ω} (hM : ω ∈ refEventInf A R L r W η ψ F q i) {ξ : ℝ} {p : ℂ} {x ε : ℝ}
    (hcol : IsRefCollar (refChartInf c R L r η ψ i ω) (relChart c (travAllInf R L r η ψ) q ω) ξ p x ε)
    (hp : p ∈ cfPocket (R ω) (L ω) r) : p ∈ F i ω := by
  obtain ⟨hω, -, hOld, -, hOldDom⟩ := refEventInf_spec hcfg hψ hc hdom heq F q i ω hM
  have hγ := ((hcfg ω hω).isDrivenCurve (hψ ω hω)).1
  have hn : p ∉ ((refChartInf c R L r η ψ i ω).dom : Set ℂ) := hcol.notMem_dom hOld
  rw [hOldDom, H_diff_liveExt_zero hω hγ] at hn
  have hCH : cfPocket (R ω) (L ω) r ⊆ H := by
    rw [← hdom ω hω, (hc ω hω).coe_dom]
    exact (hc ω hω).2.1.image_subset
  by_contra hF
  exact hn ⟨hp, hCH hp, hF⟩

/-- **The geometric part of clause 5 of `R5Clauses`** (pocket opening at the flow seed), almost-sure form. -/
theorem ae_refCoverInf {_ : MeasurableSpace Ω} {P : Measure Ω}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) {F : ℕ → Ω → Set ℂ}
    (hHull : ∀ᵐ ω ∂P, ω ∈ A → ∀ i, F i ω = fwdHull (W ω) (rationalOriginalTime i)) (q : ℝ≥0) :
    ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) → ∀ ξ : ℝ,
      extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∉ refExcInf R L r η ψ q ω →
      ∃ (i : ℕ) (x ε : ℝ), ω ∈ refEventInf A R L r W η ψ F q i ∧
          (η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r ∨ q = 0) ∧
        IsRefCollar (refChartInf c R L r η ψ i ω) (relChart c (travAllInf R L r η ψ) q ω) ξ
          (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ) x ε := by
  filter_upwards [hHull] with ω hH hω hq ξ hX
  exact refCoverInf hω (hcfg ω hω) (hψ ω hω) (hc ω hω) (hdom ω hω) (heq ω hω) (hH hω) hq ξ hX

/-- **The shifted pocket chart of an R.7 test satisfies the chart hypotheses** (pocket opening at the flow seed). -/
theorem shiftChart_cfPocketInf_facts (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (n : Ω → ℤ) :
    ∀ ω ∈ A, (shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)).IsConformal ∧
      ((shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)).dom : Set ℂ) =
        cfPocket (R ω) (L ω) r ∧
      EqOn (shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)).1 (ψ ω)
        (cfPocket (R ω) (L ω) r) :=
  shiftChart_dom_facts (fun ω hω => (pocket_of_cfgInf (hcfg ω hω) (hψ ω hω)).1.isOpen)
    (fun ω hω => (pocket_of_cfgInf (hcfg ω hω) (hψ ω hω)).1.subset_H) (fun ω hω => (hψ ω hω).2.2.2.1) n

end Inf

/-! ### The hull identities of the R.7 references -/

section Hull

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕₀ : Filtration ℝ≥0 mΩ}
  {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {h'' : Ω → DistOn upperHalfPlaneOpens}

/-- **The R.7 references are the counterflow hulls at their times, simultaneously, almost surely** (under the
original coupling with infinite lifetime): the hypothesis `hHull` of `ae_refCover(Inf)` for `F = refHull W' ζ'`. -/
theorem ae_refHull_eq (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'')
    (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤) :
    ∀ᵐ ω ∂P, ∀ i, refHull W' ζ' i ω =
      fwdHull (fun s : ℝ => W' s.toNNReal ω) (rationalOriginalTime i) := by
  filter_upwards [ae_regHull_eq hC hζ] with ω h i
  exact h _

/-- **The R.7 references are the hulls of the continuous driver at their times** wherever the lifetime is
infinite. -/
theorem refHull_eq_of_continuous {Ω : Type*} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {ω : Ω}
    (hW : Continuous fun s : ℝ => W' s.toNNReal ω) (hζ : ζ' ω = ⊤) (i : ℕ) :
    refHull W' ζ' i ω = fwdHull (fun s : ℝ => W' s.toNNReal ω) (rationalOriginalTime i) := by
  have hc : Continuous fun s : ℝ≥0 => W' s ω := by
    have h := hW.comp NNReal.continuous_coe
    simpa only [Function.comp_def, Real.toNNReal_coe] using h
  exact regHull_eq hc hζ _

end Hull

end InteractingSLE.Sec7.R5Ref
