/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1ChainK2
import InteractingSLE.Spec.Restart.DomainMarkovAux79Line
import InteractingSLE.Spec.Supplement.SB4SewLawMean

/-!
# The relative chain, part 4: (S) and (L) with infinite lifetime from deterministic physical lines

Packet PROVE-BW1-CHAIN. In BW1 the relative continuation is read at the physical counterflow times `t`; its relative
capacity `a(t)` is finite before the first contact time `T` with the retained set and **explodes at the finite time
`T`** ("Its relative capacity lifetime is infinite; `T` is finite in the original counterflow clock"). The landed
discretization `Aux79.hasSafeLaw_of_lineKernel` / `hasSafeMembers_of_lineLocal` needs a real-valued continuous clock;
here the clock `a : ℝ≥0 → Ω → ℝ≥0∞` is extended-valued (`a t = ⊤` from `T` on), and it is capped at every level `N`
(`capClock a N t = min (a t) N`): with lifetime `N` the lines at which the capped clock reaches `N` are never used, so
the line data are only asked **before the contact** (`a t < ⊤`). Intersecting over `N` gives K2's inputs with
infinite lifetime:

* `capClock` and its continuity, monotonicity, adaptedness; `setOf_le_capClock_of_le` / `_of_lt`;
* **`hasSafeLaw_top_of_lineKernel`**: (S) with lifetime `⊤` for the chart field from the line kernels (Aux. 77 at the
  line `t`) and the line mean identities (Aux. 79 at the line `t`), both only before the contact;
* **`hasSafeMembers_top_of_lineLocal`**: (L) with lifetime `⊤` from the history-marked locality of the physical
  line sets.

The time change is any filtration `𝓗'` whose `q`-events are cut into `𝓖_t`-events by `{q ≤ a t}` (e.g. the stopping
σ-algebras of the first passages of `a`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H fwdHull zeroGFFTestCov)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.BW1Chain

open Restart.DomainMarkov Restart.DomainMarkov.K2 Restart.DomainMarkov.Aux79

section Clock

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {a : ℝ≥0 → Ω → ℝ≥0∞}

/-- **The relative clock capped at the level `N`.** -/
def capClock (a : ℝ≥0 → Ω → ℝ≥0∞) (N : ℝ≥0) : ℝ≥0 → Ω → ℝ≥0 := fun t ω => (min (a t ω) N).toNNReal

theorem coe_capClock (N : ℝ≥0) (t : ℝ≥0) (ω : Ω) : (capClock a N t ω : ℝ≥0∞) = min (a t ω) N :=
  ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))

theorem capClock_eq_of_lt {N : ℝ≥0} {t : ℝ≥0} {ω : Ω} (h : a t ω < N) : capClock a N t ω = (a t ω).toNNReal := by
  simp only [capClock, min_eq_left h.le]

theorem lt_of_coe_capClock_lt {N : ℝ≥0} {t : ℝ≥0} {ω : Ω} (h : (capClock a N t ω : ℝ≥0∞) < N) : a t ω < N := by
  rw [coe_capClock] at h
  rcases min_lt_iff.1 h with h | h
  · exact h
  · exact absurd h (lt_irrefl _)

theorem continuous_capClock (hac : ∀ ω, Continuous fun t => a t ω) (N : ℝ≥0) (ω : Ω) :
    Continuous fun t => capClock a N t ω :=
  ENNReal.continuousOn_toNNReal.comp_continuous ((hac ω).min continuous_const) fun _ =>
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)

theorem monotone_capClock (ham : ∀ ω, Monotone fun t => a t ω) (N : ℝ≥0) (ω : Ω) :
    Monotone fun t => capClock a N t ω := fun s t hst => by
  have h := min_le_min_right (N : ℝ≥0∞) (ham ω hst)
  rw [← coe_capClock, ← coe_capClock] at h
  exact_mod_cast h

theorem capClock_zero (ha0 : ∀ ω, a 0 ω = 0) (N : ℝ≥0) (ω : Ω) : capClock a N 0 ω = 0 := by
  simp only [capClock, ha0 ω, zero_le, min_eq_left, ENNReal.toNNReal_zero]

theorem measurable_capClock {𝓖 : Filtration ℝ≥0 mΩ} (haa : ∀ t, Measurable[𝓖 t] (a t)) (N : ℝ≥0) (t : ℝ≥0) :
    Measurable[𝓖 t] (capClock a N t) :=
  ENNReal.measurable_toNNReal.comp ((haa t).min measurable_const)

theorem setOf_le_capClock_of_le {q N : ℝ≥0} (hqN : q ≤ N) (t : ℝ≥0) :
    {ω | q ≤ capClock a N t ω} = {ω | (q : ℝ≥0∞) ≤ a t ω} := by
  ext ω
  simp only [mem_ofPred_eq]
  rw [← ENNReal.coe_le_coe, coe_capClock, le_min_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, ENNReal.coe_le_coe.2 hqN⟩⟩

theorem setOf_le_capClock_of_lt {q N : ℝ≥0} (hNq : N < q) (t : ℝ≥0) :
    {ω | q ≤ capClock a N t ω} = ∅ := by
  ext ω
  simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
  rw [← ENNReal.coe_lt_coe, coe_capClock]
  exact lt_of_le_of_lt (min_le_right _ _) (ENNReal.coe_lt_coe.2 hNq)

/-- The cut property of the time change for every capped clock. -/
theorem measurableSet_inter_capClock {𝓖 𝓗' : Filtration ℝ≥0 mΩ}
    (h𝓗' : ∀ q D, MeasurableSet[𝓗' q] D → ∀ t, MeasurableSet[𝓖 t] (D ∩ {ω | (q : ℝ≥0∞) ≤ a t ω}))
    (N q : ℝ≥0) (D : Set Ω) (hD : MeasurableSet[𝓗' q] D) (t : ℝ≥0) :
    MeasurableSet[𝓖 t] (D ∩ {ω | q ≤ capClock a N t ω}) := by
  rcases le_or_gt q N with hqN | hNq
  · rw [setOf_le_capClock_of_le hqN]
    exact h𝓗' q D hD t
  · rw [setOf_le_capClock_of_lt hNq, inter_empty]
    exact @MeasurableSet.empty Ω (𝓖 t)

end Clock

section Lines

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {nL nR : ℕ} {κ : ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {a : ℝ≥0 → Ω → ℝ≥0∞}

/-- Regularity with infinite lifetime gives regularity with any lifetime. -/
theorem isForceReg_of_top {ζ : Ω → ℝ≥0∞} {ω : Ω} (h : IsForceReg W VL VR (fun _ => ⊤) ω) :
    IsForceReg W VL VR ζ ω :=
  ⟨h.1, h.2.1.mono fun _ _ => ENNReal.coe_lt_top, fun i => (h.2.2.1 i).mono fun _ _ => ENNReal.coe_lt_top,
    fun j => (h.2.2.2.1 j).mono fun _ _ => ENNReal.coe_lt_top, fun t _ => h.2.2.2.2 t ENNReal.coe_lt_top⟩

/-- The line safe event of the capped clock is the line safe event of the clock below the level. -/
theorem lineSafe_capClock_eq (N : ℝ≥0) (C : Set ℂ) (t : ℝ≥0) :
    lineSafe (capClock a N) W (fun _ => (N : ℝ≥0∞)) C t =
      {ω | a t ω < N} ∩ {ω | a t ω < ⊤ ∧ Disjoint C (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)} := by
  ext ω
  simp only [lineSafe, mem_ofPred_eq, mem_inter_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have hlt := lt_of_coe_capClock_lt h1
    rw [capClock_eq_of_lt hlt] at h2
    exact ⟨hlt, hlt.trans ENNReal.coe_lt_top, h2⟩
  · rintro ⟨h1, -, h2⟩
    refine ⟨?_, by rw [capClock_eq_of_lt h1]; exact h2⟩
    rw [coe_capClock, min_eq_left h1.le]
    exact h1

theorem measurableSet_lineSafe_capClock {𝓖 : Filtration ℝ≥0 mΩ} (haa : ∀ t, Measurable[𝓖 t] (a t)) {C : Set ℂ}
    {t : ℝ≥0} (hS : MeasurableSet[𝓖 t]
      {ω | a t ω < ⊤ ∧ Disjoint C (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)}) (N : ℝ≥0) :
    MeasurableSet[𝓖 t] (lineSafe (capClock a N) W (fun _ => (N : ℝ≥0∞)) C t) := by
  rw [lineSafe_capClock_eq]
  exact (measurableSet_lt (haa t) measurable_const).inter hS

/-- **(S) with infinite lifetime from the line data before the contact.** Let `a` be a continuous nondecreasing
adapted extended clock from `0` (the relative capacity reached at the physical time `t`, `⊤` from the contact on),
which reaches every level on `F`, and `𝓗'` a time change of `𝓖` along `a`. Suppose that at every deterministic
physical time `t`, almost surely on `F` **before the contact** (`a t < ⊤`): the physical field paired with test
functions supported in `inv(ℍ ∖ K̃_{a t})` is, given `𝒢L t ⊇ 𝓖_t`, Gaussian with mean `M t` and the zero-boundary
covariance of that domain (Aux. 77 at the line); and on the line safe event the chart transport of `M t` is the
canonical mean of the continuation at `a t` (Aux. 79 at the line). Then the chart field has K2's (S) with infinite
lifetime for `𝓗'`. -/
theorem hasSafeLaw_top_of_lineKernel {𝓖 𝓗' : Filtration ℝ≥0 mΩ} {F : Set Ω} (hF : MeasurableSet[𝓖 0] F)
    {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (σa k : ℝ) (hac : ∀ ω, Continuous fun t => a t ω) (ham : ∀ ω, Monotone fun t => a t ω)
    (ha0 : ∀ ω, a 0 ω = 0) (haa : ∀ t, Measurable[𝓖 t] (a t))
    (h𝓗' : ∀ q D, MeasurableSet[𝓗' q] D → ∀ t, MeasurableSet[𝓖 t] (D ∩ {ω | (q : ℝ≥0∞) ≤ a t ω}))
    (hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → ∃ t, (q : ℝ≥0∞) ≤ a t ω)
    (hreg : ∀ᵐ ω ∂P, ω ∈ F → IsForceReg W VL VR (fun _ => ⊤) ω)
    (hS : ∀ (ψ : TestOn upperHalfPlaneOpens) t, MeasurableSet[𝓖 t]
      {ω | a t ω < ⊤ ∧ Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)})
    (𝒢L : ℝ≥0 → MeasurableSpace Ω) (h𝒢L : ∀ t, 𝓖 t ≤ 𝒢L t) (h𝒢Lm : ∀ t, 𝒢L t ≤ mΩ)
    (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (hker : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ F → a t ω < ⊤ →
      tsupport φ ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal) →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢L t] ω =
        Complex.exp (Complex.I * (M t ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω)
            (a t ω).toNNReal)) φ φ : ℝ) : ℂ)))
    (hmean : ∀ (t : ℝ≥0) (ψ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ F → a t ω < ⊤ →
      Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal) →
      Chart.chartTransport (hc ω) 1 σa k (M t ω) ψ =
        ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal
          (bheProc κ ρL ρR W VL VR ω (a t ω).toNNReal) z * ψ z) :
    HasSafeLaw κ ρL ρR P 𝓗' F (fun _ => ⊤) W VL VR fun ω => Chart.chartTransport (hc ω) 1 σa k (h ω) := by
  have hN : ∀ N : ℝ≥0, HasSafeLaw κ ρL ρR P 𝓗' F (fun _ => (N : ℝ≥0∞)) W VL VR
      fun ω => Chart.chartTransport (hc ω) 1 σa k (h ω) := by
    intro N
    refine hasSafeLaw_of_lineKernel (Qc := capClock a N) hF hc hdom hfwd hliftm hliftc hh σa k
      (continuous_capClock hac N) (monotone_capClock ham N) (capClock_zero ha0 N) (measurable_capClock haa N)
      (measurableSet_inter_capClock h𝓗' N) ?_ ?_ (fun ψ t => measurableSet_lineSafe_capClock haa (hS ψ t) N)
      𝒢L h𝒢L h𝒢Lm M ?_ ?_
    · intro q
      filter_upwards [hreach q] with ω hω hωF hqN
      obtain ⟨t, ht⟩ := hω hωF
      refine ⟨t, ?_⟩
      rw [← ENNReal.coe_le_coe, coe_capClock]
      exact le_min ht hqN.le
    · filter_upwards [hreg] with ω hω hωF using isForceReg_of_top (hω hωF)
    · intro t φ
      filter_upwards [hker t φ] with ω hω hωF hlt hsupp
      have hlt' := lt_of_coe_capClock_lt hlt
      rw [capClock_eq_of_lt hlt'] at hsupp ⊢
      exact hω hωF (hlt'.trans ENNReal.coe_lt_top) hsupp
    · intro t ψ
      filter_upwards [hmean t ψ] with ω hω hωF hS'
      rw [lineSafe_capClock_eq] at hS'
      rw [capClock_eq_of_lt hS'.1]
      exact hω hωF hS'.2.1 hS'.2.2
  intro ψ q D hD hDs
  refine hN (q + 1) ψ q D hD ?_
  filter_upwards [hDs] with ω h1 hωD
  obtain ⟨hF', -, hdis⟩ := h1 hωD
  exact ⟨hF', ENNReal.coe_lt_coe.2 (lt_add_one q), hdis⟩

open LocalSets WholeField in
/-- **(L) with infinite lifetime from the history-marked locality of the physical line sets before the contact**
(`Aux79.hasSafeMembers_of_lineLocal` for every capped clock). At every deterministic physical time `t`, the line set
`B t` is a hitting-measurable relatively closed history-marked local set of the centred field for marks `ℋ t ⊇ 𝓖_t`,
and almost surely on `F` before the contact `ℍ ∖ B t = inv(ℍ ∖ K̃_{a t})`. -/
theorem hasSafeMembers_top_of_lineLocal {𝓖 𝓗' : Filtration ℝ≥0 mΩ} {F : Set Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P) {c : Ω → Chart}
    (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hlift : ∀ ω, InnerProductSpace.HarmonicOnNhd (c ω).2.2 (c ω).dom) (σa k : ℝ)
    (hac : ∀ ω, Continuous fun t => a t ω) (ham : ∀ ω, Monotone fun t => a t ω)
    (ha0 : ∀ ω, a 0 ω = 0) (haa : ∀ t, Measurable[𝓖 t] (a t))
    (h𝓗' : ∀ q D, MeasurableSet[𝓗' q] D → ∀ t, MeasurableSet[𝓖 t] (D ∩ {ω | (q : ℝ≥0∞) ≤ a t ω}))
    (hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → ∃ t, (q : ℝ≥0∞) ≤ a t ω)
    (hreg : ∀ᵐ ω ∂P, ω ∈ F → IsForceReg W VL VR (fun _ => ⊤) ω)
    (hS : ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t, MeasurableSet[𝓖 t]
      {ω | a t ω < ⊤ ∧ Disjoint (Coupling.ballsK Fb) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)})
    (ℋ : ℝ≥0 → MeasurableSpace Ω) (h𝓖ℋ : ∀ t, 𝓖 t ≤ ℋ t) (hℋ : ∀ t, ℋ t ≤ mΩ)
    (B : ℝ≥0 → Ω → Set ℂ) (hBm : ∀ t, Measurable[mΩ, hittingSigma] (B t))
    (hBc : ∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω))
    (hloc : ∀ t, IsHistoryAvoidanceLocal (ℋ t) (B t) (centredField h u₀) P)
    (hBK : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → a t ω < ⊤ →
      H \ B t ω = (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)) :
    HasSafeMembers P 𝓗' F (fun _ => ⊤) W fun ω => Chart.chartTransport (hc ω) 1 σa k (h ω) := by
  have hN : ∀ N : ℝ≥0, HasSafeMembers P 𝓗' F (fun _ => (N : ℝ≥0∞)) W
      fun ω => Chart.chartTransport (hc ω) 1 σa k (h ω) := by
    intro N
    refine hasSafeMembers_of_lineLocal (Qc := capClock a N) (VL := VL) (VR := VR) hhm hu₀ hh0 hc hdom hfwd
      hliftm hliftc hlift σa k (continuous_capClock hac N) (monotone_capClock ham N) (capClock_zero ha0 N)
      (measurable_capClock haa N) (measurableSet_inter_capClock h𝓗' N) ?_ ?_
      (fun Fb t => measurableSet_lineSafe_capClock haa (hS Fb t) N) ℋ h𝓖ℋ hℋ B hBm hBc hloc ?_
    · intro q
      filter_upwards [hreach q] with ω hω hωF hqN
      obtain ⟨t, ht⟩ := hω hωF
      refine ⟨t, ?_⟩
      rw [← ENNReal.coe_le_coe, coe_capClock]
      exact le_min ht hqN.le
    · filter_upwards [hreg] with ω hω hωF using isForceReg_of_top (hω hωF)
    · intro t
      filter_upwards [hBK t] with ω hω hωF hlt
      have hlt' := lt_of_coe_capClock_lt hlt
      rw [capClock_eq_of_lt hlt']
      exact hω hωF (hlt'.trans ENNReal.coe_lt_top)
  intro s Fb hFb D hD hDs
  refine hN (s + 1) s Fb hFb D hD ?_
  filter_upwards [hDs] with ω h1 hωD
  obtain ⟨hF', -, hdis⟩ := h1 hωD
  exact ⟨hF', ENNReal.coe_lt_coe.2 (lt_add_one s), hdis⟩

open LocalSets in
/-- **Aux. 77 at the line from history-marked locality and the active germ mean, before the contact**
(`SB.SewLaw.ae_retained_physical_cexp_of_mean` at every line, as `GW1RestartLaw.ae_physical_kernel_of_activeMean`
with the lifetime replaced by the contact `a t < ⊤`). If the physical line set `B t` is a hitting-measurable relatively
closed history-marked local set of the centred field for marks `ℋ t`, and before the contact its germ mean given
`germ(B t) ⊔ ℋ t` is `M t − 𝔥⁰` against tests off `B t`, then given `ℋ t` the field against tests off `B t` is
Gaussian with mean `M t` and the zero-boundary covariance of `ℍ ∖ B t`. With `ℍ ∖ B t = inv(ℍ ∖ K̃_{a t})` this is
`hker` of `hasSafeLaw_top_of_lineKernel`. -/
theorem ae_lineKernel_of_activeMean {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P)
    {ℋ : ℝ≥0 → MeasurableSpace Ω} (hℋ : ∀ t, ℋ t ≤ mΩ) {F : Set Ω} (hF : ∀ t, MeasurableSet[ℋ t] F)
    (haa : ∀ t, Measurable[ℋ t] (a t)) {B : ℝ≥0 → Ω → Set ℂ} (hBm : ∀ t, Measurable[ℋ t, hittingSigma] (B t))
    (hBc : ∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω))
    (hloc : ∀ t, WholeField.IsHistoryAvoidanceLocal (ℋ t) (B t) (WholeField.centredField h u₀) P)
    {M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens} (hM : ∀ t, Measurable[ℋ t] (M t))
    (hgm : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ F → a t ω < ⊤ →
      tsupport φ ⊆ H \ B t ω →
        P[fun ω' => WholeField.centredField h u₀ ω' φ | germSigma (B t) (WholeField.centredField h u₀) ⊔ ℋ t] ω =
          M t ω φ - (∫ z, u₀ z * φ z)) :
    ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ F → a t ω < ⊤ → tsupport φ ⊆ H \ B t ω →
      P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | ℋ t] ω =
        Complex.exp (Complex.I * (M t ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov (H \ B t ω) φ φ : ℝ) : ℂ)) := by
  intro t φ
  let D := {ω | ω ∈ F ∧ a t ω < ⊤ ∧ Disjoint (tsupport φ) (relClosureH (B t ω))}
  have hD : MeasurableSet[ℋ t] D := (hF t).inter ((measurableSet_lt (haa t) measurable_const).inter
    ((measurableSet_disjoint_relClosureH φ.hasCompactSupport.isCompact φ.tsupport_subset).preimage (hBm t)))
  have he := SB.SewLaw.ae_retained_physical_cexp_of_mean ⟨ℋ t, hℋ t⟩ hu₀ hh0 (hBm t) (hloc t)
    (Eventually.of_forall (hBc t)) φ hD ((LQGMetric.measurable_distOn_apply φ).comp (hM t))
    ((hgm t φ).mono fun ω hω hωD => hω hωD.1 hωD.2.1
      (fun z hz => ⟨φ.tsupport_subset hz, fun hzB =>
        Set.disjoint_left.1 hωD.2.2 hz ((relClosureH_eq (hBc t ω).1 (hBc t ω).2).symm ▸ hzB)⟩))
  filter_upwards [he] with ω heω hω hq hφ
  apply heω
  refine ⟨hω, hq, ?_⟩
  rw [relClosureH_eq (hBc t ω).1 (hBc t ω).2]
  exact Set.disjoint_left.2 fun z hz hzB => (hφ hz).2 hzB

end Lines

end InteractingSLE.Theorem14.BW1Chain
