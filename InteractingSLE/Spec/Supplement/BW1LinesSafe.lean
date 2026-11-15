/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1ChainLines
import InteractingSLE.Spec.Supplement.SB2Remainder

/-!
# BW1's lines, part 1: (S) and (L) through the relative capacity at the contact

Packet PROVE-BW1-LINES. `BW1Chain.hasSafeLaw_top_of_lineKernel` / `hasSafeMembers_top_of_lineLocal` give K2's inputs
(S), (L) with **infinite** relative lifetime, and need the hypothesis `hreach` that the relative clock reaches every
level before the contact. In Proposition BW1 that hypothesis is a *conclusion* ("Its relative capacity lifetime is
infinite", p. 614), proved in the source only after the conditional law of the relative continuation has been
identified on the positive-separation buffers and compared with the canonical counterflow (p. 615: "Let `ζ` be the
limiting relative capacity at `T` […] If `ζ < ∞` […] GB5 excludes it"). It cannot be supplied before the law.

This file removes the hypothesis: the lifetime is an arbitrary random time `V` (in BW1 the relative capacity reached
at the contact, `clockLife a = ⨆ t, a t`), the line data are asked only on `{a t < V}`, and the reach hypothesis is
the one below `V` (automatic for `V = clockLife a`, `exists_le_of_lt_clockLife`):

* `clockLife`, `le_clockLife`, `exists_le_of_lt_clockLife`, `forall_exists_le_of_clockLife_eq_top`;
* `isForceReg_mono`, `coe_capClock_lt_min_iff`, `lineSafe_capClock_life_eq`;
* **`hasSafeLaw_life_of_lineKernel`**: (S) with lifetime `V` from the line kernels and line means on `{a t < V}`;
* **`hasSafeMembers_life_of_lineLocal`**: (L) with lifetime `V` from the history-marked line locality.

With `V = ⊤` these are the `BW1Chain` statements; with a finite `V` they feed the stopped K2
(`Restart.StoppedK2.ae_isStoppedHullCoupling_k`, under `ProbabilityTheory.cond P F` as in `BW1ChainK2`), whose output
is identified with the canonical counterflow by Aux. 54 (R79) and Theorem 1.2's determination
(`Supp8.HullDetGen.ae_isStopDrvMatch_of_isStoppedHullCouplingR`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H fwdHull zeroGFFTestCov)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.BW1Lines

open Restart.DomainMarkov Restart.DomainMarkov.K2 Restart.DomainMarkov.Aux79 BW1Chain

section Life

variable {Ω : Type*} {a : ℝ≥0 → Ω → ℝ≥0∞}

/-- **The relative lifetime of an extended clock**: its supremum over the physical times (in BW1, the relative
capacity reached at the contact). -/
def clockLife (a : ℝ≥0 → Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ := ⨆ t, a t ω

theorem le_clockLife (t : ℝ≥0) (ω : Ω) : a t ω ≤ clockLife a ω :=
  le_iSup (fun t => a t ω) t

/-- Below the relative lifetime every level is reached. -/
theorem exists_le_of_lt_clockLife {q : ℝ≥0∞} {ω : Ω} (h : q < clockLife a ω) : ∃ t, q ≤ a t ω := by
  obtain ⟨t, ht⟩ := lt_iSup_iff.1 h
  exact ⟨t, ht.le⟩

/-- An infinite relative lifetime is the reach of every level (the `hreach` of `BW1Chain`). -/
theorem forall_exists_le_of_clockLife_eq_top {ω : Ω} (h : clockLife a ω = ⊤) (q : ℝ≥0) :
    ∃ t, (q : ℝ≥0∞) ≤ a t ω :=
  exists_le_of_lt_clockLife (by rw [h]; exact ENNReal.coe_lt_top)

end Life

section Lines

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {nL nR : ℕ} {κ : ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {a : ℝ≥0 → Ω → ℝ≥0∞}

omit mΩ in
/-- Regularity with a lifetime gives regularity with every smaller lifetime. -/
theorem isForceReg_mono {ζ ζ' : Ω → ℝ≥0∞} {ω : Ω} (hle : ζ' ω ≤ ζ ω) (h : IsForceReg W VL VR ζ ω) :
    IsForceReg W VL VR ζ' ω :=
  ⟨h.1, h.2.1.mono fun _ ht => lt_of_lt_of_le ht hle,
    fun i => (h.2.2.1 i).mono fun _ ht => lt_of_lt_of_le ht hle,
    fun j => (h.2.2.2.1 j).mono fun _ ht => lt_of_lt_of_le ht hle,
    fun t ht => h.2.2.2.2 t (lt_of_lt_of_le ht hle)⟩

/-- The capped clock is below the capped lifetime exactly when the clock is below the level and the lifetime. -/
theorem coe_capClock_lt_min_iff {V : Ω → ℝ≥0∞} {N t : ℝ≥0} {ω : Ω} :
    (capClock a N t ω : ℝ≥0∞) < min (V ω) N ↔ a t ω < N ∧ a t ω < V ω := by
  rw [coe_capClock]
  constructor
  · intro h
    have hN : a t ω < N := by
      by_contra hn
      rw [min_eq_right (not_lt.1 hn)] at h
      exact absurd (h.trans_le (min_le_right _ _)) (lt_irrefl _)
    rw [min_eq_left hN.le] at h
    exact ⟨hN, h.trans_le (min_le_left _ _)⟩
  · rintro ⟨hN, hV⟩
    rw [min_eq_left hN.le]
    exact lt_min hV hN

/-- The line safe event of the capped clock with the capped lifetime is the line safe event of the clock with the
lifetime, below the level. -/
theorem lineSafe_capClock_life_eq (V : Ω → ℝ≥0∞) (N : ℝ≥0) (C : Set ℂ) (t : ℝ≥0) :
    lineSafe (capClock a N) W (fun ω => min (V ω) N) C t =
      {ω | a t ω < N} ∩
        {ω | a t ω < V ω ∧ Disjoint C (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)} := by
  ext ω
  simp only [lineSafe, mem_ofPred_eq, mem_inter_iff]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨hN, hV⟩ := coe_capClock_lt_min_iff.1 h1
    rw [capClock_eq_of_lt hN] at h2
    exact ⟨hN, hV, h2⟩
  · rintro ⟨hN, hV, h2⟩
    exact ⟨coe_capClock_lt_min_iff.2 ⟨hN, hV⟩, by rw [capClock_eq_of_lt hN]; exact h2⟩

theorem measurableSet_lineSafe_capClock_life {𝓖 : Filtration ℝ≥0 mΩ} (haa : ∀ t, Measurable[𝓖 t] (a t))
    {V : Ω → ℝ≥0∞} {C : Set ℂ} {t : ℝ≥0} (hS : MeasurableSet[𝓖 t]
      {ω | a t ω < V ω ∧ Disjoint C (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)}) (N : ℝ≥0) :
    MeasurableSet[𝓖 t] (lineSafe (capClock a N) W (fun ω => min (V ω) N) C t) := by
  rw [lineSafe_capClock_life_eq]
  exact (measurableSet_lt (haa t) measurable_const).inter hS

omit [IsProbabilityMeasure P] in
/-- The reach hypothesis below a lifetime passes to every capped clock with the capped lifetime. -/
theorem reach_capClock_life {F : Set Ω} {V : Ω → ℝ≥0∞}
    (hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < V ω → ∃ t, (q : ℝ≥0∞) ≤ a t ω) (N q : ℝ≥0) :
    ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < min (V ω) N → ∃ t, q ≤ capClock a N t ω := by
  filter_upwards [hreach q] with ω hω hωF hq
  obtain ⟨t, ht⟩ := hω hωF (hq.trans_le (min_le_left _ _))
  refine ⟨t, ?_⟩
  rw [← ENNReal.coe_le_coe, coe_capClock]
  exact le_min ht (hq.trans_le (min_le_right _ _)).le

/-- **(S) with the lifetime `V` from the line data below `V`** (no a-priori explosion of the clock). Let `a` be a
continuous nondecreasing adapted extended clock from `0`, `𝓗'` a time change of `𝓖` along `a`, and `V` a random time
below which `a` reaches every level. Suppose that at every deterministic physical time `t`, almost surely on `F` and
on `{a t < V}`: the physical field paired with tests supported in `c(ℍ ∖ K̃_{a t})` is, given `𝒢L t ⊇ 𝓖_t`, Gaussian
with mean `M t` and the zero-boundary covariance of that domain (Aux. 77 at the line), and the chart transport of
`M t` is the canonical mean of the continuation at `a t` (Aux. 79 at the line). Then the chart field has K2's (S) with
lifetime `V` for `𝓗'`. With `V = ⊤` this is `BW1Chain.hasSafeLaw_top_of_lineKernel`. -/
theorem hasSafeLaw_life_of_lineKernel {𝓖 𝓗' : Filtration ℝ≥0 mΩ} {F : Set Ω} (hF : MeasurableSet[𝓖 0] F)
    {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (σa k : ℝ) (hac : ∀ ω, Continuous fun t => a t ω) (ham : ∀ ω, Monotone fun t => a t ω)
    (ha0 : ∀ ω, a 0 ω = 0) (haa : ∀ t, Measurable[𝓖 t] (a t))
    (h𝓗' : ∀ q D, MeasurableSet[𝓗' q] D → ∀ t, MeasurableSet[𝓖 t] (D ∩ {ω | (q : ℝ≥0∞) ≤ a t ω}))
    (V : Ω → ℝ≥0∞) (hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < V ω → ∃ t, (q : ℝ≥0∞) ≤ a t ω)
    (hreg : ∀ᵐ ω ∂P, ω ∈ F → IsForceReg W VL VR V ω)
    (hS : ∀ (ψ : TestOn upperHalfPlaneOpens) t, MeasurableSet[𝓖 t]
      {ω | a t ω < V ω ∧ Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)})
    (𝒢L : ℝ≥0 → MeasurableSpace Ω) (h𝒢L : ∀ t, 𝓖 t ≤ 𝒢L t) (h𝒢Lm : ∀ t, 𝒢L t ≤ mΩ)
    (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (hker : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ F → a t ω < V ω →
      tsupport φ ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal) →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢L t] ω =
        Complex.exp (Complex.I * (M t ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω)
            (a t ω).toNNReal)) φ φ : ℝ) : ℂ)))
    (hmean : ∀ (t : ℝ≥0) (ψ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ F → a t ω < V ω →
      Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal) →
      Chart.chartTransport (hc ω) 1 σa k (M t ω) ψ =
        ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal
          (bheProc κ ρL ρR W VL VR ω (a t ω).toNNReal) z * ψ z) :
    HasSafeLaw κ ρL ρR P 𝓗' F V W VL VR fun ω => Chart.chartTransport (hc ω) 1 σa k (h ω) := by
  have hN : ∀ N : ℝ≥0, HasSafeLaw κ ρL ρR P 𝓗' F (fun ω => min (V ω) N) W VL VR
      fun ω => Chart.chartTransport (hc ω) 1 σa k (h ω) := by
    intro N
    refine hasSafeLaw_of_lineKernel (Qc := capClock a N) hF hc hdom hfwd hliftm hliftc hh σa k
      (continuous_capClock hac N) (monotone_capClock ham N) (capClock_zero ha0 N) (measurable_capClock haa N)
      (measurableSet_inter_capClock h𝓗' N) (reach_capClock_life hreach N) ?_
      (fun ψ t => measurableSet_lineSafe_capClock_life haa (hS ψ t) N) 𝒢L h𝒢L h𝒢Lm M ?_ ?_
    · filter_upwards [hreg] with ω hω hωF using isForceReg_mono (min_le_left _ _) (hω hωF)
    · intro t φ
      filter_upwards [hker t φ] with ω hω hωF hlt hsupp
      obtain ⟨haN, haV⟩ := coe_capClock_lt_min_iff.1 hlt
      rw [capClock_eq_of_lt haN] at hsupp ⊢
      exact hω hωF haV hsupp
    · intro t ψ
      filter_upwards [hmean t ψ] with ω hω hωF hS'
      rw [lineSafe_capClock_life_eq] at hS'
      rw [capClock_eq_of_lt hS'.1]
      exact hω hωF hS'.2.1 hS'.2.2
  intro ψ q D hD hDs
  refine hN (q + 1) ψ q D hD ?_
  filter_upwards [hDs] with ω h1 hωD
  obtain ⟨hF', hqV, hdis⟩ := h1 hωD
  exact ⟨hF', lt_min hqV (ENNReal.coe_lt_coe.2 (lt_add_one q)), hdis⟩

open LocalSets WholeField in
/-- **(L) with the lifetime `V` from the history-marked line locality below `V`** (`Aux79.hasSafeMembers_of_lineLocal`
for every capped clock with the capped lifetime). With `V = ⊤` this is `BW1Chain.hasSafeMembers_top_of_lineLocal`. -/
theorem hasSafeMembers_life_of_lineLocal {𝓖 𝓗' : Filtration ℝ≥0 mΩ} {F : Set Ω}
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
    (V : Ω → ℝ≥0∞) (hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < V ω → ∃ t, (q : ℝ≥0∞) ≤ a t ω)
    (hreg : ∀ᵐ ω ∂P, ω ∈ F → IsForceReg W VL VR V ω)
    (hS : ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t, MeasurableSet[𝓖 t]
      {ω | a t ω < V ω ∧ Disjoint (Coupling.ballsK Fb) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)})
    (ℋ : ℝ≥0 → MeasurableSpace Ω) (h𝓖ℋ : ∀ t, 𝓖 t ≤ ℋ t) (hℋ : ∀ t, ℋ t ≤ mΩ)
    (B : ℝ≥0 → Ω → Set ℂ) (hBm : ∀ t, Measurable[mΩ, hittingSigma] (B t))
    (hBc : ∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω))
    (hloc : ∀ t, IsHistoryAvoidanceLocal (ℋ t) (B t) (centredField h u₀) P)
    (hBK : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → a t ω < V ω →
      H \ B t ω = (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)) :
    HasSafeMembers P 𝓗' F V W fun ω => Chart.chartTransport (hc ω) 1 σa k (h ω) := by
  have hN : ∀ N : ℝ≥0, HasSafeMembers P 𝓗' F (fun ω => min (V ω) N) W
      fun ω => Chart.chartTransport (hc ω) 1 σa k (h ω) := by
    intro N
    refine hasSafeMembers_of_lineLocal (Qc := capClock a N) (VL := VL) (VR := VR) hhm hu₀ hh0 hc hdom hfwd
      hliftm hliftc hlift σa k (continuous_capClock hac N) (monotone_capClock ham N) (capClock_zero ha0 N)
      (measurable_capClock haa N) (measurableSet_inter_capClock h𝓗' N) (reach_capClock_life hreach N) ?_
      (fun Fb t => measurableSet_lineSafe_capClock_life haa (hS Fb t) N) ℋ h𝓖ℋ hℋ B hBm hBc hloc ?_
    · filter_upwards [hreg] with ω hω hωF using isForceReg_mono (min_le_left _ _) (hω hωF)
    · intro t
      filter_upwards [hBK t] with ω hω hωF hlt
      obtain ⟨haN, haV⟩ := coe_capClock_lt_min_iff.1 hlt
      rw [capClock_eq_of_lt haN]
      exact hω hωF haV
  intro s Fb hFb D hD hDs
  refine hN (s + 1) s Fb hFb D hD ?_
  filter_upwards [hDs] with ω h1 hωD
  obtain ⟨hF', hsV, hdis⟩ := h1 hωD
  exact ⟨hF', lt_min hsV (ENNReal.coe_lt_coe.2 (lt_add_one s)), hdis⟩

end Lines

/-! ### The conditional counterflow sees the chart only at the conditioning sample -/

section Chart

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsFiniteMeasure P]

/-- **Chart congruence**: a conditional centred counterflow in a random chart is one in every chart that agrees with
it almost surely on the live event (so the state chart may be replaced by a version that is conformal at every
sample). -/
theorem isCondCounterflowDriverOn_congr_chart {κ : ℝ} {F : Set Ω} {h : Ω → DistOn upperHalfPlaneOpens}
    {c c' : Ω → Chart} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (he : ∀ᵐ ω ∂P, ω ∈ F → c' ω = c ω)
    (hC : SB.IsCondCounterflowDriverOn κ 𝒢 P F h c W ζ) : SB.IsCondCounterflowDriverOn κ 𝒢 P F h c' W ζ := by
  filter_upwards [hC, he] with ω₀ h1 h2 hF
  rw [h2 hF]
  exact h1 hF

end Chart

end InteractingSLE.Theorem14.BW1Lines
