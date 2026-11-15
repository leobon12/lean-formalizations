/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.DomainMarkovK2Loc

/-!
# Aux. lemmas 77 and 79 at later lines: K2's (S) and (L) from deterministic physical later lines

Packet PROVE-DOMAINMARKOV8 (specification Aux. lemmas 77 and 79, pp. 287–290). The kernel assembly K2
(`DomainMarkov.K2.ae_isOptionalHullCoupling_k`) needs, at every **deterministic capacity time** `q` of the continuation,
the protected-kernel law (S) (`K2.HasSafeLaw`) and the member identities (L) (`K2.HasSafeMembers`), on the events of a
capacity-time filtration `𝓗'`. In the retained settings (Lemma G7, Lemma 7.6) the continuation is a curve read in a
chart fixed at time `0`, and its capacity time `q` corresponds to the **random** physical later line at which the
chart capacity reaches `q`. The stop-line identifications of the specification are available at **deterministic**
physical lines (Lemma 7.6's `Lemma76MeanIdentStatement` at every pair of deterministic stops). This file transfers
them: if at every deterministic physical time `t` (with the physical filtration `𝓖`) the identities hold at the
random capacity time `Qc t` (the chart capacity reached at physical time `t`), then (S) and (L) hold at every
deterministic capacity time for the **time-changed filtration** `𝓗'_q = {D | ∀ t, D ∩ {q ≤ Qc t} ∈ 𝓖_t}`.

Proof (as `DomainMarkov.setIntegral_cexp_eq_cfAt_of_dyadic`, with the discretization in physical time): let
`σ = inf {t | q ≤ Qc t}`; cut `D ∈ 𝓗'_q` into the pieces `{⌈2ⁿ σ⌉ = k}`, which are `𝓖_{k/2ⁿ}`-events
(`linePiece`); on a piece the line identity at `t = k/2ⁿ` applies (intersected with the line's safe event); the
capacity times `Qc(⌈2ⁿσ⌉/2ⁿ)` decrease to `q` (continuity of the clock), so the pieces' safe events eventually contain
`D` (right-continuity of the hulls, `exists_pos_disjoint_fwdHull_rpath'`) and `cfAt` converges
(`tendsto_cfAt_of_isForceReg`, the deterministic part of `DomainMarkov.exists_eventually_isSafeAt_tendsto_cfAt`);
dominated convergence finishes. Only deterministic path regularity of the continuation is used (`IsForceReg`), not
its driving equations, so the result can feed (E) (whose martingale input comes from (S)) without circularity.

## Main results

* `timeChange`: the time-changed filtration `𝓗'` of a continuous nondecreasing adapted clock;
* `tendsto_cfAt_of_isForceReg`: deterministic time limits of `cfAt`;
* **`hasSafeLaw_of_lineLaw`**: (S) from the conditional laws on deterministic physical lines;
* **`hasSafeMembers_of_lineMembers`**: (L) from the member identities on deterministic physical lines.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.DomainMarkov.Aux79

open Coupling Ito K2

/-! ### The physical clock and its first passage times -/

section Clock

variable {Ω : Type*} (Qc : ℝ≥0 → Ω → ℝ≥0) (q : ℝ≥0)

/-- The first physical time at which the capacity clock `Qc` reaches `q`. -/
def hitT (ω : Ω) : ℝ≥0 := sInf {t | q ≤ Qc t ω}

variable {Qc q}

/-- For a continuous nondecreasing clock that reaches `q`, the clock is at least `q` exactly after `hitT`. -/
theorem le_Qc_iff {ω : Ω} (hc : Continuous fun t => Qc t ω) (hm : Monotone fun t => Qc t ω)
    (hr : ∃ t, q ≤ Qc t ω) {t : ℝ≥0} : q ≤ Qc t ω ↔ hitT Qc q ω ≤ t := by
  have hcl : IsClosed {t | q ≤ Qc t ω} := isClosed_le continuous_const hc
  constructor
  · intro h
    exact csInf_le (OrderBot.bddBelow _) h
  · intro h
    have hmem : hitT Qc q ω ∈ {t | q ≤ Qc t ω} := hcl.csInf_mem hr (OrderBot.bddBelow _)
    exact le_trans hmem (hm h)

/-- At the first passage time the clock equals `q`. -/
theorem Qc_hitT {ω : Ω} (hc : Continuous fun t => Qc t ω) (hm : Monotone fun t => Qc t ω) (h0 : Qc 0 ω = 0)
    (hr : ∃ t, q ≤ Qc t ω) : Qc (hitT Qc q ω) ω = q := by
  refine le_antisymm ?_ ((le_Qc_iff hc hm hr).2 le_rfl)
  rcases eq_or_ne (hitT Qc q ω) 0 with h | h
  · rw [h, h0]
    exact zero_le (a := q)
  · have hσ : 0 < hitT Qc q ω := pos_iff_ne_zero.2 h
    have : (𝓝[<] (hitT Qc q ω)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hσ⟩
    have hev : ∀ᶠ t in 𝓝[<] (hitT Qc q ω), Qc t ω ≤ q := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have hn : ¬ hitT Qc q ω ≤ t := not_le.2 ht
      rw [← le_Qc_iff hc hm hr] at hn
      exact (not_le.1 hn).le
    exact le_of_tendsto ((hc.tendsto _).mono_left nhdsWithin_le_nhds) hev

/-- The first dyadic level-`n` time after `hitT` is `⌈2ⁿ σ⌉/2ⁿ`, which tends to `σ`. -/
theorem tendsto_dyT_ceil_self (a : ℝ≥0) : Tendsto (fun n => dyT n ⌈2 ^ n * a⌉₊) atTop (𝓝 a) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (tendsto_dyT_ceil a) (fun n => le_dyT_ceil a n)
    (fun n => dyT_mono n (Nat.le_succ _))

/-- The clock at the first dyadic times after `hitT` tends to `q`. -/
theorem tendsto_Qc_dyT_hitT {ω : Ω} (hc : Continuous fun t => Qc t ω) (hm : Monotone fun t => Qc t ω)
    (h0 : Qc 0 ω = 0) (hr : ∃ t, q ≤ Qc t ω) :
    Tendsto (fun n => Qc (dyT n ⌈2 ^ n * hitT Qc q ω⌉₊) ω) atTop (𝓝 q) := by
  have h := (hc.tendsto (hitT Qc q ω)).comp (tendsto_dyT_ceil_self (hitT Qc q ω))
  rwa [Qc_hitT hc hm h0 hr] at h

/-- The `k`-th level-`n` piece of an event `D` along the first passage of the clock at `q`: the clock reaches `q`
at the dyadic time `k/2ⁿ` and not at the earlier dyadic times, and the safe event `S` of the line `k/2ⁿ` holds. -/
def linePiece (Qc : ℝ≥0 → Ω → ℝ≥0) (q : ℝ≥0) (D : Set Ω) (S : ℝ≥0 → Set Ω) (n k : ℕ) : Set Ω :=
  D ∩ {ω | q ≤ Qc (dyT n k) ω ∧ ∀ j < k, Qc (dyT n j) ω < q} ∩ S (dyT n k)

/-- On a piece, the level-`n` label `⌈2ⁿ σ⌉` is the piece index. -/
theorem lab_eq_of_mem_linePiece {D : Set Ω} {S : ℝ≥0 → Set Ω} {n k : ℕ} {ω : Ω}
    (hc : Continuous fun t => Qc t ω) (hm : Monotone fun t => Qc t ω) (hω : ω ∈ linePiece Qc q D S n k) :
    ⌈2 ^ n * hitT Qc q ω⌉₊ = k := by
  obtain ⟨⟨-, hle, hlt⟩, -⟩ := hω
  have hr : ∃ t, q ≤ Qc t ω := ⟨_, hle⟩
  have h1 : ⌈2 ^ n * hitT Qc q ω⌉₊ ≤ k := le_dyT_iff.1 ((le_Qc_iff hc hm hr).1 hle)
  refine le_antisymm h1 (not_lt.1 fun hk => ?_)
  have h2 : q ≤ Qc (dyT n ⌈2 ^ n * hitT Qc q ω⌉₊) ω := (le_Qc_iff hc hm hr).2 (le_dyT_ceil _ n)
  exact absurd (hlt _ hk) (not_lt.2 h2)

/-- A point of `D` reaching `q`, in the safe event of its level-`n` line, lies in its level-`n` piece. -/
theorem mem_linePiece_lab {D : Set Ω} {S : ℝ≥0 → Set Ω} {n : ℕ} {ω : Ω}
    (hc : Continuous fun t => Qc t ω) (hm : Monotone fun t => Qc t ω) (hr : ∃ t, q ≤ Qc t ω) (hD : ω ∈ D)
    (hS : ω ∈ S (dyT n ⌈2 ^ n * hitT Qc q ω⌉₊)) : ω ∈ linePiece Qc q D S n ⌈2 ^ n * hitT Qc q ω⌉₊ := by
  refine ⟨⟨hD, (le_Qc_iff hc hm hr).2 (le_dyT_ceil _ n), fun j hj => ?_⟩, hS⟩
  refine not_le.1 fun hle => ?_
  have h1 := le_dyT_iff.1 ((le_Qc_iff hc hm hr).1 hle)
  omega

/-- **The pieces are events of the physical filtration at their line.** -/
theorem measurableSet_linePiece {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ}
    (hQa : ∀ t, Measurable[𝓖 t] (Qc t)) {D : Set Ω} (hD : ∀ t, MeasurableSet[𝓖 t] (D ∩ {ω | q ≤ Qc t ω}))
    {S : ℝ≥0 → Set Ω} (hS : ∀ t, MeasurableSet[𝓖 t] (S t)) (n k : ℕ) :
    MeasurableSet[𝓖 (dyT n k)] (linePiece Qc q D S n k) := by
  have hj : MeasurableSet[𝓖 (dyT n k)] {ω | ∀ j < k, Qc (dyT n j) ω < q} := by
    have e : {ω | ∀ j < k, Qc (dyT n j) ω < q} = ⋂ j : Fin k, {ω | Qc (dyT n j) ω < q} := by
      ext ω
      simp only [mem_ofPred_eq, mem_iInter]
      exact ⟨fun h j => h j j.2, fun h j hj => h ⟨j, hj⟩⟩
    rw [e]
    refine MeasurableSet.iInter fun j => ?_
    exact 𝓖.mono (dyT_mono n j.2.le) _ (measurableSet_lt (hQa _) measurable_const)
  have e : linePiece Qc q D S n k = (D ∩ {ω | q ≤ Qc (dyT n k) ω}) ∩ {ω | ∀ j < k, Qc (dyT n j) ω < q} ∩
      S (dyT n k) := by
    ext ω
    simp only [linePiece, mem_inter_iff, mem_ofPred_eq]
    tauto
  rw [e]
  exact ((hD _).inter hj).inter (hS _)

theorem linePiece_subset (D : Set Ω) (S : ℝ≥0 → Set Ω) (n k : ℕ) : linePiece Qc q D S n k ⊆ D :=
  fun _ hω => hω.1.1

/-- **Pointwise convergence of the discretized integrands.** Almost surely on `D` (where the clock reaches `q`, the
lines' safe events eventually hold along clock values tending to `q`, and the integrands converge along the first
dyadic times after `hitT`), the sums over the level-`n` pieces converge to the integrand on `D`. -/
theorem ae_tendsto_sum_linePiece [MeasurableSpace Ω] {P : Measure Ω} {D : Set Ω} {S : ℝ≥0 → Set Ω}
    (hc : ∀ ω, Continuous fun t => Qc t ω) (hm : ∀ ω, Monotone fun t => Qc t ω) (h0 : ∀ ω, Qc 0 ω = 0)
    (g : ℕ → ℕ → Ω → ℂ) (g' : Ω → ℂ)
    (hgood : ∀ᵐ ω ∂P, ω ∈ D → (∃ t, q ≤ Qc t ω) ∧
      (∀ t : ℕ → ℝ≥0, Tendsto (fun n => Qc (t n) ω) atTop (𝓝 q) → ∀ᶠ n in atTop, ω ∈ S (t n)) ∧
      Tendsto (fun n => g n ⌈2 ^ n * hitT Qc q ω⌉₊ ω) atTop (𝓝 (g' ω))) :
    ∀ᵐ ω ∂P, Tendsto (fun n => ∑ k ∈ Finset.range (4 ^ n), (linePiece Qc q D S n k).indicator (g n k) ω) atTop
      (𝓝 (D.indicator g' ω)) := by
  filter_upwards [hgood] with ω hω
  have hlab : ∀ n k ω', ω' ∈ linePiece Qc q D S n k → ⌈2 ^ n * hitT Qc q ω'⌉₊ = k := fun n k ω' h =>
    lab_eq_of_mem_linePiece (hc ω') (hm ω') h
  by_cases hD : ω ∈ D
  · obtain ⟨hr, hS, hg⟩ := hω hD
    have hev : ∀ᶠ n in atTop, ⌈2 ^ n * hitT Qc q ω⌉₊ ∈ Finset.range (4 ^ n) ∧
        ω ∈ linePiece Qc q D S n ⌈2 ^ n * hitT Qc q ω⌉₊ := by
      filter_upwards [eventually_ceil_lt_four_pow (hitT Qc q ω),
        hS _ (tendsto_Qc_dyT_hitT (hc ω) (hm ω) (h0 ω) hr)] with n hn hSn
      exact ⟨Finset.mem_range.2 hn, mem_linePiece_lab (hc ω) (hm ω) hr hD hSn⟩
    rw [indicator_of_mem hD]
    refine hg.congr' (hev.mono fun n hn => ?_)
    beta_reduce
    rw [sum_indicator_eq_of_label (fun k ω' h => hlab n k ω' h) ω]
    split_ifs with hk
    · exact (indicator_of_mem hn.2 _).symm
    · exact absurd hn.1 hk
  · rw [indicator_of_notMem hD]
    refine tendsto_const_nhds.congr fun n => (Finset.sum_eq_zero fun k _ => ?_).symm
    exact indicator_of_notMem (fun h => hD (linePiece_subset D S n k h)) _

/-- The sums over the pieces have modulus at most the bound of the summands on their pieces. -/
theorem norm_sum_linePiece_le {D : Set Ω} {S : ℝ≥0 → Set Ω} (hc : ∀ ω, Continuous fun t => Qc t ω)
    (hm : ∀ ω, Monotone fun t => Qc t ω) (g : ℕ → ℕ → Ω → ℂ) (n : ℕ) (s : Finset ℕ) {ω : Ω}
    (hb : ∀ k, ω ∈ linePiece Qc q D S n k → ‖g n k ω‖ ≤ 1) :
    ‖∑ k ∈ s, (linePiece Qc q D S n k).indicator (g n k) ω‖ ≤ 1 := by
  rw [sum_indicator_eq_of_label (fun k ω' h => lab_eq_of_mem_linePiece (hc ω') (hm ω') h) ω]
  split_ifs with hk
  · by_cases hω : ω ∈ linePiece Qc q D S n ⌈2 ^ n * hitT Qc q ω⌉₊
    · rw [indicator_of_mem hω]
      exact hb _ hω
    · rw [indicator_of_notMem hω, norm_zero]
      exact zero_le_one
  · rw [norm_zero]
    exact zero_le_one

/-! ### The time-changed filtration -/

section TimeChange

variable [mΩ : MeasurableSpace Ω]

/-- The σ-algebra of the time change at capacity `q`: the events `D` cut into `𝓖_t`-events by `{q ≤ Qc t}` for every
physical time `t` (the stopping-time σ-algebra at the first passage of `Qc` at `q`). -/
@[instance_reducible]
def timeChangeSigma (𝓖 : Filtration ℝ≥0 mΩ) (Qc : ℝ≥0 → Ω → ℝ≥0) (hQa : ∀ t, Measurable[𝓖 t] (Qc t))
    (q : ℝ≥0) : MeasurableSpace Ω where
  MeasurableSet' D := MeasurableSet D ∧ ∀ t, MeasurableSet[𝓖 t] (D ∩ {ω | q ≤ Qc t ω})
  measurableSet_empty := ⟨MeasurableSet.empty, fun t => by
    rw [empty_inter]; exact @MeasurableSet.empty Ω (𝓖 t)⟩
  measurableSet_compl D hD := ⟨hD.1.compl, fun t => by
    have hA : MeasurableSet[𝓖 t] {ω | q ≤ Qc t ω} := measurableSet_le measurable_const (hQa t)
    have e : Dᶜ ∩ {ω | q ≤ Qc t ω} = {ω | q ≤ Qc t ω} \ (D ∩ {ω | q ≤ Qc t ω}) := by
      ext ω; simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff]; tauto
    rw [e]
    exact hA.diff (hD.2 t)⟩
  measurableSet_iUnion f hf := ⟨MeasurableSet.iUnion fun i => (hf i).1, fun t => by
    rw [iUnion_inter]
    exact MeasurableSet.iUnion fun i => (hf i).2 t⟩

/-- **The time-changed filtration** of a physical filtration `𝓖` along an adapted clock `Qc`. -/
def timeChange (𝓖 : Filtration ℝ≥0 mΩ) (Qc : ℝ≥0 → Ω → ℝ≥0) (hQa : ∀ t, Measurable[𝓖 t] (Qc t)) :
    Filtration ℝ≥0 mΩ where
  seq := timeChangeSigma 𝓖 Qc hQa
  mono' q q' hqq' D hD := ⟨hD.1, fun t => by
    have hA : MeasurableSet[𝓖 t] {ω | q' ≤ Qc t ω} := measurableSet_le measurable_const (hQa t)
    have e : D ∩ {ω | q' ≤ Qc t ω} = (D ∩ {ω | q ≤ Qc t ω}) ∩ {ω | q' ≤ Qc t ω} := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq]
      exact ⟨fun h => ⟨⟨h.1, hqq'.trans h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
    rw [e]
    exact (hD.2 t).inter hA⟩
  le' _ _ hD := hD.1

variable {𝓖 : Filtration ℝ≥0 mΩ} {hQa : ∀ t, Measurable[𝓖 t] (Qc t)}

theorem measurableSet_timeChange_iff {q : ℝ≥0} {D : Set Ω} :
    MeasurableSet[timeChange 𝓖 Qc hQa q] D ↔
      MeasurableSet D ∧ ∀ t, MeasurableSet[𝓖 t] (D ∩ {ω | q ≤ Qc t ω}) := Iff.rfl

/-- The cut of a time-changed event at a physical time is an event of the physical filtration. -/
theorem measurableSet_inter_of_timeChange {q : ℝ≥0} {D : Set Ω} (hD : MeasurableSet[timeChange 𝓖 Qc hQa q] D)
    (t : ℝ≥0) : MeasurableSet[𝓖 t] (D ∩ {ω | q ≤ Qc t ω}) := hD.2 t

/-- Events of the physical filtration at time `0` are events of the time change at capacity `0`. -/
theorem le_timeChange_zero : 𝓖 0 ≤ timeChange 𝓖 Qc hQa 0 := fun D hD => ⟨𝓖.le 0 _ hD, fun t => by
  have e : D ∩ {ω | (0 : ℝ≥0) ≤ Qc t ω} = D := inter_eq_left.2 fun ω _ => zero_le (a := Qc t ω)
  rw [e]
  exact 𝓖.mono (zero_le (a := t)) _ hD⟩

/-- **Adaptedness to the time change**: a process whose value at capacity `q` (before the lifetime) is read, on
`{q ≤ Qc t}`, from the physical information at time `t`, is adapted before the lifetime to the time change. -/
theorem adaptedBefore_timeChange {ζ : Ω → ℝ≥0∞} {Y : ℝ≥0 → Ω → ℝ}
    (hY : ∀ (q : ℝ≥0) (A : Set ℝ), MeasurableSet A → MeasurableSet {ω | (q : ℝ≥0∞) < ζ ω ∧ Y q ω ∈ A} ∧
      ∀ t, MeasurableSet[𝓖 t] ({ω | (q : ℝ≥0∞) < ζ ω ∧ Y q ω ∈ A} ∩ {ω | q ≤ Qc t ω})) :
    AdaptedBefore (timeChange 𝓖 Qc hQa) ζ Y := fun q A hA => hY q A hA

end TimeChange

end Clock

/-! ### Deterministic time limits of `cfAt` -/

section Reg

variable {Ω : Type*} {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The deterministic regularity of a continuation** used by the time limits: the driver starts at `0` and the
driver and force points are continuous before the lifetime, with the force points on their sides of the driver. -/
def IsForceReg (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (ω : Ω) : Prop :=
  W 0 ω = 0 ∧ ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
    (∀ i, ContinuousOn (VL i · ω) {t | (t : ℝ≥0∞) < ζ ω}) ∧ (∀ j, ContinuousOn (VR j · ω) {t | (t : ℝ≥0∞) < ζ ω}) ∧
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → (∀ i, VL i t ω ≤ W t ω) ∧ ∀ j, W t ω ≤ VR j t ω

/-- An integrated `SLE_κ(ρ)` path is regular in the sense of `IsForceReg`. -/
theorem isForceReg_of_isIntegratedSLEPath {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hp : IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun i t => VR i t ω)
      (fun t => B t ω) (ζ ω)) : IsForceReg W VL VR ζ ω :=
  ⟨hp.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, fun t ht =>
    ⟨hp.2.2.2.2.2.2.2.1 t ht, hp.2.2.2.2.2.2.2.2.1 t ht⟩⟩

/-- **Times converging to an avoidance time are eventually safe, and `cfAt` converges** (the deterministic part of
`DomainMarkov.exists_eventually_isSafeAt_tendsto_cfAt`, with the integrated path replaced by `IsForceReg`). -/
theorem tendsto_cfAt_of_isForceReg {u : Ω → ℝ≥0 → ℂ → ℝ}
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s))
    (ψ : TestOn upperHalfPlaneOpens) {ω : Ω} (hp : IsForceReg W VL VR ζ ω) {a : ℝ≥0}
    (haζ : (a : ℝ≥0∞) < ζ ω) (hdis : Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) a))
    {t : ℕ → ℝ≥0} (ht : Tendsto t atTop (𝓝 a)) :
    (∀ᶠ n in atTop, ((t n : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
      Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (t n))) ∧
      Tendsto (fun n => cfAt κ W u ψ 1 (fun _ => t n) ω) atTop (𝓝 (cfAt κ W u ψ 1 (fun _ => a) ω)) := by
  set K : Set ℂ := tsupport (ψ : ℂ → ℝ) with hKdef
  have hKH : K ⊆ H := tsupport_subset_H ψ
  have hK : IsCompact K := ψ.hasCompactSupport.isCompact
  have hw : ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω} := hp.2.1
  obtain ⟨δ', hδ', hrζ, hdisj⟩ := exists_pos_disjoint_fwdHull_rpath' hw haζ hK hKH hdis
  set r : ℝ≥0 := a + δ' with hr
  have halive : ∀ z ∈ K, ∃ v, QuantumZipper.IsForwardSol (rpath (W · ω)) z r v := fun z hz =>
    exists_isForwardSol_of_mem r.coe_nonneg ⟨hKH hz, fun hzK => Set.disjoint_left.1 (hdisj r le_rfl) hz hzK⟩
  obtain ⟨δ₀, hδ₀, hsafe⟩ := exists_isSafeAt_self hw hp.1 hK hKH hrζ halive
  have har : a < r := lt_add_of_pos_right a hδ'
  have hev_le : ∀ᶠ n in atTop, t n ≤ r := ((tendsto_order.1 ht).2 r har).mono fun n h => h.le
  refine ⟨hev_le.mono fun n hn => ⟨lt_of_le_of_lt (by exact_mod_cast hn) hrζ, hdisj _ hn⟩, ?_⟩
  set g : ℝ≥0 → ℂ := fun s => Complex.exp (Complex.I * 1 *
      ((∫ z, meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s z * ψ z : ℝ) : ℂ) -
      1 ^ 2 * ((loewnerGreenEnergy (rpath (W · ω)) s ψ : ℝ) : ℂ) / 2) with hg
  have hgc : ContinuousOn g (Iic r) := by
    have h1 := hsafe.continuousOn_meanInt (κ := κ) (ρL := ρL) (ρR := ρR) ψ.continuous ψ.hasCompactSupport hw
      hp.2.2.1 hp.2.2.2.1 hKH hδ₀
    have h2 := hsafe.continuousOn_loewnerGreenEnergy ψ.continuous ψ.hasCompactSupport hw hKH hδ₀
    exact ((continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn h1)).sub
      ((continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn h2)).div_const 2)).cexp
  have hcf : ∀ s ≤ r, cfAt κ W u ψ 1 (fun _ => s) ω = g s := fun s hs => by
    have hsζ : (s : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hs) hrζ
    have hmean : (∫ z, couplingMean κ (fun x : ℝ => W x.toNNReal ω) s (u ω s) z * ψ z) =
        ∫ z, meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s z * ψ z := by
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      by_cases hz : z ∈ K
      · have e := couplingMean_eq_meanCan (κ := κ) (ρL := ρL) (ρR := ρR) (w := (W · ω))
          (vL := fun i t => VL i t ω) (vR := fun i t => VR i t ω) hw hKH hsafe hδ₀ hs hz (hp.2.2.2.2 s hsζ).1
          (hp.2.2.2.2 s hsζ).2 (hu ω s)
        exact congrArg (· * ψ z) e
      · simp [image_eq_zero_of_notMem_tsupport hz]
    simp only [cfAt, hg, hmean]
    rfl
  have hlim : Tendsto (fun n => g (t n)) atTop (𝓝 (g a)) :=
    (hgc a (mem_Iic.2 har.le)).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨ht, hev_le⟩)
  rw [hcf a har.le]
  exact hlim.congr' (hev_le.mono fun n hn => (hcf (t n) hn).symm)

/-- `cfAt` at a safe time has modulus at most one. -/
theorem norm_cfAt_le_one_of_isForceReg (u : Ω → ℝ≥0 → ℂ → ℝ) (ψ : TestOn upperHalfPlaneOpens) {ω : Ω}
    (hp : IsForceReg W VL VR ζ ω) {r : Ω → ℝ≥0} (hrζ : (r ω : ℝ≥0∞) < ζ ω)
    (hdis : Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (r ω))) :
    ‖cfAt κ W u ψ 1 r ω‖ ≤ 1 :=
  norm_cfAt_le_one u 1 ψ (continuousOn_rpath hp.2.1 hrζ) hp.1 fun _ hz =>
    exists_isForwardSol_of_mem (r ω).coe_nonneg ⟨tsupport_subset_H ψ hz, Set.disjoint_left.1 hdis hz⟩

end Reg

/-! ### (S) from the conditional laws on deterministic physical lines -/

section Law

open LocalSets LQGMetric.MarkovZB

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL nR : ℕ} {κ : ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {F : Set Ω} {Qc : ℝ≥0 → Ω → ℝ≥0}

/-- The safe event of the physical line `t` for a compact set `C`: the continuation is alive at the capacity time
`Qc t` reached at physical time `t`, and its hull then avoids `C`. -/
def lineSafe (Qc : ℝ≥0 → Ω → ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (C : Set ℂ) (t : ℝ≥0) : Set Ω :=
  {ω | (Qc t ω : ℝ≥0∞) < ζ ω ∧ Disjoint C (fwdHull (fun s : ℝ => W s.toNNReal ω) (Qc t ω))}

omit mΩ in
/-- **Right-continuity of the safe events**: along physical times whose clock values tend to an avoidance time `q`,
the line safe events eventually hold. -/
theorem eventually_mem_lineSafe {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ H) {ω : Ω}
    (hp : IsForceReg W VL VR ζ ω) {q : ℝ≥0} (hqζ : (q : ℝ≥0∞) < ζ ω)
    (hdis : Disjoint C (fwdHull (fun s : ℝ => W s.toNNReal ω) q)) (t : ℕ → ℝ≥0)
    (ht : Tendsto (fun n => Qc (t n) ω) atTop (𝓝 q)) : ∀ᶠ n in atTop, ω ∈ lineSafe Qc W ζ C (t n) := by
  obtain ⟨δ, hδ, hqδ, hd⟩ := exists_pos_disjoint_fwdHull_rpath' hp.2.1 hqζ hC hCH hdis
  have hev : ∀ᶠ n in atTop, Qc (t n) ω ≤ q + δ :=
    ((tendsto_order.1 ht).2 _ (lt_add_of_pos_right q hδ)).mono fun n h => h.le
  filter_upwards [hev] with n hn
  exact ⟨lt_of_le_of_lt (by exact_mod_cast hn) hqδ, hd _ hn⟩

/-- **(S) from the conditional laws on deterministic physical lines** (Aux. lemmas 77 and 79 at later lines, from
their deterministic-line forms). Let `Qc` be a continuous nondecreasing clock from `0`, adapted to a physical
filtration `𝓖`, and `𝓗'` a capacity-time filtration whose `q`-events are cut into `𝓖_t`-events by
`{q ≤ Qc t}` (the time change, `timeChange`). Suppose that on the live event `F` the clock reaches every capacity time
before the lifetime, the continuation is regular (`IsForceReg`), the line safe events are `𝓖_t`-events, and at every
deterministic physical time `t` the field has, conditionally on a σ-algebra `𝒢L t ⊇ 𝓖_t`, the protected-kernel law
at the random capacity time `Qc t` on the line safe event. Then the continuation has K2's input (S) for `𝓗'`. -/
theorem hasSafeLaw_of_lineLaw [IsProbabilityMeasure P] {𝓖 𝓗' : Filtration ℝ≥0 mΩ}
    {X : Ω → DistOn upperHalfPlaneOpens} (hX : ∀ ψ : TestOn upperHalfPlaneOpens, Measurable fun ω => X ω ψ)
    (hc : ∀ ω, Continuous fun t => Qc t ω) (hm : ∀ ω, Monotone fun t => Qc t ω) (h0 : ∀ ω, Qc 0 ω = 0)
    (hQa : ∀ t, Measurable[𝓖 t] (Qc t))
    (h𝓗' : ∀ q D, MeasurableSet[𝓗' q] D → ∀ t, MeasurableSet[𝓖 t] (D ∩ {ω | q ≤ Qc t ω}))
    (hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < ζ ω → ∃ t, q ≤ Qc t ω)
    (hreg : ∀ᵐ ω ∂P, ω ∈ F → IsForceReg W VL VR ζ ω)
    (hS : ∀ (ψ : TestOn upperHalfPlaneOpens) t, MeasurableSet[𝓖 t] (lineSafe Qc W ζ (tsupport ψ) t))
    (𝒢L : ℝ≥0 → MeasurableSpace Ω) (h𝒢L : ∀ t, 𝓖 t ≤ 𝒢L t) (h𝒢Lm : ∀ t, 𝒢L t ≤ mΩ)
    (hline : ∀ (ψ : TestOn upperHalfPlaneOpens) (t : ℝ≥0), ∀ᵐ ω ∂P, ω ∈ F →
      ω ∈ lineSafe Qc W ζ (tsupport ψ) t → P[fun ω => Complex.exp (Complex.I * (X ω ψ : ℂ)) | 𝒢L t] ω =
        cfAt κ W (bheProc κ ρL ρR W VL VR) ψ 1 (Qc t) ω) :
    HasSafeLaw κ ρL ρR P 𝓗' F ζ W VL VR X := by
  intro ψ q D hD hDs
  set f : Ω → ℂ := fun ω => Complex.exp (Complex.I * (X ω ψ : ℂ)) with hf
  have hfm : Measurable f :=
    (by fun_prop : Measurable fun x : ℝ => Complex.exp (Complex.I * x)).comp (hX ψ)
  have hfn : ∀ ω, ‖f ω‖ ≤ 1 := fun ω => by
    simp only [hf, Complex.norm_exp, Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul, Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_zero, Real.exp_zero, le_refl]
  have hfi : Integrable f P := Integrable.of_bound hfm.aestronglyMeasurable 1 (Eventually.of_forall hfn)
  set u := bheProc κ ρL ρR W VL VR with hu
  set S : ℝ≥0 → Set Ω := lineSafe Qc W ζ (tsupport ψ) with hSdef
  set E : ℕ → ℕ → Set Ω := linePiece Qc q D S with hEdef
  set g : ℕ → ℕ → Ω → ℂ := fun n k => cfAt κ W u ψ 1 (Qc (dyT n k)) with hgdef
  have hDm : MeasurableSet D := 𝓗'.le q _ hD
  have hEm : ∀ n k, MeasurableSet[𝓖 (dyT n k)] (E n k) := measurableSet_linePiece hQa (h𝓗' q D hD) (hS ψ)
  have hEm' : ∀ n k, MeasurableSet (E n k) := fun n k => 𝓖.le _ _ (hEm n k)
  have hDF : ∀ᵐ ω ∂P, ω ∈ D → ω ∈ F ∧ IsForceReg W VL VR ζ ω ∧ ω ∈ avoidSet W ζ ψ q := by
    filter_upwards [hDs, hreg] with ω h1 h2 hωD using ⟨(h1 hωD).1, h2 (h1 hωD).1, (h1 hωD).2⟩
  -- the bound of the pieces' `cfAt`
  have hgb : ∀ᵐ ω ∂P, ∀ n k, ω ∈ E n k → ‖g n k ω‖ ≤ 1 := by
    filter_upwards [hDF] with ω hω n k hωE
    exact norm_cfAt_le_one_of_isForceReg u ψ (hω (linePiece_subset D S n k hωE)).2.1 hωE.2.1 hωE.2.2
  -- the line identity on each piece, with the measurability of the piece's `cfAt`
  have hpiece : ∀ n k, AEStronglyMeasurable ((E n k).indicator (g n k)) P ∧
      ∫ ω, (E n k).indicator f ω ∂P = ∫ ω, (E n k).indicator (g n k) ω ∂P := by
    intro n k
    have hae : (E n k).indicator (g n k) =ᵐ[P] (E n k).indicator (P[f | 𝒢L (dyT n k)]) := by
      filter_upwards [hline ψ (dyT n k), hDF] with ω hω hω'
      by_cases hωE : ω ∈ E n k
      · rw [indicator_of_mem hωE, indicator_of_mem hωE]
        exact (hω (hω' (linePiece_subset D S n k hωE)).1 hωE.2).symm
      · rw [indicator_of_notMem hωE, indicator_of_notMem hωE]
    have hm' : AEStronglyMeasurable ((E n k).indicator (P[f | 𝒢L (dyT n k)])) P :=
      ((stronglyMeasurable_condExp.mono (h𝒢Lm _)).indicator (hEm' n k)).aestronglyMeasurable
    refine ⟨hm'.congr hae.symm, ?_⟩
    rw [integral_congr_ae hae, integral_indicator (hEm' n k), integral_indicator (hEm' n k),
      setIntegral_condExp (h𝒢Lm _) hfi (h𝒢L _ _ (hEm n k))]
  have hgi : ∀ n k, Integrable ((E n k).indicator (g n k)) P := fun n k => by
    refine Integrable.of_bound (hpiece n k).1 1 ?_
    filter_upwards [hgb] with ω hω
    by_cases hωE : ω ∈ E n k
    · rw [indicator_of_mem hωE]; exact hω n k hωE
    · rw [indicator_of_notMem hωE, norm_zero]; exact zero_le_one
  -- the summed identity at every level
  have hsum : ∀ n, ∫ ω, ∑ k ∈ Finset.range (4 ^ n), (E n k).indicator f ω ∂P =
      ∫ ω, ∑ k ∈ Finset.range (4 ^ n), (E n k).indicator (g n k) ω ∂P := fun n => by
    rw [integral_finsetSum _ fun k _ => hfi.indicator (hEm' n k),
      integral_finsetSum _ fun k _ => hgi n k]
    exact Finset.sum_congr rfl fun k _ => (hpiece n k).2
  -- pointwise limits
  have hgood : ∀ᵐ ω ∂P, ω ∈ D → (∃ t, q ≤ Qc t ω) ∧
      (∀ t : ℕ → ℝ≥0, Tendsto (fun n => Qc (t n) ω) atTop (𝓝 q) → ∀ᶠ n in atTop, ω ∈ S (t n)) ∧
      IsForceReg W VL VR ζ ω ∧ ω ∈ avoidSet W ζ ψ q := by
    filter_upwards [hDF, hreach q] with ω hω hr hωD
    obtain ⟨hωF, hp, hav⟩ := hω hωD
    exact ⟨hr hωF hav.1, fun t ht => eventually_mem_lineSafe ψ.hasCompactSupport.isCompact
      (tsupport_subset_H ψ) hp hav.1 hav.2 t ht, hp, hav⟩
  have hlimf := ae_tendsto_sum_linePiece (P := P) (D := D) (S := S) hc hm h0 (fun _ _ => f) f (by
    filter_upwards [hgood] with ω hω hωD
    obtain ⟨hr, hS', -, -⟩ := hω hωD
    exact ⟨hr, hS', tendsto_const_nhds⟩)
  have hlimg := ae_tendsto_sum_linePiece (P := P) (D := D) (S := S) hc hm h0 g
    (cfAt κ W u ψ 1 fun _ => q) (by
    filter_upwards [hgood] with ω hω hωD
    obtain ⟨hr, hS', hp, hav⟩ := hω hωD
    exact ⟨hr, hS', (tendsto_cfAt_of_isForceReg (isBoundedHarmonicExtension_bheProc) ψ hp hav.1 hav.2
      (tendsto_Qc_dyT_hitT (hc ω) (hm ω) (h0 ω) hr)).2⟩)
  have hTf := tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun n => (Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
      (hfm.aestronglyMeasurable.indicator (hEm' n k))))
    (integrable_const 1) (fun n => Eventually.of_forall fun ω =>
      norm_sum_linePiece_le hc hm (fun _ _ => f) n _ fun k _ => hfn ω) hlimf
  have hTg := tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun n => Finset.aestronglyMeasurable_fun_sum _ fun k _ => (hpiece n k).1)
    (integrable_const 1) (fun n => by
      filter_upwards [hgb] with ω hω
      exact norm_sum_linePiece_le hc hm g n _ fun k hk => hω n k hk) hlimg
  rw [integral_indicator hDm] at hTf hTg
  exact tendsto_nhds_unique (hTf.congr fun n => hsum n) hTg

/-- **(L) from the member identities on deterministic physical lines** (the locality half of Aux. lemma 77 at later
lines, from its deterministic-line form). Clock, filtrations and live event as in `hasSafeLaw_of_lineLaw`; if at every
deterministic physical time `t`, on every `𝓖_t`-event inside the line safe event of a finite union of rational balls,
the member identities of the balls hold, then the continuation has K2's input (L) for `𝓗'`. -/
theorem hasSafeMembers_of_lineMembers [IsProbabilityMeasure P] {𝓖 𝓗' : Filtration ℝ≥0 mΩ}
    {X : Ω → DistOn upperHalfPlaneOpens} (hX : ∀ ψ : TestOn upperHalfPlaneOpens, Measurable fun ω => X ω ψ)
    (hc : ∀ ω, Continuous fun t => Qc t ω) (hm : ∀ ω, Monotone fun t => Qc t ω) (h0 : ∀ ω, Qc 0 ω = 0)
    (hQa : ∀ t, Measurable[𝓖 t] (Qc t))
    (h𝓗' : ∀ q D, MeasurableSet[𝓗' q] D → ∀ t, MeasurableSet[𝓖 t] (D ∩ {ω | q ≤ Qc t ω}))
    (hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < ζ ω → ∃ t, q ≤ Qc t ω)
    (hreg : ∀ᵐ ω ∂P, ω ∈ F → IsForceReg W VL VR ζ ω)
    (hS : ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t, MeasurableSet[𝓖 t] (lineSafe Qc W ζ (ballsK Fb) t))
    (hline : ∀ (t : ℝ≥0) (Fb : Finset (ℚ × ℚ × ℚ)), ballsK Fb ⊆ H → ∀ E : Set Ω, MeasurableSet[𝓖 t] E →
      (∀ᵐ ω ∂P, ω ∈ E → ω ∈ F ∧ ω ∈ lineSafe Qc W ζ (ballsK Fb) t) →
      ∀ (f : zsSub (ballsU Fb)) (Ξ : TestOn upperHalfPlaneOpens),
        ∫ ω in E, Complex.exp (Complex.I * (X ω (lapTest (ballsOpen Fb) f + Ξ) : ℂ)) ∂P =
          projFactor (ballsOpen Fb) f Ξ * ∫ ω in E, Complex.exp (Complex.I * (X ω Ξ : ℂ)) ∂P) :
    HasSafeMembers P 𝓗' F ζ W X := by
  intro s Fb hFbH D hD hDs f Ξ
  have hcexp : ∀ φ : TestOn upperHalfPlaneOpens,
      Measurable fun ω => Complex.exp (Complex.I * (X ω φ : ℂ)) := fun φ =>
    (by fun_prop : Measurable fun x : ℝ => Complex.exp (Complex.I * x)).comp (hX φ)
  have hnorm : ∀ (φ : TestOn upperHalfPlaneOpens) ω, ‖Complex.exp (Complex.I * (X ω φ : ℂ))‖ ≤ 1 := fun φ ω => by
    simp only [Complex.norm_exp, Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul, Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_zero, Real.exp_zero, le_refl]
  set a : Ω → ℂ := fun ω => Complex.exp (Complex.I * (X ω (lapTest (ballsOpen Fb) f + Ξ) : ℂ)) with ha
  set b : Ω → ℂ := fun ω => Complex.exp (Complex.I * (X ω Ξ : ℂ)) with hb
  have hai : Integrable a P :=
    Integrable.of_bound (hcexp _).aestronglyMeasurable 1 (Eventually.of_forall (hnorm _))
  have hbi : Integrable b P :=
    Integrable.of_bound (hcexp _).aestronglyMeasurable 1 (Eventually.of_forall (hnorm _))
  set S : ℝ≥0 → Set Ω := lineSafe Qc W ζ (ballsK Fb) with hSdef
  set E : ℕ → ℕ → Set Ω := linePiece Qc s D S with hEdef
  have hDm : MeasurableSet D := 𝓗'.le s _ hD
  have hEm : ∀ n k, MeasurableSet[𝓖 (dyT n k)] (E n k) := measurableSet_linePiece hQa (h𝓗' s D hD) (hS Fb)
  have hEm' : ∀ n k, MeasurableSet (E n k) := fun n k => 𝓖.le _ _ (hEm n k)
  have hsum : ∀ n, ∫ ω, ∑ k ∈ Finset.range (4 ^ n), (E n k).indicator a ω ∂P =
      projFactor (ballsOpen Fb) f Ξ * ∫ ω, ∑ k ∈ Finset.range (4 ^ n), (E n k).indicator b ω ∂P := fun n => by
    rw [integral_finsetSum _ fun k _ => hai.indicator (hEm' n k),
      integral_finsetSum _ fun k _ => hbi.indicator (hEm' n k), Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_indicator (hEm' n k), integral_indicator (hEm' n k)]
    refine hline (dyT n k) Fb hFbH (E n k) (hEm n k) ?_ f Ξ
    filter_upwards [hDs] with ω hω hωE
    exact ⟨(hω (linePiece_subset D S n k hωE)).1, hωE.2⟩
  have hgood : ∀ᵐ ω ∂P, ω ∈ D → (∃ t, s ≤ Qc t ω) ∧
      (∀ t : ℕ → ℝ≥0, Tendsto (fun n => Qc (t n) ω) atTop (𝓝 s) → ∀ᶠ n in atTop, ω ∈ S (t n)) := by
    filter_upwards [hDs, hreg, hreach s] with ω hω hp hr hωD
    obtain ⟨hωF, hsζ, hdis⟩ := hω hωD
    exact ⟨hr hωF hsζ, fun t ht => eventually_mem_lineSafe (isCompact_ballsK Fb) hFbH (hp hωF) hsζ hdis t ht⟩
  have hlim : ∀ c : Ω → ℂ, ∀ᵐ ω ∂P, Tendsto (fun n => ∑ k ∈ Finset.range (4 ^ n), (E n k).indicator c ω) atTop
      (𝓝 (D.indicator c ω)) := fun c =>
    ae_tendsto_sum_linePiece (P := P) (D := D) (S := S) hc hm h0 (fun _ _ => c) c (by
      filter_upwards [hgood] with ω hω hωD
      exact ⟨(hω hωD).1, (hω hωD).2, tendsto_const_nhds⟩)
  have hT : ∀ c : Ω → ℂ, Measurable c → (∀ ω, ‖c ω‖ ≤ 1) →
      Tendsto (fun n => ∫ ω, ∑ k ∈ Finset.range (4 ^ n), (E n k).indicator c ω ∂P) atTop
        (𝓝 (∫ ω in D, c ω ∂P)) := fun c hcm hcn => by
    rw [← integral_indicator hDm]
    exact tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun n => Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
        (hcm.aestronglyMeasurable.indicator (hEm' n k)))
      (integrable_const 1) (fun n => Eventually.of_forall fun ω =>
        norm_sum_linePiece_le hc hm (fun _ _ => c) n _ fun k _ => hcn ω) (hlim c)
  have hTa := hT a (hcexp _) (hnorm _)
  have hTb := (hT b (hcexp _) (hnorm _)).const_mul (projFactor (ballsOpen Fb) f Ξ)
  exact tendsto_nhds_unique (hTa.congr fun n => hsum n) hTb

end Law

end InteractingSLE.Restart.DomainMarkov.Aux79
