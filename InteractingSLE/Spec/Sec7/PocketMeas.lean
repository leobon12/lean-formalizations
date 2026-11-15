/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketAdapt
import InteractingSLE.Spec.Restart.ClockMeasCap

/-!
# Measurability of the prefix events of a random driven curve

Packet PROVE-STRIPSYS20, item 2. Specification §7.4, proof of Aux. lemma 125 (`source/spec/p385-432.md` L213–L232,
p. 396–397: "The relative stopping filtration … These are genuine stopping times in the relative history"); proof of
Aux. lemma 119 (p. 387: "the component, its endpoints, the geometric prefixes, and their normalized maps are measurable
from the incoming labels").

PROVE-STRIPSYS18's relative history filtration `PocketAdapt.prefixFilt 𝓔 h𝓔 γ hm` needs the **prefix events**
`prefixEvent γ r n k` ("before the terminal capacity time, the prefix up to capacity time `r` meets the closed dyadic
square `(n, k)`") to be measurable. Here they are, for every random curve with local Loewner drivers
(`IsDrivenCurve`) whose value at each fixed own time is measurable:

* `capClock_eq_hcapHit`: the capacity clock is the grid capacity of the path prefix (`Restart.hcapHit_image_eq`);
* **`measurable_capClock`**, **`measurable_capLife`**: the capacity clock at a fixed own time and the terminal
  capacity time are measurable (`Restart.measurable_hcapHit_image`; no adaptedness is needed, so there is no
  circularity with prefix adaptedness);
* **`prefix_nonempty_iff`** (deterministic): before the terminal capacity time, the prefix up to capacity time `r`
  meets a closed set `Q` iff for every `m` the seed or a rational own time `q` with `capClock q < r` is within
  `1/(m+1)` of `Q` (compactness of the prefix, continuity, strict monotonicity of the clock);
* **`measurableSet_prefixEvent`**: the prefix events are measurable;
* **`pocketWordEvolution_of_charFun_measurable`**: PROVE-STRIPSYS18's `pocketWordEvolution_of_charFun_prefixFilt` with
  its measurability hypothesis `hm` discharged by fixed-time measurability of the curve.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketMeas

open Lemma71C PocketTraversal PocketAdapt

/-! ### The capacity clock as a grid capacity -/

/-- A curve on `[0, ∞)` read on `ℝ≥0`. -/
def nnPath (γ : ℝ → ℂ) (t : ℝ≥0) : ℂ := γ t

theorem image_nnPath (γ : ℝ → ℂ) {u : ℝ} (hu : 0 ≤ u) : nnPath γ '' Icc 0 u.toNNReal = γ '' Icc 0 u := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ⟨t.2, (Real.le_toNNReal_iff_coe_le hu).1 ht.2⟩, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    refine ⟨s.toNNReal, ⟨zero_le, Real.toNNReal_le_toNNReal hs.2⟩, ?_⟩
    simp only [nnPath, Real.coe_toNNReal _ hs.1]

theorem continuous_nnPath {γ : ℝ → ℂ} (hγ : IsDrivenCurve γ) : Continuous (nnPath γ) :=
  hγ.continuousOn.comp_continuous NNReal.continuous_coe fun t => t.2

/-- **The capacity clock is the grid capacity of the prefix** (`Restart.hcapHit_image_eq`). -/
theorem capClock_eq_hcapHit {γ : ℝ → ℂ} (hγ : IsDrivenCurve γ) {u : ℝ} (hu : 0 ≤ u) :
    capClock γ u = (WholeField.hcapHit (nnPath γ '' Icc 0 u.toNNReal)).toReal / 2 := by
  have h0 : (nnPath γ 0).im ≤ 0 := by simp [nnPath, hγ.zero]
  rw [Restart.hcapHit_image_eq (continuous_nnPath hγ).continuousOn h0, image_nnPath γ hu]
  have hnn : 0 ≤ ConformalImage.hcapSet (fillH (γ '' Icc 0 u)) := by
    have := hγ.capClock_nonneg hu
    rw [capClock] at this
    linarith
  rw [ENNReal.toReal_ofReal hnn, capClock]

variable {Ω : Type*} [MeasurableSpace Ω] {γ : Ω → ℝ → ℂ}

/-- **The capacity clock of a random driven curve at a fixed own time is measurable.** -/
theorem measurable_capClock (hγ : ∀ ω, IsDrivenCurve (γ ω)) (hm : ∀ u, 0 ≤ u → Measurable fun ω => γ ω u)
    {u : ℝ} (hu : 0 ≤ u) : Measurable fun ω => capClock (γ ω) u := by
  have hm' : ∀ t : ℝ≥0, Measurable fun ω => nnPath (γ ω) t := fun t => hm t t.2
  have h := ((Restart.measurable_hcapHit_image (fun ω => continuous_nnPath (hγ ω)) hm'
    u.toNNReal).ennreal_toReal).div_const 2
  have e : (fun ω => capClock (γ ω) u) =
      fun ω => (WholeField.hcapHit (nnPath (γ ω) '' Icc 0 u.toNNReal)).toReal / 2 :=
    funext fun ω => capClock_eq_hcapHit (hγ ω) hu
  rw [e]
  exact h

/-- **The terminal capacity time of a random driven curve is measurable.** -/
theorem measurable_capLife (hγ : ∀ ω, IsDrivenCurve (γ ω)) (hm : ∀ u, 0 ≤ u → Measurable fun ω => γ ω u) :
    Measurable fun ω => capLife (γ ω) :=
  Measurable.iSup fun n : ℕ => ENNReal.measurable_ofReal.comp (measurable_capClock hγ hm n.cast_nonneg)

/-! ### The prefix events through rational own times -/

/-- **A prefix up to a capacity time meets a closed set** iff, at every scale `1/(m+1)`, the seed or the curve at a
rational own time before that capacity time is close to the set. -/
theorem prefix_nonempty_iff {γ : ℝ → ℂ} (hγ : IsDrivenCurve γ) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : ENNReal.ofReal r < capLife γ) {Q : Set ℂ} (hQ : IsClosed Q) :
    (Q ∩ γ '' Icc 0 (capInv γ r)).Nonempty ↔ ∀ m : ℕ, (0 : ℂ) ∈ thickening (1 / ((m : ℝ) + 1)) Q ∨
      ∃ q : ℚ, 0 ≤ (q : ℝ) ∧ capClock γ q < r ∧ γ q ∈ thickening (1 / ((m : ℝ) + 1)) Q := by
  obtain ⟨hc0, hcr⟩ := hγ.capInv_spec hr0 hr
  set c := capInv γ r with hcdef
  constructor
  · rintro ⟨z, hzQ, u, hu, rfl⟩ m
    have hε : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    have hmem : γ u ∈ thickening (1 / ((m : ℝ) + 1)) Q := self_subset_thickening hε Q hzQ
    rcases hu.1.lt_or_eq with hu0 | hu0
    · right
      have hpre : γ ⁻¹' thickening (1 / ((m : ℝ) + 1)) Q ∈ 𝓝[Ici 0] u :=
        (hγ.continuousOn u hu.1).preimage_mem_nhdsWithin (isOpen_thickening.mem_nhds hmem)
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hpre
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max (u - δ) 0 < u from max_lt (by linarith) hu0)
      have hq0 : (0 : ℝ) ≤ q := (le_max_right _ _).trans hq1.le
      refine ⟨q, hq0, ?_, hball ⟨?_, hq0⟩⟩
      · rw [← hcr]
        exact hγ.strictMonoOn_capClock hq0 hc0 (lt_of_lt_of_le hq2 hu.2)
      · rw [mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [le_max_left (u - δ) 0]
    · left
      rw [← hu0, hγ.zero] at hmem
      exact hmem
  · intro h
    by_contra hne
    have hK : IsCompact (γ '' Icc 0 c) :=
      isCompact_Icc.image_of_continuousOn (hγ.continuousOn.mono fun v hv => hv.1)
    have hdisj : Disjoint (γ '' Icc 0 c) Q := by
      rw [Set.disjoint_iff_inter_eq_empty, inter_comm]
      exact Set.not_nonempty_iff_eq_empty.1 hne
    obtain ⟨δ, hδ, hd⟩ := hdisj.exists_thickenings hK hQ
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    have hsub : thickening (1 / ((m : ℝ) + 1)) Q ⊆ thickening δ Q := thickening_mono hm.le Q
    have hKδ : γ '' Icc 0 c ⊆ thickening δ (γ '' Icc 0 c) := self_subset_thickening hδ _
    rcases h m with h0 | ⟨q, hq0, hqr, hqQ⟩
    · have h0K : (0 : ℂ) ∈ γ '' Icc 0 c := ⟨0, ⟨le_rfl, hc0⟩, hγ.zero⟩
      exact Set.disjoint_left.1 hd (hKδ h0K) (hsub h0)
    · have hqc : (q : ℝ) ≤ c := by
        by_contra hlt
        rw [not_le] at hlt
        have := hγ.strictMonoOn_capClock hc0 hq0 hlt
        linarith
      exact Set.disjoint_left.1 hd (hKδ ⟨q, ⟨hq0, hqc⟩, rfl⟩) (hsub hqQ)

/-- **The prefix events of a random driven curve are measurable**, as soon as the curve is measurable at every fixed
own time. -/
theorem measurableSet_prefixEvent (hγ : ∀ ω, IsDrivenCurve (γ ω))
    (hm : ∀ u, 0 ≤ u → Measurable fun ω => γ ω u) (r : ℝ≥0) (n : ℕ) (k : ℤ × ℤ) :
    MeasurableSet (prefixEvent γ r n k) := by
  set Q := Restart.dyadicSquare n k with hQ
  have e : prefixEvent γ r n k = {ω | (r : ℝ≥0∞) < capLife (γ ω)} ∩ ⋂ m : ℕ,
      ({_ω | (0 : ℂ) ∈ thickening (1 / ((m : ℝ) + 1)) Q} ∪ ⋃ q : ℚ,
        {ω | 0 ≤ (q : ℝ) ∧ capClock (γ ω) q < r ∧ γ ω q ∈ thickening (1 / ((m : ℝ) + 1)) Q}) := by
    ext ω
    simp only [prefixEvent, mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_union, mem_iUnion]
    constructor
    · rintro ⟨hr, hne⟩
      have hr' : ENNReal.ofReal (r : ℝ) < capLife (γ ω) := by rwa [ENNReal.ofReal_coe_nnreal]
      exact ⟨hr, (prefix_nonempty_iff (hγ ω) r.2 hr' (Restart.isClosed_dyadicSquare n k)).1 hne⟩
    · rintro ⟨hr, h⟩
      have hr' : ENNReal.ofReal (r : ℝ) < capLife (γ ω) := by rwa [ENNReal.ofReal_coe_nnreal]
      exact ⟨hr, (prefix_nonempty_iff (hγ ω) r.2 hr' (Restart.isClosed_dyadicSquare n k)).2 h⟩
  rw [e]
  refine (measurableSet_lt measurable_const (measurable_capLife hγ hm)).inter
    (MeasurableSet.iInter fun m => (MeasurableSet.const _).union (MeasurableSet.iUnion fun q => ?_))
  by_cases hq : (0 : ℝ) ≤ q
  · simp only [hq, true_and]
    exact (measurableSet_lt (measurable_capClock hγ hm hq) measurable_const).inter
      (hm q hq isOpen_thickening.measurableSet)
  · simp only [hq, false_and, ofPred_false, MeasurableSet.empty]

/-! ### hPW with the measurability hypothesis discharged -/

/-- **hPW from the coupling clause, with fixed-time measurability of the curve** (PROVE-STRIPSYS18's
`pocketWordEvolution_of_charFun_prefixFilt` with its hypothesis `hm` supplied by `measurableSet_prefixEvent`). -/
theorem pocketWordEvolution_of_charFun_measurable.{v} {κ rL rR : ℝ} (hκ : 4 < κ) (hLd : rL < κ / 2 - 4)
    (hRd : rR < κ / 2 - 4) {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} (hρL : ρL 0 = rL)
    (hρR : ρR 0 = rR) (hsL : ∀ m : Fin (nL + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρL i)
    (hsR : ∀ m : Fin (nR + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρR i)
    {Ω : Type v} {𝓔 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (h𝓔 : 𝓔 ≤ mΩ) {γ : Ω → ℝ → ℂ} (hγ : ∀ ω, IsDrivenCurve (γ ω))
    (hγm : ∀ u, 0 ≤ u → Measurable[mΩ] fun ω => γ ω u)
    (hunb : ∀ ω (M : ℝ), ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    (hxLm : Measurable[𝓔] xL) (hxRm : Measurable[𝓔] xR)
    (hseedL : ∀ ω, xL ω 0 = 0) (hseedR : ∀ ω, xR ω 0 = 0)
    (hxLd : ∀ ω (i : Fin nL), xL ω i.succ < 0) (hxRd : ∀ ω (j : Fin nR), 0 < xR ω j.succ)
    (hxLi : ∀ ω, Antitone (xL ω)) (hxRi : ∀ ω, Monotone (xR ω)) {h : Ω → DistOn upperHalfPlaneOpens}
    (hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => h ω φ) P)
    (hcf : Coupling.MartMeans.IsCouplingCharFun κ ρL ρR P
      (usualAugmentation (prefixFilt 𝓔 h𝓔 γ fun r n k => measurableSet_prefixEvent hγ hγm r n k) P)
      (fun t ω => segDriver (γ ω) t) (geomLW (fun t ω => segDriver (γ ω) t) xL)
      (geomRW (fun t ω => segDriver (γ ω) t) xR) (fun ω => capLife (γ ω)) h) :
    Lemma725Ref.PocketWordEvolution.{v} κ rL rR :=
  pocketWordEvolution_of_charFun_prefixFilt hκ hLd hRd hρL hρR hsL hsR h𝓔 _ hγ hunb hxLm hxRm hseedL hseedR
    hxLd hxRd hxLi hxRi hint hcf

end InteractingSLE.Sec7.PocketMeas
