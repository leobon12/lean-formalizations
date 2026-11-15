/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BR3RefGap
import InteractingSLE.Spec.Supplement.GB5
import InteractingSLE.Spec.Supplement.GW0
import InteractingSLE.Spec.Exist.DetField
import InteractingSLE.Spec.Sec7.ContinuityProb9Trace

/-!
# BR3's bounded reference: the two core estimates

Packet PROVE-T14-BR3. Supplement pp. 608–609, proof of Proposition BR3 ("This reference has a bounded continuous
complete history ending exactly at `a` at its finite original continuation threshold. To establish that assertion
independently, use `φ(w) = w/(w − a)` […] The transformed left partials are precisely the original admissible left
partials strictly before `a`. The transformed right partials, in order, are `r₀, c, k − 6 − L ≥ k − 4 > c` […] All these
groups are admissible. LP11 supplies the complete transient transformed path, and GB5 protects the closed ray […] The
stopped target change therefore continues throughout the path"), in the reflected form of the landed retargeting API
(the bad group is a right group, the old target goes to `−1` on the left).

The words here are distinct (`LP.IsDistinctForceWord`), separated, with at least one left mark and a right mark before
the bad one (`1 ≤ j`); every left partial sum exceeds `−2`, the right partial sums before the Lean index `j` exceed
`−2`,
and the right weights through `j` sum to at most `−2`.

* **`ae_lifetime_lt_top_core`** (A): if the bad group is the last right mark, every integrated evolution has a finite
  lifetime almost surely. Retarget at the bad mark: the transformed word is admissible (its old target carries the
  partial `κ − 6 − L ≥ κ − 4`), so one of its evolutions has infinite lifetime (GW0's backward implication), a transient
  trace (Theorem 1.3, the named input) and its old target protected by GB5; the retargeted local process agrees with
  such a solution before the new horizon (`ae_exists_code_of_upTo`). An infinite original lifetime then gives either an
  infinite new horizon — impossible with a transient trace (`PullData.false_of_newHorizon_top`) — or a finite one —
  impossible since the gap to the old target stays positive (`newHorizon_eq_top_of_gap`).
* **`ae_far_gap_core`** (B): if one more right mark of weight `0` follows the bad one, its gap to the driver is bounded
  below by a positive constant before the lifetime ("its completed spherical range avoids `1` […] `φ` maps
  `(−∞, a)` to `(1, ∞)`, so that one protected transformed ray excludes both original real rays"). Retarget at that far
  mark: the transformed word is again of type (A), so its evolutions reach a threshold at a finite time, at which the
  gap to its old target is positive (`gapBdd_of_path`); the relative clock is therefore bounded and the original far gap
  stays positive (`far_gap_of_code`).

## Named input

`Exist.Theorem13Statement` (Theorem 1.3, exactly the frozen anchor's type): the transient trace of the transformed
word. Its proof route does not use BR3 or Lemma GW0 (`Spec/Theorem13*.lean`, `Spec/Wire/*`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace BR3Ref

open Zhan Zhan.Retarget Sec2 Sec2.Assembly Sec7 Sec7.RandRestart Sec7.Band

/-! ### Partial sums along initial segments -/

/-- Partial sums along a value-preserving map of an initial segment. -/
theorem sum_filter_le_comp {a b : ℕ} (e : Fin a → Fin b) (he : ∀ l, (e l : ℕ) = l) (f : Fin b → ℝ) (i : Fin a) :
    ∑ l ∈ univ.filter (· ≤ i), f (e l) = ∑ l ∈ univ.filter (· ≤ e i), f l := by
  refine Finset.sum_bij (fun l _ => e l) (fun l hl => ?_) (fun l₁ _ l₂ _ h => ?_) (fun l hl => ?_)
    (fun _ _ => rfl)
  · simp only [mem_filter, Finset.mem_univ, true_and] at hl ⊢
    rw [Fin.le_def, he, he]; exact hl
  · exact Fin.ext (by rw [← he l₁, ← he l₂, h])
  · simp only [mem_filter, Finset.mem_univ, true_and] at hl
    have hv : (l : ℕ) ≤ i := by rw [Fin.le_def, he] at hl; exact hl
    refine ⟨⟨l, lt_of_le_of_lt hv i.isLt⟩, ?_, Fin.ext (by rw [he])⟩
    simp only [mem_filter, Finset.mem_univ, true_and, Fin.le_def]
    exact hv

theorem val_castAdd_castSucc {j m : ℕ} (l : Fin j) : ((Fin.castAdd m l.castSucc : Fin (j + 1 + m)) : ℕ) = l := by
  simp

/-- The transformed right partial sums are the original right partial sums before the target. -/
theorem sum_filter_le_retargetρR {j m : ℕ} (ρR : Fin (j + 1 + m) → ℝ) (i : Fin j) :
    ∑ l ∈ univ.filter (· ≤ i), LP.retargetρR ρR l =
      ∑ l ∈ univ.filter (· ≤ Fin.castAdd m i.castSucc), ρR l :=
  sum_filter_le_comp (fun l : Fin j => Fin.castAdd m l.castSucc) val_castAdd_castSucc ρR i

/-- The transformed left partial sums: the original ones, then `κ − 6 − Σρ_R` at the old target. -/
theorem neg_two_lt_retargetρL_partial {κ : ℝ} (hκ : 4 < κ) {nL j : ℕ} {ρL : Fin nL → ℝ}
    {ρR : Fin (j + 1 + 0) → ℝ} (hL : ∀ i : Fin nL, -2 < ∑ l ∈ univ.filter (· ≤ i), ρL l)
    (hRt : ∑ l, ρR l ≤ -2) (i : Fin (nL + (0 + 1))) :
    -2 < ∑ l ∈ univ.filter (· ≤ i), LP.retargetρL κ ρL ρR l := by
  induction i using Fin.addCases with
  | left i =>
    rw [sum_filter_le_castAdd]
    simpa [LP.retargetρL] using hL i
  | right k =>
    have hk : k = 0 := Fin.ext (by have := k.isLt; simp)
    subst hk
    rw [sum_filter_le_natAdd_zero]
    simp only [LP.retargetρL, Fin.append_left, Fin.append_right, Fin.cons_zero]
    linarith

/-- The old target's partial sum is `κ − 6 − Σρ_R`. -/
theorem retargetρL_partial_old {κ : ℝ} {nL j : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin (j + 1 + 0) → ℝ) :
    ∑ l ∈ univ.filter (· ≤ (Fin.natAdd nL 0 : Fin (nL + (0 + 1)))), LP.retargetρL κ ρL ρR l = κ - 6 - ∑ l, ρR l := by
  rw [sum_filter_le_natAdd_zero]
  simp only [LP.retargetρL, Fin.append_left, Fin.append_right, Fin.cons_zero]
  ring

/-- **GB5 for the old target of the transformed word**: almost surely the transformed driver stays strictly right of
the old target before its lifetime. -/
theorem ae_old_lt_w {κ : ℝ} (hκ : 4 < κ) {nL j : ℕ} {xL : Fin nL → ℝ} {xR : Fin (j + 1 + 0) → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin (j + 1 + 0) → ℝ} (hD : LP.IsDistinctForceWord xL xR) (hj : 1 ≤ j) (hnL : 0 < nL)
    (hL : ∀ i : Fin nL, -2 < ∑ l ∈ univ.filter (· ≤ i), ρL l) (hRt : ∑ l, ρR l ≤ -2)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin (nL + (0 + 1)) → ℝ≥0 → Ω → ℝ} {VR : Fin j → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ (LP.retargetXL xL xR) (LP.retargetXR xR) (LP.retargetρL κ ρL ρR)
      (LP.retargetρR ρR) P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → VL (Fin.natAdd nL 0) t ω < W t ω := by
  have hD' := LP.isDistinctForceWord_retarget hD hj
  have hκ0 : 0 < κ := by linarith
  refine Supp8.GB5.gb5_left hκ0 hD'.1 (Fin.natAdd nL 0) (fun i _ _ => neg_two_lt_retargetρL_partial hκ hL hRt i)
    (fun i hi _ => ?_) ?_ hE
  · have hi' : i = Fin.natAdd nL 0 := by
      refine Fin.ext (le_antisymm ?_ (Fin.le_def.1 hi))
      have := i.isLt; simp; omega
    rw [hi', retargetρL_partial_old]
    linarith
  · obtain ⟨⟨-, hL0, -, hR0⟩, -, hmono⟩ := hD
    have hp := LP.retargetPos_pos hmono hR0 hj
    have e0 : (⟨0, Fin.pos (Fin.natAdd nL (0 : Fin (0 + 1)))⟩ : Fin (nL + (0 + 1))) = Fin.castAdd (0 + 1) ⟨0, hnL⟩ :=
      Fin.ext rfl
    rw [e0]
    simp only [LP.retargetXL, Fin.append_left, Fin.append_right, Fin.cons_zero]
    exact Sec7.neg_one_lt_targetChangeReal hp (lt_of_le_of_lt (hL0 _) hp)

/-! ### Pathwise `GapPos` from positivity -/

/-- A gap that is positive at every time of an infinite lifetime, with continuous paths, is uniformly positive on
compacts. -/
theorem gapPos_of_pos {nL : ℕ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} (ℓ : Fin nL) (hw : Continuous w)
    (hv : Continuous (vL ℓ)) (hpos : ∀ t, vL ℓ t < w t) : GapPos ℓ w vL ⊤ := by
  intro N
  have hc : ContinuousOn (fun t => w t - vL ℓ t) (Icc 0 (N : ℝ≥0)) := (hw.sub hv).continuousOn
  obtain ⟨t₀, -, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, le_rfl, zero_le⟩ hc
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 (hpos t₀))
  exact ⟨n, fun q _ hq => hn.le.trans (hmin ⟨zero_le, hq⟩)⟩

/-! ### (A): the lifetime is finite -/

/-- The code event of (A): the full trace event, infinite lifetime, and the gap to the old target uniformly positive on
compacts. -/
def codeSetA (nL j : ℕ) : Set (XCode (nL + (0 + 1)) j) :=
  (fullTraceSet ∩ {x | cζ x = ⊤}) ∩ gapPosSet (Fin.natAdd nL 0)

theorem measurableSet_codeSetA (nL j : ℕ) : MeasurableSet (codeSetA nL j) :=
  (measurableSet_fullTraceSet.inter (measurableSet_eq_fun measurable_cζ measurable_const)).inter
    (measurableSet_gapPosSet _)

/-- **(A): a last bad right group is reached at a finite time.** For `κ > 4` and a distinct separated word with
`nL ≥ 1` left marks and right list of length `j + 1` (`j ≥ 1`), whose left partial sums all exceed `−2`, whose right
partial sums before the last mark exceed `−2` and whose right weights sum to at most `−2`, every integrated evolution
has a finite lifetime almost surely. -/
theorem ae_lifetime_lt_top_core (hT13 : Exist.Theorem13Statement.{0}) {κ : ℝ} (hκ : 4 < κ) {nL j : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin (j + 1 + 0) → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin (j + 1 + 0) → ℝ}
    (hD : LP.IsDistinctForceWord xL xR) (hsep : ∀ i i', xL i < xR i') (hj : 1 ≤ j) (hnL : 0 < nL)
    (hL : ∀ i : Fin nL, -2 < ∑ l ∈ univ.filter (· ≤ i), ρL l)
    (hR : ∀ i : Fin (j + 1 + 0), (i : ℕ) < j → -2 < ∑ l ∈ univ.filter (· ≤ i), ρR l)
    (hRt : ∑ l, ρR l ≤ -2) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin (j + 1 + 0) → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω < ⊤ := by
  have hκ0 : 0 < κ := by linarith
  have hD' := LP.isDistinctForceWord_retarget hD hj
  have hsep' := retarget_sep hD hj hsep
  have hL' := neg_two_lt_retargetρL_partial hκ hL hRt
  have hR' : ∀ i : Fin j, -2 < ∑ l ∈ univ.filter (· ≤ i), LP.retargetρR ρR l := fun i => by
    rw [sum_filter_le_retargetρR]
    exact hR _ (by rw [val_castAdd_castSucc]; exact i.isLt)
  -- one evolution of the transformed word with the code event
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, hE₀⟩ :=
    exists_isIntegratedSLEEvolution_assembled hκ0 hD'.1 (ρL := LP.retargetρL κ ρL ρR) (ρR := LP.retargetρR ρR)
  have hlife := GW0.ae_lifetime_eq_top_of_neg_two_lt hD'.1 (fun i _ => hL' i) (fun i _ => hR' i) hE₀
  have hgb := ae_old_lt_w hκ hD hj hnL hL hRt hE₀
  have h13 := hT13 hκ0 hD'.1 hE₀
  have hW := ae_mem_lawSetS_of_ae hκ0 hsep' hE₀ (S := codeSetA nL j)
    (Ψ := fun w vL _ τ => (FullTrace w τ ∧ τ = ⊤) ∧ GapPos (Fin.natAdd nL 0) w vL τ)
    (measurableSet_codeSetA nL j)
    (fun x hx hl => by
      show (x ∈ fullTraceSet ∧ cζ x = ⊤) ∧ GapPos (Fin.natAdd nL 0) (cw x) (cvL x) (cζ x) ↔
        (FullTrace (cw x) (cζ x) ∧ cζ x = ⊤) ∧ GapPos (Fin.natAdd nL 0) (cw x) (cvL x) (cζ x)
      rw [mem_fullTraceSet_iff x hx hl])
    (fun w w' vL vL' vR vR' τ h hw => ⟨⟨fullTrace_congr w w' τ (fun t ht => (h t ht).1) hw.1.1, hw.1.2⟩,
      gapPos_congr _ w w' vL vL' vR vR' τ h hw.2⟩)
    (by
      filter_upwards [hlife, hgb, h13, hE₀.ae_isIntegratedSLEPath] with ω hl hg h13 hp
      have hc : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₀ ω := fun t => by rw [hl]; exact ENNReal.coe_lt_top
      refine ⟨⟨fullTrace_of_traceEvent h13.2, hl⟩, ?_⟩
      rw [hl]
      exact gapPos_of_pos _ (continuousOn_univ.1 (hp.isForcePath.continuousOn_w.mono fun t _ => hc t))
        (continuousOn_univ.1 ((hp.isForcePath.continuousOn_vL _).mono fun t _ => hc t)) fun t => hg t (hc t))
  -- the retargeted local process and a canonical code driven by the same path
  obtain ⟨𝓘, β, τ, -, hτ, hloc⟩ := retargetEvolutionStatement.{u} P 𝓕 xL xR ρL ρR W VL VR B ζ hκ0 hD hj hE
  have hcode := ae_exists_code_of_upTo hloc hsep' hW
  have hcode' := Sec7.ae_of_ae_prod_fst (P := P) (Φ := fun ω => ∃ x ∈ CRel κ (LP.retargetXL xL xR) (LP.retargetXR xR)
      (LP.retargetρL κ ρL ρR) (LP.retargetρR ρR), x ∈ codeSetA nL j ∧ τ ω ≤ cζ x ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω → newW xR (fun t => W t ω) (fun i t => VR i t ω) t = cw x t ∧
        (∀ i, newVL xR (fun t => W t ω) (fun i t => VL i t ω) (fun i t => VR i t ω) i t = cvL x i t) ∧
        ∀ i, newVR xR (fun t => W t ω) (fun i t => VR i t ω) i t = cvR x i t) hcode
  filter_upwards [hcode', hτ, hE.ae_isIntegratedSLEPath] with ω hc hτω hp
  obtain ⟨x, hxC, ⟨⟨hxtr, hxζ⟩, hxgap⟩, -, hag⟩ := hc
  have hxp : IsIntegratedSLEPath κ (LP.retargetXL xL xR) (LP.retargetXR xR) (LP.retargetρL κ ρL ρR)
      (LP.retargetρR ρR) (cw x) (cvL x) (cvR x) (cb x) (cζ x) := hxC.1.2.2
  have hxζ' : cζ x = ⊤ := hxζ
  have hcx : ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x := fun t => by rw [hxζ']; exact ENNReal.coe_lt_top
  have hwc : Continuous (cw x) := continuousOn_univ.1 (hxp.isForcePath.continuousOn_w.mono fun t _ => hcx t)
  have hgap' : GapPos (Fin.natAdd nL 0) (cw x) (cvL x) ⊤ := by
    have h : GapPos (Fin.natAdd nL 0) (cw x) (cvL x) (cζ x) := hxgap
    rwa [hxζ'] at h
  have htrc : TraceEvent (cw x) ⊤ := by
    have hx1 : (cw x, cζ x) ∈ traceSet := hxtr.1
    have hx1' : ratVals (cw x) ∈ transientSet := by
      rcases hx1 with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd hxζ' h
    obtain ⟨η, hη, htr⟩ := (mem_transientSet_iff hwc hxp.1).1 hx1'
    exact ⟨η, hη, fun _ => htr⟩
  exact lifetime_lt_top_of_code hp hD hj hRt hwc
    (continuousOn_univ.1 ((hxp.isForcePath.continuousOn_vL _).mono fun t _ => hcx t)) htrc hgap'
    fun t ht => ⟨(hag t (by rw [hτω]; exact ht)).1, (hag t (by rw [hτω]; exact ht)).2.1 _⟩

/-! ### (B): the far gap stays positive -/

/-- **(B): a zero-weight mark after the bad group keeps a positive gap.** For `κ > 4` and a distinct separated word with
`nL ≥ 1` left marks and right list of length `j + 2` (`j ≥ 1`): left partial sums all `> −2`, right partial sums before
the Lean index `j` all `> −2`, the right weights through `j` summing to at most `−2`, and weight `0` at the last mark
`j + 1`. Then almost surely the gap `V^R_{j+1} − W` is bounded below by a positive constant before the lifetime. -/
theorem ae_far_gap_core (hT13 : Exist.Theorem13Statement.{0}) {κ : ℝ} (hκ : 4 < κ) {nL j : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin (j + 1 + 1 + 0) → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin (j + 1 + 1 + 0) → ℝ}
    (hD : LP.IsDistinctForceWord xL xR) (hsep : ∀ i i', xL i < xR i') (hj : 1 ≤ j) (hnL : 0 < nL)
    (hL : ∀ i : Fin nL, -2 < ∑ l ∈ univ.filter (· ≤ i), ρL l)
    (hR : ∀ i : Fin (j + 1 + 1 + 0), (i : ℕ) < j → -2 < ∑ l ∈ univ.filter (· ≤ i), ρR l)
    (hRj : ∑ l ∈ univ.filter (fun l : Fin (j + 1 + 1 + 0) => (l : ℕ) ≤ j), ρR l ≤ -2)
    (hfar : ρR (LP.retargetIdx (j + 1) 0) = 0) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin (j + 1 + 1 + 0) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → δ ≤ VR (LP.retargetIdx (j + 1) 0) t ω - W t ω := by
  have hκ0 : 0 < κ := by linarith
  have hj1 : 1 ≤ j + 1 := by omega
  have hD' := LP.isDistinctForceWord_retarget hD hj1
  have hsep' := retarget_sep hD hj1 hsep
  -- the total right weight is the bad partial sum
  have hRt : ∑ l, ρR l ≤ -2 := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun l : Fin (j + 1 + 1 + 0) => (l : ℕ) ≤ j)]
    have h0 : ∑ l ∈ univ.filter (fun l : Fin (j + 1 + 1 + 0) => ¬ (l : ℕ) ≤ j), ρR l = 0 := by
      refine Finset.sum_eq_zero fun l hl => ?_
      have hl' : l = LP.retargetIdx (j + 1) 0 := by
        simp only [mem_filter, Finset.mem_univ, true_and, not_le] at hl
        refine Fin.ext ?_
        simp only [LP.retargetIdx, Fin.val_castAdd, Fin.val_last]
        have := l.isLt; omega
      rw [hl', hfar]
    rw [h0, add_zero]
    exact hRj
  -- the transformed word is of type (A)
  have hL' := neg_two_lt_retargetρL_partial hκ hL hRt
  have hR' : ∀ i : Fin (j + 1 + 0), (i : ℕ) < j → -2 < ∑ l ∈ univ.filter (· ≤ i), LP.retargetρR ρR l := by
    intro i hi
    rw [sum_filter_le_retargetρR]
    exact hR _ (by rw [val_castAdd_castSucc]; exact hi)
  have hRt' : ∑ l, LP.retargetρR ρR l ≤ -2 := by
    have e1 : ∑ l, LP.retargetρR ρR l = ∑ l ∈ univ.filter (· ≤ Fin.last j), LP.retargetρR ρR l := by
      rw [Finset.filter_true_of_mem fun l _ => Fin.le_last l]
    rw [e1, sum_filter_le_retargetρR]
    refine le_of_eq_of_le (Finset.sum_congr ?_ fun _ _ => rfl) hRj
    ext l
    simp only [mem_filter, Finset.mem_univ, true_and, Fin.le_def, val_castAdd_castSucc, Fin.val_last]
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, hE₀⟩ :=
    exists_isIntegratedSLEEvolution_assembled hκ0 hD'.1 (ρL := LP.retargetρL κ ρL ρR) (ρR := LP.retargetρR ρR)
  have hfin := ae_lifetime_lt_top_core (j := j) hT13 hκ hD' hsep' hj (by omega) hL' hR' hRt' hE₀
  have hgb := ae_old_lt_w hκ hD hj1 hnL hL hRt hE₀
  have hW := ae_mem_lawSetS_of_ae hκ0 hsep' hE₀ (S := gapBddSet (nR := j + 1) (Fin.natAdd nL 0))
    (Ψ := fun w vL _ τ => GapBdd (Fin.natAdd nL 0) w vL τ) (measurableSet_gapBddSet _) (fun _ _ _ => Iff.rfl)
    (fun w w' vL vL' vR vR' τ h hw => gapBdd_congr _ w w' vL vL' vR vR' τ h hw)
    (by
      filter_upwards [hfin, hgb, hE₀.ae_tendsto_threshold hκ0, hE₀.ae_isIntegratedSLEPath] with ω hf hg hl hp
      exact gapBdd_of_path hp hsep' hL' (Fin.last j) (fun i hi => hR' i (Fin.lt_def.1 hi)) _ hg hf hl)
  obtain ⟨𝓘, β, τ, -, hτ, hloc⟩ := retargetEvolutionStatement.{u} P 𝓕 xL xR ρL ρR W VL VR B ζ hκ0 hD hj1 hE
  have hcode := ae_exists_code_of_upTo hloc hsep' hW
  have hcode' := Sec7.ae_of_ae_prod_fst (P := P) (Φ := fun ω => ∃ x ∈ CRel κ (LP.retargetXL xL xR) (LP.retargetXR xR)
      (LP.retargetρL κ ρL ρR) (LP.retargetρR ρR), x ∈ gapBddSet (Fin.natAdd nL 0) ∧ τ ω ≤ cζ x ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω → newW xR (fun t => W t ω) (fun i t => VR i t ω) t = cw x t ∧
        (∀ i, newVL xR (fun t => W t ω) (fun i t => VL i t ω) (fun i t => VR i t ω) i t = cvL x i t) ∧
        ∀ i, newVR xR (fun t => W t ω) (fun i t => VR i t ω) i t = cvR x i t) hcode
  filter_upwards [hcode', hτ, hE.ae_isIntegratedSLEPath] with ω hc hτω hp
  obtain ⟨x, hxC, hxgap, hle, hag⟩ := hc
  have hxp : IsIntegratedSLEPath κ (LP.retargetXL xL xR) (LP.retargetXR xR) (LP.retargetρL κ ρL ρR)
      (LP.retargetρR ρR) (cw x) (cvL x) (cvR x) (cb x) (cζ x) := hxC.1.2.2
  rw [hτω] at hle hag
  exact far_gap_of_code hp hD hj1 hRt hxp.isForcePath.continuousOn_w (hxp.isForcePath.continuousOn_vL _) hxgap hle
    fun t ht => ⟨(hag t ht).1, (hag t ht).2.1 _⟩

end BR3Ref

end Theorem14

end InteractingSLE
