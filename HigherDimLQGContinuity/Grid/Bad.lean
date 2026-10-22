import HigherDimLQGContinuity.Grid.Arithmetic
import HigherDimLQGContinuity.Endpoint.Events
import HigherDimLQGContinuity.Param.Interval

/-!
# Bad comparison events between successive parameter grids

At each fine node we compare with its lower coarse bracket, and also its upper bracket
when that bracket belongs to the window.  This is the finite-pair event of Part C §5.1.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric

def posLowerBad (d : ℕ) (lo hi R : ℝ) (j : ℕ) : Set (DistRd d) :=
  ⋃ m ∈ Finset.range (2 ^ posLevel (j + 1) + 1),
    {g | ENNReal.ofReal (posDelta j) <
      supDistLU d R (gridProfile d (posNode lo hi (j + 1) m) g)
        (gridProfile d (posNode lo hi j (posBracket j m)) g)}

def posUpperBad (d : ℕ) (lo hi R : ℝ) (j : ℕ) : Set (DistRd d) :=
  ⋃ m ∈ Finset.range (2 ^ posLevel (j + 1) + 1),
    if posBracket j m < 2 ^ posLevel j then
      {g | ENNReal.ofReal (posDelta j) <
        supDistLU d R (gridProfile d (posNode lo hi (j + 1) m) g)
          (gridProfile d (posNode lo hi j (posBracket j m + 1)) g)}
    else ∅

def posBad (d : ℕ) (lo hi R : ℝ) (j : ℕ) : Set (DistRd d) :=
  posLowerBad d lo hi R j ∪ posUpperBad d lo hi R j

private theorem posNode_subcrit {d : ℕ} (hd : 3 ≤ d)
    {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo < hi)
    (hhi : 0 < hi ∧ Real.sqrt (2 * d) < distExp d hi)
    {j m : ℕ} (hm : m ≤ 2 ^ posLevel j) :
    posNode lo hi j m ∈ subcritSet d := by
  have hmem := posNode_mem hlohi hm
  exact (gap24 (by omega : 2 ≤ d) ⟨hhi.1, hhi.2⟩).choose_spec.2.2.2.1
    ⟨hlo.trans_le hmem.1, hmem.2⟩

private theorem posPair_measurable {d : ℕ} (hd : 3 ≤ d)
    {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo < hi)
    (hhi : 0 < hi ∧ Real.sqrt (2 * d) < distExp d hi)
    {i j m n : ℕ} (hm : m ≤ 2 ^ posLevel i) (hn : n ≤ 2 ^ posLevel j) (R δ : ℝ) :
    MeasurableSet {g | ENNReal.ofReal δ <
      supDistLU d R (gridProfile d (posNode lo hi i m) g)
        (gridProfile d (posNode lo hi j n) g)} := by
  have hmeas1 := measurable_gridProfile hd (posNode_subcrit hd hlo hlohi hhi hm)
  have hmeas2 := measurable_gridProfile hd (posNode_subcrit hd hlo hlohi hhi hn)
  exact measurableSet_lt measurable_const
    (endpt_measurable_supDistLU
      (fun p => (continuous_eval_const p).measurable.comp hmeas1)
      (fun p => (continuous_eval_const p).measurable.comp hmeas2) R)

theorem measurable_posBad {d : ℕ} (hd : 3 ≤ d)
    {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo < hi)
    (hhi : 0 < hi ∧ Real.sqrt (2 * d) < distExp d hi) (R : ℝ) (j : ℕ) :
    MeasurableSet (posBad d lo hi R j) := by
  have hfin (m : ℕ) (hm : m ∈ Finset.range (2 ^ posLevel (j + 1) + 1)) :
      m ≤ 2 ^ posLevel (j + 1) := by
    simp only [Finset.mem_range] at hm
    omega
  have hlow : MeasurableSet (posLowerBad d lo hi R j) := by
    unfold posLowerBad
    exact Finset.measurableSet_biUnion _ fun m hm =>
      posPair_measurable hd hlo hlohi hhi (hfin m hm) (posBracket_le (hfin m hm)) R (posDelta j)
  have hup : MeasurableSet (posUpperBad d lo hi R j) := by
    unfold posUpperBad
    apply Finset.measurableSet_biUnion
    intro m hm
    split_ifs with hb
    · exact posPair_measurable hd hlo hlohi hhi (hfin m hm) (Nat.succ_le_iff.2 hb) R (posDelta j)
    · exact MeasurableSet.empty
  exact hlow.union hup

/-- `Prop37Shape` gives the finite union bound whenever the mesh and depth satisfy
its two comparison inequalities.  The witnesses depend on the window and `R`, as they must. -/
theorem exists_posBad_bound_constants {d : ℕ} (hd : 3 ≤ d) (hP : Prop37Shape d)
    {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo < hi)
    (hhi : 0 < hi ∧ Real.sqrt (2 * d) < distExp d hi)
    {R : ℝ} (hR : 1 ≤ R) :
    ∃ B M C c : ℝ, 0 < B ∧ 0 < M ∧ 0 < c ∧ c ≤ 1 ∧ 1 ≤ C ∧
      ∀ j : ℕ,
        posWidth lo hi j ≤ Real.exp (-(C * lo ^ (-B) * posDelta j ^ (-B))) →
        C * posDelta j ^ (-M) * Real.log (C / posDelta j) ≤
          c * posDelta j / posWidth lo hi j →
        normLGFLaw d (posBad d lo hi R j) ≤
          ENNReal.ofReal ((2 ^ posLevel (j + 1) + 1) *
            (C * posDelta j ^ (-M) * Real.exp (-(c * posDelta j ^ M *
              (c * posDelta j / posWidth lo hi j))))) +
          ENNReal.ofReal ((2 ^ posLevel (j + 1) + 1) *
            (C * posDelta j ^ (-M) * Real.exp (-(c * posDelta j ^ M *
              (c * posDelta j / posWidth lo hi j))))) := by
  obtain ⟨ps, cseed, _hps, _hps1, _hcseed, hshape⟩ := hP hi hhi.1 hhi.2
  obtain ⟨B, M, C, c, hB, hM, hc, hc1, hC, hcmp⟩ := hshape R hR
  refine ⟨B, M, C, c, hB, hM, hc, hc1, hC, ?_⟩
  intro j hG hdepth
  let δ := posDelta j
  let n : ℝ := c * δ / posWidth lo hi j
  let b : ℝ := C * δ ^ (-M) * Real.exp (-(c * δ ^ M * n))
  have hδ : 0 < δ := posDelta_pos j
  have hδ8 : δ < 1 / 8 := posDelta_lt_eighth j
  have hw : 0 < posWidth lo hi j := posWidth_pos hlohi j
  have hn : 0 ≤ n := div_nonneg (mul_nonneg hc.le hδ.le) hw.le
  have hdrift : posWidth lo hi j * n = c * δ := by
    dsimp [n]
    field_simp
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hlow (m : ℕ) (hm : m ≤ 2 ^ posLevel (j + 1)) :
      normLGFLaw d {g | ENNReal.ofReal δ <
        supDistLU d R (gridProfile d (posNode lo hi (j + 1) m) g)
          (gridProfile d (posNode lo hi j (posBracket j m)) g)} ≤ ENNReal.ofReal b := by
    have hfine := posNode_mem hlohi hm
    have hcoarse := posNode_mem hlohi (posBracket_le hm)
    have hsf := strongAt_spec hd (posNode_subcrit hd hlo hlohi hhi hm)
    have hsc := strongAt_spec hd (posNode_subcrit hd hlo hlohi hhi (posBracket_le hm))
    have hclose : |posNode lo hi (j + 1) m - posNode lo hi j (posBracket j m)| ≤
        posWidth lo hi j := by
      rw [abs_of_nonneg (by linarith [posNode_bracket_le hlohi j m])]
      exact posNode_sub_bracket_le hlohi j m
    have hdrift' : |posNode lo hi (j + 1) m - posNode lo hi j (posBracket j m)| * n ≤ c * δ :=
      (mul_le_mul_of_nonneg_right hclose hn).trans_eq hdrift
    have hG' : |posNode lo hi (j + 1) m - posNode lo hi j (posBracket j m)| ≤
        Real.exp (-(C * lo ^ (-B) * δ ^ (-B))) := hclose.trans hG
    have h := hcmp lo ⟨hlo, hlohi.le⟩ _ hfine _ hcoarse _ _ hsf hsc δ hδ hδ8 n hdepth
      hdrift' (Or.inl hG')
    change normLGFLaw d {g | ENNReal.ofReal δ <
      supDistLU d R (gridProfile d (posNode lo hi (j + 1) m) g)
        (gridProfile d (posNode lo hi j (posBracket j m)) g)} ≤ ENNReal.ofReal b at h
    exact h
  have hupp (m : ℕ) (hm : m ≤ 2 ^ posLevel (j + 1))
      (hbr : posBracket j m < 2 ^ posLevel j) :
      normLGFLaw d {g | ENNReal.ofReal δ <
        supDistLU d R (gridProfile d (posNode lo hi (j + 1) m) g)
          (gridProfile d (posNode lo hi j (posBracket j m + 1)) g)} ≤ ENNReal.ofReal b := by
    have hfine := posNode_mem hlohi hm
    have hcoarse := posNode_upper_mem hlohi hbr
    have hsf := strongAt_spec hd (posNode_subcrit hd hlo hlohi hhi hm)
    have hsc := strongAt_spec hd
      (posNode_subcrit hd hlo hlohi hhi (Nat.succ_le_iff.2 hbr))
    have hclose := abs_posNode_sub_upper_le hlohi j m
    have hdrift' : |posNode lo hi (j + 1) m - posNode lo hi j (posBracket j m + 1)| * n ≤ c * δ :=
      (mul_le_mul_of_nonneg_right hclose hn).trans_eq hdrift
    have hG' : |posNode lo hi (j + 1) m - posNode lo hi j (posBracket j m + 1)| ≤
        Real.exp (-(C * lo ^ (-B) * δ ^ (-B))) := hclose.trans hG
    have h := hcmp lo ⟨hlo, hlohi.le⟩ _ hfine _ hcoarse _ _ hsf hsc δ hδ hδ8 n hdepth
      hdrift' (Or.inl hG')
    change normLGFLaw d {g | ENNReal.ofReal δ <
      supDistLU d R (gridProfile d (posNode lo hi (j + 1) m) g)
        (gridProfile d (posNode lo hi j (posBracket j m + 1)) g)} ≤ ENNReal.ofReal b at h
    exact h
  have hupper_event (m : ℕ) (hm : m ≤ 2 ^ posLevel (j + 1)) :
      normLGFLaw d (if posBracket j m < 2 ^ posLevel j then
        {g | ENNReal.ofReal δ <
          supDistLU d R (gridProfile d (posNode lo hi (j + 1) m) g)
            (gridProfile d (posNode lo hi j (posBracket j m + 1)) g)} else ∅) ≤ ENNReal.ofReal b := by
    split_ifs with hbr
    · exact hupp m hm hbr
    · simp only [measure_empty, zero_le]
  have hL := endpt_measure_biUnion_range_le (normLGFLaw d) (2 ^ posLevel (j + 1))
    (fun m => {g | ENNReal.ofReal δ <
      supDistLU d R (gridProfile d (posNode lo hi (j + 1) m) g)
        (gridProfile d (posNode lo hi j (posBracket j m)) g)}) hlow
  have hU := endpt_measure_biUnion_range_le (normLGFLaw d) (2 ^ posLevel (j + 1))
    (fun m => if posBracket j m < 2 ^ posLevel j then
      {g | ENNReal.ofReal δ <
        supDistLU d R (gridProfile d (posNode lo hi (j + 1) m) g)
          (gridProfile d (posNode lo hi j (posBracket j m + 1)) g)} else ∅) hupper_event
  calc
    normLGFLaw d (posBad d lo hi R j) ≤
        normLGFLaw d (posLowerBad d lo hi R j) + normLGFLaw d (posUpperBad d lo hi R j) :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal ((2 ^ posLevel (j + 1) + 1) * b) +
        ENNReal.ofReal ((2 ^ posLevel (j + 1) + 1) * b) := by
      apply add_le_add
      · simpa only [posLowerBad, δ, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] using hL
      · simpa only [posUpperBad, δ, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] using hU
    _ = _ := rfl

end HigherDimLQGContinuity
