/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR4Records
import InteractingSLE.Spec.Supplement.GW2JDetR3Prefix

/-!
# Selecting the inverse-record buffer from a killed relative path

Choose the first rational prefix whose physical capacity exceeds the requested
time and which lies before the relative lifetime. All selection data are Borel.
The resulting inverse reads only the relative driver strictly before its life.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2JDetR4

open Exist.StagedLaw GW2JDetR3

/-- A literal live rational prefix is the actual source relative record. -/
theorem prefixRecord_eq_cfRec {e : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hc : ContinuousOn e.1 {t | (t : ℝ≥0∞) < e.2}) (h0 : e.1 0 = 0)
    {q : ℚ≥0} (hq : ((q : ℝ≥0) : ℝ≥0∞) < e.2) :
    prefixRecord q (killedCode e) =
      GW2TipSystem.cfRec q (fun u (_ : Unit) => e.1 u) (fun _ => e.2) () := by
  rw [← cfRec_eq_live_samples (q : ℝ≥0) hc h0 hq]
  apply Prod.ext
  · funext r
    have hcast : ((min r.toNNRat q : ℚ≥0) : ℝ≥0) =
        min (r : ℝ).toNNReal (q : ℝ≥0) := by
      rw [NNRat.cast_min, coe_toNNRat_eq]
    have hlt : (((min r.toNNRat q : ℚ≥0) : ℝ≥0) : ℝ≥0∞) < e.2 :=
      (ENNReal.coe_le_coe.mpr (by exact_mod_cast min_le_right r.toNNRat q)).trans_lt hq
    change killedCode e (min r.toNNRat q) = _
    unfold killedCode
    rw [ite_eq_left hlt, hcast]
  · rfl

private def bufferRat (n : ℕ) : ℚ≥0 := (Encodable.decode (α := ℚ≥0) n).getD 0

private theorem bufferRat_encode (q : ℚ≥0) : bufferRat (Encodable.encode q) = q := by
  simp only [bufferRat, Encodable.encodek, Option.getD_some]

/-- The selection only sees a record, rational samples, and a relative lifetime. -/
abbrev BufferInput := RecData × ((ℚ≥0 → ℝ) × ℝ≥0∞)

/-- A strictly later live rational physical-capacity buffer. -/
def IsBuffer (s t : ℝ≥0) (x : BufferInput) (q : ℚ≥0) : Prop :=
  ((q : ℝ≥0) : ℝ≥0∞) < x.2.2 ∧ (t : ℝ≥0∞) < prefixCapacity s q x.1 x.2.1

theorem measurableSet_isBuffer (s t : ℝ≥0) (q : ℚ≥0) :
    MeasurableSet {x : BufferInput | IsBuffer s t x q} :=
  (measurableSet_lt measurable_const (measurable_snd.comp measurable_snd)).inter
    (measurableSet_lt measurable_const ((measurable_prefixCapacity s q).comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))))

private theorem exists_bufferIndex (s t : ℝ≥0) (x : BufferInput) :
    ∃ n : ℕ, IsBuffer s t x (bufferRat n) ∨ ¬ ∃ q, IsBuffer s t x q := by
  classical
  by_cases h : ∃ q, IsBuffer s t x q
  · obtain ⟨q, hq⟩ := h
    exact ⟨Encodable.encode q, Or.inl (by rwa [bufferRat_encode])⟩
  · exact ⟨0, Or.inr h⟩

open scoped Classical in
private def bufferIndex (s t : ℝ≥0) (x : BufferInput) : ℕ :=
  Nat.find (exists_bufferIndex s t x)

private theorem measurable_bufferIndex (s t : ℝ≥0) : Measurable (bufferIndex s t) := by
  classical
  apply measurable_find
  intro n
  have he : MeasurableSet {x : BufferInput | ∃ q, IsBuffer s t x q} := by
    simpa only [ofPred_exists] using
      (MeasurableSet.iUnion fun q => measurableSet_isBuffer s t q)
  exact (measurableSet_isBuffer s t (bufferRat n)).union
    he.compl

/-- The rational horizon selected by the killed-path data. -/
def bufferTime (s t : ℝ≥0) (x : BufferInput) : ℚ≥0 := bufferRat (bufferIndex s t x)

theorem isBuffer_bufferTime (s t : ℝ≥0) (x : BufferInput)
    (hx : ∃ q, IsBuffer s t x q) : IsBuffer s t x (bufferTime s t x) := by
  classical
  exact (Nat.find_spec (exists_bufferIndex s t x)).resolve_right (not_not.mpr hx)

/-- The selected live relative record. A default is also defined if none exists. -/
def bufferRecord (s t : ℝ≥0) (x : BufferInput) : RecData :=
  prefixRecord (bufferTime s t x) x.2.1

theorem measurable_bufferRecord (s t : ℝ≥0) : Measurable (bufferRecord s t) := by
  let F : BufferInput × ℕ → RecData := fun p => prefixRecord (bufferRat p.2) p.1.2.1
  let G : BufferInput → BufferInput × ℕ := fun x => (x, bufferIndex s t x)
  change Measurable (F ∘ G)
  have hf : Measurable F :=
    measurable_from_prod_countable_left fun n =>
      (measurable_prefixRecord (bufferRat n)).comp (measurable_fst.comp measurable_snd)
  have hg : Measurable G := measurable_id.prodMk (measurable_bufferIndex s t)
  exact hf.comp hg

/-- A total Borel inverse from a counterflow record and a killed relative path. -/
def inverseRecord (s t : ℝ≥0) (p : RecData × ((ℝ≥0 → ℝ) × ℝ≥0∞)) : RecData :=
  physicalRecordRead s t (p.1, bufferRecord s t (p.1, killedCode p.2, p.2.2))

theorem measurable_inverseRecord (s t : ℝ≥0) : Measurable (inverseRecord s t) := by
  exact (measurable_physicalRecordRead s t).comp (measurable_fst.prodMk
    ((measurable_bufferRecord s t).comp (measurable_fst.prodMk
      ((measurable_killedCode.comp measurable_snd).prodMk
        (measurable_snd.comp measurable_snd)))))

/-- The exact invariance premise of the landed record-determination argument is
proved outright for the concrete inverse, on arbitrary input paths. -/
theorem inverseRecord_congr (s t : ℝ≥0) (r : RecData) (U V : ℝ≥0 → ℝ) (e : ℝ≥0∞)
    (h : ∀ q : ℝ≥0, (q : ℝ≥0∞) < e → U q = V q) :
    inverseRecord s t (r, (U, e)) = inverseRecord s t (r, (V, e)) := by
  have he : killedCode (U, e) = killedCode (V, e) := by
    funext q
    unfold killedCode
    split_ifs with hq
    · exact h q hq
    · rfl
  unfold inverseRecord
  rw [he]

end InteractingSLE.Theorem14.GW2JDetR4
