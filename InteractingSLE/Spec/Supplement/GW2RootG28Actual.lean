/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootG28Buffer
import InteractingSLE.Spec.Supplement.GW2FbConfig

/-!
# Recorded geometric buffers are safe for the original finite flow trace

Packet PROVE-T14-GW2ROOT2. The recording cutoff only needs to be alive;
it need not precede contact. The constructed smaller buffer is proved
strictly before both contact and the original lifetime. FABLE's prefix
contact lemma transfers the frozen-record assertion back to the source.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2TipSystem.RootG28

open Exist Staged StagedLaw Restart Supp8.GB6

variable {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (s : ℝ≥0) (ω : Ω)
  (hW : Continuous (W · ω)) (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤)
  {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) ⊤ α)
  {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e)
  {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace e.1 e.2 γ)
  {v : ℝ≥0} (hv : (v : ℝ≥0∞) < e.2)

include hW hW0 hζ hα he hγ hv

/-- The record's contact is the source contact with only the moving
physical curve frozen at the available recording cutoff. -/
theorem recordContact_eq_source :
    recordContact s v (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) =
      firstContactTime (fun t => sphereInv (γ (min t v) : OnePoint ℂ))
        ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) := by
  rw [recordContact, frozenTraceRead_recOf_eq he hγ hv,
    frozenTraceRead_cfRec_eq W ζ s ω hW hW0 hζ hα]
  exact SourceC.firstContactTime_eq_of_prefix_eq (fun u hu => by rw [min_eq_left hu])

/-- Before the recording cutoff, strict pre-contact events agree with
the original trace even if contact happens before that cutoff. -/
theorem lt_recordContact_iff {t : ℝ≥0} (htv : t < v) :
    (t : ℝ≥0∞) < recordContact s v (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) ↔
      (t : ℝ≥0∞) < firstContactTime (fun u => sphereInv (γ u : OnePoint ℂ))
        ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) := by
  rw [recordContact_eq_source W ζ s ω hW hW0 hζ hα he hγ hv]
  constructor
  · exact fun ht => GW2Fb.lt_firstContactTime_of_prefix htv
      (fun u hu => by rw [min_eq_left hu]) ht
  · exact fun ht => GW2Fb.lt_firstContactTime_of_prefix htv
      (fun u hu => by rw [min_eq_left hu]) ht

/-- The constructed buffer is positive and strictly before the actual
contact and lifetime. No pre-contact recording cutoff is assumed. -/
theorem contactBuffer_before_contact (hs : 0 < s) {b : ℝ≥0}
    (hb : 0 < b) (hbv : b < v) (m : ℕ) :
    let p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
    0 < contactBuffer s v b m p ∧ (contactBuffer s v b m p : ℝ≥0∞) < min
      (firstContactTime (fun u => sphereInv (γ u : OnePoint ℂ))
        ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)) e.2 := by
  have h0 : frozenTraceRead v (recOf (v : ℝ≥0∞) e) 0 = 0 := by
    rw [frozenTraceRead_recOf_eq he hγ hv]
    simp only [zero_min, hγ.1]
  have hbuf := contactBuffer_spec s v b m
    (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) hs hb h0
  have hFv := (contactBuffer_le s v b m
    (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)).trans_lt hbv
  exact ⟨hbuf.1, lt_min
    ((lt_recordContact_iff W ζ s ω hW hW0 hζ hα he hγ hv hFv).mp hbuf.2)
    ((ENNReal.coe_lt_coe.mpr hFv).trans hv)⟩

/-- The original dense candidate family supplies finite caps for buffers
beyond every strictly pre-contact query below the recording cutoff. -/
theorem exists_source_contactBuffer {Q : Set ℝ≥0} (hQ : Dense Q) {t : ℝ≥0}
    (htv : t < v)
    (ht : (t : ℝ≥0∞) < firstContactTime (fun u => sphereInv (γ u : OnePoint ℂ))
      ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)) :
    ∃ b : Q, 0 < (b : ℝ≥0) ∧ (b : ℝ≥0) < v ∧ ∃ m : ℕ,
      t < contactBuffer s v b m (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) := by
  obtain ⟨b, hb, hbQ⟩ := hQ.inter_open_nonempty (Ioo t v) isOpen_Ioo
    (nonempty_Ioo.mpr htv)
  obtain ⟨m, hm⟩ := exists_lt_contactBuffer s v b t
    (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) hb.1
    ((lt_recordContact_iff W ζ s ω hW hW0 hζ hα he hγ hv htv).mpr ht)
  exact ⟨⟨b, hbQ⟩, (zero_le : (0 : ℝ≥0) ≤ t).trans_lt hb.1, hb.2, m, hm⟩

end InteractingSLE.Theorem14.GW2TipSystem.RootG28
