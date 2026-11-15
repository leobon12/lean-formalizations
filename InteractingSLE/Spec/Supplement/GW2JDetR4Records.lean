/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR4Actual

/-!
# Borel reconstruction of the actual live physical stopped record

The record includes every rational driver sample, the exact physical time and
the live flag. The identities are proved from the source generating traces.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2JDetR4

open Exist.Staged Exist.StagedLaw Supp8.GB6 GW2TipSystem GW2JDetR3 GW2JointKernel

/-- The complete live physical stopped record, read from two retained records. -/
def physicalRecordRead (s t : ℝ≥0) (p : RecData × RecData) : RecData :=
  (fun q : ℚ => physicalDriverRead s (min (q : ℝ).toNNReal t) p, (t : ℝ≥0∞), false)

theorem measurable_physicalRecordRead (s t : ℝ≥0) : Measurable (physicalRecordRead s t) := by
  unfold physicalRecordRead
  exact (measurable_pi_iff.mpr fun q : ℚ => measurable_physicalDriverRead s
    (min (q : ℝ).toNNReal t)).prodMk (measurable_const.prodMk measurable_const)

/-- The actual regularized record at a strictly live finite cutoff. -/
theorem cfRec_eq_live_samples (t : ℝ≥0)
    {w : ℝ≥0 → ℝ} {T : ℝ≥0∞}
    (hw : ContinuousOn w {u | (u : ℝ≥0∞) < T}) (hw0 : w 0 = 0)
    (ht : (t : ℝ≥0∞) < T) :
    (fun q : ℚ => w (min (q : ℝ).toNNReal t), (t : ℝ≥0∞), false) =
      cfRec t (fun u (_ : Unit) => w u) (fun _ => T) () := by
  have hmin : ∀ u : ℝ≥0, min (u : ℝ≥0∞) (t : ℝ≥0∞) = (min u t : ℝ≥0) :=
    fun u => (ENNReal.coe_min u t).symm
  apply Prod.ext
  · funext q
    change w (min (q : ℝ).toNNReal t) =
      (cfE t (fun u (_ : Unit) => w u) (fun _ => T) ()).1
        (min (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞)
          (min (t : ℝ≥0∞) (cfE t (fun u (_ : Unit) => w u) (fun _ => T) ()).2)).toNNReal
    rw [cfE_snd, min_eq_left ht.le, hmin, ENNReal.toNNReal_coe]
    exact (cfE_fst_of_lt (W := fun u (_ : Unit) => w u) (ζ := fun _ => T) (ω := ())
      t hw0 hw
      ((ENNReal.coe_le_coe.mpr (min_le_right _ _)).trans_lt ht)).symm
  · change ((t : ℝ≥0∞), false) =
      (min (t : ℝ≥0∞) (cfE t (fun u (_ : Unit) => w u) (fun _ => T) ()).2,
        decide ((cfE t (fun u (_ : Unit) => w u) (fun _ => T) ()).2 ≤ t))
    rw [cfE_snd, min_eq_left ht.le, decide_eq_false (not_le.mpr ht)]

/-- The physical record readout agrees with the regularized source record
whenever its reconstructed driver agrees through the strictly live cutoff. -/
theorem physicalRecordRead_eq_cfRec (s t : ℝ≥0) (p : RecData × RecData)
    {w : ℝ≥0 → ℝ} {T : ℝ≥0∞}
    (hw : ContinuousOn w {u | (u : ℝ≥0∞) < T}) (hw0 : w 0 = 0)
    (ht : (t : ℝ≥0∞) < T)
    (hread : ∀ u ≤ t, physicalDriverRead s u p = w u) :
    physicalRecordRead s t p = cfRec t (fun u (_ : Unit) => w u) (fun _ => T) () := by
  rw [← cfRec_eq_live_samples t hw hw0 ht]
  exact Prod.ext (funext fun q => hread _ (min_le_right _ _)) rfl

/-- The physical inverse-record theorem, with all inverse and capacity premises
discharged from the two original generating traces. -/
theorem exists_actual_physicalRecordRead {Ω : Type*}
    (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) (ζ ω) α)
    (hW : ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω}) (hW0 : W 0 ω = 0)
    {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ ω) (hsH : α s ∈ H)
    {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace w T γ)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < T}) (hw0 : w 0 = 0) (hT : 0 < T) :
    let r := cfRec s W ζ ω
    let S := min
      (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
        ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) T
    let a : ℝ≥0 → ℝ := fun t => relClock (rdrv r) s (Ito.rpath w) t
    let L := ⨆ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < S), ((a t).toNNReal : ℝ≥0∞)
    ∃ V : ℝ≥0 → ℝ, V 0 = 0 ∧ ContinuousOn V {q | (q : ℝ≥0∞) < L} ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < S →
        ∀ b : ℝ≥0, (a t).toNNReal < b → (b : ℝ≥0∞) < L →
          physicalRecordRead s t
            (r, cfRec b (fun u (_ : Unit) => V u) (fun _ => L) ()) =
              cfRec t (fun u (_ : Unit) => w u) (fun _ => T) () := by
  dsimp only
  obtain ⟨V, hV0, _, _, _, hVc, _, hread⟩ := exists_actual_physicalDriverRead
    W ζ ω hα hW hW0 hs hsH hγ hw hw0 hT
  refine ⟨V, hV0, hVc, ?_⟩
  intro t ht b htb hb
  exact physicalRecordRead_eq_cfRec s t _ hw hw0 (lt_min_iff.mp ht).2
    (hread t ht b htb hb).2

end InteractingSLE.Theorem14.GW2JDetR4
