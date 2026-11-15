/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootC11Schedule

/-!
# GW2's actual normalized capacity clock from prefix geometry

Packet PROVE-T14-GW2ROOT2. The hypothesis identifies the actual prefix
fillings and the generating trace in the scaled relative chart. The
desired `capR` increment is proved from it, using the old running-maximum
collapse and only the lower bound on the extended running maximum.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Complex
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootC11

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
  (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (b : ℝ → ℝ)
  (jumps : Finset ℝ) (c₀ : BoundaryWord) {Ω : Type u}
  (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ)
  (s : ℝ≥0) (Θ : Set ℝ) (Q : Set ℝ≥0) (ζ' : Ω → ℝ≥0∞)

/-- The physical clock inequality for the repaired `capR`. The geometric
extension and the generating trace, rather than a capacity increment, are inputs.
No attachment hypothesis on the intermediate prefixes of the extension is needed. -/
theorem capR_add_clock_le (r : ScaledRootIdx Θ Q) (l : List (EntryIdx Θ Q))
    (e : EntryIdx Θ Q) (ω : Ω) {K P : Set ℂ} {g φ ψ : ℂ → ℂ}
    {x₀ : ℂ} {Γ : ℝ≥0 → ℂ} {t : ℝ≥0}
    (hadm : SchedAdm b jumps Θ Q (κ := κ) (rootPt r.1) (rootEntry r.1)
      (entryList (e :: l)))
    (hHist : HasAttachedHistory hκ h12p βA b jumps c₀ h (regW s W' ζ') s
      (rootPt r.1) (rootEntry r.1) (entryList l) ω)
    (hGeom : IsCapacityExtension
      (rootImage hκ h12p βA b jumps c₀ h W' s Θ Q ζ' r l ω)
      (rootImage hκ h12p βA b jumps c₀ h W' s Θ Q ζ' r (e :: l) ω)
      K P g φ ψ x₀ Γ t)
    (hΓc : ContinuousOn Γ (Icc 0 t)) (hΓ0 : (Γ 0).im ≤ 0)
    {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {x : ℝ}
    (hgen : IsGeneratingTrace w T (fun q => (((2 : ℝ) ^ r.2 : ℝ) : ℂ) * Γ q - x))
    (hw : ContinuousOn w {q | (q : ℝ≥0∞) < T}) (hw0 : w 0 = 0)
    (ht : (t : ℝ≥0∞) < T) :
    capR hκ h12p βA b jumps c₀ h W' ζ' s r l ω + t ≤
      capR hκ h12p βA b jumps c₀ h W' ζ' s r (e :: l) ω := by
  have hscale : ((2 : ℝ) ^ r.2) ^ 2 = 4 ^ r.2 := by
    rw [pow_two, ← mul_pow]
    norm_num
  have hinc := hGeom.scaled_capOf_eq_add
    (rootImage_subset_cons hκ h12p βA b jumps c₀ h W' s Θ Q ζ' r l e ω)
    hΓc hΓ0 (pow_pos (by norm_num) r.2) hgen hw hw0 ht
  rw [hscale] at hinc
  have hadm' := hadm
  rw [entryList_cons] at hadm'
  have hbefore := capR_eq_scaled_capOf hκ h12p βA b jumps c₀ h W' s Θ Q ζ'
    r l ω (SchedAdm.of_cons b jumps Θ Q hadm') hHist
  have hafter := capV_le_schedCap hκ h12p βA b jumps c₀ h (regW s W' ζ') s Θ Q
    (rootPt r.1) (rootEntry r.1) (entryList (e :: l)) ω
  rw [capV, ite_eq_left hadm] at hafter
  calc
    capR hκ h12p βA b jumps c₀ h W' ζ' s r l ω + t =
        4 ^ r.2 * capOf (rootImage hκ h12p βA b jumps c₀ h W' s Θ Q ζ' r (e :: l) ω) := by
      rw [hbefore]
      exact hinc.symm
    _ ≤ capR hκ h12p βA b jumps c₀ h W' ζ' s r (e :: l) ω :=
      mul_le_mul_of_nonneg_left hafter (by positivity)

end InteractingSLE.Theorem14.GW2TipSystem.RootC11
