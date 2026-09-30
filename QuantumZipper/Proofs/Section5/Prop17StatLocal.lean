import QuantumZipper.Proofs.Section5.Prop17Stat
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Proposition 1.7, node D5-e: locality of the shift in determination form (PROP17-STAT)

`Prop17ShiftLocalStmt` asks for *measurable* local events. Here it is derived from the purely
deterministic statement `Prop17ShiftDetStmt γ L`: on `B n`, for good coordinate vectors, the
membership in `B n` and each coordinate of `shiftCoords γ L` are determined by the local
coordinates `locFull R` for some `R`. The measurable local event is produced by the Lusin
separation theorem (`MeasureTheory.AnalyticSet.measurablySeparable`; A. S. Kechris, *Classical
Descriptive Set Theory*, Thm. 14.7) applied to the images of the two sides under the continuous
map `locFull R` on the Polish space `ℕ → ℝ`.
-/

noncomputable section

open MeasureTheory Filter Set

namespace QuantumZipper
namespace S5
namespace FieldLaw
namespace Raw

open CoordsFull

theorem continuous_locFull (R : ℕ) : Continuous (locFull R) := by
  classical
  refine continuous_pi fun i => ?_
  unfold locFull
  split_ifs
  · exact continuous_apply i
  · exact continuous_const

theorem locFull_mono {R R' : ℕ} (hR : R ≤ R') {c c' : ℕ → ℝ}
    (h : locFull R' c = locFull R' c') : locFull R c = locFull R c' := by
  funext i
  have hi := congrFun h i
  unfold locFull at hi ⊢
  by_cases hin : inBallFull R i
  · have hin' : inBallFull R' i := by
      unfold inBallFull at hin ⊢
      exact hin.trans (by exact_mod_cast hR)
    simp only [hin, hin', ite_true] at hi ⊢
    exact hi
  · simp [hin]

/-- **Lusin separation for local determination.** A measurable set whose membership, among
vectors of a measurable set `Good`, is determined by `locFull R`, agrees on `Good` with a local
event. -/
theorem exists_locEvent_of_determined {Good S : Set (ℕ → ℝ)} (hG : MeasurableSet Good)
    (hS : MeasurableSet S) {R : ℕ}
    (hdet : ∀ c ∈ Good, ∀ c' ∈ Good, locFull R c = locFull R c' → (c ∈ S ↔ c' ∈ S)) :
    ∃ F ∈ locEvents, S ∩ Good = F ∩ Good := by
  have h1 : AnalyticSet (locFull R '' (S ∩ Good)) :=
    (hS.inter hG).analyticSet.image_of_continuous (continuous_locFull R)
  have h2 : AnalyticSet (locFull R '' (Sᶜ ∩ Good)) :=
    (hS.compl.inter hG).analyticSet.image_of_continuous (continuous_locFull R)
  have hdisj : Disjoint (locFull R '' (S ∩ Good)) (locFull R '' (Sᶜ ∩ Good)) := by
    rw [Set.disjoint_left]
    rintro v ⟨c, ⟨hcS, hcG⟩, rfl⟩ ⟨c', ⟨hc'S, hc'G⟩, hc'⟩
    exact hc'S ((hdet c hcG c' hc'G hc'.symm).1 hcS)
  obtain ⟨u, hsu, htu, hu⟩ := h1.measurablySeparable h2 hdisj
  refine ⟨locFull R ⁻¹' u, ⟨R, u, hu, rfl⟩, ?_⟩
  ext c
  simp only [mem_inter_iff, mem_preimage]
  constructor
  · rintro ⟨hc, hg⟩
    exact ⟨hsu ⟨c, ⟨hc, hg⟩, rfl⟩, hg⟩
  · rintro ⟨hc, hg⟩
    refine ⟨by_contra fun hn => ?_, hg⟩
    exact Set.disjoint_left.1 htu ⟨c, ⟨hn, hg⟩, rfl⟩ hc

end Raw
end FieldLaw
end S5
end QuantumZipper
