import HigherDimLQGContinuity.MomentsW1.BadScaleGeometry
import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGMetric.DGZ.Sec41Prob

/-! # The finite-region fine-field statuses and last bad scale -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt closedSite SiteClosed)
open HigherDimLQGMetric.DGZ

/-- The scale-`k` sites whose physical points lie strictly inside the coarse box. -/
def wnRegion {d : ℕ} (R : ℝ) (k : ℕ) : Set (Zd d) :=
  {x | ∀ i, |latPt ((2 : ℝ)⁻¹ ^ k) x i| < R + 3}

/-- A bad fine-field site in the enlarged observation box. The field is `h_n-h_k`. -/
def wnClosed {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (H : ℕ → Rd d → Ω → ℝ)
    (ξ R : ℝ) (q : ℝ≥0∞) (k n : ℕ) (x : Zd d) : Set Ω :=
  {ω | x ∈ wnRegion R k ∧ ω ∈ closedSite ξ
    (fun z ω => H n z ω - H k z ω) ((2 : ℝ)⁻¹ ^ k)
    (aQ P H ξ (n - k) q) (R + 3) x}

/-- The complement of the fine-field bad-site configuration. -/
def wnGood {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (H : ℕ → Rd d → Ω → ℝ)
    (ξ R : ℝ) (q : ℝ≥0∞) (k n : ℕ) (ω : Ω) : Set (Zd d) :=
  {x | ω ∉ wnClosed P H ξ R q k n x}

/-- A rough coarse site fails the coarse good test or a neighboring fine good test. -/
def wnRough {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (H : ℕ → Rd d → Ω → ℝ)
    (ξ R : ℝ) (q : ℝ≥0∞) (k n : ℕ) (y : Zd d) : Set Ω :=
  {ω | y ∉ wnNice (wnGood P H ξ R q (k - 1) n ω)
    (wnGood P H ξ R q k n ω)}

/-- `D_k = (k²-101²)_+`. -/
def wnBadDiameter (k : ℕ) : ℕ := k ^ 2 - 101 ^ 2

/-- `D'_k = ⌊(k²-3)/2⌋`. -/
def wnRoughDiameter (k : ℕ) : ℕ := (k ^ 2 - 3) / 2

/-- The three fine-field failures at scale `k`. -/
def wnBadAt {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (H : ℕ → Rd d → Ω → ℝ)
    (ξ R : ℝ) (q : ℝ≥0∞) (k n : ℕ) : Set Ω :=
  {ω | ¬ SmallClusters (wnGood P H ξ R q k n ω) (wnBadDiameter k) ∨
    ¬ SmallClusters (wnGood P H ξ R q (k - 1) n ω) (wnBadDiameter (k - 1)) ∨
    ¬ SmallClusters (wnNice (wnGood P H ξ R q (k - 1) n ω)
      (wnGood P H ξ R q k n ω)) (wnRoughDiameter k)}

/-- One plus the last bad scale below `n`, with a floor of `110`. -/
def wnBadScale {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (H : ℕ → Rd d → Ω → ℝ)
    (ξ R : ℝ) (q : ℝ≥0∞) (n : ℕ) (ω : Ω) : ℕ := by
  classical
  exact max 110 ((Finset.Ico 110 n).sup fun k => if ω ∈ wnBadAt P H ξ R q k n then k + 1 else 0)

/-- Above the last bad scale, all three small-cluster conditions hold. -/
theorem wnBadScale_small {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {H : ℕ → Rd d → Ω → ℝ}
    {ξ R : ℝ} {q : ℝ≥0∞} {n k : ℕ} {ω : Ω}
    (h110 : 110 ≤ k) (hkn : k < n) (hMk : wnBadScale P H ξ R q n ω ≤ k) :
    SmallClusters (wnGood P H ξ R q k n ω) (wnBadDiameter k) ∧
    SmallClusters (wnGood P H ξ R q (k - 1) n ω) (wnBadDiameter (k - 1)) ∧
    SmallClusters (wnNice (wnGood P H ξ R q (k - 1) n ω)
      (wnGood P H ξ R q k n ω)) (wnRoughDiameter k) := by
  have hnot : ω ∉ wnBadAt P H ξ R q k n := by
    intro hbad
    have hmem : k ∈ Finset.Ico 110 n := Finset.mem_Ico.mpr ⟨h110, hkn⟩
    have hle : k + 1 ≤ wnBadScale P H ξ R q n ω := by
      dsimp [wnBadScale]
      classical
      have hle' := Finset.le_sup (s := Finset.Ico 110 n)
        (f := fun j => if ω ∈ wnBadAt P H ξ R q j n then j + 1 else 0) hmem
      have hval : (if ω ∈ wnBadAt P H ξ R q k n then k + 1 else 0) = k + 1 := by
        simp [hbad]
      exact (hval ▸ hle').trans (le_max_right _ _)
    omega
  simp only [wnBadAt, Set.mem_ofPred_eq, not_or, not_not] at hnot
  exact ⟨hnot.1, hnot.2.1, hnot.2.2⟩

end HigherDimLQGContinuity
