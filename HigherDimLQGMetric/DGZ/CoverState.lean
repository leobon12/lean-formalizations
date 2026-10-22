import HigherDimLQGMetric.DGZ.CoverControl

/-!
# Downward cover induction for DGZ Proposition 5.10

The state records the centres already selected at levels `lo,…,m-1`, their bypass control, and
the induction assertion that every box at levels `lo,…,m` outside the current union is nice.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric.DGZ

open Set HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt cbox obox)

variable {d : ℕ}

/-- The weights of Proposition 5.10. -/
def coverWeight (p : NiceParams) (j : ℕ) : ℝ :=
  Real.exp (-(p.K * √(p.a j : ℝ)))

theorem mem_coverU_iff {R : ℝ} {m : ℕ} {s : ℕ → ℝ} {X : ℕ → Set (Rd d)}
    {v : Rd d} : v ∈ coverU R m s X ↔
      ∃ j, 1 ≤ j ∧ j < m ∧ ∃ z ∈ X j, v ∈ obox z (R * s j) := by
  simp only [coverU, Set.mem_iUnion, Finset.mem_Ico]
  constructor
  · rintro ⟨j, ⟨hj1, hjm⟩, z, hz, hv⟩
    exact ⟨j, hj1, hjm, z, hz, hv⟩
  · rintro ⟨j, hj1, hjm, z, hz, hv⟩
    exact ⟨j, ⟨hj1, hjm⟩, z, hz, hv⟩

theorem coverU_mono {R : ℝ} {m : ℕ} {s : ℕ → ℝ}
    {X Y : ℕ → Set (Rd d)} (h : ∀ j, X j ⊆ Y j) :
    coverU R m s X ⊆ coverU R m s Y := by
  intro v hv
  obtain ⟨j, hj1, hjm, z, hz, hvz⟩ := mem_coverU_iff.mp hv
  exact mem_coverU_iff.mpr ⟨j, hj1, hjm, z, h j hz, hvz⟩

/-- Change exactly one level of a family of sets. -/
def coverInsert (X : ℕ → Set (Rd d)) (j : ℕ) (Z : Set (Rd d)) (q : ℕ) : Set (Rd d) :=
  if q = j then Z else X q

theorem coverInsert_at (X : ℕ → Set (Rd d)) (j : ℕ) (Z : Set (Rd d)) :
    coverInsert X j Z j = Z := by simp [coverInsert]

theorem coverInsert_ne (X : ℕ → Set (Rd d)) {j q : ℕ} (h : q ≠ j) (Z : Set (Rd d)) :
    coverInsert X j Z q = X q := by simp [coverInsert, h]

theorem coverU_subset_coverInsert {R : ℝ} {m : ℕ} {s : ℕ → ℝ}
    (X : ℕ → Set (Rd d)) {j : ℕ} (hX : X j = ∅) (Z : Set (Rd d)) :
    coverU R m s X ⊆ coverU R m s (coverInsert X j Z) := by
  apply coverU_mono
  intro q v hv
  by_cases hq : q = j
  · subst q
    rw [hX] at hv
    simp at hv
  · simpa only [coverInsert_ne X hq Z] using hv

/-- The downward induction invariant. -/
structure CoverState (p : NiceParams) (H : ℕ → Rd d → ℝ) (m lo : ℕ) : Type where
  X : ℕ → Set (Rd d)
  emptyBelow : ∀ j, j < lo → X j = ∅
  emptyAbove : ∀ j, m ≤ j → X j = ∅
  finite : ∀ j, (X j).Finite
  sub : ∀ j, X j ⊆ obox (0 : Rd d) 2
  lattice : ∀ j, ∀ z ∈ X j, ∃ u : Zd d, z = latPt (p.s j) u
  sep : ∀ j, ∀ z ∈ X j, ∀ z' ∈ X j, z ≠ z' →
    z' ∉ cbox z (p.s (j + 1) / 4)
  ctrl : ∀ j, 1 ≤ j → j < m → ∀ z ∈ X j,
    ∃ x ∈ cbox z (p.s (j + 1)), ∃ t : ℝ,
      AroundGood p.ξ (H p.n) z (4 * p.R * p.s j) (2 * p.R * p.s j)
        (obox (0 : Rd d) 2) t ∧
      t < coverWeight p j *
        acrossDist p.ξ (H p.n) x (4 * p.s (j + 1)) (2 * p.s (j + 1))
  niceOutside : ∀ l, lo ≤ l → l ≤ m → ∀ u : Zd d,
    obox (latPt (p.s l) u) (p.s l) ⊆ obox (0 : Rd d) 2 →
    ¬ obox (latPt (p.s l) u) (p.s l) ⊆
      coverU (p.R : ℝ) m p.s X → NiceBox p H l u

/-- The top state is supplied by `𝒥₁`. -/
def coverState_top (p : NiceParams) (H : ℕ → Rd d → ℝ) (m : ℕ)
    (hJ : EventJ1 p H m) : CoverState p H m m := by
  refine ⟨fun _ => ∅, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j _; rfl
  · intro j _; rfl
  · intro j; exact Set.finite_empty
  · intro j z hz; simp at hz
  · intro j z hz; simp at hz
  · intro j z hz; simp at hz
  · intro j _ _ z hz; simp at hz
  · intro l hlo hlm u hu _
    have : l = m := by omega
    subst l
    exact hJ u hu

end HigherDimLQGMetric.DGZ
