import HigherDimLQGMetric.DGZ.Functionals

/-!
# The bypass lemma (DGZ Lemma 5.11): statement (packet L4b2)

Source: [2] = Ding–Gwynne–Zhuang, arXiv:2310.03996v5, Lemma 5.11 (TeX l. 2486–2598, pp. 48–50);
planning audit `planning/audits/MA7-ref2-sections-4-6.md`, §3 (gap G12), §5 row L4b2, Details (a)
D-5.11 and Details (c). The three definitions below are copied **verbatim** (names, binders, bodies
and docstrings) from the type-checked statement surface
`planning/audits/statements/MA7Statements.lean.txt` §E, with the namespace `MA7Scratch` replaced by
`HigherDimLQGMetric.DGZ`:
* `IsBypassCover ξ φ R m s w X` — the output of DGZ Prop 5.10 used by Lemma 5.11; it is kept
  abstract, so the bypass lemma is a deterministic statement about one continuous field `φ`;
* `coverU R m s X` — the covered region `𝒰`;
* `BypassShape d` — DGZ Lemma 5.11, deterministic.

The proof is in `HigherDimLQGMetric.DGZ.Bypass` (`bypass : ∀ d, 2 ≤ d → BypassShape d`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP
open HigherDimLFPP.DGZ (latPt cbox obox)

variable {d : ℕ}

/-- the output of DGZ Prop 5.10 used by Lemma 5.11 (MA7 D-5.10): sets `X j` of centres at levels
`1 ≤ j < m` with scales `s j`, separation `s (j+1) / 4`, and the around/across control of (5.25)
with the weights `w j` (`= exp(-K √a_j)`) -/
structure IsBypassCover (ξ : ℝ) (φ : Rd d → ℝ) (R : ℝ) (m : ℕ) (s w : ℕ → ℝ)
    (X : ℕ → Set (Rd d)) : Prop where
  finite : ∀ j, (X j).Finite
  sub : ∀ j, X j ⊆ obox 0 2
  sep : ∀ j, ∀ z ∈ X j, ∀ z' ∈ X j, z ≠ z' → ¬ (z' ∈ cbox z (s (j + 1) / 4))
  ctrl : ∀ j, 1 ≤ j → j < m → ∀ z ∈ X j, ∃ x ∈ cbox z (s (j + 1)), ∃ t : ℝ,
    AroundGood ξ φ z (4 * R * s j) (2 * R * s j) (obox 0 2) t ∧
    t < w j * acrossDist ξ φ x (4 * s (j + 1)) (2 * s (j + 1))

/-- the covered region `𝒰 = ⋃_{1 ≤ j < m} ⋃_{z ∈ X j} B_{R s_j}(z)` (DGZ (5.26)) -/
def coverU (R : ℝ) (m : ℕ) (s : ℕ → ℝ) (X : ℕ → Set (Rd d)) : Set (Rd d) :=
  ⋃ j ∈ Finset.Ico 1 m, ⋃ z ∈ X j, obox z (R * s j)

/-- **DGZ Lemma 5.11, deterministic** (MA7 D-5.11): bypassing `𝒰` costs at most a factor `2` -/
def BypassShape (d : ℕ) : Prop :=
  ∀ (ξ : ℝ) (φ : Rd d → ℝ), Continuous φ → ∀ (R : ℝ) (m : ℕ) (s w : ℕ → ℝ) (X : ℕ → Set (Rd d)),
    100 ≤ R → (∀ j, 0 < s j) → (∀ j, 40 * R * s j ≤ s (j + 1)) → (∀ j, 0 ≤ w j) →
    (∑ j ∈ Finset.Ico 1 m, 2 * (41 : ℝ) ^ d * w j) ≤ 1 / 2 → s m ≤ 1 / 100 →
    IsBypassCover ξ φ R m s w X →
    ∀ γ : ℝ → Rd d, IsPcwC1Path γ (γ 0) (γ 1) → MapsTo γ (Icc 0 1) (obox 0 2) →
      γ 1 ∉ cbox (γ 0) (10 * s m) →
      ∃ γ' : ℝ → Rd d, IsPcwC1Path γ' (γ' 0) (γ' 1) ∧
        MapsTo γ' (Icc 0 1) (obox 0 2 \ coverU R m s X) ∧
        γ' 0 ∈ cbox (γ 0) (10 * s m) ∧ γ' 1 ∈ cbox (γ 1) (10 * s m) ∧
        lfppLength ξ φ γ' ≤ 2 * lfppLengthIn ξ φ γ (obox 0 2 \ coverU R m s X)

end HigherDimLQGMetric.DGZ
