import QuantumZipper.Proofs.Zipper.Thm13AssemblyStmt

/-!
# E5-MAIN, part 1: two-sided TV-nearness of functionals, and E5 in that language

Blueprint `blueprint/E_BRANCH_BLUEPRINT.md` §4, node **E5**. `E5.E5Stmt loc` is a two-sided
`ℝ≥0∞` statement "for every `R` and `η > 0`, eventually in `C`, uniformly over measurable tests
`Γ ∈ [0,1]`". We package this as a relation `TVNear A B` between two families of functionals
`A C, B C : (E → ℝ≥0∞) → ℝ≥0∞` and prove its algebra (reflexive, symmetric, transitive, stable
under multiplication by a finite constant, approximation), so that E5 becomes a chain of
TV-near steps (E5 steps (1)–(5)).

* `TVNear`, `TVNear.refl`, `TVNear.symm`, `TVNear.trans`, `TVNear.const_mul`,
  `TVNear.of_approx`, `TVNear.of_seq`.
* `lhsF`, `rhsF`, `pmass`: the two sides of `E5Stmt`; `e5Stmt_of_tvNear`: `E5Stmt loc` follows
  from `TVNear (lhsF …) (rhsF …)` for every setup, `δ > 0` and `R`.

Own elementary bookkeeping (no source needed: triangle inequality in `ℝ≥0∞`).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5
open B2 E1 CoordsFull

/-- **Two-sided TV-nearness** of two families of functionals on tests `E → ℝ≥0∞`: for every
`η > 0`, eventually in `C`, for all measurable `Γ ≤ 1`, `A C Γ ≤ B C Γ + η` and
`B C Γ ≤ A C Γ + η`. -/
def TVNear {E : Type*} [MeasurableSpace E] (A B : ℝ → (E → ℝ≥0∞) → ℝ≥0∞) : Prop :=
  ∀ η : ℝ≥0∞, 0 < η → ∀ᶠ C in atTop, ∀ Γ : E → ℝ≥0∞, Measurable Γ → (∀ y, Γ y ≤ 1) →
    A C Γ ≤ B C Γ + η ∧ B C Γ ≤ A C Γ + η

namespace TVNear

variable {E : Type*} [MeasurableSpace E] {A B D : ℝ → (E → ℝ≥0∞) → ℝ≥0∞}

theorem refl (A : ℝ → (E → ℝ≥0∞) → ℝ≥0∞) : TVNear A A := fun _ _ =>
  Eventually.of_forall fun _ _ _ _ => ⟨le_self_add, le_self_add⟩

theorem symm (h : TVNear A B) : TVNear B A := fun η hη =>
  (h η hη).mono fun _ hC Γ hΓ h1 => (hC Γ hΓ h1).symm

theorem trans (h1 : TVNear A B) (h2 : TVNear B D) : TVNear A D := by
  intro η hη
  have hη2 : 0 < η / 2 := ENNReal.half_pos hη.ne'
  filter_upwards [h1 _ hη2, h2 _ hη2] with C hC1 hC2 Γ hΓ hΓ1
  obtain ⟨a1, a2⟩ := hC1 Γ hΓ hΓ1
  obtain ⟨b1, b2⟩ := hC2 Γ hΓ hΓ1
  constructor
  · calc A C Γ ≤ B C Γ + η / 2 := a1
      _ ≤ D C Γ + η / 2 + η / 2 := by gcongr
      _ = D C Γ + η := by rw [add_assoc, ENNReal.add_halves]
  · calc D C Γ ≤ B C Γ + η / 2 := b2
      _ ≤ A C Γ + η / 2 + η / 2 := by gcongr
      _ = A C Γ + η := by rw [add_assoc, ENNReal.add_halves]

/-- Exact equality eventually gives TV-nearness. -/
theorem of_eventually_eq (h : ∀ᶠ C in atTop, ∀ Γ : E → ℝ≥0∞, Measurable Γ → (∀ y, Γ y ≤ 1) →
    A C Γ = B C Γ) : TVNear A B := fun _ _ =>
  h.mono fun _ hC Γ hΓ h1 => by rw [hC Γ hΓ h1]; exact ⟨le_self_add, le_self_add⟩

/-- Multiplying both families by a finite constant. -/
theorem const_mul (h : TVNear A B) {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    TVNear (fun C Γ => c * A C Γ) (fun C Γ => c * B C Γ) := by
  intro η hη
  rcases eq_or_ne c 0 with rfl | hc0
  · exact Eventually.of_forall fun _ _ _ _ => by simp
  have hη' : 0 < η / c := ENNReal.div_pos hη.ne' hc
  filter_upwards [h _ hη'] with C hC Γ hΓ h1
  obtain ⟨a1, a2⟩ := hC Γ hΓ h1
  have hcc : c * (η / c) = η := ENNReal.mul_div_cancel hc0 hc
  constructor
  · calc c * A C Γ ≤ c * (B C Γ + η / c) := by gcongr
      _ = c * B C Γ + η := by rw [mul_add, hcc]
  · calc c * B C Γ ≤ c * (A C Γ + η / c) := by gcongr
      _ = c * A C Γ + η := by rw [mul_add, hcc]

/-- Approximation: if for every `η > 0` some `A'` is TV-near `B` and eventually within `η` of `A`
(uniformly in `Γ`), then `A` is TV-near `B`. -/
theorem of_approx (h : ∀ η : ℝ≥0∞, 0 < η → ∃ A' : ℝ → (E → ℝ≥0∞) → ℝ≥0∞, TVNear A' B ∧
    ∀ᶠ C in atTop, ∀ Γ : E → ℝ≥0∞, Measurable Γ → (∀ y, Γ y ≤ 1) →
      A C Γ ≤ A' C Γ + η ∧ A' C Γ ≤ A C Γ + η) : TVNear A B := by
  intro η hη
  have hη2 : 0 < η / 2 := ENNReal.half_pos hη.ne'
  obtain ⟨A', hA'B, hAA'⟩ := h _ hη2
  filter_upwards [hAA', hA'B _ hη2] with C hC1 hC2 Γ hΓ h1
  obtain ⟨a1, a2⟩ := hC1 Γ hΓ h1
  obtain ⟨b1, b2⟩ := hC2 Γ hΓ h1
  constructor
  · calc A C Γ ≤ A' C Γ + η / 2 := a1
      _ ≤ B C Γ + η / 2 + η / 2 := by gcongr
      _ = B C Γ + η := by rw [add_assoc, ENNReal.add_halves]
  · calc B C Γ ≤ A' C Γ + η / 2 := b2
      _ ≤ A C Γ + η / 2 + η / 2 := by gcongr
      _ = A C Γ + η := by rw [add_assoc, ENNReal.add_halves]

/-- Sequential criterion: it suffices that along every sequence `C n → ∞` the bounds hold for
all large `n`. -/
theorem of_seq (h : ∀ η : ℝ≥0∞, 0 < η → ∀ Cs : ℕ → ℝ, Tendsto Cs atTop atTop →
    ∀ᶠ n in atTop, ∀ Γ : E → ℝ≥0∞, Measurable Γ → (∀ y, Γ y ≤ 1) →
      A (Cs n) Γ ≤ B (Cs n) Γ + η ∧ B (Cs n) Γ ≤ A (Cs n) Γ + η) : TVNear A B :=
  fun η hη => Filter.eventually_iff_seq_eventually.2 (h η hη)

end TVNear

/-! ## The two sides of `E5Stmt` -/

/-- The zoomed normalized collided configuration `Z_C C̄_x` of `E5Stmt`. -/
def zcfg (κ T : ℝ) {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ϖ : Measure ℂ)
    (C : ℝ) (ω : Ω) (x : ℝ) : FieldSample × (ℝ → ℝ) :=
  canonConfig (Real.sqrt κ) (addConst (collided κ T B X ω x).1
    (-(mReg κ T B X ϖ ω) + C / Real.sqrt κ), (collided κ T B X ω x).2)

/-- The left side of `E5Stmt` as a family of functionals of `Γ`. -/
def lhsF {L : Type*} (loc : ℕ → FieldSample × (ℝ → ℝ) → L) (κ T : ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ϖ : Measure ℂ) (δ : ℝ) (R : ℕ) :
    ℝ → (L → ℝ≥0∞) → ℝ≥0∞ := fun C Γ =>
  ∫⁻ ω, ∫⁻ x in Icc (-δ) 0,
    {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T}.indicator
      (fun x => Γ (loc R (zcfg κ T B X ϖ C ω x))) x ∂nuPalm κ T B X ϖ ω ∂P

/-- The Palm mass `p` of `E5Stmt`. -/
def pmass (κ T : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ϖ : Measure ℂ) (δ : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, nuPalm κ T B X ϖ ω
    {x | x ∈ Icc (-δ) 0 ∧ realHitTime (Vr κ T B ω) x < ENNReal.ofReal T} ∂P

/-- The right side of `E5Stmt` (constant in `C`). -/
def rhsF {L : Type*} (loc : ℕ → FieldSample × (ℝ → ℝ) → L) (κ : ℝ) (pm : ℝ≥0∞) {Ω' : Type*}
    [MeasurableSpace Ω'] (P' : Measure Ω') (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ) (R : ℕ) :
    ℝ → (L → ℝ≥0∞) → ℝ≥0∞ := fun _ Γ =>
  pm * ∫⁻ ω', Γ (loc R (Y ω', drive κ B' ω')) ∂P'

end E5
end QuantumZipper
