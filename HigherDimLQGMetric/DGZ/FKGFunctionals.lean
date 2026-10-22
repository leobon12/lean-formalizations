import HigherDimLQGMetric.DGZ.FKG
import HigherDimLQGMetric.DGZ.Crossing

/-!
# The LFPP functionals satisfy the hypotheses of the FKG inequality (packet L3b3, MA7 D-FKG)

Source: planning audit `planning/audits/MA7-ref2-sections-4-6.md`, Details (a) D-FKG ("applies to
`lfppDistOn` on bounded open sets and to set distances (nondecreasing in the field for `ξ ≥ 0`,
log-Lipschitz)") and D-6.5–D-6.7 (the uses in DGZ Lemmas 6.5–6.7).

For `ξ ≥ 0` the internal distance `D_V(x, y)`, the set distance `D(A, B; V)`, the across distance
of a shell and the self-internal diameter of a box are nondecreasing in the field
(`IsMonotoneFunctional`); for every `ξ` they are continuous for the sup norm on any set `K`
containing the region they see (`IsSupContinuousOn`), by the multiplicative comparisons
`F(φ) ≤ e^{|ξ| M} F(ψ)` for `|φ - ψ| ≤ M` (`IsSupContinuousOn.of_le_exp_mul`). No positivity or
joinability is needed: in the degenerate cases these functionals vanish identically.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP
open HigherDimLFPP.DGZ (cbox obox)

variable {d : ℕ}

/-! ### Internal distances -/

/-- `φ ↦ D_V(x, y)(φ)` is sup-continuous on every `K ⊇ V`. -/
theorem isSupContinuousOn_lfppDistOn {V K : Set (Rd d)} (hVK : V ⊆ K) (ξ : ℝ) (x y : Rd d) :
    IsSupContinuousOn K fun φ => lfppDistOn ξ φ V x y :=
  IsSupContinuousOn.of_le_exp_mul (abs_nonneg ξ) (fun φ _ => lfppDistOn_nonneg ξ φ V x y)
    fun _ _ hφ hψ _ _ hM => lfppDistOn_le_exp_mul hφ hψ fun z hz => hM z (hVK hz)

/-- `φ ↦ D_V(x, y)(φ)` is nondecreasing for `ξ ≥ 0`. -/
theorem isMonotoneFunctional_lfppDistOn {ξ : ℝ} (hξ : 0 ≤ ξ) (V : Set (Rd d)) (x y : Rd d) :
    IsMonotoneFunctional fun φ => lfppDistOn ξ φ V x y :=
  fun _ _ hφ hψ hle => lfppDistOn_mono_field hξ hφ hψ fun z _ => hle z

/-- The frozen distance `D^ξ(φ) = D_{(-2,2)^d}(0, e₁)(φ)` is sup-continuous on every
`K ⊇ (-2,2)^d`. -/
theorem isSupContinuousOn_lfppDistance {K : Set (Rd d)} (hK : cube d ⊆ K) (ξ : ℝ) :
    IsSupContinuousOn K fun φ => lfppDistance d ξ φ := by
  simp only [lfppDistance_eq_lfppDistOn]
  exact isSupContinuousOn_lfppDistOn hK ξ 0 (e₁ d)

/-- The frozen distance `D^ξ` is nondecreasing for `ξ ≥ 0`. -/
theorem isMonotoneFunctional_lfppDistance {ξ : ℝ} (hξ : 0 ≤ ξ) :
    IsMonotoneFunctional fun φ : Rd d → ℝ => lfppDistance d ξ φ := by
  simp only [lfppDistance_eq_lfppDistOn]
  exact isMonotoneFunctional_lfppDistOn hξ (cube d) 0 (e₁ d)

/-! ### Set distances -/

/-- `φ ↦ D(A, B; V)(φ)` is sup-continuous on every `K ⊇ V`. -/
theorem isSupContinuousOn_lfppSetDist {V K : Set (Rd d)} (hVK : V ⊆ K) (ξ : ℝ)
    (A B : Set (Rd d)) : IsSupContinuousOn K fun φ => lfppSetDist ξ φ V A B :=
  IsSupContinuousOn.of_le_exp_mul (abs_nonneg ξ) (fun φ _ => lfppSetDist_nonneg ξ φ V A B)
    fun _ _ hφ hψ _ _ hM => lfppSetDist_le_exp_mul hφ hψ fun z hz => hM z (hVK hz)

/-- `φ ↦ D(A, B; V)(φ)` is nondecreasing for `ξ ≥ 0`. -/
theorem isMonotoneFunctional_lfppSetDist {ξ : ℝ} (hξ : 0 ≤ ξ) (V A B : Set (Rd d)) :
    IsMonotoneFunctional fun φ => lfppSetDist ξ φ V A B :=
  fun _ _ hφ hψ hle => lfppSetDist_mono_field hξ hφ hψ fun z _ => hle z

/-! ### Across distances of hypercubic shells -/

/-- `φ ↦ D(across B_{r₁}(c) \ B_{r₂}(c))(φ)` is sup-continuous on every `K ⊇ B̄_{r₁}(c)` (a
minimizing family of crossings stays in the closed shell). -/
theorem isSupContinuousOn_acrossDist {K : Set (Rd d)} {c : Rd d} {r₁ r₂ : ℝ} (hr : r₂ < r₁)
    (hK : cbox c r₁ ⊆ K) (ξ : ℝ) : IsSupContinuousOn K fun φ => acrossDist ξ φ c r₁ r₂ :=
  IsSupContinuousOn.of_le_exp_mul (abs_nonneg ξ) (fun φ _ => acrossDist_nonneg ξ φ c r₁ r₂)
    fun _ _ hφ hψ _ _ hM => acrossDist_le_exp_mul hφ hψ hr fun z hz => hM z (hK hz.1)

/-- `φ ↦ D(across B_{r₁}(c) \ B_{r₂}(c))(φ)` is nondecreasing for `ξ ≥ 0`. -/
theorem isMonotoneFunctional_acrossDist {ξ : ℝ} (hξ : 0 ≤ ξ) (c : Rd d) {r₁ r₂ : ℝ}
    (hr : r₂ < r₁) : IsMonotoneFunctional fun φ => acrossDist ξ φ c r₁ r₂ :=
  fun _ _ hφ hψ hle => acrossDist_mono_field hξ hφ hψ hr fun z _ => hle z

/-! ### Self-internal diameters -/

/-- `φ ↦ selfDiam(B_r(c))(φ)` is sup-continuous on every `K ⊇ B_r(c)`. -/
theorem isSupContinuousOn_selfDiam {K : Set (Rd d)} {c : Rd d} {r : ℝ} (hK : obox c r ⊆ K)
    (ξ : ℝ) : IsSupContinuousOn K fun φ => selfDiam ξ φ c r :=
  IsSupContinuousOn.of_le_exp_mul (abs_nonneg ξ) (fun φ _ => selfDiam_nonneg ξ φ c r)
    fun _ _ hφ hψ _ _ hM => selfDiam_le_exp_mul hφ hψ fun z hz => hM z (hK hz)

/-- `φ ↦ selfDiam(B_r(c))(φ)` is nondecreasing for `ξ ≥ 0`. -/
theorem isMonotoneFunctional_selfDiam {ξ : ℝ} (hξ : 0 ≤ ξ) (c : Rd d) (r : ℝ) :
    IsMonotoneFunctional fun φ => selfDiam ξ φ c r :=
  fun _ _ hφ hψ hle => selfDiam_mono_field hξ hφ hψ fun z _ => hle z

end HigherDimLQGMetric.DGZ
