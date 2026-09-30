import QuantumZipper.Proofs.Zipper.FieldLawler2Circ

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL4-WD (polar): thin polar sectors along a circular arc

Task FL4-WD (Track A round 4). Elementary point-set topology near an arc
`flCircArc ε α β = {ε e^{iθ} : α < θ < β}`: thin polar sectors on either side of the arc lie in
any open set containing the arc, they are connected, and every point near `ε e^{iθ₀}` has polar
coordinates near `(ε, θ₀)`. Own elementary argument (the facts are used implicitly in
Field–Lawler, *Escape probability and transience for SLE*, EJP 20 (2015), proof of Prop. 3.4,
p. 9, where the domain between `ηⱼ` and `C_R` is taken without comment).
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology

namespace QuantumZipper
namespace FieldLawler

/-- Polar parametrization `(r, φ) ↦ r e^{iφ}`. -/
def fl4Pol (r φ : ℝ) : ℂ := (r : ℂ) * exp (φ * I)

lemma fl4Pol_norm (r φ : ℝ) : ‖fl4Pol r φ‖ = |r| := by
  simp [fl4Pol, norm_exp_ofReal_mul_I]

lemma fl4Pol_dist (r s φ : ℝ) : dist (fl4Pol r φ) (fl4Pol s φ) = |r - s| := by
  rw [dist_eq_norm, fl4Pol, fl4Pol, ← sub_mul, norm_mul, norm_exp_ofReal_mul_I, mul_one,
    ← ofReal_sub, norm_real, Real.norm_eq_abs]

lemma fl4Pol_mem_arc {ε α β φ : ℝ} (hφ : φ ∈ Ioo α β) : fl4Pol ε φ ∈ flCircArc ε α β :=
  ⟨φ, hφ, rfl⟩

lemma fl4_closure_arc_subset {ε α β : ℝ} : closure (flCircArc ε α β) ⊆ sphere 0 |ε| := by
  refine closure_minimal ?_ isClosed_sphere
  rintro _ ⟨φ, -, rfl⟩
  simp

end FieldLawler
end QuantumZipper
