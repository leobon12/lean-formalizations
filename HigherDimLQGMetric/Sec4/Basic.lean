import HigherDimLQGMetric.B4.Interfaces
import HigherDimLQGMetric.Weak.DetLFPP
import HigherDimLQGMetric.DGZ.Crossing
import HigherDimLQGMetric.DGZ.Continuity

/-!
# Internal LFPP distances of a field in `[0, ∞]` (packet L9b)

The orchestrator-owned `lfppDistIn κ ξ ε h V x y` (B4 interface, MA6 Details (c)) is the infimum over piecewise
`C¹` paths in `V` of the extended LFPP length of the convolution field `h*_ε`. For the proofs of [1] §4.1 we need
the same quantity for other fields (the localized field `ĥ*_ε` of [1] (4.1)), so it is introduced here with the
field as an explicit argument (`fieldDistIn`), together with the bridges to HigherDimLFPP's real-valued
`lfppDistOn` (junk value `0` for non-joinable pairs; here the value is `⊤`), monotonicity in the domain, the
triangle inequality, the field comparison, and the diagonal patch used to feed the sphere-chain lemma.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd PcwJoined lfppDistOn lfppLength)

variable {d : ℕ}

/-- the internal LFPP distance of a field `φ` in `[0, ∞]`: infimum over piecewise `C¹` paths in `V` of the
extended LFPP length (`⊤` if `x, y` are not joined in `V`) -/
def fieldDistIn (ξ : ℝ) (φ : Rd d → ℝ) (V : Set (Rd d)) (x y : Rd d) : ℝ≥0∞ :=
  ⨅ P : {P : ℝ → Rd d // IsPiecewiseC1Path P x y ∧ MapsTo P (Icc 0 1) V}, lfppLen ξ φ P.1

/-- the set-to-set version -/
def fieldSetDistIn (ξ : ℝ) (φ : Rd d → ℝ) (V A B : Set (Rd d)) : ℝ≥0∞ :=
  ⨅ (x ∈ A) (y ∈ B), fieldDistIn ξ φ V x y

theorem lfppDistIn_eq_fieldDistIn (κ : Rd d → ℝ) (ξ ε : ℝ) (h : DistRd d) (V : Set (Rd d))
    (x y : Rd d) : lfppDistIn κ ξ ε h V x y = fieldDistIn ξ (convMollify κ ε h) V x y := rfl

theorem lfppSetDistIn_eq_fieldSetDistIn (κ : Rd d → ℝ) (ξ ε : ℝ) (h : DistRd d)
    (V A B : Set (Rd d)) :
    lfppSetDistIn κ ξ ε h V A B = fieldSetDistIn ξ (convMollify κ ε h) V A B := rfl

section Field

variable {ξ : ℝ} {φ ψ : Rd d → ℝ} {V W A B : Set (Rd d)} {x y z : Rd d}

theorem fieldDistIn_le_lfppLen {γ : ℝ → Rd d} (hγ : IsPiecewiseC1Path γ x y)
    (hV : MapsTo γ (Icc 0 1) V) : fieldDistIn ξ φ V x y ≤ lfppLen ξ φ γ :=
  iInf_le (fun P : {P : ℝ → Rd d // IsPiecewiseC1Path P x y ∧ MapsTo P (Icc 0 1) V} =>
    lfppLen ξ φ P.1) ⟨γ, hγ, hV⟩

theorem fieldDistIn_le_ofReal_lfppLength (hφ : Continuous φ) {γ : ℝ → Rd d}
    (hγ : IsPiecewiseC1Path γ x y) (hV : MapsTo γ (Icc 0 1) V) :
    fieldDistIn ξ φ V x y ≤ ENNReal.ofReal (lfppLength ξ φ γ) :=
  (fieldDistIn_le_lfppLen hγ hV).trans_eq (lfppLen_eq_ofReal hφ hγ)

/-- **Bridge** to HigherDimLFPP's real internal distance (continuous field, joined points). -/
theorem fieldDistIn_eq_ofReal (hφ : Continuous φ) (hj : PcwJoined V x y) :
    fieldDistIn ξ φ V x y = ENNReal.ofReal (lfppDistOn ξ φ V x y) := by
  have hne := hj.nonempty
  unfold fieldDistIn lfppDistOn
  calc
    (⨅ P : {P : ℝ → Rd d // IsPiecewiseC1Path P x y ∧ MapsTo P (Icc 0 1) V},
        lfppLen ξ φ P.1) =
        ⨅ P : {P : ℝ → Rd d // HigherDimLFPP.IsPcwC1Path P x y ∧ MapsTo P (Icc 0 1) V},
          ENNReal.ofReal (lfppLength ξ φ P.1) :=
      iInf_congr fun P => lfppLen_eq_ofReal hφ P.2.1
    _ = _ := (@ENNReal.ofReal_iInf _ hne _).symm

/-- Non-joined points are at distance `⊤`. -/
theorem fieldDistIn_eq_top (hj : ¬ PcwJoined V x y) : fieldDistIn ξ φ V x y = ⊤ := by
  have : IsEmpty {P : ℝ → Rd d // IsPiecewiseC1Path P x y ∧ MapsTo P (Icc 0 1) V} :=
    ⟨fun P => hj ⟨P.1, P.2.1, P.2.2⟩⟩
  exact iInf_of_empty _

theorem pcwJoined_of_fieldDistIn_ne_top (h : fieldDistIn ξ φ V x y ≠ ⊤) : PcwJoined V x y := by
  by_contra hj
  exact h (fieldDistIn_eq_top hj)

/-- **Monotonicity in the domain.** -/
theorem fieldDistIn_mono (hVW : V ⊆ W) : fieldDistIn ξ φ W x y ≤ fieldDistIn ξ φ V x y :=
  le_iInf fun P => fieldDistIn_le_lfppLen P.2.1 (P.2.2.mono_right hVW)

theorem fieldDistIn_self (hx : x ∈ V) : fieldDistIn ξ φ V x x = 0 := by
  refine le_antisymm ((fieldDistIn_le_lfppLen (HigherDimLFPP.isPcwC1Path_segPath x x)
    (fun u _ => by simp [HigherDimLFPP.segPath, hx])).trans_eq ?_) bot_le
  have hd : ∀ t, deriv (HigherDimLFPP.segPath x x) t = 0 := fun t => by
    rw [HigherDimLFPP.deriv_segPath, sub_self]
  simp only [lfppLen, hd, norm_zero, mul_zero, ENNReal.ofReal_zero, lintegral_zero]

/-- **Triangle inequality** (continuous field). -/
theorem fieldDistIn_triangle (hφ : Continuous φ) (x y z : Rd d) :
    fieldDistIn ξ φ V x z ≤ fieldDistIn ξ φ V x y + fieldDistIn ξ φ V y z := by
  by_cases hxy : PcwJoined V x y
  · by_cases hyz : PcwJoined V y z
    · rw [fieldDistIn_eq_ofReal hφ (hxy.trans hyz), fieldDistIn_eq_ofReal hφ hxy,
        fieldDistIn_eq_ofReal hφ hyz, ← ENNReal.ofReal_add
          (HigherDimLFPP.lfppDistOn_nonneg _ _ _ _ _) (HigherDimLFPP.lfppDistOn_nonneg _ _ _ _ _)]
      exact ENNReal.ofReal_le_ofReal (HigherDimLFPP.lfppDistOn_triangle hφ hxy hyz)
    · rw [fieldDistIn_eq_top hyz, add_top]
      exact le_top
  · rw [fieldDistIn_eq_top hxy, top_add]
    exact le_top

/-- **Field comparison** on the domain: `|φ - ψ| ≤ M` on `V` gives
`D_V(φ) ≤ e^{|ξ| M} D_V(ψ)` (no continuity needed). -/
theorem fieldDistIn_le_exp_mul {M : ℝ} (hM : ∀ z ∈ V, |φ z - ψ z| ≤ M) :
    fieldDistIn ξ φ V x y ≤ ENNReal.ofReal (Real.exp (|ξ| * M)) * fieldDistIn ξ ψ V x y := by
  unfold fieldDistIn
  rw [ENNReal.mul_iInf_of_ne (by simp [Real.exp_pos]) ENNReal.ofReal_ne_top]
  refine iInf_mono fun P => ?_
  unfold lfppLen
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← mul_assoc]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  exact HigherDimLFPP.exp_mul_le_exp_abs_mul (hM _ (P.2.2 ht))

end Field

/-! ## Diagonal patch -/

/-- `δ` with the diagonal set to `0` -/
def diagPatch (δ : Rd d → Rd d → ℝ≥0∞) (x y : Rd d) : ℝ≥0∞ := if x = y then 0 else δ x y

theorem diagPatch_self (δ : Rd d → Rd d → ℝ≥0∞) (x : Rd d) : diagPatch δ x x = 0 := by
  simp [diagPatch]

theorem diagPatch_le (δ : Rd d → Rd d → ℝ≥0∞) (x y : Rd d) : diagPatch δ x y ≤ δ x y := by
  unfold diagPatch
  split_ifs <;> simp

theorem diagPatch_triangle {δ : Rd d → Rd d → ℝ≥0∞} (hδ : ∀ x y z, δ x z ≤ δ x y + δ y z)
    (x y z : Rd d) : diagPatch δ x z ≤ diagPatch δ x y + diagPatch δ y z := by
  unfold diagPatch
  by_cases hxz : x = z
  · simp [hxz]
  · simp only [hxz, ite_false]
    by_cases hxy : x = y
    · subst hxy
      simp [hxz]
    · by_cases hyz : y = z
      · subst hyz
        simp [hxy]
      · simp only [hxy, hyz, ite_false]
        exact hδ x y z

theorem le_diagPatch {δ : Rd d → Rd d → ℝ≥0∞} {x y : Rd d} (h : x = y → δ x x = 0) :
    δ x y ≤ diagPatch δ x y := by
  unfold diagPatch
  split_ifs with hxy
  · subst hxy
    rw [h rfl]
  · exact le_rfl

end HigherDimLQGMetric
