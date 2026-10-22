import HigherDimLQGMetric.Metric.WeylCompose
import HigherDimLQGMetric.Frozen.IsStrongExpMetric
import HigherDimLQGMetric.Frozen.IsWeakExpMetric

/-!
# Consequences of Axioms (I) and (III) for metric assignments (strong and weak classes)

Packet M1 (Phase A, block A2). Port of the deterministic-to-a.s. layer of LQGMetric's
`Metric/WeylLQG.lean` (GM.S1.6, DFGPS.S5) to the frozen `IsStrongExpMetric` and `IsWeakExpMetric`
([S] Definitions 1.1 and 1.3): almost surely, simultaneously for all continuous `f`,

* `D_{h+c} = e^{ξ c} D_h` for constants (`ae_apply_addFun_const`);
* `e^a D_h ≤ D_{h+f} ≤ e^b D_h` when `a ≤ ξ f ≤ b` (`ae_apply_mem_Icc`);
* for every open `U`, `D_{h+f}(·,·;U)` is the Weyl infimum over paths in `U`
  (`ae_internal_eq_weylScaleOn`), hence `e^a D_h(·,·;U) ≤ D_{h+f}(·,·;U) ≤ e^b D_h(·,·;U)` when
  `a ≤ ξ f ≤ b` on `U` (`ae_internal_mem_Icc`);
* (MA1 A1.2 (v), [S] l. 169–177) a comparison `c D_h ≤ D̃_h ≤ C D_h` of two assignments passes to
  `D_{h+f}`, `D̃_{h+f}` for all continuous `f` simultaneously (`ae_apply_compare`).

The deterministic inputs are `apply_eq_exp_mul_of_weyl_const`, `apply_mem_Icc_of_weyl`,
`weylScaleOn_eq_internal`, `internal_mem_Icc_of_le`, `apply_le_mul_of_weyl`,
`mul_apply_le_of_weyl`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {ξ Q : ℝ} {D D' : DistRd d → ContMetric d} {c₀ c₀' : ℝ → ℝ}
variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistRd d}

/-! ### Strong assignments -/

/-- (I) + (III): a.s., for every constant `c`, `D_{h+c} = e^{ξ c} D_h`. -/
theorem IsStrongExpMetric.ae_apply_addFun_const (hD : IsStrongExpMetric d ξ Q D)
    (hh : IsLGFPlusCont h P) :
    ∀ᵐ ω ∂P, ∀ (c : ℝ) (x y : Rd d), (D (addFun (h ω) (ContinuousMap.const (Rd d) c))).1 (x, y) =
      Real.exp (ξ * c) * (D (h ω)).1 (x, y) := by
  filter_upwards [hD.length P h hh, hD.weyl P h hh] with ω hl hw
  exact fun c x y => apply_eq_exp_mul_of_weyl_const hl (fun x y => (hw _ x y).symm) x y

/-- (I) + (III): a.s., for every continuous `f` with `a ≤ ξ f ≤ b`, `e^a D_h ≤ D_{h+f} ≤ e^b D_h`. -/
theorem IsStrongExpMetric.ae_apply_mem_Icc (hD : IsStrongExpMetric d ξ Q D)
    (hh : IsLGFPlusCont h P) :
    ∀ᵐ ω ∂P, ∀ (f : C(Rd d, ℝ)) (a b : ℝ), (∀ x, a ≤ ξ * f x) → (∀ x, ξ * f x ≤ b) →
      ∀ x y : Rd d, Real.exp a * (D (h ω)).1 (x, y) ≤ (D (addFun (h ω) f)).1 (x, y) ∧
        (D (addFun (h ω) f)).1 (x, y) ≤ Real.exp b * (D (h ω)).1 (x, y) := by
  filter_upwards [hD.length P h hh, hD.weyl P h hh] with ω hl hw
  exact fun f a b ha hb x y => apply_mem_Icc_of_weyl hl (fun x y => (hw f x y).symm) ha hb x y

/-- (III): a.s., for every continuous `f` and open `U`, `D_{h+f}(·,·;U) = (e^{ξ f}·D_h)_U`. -/
theorem IsStrongExpMetric.ae_internal_eq_weylScaleOn (hD : IsStrongExpMetric d ξ Q D)
    (hh : IsLGFPlusCont h P) :
    ∀ᵐ ω ∂P, ∀ (f : C(Rd d, ℝ)) (U : Set (Rd d)), IsOpen U → ∀ z w : Rd d,
      (D (addFun (h ω) f)).internal U z w = weylScaleOn ξ f (D (h ω)) U z w := by
  filter_upwards [hD.weyl P h hh] with ω hw
  exact fun f U hU z w =>
    (weylScaleOn_eq_internal _ (fun x y => (hw f x y).symm) hU z w).symm

/-- (III): a.s., for every continuous `f`, open `U`, and `a ≤ ξ f ≤ b` on `U`,
`e^a D_h(·,·;U) ≤ D_{h+f}(·,·;U) ≤ e^b D_h(·,·;U)`. -/
theorem IsStrongExpMetric.ae_internal_mem_Icc (hD : IsStrongExpMetric d ξ Q D)
    (hh : IsLGFPlusCont h P) :
    ∀ᵐ ω ∂P, ∀ (f : C(Rd d, ℝ)) (U : Set (Rd d)) (a b : ℝ), IsOpen U →
      (∀ x ∈ U, a ≤ ξ * f x) → (∀ x ∈ U, ξ * f x ≤ b) → ∀ z w : Rd d,
        ENNReal.ofReal (Real.exp a) * (D (h ω)).internal U z w ≤
            (D (addFun (h ω) f)).internal U z w ∧
          (D (addFun (h ω) f)).internal U z w ≤
            ENNReal.ofReal (Real.exp b) * (D (h ω)).internal U z w := by
  filter_upwards [hD.weyl P h hh] with ω hw
  exact fun f U a b hU ha hb z w =>
    internal_mem_Icc_of_le _ (fun x y => (hw f x y).symm) hU ha hb z w

/-- **Comparison passes to Weyl reweightings** (MA1 A1.2 (v)): if a.s. `c D_h ≤ D'_h ≤ C D_h`,
then a.s., simultaneously for all continuous `f`, `c D_{h+f} ≤ D'_{h+f} ≤ C D_{h+f}`. -/
theorem IsStrongExpMetric.ae_apply_compare (hD : IsStrongExpMetric d ξ Q D)
    (hD' : IsStrongExpMetric d ξ Q D') (hh : IsLGFPlusCont h P) {c C : ℝ} (hc : 0 ≤ c)
    (hC : 0 < C)
    (hcomp : ∀ᵐ ω ∂P, ∀ x y : Rd d, c * (D (h ω)).1 (x, y) ≤ (D' (h ω)).1 (x, y) ∧
      (D' (h ω)).1 (x, y) ≤ C * (D (h ω)).1 (x, y)) :
    ∀ᵐ ω ∂P, ∀ (f : C(Rd d, ℝ)) (x y : Rd d),
      c * (D (addFun (h ω) f)).1 (x, y) ≤ (D' (addFun (h ω) f)).1 (x, y) ∧
        (D' (addFun (h ω) f)).1 (x, y) ≤ C * (D (addFun (h ω) f)).1 (x, y) := by
  filter_upwards [hD.weyl P h hh, hD'.weyl P h hh, hcomp] with ω hw hw' hcmp
  exact fun f x y =>
    ⟨mul_apply_le_of_weyl hc (fun x y => (hcmp x y).1) (fun x y => (hw f x y).symm)
        (fun x y => (hw' f x y).symm) x y,
      apply_le_mul_of_weyl hC (fun x y => (hcmp x y).2) (fun x y => (hw f x y).symm)
        (fun x y => (hw' f x y).symm) x y⟩

/-! ### Weak assignments -/

/-- (I) + (III): a.s., for every constant `c`, `D_{h+c} = e^{ξ c} D_h`. -/
theorem IsWeakExpMetric.ae_apply_addFun_const (hD : IsWeakExpMetric d ξ D c₀)
    (hh : IsLGFPlusCont h P) :
    ∀ᵐ ω ∂P, ∀ (c : ℝ) (x y : Rd d), (D (addFun (h ω) (ContinuousMap.const (Rd d) c))).1 (x, y) =
      Real.exp (ξ * c) * (D (h ω)).1 (x, y) := by
  filter_upwards [hD.length P h hh, hD.weyl P h hh] with ω hl hw
  exact fun c x y => apply_eq_exp_mul_of_weyl_const hl (fun x y => (hw _ x y).symm) x y

/-- (I) + (III): a.s., for every continuous `f` with `a ≤ ξ f ≤ b`, `e^a D_h ≤ D_{h+f} ≤ e^b D_h`. -/
theorem IsWeakExpMetric.ae_apply_mem_Icc (hD : IsWeakExpMetric d ξ D c₀)
    (hh : IsLGFPlusCont h P) :
    ∀ᵐ ω ∂P, ∀ (f : C(Rd d, ℝ)) (a b : ℝ), (∀ x, a ≤ ξ * f x) → (∀ x, ξ * f x ≤ b) →
      ∀ x y : Rd d, Real.exp a * (D (h ω)).1 (x, y) ≤ (D (addFun (h ω) f)).1 (x, y) ∧
        (D (addFun (h ω) f)).1 (x, y) ≤ Real.exp b * (D (h ω)).1 (x, y) := by
  filter_upwards [hD.length P h hh, hD.weyl P h hh] with ω hl hw
  exact fun f a b ha hb x y => apply_mem_Icc_of_weyl hl (fun x y => (hw f x y).symm) ha hb x y

/-- (III): a.s., for every continuous `f` and open `U`, `D_{h+f}(·,·;U) = (e^{ξ f}·D_h)_U`. -/
theorem IsWeakExpMetric.ae_internal_eq_weylScaleOn (hD : IsWeakExpMetric d ξ D c₀)
    (hh : IsLGFPlusCont h P) :
    ∀ᵐ ω ∂P, ∀ (f : C(Rd d, ℝ)) (U : Set (Rd d)), IsOpen U → ∀ z w : Rd d,
      (D (addFun (h ω) f)).internal U z w = weylScaleOn ξ f (D (h ω)) U z w := by
  filter_upwards [hD.weyl P h hh] with ω hw
  exact fun f U hU z w =>
    (weylScaleOn_eq_internal _ (fun x y => (hw f x y).symm) hU z w).symm

/-- (III): a.s., for every continuous `f`, open `U`, and `a ≤ ξ f ≤ b` on `U`,
`e^a D_h(·,·;U) ≤ D_{h+f}(·,·;U) ≤ e^b D_h(·,·;U)`. -/
theorem IsWeakExpMetric.ae_internal_mem_Icc (hD : IsWeakExpMetric d ξ D c₀)
    (hh : IsLGFPlusCont h P) :
    ∀ᵐ ω ∂P, ∀ (f : C(Rd d, ℝ)) (U : Set (Rd d)) (a b : ℝ), IsOpen U →
      (∀ x ∈ U, a ≤ ξ * f x) → (∀ x ∈ U, ξ * f x ≤ b) → ∀ z w : Rd d,
        ENNReal.ofReal (Real.exp a) * (D (h ω)).internal U z w ≤
            (D (addFun (h ω) f)).internal U z w ∧
          (D (addFun (h ω) f)).internal U z w ≤
            ENNReal.ofReal (Real.exp b) * (D (h ω)).internal U z w := by
  filter_upwards [hD.weyl P h hh] with ω hw
  exact fun f U a b hU ha hb z w =>
    internal_mem_Icc_of_le _ (fun x y => (hw f x y).symm) hU ha hb z w

/-- **Comparison passes to Weyl reweightings** (MA1 A1.2 (v)), weak class (normalizers may
differ): if a.s. `c D_h ≤ D'_h ≤ C D_h`, then a.s., simultaneously for all continuous `f`,
`c D_{h+f} ≤ D'_{h+f} ≤ C D_{h+f}`. -/
theorem IsWeakExpMetric.ae_apply_compare (hD : IsWeakExpMetric d ξ D c₀)
    (hD' : IsWeakExpMetric d ξ D' c₀') (hh : IsLGFPlusCont h P) {c C : ℝ} (hc : 0 ≤ c)
    (hC : 0 < C)
    (hcomp : ∀ᵐ ω ∂P, ∀ x y : Rd d, c * (D (h ω)).1 (x, y) ≤ (D' (h ω)).1 (x, y) ∧
      (D' (h ω)).1 (x, y) ≤ C * (D (h ω)).1 (x, y)) :
    ∀ᵐ ω ∂P, ∀ (f : C(Rd d, ℝ)) (x y : Rd d),
      c * (D (addFun (h ω) f)).1 (x, y) ≤ (D' (addFun (h ω) f)).1 (x, y) ∧
        (D' (addFun (h ω) f)).1 (x, y) ≤ C * (D (addFun (h ω) f)).1 (x, y) := by
  filter_upwards [hD.weyl P h hh, hD'.weyl P h hh, hcomp] with ω hw hw' hcmp
  exact fun f x y =>
    ⟨mul_apply_le_of_weyl hc (fun x y => (hcmp x y).1) (fun x y => (hw f x y).symm)
        (fun x y => (hw' f x y).symm) x y,
      apply_le_mul_of_weyl hC (fun x y => (hcmp x y).2) (fun x y => (hw f x y).symm)
        (fun x y => (hw' f x y).symm) x y⟩

end HigherDimLQGMetric
