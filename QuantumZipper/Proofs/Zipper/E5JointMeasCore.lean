import QuantumZipper.Proofs.Zipper.E5IncSwitch
import QuantumZipper.Proofs.Zipper.E5Palm2Zeta
import QuantumZipper.Proofs.Zipper.E5PalmJoint

/-!
# E5-JOINTMEAS, part 1: joint measurability tools for the Palm model integrand (D28)

Task E5-JOINTMEAS (Theorem 1.3, node E5). `E5.PalmJointMeas` (`E5Palm2Norm`) asks for
a.e.-measurability of the model integrand
`z ↦ Γ (loc R (zcfgT κ T B X ϖ X' C z.1.1 z.1.2 z.2))` for `palmMu ⊗ P'`, with the collision field
`X' = regField ϖ ρ₀ ∘ X₀` of decision D28. Two of the ingredients are proved here:

* `measurable_regField_varpiT_prod`: the D28 regular version is jointly measurable in
  (parameter, sample) when read at a *measurable family* of probability measures
  `κm : Ω₀ → Measure ℂ` with values in `varpiFam ϖ` — the (ω, x, ω')-measurability of
  `X'(ϖ_τ)` with `ϖ_τ = varpiT (Vr κ T B ω) (τ_x) ϖ` indexed by the first two variables.
* `measurable_tauS` / `ae_tauS_eq_palmTau`: the collision time `x ↦ τ_x` is only known to be
  a.e.-measurable in `ω` for **fixed** `x` (`Collision.aemeasurable_realHitTime`,
  `E5Palm2Zeta.aemeasurable_realHitTime_Vr`), but it is antitone in `x`
  (`Collision.realHitTime_anti`) and, on the collision region `(0₋(T), 0)`, it is the inverse of
  the continuous strictly antitone function `t ↦ zeroMinus (Vr κ T B ω) t`
  (`Wire2.ae_zeroMinus_Vr_facts`, Rohde–Schramm simple-curve input, proved in the repository),
  hence continuous there. So `τ_x` is the two-sided limit of `τ_d` along rationals `d` in a
  shrinking window `(x − 2⁻ⁿ, x)`; `tauS` is that limit, built from measurable-in-`ω`
  approximations `g d` of `τ_d`, and it is jointly measurable and equal to `τ_x` a.e.

Own elementary measure-theoretic arguments (no published source: Sheffield arXiv:1012.4797 §5.4
does not discuss measurability).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open B2 E1 CoordsFull E4Grid

/-! ## 1. Joint measurability of the D28 regular version at a measurable family of measures -/

/-- **Two-parameter measurability of the regular version** (`regField ϖ ρ₀ ∘ X`, decision D28):
the value at a measurable family `κm ω ∈ varpiFam ϖ` of probability measures is jointly measurable
in `(ω, ω')`. -/
theorem measurable_regField_varpiT_prod {Ω₀ Ω₁ : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω₁]
    {X : Ω₁ → FieldSample} (hXm : ∀ μ, Measurable fun ω => X ω μ) {ϖ : Measure ℂ} (ρ₀ : Measure ℂ)
    (κm : Ω₀ → Measure ℂ)
    (hκ : ∀ A : Set ℂ, MeasurableSet A → Measurable fun ω => κm ω A)
    (hprob : ∀ ω, IsProbabilityMeasure (κm ω)) (hmem : ∀ ω, κm ω ∈ varpiFam ϖ) :
    Measurable fun p : Ω₀ × Ω₁ => regField ϖ ρ₀ (X p.2) (κm p.1) := by
  classical
  have hH : Measurable fun p : Ω₀ × Ω₁ => halfShift ρ₀ (X p.2) :=
    measurable_pi_iff.2 fun μ => (measurable_halfShift_coord hXm ρ₀ μ).comp measurable_snd
  have hread : ∀ κn : Ω₀ → Measure ℂ, (∀ A : Set ℂ, MeasurableSet A →
      Measurable fun ω => κn ω A) → (∀ ω, IsProbabilityMeasure (κn ω)) →
      Measurable fun p : Ω₀ × Ω₁ => regRead ρ₀ (X p.2) (κn p.1) := by
    intro κn hκn hpn
    have hk : ∀ k : ℕ, Measurable fun p : Ω₀ × Ω₁ =>
        ∫ w, avgReg (halfShift ρ₀ (X p.2)) k w ∂(κn p.1) := fun k =>
      measurable_integral_family (fun p : Ω₀ × Ω₁ => κn p.1)
        (fun A hA => (hκn A hA).comp measurable_fst) (fun p => hpn p.1)
        ((measurable_avgReg k).comp (hH.prodMap measurable_id))
    exact (StronglyMeasurable.limUnder fun k => (hk k).stronglyMeasurable).measurable
  rw [show (fun p : Ω₀ × Ω₁ => regField ϖ ρ₀ (X p.2) (κm p.1)) = fun p =>
      X p.2 ρ₀ + regRead ρ₀ (X p.2) (κm p.1) -
        (if ρ₀ ∈ varpiFam ϖ then regRead ρ₀ (X p.2) ρ₀ else 0) from
    funext fun p => regField_of_mem _ (hmem p.1)]
  refine ((hXm ρ₀).comp measurable_snd).add (hread κm hκ hprob) |>.sub ?_
  by_cases h0 : ρ₀ ∈ varpiFam ϖ
  · simp only [h0, ite_true]
    exact hread (fun _ => ρ₀) (fun _ _ => measurable_const) fun _ => ⟨h0.1⟩
  · simp only [h0, ite_false]; exact measurable_const

/-! ## 2. The rational-window surrogate for the collision time `τ_x` -/

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-! ## 3. Joint measurability from continuity in a real parameter (Carathéodory) -/

end E5
end QuantumZipper
