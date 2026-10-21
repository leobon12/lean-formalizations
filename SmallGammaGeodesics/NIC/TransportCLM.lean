import SmallGammaGeodesics.NIC.Transport

/-!
# NIC, part 1 (T1 complement): the transport is continuous on `𝓓(ℂ)`

GA2 D5 Step 3: "`τ` is continuous on `𝒟(ℂ)` (composition with a diffeomorphism … times a smooth
function). Hence `X := h ∘ Φ⁻¹`, `(X, φ) := (h, τφ)`, is a random distribution." Part 2 needs
this for Weyl's lemma, whose input is a distribution (`LQGMetric.MarkovWeyl3`).

* `transport_derivative_bound`: on a compact `A`, `‖Dⁱ(τ g)(x)‖ ≤ C_{A,i} · S` whenever
  `‖Dʲ g‖ ≤ S` for all `j ≤ i` (Leibniz `norm_iteratedFDeriv_mul_le` and Faà di Bruno
  `norm_iteratedFDeriv_comp_le`, with the derivatives of `Φ` and of `jac Φ` bounded on `A`);
* `transportCLM : TestC →L[ℝ] TestC` with `transportCLM g = τ g` (`TestFunction.mkCLM`; on each
  `𝓓_K` the map lands in `𝓓_{Ψ(K)}` and is continuous by the seminorm estimate).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped Distributions

namespace SmallGammaGeodesics
namespace NIC

open LQGMetric

lemma natCast_le_smooth (j : ℕ) : ((j : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  WithTop.coe_le_coe.2 le_top

namespace NearIdPair

variable (D : NearIdPair)

/-- **Seminorm estimate**: on a compact `A`, `‖Dⁱ(τ g)‖ ≤ C · S` if `‖Dʲ g‖ ≤ S` for `j ≤ i`. -/
theorem transport_derivative_bound {A : Set ℂ} (hA : IsCompact A) (i : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : TestC) (S : ℝ), (∀ j ≤ i, ∀ y, ‖iteratedFDeriv ℝ j g y‖ ≤ S) →
      ∀ x ∈ A, ‖iteratedFDeriv ℝ i (D.transport g) x‖ ≤ C * S := by
  choose C₁ hC₁ using fun j : ℕ => hA.exists_bound_of_continuousOn
    (D.smooth.continuous_iteratedFDeriv (natCast_le_smooth j)).continuousOn
  choose C₂ hC₂ using fun j : ℕ => hA.exists_bound_of_continuousOn
    (D.contDiff_jac.continuous_iteratedFDeriv (natCast_le_smooth j)).continuousOn
  set B := ∑ j ∈ Finset.range (i + 1), (|C₁ j| + |C₂ j|) with hBdef
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => by positivity
  have hbound : ∀ j ≤ i, ∀ x ∈ A,
      ‖iteratedFDeriv ℝ j D.Φ x‖ ≤ B ∧ ‖iteratedFDeriv ℝ j (jac D.Φ) x‖ ≤ B := by
    intro j hj x hx
    have hs : |C₁ j| + |C₂ j| ≤ B := Finset.single_le_sum
      (f := fun j => |C₁ j| + |C₂ j|) (fun _ _ => by positivity)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
    constructor
    · exact (hC₁ j x hx).trans ((le_abs_self _).trans (by linarith [abs_nonneg (C₂ j)]))
    · exact (hC₂ j x hx).trans ((le_abs_self _).trans (by linarith [abs_nonneg (C₁ j)]))
  set E := 1 + B with hEdef
  have hE : 1 ≤ E := by rw [hEdef]; linarith
  refine ⟨∑ k ∈ Finset.range (i + 1),
    (i.choose k : ℝ) * B * ((i - k).factorial * E ^ (i - k)),
    Finset.sum_nonneg fun _ _ => by positivity, ?_⟩
  intro g S hS x hx
  have e : (D.transport g : ℂ → ℝ) = fun y => jac D.Φ y * ((g : ℂ → ℝ) ∘ D.Φ) y := rfl
  rw [e]
  refine (norm_iteratedFDeriv_mul_le D.contDiff_jac (g.contDiff.comp D.smooth) x
    (natCast_le_smooth i)).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' : k ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  have h₁ : ‖iteratedFDeriv ℝ k (jac D.Φ) x‖ ≤ B := (hbound k hk' x hx).2
  have h₂ : ‖iteratedFDeriv ℝ (i - k) ((g : ℂ → ℝ) ∘ D.Φ) x‖ ≤
      (i - k).factorial * S * E ^ (i - k) := by
    refine norm_iteratedFDeriv_comp_le g.contDiff D.smooth (natCast_le_smooth _) x
      (fun j hj => hS j (hj.trans (Nat.sub_le i k)) _) (fun j hj₁ hjk => ?_)
    refine ((hbound j (hjk.trans (Nat.sub_le i k)) x hx).1).trans ?_
    calc B ≤ E := by rw [hEdef]; linarith
      _ = E ^ 1 := (pow_one E).symm
      _ ≤ E ^ j := pow_le_pow_right₀ hE hj₁
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS 0 (Nat.zero_le _) x)
  calc (i.choose k : ℝ) * ‖iteratedFDeriv ℝ k (jac D.Φ) x‖ *
        ‖iteratedFDeriv ℝ (i - k) ((g : ℂ → ℝ) ∘ D.Φ) x‖
      ≤ (i.choose k : ℝ) * B * ((i - k).factorial * S * E ^ (i - k)) := by
        gcongr
    _ = (i.choose k : ℝ) * B * ((i - k).factorial * E ^ (i - k)) * S := by ring

/-- **The transport as a continuous linear map** `𝓓(ℂ) →L 𝓓(ℂ)` (GA2 D5 Step 3). -/
def transportCLM : TestC →L[ℝ] TestC :=
  TestFunction.mkCLM ℝ D.transport (map_add D.transport) (map_smul D.transport) fun K hK => by
    let K' : Compacts ℂ := ⟨D.Ψ '' (K : Set ℂ), K.isCompact.image D.continuous_inv⟩
    have hK' : (K' : Set ℂ) ⊆ ((⊤ : Opens ℂ) : Set ℂ) := subset_univ _
    have hzero : ∀ φ : 𝓓^{⊤}_{K}(ℂ, ℝ), ∀ x ∉ (K' : Set ℂ),
        D.transport (TestFunction.ofSupportedIn hK φ) x = 0 := by
      intro φ x hx
      have hxF : D.Φ x ∉ (K : Set ℂ) := fun hh => hx ⟨D.Φ x, hh, D.left_inv x⟩
      rw [transport_apply]
      change jac D.Φ x * φ (D.Φ x) = 0
      rw [φ.zero_on_compl hxF]
      simp only [Pi.zero_apply, mul_zero]
    let L : 𝓓^{⊤}_{K}(ℂ, ℝ) →ₗ[ℝ] 𝓓^{⊤}_{K'}(ℂ, ℝ) :=
      { toFun := fun φ =>
          { toFun := D.transport (TestFunction.ofSupportedIn hK φ)
            contDiff' := (D.transport (TestFunction.ofSupportedIn hK φ)).contDiff
            zero_on_compl' := fun x hx => hzero φ x hx }
        map_add' := by
          intro φ ψ
          ext x
          change D.transport (TestFunction.ofSupportedIn hK (φ + ψ)) x = _
          rw [show TestFunction.ofSupportedIn hK (φ + ψ) =
            TestFunction.ofSupportedIn hK φ + TestFunction.ofSupportedIn hK ψ from rfl, map_add]
          rfl
        map_smul' := by
          intro r φ
          ext x
          change D.transport (TestFunction.ofSupportedIn hK (r • φ)) x = _
          rw [show TestFunction.ofSupportedIn hK (r • φ) =
            r • TestFunction.ofSupportedIn hK φ from rfl, map_smul]
          rfl }
    have hLc : Continuous L := by
      refine WithSeminorms.continuous_of_isBounded
        (ContDiffMapSupportedIn.withSeminorms ℝ ℂ ℝ ⊤ K)
        (ContDiffMapSupportedIn.withSeminorms ℝ ℂ ℝ ⊤ K') L
        (Seminorm.IsBounded.of_real fun i => ?_)
      obtain ⟨C, hC, hbound⟩ := D.transport_derivative_bound K'.isCompact i
      refine ⟨Finset.Iic i, C, fun φ => ?_⟩
      have hS : 0 ≤ ((Finset.Iic i).sup
          (ContDiffMapSupportedIn.seminorm ℝ ℂ ℝ ⊤ K)) φ := apply_nonneg _ _
      refine (ContDiffMapSupportedIn.seminorm_top_le_iff ℝ (mul_nonneg hC hS) i _).2
        (fun x hx => ?_)
      refine hbound (TestFunction.ofSupportedIn hK φ) _ (fun j hj y => ?_) x hx
      exact (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ).trans
        (Seminorm.le_def.1 (Finset.le_sup
          (f := ContDiffMapSupportedIn.seminorm ℝ ℂ ℝ ⊤ K) (Finset.mem_Iic.2 hj)) φ)
    have he : D.transport ∘ TestFunction.ofSupportedIn hK =
        TestFunction.ofSupportedInCLM ℝ hK' ∘ L := by
      funext φ
      ext x
      rfl
    rw [he]
    exact (TestFunction.ofSupportedInCLM ℝ hK').continuous.comp hLc

@[simp] lemma transportCLM_apply (g : TestC) : D.transportCLM g = D.transport g := rfl

end NearIdPair

end NIC
end SmallGammaGeodesics
