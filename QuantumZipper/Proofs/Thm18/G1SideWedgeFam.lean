import QuantumZipper.Proofs.Thm18.G1SideTarget
import QuantumZipper.Proofs.Thm18.G1SideAddWT
import QuantumZipper.Proofs.Thm18.G1Z3WedgeAe

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE (3): uniform boundary transport for the wedge field over a family of maps

For a free field `X`, an independent wedge radial process `A` and a finite-parameter family
`q ↦ Ψ q` of maps of one rational boundary class (compact parameter set, Lipschitz in `q`,
values on the `ρ`-thickening of `[a,b]` at distance `≥ c₀ > 0` from `0`, `Hbar` mapped into
`Hbar`), almost surely, for every continuous test function `f` supported in `(a,b)`, uniformly
in `q`,

  `∫ f d(bdryApprox γ (coordChange w (Ψ q) Q) k) → ∫_{Ψ_q([a,b])} f(Ψ_q⁻¹ u) dν_w(u)`,

`w = wedgeField (lateralPart X) A Q` the (unscaled) wedge field (`ae_wedge_transport_family`).

This is the coordinate-change rule for the wedge's boundary measure, simultaneously for all maps of
the family: Sheffield–Wang, arXiv:1605.06171, Thm 4.3 (all maps at once), in the repository's
finite-parameter-family form (`G1Side.ae_transport_family_addFun`, from `SWCore.ae_transport_family`),
combined with the rule `h ↦ h + φ` of Duplantier–Sheffield, *LQG and KPZ*, Invent. Math. 185
(2011), (5.1)/Prop. 2.1: the wedge field is the free field plus its (continuous off `0`) profile
(`G1Side.bdryApprox_wedgeField_family_restrict_eq`, `G1Side.integral_target_wedge`).
Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace G1Side

open SWCore

set_option maxHeartbeats 400000 in
/-- **Uniform boundary transport for the wedge field over a finite-parameter family, a.s.** -/
theorem ae_wedge_transport_family {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ} (hX : IsFreeGFFModConstH X P')
    (hA : IsWedgeProcess α (Qc γ) A P') (hI : IndepFun X (fun ω t => A t ω) P')
    {n : ℕ} (Ψ : (Fin n → ℝ) → ℂ → ℂ) (K : Set (Fin n → ℝ)) {a b ρ M m : ℚ}
    {L R : ℝ} {Kπ : ℝ≥0} {π : (Fin n → ℝ) → Fin n → ℝ} (hab : (a : ℝ) < b) (hρ : (0 : ℝ) < ρ)
    (hm : (0 : ℝ) < m) (hL : 0 ≤ L)
    (hcl : ∀ q ∈ K, Ψ q ∈ BdryClass a b ρ M m)
    (hlip : ∀ q ∈ K, ∀ q' ∈ K, ∀ z ∈ thickening (ρ : ℝ) (segC a b),
      ‖Ψ q z - Ψ q' z‖ ≤ L * ‖q - q'‖)
    (hπ : LipschitzWith Kπ π) (hπK : ∀ q, π q ∈ K) (hπid : ∀ q ∈ K, π q = q)
    (hR : 0 ≤ R) (hKR : ∀ q ∈ K, ‖q‖ ≤ R) (hK : IsCompact K) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hsep : ∀ q ∈ K, ∀ z ∈ thickening (ρ : ℝ) (segC a b), c₀ ≤ ‖Ψ q z‖)
    (hHb : ∀ q ∈ K, ∀ z ∈ thickening (ρ : ℝ) (segC a b), z ∈ Hbar → Ψ q z ∈ Hbar) :
    ∀ᵐ ω ∂P', ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ Ioo (a : ℝ) b →
      ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ q ∈ K,
        |∫ t, f t ∂bdryApprox γ (coordChange (wedgeField (lateralPart (X ω)) (fun t => A t ω)
            (Qc γ)) (Ψ q) (Qc γ)) k -
          ∫ u in Icc (Ψ q (a : ℝ)).re (Ψ q (b : ℝ)).re,
            f (Function.invFunOn (fun t : ℝ => (Ψ q t).re) (Icc (a : ℝ) b) u)
              ∂qBoundaryMeasure γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))| ≤
          η := by
  obtain ⟨G, hG⟩ := WedgeTK.exists_isRegVersion hX
  filter_upwards [ae_transport_family_addFun hX hγ hγ2 Ψ K hab hρ hm hL hcl hlip hπ hπK hπid hR
      hKR hK, hG.ae_good, WedgeCan.ae_raw_dyadic hG, WedgeCan4.ae_continuous_wedgeProcess hA,
    BdryExist.ae_isVagueLimitR_qBoundaryMeasure hX hγ hγ2,
    WedgeBdry.ae_bReg_wedgeField hγ hγ2 hα hX hA hI]
    with ω hT hgood hraw hAc hx hW f hf hfc hfs η hη
  set g := profCut (X ω) (fun t => A t ω) (Qc γ) (c₀ / 2) with hgdef
  have hgc : Continuous g := continuous_profCut hgood hAc (Qc γ) (by positivity)
  have hW' := Thm18Asm.G1Z3.isVagueLimitR_of_good_z3 hW.1
  have hk3 : ∀ᶠ k in atTop, 3 * radius k < (ρ : ℝ) := by
    have ht : Tendsto (fun k => 3 * radius k) atTop (𝓝 (3 * 0)) :=
      tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    rw [mul_zero] at ht
    exact ht.eventually (gt_mem_nhds hρ)
  filter_upwards [hT g hgc f hf hfc hfs η hη, hk3] with k hk hk3 q hq
  have hz : ∀ t, t ∉ Icc (a : ℝ) b → f t = 0 := fun t ht =>
    image_eq_zero_of_notMem_tsupport fun h => ht (Ioo_subset_Icc_self (hfs h))
  have hcong := bdryApprox_wedgeField_family_restrict_eq γ (Qc γ) (Q := Qc γ) hgood hraw hAc hc₀
    hab.le hcl hsep hHb hk3 hq
  have e1 : ∫ t, f t ∂bdryApprox γ (coordChange (wedgeField (lateralPart (X ω)) (fun t => A t ω)
      (Qc γ)) (Ψ q) (Qc γ)) k =
      ∫ t, f t ∂bdryApprox γ (coordChange (X ω + ofFun g) (Ψ q) (Qc γ)) k := by
    have h := congrArg (fun μ : Measure ℝ => ∫ t, f t ∂μ) hcong
    rwa [setIntegral_eq_integral_of_forall_compl_eq_zero hz,
      setIntegral_eq_integral_of_forall_compl_eq_zero hz] at h
  have e2 := integral_target_wedge (γ := γ) hgood hraw hAc hx hW' hab hρ (hcl q hq) hc₀
    (hsep q hq) hfs
  rw [e1, ← e2]
  exact hk q hq

end G1Side
end QuantumZipper
