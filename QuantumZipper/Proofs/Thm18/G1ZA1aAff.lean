import QuantumZipper.Proofs.Thm18.G1ZA1aDrv
import QuantumZipper.Proofs.Complex.UniformizerUnique
import QuantumZipper.Proofs.RS.KoebeLoewnerTime
import QuantumZipper.Proofs.Complex.KernelChordRight

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-A1a (ii): the rerooting composite is affine

Part (ii) of `G1RerootAffineStmt` (`G1ZSplitDefs.lean`, handoff `G1-ZSPLIT.md` item 1).

* `exists_affine_of_bijOn` (abstract): if `M` is a holomorphic bijection of `D'` onto `D` sending
  `∞` to `∞`, and `φ`, `φ'` are normalized uniformizers of `D`, `D'`, then
  `M ∘ φ'⁻¹ = φ⁻¹ ∘ (w ↦ μ w + ν)` on `ℍ` with `μ > 0`, `ν ∈ ℝ`. Source: `χ = φ ∘ M ∘ φ'⁻¹` is a
  holomorphic bijection of `ℍ`, hence a real Möbius map (Burckel, *Classical Analysis in the
  Complex Plane*, Thm 6.2(ii); `CA.exists_realMobius_of_bijOn_H`); `χ(∞) = ∞` forces `c = 0`
  (the same own elementary argument as `CA.Uniformizer.normalizedUniformizer_unique`, without the
  normalization at `0`). Sheffield, arXiv:1012.4797, pp. 69–70 ("affine").
* `g1RerootAffineStmt_of`: `G1RerootAffineStmt` from part (i) (`g1zDrvGood_newDrv`, proved), the
  component transport `G1zCompTransportStmt` and the boundary node `G1zRerootBdryStmt` (below).
-/

noncomputable section

open Filter Set Complex Function Bornology
open scoped Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1ZA1a

open QuantumZipper.CA QuantumZipper.CA.Uniformizer

/-- **Abstract affine lemma.** -/
theorem exists_affine_of_bijOn {D D' : Set ℂ} (hD'o : IsOpen D')
    (hD'inf : (cobounded ℂ ⊓ 𝓟 D').NeBot) {φ φ' M : ℂ → ℂ}
    (hφ : IsNormalizedUniformizer D φ) (hφ' : IsNormalizedUniformizer D' φ')
    (hM : BijOn M D' D) (hMd : DifferentiableOn ℂ M D')
    (hMinf : Tendsto (fun z => ‖M z‖) (cobounded ℂ ⊓ 𝓟 D') atTop) :
    ∃ μ ν : ℝ, 0 < μ ∧ ∀ w ∈ H, M (invFunOn φ' D' w) = invFunOn φ D ((μ : ℂ) * w + ν) := by
  obtain ⟨hb, hd, -, hi⟩ := hφ
  obtain ⟨hb', hd', -, hi'⟩ := hφ'
  have hψ'b : BijOn (invFunOn φ' D') H D' := BijOn.symm hb'.invOn_invFunOn.symm hb'
  have hψ'd : DifferentiableOn ℂ (invFunOn φ' D') H := fun v hv => by
    obtain ⟨z, hz, rfl⟩ := hb'.surjOn hv
    exact (Koebe.hasDerivAt_invFunOn_of_injOn hD'o hd' hb'.injOn hz).differentiableAt
      |>.differentiableWithinAt
  set χ : ℂ → ℂ := fun w => φ (M (invFunOn φ' D' w)) with hχ
  have hχb : BijOn χ H H := hb.comp (hM.comp hψ'b)
  have hχd : DifferentiableOn ℂ χ H :=
    hd.comp (hMd.comp hψ'd hψ'b.mapsTo) (hM.mapsTo.comp hψ'b.mapsTo)
  obtain ⟨a, b, c, d, hdet, hEq⟩ := exists_realMobius_of_bijOn_H hχd hχb
  have hc : c = 0 := by
    by_contra hc
    have hkey : ∀ z ∈ D', χ (φ' z) = φ (M z) := fun z hz => by
      simp only [hχ, hb'.invOn_invFunOn.1 hz]
    have hMD : Tendsto M (cobounded ℂ ⊓ 𝓟 D') (cobounded ℂ ⊓ 𝓟 D) := by
      refine tendsto_inf.2 ⟨?_, tendsto_principal.2 ?_⟩
      · rw [← tendsto_norm_atTop_iff_cobounded]; exact hMinf
      · exact mem_inf_of_right (mem_principal.2 fun z hz => hM.mapsTo hz)
    have h1 : Tendsto (fun z => ‖χ (φ' z)‖) (cobounded ℂ ⊓ 𝓟 D') atTop := by
      refine (hi.comp hMD).congr' ?_
      filter_upwards [mem_inf_of_right (mem_principal_self D')] with z hz
      simp only [Function.comp_apply, hkey z hz]
    have hφ'H : Tendsto φ' (cobounded ℂ ⊓ 𝓟 D') (cobounded ℂ ⊓ 𝓟 H) := by
      refine tendsto_inf.2 ⟨?_, tendsto_principal.2 ?_⟩
      · rw [← tendsto_norm_atTop_iff_cobounded]; exact hi'
      · exact mem_inf_of_right (mem_principal.2 fun z hz => hb'.mapsTo hz)
    have hinv : Tendsto (fun w : ℂ => w⁻¹) (cobounded ℂ ⊓ 𝓟 H) (𝓝 0) :=
      tendsto_inv₀_cobounded.mono_left inf_le_left
    have hq : Tendsto (fun w : ℂ => ((a : ℂ) + b * w⁻¹) / ((c : ℂ) + d * w⁻¹))
        (cobounded ℂ ⊓ 𝓟 H) (𝓝 (((a : ℂ) + b * 0) / ((c : ℂ) + d * 0))) :=
      ((hinv.const_mul _).const_add _).div ((hinv.const_mul _).const_add _)
        (by simpa using (show (c : ℂ) ≠ 0 by exact_mod_cast hc))
    have hχlim : Tendsto χ (cobounded ℂ ⊓ 𝓟 H) (𝓝 (((a : ℂ) + b * 0) / ((c : ℂ) + d * 0))) := by
      refine hq.congr' ?_
      filter_upwards [mem_inf_of_right (mem_principal_self H)] with w hw
      have hw0 : w ≠ 0 := fun h => by
        have : (0 : ℝ) < w.im := hw
        rw [h] at this; simp at this
      have hden := realMobius_denom_ne_zero hdet hw
      rw [hEq hw, realMobius]
      field_simp
    exact not_tendsto_atTop_of_tendsto_nhds (hχlim.comp hφ'H).norm h1
  subst hc
  have had : 0 < a * d := by simpa using hdet
  have hd0 : d ≠ 0 := by rintro rfl; simp at had
  refine ⟨a / d, b / d, ?_, fun w hw => ?_⟩
  · have : a / d = a * d / (d * d) := by field_simp
    rw [this]; exact div_pos had (mul_self_pos.2 hd0)
  · have hMw : M (invFunOn φ' D' w) ∈ D := hM.mapsTo (hψ'b.mapsTo hw)
    have h1 : invFunOn φ D (χ w) = M (invFunOn φ' D' w) := hb.invOn_invFunOn.1 hMw
    rw [← h1, hEq hw, realMobius]
    congr 1
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd0
    rw [Complex.ofReal_zero, zero_mul, zero_add, div_eq_iff hd', Complex.ofReal_div,
      Complex.ofReal_div, add_mul, mul_assoc, mul_comm w, ← mul_assoc, div_mul_cancel₀ _ hd',
      div_mul_cancel₀ _ hd']

/-- The affine factorization with `λ = 1/μ` and `β = −ν/μ`. -/
theorem exists_lam_beta_of_bijOn {D D' : Set ℂ} (hD'o : IsOpen D')
    (hD'inf : (cobounded ℂ ⊓ 𝓟 D').NeBot) {φ φ' M : ℂ → ℂ}
    (hφ : IsNormalizedUniformizer D φ) (hφ' : IsNormalizedUniformizer D' φ')
    (hM : BijOn M D' D) (hMd : DifferentiableOn ℂ M D')
    (hMinf : Tendsto (fun z => ‖M z‖) (cobounded ℂ ⊓ 𝓟 D') atTop) :
    ∃ lam β : ℝ, 0 < lam ∧
      EqOn (fun u => M (invFunOn φ' D' (u + β))) (fun u => invFunOn φ D (u / lam)) H := by
  obtain ⟨μ, ν, hμ, h⟩ := exists_affine_of_bijOn hD'o hD'inf hφ hφ' hM hMd hMinf
  refine ⟨1 / μ, -ν / μ, by positivity, fun u hu => ?_⟩
  have huH : u + ((-ν / μ : ℝ) : ℂ) ∈ H := by
    show 0 < (u + ((-ν / μ : ℝ) : ℂ)).im
    simpa using (show (0 : ℝ) < u.im from hu)
  show M (invFunOn φ' D' (u + ((-ν / μ : ℝ) : ℂ))) = invFunOn φ D (u / ((1 / μ : ℝ) : ℂ))
  rw [h _ huH]
  congr 1
  have hμ' : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
  push_cast
  field_simp
  ring

/-! ## The side components -/

theorem isNormalizedUniformizer_sideDom {η : ℝ → ℂ} (hη : IsSimpleChord η) (left : Bool) :
    IsNormalizedUniformizer (sideDom η left) (uniformizer (sideDom η left)) := by
  unfold uniformizer
  cases left
  · exact Classical.epsilon_spec (exists_normalizedUniformizer_rightComponent hη)
  · exact Classical.epsilon_spec (exists_normalizedUniformizer_leftComponent hη)

theorem isOpen_sideDom {η : ℝ → ℂ} (hη : IsSimpleChord η) (left : Bool) :
    IsOpen (sideDom η left) := by
  cases left
  · exact Kernel.isOpen_rightComponent_qz hη
  · exact isOpen_leftComponent hη

theorem sideDom_subset_H (η : ℝ → ℂ) (left : Bool) : sideDom η left ⊆ H := by
  cases left
  · exact rightComponent_subset_H η
  · exact leftComponent_subset_H η

theorem neBot_cobounded_inf_sideDom {η : ℝ → ℂ} (hη : IsSimpleChord η) (left : Bool) :
    (cobounded ℂ ⊓ 𝓟 (sideDom η left)).NeBot := by
  cases left
  · have hη' := isSimpleChord_refl_comp hη
    have hsub : refl '' leftComponent (refl ∘ η) ⊆ rightComponent η := by
      rintro _ ⟨w, hw, rfl⟩; exact refl_mem_right_of_mem_left hw
    have hL := neBot_cobounded_inf_leftComponent hη'
    show (cobounded ℂ ⊓ 𝓟 (rightComponent η)).NeBot
    rw [inf_principal_neBot_iff] at hL ⊢
    intro U hU
    have hrefl : Tendsto refl (cobounded ℂ) (cobounded ℂ) := by
      rw [← tendsto_norm_atTop_iff_cobounded]
      simpa using tendsto_norm_cobounded_atTop
    obtain ⟨z, hzU, hzL⟩ := hL _ (hrefl hU)
    exact ⟨refl z, hzU, hsub ⟨z, hzL, rfl⟩⟩
  · exact neBot_cobounded_inf_leftComponent hη

/-! ## Open nodes of part (ii) and the assembly -/

/-- **Component transport** (Loewner flow and the topology of the two sides): the map
`z ↦ f_t⁻¹(a z)` sends the side component of the new trace bijectively onto the side component
of the old trace. -/
def G1zCompTransportStmt : Prop :=
  ∀ W : ℝ → ℝ, G1zDrvGood W → ∀ t a : ℝ, 0 < t → 0 < a → ∀ left : Bool,
    BijOn (fun z => fwdMapInv W t ((a : ℂ) * z))
      (sideDom (trace (g1zNewDrv W t a)) left) (sideDom (trace W) left)

/-- **Boundary point of the affine factorization**: for every affine factorization, the point
`β` lies in the side half-line and `a ψ'(u) → O^∓_t` as `u → β` (Carathéodory boundary behaviour
of `ψ` at `0` and of `f_t` at the base of the curve). -/
def G1zRerootBdryStmt : Prop :=
  ∀ W : ℝ → ℝ, G1zDrvGood W → ∀ t a : ℝ, 0 < t → 0 < a → ∀ left : Bool, ∀ lam β : ℝ, 0 < lam →
    EqOn (fun u => fwdMapInv W t ((a : ℂ) * g1zSideMap left (g1zNewDrv W t a) (u + β)))
      (fun u => g1zSideMap left W (u / lam)) H →
    β ∈ g1SideHalf left ∧
      Tendsto (fun u => (a : ℂ) * g1zSideMap left (g1zNewDrv W t a) u) (𝓝[H] (β : ℂ))
        (𝓝 (g1zSideImage left W t : ℂ))

/-- **The affine factorization exists** (given the component transport). -/
theorem exists_lam_beta_reroot (hT : G1zCompTransportStmt) {W : ℝ → ℝ} (hG : G1zDrvGood W)
    {t a : ℝ} (ht : 0 < t) (ha : 0 < a) (left : Bool) :
    ∃ lam β : ℝ, 0 < lam ∧
      EqOn (fun u => fwdMapInv W t ((a : ℂ) * g1zSideMap left (g1zNewDrv W t a) (u + β)))
        (fun u => g1zSideMap left W (u / lam)) H := by
  have hG' := g1zDrvGood_newDrv hG ht ha
  have hη := hG.2.2.2.1
  have hη' := hG'.2.2.2.1
  obtain ⟨C, hC⟩ := exists_bound_fwdMapInv hG ht
  have hMd : DifferentiableOn ℂ (fun z => fwdMapInv W t ((a : ℂ) * z))
      (sideDom (trace (g1zNewDrv W t a)) left) := by
    intro z hz
    have hzH : (a : ℂ) * z ∈ H := by
      show 0 < ((a : ℂ) * z).im
      simpa using mul_pos ha (show (0 : ℝ) < z.im from sideDom_subset_H _ left hz)
    exact ((RS.differentiableOn_fwdMapInv hG.1 hG.2.1 ht.le _ hzH).differentiableAt
      (isOpen_H.mem_nhds hzH)).comp z ((differentiableAt_id.const_mul _))
      |>.differentiableWithinAt
  have hMinf : Tendsto (fun z => ‖fwdMapInv W t ((a : ℂ) * z)‖)
      (cobounded ℂ ⊓ 𝓟 (sideDom (trace (g1zNewDrv W t a)) left)) atTop := by
    have hlow : ∀ z ∈ sideDom (trace (g1zNewDrv W t a)) left,
        a * ‖z‖ + -C ≤ ‖fwdMapInv W t ((a : ℂ) * z)‖ := by
      intro z hz
      have hzH : (a : ℂ) * z ∈ H := by
        show 0 < ((a : ℂ) * z).im
        simpa using mul_pos ha (show (0 : ℝ) < z.im from sideDom_subset_H _ left hz)
      have h1 := hC _ hzH
      have h2 := norm_sub_norm_le ((a : ℂ) * z) (fwdMapInv W t ((a : ℂ) * z))
      rw [norm_sub_rev] at h2
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha] at h2
      linarith
    have hbig : Tendsto (fun z : ℂ => a * ‖z‖ + -C)
        (cobounded ℂ ⊓ 𝓟 (sideDom (trace (g1zNewDrv W t a)) left)) atTop :=
      tendsto_atTop_add_const_right _ (-C)
        ((tendsto_norm_cobounded_atTop.mono_left inf_le_left).const_mul_atTop ha)
    exact tendsto_atTop_mono' _ (mem_inf_of_right (mem_principal.2 hlow)) hbig
  exact exists_lam_beta_of_bijOn (isOpen_sideDom hη' left) (neBot_cobounded_inf_sideDom hη' left)
    (isNormalizedUniformizer_sideDom hη left) (isNormalizedUniformizer_sideDom hη' left)
    (hT W hG t a ht ha left) hMd hMinf

/-- **`G1RerootAffineStmt` (A1a)** from the component transport and the boundary node; part (i)
(`g1zDrvGood_newDrv`) and the affine factorization are proved. -/
theorem g1RerootAffineStmt_of (hT : G1zCompTransportStmt) (hB : G1zRerootBdryStmt) :
    G1RerootAffineStmt := by
  intro W hG t a ht ha left
  refine ⟨g1zDrvGood_newDrv hG ht ha, ?_⟩
  obtain ⟨lam, β, hlam, hEq⟩ := exists_lam_beta_reroot hT hG ht ha left
  obtain ⟨hβ, hlim⟩ := hB W hG t a ht ha left lam β hlam hEq
  exact ⟨lam, β, hlam, hβ, hEq, hlim⟩

end G1ZA1a
end Thm18Asm
end QuantumZipper
