import QuantumZipper.Proofs.Thm18.G1PkgUnif
import QuantumZipper.Proofs.Complex.KernelChordR

/-!
# G1 package: boundary values of a normalized left uniformizer on `(−∞,0)`

`exists_boundary_values_normalized` is `CA.Kernel.exists_boundary_values_leftUniformizer`
(KernelChordR1.lean) for a **normalized** uniformizer (`IsNormalizedUniformizer`), without the
extra normalization `φ(−1) = −1`, which that proof never uses (its first line discards it); the
proof is copied verbatim. Source: the Carathéodory boundary correspondence (Pommerenke,
*Boundary Behaviour of Conformal Maps* (1992), Thm 2.6), as in KernelChordR1.lean.
-/

noncomputable section

open Set Metric Filter Topology Complex Function Bornology
open QuantumZipper.CA QuantumZipper.CA.Uniformizer QuantumZipper.CA.Kernel
open scoped ComplexConjugate

namespace QuantumZipper
namespace Thm18Asm
namespace G1Chord

variable {η : ℝ → ℂ}

theorem exists_boundary_values_normalized (hη : IsSimpleChord η) {φ : ℂ → ℂ}
    (hφ : IsNormalizedUniformizer (leftComponent η) φ) :
    ∃ b : ℝ → ℝ, (∀ x : ℝ, x < 0 → Tendsto φ (𝓝[leftComponent η] (x : ℂ)) (𝓝 (b x : ℂ))) ∧
      InjOn b (Iio 0) ∧ ∀ x : ℝ, x < 0 → b x ≠ 0 := by
  obtain ⟨hbij, hd, h0, hinf⟩ := hφ
  set D := leftComponent η with hD
  have hDo : IsOpen D := isOpen_leftComponent hη
  set ψ := invFunOn φ D
  have hψb : BijOn ψ H D := BijOn.symm hbij.invOn_invFunOn.symm hbij
  have hψd : DifferentiableOn ℂ ψ H := fun v hv => by
    obtain ⟨z, hz, rfl⟩ := hbij.surjOn hv
    exact (Koebe.hasDerivAt_invFunOn_of_injOn hDo hd hbij.injOn hz).differentiableAt
      |>.differentiableWithinAt
  have hinv : LeftInvOn ψ φ D := hbij.invOn_invFunOn.1
  have h := carHyp_cayley_comp hη hψb hψd
  obtain ⟨F, hEq, hF, -, wInf, -, hInf⟩ := Car.continuousOn_extension h (ulc_thetaCurve hη)
  have hfr := Car.frontier_eq_insert_range h hEq hF hInf
  have hMaps : MapsTo (cayley ∘ ψ) H (ball 0 1) := fun z hz => h.bdd (h.bij.mapsTo hz)
  have hnotΩ : ∀ w : ℂ, ‖w‖ = 1 → w ∉ cayley '' D := fun w hw hwΩ => by
    have := h.bdd hwΩ
    rw [mem_ball_zero_iff, hw] at this
    exact lt_irrefl 1 this
  -- boundary points `x ≤ 0`
  have happ : ∀ x : ℝ, x ≤ 0 → ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
      ((ζ = 1 ∧ wInf = cayley (x : ℂ)) ∨ (ζ ≠ 1 ∧ F (cayleyInv ζ) = cayley (x : ℂ))) ∧
      Tendsto (fun z => cayley (φ z)) (𝓝[D] (x : ℂ)) (𝓝 ζ) := by
    intro x hx
    have hcl : (x : ℂ) ∈ closure D := by
      rcases hx.lt_or_eq with hx | rfl
      · exact ofReal_mem_closure_leftComponent hη hx
      · rw [ofReal_zero]; exact zero_mem_closure_leftComponent hη
    have hconn : IsPreconnected (thetaCurve η \ {cayley (x : ℂ)}) := by
      rcases hx.lt_or_eq with hx | rfl
      · exact isPreconnected_thetaCurve_diff_cayley_neg hη hx
      · rw [ofReal_zero]; exact isPreconnected_thetaCurve_diff_cayley_zero hη
    have hc : ContinuousAt cayley (x : ℂ) :=
      (differentiableAt_cayley (add_I_ne_zero_of_mem_Hbar (ofReal_mem_Hbar' x))).continuousAt
    have hfx : cayley (x : ℂ) ∈ frontier (cayley '' D) := by
      rw [h.isOpen.frontier_eq]
      exact ⟨mem_closure_image hc hcl, hnotΩ _ (norm_cayley_ofReal x)⟩
    exact tendsto_cayley_comp_inv hbij.mapsTo hinv hEq hF hInf hMaps (norm_cayley_ofReal x)
      (Car.eq_of_isPreconnected_diff h hEq hF hInf hconn) (hfr ▸ hfx) self_mem_nhdsWithin
      (hc.tendsto.mono_left nhdsWithin_le_nhds)
  -- the point at infinity: `wInf = 1`
  have hwInf : wInf = 1 := by
    have : (cobounded ℂ ⊓ 𝓟 D).NeBot := neBot_cobounded_inf_leftComponent hη
    have hp1 : (1 : ℂ) ∈ frontier (cayley '' D) := by
      rw [h.isOpen.frontier_eq]
      refine ⟨?_, hnotΩ _ (by simp)⟩
      exact mem_closure_of_tendsto (tendsto_cayley_cobounded.mono_left inf_le_left)
        (eventually_inf_principal.2 (Eventually.of_forall fun z hz => mem_image_of_mem cayley hz))
    obtain ⟨ζ, -, hζ, hlim⟩ := tendsto_cayley_comp_inv hbij.mapsTo hinv hEq hF hInf hMaps
      (q := 1) (l := cobounded ℂ ⊓ 𝓟 D) (by simp)
      (Car.eq_of_isPreconnected_diff h hEq hF hInf (isPreconnected_thetaCurve_diff_one hη))
      (hfr ▸ hp1) (mem_inf_of_right (mem_principal_self _))
      (tendsto_cayley_cobounded.mono_left inf_le_left)
    have h1 : Tendsto (fun z => cayley (φ z)) (cobounded ℂ ⊓ 𝓟 D) (𝓝 1) :=
      tendsto_cayley_cobounded.comp (tendsto_norm_atTop_iff_cobounded.1 hinf)
    have hζ1 : ζ = 1 := tendsto_nhds_unique hlim h1
    rcases hζ with ⟨-, hw⟩ | ⟨hne, -⟩
    · exact hw
    · exact absurd hζ1 hne
  -- the point `0`: `F 0 = cayley 0`
  have hF0 : F 0 = cayley 0 := by
    obtain ⟨ζ, -, hζ, hlim⟩ := happ 0 le_rfl
    have : (𝓝[D] ((0 : ℝ) : ℂ)).NeBot := by
      rw [ofReal_zero]; exact mem_closure_iff_nhdsWithin_neBot.1 (zero_mem_closure_leftComponent hη)
    have hc0 : ContinuousAt cayley 0 := (differentiableAt_cayley (by simp)).continuousAt
    have h1 : Tendsto (fun z => cayley (φ z)) (𝓝[D] ((0 : ℝ) : ℂ)) (𝓝 (cayley 0)) := by
      rw [ofReal_zero]; exact hc0.tendsto.comp h0
    have hζ0 : ζ = cayley 0 := tendsto_nhds_unique hlim h1
    rw [ofReal_zero] at hζ
    rcases hζ with ⟨h1', -⟩ | ⟨-, hFζ⟩
    · rw [hζ0, cayley_zero] at h1'; norm_num at h1'
    · rw [hζ0, cayley_zero, show cayleyInv (-1) = 0 by simp [cayleyInv]] at hFζ
      rw [hFζ, cayley_zero]
  -- boundary values at `x < 0`
  have hB : ∀ x : ℝ, x < 0 → ∃ c : ℝ, Tendsto φ (𝓝[D] (x : ℂ)) (𝓝 (c : ℂ)) ∧
      F c = cayley (x : ℂ) := by
    intro x hx
    obtain ⟨ζ, hζn, hζ, hlim⟩ := happ x hx.le
    rcases hζ with ⟨-, hw⟩ | ⟨hζ1, hFζ⟩
    · rw [hwInf] at hw
      exact absurd hw.symm (cayley_ne_one (add_I_ne_zero_of_mem_Hbar (ofReal_mem_Hbar' x)))
    have hre := cayleyInv_real_of_norm_eq_one hζn
    refine ⟨(cayleyInv ζ).re, ?_, by rw [hre]; exact hFζ⟩
    rw [hre]
    have hci : ContinuousAt cayleyInv ζ := continuousOn_cayleyInv.continuousAt
      (isOpen_ne.mem_nhds hζ1)
    refine (hci.tendsto.comp hlim).congr' (eventually_mem_nhdsWithin.mono fun z hz => ?_)
    exact cayleyInv_cayley (add_I_ne_zero_of_im_nonneg (hbij.mapsTo hz).le)
  choose! b hb hFb using hB
  refine ⟨b, hb, fun x hx y hy hxy => ?_, fun x hx hx0 => ?_⟩
  · have h1 := hFb x hx
    have h2 := hFb y hy
    rw [hxy] at h1
    exact cayley_ofReal_inj (h1.symm.trans h2)
  · have h1 := hFb x hx
    rw [hx0, ofReal_zero, hF0, ← ofReal_zero] at h1
    have := cayley_ofReal_inj h1
    linarith

end G1Chord
end Thm18Asm
end QuantumZipper
