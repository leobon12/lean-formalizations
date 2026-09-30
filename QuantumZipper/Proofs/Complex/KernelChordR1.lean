import QuantumZipper.Proofs.Complex.KernelChordDoubled
import QuantumZipper.Proofs.Complex.UniformizerLimits

/-!
# KT2 input R, part 1: boundary values of the left-normalized uniformizer on `(−∞,0)`

For a simple chord `η` and a left-normalized uniformizer `φ : D₁ = leftComponent η → ℍ`
(`IsLeftUniformizer`), `exists_boundary_values_leftUniformizer` gives a real function `b` on
`(−∞,0)` with `φ z → b x` as `z → x` in `D₁`, `b` injective on `(−∞,0)` and `b x ≠ 0`.

Proof: this is the Carathéodory boundary correspondence (Pommerenke, *Boundary Behaviour of
Conformal Maps* (1992), Thm 2.6) at the boundary points `x < 0`, obtained exactly as node U4
(`UniformizerLimits.lean`) does at `q = cayley 0` and `q = 1`: in the disk model `cayley ∘ ψ`
(`ψ = φ⁻¹`) the Carathéodory extension `F` (C3) takes the value `cayley x` at most once on
`ℝ ∪ {∞}` because `E \ {cayley x}` is connected (C6, `isPreconnected_thetaCurve_diff_cayley_neg`),
so `tendsto_cayley_comp_inv` gives the limit `ζ` of `cayley ∘ φ` at `x`. The normalization
`φ(∞) = ∞` forces `wInf = 1`, so `ζ ≠ 1` and `b x = cayleyInv ζ` is real with `F (b x) = cayley x`;
`φ(0) = 0` gives `F 0 = cayley 0`. Injectivity of `b` and `b x ≠ 0` follow from the
injectivity of `cayley` on `ℝ`.
-/

noncomputable section

open Set Metric Filter Topology Complex Function Bornology
open QuantumZipper.CA.Uniformizer
open scoped ComplexConjugate

namespace QuantumZipper.CA.Kernel

variable {η : ℝ → ℂ}

theorem ofReal_mem_Hbar' (x : ℝ) : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ ((x : ℝ) : ℂ).im by simp

theorem cayley_ofReal_inj {x y : ℝ} (h : cayley (x : ℂ) = cayley (y : ℂ)) : x = y :=
  ofReal_injective (cayley_injOn_Hbar (ofReal_mem_Hbar' x) (ofReal_mem_Hbar' y) h)

theorem isPreconnected_sphere_diff {q : ℂ} (hq : ‖q‖ = 1) :
    IsPreconnected (sphere (0 : ℂ) 1 \ {q}) := by
  have hqq : q * conj q = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hq]; simp
  have heq : sphere (0 : ℂ) 1 \ {q} = (fun w => q * w) '' (sphere (0 : ℂ) 1 \ {1}) := by
    ext w
    constructor
    · rintro ⟨hw, hwq⟩
      refine ⟨conj q * w, ⟨?_, fun h => hwq ?_⟩, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_mul, Complex.norm_conj, hq, one_mul]
        exact mem_sphere_zero_iff_norm.1 hw
      · rw [mem_singleton_iff] at h ⊢
        rw [← one_mul w, ← hqq, mul_assoc, h, mul_one]
      · show q * (conj q * w) = w
        rw [← mul_assoc, hqq, one_mul]
    · rintro ⟨v, ⟨hv, hv1⟩, rfl⟩
      refine ⟨?_, fun h => hv1 ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_mul, hq, one_mul]
        exact mem_sphere_zero_iff_norm.1 hv
      · rw [mem_singleton_iff] at h ⊢
        have hq0 : q ≠ 0 := fun h0 => by rw [h0, norm_zero] at hq; exact zero_ne_one hq
        exact mul_left_cancel₀ hq0 (h.trans (mul_one q).symm)
  rw [heq]
  exact isPreconnected_sphere_diff_one.image _ (continuous_const.mul continuous_id).continuousOn

/-- **C6 input at `q = cayley x`, `x < 0`.** `E \ {cayley x}` is connected. -/
theorem isPreconnected_thetaCurve_diff_cayley_neg (hη : IsSimpleChord η) {x : ℝ} (hx : x < 0) :
    IsPreconnected (thetaCurve η \ {cayley (x : ℂ)}) := by
  have hnot : cayley (x : ℂ) ∉ cayley '' chordSet η := by
    rintro ⟨c, hc, hce⟩
    have hcx : c = x := cayley_injOn_Hbar (chordSet_subset_Hbar hη hc) (ofReal_mem_Hbar' x) hce
    have := eq_zero_of_mem_chordSet_of_im_nonpos hη hc (by rw [hcx]; simp)
    rw [hcx] at this
    have : x = 0 := by exact_mod_cast this
    linarith
  have hne : (-1 : ℂ) ≠ cayley (x : ℂ) := fun h => by
    rw [← cayley_zero, ← ofReal_zero] at h
    have := cayley_ofReal_inj h
    linarith
  rw [thetaCurve_eq, union_sdiff_distrib, sdiff_singleton_eq_self hnot]
  have hC : IsPreconnected (cayley '' chordSet η) :=
    (isPreconnected_Ici.image η hη.2.1).image _ (continuousOn_cayley.mono fun z hz =>
      ne_neg_I_iff.2 (add_I_ne_zero_of_mem_Hbar (chordSet_subset_Hbar hη hz)))
  exact (isPreconnected_sphere_diff (norm_cayley_ofReal x)).union (-1)
    ⟨by simp, hne⟩ ⟨0, zero_mem_chordSet hη, cayley_zero⟩ hC

/-- **Boundary values on `(−∞,0)`** of a left-normalized uniformizer (Carathéodory boundary
correspondence, Pommerenke Thm 2.6, at the points `x < 0`). -/
theorem exists_boundary_values_leftUniformizer (hη : IsSimpleChord η) {φ : ℂ → ℂ}
    (hφ : IsLeftUniformizer η φ) :
    ∃ b : ℝ → ℝ, (∀ x : ℝ, x < 0 → Tendsto φ (𝓝[leftComponent η] (x : ℂ)) (𝓝 (b x : ℂ))) ∧
      InjOn b (Iio 0) ∧ ∀ x : ℝ, x < 0 → b x ≠ 0 := by
  obtain ⟨⟨hbij, hd, h0, hinf⟩, -⟩ := hφ
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

end QuantumZipper.CA.Kernel
