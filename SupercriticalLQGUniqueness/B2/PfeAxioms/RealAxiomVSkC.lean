import SupercriticalLQGUniqueness.B2.PfeAxioms.RealAxiomV
import SupercriticalLQGUniqueness.B2.PfeAxioms.RationalAxiomVSkC

 


set_option autoImplicit false
noncomputable section

open Set Filter Topology Classical
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem exists_real_axiomV_of_DG20LimitSkC
    (hS : DG20Section4) (hSk : B2.DG20Lim.DG20LimitSkC)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    (ε : ℕ → Set.Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
        (∀ r : ℚ, ∀ hr : 0 < r,
          Tendsto (fun n => (r : ℝ) *
            (m ⟨(ε (φ n) : ℝ) / (r : ℝ),
              Set.mem_Ioi.mpr (div_pos (ε (φ n)).property
                (Rat.cast_pos.mpr hr))⟩ : ℝ) /
            (m (ε (φ n)) : ℝ)) atTop
            (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ))) ∧
        ∃ Λ : ℝ, 1 < Λ ∧
          ∀ δ : Set.Ioo (0 : ℝ) 1, ∀ r : ℚ, ∀ hr : 0 < r,
            Λ⁻¹ * (δ : ℝ) ^ Λ ≤
              (c ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr
                (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
                (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ∧
            (c ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr
                (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
                (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ≤
              Λ * (δ : ℝ) ^ (-Λ) := by
  obtain ⟨φ, hφ, c₀, hc₀, Λ, hΛ, hV⟩ :=
    exists_rational_axiomV_of_DG20LimitSkC hS hSk ξ Q hQ m hm ε hε
  let c := pfeNormalizer c₀ hΛ hV
  refine ⟨φ, hφ, c, ?_, Λ, hΛ, ?_⟩
  · intro r hr
    simpa only [c, pfeNormalizer_rat c₀ hΛ hV ⟨r, hr⟩] using hc₀ r hr
  · exact pfeNormalizer_ratio_bounds c₀ hΛ hV

end SupercriticalLQGUniqueness.B2.PfeAxioms
