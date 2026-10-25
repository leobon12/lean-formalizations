import SupercriticalLQGUniqueness.B2.PfeAxioms.InternalRadiusCompact
import SupercriticalLQGUniqueness.B2.Iface.Statements

 











set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

open SupercriticalLQGUniqueness.B2.Iface

 

theorem exists_rational_scale_bounds_of_DG20Limit
    (hS : DG20Section4) (hL : DG20Limit)
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
        ∀ ζ : ℝ, 0 < ζ → ∃ C : ℝ, 0 < C ∧
          ∀ r : ℚ, ∀ hr : 0 < r, (r : ℝ) < 1 →
            C⁻¹ * (r : ℝ) ^ ((ξ : ℝ) * Q + ζ) ≤
              (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ∧
            (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ≤
              C * (r : ℝ) ^ ((ξ : ℝ) * Q - ζ) := by
  obtain ⟨φ, hφ, c, hratio, -⟩ := hL ξ Q hQ m hm ε hε
  refine ⟨φ, hφ, c, hratio, ?_⟩
  intro ζ hζ
  obtain ⟨C, hCpos, hC⟩ := (hS ξ Q hQ m hm).2.1 ζ hζ
  refine ⟨C, hCpos, ?_⟩
  intro r hr hr1
  have hrpos : 0 < (r : ℝ) := Rat.cast_pos.mpr hr
  let r₀ : Set.Ioo (0 : ℝ) 1 := ⟨(r : ℝ), hrpos, hr1⟩
  have hεφ : Tendsto (fun n => (ε (φ n) : ℝ)) atTop (𝓝 0) :=
    hε.comp hφ.tendsto_atTop
  have hev : ∀ᶠ n in atTop, (ε (φ n) : ℝ) < (r : ℝ) :=
    hεφ.eventually (Iio_mem_nhds hrpos)
  have hb : ∀ᶠ n in atTop,
      C⁻¹ * (r : ℝ) ^ ((ξ : ℝ) * Q + ζ) ≤
        (r : ℝ) *
          (m ⟨(ε (φ n) : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos (ε (φ n)).property hrpos)⟩ : ℝ) /
          (m (ε (φ n)) : ℝ) ∧
        (r : ℝ) *
          (m ⟨(ε (φ n) : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos (ε (φ n)).property hrpos)⟩ : ℝ) /
          (m (ε (φ n)) : ℝ) ≤ C * (r : ℝ) ^ ((ξ : ℝ) * Q - ζ) := by
    filter_upwards [hev] with n hn
    exact hC r₀ ⟨(ε (φ n) : ℝ), (ε (φ n)).property, hn⟩
  exact ⟨ge_of_tendsto (hratio r hr) (hb.mono fun n hn => hn.1),
    le_of_tendsto (hratio r hr) (hb.mono fun n hn => hn.2)⟩

end SupercriticalLQGUniqueness.B2.PfeAxioms
