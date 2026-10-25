import SupercriticalLQGUniqueness.B2.PfeAxioms.RealScale

 







set_option autoImplicit false
noncomputable section

open Set Filter Topology
open Classical

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem pfeNormalizer_ratio_bounds
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    {Λ : ℝ} (hΛ : 1 < Λ)
    (hV : ∀ (δ r : ℚ) (hδ : 0 < δ), (δ : ℝ) < 1 → ∀ (hr : 0 < r),
      Λ⁻¹ * (δ : ℝ) ^ Λ ≤
        (c ⟨((δ * r : ℚ) : ℝ), Set.mem_Ioi.mpr
          (Rat.cast_pos.mpr (mul_pos hδ hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ∧
      (c ⟨((δ * r : ℚ) : ℝ), Set.mem_Ioi.mpr
          (Rat.cast_pos.mpr (mul_pos hδ hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ≤
        Λ * (δ : ℝ) ^ (-Λ))
    (δ : Set.Ioo (0 : ℝ) 1) (r : ℚ) (hr : 0 < r) :
    Λ⁻¹ * (δ : ℝ) ^ Λ ≤
        (pfeNormalizer c hΛ hV
          ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr
            (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
          (pfeNormalizer c hΛ hV
            ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ∧
      (pfeNormalizer c hΛ hV
          ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr
            (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
          (pfeNormalizer c hΛ hV
            ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ≤
        Λ * (δ : ℝ) ^ (-Λ) := by
  let R : PosRat := ⟨r, hr⟩
  let t : Set.Ioi (0 : ℝ) :=
    ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr
      (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩
  have hRpos : 0 < (R : ℝ) := Rat.cast_pos.mpr hr
  have htR : (t : ℝ) < (R : ℝ) := by
    dsimp [t, R]
    exact (mul_lt_iff_lt_one_left hRpos).mpr δ.property.2
  change Λ⁻¹ * (δ : ℝ) ^ Λ ≤
      (pfeNormalizer c hΛ hV t : ℝ) /
        (pfeNormalizer c hΛ hV
          ⟨(R : ℝ), Set.mem_Ioi.mpr hRpos⟩ : ℝ) ∧
    (pfeNormalizer c hΛ hV t : ℝ) /
        (pfeNormalizer c hΛ hV
          ⟨(R : ℝ), Set.mem_Ioi.mpr hRpos⟩ : ℝ) ≤
      Λ * (δ : ℝ) ^ (-Λ)
  have hden := pfeNormalizer_rat c hΛ hV R
  by_cases hrat : ∃ q : PosRat, (q : ℝ) = (t : ℝ)
  · obtain ⟨q, hq⟩ := hrat
    have htq : t = ⟨(q : ℝ), Set.mem_Ioi.mpr
        (Rat.cast_pos.mpr q.property)⟩ := Subtype.ext hq.symm
    rw [htq, pfeNormalizer_rat c hΛ hV q, hden]
    have hqR : (q : ℝ) / (R : ℝ) = (δ : ℝ) := by
      rw [hq]
      dsimp [t, R]
      field_simp
    have hqRlt : (q : ℝ) < (R : ℝ) := by simpa only [hq] using htR
    simpa only [ratNormalizerValue, hqR] using
      (ratNormalizerValue_ratio_bounds c hV q R hqRlt)
  · have hnum : (pfeNormalizer c hΛ hV t : ℝ) =
        (rationalRightLiminf c t).toReal := by
      simp only [pfeNormalizer, pfeNormalizerRaw, hrat, ↓reduceIte]
    rw [hnum, hden]
    have htr : (t : ℝ) / (R : ℝ) = (δ : ℝ) := by
      dsimp [t, R]
      field_simp
    simpa only [ratNormalizerValue, htr] using
      (rationalRightLiminf_ratio_bounds c hΛ hV t R htR)

open SupercriticalLQGUniqueness.B2.Iface

 


theorem exists_real_axiomV_of_DG20Limit
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
    exists_rational_axiomV_of_DG20Limit hS hL ξ Q hQ m hm ε hε
  let c := pfeNormalizer c₀ hΛ hV
  refine ⟨φ, hφ, c, ?_, Λ, hΛ, ?_⟩
  · intro r hr
    simpa only [c, pfeNormalizer_rat c₀ hΛ hV ⟨r, hr⟩] using hc₀ r hr
  · exact pfeNormalizer_ratio_bounds c₀ hΛ hV

set_option pp.fullNames true

end SupercriticalLQGUniqueness.B2.PfeAxioms
