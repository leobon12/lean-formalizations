import SupercriticalLQGUniqueness.B2.PfeAxioms.RationalScaleSkC

 









set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

open SupercriticalLQGUniqueness.B2.Iface

private theorem normalized_ratio_cancel (δ r a b m : ℝ)
    (hr : r ≠ 0) (hb : b ≠ 0) (hm : m ≠ 0) :
    (((δ * r) * a / m) / (r * b / m)) = δ * a / b := by
  field_simp

 


theorem exists_rational_scale_ratio_bounds_of_DG20LimitSkC
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
        ∀ ζ : ℝ, 0 < ζ → ∃ C : ℝ, 0 < C ∧
          ∀ (δ r : ℚ) (hδ : 0 < δ), (δ : ℝ) < 1 → ∀ (hr : 0 < r),
            C⁻¹ * (δ : ℝ) ^ ((ξ : ℝ) * Q + ζ) ≤
              (c ⟨((δ * r : ℚ) : ℝ), Set.mem_Ioi.mpr
                (Rat.cast_pos.mpr (mul_pos hδ hr))⟩ : ℝ) /
                (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ∧
            (c ⟨((δ * r : ℚ) : ℝ), Set.mem_Ioi.mpr
                (Rat.cast_pos.mpr (mul_pos hδ hr))⟩ : ℝ) /
                (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ≤
              C * (δ : ℝ) ^ ((ξ : ℝ) * Q - ζ) := by
  obtain ⟨φ, hφ, c, hratio, -⟩ :=
    exists_rational_scale_bounds_of_DG20LimitSkC hS hSk ξ Q hQ m hm ε hε
  refine ⟨φ, hφ, c, hratio, ?_⟩
  intro ζ hζ
  obtain ⟨C, hCpos, hC⟩ := (hS ξ Q hQ m hm).2.1 ζ hζ
  refine ⟨C, hCpos, ?_⟩
  intro δ r hδ hδ1 hr
  have hδpos : 0 < (δ : ℝ) := Rat.cast_pos.mpr hδ
  have hrpos : 0 < (r : ℝ) := Rat.cast_pos.mpr hr
  have hdrpos : 0 < ((δ * r : ℚ) : ℝ) := Rat.cast_pos.mpr (mul_pos hδ hr)
  let dr : ℚ := δ * r
  have hεφ : Tendsto (fun n => (ε (φ n) : ℝ)) atTop (𝓝 0) :=
    hε.comp hφ.tendsto_atTop
  have hev : ∀ᶠ n in atTop, (ε (φ n) : ℝ) < (δ : ℝ) * (r : ℝ) :=
    hεφ.eventually (Iio_mem_nhds (mul_pos hδpos hrpos))
  let A : ℕ → ℝ := fun n => (dr : ℝ) *
    (m ⟨(ε (φ n) : ℝ) / (dr : ℝ),
      Set.mem_Ioi.mpr (div_pos (ε (φ n)).property hdrpos)⟩ : ℝ) /
      (m (ε (φ n)) : ℝ)
  let B : ℕ → ℝ := fun n => (r : ℝ) *
    (m ⟨(ε (φ n) : ℝ) / (r : ℝ),
      Set.mem_Ioi.mpr (div_pos (ε (φ n)).property hrpos)⟩ : ℝ) /
      (m (ε (φ n)) : ℝ)
  have hA : Tendsto A atTop
      (𝓝 (c ⟨(dr : ℝ), Set.mem_Ioi.mpr hdrpos⟩ : ℝ)) := hratio dr (mul_pos hδ hr)
  have hB : Tendsto B atTop
      (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr hrpos⟩ : ℝ)) := hratio r hr
  have hAB : Tendsto (fun n => A n / B n) atTop
      (𝓝 ((c ⟨(dr : ℝ), Set.mem_Ioi.mpr hdrpos⟩ : ℝ) /
        (c ⟨(r : ℝ), Set.mem_Ioi.mpr hrpos⟩ : ℝ))) :=
    hA.div hB (ne_of_gt (c ⟨(r : ℝ), Set.mem_Ioi.mpr hrpos⟩).property)
  have hbound : ∀ᶠ n in atTop,
      C⁻¹ * (δ : ℝ) ^ ((ξ : ℝ) * Q + ζ) ≤ A n / B n ∧
      A n / B n ≤ C * (δ : ℝ) ^ ((ξ : ℝ) * Q - ζ) := by
    filter_upwards [hev] with n hn
    let e : Set.Ioo (0 : ℝ) (δ : ℝ) :=
      ⟨(ε (φ n) : ℝ) / (r : ℝ), div_pos (ε (φ n)).property hrpos,
        (div_lt_iff₀ hrpos).mpr hn⟩
    have hstep := hC ⟨(δ : ℝ), hδpos, hδ1⟩ e
    have he : (⟨(e : ℝ) / (δ : ℝ),
        Set.mem_Ioi.mpr (div_pos e.property.1 hδpos)⟩ : Set.Ioi (0 : ℝ)) =
        ⟨(ε (φ n) : ℝ) / (dr : ℝ),
          Set.mem_Ioi.mpr (div_pos (ε (φ n)).property hdrpos)⟩ := by
      apply Subtype.ext
      change ((ε (φ n) : ℝ) / (r : ℝ)) / (δ : ℝ) =
        (ε (φ n) : ℝ) / ((δ * r : ℚ) : ℝ)
      rw [Rat.cast_mul]
      field_simp
    have hcancel : A n / B n = (δ : ℝ) *
        (m ⟨(e : ℝ) / (δ : ℝ),
          Set.mem_Ioi.mpr (div_pos e.property.1 hδpos)⟩ : ℝ) /
          (m ⟨(e : ℝ), Set.mem_Ioi.mpr e.property.1⟩ : ℝ) := by
      simp only [A, B]
      have heA : (⟨(ε (φ n) : ℝ) / (dr : ℝ),
          Set.mem_Ioi.mpr (div_pos (ε (φ n)).property hdrpos)⟩ : Set.Ioi (0 : ℝ)) =
          ⟨(e : ℝ) / (δ : ℝ),
            Set.mem_Ioi.mpr (div_pos e.property.1 hδpos)⟩ := he.symm
      have heB : (⟨(ε (φ n) : ℝ) / (r : ℝ),
          Set.mem_Ioi.mpr (div_pos (ε (φ n)).property hrpos)⟩ : Set.Ioi (0 : ℝ)) =
          ⟨(e : ℝ), Set.mem_Ioi.mpr e.property.1⟩ := rfl
      rw [heA, heB]
      simpa only [dr, Rat.cast_mul] using normalized_ratio_cancel _ _ _ _ _ (ne_of_gt hrpos)
        (ne_of_gt (m ⟨(e : ℝ), Set.mem_Ioi.mpr e.property.1⟩).property)
        (ne_of_gt (m (ε (φ n))).property)
    rw [hcancel]
    exact hstep
  exact ⟨ge_of_tendsto hAB (hbound.mono fun n hn => hn.1),
    le_of_tendsto hAB (hbound.mono fun n hn => hn.2)⟩

end SupercriticalLQGUniqueness.B2.PfeAxioms
