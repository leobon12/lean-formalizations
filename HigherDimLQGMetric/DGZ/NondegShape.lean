import HigherDimLQGMetric.DGZ.NondegTranslate

/-! DGZ Proposition 6.4: normalized crossings of every box shell stay away from zero. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (obox)

variable {d : ℕ}

theorem nondegShape (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ) :
    NondegShape d κ ξ Q := by
  intro h c r₁ r₂ hr₂ hr θ hθ
  have hd0 : 0 < d := by have hh := h.dim; omega
  let ρ : ℝ := min ((r₁ - r₂) / 8) (1 / (10 * Real.sqrt d + 4))
  have hρ : 0 < ρ := by
    dsimp [ρ]
    apply lt_min
    · positivity
    · positivity
  have hρgap : 2 * ρ ≤ (r₁ - r₂) / 2 := by
    have hh : ρ ≤ (r₁ - r₂) / 8 := min_le_left _ _
    linarith
  have hrd : ρ * (10 * Real.sqrt d) ≤ 1 := by
    have hh : ρ ≤ 1 / (10 * Real.sqrt d + 4) := min_le_right _ _
    have hs : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
    have hden : 0 < 10 * Real.sqrt d + 4 := by positivity
    have hmul := mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ 10 * Real.sqrt d)
    have hratio : (1 / (10 * Real.sqrt d + 4)) * (10 * Real.sqrt d) ≤ 1 := by
      calc
        (1 / (10 * Real.sqrt d + 4)) * (10 * Real.sqrt d) ≤
            (1 / (10 * Real.sqrt d + 4)) * (10 * Real.sqrt d + 4) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = 1 := by field_simp
    calc
      ρ * (10 * Real.sqrt d) ≤
          (1 / (10 * Real.sqrt d + 4)) * (10 * Real.sqrt d) := hmul
      _ ≤ 1 := hratio
  obtain ⟨Z, hZs, hZcov⟩ :=
    tn_exists_obox_cover (tn_isCompact_lsph c ((r₁ + r₂) / 2)) hρ
  have hZne : Z.Nonempty := by
    obtain ⟨p, hp⟩ := lsph_nonempty hd0 c (by linarith : 0 ≤ (r₁ + r₂) / 2)
    obtain ⟨g, hg, -⟩ := mem_iUnion₂.1 (hZcov hp)
    exact ⟨g, hg⟩
  let θw : ℝ := min θ 1
  have hθw0 : 0 < θw := lt_min hθ (by norm_num)
  have hθw1 : θw ≤ 1 := min_le_right _ _
  have hθwθ : θw ≤ θ := min_le_left _ _
  let b : ℝ := θw / (Z.card + 1)
  have hden : 0 < (Z.card : ℝ) + 1 := by positivity
  have hb0 : 0 < b := div_pos hθw0 hden
  have hb1 : b ≤ 1 := by
    dsimp [b]
    apply (div_le_iff₀ hden).2
    have hc : 0 ≤ (Z.card : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨δ, hδ, N, hsmall⟩ :=
    nd_smallShell_median_center h hρ hrd (θ := ENNReal.ofReal b)
      (ENNReal.ofReal_pos.mpr hb0) (by exact ENNReal.ofReal_le_one.mpr hb1)
  refine ⟨δ, hδ, N, ?_⟩
  intro Ω _ P W H hH n hn
  let E : Rd d → Set Ω := fun g =>
    {ω | acrossDist ξ (fun z => H n z ω) g (2 * ρ) ρ ≤ δ * aQ P H ξ n 2⁻¹}
  have hsub : {ω | acrossDist ξ (fun z => H n z ω) c r₁ r₂ ≤
      δ * aQ P H ξ n 2⁻¹} ⊆ {ω | ∃ g ∈ Z, ω ∈ E g} := by
    intro ω hω
    have hinf := nd_across_general_ge_inf (ξ := ξ) hd0 ((hH.band n).continuous ω)
      hr₂ hr hρ hρgap hZne hZs hZcov
    have hle : Z.inf' hZne (fun g => acrossDist ξ (fun z => H n z ω) g (2 * ρ) ρ) ≤
        δ * aQ P H ξ n 2⁻¹ := hinf.trans hω
    by_contra hc
    have hstrict : δ * aQ P H ξ n 2⁻¹ <
        Z.inf' hZne (fun g => acrossDist ξ (fun z => H n z ω) g (2 * ρ) ρ) :=
      (Finset.lt_inf'_iff hZne).2 (by
        intro g hg
        exact lt_of_not_ge (fun hgle => hc ⟨g, hg, hgle⟩))
    exact (not_lt_of_ge hle) hstrict
  have hbound : ∀ g ∈ Z, P (E g) ≤ ENNReal.ofReal b := by
    intro g _
    exact hsmall g Ω P W H hH n hn
  have hreal : (Z.card : ℝ) * b ≤ θw := by
    dsimp [b]
    have hratio : (Z.card : ℝ) / (Z.card + 1) ≤ 1 :=
      (div_le_iff₀ hden).2 (by linarith)
    calc
      (Z.card : ℝ) * (θw / (Z.card + 1)) =
          θw * ((Z.card : ℝ) / (Z.card + 1)) := by ring
      _ ≤ θw := by nlinarith [mul_le_mul_of_nonneg_left hratio hθw0.le]
  have hsum : (∑ g ∈ Z, ENNReal.ofReal b) ≤ ENNReal.ofReal θ := by
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [← ENNReal.ofReal_natCast,
      mul_comm (ENNReal.ofReal (Z.card : ℝ)) (ENNReal.ofReal b),
      ← ENNReal.ofReal_mul hb0.le]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [hreal, hθwθ])
  calc
    P {ω | acrossDist ξ (fun z => H n z ω) c r₁ r₂ ≤
        δ * aQ P H ξ n 2⁻¹} ≤ P {ω | ∃ g ∈ Z, ω ∈ E g} := measure_mono hsub
    _ = P (⋃ g ∈ Z, E g) := by congr 1; ext ω; simp
    _ ≤ ∑ g ∈ Z, P (E g) := measure_biUnion_finset_le Z E
    _ ≤ ∑ g ∈ Z, ENNReal.ofReal b := Finset.sum_le_sum hbound
    _ ≤ ENNReal.ofReal θ := hsum

end HigherDimLQGMetric.DGZ
