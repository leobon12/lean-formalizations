import SupercriticalLQGUniqueness.B2.DG20Lim.PolarPointTightness

 

set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 
theorem exists_polar_point_upper_tail_of_section4
    (hS4 : B2.Iface.DG20Section4)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε))
    (A : EuclideanAnnulus) (η : ℝ) (hη : 0 < η) :
    ∃ z w : Fin 4 → ℂ, ∃ M : ℝ,
      (∀ j, z j ∈ B2.Strong.cfgSet₁ A j) ∧
      (∀ j, w j ∈ B2.Strong.cfgSet₂ A j) ∧
      0 < M ∧
      ∀ ε : Ioo (0 : ℝ) 1,
        P (⋃ j : Fin 4, {ω | ENNReal.ofReal M <
          ENNReal.ofReal ((m ⟨(ε : ℝ), ε.property.1⟩ : ℝ)⁻¹) *
            crossLenIn (ξ : ℝ) (X ⟨(ε : ℝ), ε.property.1⟩ ω)
              (B2.Strong.cfgOpens A j) {z j} {w j}}) ≤
          ENNReal.ofReal η := by
  obtain ⟨z, w, hz, hw, hT⟩ :=
    exists_polar_point_tightness_of_section4 hS4 ξ Q hQ m hm P h hh X hX A
  let δ : ℝ := η / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hEach (j : Fin 4) : ∃ T : ℝ, 0 < T ∧
      ∀ ε : Ioo (0 : ℝ) 1,
        P {ω | ENNReal.ofReal T <
          ENNReal.ofReal ((m ⟨(ε : ℝ), ε.property.1⟩ : ℝ)⁻¹) *
            crossLenIn (ξ : ℝ) (X ⟨(ε : ℝ), ε.property.1⟩ ω)
              (B2.Strong.cfgOpens A j) {z j} {w j}} ≤
          ENNReal.ofReal δ := by
    obtain ⟨T, hTpos, hTupper⟩ := (hT j).2 δ hδ
    exact ⟨T, hTpos, fun ε => (hTupper ε).1⟩
  choose T hTpos hTupper using hEach
  have hFin : (Finset.univ : Finset (Fin 4)).Nonempty :=
    ⟨0, Finset.mem_univ 0⟩
  let M : ℝ := (Finset.univ : Finset (Fin 4)).sup' hFin T + 1
  have hM : 0 < M := by
    have hle : T 0 ≤ (Finset.univ : Finset (Fin 4)).sup' hFin T :=
      Finset.le_sup' T (Finset.mem_univ 0)
    dsimp [M]
    linarith [hTpos 0]
  refine ⟨z, w, M, hz, hw, hM, ?_⟩
  intro ε
  let V : Fin 4 → Ω → ℝ≥0∞ := fun j ω =>
    ENNReal.ofReal ((m ⟨(ε : ℝ), ε.property.1⟩ : ℝ)⁻¹) *
      crossLenIn (ξ : ℝ) (X ⟨(ε : ℝ), ε.property.1⟩ ω)
        (B2.Strong.cfgOpens A j) {z j} {w j}
  have hProb (j : Fin 4) :
      P {ω | ENNReal.ofReal M < V j ω} ≤ ENNReal.ofReal δ := by
    have hj : T j ≤ M := by
      have := Finset.le_sup' T (Finset.mem_univ j : j ∈ (Finset.univ : Finset (Fin 4)))
      dsimp [M]
      linarith
    calc
      P {ω | ENNReal.ofReal M < V j ω}
          ≤ P {ω | ENNReal.ofReal (T j) < V j ω} := by
            apply measure_mono
            intro ω hω
            exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hj) hω
      _ ≤ ENNReal.ofReal δ := by simpa only [V] using hTupper j ε
  change P (⋃ j : Fin 4, {ω | ENNReal.ofReal M < V j ω}) ≤ ENNReal.ofReal η
  calc
    P (⋃ j : Fin 4, {ω | ENNReal.ofReal M < V j ω})
        ≤ ∑ j : Fin 4, P {ω | ENNReal.ofReal M < V j ω} :=
      measure_iUnion_fintype_le P _
    _ ≤ ∑ _j : Fin 4, ENNReal.ofReal δ :=
      Finset.sum_le_sum (fun j _ => hProb j)
    _ = ENNReal.ofReal η := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg (Fintype.card (Fin 4)))]
      congr 1
      simp only [Fintype.card_fin, δ]
      ring

end SupercriticalLQGUniqueness.B2.DG20Lim
