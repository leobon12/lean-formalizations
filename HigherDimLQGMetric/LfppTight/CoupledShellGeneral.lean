import HigherDimLQGMetric.LfppTight.CoupledShellTail

/-! Nondegenerate coupled crossings for every fixed Euclidean shell. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd WN bandVecM)

theorem l6a_coupled_shell_tail_general {d : ℕ} {κ : Rd d → ℝ} {ξ Q β : ℝ}
    (hDGZ : DGZ.DGZHyp d κ ξ Q)
    (hAdapter : DGZ.RealEpsAdapterShape d κ ξ Q)
    (hβ0 : 0 < β) (hβ : β < ξ * (Q - Real.sqrt (2 * d)))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : WN d → Ω → ℝ) (hW : HigherDimLFPP.IsWhiteNoise P W)
    (G : ℝ → Rd d → Ω → ℝ)
    (hG : ∀ ε ∈ Ioo (0 : ℝ) 1, HigherDimLFPP.IsBandVersion P W κ ε 1 (G ε))
    (Ψ : Rd d → Ω → ℝ) (hΨc : ∀ ω, Continuous fun z => Ψ z ω)
    (hΨm : ∀ z, Measurable (Ψ z))
    (c : Rd d) {r₁ r₂ θ : ℝ} (hr₂ : 0 < r₂) (hr : r₂ < r₁) (hθ : 0 < θ) :
    ∃ m ε₀ : ℝ, 0 < m ∧ 0 < ε₀ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₀,
      P {ω | DGZ.lfppSetDist ξ
        (fun z => G ε z ω -
          W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω + Ψ z ω)
        univ (sphere c r₂) (sphere c r₁) ≤
          m * DGZ.aHat P G ξ ε} ≤ ENNReal.ofReal θ := by
  have hq : 0 < θ / 3 := by positivity
  obtain ⟨_, hLower, _, _⟩ := hAdapter hDGZ β hβ0 hβ Ω P W G hW hG
  obtain ⟨δ, hδ, εc, hεc, hCross⟩ := hLower c r₁ r₂ (θ / 3) hr₂ hr hq
  obtain ⟨C, hC0, hC⟩ := l6a_uniform_sphereBand_tail_at hDGZ.dim
    hDGZ.kernel P W hW hq
  let R : ℝ := ‖c‖ + r₁ + 1
  have hR : 0 < R := by dsimp [R]; have := norm_nonneg c; linarith
  obtain ⟨L, hL0, hL⟩ := l6a_exists_highField_sup_tail P Ψ hΨc hΨm hq
    (R := R)
  let F : ℝ := Real.exp (|ξ| * (C + L))
  let m : ℝ := δ / F
  let ε₀ : ℝ := min εc (1 / 2)
  have hF : 0 < F := Real.exp_pos _
  have hm : 0 < m := div_pos hδ hF
  have hε₀ : 0 < ε₀ := lt_min hεc (by norm_num)
  refine ⟨m, ε₀, hm, hε₀, ?_⟩
  intro ε hε
  have hε1 : ε ∈ Ioo (0 : ℝ) 1 :=
    ⟨hε.1, hε.2.trans_le ((min_le_right _ _).trans (by norm_num))⟩
  have hεc' : ε ∈ Ioo (0 : ℝ) εc :=
    ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩
  let E₁ : Set Ω := {ω | DGZ.lfppSetDist ξ (fun z => G ε z ω) univ
    (sphere c r₂) (sphere c r₁) ≤ δ * DGZ.aHat P G ξ ε}
  let E₂ : Set Ω := {ω | C < |W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω|}
  let E₃ : Set Ω := {ω | L < l6a_highNorm Ψ hΨc R ω}
  have hsub : {ω | DGZ.lfppSetDist ξ
        (fun z => G ε z ω -
          W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω + Ψ z ω)
        univ (sphere c r₂) (sphere c r₁) ≤
          m * DGZ.aHat P G ξ ε} ⊆ E₁ ∪ E₂ ∪ E₃ := by
    intro ω hw
    by_contra hn
    have hno₁ : ω ∉ E₁ := fun h => hn (Or.inl (Or.inl h))
    have hno₂ : ω ∉ E₂ := fun h => hn (Or.inl (Or.inr h))
    have hno₃ : ω ∉ E₃ := fun h => hn (Or.inr h)
    have hH : Continuous (fun z => G ε z ω) := (hG ε hε1).continuous ω
    have hc : |W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω| ≤ C :=
      le_of_not_gt hno₂
    have hl : ∀ z ∈ closedBall c r₁, |Ψ z ω| ≤ L := by
      intro z hz
      have hzc : ‖z‖ ≤ ‖c‖ + r₁ := by
        have hh := norm_le_insert' z c
        have hdist : ‖z - c‖ ≤ r₁ := by
          simpa only [mem_closedBall, dist_eq_norm] using hz
        linarith
      have hzR : z ∈ closedBall (0 : Rd d) R := by
        rw [mem_closedBall, dist_zero_right]
        dsimp [R]
        linarith
      exact (l6a_abs_highField_le_norm Ψ hΨc R ω hzR).trans
        (le_of_not_gt hno₃)
    have hcomp := l6a_coupled_shell_lower ξ
      (W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω) C L
      (fun z => G ε z ω) (fun z => Ψ z ω) hH (hΨc ω)
      (x := c) (r₁ := r₁) (r₂ := r₂) hr hc hl
    have hbad : DGZ.lfppSetDist ξ (fun z => G ε z ω) univ
        (sphere c r₂) (sphere c r₁) ≤ δ * DGZ.aHat P G ξ ε := by
      calc
        _ ≤ F * DGZ.lfppSetDist ξ
          (fun z => G ε z ω -
            W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω + Ψ z ω)
          univ (sphere c r₂) (sphere c r₁) := hcomp
        _ ≤ F * (m * DGZ.aHat P G ξ ε) :=
          mul_le_mul_of_nonneg_left hw hF.le
        _ = δ * DGZ.aHat P G ξ ε := by
          dsimp [m, F]
          field_simp [Real.exp_ne_zero]
    exact hno₁ hbad
  have h1 : P E₁ ≤ ENNReal.ofReal (θ / 3) := hCross ε hεc'
  have h2 : P E₂ ≤ ENNReal.ofReal (θ / 3) := hC ε hε1
  have h3 : P E₃ ≤ ENNReal.ofReal (θ / 3) := hL
  calc
    P {ω | DGZ.lfppSetDist ξ
        (fun z => G ε z ω -
          W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω + Ψ z ω)
        univ (sphere c r₂) (sphere c r₁) ≤
          m * DGZ.aHat P G ξ ε} ≤ P (E₁ ∪ E₂ ∪ E₃) := measure_mono hsub
    _ ≤ P E₁ + P E₂ + P E₃ := by
      calc
        P (E₁ ∪ E₂ ∪ E₃) ≤ P (E₁ ∪ E₂) + P E₃ := measure_union_le _ _
        _ ≤ (P E₁ + P E₂) + P E₃ := by gcongr; exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (θ / 3) + ENNReal.ofReal (θ / 3) +
          ENNReal.ofReal (θ / 3) := by gcongr
    _ = ENNReal.ofReal θ := by
      rw [← ENNReal.ofReal_add hq.le hq.le,
        ← ENNReal.ofReal_add (add_nonneg hq.le hq.le) hq.le]
      congr 1
      ring

end HigherDimLQGMetric
