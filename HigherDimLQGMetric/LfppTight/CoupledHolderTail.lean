import HigherDimLQGMetric.LfppTight.CoupledProb
import HigherDimLQGMetric.DGZ.AdapterBasics

/-! A7(3): local Hölder tails for the explicitly coupled centered LFPP field. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd WN bandVecM)

theorem l6a_coupled_holder_tail {d : ℕ} {κ : Rd d → ℝ} {ξ Q β : ℝ}
    (hDGZ : DGZ.DGZHyp d κ ξ Q)
    (hAdapter : DGZ.RealEpsAdapterShape d κ ξ Q)
    (hβ0 : 0 < β) (hβ : β < ξ * (Q - Real.sqrt (2 * d)))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : WN d → Ω → ℝ) (hW : HigherDimLFPP.IsWhiteNoise P W)
    (G : ℝ → Rd d → Ω → ℝ)
    (hG : ∀ ε ∈ Ioo (0 : ℝ) 1, HigherDimLFPP.IsBandVersion P W κ ε 1 (G ε))
    (Ψ : Rd d → Ω → ℝ) (hΨc : ∀ ω, Continuous fun z => Ψ z ω)
    (hΨm : ∀ z, Measurable (Ψ z))
    {r θ : ℝ} (hr : 0 < r) (hθ : 0 < θ) :
    ∃ M ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₀,
      P {ω | ∃ x ∈ closedBall (0 : Rd d) r, ∃ y ∈ closedBall (0 : Rd d) r,
        M * DGZ.aHat P G ξ ε * ‖x - y‖ ^ β <
          DGZ.lfppMetric ξ (fun z => G ε z ω -
            W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω + Ψ z ω) x y} ≤
        ENNReal.ofReal θ := by
  let s : ℝ := r + 1
  have hs : 0 < s := by dsimp [s]; linarith
  have hrs : r < s := by dsimp [s]; linarith
  have hq : 0 < θ / 4 := by positivity
  obtain ⟨hHolderA, _, hConfinement, _⟩ :=
    hAdapter hDGZ β hβ0 hβ Ω P W G hW hG
  obtain ⟨B, hB⟩ := hHolderA s (θ / 4) hs hq
  obtain ⟨R, hsR, εc, hεc, hCross⟩ := hConfinement s (θ / 4) hs hq
  obtain ⟨C, hC0, hC⟩ := l6a_uniform_sphereBand_tail_at hDGZ.dim
    hDGZ.kernel P W hW hq
  obtain ⟨L, hL0, hL⟩ := l6a_exists_highField_sup_tail P Ψ hΨc hΨm hq
    (R := R)
  let M : ℝ := Real.exp (|ξ| * (C + L)) * B
  let ε₀ : ℝ := min εc (1 / 2)
  have hε₀ : 0 < ε₀ := lt_min hεc (by norm_num)
  refine ⟨M, ε₀, hε₀, ?_⟩
  intro ε hε
  have hε1 : ε ∈ Ioo (0 : ℝ) 1 :=
    ⟨hε.1, hε.2.trans_le ((min_le_right _ _).trans (by norm_num))⟩
  have hεhalf : ε ∈ Ioo (0 : ℝ) (1 / 2) :=
    ⟨hε.1, hε.2.trans_le (min_le_right _ _)⟩
  have hεc' : ε ∈ Ioo (0 : ℝ) εc :=
    ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩
  let E₁ : Set Ω := {ω | ∃ x ∈ closedBall (0 : Rd d) s,
    ∃ y ∈ closedBall (0 : Rd d) s,
      B * DGZ.aHat P G ξ ε * ‖x - y‖ ^ β <
        DGZ.lfppMetric ξ (fun z => G ε z ω) x y}
  let E₂ : Set Ω := {ω | DGZ.lfppSetDist ξ (fun z => G ε z ω) univ
      (sphere (0 : Rd d) s) (sphere 0 R) ≤
      ⨆ p : ball (0 : Rd d) s × ball (0 : Rd d) s,
        DGZ.lfppMetric ξ (fun z => G ε z ω) p.1 p.2}
  let E₃ : Set Ω := {ω | C < |W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω|}
  let E₄ : Set Ω := {ω | L < l6a_highNorm Ψ hΨc R ω}
  have hsub : {ω | ∃ x ∈ closedBall (0 : Rd d) r, ∃ y ∈ closedBall (0 : Rd d) r,
        M * DGZ.aHat P G ξ ε * ‖x - y‖ ^ β <
          DGZ.lfppMetric ξ (fun z => G ε z ω -
            W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω + Ψ z ω) x y} ⊆
      E₁ ∪ E₂ ∪ E₃ ∪ E₄ := by
    intro ω hbad
    obtain ⟨x, hx, y, hy, hxy⟩ := hbad
    by_contra hnot
    have hno₁ : ω ∉ E₁ := fun h => hnot (Or.inl (Or.inl (Or.inl h)))
    have hno₂ : ω ∉ E₂ := fun h => hnot (Or.inl (Or.inl (Or.inr h)))
    have hno₃ : ω ∉ E₃ := fun h => hnot (Or.inl (Or.inr h))
    have hno₄ : ω ∉ E₄ := fun h => hnot (Or.inr h)
    have hH : Continuous (fun z => G ε z ω) := (hG ε hε1).continuous ω
    have hholder : ∀ x ∈ closedBall (0 : Rd d) s,
        ∀ y ∈ closedBall (0 : Rd d) s,
          DGZ.lfppMetric ξ (fun z => G ε z ω) x y ≤
            B * DGZ.aHat P G ξ ε * ‖x - y‖ ^ β := by
      intro u hu v hv
      exact le_of_not_gt (fun h => hno₁ ⟨u, hu, v, hv, h⟩)
    have hgap : ¬ DGZ.lfppSetDist ξ (fun z => G ε z ω) univ
        (sphere (0 : Rd d) s) (sphere 0 R) ≤
        ⨆ p : ball (0 : Rd d) s × ball (0 : Rd d) s,
          DGZ.lfppMetric ξ (fun z => G ε z ω) p.1 p.2 := hno₂
    have hc : |W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω| ≤ C :=
      le_of_not_gt hno₃
    have hl : ∀ z ∈ ball (0 : Rd d) R, |Ψ z ω| ≤ L := by
      intro z hz
      exact (l6a_abs_highField_le_norm Ψ hΨc R ω
        (ball_subset_closedBall hz)).trans (le_of_not_gt hno₄)
    have hxs : x ∈ ball (0 : Rd d) s := by
      rw [mem_ball]
      exact lt_of_le_of_lt (mem_closedBall.1 hx) hrs
    have hys : y ∈ ball (0 : Rd d) s := by
      rw [mem_ball]
      exact lt_of_le_of_lt (mem_closedBall.1 hy) hrs
    have hdet := l6a_coupled_holder_on_gap ξ β (DGZ.aHat P G ξ ε) B C L
      (W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω)
      (fun z => G ε z ω) (fun z => Ψ z ω) hH (hΨc ω)
      hsR hgap hc hl hholder hxs hys
    have hdet' : DGZ.lfppMetric ξ (fun z => G ε z ω -
          W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω + Ψ z ω) x y ≤
        M * DGZ.aHat P G ξ ε * ‖x - y‖ ^ β := by
      simpa only [M, mul_assoc] using hdet
    exact not_lt_of_ge hdet' hxy
  have h1 : P E₁ ≤ ENNReal.ofReal (θ / 4) := hB ε (by simpa [one_div] using hεhalf)
  have h2 : P E₂ ≤ ENNReal.ofReal (θ / 4) := hCross ε hεc'
  have h3 : P E₃ ≤ ENNReal.ofReal (θ / 4) := hC ε hε1
  have h4 : P E₄ ≤ ENNReal.ofReal (θ / 4) := hL
  calc
    P {ω | ∃ x ∈ closedBall (0 : Rd d) r, ∃ y ∈ closedBall (0 : Rd d) r,
        M * DGZ.aHat P G ξ ε * ‖x - y‖ ^ β <
          DGZ.lfppMetric ξ (fun z => G ε z ω -
            W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω + Ψ z ω) x y} ≤
      P (E₁ ∪ E₂ ∪ E₃ ∪ E₄) := measure_mono hsub
    _ ≤ P E₁ + P E₂ + P E₃ + P E₄ := by
      calc
        P (E₁ ∪ E₂ ∪ E₃ ∪ E₄) ≤ P (E₁ ∪ E₂ ∪ E₃) + P E₄ :=
          measure_union_le _ _
        _ ≤ (P (E₁ ∪ E₂) + P E₃) + P E₄ := by gcongr; exact measure_union_le _ _
        _ ≤ (P E₁ + P E₂) + P E₃ + P E₄ := by gcongr; exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (θ / 4) + ENNReal.ofReal (θ / 4) +
          ENNReal.ofReal (θ / 4) + ENNReal.ofReal (θ / 4) := by
      gcongr
    _ = ENNReal.ofReal θ := by
      rw [← ENNReal.ofReal_add hq.le hq.le,
        ← ENNReal.ofReal_add (add_nonneg hq.le hq.le) hq.le,
        ← ENNReal.ofReal_add (add_nonneg (add_nonneg hq.le hq.le) hq.le) hq.le]
      congr 1
      ring

end HigherDimLQGMetric
