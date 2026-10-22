import HigherDimLQGContinuity.MomentsW1.FieldCosts

/-! The localized chain applied to fine-field statuses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open MeasureTheory Set HigherDimLFPP HigherDimLFPP.Perc
open scoped ENNReal
open HigherDimLFPP.DGZ (latPt obox cbox)
open HigherDimLQGMetric.DGZ

variable {d : ℕ}

theorem wnCube_chain {κ : Rd d → ℝ} (hd : 2 ≤ d)
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {ξ R Q CZ : ℝ} (hξ : 0 ≤ ξ)
    {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1)
    {n : ℕ} {ω : Ω} (hfinite : wnZRext (d := d) R Q CZ H ω ≠ ⊤)
    {w : Rd d} (hw : w ∈ cbox (0 : Rd d) (R+1))
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    (∀ j : ℕ, wnBadScale P H ξ R q n ω ≤ j →
      chainDelta j ≤ ρ/100 → j ≤ n →
      selfDiam ξ (fun u => H n u ω) w ρ ≤
        (2*ρ*(2 : ℝ)^j+2)*(2*(2011:ℝ)^d+4004*Real.sqrt d)*
          wnLocalChain_sum d j n (wnEdgeCost P H ξ R Q CZ q n ω)
            (wnSegmentCost H ξ R Q CZ n ω)) ∧
      selfDiam ξ (fun u => H n u ω) w ρ ≤
        2*Real.sqrt (d:ℝ)*ρ*wnSegmentCost H ξ R Q CZ n ω := by
  let M : ℕ := wnBadScale P H ξ R q n ω
  let c : ℕ → ℝ := wnEdgeCost P H ξ R Q CZ q n ω
  let e : ℝ := wnSegmentCost H ξ R Q CZ n ω
  have hM : 110 ≤ M := by dsimp [M, wnBadScale]; exact le_max_left _ _
  have hφ : Continuous (fun u => H n u ω) := (hH.band n).continuous ω
  have hbox : obox w ρ ⊆ cbox (0 : Rd d) (R+5) :=
    wnBox_subset_coarse hρ hρ1 hw
  have he : ∀ u ∈ obox w ρ, Real.exp (ξ*H n u ω) ≤ e := by
    intro u hu
    exact wnSeg_cost hH hξ hfinite (hbox hu)
  have hseg := wnLocalChain_diameter_segment hφ w hρ he
  refine ⟨?_, hseg⟩
  intro j hMj hδj hjn
  have hE : ∀ k, M ≤ k → k < n → SmallClusters
      (wnGood P H ξ R q k n ω) (wnBadDiameter k) := by
    intro k hMk hkn
    exact (wnBadScale_small (hM.trans hMk) hkn hMk).1
  have hF : ∀ k, M ≤ k → k < n → ∀ x : Zd d, ∃ y : Zd d,
      WithinInf ((k:ℤ)^2) x (2 • y) ∧
      FreeSite (wnGood P H ξ R q k n ω) (2 • y) ∧
      FreeSite (wnGood P H ξ R q (k-1) n ω) y := by
    intro k hMk hkn x
    exact wnBadScale_free hd (hM.trans hMk) hkn hMk x
  have hc : ∀ k, M ≤ k → k < n → 0 ≤ c k := by
    intro k _ _
    dsimp [c, wnEdgeCost]
    have ha : 0 ≤ aQ P H ξ (n-k) q :=
      (tight_aQ_pos (by omega : 0 < d) hH ξ (n-k) hq0 hq1).le
    positivity
  have hcost : ∀ k, M ≤ k → k < n → ∀ z ∈ wnGood P H ξ R q k n ω,
      obox (latPt ((2:ℝ)⁻¹ ^ k) z) (2*(2:ℝ)⁻¹ ^ k) ⊆ obox w ρ →
      ∀ z', LAdj z z' →
        lfppDistOn ξ (fun u => H n u ω)
          (obox (latPt ((2:ℝ)⁻¹ ^ k) z) (2*(2:ℝ)⁻¹ ^ k))
          (latPt ((2:ℝ)⁻¹ ^ k) z) (latPt ((2:ℝ)⁻¹ ^ k) z') ≤ c k := by
    intro k _ _ z hz hcell z' hadj
    exact wnGood_edge_cost hH hξ hfinite hz
      (wnBox_region hρ hρ1 hw hcell) (hcell.trans hbox) hadj
  have hchain := chain_selfInternal_loc hd hφ w hM hMj hjn hρ hδj hE hF hc hcost he
  exact hchain.2.1

end HigherDimLQGContinuity
