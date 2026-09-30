import QuantumZipper.Proofs.Thm18.G1A1b2Int
import QuantumZipper.Proofs.Thm18.A1RCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1R (nodes): the last G1 A1b node with the contact region cut off (D90)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, proof of Theorem 1.8,
pp. 69–71 (the side surface of `Z_{−ℓ} c` is the rerooted side surface of `c`; coordinate change
(1.3)). Decision D90 (DECISIONS.md): in the regularized model the identity is the exactness of
the unzipped field `U_t = coordChange Y f_t⁻¹ Q` at the pushed side circles
`μ = (f_t ∘ ψ)_* fc(d, s)`; it cannot be removed by a definition change (the law input would be
rerooting invariance itself). The contact region — the points of `μ` within `√ρ` of `ℝ`, where
the smoothing circles of radius `ρ` may meet the unzipped segment `f_t(η[0,t])` — is cut off and
controlled by "log growth × small mass", as in RT2 (`R18.maskPullCoreStmt_of_growth_mass`;
Berestycki–Powell arXiv:2404.16642, Thm 8.16, Rem 8.10 p. 283; Hu–Miller–Peres, Ann. Probab. 38
(2010), Prop. 2.1; Beurling estimate, Lawler arXiv:0712.3256, Thm 2.10 p. 18).

* **`g1A1b2SideTendstoStmt_of_cut`**: `A1RMassStmt → A1RGrowthStmt → A1RFarStmt →
  G1A1b2SideTendstoStmt`.

Open inputs (each strictly smaller than `G1A1b2SideTendstoStmt`):
* `A1RMassStmt` (deterministic, Beurling): for a good driver the pushed side circles give mass
  `O(δ^β)` to the strip `{Im z ≤ δ}`;
* `A1RGrowthStmt` (log growth of circle averages of the unzipped field near `ℝ`, Hu–Miller–Peres
  Prop. 2.1 in the unzipped picture);
* `A1RFarStmt` (the smoothing limit over the part of `μ` at height `> √ρ`: smoothing circles that
  never meet `ℝ`, so no contact moduli).

Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- The pushed side circle `(f_t ∘ ψ)_* fc(d, s)`. -/
def a1rMu (W : ℝ → ℝ) (t : ℝ) (left : Bool) (d : ℂ) (s : ℝ) : Measure ℂ :=
  (foldedCircle d s).map fun w => fwdMap W t (g1zSideMap left W w)

/-- The contact region at smoothing radius `ρ`: height at most `√ρ`. -/
def a1rNear (ρ : ℝ) : Set ℂ := {z : ℂ | z.im ≤ Real.sqrt ρ}

/-- **Mass node (deterministic; Beurling estimate).** For a good driver, every pushed side circle
gives mass `O(δ^β)` (some `β > 0`) to the strip `{Im z ≤ δ}`. -/
def A1RMassStmt : Prop :=
  ∀ W : ℝ → ℝ, G1zDrvGood W → ∀ t : ℝ, 0 < t → ∀ left : Bool, ∀ d ∈ Hbar, ∀ s : ℝ, 0 < s →
    ∃ Cm β : ℝ, 0 < β ∧ ∀ δ : ℝ, 0 < δ → δ < 1 →
      (a1rMu W t left d s).real {z : ℂ | z.im ≤ δ} ≤ Cm * δ ^ β

namespace A1R

theorem measurableSet_a1rNear (ρ : ℝ) : MeasurableSet (a1rNear ρ) :=
  (isClosed_le Complex.continuous_im continuous_const).measurableSet

/-- The pushed side circles live on a bounded subset of `ℍ̄` (the support part of
`G1A1b.integrable_sideFamily`). -/
theorem exists_ae_bdd_a1rMu {W : ℝ → ℝ} (hG : G1zDrvGood W) {t : ℝ} (ht : 0 < t)
    (left : Bool) (d : ℂ) {s : ℝ} (hs : 0 < s) :
    ∃ Rr : ℝ, ∀ᵐ z ∂a1rMu W t left d s, z ∈ Hbar ∧ ‖z‖ ≤ Rr := by
  obtain ⟨hWc, hW0, hWm, hη, hK⟩ := hG
  set D := sideDom (trace W) left with hD
  have hU := G1ZA1a.isNormalizedUniformizer_sideDom hη left
  obtain ⟨-, -, hψm, hmaps⟩ := G1.invFunOn_props (G1ZA1a.isOpen_sideDom hη left) hU
  set h : ℂ → ℂ := fun w => fwdMap W t (g1zSideMap left W w) with hh
  obtain ⟨R', hR'⟩ := G1A1b.exists_bound_invFunOn hU (‖d‖ + s)
  obtain ⟨C, hC⟩ := G1ZA1a.exists_bound_fwdMapInv ⟨hWc, hW0, hWm, hη, hK⟩ ht
  refine ⟨R' + C, ?_⟩
  have hpt : ∀ w ∈ H, ‖w‖ ≤ ‖d‖ + s → h w ∈ Hbar ∧ ‖h w‖ ≤ R' + C := by
    intro w hw hwR
    set z := g1zSideMap left W w with hz
    have hzD : z ∈ D := hmaps hw
    have hzH : z ∈ H := G1ZA1a.sideDom_subset_H _ left hzD
    have hzK : z ∉ fwdHull W t := by
      rw [hK t ht.le]
      rintro ⟨u, hu, hzu⟩
      have hnot : z ∉ trace W '' Ici (0 : ℝ) := by
        cases left
        · exact hzD.1.2
        · exact hzD.1.2
      exact hnot ⟨u, le_of_lt hu.1, hzu⟩
    have hv : fwdMap W t z ∈ H := FwdHolo.mapsTo_fwdMap hWc ht.le ⟨hzH, hzK⟩
    have hinv : fwdMapInv W t (fwdMap W t z) = z := RS.fwdMapInv_fwdMap hWc hW0 ht.le ⟨hzH, hzK⟩
    have h1 := hC _ hv
    rw [hinv] at h1
    have h2 : ‖fwdMap W t z‖ ≤ ‖z‖ + C := by
      have := norm_sub_norm_le (fwdMap W t z) z
      rw [norm_sub_rev] at h1
      linarith
    refine ⟨show 0 ≤ (h w).im from le_of_lt hv, ?_⟩
    have h3 : ‖z‖ ≤ R' := hR' w hw hwR
    have h4 : h w = fwdMap W t z := rfl
    rw [h4]
    linarith
  -- measurability of the pushing map (continuous on the open complement of the hull)
  have hm : AEMeasurable h (foldedCircle d s) := by
    classical
    set U := H \ fwdHull W t with hUdef
    have hUo : IsOpen U := FwdHolo.isOpen_compl_fwdHull hWc ht.le
    have hgm : Measurable (U.piecewise (fwdMap W t) fun _ => (0 : ℂ)) :=
      ContinuousOn.measurable_piecewise (FwdHolo.differentiableOn_fwdMap hWc ht.le).continuousOn
        continuousOn_const hUo.measurableSet
    refine (hgm.comp hψm).aemeasurable.congr ?_
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hs] with w hw
    have hzD : g1zSideMap left W w ∈ D := hmaps hw
    have hzU : g1zSideMap left W w ∈ U := by
      refine ⟨G1ZA1a.sideDom_subset_H _ left hzD, ?_⟩
      rw [hK t ht.le]
      rintro ⟨u, hu, hzu⟩
      have hnot : g1zSideMap left W w ∉ trace W '' Ici (0 : ℝ) := by
        cases left
        · exact hzD.1.2
        · exact hzD.1.2
      exact hnot ⟨u, le_of_lt hu.1, hzu⟩
    show U.piecewise (fwdMap W t) (fun _ => (0 : ℂ)) (g1zSideMap left W w) = h w
    rw [Set.piecewise_eq_of_mem _ _ _ hzU]
  have hKm : MeasurableSet (Hbar ∩ Metric.closedBall (0 : ℂ) (R' + C)) :=
    ((isClosed_le continuous_const Complex.continuous_im).inter
      Metric.isClosed_closedBall).measurableSet
  have hae : ∀ᵐ z ∂a1rMu W t left d s, z ∈ Hbar ∩ Metric.closedBall (0 : ℂ) (R' + C) := by
    refine (ae_map_iff hm hKm).2 ?_
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hs,
      TwoPoint.foldedCircle_ae_norm_le d hs.le] with w hw hwn
    obtain ⟨h1, h2⟩ := hpt w hw hwn
    exact ⟨h1, by rw [Metric.mem_closedBall, dist_zero_right]; exact h2⟩
  filter_upwards [hae] with z hz
  exact ⟨hz.1, by simpa [Metric.mem_closedBall, dist_zero_right] using hz.2⟩

/-- `√ρ ^ β = ρ ^ (β / 2)`. -/
theorem sqrt_rpow_eq {ρ : ℝ} (hρ : 0 ≤ ρ) (β : ℝ) : Real.sqrt ρ ^ β = ρ ^ (β / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hρ]
  ring_nf

end A1R

end R18
end QuantumZipper
