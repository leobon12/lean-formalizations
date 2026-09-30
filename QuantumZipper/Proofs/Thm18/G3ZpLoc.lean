import QuantumZipper.Proofs.Thm18.G3Z2b2Mz
import QuantumZipper.Proofs.Thm18.G3G2LocZoom
import QuantumZipper.Proofs.Thm18.G3AreaCore
import QuantumZipper.Proofs.Thm18.G2ZoomLoc

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Z-PARTNER (2): locality of the zooms through the local maps

The map version of the deterministic zoom locality `zoomLaw_mem_lawCyl_iff` (G3G2LocZoom), for
the measurable zoom datum `g3zoomLawM` read by the fixed-path functional `g3PhiM2` of
`G3ZpPathStmt` (G3ZpFub).

* `canonOfCoords_mem_lawCyl_iff`: the canonical description rebuilt from circle coordinates
  depends, on a cylinder event, only on the coordinates of the dyadic folded circles inside a
  region `V ⊇ closedBall 0 (q₀ R) ∩ Hbar`, once the rebuilt field has unit area in the `q₀`-ball.
* `g3coordsM_eq_of_circAgree`: the coordinates of the zoom through the local map of two fields
  that agree on the dyadic circles inside an open set `W` coincide on every folded circle whose
  image under the local map lies in a compact subset of `W`.
* `g3zoomLawM_mem_iff_of_agree`: hence the zoom events of the two fields through the same local
  map coincide.

This is the locality used in Sheffield's conditioning argument (arXiv:1012.4797, proof of Thm 1.8,
p. 71: the zoomed-in figure near `x` only depends on the field inside `B¹`), for zooms through the
local maps. Own elementary proof (AGENT_GUIDE cost rule), following `zoomLaw_mem_lawCyl_iff`.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G3Zp

open Prop16Area.G Factorization G3Z2b2

/-- **Locality of the canonical description rebuilt from coordinates.** -/
theorem canonOfCoords_mem_lawCyl_iff {s : Set LawD} (hs : s ∈ lawCyl) : ∃ R : ℝ, 1 ≤ R ∧
    ∀ (γ : ℝ) (c c' : ℕ → ℝ) (V : Set ℂ), IsOpen V →
    (∀ (i : ℕ) (d : ℂ) (r : ℝ), d ∈ Hbar → 0 < r → closedBall d r ∩ Hbar ⊆ V →
      foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2) = foldedCircle d r → c i = c' i) →
    ∀ q₀ : ℚ, 0 < (q₀ : ℝ) → closedBall (0 : ℂ) (q₀ * R) ∩ Hbar ⊆ V →
      1 ≤ areaProxy γ (reconstruct c') q₀ →
      (lawOf (canonOfCoords γ c) ∈ s ↔ lawOf (canonOfCoords γ c') ∈ s) := by
  obtain ⟨R, hR, hRs⟩ := exists_radius_lawCyl hs
  refine ⟨R, hR, fun γ c c' V hVo hc q₀ hq₀ hV h1 => ?_⟩
  have hCA : CircAgree V (reconstruct c) (reconstruct c') := by
    classical
    intro n k z hz hW
    obtain ⟨i, hi⟩ := dyadicIndex_surj n k z
    have h : ∃ j, foldedCircle (dyadicIndex j).1 (radius (dyadicIndex j).2) =
        foldedCircle (dyadicRoundC n z) (radius k) := ⟨i, by rw [hi]⟩
    unfold reconstruct
    rw [dif_pos h, dif_pos h]
    exact hc _ _ _ (CircleCont.dyadicRoundC_mem_Hbar hz n) (radius_pos k) hW
      (by convert Nat.find_spec h)
  have hq₀R : (q₀ : ℝ) ≤ q₀ * R := le_mul_of_one_le_right hq₀.le hR
  obtain ⟨ha, haq⟩ := scaleProxy_congr γ hVo hCA hq₀
    (fun u hu => hV ⟨closedBall_subset_closedBall hq₀R hu.1, hu.2⟩) h1
  unfold canonOfCoords
  rw [ha]
  refine hRs _ _ fun μ hμ =>
    rescale_apply_congr hVo hCA _ (scaleProxy_nonneg γ _) (R := R) ?_ hμ
  intro u hu
  exact hV ⟨closedBall_subset_closedBall
    (mul_le_mul_of_nonneg_right haq (by linarith)) hu.1, hu.2⟩

/-- **The coordinates of the zoom through the local map are local.** If the translated fields
agree on the dyadic circles inside the open set `W`, the coordinates of the zooms through the
same local map agree at every folded circle whose image lies in a compact subset of `W`. -/
theorem g3coordsM_eq_of_circAgree {γ L : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} {left : Bool}
    {y y' : FieldSample} {a : ℝ≥0 → ℝ} {b x : ℝ} {W : Set ℂ} (hWo : IsOpen W)
    (hag : CircAgree W (translate y (x : ℂ)) (translate y' (x : ℂ))) (i : ℕ)
    {K : Set ℂ} (hK : IsCompact K) (hKW : K ⊆ W)
    (hsupp : ∀ᵐ u ∂((G3Z2b2.fcI i).map (g3mapP Ψ left (y, a, b, x))), u ∈ K ∩ Hbar) :
    g3coordsM γ L Ψ left (y, a, b, x) i = g3coordsM γ L Ψ left (y', a, b, x) i := by
  unfold g3coordsM
  dsimp only
  rw [evalReg_eq_of_circAgree hWo hag hK hKW hsupp]
  rfl

/-- **Locality of the zoom events through the local map.** Two fields that agree near `x` (on
the dyadic circles of the translated fields inside `W`) have the same cylinder zoom events through
the local map, provided every folded circle inside `V ⊇ closedBall 0 (q₀ R) ∩ Hbar` is carried by
the map into a compact subset of `W` and the second zoom has unit area in the `q₀`-ball. -/
theorem g3zoomLawM_mem_iff_of_agree {s : Set LawD} (hs : s ∈ lawCyl) : ∃ R : ℝ, 1 ≤ R ∧
    ∀ (γ L : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool) (y y' : FieldSample)
      (a : ℝ≥0 → ℝ) (b x : ℝ) (W V : Set ℂ), IsOpen W → IsOpen V →
      CircAgree W (translate y (x : ℂ)) (translate y' (x : ℂ)) →
      (∀ (d : ℂ) (r : ℝ), d ∈ Hbar → 0 < r → closedBall d r ∩ Hbar ⊆ V → ∃ K : Set ℂ, IsCompact K ∧
        K ⊆ W ∧ ∀ᵐ u ∂((foldedCircle d r).map (g3mapP Ψ left (y, a, b, x))), u ∈ K ∩ Hbar) →
      ∀ q₀ : ℚ, 0 < (q₀ : ℝ) → closedBall (0 : ℂ) (q₀ * R) ∩ Hbar ⊆ V →
      1 ≤ areaProxy γ (reconstruct (g3coordsM γ L Ψ left (y', a, b, x))) q₀ →
      (g3zoomLawM γ L Ψ left (y, a, b, x) ∈ s ↔ g3zoomLawM γ L Ψ left (y', a, b, x) ∈ s) := by
  obtain ⟨R, hR, H⟩ := canonOfCoords_mem_lawCyl_iff hs
  refine ⟨R, hR, fun γ L Ψ left y y' a b x W V hWo hVo hag hmapK q₀ hq₀ hV h1 => ?_⟩
  unfold g3zoomLawM
  refine H γ _ _ V hVo (fun i d r hd hr hdr he => ?_) q₀ hq₀ hV h1
  obtain ⟨K, hK, hKW, hsupp⟩ := hmapK d r hd hr hdr
  refine g3coordsM_eq_of_circAgree hWo hag i hK hKW ?_
  rw [show G3Z2b2.fcI i = foldedCircle d r from he]
  exact hsupp

/-- Adding a constant to the coordinates adds it to the rebuilt field (circle averages). -/
theorem avgReg_reconstruct_add_const (c : ℕ → ℝ) (k : ℝ) :
    avgReg (reconstruct fun j => c j + k) = avgReg (addConst (reconstruct c) k) := by
  classical
  funext n' z
  unfold avgReg
  congr 1
  funext n
  obtain ⟨i, hi⟩ := dyadicIndex_surj n n' z
  have h : ∃ j, foldedCircle (dyadicIndex j).1 (radius (dyadicIndex j).2) =
      foldedCircle (dyadicRoundC n z) (radius n') := ⟨i, by rw [hi]⟩
  have e1 : reconstruct (fun j => c j + k) (foldedCircle (dyadicRoundC n z) (radius n')) =
      c (Nat.find h) + k := by
    unfold reconstruct; rw [dif_pos h]
  have e2 : reconstruct c (foldedCircle (dyadicRoundC n z) (radius n')) = c (Nat.find h) := by
    unfold reconstruct; rw [dif_pos h]
  rw [e1]
  simp [addConst, measure_univ, e2]

/-- The coordinates at level `L` are those at level `0` plus `L / γ`. -/
theorem g3coordsM_level {γ L : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} {left : Bool} (p : G3Par) :
    g3coordsM γ L Ψ left p = fun i => g3coordsM γ 0 Ψ left p i + L / γ := by
  funext i
  simp only [g3coordsM, zero_div, add_zero]

/-- **The support condition for a map with a continuous extension up to the boundary.** If
the measurable map `ψ` agrees on `closedBall 0 ρ ∩ H` with a map `Φ` continuous on
`closedBall 0 ρ ∩ Hbar`, mapping it into `Hbar` and fixing `0`, then every folded circle inside a
small enough ball is carried by `ψ` into a compact subset of a given neighbourhood `W` of `0`. -/
theorem exists_small_of_ext {ψ Φ : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hc : ContinuousOn Φ (closedBall 0 ρ ∩ Hbar)) (hmt : MapsTo Φ (closedBall 0 ρ ∩ Hbar) Hbar)
    (heq : EqOn ψ Φ (closedBall 0 ρ ∩ H)) (hm : Measurable ψ) (h0 : Φ 0 = 0) {W : Set ℂ}
    (hWo : IsOpen W) (hW0 : (0 : ℂ) ∈ W) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ∀ (d : ℂ) (r : ℝ), d ∈ Hbar → 0 < r → closedBall d r ∩ Hbar ⊆ ball 0 ρ' →
      ∃ K : Set ℂ, IsCompact K ∧ K ⊆ W ∧ ∀ᵐ u ∂((foldedCircle d r).map ψ), u ∈ K ∩ Hbar := by
  set S := closedBall (0 : ℂ) ρ ∩ Hbar with hS
  have h0S : (0 : ℂ) ∈ S := ⟨mem_closedBall_self hρ.le, by simp [Hbar]⟩
  have hcw : ContinuousWithinAt Φ S 0 := hc 0 h0S
  have hpre : Φ ⁻¹' W ∈ 𝓝[S] (0 : ℂ) := hcw.preimage_mem_nhdsWithin (by
    rw [h0]; exact hWo.mem_nhds hW0)
  obtain ⟨ε, hε, hεS⟩ := Metric.mem_nhdsWithin_iff.1 hpre
  refine ⟨min ε ρ, lt_min hε hρ, fun d r hd hr hsub => ?_⟩
  set C := closedBall d r ∩ Hbar with hC
  have hCS : C ⊆ S := fun u hu => ⟨ball_subset_closedBall (ball_subset_ball (min_le_right _ _)
    (hsub hu)), hu.2⟩
  have hCW : C ⊆ Φ ⁻¹' W := fun u hu =>
    hεS ⟨ball_subset_ball (min_le_left _ _) (hsub hu), hCS hu⟩
  have hCc : IsCompact C := (isCompact_closedBall d r).inter_right isClosed_Hbar
  have hKc : IsCompact (Φ '' C) := hCc.image_of_continuousOn (hc.mono hCS)
  refine ⟨Φ '' C, hKc, fun v ⟨u, hu, hv⟩ => hv ▸ hCW hu, ?_⟩
  have hKm : MeasurableSet (Φ '' C ∩ Hbar) := (hKc.isClosed.inter isClosed_Hbar).measurableSet
  refine (ae_map_iff (p := fun u => u ∈ Φ '' C ∩ Hbar) hm.aemeasurable hKm).2 ?_
  filter_upwards [foldedCircle_ae_dist_le_zl hd hr.le, TwoPoint.foldedCircle_ae_mem_H d hr]
    with u hu huH
  have huC : u ∈ C := ⟨by rw [mem_closedBall]; exact hu, H_subset_Hbar huH⟩
  rw [heq ⟨(hCS huC).1, huH⟩]
  exact ⟨mem_image_of_mem Φ huC, hmt (hCS huC)⟩

end G3Zp
end Thm18Asm
end QuantumZipper
