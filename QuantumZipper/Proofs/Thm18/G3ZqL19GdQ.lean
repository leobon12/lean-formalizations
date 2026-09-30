import QuantumZipper.Proofs.Thm18.G3ZqL17Head
import QuantumZipper.Proofs.Thm18.G3ZqL10Cert
import QuantumZipper.Proofs.GFF.CircleContinuity
import QuantumZipper.Proofs.Thm18.G3ZqL11Reg
import QuantumZipper.Proofs.Thm18.G3ZqTop
import QuantumZipper.Proofs.Thm18.G3ZqPath
import QuantumZipper.Proofs.Thm18.G3ZqFLeaf
import QuantumZipper.Proofs.Thm18.G3ZqG3LRegG
import QuantumZipper.Proofs.Thm18.G3ZqG3Unif

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH-LOC (19): area-only pulled-back goodness suffices for the ball locality

`R18.g3zMapGd` asks `IsLQGGood` (boundary clause included, the D89 obstruction) of the
pulled-back field. The ball locality of the map zoom (`R18.g3zMapZ_ballLocG`) only uses the area:
`g3zMapGdQ` replaces it by the rational local-area condition `LocAreaQ` (G3ZqL10Cert), and
`g3zMapZ_ballLocQ` proves ball locality under it (copy of `g3zMapZ_ballLocG` through
`g3zoomLawM_eventually_iff_ballQ`). `g3zMapGdQ_of_gd`: the old condition implies the new one.
Own bookkeeping (Sheffield, arXiv:1012.4797, proof of Prop. 5.5, p. 65).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G3ZqL

open Prop16Area.G Factorization G3Z2b2 G3Zp G3Zq LQGMeas LocalRule R18

/-- **Locality of the zoom events through a local map at large level, rational local-area
form.** -/
theorem g3zoomLawM_eventually_iff_ballQ {s : Set LawD} (hs : s ∈ lawCyl) {γ : ℝ} (hγ : 0 < γ)
    {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} {left : Bool} {y y' : FieldSample} {a : ℝ≥0 → ℝ} {b x : ℝ}
    {ε : ℝ} (hε : 0 < ε) (hag : CircAgree (ball 0 ε) (translate y (x : ℂ)) (translate y' (x : ℂ)))
    {ρ : ℝ} (hρ : 0 < ρ) {Φ : ℂ → ℂ} (hc : ContinuousOn Φ (closedBall 0 ρ ∩ Hbar))
    (hmt : MapsTo Φ (closedBall 0 ρ ∩ Hbar) Hbar)
    (heq : EqOn (g3mapP Ψ left (y, a, b, x)) Φ (closedBall 0 ρ ∩ H))
    (hm : Measurable (g3mapP Ψ left (y, a, b, x))) (h0 : Φ 0 = 0)
    (hloc : LocAreaQ γ (reconstruct (g3coordsM γ 0 Ψ left (y', a, b, x)))) :
    ∀ᶠ L in atTop,
      (g3zoomLawM γ L Ψ left (y, a, b, x) ∈ s ↔ g3zoomLawM γ L Ψ left (y', a, b, x) ∈ s) := by
  obtain ⟨R, hR, Hm⟩ := g3zoomLawM_mem_iff_of_agree hs
  obtain ⟨ρ', hρ', hK⟩ := exists_small_of_ext hρ hc hmt heq hm h0 isOpen_ball (mem_ball_self hε)
  obtain ⟨ρ₁, hρ₁, k₀, hraw, hpos⟩ := hloc
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  obtain ⟨q₀, hq₀, hq₀'⟩ := exists_rat_btwn (lt_min (div_pos hρ' hR0) hρ₁)
  have hq₀R : (q₀ : ℝ) * R < ρ' := by
    have := lt_of_lt_of_le hq₀' (min_le_left _ _)
    rwa [lt_div_iff₀ hR0] at this
  have hq₀ρ : (q₀ : ℝ) < ρ₁ := lt_of_lt_of_le hq₀' (min_le_right _ _)
  obtain ⟨n, v, hv, ht⟩ := hpos q₀ hq₀ hq₀ρ
  have hraw' : ∀ k : ℕ, k₀ ≤ k → ∀ z ∈ ball (0 : ℂ) q₀ ∩ H, ∃ l : ℝ, Tendsto
      (fun n => reconstruct (g3coordsM γ 0 Ψ left (y', a, b, x))
        (foldedCircle (dyadicRoundC n z) (radius k))) atTop (𝓝 l) := fun k hk z hz =>
    hraw k hk z ⟨ball_subset_ball hq₀ρ.le hz.1, hz.2⟩
  have hev := eventually_one_le_areaProxy_addConst_of_loc hγ hraw' hv ht
  have htL : Tendsto (fun L : ℝ => L / γ) atTop atTop := tendsto_id.atTop_div_const hγ
  filter_upwards [htL.eventually hev] with L hL
  refine Hm γ L Ψ left y y' a b x (ball 0 ε) (ball 0 ρ') isOpen_ball isOpen_ball
    hag hK q₀ hq₀ (fun u hu => mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hu.1) hq₀R)) ?_
  have e : areaProxy γ (reconstruct (g3coordsM γ L Ψ left (y', a, b, x))) q₀ =
      areaProxy γ (addConst (reconstruct (g3coordsM γ 0 Ψ left (y', a, b, x))) (L / γ)) q₀ := by
    rw [g3coordsM_level]
    unfold areaProxy LQGMeas.areaFun
    rw [Factorization.areaApprox_congr (avgReg_reconstruct_add_const _ _)]
  rw [e]
  exact hL

open Classical in
/-- Area-only pulled-back goodness (plain goodness off the side half-line). -/
def g3zMapGdQ (γ : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (side : Bool) (a : ℝ≥0 → ℝ)
    (y : FieldSample) (x : ℝ) : Prop :=
  if x ∈ g1SideHalf side then LocAreaQ γ (reconstruct (g3coordsM γ 0 Ψ side (y, a, 1, x)))
  else g3PlainGd γ y x

theorem locAreaQ_of_locArea {γ : ℝ} {u : FieldSample} (h : LocArea γ u) : LocAreaQ γ u := by
  obtain ⟨ρ, hρ, k₀, hraw, hpos⟩ := h
  obtain ⟨ρ', hρ'0, hρ'ρ⟩ := exists_rat_btwn hρ
  exact ⟨ρ', hρ'0, k₀, fun k hk z hz => hraw k hk z ⟨ball_subset_ball hρ'ρ.le hz.1, hz.2⟩,
    fun q hq hqρ => hpos q hq (hqρ.trans hρ'ρ)⟩

/-- **Ball locality of the map zoom of a good path under area-only goodness.** -/
theorem g3zMapZ_ballLocQ {γ : ℝ} (hγ : 0 < γ) {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}
    (hsel : G1PsiSel γ Ψ) {a : ℝ≥0 → ℝ} (ha : G3ZqGoodPath γ a) (side : Bool) :
    G3ZqZoomBallLocGZ (g3zMapZ γ Ψ side a) (g3zMapGdQ γ Ψ side a) := by
  intro s hs y y' x W hWo hag hxW hGd
  by_cases hxs : x ∈ g1SideHalf side
  · simp only [g3zMapGdQ, if_pos hxs] at hGd
    obtain ⟨φ₀, hφ₀, hΨa⟩ := hsel.2.2 a ha.1 ha.2 side
    obtain ⟨Φo, hR⟩ := G1Z2.sideReflChordStmt_holds _ ha.2 side φ₀ hφ₀
    rw [← hΨa] at hR
    have hψH : MapsTo (Ψ side a) H H := (G1RC.psiGood_of_sel hsel ha.1 ha.2 side).2.2.2.1
    obtain ⟨ρ, hρ, Φ₁, hc, hmt, heq, h0⟩ := g3mapP_ext hψH hR hxs y
    have hm : Measurable (g3mapP Ψ side (y, a, 1, x)) :=
      (g3mapB_props hsel ha.1 ha.2 side one_pos (x / 1)).2.2
    have hT := fcAgree_translate hWo hag.circAgree x
    have h0W : (0 : ℂ) ∈ (fun z => z + (x : ℂ)) ⁻¹' W := by simpa using hxW
    obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 (hWo.preimage (by fun_prop)) 0 h0W
    have hagC : CircAgree (ball 0 ε) (translate y (x : ℂ)) (translate y' (x : ℂ)) :=
      fun n k z hz hW => hT.circAgree n k z hz (hW.trans hεW)
    have hev := g3zoomLawM_eventually_iff_ballQ hs hγ hε hagC hρ hc hmt heq hm h0 hGd
    filter_upwards [hev] with L hL
    simp only [g3zMapZ, if_pos hxs]
    exact hL
  · simp only [g3zMapGdQ, if_neg hxs] at hGd
    have hev := g3ZqZoomBallLocZ_zoomLaw hγ s hs y y' x W hWo hag hxW hGd.1 hGd.2
    filter_upwards [hev] with L hL
    simp only [g3zMapZ, if_neg hxs]
    exact hL

end G3ZqL
end Thm18Asm
end QuantumZipper
