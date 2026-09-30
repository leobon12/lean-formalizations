import QuantumZipper.Proofs.Thm18.G1ZZ1Main
import QuantumZipper.Proofs.Thm18.G1ZBdryDet
import QuantumZipper.Proofs.Thm18.LenPos
import QuantumZipper.Proofs.Thm18.R18G3Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 4: change of variables to the wedge boundary, both sides (`G3JointPalmToWedgeStmt`)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, proof of Theorem 1.8
(pp. 69–71, Figure 1.7: the pair `(x, R(x))` of boundary points of the wedge at the same quantum
length from the root).

Copy of `Thm18Asm.g1PalmToWedgeStmt_of` (G1ZZ1Main.lean) for a pair of functionals
`Γ₁` (left side) `* Γ₂` (right side). A.s. both side boundary measures are transports of the wedge
boundary measure `ν_Y` by the boundary values `Φ_L`, `Φ_R` of the side maps
(`G1SideTransportIdStmt`), and each side field rerooted at `Φ⁻¹ x` and shifted by `C` is the zoom
of `Y` at `x` through the local map (`g3z_side_zoom`, the per-side body of the template). The
left Palm window is transported to the wedge window by `window_transport`; the new ingredient is
the length partner: at `b = Φ_L⁻¹ x` the left length is `ν_Y[x, 0]` and the right side point at
that length is `Φ_R⁻¹ (R x)` (`g3_lenRight_pull`: the quantile of a pushforward under an order
isomorphism fixing `0`), with `R x > 0` (`g3_lenRight_pos`; `ν_Y` atomless, locally finite and
infinite on `[0, ∞)`). The two quantile lemmas are own elementary proofs.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm D3Plus

/-- **Quantile of a pushforward** (own elementary proof): for an order isomorphism `Φ` fixing `0`
and `m` without atom at `0`, the right quantile of `(m|_{(0,∞)}).map Φ⁻¹` is `Φ⁻¹` of the right
quantile of `m`. -/
theorem g3_lenRight_pull {m : Measure ℝ} {Φ : ℝ ≃o ℝ} (h0 : Φ 0 = 0) (hatom : m {0} = 0)
    (ℓ : ℝ) :
    lenRight ((m.restrict (g1SideHalf false)).map Φ.symm) ℓ = Φ.symm (lenRight m ℓ) := by
  have hs0 : Φ.symm 0 = 0 := Φ.symm_apply_eq.2 h0.symm
  unfold lenRight
  set S := {y : ℝ | 0 < y ∧ ENNReal.ofReal ℓ ≤ m (Icc 0 y)} with hSdef
  have hν : ∀ y : ℝ, ((m.restrict (g1SideHalf false)).map Φ.symm) (Icc 0 y) =
      m (Icc 0 (Φ y)) := fun y => by
    rw [pull_apply Φ measurableSet_Icc, OrderIso.image_Icc, h0]
    exact G1ZZ1.seg_inter_half hatom false (Φ y)
  have hset : {y : ℝ | 0 < y ∧ ENNReal.ofReal ℓ ≤
      ((m.restrict (g1SideHalf false)).map Φ.symm) (Icc 0 y)} = Φ.symm '' S := by
    ext y
    constructor
    · rintro ⟨hy, hl⟩
      refine ⟨Φ y, ⟨?_, ?_⟩, Φ.symm_apply_apply y⟩
      · rw [← h0]; exact Φ.strictMono hy
      · rw [← hν y]; exact hl
    · rintro ⟨z, ⟨hz, hl⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← hs0]; exact Φ.symm.strictMono hz
      · rw [hν, OrderIso.apply_symm_apply]; exact hl
  rw [hset]
  rcases S.eq_empty_or_nonempty with he | hne
  · rw [he, image_empty, Real.sInf_empty, hs0]
  · exact (Φ.symm.monotone.map_csInf_of_continuousAt Φ.symm.continuous.continuousAt hne
      ⟨0, fun y hy => hy.1.le⟩).symm

/-- **The length partner is positive** (own elementary proof): for `m` without atom at `0`,
finite on compact intervals and infinite on `[0, ∞)`, every positive length has a positive right
quantile. -/
theorem g3_lenRight_pos {m : Measure ℝ} (hatom : m {0} = 0) (hinf : m (Ici 0) = ⊤)
    (hfin : ∀ b : ℝ, m (Icc 0 b) < ⊤) {ℓ : ℝ} (hℓ : 0 < ℓ) : 0 < lenRight m ℓ := by
  have hne : ∃ z : ℝ, 0 < z ∧ ENNReal.ofReal ℓ ≤ m (Icc 0 z) := by
    have hU : ⋃ n : ℕ, Icc (0 : ℝ) n = Ici 0 := by
      ext y
      simp only [mem_iUnion, mem_Icc, mem_Ici]
      constructor
      · rintro ⟨n, h, -⟩; exact h
      · intro h
        obtain ⟨n, hn⟩ := exists_nat_ge y
        exact ⟨n, h, hn⟩
    have ht := tendsto_measure_iUnion_atTop (μ := m) (s := fun n : ℕ => Icc (0 : ℝ) n)
      (fun a b hab => Icc_subset_Icc_right (Nat.cast_le.2 hab))
    rw [hU, hinf] at ht
    obtain ⟨n, hn1, hn2⟩ :=
      ((ht.eventually (lt_mem_nhds ENNReal.ofReal_lt_top)).and (eventually_gt_atTop 0)).exists
    exact ⟨n, Nat.cast_pos.2 hn2, hn1.le⟩
  have hδ : ∃ δ : ℝ, 0 < δ ∧ m (Icc 0 δ) < ENNReal.ofReal ℓ := by
    have hI : ⋂ n : ℕ, Icc (0 : ℝ) (1 / ((n : ℝ) + 1)) = {0} := by
      ext y
      simp only [mem_iInter, mem_Icc, mem_singleton_iff]
      constructor
      · intro h
        by_contra hy
        have hy0 : 0 < y := lt_of_le_of_ne (h 0).1 (Ne.symm hy)
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hy0
        exact absurd (h n).2 (not_le.2 hn)
      · rintro rfl n
        exact ⟨le_rfl, by positivity⟩
    have ht := tendsto_measure_iInter_atTop (μ := m)
      (s := fun n : ℕ => Icc (0 : ℝ) (1 / ((n : ℝ) + 1)))
      (fun _ => measurableSet_Icc.nullMeasurableSet)
      (fun a b hab => Icc_subset_Icc_right (Nat.one_div_le_one_div hab)) ⟨0, (hfin _).ne⟩
    rw [hI, hatom] at ht
    obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hℓ))).exists
    exact ⟨1 / ((n : ℝ) + 1), by positivity, hn⟩
  obtain ⟨δ, hδ0, hδm⟩ := hδ
  obtain ⟨z, hz0, hz⟩ := hne
  have hle : δ ≤ lenRight m ℓ := by
    unfold lenRight
    refine le_csInf ⟨z, hz0, hz⟩ fun y hy => ?_
    by_contra h
    exact absurd (hy.2.trans (measure_mono (Icc_subset_Icc_right (not_le.1 h).le)))
      (not_le.2 hδm)
  linarith

/-- **Per-side body of `g1PalmToWedgeStmt_of`**: a.s. the side boundary measure is the transport
of `ν_Y|_S` by the boundary values `Φ` of the side map, and the side field rerooted at `Φ⁻¹ x`
and shifted by `C` has the canonical data of the zoom of `Y` at `x` at level `γ C` through the
local map. -/
theorem g3z_side_zoom (hReg : G1RegExStmt) (hT : G1SideTransportIdStmt) {γ : ℝ} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    {Y : Ω → FieldSample} (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) (left : Bool) :
    ∀ᵐ ω ∂P, ∃ Φ : ℝ ≃o ℝ, SideReflGood left (g1zSideMap left (drive (γ ^ 2) B ω)) Φ ∧
      g1SideNu γ left (g1SideField γ B Y left ω) =
        ((qBoundaryMeasure γ (Y ω)).restrict (g1SideHalf left)).map Φ.symm ∧
      ∀ x ∈ g1SideHalf left, ∀ C : ℝ,
        canonical γ (addConst (translate (g1SideField γ B Y left ω) ((Φ.symm x : ℝ) : ℂ)) C) =
          canonical γ (zoomFieldVia γ (γ * C) (Y ω) x
            (g1zLocMap left (drive (γ ^ 2) B ω) x)) := by
  have hγ : 0 < γ := hS.1
  have hReg' : G1RegExSide γ P B Y left := by
    cases left
    exacts [(hReg γ P B Y hS hIn).2, (hReg γ P B Y hS hIn).1]
  filter_upwards [hT γ P B Y hS hIn left, hReg', hIn.1, hIn.2.2]
    with ω ⟨Φ, hΦ, hν⟩ ⟨φ, hφ, hcore⟩ ⟨hgood, _⟩ ⟨hsimp, _, hnL, hnR⟩
  have hu : IsNormalizedUniformizer (sideDom (sleTrace (γ ^ 2) B ω) left)
      (uniformizer (sideDom (sleTrace (γ ^ 2) B ω) left)) := by
    cases left
    exacts [hnR, hnL]
  have hcore' := G1.choiceRegularCore_invFunOn_of_normalized hsimp left hφ hu hcore
  have hD : IsOpen (sideDom (sleTrace (γ ^ 2) B ω) left) := G1.isOpen_component hsimp left
  obtain ⟨-, -, hψm, hψD⟩ := G1.invFunOn_props hD hu
  have hDH : sideDom (sleTrace (γ ^ 2) B ω) left ⊆ H := by
    cases left
    exacts [rightComponent_subset_H _, leftComponent_subset_H _]
  obtain ⟨F, hF⟩ := hgood.1
  refine ⟨Φ, hΦ, hν, fun x hxh C => ?_⟩
  have hpre := G1ZZ1.g1zBdryPre_eq hΦ hxh
  have hreg := G1ZZ1.regEq_side_zoomVia hγ.ne' hF hψm (fun z hz => hDH (hψD hz))
    hcore'.2.1 (Φ.symm x) x C
  have hc := S5.FieldShift.canonical_congr hreg γ
  have hloc : g1zLocMap left (drive (γ ^ 2) B ω) x =
      fun w => g1zSideMap left (drive (γ ^ 2) B ω) (w + ((Φ.symm x : ℝ) : ℂ)) - (x : ℂ) := by
    unfold g1zLocMap; rw [hpre]
  rw [hloc]
  exact hc

/-- **Step 4 of route (b)**: the joint Palm-window integral of the two side surfaces is the joint
Palm-window integral of the wedge at `x` and its length partner `R(x)`. -/
theorem g3JointPalmToWedgeStmt_of (hReg : G1RegExStmt) (hT : G1SideTransportIdStmt) :
    G3JointPalmToWedgeStmt := by
  intro γ Ω _ P _ B Y hS hIn U hU C R Γ₁ Γ₂ hΓ₁ hΓ₂ _ _
  have ⟨hγ, hγ2, _, hW, _⟩ := hS
  unfold g3PalmIntC g3zWedgePalmInt
  refine lintegral_congr_ae ?_
  filter_upwards [g3z_side_zoom hReg hT hS hIn true, g3z_side_zoom hReg hT hS hIn false,
    ae_atomless_pos_wedge hS hIn, wedgeRightInfStmt_holds γ P Y hγ hγ2 hW]
    with ω ⟨ΦL, hΦL, hνL, hzL⟩ ⟨ΦR, hΦR, hνR, hzR⟩ ⟨hatom, hpos⟩ hRinf
  have hwin : g1Win γ true (g1SideField γ B Y true ω) U =
      {b | b ∈ g1SideHalf true ∧
        ((qBoundaryMeasure γ (Y ω)).restrict (g1SideHalf true)).map ΦL.symm
          (g1SideSeg true b) ≤ ENNReal.ofReal U} := by
    unfold g1Win; rw [hνL]
  rw [hwin, hνL, G1ZZ1.window_transport hΦL.1 (hatom 0) true (ENNReal.ofReal U)]
  refine setLIntegral_congr_fun
    (G1ZZ1.measurableSet_win (qBoundaryMeasure γ (Y ω)) true (ENNReal.ofReal U)) ?_
  intro x hx
  have hxh : x ∈ g1SideHalf true := hx.1
  have hx0 : x < 0 := hxh
  have hlen : g3LenL γ (g1SideField γ B Y true ω) (ΦL.symm x) =
      ((qBoundaryMeasure γ (Y ω)) (Icc x 0)).toReal := by
    unfold g3LenL
    rw [hνL, pull_apply ΦL (G1ZZ1.measurableSet_seg true _), G1ZZ1.image_seg hΦL.1,
      OrderIso.apply_symm_apply, G1ZZ1.seg_inter_half (hatom 0)]
    rfl
  have hpt : g1SidePt γ false (g1SideField γ B Y false ω)
      (((qBoundaryMeasure γ (Y ω)) (Icc x 0)).toReal) = ΦR.symm (g3zPartner γ (Y ω) x) := by
    show lenRight (g1SideNu γ false (g1SideField γ B Y false ω)) _ = _
    rw [hνR]
    exact g3_lenRight_pull hΦR.1 (hatom 0) _
  have hRpos : g3zPartner γ (Y ω) x ∈ g1SideHalf false := by
    show 0 < lenRight (qBoundaryMeasure γ (Y ω)) _
    refine g3_lenRight_pos (hatom 0) hRinf (fun b => qBoundaryMeasure_Icc_lt_top γ _ 0 b) ?_
    exact ENNReal.toReal_pos
      (lt_of_lt_of_le (hpos x 0 hx0) (measure_mono Ioo_subset_Icc_self)).ne'
      (qBoundaryMeasure_Icc_lt_top γ _ x 0).ne
  beta_reduce
  rw [hlen, hpt, hzL x hxh C, hzR _ hRpos C]

end R18
end QuantumZipper
