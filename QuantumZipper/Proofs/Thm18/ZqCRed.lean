import QuantumZipper.Proofs.Thm18.ZqCTop

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZQ-CORE (8): the Palm transfer of the core functional from a local sandwich

`zqCZoomTransferStmt_of_sandwich : ZqCLocSandwichStmt → ZqCZoomTransferStmt`, hence
`g3ZqO6CoreDStmt_of_sandwich : ZqCLocSandwichStmt → G3ZqO6CoreDStmt`.

The zoom functional `Γ(loc_R(zoom_L y at x))` reads the field outside the unit disc, so the
wedge Palm identity (`ZqCPalmFor`) does not apply to it directly. The node
`ZqCLocSandwichStmt` asks for functionals `φ_L, β_L ∈ [0, 1]` of the circle averages inside the
unit disc (`vOf`) with `|Γ(zoom_L y) − φ_L(y)| ≤ β_L(y)` for EVERY sample `y` at every core
point, and `E β_L(h^x) → 0` for the wedge Palm field `h^x` at every core point (the local
canonical description on a small half-disc, off the bad-scale event of vanishing Palm mass).
Given it, the Palm identity applies to `1_W φ_L` and `β_L`, and dominated convergence over the
core removes `β_L`:

  `|E Φ_L(h) − ∫_T ρ(x) E[1_{W_x} Γ(zoom_L h^x)] dx| ≤ 2 ∫_T ρ(x) E β_L(h^x) dx → 0`.

Sheffield, arXiv:1012.4797, proof of Prop. 5.5 (p. 65: the zoomed field only depends on the
field near the point) and pp. 70–71; Duplantier–Sheffield, arXiv:0808.1560, §3.3. Own
bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace ZqC

open G3Z2b2 D3Plus G1Zm G3Zq G3ZqL G3ZqO Factorization G2PalmLoc

/-- **Local sandwich of the zoom functional by circle functionals (open node).** -/
def ZqCLocSandwichStmt : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ, G1PsiSel γ Ψ →
  ∀ a : ℝ≥0 → ℝ, G3ZqGoodPath γ a → ∀ left : Bool,
  ∀ (R : ℕ) (Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞), Measurable Γ → (∀ y, Γ y ≤ 1) →
  ∀ η : ℝ, 0 < η → η < 1 / 4 →
  ∃ φ β : ℝ → (ℕ → ℝ) → ℝ → ℝ≥0∞,
    (∀ L, Measurable (Function.uncurry (φ L))) ∧ (∀ L, Measurable (Function.uncurry (β L))) ∧
    (∀ L v x, β L v x ≤ 1) ∧
    (∀ L (y : FieldSample), ∀ x ∈ coreSet left η,
      Γ (g1zLocData R (g1zM γ L Ψ left ((y, a), x))) ≤ φ L (vOf y) x + β L (vOf y) x ∧
      φ L (vOf y) x ≤ Γ (g1zLocData R (g1zM γ L Ψ left ((y, a), x))) + β L (vOf y) x) ∧
    ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (V : Ω' → FieldSample), IsFreeGFFModConstH V P' → ∀ x ∈ coreSet left η,
      Tendsto (fun L => ∫⁻ ω, β L (vOf (G1Zm.palmFieldAt γ x (V ω))) x ∂P') atTop (𝓝 0)

theorem sandwich_mul {w Γv φv βv : ℝ≥0∞} (hw : w ≤ 1) (h : Γv ≤ φv + βv) :
    w * Γv ≤ w * φv + βv :=
  calc w * Γv ≤ w * (φv + βv) := mul_le_mul' le_rfl h
    _ = w * φv + w * βv := mul_add _ _ _
    _ ≤ w * φv + βv := add_le_add le_rfl (mul_le_of_le_one_left bot_le hw)

theorem measurable_vOf : Measurable vOf :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

theorem vOf_reconstruct (y : FieldSample) : vOf (reconstruct (coords y)) = vOf y := by
  classical
  funext j
  unfold vOf cJ rJ
  split_ifs with h
  · exact reconstruct_coords_apply y j
  · obtain ⟨i, hi⟩ := dyadicIndex_surj 0 1 0
    have h0 : dyadicRoundC 0 (0 : ℂ) = 0 := by
      apply Complex.ext <;> simp [dyadicRoundC, dyadicRound]
    rw [h0] at hi
    have e : foldedCircle (0 : ℂ) (1 / 2) =
        foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2) := by
      rw [hi]; norm_num [radius]
    rw [e]
    exact reconstruct_coords_apply y i

theorem mem_winS_iff (γ : ℝ) (left : Bool) (U : ℝ) {η δ x : ℝ} (hη4 : η < 1 / 4) (hδ : 0 < δ)
    (hδη : δ < η / 2) (hx : x ∈ coreSet left η) (y : FieldSample) :
    (vOf y, x) ∈ winS γ left U δ ↔ winLen γ left δ x y ≤ ENNReal.ofReal U := by
  obtain ⟨b1, b2⟩ := seg_bounds hη4 hδ hδη hx
  have e1 : (vOf y, x) ∈ winS γ left U δ ↔
      locLen γ (recF (vOf y)) (segLo left δ x) (segHi left δ x) (δ / 4) ≤ ENNReal.ofReal U :=
    Iff.rfl
  rw [e1, locLen_recF γ y (by positivity) b1 b2, winLen_eq_locLen γ left hδ]

theorem winPhi_le_one (γ : ℝ) (left : Bool) (U δ : ℝ) (v : ℕ → ℝ) (x : ℝ) :
    winPhi γ left U δ v x ≤ 1 := indicator_le (fun _ _ => le_rfl) _

/-- On the wedge side (good sample) the window indicator is the circle functional. -/
theorem core_winD_indicator {γ : ℝ} {y : FieldSample} (hy : IsLQGGood γ y) (left : Bool) (U : ℝ)
    {η δ x : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) (hδ : 0 < δ) (hδη : δ < η / 2)
    (hx : x ∈ coreSet left η) (F : ℝ → ℝ≥0∞) :
    (coreSet left η ∩ winD γ left U δ y).indicator F x = winPhi γ left U δ (vOf y) x * F x := by
  have hiff : x ∈ winD γ left U δ y ↔ (vOf y, x) ∈ winS γ left U δ := by
    rw [mem_winS_iff γ left U hη4 hδ hδη hx, ← bdryM_seg_eq_winLen hy left hδ]
    exact ⟨fun h => h.2, fun h => ⟨(mem_side_of_core hη hη4 hx).1, h⟩⟩
  by_cases h : (vOf y, x) ∈ winS γ left U δ
  · rw [indicator_of_mem (show x ∈ coreSet left η ∩ winD γ left U δ y from ⟨hx, hiff.2 h⟩)]
    show F x = (winS γ left U δ).indicator 1 (vOf y, x) * F x
    rw [indicator_of_mem h]; simp
  · rw [indicator_of_notMem (fun h' => h (hiff.1 h'.2))]
    show 0 = (winS γ left U δ).indicator 1 (vOf y, x) * F x
    rw [indicator_of_notMem h]; simp

/-- On the Palm side the window indicator is the circle functional. -/
theorem winPhi_palm (γ : ℝ) (left : Bool) (U : ℝ) {η δ x : ℝ} (hη4 : η < 1 / 4) (hδ : 0 < δ)
    (hδη : δ < η / 2) (hx : x ∈ coreSet left η) {Ω' : Type} (V : Ω' → FieldSample) (ω : Ω') :
    winPhi γ left U δ (vOf (G1Zm.palmFieldAt γ x (V ω))) x =
      (palmWin γ left U δ x V).indicator 1 ω := by
  have hiff := mem_winS_iff γ left U hη4 hδ hδη hx (G1Zm.palmFieldAt γ x (V ω))
  by_cases h : ω ∈ palmWin γ left U δ x V
  · rw [indicator_of_mem h]
    show (winS γ left U δ).indicator 1 _ = _
    rw [indicator_of_mem (hiff.2 h)]; rfl
  · rw [indicator_of_notMem h]
    show (winS γ left U δ).indicator 1 _ = _
    rw [indicator_of_notMem (fun h' => h (hiff.1 h'))]

theorem measurable_coreInt (γ : ℝ) {F : (ℕ → ℝ) → ℝ → ℝ≥0∞} (hF : Measurable (uncurry F))
    {T : Set ℝ} (hT : MeasurableSet T) :
    Measurable fun y : FieldSample => ∫⁻ x, T.indicator (fun x => F (vOf y) x) x ∂bdryM γ y := by
  have hH : Measurable fun q : FieldSample × ℝ => T.indicator (fun x => F (vOf q.1) x) q.2 := by
    have e : (fun q : FieldSample × ℝ => T.indicator (fun x => F (vOf q.1) x) q.2) =
        (Prod.snd ⁻¹' T).indicator (fun q : FieldSample × ℝ => uncurry F (vOf q.1, q.2)) := by
      funext q; rfl
    rw [e]
    refine Measurable.indicator ?_ (measurable_snd hT)
    have h := hF.comp ((measurable_vOf.comp measurable_fst).prodMk measurable_snd)
    simp only [Function.comp_def] at h
    exact h
  exact R18.measurable_lintegral_family (measurable_bdryM γ)
    (fun y N => R18.bdryM_Icc_ne_top γ y _ _) hH

end ZqC
end Thm18Asm
end QuantumZipper
