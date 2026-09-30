import QuantumZipper.Proofs.Thm18.G1Side3Rep

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE3 (17): the area limit at the selected side maps of the representative

`ae_areaLimit_rep`: for a.e. path, both sides, almost surely, the canonical wedge representative
pulled back by the selected side map `ψ = Ψ left a` has the area limit along all radii
`pullMu μ_w (s ψ)` (`w` the unscaled wedge field, `s = scaleParam γ w`). See G1Side3Rep.lean for
the ingredients. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace G1Side

open SWCore Thm18Asm

/-- The unscaled wedge field of the representative. -/
abbrev wU (γ : ℝ) {Ω' : Type} (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ) (ω : Ω') : FieldSample :=
  wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)

theorem exists_N {s : ℝ} (hs : 0 < s) : ∃ N : ℕ, 1 ≤ N ∧ s ∈ Icc (1 / (N : ℝ)) N := by
  obtain ⟨N, hN⟩ := exists_nat_gt (s + 1 / s + 1)
  have hN1 : (1 : ℝ) ≤ N := by
    have : 0 < 1 / s := by positivity
    linarith
  refine ⟨N, by exact_mod_cast hN1, ?_, by linarith [one_div_pos.2 hs]⟩
  rw [div_le_iff₀ (by linarith)]
  have h1 : 1 / s < N := by linarith [hs]
  rw [div_lt_iff₀ hs] at h1
  linarith

/-- **The area limit at the selected maps, a.s.** -/
theorem ae_areaLimit_rep :
    G1RepSetting fun γ _ _ P B _ _ P' X A => ∀ Ψ, G1PsiSel γ Ψ →
      ∀ᵐ a ∂(P.map (pathOf B)), ∀ left : Bool, ∀ᵐ ω' ∂P',
        SideMapFacts (Ψ left a) ∧
        HasAreaLimit γ (coordChange (wedgeRep γ X A ω') (Ψ left a) (Qc γ))
          (pullMu (qAreaMeasure γ (wU γ X A ω'))
            fun u => (scaleParam γ (wU γ X A ω') : ℂ) * Ψ left a u) := by
  intro γ hγ hγ2 Ω _ P _ B hB Ω' _ P' _ X A hX hA hXA Ψ hΨ
  obtain ⟨G, hG⟩ := WedgeTK.exists_isRegVersion hX
  have hαQ : γ - 2 / γ < Qc γ := alpha_lt_Qc hγ hγ2
  have hfacts : ∀ᵐ a ∂(P.map (pathOf B)), ∀ left : Bool, SideMapFacts (Ψ left a) :=
    G1RC.ae_map_pathOf_of_chord G1RC.g1RegPathChordStmt hγ hγ2 hB hΨ
      (fun ms => ∀ left : Bool, SideMapFacts (ms left))
      (fun a hc hs left => sideMapFacts_of_sel hΨ hc hs left)
  have hrc3 := G1Rest.ae_rc3_rep γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hΨ
  -- the wedge window limits
  have hWS : E6.WedgeWindowStmt := wedgeWindowStmt_of_splitR fun κ hκ hκ4 => by
    have h2 : Real.sqrt κ < 2 := (Real.sqrt_lt' (by norm_num)).2 (by linarith)
    exact ⟨E6.swC (Real.sqrt κ), E6.swC' (Real.sqrt κ), E6.tendsto_swC _, E6.tendsto_swC' _,
      swWindowSplitStmtR_holds (Real.sqrt_pos.2 hκ) h2⟩
  have hsq : Real.sqrt (γ ^ 2) = γ := Real.sqrt_sq hγ.le
  obtain ⟨cw, cw', hcw, hcw', hWin⟩ := hWS (γ ^ 2) (by positivity) (by nlinarith)
  have hA' : IsWedgeProcess (Real.sqrt (γ ^ 2) - 2 / Real.sqrt (γ ^ 2)) (Qc (Real.sqrt (γ ^ 2)))
      A P' := by rw [hsq]; exact hA
  have hWin' := hWin P' X A hX hA' hXA
  simp only [hsq] at hWin'
  filter_upwards [hfacts, hrc3] with a hfa hra left
  filter_upwards [ae_inputs hX hG (hfa left), hra left, hG.ae_good, WedgeCan.ae_raw_dyadic hG,
    WedgeCan4.ae_continuous_wedgeProcess hA, WedgeBdry.ae_bReg_wedgeField hγ hγ2 hαQ hX hA hXA,
    hWin', WedgeCan4.ae_wedge_canonical_spec_of_inputs
      (WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hαQ) (WedgeInf.wedgeInfiniteTotal hγ hγ2 hαQ)
      hγ hγ2 hαQ hX hA hXA] with ω hin hrc hgood hraw hAc hWg hwin hcan
  obtain ⟨hψm, hψd, hψi, hψH, hψ0, hψint⟩ := hfa left
  have hs : 0 < scaleParam γ (wU γ X A ω) := hcan.1
  obtain ⟨N, hN, hsN⟩ := exists_N hs
  refine ⟨hfa left, ?_⟩
  exact hasAreaLimit_sample hγ hgood hraw hAc hWg.1 hcw hcw' hwin hψm hψd hψi hψH hψ0 hψint hs
    hrc (fun n => (hin n N hN _ hsN).1) (fun n => (hin n N hN _ hsN).2.1)
    (fun n => (hin n N hN _ hsN).2.2)

end G1Side
end QuantumZipper
