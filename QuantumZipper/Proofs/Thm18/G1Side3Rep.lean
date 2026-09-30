import QuantumZipper.Proofs.Thm18.G1Side3Has
import QuantumZipper.Proofs.Thm18.G1Side3Tr
import QuantumZipper.Proofs.Thm18.G1RestRed
import QuantumZipper.Proofs.Thm18.G1ProfileConv
import QuantumZipper.Proofs.Zipper.SWCoreA6

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE3 (16): the area limit at the selected side maps of the representative, a.s.

`ae_areaLimit_rep`: for a.e. path, both sides, almost surely, the canonical wedge representative
pulled back by the selected side map `ψ = Ψ left a` has the area limit along all radii
`pullMu μ_w (s ψ)`, `w` the unscaled wedge field and `s` its canonical scale
(`G1Side.hasAreaLimit_sample`). The a.s. inputs: the free-field family core and the continuum
limits over the countably many rectangles `R_n`, `U_n` and scale ranges `[1/N, N]`
(`G1Side.ae_scale_family`, `G1Side.ae_family_continuum`), the wedge window limits
(`SWCore.swWindowSplitStmtR_holds`), the regularity of the wedge field, the canonical scale
(`WedgeCan4.ae_wedge_canonical_spec_of_inputs`) and RC3 (`Thm18Asm.G1Rest.ae_rc3_rep`).
Sheffield–Wang arXiv:1605.06171 Thm 1.4 (area measure) for the side map; own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace G1Side

open SWCore Thm18Asm

/-- The analytic facts of a selected side map. -/
def SideMapFacts (ψ : ℂ → ℂ) : Prop :=
  Measurable ψ ∧ DifferentiableOn ℂ ψ H ∧ InjOn ψ H ∧ MapsTo ψ H H ∧
    (∀ z ∈ H, deriv ψ z ≠ 0) ∧
    ∀ d ∈ Hbar, ∀ r > 0, Integrable (fun z => Real.log ‖deriv ψ z‖) (foldedCircle d r)

theorem sideMapFacts_of_sel {γ : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} (hΨ : G1PsiSel γ Ψ)
    {a : ℝ≥0 → ℝ} (hc : Continuous a) (hs : IsSimpleChord (pathTrace (γ ^ 2) a)) (left : Bool) :
    SideMapFacts (Ψ left a) := by
  obtain ⟨hm, hd, hi, hH, -⟩ := G1RC.psiGood_of_sel hΨ hc hs left
  obtain ⟨φ₀, hφ₀, hΨa⟩ := hΨ.2.2 a hc hs left
  have hD : IsOpen (sideDom (pathTrace (γ ^ 2) a) left) := G1.isOpen_component hs left
  obtain ⟨-, hψ0, -, -⟩ := G1.invFunOn_props hD hφ₀
  have hint := G1.choiceRegular_logDeriv hD hφ₀
  rw [← hΨa] at hψ0 hint
  exact ⟨hm, hd, hi, hH, hψ0, hint⟩

theorem recR_empty_zero : recR 0 = ∅ := by
  ext z
  simp only [recR, rectC, mem_setOf_eq, mem_Icc, Nat.cast_zero, mem_empty_iff_false, iff_false]
  intro h
  norm_num at h
  linarith [h.2.1, h.2.2]

/-- The per-path, per-rectangle a.s. inputs. -/
theorem ae_inputs {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : Ω' → FieldSample} (hX : IsFreeGFFModConstH X P') {G : Ω' → ℂ × ℝ → ℝ}
    (hG : WedgeTK.IsRegVersion X P' G) {ψ : ℂ → ℂ} (hψ : SideMapFacts ψ) :
    ∀ᵐ ω ∂P', ∀ n N : ℕ, 1 ≤ N → ∀ s ∈ Icc (1 / (N : ℝ)) N,
      (∀ᶠ k in atTop, ∀ α ∈ Icc (1 : ℝ) 2, ∀ z ∈ recR n,
        Tendsto (fun j => ∫ u, avgReg (X ω) j u
            ∂((foldedCircle z (α * radius k)).map fun u => (s : ℂ) * ψ u)) atTop
          (𝓝 (evalReg (X ω) ((foldedCircle z (α * radius k)).map fun u => (s : ℂ) * ψ u)))) ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ α ∈ Icc (1 : ℝ) 2, ∀ z ∈ recR n,
        |evalReg (X ω) ((foldedCircle z (α * radius k)).map fun u => (s : ℂ) * ψ u) -
          evalReg (X ω) (foldedCircle ((s : ℂ) * ψ z)
            (α * radius k * ‖deriv (fun u => (s : ℂ) * ψ u) z‖))| ≤ η) ∧
      ∃ k₁ : ℕ, ∀ k ≥ k₁, ∀ α ∈ Icc (1 : ℝ) 2, ∀ v ∈ recU n, ∃ Y : ℝ,
        Tendsto (fun σ => ∫ u, G ω (u, σ)
          ∂((foldedCircle v (α * radius k)).map fun u => (s : ℂ) * ψ u)) (𝓝[>] 0) (𝓝 Y) := by
  obtain ⟨hm, hd, hi, hH, h0, -⟩ := hψ
  rw [ae_all_iff]; intro n
  rw [ae_all_iff]; intro N
  by_cases hN : 1 ≤ N
  swap
  · exact ae_of_all _ fun ω h => absurd h hN
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- the class on `U_n`
  obtain ⟨ρU, MU, mU, hρU, hmU, hclU⟩ := exists_areaClass (a := -(n + 1 : ℝ)) (b := n + 1)
    (d := n + 1) hd hi hH h0 (c := 1 / (2 * (n + 1 : ℝ))) (by positivity)
  have hUu := scaleFam_unif (by linarith) (by
      rw [div_le_iff₀ (by positivity)]; nlinarith) (by positivity) hρU hmU hclU hN
  obtain ⟨k₁, hC⟩ := ae_family_continuum hX hG hUu
  -- the class on `R_n` (nonempty only for `n ≥ 1`)
  have hFam : ∀ᵐ ω ∂P', ∀ s ∈ Icc (1 / (N : ℝ)) N,
      (∀ᶠ k in atTop, ∀ α ∈ Icc (1 : ℝ) 2, ∀ z ∈ recR n,
        Tendsto (fun j => ∫ u, avgReg (X ω) j u
            ∂((foldedCircle z (α * radius k)).map fun u => (s : ℂ) * ψ u)) atTop
          (𝓝 (evalReg (X ω) ((foldedCircle z (α * radius k)).map fun u => (s : ℂ) * ψ u)))) ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ α ∈ Icc (1 : ℝ) 2, ∀ z ∈ recR n,
        |evalReg (X ω) ((foldedCircle z (α * radius k)).map fun u => (s : ℂ) * ψ u) -
          evalReg (X ω) (foldedCircle ((s : ℂ) * ψ z)
            (α * radius k * ‖deriv (fun u => (s : ℂ) * ψ u) z‖))| ≤ η) := by
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · refine ae_of_all _ fun ω s _ => ⟨Eventually.of_forall fun k α _ z hz => ?_,
        fun η _ => Eventually.of_forall fun k α _ z hz => ?_⟩ <;>
      · rw [recR_empty_zero] at hz; exact absurd hz (notMem_empty z)
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
      obtain ⟨ρR, MR, mR, hρR, hmR, hclR⟩ := exists_areaClass (a := -(n : ℝ)) (b := n)
        (d := n) hd hi hH h0 (c := 1 / (n + 1 : ℝ)) (by positivity)
      exact ae_scale_family hX (by linarith) (by
        rw [div_le_iff₀ (by positivity)]; nlinarith) (by positivity) hρR hmR hclR hN
  filter_upwards [hFam, hC] with ω hω hωC
  intro _ s hs
  obtain ⟨h1, h2⟩ := hω s hs
  refine ⟨h1, h2, k₁, fun k hk α hα v hv => ?_⟩
  obtain ⟨Y, hY⟩ := hωC k hk (parQ s α v)
  refine ⟨Y, ?_⟩
  rw [famF_parQ hs, famA_parQ hα, famZ_parQ hv] at hY
  exact hY

end G1Side
end QuantumZipper
