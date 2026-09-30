import QuantumZipper.Proofs.Thm18.ZqT1Prod
import QuantumZipper.Proofs.Thm18.ZqT2Area

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZQ-TYP (3): area-only goodness of the unscaled wedge at every point, for a.e. path

For a good path `a` (a.e. for the Brownian path law) and a.s. in the field, the unscaled wedge
`w = g3plUW γ X A ω` satisfies the area-only map goodness `g3zMapGdQ` at EVERY boundary point, on
both sides (`wedge_gdQ_pt`, `ae_wedge_typQ`); in particular at `ν_w`-typical points and their
length partners (the wedge clause of `G3ZqLMapTypQAEStmt`). At a point `x` of the side half-line:

* the continuum limits, the core and the area-only choice regularity of `w` along `Ψ_a` come from
  the canonical wedge along the scaled path (`ZqT.ae_unsc_facts`, G3ZqS pointwise transfers);
* the area limit of `w` pulled back by `Ψ_a` is `pullMu μ_w Ψ_a` (`ZqT.hasAreaLimit_unsc`), which
  charges every open subset of `ℍ` (`G3ZqL.pullMu_pos`, area goodness of `w`);
* moving it to the local map at `x` gives positive area proxy (`ZqT.areaProxy_pos_translate`),
  hence `LocAreaQ` of the pulled-back field (`G3ZqL.locAreaQ_of_choiceA`).

Off the side half-line the plain goodness is the area goodness of the translated wedge.
Sheffield, arXiv:1012.4797, pp. 65, 70; Duplantier–Sheffield, arXiv:0808.1560, Prop. 2.1.
Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace ZqT

open G1Zm G3Zq G3Zr G3Z2b2 G1SSR2 G3ZqS G1Side

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- **Pointwise area-only map goodness of the unscaled wedge.** -/
theorem wedge_gdQ_pt {γ : ℝ} (hγ : 0 < γ) (hsel : G1PsiSel γ Ψ) {a : ℝ≥0 → ℝ}
    (ha : G3ZqGoodPathF γ a) {x0 : FieldSample} {F : ℂ × ℝ → ℝ} {A0 : ℝ → ℝ}
    (hgood : WedgeTK.GoodRad x0 F)
    (hraw : ∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
      x0 (foldedCircle (dyadicRoundC n z) (radius k)) = F (dyadicRoundC n z, radius k))
    (hA : Continuous A0) (hWg : IsLQGGood γ (wedgeField (lateralPart x0) A0 (Qc γ)))
    {cw cw' : ℕ → ℝ} (hcw : Tendsto cw atTop (𝓝 1)) (hcw' : Tendsto cw' atTop (𝓝 1))
    (hWin : E6.WindowLimits γ (wedgeField (lateralPart x0) A0 (Qc γ)) cw cw')
    (hAG : IsAreaGood γ (wedgeField (lateralPart x0) A0 (Qc γ)))
    (hb : 0 < scaleParam γ (wedgeField (lateralPart x0) A0 (Qc γ)))
    (hcs : ∀ left : Bool,
      (∀ φ, IsNormalizedUniformizer (sideDom (pathTrace (γ ^ 2)
          (scalePath (scaleParam γ (wedgeField (lateralPart x0) A0 (Qc γ))) a)) left) φ →
        G1.ChoiceRegularCore γ (canonical γ (wedgeField (lateralPart x0) A0 (Qc γ)))
          (invFunOn φ (sideDom (pathTrace (γ ^ 2)
            (scalePath (scaleParam γ (wedgeField (lateralPart x0) A0 (Qc γ))) a)) left)) ∧
        G1Z2MeasGood γ left (coordChange (canonical γ (wedgeField (lateralPart x0) A0 (Qc γ)))
          (invFunOn φ (sideDom (pathTrace (γ ^ 2)
            (scalePath (scaleParam γ (wedgeField (lateralPart x0) A0 (Qc γ))) a)) left))
          (Qc γ))) ∧
      ∀ (d : ℂ) (r : ℝ), 0 < r → F1.ContData (wedgeField (lateralPart x0) A0 (Qc γ))
        ((foldedCircle d r).map (Ψ left a)))
    (hin : ∀ left : Bool, ∀ n N : ℕ, 1 ≤ N → ∀ s ∈ Icc (1 / (N : ℝ)) N,
      (∀ᶠ k in atTop, ∀ α ∈ Icc (1 : ℝ) 2, ∀ z ∈ recR n,
        Tendsto (fun j => ∫ u, avgReg x0 j u
            ∂((foldedCircle z (α * radius k)).map fun u => (s : ℂ) * Ψ left a u)) atTop
          (𝓝 (evalReg x0 ((foldedCircle z (α * radius k)).map fun u => (s : ℂ) * Ψ left a u)))) ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ α ∈ Icc (1 : ℝ) 2, ∀ z ∈ recR n,
        |evalReg x0 ((foldedCircle z (α * radius k)).map fun u => (s : ℂ) * Ψ left a u) -
          evalReg x0 (foldedCircle ((s : ℂ) * Ψ left a z)
            (α * radius k * ‖deriv (fun u => (s : ℂ) * Ψ left a u) z‖))| ≤ η) ∧
      ∃ k₁ : ℕ, ∀ k ≥ k₁, ∀ α ∈ Icc (1 : ℝ) 2, ∀ v ∈ recU n, ∃ Y : ℝ,
        Tendsto (fun σ => ∫ u, F (u, σ)
          ∂((foldedCircle v (α * radius k)).map fun u => (s : ℂ) * Ψ left a u)) (𝓝[>] 0)
          (𝓝 Y))
    (side : Bool) (x : ℝ) :
    G3ZqL.g3zMapGdQ γ Ψ side a (wedgeField (lateralPart x0) A0 (Qc γ)) x := by
  set y := wedgeField (lateralPart x0) A0 (Qc γ) with hy
  unfold G3ZqL.g3zMapGdQ
  split_ifs with hxs
  swap
  · exact ⟨(hAG.translate x).1, fun q hq => pos_areaProxy_of_isAreaGood (hAG.translate x) hq⟩
  obtain ⟨hac, hs, hWd, hW0, hex⟩ := ha
  set b := scaleParam γ y with hbdef
  have hΨm : Measurable (Ψ side a) := (hsel.1 side).comp (measurable_const.prodMk measurable_id)
  have hΨH : MapsTo (Ψ side a) H H := (G1RC.psiGood_of_sel hsel hac hs side).2.2.2.1
  have hgB : g3mapP Ψ side (y, a, 1, x) = g3mapB Ψ side a 1 x := by
    show g3mapB Ψ side a 1 (x / 1) = _
    rw [div_one]
  have hg3 : g3mapP Ψ side (y, a, 1, x) =
      fun w => Ψ side a (w + (g3bpre Ψ side a (x / 1) : ℂ)) - (x : ℂ) := by
    funext w
    simp [g3mapP, g3mapB, g3locM]
  -- the core of `y` along `Ψ_a` and the area limit `pullMu μ_y Ψ_a`
  obtain ⟨φ, hφ, hΨa⟩ := hsel.2.2 a hac hs side
  obtain ⟨φ'', hN'', hdil⟩ := exists_dilUnif (γ := γ) hb hs hWd hW0 hex side hφ
  set D' := sideDom (pathTrace (γ ^ 2) (scalePath b a)) side with hD'def
  have hsb : IsSimpleChord (pathTrace (γ ^ 2) (scalePath b a)) :=
    isSimpleChord_scalePath hb _ hWd hW0 hex hs
  obtain ⟨hcB, -⟩ := (hcs side).1 φ'' hN''
  obtain ⟨hd'', hd0'', hm'', hH''⟩ := G1.invFunOn_props (G1.isOpen_component hsb side) hN''
  have hH''H : MapsTo (invFunOn φ'' D') H H := fun w hw =>
    G1ZA1a.sideDom_subset_H _ side (hH'' hw)
  have hinj'' : InjOn (invFunOn φ'' D') H := hN''.1.invOn_invFunOn.2.injOn
  have hEq : EqOn (Ψ side a) (fun u => (b : ℂ) * invFunOn φ'' D' u) H := fun w hw => by
    rw [hΨa]; exact (hdil w hw).symm
  have hfc : ∀ (d : ℂ) (r : ℝ), 0 < r →
      coordChange y (Ψ side a) (Qc γ) (foldedCircle d r) =
        coordChange (canonical γ y) (invFunOn φ'' D') (Qc γ) (foldedCircle d r) := by
    intro d r hr
    rw [g1zMeas_coordChange_fc_congr y hEq (Qc γ) d hr]
    have hc' : F1.ContData y ((foldedCircle d r).map fun u => (b : ℂ) * invFunOn φ'' D' u) := by
      rw [← Measure.map_congr ((TwoPoint.foldedCircle_ae_mem_H d hr).mono fun w hw => hEq hw)]
      exact (hcs side).2 d r hr
    exact raw_rescale_side hWg.1 hb hm'' hH''H hd0'' d hr
      (G1.integrable_log_norm_deriv_foldedCircle_of_injOn hd'' hinj'' d hr) hc'
  have hcoreA : G1.ChoiceRegularCore γ y (Ψ side a) := core_of_fc_eq hcB hfc
  have hb0 : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hb.ne'
  have hEqψ : EqOn (fun u => ((b⁻¹ : ℝ) : ℂ) * Ψ side a u) (invFunOn φ'' D') H := fun w hw => by
    simp only
    rw [hEq hw]; push_cast; field_simp
  have hfcψ : ∀ (d : ℂ) (r : ℝ), 0 < r →
      coordChange (canonical γ y) (fun u => ((b⁻¹ : ℝ) : ℂ) * Ψ side a u) (Qc γ)
          (foldedCircle d r) =
        coordChange (canonical γ y) (invFunOn φ'' D') (Qc γ) (foldedCircle d r) :=
    fun d r hr => g1zMeas_coordChange_fc_congr _ hEqψ _ d hr
  have hcoreψ := core_of_fc_eq hcB hfcψ
  have hin1 := fun n => hin side n 1 le_rfl 1 ⟨by norm_num, by norm_num⟩
  have hA1 := hasAreaLimit_unsc hγ hgood hraw hA hWg hcw hcw' hWin
    (sideMapFacts_of_sel hsel hac hs side) hb hcoreψ.2.1 (fun n => (hin1 n).1)
    (fun n => (hin1 n).2.1) (fun n => (hin1 n).2.2)
  have hμ : HasAreaLimit γ (coordChange y (Ψ side a) (Qc γ))
      (pullMu (qAreaMeasure γ y) fun u => ((1 : ℝ) : ℂ) * Ψ side a u) :=
    hasAreaLimit_of_fc_eq hA1 fun d r hr => (hfc d r hr).trans (hfcψ d r hr).symm
  obtain ⟨hd1, hi1, hH1, h01⟩ := G3ZqL.sideMapFacts_smul (sideMapFacts_of_sel hsel hac hs side)
    one_pos
  have hpos : ∀ V : Set ℂ, IsOpen V → V ⊆ H → V.Nonempty →
      0 < pullMu (qAreaMeasure γ y) (fun u => ((1 : ℝ) : ℂ) * Ψ side a u) V :=
    fun V hV hVH hne => G3ZqL.pullMu_pos hd1 hi1 hH1 h01
      (fun W hW hWH hWn => hAG.2 W hW hWH hWn) hV hVH hne
  -- the three inputs of `locAreaQ_of_choiceA`
  have hcr := choiceRegularA_unscaled_pt hsel hWg hb hac hs hWd hW0 hex side (hcs side).1
    (hcs side).2 0 x
  have hrs := (regShiftU_pt hWg.1 hΨm hΨH (hcs side).2 x).1
  refine G3ZqL.locAreaQ_of_choiceA hsel hac hs (fun d j => ?_) ?_ ?_
  · rw [hgB]; exact hrs d j
  · rw [hgB]; exact hcr
  · intro q hq
    rw [hg3]
    exact areaProxy_pos_translate hWg.1 hΨm hΨH hcoreA hμ hpos (hcs side).2
      (g3bpre Ψ side a (x / 1)) x (0 / γ) hq

end ZqT
end Thm18Asm
end QuantumZipper
