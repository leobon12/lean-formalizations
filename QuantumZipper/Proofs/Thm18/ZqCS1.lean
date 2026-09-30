import QuantumZipper.Proofs.Thm18.ZqCRed3
import QuantumZipper.Proofs.Thm18.ZqCALoc
import QuantumZipper.Proofs.Thm18.ZqCBMono
import QuantumZipper.Proofs.Thm18.G1ZA1aAff

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZQ-CORE (11): the local sandwich functionals

For the good path `a` and the core point `x`, `mapX x` is the measurable local map at `x`, and
`Zr L v x` the field rebuilt from the pulled-back dyadic coordinates of the zoom of `recF v`
(`G3Z2b2.g3coordsM`). At the radii `ρ_m = 1/(m+1)`:

* `mapOK m x`: the local map sends the rational points of the upper half of `ball 0 ρ_m` into
  `{‖w + x‖ < 1/2}` (a measurable condition on `x`); by continuity it then sends the whole
  upper half-ball into `{‖w + x‖ ≤ 1/2} ∩ ℍ` (`hpsi_of_mapOK`), so the zoom only reads the field
  on dyadic circles inside the unit disc (`ZqC.agreeNear_zoomFieldVia_recF`);
* `okSet m`: `mapOK m x`, the measurable local area certificate (`G3ZqF.dyadCert`) and the
  small local scale (`dyadBad`) at `ρ_m`;
* `phiS = sup_m 1_{okSet m} Γ(dyadT …)` and `betaS = 1 − 1_{⋃ okSet m}`.

`sandwichS`: for every sample `y` and core point `x`,
`|Γ(loc_R(zoom_L y at x)) − phiS(vOf y, x)| ≤ betaS(vOf y, x)`: on `okSet m` the global
canonical description of the zoom is the local one on `halfDisc ρ_m` (`gamma_eq_of_not_bad`),
a function of the dyadic data there (`locFieldFull_canonicalOn_eq_dyadT_of_good`), which are
those of `Zr` (`agreeNear_zoomFieldVia_recF`).

Sheffield, arXiv:1012.4797, proof of Prop. 5.5 (p. 65: the zoomed field only depends on the
field near the point). Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace ZqC

open G3Z2b2 D3Plus G1Zm G3Zq G3ZqL G3ZqO Factorization G2PalmLoc G3Cv

/-- The radii `ρ_m = 1/(m+1)`. -/
def rhoM (m : ℕ) : ℝ := 1 / ((m : ℝ) + 1)

theorem rhoM_pos (m : ℕ) : 0 < rhoM m := by unfold rhoM; positivity

/-- The zero field. -/
def fz : FieldSample := fun _ => 0

/-- The measurable local map at `x`. -/
def mapX (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool) (a : ℝ≥0 → ℝ) (x : ℝ) : ℂ → ℂ :=
  g3mapP Ψ left (fz, a, 1, x)

/-- The rational points of the upper half-plane. -/
def qpt (q : ℚ × ℚ) : ℂ := ⟨q.1, q.2⟩

/-- The measurable condition on the local map at scale `ρ_m`. -/
def mapOK (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool) (a : ℝ≥0 → ℝ) (m : ℕ) (x : ℝ) : Prop :=
  ∀ q : ℚ × ℚ, (0 : ℝ) < q.2 → ‖qpt q‖ < rhoM m → ‖mapX Ψ left a x (qpt q) + (x : ℂ)‖ < 1 / 2

variable {γ : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

theorem measurable_mapX_apply (hsel : G1PsiSel γ Ψ) (left : Bool) (a : ℝ≥0 → ℝ) (w : ℂ) :
    Measurable fun x : ℝ => mapX Ψ left a x w := by
  have h : Measurable fun x : ℝ => g3locM Ψ left (a, x / 1, w) :=
    (measurable_g3locM hsel.1 left).comp (measurable_const.prodMk
      ((measurable_id.div_const 1).prodMk measurable_const))
  show Measurable fun x : ℝ => ((1 : ℝ) : ℂ) * g3locM Ψ left (a, x / 1, w)
  exact h.const_mul _

theorem measurableSet_mapOK (hsel : G1PsiSel γ Ψ) (left : Bool) (a : ℝ≥0 → ℝ) (m : ℕ) :
    MeasurableSet {x | mapOK Ψ left a m x} := by
  classical
  have e : {x | mapOK Ψ left a m x} = ⋂ q : ℚ × ℚ,
      (if (0 : ℝ) < q.2 ∧ ‖qpt q‖ < rhoM m then
        {x : ℝ | ‖mapX Ψ left a x (qpt q) + (x : ℂ)‖ < 1 / 2} else univ) := by
    ext x
    simp only [mem_setOf_eq, mem_iInter, mapOK]
    refine forall_congr' fun q => ?_
    split_ifs with h
    · exact ⟨fun hh => hh h.1 h.2, fun hh _ _ => hh⟩
    · simp only [mem_univ, iff_true]
      intro h1 h2; exact absurd ⟨h1, h2⟩ h
  rw [e]
  refine MeasurableSet.iInter fun q => ?_
  split_ifs
  · exact measurableSet_lt (((measurable_mapX_apply hsel left a _).add
      Complex.measurable_ofReal).norm) measurable_const
  · exact MeasurableSet.univ

theorem exists_qpt_near (w : ℂ) {ε : ℝ} (hε : 0 < ε) : ∃ q : ℚ × ℚ, ‖qpt q - w‖ < ε := by
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show w.re - ε / 2 < w.re by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show w.im - ε / 2 < w.im by linarith)
  refine ⟨(a, b), ?_⟩
  calc ‖qpt (a, b) - w‖ ≤ |(qpt (a, b) - w).re| + |(qpt (a, b) - w).im| := Complex.norm_le_abs_re_add_abs_im _
    _ < ε / 2 + ε / 2 := by
        simp only [qpt, Complex.sub_re, Complex.sub_im]
        refine add_lt_add ?_ ?_
        · rw [abs_lt]; constructor <;> linarith
        · rw [abs_lt]; constructor <;> linarith
    _ = ε := by ring

/-- **The measurable condition controls the local map on the whole upper half-ball.** -/
theorem hpsi_of_mapOK (hsel : G1PsiSel γ Ψ) {a : ℝ≥0 → ℝ} (ha : G3ZqGoodPath γ a) (left : Bool)
    {m : ℕ} {x : ℝ} (hm : mapOK Ψ left a m x) :
    ∀ w ∈ ball (0 : ℂ) (rhoM m), 0 < w.im →
      0 < (mapX Ψ left a x w).im ∧ ‖mapX Ψ left a x w + (x : ℂ)‖ ≤ 1 / 2 := by
  obtain ⟨hd, -, -⟩ := g3mapB_props hsel ha.1 ha.2 left (zero_lt_one' ℝ) (x / 1)
  have hHo : IsOpen H := isOpen_lt continuous_const Complex.continuous_im
  intro w hw hwim
  have hwH : w ∈ H := hwim
  refine ⟨?_, ?_⟩
  · obtain ⟨φ, hφ, hΨa⟩ := hsel.2.2 a ha.1 ha.2 left
    obtain ⟨-, -, -, hmaps⟩ := G1.invFunOn_props (G1.isOpen_component ha.2 left) hφ
    have hB : w + (g3bpre Ψ left a (x / 1) : ℂ) ∈ H := by
      show 0 < (w + (g3bpre Ψ left a (x / 1) : ℂ)).im
      simpa using hwim
    have h1 := G1ZA1a.sideDom_subset_H _ left (hmaps hB)
    rw [← hΨa] at h1
    show 0 < ((1 : ℝ) * (Ψ left a (w + (g3bpre Ψ left a (x / 1) : ℂ)) - ((x / 1 : ℝ) : ℂ))).im
    have h1' : 0 < (Ψ left a (w + (g3bpre Ψ left a (x / 1) : ℂ))).im := h1
    simpa using h1'
  · by_contra hc
    push_neg at hc
    have hcont : ContinuousAt (fun u => ‖mapX Ψ left a x u + (x : ℂ)‖) w :=
      ((hd.differentiableAt (hHo.mem_nhds hwH)).continuousAt.add continuousAt_const).norm
    have hO : ∀ᶠ u in 𝓝 w, 1 / 2 < ‖mapX Ψ left a x u + (x : ℂ)‖ ∧ u ∈ ball (0 : ℂ) (rhoM m) ∧
        0 < u.im :=
      (hcont.eventually (lt_mem_nhds hc)).and ((isOpen_ball.eventually_mem hw).and
        (hHo.eventually_mem hwH))
    obtain ⟨ε, hε, hεs⟩ := Metric.eventually_nhds_iff.1 hO
    obtain ⟨q, hq⟩ := exists_qpt_near w hε
    obtain ⟨h1, h2, h3⟩ := hεs (by rw [dist_eq_norm]; exact hq)
    have h2' : ‖qpt q‖ < rhoM m := by simpa using h2
    have h3' : (0 : ℝ) < q.2 := by simpa [qpt] using h3
    linarith [hm q h3' h2']

end ZqC
end Thm18Asm
end QuantumZipper
