import QuantumZipper.Proofs.Thm18.G1SSRMain
import QuantumZipper.Proofs.LQG.IndepParams

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1SSR2 (1): a countable condition giving the continuum limit at all pushed circles

Theorem 1.8, G1 zoom, node `G1SidePushContStmt` (G1SSRMain.lean). Deterministic part.

For a field `x` and a map `ψ`, `gPush x ψ d r σ = ∫ evalReg x (fc(ψ u, σ)) dfc(d, r)(u)` is the
circle-smoothed pairing of `x` against the pushed folded circle `ψ_* fc(d, r)`. `UCond x ψ` is a
countable uniform Cauchy condition at rational parameters. If `x` is a regular sample and `ψ`
agrees on `ℍ` with a map continuous on `ℍ̄`, then `UCond x ψ` gives the continuum limit
`F1.ContData x (ψ_* fc(d, r))` at every `d` and `r > 0` (`contData_of_ucond`): the pairings are
jointly continuous for `σ > 0` (`RegClosure.continuousOn_integral_fc`), so the rational Cauchy
bound extends to all parameters, and `ℝ` is complete.

This is the countable form of the continuum limit that is transported from the explicit wedge
representative to `(Y, B)` (G1SSR2Meas.lean). Own elementary argument (density of rationals and
completeness; the analytic content is Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1).
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1SSR2

/-- The smoothed pairing of `x` against the pushed folded circle `ψ_* fc(d, r)`. -/
def gPush (x : FieldSample) (ψ : ℂ → ℂ) (d : ℂ) (r σ : ℝ) : ℝ :=
  ∫ u, evalReg x (foldedCircle (ψ u) σ) ∂(foldedCircle d r)

/-- **Countable uniform Cauchy condition** of the smoothed pairings as `σ → 0⁺`. -/
def UCond (x : FieldSample) (ψ : ℂ → ℂ) : Prop :=
  ∀ N : ℕ, ∀ ε : ℚ, 0 < ε → ∃ δ : ℚ, 0 < δ ∧ ∀ a b r σ σ' : ℚ,
    |(a : ℝ)| ≤ N → |(b : ℝ)| ≤ N → 1 / ((N : ℝ) + 1) ≤ r → (r : ℝ) ≤ N →
    0 < σ → σ < δ → 0 < σ' → σ' < δ →
    |gPush x ψ ⟨a, b⟩ r σ - gPush x ψ ⟨a, b⟩ r σ'| ≤ ε

theorem mem_Hbar_of_mem_H' {u : ℂ} (hu : u ∈ H) : u ∈ Hbar :=
  show (0 : ℝ) ≤ u.im from le_of_lt (show (0 : ℝ) < u.im from hu)

theorem exists_rat_near (x : ℝ) {ρ : ℝ} (hρ : 0 < ρ) : ∃ q : ℚ, |(q : ℝ) - x| < ρ := by
  obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show x - ρ < x + ρ by linarith)
  exact ⟨q, abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩⟩

section Det

variable {x : FieldSample} {F : ℂ × ℝ → ℝ} {ψ ψe : ℂ → ℂ}

/-- The continuous version of the pairing. -/
def gCont (F : ℂ × ℝ → ℝ) (ψe : ℂ → ℂ) (p : ℂ × ℝ × ℝ) : ℝ :=
  ∫ u, F (ψe u, p.2.2) ∂foldedCircle p.1 p.2.1

theorem gPush_eq (hF : IsRegularWith x F) (heq : EqOn ψ ψe H) (hψeH : MapsTo ψe Hbar Hbar)
    (d : ℂ) {r σ : ℝ} (hr : 0 < r) (hσ : 0 < σ) : gPush x ψ d r σ = gCont F ψe (d, r, σ) := by
  unfold gPush gCont
  refine integral_congr_ae ((TwoPoint.foldedCircle_ae_mem_H d hr).mono fun u hu => ?_)
  simp only
  rw [heq hu, hF.evalReg_fc_of_mem (hψeH (mem_Hbar_of_mem_H' hu)) hσ]

theorem continuousOn_gCont (hF : IsRegularWith x F) (hψe : ContinuousOn ψe Hbar)
    (hψeH : MapsTo ψe Hbar Hbar) :
    ContinuousOn (gCont F ψe) (univ ×ˢ univ ×ˢ Ioi 0) := by
  refine RegClosure.continuousOn_integral_fc (P := ℂ × ℝ × ℝ) (S := univ ×ˢ univ ×ˢ Ioi 0)
    (H := fun p u => F (ψe u, p.2.2)) ?_ continuousOn_fst
    (continuous_snd.fst.continuousOn)
  refine hF.1.comp ((hψe.comp continuousOn_snd fun q hq => hq.2).prodMk
    (continuous_fst.snd.snd.continuousOn)) fun q hq => ⟨hψeH hq.2, hq.1.2.2⟩

theorem continuousAt_gCont (hF : IsRegularWith x F) (hψe : ContinuousOn ψe Hbar)
    (hψeH : MapsTo ψe Hbar Hbar) {p : ℂ × ℝ × ℝ} (hp : 0 < p.2.2) :
    ContinuousAt (gCont F ψe) p :=
  (continuousOn_gCont hF hψe hψeH).continuousAt
    ((isOpen_univ.prod (isOpen_univ.prod isOpen_Ioi)).mem_nhds ⟨mem_univ _, mem_univ _, hp⟩)

/-- Closeness in `ℂ × ℝ × ℝ` from closeness of the real coordinates. -/
theorem dist_lt_of_coord {a b r a' b' r' σ : ℝ} {ρ : ℝ} (ha : |a - a'| < ρ / 2)
    (hb : |b - b'| < ρ / 2) (hr : |r - r'| < ρ) (hρ : 0 < ρ) :
    dist ((⟨a, b⟩ : ℂ), r, σ) ((⟨a', b'⟩ : ℂ), r', σ) < ρ := by
  rw [Prod.dist_eq, Prod.dist_eq, dist_self, Complex.dist_eq, Real.dist_eq]
  have h1 : ‖(⟨a, b⟩ : ℂ) - ⟨a', b'⟩‖ < ρ := by
    refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
    simp only [Complex.sub_re, Complex.sub_im]
    linarith
  exact max_lt h1 (max_lt hr hρ)

/-- **The rational Cauchy bound extends to all parameters.** -/
theorem cauchy_bound (hF : IsRegularWith x F) (hψe : ContinuousOn ψe Hbar)
    (hψeH : MapsTo ψe Hbar Hbar) (heq : EqOn ψ ψe H) (hU : UCond x ψ) (d : ℂ) {r : ℝ}
    (hr : 0 < r) {ε : ℚ} (hε : 0 < ε) : ∃ δ : ℝ, 0 < δ ∧ ∀ σ ∈ Ioo 0 δ, ∀ σ' ∈ Ioo 0 δ,
      |gCont F ψe (d, r, σ) - gCont F ψe (d, r, σ')| ≤ ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (|d.re| + |d.im| + r + 2 / r + 2)
  have hN1 : |d.re| + 1 ≤ N := by linarith [abs_nonneg d.im, (div_pos two_pos hr).le]
  have hN2 : |d.im| + 1 ≤ N := by linarith [abs_nonneg d.re, (div_pos two_pos hr).le]
  have hN3 : r + 1 ≤ N := by linarith [abs_nonneg d.re, abs_nonneg d.im, (div_pos two_pos hr).le]
  have hN4 : 1 / ((N : ℝ) + 1) ≤ r / 2 := by
    rw [div_le_div_iff₀ (by positivity) two_pos]
    have : 2 / r < N := by linarith [abs_nonneg d.re, abs_nonneg d.im]
    rw [div_lt_iff₀ hr] at this
    nlinarith
  obtain ⟨δq, hδq, hb⟩ := hU N ε hε
  refine ⟨δq, by exact_mod_cast hδq, fun σ hσ σ' hσ' => ?_⟩
  refine le_of_forall_pos_lt_add fun η hη => ?_
  have hc1 := Metric.continuousAt_iff.1 (continuousAt_gCont hF hψe hψeH (p := (d, r, σ)) hσ.1)
  have hc2 := Metric.continuousAt_iff.1 (continuousAt_gCont hF hψe hψeH (p := (d, r, σ')) hσ'.1)
  obtain ⟨ρ₁, hρ₁, h₁⟩ := hc1 (η / 4) (by positivity)
  obtain ⟨ρ₂, hρ₂, h₂⟩ := hc2 (η / 4) (by positivity)
  set ρ := min (min ρ₁ ρ₂) (min (1 / 2) (r / 2)) with hρdef
  have hρ : 0 < ρ := by positivity
  have hρ1 : ρ ≤ ρ₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρ2 : ρ ≤ ρ₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρh : ρ ≤ 1 / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρr : ρ ≤ r / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  obtain ⟨a, ha⟩ := exists_rat_near d.re (half_pos hρ)
  obtain ⟨b, hb'⟩ := exists_rat_near d.im (half_pos hρ)
  obtain ⟨rq, hrq⟩ := exists_rat_near r hρ
  have hrq0 : r / 2 < rq := by linarith [(abs_sub_lt_iff.1 hrq).2]
  have hdq : ((⟨(a : ℝ), (b : ℝ)⟩ : ℂ).re) = a := rfl
  -- closeness of the rational centre and radius
  have hd1 : dist (gCont F ψe ((⟨(a : ℝ), (b : ℝ)⟩ : ℂ), (rq : ℝ), σ)) (gCont F ψe (d, r, σ)) <
      η / 4 := by
    refine h₁ (lt_of_lt_of_le ?_ hρ1)
    have := dist_lt_of_coord (σ := σ) ha hb' hrq hρ
    simpa using this
  have hd2 : dist (gCont F ψe ((⟨(a : ℝ), (b : ℝ)⟩ : ℂ), (rq : ℝ), σ')) (gCont F ψe (d, r, σ')) <
      η / 4 := by
    refine h₂ (lt_of_lt_of_le ?_ hρ2)
    have := dist_lt_of_coord (σ := σ') ha hb' hrq hρ
    simpa using this
  -- rational smoothing radii
  have hq1 := Metric.continuousAt_iff.1 (continuousAt_gCont hF hψe hψeH
    (p := ((⟨(a : ℝ), (b : ℝ)⟩ : ℂ), (rq : ℝ), σ)) hσ.1)
  have hq2 := Metric.continuousAt_iff.1 (continuousAt_gCont hF hψe hψeH
    (p := ((⟨(a : ℝ), (b : ℝ)⟩ : ℂ), (rq : ℝ), σ')) hσ'.1)
  obtain ⟨τ₁, hτ₁, k₁⟩ := hq1 (η / 4) (by positivity)
  obtain ⟨τ₂, hτ₂, k₂⟩ := hq2 (η / 4) (by positivity)
  obtain ⟨s₁, hs₁a, hs₁b⟩ := exists_rat_btwn (show max 0 (σ - τ₁) < min (σ + τ₁) δq by
    refine max_lt (lt_min (by linarith [hσ.1]) (by exact_mod_cast hδq))
      (lt_min (by linarith) (by linarith [hσ.2])))
  obtain ⟨s₂, hs₂a, hs₂b⟩ := exists_rat_btwn (show max 0 (σ' - τ₂) < min (σ' + τ₂) δq by
    refine max_lt (lt_min (by linarith [hσ'.1]) (by exact_mod_cast hδq))
      (lt_min (by linarith) (by linarith [hσ'.2])))
  have hs₁0 : (0 : ℝ) < s₁ := lt_of_le_of_lt (le_max_left _ _) hs₁a
  have hs₂0 : (0 : ℝ) < s₂ := lt_of_le_of_lt (le_max_left _ _) hs₂a
  have hs₁δ : (s₁ : ℝ) < δq := lt_of_lt_of_le hs₁b (min_le_right _ _)
  have hs₂δ : (s₂ : ℝ) < δq := lt_of_lt_of_le hs₂b (min_le_right _ _)
  have he1 : dist (gCont F ψe ((⟨(a : ℝ), (b : ℝ)⟩ : ℂ), (rq : ℝ), (s₁ : ℝ)))
      (gCont F ψe ((⟨(a : ℝ), (b : ℝ)⟩ : ℂ), (rq : ℝ), σ)) < η / 4 := by
    refine k₁ ?_
    rw [Prod.dist_eq, Prod.dist_eq, dist_self, dist_self, Real.dist_eq]
    refine max_lt hτ₁ (max_lt hτ₁ (abs_sub_lt_iff.2 ⟨?_, ?_⟩))
    · linarith [lt_of_lt_of_le hs₁b (min_le_left _ _)]
    · linarith [lt_of_le_of_lt (le_max_right _ _) hs₁a]
  have he2 : dist (gCont F ψe ((⟨(a : ℝ), (b : ℝ)⟩ : ℂ), (rq : ℝ), (s₂ : ℝ)))
      (gCont F ψe ((⟨(a : ℝ), (b : ℝ)⟩ : ℂ), (rq : ℝ), σ')) < η / 4 := by
    refine k₂ ?_
    rw [Prod.dist_eq, Prod.dist_eq, dist_self, dist_self, Real.dist_eq]
    refine max_lt hτ₂ (max_lt hτ₂ (abs_sub_lt_iff.2 ⟨?_, ?_⟩))
    · linarith [lt_of_lt_of_le hs₂b (min_le_left _ _)]
    · linarith [lt_of_le_of_lt (le_max_right _ _) hs₂a]
  -- the rational bound
  have hbox := hb a b rq s₁ s₂ (by linarith [abs_sub_abs_le_abs_sub (a : ℝ) d.re,
      (abs_sub_lt_iff.1 ha).1])
    (by linarith [abs_sub_abs_le_abs_sub (b : ℝ) d.im])
    (by linarith) (by linarith [(abs_sub_lt_iff.1 hrq).1])
    (by exact_mod_cast hs₁0) (by exact_mod_cast hs₁δ) (by exact_mod_cast hs₂0)
    (by exact_mod_cast hs₂δ)
  have hrq0' : (0 : ℝ) < rq := by linarith
  rw [gPush_eq hF heq hψeH _ hrq0' hs₁0, gPush_eq hF heq hψeH _ hrq0' hs₂0] at hbox
  rw [Real.dist_eq] at hd1 hd2 he1 he2
  have := abs_sub_le (gCont F ψe (d, r, σ)) (gCont F ψe ((⟨(a : ℝ), (b : ℝ)⟩ : ℂ), (rq : ℝ), σ))
    (gCont F ψe (d, r, σ'))
  rw [abs_sub_lt_iff] at hd1 hd2 he1 he2
  rw [abs_le] at hbox
  rw [abs_sub_lt_iff]
  constructor <;> linarith [hd1.1, hd1.2, hd2.1, hd2.2, he1.1, he1.2, he2.1, he2.2, hbox.1, hbox.2]

/-- **The continuum limit at every pushed folded circle from the countable condition.** -/
theorem contData_of_ucond (hF : IsRegularWith x F) (hψm : Measurable ψ)
    (hψe : ContinuousOn ψe Hbar) (hψeH : MapsTo ψe Hbar Hbar) (heq : EqOn ψ ψe H)
    (hU : UCond x ψ) (d : ℂ) {r : ℝ} (hr : 0 < r) :
    F1.ContData x ((foldedCircle d r).map ψ) := by
  have hmeas : ∀ ρ : ℝ, Measurable fun v : ℂ => evalReg x (foldedCircle v ρ) := fun ρ =>
    g1z2_measurable_evalReg_fc x ρ
  have hint' : ∀ ρ : ℝ, 0 < ρ →
      Integrable (fun u => evalReg x (foldedCircle (ψ u) ρ)) (foldedCircle d r) := by
    intro ρ hρ
    have hg : ContinuousOn (fun u => F (ψe u, ρ)) Hbar :=
      hF.1.comp (hψe.prodMk continuousOn_const) fun u hu => ⟨hψeH hu, hρ⟩
    refine (RegClosure.integrable_fc hg d hr.le).congr
      ((TwoPoint.foldedCircle_ae_mem_H d hr).mono fun u hu => ?_)
    simp only
    rw [heq hu, hF.evalReg_fc_of_mem (hψeH (mem_Hbar_of_mem_H' hu)) hρ]
  have hmap : ∀ ρ : ℝ, 0 < ρ → ∫ v, evalReg x (foldedCircle v ρ) ∂((foldedCircle d r).map ψ) =
      gCont F ψe (d, r, ρ) := fun ρ hρ => by
    rw [integral_map hψm.aemeasurable (hmeas ρ).aestronglyMeasurable]
    exact gPush_eq hF heq hψeH d hr hρ
  refine ⟨fun ρ hρ => (integrable_map_measure (hmeas ρ).aestronglyMeasurable
    hψm.aemeasurable).2 (hint' ρ hρ), ?_⟩
  set f : ℝ → ℝ := fun σ => gCont F ψe (d, r, σ) with hf
  have hcauchy : Cauchy (map f (𝓝[>] (0 : ℝ))) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ?_⟩
    obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn (half_pos hε)
    obtain ⟨δ, hδ, hb⟩ := cauchy_bound hF hψe hψeH heq hU d hr (ε := q) (by exact_mod_cast hq0)
    refine ⟨f '' Ioo 0 δ, image_mem_map (Ioo_mem_nhdsGT hδ), ?_⟩
    rintro _ ⟨σ, hσ, rfl⟩ _ ⟨σ', hσ', rfl⟩
    rw [Real.dist_eq]
    have := hb σ hσ σ' hσ'
    linarith
  obtain ⟨L, hL⟩ := cauchy_map_iff_exists_tendsto.1 hcauchy
  refine ⟨L, hL.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
  exact (hmap ρ hρ).symm

end Det

end G1SSR2
end Thm18Asm
end QuantumZipper
