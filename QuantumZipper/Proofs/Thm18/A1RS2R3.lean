import QuantumZipper.Proofs.Thm18.G1SSR2Det

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS2 (7): (R3) continuity of the regularized pairings along the pushed side circles

Deterministic, for a regular sample `x` (witness `F`) and a map `ψ` agreeing on `ℍ` with a map
`ψe` continuous on `ℍ̄`, `ψe(ℍ̄) ⊆ ℍ̄`, under the countable Cauchy condition `G1SSR2.UCond x ψ`
(which holds a.s. for the Theorem 1.8 field and the side maps, G1SSR2Meas.lean):

* `cauchy_bound_N`: the Cauchy bound of `G1SSR2.cauchy_bound` with the box index `N` fixed, hence
  uniform over the parameters `(d, r)` of a box (same proof);
* **`continuousOn_evalReg_push`**: `(d, r) ↦ evalReg x ((fc(d, r)).map ψ)` is continuous on
  `ℂ × (0, ∞)` (uniform limit of the continuous smoothed pairings `gCont F ψe (d, r, 2^{-k})`).

This is the continuity at `ρ = 0` input (R3) of `A1RFSmearContStmt`: the member at `ρ = 0` of the
smeared family is `ψ_* fc(d, s)`. Own bookkeeping on the proved G1SSR2 estimates.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm Thm18Asm.G1SSR2

/-- **The Cauchy bound, uniform over a box.** -/
theorem cauchy_bound_N {x : FieldSample} {F : ℂ × ℝ → ℝ} {ψ ψe : ℂ → ℂ}
    (hF : IsRegularWith x F) (hψe : ContinuousOn ψe Hbar)
    (hψeH : MapsTo ψe Hbar Hbar) (heq : EqOn ψ ψe H) (hU : UCond x ψ) (N : ℕ) {ε : ℚ}
    (hε : 0 < ε) : ∃ δ : ℝ, 0 < δ ∧ ∀ d : ℂ, ∀ r : ℝ, 0 < r → |d.re| + 1 ≤ N →
      |d.im| + 1 ≤ N → r + 1 ≤ N → 1 / ((N : ℝ) + 1) ≤ r / 2 →
      ∀ σ ∈ Ioo 0 δ, ∀ σ' ∈ Ioo 0 δ,
      |gCont F ψe (d, r, σ) - gCont F ψe (d, r, σ')| ≤ ε := by
  obtain ⟨δq, hδq, hb⟩ := hU N ε hε
  refine ⟨δq, by exact_mod_cast hδq, fun d r hr hN1 hN2 hN3 hN4 σ hσ σ' hσ' => ?_⟩
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
  obtain ⟨a, ha⟩ := G1SSR2.exists_rat_near d.re (half_pos hρ)
  obtain ⟨b, hb'⟩ := G1SSR2.exists_rat_near d.im (half_pos hρ)
  obtain ⟨rq, hrq⟩ := G1SSR2.exists_rat_near r hρ
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

/-- **(R3) Continuity of the regularized pairings along the pushed folded circles.** -/
theorem continuousOn_evalReg_push {x : FieldSample} {F : ℂ × ℝ → ℝ} {ψ ψe : ℂ → ℂ}
    (hF : IsRegularWith x F) (hψm : Measurable ψ) (hψe : ContinuousOn ψe Hbar)
    (hψeH : MapsTo ψe Hbar Hbar) (heq : EqOn ψ ψe H) (hU : UCond x ψ) :
    ContinuousOn (fun p : ℂ × ℝ => evalReg x ((foldedCircle p.1 p.2).map ψ)) (univ ×ˢ Ioi 0) := by
  set g : ℕ → ℂ × ℝ → ℝ := fun k p => gCont F ψe (p.1, p.2, radius k) with hg
  set E : ℂ × ℝ → ℝ := fun p => evalReg x ((foldedCircle p.1 p.2).map ψ) with hE
  have hpair : ∀ p : ℂ × ℝ, 0 < p.2 → ∀ k : ℕ,
      ∫ w, avgReg x k w ∂((foldedCircle p.1 p.2).map ψ) = g k p := by
    intro p hp k
    have hak : Measurable (avgReg x k) :=
      (measurable_avgReg k).comp (measurable_const.prodMk measurable_id)
    rw [integral_map hψm.aemeasurable hak.aestronglyMeasurable]
    refine integral_congr_ae ((TwoPoint.foldedCircle_ae_mem_H p.1 hp).mono fun u hu => ?_)
    have hmem : ψ u ∈ Hbar := by rw [heq hu]; exact hψeH (mem_Hbar_of_mem_H' hu)
    show avgReg x k (ψ u) = F (ψe u, radius k)
    have e1 : avgReg x k (ψ u) = F (ψ u, radius k) := (hF.2.1 k (ψ u) hmem).limUnder_eq
    rw [e1, heq hu]
  intro p₀ hp₀
  have hr₀ : 0 < p₀.2 := hp₀.2
  obtain ⟨N, hN⟩ := exists_nat_gt (|p₀.1.re| + |p₀.1.im| + 2 * p₀.2 + 4 / p₀.2 + 2)
  have h4 : 0 < 4 / p₀.2 := by positivity
  set U : Set (ℂ × ℝ) := {p | |p.1.re - p₀.1.re| < 1 ∧ |p.1.im - p₀.1.im| < 1 ∧
    |p.2 - p₀.2| < p₀.2 / 2} with hUdef
  have hUo : IsOpen U := by
    have c1 : Continuous fun p : ℂ × ℝ => p.1 := continuous_fst
    exact (isOpen_lt (continuous_abs.comp ((Complex.continuous_re.comp c1).sub continuous_const))
      continuous_const).inter ((isOpen_lt (continuous_abs.comp ((Complex.continuous_im.comp c1).sub
      continuous_const)) continuous_const).inter (isOpen_lt (continuous_abs.comp
      (continuous_snd.sub continuous_const)) continuous_const))
  have hp₀U : p₀ ∈ U := by
    refine ⟨by simp, by simp, by simp; linarith⟩
  have hbox : ∀ p ∈ U, 0 < p.2 ∧ |p.1.re| + 1 ≤ N ∧ |p.1.im| + 1 ≤ N ∧ p.2 + 1 ≤ N ∧
      1 / ((N : ℝ) + 1) ≤ p.2 / 2 := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hp
    have a1 := abs_sub_abs_le_abs_sub p.1.re p₀.1.re
    have a2 := abs_sub_abs_le_abs_sub p.1.im p₀.1.im
    have a3 := abs_lt.1 h3
    have hp2 : p₀.2 / 2 < p.2 := by linarith
    refine ⟨by linarith, by linarith [abs_nonneg p₀.1.im], by linarith [abs_nonneg p₀.1.re],
      by linarith [abs_nonneg p₀.1.re, abs_nonneg p₀.1.im], ?_⟩
    rw [div_le_div_iff₀ (by positivity) two_pos]
    have : 4 / p₀.2 < N := by linarith [abs_nonneg p₀.1.re, abs_nonneg p₀.1.im]
    rw [div_lt_iff₀ hr₀] at this
    nlinarith
  -- uniform Cauchy on `U`
  have hrad : Tendsto radius atTop (𝓝 0) :=
    RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds
  have hUC : ∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ j ≥ K, ∀ p ∈ U, dist (g k p) (g j p) < ε := by
    intro ε hε
    obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn hε
    obtain ⟨δ, hδ, hb⟩ := cauchy_bound_N hF hψe hψeH heq hU N (ε := q) (by exact_mod_cast hq0)
    obtain ⟨K, hK⟩ := eventually_atTop.1 (hrad.eventually (gt_mem_nhds hδ))
    refine ⟨K, fun k hk j hj p hp => ?_⟩
    obtain ⟨hp0, hp1, hp2, hp3, hp4⟩ := hbox p hp
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (hb p.1 p.2 hp0 hp1 hp2 hp3 hp4 _ ⟨radius_pos k, hK k hk⟩ _
      ⟨radius_pos j, hK j hj⟩) hqε
  have hlim : ∀ p ∈ U, Tendsto (fun k => g k p) atTop (𝓝 (E p)) := by
    intro p hp
    have hc : CauchySeq fun k => g k p := by
      rw [Metric.cauchySeq_iff']
      intro ε hε
      obtain ⟨K, hK⟩ := hUC ε hε
      exact ⟨K, fun k hk => hK k hk K le_rfl p hp⟩
    obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hc
    have ha' : Tendsto (fun k => ∫ w, avgReg x k w ∂((foldedCircle p.1 p.2).map ψ)) atTop
        (𝓝 a) := ha.congr fun k => (hpair p (hbox p hp).1 k).symm
    have e : E p = a := ha'.limUnder_eq
    rw [e]; exact ha
  have hTU : TendstoUniformlyOn g E atTop U := by
    refine UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto ?_ hlim
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨K, hK⟩ := hUC ε hε
    exact ⟨K, fun k hk j hj p hp => hK k hk j hj p hp⟩
  have hgc : ∀ k : ℕ, ContinuousOn (g k) U := by
    intro k
    exact (continuousOn_gCont hF hψe hψeH).comp
      (f := fun p : ℂ × ℝ => ((p.1, p.2, radius k) : ℂ × ℝ × ℝ))
      (by fun_prop) fun p _ => ⟨mem_univ _, mem_univ _, radius_pos k⟩
  have hEc : ContinuousOn E U :=
    hTU.continuousOn (Eventually.frequently (Eventually.of_forall hgc))
  exact (hEc.continuousAt (hUo.mem_nhds hp₀U)).continuousWithinAt

end A1RS
end R18
end QuantumZipper
