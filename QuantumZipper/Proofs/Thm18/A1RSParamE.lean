import QuantumZipper.Proofs.Thm18.A1RSParam

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS (13): the Neumann energy of two smeared members at different parameters

Combines the pointwise coupling `norm_smear_param_le` (A1RSParam.lean) with the abstract coupling
estimate `abs_kernelCov2_map_le` (A1RSCouple.lean) on the common angle space
`circM ⊗ angMeas` (`a1rfNu_eq_map_angles`): **`abs_kernelCov2_smear_param_le`** bounds
`|E(ν_{t,d,s,ρ} − ν_{t+h,d',s',ρ})|` by `2 (holderKα · δ^{α/2} + 2 potMaxα · ε_E)`, where `δ` is the
pointwise bound off the strips and `ε_E` the total mass of the four strips
`{Im w ≤ τ₁}`, `{Im w' ≤ τ₁}`, `{Im U ≤ τ}`, `{Im U' ≤ τ}`. The strip masses, the Frostman bounds and
the support bound are hypotheses here (they are supplied by `prod_strip_le`, `A1R.foldedCircle_strip_le`,
`isFrostman_a1rfNu_unif`). Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Set Filter Metric Complex
open scoped Topology ENNReal

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm Thm18Asm.G1RC TwoPoint

/-- **Energy of two smeared members at different parameters.** -/
theorem abs_kernelCov2_smear_param_le {W : ℝ → ℝ} (hG : G1zDrvGood W) (left : Bool)
    {t h ε τ τ₁ R B Rh ρ α CF Bf εw εU : ℝ} (ht : 0 < t) (hh : 0 ≤ h)
    (hosc1 : ∀ r ∈ Icc (0 : ℝ) h, |W (t + r) - W t| ≤ ε)
    (hosc2 : ∀ q ∈ Icc (0 : ℝ) h, |W (t + h - q) - W (t + h)| ≤ ε)
    (hB : ∀ z ∈ H, ‖z‖ < R + 1 → ‖fwdMap W t (g1zSideMap left W z)‖ ≤ B)
    (hτ : 0 < τ) (hτ₁ : 0 < τ₁) (hτ₁1 : τ₁ ≤ 1) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hα : 0 < α) (hα1 : α ≤ 1) (hCF : 0 ≤ CF) (hBf0 : 0 ≤ Bf)
    {g g' : ℂ → ℂ} (hgm : Measurable g) (hgm' : Measurable g')
    (hEq : EqOn (fun w => fwdMap W t (g1zSideMap left W w)) g H)
    (hEq' : EqOn (fun w => fwdMap W (t + h) (g1zSideMap left W w)) g' H)
    {d d' : ℂ} {s s' : ℝ} (hdR : ‖d‖ + s ≤ R) (hdR' : ‖d'‖ + s' ≤ R) (hs : 0 ≤ s) (hs' : 0 ≤ s')
    (hRh : ∀ w ∈ H, ‖w‖ ≤ R → ‖g w‖ + 1 ≤ Rh ∧ ‖g' w‖ + 1 ≤ Rh) :
    let m := G1RC.circM.prod E6.XAreaPC.angMeas
    let wq : ℝ × ℝ → ℂ := fun q => foldH (circleMap d s q.1)
    let wq' : ℝ × ℝ → ℂ := fun q => foldH (circleMap d' s' q.1)
    let Uq : ℝ × ℝ → ℂ := fun q => foldH (circleMap (g (wq q)) ρ q.2)
    let Uq' : ℝ × ℝ → ℂ := fun q => foldH (circleMap (g' (wq' q)) ρ q.2)
    IsFrostman (m.map fun q => fwdMapInv W t (Uq q)) α CF →
    IsFrostman (m.map fun q => fwdMapInv W (t + h) (Uq' q)) α CF →
    (∀ᵐ q ∂m, ‖fwdMapInv W t (Uq q)‖ ≤ Bf) → (∀ᵐ q ∂m, ‖fwdMapInv W (t + h) (Uq' q)‖ ≤ Bf) →
    m.real {q | (wq q).im ≤ τ₁} ≤ εw → m.real {q | (wq' q).im ≤ τ₁} ≤ εw →
    m.real {q | (Uq q).im ≤ τ} ≤ εU → m.real {q | (Uq' q).im ≤ τ} ≤ εU →
    |kernelCov2 neumannH (m.map fun q => fwdMapInv W t (Uq q),
        m.map fun q => fwdMapInv W (t + h) (Uq' q))
      (m.map fun q => fwdMapInv W t (Uq q), m.map fun q => fwdMapInv W (t + h) (Uq' q))| ≤
      2 * (holderKα α CF Bf * ((Real.sqrt (Rh ^ 2 + 4 * t) *
          (2 * B / τ₁ * (‖d - d'‖ + |s - s'|) + (24 * ε + 8 * Real.sqrt h)) +
        Real.sqrt ((Rh + (3 * ε + 6 * Real.sqrt h)) ^ 2 + 4 * t) * (3 * ε + 6 * Real.sqrt h)) /
          τ) ^ (α / 2) + 2 * potMaxα α CF Bf * (2 * εw + 2 * εU)) := by
  intro m wq wq' Uq Uq' hF hF' hb hb' hw1 hw2 hU1 hU2
  have hc : ∀ (c : ℂ) (r : ℝ), Measurable fun θ : ℝ => foldH (circleMap c r θ) := fun c r =>
    (CircleFubini.continuous_foldH'.measurable).comp (continuous_circleMap c r).measurable
  have hcont : ∀ (c : ℂ) (r : ℝ), Continuous fun p : ℂ × ℝ => circleMap p.1 r p.2 := by
    intro c r; unfold circleMap; fun_prop
  have hwm : Measurable wq := (hc d s).comp measurable_fst
  have hwm' : Measurable wq' := (hc d' s').comp measurable_fst
  have hUm : Measurable Uq := measurable_foldH.comp
    ((hcont 0 ρ).measurable.comp ((hgm.comp hwm).prodMk measurable_snd))
  have hUm' : Measurable Uq' := measurable_foldH.comp
    ((hcont 0 ρ).measurable.comp ((hgm'.comp hwm').prodMk measurable_snd))
  have hfi : Measurable (fwdMapInv W t) := RTBeur.measurable_fwdMapInv_rt hG.1 hG.2.1 ht.le
  have hfi' : Measurable (fwdMapInv W (t + h)) :=
    RTBeur.measurable_fwdMapInv_rt hG.1 hG.2.1 (by linarith)
  have hms : ∀ (f : ℝ × ℝ → ℂ) (c : ℝ), Measurable f → MeasurableSet {q | (f q).im ≤ c} :=
    fun f c hf => measurableSet_le (Complex.continuous_im.measurable.comp hf) measurable_const
  set E := ({q | (wq q).im ≤ τ₁} ∪ {q | (wq' q).im ≤ τ₁}) ∪
    ({q | (Uq q).im ≤ τ} ∪ {q | (Uq' q).im ≤ τ}) with hE
  have hEm : MeasurableSet E :=
    ((hms _ _ hwm).union (hms _ _ hwm')).union ((hms _ _ hUm).union (hms _ _ hUm'))
  have hEε : m.real E ≤ 2 * εw + 2 * εU := by
    refine (measureReal_union_le _ _).trans ?_
    have e1 := (measureReal_union_le (μ := m) {q | (wq q).im ≤ τ₁} {q | (wq' q).im ≤ τ₁})
    have e2 := (measureReal_union_le (μ := m) {q | (Uq q).im ≤ τ} {q | (Uq' q).im ≤ τ})
    linarith
  set δ : ℝ := (Real.sqrt (Rh ^ 2 + 4 * t) *
          (2 * B / τ₁ * (‖d - d'‖ + |s - s'|) + (24 * ε + 8 * Real.sqrt h)) +
        Real.sqrt ((Rh + (3 * ε + 6 * Real.sqrt h)) ^ 2 + 4 * t) * (3 * ε + 6 * Real.sqrt h)) /
          τ with hδ
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hosc1 0 ⟨le_rfl, hh⟩)
  have hR0 : 0 ≤ R := le_trans (by positivity) hdR
  have hB0 : 0 ≤ B := by
    have hz : ((1 / 2 : ℝ) : ℂ) * I ∈ H := by
      show 0 < (((1 / 2 : ℝ) : ℂ) * I).im; simp
    have hzn : ‖((1 / 2 : ℝ) : ℂ) * I‖ < R + 1 := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (by norm_num)]; linarith
    exact (norm_nonneg _).trans (hB _ hz hzn)
  have hδ0 : 0 ≤ δ := by positivity
  have hclose : ∀ᵐ q ∂m, q ∉ E →
      ‖fwdMapInv W t (Uq q) - fwdMapInv W (t + h) (Uq' q)‖ ≤ δ := by
    refine Eventually.of_forall fun q hq => ?_
    simp only [hE, mem_union, not_or, mem_setOf_eq, not_le] at hq
    obtain ⟨⟨hw1q, hw2q⟩, hU1q, hU2q⟩ := hq
    have hwH : wq q ∈ H := show 0 < (wq q).im by linarith
    have hwH' : wq' q ∈ H := show 0 < (wq' q).im by linarith
    have hwn : ‖wq q‖ ≤ R := by
      simp only [wq]
      rw [norm_foldH]; exact (norm_circleMap_le_add d hs q.1).trans hdR
    have hwn' : ‖wq' q‖ ≤ R := by
      simp only [wq']
      rw [norm_foldH]; exact (norm_circleMap_le_add d' hs' q.1).trans hdR'
    have hgw : g (wq q) = fwdMap W t (g1zSideMap left W (wq q)) := (hEq hwH).symm
    have hgw' : g' (wq' q) = fwdMap W (t + h) (g1zSideMap left W (wq' q)) := (hEq' hwH').symm
    have hht : ∀ c : ℂ, ‖c‖ + 1 ≤ Rh → (foldH (circleMap c ρ q.2)).im ≤ Rh := fun c hcR =>
      (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans (by
        rw [norm_foldH]; exact (norm_circleMap_le_add c hρ q.2).trans (by linarith)))
    have hR1 := (hRh _ hwH hwn).1
    have hR2 := (hRh _ hwH' hwn').2
    have hUq : Uq q = foldH (circleMap (fwdMap W t (g1zSideMap left W (wq q))) ρ q.2) := by
      simp only [Uq]; rw [hgw]
    have hUq' : Uq' q = foldH (circleMap (fwdMap W (t + h) (g1zSideMap left W (wq' q))) ρ q.2) := by
      simp only [Uq']; rw [hgw']
    rw [hgw] at hR1
    rw [hgw'] at hR2
    have a1 : τ ≤ (foldH (circleMap (fwdMap W t (g1zSideMap left W (wq q))) ρ q.2)).im := by
      rw [← hUq]; exact hU1q.le
    have a2 : τ ≤ (foldH (circleMap (fwdMap W (t + h) (g1zSideMap left W (wq' q))) ρ q.2)).im := by
      rw [← hUq']; exact hU2q.le
    have key := norm_smear_param_le hG left ht hh hosc1 hosc2 hB hτ hτ₁ hτ₁1 hw1q.le hw2q.le hwn
      hwn' a1 a2 (hht _ hR1) (hht _ hR2)
    have hww : ‖wq q - wq' q‖ ≤ ‖d - d'‖ + |s - s'| := by
      simp only [wq, wq']
      refine (TwoPoint.norm_foldH_sub_le _ _).trans ?_
      have e : circleMap d s q.1 - circleMap d' s' q.1 =
          (d - d') + (circleMap 0 s q.1 - circleMap 0 s' q.1) := by
        simp only [circleMap]; ring
      rw [e]
      refine (norm_add_le _ _).trans (add_le_add le_rfl (le_of_eq ?_))
      exact norm_circleMap_sub_radius 0 s s' q.1
    rw [hδ, le_div_iff₀ hτ, mul_comm, hUq, hUq']
    refine key.trans ?_
    have hB0' : 0 ≤ 2 * B / τ₁ := by positivity
    have := mul_le_mul_of_nonneg_left hww hB0'
    have h3 := mul_le_mul_of_nonneg_left (add_le_add_right this (24 * ε + 8 * Real.sqrt h))
      (Real.sqrt_nonneg (Rh ^ 2 + 4 * t))
    linarith
  exact abs_kernelCov2_map_le (m := m) (hfi.comp hUm) (hfi'.comp hUm') hα hα1 hF hF' hCF hBf0
    hb hb' hEm hδ0 hEε hclose

end A1RS
end R18
end QuantumZipper
