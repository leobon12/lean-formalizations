import QuantumZipper.Proofs.Thm18.A1RSParamE

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS (14): box facts and the uniform radius modulus of `a1rfNu`

On the parameter boxes `t ∈ (0, T]`, `‖d‖ ≤ 2R`, `s ∈ [e^{-R}, e^R]`:

* `a1rMu_box_facts`: the pushed side circles are probability measures on `ℍ̄` with support in one
  ball `closedBall 0 R₁` and mass `≤ C_m δ^{1/2}` in the strips `{Im ≤ δ}`;
* `norm_fwdMapInv_le_unif`: `‖f_t⁻¹ u‖ ≤ ‖u‖ + C` for all `u` and `t ∈ (0, T]` (the reverse flow
  moves points by at most `6M + 6√t`, `CaraR.norm_revMap_sub_self_le`; Lawler, *Conformally
  Invariant Processes in the Plane*, Lemma 4.12; `f_t⁻¹ = 0` below `ℝ`);
* **`a1rfNu_radius_unif`**: `|E(ν_ρ − ν_ρ')| ≤ C₁ |ρ − ρ'|^{a₁}` uniformly on the box, for
  `ρ, ρ' ∈ [0, 1]` — the radius modulus of the Kolmogorov family behind `A1RFSmearContStmt`
  (from `abs_kernelCov2_smeared_radius_le` and `isFrostman_a1rfNu_unif`).

Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Set Filter Metric Complex
open scoped Topology ENNReal

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm Thm18Asm.G1RC TwoPoint

/-- **Uniform facts on the pushed side circles over a box.** -/
theorem a1rMu_box_facts {W : ℝ → ℝ} (hG : G1zDrvGood W) (left : Bool) {T : ℝ} (hT : 0 < T)
    (R : ℕ) :
    ∃ R₁ Cm : ℝ, 0 ≤ R₁ ∧ 0 ≤ Cm ∧ ∀ t ∈ Ioc (0 : ℝ) T, ∀ d : ℂ, ‖d‖ ≤ 2 * R → ∀ s : ℝ,
      Real.exp (-R) ≤ s → s ≤ Real.exp R →
        IsProbabilityMeasure (a1rMu W t left d s) ∧
        (∀ᵐ z ∂a1rMu W t left d s, 0 ≤ z.im ∧ ‖z‖ ≤ R₁) ∧
        ∀ δ : ℝ, 0 < δ → (a1rMu W t left d s).real {z : ℂ | z.im ≤ δ} ≤ Cm * δ ^ (1 / 2 : ℝ) := by
  obtain ⟨ψe, -, hψc, hψeq, -⟩ := exists_sideMap_ext hG left
  set R₂ : ℝ := 2 * R + Real.exp R with hR₂
  have hK : IsCompact (Hbar ∩ closedBall (0 : ℂ) R₂) :=
    (isCompact_closedBall (0 : ℂ) R₂).inter_left isClosed_Hbar
  obtain ⟨Bψ, hBψ⟩ := hK.exists_bound_of_continuousOn (hψc.mono inter_subset_left)
  obtain ⟨MW, hMW⟩ := RegCont.exists_abs_le_on_Icc hG.1 T
  have hMW0 : 0 ≤ MW := (abs_nonneg _).trans (hMW 0 ⟨le_rfl, hT.le⟩)
  have hBψ0 : 0 ≤ Bψ := by
    have := hBψ 0 ⟨show (0 : ℝ) ≤ (0 : ℂ).im by simp, by simp [hR₂]; positivity⟩
    exact (norm_nonneg _).trans this
  set R₁ : ℝ := Bψ + 24 * MW + 8 * Real.sqrt T with hR₁
  have hs₀ : 0 < Real.exp (-(R : ℝ)) := Real.exp_pos _
  obtain ⟨Cm, hCm, hmass⟩ := a1rMu_strip_le_unif hG hT left (R₀ := max (2 * R) (Real.exp R)) hs₀
  refine ⟨R₁, Cm, by positivity, hCm, fun t ht d hd s hs1 hs2 => ?_⟩
  have hs : 0 < s := hs₀.trans_le hs1
  obtain ⟨-, -, g, hgm, hEq⟩ := A1R.sidePush_props hG ht.1 left
  have hmapeq : a1rMu W t left d s = (foldedCircle d s).map g := by
    unfold a1rMu
    refine Measure.map_congr ?_
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hs] with u hu
    exact hEq hu
  have hP : IsProbabilityMeasure (a1rMu W t left d s) := by
    rw [hmapeq]; exact (Measure.isProbabilityMeasure_map_iff hgm.aemeasurable).2 inferInstance
  refine ⟨hP, ?_, fun δ hδ => hmass t ht d (hd.trans (le_max_left _ _)) s hs1
      (hs2.trans (le_max_right _ _)) δ hδ⟩
  have hcl : MeasurableSet {z : ℂ | 0 ≤ z.im ∧ ‖z‖ ≤ R₁} :=
    (measurableSet_le measurable_const Complex.continuous_im.measurable).inter
      (measurableSet_le measurable_norm measurable_const)
  rw [hmapeq, ae_map_iff hgm.aemeasurable hcl]
  filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hs,
    TwoPoint.foldedCircle_ae_norm_le d hs.le] with w hw hwn
  have hmem := sideMap_mem_compl_fwdHull hG ht.1.le left hw
  have hgw : g w = fwdMap W t (g1zSideMap left W w) := (hEq hw).symm
  rw [hgw]
  refine ⟨(FwdHolo.mapsTo_fwdMap hG.1 ht.1.le hmem).le, ?_⟩
  have h1 := CoreArc.norm_fwdMap_sub_le_uniform hG.1 hG.2.1 ht.1
    (fun r hr => hMW r ⟨hr.1, hr.2.trans ht.2⟩) hmem
  have h2 : ‖g1zSideMap left W w‖ ≤ Bψ := by
    rw [hψeq hw]
    refine hBψ w ⟨show 0 ≤ w.im from le_of_lt hw, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    have : ‖d‖ + s ≤ R₂ := by rw [hR₂]; linarith
    linarith
  have h3 : Real.sqrt t ≤ Real.sqrt T := Real.sqrt_le_sqrt ht.2
  have h4 := norm_sub_norm_le (fwdMap W t (g1zSideMap left W w)) (g1zSideMap left W w)
  rw [hR₁]
  linarith

/-- **`f_t⁻¹` moves points by a bounded amount, uniformly for `t ∈ (0, T]`.** -/
theorem norm_fwdMapInv_le_unif {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ}
    (hT : 0 < T) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioc (0 : ℝ) T, ∀ u : ℂ,
      ‖fwdMapInv W t u‖ ≤ ‖u‖ + C := by
  obtain ⟨M, hM⟩ := RegCont.exists_abs_le_on_Icc hW T
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, hT.le⟩)
  refine ⟨6 * M + 6 * Real.sqrt T, by positivity, fun t ht u => ?_⟩
  rcases le_or_gt u.im 0 with hu | hu
  · rw [RTBeur.fwdMapInv_of_im_nonpos hW ht.1.le hu, norm_zero]
    positivity
  · have huH : u ∈ H := hu
    rw [UnzipInvariance.fwdMapInv_eq_revMap_timeRev W hW hW0 ht.1.le huH]
    have hV : Continuous (fun s => W (t - s) - W t) :=
      (hW.comp (continuous_const.sub continuous_id)).sub continuous_const
    have hb : ∀ r ∈ Icc (0 : ℝ) t, |W (t - r) - W t| ≤ 2 * M := fun r hr => by
      have h1 := abs_le.1 (hM (t - r) ⟨by linarith [hr.2], by linarith [hr.1, ht.2]⟩)
      have h2 := abs_le.1 (hM t ⟨ht.1.le, ht.2⟩)
      rw [abs_le]; constructor <;> linarith
    have := CaraR.norm_revMap_sub_self_le hV ht.1 hb huH
    have h3 : Real.sqrt t ≤ Real.sqrt T := Real.sqrt_le_sqrt ht.2
    have h4 := norm_sub_norm_le (revMap (fun s => W (t - s) - W t) t u) u
    linarith

/-- **Uniform radius modulus of the smeared-loop family.** -/
theorem a1rfNu_radius_unif {W : ℝ → ℝ} (hG : G1zDrvGood W) (left : Bool) {T : ℝ} (hT : 0 < T)
    (R : ℕ) :
    ∃ C₁ a₁ : ℝ, 0 ≤ C₁ ∧ 0 < a₁ ∧ ∀ t ∈ Ioc (0 : ℝ) T, ∀ d : ℂ, ‖d‖ ≤ 2 * R → ∀ s : ℝ,
      Real.exp (-R) ≤ s → s ≤ Real.exp R → ∀ ρ ∈ Icc (0 : ℝ) 1, ∀ ρ' ∈ Icc (0 : ℝ) 1,
        |kernelCov2 neumannH (a1rfNu W t left d s ρ, a1rfNu W t left d s ρ')
          (a1rfNu W t left d s ρ, a1rfNu W t left d s ρ')| ≤ C₁ * |ρ - ρ'| ^ a₁ := by
  obtain ⟨R₁, Cm, hR₁, hCm, hbox⟩ := a1rMu_box_facts hG left hT R
  obtain ⟨α, CF, hα, hα1, hCF, hFr⟩ := isFrostman_a1rfNu_unif hG left hT R
  obtain ⟨Ci, hCi, hinv⟩ := norm_fwdMapInv_le_unif hG.1 hG.2.1 hT
  set Bf := R₁ + 1 + Ci with hBf
  refine ⟨2 * (holderKα α CF Bf * Real.sqrt ((R₁ + 1) ^ 2 + 4 * T) ^ (α / 2) +
      4 * potMaxα α CF Bf * (2 * Cm + 2)), min (α / 4) (1 / 8 : ℝ), ?_,
      lt_min (by linarith) (by norm_num), ?_⟩
  · have h1 := holderKα_nonneg hα hCF (by positivity : (0 : ℝ) ≤ Bf)
    have h2 := potMaxα_nonneg hα hCF (by positivity : (0 : ℝ) ≤ Bf)
    have h3 := Real.rpow_nonneg (Real.sqrt_nonneg ((R₁ + 1) ^ 2 + 4 * T)) (α / 2)
    positivity
  intro t ht d hd s hs1 hs2 ρ hρ ρ' hρ'
  obtain ⟨hP, hsupp, hmass⟩ := hbox t ht d hd s hs1 hs2
  exact abs_kernelCov2_smeared_radius_le hG.1 hG.2.1 ht.1.le ht.2 hR₁ hCm hα hα1 hCF
    (by positivity) hsupp hmass (fun σ hσ => hFr t ht d hd s hs1 hs2 σ hσ)
    (fun u hu => (hinv t ht u).trans (by rw [hBf]; linarith)) hρ hρ'

end A1RS
end R18
end QuantumZipper
