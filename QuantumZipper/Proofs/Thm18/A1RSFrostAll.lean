import QuantumZipper.Proofs.Thm18.A1RSFrostMu

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS (9): the smeared-loop measures `a1rfNu` are Frostman, uniformly on parameter boxes

**`isFrostman_a1rfNu_unif`**: for a good driver, `T > 0` and `R ∈ ℕ` there are `α > 0`, `C ≥ 0`
such that `a1rfNu W t left d s ρ` is `α`-Frostman with constant `C` for all `t ∈ (0, T]`,
`‖d‖ ≤ 2R`, `s ∈ [e^{-R}, e^R]` and `ρ ∈ [0, 1]` (the smoothing radius, including `ρ = 0`).

Assembly of `isFrostman_smeared` (A1RSFrostNu.lean) with the uniform inputs on the pushed side
circle `μ_t = a1rMu`: its Frostman bound (`isFrostman_a1rMu_unif`), its mass near `ℝ`
(`a1rMu_strip_le_unif`) and a uniform bound on its support (`‖f_t z − z‖ ≤ 24 M + 8 √t`,
`CoreArc.norm_fwdMap_sub_le_uniform`, and the bound of the continuous extension of `ψ` on a
compact set). Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Set Filter Metric Complex
open scoped Topology ENNReal

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm Thm18Asm.G1RC TwoPoint

theorem isFrostman_const_nonneg {μ : Measure ℂ} [IsFiniteMeasure μ] {α C : ℝ}
    (h : IsFrostman μ α C) : 0 ≤ C := by
  have := h 0 1 one_pos
  rw [Real.one_rpow, mul_one] at this
  exact ENNReal.toReal_nonneg.trans this

theorem isFrostman_mono_const {μ : Measure ℂ} {α C C' : ℝ} (h : IsFrostman μ α C)
    (hC : C ≤ C') : IsFrostman μ α C' := fun w r hr =>
  (h w r hr).trans (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hr.le _))

/-- **Uniform Frostman bound for the smeared-loop family.** -/
theorem isFrostman_a1rfNu_unif {W : ℝ → ℝ} (hG : G1zDrvGood W) (left : Bool) {T : ℝ}
    (hT : 0 < T) (R : ℕ) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ C ∧ ∀ t ∈ Ioc (0 : ℝ) T, ∀ d : ℂ, ‖d‖ ≤ 2 * R → ∀ s : ℝ,
      Real.exp (-R) ≤ s → s ≤ Real.exp R → ∀ ρ ∈ Icc (0 : ℝ) 1,
        IsFrostman (a1rfNu W t left d s ρ) α C := by
  set αμ : ℝ := min (1 / 2) koebeFrostExp / 2 with hαμ
  have hαμ0 : 0 < αμ := half_pos (lt_min (by norm_num) koebeFrostExp_pos)
  obtain ⟨Cμ, hFμ⟩ := isFrostman_a1rMu_unif hG left hT R
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
  have hR₁0 : 0 ≤ R₁ := by positivity
  have hs₀ : 0 < Real.exp (-(R : ℝ)) := Real.exp_pos _
  obtain ⟨Cm, hCm, hmass⟩ := a1rMu_strip_le_unif hG hT left (R₀ := max (2 * R) (Real.exp R)) hs₀
  -- a dummy parameter point gives `0 ≤ Cμ`
  have hCμ0 : 0 ≤ Cμ := by
    obtain ⟨-, -, g, hgm, hEq⟩ := A1R.sidePush_props hG hT left
    have hmapeq : a1rMu W T left 0 1 = (foldedCircle 0 1).map g := by
      unfold a1rMu
      refine Measure.map_congr ?_
      filter_upwards [TwoPoint.foldedCircle_ae_mem_H (0 : ℂ) one_pos] with u hu
      exact hEq hu
    have : IsFiniteMeasure (a1rMu W T left 0 1) := by rw [hmapeq]; infer_instance
    exact isFrostman_const_nonneg (hFμ T ⟨hT, le_rfl⟩ 0 (by simp) 1
      (by rw [Real.exp_le_one_iff]; simp) (Real.one_le_exp (Nat.cast_nonneg R)))
  set α : ℝ := min (1 / 4) αμ / 2 with hα
  refine ⟨α, (2 * Cm + 2) + 2 * Cμ * (2 * Real.sqrt ((R₁ + 1) ^ 2 + 4 * T)) ^ αμ + 1,
    half_pos (lt_min (by norm_num) hαμ0),
    by rw [hα]; linarith [min_le_left (1 / 4 : ℝ) αμ], by positivity, ?_⟩
  intro t ht d hd s hs1 hs2 ρ hρ
  have hs : 0 < s := hs₀.trans_le hs1
  obtain ⟨-, -, g, hgm, hEq⟩ := A1R.sidePush_props hG ht.1 left
  have hmapeq : a1rMu W t left d s = (foldedCircle d s).map g := by
    unfold a1rMu
    refine Measure.map_congr ?_
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hs] with u hu
    exact hEq hu
  have : IsProbabilityMeasure (a1rMu W t left d s) := by
    rw [hmapeq]; exact (Measure.isProbabilityMeasure_map_iff hgm.aemeasurable).2 inferInstance
  -- support of the pushed side circle
  have hsupp : ∀ᵐ z ∂a1rMu W t left d s, 0 ≤ z.im ∧ ‖z‖ ≤ R₁ := by
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
  have hF := isFrostman_smeared hG.1 hG.2.1 ht.1.le (μ := a1rMu W t left d s) hαμ0 hCμ0
    (by linarith) hR₁0 (hFμ t ht d hd s hs1 hs2) (hsupp.mono fun z hz => hz.1)
    (hsupp.mono fun z hz => hz.2)
    (fun δ hδ => hmass t ht d (hd.trans (le_max_left _ _)) s hs1
      (hs2.trans (le_max_right _ _)) δ hδ) hρ.1 hρ.2
  refine isFrostman_mono_const hF ?_
  have hsq : Real.sqrt ((R₁ + 1) ^ 2 + 4 * t) ≤ Real.sqrt ((R₁ + 1) ^ 2 + 4 * T) :=
    Real.sqrt_le_sqrt (by linarith [ht.2])
  have hpow : (2 * Real.sqrt ((R₁ + 1) ^ 2 + 4 * t)) ^ αμ ≤
      (2 * Real.sqrt ((R₁ + 1) ^ 2 + 4 * T)) ^ αμ :=
    Real.rpow_le_rpow (by positivity) (by linarith) hαμ0.le
  have := mul_le_mul_of_nonneg_left hpow (by positivity : (0 : ℝ) ≤ 2 * Cμ)
  linarith

end A1RS
end R18
end QuantumZipper
