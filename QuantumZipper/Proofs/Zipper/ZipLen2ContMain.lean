import QuantumZipper.Proofs.Zipper.ZipLenMain
import QuantumZipper.Proofs.Zipper.ZipLen2ContIdent
import QuantumZipper.Proofs.Zipper.ZipLen2ContDet
import QuantumZipper.Proofs.Zipper.ZipLen2ContFix
import QuantumZipper.Proofs.Zipper.ZipLen2ContTr
import QuantumZipper.Proofs.Zipper.ZipLen2ContPath

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZIPLEN-2 continuum: the `Γ⁰` flow continuum node `YFlowContStmt`

Main result `yFlowContStmt_holds : YFlowContStmt`.

* Fixed driver (`flowFixedUCc_of`): `Φ^c(p, ρ) = X(μ_{p,ρ}) + det^c(p, ρ)` a.s. at fixed
  `(p, ρ)` (`flowIdentC_holds`, Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1); the
  six-parameter continuous modification of `X(μ_{p,ρ})` on `flowBox m × [0,1]`
  (`F1.exists_contMod_flow`, Revuz–Yor, 3rd ed., Ch. I, Thm (2.1)) and the uniform convergence
  of `det^c` (`flowDetC_tendstoUniformlyOn`) give the Cauchy property as `ρ → 0⁺` along rational
  radii, uniformly at the rational box points.
* Brownian driver (`flowBrownUCc_of_fixed`): conditioning on the path.
* Pathwise (`ae_flowPhiYc_joint`): `Φ^c` is jointly continuous on `flowPar × (0, ∞)`, so the
  Cauchy property extends to every box point and every real radius; completeness of `ℝ` gives
  the limit.
* The pushed circle of the target is `ν_p`, `p = (u, t, foldH c, r)`
  (`RegUnif.eqOn_fwdMapInv_shift`, `CoordReg.foldedCircle_foldH`).

Own bookkeeping on top of the cited results.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace QuantumZipper
namespace B3d
namespace ZipLen

open F1

/-- A bound at rational radii in `(0, δ]` extends to real radii in `(0, δ)` by continuity. -/
theorem le_of_rat_radii {f : ℝ → ℝ} (hf : ContinuousOn f (Ioi 0)) {δ c : ℝ}
    (h : ∀ r : ℚ, 0 < r → (r : ℝ) ≤ δ → f r ≤ c) {x : ℝ} (hx0 : 0 < x) (hxδ : x < δ) :
    f x ≤ c := by
  set s : Set ℝ := (fun r : ℚ => (r : ℝ)) '' {r : ℚ | 0 < r ∧ (r : ℝ) ≤ δ} with hs
  have hsub : s ⊆ Ioi 0 := by
    rintro _ ⟨r, hr, rfl⟩
    exact (show (0 : ℝ) < r by exact_mod_cast hr.1)
  have hcl : x ∈ closure s := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show max (x - ε) 0 < x from
      max_lt (by linarith) hx0)
    have h0 : (0 : ℝ) < r := lt_of_le_of_lt (le_max_right _ _) hr1
    refine ⟨r, ⟨r, ⟨by exact_mod_cast h0, by linarith⟩, rfl⟩, ?_⟩
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [le_max_left (x - ε) 0]
  refine ContinuousWithinAt.closure_le hcl ((hf x hx0).mono hsub) continuousWithinAt_const ?_
  rintro _ ⟨r, hr, rfl⟩
  exact h r hr.1 hr.2

/-- **The `Γ⁰` flow continuum node.** -/
theorem yFlowContStmt_holds : YFlowContStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind
  have hfix := flowFixedUCc_of @flowIdentC_holds @flowDetC_tendstoUniformlyOn
  have hUC := flowBrownUCc_of_fixed hfix hκ hκ4 hB hX hind
  filter_upwards [ae_all_iff.2 hUC, ae_flowPhiYc_joint hκ hB hX hind, hB.cont,
    hB.eval_zero_ae_eq_zero] with ω hUCω hcont hc h0
  set W := drive κ B ω with hWdef
  have hW : Continuous W := by
    rw [hWdef]; unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  intro u t hu ht c r hr
  set p : ℝ × ℝ × ℂ × ℝ := (u, t, foldH c, r) with hpdef
  -- the pushed circle is `ν_p`
  have hν : (foldedCircle c r).map (fwdMapInv (F1.shiftDrv W u) t) = flowNu W p := by
    unfold flowNu
    simp only [hpdef]
    rw [CoordReg.foldedCircle_foldH c r]
    refine Measure.map_congr ((TwoPoint.foldedCircle_ae_mem_H c hr).mono fun z hz => ?_)
    exact RegUnif.eqOn_fwdMapInv_shift hW hu ht hz
  rw [hν]
  simp_rw [← unzippedField_cfg_eq κ u (X ω) W]
  show ∃ L, Tendsto (fun ρ => flowPhiYc κ (X ω) W ρ p) (𝓝[>] 0) (𝓝 L)
  have hpH : foldH c ∈ Hbar := by
    unfold foldH; split_ifs with h
    · exact h
    · show (0 : ℝ) ≤ ((starRingEnd ℂ) c).im
      rw [Complex.conj_im]; linarith [not_le.1 h]
  have hpP : p ∈ flowPar := ⟨hu, ht, hpH, hr⟩
  -- a box containing `p`
  obtain ⟨m, hm⟩ := exists_nat_gt (max (max u t) (max (max |(foldH c).re| (foldH c).im)
    (max r (1 / r))))
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hpbox : p ∈ flowBox m := by
    have e1 := le_max_left (max u t) (max (max |(foldH c).re| (foldH c).im) (max r (1 / r)))
    have e2 := le_max_right (max u t) (max (max |(foldH c).re| (foldH c).im) (max r (1 / r)))
    have hu' : u ≤ m := by linarith [le_max_left u t]
    have ht' : t ≤ m := by linarith [le_max_right u t]
    have hre : |(foldH c).re| ≤ m := by
      linarith [le_max_left |(foldH c).re| (foldH c).im,
        le_max_left (max |(foldH c).re| (foldH c).im) (max r (1 / r))]
    have him : (foldH c).im ≤ m := by
      linarith [le_max_right |(foldH c).re| (foldH c).im,
        le_max_left (max |(foldH c).re| (foldH c).im) (max r (1 / r))]
    have hr' : r ≤ m := by
      linarith [le_max_left r (1 / r),
        le_max_right (max |(foldH c).re| (foldH c).im) (max r (1 / r))]
    have hr'' : 1 / r ≤ m := by
      linarith [le_max_right r (1 / r),
        le_max_right (max |(foldH c).re| (foldH c).im) (max r (1 / r))]
    have hrlow : 1 / ((m : ℝ) + 2) ≤ r := by
      rw [div_le_iff₀ (by positivity)]
      have : 1 ≤ r * m := by
        rw [div_le_iff₀ hr] at hr''; linarith
      nlinarith
    refine ⟨⟨hu, by linarith⟩, ⟨ht, by linarith⟩, ⟨?_, ?_⟩, ⟨hpH, by linarith⟩,
      ⟨hrlow, by linarith⟩⟩
    · linarith [neg_abs_le (foldH c).re]
    · linarith [le_abs_self (foldH c).re]
  -- continuity facts
  have hcρ : ∀ p' ∈ flowPar, ContinuousOn (fun ρ => flowPhiYc κ (X ω) W ρ p') (Ioi 0) :=
    fun p' hp' => hcont.comp (f := fun ρ : ℝ => (p', ρ)) (by fun_prop) fun ρ hρ => ⟨hp', hρ⟩
  have hcp : ∀ ρ : ℝ, 0 < ρ → ContinuousOn (fun p' => flowPhiYc κ (X ω) W ρ p') flowPar :=
    fun ρ hρ => hcont.comp (f := fun p' => (p', ρ)) (by fun_prop) fun p' hp' => ⟨hp', hρ⟩
  -- the Cauchy estimate at `p`
  have hcauchy : ∀ n : ℕ, ∃ δ > 0, ∀ ρ ρ' : ℝ, 0 < ρ → ρ < δ → 0 < ρ' → ρ' < δ →
      |flowPhiYc κ (X ω) W ρ p - flowPhiYc κ (X ω) W ρ' p| ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨N, hN⟩ := hUCω m n
    refine ⟨1 / ((N : ℝ) + 1), by positivity, fun ρ ρ' hρ hρδ hρ' hρ'δ => ?_⟩
    -- rational radii, all box points
    have hA : ∀ r1 r1' : ℚ, 0 < r1 → (r1 : ℝ) ≤ 1 / ((N : ℝ) + 1) → 0 < r1' →
        (r1' : ℝ) ≤ 1 / ((N : ℝ) + 1) →
        |flowPhiYc κ (X ω) W r1 p - flowPhiYc κ (X ω) W r1' p| ≤ 1 / ((n : ℝ) + 1) := by
      intro r1 r1' h1 h2 h3 h4
      have h1' : (0 : ℝ) < r1 := by exact_mod_cast h1
      have h3' : (0 : ℝ) < r1' := by exact_mod_cast h3
      set s : Set (ℝ × ℝ × ℂ × ℝ) := {p' | ∃ q, flowQ q = p' ∧ p' ∈ flowBox m} with hs
      have hsub : s ⊆ flowPar := fun p' ⟨_, _, hp'⟩ => flowBox_subset_flowPar m hp'
      have hF : ContinuousWithinAt (fun p' => |flowPhiYc κ (X ω) W r1 p' -
          flowPhiYc κ (X ω) W r1' p'|) flowPar p :=
        (((hcp _ h1') p hpP).sub ((hcp _ h3') p hpP)).abs
      refine ContinuousWithinAt.closure_le (flowBox_subset_closure m hpbox) (hF.mono hsub)
        continuousWithinAt_const ?_
      rintro _ ⟨q, rfl, hq⟩
      exact hN r1 r1' h1 h2 h3 h4 q hq
    have hB' : ∀ r1' : ℚ, 0 < r1' → (r1' : ℝ) ≤ 1 / ((N : ℝ) + 1) →
        |flowPhiYc κ (X ω) W ρ p - flowPhiYc κ (X ω) W r1' p| ≤ 1 / ((n : ℝ) + 1) := by
      intro r1' h3 h4
      exact le_of_rat_radii (f := fun x => |flowPhiYc κ (X ω) W x p -
          flowPhiYc κ (X ω) W r1' p|) ((hcρ p hpP).sub continuousOn_const).abs
        (fun r1 h1 h2 => hA r1 r1' h1 h2 h3 h4) hρ hρδ
    exact le_of_rat_radii (f := fun x => |flowPhiYc κ (X ω) W ρ p - flowPhiYc κ (X ω) W x p|)
      (continuousOn_const.sub (hcρ p hpP)).abs hB' hρ' hρ'δ
  -- completeness
  refine cauchy_map_iff_exists_tendsto.1 (Metric.cauchy_iff.2 ⟨inferInstance, fun ε hε => ?_⟩)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  obtain ⟨δ, hδ, hδc⟩ := hcauchy n
  refine ⟨(fun ρ => flowPhiYc κ (X ω) W ρ p) '' Ioo 0 δ,
    image_mem_map (Ioo_mem_nhdsGT hδ), ?_⟩
  rintro _ ⟨ρ, hρ, rfl⟩ _ ⟨ρ', hρ', rfl⟩
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (hδc ρ ρ' hρ.1 hρ.2 hρ'.1 hρ'.2) hn

end ZipLen
end B3d
end QuantumZipper
