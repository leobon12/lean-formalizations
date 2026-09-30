import QuantumZipper.Proofs.LQG.FiniteArea

/-!
# M4-P3(b), area version, part 1: the interior inner-field decomposition

Blueprint `M4_BLUEPRINT.md`, node M4-P3(b) (area analogue at an interior point `z ∈ ℍ`).

Fix `z ∈ ℍ`, radii `0 < δ ≤ D ≤ Im z` and `R` with `‖z‖ + D ≤ R`. For the normalized field
`Z = aZ X R` and circles `B̄(w, r) ⊆ B̄(z, δ)` we split
`Z_r(w) = Ω + Y_r(w)` with the circle-average increment `Ω = Z_δ(z) − Z_D(z)` and the inner field
`Y_r(w) = (X_r(w) − X_δ(z)) + (X_D(z) − X_R(0))`. All covariances between `Ω` and the pair
differences building `Y` vanish (the reflected term `−log‖w − z̄‖` is the same for the two
concentric circles `fc(z, δ)`, `fc(z, D)`), so `Ω` is independent of the whole inner field
(`indepFun_omZ_innerS`), and pathwise

  `μ_{2^{-k}}(S) = e^{γΩ} δ^{γ²/2} W_k(S)`,   `W_k = FinArea.massFunC γ S δ k (inner field)`

(`ae_areaApprox_eq_omZ_mul`). This is the interior analogue of `FinArea.innerSampleC` (real
centre) and of the Brownian-motion structure of circle averages, Duplantier–Sheffield, *Liouville
quantum gravity and KPZ*, Invent. Math. 185 (2011), Prop. 3.3, p. 18 (the circle average process
`h_{e^{-t}}(z)` is a Brownian motion in `t`, so its increments over disjoint log-radius intervals
are independent; AUDIT10 G10-2 corrects the earlier "§3.1"). The choice `Ω = Z_δ(z) − Z_D(z)` (instead of `Z_δ(z)`) is an own
adaptation making the independence exact for the Neumann field on `ℍ`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace AreaP3b

open GaussTK KernelId

/-- Circles inside `B̄(z, δ)`: `(w, r)` with `r > 0` and `‖w − z‖ + r ≤ δ`. -/
abbrev InnerZ (z : ℂ) (δ : ℝ) := {q : ℂ × ℝ // 0 < q.2 ∧ ‖q.1 - z‖ + q.2 ≤ δ}

/-- Pair indices of the inner process: `none ↦ (z, D; 0, R)`, `some q ↦ (w, r; z, δ)`. -/
def innerIdx (z : ℂ) (δ D R : ℝ) : Option (InnerZ z δ) → FcIdx
  | none => (z, D, 0, R)
  | some q => (q.1.1, q.1.2, z, δ)

section Geometry

variable {z : ℂ} {δ D R : ℝ}

theorem im_ge_of_inner {w : ℂ} {r : ℝ} (h : ‖w - z‖ + r ≤ δ) (hδz : δ ≤ z.im) : r ≤ w.im := by
  have h1 : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
  rw [Complex.sub_im] at h1
  have := neg_abs_le (w.im - z.im)
  linarith

theorem good_innerIdx (hδ : 0 < δ) (hδD : δ ≤ D) (hDz : D ≤ z.im) (hDR : ‖z‖ + D ≤ R) :
    ∀ o : Option (InnerZ z δ), (innerIdx z δ D R o).Good := by
  have hz : z ∈ Hbar := show 0 ≤ z.im by linarith
  have hR : 0 < R := by linarith [norm_nonneg z]
  rintro (_ | q)
  · exact ⟨hz, show (0:ℝ) < D by linarith, zero_mem_Hbar, hR⟩
  · have hr := q.2.1
    have hw := im_ge_of_inner q.2.2 (hδD.trans hDz)
    exact ⟨show 0 ≤ q.1.1.im by linarith, hr, hz, hδ⟩

theorem good_omZ (hδ : 0 < δ) (hδD : δ ≤ D) (hDz : D ≤ z.im) :
    FcIdx.Good (z, δ, z, D) := by
  have hz : z ∈ Hbar := show 0 ≤ z.im by linarith
  exact ⟨hz, hδ, hz, by linarith⟩

/-- Zero covariance between an inner pair `(w, r; z, δ)` and `Ω = (z, δ; z, D)`. -/
theorem fcPairCov_inner_omZ {w : ℂ} {r : ℝ} (hr : 0 < r) (hwr : ‖w - z‖ + r ≤ δ)
    (hδD : δ ≤ D) (hDz : D ≤ z.im) :
    fcPairCov (w, r, z, δ) (z, δ, z, D) = 0 := by
  have hδ : 0 < δ := by linarith [norm_nonneg (w - z)]
  have hrw : r ≤ w.im := im_ge_of_inner hwr (hδD.trans hDz)
  simp only [fcPairCov, kernelCov2]
  rw [kernelCov_fc_interior_nested' hr hrw (hδD.trans hDz) hwr,
    kernelCov_fc_interior_nested' hr hrw hDz (by linarith),
    kernelCov_fc_interior_sameCenter hδ hδ (hδD.trans hDz) (hδD.trans hDz),
    kernelCov_fc_interior_sameCenter hδ (by linarith) (hδD.trans hDz) hDz, max_self,
    max_eq_right hδD]
  ring

/-- Zero covariance between `(z, D; 0, R)` and `Ω = (z, δ; z, D)`. -/
theorem fcPairCov_C_omZ (hδ : 0 < δ) (hδD : δ ≤ D) (hDz : D ≤ z.im) (hDR : ‖z‖ + D ≤ R) :
    fcPairCov (z, D, 0, R) (z, δ, z, D) = 0 := by
  have hD : 0 < D := by linarith
  simp only [fcPairCov, kernelCov2]
  rw [kernelCov_fc_interior_sameCenter hD hδ hDz (hδD.trans hDz),
    kernelCov_fc_interior_sameCenter hD hD hDz hDz, max_self, max_eq_left hδD,
    kernelCov_fc_bigCircle_left hδ (by linarith), kernelCov_fc_bigCircle_left hD hDR]
  ring

theorem fcPairCov_innerIdx_omZ (hδ : 0 < δ) (hδD : δ ≤ D) (hDz : D ≤ z.im) (hDR : ‖z‖ + D ≤ R) :
    ∀ o : Option (InnerZ z δ), fcPairCov (innerIdx z δ D R o) (z, δ, z, D) = 0 := by
  rintro (_ | q)
  · exact fcPairCov_C_omZ hδ hδD hDz hDR
  · exact fcPairCov_inner_omZ q.2.1 q.2.2 hδD hDz

end Geometry

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- The inner process. -/
def innerProc (X : Ω → FieldSample) (z : ℂ) (δ D R : ℝ) (ω : Ω) : Option (InnerZ z δ) → ℝ :=
  fun o => fcPairVal X (innerIdx z δ D R o) ω

open Classical in
/-- Rebuild a field sample from inner coordinates: `fc(w, r) ↦ y(some q) + y(none)`. -/
def innerRebuild (z : ℂ) (δ : ℝ) (y : Option (InnerZ z δ) → ℝ) : FieldSample := fun μ =>
  if h : ∃ q : InnerZ z δ, foldedCircle q.1.1 q.1.2 = μ then y (some h.choose) + y none else 0

/-- The inner field sample, a function of the inner process only. -/
def innerS (X : Ω → FieldSample) (z : ℂ) (δ D R : ℝ) (ω : Ω) : FieldSample :=
  innerRebuild z δ (innerProc X z δ D R ω)

/-- The circle-average increment `Ω = X_δ(z) − X_D(z) = Z_δ(z) − Z_D(z)`. -/
def omZ (X : Ω → FieldSample) (z : ℂ) (δ D : ℝ) (ω : Ω) : ℝ := fcPairVal X (z, δ, z, D) ω

theorem measurable_innerRebuild (z : ℂ) (δ : ℝ) : Measurable (innerRebuild z δ) := by
  refine measurable_pi_iff.mpr fun μ => ?_
  by_cases h : ∃ q : InnerZ z δ, foldedCircle q.1.1 q.1.2 = μ
  · have e : (fun y : Option (InnerZ z δ) → ℝ => innerRebuild z δ y μ) =
        fun y => y (some h.choose) + y none := by
      funext y; simp only [innerRebuild, dif_pos h]
    rw [e]; exact (measurable_pi_apply _).add (measurable_pi_apply _)
  · have e : (fun y : Option (InnerZ z δ) → ℝ => innerRebuild z δ y μ) = fun _ => 0 := by
      funext y; simp only [innerRebuild, dif_neg h]
    rw [e]; exact measurable_const

theorem measurable_innerProc (hX : IsFreeGFFModConstH X P) (z : ℂ) (δ D R : ℝ) :
    Measurable (innerProc X z δ D R) :=
  measurable_pi_iff.mpr fun _ => measurable_fcPairVal hX _

theorem measurable_innerS (hX : IsFreeGFFModConstH X P) (z : ℂ) (δ D R : ℝ) :
    Measurable (innerS X z δ D R) :=
  (measurable_innerRebuild z δ).comp (measurable_innerProc hX z δ D R)

theorem measurable_omZ (hX : IsFreeGFFModConstH X P) (z : ℂ) (δ D : ℝ) :
    Measurable (omZ X z δ D) := measurable_fcPairVal hX _

omit [MeasurableSpace Ω] in
theorem innerS_apply (z : ℂ) (δ D R : ℝ) (ω : Ω) (q : InnerZ z δ) :
    innerS X z δ D R ω (foldedCircle q.1.1 q.1.2) =
      X ω (foldedCircle q.1.1 q.1.2) - X ω (foldedCircle 0 R) - omZ X z δ D ω := by
  have h : ∃ q' : InnerZ z δ, foldedCircle q'.1.1 q'.1.2 = foldedCircle q.1.1 q.1.2 := ⟨q, rfl⟩
  have e : innerS X z δ D R ω (foldedCircle q.1.1 q.1.2) =
      fcPairVal X (innerIdx z δ D R (some h.choose)) ω +
        fcPairVal X (innerIdx z δ D R none) ω := by
    simp only [innerS, innerRebuild, dif_pos h, innerProc]
  rw [e]
  simp only [innerIdx, fcPairVal, omZ]
  rw [h.choose_spec]
  ring

/-- **Independence** of `Ω` and the inner field. -/
theorem indepFun_omZ_innerS (hX : IsFreeGFFModConstH X P) {z : ℂ} {δ D R : ℝ} (hδ : 0 < δ)
    (hδD : δ ≤ D) (hDz : D ≤ z.im) (hDR : ‖z‖ + D ≤ R) :
    IndepFun (omZ X z δ D) (innerS X z δ D R) P := by
  have hI := indepFun_fcPair hX (P := P)
    (fun o : Option (InnerZ z δ) => (⟨innerIdx z δ D R o, good_innerIdx hδ hδD hDz hDR o⟩ :
      {p : FcIdx // p.Good}))
    (fun _ : Unit => (⟨(z, δ, z, D), good_omZ hδ hδD hDz⟩ : {p : FcIdx // p.Good}))
    (fun o _ => fcPairCov_innerIdx_omZ hδ hδD hDz hDR o)
  exact hI.symm.comp (measurable_pi_apply ()) (measurable_innerRebuild z δ)

omit [MeasurableSpace Ω] in
/-- Pathwise identification of the inner field's regularized averages. -/
theorem avgReg_innerS_eq {z : ℂ} {δ D R : ℝ} {w : ℂ} {k : ℕ} (hs : ‖w - z‖ + radius k < δ)
    {ω : Ω} (hlim : Tendsto (fun j => X ω (foldedCircle (dyadicRoundC j w) (radius k))) atTop
      (𝓝 (avgReg (X ω) k w))) :
    avgReg (innerS X z δ D R ω) k w =
      avgReg (X ω) k w - X ω (foldedCircle 0 R) - omZ X z δ D ω := by
  have hr := radius_pos k
  have hε : 0 < (δ - ‖w - z‖ - radius k) / 2 := by linarith
  have hev : ∀ᶠ j : ℕ in atTop, (1 / 2 : ℝ) ^ j < (δ - ‖w - z‖ - radius k) / 2 :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1)).eventually
      (gt_mem_nhds hε)
  have heq : ∀ᶠ j : ℕ in atTop,
      X ω (foldedCircle (dyadicRoundC j w) (radius k)) - X ω (foldedCircle 0 R) - omZ X z δ D ω =
        innerS X z δ D R ω (foldedCircle (dyadicRoundC j w) (radius k)) := by
    filter_upwards [hev] with j hj
    set d := dyadicRoundC j w with hd
    have hdw : ‖d - w‖ ≤ 2 * (1 / 2 ^ j) := CircleCont.norm_dyadicRoundC_sub_le j w
    rw [one_div_pow] at hj
    have hdz : ‖d - z‖ ≤ ‖d - w‖ + ‖w - z‖ := by
      calc ‖d - z‖ = ‖(d - w) + (w - z)‖ := by rw [sub_add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    let q : InnerZ z δ := ⟨(d, radius k), hr, by dsimp only; linarith⟩
    exact (innerS_apply z δ D R ω q).symm
  exact (((hlim.sub_const _).sub_const _).congr' heq).limUnder_eq

/-- Almost surely, on `Hbar ∩ B(z, δ − 2^{-k})`, `Z_{2^{-k}} = Ω + Y_{2^{-k}}`. -/
theorem ae_avgReg_aZ_eq_inner (hX : IsFreeGFFModConstH X P) (z : ℂ) (δ D R : ℝ) (k : ℕ) :
    ∀ᵐ ω ∂P, ∀ w ∈ Hbar, ‖w - z‖ + radius k < δ →
      avgReg (AreaExist.aZ X R ω) k w = omZ X z δ D ω + avgReg (innerS X z δ D R ω) k w := by
  filter_upwards [(AreaExist.ae_avgReg_spec hX k).1, AreaExist.ae_avgReg_aZ hX R k]
    with ω h1 h2 w hw hs
  rw [h2 w hw, avgReg_innerS_eq hs (h1 w hw)]
  ring

/-- **Decomposition** `μ_{2^{-k}}(S) = e^{γΩ} δ^{γ²/2} W_k(S)`, a.s. simultaneously for all `k`
with `‖w − z‖ + 2^{-k} < δ` on `S`. -/
theorem ae_areaApprox_eq_omZ_mul (hX : IsFreeGFFModConstH X P) (γ : ℝ) {z : ℂ} {δ D R : ℝ}
    (hδ : 0 < δ) {S : Set ℂ} (hS : MeasurableSet S) (hSH : S ⊆ H) :
    ∀ᵐ ω ∂P, ∀ k : ℕ, (∀ w ∈ S, ‖w - z‖ + radius k < δ) →
      areaApprox γ (AreaExist.aZ X R ω) k S =
        ENNReal.ofReal (exp (γ * omZ X z δ D ω) * δ ^ (γ ^ 2 / 2)) *
          FinArea.massFunC γ S δ k (innerS X z δ D R ω) := by
  have h := fun k => ae_avgReg_aZ_eq_inner hX (P := P) z δ D R k
  rw [← ae_all_iff] at h
  filter_upwards [h] with ω hω k hk
  exact FinArea.areaApprox_eq_of γ hδ k _ _ _ hS hSH fun w hw =>
    hω k w (show (0 : ℝ) ≤ w.im from le_of_lt (hSH hw)) (hk w hw)

end AreaP3b
end QuantumZipper
