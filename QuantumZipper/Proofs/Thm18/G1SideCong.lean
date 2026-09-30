import QuantumZipper.Proofs.Zipper.SWCoreN2IdPush
import QuantumZipper.Proofs.LQG.WedgeCanonical2
import QuantumZipper.Proofs.GFF.CircleContinuity
import QuantumZipper.Proofs.LQG.CoordChangeAvg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE (1): the wedge field and a free field plus a continuous function, uniformly over a
family of maps

For a family `q ↦ Ψ q` of maps of one boundary class `BdryClass a b ρ M m` whose images of the
`ρ`-thickening of `[a,b]` stay at distance `≥ c₀ > 0` from `0` and map `Hbar` into `Hbar`, two
fields whose dyadic averages agree at all points `w ∈ Hbar` with `‖w‖ ≥ c₀` (for small dyadic
radii) have the same pulled-back boundary approximations on `[a,b]`, for every `k` with
`3 · 2^{-k} < ρ`, simultaneously for all maps of the family
(`bdryApprox_coordChange_family_restrict_eq`). This is the family (uniform) form of
`Thm18Asm.G1Z3.bdryApprox_coordChange_eq_of_avgReg_away` (G1Z3Wedge.lean).

Applications: the wedge field `wedgeField (lateralPart x) A Q` and `x + ofFun g`, where `g` is the
wedge profile cut off near `0` (`profCut`), a continuous function on `ℂ`
(`bdryApprox_wedgeField_family_restrict_eq`). Together with the free-field add-on transport this
gives the coordinate-change rule for the wedge field uniformly over finite-parameter families
(Duplantier–Sheffield, *LQG and KPZ*, Invent. Math. 185 (2011), rule (5.1) and Prop. 2.1;
Sheffield–Wang arXiv:1605.06171 Thm 4.3). Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace G1Side

open SWCore

theorem limUnder_congr_side {f g : ℕ → ℝ} (h : f =ᶠ[atTop] g) :
    limUnder atTop f = limUnder atTop g := by
  unfold limUnder
  rw [Filter.map_congr h]

/-- A property holding at all points `ψ(fold(circle))` holds a.e. for the pushed folded circle. -/
theorem ae_map_fc_of_forall {ψ : ℂ → ℂ} {s R : ℝ} (hR : 0 ≤ R)
    (hψ : ContinuousOn ψ (closedBall (s : ℂ) R)) {S : Set ℂ} (hS : MeasurableSet S)
    (h : ∀ θ : ℝ, ψ (foldH (circleMap (s : ℂ) R θ)) ∈ S) :
    ∀ᵐ w ∂((foldedCircle (s : ℂ) R).map ψ), w ∈ S := by
  rw [swcN2_fc_map_eq hR hψ]
  have hc : Continuous fun θ : ℝ => ψ (foldH (circleMap (s : ℂ) R θ)) :=
    hψ.comp_continuous (CircleFubini.continuous_foldH'.comp (continuous_circleMap _ _))
      fun θ => swcN2_fold_circle_mem hR θ
  exact (ae_map_iff hc.measurable.aemeasurable hS).2 (Eventually.of_forall h)

variable {ι : Type*} {Ψ : ι → ℂ → ℂ} {K : Set ι} {a b ρ M m c₀ ε₀ Q : ℝ}

/-- **Family congruence of the pulled-back regularized averages.** -/
theorem avgReg_coordChange_family_eq {y y' : FieldSample}
    (hyy : ∀ j w, w ∈ Hbar → c₀ ≤ ‖w‖ → radius j < ε₀ → avgReg y j w = avgReg y' j w)
    (hε₀ : 0 < ε₀) (hab : a ≤ b) (hcl : ∀ q ∈ K, Ψ q ∈ BdryClass a b ρ M m)
    (hsep : ∀ q ∈ K, ∀ z ∈ thickening ρ (segC a b), c₀ ≤ ‖Ψ q z‖)
    (hHb : ∀ q ∈ K, ∀ z ∈ thickening ρ (segC a b), z ∈ Hbar → Ψ q z ∈ Hbar)
    {k : ℕ} (hk : 3 * radius k < ρ) {q : ι} (hq : q ∈ K) {t : ℝ} (ht : t ∈ Icc a b) :
    avgReg (coordChange y (Ψ q) Q) k (t : ℂ) = avgReg (coordChange y' (Ψ q) Q) k (t : ℂ) := by
  have hr := radius_pos k
  -- the pushed folded circles centred in `[a - r, b + r]`
  have hpush : ∀ s ∈ Icc (a - radius k) (b + radius k),
      evalReg y ((foldedCircle (s : ℂ) (radius k)).map (Ψ q)) =
        evalReg y' ((foldedCircle (s : ℂ) (radius k)).map (Ψ q)) := by
    intro s hs
    have hball : closedBall (s : ℂ) (radius k) ⊆ thickening ρ (segC a b) := by
      intro z hz
      refine swcN2_ball_sub_thick (swcN2Clamp_mem hab s) (R := 2 * radius k) (by linarith) ?_
      have h3 : dist (s : ℂ) ((swcN2Clamp a b s : ℝ) : ℂ) = |s - swcN2Clamp a b s| := by
        rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have := swcN2Clamp_near hab hr.le hs
      rw [mem_closedBall] at hz ⊢
      linarith [dist_triangle z (s : ℂ) ((swcN2Clamp a b s : ℝ) : ℂ)]
    have hψc : ContinuousOn (Ψ q) (closedBall (s : ℂ) (radius k)) :=
      (hcl q hq).1.continuousOn.mono hball
    have hmeas : MeasurableSet {w : ℂ | w ∈ Hbar ∧ c₀ ≤ ‖w‖} :=
      (isClosed_le continuous_const Complex.continuous_im).measurableSet.inter
        (isClosed_le continuous_const continuous_norm).measurableSet
    have hae := ae_map_fc_of_forall hr.le hψc hmeas fun θ => by
      have hz := swcN2_fold_circle_mem (s := s) hr.le θ
      have hzt := hball hz
      have hzH : foldH (circleMap (s : ℂ) (radius k) θ) ∈ Hbar := by
        show 0 ≤ (foldH _).im
        unfold foldH
        split_ifs with h
        · exact h
        · simp only [Complex.conj_im]; linarith
      exact ⟨hHb q hq _ hzt hzH, hsep q hq _ hzt⟩
    unfold evalReg
    refine limUnder_congr_side ?_
    have hj : ∀ᶠ j in atTop, radius j < ε₀ :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
        (by norm_num)).eventually (gt_mem_nhds hε₀) |>.mono fun j hj => by
          simpa [radius, one_div, inv_pow] using hj
    filter_upwards [hj] with j hj
    refine integral_congr_ae ?_
    filter_upwards [hae] with w hw
    exact hyy j w hw.1 hw.2 hj
  unfold avgReg
  refine limUnder_congr_side ?_
  have hn : ∀ᶠ n : ℕ in atTop, dyadicRound n t ∈ Icc (a - radius k) (b + radius k) := by
    filter_upwards [eventually_ge_atTop k] with n hn
    have h1 := CircleCont.abs_dyadicRound_sub_le n t
    have h2 : (1 : ℝ) / 2 ^ n ≤ radius k := by
      unfold radius
      rw [one_div, ← inv_pow]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    rw [abs_le] at h1
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  filter_upwards [hn] with n hn
  have e : dyadicRoundC n (t : ℂ) = ((dyadicRound n t : ℝ) : ℂ) := CoordChange.dyadicRoundC_ofReal n t
  simp only [coordChange, e]
  rw [hpush _ hn]

/-- **Family congruence of the pulled-back boundary approximations on `[a,b]`.** -/
theorem bdryApprox_coordChange_family_restrict_eq (γ : ℝ) {y y' : FieldSample}
    (hyy : ∀ j w, w ∈ Hbar → c₀ ≤ ‖w‖ → radius j < ε₀ → avgReg y j w = avgReg y' j w)
    (hε₀ : 0 < ε₀) (hab : a ≤ b) (hcl : ∀ q ∈ K, Ψ q ∈ BdryClass a b ρ M m)
    (hsep : ∀ q ∈ K, ∀ z ∈ thickening ρ (segC a b), c₀ ≤ ‖Ψ q z‖)
    (hHb : ∀ q ∈ K, ∀ z ∈ thickening ρ (segC a b), z ∈ Hbar → Ψ q z ∈ Hbar)
    {k : ℕ} (hk : 3 * radius k < ρ) {q : ι} (hq : q ∈ K) :
    (bdryApprox γ (coordChange y (Ψ q) Q) k).restrict (Icc a b) =
      (bdryApprox γ (coordChange y' (Ψ q) Q) k).restrict (Icc a b) := by
  unfold bdryApprox
  rw [restrict_withDensity measurableSet_Icc, restrict_withDensity measurableSet_Icc]
  refine withDensity_congr_ae ((ae_restrict_iff' measurableSet_Icc).2
    (Eventually.of_forall fun t ht => ?_))
  simp only
  rw [avgReg_coordChange_family_eq hyy hε₀ hab hcl hsep hHb hk hq ht]

/-- The wedge profile, cut off (made constant in `‖z‖`) inside the disc of radius `c`. -/
def profCut (x : FieldSample) (A : ℝ → ℝ) (Q c : ℝ) : ℂ → ℝ := fun z =>
  -radAvgReg x (max ‖z‖ c) + Q * -Real.log (max ‖z‖ c) + A (-Real.log (max ‖z‖ c))

theorem profCut_eq {x : FieldSample} {A : ℝ → ℝ} {Q c : ℝ} {z : ℂ} (hz : c ≤ ‖z‖) :
    profCut x A Q c z = WedgeCan.wedgeProfile x A Q z := by
  unfold profCut WedgeCan.wedgeProfile
  rw [max_eq_left hz]

theorem continuous_profCut {x : FieldSample} {F : ℂ × ℝ → ℝ} (hG : WedgeTK.GoodRad x F)
    {A : ℝ → ℝ} (hA : Continuous A) (Q : ℝ) {c : ℝ} (hc : 0 < c) :
    Continuous (profCut x A Q c) := by
  have hm : Continuous fun z : ℂ => max ‖z‖ c := continuous_norm.max continuous_const
  have hpos : ∀ z : ℂ, 0 < max ‖z‖ c := fun z => lt_of_lt_of_le hc (le_max_right _ _)
  have hrad : Continuous fun z : ℂ => radAvgReg x (max ‖z‖ c) := by
    have e : (fun z : ℂ => radAvgReg x (max ‖z‖ c)) = fun z => F (0, max ‖z‖ c) :=
      funext fun z => hG.radAvgReg_eq (hpos z)
    rw [e]
    exact hG.1.1.comp_continuous (continuous_const.prodMk hm)
      fun z => ⟨GaussTK.zero_mem_Hbar, hpos z⟩
  have hlog : Continuous fun z : ℂ => -Real.log (max ‖z‖ c) :=
    (hm.log fun z => (hpos z).ne').neg
  exact (hrad.neg.add (continuous_const.mul hlog)).add (hA.comp hlog)

/-- Dyadic averages of `x + ofFun φ` and `x + ofFun φ'` agree where `φ = φ'` near the circle. -/
theorem avgReg_add_ofFun_congr {x : FieldSample} {φ φ' : ℂ → ℝ} {c : ℝ} (hc : 0 < c)
    (h : ∀ z : ℂ, c / 2 ≤ ‖z‖ → φ z = φ' z) {j : ℕ} {w : ℂ} (hw : c ≤ ‖w‖)
    (hj : radius j < c / 4) : avgReg (x + ofFun φ) j w = avgReg (x + ofFun φ') j w := by
  unfold avgReg
  refine limUnder_congr_side ?_
  have hn : ∀ᶠ n : ℕ in atTop, 2 * (1 / 2 ^ n : ℝ) < c / 4 := by
    have ht : Tendsto (fun n : ℕ => 2 * (1 / 2 ^ n : ℝ)) atTop (𝓝 (2 * 0)) := by
      refine tendsto_const_nhds.mul ?_
      simp_rw [one_div, ← inv_pow]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    rw [mul_zero] at ht
    exact ht.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hn] with n hn
  set y := dyadicRoundC n w with hy
  have hyw : c - c / 4 ≤ ‖y‖ := by
    have := CircleCont.norm_dyadicRoundC_sub_le n w
    have h2 := norm_sub_norm_le w y
    rw [norm_sub_rev] at this
    linarith
  simp only [Pi.add_apply, ofFun]
  congr 1
  refine integral_congr_ae ?_
  rw [swcN2_fc_eq_map]
  have hmeas : MeasurableSet {u : ℂ | c / 2 ≤ ‖u‖} :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  have hae : ∀ᵐ u ∂(Thm18Asm.G1RC.circM.map (fun θ => foldH (circleMap y (radius j) θ))), c / 2 ≤ ‖u‖ := by
    refine (ae_map_iff (swcN2_measurable_fold_circle _ _).aemeasurable hmeas).2
      (Eventually.of_forall fun θ => ?_)
    have hf : ‖foldH (circleMap y (radius j) θ)‖ = ‖circleMap y (radius j) θ‖ := by
      unfold foldH
      split_ifs
      · rfl
      · exact Complex.norm_conj _
    have hcm : ‖circleMap y (radius j) θ - y‖ = radius j := by
      rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos (radius_pos j)]
    have h3 := norm_sub_norm_le y (circleMap y (radius j) θ)
    rw [norm_sub_rev] at h3
    show c / 2 ≤ ‖foldH (circleMap y (radius j) θ)‖
    rw [hf]
    linarith
  filter_upwards [hae] with u hu
  exact h u hu

/-- **The wedge field versus the free field plus the cut-off profile, uniformly over a family**:
for every `k` with `3 · 2^{-k} < ρ`, the pulled-back boundary approximations agree on `[a,b]`. -/
theorem bdryApprox_wedgeField_family_restrict_eq (γ Q₀ : ℝ) {x : FieldSample}
    {F : ℂ × ℝ → ℝ} (hG : WedgeTK.GoodRad x F)
    (hraw : ∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
      x (foldedCircle (dyadicRoundC n z) (radius k)) = F (dyadicRoundC n z, radius k))
    {A : ℝ → ℝ} (hA : Continuous A) (hc₀ : 0 < c₀) (hab : a ≤ b)
    (hcl : ∀ q ∈ K, Ψ q ∈ BdryClass a b ρ M m)
    (hsep : ∀ q ∈ K, ∀ z ∈ thickening ρ (segC a b), c₀ ≤ ‖Ψ q z‖)
    (hHb : ∀ q ∈ K, ∀ z ∈ thickening ρ (segC a b), z ∈ Hbar → Ψ q z ∈ Hbar)
    {k : ℕ} (hk : 3 * radius k < ρ) {q : ι} (hq : q ∈ K) :
    (bdryApprox γ (coordChange (wedgeField (lateralPart x) A Q₀) (Ψ q) Q) k).restrict
        (Icc a b) =
      (bdryApprox γ (coordChange (x + ofFun (profCut x A Q₀ (c₀ / 2))) (Ψ q) Q) k).restrict
        (Icc a b) := by
  refine bdryApprox_coordChange_family_restrict_eq γ (ε₀ := c₀ / 4) (fun j w hw hwc hj => ?_)
    (by positivity) hab hcl hsep hHb hk hq
  have hne : ‖w‖ ≠ radius j := by
    intro h; rw [h] at hwc; linarith
  rw [WedgeCan.avgReg_wedgeField_eq hG hraw hA Q₀ hw hne]
  exact avgReg_add_ofFun_congr hc₀ (fun z hz => (profCut_eq hz).symm) hwc hj

end G1Side
end QuantumZipper
