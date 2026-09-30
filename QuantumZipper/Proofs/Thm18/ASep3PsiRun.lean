import QuantumZipper.Proofs.Thm18.ASep3Psi
import QuantumZipper.Proofs.Thm18.ASep3Ident
import QuantumZipper.Proofs.Thm18.ASepFreeBox
import QuantumZipper.Proofs.Thm18.ASepPathDefs
import QuantumZipper.Proofs.Zipper.UnifUC1Push

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP3 (step 12): the scale analogue of `ae_tendsto_PsiK_all` on one box

For a fixed dyadic folded circle `fc(w, r)` and a rational box of `(t, s)` with `t ∈ [0, T]`,
`s ∈ [s₀, s₁]`, `s₀ > 0`: almost surely, for all `(t, s)` in the box, the level-`j`
regularizations `∫ avgReg (rescale X Q s) j dν_t`, `ν_t = fc(w, r).map f_t⁻¹`, converge as
`j → ∞` (`ae_tendsto_rescale_νT_box`).

Engine run (`GenUC.ae_unifConv_all`): family `genFam_bindνT_dil` (ASep3Psi), identity
`ae_integral_avgReg_rescale_eq` (ASep3Ident), pathwise continuity in `(t, s)`
(`continuousOn_integral_avgReg_rescale`, dominated convergence as in
`RegCont.continuousOn_integral_νT`). Own bookkeeping.

Also: all dyadic circles, times and scales at once (`ae_tendsto_rescale_νT_all`,
`ae_tendsto_PsiK_rescale_all` — the scale version of the input `hψω` of `ae_concl0_prof`);
inner exactness at a fixed parameter (`ae_tendsto_rescale_νT_fixed`); continuity in `(t, s)`
of `evalReg (rescale X Q s) ν_t` on boxes (`ae_continuousOn_evalReg_rescale_box`).

**Remaining for `G4SepScale0Stmt` (ASEP3 route).** (i) the scale joint witness: a.s. a `Z(s,t,·)`
jointly continuous with `IsRegularWith (coordChange (rescale X Q s) f_t⁻¹ Q) (Z (s, t, ·))`
(from the glued modification `exists_contMod_νT_rescale` (ASep3InnerGlob), `ae_tendsto_rescale_νT_fixed`,
`ae_continuousOn_evalReg_rescale_box`, `integral_circleAvg_ae_eq_bind_rho`,
`RegUnif.forall_isRegularWith_of_joint`); (ii) the outer runs (scale versions of
`ae_tendsto_free_all` and `ae_tendsto_Phi_zero_all`) with `genFam_scaleBox` and
`ae_tendsto_open_depShift`; (iii) the deterministic re-run of `ae_conj1_add_good`,
`ae_conj2_add_good`, `ae_concl0_prof` for `rescale (ofFun g + X ω) Q s`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology

namespace QuantumZipper
namespace ASep

open GenUC

/-- **Pathwise continuity in `(t, s)` of level-`j` averages of a field family.** -/
theorem continuousOn_integral_avgReg_fam {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {T s₀ s₁ : ℝ} (w : ℂ) {r : ℝ} (hr : 0 < r) (y : ℝ → FieldSample) (j : ℕ)
    {G : ℝ × ℂ → ℝ} (hGc : ContinuousOn G (Icc s₀ s₁ ×ˢ Hbar))
    (hGeq : ∀ s ∈ Icc s₀ s₁, ∀ z ∈ Hbar, avgReg (y s) j z = G (s, z)) {S : Set (Fin 2 → ℝ)}
    (hS : ∀ q ∈ S, q 0 ∈ Icc (0 : ℝ) T ∧ q 1 ∈ Icc s₀ s₁) :
    ContinuousOn (fun q : Fin 2 → ℝ => ∫ z, avgReg (y (q 1)) j z ∂RegCont.νT W w r (q 0)) S := by
  obtain ⟨M, hM⟩ := RegCont.exists_abs_le_on_Icc hW T
  obtain ⟨Bf, hBf⟩ : ∃ Bf : ℝ, Bf = RegCont.revBound (2 * M) T (‖w‖ + r) := ⟨_, rfl⟩
  have hK : IsCompact (Icc s₀ s₁ ×ˢ (closedBall (0 : ℂ) Bf ∩ Hbar)) :=
    isCompact_Icc.prod ((isCompact_closedBall _ _).inter_right isClosed_Hbar)
  obtain ⟨Cb, hCb⟩ := hK.exists_bound_of_continuousOn
    (hGc.mono (prod_mono subset_rfl inter_subset_right))
  have hmz : ∀ s : ℝ, Measurable fun z => avgReg (y s) j z := fun s =>
    (measurable_avgReg j).comp (f := fun z : ℂ => (y s, z)) (measurable_const.prodMk measurable_id)
  have e : EqOn (fun q : Fin 2 → ℝ => ∫ z, avgReg (y (q 1)) j z ∂RegCont.νT W w r (q 0))
      (fun q => ∫ u, avgReg (y (q 1)) j (fwdMapInv W (q 0) u) ∂foldedCircle w r) S :=
    fun q hq => by
      simp only [RegCont.νT]
      rw [integral_map (RegCont.aemeasurable_fwdMapInv hW hW0 (hS q hq).1.1 w hr)
        (hmz _).aestronglyMeasurable]
  refine ContinuousOn.congr ?_ e
  refine continuousOn_of_dominated (bound := fun _ => Cb)
    (fun q hq => ((hmz _).comp_aemeasurable
      (RegCont.aemeasurable_fwdMapInv hW hW0 (hS q hq).1.1 w hr)).aestronglyMeasurable)
    (fun q hq => ?_) (integrable_const Cb) ?_
  · filter_upwards [TwoPoint.foldedCircle_ae_mem_H w hr, TwoPoint.foldedCircle_ae_norm_le w hr.le]
      with u hu hun
    obtain ⟨h1, h2⟩ := RegCont.fwdMapInv_mem_H_bound hW hW0 hM (hS q hq).1.1 (hS q hq).1.2 hu hun
    rw [← hBf] at h2
    have hzH : fwdMapInv W (q 0) u ∈ Hbar := (show 0 < (fwdMapInv W (q 0) u).im from h1).le
    rw [hGeq _ (hS q hq).2 _ hzH]
    exact hCb _ ⟨(hS q hq).2, mem_closedBall_zero_iff.2 h2, hzH⟩
  · filter_upwards [TwoPoint.foldedCircle_ae_mem_H w hr] with u hu
    have hmemH : ∀ q ∈ S, fwdMapInv W (q 0) u ∈ Hbar := fun q hq => by
      obtain ⟨h1, -⟩ := RegCont.fwdMapInv_mem_H_bound hW hW0 hM (hS q hq).1.1 (hS q hq).1.2 hu
        (le_refl ‖u‖)
      exact (show 0 < (fwdMapInv W (q 0) u).im from h1).le
    have hc1 : ContinuousOn (fun q : Fin 2 → ℝ => (q 1, fwdMapInv W (q 0) u)) S := by
      refine (continuous_apply 1).continuousOn.prodMk ?_
      exact (RegCont.continuousOn_fwdMapInv_time hW hW0 (T := T) hu).comp
        (continuous_apply 0).continuousOn fun q hq => (hS q hq).1
    refine ((hGc.comp hc1 fun q hq => ⟨(hS q hq).2, hmemH q hq⟩)).congr fun q hq => ?_
    exact hGeq _ (hS q hq).2 _ (hmemH q hq)

/-- The rescaled field's level-`j` averages through the witness. -/
theorem avgReg_rescale_eq_G {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F) (Q : ℝ)
    (j : ℕ) {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z ∈ Hbar) :
    avgReg (rescale x Q s) j z = F ((s : ℂ) * z, s * radius j) + Q * Real.log s :=
  (hF.rescale' Q hs).avgReg_eq j hz

theorem continuousOn_G_rescale {F : ℂ × ℝ → ℝ} (hF : ContinuousOn F (Hbar ×ˢ Ioi 0)) (Q : ℝ)
    (j : ℕ) {s₀ s₁ : ℝ} (hs₀ : 0 < s₀) :
    ContinuousOn (fun p : ℝ × ℂ => F ((p.1 : ℂ) * p.2, p.1 * radius j) + Q * Real.log p.1)
      (Icc s₀ s₁ ×ˢ Hbar) := by
  have h1 : ContinuousOn (fun p : ℝ × ℂ => ((p.1 : ℂ) * p.2, p.1 * radius j))
      (Icc s₀ s₁ ×ˢ Hbar) :=
    (((Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd).prodMk
      (continuous_fst.mul continuous_const)).continuousOn
  have h2 : MapsTo (fun p : ℝ × ℂ => ((p.1 : ℂ) * p.2, p.1 * radius j)) (Icc s₀ s₁ ×ˢ Hbar)
      (Hbar ×ˢ Ioi 0) := fun p hp =>
    ⟨RegClosure.mapsTo_mul_pos (hs₀.trans_le hp.1.1) hp.2,
      mul_pos (hs₀.trans_le hp.1.1) (radius_pos j)⟩
  refine (hF.comp h1 h2).add (continuousOn_const.mul ?_)
  exact Real.continuousOn_log.comp continuous_fst.continuousOn fun p hp =>
    (hs₀.trans_le hp.1.1).ne'
/-- **Engine run on one box**, with the limit identified at each fixed parameter. -/
theorem rescale_νT_box_engine {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T a CH : ℝ} (hT : 0 < T) (ha : 0 < a)
    (ha1 : a ≤ 1) (hCH : 0 ≤ CH)
    (hH : ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, |t - t'| ≤ 1 / 2 →
      |W t - W t'| ≤ CH * |t - t'| ^ a)
    (w : ℂ) {r : ℝ} (hr : 0 < r) (Q : ℝ) {lo hi : Fin 2 → ℚ} (hlohi : ∀ i, (lo i : ℝ) ≤ hi i)
    (h0 : (0 : ℝ) ≤ lo 0) (h1 : (hi 0 : ℝ) ≤ T) (hs₀ : (0 : ℝ) < lo 1) :
    ∃ Lim : (Fin 2 → ℝ) → Ω → ℝ, (∀ ω, ContinuousOn (fun q => Lim q ω) (ratBox lo hi)) ∧
      (∀ q ∈ ratBox lo hi, (fun ω => Lim q ω) =ᵐ[P] fun ω =>
        X ω ((RegCont.bindFc (RegCont.νT W w r (q 0)) 0).map fun z => ((q 1 : ℝ) : ℂ) * z) +
          Q * Real.log (q 1)) ∧
      ∀ᵐ ω ∂P, ∀ q ∈ ratBox lo hi, Tendsto
        (fun j : ℕ => ∫ z, avgReg (rescale (X ω) Q (q 1)) j z ∂RegCont.νT W w r (q 0)) atTop
          (𝓝 (Lim q ω)) := by
  set S := ratBox lo hi with hSdef
  have hSb : ∀ q ∈ S, q 0 ∈ Icc (0 : ℝ) T ∧ q 1 ∈ Icc (lo 1 : ℝ) (hi 1) := fun q hq =>
    ⟨⟨h0.trans (hq 0 (mem_univ _)).1, (hq 0 (mem_univ _)).2.trans h1⟩, hq 1 (mem_univ _)⟩
  have hs : ∀ q ∈ S, 0 < q 1 := fun q hq => hs₀.trans_le (hSb q hq).2.1
  have hS₁ : ∀ p ∈ ratBox (Fin.init lo) (Fin.init hi), p 0 ∈ Icc (0 : ℝ) T := fun p hp =>
    ⟨h0.trans (hp 0 (mem_univ _)).1, (hp 0 (mem_univ _)).2.trans h1⟩
  obtain ⟨K, c, hF⟩ := genFam_bindνT_dil hW hW0 hT ha ha1 hCH hH hr hS₁
    (s₀ := (lo (Fin.last 1) : ℝ)) (s₁ := (hi (Fin.last 1) : ℝ)) hs₀
  rw [← ratBox_eq_dilSet] at hF
  obtain ⟨D, hDc, hDS, hSD⟩ := TopologicalSpace.exists_countable_dense_subset S
  obtain ⟨Cν, Bν, -, -, hν⟩ := RegCont.νT_facts hW hW0 T w hr
  have hRI : range radius ⊆ Icc (0 : ℝ) 1 := by
    rintro _ ⟨j, rfl⟩
    exact ⟨(radius_pos j).le, by unfold radius; exact pow_le_one₀ (by norm_num) (by norm_num)⟩
  set Φ : ℝ → (Fin 2 → ℝ) → Ω → ℝ := fun ρ q ω =>
    ∫ z, avgReg (rescale (X ω) Q (q 1)) (jOf ρ) z ∂RegCont.νT W w r (q 0) with hΦ
  set dt : ℝ → (Fin 2 → ℝ) → ℝ := fun _ q => Q * Real.log (q 1) with hdt
  have hdetc : ContinuousOn (fun q : Fin 2 → ℝ => Q * Real.log (q 1)) S :=
    continuousOn_const.mul (Real.continuousOn_log.comp (continuous_apply 1).continuousOn
      fun q hq => (hs q hq).ne')
  have hid : ∀ ρ ∈ range radius, ∀ q ∈ D, ∀ᵐ ω ∂P,
      Φ ρ q ω = X ω (dilFam (bindνT W w r) q ρ) + dt ρ q := by
    rintro _ ⟨j, rfl⟩ q hq
    have hqS := hDS hq
    obtain ⟨hP, -, hB⟩ := hν (q 0) (hSb q hqS).1
    have hKc : IsCompact (closedBall (0 : ℂ) Bν ∩ Hbar) :=
      (isCompact_closedBall _ _).inter_right isClosed_Hbar
    have hνK : RegCont.νT W w r (q 0) (closedBall (0 : ℂ) Bν ∩ Hbar)ᶜ = 0 := by
      refine ae_iff.1 ?_
      filter_upwards [hB] with z hz
      exact ⟨mem_closedBall_zero_iff.2 hz.2, (show (0 : ℝ) < z.im from hz.1).le⟩
    filter_upwards [ae_integral_avgReg_rescale_eq hX Q (hs q hqS) j (RegCont.νT W w r (q 0)) hKc
      inter_subset_right hνK] with ω hω
    simp only [hΦ, hdt, jOf_radius]
    exact hω
  have hdet : ∀ ε > 0, ∃ δ > 0, ∀ ρ ∈ range radius, ρ < δ → ∀ q ∈ S,
      |dt ρ q - Q * Real.log (q 1)| < ε := fun ε hε => ⟨1, one_pos, fun ρ _ _ q _ => by
        simp only [hdt, sub_self, abs_zero]; exact hε⟩
  have hΦc : ∀ᵐ ω ∂P, ∀ ρ ∈ range radius, ContinuousOn (fun q => Φ ρ q ω) S := by
    filter_upwards [RegSample.ae_isRegularSample hX] with ω hreg
    obtain ⟨F, hFw⟩ := hreg
    rintro _ ⟨j, rfl⟩
    simp only [hΦ, jOf_radius]
    exact continuousOn_integral_avgReg_fam hW hW0 w hr (fun s => rescale (X ω) Q s) j
      (continuousOn_G_rescale hFw.1 Q j hs₀)
      (fun s hs' z hz => avgReg_rescale_eq_G hFw Q j (hs₀.trans_le hs'.1) hz) hSb
  obtain ⟨Lim, hLc, hLe, hconv⟩ := ae_unifConv_all hX hF (isLipRetr_ratBox hlohi)
    (isCompact_ratBox _ _) hDc hDS hSD (countable_range _) hRI Φ dt
    (fun q => Q * Real.log (q 1)) hdetc hid hdet hΦc
  have hrad : Tendsto radius atTop (𝓝 0) := by
    unfold radius
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  refine ⟨Lim, hLc, fun q hq => hLe q hq, ?_⟩
  filter_upwards [hconv] with ω hω q hq
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  obtain ⟨δ, hδ, hδc⟩ := hω (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hrad.eventually (gt_mem_nhds hδ))
  refine ⟨N, fun j hj => ?_⟩
  have := hδc (radius j) ⟨j, rfl⟩ (hN j hj) q hq
  simp only [hΦ, jOf_radius] at this
  rw [Real.dist_eq]
  linarith
/-- **The scale analogue of `ae_tendsto_PsiK_all` on one box.** -/
theorem ae_tendsto_rescale_νT_box {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T a CH : ℝ} (hT : 0 < T) (ha : 0 < a)
    (ha1 : a ≤ 1) (hCH : 0 ≤ CH)
    (hH : ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, |t - t'| ≤ 1 / 2 →
      |W t - W t'| ≤ CH * |t - t'| ^ a)
    (w : ℂ) {r : ℝ} (hr : 0 < r) (Q : ℝ) {lo hi : Fin 2 → ℚ} (hlohi : ∀ i, (lo i : ℝ) ≤ hi i)
    (h0 : (0 : ℝ) ≤ lo 0) (h1 : (hi 0 : ℝ) ≤ T) (hs₀ : (0 : ℝ) < lo 1) :
    ∀ᵐ ω ∂P, ∀ q ∈ ratBox lo hi, ∃ L : ℝ, Tendsto
      (fun j : ℕ => ∫ z, avgReg (rescale (X ω) Q (q 1)) j z ∂RegCont.νT W w r (q 0)) atTop
        (𝓝 L) := by
  obtain ⟨Lim, -, -, h⟩ := rescale_νT_box_engine hX hW hW0 hT ha ha1 hCH hH w hr Q hlohi h0 h1 hs₀
  filter_upwards [h] with ω hω q hq
  exact ⟨_, hω q hq⟩

/-- **The scale analogue of `ae_tendsto_PsiK_all`**: almost surely, for every dyadic folded
circle, every time `t ≥ 0` and **every scale `s > 0`**, the regularizations of `rescale X Q s`
at the pushed circle converge. -/
theorem ae_tendsto_rescale_νT_all {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P)
    {W : ℝ → ℝ} (hWg : DrvGood W) (Q : ℝ) :
    ∀ᵐ ω ∂P, ∀ d ∈ RegUnif.Dy, ∀ k : ℕ, ∀ t : ℝ, 0 ≤ t → ∀ s : ℝ, 0 < s → ∃ L : ℝ, Tendsto
      (fun j : ℕ => ∫ z, avgReg (rescale (X ω) Q s) j z ∂RegCont.νT W d (radius k) t) atTop
        (𝓝 L) := by
  obtain ⟨hW, hW0, hHol, -⟩ := hWg
  have hbox : ∀ lohi : (Fin 2 → ℚ) × (Fin 2 → ℚ), ∀ k : ℕ, ∀ d : ℂ, ∀ᵐ ω ∂P,
      ((∀ i, (lohi.1 i : ℝ) ≤ lohi.2 i) ∧ (0 : ℝ) ≤ lohi.1 0 ∧ (0 : ℝ) < lohi.1 1 ∧
        (0 : ℝ) < lohi.2 0) → ∀ q ∈ ratBox lohi.1 lohi.2, ∃ L : ℝ, Tendsto
          (fun j : ℕ => ∫ z, avgReg (rescale (X ω) Q (q 1)) j z ∂RegCont.νT W d (radius k) (q 0))
          atTop (𝓝 L) := by
    intro lohi k d
    by_cases hc : (∀ i, (lohi.1 i : ℝ) ≤ lohi.2 i) ∧ (0 : ℝ) ≤ lohi.1 0 ∧ (0 : ℝ) < lohi.1 1 ∧
        (0 : ℝ) < lohi.2 0
    · obtain ⟨hlohi, h0, hs₀, hT⟩ := hc
      obtain ⟨α, CH, hα, hα1, hCH, hH⟩ := hHol _ hT
      filter_upwards [ae_tendsto_rescale_νT_box hX hW hW0 hT hα hα1 hCH hH d (radius_pos k) Q
        hlohi h0 le_rfl hs₀] with ω hω _
      exact hω
    · exact ae_of_all _ fun ω h => absurd h hc
  have hall := ae_all_iff.2 fun lohi => ae_all_iff.2 fun k =>
    (eventually_countable_ball RegUnif.countable_Dy).2 fun d _ => hbox lohi k d
  filter_upwards [hall] with ω hω d hd k t ht s hs
  obtain ⟨q₁, hq₁0, hq₁s⟩ := exists_rat_btwn hs
  obtain ⟨q₃, hq₃⟩ := exists_rat_gt s
  obtain ⟨q₂, hq₂⟩ := exists_rat_gt t
  have hmem : (![t, s] : Fin 2 → ℝ) ∈ ratBox (![0, q₁] : Fin 2 → ℚ) ![q₂, q₃] := by
    intro i _
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, Rat.cast_zero, mem_Icc]
      exact ⟨ht, hq₂.le⟩
    · simp only [Fin.mk_one, Matrix.cons_val_one, Rat.cast_zero, mem_Icc]
      exact ⟨hq₁s.le, hq₃.le⟩
  have hcond : (∀ i, (((![0, q₁] : Fin 2 → ℚ) i : ℚ) : ℝ) ≤ ((![q₂, q₃] : Fin 2 → ℚ) i : ℝ)) ∧
      (0 : ℝ) ≤ ((![0, q₁] : Fin 2 → ℚ) 0 : ℝ) ∧ (0 : ℝ) < ((![0, q₁] : Fin 2 → ℚ) 1 : ℝ) ∧
      (0 : ℝ) < ((![q₂, q₃] : Fin 2 → ℚ) 0 : ℝ) := by
    refine ⟨fun i => ?_, ?_, ?_, ?_⟩
    · fin_cases i
      · simp only [Fin.zero_eta, Matrix.cons_val_zero, Rat.cast_zero]; linarith
      · show ((q₁ : ℚ) : ℝ) ≤ ((q₃ : ℚ) : ℝ)
        linarith
    · simp
    · simpa using hq₁0
    · simp only [Matrix.cons_val_zero]; linarith
  obtain ⟨L, hL⟩ := hω (![0, q₁], ![q₂, q₃]) k d hd hcond _ hmem
  exact ⟨L, by simpa using hL⟩
/-- **Scale analogue of `ae_tendsto_PsiK_all`, `evalReg` form** (the exact scale version of the
input `hψω` of `ae_concl0_prof`). -/
theorem ae_tendsto_PsiK_rescale_all {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P)
    {W : ℝ → ℝ} (hWg : DrvGood W) (Q : ℝ) :
    ∀ᵐ ω ∂P, ∀ s : ℝ, 0 < s → ∀ d ∈ RegUnif.Dy, ∀ k : ℕ, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun j => ∫ z, avgReg (rescale (X ω) Q s) j z ∂RegCont.νT W d (radius k) t) atTop
        (𝓝 (evalReg (rescale (X ω) Q s) (RegCont.νT W d (radius k) t))) := by
  filter_upwards [ae_tendsto_rescale_νT_all hX hWg Q] with ω hω s hs d hd k t ht
  obtain ⟨L, hL⟩ := hω d hd k t ht s hs
  have e : evalReg (rescale (X ω) Q s) (RegCont.νT W d (radius k) t) = L := hL.limUnder_eq
  rw [e]; exact hL
/-- **Inner exactness at a fixed parameter**: for fixed `t ≥ 0`, `s > 0`, almost surely the
regularizations of `rescale X Q s` at the pushed circle converge to
`X(ν_t.map (s ·)) + Q log s`, the raw pairing of the rescaled field there. -/
theorem ae_tendsto_rescale_νT_fixed {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P)
    {W : ℝ → ℝ} (hWg : DrvGood W) (Q : ℝ) (w : ℂ) {r : ℝ} (hr : 0 < r) {t : ℝ} (ht : 0 ≤ t)
    {s : ℝ} (hs : 0 < s) :
    ∀ᵐ ω ∂P, Tendsto (fun j => ∫ z, avgReg (rescale (X ω) Q s) j z ∂RegCont.νT W w r t) atTop
      (𝓝 (X ω ((RegCont.νT W w r t).map fun z => (s : ℂ) * z) + Q * Real.log s)) := by
  obtain ⟨hW, hW0, hHol, -⟩ := hWg
  obtain ⟨q₁, hq₁0, hq₁s⟩ := exists_rat_btwn hs
  obtain ⟨q₃, hq₃⟩ := exists_rat_gt s
  obtain ⟨q₂, hq₂⟩ := exists_rat_gt t
  have hT : (0 : ℝ) < q₂ := lt_of_le_of_lt ht hq₂
  obtain ⟨α, CH, hα, hα1, hCH, hH⟩ := hHol _ hT
  have hlohi : ∀ i, (((![0, q₁] : Fin 2 → ℚ) i : ℚ) : ℝ) ≤ ((![q₂, q₃] : Fin 2 → ℚ) i : ℝ) := by
    intro i
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, Rat.cast_zero]; linarith
    · show ((q₁ : ℚ) : ℝ) ≤ ((q₃ : ℚ) : ℝ)
      linarith
  have hmem : (![t, s] : Fin 2 → ℝ) ∈ ratBox (![0, q₁] : Fin 2 → ℚ) ![q₂, q₃] := by
    intro i _
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, Rat.cast_zero, mem_Icc]
      exact ⟨ht, hq₂.le⟩
    · simp only [Fin.mk_one, Matrix.cons_val_one, Rat.cast_zero, mem_Icc]
      exact ⟨hq₁s.le, hq₃.le⟩
  obtain ⟨Lim, -, hLe, hconv⟩ := rescale_νT_box_engine hX hW hW0 hT hα hα1 hCH hH w hr Q hlohi
    (by simp) le_rfl (by simpa using hq₁0)
  obtain ⟨Cν, Bν, -, -, hν⟩ := RegCont.νT_facts hW hW0 (q₂ : ℝ) w hr
  obtain ⟨hP, -, hB⟩ := hν t ⟨ht, hq₂.le⟩
  have hH' : ∀ᵐ z ∂RegCont.νT W w r t, z ∈ H := hB.mono fun z hz => hz.1
  have e0 : RegCont.bindFc (RegCont.νT W w r t) 0 = RegCont.νT W w r t :=
    RegUnif.bindFc_zero_of_ae_H hH'
  filter_upwards [hLe _ hmem, hconv] with ω h1 h2
  have h3 := h2 _ hmem
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h1 h3
  rw [e0] at h1
  rw [← h1]
  exact h3
/-- **Continuity in `(t, s)` of the regularized pairing of the rescaled field** at a pushed
circle, on one box (the scale analogue of the continuity input
`ae_continuousOn_coordChange_logAdd_Dy` of the joint witness). -/
theorem ae_continuousOn_evalReg_rescale_box {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T a CH : ℝ} (hT : 0 < T) (ha : 0 < a)
    (ha1 : a ≤ 1) (hCH : 0 ≤ CH)
    (hH : ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, |t - t'| ≤ 1 / 2 →
      |W t - W t'| ≤ CH * |t - t'| ^ a)
    (w : ℂ) {r : ℝ} (hr : 0 < r) (Q : ℝ) {lo hi : Fin 2 → ℚ} (hlohi : ∀ i, (lo i : ℝ) ≤ hi i)
    (h0 : (0 : ℝ) ≤ lo 0) (h1 : (hi 0 : ℝ) ≤ T) (hs₀ : (0 : ℝ) < lo 1) :
    ∀ᵐ ω ∂P, ContinuousOn
      (fun q : Fin 2 → ℝ => evalReg (rescale (X ω) Q (q 1)) (RegCont.νT W w r (q 0)))
      (ratBox lo hi) := by
  obtain ⟨Lim, hLc, -, h⟩ := rescale_νT_box_engine hX hW hW0 hT ha ha1 hCH hH w hr Q hlohi h0 h1
    hs₀
  filter_upwards [h] with ω hω
  refine (hLc ω).congr fun q hq => ?_
  exact (hω q hq).limUnder_eq

end ASep
end QuantumZipper
