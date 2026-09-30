import QuantumZipper.Proofs.Thm18.RT5FarDrv
import QuantumZipper.Proofs.Loewner.CaraR8
import QuantumZipper.Proofs.Loewner.Algebra
import QuantumZipper.Proofs.Thm18.LWFarCondFlow
import QuantumZipper.Proofs.Thm12.CharFun
import QuantumZipper.Proofs.Zipper.Cor15Partial
import QuantumZipper.Proofs.Zipper.F1ReflReg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT5 FarPull, deterministic geometric form

Sheffield, arXiv:1012.4797, p. 26 (`Z_ℓ` welds the pieces conformally). With the Carathéodory
extension `E` of `revMap W' T` (`CaraR.revMapCaratheodory`; Pommerenke, *Boundary Behaviour of
Conformal Maps*, Thm 2.1), Loewner concatenation gives `E(η'(u)) = η_V(T + u)` for the unzipped
curve `η'` of `D = outDrv W s b`, and the zipped hull `K_T` is the first part of the zipped curve
(`LoewnerAlgebra.revHull_eq_fwdHull_timeRev`, hull scaling). When the canonical zipped driver
agrees with the good driver `W` (T7b), both lie in the zipped curve; the compactness core
`rt5far_pointwise` then gives positive distance. Own elementary argument.
-/

noncomputable section

open MeasureTheory Filter Set Metric Topology
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

theorem rt5far_geo {W W' : ℝ → ℝ} {T s b a : ℝ} (hW : RS.RadialGood W)
    (hinj : InjOn (trace W) (Ici 0)) (hH : ∀ t > (0 : ℝ), trace W t ∈ H)
    (hhull : ∀ t : ℝ, 0 ≤ t → fwdHull W t = trace W '' Ioc 0 t) (hs : 0 ≤ s) (hb : 0 < b)
    (hT : 0 ≤ T) (hW'c : Continuous W') (hW'0 : W' 0 = 0)
    (hK : T = 0 ∨ IsSimpleCurveHull (revHull W' T)) (ha : 0 < a)
    (hV : ∀ u : ℝ, 0 ≤ u → rt5V T W' (outDrv W s b) (a ^ 2 * max u 0) / a = W u)
    (d : ℂ) (k : ℕ)
    (hoff : CircleOff {w : ℂ | ((a⁻¹ : ℝ) : ℂ) * w ∈
      curveOf (fun u => rt5V T W' (outDrv W s b) (a ^ 2 * max u 0) / a)} d (radius k)) :
    ∃ δ > 0, ∀ᵐ w ∂((foldedCircle d (radius k)).map (revMapInv W' T)),
      0 ≤ w.im ∧ ∀ q ∈ curveOf (outDrv W s b), δ ≤ dist w q := by
  have hWc := hW.1
  have hW0 := hW.2.1
  set D := outDrv W s b with hDdef
  set V := rt5V T W' D with hVdef
  have hDc : Continuous D := by rw [hDdef]; unfold outDrv; fun_prop
  have hD0 : D 0 = 0 := by simp [hDdef, outDrv]
  have hVc : Continuous V := continuous_rt5V hT hWc hW0 ha hV
  have hV0 : V 0 = 0 := rt5V_zero hT
  have hai : 0 < a⁻¹ := inv_pos.2 ha
  -- the zipped curve is the curve of `W`
  have hcurve : curveOf (fun u => V (a ^ 2 * max u 0) / a) = curveOf W := by
    have hCc : Continuous fun u => V (a ^ 2 * max u 0) / a := by fun_prop
    have hC0 : (fun u => V (a ^ 2 * max u 0) / a) 0 = 0 := by simp [hV0]
    unfold curveOf
    congr 1
    ext z
    simp only [mem_range]
    refine exists_congr fun q => ?_
    rw [RS.trace_congr_drive hCc hC0 hWc hW0 q.cast_nonneg fun r hr => hV r hr.1]
  rw [hcurve] at hoff
  set Z : Set ℂ := {w : ℂ | ((a⁻¹ : ℝ) : ℂ) * w ∈ curveOf W} with hZdef
  have hZc : IsClosed Z := isClosed_closure.preimage (continuous_const.mul continuous_id)
  have hmemZ : ∀ τ : ℝ, 0 ≤ τ → trace W τ / ((a⁻¹ : ℝ) : ℂ) ∈ Z := fun τ hτ => by
    have hac : ((a⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hai.ne'
    show ((a⁻¹ : ℝ) : ℂ) * (trace W τ / ((a⁻¹ : ℝ) : ℂ)) ∈ curveOf W
    rw [mul_div_cancel₀ _ hac]
    exact trace_mem_curveOf hW.2.2.2.1 hτ
  -- the Carathéodory extension
  obtain ⟨E, hE, hEc⟩ : ∃ E : ℂ → ℂ, EqOn E (revMap W' T) H ∧ ContinuousOn E Hbar := by
    rcases hT.lt_or_eq with hTp | hT0
    · have hK' : IsSimpleCurveHull (revHull W' T) := hK.resolve_left hTp.ne'
      obtain ⟨F, hF⟩ := CaraR.revMapCaratheodory W' hW'c hW'0 T hTp hK'
      exact ⟨F, hF.1, hF.2.1⟩
    · subst hT0
      exact ⟨id, fun z hz => (CharFun.revMap_zero_eq hW'c hW'0 hz).symm, continuousOn_id⟩
  -- the unzipped curve lies in `ℍ̄` and is mapped by `E` into the zipped curve
  have hDbar : ∀ u : ℝ, 0 ≤ u → trace D u ∈ Hbar := fun u hu =>
    isClosed_Hbar.mem_of_tendsto
      (tendsto_fwdMapInv_outDrv hW hinj hH hs (hhull s hs) hb hu)
      (Eventually.of_forall fun y => F1.fwdMapInv_mem_Hbar _ _ _)
  have htrD : ∀ u : ℝ, 0 ≤ u → E (trace D u) ∈ Z := by
    intro u hu
    have hlimD := tendsto_fwdMapInv_outDrv hW hinj hH hs (hhull s hs) hb hu
    have hE1 : Tendsto (fun y : ℝ => E (fwdMapInv D u (y * Complex.I))) (𝓝[>] 0)
        (𝓝 (E (trace D u))) :=
      (hEc _ (hDbar u hu)).tendsto.comp (tendsto_nhdsWithin_iff.2
        ⟨hlimD, Eventually.of_forall fun y => F1.fwdMapInv_mem_Hbar _ _ _⟩)
    have hV2 := (tendsto_fwdMapInv_rt5V hT hW ha hV (t := T + u) (by linarith)).1
    have hSc : Continuous (RS.shiftDrive V T) := RS.continuous_shiftDrive hVc T
    have hE2 : Tendsto (fun y : ℝ => E (fwdMapInv D u (y * Complex.I))) (𝓝[>] 0)
        (𝓝 (trace W (a⁻¹ ^ 2 * (T + u)) / ((a⁻¹ : ℝ) : ℂ))) := by
      refine hV2.congr' (eventually_mem_nhdsWithin.mono fun y hy => ?_)
      have hyH := RS.mul_I_mem_H hy
      have hDH := RS.fwdMapInv_mem_H hDc hD0 hu hyH
      rw [RS.fwdMapInv_add_shift hVc hV0 hT hu hyH,
        RS.fwdMapInv_congr_Ici hSc (RS.shiftDrive_zero V T) hDc hD0
          (rt5V_shift hW'0 hT hD0) hu hyH,
        fwdMapInv_rt5V_eq hVc hT hW'0 hDH]
      exact (hE hDH).symm
    rw [tendsto_nhds_unique hE1 hE2]
    exact hmemZ _ (by positivity)
  have hEK : ∀ q ∈ curveOf D, E q ∈ Z := by
    intro q hq
    have hsub : closure (range fun q : ℚ≥0 => trace D (q : ℝ)) ⊆ Hbar :=
      closure_minimal (by rintro _ ⟨r, rfl⟩; exact hDbar _ r.cast_nonneg) isClosed_Hbar
    have h1 := (hEc.mono hsub).image_closure (mem_image_of_mem E hq)
    refine closure_minimal ?_ hZc h1
    rintro _ ⟨_, ⟨r, rfl⟩, rfl⟩
    exact htrD _ r.cast_nonneg
  -- the zipped hull lies in the zipped curve
  have hhullZ : H \ revMap W' T '' H ⊆ Z := by
    rintro z ⟨hzH, hzn⟩
    rcases hT.lt_or_eq with hTp | hT0
    · have hz : z ∈ revHull W' T := ⟨hzH, hzn⟩
      rw [LoewnerAlgebra.revHull_eq_fwdHull_timeRev W' hW'c hW'0 hTp] at hz
      have hRc : Continuous fun r => W' (T - r) - W' T := by fun_prop
      have hz2 : z ∈ fwdHull V T :=
        (Thm18Asm.LWFar.lwc_mem_fwdHull_congr hRc hVc hT (fun r hr => by
          simp only [hVdef, rt5V, if_pos hr.2, max_eq_left hr.1]) z).1 hz
      have hSc : Continuous fun r => W (a⁻¹ ^ 2 * r) / a⁻¹ := by fun_prop
      have hz3 : z ∈ fwdHull (fun r => W (a⁻¹ ^ 2 * r) / a⁻¹) T :=
        (Thm18Asm.LWFar.lwc_mem_fwdHull_congr hVc hSc hT (fun r hr => by
          rw [hVdef, rt5V_eq_scale hT hW0 ha hV r, max_eq_left hr.1]) z).1 hz2
      rw [LoewnerAlgebra.mem_fwdHull_scale_iff W hai hT, hhull _ (by positivity)] at hz3
      obtain ⟨τ, hτ, heq⟩ := hz3
      show ((a⁻¹ : ℝ) : ℂ) * z ∈ curveOf W
      rw [← heq]
      exact trace_mem_curveOf hW.2.2.2.1 hτ.1.le
    · subst hT0
      exact absurd ⟨z, hzH, CharFun.revMap_zero_eq hW'c hW'0 hzH⟩ hzn
  -- bounded preimages
  have hbd : ∃ M : ℝ, ∀ w ∈ ASep.foldSph d (radius k), w ∈ H → ‖revMapInv W' T w‖ ≤ M := by
    obtain ⟨C, hC⟩ := (ASep.isCompact_foldSph d (radius k)).isBounded.exists_norm_le
    rcases hT.lt_or_eq with hTp | hT0
    · obtain ⟨M0, hM0⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
        hW'c.continuousOn
      have hM0' : ∀ r ∈ Icc (0 : ℝ) T, |W' r| ≤ M0 := fun r hr => by
        have := hM0 r hr; rwa [Real.norm_eq_abs] at this
      have hM0n : 0 ≤ M0 := le_trans (abs_nonneg _) (hM0' 0 ⟨le_rfl, hTp.le⟩)
      refine ⟨C + (12 * M0 + 8 * Real.sqrt T), fun w hwS hwH => ?_⟩
      by_cases hw : w ∈ revMap W' T '' H
      · have := Cor15Group.norm_revMapInv_le hW'c hW'0 hTp hM0' hw
        linarith [hC w hwS]
      · rw [Cor15Group.revMapInv_eq_zero_of_notMem hw, norm_zero]
        have := hC w hwS
        have := norm_nonneg w
        linarith [Real.sqrt_nonneg T]
    · subst hT0
      exact ⟨C, fun w hwS hwH => by
        rw [Cor15Partial.revMapInv_zero_eqOn hW'c hW'0 hwH]; exact hC w hwS⟩
  obtain ⟨δ, hδ, hpt⟩ := rt5far_pointwise hE hEc isClosed_closure hEK hhullZ
    (ASep.isCompact_foldSph d (radius k)) (rt5far_foldSph_notMem hoff) hbd
    (fun w hw => Cor15Group.revMapInv_mem_H hW'c hT hw)
  exact ⟨δ, hδ, rt5far_ae hW'c hT (radius_pos k) hpt⟩

end R18
end QuantumZipper
