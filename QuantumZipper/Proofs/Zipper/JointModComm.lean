import QuantumZipper.Proofs.Zipper.JointModRandom
import QuantumZipper.Proofs.Zipper.JointModDetCont
import QuantumZipper.Proofs.GFF.CoordRegRC2

/-!
# JOINTMOD, step 6: circle commutation of the continuous modification

* Deterministic part: `integral_Ddet_swap` (the smoothing symmetry `CoordReg.integral_Dfun_swap`
  of the fixed-time deterministic part, for the reverse map of the time-reversed driver).
* Random part, fixed driver: `ae_comm_fibre`. By `ae_ZE_eq_fibre` the extension `ZE` equals the
  Kolmogorov modification `Y` of `exists_contMod_ν4`; freezing the time coordinate at `t`, `Y` is
  a continuous modification of the pushed circles `pK ρ u` of `CoordReg`, so the stochastic Fubini
  theorem `CoordReg.ae_integral_Vhat_eq` and `CoordReg.pushKernel_bind_comm` give the commutation.
* Transfer to the Brownian driver (`ae_comm_ZE`): the commutation event is measurable in
  (path, field) (`measurable_integral_ZE`, Carathéodory: `ZE` is continuous in the parameter and
  measurable in (path, field)), and `CharFun.ae_indep` applies.

Sources: Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1 (the circle-average process);
stochastic Fubini and the smoothing symmetry as in `CoordReg` (own arguments there); the transfer
is the device of `RegContRandom` (**own elementary argument**).
-/

noncomputable section

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped Topology Real ENNReal NNReal

namespace QuantumZipper
namespace RegUnif

open CharFun TwoPoint UnzipInvariance RegCont KolmD RegSample CoordReg

/-! ## The deterministic part -/

theorem Ddet_eq_Dfun (κ γ : ℝ) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    Ddet κ γ W (t, (c, r)) = Dfun (vRev W t) t (2 / Real.sqrt κ) (fun _ => 0) (Qc γ) (c, r) := by
  simp only [Ddet, Dfun, integral_zero, add_zero]
  congr 2
  · show ∫ z, Real.log ‖z‖ ∂(foldedCircle c r).map (fwdMapInv W t) = _
    rw [integral_map (aemeasurable_fwdMapInv hW hW0 ht c hr)
      measurable_norm.log.aestronglyMeasurable]
    refine integral_congr_ae ?_
    filter_upwards [foldedCircle_ae_mem_H c hr] with u hu
    show Real.log ‖fwdMapInv W t u‖ = Real.log ‖revMap (vRev W t) t u‖
    rw [fwdMapInv_eq_revMap_timeRev W hW hW0 ht hu]
  · refine integral_congr_ae ?_
    filter_upwards [foldedCircle_ae_mem_H c hr] with u hu
    show Real.log ‖deriv (fwdMapInv W t) u‖ = Real.log ‖deriv (revMap (vRev W t) t) u‖
    rw [deriv_fwdMapInv_eq hW hW0 ht hu]

/-- **Smoothing symmetry of the deterministic part.** -/
theorem integral_Ddet_swap (κ γ : ℝ) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) (w : ℂ) {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) :
    ∫ u, Ddet κ γ W (t, (u, ρ)) ∂foldedCircle w r =
      ∫ v, Ddet κ γ W (t, (v, r)) ∂foldedCircle w ρ := by
  simp only [Ddet_eq_Dfun κ γ hW hW0 ht _ hρ, Ddet_eq_Dfun κ γ hW hW0 ht _ hr]
  exact integral_Dfun_swap (continuous_vRev hW t) ht _ continuous_const _ w hr hρ

/-! ## The random part for a fixed driver -/

variable {T : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

theorem update_pr (u : ℂ) (s t : ℝ) : Function.update (pr u s 0) 3 t = pr u s t := by
  funext i
  fin_cases i <;> simp [pr, Function.update_apply]

/-- For a good path, `ZE` is almost surely the Kolmogorov modification of `exists_contMod_ν4`. -/
theorem ae_ZE_eq_fibre (hX : IsFreeGFFModConstH X P) [IsProbabilityMeasure P] (hT : 0 < T)
    (κ : ℝ) {f : C(Icc (0 : ℝ) T, ℝ)} (hf : f ∈ GoodP hT.le (1 / 3)) :
    ∃ Y : (Fin 4 → ℝ) → Ω → ℝ, (∀ ω, Continuous fun q => Y q ω) ∧
      (∀ q, (fun ω => Y q ω) =ᵐ[P] fun ω => X ω (ν4 (Wof κ T hT.le f) T q)) ∧
      ∀ᵐ ω ∂P, ∀ q, ZE hT.le κ (f, X ω) q = Y q ω := by
  have hf0 := Wof_zero_of_GoodP hT.le κ hf
  obtain ⟨C, hC⟩ := hf.2
  have hWc := continuous_Wof κ T hT.le f
  obtain ⟨Y, hYc, hYeq, -⟩ := exists_contMod_ν4 hX hWc hf0 hT (a := 1 / 3) (by norm_num)
    (by norm_num) (by positivity : 0 ≤ Real.sqrt κ * C) (Wof_holder hT.le κ hC)
  have hev : ∀ q', ∀ᵐ ω ∂P, evalReg (X ω) (ν4 (Wof κ T hT.le f) T q') = Y q' ω := by
    intro q'
    obtain ⟨M, hM⟩ := exists_abs_le_on_Icc hWc T
    obtain ⟨i1, f1, b1⟩ := νT_box_facts hWc hf0 (rad_pos q') hM (tP_mem hT.le q') le_rfl le_rfl
    have h1 : ∀ᵐ x ∂ν4 (Wof κ T hT.le f) T q', x ∈ Metric.closedBall (0 : ℂ)
        (revBound (2 * M) T (‖cen q'‖ + rad q')) ∩ Hbar :=
      b1.mono fun z hz => ⟨mem_closedBall_zero_iff.2 hz.2, (show (0 : ℝ) < z.im from hz.1).le⟩
    filter_upwards [FrostmanReg.ae_evalReg_eq_frostman hX (ae_iff.1 h1) f1 (by norm_num),
      hYeq q'] with ω e1 e2
    rw [e1, e2]
  have hall : ∀ᵐ ω ∂P, ∀ (j : ℕ) (a : Fin 4 → ℤ),
      evalReg (X ω) (ν4 (Wof κ T hT.le f) T (lptD j a)) = Y (lptD j a) ω :=
    ae_all_iff.2 fun j => ae_all_iff.2 fun a => hev _
  refine ⟨Y, hYc, hYeq, ?_⟩
  filter_upwards [hall] with ω h1 q
  have hgY : ∀ (j : ℕ) (a : Fin 4 → ℤ), Gm hT.le κ (f, X ω) (lptD j a) = Y (lptD j a) ω :=
    fun j a => (Gm_eq hT.le κ _ hf0 (X ω)).trans (h1 j a)
  have hU := UCD_of_continuous (hYc ω) hgY
  simp only [ZE, hU, ↓reduceIte]
  exact extD_eq_of_continuous (hYc ω) hgY q

/-- **Commutation for a fixed good path.** -/
theorem ae_comm_fibre (hX : IsFreeGFFModConstH X P) [IsProbabilityMeasure P] (hT : 0 < T)
    (κ : ℝ) {f : C(Icc (0 : ℝ) T, ℝ)} (hf : f ∈ GoodP hT.le (1 / 3)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) {w : ℂ} (hw : w ∈ Hbar) {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) :
    ∀ᵐ ω ∂P, ∫ u, ZE hT.le κ (f, X ω) (pr u ρ t) ∂foldedCircle w r =
      ∫ v, ZE hT.le κ (f, X ω) (pr v r t) ∂foldedCircle w ρ := by
  have hf0 := Wof_zero_of_GoodP hT.le κ hf
  have hWc := continuous_Wof κ T hT.le f
  obtain ⟨Y, hYc, hYeq, hZY⟩ := ae_ZE_eq_fibre hX hT κ hf
  have hV := continuous_vRev hWc t
  set Vh : (Fin 4 → ℝ) → Ω → ℝ := fun q ω => Y (Function.update q 3 t) ω with hVh
  have hVc : ∀ ω, Continuous fun q => Vh q ω := fun ω =>
    (hYc ω).comp (continuous_id.update 3 continuous_const)
  have hVV : ∀ q, (fun ω => Vh q ω) =ᵐ[P] fun ω => X ω (pK hV ht.1 (rad q) (cen q)) := by
    intro q
    have e0 : Function.update q 3 t 0 = q 0 := Function.update_of_ne (by decide) _ _
    have e1 : Function.update q 3 t 1 = q 1 := Function.update_of_ne (by decide) _ _
    have e2 : Function.update q 3 t 2 = q 2 := Function.update_of_ne (by decide) _ _
    have e3 : Function.update q 3 t 3 = t := by simp
    have hcen : cen (Function.update q 3 t) = cen q := by unfold cen; rw [e0, e1]
    have hrad : rad (Function.update q 3 t) = rad q := by unfold rad; rw [e2]
    have htP : tP T (Function.update q 3 t) = t := by
      unfold tP; rw [e3, min_eq_left ht.2, max_eq_left ht.1]
    have hν : ν4 (Wof κ T hT.le f) T (Function.update q 3 t) = pK hV ht.1 (rad q) (cen q) := by
      simp only [ν4, hcen, hrad, htP]
      rw [νT_eq_pfc hWc hf0 ht.1 _ (rad_pos q)]
      rfl
    filter_upwards [hYeq (Function.update q 3 t)] with ω h
    simp only [hVh, h, hν]
  have hcomm := pushKernel_bind_comm (revMap (vRev (Wof κ T hT.le f) t) t)
    (TwoPoint.measurable_revMap hV ht.1) w r ρ
  filter_upwards [hZY, ae_integral_Vhat_eq hV ht.1 hX hVc hVV hw hr hρ,
    ae_integral_Vhat_eq hV ht.1 hX hVc hVV hw hρ hr] with ω hZ h1 h2
  have e : ∀ u s, ZE hT.le κ (f, X ω) (pr u s t) = Vh (pr u s 0) ω := fun u s => by
    rw [hZ, hVh]; simp only [update_pr]
  simp only [e]
  rw [h1, h2]
  exact congrArg (X ω) hcomm

/-! ## Measurability and transfer to the Brownian driver -/

theorem measurable_integral_ZE (hT : 0 ≤ T) (κ : ℝ) (w : ℂ) (s t r : ℝ) :
    Measurable fun p : C(Icc (0 : ℝ) T, ℝ) × FieldSample =>
      ∫ u, ZE hT κ p (pr u s t) ∂foldedCircle w r := by
  have hj : Measurable (Function.uncurry fun (q : Fin 4 → ℝ)
      (p : C(Icc (0 : ℝ) T, ℝ) × FieldSample) => ZE hT κ p q) :=
    measurable_uncurry_of_continuous_of_measurable (fun p => continuous_ZE hT κ p)
      (fun q => measurable_ZE hT κ q)
  have hf : Measurable fun z : (C(Icc (0 : ℝ) T, ℝ) × FieldSample) × ℂ => (pr z.2 s t, z.1) :=
    ((continuous_pr_fst s t).measurable.comp measurable_snd).prodMk measurable_fst
  have hj2 := hj.comp hf
  exact (hj2.stronglyMeasurable.integral_prod_right' (ν := foldedCircle w r)).measurable

/-- **Commutation of `ZE` for the Brownian driver.** -/
theorem ae_comm_ZE [IsProbabilityMeasure P] (κ : ℝ) {B B' : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hB'm : ∀ t, Measurable (B' t))
    (hB'c : ∀ ω, Continuous fun t => B' t ω) (hB'eq : ∀ᵐ ω ∂P, ∀ t, B' t ω = B t ω)
    (hind' : IndepFun (pathC T B' hB'c) X P) (hT : 0 < T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    {w : ℂ} (hw : w ∈ Hbar) {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) :
    ∀ᵐ ω ∂P, ∫ u, ZE hT.le κ (pathC T B' hB'c ω, X ω) (pr u ρ t) ∂foldedCircle w r =
      ∫ v, ZE hT.le κ (pathC T B' hB'c ω, X ω) (pr v r t) ∂foldedCircle w ρ := by
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  set E : Set (C(Icc (0 : ℝ) T, ℝ) × FieldSample) := ((GoodP hT.le (1 / 3))ᶜ ×ˢ univ) ∪
    {p | ∫ u, ZE hT.le κ p (pr u ρ t) ∂foldedCircle w r =
      ∫ v, ZE hT.le κ p (pr v r t) ∂foldedCircle w ρ} with hE
  have hEm : MeasurableSet E :=
    ((measurableSet_GoodP hT.le _).compl.prod MeasurableSet.univ).union
      (measurableSet_eq_fun (measurable_integral_ZE hT.le κ w ρ t r)
        (measurable_integral_ZE hT.le κ w r t ρ))
  have hfib : ∀ f, ∀ᵐ ω ∂P, (f, X ω) ∈ E := by
    intro f
    by_cases hf : f ∈ GoodP hT.le (1 / 3)
    · filter_upwards [ae_comm_fibre hX hT κ hf ht hw hr hρ] with ω h
      exact Or.inr h
    · exact ae_of_all _ fun ω => Or.inl ⟨hf, trivial⟩
  filter_upwards [ae_indep (measurable_pathC T hB'm hB'c) hXm hind' hEm hfib,
    ae_pathC_good hB hB'c hB'eq hT] with ω h hgood
  rcases h with h | h
  · exact absurd hgood h.1
  · exact h

end RegUnif
end QuantumZipper
