import QuantumZipper.Proofs.LQG.CoordChangeAreaZoom
import QuantumZipper.Proofs.GFF.CoordRegSwap
import QuantumZipper.Proofs.Section5.Prop16ShiftGoodBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Coordinate change of the area measure: RC3 at interior circles (COORD-CHANGE, D98)

First step towards the dilation clause of `Prop16Lit.Prop16LitCovStmt` (the canonical
description (1.8) of the chart field rescales it by the random canonical scale, which reads the
coordinate-changed field `y ∘ ψ + Q log|ψ'|` at circles of non-dyadic radius). For a regular
sample `y` whose pushed circle averages `E(u, α) = ⟨y, ψ_* fc(u, α 2^{-k})⟩` converge uniformly
(dyadic smoothing) and are continuous in `(u, α)` on a rectangle (the finite-parameter primed
core, `SWCore.swcNA2I_primed`, Duplantier–Sheffield 2011 Prop. 3.1), the regularized value of
the coordinate change at an interior folded circle is its raw value:
`evalReg (y ∘ ψ + Q log|ψ'|) (fc(w, ρ)) = (y ∘ ψ + Q log|ψ'|)(fc(w, ρ))`
(`CoordChangeArea.evalReg_coordChange_fc`). Proof: the smoothing symmetry
`∫ E(u, r) dfc(w, ρ) = ∫ E(v, ρ) dfc(w, r)` (commutation of folded-circle convolutions,
`CoordReg.foldedCircle_bind_comm`, passed to the limit through the uniform convergence) and the
continuity of `E(·, ρ)`. Own bookkeeping (as `Thm18Asm.G1RC.rc_of_raw`).
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace CoordChangeArea

open SWCore GoodSample G1Side

/-- **Smoothing symmetry for a bounded continuous integrand.** -/
theorem integral_fc_swap {g : ℂ → ℝ} (hg : Continuous g) {M : ℝ} (hM : ∀ z, |g z| ≤ M)
    (w : ℂ) (r ρ : ℝ) :
    ∫ u, (∫ x, g x ∂foldedCircle u ρ) ∂foldedCircle w r =
      ∫ v, (∫ x, g x ∂foldedCircle v r) ∂foldedCircle w ρ := by
  have hint : ∀ (a b : ℝ), Integrable g ((foldedCircle w a).bind fun u => foldedCircle u b) := by
    intro a b
    haveI := CircleFubini.isFiniteMeasure_bind_circle (r := b) (foldedCircle w a)
    exact Integrable.of_bound hg.aestronglyMeasurable M (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs]; exact hM z)
  rw [← (CircleFubini.integral_bind_circle (foldedCircle w r) (hint r ρ)).2,
    ← (CircleFubini.integral_bind_circle (foldedCircle w ρ) (hint ρ r)).2,
    CoordReg.foldedCircle_bind_comm]

/-- Uniform convergence on a carrier passes to the integrals against a probability measure. -/
theorem tendsto_integral_of_tendstoUniformlyOn {f : ℕ → ℂ → ℝ} {f₀ : ℂ → ℝ} {S : Set ℂ}
    (hU : TendstoUniformlyOn f f₀ atTop S) {ν : Measure ℂ} [IsProbabilityMeasure ν]
    (hν : ∀ᵐ u ∂ν, u ∈ S) (hi : ∀ᶠ j in atTop, Integrable (f j) ν) (hi₀ : Integrable f₀ ν) :
    Tendsto (fun j => ∫ u, f j u ∂ν) atTop (𝓝 (∫ u, f₀ u ∂ν)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hU' := Metric.tendstoUniformlyOn_iff.1 hU (ε / 2) (half_pos hε)
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hU'.and hi)
  refine ⟨J, fun j hj => ?_⟩
  obtain ⟨hj1, hj2⟩ := hJ j hj
  rw [Real.dist_eq, ← integral_sub hj2 hi₀]
  calc |∫ u, (f j u - f₀ u) ∂ν| = ‖∫ u, (f j u - f₀ u) ∂ν‖ := (Real.norm_eq_abs _).symm
    _ ≤ ε / 2 := by
        refine norm_integral_le_of_norm_le_const ?_ |>.trans (by rw [probReal_univ, mul_one])
        filter_upwards [hν] with u hu
        rw [Real.norm_eq_abs, abs_sub_comm, ← Real.dist_eq]
        exact (hj1 u hu).le
    _ < ε := half_lt_self hε

/-- A continuous bounded function agreeing with a given one on a compact set. -/
theorem exists_bounded_extension {φ : ℂ → ℝ} {K : Set ℂ} (hK : IsCompact K)
    (hφ : ContinuousOn φ K) : ∃ g : ℂ → ℝ, Continuous g ∧ EqOn g φ K ∧ ∃ M, ∀ z, |g z| ≤ M := by
  obtain ⟨g, hgc, hgφ⟩ := exists_continuous_extension hK.isClosed hφ
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hφ
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  refine ⟨fun z => max (-(max M 0)) (min (max M 0) (g z)), by fun_prop, fun z hz => ?_,
    max M 0, fun z => ?_⟩
  · have h1 := hM z hz
    rw [Real.norm_eq_abs] at h1
    obtain ⟨h2, h3⟩ := abs_le.1 h1
    simp only [hgφ hz]
    rw [min_eq_right (by linarith [le_max_left M 0]), max_eq_right (by linarith [le_max_left M 0])]
  · rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

set_option maxHeartbeats 800000 in
/-- **Smoothing symmetry of the pushed averages.** -/
theorem integral_pushed_swap {y : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith y F)
    {ψ : ℂ → ℂ} (hψm : Measurable ψ) (hψc : ContinuousOn ψ H) (hψH : MapsTo ψ H H)
    {w : ℂ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hK : closedBall w (a + b) ⊆ H)
    (hUb : TendstoUniformlyOn (fun j u => ∫ v, avgReg y j v ∂((foldedCircle u b).map ψ))
      (fun u => evalReg y ((foldedCircle u b).map ψ)) atTop (closedBall w a))
    (hCb : ContinuousOn (fun u => evalReg y ((foldedCircle u b).map ψ)) (closedBall w a))
    (hUa : TendstoUniformlyOn (fun j u => ∫ v, avgReg y j v ∂((foldedCircle u a).map ψ))
      (fun u => evalReg y ((foldedCircle u a).map ψ)) atTop (closedBall w b))
    (hCa : ContinuousOn (fun u => evalReg y ((foldedCircle u a).map ψ)) (closedBall w b)) :
    ∫ u, evalReg y ((foldedCircle u b).map ψ) ∂foldedCircle w a =
      ∫ v, evalReg y ((foldedCircle v a).map ψ) ∂foldedCircle w b := by
  set K₃ := closedBall w (a + b) with hK₃def
  have hK₃ : IsCompact K₃ := isCompact_closedBall _ _
  have hwH : w ∈ Hbar := H_subset_Hbar (hK (mem_closedBall_self (by linarith)))
  have hgi : ∀ i : ℕ, ∃ g : ℂ → ℝ, Continuous g ∧ EqOn g (fun t => F (ψ t, radius i)) K₃ ∧
      ∃ M, ∀ z, |g z| ≤ M := fun i =>
    exists_bounded_extension hK₃ ((hF.1.comp ((hψc.mono hK).prodMk continuousOn_const)
      fun t ht => ⟨H_subset_Hbar (hψH (hK ht)), radius_pos i⟩))
  choose g hgc hgeq M hM using hgi
  have hinner : ∀ (i : ℕ) (u : ℂ) (r : ℝ), 0 < r → u ∈ Hbar → closedBall u r ⊆ K₃ →
      ∫ v, avgReg y i v ∂((foldedCircle u r).map ψ) = ∫ t, g i t ∂foldedCircle u r := by
    intro i u r hr hu hsub
    have hm : Measurable fun v => avgReg y i v :=
      (measurable_avgReg i).comp (measurable_const.prodMk measurable_id)
    rw [integral_map hψm.aemeasurable hm.aestronglyMeasurable]
    refine integral_congr_ae ((G1Side.ae_fc_mem_closedBall hu hr.le).mono fun t ht => ?_)
    show avgReg y i (ψ t) = g i t
    rw [hF.avgReg_eq i (H_subset_Hbar (hψH (hK (hsub ht))))]
    exact (hgeq i (hsub ht)).symm
  have hbd : ∀ (i : ℕ) (r : ℝ) (u : ℂ), |∫ t, g i t ∂foldedCircle u r| ≤ M i := by
    intro i r u
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ t, |g i t| ∂foldedCircle u r ≤ ∫ _, M i ∂foldedCircle u r :=
          integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
            (integrable_const _) (ae_of_all _ fun t => hM i t)
      _ = M i := by rw [integral_const, probReal_univ, one_smul]
  have hsub : ∀ {c d : ℝ}, 0 ≤ c → 0 ≤ d → c + d ≤ a + b → ∀ u ∈ closedBall w c,
      closedBall u d ⊆ K₃ := by
    intro c d hc hd hcd u hu t ht
    refine mem_closedBall.2 ((dist_triangle t u w).trans ?_)
    linarith [mem_closedBall.1 ht, mem_closedBall.1 hu]
  have hlim : ∀ {c d : ℝ}, 0 < c → 0 < d → c + d ≤ a + b →
      TendstoUniformlyOn (fun j u => ∫ v, avgReg y j v ∂((foldedCircle u d).map ψ))
        (fun u => evalReg y ((foldedCircle u d).map ψ)) atTop (closedBall w c) →
      ContinuousOn (fun u => evalReg y ((foldedCircle u d).map ψ)) (closedBall w c) →
      Tendsto (fun i => ∫ u, (∫ t, g i t ∂foldedCircle u d) ∂foldedCircle w c) atTop
        (𝓝 (∫ u, evalReg y ((foldedCircle u d).map ψ) ∂foldedCircle w c)) := by
    intro c d hc hd hcd hU hC
    have hfc : ∀ᵐ u ∂foldedCircle w c, u ∈ closedBall w c :=
      G1Side.ae_fc_mem_closedBall hwH hc.le
    have h := tendsto_integral_of_tendstoUniformlyOn hU hfc
      (Eventually.of_forall fun i => (Integrable.of_bound (continuous_smoothFun
        (hgc i).continuousOn d).aestronglyMeasurable (M i) (ae_of_all _ fun u => by
          rw [Real.norm_eq_abs]; exact hbd i d u)).congr (hfc.mono fun u hu =>
            (hinner i u d hd (H_subset_Hbar (hK (hsub hc.le hd.le hcd u hu
              (mem_closedBall_self hd.le)))) (hsub hc.le hd.le hcd u hu)).symm))
      (integrable_of_continuousOn_carrier (isCompact_closedBall _ _) hC hfc)
    refine h.congr fun i => integral_congr_ae (hfc.mono fun u hu => ?_)
    exact hinner i u d hd (H_subset_Hbar (hK (hsub hc.le hd.le hcd u hu
      (mem_closedBall_self hd.le)))) (hsub hc.le hd.le hcd u hu)
  have hA := hlim ha hb le_rfl hUb hCb
  have hB := hlim hb ha (by linarith) hUa hCa
  have hAB : ∀ i, ∫ u, (∫ t, g i t ∂foldedCircle u b) ∂foldedCircle w a =
      ∫ v, (∫ t, g i t ∂foldedCircle v a) ∂foldedCircle w b := fun i =>
    integral_fc_swap (hgc i) (hM i) w a b
  simp_rw [hAB] at hA
  exact tendsto_nhds_unique hA hB

/-- The pushed circle average `u ↦ ⟨y, ψ_* fc(u, r)⟩`. -/
def pushE (y : FieldSample) (ψ : ℂ → ℂ) (r : ℝ) (u : ℂ) : ℝ :=
  evalReg y ((foldedCircle u r).map ψ)

set_option maxHeartbeats 1600000 in
/-- **RC3 at interior circles for the coordinate change** (deterministic). -/
theorem evalReg_coordChange_fc {y : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith y F)
    {ψ : ℂ → ℂ} (hψm : Measurable ψ) (hψd : DifferentiableOn ℂ ψ H)
    (hψ0 : ∀ z ∈ H, deriv ψ z ≠ 0) (hψH : MapsTo ψ H H) {R : Set ℂ} (hRH : R ⊆ H) {k₀ : ℕ}
    (hU : ∀ k ≥ k₀, TendstoUniformlyOn (fun j (p : ℂ × ℝ) =>
        ∫ u, avgReg y j u ∂((foldedCircle p.1 (p.2 * radius k)).map ψ))
      (fun p => evalReg y ((foldedCircle p.1 (p.2 * radius k)).map ψ)) atTop (R ×ˢ Icc 1 2))
    (hC : ∀ k ≥ k₀, ContinuousOn (fun p : ℂ × ℝ =>
      evalReg y ((foldedCircle p.1 (p.2 * radius k)).map ψ)) (R ×ˢ Icc 1 2))
    (Q : ℝ) {w : ℂ} {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) (hwR : closedBall w (ρ + δ) ⊆ R)
    {k₁ : ℕ} (hk₁ : k₀ ≤ k₁) {α₀ : ℝ} (hα₀ : α₀ ∈ Icc (1 : ℝ) 2) (hρk : ρ = α₀ * radius k₁) :
    evalReg (coordChange y ψ Q) (foldedCircle w ρ) = coordChange y ψ Q (foldedCircle w ρ) := by
  have hψc : ContinuousOn ψ H := hψd.continuousOn
  have hK₃H : closedBall w (ρ + δ) ⊆ H := hwR.trans hRH
  have hwH : w ∈ Hbar := H_subset_Hbar (hK₃H (mem_closedBall_self (by linarith)))
  have hρK : closedBall w ρ ⊆ closedBall w (ρ + δ) := closedBall_subset_closedBall (by linarith)
  have hg1 : ∀ u ∈ R, ((u, (1 : ℝ)) : ℂ × ℝ) ∈ R ×ˢ Icc (1 : ℝ) 2 :=
    fun u hu => ⟨hu, by norm_num, by norm_num⟩
  have hgα : ∀ u ∈ R, ((u, α₀) : ℂ × ℝ) ∈ R ×ˢ Icc (1 : ℝ) 2 := fun u hu => ⟨hu, hα₀⟩
  have hE1 : ∀ k ≥ k₀, ContinuousOn (pushE y ψ (radius k)) R := fun k hk =>
    ((hC k hk).comp (continuousOn_id.prodMk continuousOn_const) hg1).congr fun u _ => by
      show evalReg y _ = evalReg y _
      rw [one_mul]
      rfl
  have hU1 : ∀ k ≥ k₀, TendstoUniformlyOn (fun j u =>
      ∫ v, avgReg y j v ∂((foldedCircle u (radius k)).map ψ)) (pushE y ψ (radius k)) atTop R := by
    intro k hk
    have h := ((hU k hk).comp fun u : ℂ => ((u, (1 : ℝ)) : ℂ × ℝ)).mono fun u hu => hg1 u hu
    have e1 : (fun j u => ∫ v, avgReg y j v ∂((foldedCircle u (radius k)).map ψ)) =
        fun j => (fun p : ℂ × ℝ => ∫ v, avgReg y j v ∂((foldedCircle p.1 (p.2 * radius k)).map ψ)) ∘
          fun u : ℂ => ((u, (1 : ℝ)) : ℂ × ℝ) := by
      funext j u; simp only [Function.comp_apply, one_mul]
    have e2 : pushE y ψ (radius k) =
        (fun p : ℂ × ℝ => evalReg y ((foldedCircle p.1 (p.2 * radius k)).map ψ)) ∘
          fun u : ℂ => ((u, (1 : ℝ)) : ℂ × ℝ) := by
      funext u; simp only [pushE, Function.comp_apply, one_mul]
    rw [e1, e2]; exact h
  have hEρc : ContinuousOn (pushE y ψ ρ) R := by
    have h := (hC k₁ hk₁).comp (continuousOn_id.prodMk continuousOn_const) hgα
    rw [hρk]; exact h
  have hUρ : TendstoUniformlyOn (fun j u =>
      ∫ v, avgReg y j v ∂((foldedCircle u ρ).map ψ)) (pushE y ψ ρ) atTop R := by
    have h := ((hU k₁ hk₁).comp fun u : ℂ => ((u, α₀) : ℂ × ℝ)).mono fun u hu => hgα u hu
    rw [hρk]; exact h
  have hlog : ContinuousOn (fun u => Real.log ‖deriv ψ u‖) H := fun u hu => by
    have hA : AnalyticOnNhd ℂ ψ H := hψd.analyticOnNhd isOpen_H
    exact ((hA.deriv u hu).continuousAt.norm.log (norm_ne_zero_iff.2 (hψ0 u hu))).continuousWithinAt
  have hfcρ : ∀ᵐ u ∂foldedCircle w ρ, u ∈ closedBall w ρ :=
    G1Side.ae_fc_mem_closedBall hwH hρ.le
  have hlogi : Integrable (fun u => Real.log ‖deriv ψ u‖) (foldedCircle w ρ) :=
    integrable_of_continuousOn_carrier (isCompact_closedBall _ _)
      (hlog.mono (hρK.trans hK₃H)) hfcρ
  have hsym : ∀ j : ℕ, k₀ ≤ j → radius j ≤ δ →
      ∫ u, pushE y ψ (radius j) u ∂foldedCircle w ρ =
        ∫ v, pushE y ψ ρ v ∂foldedCircle w (radius j) := by
    intro j hj hjδ
    have hjK : closedBall w (radius j) ⊆ closedBall w (ρ + δ) :=
      closedBall_subset_closedBall (by linarith)
    exact integral_pushed_swap hF hψm hψc hψH hρ (radius_pos j)
      ((closedBall_subset_closedBall (by linarith)).trans hK₃H)
      ((hU1 j hj).mono (hρK.trans hwR)) ((hE1 j hj).mono (hρK.trans hwR))
      (hUρ.mono (hjK.trans hwR)) (hEρc.mono (hjK.trans hwR))
  have havg : ∀ j : ℕ, k₀ ≤ j → 2 * radius j ≤ δ → ∀ u ∈ closedBall w ρ,
      avgReg (coordChange y ψ Q) j u = pushE y ψ (radius j) u + Q * Real.log ‖deriv ψ u‖ := by
    intro j hj hjδ u hu
    refine avgReg_coordChange_eq_push hψd hψ0 hRH Q (hE1 j hj) fun v hv => hwR ?_
    refine mem_closedBall.2 ((dist_triangle v u w).trans ?_)
    linarith [mem_closedBall.1 hv, mem_closedBall.1 hu]
  have hrad : ∀ᶠ j in atTop, k₀ ≤ j ∧ 2 * radius j ≤ δ :=
    (eventually_ge_atTop k₀).and ((RegClosure.tendsto_radius_nhdsGT.mono_right
      nhdsWithin_le_nhds).eventually (ge_mem_nhds (by linarith : (0 : ℝ) < δ / 2)) |>.mono
      fun k hk => by linarith)
  have hev : ∀ᶠ j in atTop, ∫ u, avgReg (coordChange y ψ Q) j u ∂foldedCircle w ρ =
      ∫ v, pushE y ψ ρ v ∂foldedCircle w (radius j) +
        Q * ∫ u, Real.log ‖deriv ψ u‖ ∂foldedCircle w ρ := by
    filter_upwards [hrad] with j hj
    have hEi : Integrable (pushE y ψ (radius j)) (foldedCircle w ρ) :=
      integrable_of_continuousOn_carrier (isCompact_closedBall _ _)
        ((hE1 j hj.1).mono (hρK.trans hwR)) hfcρ
    rw [integral_congr_ae (hfcρ.mono fun u hu => havg j hj.1 hj.2 u hu),
      integral_add hEi (hlogi.const_mul Q), integral_const_mul,
      hsym j hj.1 (by linarith [radius_pos j])]
  have hlim : Tendsto (fun j => ∫ v, pushE y ψ ρ v ∂foldedCircle w (radius j)) atTop
      (𝓝 (pushE y ψ ρ w)) := by
    have hnhds : R ∈ 𝓝 w := Filter.mem_of_superset (ball_mem_nhds w (by linarith))
      (ball_subset_closedBall.trans hwR)
    exact Prop16Asm.tendsto_integral_foldedCircle_radius hδ
      ((hEρc.mono ((closedBall_subset_closedBall (by linarith)).trans hwR)).mono
        inter_subset_left) hwH (hEρc.continuousAt hnhds)
  have hT : coordChange y ψ Q (foldedCircle w ρ) =
      pushE y ψ ρ w + Q * ∫ u, Real.log ‖deriv ψ u‖ ∂foldedCircle w ρ := rfl
  rw [hT]
  unfold evalReg
  exact ((hlim.add_const _).congr' (hev.mono fun j hj => hj.symm)).limUnder_eq

/-- The parameter of the constant family at the centre `p.1` and radius factor `p.2`. -/
def qdα (p : ℂ × ℝ) : Fin 5 → ℝ := ![0, 0, p.1.re, p.1.im, p.2]

theorem continuous_qdα : Continuous qdα := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [qdα] <;> fun_prop

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- **Uniform regularity of the pushed averages in centre and radius factor** (free field). -/
theorem ae_pushed_regular_alpha [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {ψ : ℂ → ℂ} {x₁ x₂ y₁ y₂ ρ M m : ℝ} (hx : x₁ ≤ x₂) (hy0 : 0 < y₁) (hy : y₁ ≤ y₂)
    (hρ : 0 < ρ) (hm : 0 < m) (hψ : ψ ∈ AreaClass x₁ x₂ y₁ y₂ ρ M m) :
    ∃ k₀ : ℕ, ∀ᵐ ω ∂P, ∀ k ≥ k₀,
      TendstoUniformlyOn (fun j (p : ℂ × ℝ) =>
          ∫ u, avgReg (X ω) j u ∂((foldedCircle p.1 (p.2 * radius k)).map ψ))
        (fun p => evalReg (X ω) ((foldedCircle p.1 (p.2 * radius k)).map ψ)) atTop
        (rectC x₁ x₂ y₁ y₂ ×ˢ Icc 1 2) ∧
      ContinuousOn (fun p : ℂ × ℝ => evalReg (X ω) ((foldedCircle p.1 (p.2 * radius k)).map ψ))
        (rectC x₁ x₂ y₁ y₂ ×ˢ Icc 1 2) := by
  obtain ⟨k₀, hae⟩ := swcNA2I_primed hX (constFam_unif hx hy0 hy hρ hm hψ)
  refine ⟨k₀, ?_⟩
  filter_upwards [hae] with ω hω k hk
  obtain ⟨hU, hC, -⟩ := hω
  obtain ⟨j, rfl⟩ : ∃ j, k = j + k₀ := ⟨k - k₀, by omega⟩
  set S := rectC x₁ x₂ y₁ y₂ ×ˢ Icc (1 : ℝ) 2 with hSdef
  have hS : IsCompact S := (SWCore.isCompact_rectC _ _ _ _).prod isCompact_Icc
  have hcen : ∀ p ∈ S, a7Cen x₁ x₂ y₁ y₂ (qdα p) = p.1 := fun p hp => by
    apply Complex.ext
    · simp [qdα, a7Cen, clampI_eq hp.1.1]
    · simp [qdα, a7Cen, clampI_eq hp.1.2]
  have hrad : ∀ p ∈ S, a7Rad (qdα p) = p.2 := fun p hp => by
    simp [qdα, a7Rad, clampI_eq hp.2]
  refine ⟨?_, ?_⟩
  · have h := ((hU j (qdα '' S) (hS.image continuous_qdα)).comp qdα).mono
      (fun p hp => mem_image_of_mem qdα hp)
    refine (h.congr ?_).congr_right ?_
    · exact Eventually.of_forall fun i p hp => by
        simp only [Function.comp_apply, hcen p hp, hrad p hp]
    · exact fun p hp => by simp only [Function.comp_apply, hcen p hp, hrad p hp]
  · exact ((hC j).comp continuous_qdα).continuousOn.congr fun p hp => by
      simp only [Function.comp_apply, hcen p hp, hrad p hp]

end CoordChangeArea
end QuantumZipper
