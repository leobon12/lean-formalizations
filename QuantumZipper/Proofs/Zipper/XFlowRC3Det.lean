import QuantumZipper.Proofs.Zipper.XFlowRC3Raw
import QuantumZipper.Proofs.Zipper.XFlowRC3DetParam
import QuantumZipper.Proofs.Zipper.UnifRC3Det

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# X-FLOW-RC3: the deterministic input `FlowLogDerContStmt`, proved

For a continuous driver `W` with `W 0 = 0`, `p = (u, s, d, r) ↦ ∫ log|(f_u⁻¹)'| dν_p`,
`ν_p = (R_{u,s})_* fc(d, r)`, is continuous on `flowPar`. By the flow property
(`RegUnif.log_norm_deriv_R_eq`: `log|(f_u⁻¹)' ∘ R| = log|(f_{u+s}⁻¹)'| − log|R'|` on `ℍ`),

`∫ log|(f_u⁻¹)'| dν_p = ∫ log|(f_{u+s}⁻¹)'| dfc(d, r) − ∫ log|R_{u,s}'| dfc(d, r)`,

and both folded-circle means are jointly continuous in the time parameters and the circle
parameters: the integrands are jointly continuous on (times) × `ℍ`
(`RegUnif.continuousOn_log_deriv_fwdMapInv_joint`, `RegUnif.continuousOn_revMap_vrev`) and
bounded by `A + |log Im|` (`TwoPoint.abs_log_norm_deriv_revMap_le`), so
`RegUnif.continuousOn_integral_foldedCircle_param` and its two-parameter form
`continuousOn_integral_foldedCircle_param'` apply. Own elementary argument (as
`JointModDetCont.lean`, `UnifRC3Det.lean`).

Consequence: `xFlowRC3Stmt_of_regCont'` — **`XFlowRC3Stmt` follows from `XFlowRegContStmt`
alone**, and so does X-X (`xExactAll_of_regCont'`).
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology Real

namespace QuantumZipper
namespace F1

/-- Uniform `A + |log Im|` bound for `log|(revMap V t)'|`, `t ∈ [0, T']`, on `‖u‖ ≤ R`. -/
theorem abs_log_deriv_revMap_le_unif {V : ℝ → ℝ} (hV : Continuous V) {t T' R : ℝ} (ht : 0 ≤ t)
    (htT : t ≤ T') {u : ℂ} (hu : u ∈ H) (huR : ‖u‖ ≤ R) :
    |Real.log ‖deriv (revMap V t) u‖| ≤
      |Real.log (Real.sqrt (max R 1 ^ 2 + 4 * T'))| + |Real.log u.im| := by
  have hb := TwoPoint.abs_log_norm_deriv_revMap_le hV ht hu (R := max R 1)
    ((Complex.im_le_norm u).trans (huR.trans (le_max_left _ _)))
  have hR'1 : 1 ≤ max R 1 := le_max_right _ _
  have hlo : 1 ≤ Real.sqrt (max R 1 ^ 2 + 4 * t) := by
    have h1 : (1 : ℝ) ≤ max R 1 ^ 2 + 4 * t := by nlinarith
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ _ := Real.sqrt_le_sqrt h1
  have hhi : Real.sqrt (max R 1 ^ 2 + 4 * t) ≤ Real.sqrt (max R 1 ^ 2 + 4 * T') :=
    Real.sqrt_le_sqrt (by linarith)
  have hm := TwoPoint.abs_log_le_of_mem one_pos hlo hhi
  rw [Real.log_one, abs_zero, zero_add] at hm
  linarith

/-- **`FlowLogDerContStmt` holds.** -/
theorem flowLogDerContStmt_holds : FlowLogDerContStmt := by
  intro W hW hW0
  have hmeas : ∀ f : ℂ → ℂ, Measurable fun z => Real.log ‖deriv f z‖ := fun f =>
    Real.measurable_log.comp (measurable_deriv _).norm
  -- the single-map term, continuous in `(t, c, r)`
  have hI1 : ∀ T' : ℝ, 0 ≤ T' → ContinuousOn (fun q : ℝ × (ℂ × ℝ) =>
      ∫ z, Real.log ‖deriv (fwdMapInv W q.1) z‖ ∂foldedCircle q.2.1 q.2.2)
      (Icc 0 T' ×ˢ {p : ℂ × ℝ | 0 < p.2}) := by
    intro T' hT'
    refine RegUnif.continuousOn_integral_foldedCircle_param hT' (fun t _ => hmeas _)
      (RegUnif.continuousOn_log_deriv_fwdMapInv_joint hW hW0 T') fun R =>
        ⟨|Real.log (Real.sqrt (max R 1 ^ 2 + 4 * T'))|, abs_nonneg _,
          fun t ht u hu huR => ?_⟩
    rw [RegCont.deriv_fwdMapInv_eq hW hW0 ht.1 hu]
    exact abs_log_deriv_revMap_le_unif (RegCont.continuous_vRev hW t) ht.1 ht.2 hu huR
  -- the second-unzipping term, continuous in `((u, s), (c, r))`
  have hI2 : ∀ T' : ℝ, 0 ≤ T' → ContinuousOn (fun p : (ℝ × ℝ) × (ℂ × ℝ) =>
      ∫ z, Real.log ‖deriv (revMap (B2.vrev W (p.1.1 + p.1.2)) p.1.2) z‖
        ∂foldedCircle p.2.1 p.2.2)
      ((Icc 0 T' ×ˢ Icc 0 T') ×ˢ {p : ℂ × ℝ | 0 < p.2}) := by
    intro T' hT'
    have hbox : ∀ q ∈ Icc (0 : ℝ) T' ×ˢ Icc (0 : ℝ) T', q ∈ RegUnif.tri (2 * T') :=
      fun q hq => ⟨hq.1.1, hq.2.1, by linarith [hq.1.2, hq.2.2]⟩
    have hJ := RegUnif.continuousOn_log_deriv_fwdMapInv_joint hW hW0 (2 * T')
    have hRc : ContinuousOn (fun x : (ℝ × ℝ) × ℂ => revMap (B2.vrev W (x.1.1 + x.1.2)) x.1.2 x.2)
        ((Icc 0 T' ×ˢ Icc 0 T') ×ˢ H) :=
      (RegUnif.continuousOn_revMap_vrev hW (2 * T')).mono fun x hx => ⟨hbox x.1 hx.1, hx.2⟩
    have c1 : ContinuousOn (fun x : (ℝ × ℝ) × ℂ =>
        Real.log ‖deriv (fwdMapInv W (x.1.1 + x.1.2)) x.2‖) ((Icc 0 T' ×ˢ Icc 0 T') ×ˢ H) :=
      hJ.comp (f := fun x : (ℝ × ℝ) × ℂ => (x.1.1 + x.1.2, x.2)) (by fun_prop) fun x hx =>
        ⟨⟨add_nonneg hx.1.1.1 hx.1.2.1, by linarith [hx.1.1.2, hx.1.2.2]⟩, hx.2⟩
    have c2 : ContinuousOn (fun x : (ℝ × ℝ) × ℂ =>
        Real.log ‖deriv (fwdMapInv W x.1.1) (revMap (B2.vrev W (x.1.1 + x.1.2)) x.1.2 x.2)‖)
        ((Icc 0 T' ×ˢ Icc 0 T') ×ˢ H) :=
      hJ.comp (f := fun x : (ℝ × ℝ) × ℂ =>
          (x.1.1, revMap (B2.vrev W (x.1.1 + x.1.2)) x.1.2 x.2))
        ((continuous_fst.comp continuous_fst).continuousOn.prodMk hRc) fun x hx =>
          ⟨⟨hx.1.1.1, by linarith [hx.1.1.2]⟩,
            TwoPoint.im_revMap_pos (B2.continuous_vrev hW _) hx.2 hx.1.2.1⟩
    set ρ : ℝ × ℝ → ℝ × ℝ := fun q => ((projIcc 0 T' hT' q.1 : ℝ), (projIcc 0 T' hT' q.2 : ℝ))
      with hρ
    have hρc : Continuous ρ :=
      (continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst)).prodMk
        (continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd))
    have hρK : ∀ q, ρ q ∈ Icc (0 : ℝ) T' ×ˢ Icc (0 : ℝ) T' := fun q =>
      ⟨(projIcc 0 T' hT' q.1).2, (projIcc 0 T' hT' q.2).2⟩
    have hρid : ∀ q ∈ Icc (0 : ℝ) T' ×ˢ Icc (0 : ℝ) T', ρ q = q := fun q hq =>
      Prod.ext (by simp [hρ, projIcc_of_mem hT' hq.1]) (by simp [hρ, projIcc_of_mem hT' hq.2])
    have hGc : ContinuousOn (fun p : (ℝ × ℝ) × ℂ =>
        Real.log ‖deriv (revMap (B2.vrev W (p.1.1 + p.1.2)) p.1.2) p.2‖)
        ((Icc 0 T' ×ˢ Icc 0 T') ×ˢ H) :=
      (c1.sub c2).congr fun x hx => RegUnif.log_norm_deriv_R_eq hW hW0 hx.1.1.1 hx.1.2.1 hx.2
    have hGb : ∀ R, ∃ A, 0 ≤ A ∧ ∀ q ∈ Icc (0 : ℝ) T' ×ˢ Icc (0 : ℝ) T', ∀ u ∈ H, ‖u‖ ≤ R →
        |Real.log ‖deriv (revMap (B2.vrev W (q.1 + q.2)) q.2) u‖| ≤ A + |Real.log u.im| :=
      fun R => ⟨|Real.log (Real.sqrt (max R 1 ^ 2 + 4 * T'))|, abs_nonneg _,
        fun q hq u hu huR =>
          abs_log_deriv_revMap_le_unif (B2.continuous_vrev hW _) hq.2.1 hq.2.2 hu huR⟩
    exact continuousOn_integral_foldedCircle_param'
      (G := fun (q : ℝ × ℝ) (z : ℂ) => Real.log ‖deriv (revMap (B2.vrev W (q.1 + q.2)) q.2) z‖)
      hρc hρK hρid (fun q _ => hmeas (revMap (B2.vrev W (q.1 + q.2)) q.2)) hGc hGb
  -- the identity on `flowPar`
  have hid : ∀ p ∈ flowPar, (∫ z, Real.log ‖deriv (fwdMapInv W p.1) z‖ ∂flowNu W p) =
      (∫ z, Real.log ‖deriv (fwdMapInv W (p.1 + p.2.1)) z‖ ∂foldedCircle p.2.2.1 p.2.2.2) -
        ∫ z, Real.log ‖deriv (revMap (B2.vrev W (p.1 + p.2.1)) p.2.1) z‖
          ∂foldedCircle p.2.2.1 p.2.2.2 := by
    rintro ⟨u, s, d, r⟩ ⟨hu, hs, -, hr⟩
    simp only at hu hs hr ⊢
    have hV := B2.continuous_vrev hW (u + s)
    have hRm := TwoPoint.measurable_revMap hV hs
    have hus : 0 ≤ u + s := add_nonneg hu hs
    have hb1 : Integrable (fun z => Real.log ‖deriv (fwdMapInv W (u + s)) z‖)
        (foldedCircle d r) :=
      TwoPoint.integrable_of_log_bound (hmeas _) (R := ‖d‖ + r) (fun z hz hzR => by
        rw [RegCont.deriv_fwdMapInv_eq hW hW0 hus hz]
        exact abs_log_deriv_revMap_le_unif (RegCont.continuous_vRev hW _) hus le_rfl hz hzR)
        d hr le_rfl
    have hb2 : Integrable (fun z => Real.log ‖deriv (revMap (B2.vrev W (u + s)) s) z‖)
        (foldedCircle d r) :=
      TwoPoint.integrable_of_log_bound (hmeas _) (R := ‖d‖ + r) (fun z hz hzR =>
        abs_log_deriv_revMap_le_unif hV hs le_rfl hz hzR) d hr le_rfl
    unfold flowNu
    simp only
    rw [integral_map hRm.aemeasurable (hmeas _).aestronglyMeasurable, ← integral_sub hb1 hb2]
    refine integral_congr_ae ((TwoPoint.foldedCircle_ae_mem_H d hr).mono fun z hz => ?_)
    simp only
    rw [RegUnif.log_norm_deriv_R_eq hW hW0 hu hs hz]
    ring
  -- local continuity
  intro p0 hp0
  set T' := p0.1 + p0.2.1 + 1 with hT'def
  have hT' : 0 ≤ T' := by linarith [hp0.1, hp0.2.1]
  set S : Set (ℝ × ℝ × ℂ × ℝ) :=
    {p | p.1 ∈ Icc 0 T' ∧ p.2.1 ∈ Icc 0 T' ∧ p.2.2.1 ∈ Hbar ∧ 0 < p.2.2.2} with hSdef
  have hS : S ⊆ flowPar := fun p hp => ⟨hp.1.1, hp.2.1.1, hp.2.2.1, hp.2.2.2⟩
  have hcS : ContinuousOn (fun p : ℝ × ℝ × ℂ × ℝ =>
      (∫ z, Real.log ‖deriv (fwdMapInv W (p.1 + p.2.1)) z‖ ∂foldedCircle p.2.2.1 p.2.2.2) -
        ∫ z, Real.log ‖deriv (revMap (B2.vrev W (p.1 + p.2.1)) p.2.1) z‖
          ∂foldedCircle p.2.2.1 p.2.2.2) S :=
    ((hI1 (2 * T') (by linarith)).comp
      (f := fun p : ℝ × ℝ × ℂ × ℝ => (p.1 + p.2.1, p.2.2.1, p.2.2.2)) (by fun_prop)
      fun p hp => ⟨⟨add_nonneg hp.1.1 hp.2.1.1, by linarith [hp.1.2, hp.2.1.2]⟩, hp.2.2.2⟩).sub
    ((hI2 T' hT').comp
      (f := fun p : ℝ × ℝ × ℂ × ℝ => ((p.1, p.2.1), (p.2.2.1, p.2.2.2))) (by fun_prop)
      fun p hp => ⟨⟨hp.1, hp.2.1⟩, hp.2.2.2⟩)
  have hfS := hcS.congr fun p hp => hid p (hS hp)
  have hp0S : p0 ∈ S :=
    ⟨⟨hp0.1, by linarith [hp0.2.1]⟩, ⟨hp0.2.1, by linarith [hp0.1]⟩, hp0.2.2.1, hp0.2.2.2⟩
  have hmem : S ∈ 𝓝[flowPar] p0 := by
    refine mem_nhdsWithin.2 ⟨{p : ℝ × ℝ × ℂ × ℝ | p.1 < T' ∧ p.2.1 < T'},
      (isOpen_lt continuous_fst continuous_const).inter
        (isOpen_lt (continuous_fst.comp continuous_snd) continuous_const),
      ⟨by linarith [hp0.2.1], by linarith [hp0.1]⟩, fun p hp => ?_⟩
    exact ⟨⟨hp.2.1, hp.1.1.le⟩, ⟨hp.2.2.1, hp.1.2.le⟩, hp.2.2.2.1, hp.2.2.2.2⟩
  exact (hfS p0 hp0S).mono_of_mem_nhdsWithin hmem

/-- **`XFlowRC3Stmt` from the regularized-side continuity alone.** -/
theorem xFlowRC3Stmt_of_regCont' (hR : XFlowRegContStmt) : XFlowRC3Stmt :=
  xFlowRC3Stmt_of_regCont hR flowLogDerContStmt_holds

/-- **X-X from the regularized-side continuity alone.** -/
theorem xExactAll_of_regCont' (hR : XFlowRegContStmt) : WedgeUnzip.XExactAllStmt :=
  xExactAll_of_regCont hR flowLogDerContStmt_holds

end F1
end QuantumZipper
