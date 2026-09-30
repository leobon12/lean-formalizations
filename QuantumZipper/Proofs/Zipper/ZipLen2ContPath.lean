import QuantumZipper.Proofs.Zipper.ZipLen2ContDefs
import QuantumZipper.Proofs.Zipper.XFlowRC3Phi

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZIPLEN-2 continuum: pathwise joint continuity of `Φ^c`

A.s., `(p, ρ) ↦ Φ^c(p, ρ) = ∫ evalReg y_u (fc(z, ρ)) dν_p(z)` is continuous on
`flowPar × (0, ∞)`. The integrand is the joint regularity witness `Z(u, (z, ρ))`
(`RegUnif.ae_exists_joint_witness`, `IsRegularWith.evalReg_fc_of_mem`), and the parametric
continuity is `F1.continuousOn_integral_foldedCircle_param'` with the smoothing radius added to
the parameter. The pattern is `F1.xFlowPhiContStmt_holds` (XFlowRC3Phi.lean). Own bookkeeping.
-/

noncomputable section

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped Topology Real NNReal ENNReal

namespace QuantumZipper
namespace B3d
namespace ZipLen

open F1 RegCont TwoPoint RegUnif

/-- Measurability of `z ↦ evalReg x (fc(z, ρ))`. -/
theorem measurable_evalReg_fc (x : FieldSample) (ρ : ℝ) :
    Measurable fun z : ℂ => evalReg x (foldedCircle z ρ) := by
  unfold evalReg
  exact (StronglyMeasurable.limUnder fun k =>
    ((measurable_integral_foldedCircle (α := Unit)
      (G := fun q : Unit × ℂ => avgReg x k q.2)
      ((RegClosure.measurable_avgReg_slice _ k).comp measurable_snd) ρ).comp
      ((measurable_const : Measurable fun _ : ℂ => ()).prodMk measurable_id)
      ).stronglyMeasurable).measurable

/-- **Pathwise joint continuity of the continuous-radius `Γ⁰` pairings.** -/
theorem ae_flowPhiYc_joint {κ : ℝ} (hκ : 0 < κ) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, ContinuousOn (fun x : (ℝ × ℝ × ℂ × ℝ) × ℝ =>
      flowPhiYc κ (X ω) (drive κ B ω) x.2 x.1) (flowPar ×ˢ Ioi 0) := by
  classical
  have hwit : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ Z : ℝ × (ℂ × ℝ) → ℝ, ContinuousOn Z (parSet ((n : ℝ) + 1)) ∧
      ∀ t ∈ Icc 0 ((n : ℝ) + 1), IsRegularWith
        (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) t) (fun p => Z (t, p)) :=
    ae_all_iff.2 fun n => ae_exists_joint_witness (κ := κ) (γ := Real.sqrt κ) hB hX hind
      (by positivity)
  filter_upwards [hwit, hB.cont, hB.eval_zero_ae_eq_zero] with ω hZ hc h0
  set W := drive κ B ω with hWdef
  have hW : Continuous W := by
    rw [hWdef]; unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hW0 : W 0 = 0 := by simp [hWdef, drive, h0]
  rintro ⟨p0, ρ0⟩ ⟨hp0, hρ0⟩
  have hρ0' : (0 : ℝ) < ρ0 := hρ0
  set T' := p0.1 + p0.2.1 + 1 with hT'def
  have hT' : 0 ≤ T' := by linarith [hp0.1, hp0.2.1]
  set N := ⌈2 * T'⌉₊ with hN
  set TT : ℝ := (N : ℝ) + 1 with hTT
  have h2T : 2 * T' ≤ TT := by linarith [Nat.le_ceil (2 * T')]
  have hTT0 : 0 ≤ TT := by linarith
  obtain ⟨Z, hZc, hZr⟩ := hZ N
  set a : ℝ := ρ0 / 2 with ha
  set b : ℝ := 2 * ρ0 with hb
  have ha0 : 0 < a := by positivity
  have hab : a ≤ b := by linarith
  -- the parameter box and its retraction
  set K : Set ((ℝ × ℝ) × ℝ) := (Icc 0 T' ×ˢ Icc 0 T') ×ˢ Icc a b with hK
  have hKtri : ∀ q ∈ K, q.1 ∈ tri TT := fun q hq =>
    ⟨hq.1.1.1, hq.1.2.1, by linarith [hq.1.1.2, hq.1.2.2]⟩
  set rt : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ := fun q =>
    (((projIcc 0 T' hT' q.1.1 : ℝ), (projIcc 0 T' hT' q.1.2 : ℝ)), (projIcc a b hab q.2 : ℝ))
    with hrt
  have hrtc : Continuous rt :=
    ((continuous_subtype_val.comp (continuous_projIcc.comp (continuous_fst.comp continuous_fst))).prodMk
      (continuous_subtype_val.comp (continuous_projIcc.comp (continuous_snd.comp continuous_fst)))).prodMk
      (continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd))
  have hrtK : ∀ q, rt q ∈ K := fun q =>
    ⟨⟨(projIcc 0 T' hT' q.1.1).2, (projIcc 0 T' hT' q.1.2).2⟩, (projIcc a b hab q.2).2⟩
  have hrtid : ∀ q ∈ K, rt q = q := fun q hq =>
    Prod.ext (Prod.ext (by simp [hrt, projIcc_of_mem hT' hq.1.1])
      (by simp [hrt, projIcc_of_mem hT' hq.1.2])) (by simp [hrt, projIcc_of_mem hab hq.2])
  -- the integrand
  set G : (ℝ × ℝ) × ℝ → ℂ → ℝ := fun q => H.piecewise
    (fun z => Z (q.1.1, (revMap (B2.vrev W (q.1.1 + q.1.2)) q.1.2 z, q.2))) (fun _ => 0) with hG
  have hRin : ∀ q ∈ K, ∀ z ∈ H,
      (q.1.1, (revMap (B2.vrev W (q.1.1 + q.1.2)) q.1.2 z, q.2)) ∈ parSet TT :=
    fun q hq z hz => ⟨⟨hq.1.1.1, by linarith [hq.1.1.2]⟩,
      (im_revMap_pos (B2.continuous_vrev hW _) hz hq.1.2.1).le,
      show (0 : ℝ) < q.2 from lt_of_lt_of_le ha0 hq.2.1⟩
  have hGm : ∀ q ∈ K, Measurable (G q) := by
    intro q hq
    refine ContinuousOn.measurable_piecewise ?_ continuousOn_const isOpen_H.measurableSet
    exact hZc.comp (f := fun z => (q.1.1, (revMap (B2.vrev W (q.1.1 + q.1.2)) q.1.2 z, q.2)))
      (continuousOn_const.prodMk
        ((QuantumZipper.differentiableOn_revMap _ (B2.continuous_vrev hW _)
          hq.1.2.1).continuousOn.prodMk continuousOn_const))
      fun z hz => hRin q hq z hz
  have hGc : ContinuousOn (fun x : ((ℝ × ℝ) × ℝ) × ℂ => G x.1 x.2) (K ×ˢ H) := by
    have hRc : ContinuousOn (fun x : ((ℝ × ℝ) × ℝ) × ℂ =>
        revMap (B2.vrev W (x.1.1.1 + x.1.1.2)) x.1.1.2 x.2) (K ×ˢ H) :=
      (continuousOn_revMap_vrev hW TT).comp (f := fun x : ((ℝ × ℝ) × ℝ) × ℂ => (x.1.1, x.2))
        (by fun_prop) fun x hx => ⟨hKtri x.1 hx.1, hx.2⟩
    refine (hZc.comp (f := fun x : ((ℝ × ℝ) × ℝ) × ℂ =>
        (x.1.1.1, (revMap (B2.vrev W (x.1.1.1 + x.1.1.2)) x.1.1.2 x.2, x.1.2)))
      ((continuous_fst.comp (continuous_fst.comp continuous_fst)).continuousOn.prodMk
        (hRc.prodMk (continuous_snd.comp continuous_fst).continuousOn))
      fun x hx => hRin x.1 hx.1 x.2 hx.2).congr fun x hx => ?_
    show H.piecewise _ _ x.2 = _
    rw [Set.piecewise_eq_of_mem _ _ _ hx.2]
    rfl
  have hGb : ∀ R, ∃ A, 0 ≤ A ∧ ∀ q ∈ K, ∀ u ∈ H, ‖u‖ ≤ R →
      |G q u| ≤ A + |Real.log u.im| := by
    intro R
    obtain ⟨M, hM⟩ := exists_abs_le_on_Icc hW TT
    set Rb := revBound (2 * M) TT R with hRb
    have hKc : IsCompact (Icc (0 : ℝ) TT ×ˢ ((Metric.closedBall (0 : ℂ) Rb ∩ Hbar) ×ˢ Icc a b)) :=
      isCompact_Icc.prod (((isCompact_closedBall _ _).inter_right isClosed_Hbar).prod
        isCompact_Icc)
    obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn
      (hZc.mono fun x hx => ⟨hx.1, hx.2.1.2, show (0 : ℝ) < x.2.2 from lt_of_lt_of_le ha0 hx.2.2.1⟩)
    refine ⟨max C 0, le_max_right _ _, fun q hq u hu huR => ?_⟩
    have hV := B2.continuous_vrev hW (q.1.1 + q.1.2)
    have hqT : q.1.1 + q.1.2 ∈ Icc (0 : ℝ) TT :=
      ⟨add_nonneg hq.1.1.1 hq.1.2.1, by linarith [hq.1.1.2, hq.1.2.2]⟩
    have hbd : ‖revMap (B2.vrev W (q.1.1 + q.1.2)) q.1.2 u‖ ≤ revBound (2 * M) q.1.2 R :=
      norm_revMap_le_revBound hV hq.1.2.1 (fun x _ => abs_vrev_le hM hqT x) _ huR
    have hmono : revBound (2 * M) q.1.2 R ≤ Rb := by
      rw [hRb]; unfold revBound; linarith [hq.1.2.2]
    have hmem : (q.1.1, (revMap (B2.vrev W (q.1.1 + q.1.2)) q.1.2 u, q.2)) ∈
        Icc (0 : ℝ) TT ×ˢ ((Metric.closedBall (0 : ℂ) Rb ∩ Hbar) ×ˢ Icc a b) :=
      ⟨(hRin q hq u hu).1, ⟨mem_closedBall_zero_iff.2 (hbd.trans hmono), (hRin q hq u hu).2.1⟩,
        hq.2⟩
    have h1 := hC _ hmem
    have hGq : G q u = Z (q.1.1, (revMap (B2.vrev W (q.1.1 + q.1.2)) q.1.2 u, q.2)) := by
      show H.piecewise _ _ u = _
      rw [Set.piecewise_eq_of_mem _ _ _ hu]
    rw [hGq]
    rw [Real.norm_eq_abs] at h1
    linarith [le_max_left C 0, abs_nonneg (Real.log u.im)]
  have hcont := continuousOn_integral_foldedCircle_param' hrtc hrtK hrtid hGm hGc hGb
  -- the identity on the box part
  set S : Set ((ℝ × ℝ × ℂ × ℝ) × ℝ) :=
    {x | x.1.1 ∈ Icc 0 T' ∧ x.1.2.1 ∈ Icc 0 T' ∧ x.1.2.2.1 ∈ Hbar ∧ 0 < x.1.2.2.2 ∧
      x.2 ∈ Icc a b} with hSdef
  have hid : ∀ x ∈ S, flowPhiYc κ (X ω) W x.2 x.1 =
      ∫ z, G ((x.1.1, x.1.2.1), x.2) z ∂foldedCircle x.1.2.2.1 x.1.2.2.2 := by
    rintro ⟨⟨u, s, d, r⟩, ρ⟩ ⟨hu, hs, -, hr, hρ⟩
    simp only at hu hs hr hρ ⊢
    have hV := B2.continuous_vrev hW (u + s)
    have hRm := measurable_revMap hV hs.1
    unfold flowPhiYc flowNu
    simp only
    rw [integral_map hRm.aemeasurable (measurable_evalReg_fc _ ρ).aestronglyMeasurable]
    refine integral_congr_ae ((foldedCircle_ae_mem_H d hr).mono fun z hz => ?_)
    have hq : (((u, s), ρ) : (ℝ × ℝ) × ℝ) ∈ K := ⟨⟨hu, hs⟩, hρ⟩
    have huT : u ∈ Icc (0 : ℝ) ((N : ℝ) + 1) := ⟨hu.1, by linarith [hu.2]⟩
    have hRz := hRin _ hq z hz
    have hGz : G ((u, s), ρ) z = Z (u, (revMap (B2.vrev W (u + s)) s z, ρ)) :=
      Set.piecewise_eq_of_mem _ _ _ hz
    rw [hGz]
    exact (hZr u huT).evalReg_fc_of_mem hRz.2.1 hRz.2.2
  have hcS : ContinuousOn (fun x : (ℝ × ℝ × ℂ × ℝ) × ℝ =>
      ∫ z, G ((x.1.1, x.1.2.1), x.2) z ∂foldedCircle x.1.2.2.1 x.1.2.2.2) S :=
    hcont.comp (f := fun x : (ℝ × ℝ × ℂ × ℝ) × ℝ =>
        (((x.1.1, x.1.2.1), x.2), (x.1.2.2.1, x.1.2.2.2)))
      (by fun_prop) fun x hx => ⟨⟨⟨hx.1, hx.2.1⟩, hx.2.2.2.2⟩, hx.2.2.2.1⟩
  have hfS := hcS.congr fun x hx => hid x hx
  have hx0S : ((p0, ρ0) : (ℝ × ℝ × ℂ × ℝ) × ℝ) ∈ S :=
    ⟨⟨hp0.1, by linarith [hp0.2.1]⟩, ⟨hp0.2.1, by linarith [hp0.1]⟩, hp0.2.2.1, hp0.2.2.2,
      ⟨by linarith, by linarith⟩⟩
  have hmem : S ∈ 𝓝[flowPar ×ˢ Ioi 0] (p0, ρ0) := by
    refine mem_nhdsWithin.2 ⟨{x : (ℝ × ℝ × ℂ × ℝ) × ℝ | x.1.1 < T' ∧ x.1.2.1 < T' ∧
        a < x.2 ∧ x.2 < b},
      ((isOpen_lt (continuous_fst.comp continuous_fst) continuous_const).inter
        ((isOpen_lt ((continuous_fst.comp continuous_snd).comp continuous_fst)
          continuous_const).inter
        ((isOpen_lt continuous_const continuous_snd).inter
          (isOpen_lt continuous_snd continuous_const)))),
      ⟨by linarith [hp0.2.1], by linarith [hp0.1], by linarith, by linarith⟩, fun x hx => ?_⟩
    exact ⟨⟨hx.2.1.1, hx.1.1.le⟩, ⟨hx.2.1.2.1, hx.1.2.1.le⟩, hx.2.1.2.2.1, hx.2.1.2.2.2,
      ⟨hx.1.2.2.1.le, hx.1.2.2.2.le⟩⟩
  exact (hfS _ hx0S).mono_of_mem_nhdsWithin hmem

end ZipLen
end B3d
end QuantumZipper
