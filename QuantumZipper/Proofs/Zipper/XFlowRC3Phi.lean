import QuantumZipper.Proofs.Zipper.XFlowRC3PhiBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# X-FLOW-RC3: `XFlowPhiContStmt` proved; the flow node from the five-parameter UC node alone

A.s., every `Φ_j(p) = ∫ avgReg x_u j dν_p` is continuous on `flowPar`:

* on one full event, for every horizon `N + 1`, the `Γ⁰` JointMod witness `Z` of the unzipped
  `y = 𝔥₀ + X` (`RegUnif.ae_exists_joint_witness`) and the regularity of `y` along the unzipped
  dyadic circles (`RegUnif.gaugeRegDyStmt_holds`) give
  `avgReg x_u j w = Z(u, w, 2^{-j}) − √κ ∫ log|f_u⁻¹| dfc(w, 2^{-j})` (`avgReg_unzX_eq`), a
  function `Zx(u, w)` jointly continuous on `[0, N+1] × ℍ̄`
  (`continuousOn_integral_log_fwdMapInv_joint`);
* `Φ_j(p) = ∫ Zx(u, R_{u,s} z) dfc(d, r)(z)`, and the folded-circle means of the bounded
  integrand `(u, s, z) ↦ Zx(u, R_{u,s} z)` (jointly continuous on `[0,T']² × ℍ`,
  `RegUnif.continuousOn_revMap_vrev`; the images stay in a compact part of `ℍ̄`,
  `RegCont.norm_revMap_le_revBound`) are jointly continuous in `(u, s, d, r)`
  (`continuousOn_integral_foldedCircle_param'`).

Own elementary bookkeeping (as `UnifRC3Det.continuousOn_integral_comp_R`, with the circle
parameters added). Consequences: `xFlowRC3Stmt_of_flowUC : XFlowUCStmt → XFlowRC3Stmt` and
`xExactAll_of_flowUC : XFlowUCStmt → WedgeUnzip.XExactAllStmt`.
-/

noncomputable section

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped Topology Real NNReal ENNReal

namespace QuantumZipper
namespace F1

open RegCont TwoPoint RegUnif

/-- **`XFlowPhiContStmt` holds.** -/
theorem xFlowPhiContStmt_holds : XFlowPhiContStmt := by
  classical
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind
  have hwit : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ Z : ℝ × (ℂ × ℝ) → ℝ, ContinuousOn Z (parSet ((n : ℝ) + 1)) ∧
      ∀ t ∈ Icc 0 ((n : ℝ) + 1), IsRegularWith
        (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) t) (fun p => Z (t, p)) :=
    ae_all_iff.2 fun n => ae_exists_joint_witness (κ := κ) (γ := Real.sqrt κ) hB hX hind
      (by positivity)
  have hreg : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ s ∈ Icc (0 : ℝ) ((n : ℝ) + 1),
      (∀ k : ℕ, ∀ d ∈ Dy, E1.RegShift (B2.cfg κ B X ω).1
        ((foldedCircle d (radius k)).map (fwdMapInv (drive κ B ω) s))) ∧
        Cor15Group.BdryConvAE (B2.h0f κ s B X ω) :=
    ae_all_iff.2 fun n => gaugeRegDyStmt_holds hB hX hind (by positivity)
  filter_upwards [hwit, hreg, hB.cont, hB.eval_zero_ae_eq_zero] with ω hZ hRg hc h0 j
  set W := drive κ B ω with hWdef
  have hW : Continuous W := by
    rw [hWdef]; unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hW0 : W 0 = 0 := by simp [hWdef, drive, h0]
  intro p0 hp0
  set T' := p0.1 + p0.2.1 + 1 with hT'def
  have hT' : 0 ≤ T' := by linarith [hp0.1, hp0.2.1]
  set N := ⌈2 * T'⌉₊ with hN
  set TT : ℝ := (N : ℝ) + 1 with hTT
  have h2T : 2 * T' ≤ TT := by linarith [Nat.le_ceil (2 * T')]
  have hTT0 : 0 ≤ TT := by linarith
  obtain ⟨Z, hZc, hZr⟩ := hZ N
  set Zx : ℝ → ℂ → ℝ := fun t w => Z (t, (w, radius j)) +
    -Real.sqrt κ * ∫ u, Real.log ‖fwdMapInv W t u‖ ∂foldedCircle w (radius j) with hZx
  have hZxc : ContinuousOn (fun q : ℝ × ℂ => Zx q.1 q.2) (Icc 0 TT ×ˢ Hbar) := by
    have c1 : ContinuousOn (fun q : ℝ × ℂ => Z (q.1, (q.2, radius j))) (Icc 0 TT ×ˢ Hbar) :=
      hZc.comp (f := fun q : ℝ × ℂ => (q.1, (q.2, radius j))) (by fun_prop)
        fun q hq => ⟨hq.1, hq.2, radius_pos j⟩
    have c2 : ContinuousOn (fun q : ℝ × ℂ =>
        ∫ u, Real.log ‖fwdMapInv W q.1 u‖ ∂foldedCircle q.2 (radius j)) (Icc 0 TT ×ˢ Hbar) :=
      (continuousOn_integral_log_fwdMapInv_joint hW hW0 hTT0).comp
        (f := fun q : ℝ × ℂ => (q.1, (q.2, radius j))) (by fun_prop)
        fun q hq => ⟨hq.1, show (0 : ℝ) < radius j from radius_pos j⟩
    exact c1.add (continuousOn_const.mul c2)
  -- the box and its retraction
  set K : Set (ℝ × ℝ) := Icc 0 T' ×ˢ Icc 0 T' with hK
  have hKtri : ∀ q ∈ K, q ∈ tri TT := fun q hq =>
    ⟨hq.1.1, hq.2.1, by linarith [hq.1.2, hq.2.2]⟩
  set ρ : ℝ × ℝ → ℝ × ℝ := fun q => ((projIcc 0 T' hT' q.1 : ℝ), (projIcc 0 T' hT' q.2 : ℝ))
    with hρ
  have hρc : Continuous ρ :=
    (continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst)).prodMk
      (continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd))
  have hρK : ∀ q, ρ q ∈ K := fun q => ⟨(projIcc 0 T' hT' q.1).2, (projIcc 0 T' hT' q.2).2⟩
  have hρid : ∀ q ∈ K, ρ q = q := fun q hq =>
    Prod.ext (by simp [hρ, projIcc_of_mem hT' hq.1]) (by simp [hρ, projIcc_of_mem hT' hq.2])
  -- the integrand
  set G : ℝ × ℝ → ℂ → ℝ := fun q => H.piecewise
    (fun z => Zx q.1 (revMap (B2.vrev W (q.1 + q.2)) q.2 z)) (fun _ => 0) with hG
  have hRin : ∀ q ∈ K, ∀ z ∈ H, (q.1, revMap (B2.vrev W (q.1 + q.2)) q.2 z) ∈ Icc 0 TT ×ˢ Hbar :=
    fun q hq z hz => ⟨⟨hq.1.1, by linarith [hq.1.2]⟩,
      (im_revMap_pos (B2.continuous_vrev hW _) hz hq.2.1).le⟩
  have hGm : ∀ q ∈ K, Measurable (G q) := by
    intro q hq
    refine ContinuousOn.measurable_piecewise ?_ continuousOn_const isOpen_H.measurableSet
    exact hZxc.comp (f := fun z => (q.1, revMap (B2.vrev W (q.1 + q.2)) q.2 z))
      (continuousOn_const.prodMk
        (QuantumZipper.differentiableOn_revMap _ (B2.continuous_vrev hW _) hq.2.1).continuousOn)
      fun z hz => hRin q hq z hz
  have hGc : ContinuousOn (fun x : (ℝ × ℝ) × ℂ => G x.1 x.2) (K ×ˢ H) := by
    have hRc : ContinuousOn (fun x : (ℝ × ℝ) × ℂ =>
        revMap (B2.vrev W (x.1.1 + x.1.2)) x.1.2 x.2) (K ×ˢ H) :=
      (continuousOn_revMap_vrev hW TT).mono fun x hx => ⟨hKtri x.1 hx.1, hx.2⟩
    refine (hZxc.comp (f := fun x : (ℝ × ℝ) × ℂ =>
        (x.1.1, revMap (B2.vrev W (x.1.1 + x.1.2)) x.1.2 x.2))
      ((continuous_fst.comp continuous_fst).continuousOn.prodMk hRc)
      fun x hx => hRin x.1 hx.1 x.2 hx.2).congr fun x hx => ?_
    show H.piecewise _ _ x.2 = _
    rw [Set.piecewise_eq_of_mem _ _ _ hx.2]
    rfl
  have hGb : ∀ R, ∃ A, 0 ≤ A ∧ ∀ q ∈ K, ∀ u ∈ H, ‖u‖ ≤ R →
      |G q u| ≤ A + |Real.log u.im| := by
    intro R
    obtain ⟨M, hM⟩ := exists_abs_le_on_Icc hW TT
    set Rb := revBound (2 * M) TT R with hRb
    have hKc : IsCompact (Icc (0 : ℝ) TT ×ˢ (Metric.closedBall (0 : ℂ) Rb ∩ Hbar)) :=
      isCompact_Icc.prod ((isCompact_closedBall _ _).inter_right isClosed_Hbar)
    obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn
      (hZxc.mono fun x hx => ⟨hx.1, hx.2.2⟩)
    refine ⟨max C 0, le_max_right _ _, fun q hq u hu huR => ?_⟩
    have hV := B2.continuous_vrev hW (q.1 + q.2)
    have hqT : q.1 + q.2 ∈ Icc (0 : ℝ) TT :=
      ⟨add_nonneg hq.1.1 hq.2.1, by linarith [hq.1.2, hq.2.2]⟩
    have hb : ‖revMap (B2.vrev W (q.1 + q.2)) q.2 u‖ ≤ revBound (2 * M) q.2 R :=
      norm_revMap_le_revBound hV hq.2.1 (fun x _ => abs_vrev_le hM hqT x) _ huR
    have hmono : revBound (2 * M) q.2 R ≤ Rb := by
      rw [hRb]; unfold revBound; linarith [hq.2.2]
    have hmem : (q.1, revMap (B2.vrev W (q.1 + q.2)) q.2 u) ∈
        Icc (0 : ℝ) TT ×ˢ (Metric.closedBall (0 : ℂ) Rb ∩ Hbar) :=
      ⟨(hRin q hq u hu).1, mem_closedBall_zero_iff.2 (hb.trans hmono), (hRin q hq u hu).2⟩
    have h1 := hC _ hmem
    have hGq : G q u = Zx q.1 (revMap (B2.vrev W (q.1 + q.2)) q.2 u) := by
      show H.piecewise _ _ u = _
      rw [Set.piecewise_eq_of_mem _ _ _ hu]
    rw [hGq]
    rw [Real.norm_eq_abs] at h1
    linarith [le_max_left C 0, abs_nonneg (Real.log u.im)]
  have hcont := continuousOn_integral_foldedCircle_param' hρc hρK hρid hGm hGc hGb
  -- the identity on the box part of `flowPar`
  set S : Set (ℝ × ℝ × ℂ × ℝ) :=
    {p | p.1 ∈ Icc 0 T' ∧ p.2.1 ∈ Icc 0 T' ∧ p.2.2.1 ∈ Hbar ∧ 0 < p.2.2.2} with hSdef
  have hid : ∀ p ∈ S, flowPhi κ (X ω) W j p =
      ∫ z, G (p.1, p.2.1) z ∂foldedCircle p.2.2.1 p.2.2.2 := by
    rintro ⟨u, s, d, r⟩ ⟨hu, hs, -, hr⟩
    simp only at hu hs hr ⊢
    have hV := B2.continuous_vrev hW (u + s)
    have hRm := measurable_revMap hV hs.1
    unfold flowPhi flowNu
    simp only
    rw [integral_map hRm.aemeasurable
      (CoordRegComp.measurable_avgReg_right _ j).aestronglyMeasurable]
    refine integral_congr_ae ((foldedCircle_ae_mem_H d hr).mono fun z hz => ?_)
    have hq : ((u, s) : ℝ × ℝ) ∈ K := ⟨hu, hs⟩
    have huT : u ∈ Icc (0 : ℝ) TT := ⟨hu.1, by linarith [hu.2]⟩
    have hRz := hRin (u, s) hq z hz
    have hGz : G (u, s) z = Zx u (revMap (B2.vrev W (u + s)) s z) :=
      Set.piecewise_eq_of_mem _ _ _ hz
    rw [hGz]
    exact avgReg_unzX_eq κ hW hW0 hu.1 (hRg N u huT).1 (hZr u huT) j hRz.2
  have hcS : ContinuousOn (fun p : ℝ × ℝ × ℂ × ℝ =>
      ∫ z, G (p.1, p.2.1) z ∂foldedCircle p.2.2.1 p.2.2.2) S :=
    hcont.comp (f := fun p : ℝ × ℝ × ℂ × ℝ => ((p.1, p.2.1), (p.2.2.1, p.2.2.2)))
      (by fun_prop) fun p hp => ⟨⟨hp.1, hp.2.1⟩, hp.2.2.2⟩
  have hfS := hcS.congr fun p hp => hid p hp
  have hp0S : p0 ∈ S :=
    ⟨⟨hp0.1, by linarith [hp0.2.1]⟩, ⟨hp0.2.1, by linarith [hp0.1]⟩, hp0.2.2.1, hp0.2.2.2⟩
  have hmem : S ∈ 𝓝[flowPar] p0 := by
    refine mem_nhdsWithin.2 ⟨{p : ℝ × ℝ × ℂ × ℝ | p.1 < T' ∧ p.2.1 < T'},
      (isOpen_lt continuous_fst continuous_const).inter
        (isOpen_lt (continuous_fst.comp continuous_snd) continuous_const),
      ⟨by linarith [hp0.2.1], by linarith [hp0.1]⟩, fun p hp => ?_⟩
    exact ⟨⟨hp.2.1, hp.1.1.le⟩, ⟨hp.2.2.1, hp.1.2.le⟩, hp.2.2.2.1, hp.2.2.2.2⟩
  exact (hfS p0 hp0S).mono_of_mem_nhdsWithin hmem

/-- **`XFlowRC3Stmt` from the five-parameter uniform-convergence node alone.** -/
theorem xFlowRC3Stmt_of_flowUC (hU : XFlowUCStmt) : XFlowRC3Stmt :=
  xFlowRC3Stmt_of_uc xFlowPhiContStmt_holds hU

/-- **X-X from the five-parameter uniform-convergence node alone.** -/
theorem xExactAll_of_flowUC (hU : XFlowUCStmt) : WedgeUnzip.XExactAllStmt :=
  xExactAll_of_uc xFlowPhiContStmt_holds hU

end F1
end QuantumZipper
