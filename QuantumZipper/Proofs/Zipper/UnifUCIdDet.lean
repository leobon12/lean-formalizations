import QuantumZipper.Proofs.Zipper.UnifRC3Split
import QuantumZipper.Proofs.Zipper.UnifRC3Det
import QuantumZipper.Proofs.GFF.CoordRegCompLim
import QuantumZipper.Proofs.GFF.CoordRegFwd
import QuantumZipper.Proofs.Zipper.RegContEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# UNIF-RC3-ID: the fixed-parameter identity `PhiW = X(μ) + detJ`

Task UC-ID-DET, item ID (`handoff/REG-UNIF.md`, D33). `RegUnif.IdentStmt κ T` is the identity

`∫ z, avgReg y_u j z ∂α_{u,s} = X ω (μ_{u,s,2^{-j}}) + detJ κ W d k p j`

at *fixed* parameters `p = (u, s) ∈ tri T` and fixed scale `j`, where `y_u` is the field unzipped
by `u` along the driver `W`, `α_{u,s} = (R_{u,s})_* fc(d, 2^{-k})` is the pushed circle and
`μ_{u,s,ρ} = ((ψ_u)_* α_{u,s}) ⋆ fc(·, ρ)` is its circle smoothing in free-field coordinates.

The proof is the proof of `CoordReg.ae_regShift_coordChange_revMap_gen`
(`QuantumZipper/Proofs/GFF/CoordRegCompLim.lean`), stopped before the limit `j → ∞`:

* `RC2` for the time-reversed driver `V = fun r => W (u - r) - W u`, whose reverse map
  `revMap V u` agrees with `ψ_u = fwdMapInv W u` on `ℍ` (`CoordReg.eqOn_fwdMapInv`,
  EXT_RS P3(e)), gives a witness `Vh` continuous in the parameter with
  `Vh (pr x (radius j) 0) ω = X ω (pK V u (radius j) x)` a.s.
  (`CoordReg.exists_regular_witness_revMap`);
* the raw values of `y_u` at the circles `fc(z, radius j)` are that witness plus
  `Dfun V u (2/√κ) 0 (Qc √κ)`, which is the folded-circle mean of `PsiU κ W u`
  (`Dfun_timeRev_eq_integral_PsiU`);
* stochastic Fubini at the fixed radius (`CoordReg.ae_integral_Vhat_eq_gen`) turns the `α_{u,s}`
  average of the witness into `X ω ((α_{u,s}).bind (pK V u (radius j)))`, and
  `CoordReg.bind_pK_eq` identifies that measure with `μ_{u,s,2^{-j}}`
  (the two maps agree on `ℍ`, where the underlying measure lives, `bindFc_ae_mem_H`).

Sources: Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
Prop. 3.1 and its proof (p. 18); Revuz–Yor, 3rd ed., Ch. I, Thm (2.1). Everything else is the
bookkeeping of the project's formalization (own elementary arguments).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace QuantumZipper
namespace RegUnif

open RegCont TwoPoint B2 CoordReg CircleFubini RegSample

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- `ofFun (2/√κ · log ‖·‖ + 0) = ofFun (h0rev κ)`: the deterministic background `h0rev κ` is
the `a = 2/√κ`, `g₁ = 0` case of the RC3 machinery (so that no continuity of `h0rev κ`, which
fails at `0`, is needed). -/
theorem ofFun_h0rev_of_zero (κ : ℝ) :
    ofFun (fun v : ℂ => (2 / Real.sqrt κ) * Real.log ‖v‖ + (fun _ : ℂ => (0 : ℝ)) v) =
      ofFun (h0rev κ) := by
  unfold ofFun h0rev
  funext μ
  exact integral_congr_ae (Filter.Eventually.of_forall fun z => by simp)

/-- **The deterministic part is the folded-circle mean of `PsiU`.** For the time-reversed driver
`V = fun r => W (u - r) - W u` (so that `revMap V u = fwdMapInv W u` on `ℍ`), the `Dfun` of the
RC3 machinery equals `∫ v PsiU κ W u v ∂fc(w, r)`. -/
theorem Dfun_timeRev_eq_integral_PsiU {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {u : ℝ} (hu : 0 ≤ u) (κ : ℝ) {w : ℂ} {r : ℝ} (hr : 0 < r) :
    Dfun (fun s => W (u - s) - W u) u (2 / Real.sqrt κ) (fun _ : ℂ => (0 : ℝ))
        (Qc (Real.sqrt κ)) (w, r) =
      ∫ v, PsiU κ W u v ∂foldedCircle w r := by
  have hV : Continuous fun s => W (u - s) - W u :=
    (hW.comp (continuous_const.sub continuous_id)).sub continuous_const
  have hL1 : LogBounded (fun v : ℂ => Real.log ‖revMap (fun s => W (u - s) - W u) u v‖) :=
    logBounded_log_norm_revMap (W := fun s => W (u - s) - W u) (T := u) hV hu
  have hL3 : LogBounded (fun v : ℂ => Real.log ‖deriv (revMap (fun s => W (u - s) - W u) u) v‖) :=
    logBounded_log_norm_deriv_revMap (W := fun s => W (u - s) - W u) (T := u) hV hu
  have hkey : (∫ v, PsiU κ W u v ∂foldedCircle w r) =
      ∫ v, ((2 / Real.sqrt κ) * Real.log ‖revMap (fun s => W (u - s) - W u) u v‖ +
        Qc (Real.sqrt κ) * Real.log ‖deriv (revMap (fun s => W (u - s) - W u) u) v‖) ∂
          foldedCircle w r := by
    refine integral_congr_ae ((foldedCircle_ae_mem_H w hr).mono fun v hv => ?_)
    have h1 : fwdMapInv W u v = revMap (fun s => W (u - s) - W u) u v :=
      eqOn_fwdMapInv hW hW0 hu hv
    have h2 : deriv (fwdMapInv W u) v = deriv (revMap (fun s => W (u - s) - W u) u) v :=
      Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem (isOpen_H.mem_nhds hv)
        (eqOn_fwdMapInv hW hW0 hu))
    simp only [PsiU, h0rev, h1, h2]
  rw [hkey, integral_add (((hL1.integrable w hr).const_mul _))
      ((hL3.integrable w hr).const_mul _), integral_const_mul, integral_const_mul]
  unfold Dfun
  simp only [Pi.zero_apply, integral_zero, add_zero]

/-- **The pushed folded circle is almost surely in the upper half-plane and has bounded support.**
`alphaUS W d k p = (R_{p.1,p.2})_* fc(d, 2^{-k})`. -/
theorem alphaUS_ae_mem {W : ℝ → ℝ} (hW : Continuous W) (T : ℝ) (d : ℂ) (k : ℕ)
    {p : ℝ × ℝ} (hp : p ∈ tri T) :
    ∃ R₁ : ℝ, 0 ≤ R₁ ∧ (alphaUS W d k p) (ballH R₁)ᶜ = 0 ∧
      ∀ᵐ z ∂alphaUS W d k p, z ∈ H := by
  obtain ⟨hu, hs, hus⟩ := hp
  have hT0 : 0 ≤ T := le_trans (add_nonneg hu hs) hus
  obtain ⟨M, hM⟩ := exists_abs_le_on_Icc hW T
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, hT0⟩)
  set Ra : ℝ := ‖d‖ + radius k with hRa
  have hRa0 : 0 ≤ Ra := by rw [hRa]; exact add_nonneg (norm_nonneg d) (radius_pos k).le
  set R₁ : ℝ := revBound (2 * M) p.2 Ra with hR₁
  have hR₁0 : 0 ≤ R₁ := by
    rw [hR₁]; unfold revBound
    have := abs_nonneg Ra
    linarith
  have hVc : Continuous (vrev W (p.1 + p.2)) := continuous_vrev hW _
  have hfm : Measurable (revMap (vrev W (p.1 + p.2)) p.2) := TwoPoint.measurable_revMap hVc hs
  have hsrc : ∀ᵐ z ∂foldedCircle d (radius k), z ∈ H ∧ ‖z‖ ≤ Ra := by
    filter_upwards [foldedCircle_ae_mem_H d (radius_pos k),
      foldedCircle_ae_norm_le d (radius_pos k).le] with z hz hzn
    exact ⟨hz, hzn⟩
  have himg : ∀ z : ℂ, z ∈ H → ‖z‖ ≤ Ra →
      revMap (vrev W (p.1 + p.2)) p.2 z ∈ ballH R₁ := by
    intro z hz hzn
    refine ⟨?_, (im_revMap_pos hVc hz hs).le⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine norm_revMap_le_revBound hVc hs (fun x _ => abs_vrev_le hM ⟨add_nonneg hu hs, hus⟩ x) Ra ?_
    exact hzn
  refine ⟨R₁, hR₁0, ?_, ?_⟩
  · rw [alphaUS, Measure.map_apply hfm (measurableSet_ballH R₁).compl]
    refine measure_mono_null (fun z hz => ?_) (mem_ae_iff.2 hsrc)
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_setOf_eq] at hz ⊢
    intro hzS
    exact hz (himg z hzS.1 hzS.2)
  · rw [alphaUS]
    exact (MeasureTheory.ae_map_iff hfm.aemeasurable isOpen_H.measurableSet).2
      (hsrc.mono fun z hz => im_revMap_pos hVc hz.1 hs)

/-- **A circle smoothing of any finite measure is almost surely supported in `ℍ`** (every folded
circle is). -/
theorem bindFc_ae_mem_H (ν : Measure ℂ) [IsFiniteMeasure ν] {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᵐ z ∂bindFc ν ρ, z ∈ H := by
  rw [ae_iff]
  show (ν.bind fun w => foldedCircle w ρ) {z : ℂ | z ∉ H} = 0
  rw [CircleFubini.bind_circle_apply (ν := ν) (r := ρ) (A := {z : ℂ | z ∉ H})
    isOpen_H.measurableSet.compl]
  have hz : (fun y : ℂ => foldedCircle y ρ {z : ℂ | z ∉ H}) = fun _ => 0 :=
    funext fun y => mem_ae_iff.1 (foldedCircle_ae_mem_H y hρ)
  rw [hz, lintegral_zero]

/-- **The fixed-parameter identity** (item ID of D33). -/
theorem identStmt (κ T : ℝ) : IdentStmt κ T := by
  intro Ω _ P _ X hX W hW hW0 d k p hp j
  obtain ⟨hu, hs, hus⟩ := hp
  -- the time-reversed driver `V`, whose reverse map is `ψ_u = fwdMapInv W u` on `ℍ`
  set V : ℝ → ℝ := fun r => W (p.1 - r) - W p.1 with hVdef
  have hV : Continuous V := (hW.comp (continuous_const.sub continuous_id)).sub continuous_const
  have hE : EnergyModulus V p.1 (1 / 12) := energyModulus_holds_timeRev hW hu
  obtain ⟨Vh, hVc, hVV, hreg⟩ := exists_regular_witness_revMap (W := V) (T := p.1) hV hu hX
    (by norm_num : (0 : ℝ) < 1 / 12) hE (2 / Real.sqrt κ) (g₁ := fun _ : ℂ => (0 : ℝ))
    continuous_const (Qc (Real.sqrt κ))
  -- the regular structure of the unzipped field with this witness
  have hreg' : ∀ᵐ ω ∂P, IsRegularWith
      (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, W) p.1)
      (fun q => Vh (pr q.1 q.2 0) ω + Dfun V p.1 (2 / Real.sqrt κ) (fun _ : ℂ => (0 : ℝ))
        (Qc (Real.sqrt κ)) q) := by
    filter_upwards [hreg] with ω hω
    rw [ofFun_h0rev_of_zero κ] at hω
    have h := (isRegularWith_coordChange_congr (ofFun (h0rev κ) + X ω)
      (eqOn_fwdMapInv hW hW0 hu) (Qc (Real.sqrt κ))).2 hω
    simpa only [unzippedField] using h
  -- the raw values at scale `j`
  have havg : ∀ᵐ ω ∂P, ∀ z ∈ Hbar,
      avgReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, W) p.1) j z =
        Vh (pr z (radius j) 0) ω + ∫ v, PsiU κ W p.1 v ∂foldedCircle z (radius j) := by
    filter_upwards [hreg'] with ω hω z hz
    rw [avgReg, (hω.2.1 j z hz).limUnder_eq]
    simp only [Pi.add_apply]
    rw [Dfun_timeRev_eq_integral_PsiU hW hW0 hu κ (radius_pos j)]
  -- the geometry of `alphaUS`
  obtain ⟨R₁, hR₁0, hsupp, haeH⟩ := alphaUS_ae_mem (p := p) hW T d k ⟨hu, hs, hus⟩
  haveI : IsProbabilityMeasure (alphaUS W d k p) :=
    ⟨by rw [alphaUS, Measure.map_apply (TwoPoint.measurable_revMap (continuous_vrev hW _) hs)
        MeasurableSet.univ, Set.preimage_univ]; exact measure_univ⟩
  -- stochastic Fubini at the fixed radius
  have hfub : ∀ᵐ ω ∂P, ∫ z, Vh (pr z (radius j) 0) ω ∂alphaUS W d k p =
      X ω ((alphaUS W d k p).bind (pK hV hu (radius j))) :=
    ae_integral_Vhat_eq_gen (W := V) (T := p.1) hV hu hX hVc hVV hR₁0 hsupp (radius_pos j)
  -- the `pK` measure is `muUS`
  have hbind : (alphaUS W d k p).bind (pK hV hu (radius j)) = muUS W d k p (radius j) := by
    rw [bind_pK_eq (W := V) (T := p.1) hV hu (alphaUS W d k p) (radius j)]
    unfold muUS bindFc
    refine Measure.map_congr ?_
    filter_upwards [bindFc_ae_mem_H (alphaUS W d k p) (radius_pos j)] with z hz
    exact (eqOn_fwdMapInv hW hW0 hu hz).symm
  -- integrability of the two summands against `alphaUS`
  have hL1 : LogBounded (fun v : ℂ => Real.log ‖revMap V p.1 v‖) :=
    logBounded_log_norm_revMap (W := V) (T := p.1) hV hu
  have hL3 : LogBounded (fun v : ℂ => Real.log ‖deriv (revMap V p.1) v‖) :=
    logBounded_log_norm_deriv_revMap (W := V) (T := p.1) hV hu
  have hint2 : Integrable (fun z => ∫ v, PsiU κ W p.1 v ∂foldedCircle z (radius j))
      (alphaUS W d k p) := by
    have hc1 : Continuous fun z : ℂ => ∫ v, Real.log ‖revMap V p.1 v‖ ∂foldedCircle z (radius j) :=
      hL1.continuousOn.comp_continuous (continuous_id.prodMk continuous_const)
        (fun z => radius_pos j)
    have hc3 : Continuous fun z : ℂ =>
        ∫ v, Real.log ‖deriv (revMap V p.1) v‖ ∂foldedCircle z (radius j) :=
      hL3.continuousOn.comp_continuous (continuous_id.prodMk continuous_const)
        (fun z => radius_pos j)
    have hsum : Integrable (fun z : ℂ =>
        (2 / Real.sqrt κ) * (∫ v, Real.log ‖revMap V p.1 v‖ ∂foldedCircle z (radius j)) +
        Qc (Real.sqrt κ) * (∫ v, Real.log ‖deriv (revMap V p.1) v‖ ∂foldedCircle z (radius j)))
        (alphaUS W d k p) :=
      ((integrable_of_continuous_ballH hc1 hsupp).const_mul _).add
        ((integrable_of_continuous_ballH hc3 hsupp).const_mul _)
    refine Integrable.congr (f := fun z : ℂ =>
        (2 / Real.sqrt κ) * (∫ v, Real.log ‖revMap V p.1 v‖ ∂foldedCircle z (radius j)) +
        Qc (Real.sqrt κ) * (∫ v, Real.log ‖deriv (revMap V p.1) v‖ ∂foldedCircle z (radius j)))
      hsum ?_
    refine Filter.Eventually.of_forall fun z => ?_
    show (2 / Real.sqrt κ) * (∫ v, Real.log ‖revMap V p.1 v‖ ∂foldedCircle z (radius j)) +
        Qc (Real.sqrt κ) * (∫ v, Real.log ‖deriv (revMap V p.1) v‖ ∂foldedCircle z (radius j)) =
      ∫ v, PsiU κ W p.1 v ∂foldedCircle z (radius j)
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((hL1.integrable z (radius_pos j)).const_mul (2 / Real.sqrt κ))
        ((hL3.integrable z (radius_pos j)).const_mul (Qc (Real.sqrt κ)))]
    exact integral_congr_ae ((foldedCircle_ae_mem_H z (radius_pos j)).mono fun v hv => by
      have h1 : fwdMapInv W p.1 v = revMap V p.1 v := eqOn_fwdMapInv hW hW0 hu hv
      have h2 : deriv (fwdMapInv W p.1) v = deriv (revMap V p.1) v :=
        Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem (isOpen_H.mem_nhds hv)
          (eqOn_fwdMapInv hW hW0 hu))
      simp only [PsiU, h0rev, h1, h2])
  filter_upwards [havg, hfub] with ω havgω hfubω
  have hint1 : Integrable (fun z => Vh (pr z (radius j) 0) ω) (alphaUS W d k p) :=
    integrable_of_continuous_ballH ((hVc ω).comp (continuous_pr_fst (radius j) 0)) hsupp
  have hdet : detJ κ W d k p j = ∫ z, (∫ v, PsiU κ W p.1 v ∂foldedCircle z (radius j)) ∂
      alphaUS W d k p := rfl
  rw [PhiW, hdet, integral_congr_ae
      ((haeH.mono fun z hz => havgω z (show (0 : ℝ) ≤ z.im from hz.le)) : _ =ᵐ[alphaUS W d k p] _),
    integral_add hint1 hint2, hfubω, hbind]

end RegUnif
end QuantumZipper
