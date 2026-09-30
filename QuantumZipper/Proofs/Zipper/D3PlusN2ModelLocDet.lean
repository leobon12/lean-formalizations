import QuantumZipper.Proofs.Zipper.D3PlusN2TmZWedge
import QuantumZipper.Proofs.Section5.Prop16D4WRescale
import QuantumZipper.Proofs.Zipper.WedgeAddConstReDet
import QuantumZipper.Proofs.Zipper.F1B4dPath

/-!
# N2-zero, node N2Z-MODELLOC: the deterministic window transfer on the model side

Task N2-MODELLOC. For a local model field `y = locModel γ L r p` embedded at scale `a > 0`
(`W = rescale y Q a`, `a K ≤ r`), on the window event `resField K W ∈ n2Good γ K R`:

  `TmRichN1 γ r R L p = gK γ K R (resField K W)`,

provided (deterministic hypotheses, to be supplied almost surely for the model):

* `y` is locally good on `halfDisc r` (`Prop16Area.G.IsLocallyGoodOn`): gives the local area
  measure of `W` on `a⁻¹ halfDisc r ⊇ halfDisc K` and the rescaling rule for the local scale
  (`Prop16Asm.scaleParamOn_rescale_of_locallyGood`);
* `y` agrees near `0` (radius `r`) with a regular sample `y'` (witness `F`), and the continuum
  radius limits of the test pairings `t ↦ ∫ F(c u, t) f(u) du` exist (`f = ±ρ`, `ρ` supported in
  `closedBall 0 R`, all `c > 0`): this is what makes the double rescaling
  `rescale (rescale y' Q a) Q b` agree with `rescale y' Q (a b)` on the test pairings
  (`F1.rescale_rescale_eq_of_lim`).

Steps (`n2_modelLoc_det`): the window scale `scaleSur` equals `scaleParamOn W (halfDisc K)`,
equals `scaleParamOn W (a⁻¹ halfDisc r)` (the window scale is `< K`, and the two local measures
agree below `K`), equals `scaleParamOn y (halfDisc r) / a` (local rescaling rule); then the rich
data of both sides are those of `rescale y' Q s`, `s = scaleParamOn y (halfDisc r)`, by locality
(`locFieldFull_rescale_congr`) and the composition of rescalings.

Source: Duplantier–Miller–Sheffield arXiv:1409.7055, proof of Prop. 4.8 (p. 79: the surfaces
agree in `B(0,R)` after the embedding); Sheffield arXiv:1012.4797 (1.8)/p. 25 (the canonical
description does not depend on the embedding). The Lean steps are own elementary arguments on top
of the project's locality and rescaling tools.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace D3Plus

open Prop16Area.G GoodSample RegClosure LocalRule

theorem halfDisc_subset_preimage_mul {a r : ℝ} (ha : 0 < a) {K : ℝ} (hKa : a * K ≤ r) :
    halfDisc K ⊆ (fun z => (a : ℂ) * z) ⁻¹' halfDisc r := by
  intro z hz
  obtain ⟨h1, h2⟩ := hz
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right] at h1 ⊢
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le]
    nlinarith
  · show 0 < ((a : ℂ) * z).im
    rw [Complex.im_ofReal_mul]
    exact mul_pos ha h2

/-- With a local area measure on the window, the window data determine the scale surrogate. -/
theorem scaleSur_res_eq_on {γ : ℝ} {y : FieldSample} {K : ℕ} {m : Measure ℂ}
    (hy : IsVagueLimitOn (halfDisc K) (areaApprox γ y) m) :
    scaleSur γ 0 K (resField K y, 0) = scaleParamOn γ y (halfDisc K) := by
  have hag := agreeNear_locModel_res γ K y
  have hgood : (resField K y, (0 : FieldSample)) ∈ goodN1 γ 0 K :=
    ⟨_, isVagueLimitOn_halfDisc_of_agree hag hy⟩
  rw [scaleSur_eq hgood, ← scaleParamOn_halfDisc_congr hag]

/-- A window scale `< K` is the scale on any larger open domain carrying a local area measure. -/
theorem scaleParamOn_eq_window {γ : ℝ} {y : FieldSample} {U : Set ℂ} (hU : IsOpen U) {K : ℕ}
    (hsub : halfDisc K ⊆ U) {m : Measure ℂ} (hm : IsVagueLimitOn U (areaApprox γ y) m)
    (h0 : 0 < scaleParamOn γ y (halfDisc K)) (hlt : scaleParamOn γ y (halfDisc K) < K) :
    scaleParamOn γ y U = scaleParamOn γ y (halfDisc K) := by
  have e1 : qAreaMeasureOn γ y U = m := qAreaMeasureOn_eq hU hm
  have e2 : qAreaMeasureOn γ y (halfDisc K) = m.restrict (halfDisc K) :=
    qAreaMeasureOn_eq (isOpen_halfDisc K) (D3Plus.isVagueLimitOn_restrict (isOpen_halfDisc K) hsub hm)
  have hag : ∀ b : ℝ, b < K → qAreaMeasureOn γ y (halfDisc K) (Metric.ball 0 b ∩ H) =
      qAreaMeasureOn γ y U (Metric.ball 0 b ∩ H) := by
    intro b hb
    have hs : Metric.ball (0 : ℂ) b ∩ H ⊆ halfDisc K :=
      fun z hz => ⟨Metric.ball_subset_ball hb.le hz.1, hz.2⟩
    rw [e1, e2, Measure.restrict_apply (Metric.isOpen_ball.inter isOpen_H).measurableSet,
      inter_eq_left.2 hs]
  unfold scaleParamOn at h0 hlt ⊢
  refine sInf_eq_of_agree_below (ε := K) (fun a ha => ha.1) (fun a ha => ha.1)
    (fun a ha => ?_) ?_ hlt
  · simp only [mem_ofPred_eq, hag a ha]
  · by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, Real.sInf_empty] at h0
    exact lt_irrefl _ h0

/-- **Scale transfer**: the window scale of the embedded field is the model's local scale over
the embedding scale. -/
theorem n2_scale_transfer {γ : ℝ} (hγ : 0 < γ) {r a : ℝ} (ha : 0 < a) {K : ℕ}
    (hKa : a * K ≤ r) {y : FieldSample} (hloc : IsLocallyGoodOn γ (halfDisc r) y)
    (h0 : 0 < scaleSur γ 0 K (resField K (rescale y (Qc γ) a), 0))
    (hlt : scaleSur γ 0 K (resField K (rescale y (Qc γ) a), 0) < K) :
    scaleSur γ 0 K (resField K (rescale y (Qc γ) a), 0) = scaleParamOn γ y (halfDisc r) / a := by
  have hU := isOpen_halfDisc r
  have hUH := halfDisc_subset_H r
  set U' := (fun z => (a : ℂ) * z) ⁻¹' halfDisc r with hU'def
  have hmul : Continuous fun z : ℂ => (a : ℂ) * z := continuous_const.mul continuous_id
  have hU' : IsOpen U' := hU.preimage hmul
  have hsub : halfDisc K ⊆ U' := halfDisc_subset_preimage_mul ha hKa
  obtain ⟨m, hm⟩ : ∃ m, IsVagueLimitOn U' (areaApprox γ (rescale y (Qc γ) a)) m := by
    obtain ⟨W, hWo, hWV, y0, ψ, hy0, hψ, h⟩ := hloc
    have hUW : halfDisc r ⊆ W := fun z hz => by
      rw [← hWV] at hz
      exact hz.1
    rw [← hWV] at hψ
    set W' := (fun z => (a : ℂ) * z) ⁻¹' W
    have hW' : IsOpen W' := hWo.preimage hmul
    have hU'H : U' ⊆ H := fun z hz => by
      have h1 : (0 : ℝ) < ((a : ℂ) * z).im := hUH hz
      rw [Complex.im_ofReal_mul] at h1
      exact pos_of_mul_pos_right h1 ha.le
    have hU'W : U' ⊆ W' := fun z hz => hUW hz
    have hψ' : ContinuousOn (fun u => ψ ((a : ℂ) * u)) (W' ∩ Hbar) :=
      hψ.comp hmul.continuousOn fun u hu => ⟨hu.1, mapsTo_mul_pos ha hu.2⟩
    have hag : CircAgree W' (rescale y (Qc γ) a)
        (rescale y0 (Qc γ) a + ofFun fun u => ψ ((a : ℂ) * u)) :=
      ((fcAgree_rescale hWo h (Qc γ) ha).trans
        (fcAgree_rescale_add_ofFun hy0.1 hWo hψ (Qc γ) ha)).circAgree
    exact exists_limit_of_agree hW' (hy0.rescale hγ ha) hψ' hag hU' hU'H hU'W
  have hmK := D3Plus.isVagueLimitOn_restrict (isOpen_halfDisc K) hsub hm
  rw [scaleSur_res_eq_on hmK] at h0 hlt ⊢
  rw [← Prop16Asm.scaleParamOn_rescale_of_locallyGood hγ hloc hU hUH subset_rfl ha]
  exact (scaleParamOn_eq_window hU' hsub hm h0 hlt).symm

/-- **Composition of rescalings on the rich local data** of a regular sample, given the continuum
radius limits of the test pairings at the composed scale. -/
theorem locFieldFull_rescale_rescale {y : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith y F)
    (Q : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (R : ℕ)
    (hlim : ∀ ρ : TestFun H, suppIn R ρ → ∀ f ∈ ({ρ.1, -ρ.1} : Set (ℂ → ℝ)), ∃ L : ℝ,
      Tendsto (fun t => ∫ u, F (((a * b : ℝ) : ℂ) * u, t)
        ∂(volume.withDensity fun z => ENNReal.ofReal (f z))) (𝓝[>] 0) (𝓝 L)) :
    locFieldFull R (rescale (rescale y Q a) Q b) = locFieldFull R (rescale y Q (a * b)) := by
  classical
  have hdens : ∀ {f : ℂ → ℝ}, Continuous f → HasCompactSupport f → tsupport f ⊆ H →
      (∃ L : ℝ, Tendsto (fun t => ∫ u, F (((a * b : ℝ) : ℂ) * u, t)
        ∂(volume.withDensity fun z => ENNReal.ofReal (f z))) (𝓝[>] 0) (𝓝 L)) →
      rescale (rescale y Q a) Q b (volume.withDensity fun z => ENNReal.ofReal (f z)) =
        rescale y Q (a * b) (volume.withDensity fun z => ENNReal.ofReal (f z)) := by
    intro f hfc hfs hfH hL
    obtain ⟨L, hL⟩ := hL
    obtain ⟨hfin, hae⟩ := F1.B4d.withDensity_facts hfc hfs
    exact F1.rescale_rescale_eq_of_lim hF Q ha hb _ hfs (hfH.trans F1.B4d.H_subset_Hbar) hae hL
  have hFa := hF.rescale' Q ha
  have key : ∀ d : ℂ, ∀ ρ > 0, rescale (rescale y Q a) Q b (foldedCircle d ρ) =
      rescale y Q (a * b) (foldedCircle d ρ) := by
    intro d ρ hρ
    rw [rescale_fc_eq hFa Q hb d hρ, rescale_fc_eq hF Q (mul_pos ha hb) d hρ]
    have e1 : (a : ℂ) * foldH ((b : ℂ) * d) = foldH (((a * b : ℝ) : ℂ) * d) := by
      rw [← foldH_mul_pos _ ha]; push_cast; ring_nf
    rw [e1, show a * (b * ρ) = a * b * ρ by ring, Real.log_mul ha.ne' hb.ne']
    ring
  unfold locFieldFull
  refine Prod.ext (funext fun i => ?_) (funext fun ρ => ?_)
  · simp only
    split_ifs
    · have hr : 0 < (CoordsFull.fullIndex i).2 := by
        simp only [CoordsFull.fullIndex]; positivity
      exact key _ _ hr
    · rfl
  · simp only
    split_ifs with h
    · obtain ⟨hρs, hρc, hρH⟩ := ρ.2
      simp only [pairRaw]
      rw [hdens hρs.continuous hρc hρH (hlim ρ h _ (mem_insert _ _)),
        hdens (f := fun z => -ρ.1 z) hρs.continuous.neg hρc.neg
          (by rw [show (fun z => -ρ.1 z) = -ρ.1 from rfl, tsupport_neg]; exact hρH)
          (hlim ρ h _ (mem_insert_of_mem _ rfl))]
    · rfl

/-- Locality through an embedding: `AgreeNear y y' r` gives `AgreeNear` of the rescalings by
`a` at radius `r / a`. -/
theorem agreeNear_rescale {y y' : FieldSample} {r : ℝ} (hag : AgreeNear y y' r) (Q : ℝ) {a : ℝ}
    (ha : 0 < a) : AgreeNear (rescale y Q a) (rescale y' Q a) (r / a) := by
  intro n k z hz
  have hsupp := CircleFubini.foldedCircle_support (radius_pos k).le
    (z := dyadicRoundC n z) le_rfl
  refine rescale_congr hag ha (measure_mono_null (compl_subset_compl.2 inter_subset_left) hsupp) ?_
  rw [lt_div_iff₀ ha] at hz
  linarith

/-- **Deterministic window transfer on the model side.** -/
theorem n2_modelLoc_det {γ L r r' a : ℝ} (hγ : 0 < γ) (ha : 0 < a) {K R : ℕ} (hK : 0 < K)
    (hKa : a * K ≤ r') (hr' : r' ≤ r) {p : N1Idx r}
    (hloc : IsLocallyGoodOn γ (halfDisc r) (locModel γ L r p))
    {y' : FieldSample} {F : ℂ × ℝ → ℝ} (hag : AgreeNear (locModel γ L r p) y' r')
    (hF : IsRegularWith y' F)
    (hlim : ∀ c : ℝ, 0 < c → ∀ ρ : TestFun H, suppIn R ρ → ∀ f ∈ ({ρ.1, -ρ.1} : Set (ℂ → ℝ)),
      ∃ L' : ℝ, Tendsto (fun t => ∫ u, F ((c : ℂ) * u, t)
        ∂(volume.withDensity fun z => ENNReal.ofReal (f z))) (𝓝[>] 0) (𝓝 L'))
    (hG : resField K (rescale (locModel γ L r p) (Qc γ) a) ∈ n2Good γ K R) :
    TmRichN1 γ r R L p = gK γ K R (resField K (rescale (locModel γ L r p) (Qc γ) a)) := by
  set y := locModel γ L r p with hy
  set W := rescale y (Qc γ) a with hW
  set sK := scaleSur γ 0 K (resField K W, 0) with hsK
  obtain ⟨h0, hlt⟩ := hG
  have hK' : (0 : ℝ) < K := Nat.cast_pos.2 hK
  have hR0 : (0 : ℝ) ≤ R := R.cast_nonneg
  have hsKR : sK * (R + 2) < K := (lt_div_iff₀ (by linarith)).1 hlt
  have hltK : sK < K := by nlinarith
  have hsKR' : sK * R < K := by nlinarith
  have hKr : (K : ℝ) ≤ r' / a := by rw [le_div_iff₀ ha]; linarith
  have hsc := n2_scale_transfer hγ ha (hKa.trans hr') hloc h0 hltK
  set s := scaleParamOn γ y (halfDisc r) with hs
  have hs' : s = a * sK := by
    have e : sK = s / a := hsc
    rw [e, mul_div_cancel₀ _ ha.ne']
  have hspos : 0 < s := by rw [hs']; positivity
  have hgood : p ∈ goodN1 γ L r := mem_goodN1_of_pos hspos
  have hLHS : TmRichN1 γ r R L p = locFieldFull R (rescale y' (Qc γ) s) := by
    unfold TmRichN1 zoomN1
    rw [scaleSur_eq hgood]
    refine locFieldFull_rescale_congr hag hspos ?_
    rw [hs']; nlinarith
  have hRHS : gK γ K R (resField K W) = locFieldFull R (rescale W (Qc γ) sK) := by
    unfold gK TmRichN1 zoomN1
    exact locFieldFull_rescale_congr (agreeNear_locModel_res γ K W).symm' h0 hsKR'
  rw [hLHS, hRHS, locFieldFull_rescale_congr (agreeNear_rescale hag (Qc γ) ha) h0
    (hsKR'.trans_le hKr), locFieldFull_rescale_rescale hF (Qc γ) ha h0 R
    (fun ρ hρ f hf => hlim (a * sK) (mul_pos ha h0) ρ hρ f hf), hs']

end D3Plus
end QuantumZipper
