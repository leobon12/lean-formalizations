import QuantumZipper.Proofs.Zipper.SWCoreA9Err
import QuantumZipper.Proofs.Zipper.WedgeYGoodArea
import QuantumZipper.Proofs.Zipper.AreaWinTransfer
import QuantumZipper.Proofs.Zipper.SWCoreWinRArea
import QuantumZipper.Proofs.Zipper.AreaWinMkFinal
import QuantumZipper.Proofs.Zipper.AreaWinDense
import QuantumZipper.Proofs.Zipper.JointModFinal

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-A9 (5): `WedgeUnzip.YAreaMergeStmt` (area merging for `Γ⁰`, offsets uniform, all times)

**`yAreaMergeStmt_holds`**: almost surely, for all `t ≥ 0` and all test functions `f`
(continuous, compact support in `ℍ`), the offset merging differences `mergeDiffG` of the
unzipped `Γ⁰` field `y_t = (𝔥₀ + X) ∘ f_t⁻¹ + Q log|(f_t⁻¹)'|` tend to `0` along `goodFilter`
(radii `α 2^{-k}`, `α ∈ [1,2]`). Sheffield–Wang, *Field-measure correspondence in Liouville
quantum gravity almost surely commutes with all conformal maps simultaneously*, Trans. AMS 372
(2020), arXiv:1605.06171, proof of Thm 1.4, (3.5)–(3.7), pp. 11–13, for the flow `φ = f_t⁻¹`
(their radius `ε → 0` is continuous, so the offsets are part of their statement).

Ingredients (all proved):
* window limits of `𝔥₀ + X` (SW proof of Thm 1.1, p. 9, for `X`: `freeWindowStmt_of_splitR`;
  transfer to `𝔥₀ + X`: `windowLimits_transfer`, own bookkeeping, `a9_windowLimits_h0`);
* offset transport along `goodFilter` for one map (`a9_tendsto_goodFilter`, SW Cor. 3.2 via
  `unifWin` indexed by the offset);
* the offset distortion bound (`a9_pushErrR_path`) from the offset flow data at rational
  parameters (`a9_rand_data`: D64 primed core with the radius factor of the family, D70
  independence transfer) and the jointly continuous regular witness of the unzipped fields
  (`RegUnif.jointModStmt_holds`, `a9_ae_regular_Zh`);
* the offset area limit of the time-`0` field (`AreaOffsets.ae_hasAreaLimit`,
  `LogSingGood.hasAreaLimit_add_Lf`) for the transported test function.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace SWCore

open E6

/-- **Window limits of `𝔥₀ + X₀`** from those of `X₀` (deterministic transfer). -/
theorem a9_windowLimits_h0 (κ : ℝ) (hκ : 0 < κ) {X0 : FieldSample} {FX : ℂ × ℝ → ℝ}
    (hFX : IsRegularWith X0 FX)
    (hA : HasAreaLimit (Real.sqrt κ) X0 (qAreaMeasure (Real.sqrt κ) X0))
    {c c' : ℕ → ℝ} (hW : WindowLimits (Real.sqrt κ) X0 c c') :
    WindowLimits (Real.sqrt κ) (ofFun (h0rev κ) + X0) c c' := by
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hg : ContinuousOn (h0rev κ) H := by
    unfold h0rev
    refine continuousOn_const.mul (continuous_norm.continuousOn.log fun z hz => ?_)
    refine norm_ne_zero_iff.2 fun h => ?_
    have h1 : (0 : ℝ) < z.im := hz
    rw [h, Complex.zero_im] at h1
    exact lt_irrefl _ h1
  refine windowLimits_transfer hg ?_ ?_ hW
  · have hreg : IsRegularSample (ofFun (h0rev κ) + X0) := by
      rw [WedgeUnzip.h0rev_add_eq_Lf]; exact ⟨_, LogSingGood.regular_add_Lf hFX _⟩
    have hlim : HasAreaLimit (Real.sqrt κ) (ofFun (h0rev κ) + X0)
        ((qAreaMeasure (Real.sqrt κ) X0).withDensity fun z =>
          ENNReal.ofReal (‖z‖ ^ (-(-(2 / Real.sqrt κ) * Real.sqrt κ)))) := by
      rw [WedgeUnzip.h0rev_add_eq_Lf]; exact LogSingGood.hasAreaLimit_add_Lf hFX hA _
    rw [GoodSample.qAreaMeasure_eq_of_hasAreaLimit hreg hlim]
    refine withDensity_congr_ae ?_
    have hae : ∀ᵐ z ∂qAreaMeasure (Real.sqrt κ) X0, z ∈ H := by
      rw [ae_iff]; exact hA.1
    filter_upwards [hae] with z hz
    have hz0 : 0 < ‖z‖ := lt_of_lt_of_le (show (0 : ℝ) < z.im from hz) (Complex.im_le_norm z)
    congr 1
    rw [Real.rpow_def_of_pos hz0]
    congr 1
    unfold h0rev
    field_simp
  · intro w hw ρ hρ hρw
    have hδ : 0 < (w.im - ρ) / 3 := by linarith
    have hcar := a8_ae_circ hρ hρw.le isClosed_closedBall
      fun θ => circleMap_mem_closedBall w hρ.le θ
    have hKim : ∀ u ∈ closedBall w ρ, 3 * ((w.im - ρ) / 3) ≤ u.im := by
      intro u hu
      rw [mem_closedBall, dist_eq_norm] at hu
      have h := (Complex.abs_im_le_norm (u - w)).trans hu
      rw [Complex.sub_im, abs_le] at h
      linarith [h.1]
    rw [a9_evalReg_h0_add κ hFX hδ (isCompact_closedBall w ρ) hKim hcar
      (a8_reg_tendsto hFX w hρ)]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hcar] with u hu
    exact h0cut_eq (le_trans (by linarith [hKim u hu]) (Complex.im_le_norm u))

/-- **Regularity of the unzipped fields with the joint witness `Zh(t, ·)`**, all `t ∈ [0,T]`
(as `RegUnif.ae_forall_isRegularWith_of_jointMod`, keeping the witness). -/
theorem a9_ae_regular_Zh {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ γ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hT : 0 < T) {Zh : ℝ × (ℂ × ℝ) → Ω → ℝ}
    (hc : ∀ ω, ContinuousOn (fun q => Zh q ω) (RegUnif.parSet T))
    (hmod : ∀ q ∈ RegUnif.parSet T, (fun ω => Zh q ω) =ᵐ[P] fun ω =>
      unzippedField γ (ofFun (h0rev κ) + X ω, drive κ B ω) q.1 (foldedCircle q.2.1 q.2.2))
    (hcomm : ∀ t ∈ Icc 0 T, ∀ w ∈ Hbar, ∀ r ρ : ℝ, 0 < r → 0 < ρ → ∀ᵐ ω ∂P,
      ∫ u, Zh (t, (u, ρ)) ω ∂foldedCircle w r = ∫ v, Zh (t, (v, r)) ω ∂foldedCircle w ρ) :
    ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T,
      IsRegularWith (unzippedField γ (ofFun (h0rev κ) + X ω, drive κ B ω) t)
        (fun p => Zh (t, p) ω) := by
  obtain ⟨D, hDc, hDT, hTD⟩ := TopologicalSpace.exists_countable_dense_subset (Icc (0 : ℝ) T)
  set S4 : Set (ℝ × ((ℂ × ℝ) × ℝ)) := Icc 0 T ×ˢ ((Hbar ×ˢ Ioi 0) ×ˢ Ioi 0) with hS4
  obtain ⟨D4, hD4c, hD4S, hSD4⟩ := TopologicalSpace.exists_countable_dense_subset S4
  have hraw : ∀ᵐ ω ∂P, ∀ t ∈ D, ∀ k : ℕ, ∀ d ∈ RegUnif.Dy,
      unzippedField γ (ofFun (h0rev κ) + X ω, drive κ B ω) t (foldedCircle d (radius k)) =
        Zh (t, (d, radius k)) ω :=
    (eventually_countable_ball hDc).2 fun t ht => ae_all_iff.2 fun k =>
      (eventually_countable_ball RegUnif.countable_Dy).2 fun d hd =>
        (hmod (t, (d, radius k)) ⟨hDT ht, RegUnif.Dy_subset_Hbar hd, radius_pos k⟩).mono
          fun ω hω => hω.symm
  have hcm : ∀ᵐ ω ∂P, ∀ q ∈ D4, ∫ u, Zh (q.1, (u, q.2.2)) ω ∂foldedCircle q.2.1.1 q.2.1.2 =
      ∫ v, Zh (q.1, (v, q.2.1.2)) ω ∂foldedCircle q.2.1.1 q.2.2 :=
    (eventually_countable_ball hD4c).2 fun q hq => by
      obtain ⟨h1, ⟨h2, h3⟩, h4⟩ := hD4S hq
      exact hcomm q.1 h1 q.2.1.1 h2 q.2.1.2 q.2.2 h3 h4
  have hyc : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ d ∈ RegUnif.Dy, ContinuousOn
      (fun t => unzippedField γ (ofFun (h0rev κ) + X ω, drive κ B ω) t
        (foldedCircle d (radius k))) (Icc 0 T) :=
    ae_all_iff.2 fun k => (eventually_countable_ball RegUnif.countable_Dy).2 fun d _ =>
      RegCont.ae_continuousOn_unzippedField κ γ hB hX hind hT d (radius_pos k)
  filter_upwards [hraw, hcm, hyc] with ω h1 h2 h3
  exact fun t ht =>
    (RegUnif.forall_isRegularWith_of_joint (G := fun t p => Zh (t, p) ω) (hc ω) h3 hDT hTD h1
      hD4S hSD4 h2 t ht).1

/-- **`WedgeUnzip.YAreaMergeStmt` holds** (Sheffield–Wang, arXiv:1605.06171, proof of Thm 1.4,
(3.5)–(3.7), for the flow `φ = f_t⁻¹`, offsets uniform). -/
theorem yAreaMergeStmt_holds : WedgeUnzip.YAreaMergeStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt κ < 2 := F2.sqrt_lt_two_of' hκ hκ4
  have hJ : ∀ N : ℕ, RegUnif.JointModStmt κ (Real.sqrt κ) ((((N : ℚ) + 1 : ℚ)) : ℝ) P B X :=
    fun N => RegUnif.jointModStmt_holds κ (Real.sqrt κ) hB hX hind (by push_cast; positivity)
  simp only [RegUnif.JointModStmt] at hJ
  choose Zh hZc hZm hZcomm using hJ
  have hregZ : ∀ᵐ ω ∂P, ∀ N : ℕ, ∀ t ∈ Icc (0 : ℝ) ((((N : ℚ) + 1 : ℚ)) : ℝ),
      IsRegularWith (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) t)
        (fun p => Zh N (t, p) ω) :=
    ae_all_iff.2 fun N => a9_ae_regular_Zh hB hX hind (by push_cast; positivity) (hZc N)
      (hZm N) (hZcomm N)
  have hratZ : ∀ᵐ ω ∂P, ∀ N : ℕ, ∀ q : ℚ, ∀ z : ℚ × ℚ, ∀ α : ℚ, ∀ k : ℕ,
      (q : ℝ) ∈ Icc (0 : ℝ) ((((N : ℚ) + 1 : ℚ)) : ℝ) → zQ z ∈ Hbar →
      (α : ℝ) ∈ Icc (1 : ℝ) 2 →
      Zh N ((q : ℝ), (zQ z, (α : ℝ) * radius k)) ω =
        unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) q
          (foldedCircle (zQ z) ((α : ℝ) * radius k)) := by
    refine ae_all_iff.2 fun N => ae_all_iff.2 fun q => ae_all_iff.2 fun z =>
      ae_all_iff.2 fun α => ae_all_iff.2 fun k => ?_
    by_cases h : (q : ℝ) ∈ Icc (0 : ℝ) ((((N : ℚ) + 1 : ℚ)) : ℝ) ∧ zQ z ∈ Hbar ∧
      (α : ℝ) ∈ Icc (1 : ℝ) 2
    · filter_upwards [hZm N ((q : ℝ), (zQ z, (α : ℝ) * radius k))
        ⟨h.1, h.2.1, mul_pos (by linarith [h.2.2.1]) (radius_pos k)⟩] with ω hω _ _ _
      exact hω
    · exact ae_of_all _ fun ω h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h
  have hWin : ∀ᵐ ω ∂P, WindowLimits (Real.sqrt κ) (X ω) (swC (Real.sqrt κ))
      (swC' (Real.sqrt κ)) :=
    freeWindowStmt_of_splitR hγ hγ2 (swWindowSplitStmtR_holds hγ hγ2) P X hX
  filter_upwards [hregZ, hratZ, a9_rand_data κ hB hX hind, RegSample.ae_isRegularSample hX,
    AreaOffsets.ae_hasAreaLimit hX hγ hγ2, hWin, RegUnif.ae_drive_good hB κ]
    with ω hregω hratω hDω hXreg hAω hWω hdr
  intro t ht f hf hfc hfH
  obtain ⟨FX, hFX⟩ := hXreg
  have hW := hdr.1
  have hW0 := hdr.2
  have hxr : IsRegularSample (ofFun (h0rev κ) + X ω) := by
    rw [WedgeUnzip.h0rev_add_eq_Lf]; exact ⟨_, LogSingGood.regular_add_Lf hFX _⟩
  obtain ⟨Fx, hFx⟩ := hxr
  have hAx : HasAreaLimit (Real.sqrt κ) (ofFun (h0rev κ) + X ω)
      (qAreaMeasure (Real.sqrt κ) (ofFun (h0rev κ) + X ω)) := by
    have h : HasAreaLimit (Real.sqrt κ) (ofFun (h0rev κ) + X ω)
        ((qAreaMeasure (Real.sqrt κ) (X ω)).withDensity fun z =>
          ENNReal.ofReal (‖z‖ ^ (-(-(2 / Real.sqrt κ) * Real.sqrt κ)))) := by
      rw [WedgeUnzip.h0rev_add_eq_Lf]; exact LogSingGood.hasAreaLimit_add_Lf hFX hAω _
    rwa [GoodSample.qAreaMeasure_eq_of_hasAreaLimit ⟨Fx, hFx⟩ h]
  have hWx := a9_windowLimits_h0 κ hκ hFX hAω hWω
  obtain ⟨a, b, c, d, hc, hsub⟩ := exists_rect_of_compact hfc hfH
  obtain ⟨ρ, M, m, hρ, hm, hcl⟩ := flow_mem_areaClass hW hW0 ht (a := a) (b := b) (d := d) hc
  have hψ := hcl t ⟨ht, le_rfl⟩
  have hKH : rectC (a : ℝ) b c d ⊆ H := rectC_subset_H hc
  have hHHbar : H ⊆ Hbar := fun w hw => le_of_lt (show 0 < w.im from hw)
  have hErr : ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ α ∈ Icc (1 : ℝ) 2, ∀ z ∈ rectC (a : ℝ) b c d,
      |pushErrR (Real.sqrt κ) (ofFun (h0rev κ) + X ω) (fwdMapInv (drive κ B ω) t)
        (α * radius k) z| ≤ η := by
    intro η hη
    by_cases hab : (a : ℝ) ≤ b
    swap
    · exact Eventually.of_forall fun k α _ z hz => absurd (hz.1.1.trans hz.1.2) hab
    by_cases hcd : (c : ℝ) ≤ d
    swap
    · exact Eventually.of_forall fun k α _ z hz => absurd (hz.2.1.trans hz.2.2) hcd
    obtain ⟨N, hN⟩ := exists_nat_ge t
    have hTN : ((((N : ℚ) + 1 : ℚ)) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    have htN : t ∈ Icc (0 : ℝ) ((((N : ℚ) + 1 : ℚ)) : ℝ) := ⟨ht, by rw [hTN]; linarith⟩
    have hmain := a9_pushErrR_path κ (Real.sqrt κ) hFX hFx hW hW0 (Tq := (N : ℚ) + 1)
      (by push_cast; positivity) hab hc hcd (hZc N ω) (hregω N)
      (fun q hq z hz α hα k => hratω N q z α k hq (hHHbar (hKH hz)) hα)
      (hDω N a b c d hab hc hcd) η hη
    filter_upwards [hmain] with k hk α hα z hz
    exact hk t htN α hα z hz
  have hT1 := a9_tendsto_goodFilter hγ (tendsto_swC _) (tendsto_swC' _) hWx hAx.2.1
    (measurable_supWin ⟨Fx, hFx⟩ _) (measurable_infWin ⟨Fx, hFx⟩ _) hc hρ hm hψ hErr hf hfc hsub
  rw [pullTest_eq_transTest hW hW0 ht hKH (hsub.trans interior_subset)] at hT1
  have hT2 := hAx.2.2 (E6.transTest (drive κ B ω) t f)
    (E6.continuous_transTest hW hW0 ht hf hfc hfH)
    (E6.hasCompactSupport_transTest hW hW0 ht hfc hfH)
    (E6.tsupport_transTest_subset hW hW0 ht hfc hfH)
  have h := hT1.sub hT2
  rw [sub_self] at h
  exact h.congr fun i => rfl

end SWCore
end QuantumZipper
