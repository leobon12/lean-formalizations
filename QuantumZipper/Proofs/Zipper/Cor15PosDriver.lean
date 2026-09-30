import QuantumZipper.Proofs.Thm14.Wire
import QuantumZipper.Proofs.Loewner.CoreArc3e
import QuantumZipper.Proofs.Zipper.UnzipFullSplit
import QuantumZipper.Proofs.Zipper.Cor15GroupZero

/-!
# Corollary 1.5, positive times: the welding driver of an unzipped configuration

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18;
the paper gives no proof, it calls the corollary immediate from Theorems 1.3 and 1.4).
Blocker 1 of `handoff/COR15.md`, driver half. With `c = (𝔥₀ + X, W)`, `W = √κ B`, and
`y = zipCapDown √κ t c` (`t > 0`), almost surely

* `ae_eqOn_weldDriver_zipCapDown`: the welding driver `weldDriver √κ y.1 t` agrees on `[0,t]`
  with the time reversal `vrev W t` of `W` (existence and uniqueness of the welding driver);
* `ae_zipCapUp_zipCapDown_snd`: the driving function of `zipCapUp √κ t y` is `W` on `[0,∞)`;
* `ae_zipCapUp_zipCapDown_fst`: the field of `zipCapUp √κ t y` is
  `coordChange y.1 (revMapInv (vrev W t) t) Q`.

Route (**own argument**; the paper has no proof). The unzipping map `fwdMapInv W t` equals
`revMap V' t` on `ℍ` for an independent Brownian motion `B'`, `V' = √κ B'`, and the unzipped
field has a.s. the circle coordinates of the Theorem 1.3 field of `V'`
(`UnzipFull.exists_unzip_driver`, `UnzipFull.ae_coordsFull_unzip`, re-proved here with both
facts for the same `B'`). Theorem 1.4(a)'s first conjunct (from Theorem 1.3 and Rohde–Schramm
simplicity) and `Thm14OptB.ae_good_drive'` make `V'` a welding driver of `y.1`. Since
`revHull`, `zeroMinus` and `weldingHom` read `revMap _ t` only on `ℍ`, the time reversal
`vrev W t` (same reverse map on `ℍ`, `B2.fwdMapInv_eq_revMap_vrev`) is a welding driver too.
Weld-driver uniqueness (`WeldingConsistency.eqOn_of_isWeldingDriver`, with removability of the
hulls of `V'` at `t` and at rational times, `JS.ae_removable_doubledHull'`) identifies
`weldDriver`, `V'` and `vrev W t` on `[0,t]`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped Topology NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace Cor15Group

open UnzipFull CharFun UnzipInvariance B2

/-! ### Deterministic: welding data read `revMap _ t` only on `ℍ` -/

theorem revMapBdry_congr_H {V₁ V₂ : ℝ → ℝ} {t : ℝ} (h : EqOn (revMap V₁ t) (revMap V₂ t) H) :
    revMapBdry V₁ t = revMapBdry V₂ t := by
  funext x
  have he : (fun y : ℝ => revMap V₁ t (x + y * I)) =ᶠ[𝓝[>] (0 : ℝ)]
      fun y : ℝ => revMap V₂ t (x + y * I) := by
    filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
    exact h (show (0 : ℝ) < (↑x + ↑y * I).im by simpa using hy)
  unfold revMapBdry limUnder
  rw [Filter.map_congr he]

theorem isWeldingDriver_of_eqOn_H {γ : ℝ} {x : FieldSample} {t : ℝ} {V₁ V₂ : ℝ → ℝ}
    (h₁ : IsWeldingDriver γ x t V₁) (hc : Continuous V₂) (h0 : V₂ 0 = 0)
    (h : EqOn (revMap V₁ t) (revMap V₂ t) H) : IsWeldingDriver γ x t V₂ := by
  obtain ⟨-, -, hK, hw⟩ := h₁
  have hb := revMapBdry_congr_H h
  have hK' : revHull V₁ t = revHull V₂ t := by
    unfold revHull; rw [h.image_eq]
  have hz : zeroMinus V₁ t = zeroMinus V₂ t := by unfold zeroMinus; rw [hb]
  have hwh : weldingHom V₁ t = weldingHom V₂ t := by
    funext s; unfold weldingHom; rw [hb]
  refine ⟨hc, h0, hK' ▸ hK, fun s hs => ?_⟩
  rw [← hwh, hw s (hz ▸ hs)]

/-! ### The unzipped field and its driver, for one Brownian motion `B'` -/

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- `UnzipFull.ae_coordsFull_unzip` with the map identity of `exists_unzip_driver` kept for
the same Brownian motion `B'` (the proof is that of `ae_coordsFull_unzip`). -/
theorem ae_coordsFull_unzip_map (κ : ℝ) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) {t : ℝ} (ht : 0 ≤ t) :
    ∃ B' : ℝ≥0 → Ω → ℝ, IsBrownianReal B' P ∧ IndepFun (pathOf B') X P ∧
      ∀ᵐ ω ∂P, EqOn (fwdMapInv (drive κ B ω) t) (revMap (drive κ B' ω) t) H ∧
        CoordsFull.coordsFull
          (coordChange (ofFun (h0rev κ) + X ω) (fwdMapInv (drive κ B ω) t) (Qc (Real.sqrt κ))) =
        CoordsFull.coordsFull (couplingFieldRev κ (drive κ B' ω) t (X ω)) := by
  have hI := inputs_holds
  obtain ⟨B', hB', hB'm, hB'c, hind', hEq⟩ := exists_unzip_driver κ hB hind ht
  refine ⟨B', hB', hind', ?_⟩
  set g := pathC t B' hB'c with hg_def
  have hgm : Measurable g := measurable_pathC t hB'm hB'c
  have hig : IndepFun g X P := indepFun_pathC t hind' hB'c
  have hsp : ∀ i, ∀ᵐ ω ∂P, evalReg (ofFun (h0rev κ) + X ω)
        ((foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2).map
          (revMap (Wof κ t ht (g ω)) t)) =
      (∫ z, h0rev κ z ∂((foldedCircle (CoordsFull.fullIndex i).1
          (CoordsFull.fullIndex i).2).map (revMap (Wof κ t ht (g ω)) t))) +
        evalReg (X ω) ((foldedCircle (CoordsFull.fullIndex i).1
          (CoordsFull.fullIndex i).2).map (revMap (Wof κ t ht (g ω)) t)) := fun i =>
    ae_split_fc_random hI κ ht hX hgm hig _ (fullIndex_radius_pos i)
  filter_upwards [hEq, ae_all_iff.2 hsp] with ω hE hs
  refine ⟨hE, ?_⟩
  funext i
  have hri := fullIndex_radius_pos i
  set μ := foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2 with hμ
  have hμH : μ Hᶜ = 0 := ae_iff.1 (hI.aeH _ hri)
  have hrev : revMap (drive κ B' ω) t = revMap (Wof κ t ht (g ω)) t :=
    revMap_drive_eq κ t ht B' hB'c ω
  have hWc := continuous_Wof κ t ht (g ω)
  have hWm := measurable_revMap_Wof κ t ht (g ω)
  show coordChange (ofFun (h0rev κ) + X ω) (fwdMapInv (drive κ B ω) t) (Qc (Real.sqrt κ)) μ =
    couplingFieldRev κ (drive κ B' ω) t (X ω) μ
  rw [coordChange_congr_of_eqOn hE hμH, CouplingMarkov.couplingFieldRev_eq, hTrev_congr hrev κ,
    hrev]
  show evalReg (ofFun (h0rev κ) + X ω) (μ.map (revMap (Wof κ t ht (g ω)) t)) +
      Qc (Real.sqrt κ) * ∫ z, Real.log ‖deriv (revMap (Wof κ t ht (g ω)) t) z‖ ∂μ =
    ofFun (hTrev κ (Wof κ t ht (g ω)) t) μ +
      (evalReg (X ω) (μ.map (revMap (Wof κ t ht (g ω)) t)) +
        0 * ∫ z, Real.log ‖deriv (revMap (Wof κ t ht (g ω)) t) z‖ ∂μ)
  rw [hs i, zero_mul, add_zero,
    show ofFun (hTrev κ (Wof κ t ht (g ω)) t) μ = ∫ z, hTrev κ (Wof κ t ht (g ω)) t z ∂μ from rfl,
    integral_hTrev_fc hI κ hWc ht hWm _ hri]
  ring

/-- **The welding driver of the unzipped field** (`t > 0`, conditional on Theorem 1.3 and
Rohde–Schramm simplicity). A.s. `weldDriver √κ y.1 t = vrev W t` on `[0,t]`, where
`y = zipCapDown √κ t (𝔥₀ + X, W)`. -/
theorem ae_eqOn_weldDriver_zipCapDown (h13 : theorem1_3) (hRSS : Blueprint.RohdeSchrammSimple)
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, EqOn
      (weldDriver (Real.sqrt κ)
        (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1 t)
      (vrev (drive κ B ω) t) (Icc 0 t) := by
  obtain ⟨B', hB', hind', hae⟩ := ae_coordsFull_unzip_map κ hB hX hind ht.le
  have h4a := Thm14Wire.theorem1_4a_of_theorem1_3_rss h13 hRSS κ hκ hκ4 t ht P B' X hB' hX hind'
  have hgood := Thm14OptB.ae_good_drive' CaraR.revMapCaratheodory hRSS hκ hκ4 ht P B' hB'
  have hremq : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < t →
      IsConformallyRemovable (closure (revHull (drive κ B' ω) q) ∪
        conj '' closure (revHull (drive κ B' ω) q)) := by
    rw [ae_all_iff]
    intro q
    by_cases hq : 0 < (q : ℝ)
    · filter_upwards [JS.ae_removable_doubledHull' CaraR.revMapCaratheodory hRSS κ hκ hκ4 q hq
        P B' hB'] with ω h _ _ using h
    · exact Filter.Eventually.of_forall fun ω h => absurd h hq
  filter_upwards [hae, h4a, hgood, hremq, hB.cont, hB.eval_zero_ae_eq_zero] with ω ⟨hE, hC⟩
    ⟨⟨_, hw⟩, _⟩ ⟨hVc, hV0, hS, hrem⟩ hrq hc h0
  set y1 := (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1 with hy1
  have hV : IsWeldingDriver (Real.sqrt κ) y1 t (drive κ B' ω) := by
    refine ⟨hVc, hV0, Or.inr hS, fun s hs => ?_⟩
    rw [hw s hs]
    have hq : qBoundaryMeasure (Real.sqrt κ) y1 =
        qBoundaryMeasure (Real.sqrt κ) (couplingFieldRev κ (drive κ B' ω) t (X ω)) :=
      qBoundaryMeasure_congr_of_coordsFull _ hC
    unfold weldR weldHomR
    rw [hq]
  have hW' := weldDriver_spec ⟨_, hV⟩
  have hWc : Continuous (drive κ B ω) := drive_continuous hc
  have hW0 : drive κ B ω 0 = 0 := drive_zero h0
  have hmap : EqOn (revMap (drive κ B' ω) t) (revMap (vrev (drive κ B ω) t) t) H :=
    fun z hz => by rw [← hE hz, fwdMapInv_eq_revMap_vrev hWc hW0 ht.le hz]
  have hvr : IsWeldingDriver (Real.sqrt κ) y1 t (vrev (drive κ B ω) t) :=
    isWeldingDriver_of_eqOn_H hV (continuous_vrev hWc t) (vrev_zero ht.le) hmap
  have e1 := WeldingConsistency.eqOn_of_isWeldingDriver CaraR.revMapCaratheodory
    CoreArc.loewnerSubhullsOfArc ht hV hW' hrem hrq
  have e2 := WeldingConsistency.eqOn_of_isWeldingDriver CaraR.revMapCaratheodory
    CoreArc.loewnerSubhullsOfArc ht hV hvr hrem hrq
  intro s hs
  rw [← e1 hs, e2 hs]

end Cor15Group
end QuantumZipper
