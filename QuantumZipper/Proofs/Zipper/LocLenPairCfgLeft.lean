import QuantumZipper.Proofs.Zipper.LocLenPairCfgDefs
import QuantumZipper.Proofs.Zipper.LocLenB5UPlus
import QuantumZipper.Proofs.Zipper.UnifClColl
import QuantumZipper.Proofs.Zipper.UnifD33Close
import QuantumZipper.Proofs.Zipper.LocLenRules

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75, task R6a: the left open-arc cocycle in the `Γ⁰` picture (no tip input)

Sheffield arXiv:1012.4797 p. 56 and p. 70 ("additivity along the flow": the boundary length of
`η[0,u+s]` is read in one fixed chart as the mass of nested arcs); Berestycki–Powell
arXiv:2404.16642 Def 8.12 p. 281 (lengths of open boundary arcs).

In the fixed chart `T` (field `h⁰_T`, boundary measure `ν_T`):

* `ae_pieceArc_left`: the open-arc left length of `zipCapDown γ u cfg` at time `s` is
  `ν_T(0₋(T−u), 0₋(T−u−s))`. Copy of `RegUnif.lenCollidedStmt_of_windows` (UnifClColl.lean) with
  the global inputs UW/UA replaced by the off-tip local windows (`ae_windows_local_of_anchor`) and
  the off-tip local limit at time `u+s` (`unifLocalStmt_holds`), and closed arcs by open ones
  (`B5.measure_Ioo_eq_of_windows`); the field of `zipCapDown γ u cfg` at `s` is `h⁰_{u+s}` in
  regular coordinates (`RegUnif.capCocycleRegStmt_holds`, D33, proved).
* `ae_leftCocycleArc`: additivity `L⁻_{u+s} = L⁻_u + L⁻_s ∘ zipCapDown γ u` for all `u, s ≥ 0`
  (copy of `RegUnif.lenCocycleStmt_of_windows` + `ae_lenCocycle_all_of_unifAll`), from the above,
  the open-arc B5 (`ae_b5MinusArc_of_extAll`) and the fixed-time atomlessness of `ν_T`
  (`Wire2.ae_nu0_regular`).

Forbidden tip inputs (`TipCore`, UT, UG, UA, `CfgFlowRegStmt`) are not used. Own bookkeeping
otherwise (the paper states the additivity without details).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open B2 B5 RegUnif RealLine CaraR

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ T : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- **The newly unzipped left piece in the fixed chart `T`**: a.s., for `u, s ≥ 0`, `u + s ≤ T`,
the open-arc left length of `zipCapDown γ u cfg` at time `s` is `ν_T(0₋(T−u), 0₋(T−u−s))`. -/
theorem ae_pieceArc_left (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, ∀ u s : ℝ, 0 ≤ u → 0 ≤ s → u + s ≤ T →
      (unzipLengthsArc (Real.sqrt κ) (zipCapDown (Real.sqrt κ) u (cfg κ B X ω)) s).1 =
        qBoundaryMeasure (Real.sqrt κ) (h0f κ T B X ω)
          (Ioo (zeroMinus (Vr κ T B ω) (T - u)) (zeroMinus (Vr κ T B ω) (T - u - s))) := by
  have hRSS := RS.rohdeSchrammSimple
  have hF := E5.extAllInput_holds κ P B X hκ hκ4 hB hX hind
  filter_upwards [ae_windows_local_of_anchor hκ hκ4 hT hB hX hind
      (anchorWindowAllStmt_of_extAll hκ hκ4 hB hX hind hF T hT),
    unifLocalStmt_holds hκ hκ4 hT hB hX hind,
    capCocycleRegStmt_holds (κ := κ) hB hX hind hT,
    ae_b5MinusArc_of_extAll hκ hκ4 hT hB hX hind hF, hB.cont, hB.eval_zero_ae_eq_zero,
    ae_isSimpleCurveHull_revHull_Vr hRSS hκ hκ4.le hT P B hB,
    ae_forall_isSimpleCurveHull_revHull_Vr hRSS hκ hκ4.le P B hB] with
    ω hw hloc hcr hb5 hc h0 hK hKs
  intro u s hu hs hus
  set W := drive κ B ω with hWdef
  have hWc : Continuous W := Thm14FromThm13.continuous_drive hc
  have hW0 : W 0 = 0 := by simp [hWdef, drive, h0]
  set V := Vr κ T B ω with hVdef
  have hVc : Continuous V := continuous_vrev hWc T
  have hV0 : V 0 = 0 := vrev_zero hT.le
  have hanti := strictAntiOn_zeroMinus hVc hV0 hT hK
  obtain ⟨hreg, -, -⟩ := hcr u s hu hs hus
  have hL : (unzipLengthsArc (Real.sqrt κ) (zipCapDown (Real.sqrt κ) u (cfg κ B X ω)) s).1 =
      arcLen (Real.sqrt κ) (h0f κ (u + s) B X ω)
        (sideImages (zipCapDown (Real.sqrt κ) u (cfg κ B X ω)).2 s).1 0 := by
    rw [h0f_eq_unzippedField]
    exact arcLen_congr (B3d.avgReg_eq_of_regEq hreg) _ _
  rw [hL]
  have hdrv : (zipCapDown (Real.sqrt κ) u (cfg κ B X ω)).2 = fun r => W (u + max r 0) - W u :=
    rfl
  have hsub : ∀ {p r : ℝ}, r ≤ 0 → Ioo p r ⊆ ({0} : Set ℝ)ᶜ := fun hr z hz hz0 => by
    rw [mem_singleton_iff] at hz0; linarith [hz.2]
  rcases hs.eq_or_lt with hs0 | hs0
  · -- `s = 0`
    subst hs0
    rw [hdrv, sideImages_fst_zero_time (by simp), arcLen_self, sub_zero, Ioo_self, measure_empty]
  rcases hu.eq_or_lt with hu0 | hu0
  · -- `u = 0`: the open-arc B5
    subst hu0
    have hside : sideImages (fun r => W (0 + max r 0) - W 0) s = sideImages W s :=
      ESM.sideImages_congr_drive hs0.le fun r hr => by
        simp [max_eq_left hr.1, hW0]
    have e1 : arcLen (Real.sqrt κ) (h0f κ (0 + s) B X ω) (sideImages W s).1 0 =
        (unzipLengthsArc (Real.sqrt κ) (cfg κ B X ω) s).1 := by
      rw [zero_add, h0f_eq_unzippedField]; rfl
    rw [hdrv, hside, e1, hb5 s ⟨hs0.le, by linarith⟩, sub_zero]
  -- `u, s > 0`
  have hKu := hKs u hu0
  have hside := sideImages_fst_shift_eq (W := W) (T := T) (u := u) (s := s) hWc hT hK hKu hu0 hs0
    hus
  rw [hdrv, hside]
  have ht : (0 : ℝ) ≤ T - u - s := by linarith
  have hVs : Continuous (Vr κ (u + s) B ω) := continuous_vrev hWc (u + s)
  have e : T - (u + s) = T - u - s := by ring
  obtain ⟨-, hmono, -, hC⟩ := realRevMap_endpoints hVc hV0 hT hK hVs (vrev_zero (by linarith))
    (by linarith : 0 < u + s) (hKs (u + s) (by linarith)) ht (by ring)
    (fun r hr => by
      show vrev W (u + s) r = vrev W T (T - u - s + r) - vrev W T (T - u - s)
      rw [← e]; exact (vrev_shift (by linarith : (0 : ℝ) ≤ u + s) hus hr).symm)
  have hac1 : zeroMinus V T < zeroMinus V (T - u) :=
    hanti ⟨by linarith, by linarith⟩ ⟨hT.le, le_rfl⟩ (by linarith)
  have hcc' : zeroMinus V (T - u) < zeroMinus V (T - u - s) :=
    hanti ⟨ht, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
  have hA : Tendsto (realRevMap V (T - u - s)) (𝓝[>] (zeroMinus V (T - u)))
      (𝓝 (realRevMap V (T - u - s) (zeroMinus V (T - u)))) :=
    (continuousAt_realRevMap_zeroMinus hVc hV0 hT hK ht (by linarith) (by linarith)).tendsto.mono_left
      nhdsWithin_le_nhds
  obtain ⟨ν, hν, -⟩ := hloc (u + s) ⟨by linarith, hus⟩
  have hmono' : StrictMonoOn (realRevMap V (T - u - s)) (Ioo (zeroMinus V T) (zeroMinus V (T - u - s))) :=
    hmono
  rw [arcLen_eq_of_isVagueLimitOnR hν (hsub le_rfl)]
  refine (measure_Ioo_eq_of_windows hcc' (hmono'.mono (Ioo_subset_Ioo_left hac1.le)) hA hC
    fun u' v' h1 h2 h3 => ?_).symm
  have h3' : (v' : ℝ) < zeroMinus V (T - (u + s)) := by rw [e]; exact h3
  have hwin := hw (u + s) ⟨by linarith, hus⟩ u' v' (hac1.trans h1) h2 h3'
  rw [e] at hwin
  rw [hwin, arcLen_eq_of_isVagueLimitOnR hν (hsub
    (lt_of_strictMonoOn_tendsto_left hmono' hC ⟨hac1.trans (h1.trans h2), h3⟩).le)]

/-- **Additivity of the open-arc left length along the capacity flow, all times** (no tip
input): a.s., for all `u, s ≥ 0`, `L⁻_{u+s} = L⁻_u + L⁻_s(zipCapDown γ u cfg)`. -/
theorem ae_leftCocycleArc (hκ : 0 < κ) (hκ4 : κ < 4)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, ∀ u s : ℝ, 0 ≤ u → 0 ≤ s →
      (unzipLengthsArc (Real.sqrt κ) (cfg κ B X ω) (u + s)).1 =
        (unzipLengthsArc (Real.sqrt κ) (cfg κ B X ω) u).1 +
          (unzipLengthsArc (Real.sqrt κ) (zipCapDown (Real.sqrt κ) u (cfg κ B X ω)) s).1 := by
  have hF := E5.extAllInput_holds κ P B X hκ hκ4 hB hX hind
  have hper : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ u s : ℝ, 0 ≤ u → 0 ≤ s → u + s ≤ (n : ℝ) + 1 →
      (unzipLengthsArc (Real.sqrt κ) (cfg κ B X ω) (u + s)).1 =
        (unzipLengthsArc (Real.sqrt κ) (cfg κ B X ω) u).1 +
          (unzipLengthsArc (Real.sqrt κ) (zipCapDown (Real.sqrt κ) u (cfg κ B X ω)) s).1 := by
    intro n
    have hT : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    filter_upwards [ae_pieceArc_left hκ hκ4 hT hB hX hind,
      ae_b5MinusArc_of_extAll hκ hκ4 hT hB hX hind hF,
      Wire2.ae_nu0_regular hκ hκ4 hT hB hX hind,
      ae_zeroMinus_Vr_facts RS.rohdeSchrammSimple hκ hκ4.le hT P B hB] with ω hLC hU hν hzm
    intro u s hu hs hus
    obtain ⟨-, -, hanti, -, -, -⟩ := hzm
    set T : ℝ := (n : ℝ) + 1 with hTdef
    set ν := qBoundaryMeasure (Real.sqrt κ) (h0f κ T B X ω)
    set zm := zeroMinus (Vr κ T B ω)
    have : NullSingletonClass ν := ⟨hν.1⟩
    rw [hU (u + s) ⟨by linarith, hus⟩, hU u ⟨hu, by linarith⟩, hLC u s hu hs hus]
    show ν (Ioo (zm T) (zm (T - (u + s)))) = ν (Ioo (zm T) (zm (T - u))) +
      ν (Ioo (zm (T - u)) (zm (T - u - s)))
    rw [show T - (u + s) = T - u - s by ring]
    have ha1 : zm T ≤ zm (T - u) :=
      hanti.antitoneOn ⟨by linarith, by linarith⟩ ⟨hT.le, le_rfl⟩ (by linarith)
    have h12 : zm (T - u) ≤ zm (T - u - s) :=
      hanti.antitoneOn ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
    rw [measure_congr (Ioo_ae_eq_Icc (μ := ν)), measure_congr (Ioo_ae_eq_Icc (μ := ν)),
      measure_congr (Ioo_ae_eq_Icc (μ := ν)),
      ← Icc_union_Ioc_eq_Icc ha1 h12, measure_union _ measurableSet_Ioc,
      measure_congr (Ioc_ae_eq_Icc (μ := ν))]
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx.2 (not_le.2 hx'.1)
  filter_upwards [ae_all_iff.2 hper] with ω hω u s hu hs
  obtain ⟨n, hn⟩ := exists_nat_ge (u + s)
  exact hω n u s hu hs (by linarith)

end LocLen
end QuantumZipper
