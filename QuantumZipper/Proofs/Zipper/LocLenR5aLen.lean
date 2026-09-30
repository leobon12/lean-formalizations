import QuantumZipper.Proofs.Zipper.LocLenR5aStmts
import QuantumZipper.Proofs.Zipper.LocLenB5UPlus
import QuantumZipper.Proofs.Zipper.UnifClColl
import QuantumZipper.Proofs.Zipper.UnifD33Close
import QuantumZipper.Proofs.Zipper.LocLenRules

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R5a (D75): `LenCollidedAllArcStmt` without the tip core

Open-arc copy of `RegUnif.lenCollidedStmt_of_windows` (UnifClColl.lean:65): the left open-arc
length unzipped from `C_u = zipCapDown γ u 𝒵` in capacity time `s` is the `ν_{h⁰_T}`-mass of
the open window `(0₋(T − u), 0₋(T − u − s))`. Inputs, all proved without any tip estimate:

* the field cocycle `RegUnif.capCocycleRegStmt_holds` (the field of `C_u` unzipped by `s` is
  `RegEq` to `h⁰_{u+s}`), and `arcLen_congr`;
* the local window identities `ae_windows_local_of_anchor` (UW without UG, from AC-fam-ext);
* the atomless local limit off the tip `unifLocalStmt_of_extAll` (UnifLocal, R3b);
* `b5UniformArcStmt_holds` (B5UniformArc, R3b) for `u = 0`;
* the open-window exhaustion `B5.measure_Ioo_eq_of_windows`.

Sources: Sheffield, arXiv:1012.4797, proof of Theorem 1.3 (§5, pp. 66–72, lengths of the two
sides of `η[0,t]` read in the fixed chart); Berestycki–Powell arXiv:2404.16642 Def 6.41 p. 229
(open boundary arcs). The Lean bookkeeping is a verbatim copy of the old proof.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open B2 B5 RealLine CaraR RegUnif

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ T : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- **`LenCollidedArcStmt` at a fixed horizon**, without any tip input. -/
theorem lenCollidedArcStmt_holds (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    LenCollidedArcStmt κ T P B X := by
  have hRSS := RS.rohdeSchrammSimple
  have hF := E5.extAllInput_holds κ P B X hκ hκ4 hB hX hind
  filter_upwards [ae_windows_local_of_anchor hκ hκ4 hT hB hX hind
      (anchorWindowAllStmt_of_extAll hκ hκ4 hB hX hind hF T hT),
    unifLocalStmt_of_extAll hκ hκ4 hT hB hX hind hF,
    b5UniformArcStmt_holds κ hκ hκ4 T hT P B X hB hX hind,
    capCocycleRegStmt_holds hB hX hind hT, hB.cont, hB.eval_zero_ae_eq_zero,
    ae_isSimpleCurveHull_revHull_Vr hRSS hκ hκ4.le hT P B hB,
    ae_forall_isSimpleCurveHull_revHull_Vr hRSS hκ hκ4.le P B hB]
    with ω hw hloc hU hcr hc h0 hK hKs
  intro u s hu hs hus
  set W := drive κ B ω with hWdef
  have hWc : Continuous W := Thm14FromThm13.continuous_drive hc
  have hW0 : W 0 = 0 := by simp [hWdef, drive, h0]
  set V := Vr κ T B ω with hVdef
  have hVc : Continuous V := continuous_vrev hWc T
  have hV0 : V 0 = 0 := vrev_zero hT.le
  have hanti := strictAntiOn_zeroMinus hVc hV0 hT hK
  -- the field: `RegEq` with `h⁰_{u+s}`
  obtain ⟨hreg, -, -⟩ := hcr u s hu hs hus
  have hL : (unzipLengthsArc (Real.sqrt κ) (zipCapDown (Real.sqrt κ) u (cfg κ B X ω)) s).1 =
      arcLen (Real.sqrt κ) (h0f κ (u + s) B X ω)
        (sideImages (zipCapDown (Real.sqrt κ) u (cfg κ B X ω)).2 s).1 0 := by
    rw [h0f_eq_unzippedField]
    exact arcLen_congr (funext fun k => funext fun z => hreg k z) _ _
  rw [hL]
  have hdrv : (zipCapDown (Real.sqrt κ) u (cfg κ B X ω)).2 = fun r => W (u + max r 0) - W u :=
    rfl
  rcases hs.eq_or_lt with hs0 | hs0
  · -- `s = 0`
    subst hs0
    rw [hdrv, sideImages_fst_zero_time (by simp), arcLen_self, sub_zero, Ioo_self,
      measure_empty]
  rcases hu.eq_or_lt with hu0 | hu0
  · -- `u = 0`: `B5UniformArcStmt`
    subst hu0
    have hside : sideImages (fun r => W (0 + max r 0) - W 0) s = sideImages W s :=
      ESM.sideImages_congr_drive hs0.le fun r hr => by
        simp [max_eq_left hr.1, hW0]
    have e2 : arcLen (Real.sqrt κ) (h0f κ s B X ω) (sideImages W s).1 0 =
        (unzipLengthsArc (Real.sqrt κ) (cfg κ B X ω) s).1 := by
      rw [h0f_eq_unzippedField]; rfl
    rw [hdrv, hside, zero_add, sub_zero, e2, (hU s ⟨hs0.le, by linarith⟩).1]
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
  have hmono' := hmono.mono (Ioo_subset_Ioo_left hac1.le)
  have hA : Tendsto (realRevMap V (T - u - s)) (𝓝[>] (zeroMinus V (T - u)))
      (𝓝 (realRevMap V (T - u - s) (zeroMinus V (T - u)))) :=
    (continuousAt_realRevMap_zeroMinus hVc hV0 hT hK ht (by linarith)
      (by linarith)).tendsto.mono_left nhdsWithin_le_nhds
  obtain ⟨ν, hν, -⟩ := hloc (u + s) ⟨by linarith, hus⟩
  have hsub : ∀ {p r : ℝ}, r ≤ 0 → Ioo p r ⊆ ({0} : Set ℝ)ᶜ := fun hr z hz hz0 => by
    rw [mem_singleton_iff] at hz0; linarith [hz.2]
  have hwin : ∀ u' v' : ℚ, zeroMinus V (T - u) < u' → (u' : ℝ) < v' →
      (v' : ℝ) < zeroMinus V (T - u - s) →
      qBoundaryMeasure (Real.sqrt κ) (h0f κ T B X ω) (Ioo u' v') =
        ν (Ioo (realRevMap V (T - u - s) u') (realRevMap V (T - u - s) v')) := by
    intro u' v' h1 h2 h3
    have := hw (u + s) ⟨by linarith, hus⟩ u' v' (hac1.trans h1) h2 (by rw [e]; exact h3)
    rw [e] at this
    rw [this, arcLen_eq_of_isVagueLimitOnR hν (hsub
      (lt_of_strictMonoOn_tendsto_left hmono' hC ⟨h1.trans h2, h3⟩).le)]
  rw [arcLen_eq_of_isVagueLimitOnR hν (hsub le_rfl)]
  exact (measure_Ioo_eq_of_windows hcc' hmono' hA hC hwin).symm

/-- **`LenCollidedAllArcStmt` PROVED** (no tip core, no global boundary limit). -/
theorem lenCollidedAllArcStmt_holds : LenCollidedAllArcStmt :=
  fun _ _ _ _ _ _ _ _ hκ hκ4 hT hB hX hind => lenCollidedArcStmt_holds hκ hκ4 hT hB hX hind

end LocLen
end QuantumZipper
