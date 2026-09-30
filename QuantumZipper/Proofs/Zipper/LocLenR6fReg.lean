import QuantumZipper.Proofs.Zipper.LocLenR6fDefs
import QuantumZipper.Proofs.Zipper.LocLenB5UPlus
import QuantumZipper.Proofs.Wire2
import QuantumZipper.Proofs.Thm18.G4BSideGeom
import QuantumZipper.Proofs.Zipper.UnifUOPlus

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75, task R6f (3): regularity of the `Γ⁰` open-arc lengths (`LenRegCfgArcStmt`, proved)

In the `Γ⁰` picture the open-arc lengths of `η[0,s]` are, in the fixed chart `T`, the masses
`ν_T(0₋(T), 0₋(T−s))` and `ν_T(0₊(T−s), 0₊(T))` (`B5UniformArcStmt`, proved outright,
Sheffield arXiv:1012.4797 p. 56; Berestycki–Powell arXiv:2404.16642 Def 8.12 p. 281), where
`ν_T` is atomless, positive on intervals and finite on compacts (L1,
`RevCouplingReg.revCouplingBoundaryMeasureRegular`), and `0₋`, `0₊` are continuous and strictly
monotone on `[0,T]` (Rohde–Schramm, `B5.ae_zeroMinus_Vr_facts`; the `0₊` side by the reflection
`0₊^V = −0₋^{−V}`). Hence the open-arc lengths are finite, continuous and vanish at `0`
(`B5.lengthRHS_props`, the length-process properties of the right side of B5-V). Gluing over
the horizons `T = n + 1` gives `lenRegCfgArc_holds : LenRegCfgArcStmt`. No tip input.

Own bookkeeping (the paper states these facts without proof, p. 70).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

/-- One side at a fixed horizon (deterministic). -/
theorem side_reg_minus {ν : Measure ℝ} (hatom : ∀ x, ν {x} = 0)
    (hpos : ∀ u v, u < v → 0 < ν (Ioo u v)) (hfin : ∀ u v, ν (Icc u v) < ⊤) {T : ℝ}
    (hT : 0 < T) {z : ℝ → ℝ} (hz : StrictAntiOn z (Icc 0 T)) (hzc : ContinuousOn z (Icc 0 T))
    (hz0 : z 0 = 0) :
    ν (Ioo (z T) (z (T - 0))) = 0 ∧
      (∀ s ∈ Icc 0 T, ν (Ioo (z T) (z (T - s))) ≠ ⊤) ∧
      ContinuousOn (fun s => (ν (Ioo (z T) (z (T - s)))).toReal) (Icc 0 T) ∧
      StrictMonoOn (fun s => ν (Ioo (z T) (z (T - s)))) (Icc 0 T) := by
  obtain ⟨h0, hsm, hc⟩ := B5.lengthRHS_props hatom hpos (hfin _ _) hT hz hzc rfl hz0
  have e : ∀ s, ν (Ioo (z T) (z (T - s))) = ν (Icc (z T) (z (T - s))) := fun s =>
    (measure_Icc_eq_Ioo_of_noAtoms (hatom _) (hatom _)).symm
  simp only [e]
  exact ⟨h0, fun s _ => (hfin _ _).ne,
    ENNReal.continuousOn_toReal.comp hc fun s _ => (hfin _ _).ne, hsm⟩

/-- Reflection of a measure on `ℝ` (the push-forward by `x ↦ −x`) on intervals. -/
theorem map_neg_Ioo (ν : Measure ℝ) (u v : ℝ) :
    ν.map (fun x => -x) (Ioo u v) = ν (Ioo (-v) (-u)) := by
  rw [Measure.map_apply measurable_neg measurableSet_Ioo]
  congr 1
  ext x
  simp only [mem_preimage, mem_Ioo]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem map_neg_Icc (ν : Measure ℝ) (u v : ℝ) :
    ν.map (fun x => -x) (Icc u v) = ν (Icc (-v) (-u)) := by
  rw [Measure.map_apply measurable_neg measurableSet_Icc]
  congr 1
  ext x
  simp only [mem_preimage, mem_Icc]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem map_neg_singleton (ν : Measure ℝ) (x : ℝ) :
    ν.map (fun x => -x) {x} = ν {-x} := by
  rw [Measure.map_apply measurable_neg (measurableSet_singleton x)]
  congr 1
  ext y
  simp only [mem_preimage, mem_singleton_iff]
  constructor <;> intro h <;> linarith

/-- **Gluing local continuity over the horizons** (deterministic). -/
theorem continuousOn_Ici_of_horizons {L : ℝ → ℝ≥0∞} {R : ℕ → ℝ → ℝ≥0∞}
    (hLR : ∀ n : ℕ, ∀ s ∈ Icc (0 : ℝ) ((n : ℝ) + 1), L s = R n s)
    (hc : ∀ n : ℕ, ContinuousOn (fun s => (R n s).toReal) (Icc 0 ((n : ℝ) + 1))) :
    ContinuousOn (fun s => (L s).toReal) (Ici 0) := by
  intro t ht
  obtain ⟨n, hn⟩ := exists_nat_gt t
  have hT : t < (n : ℝ) + 1 := by linarith
  have hmem : t ∈ Icc (0 : ℝ) ((n : ℝ) + 1) := ⟨ht, hT.le⟩
  have h1 : ContinuousWithinAt (fun s => (L s).toReal) (Icc 0 ((n : ℝ) + 1)) t :=
    (hc n t hmem).congr (fun s hs => by simp only [hLR n s hs]) (by simp only [hLR n t hmem])
  refine h1.mono_of_mem_nhdsWithin ?_
  refine mem_of_superset (inter_mem_nhdsWithin (Ici (0 : ℝ)) (Iio_mem_nhds hT)) ?_
  rintro s ⟨hs1, hs2⟩
  exact ⟨hs1, (mem_Iio.1 hs2).le⟩

variable {κ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- Both sides at one horizon, a.s. -/
theorem ae_regArc_horizon (hκ : 0 < κ) (hκ4 : κ < 4) {T : ℝ} (hT : 0 < T)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hI : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, ∃ Rm Rp : ℝ → ℝ≥0∞,
      (∀ s ∈ Icc 0 T, (unzipLengthsArc (Real.sqrt κ) (B2.cfg κ B X ω) s).1 = Rm s ∧
        (unzipLengthsArc (Real.sqrt κ) (B2.cfg κ B X ω) s).2 = Rp s) ∧
      Rm 0 = 0 ∧ Rp 0 = 0 ∧ (∀ s ∈ Icc 0 T, Rm s ≠ ⊤ ∧ Rp s ≠ ⊤) ∧
      ContinuousOn (fun s => (Rm s).toReal) (Icc 0 T) ∧
      ContinuousOn (fun s => (Rp s).toReal) (Icc 0 T) ∧ StrictMonoOn Rm (Icc 0 T) := by
  have hB' : IsBrownianReal (RegUnif.negB B) P := hB.neg
  filter_upwards [b5UniformArcStmt_holds κ hκ hκ4 T hT P B X hB hX hI,
    B5.ae_nu0_regular RevCouplingReg.revCouplingBoundaryMeasureRegular hκ hκ4 hT hB hX hI,
    B5.ae_zeroMinus_Vr_facts RS.rohdeSchrammSimple hκ hκ4.le hT P B hB,
    B5.ae_zeroMinus_Vr_facts RS.rohdeSchrammSimple hκ hκ4.le hT P _ hB',
    hB.cont] with ω hU hν hzm hzp hc
  obtain ⟨hatom, hpos, hfin⟩ := hν
  obtain ⟨hz0, -, hanti, hzc, -, -⟩ := hzm
  obtain ⟨hz0', -, hanti', hzc', -, -⟩ := hzp
  set ν := qBoundaryMeasure (Real.sqrt κ) (B2.h0f κ T B X ω) with hνdef
  set V := B2.Vr κ T B ω with hV
  have hVc : Continuous V := by
    rw [hV]
    exact B2.continuous_vrev (Thm14FromThm13.continuous_drive hc) T
  have hV' : B2.Vr κ T (RegUnif.negB B) ω = -V := by
    simp only [hV, B2.Vr, RegUnif.drive_negB, Thm18Asm.G4Core.vrev_neg]
  rw [hV'] at hz0' hanti' hzc'
  -- the plus side as a minus side for the reflected measure
  have hzp_eq : ∀ r, 0 ≤ r → zeroPlus V r = -zeroMinus (-V) r := fun r hr =>
    Thm18Asm.G4Core.zeroPlus_eq_neg_zeroMinus_neg hVc hr
  set ν' := ν.map (fun x => -x) with hν'
  have hatom' : ∀ x, ν' {x} = 0 := fun x => by rw [hν', map_neg_singleton]; exact hatom _
  have hpos' : ∀ u v, u < v → 0 < ν' (Ioo u v) := fun u v huv => by
    rw [hν', map_neg_Ioo]; exact hpos _ _ (by linarith)
  have hfin' : ∀ u v, ν' (Icc u v) < ⊤ := fun u v => by rw [hν', map_neg_Icc]; exact hfin _ _
  obtain ⟨m0, mfin, mc, msm⟩ := side_reg_minus hatom hpos hfin hT hanti hzc hz0
  obtain ⟨p0, pfin, pc, -⟩ := side_reg_minus hatom' hpos' hfin' hT hanti' hzc' hz0'
  have hTs : ∀ s ∈ Icc 0 T, 0 ≤ T - s := fun s hs => by linarith [hs.2]
  have ep : ∀ s ∈ Icc 0 T, ν (Ioo (zeroPlus V (T - s)) (zeroPlus V T)) =
      ν' (Ioo (zeroMinus (-V) T) (zeroMinus (-V) (T - s))) := fun s hs => by
    rw [hν', map_neg_Ioo, hzp_eq _ (hTs s hs), hzp_eq _ hT.le]
  refine ⟨fun s => ν (Ioo (zeroMinus V T) (zeroMinus V (T - s))),
    fun s => ν' (Ioo (zeroMinus (-V) T) (zeroMinus (-V) (T - s))),
    fun s hs => ⟨(hU s hs).1, (hU s hs).2.trans (ep s hs)⟩, ?_, ?_,
    fun s hs => ⟨mfin s hs, pfin s hs⟩, mc, pc, msm⟩
  · simp
  · simp

/-- **`LenRegCfgArcStmt` holds** (no tip input). -/
theorem lenRegCfgArc_holds : LenRegCfgArcStmt := by
  intro κ Ω _ P _ B X hκ hκ4 hB hX hI
  have hall := ae_all_iff.2 fun n : ℕ =>
    ae_regArc_horizon (T := (n : ℝ) + 1) hκ hκ4 (by positivity) hB hX hI
  filter_upwards [hall] with ω h
  choose Rm Rp hR hm0 hp0 hfin hcm hcp _hsm using h
  refine ⟨fun t ht => ?_, continuousOn_Ici_of_horizons (fun n s hs => (hR n s hs).1) hcm, ?_,
    continuousOn_Ici_of_horizons (fun n s hs => (hR n s hs).2) hcp, ?_⟩
  · obtain ⟨n, hn⟩ := exists_nat_gt t
    have hmem : t ∈ Icc (0 : ℝ) ((n : ℝ) + 1) := ⟨ht, by linarith⟩
    rw [(hR n t hmem).1, (hR n t hmem).2]
    exact hfin n t hmem
  · rw [(hR 0 0 ⟨le_rfl, by positivity⟩).1]; exact hm0 0
  · rw [(hR 0 0 ⟨le_rfl, by positivity⟩).2]; exact hp0 0

/-- **`LenStrictMonoCfgArcStmt` holds**: in the `Γ⁰` picture the open-arc length `L⁻` is
strictly increasing (`ν_T` charges every interval and `0₋` is strictly decreasing). -/
theorem lenStrictMonoCfgArc_holds : LenStrictMonoCfgArcStmt := by
  intro κ Ω _ P _ B X hκ hκ4 hB hX hI
  have hall := ae_all_iff.2 fun n : ℕ =>
    ae_regArc_horizon (T := (n : ℝ) + 1) hκ hκ4 (by positivity) hB hX hI
  filter_upwards [hall] with ω h
  choose Rm Rp hR _h1 _h2 _h3 _h4 _h5 hsm using h
  intro s hs t ht hst
  obtain ⟨n, hn⟩ := exists_nat_gt t
  have hsn : s ∈ Icc (0 : ℝ) ((n : ℝ) + 1) := ⟨hs, by linarith⟩
  have htn : t ∈ Icc (0 : ℝ) ((n : ℝ) + 1) := ⟨ht, by linarith⟩
  show (unzipLengthsArc _ _ s).1 < (unzipLengthsArc _ _ t).1
  rw [(hR n s hsn).1, (hR n t htn).1]
  exact hsm n hsn htn hst

end LocLen
end QuantumZipper
