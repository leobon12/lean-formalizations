import QuantumZipper.Proofs.Zipper.E1TransferM4Main
import QuantumZipper.Proofs.Zipper.E1Main

/-!
# E1-TR and E1, unconditional (given B3(a))

`handoff/E1-TR.md`, `handoff/E1-PLAN.md` (nodes E1-TR and E1).

* `Hf0_eq_Hf1`, `ae_trInt_eq_Hf1_left`, `ae_trInt_eq_Hf1_right`: the representation of both
  transfer integrands through `(lawData (N ·), (V^t, W⁰))` with the integrand `Hf1` (driver read
  through the measurable continuous version `M4.extC`; see `E1TransferM4Main` for why `Hf0` is not
  suitable);
* `e1_tr_of_aemeasurable_Hf1`: E1-TR from a.e.-measurability of `Hf1` (as
  `e1_tr_of_aemeasurable`);
* **`e1_tr`**: E1-TR exactly as in `handoff/E1-PLAN.md` (with the measurability hypotheses on
  `Ψ`, `Φ`; the plan's `0 < δ` is not needed);
* **`e1_main`**: E1 (`e1_main_of_tr … (e1_tr …)`).

Paper: Sheffield, arXiv:1012.4797, Theorem 4.5 (p. 51), Lemma 5.6 with its proof (pp. 66–68),
§5.2 (pp. 57–59). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E1

open B2 CharFun UnzipInvariance UnzipFull CoordsFull B1Full M4

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T t : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}

omit [MeasurableSpace Ω] in
/-- Along the data, `Hf0 = Hf1` whenever `B` is continuous. -/
theorem Hf0_eq_Hf1 (ht : 0 ≤ t) (δ : ℝ) (Ψ : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞)
    (Φ : (ℕ → ℝ) → ℝ≥0∞) {ω : Ω} (hc : Continuous fun s => B s ω)
    (l : (ℕ → ℝ) × (TestFun H → ℝ)) :
    Hf0 κ t δ ϖ Ψ Φ (l, (Vstop κ T t B ω, W0p κ T B ω)) =
      Hf1 κ t δ ht ϖ Ψ Φ (l, (Vstop κ T t B ω, W0p κ T B ω)) := by
  have hV : Continuous (Vr κ T B ω) := continuous_vrev (drive_continuous hc) T
  have hS : Continuous (stopDrive (Vstop κ T t B ω, W0p κ T B ω)) := by
    unfold stopDrive Vstop
    exact hV.comp ((NNReal.continuous_coe.comp continuous_real_toNNReal).min continuous_const)
  refine trInt_congr_drive δ Ψ Φ hS (continuous_Wof 1 t ht _) ht (fun s hs => ?_) _ _
  rw [eqOn_Wof_extC_Vstop ht hc hs]
  simp only [stopDrive, Vstop, Real.coe_toNNReal _ hs.1, min_eq_left hs.2]

/-- **TR-MEAS, left representation with `Hf1`.** -/
theorem ae_trInt_eq_Hf1_left (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) (ht : 0 ≤ t) (htT : t ≤ T) (hϖ : IsNormalizer ϖ) (δ : ℝ)
    (Ψ : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞) (Φ : (ℕ → ℝ) → ℝ≥0∞) :
    ∀ᵐ ω ∂P, trInt κ t δ ϖ Ψ Φ (Vr κ T B ω) (Vstop κ T t B ω, W0p κ T B ω) (Yf κ T t B X ω) =
      Hf1 κ t δ ht ϖ Ψ Φ (lawData (fun ω => nrm (Yf κ T t B X ω)) ω,
        (Vstop κ T t B ω, W0p κ T B ω)) := by
  filter_upwards [ae_trInt_eq_Hf0_left hB hX hind ht htT hϖ δ Ψ Φ, hB.cont] with ω h hc
  rw [h, Hf0_eq_Hf1 ht δ Ψ Φ hc]

/-- **TR-MEAS, right representation with `Hf1`.** -/
theorem ae_trInt_eq_Hf1_right (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (ht : 0 ≤ t) (hϖ : IsNormalizer ϖ) (δ : ℝ)
    (Ψ : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞) (Φ : (ℕ → ℝ) → ℝ≥0∞) :
    ∀ᵐ ω ∂P, ∀ᵐ ω' ∂P, trInt κ t δ ϖ Ψ Φ (Vr κ T B ω) (Vstop κ T t B ω, W0p κ T B ω)
        (ofFun (h0rev κ) + X ω') =
      Hf1 κ t δ ht ϖ Ψ Φ (lawData (fun ω => nrm (ofFun (h0rev κ) + X ω)) ω',
        (Vstop κ T t B ω, W0p κ T B ω)) := by
  filter_upwards [ae_trInt_eq_Hf0_right (T := T) (B := B) hB hX ht hϖ δ Ψ Φ, hB.cont] with ω h hc
  filter_upwards [h] with ω' h'
  rw [h', Hf0_eq_Hf1 ht δ Ψ Φ hc]

/-- **E1-TR from a.e.-measurability of `Hf1`** (the proof of `e1_tr_of_aemeasurable` with `Hf1`). -/
theorem e1_tr_of_aemeasurable_Hf1 (hReg : Blueprint.RevCouplingBoundaryMeasureRegular)
    (hκ : 0 < κ) (hκ4 : κ < 4) (ht : 0 ≤ t) (htT : t < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hϖ : IsNormalizer ϖ) (δ : ℝ) (Ψ : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞)
    (Φ : (ℕ → ℝ) → ℝ≥0∞)
    (hM : AEMeasurable (Hf1 κ t δ ht ϖ Ψ Φ)
      ((P.map fun ω => lawData (fun ω => nrm (ofFun (h0rev κ) + X ω)) ω).prod
        (P.map fun ω => (Vstop κ T t B ω, W0p κ T B ω)))) :
    ∫⁻ ω, ∫⁻ x in Icc (-δ) 0, {x | IsLive (Vr κ T B ω) t x}.indicator (fun x =>
        Ψ x (Vstop κ T t B ω, W0p κ T B ω) *
          Φ (CoordsFull.coordsFull (addConst (Yf κ T t B X ω) (-(mReg κ T B X ϖ ω))))) x
        ∂nuPalm κ T B X ϖ ω ∂P =
      ∫⁻ ω, ∫⁻ ω', ∫⁻ x in Icc (-δ) 0, Ψ x (Vstop κ T t B ω, W0p κ T B ω) *
          Φ (CoordsFull.coordsFull (addConst (ofFun (h0rev κ) + X ω')
            (-(mFix κ (Vr κ T B ω) t ϖ (X ω')))))
        ∂qBoundaryMeasureOn (Real.sqrt κ) (addConst (hFix κ (Vr κ T B ω) t (X ω'))
            (-(mFix κ (Vr κ T B ω) t ϖ (X ω')))) (liveNeg (Vr κ T B ω) t) ∂P ∂P := by
  obtain ⟨hI, hL, -⟩ := b2_markov hκ hB hX hind ht htT
  set L := fun ω => lawData (fun ω => nrm (Yf κ T t B X ω)) ω with hLdef
  set L0 := fun ω => lawData (fun ω => nrm (ofFun (h0rev κ) + X ω)) ω with hL0def
  set D := fun ω => (Vstop κ T t B ω, W0p κ T B ω) with hDdef
  have hg : Measurable (Prod.map (id : (ℕ → ℝ) × (TestFun H → ℝ) → _) (splitAt t)) :=
    measurable_id.prodMap (measurable_splitAt t)
  have hfg : AEMeasurable (fun ω => (L ω, D ω)) P := by
    rw [hLdef, hDdef, data_eq_comp ht htT.le]
    exact hg.comp_aemeasurable (aemeasurable_data_unzip hB hX hind (sub_pos.2 htT).le)
  have hL0m : AEMeasurable L0 P := (aemeasurable_data0 (κ := κ) hB hX).fst
  have hDm : AEMeasurable D P := hfg.snd
  have hprod : P.map (fun ω => (L ω, D ω)) = (P.map L0).prod (P.map D) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hfg.fst hfg.snd).1 hI, hL]
  obtain ⟨Hf, hHf, hae⟩ := hM
  refine e1_tr_of_rep hReg hκ hκ4 ht htT hB hX hind hϖ δ Ψ Φ Hf hHf ?_ ?_
  · rw [← hprod] at hae
    filter_upwards [ae_trInt_eq_Hf1_left hB hX hind ht htT.le hϖ δ Ψ Φ,
      ae_of_ae_map hfg hae] with ω h1 h2
    rw [h1]; exact h2
  · set L0' := hL0m.mk with hL0'
    set D' := hDm.mk with hD'
    have hm1 : P.map L0 = P.map L0' := Measure.map_congr hL0m.ae_eq_mk
    have hm2 : P.map D = P.map D' := Measure.map_congr hDm.ae_eq_mk
    have hlaw : (P.prod P).map (fun q => (L0' q.2, D' q.1)) = (P.map L0).prod (P.map D) := by
      rw [hm1, hm2]
      calc (P.prod P).map (fun q => (L0' q.2, D' q.1)) =
            ((P.prod P).map (Prod.map D' L0')).map Prod.swap := by
            rw [Measure.map_map measurable_swap (hDm.measurable_mk.prodMap hL0m.measurable_mk)]
            rfl
        _ = ((P.map D').prod (P.map L0')).map Prod.swap := by
            rw [Measure.map_prod_map _ _ hDm.measurable_mk hL0m.measurable_mk]
        _ = (P.map L0').prod (P.map D') := Measure.prod_swap
    rw [← hlaw] at hae
    have h2 := Measure.ae_ae_of_ae_prod (ae_of_ae_map
      ((hL0m.measurable_mk.comp measurable_snd).prodMk
        (hDm.measurable_mk.comp measurable_fst)).aemeasurable hae)
    filter_upwards [h2, hDm.ae_eq_mk, ae_trInt_eq_Hf1_right (T := T) hB hX ht hϖ δ Ψ Φ]
      with ω h hDω hR
    filter_upwards [h, hL0m.ae_eq_mk, hR] with ω' h' hLω' hR'
    rw [hR']
    have e : (L0 ω', D ω) = (L0' ω', D' ω) := by rw [hLω', hDω]
    exact (congrArg (Hf1 κ t δ ht ϖ Ψ Φ) e).trans (h'.trans (congrArg Hf e.symm))

/-- **E1-TR** (`handoff/E1-PLAN.md`), unconditional given B3(a) (`hReg`). -/
theorem e1_tr (hReg : Blueprint.RevCouplingBoundaryMeasureRegular)
    (hκ : 0 < κ) (hκ4 : κ < 4) (ht : 0 ≤ t) (htT : t < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hϖ : IsNormalizer ϖ) (δ : ℝ) {Ψ : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞}
    {Φ : (ℕ → ℝ) → ℝ≥0∞} (hΨ : Measurable (Function.uncurry Ψ)) (hΦ : Measurable Φ) :
    ∫⁻ ω, ∫⁻ x in Icc (-δ) 0, {x | IsLive (Vr κ T B ω) t x}.indicator (fun x =>
        Ψ x (Vstop κ T t B ω, W0p κ T B ω) *
          Φ (CoordsFull.coordsFull (addConst (Yf κ T t B X ω) (-(mReg κ T B X ϖ ω))))) x
        ∂nuPalm κ T B X ϖ ω ∂P =
      ∫⁻ ω, ∫⁻ ω', ∫⁻ x in Icc (-δ) 0, Ψ x (Vstop κ T t B ω, W0p κ T B ω) *
          Φ (CoordsFull.coordsFull (addConst (ofFun (h0rev κ) + X ω')
            (-(mFix κ (Vr κ T B ω) t ϖ (X ω')))))
        ∂qBoundaryMeasureOn (Real.sqrt κ) (addConst (hFix κ (Vr κ T B ω) t (X ω'))
            (-(mFix κ (Vr κ T B ω) t ϖ (X ω')))) (liveNeg (Vr κ T B ω) t) ∂P ∂P :=
  e1_tr_of_aemeasurable_Hf1 hReg hκ hκ4 ht htT hB hX hind hϖ δ Ψ Φ
    (aemeasurable_Hf1 hReg hκ hκ4 ht htT hB hX hind hϖ δ hΨ hΦ)

end E1
end QuantumZipper
