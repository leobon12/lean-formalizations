import QuantumZipper.Proofs.Thm14.ZeroMinusWeld
import QuantumZipper.Proofs.Zipper.B5LRID
import QuantumZipper.Proofs.Zipper.B5ZeroMinus
import QuantumZipper.Proofs.Zipper.ESMLenLRID
import QuantumZipper.Proofs.Zipper.Cor15HullNull
import QuantumZipper.Proofs.RS.RohdeSchrammSimple
import QuantumZipper.Proofs.LQG.RevCouplingReg

/-!
# WIRE-2: discharging the proved blueprint inputs

Wiring only (small proofs by application). Several committed theorems take as hypotheses the
blueprint facts `Blueprint.RohdeSchrammSimple` (Rohde–Schramm, Ann. of Math. 161 (2005), Thm 6.1,
p. 23: SLE_κ is a simple curve for `κ ≤ 4`), `Blueprint.RevCouplingBoundaryMeasureRegular`
(regularity of the reverse coupling boundary measure) and `Cor15Group.Cor15HullNullStmt` (the
dyadic folded circles do not charge the SLE hull, Cor 1.5 (K0)); those are now proved:

* `RS.rohdeSchrammSimple` (`Proofs/RS/RohdeSchrammSimple.lean`),
* `RevCouplingReg.revCouplingBoundaryMeasureRegular` (`Proofs/LQG/RevCouplingReg.lean`),
* `Cor15Group.cor15HullNullStmt` (`Proofs/Zipper/Cor15HullNull.lean`).

This file states the unconditional corollaries (same conclusions, the discharged hypotheses
removed; every remaining hypothesis is unchanged). The proofs are pure applications of the
original theorems with the proved inputs substituted.

Nothing here is new mathematics; no source beyond the above is used.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper

namespace Wire2

/-! ## 1. Theorem 1.4 with Rohde–Schramm simplicity discharged -/

/-- **Theorem 1.4(a)** from Theorem 1.3 alone. -/
theorem theorem1_4a_of_theorem1_3 (h13 : theorem1_3) : theorem1_4a :=
  Thm14Wire.theorem1_4a_of_theorem1_3_rss (h13 := h13) (hRSS := RS.rohdeSchrammSimple)

/-- The field-side input 2 of Theorem 1.4(b): `R_h` determines `0₋`, without hypotheses. -/
theorem zeroMinusOfWeldR (h13 : theorem1_3) : Thm14WDG.ZeroMinusOfWeldR :=
  Thm14WDG.zeroMinusOfWeldR (h13 := h13) (hRSS := RS.rohdeSchrammSimple)

/-- `WeldingDeterminationGraph` from Theorem 1.3 and the remaining field-side input
`WeldRPairingReadable` (`ZeroMinusOfWeldR` discharged). -/
theorem weldingDeterminationGraph_of (h13 : theorem1_3) (hR : Thm14WDG.WeldRPairingReadable) :
    Thm14Determination.WeldingDeterminationGraph :=
  Thm14WDG.weldingDeterminationGraph_of (h13 := h13) (hRSS := RS.rohdeSchrammSimple) (hR := hR)
    (hZ := zeroMinusOfWeldR h13)

/-- **Theorem 1.4(b)** from Theorem 1.3 and the remaining field-side input
`WeldRPairingReadable`. -/
theorem theorem1_4b_of_theorem1_3_pairing (h13 : theorem1_3) (hR : Thm14WDG.WeldRPairingReadable) :
    theorem1_4b :=
  Thm14WDG.theorem1_4b_of_theorem1_3_rss_pairing (h13 := h13) (hRSS := RS.rohdeSchrammSimple) hR

/-! ## 2. B5: LR-ID and its inputs -/

section B5Wrap

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- A.s. `ν₀ = ν_{h⁰}` is atomless, positive on intervals and finite on compacts. -/
theorem ae_nu0_regular (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, (∀ x, qBoundaryMeasure (Real.sqrt κ) (B2.h0f κ T B X ω) {x} = 0) ∧
      (∀ u v : ℝ, u < v → 0 < qBoundaryMeasure (Real.sqrt κ) (B2.h0f κ T B X ω) (Ioo u v)) ∧
      (∀ u v : ℝ, qBoundaryMeasure (Real.sqrt κ) (B2.h0f κ T B X ω) (Icc u v) < ⊤) :=
  B5.ae_nu0_regular (hReg := RevCouplingReg.revCouplingBoundaryMeasureRegular) (hκ := hκ)
    (hκ4 := hκ4) (hT := hT) (hB := hB) (hX := hX) (hind := hind)

/-- A.s. the right side `s ↦ ν_{h⁰}[0₋(T), 0₋(T − s)]` of B5-V vanishes at `0`, is strictly
increasing and continuous on `[0,T]`. -/
theorem ae_lengthRHS_props (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P,
      qBoundaryMeasure (Real.sqrt κ) (B2.h0f κ T B X ω)
          (Icc (zeroMinus (B2.Vr κ T B ω) T) (zeroMinus (B2.Vr κ T B ω) (T - 0))) = 0 ∧
      StrictMonoOn (fun s => qBoundaryMeasure (Real.sqrt κ) (B2.h0f κ T B X ω)
          (Icc (zeroMinus (B2.Vr κ T B ω) T) (zeroMinus (B2.Vr κ T B ω) (T - s)))) (Icc 0 T) ∧
      ContinuousOn (fun s => qBoundaryMeasure (Real.sqrt κ) (B2.h0f κ T B X ω)
          (Icc (zeroMinus (B2.Vr κ T B ω) T) (zeroMinus (B2.Vr κ T B ω) (T - s)))) (Icc 0 T) :=
  B5.ae_lengthRHS_props (hReg := RevCouplingReg.revCouplingBoundaryMeasureRegular)
    (hRSS := RS.rohdeSchrammSimple) (hκ := hκ) (hκ4 := hκ4) (hT := hT) (hB := hB) (hX := hX)
    (hind := hind)

/-- **LR-ID with the length process `lenRHS`, unconditional** (no B5-V). -/
theorem ae_lr_id_rhs (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) (ϖ : Measure ℂ) (δ : ℝ)
    (G : Ω → ℝ → FieldSample × (ℝ → ℝ) → ℝ≥0∞) :
    ∀ᵐ ω ∂P,
      ∫⁻ x in Icc (-δ) 0, {x | realHitTime (B2.Vr κ T B ω) x < ENNReal.ofReal T}.indicator
          (fun x => G ω x (B2.collided κ T B X ω x)) x ∂E1.nuPalm κ T B X ϖ ω =
        ENNReal.ofReal (Real.exp (Real.sqrt κ * -(E1.mReg κ T B X ϖ ω) / 2)) *
          ∫⁻ ℓ in Ioi (0 : ℝ),
            {ℓ | 0 < ESM.lenTime (B5.lenRHS κ T B X ω) ℓ ∧ ESM.lenTime (B5.lenRHS κ T B X ω) ℓ < T ∧
                -δ ≤ zeroMinus (B2.Vr κ T B ω) (T - ESM.lenTime (B5.lenRHS κ T B X ω) ℓ)}.indicator
              (fun ℓ => G ω (zeroMinus (B2.Vr κ T B ω) (T - ESM.lenTime (B5.lenRHS κ T B X ω) ℓ))
                (zipCapDown (Real.sqrt κ) (ESM.lenTime (B5.lenRHS κ T B X ω) ℓ)
                  (B2.cfg κ B X ω))) ℓ :=
  B5.ae_lr_id_rhs (hReg := RevCouplingReg.revCouplingBoundaryMeasureRegular)
    (hRSS := RS.rohdeSchrammSimple) (hκ := hκ) (hκ4 := hκ4) (hT := hT) (hB := hB) (hX := hX)
    (hind := hind) (ϖ := ϖ) (δ := δ) (G := G)

end B5Wrap

/-! ## 3. B5-V sample facts of the reversed driver `V = Vr κ T B ω` -/

theorem ae_zeroMinus_Vr_facts {Ω : Type} [MeasurableSpace Ω] {κ : ℝ} (hκ0 : 0 < κ)
    (hκ4 : κ ≤ 4) {T : ℝ} (hT : 0 < T) (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, zeroMinus (B2.Vr κ T B ω) 0 = 0 ∧ zeroMinus (B2.Vr κ T B ω) T < 0 ∧
      StrictAntiOn (zeroMinus (B2.Vr κ T B ω)) (Icc 0 T) ∧
      ContinuousOn (zeroMinus (B2.Vr κ T B ω)) (Icc 0 T) ∧
      (∀ x ∈ Ioc (zeroMinus (B2.Vr κ T B ω) T) 0,
        realHitTime (B2.Vr κ T B ω) x =
            ENNReal.ofReal (realHitTime (B2.Vr κ T B ω) x).toReal ∧
          (realHitTime (B2.Vr κ T B ω) x).toReal ∈ Icc 0 T ∧
          zeroMinus (B2.Vr κ T B ω) (realHitTime (B2.Vr κ T B ω) x).toReal = x) ∧
      (∀ x ≤ 0, realHitTime (B2.Vr κ T B ω) x < ENNReal.ofReal T ↔
        zeroMinus (B2.Vr κ T B ω) T < x) :=
  B5.ae_zeroMinus_Vr_facts (hRSS := RS.rohdeSchrammSimple) (hκ0 := hκ0) (hκ4 := hκ4)
    (hT := hT) (P := P) (B := B) (hB := hB)

/-! ## 4. E-SM: lengths, adaptedness and LR-ID in level-time coordinates -/

section ESMWrap

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- A.s. `ω ∈ lenGood`. -/
theorem ae_mem_lenGood (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, ω ∈ ESM.lenGood κ T B X :=
  ESM.ae_mem_lenGood (hReg := RevCouplingReg.revCouplingBoundaryMeasureRegular)
    (hRSS := RS.rohdeSchrammSimple) (hκ := hκ) (hκ4 := hκ4) (hT := hT) (hB := hB) (hX := hX)
    (hind := hind)

/-- The E-SM strong Markov identity for the stopping times of the length process. -/
theorem lintegral_levelTime_strongMarkov_lenA {𝓕 : Filtration ℝ≥0 mΩ}
    (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hBc : ∀ ω, Continuous (B · ω)) (hBad : ∀ t, Measurable[𝓕 t] (B t))
    (hindF : ∀ t, Indep (𝓕 t) (MeasurableSpace.comap (StrongMarkov.smPath B (fun _ => t))
      MeasurableSpace.pi) P)
    (hnull : ∀ N : Set Ω, P N = 0 → MeasurableSet[𝓕 0] N)
    (hLad : ∀ s, Measurable[𝓕 s] (ESM.lenMinus κ B X s))
    (hB5V : ∀ s : ℝ≥0, (s : ℝ) ≤ T →
      ∀ᵐ ω ∂P, ESM.lenMinus κ B X s ω = B5.lenRHS κ T B X ω s)
    (μ : Measure ℝ≥0) [SFinite μ]
    {H : ℝ≥0 → Ω → ℝ≥0∞} (hH : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hHT : ∀ ℓ, Measurable[(LengthMarkov.isStoppingTime_levelTime (ESM.continuous_lenA hT.le)
      (ESM.monotone_lenA hT.le) (ESM.adapted_lenA hT.le
        (ae_mem_lenGood hκ hκ4 hT hB hX hind) hnull hLad hB5V)
      T.toNNReal ℓ).measurableSpace] (H ℓ))
    {Ψ : (ℝ → ℝ) → ℝ≥0∞} (hΨ : Measurable Ψ) :
    ∫⁻ ω, ∫⁻ ℓ, {ω | (ℓ : ℝ≥0∞) ≤ ESM.lenA κ T B X T.toNNReal ω}.indicator (H ℓ) ω *
        Ψ (zipCapDown (Real.sqrt κ) (LengthMarkov.levelTime (ESM.lenA κ T B X) T.toNNReal ℓ ω)
          (B2.cfg κ B X ω)).2 ∂μ ∂P =
      (∫⁻ ω, Ψ (drive κ B ω) ∂P) *
        ∫⁻ ω, ∫⁻ ℓ, {ω | (ℓ : ℝ≥0∞) ≤ ESM.lenA κ T B X T.toNNReal ω}.indicator (H ℓ) ω
          ∂μ ∂P :=
  ESM.lintegral_levelTime_strongMarkov_lenA
    (hReg := RevCouplingReg.revCouplingBoundaryMeasureRegular)
    (hRSS := RS.rohdeSchrammSimple) (hκ := hκ) (hκ4 := hκ4) (hT := hT) (hB := hB) (hX := hX)
    (hind := hind) (hBc := hBc) (hBad := hBad) (hindF := hindF) (hnull := hnull) (hLad := hLad)
    (hB5V := hB5V) (μ := μ) (H := H) (hH := hH) (hHT := hHT) (hΨ := hΨ)

/-- **LR-ID with the E-SM stopping times, a.s.** -/
theorem ae_lr_id_levelTime (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) (ϖ : Measure ℂ) (δ : ℝ)
    (G : Ω → ℝ → FieldSample × (ℝ → ℝ) → ℝ≥0∞) :
    ∀ᵐ ω ∂P,
      ∫⁻ x in Icc (-δ) 0, {x | realHitTime (B2.Vr κ T B ω) x < ENNReal.ofReal T}.indicator
          (fun x => G ω x (B2.collided κ T B X ω x)) x ∂E1.nuPalm κ T B X ϖ ω =
        ENNReal.ofReal (Real.exp (Real.sqrt κ * -(E1.mReg κ T B X ϖ ω) / 2)) *
          ∫⁻ ℓ in Ioi (0 : ℝ),
            {ℓ | ENNReal.ofReal ℓ < ESM.lenA κ T B X T.toNNReal ω ∧
                -δ ≤ zeroMinus (B2.Vr κ T B ω)
                  (T - LengthMarkov.levelTime (ESM.lenA κ T B X) T.toNNReal ℓ.toNNReal ω)}.indicator
              (fun ℓ => G ω (zeroMinus (B2.Vr κ T B ω)
                  (T - LengthMarkov.levelTime (ESM.lenA κ T B X) T.toNNReal ℓ.toNNReal ω))
                (zipCapDown (Real.sqrt κ)
                  (LengthMarkov.levelTime (ESM.lenA κ T B X) T.toNNReal ℓ.toNNReal ω)
                  (B2.cfg κ B X ω))) ℓ :=
  ESM.ae_lr_id_levelTime (hReg := RevCouplingReg.revCouplingBoundaryMeasureRegular)
    (hRSS := RS.rohdeSchrammSimple) (hκ := hκ) (hκ4 := hκ4) (hT := hT) (hB := hB) (hX := hX)
    (hind := hind) (ϖ := ϖ) (δ := δ) (G := G)

end ESMWrap

/-! ## 5. Corollary 1.5, positive times, with (K0) discharged -/

section Cor15Wrap

variable {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample)

/-- The field statement of blocker 1 from (R) alone (K0 is proved). -/
theorem cor15RezipFieldStmt_of (hR : Cor15Group.Cor15RezipRegStmt) :
    Cor15Group.Cor15RezipFieldStmt :=
  Cor15Group.cor15RezipFieldStmt_of Cor15Group.cor15HullNullStmt hR

/-- **The welding driver of the unzipped field** (`t > 0`). -/
theorem ae_eqOn_weldDriver_zipCapDown (h13 : theorem1_3) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, EqOn
      (weldDriver (Real.sqrt κ)
        (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)).1 t)
      (B2.vrev (drive κ B ω) t) (Icc 0 t) :=
  Cor15Group.ae_eqOn_weldDriver_zipCapDown (h13 := h13) (hRSS := RS.rohdeSchrammSimple)
    (hκ := hκ) (hκ4 := hκ4) (P := P) (B := B) (X := X) (hB := hB) (hX := hX) (hind := hind)
    (ht := ht)

/-- **Driver half of blocker 1.** A.s. the driver of `Z^CAP_t (Z^CAP_{−t} c)` is `W` on `[0,∞)`. -/
theorem ae_zipCapUp_zipCapDown_snd (h13 : theorem1_3) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, ∀ u : ℝ, 0 ≤ u →
      (zipCapUp (Real.sqrt κ) t
        (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω))).2 u =
      drive κ B ω u :=
  Cor15Group.ae_zipCapUp_zipCapDown_snd (h13 := h13) (hRSS := RS.rohdeSchrammSimple)
    (hκ := hκ) (hκ4 := hκ4) (hB := hB) (hX := hX) (hind := hind) (ht := ht)

/-- **Field of `Z^CAP_t (Z^CAP_{−t} c)`.** -/
theorem ae_zipCapUp_zipCapDown_fst (h13 : theorem1_3) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P,
      (zipCapUp (Real.sqrt κ) t
        (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω))).1 =
      coordChange (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) t)
        (revMapInv (B2.vrev (drive κ B ω) t) t) (Qc (Real.sqrt κ)) :=
  Cor15Group.ae_zipCapUp_zipCapDown_fst (h13 := h13) (hRSS := RS.rohdeSchrammSimple)
    (hκ := hκ) (hκ4 := hκ4) (hB := hB) (hX := hX) (hind := hind) (ht := ht)

/-- **Blocker 1** from Theorem 1.3 and the field statement. -/
theorem ae_configEq_zipCapUp_zipCapDown (h13 : theorem1_3) (hF : Cor15Group.Cor15RezipFieldStmt)
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, ConfigEq
      (zipCapUp (Real.sqrt κ) t
        (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)))
      (ofFun (h0rev κ) + X ω, drive κ B ω) :=
  Cor15Group.ae_configEq_zipCapUp_zipCapDown (h13 := h13) (hRSS := RS.rohdeSchrammSimple)
    (hF := hF) (hκ := hκ) (hκ4 := hκ4) (hB := hB) (hX := hX) (hind := hind) (ht := ht)

/-- **Corollary 1.5 (b) for `s > 0`, `t = −s`.** -/
theorem theorem1_5b_pos_cancel (h13 : theorem1_3) (hF : Cor15Group.Cor15RezipFieldStmt)
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) {s t : ℝ} (hs : 0 < s)
    (hst : s + t = 0) :
    ∀ᵐ ω ∂P, ConfigEq
      (zipCap (Real.sqrt κ) (s + t) (ofFun (h0rev κ) + X ω, drive κ B ω))
      (zipCap (Real.sqrt κ) s (zipCap (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω))) :=
  Cor15Group.theorem1_5b_pos_cancel (h13 := h13) (hRSS := RS.rohdeSchrammSimple) (hF := hF)
    (hκ := hκ) (hκ4 := hκ4) (hB := hB) (hX := hX) (hind := hind) (hs := hs) (hst := hst)

end Cor15Wrap

end Wire2

end QuantumZipper
