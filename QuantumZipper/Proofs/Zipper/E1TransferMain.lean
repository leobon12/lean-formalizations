import QuantumZipper.Proofs.Zipper.E1Transfer
import QuantumZipper.Proofs.Zipper.E1NuExist
import QuantumZipper.Proofs.Zipper.B2Uncond
import QuantumZipper.Proofs.Zipper.E1TransferMeas

/-!
# E1-TR: the left side as an integral of `trInt`, and the law step (TR-LAW)

`handoff/E1-PLAN.md`, node E1-TR. Paper: Sheffield, arXiv:1012.4797, Lemma 5.6 and its proof
(pp. 66–68: "given `f_t`, `h₀ = h̃ ∘ f_t + ĥ_t`"), §5.2 (pp. 57–59), Theorem 4.5 (p. 51).

* `lintegral_lhs_eq_trInt`: the left side of E1-TR is `∫⁻ ω, trInt … (Vr ω) (V^t, W⁰) (Y_t ω)`
  (pathwise part `E1.lhs_integrand_eq`, B2(b) `B2.b2_coordsFull_eq`, `B2.b2_evalReg_split`, and
  the existence of `ν` from NU-EX, `ae_exists_isVagueLimitR_nuPalm`).
* `lintegral_transfer_of_rep` (TR-LAW): if an integrand on the left is a.s. a measurable function
  `H` of `(lawData (N Y_t), (V^t, W⁰))` and the integrand on the right is, for a.e. `ω` and a.e.
  `ω'`, `H (lawData (N (𝔥₀ + X)) ω', (V^t, W⁰) ω)`, the two integrals agree (B2(b):
  `B2.b2_markov`, the Markov property at time `t`; then Tonelli). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E1

open B2 CharFun UnzipInvariance UnzipFull B1Full

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T t : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}

/-- **E1-TR, left side.** The left side of E1-TR is the integral of `trInt` at `(V, (V^t, W⁰), Y_t)`. -/
theorem lintegral_lhs_eq_trInt (hReg : Blueprint.RevCouplingBoundaryMeasureRegular)
    (hκ : 0 < κ) (hκ4 : κ < 4) (ht : 0 ≤ t) (htT : t < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) (hϖ : IsNormalizer ϖ)
    (δ : ℝ) (Ψ : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞) (Φ : (ℕ → ℝ) → ℝ≥0∞) :
    ∫⁻ ω, ∫⁻ x in Icc (-δ) 0, {x | IsLive (Vr κ T B ω) t x}.indicator (fun x =>
        Ψ x (Vstop κ T t B ω, W0p κ T B ω) *
          Φ (CoordsFull.coordsFull (addConst (Yf κ T t B X ω) (-(mReg κ T B X ϖ ω))))) x
        ∂nuPalm κ T B X ϖ ω ∂P =
      ∫⁻ ω, trInt κ t δ ϖ Ψ Φ (Vr κ T B ω) (Vstop κ T t B ω, W0p κ T B ω) (Yf κ T t B X ω)
        ∂P := by
  haveI := hϖ.prob
  obtain ⟨K, hK, hKH, hϖK⟩ := hϖ.cpt
  obtain ⟨α, C, hα, hF⟩ := hϖ.frost
  have hT : 0 < T := ht.trans_lt htT
  refine lintegral_congr_ae ?_
  filter_upwards [b2_coordsFull_eq (κ := κ) hB hX hind ht htT.le,
    b2_evalReg_split (κ := κ) hB hX hind ht htT.le hK hKH hϖK hF hα,
    ae_exists_isVagueLimitR_nuPalm hReg hκ hκ4 hT hB hX hind ϖ, hB.cont] with ω hcf hm hex hc
  exact lhs_integrand_eq hc hT.le δ Ψ Φ _ hcf hex hm

/-- **TR-LAW.** Transfer of an integral of a functional of `(lawData (N Y_t), (V^t, W⁰))` to the
product of the laws (Markov property B2(b) and Tonelli). -/
theorem lintegral_transfer_of_rep (hκ : 0 < κ) (ht : 0 ≤ t) (htT : t < T)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (Hf : ((ℕ → ℝ) × (TestFun H → ℝ)) × ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) → ℝ≥0∞) (hHf : Measurable Hf)
    {G : Ω → ℝ≥0∞} {G' : Ω → Ω → ℝ≥0∞}
    (hl : ∀ᵐ ω ∂P, G ω = Hf (lawData (fun ω => nrm (Yf κ T t B X ω)) ω,
      (Vstop κ T t B ω, W0p κ T B ω)))
    (hr : ∀ᵐ ω ∂P, ∀ᵐ ω' ∂P, G' ω ω' = Hf (lawData (fun ω => nrm (ofFun (h0rev κ) + X ω)) ω',
      (Vstop κ T t B ω, W0p κ T B ω))) :
    ∫⁻ ω, G ω ∂P = ∫⁻ ω, ∫⁻ ω', G' ω ω' ∂P ∂P := by
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
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hfg.fst hfg.snd).1 hI
  have hin : Measurable fun d => ∫⁻ l, Hf (l, d) ∂(P.map L0) :=
    hHf.lintegral_prod_left'
  calc ∫⁻ ω, G ω ∂P = ∫⁻ ω, Hf (L ω, D ω) ∂P := lintegral_congr_ae hl
    _ = ∫⁻ p, Hf p ∂(P.map fun ω => (L ω, D ω)) :=
        (lintegral_map' hHf.aemeasurable hfg).symm
    _ = ∫⁻ d, ∫⁻ l, Hf (l, d) ∂(P.map L0) ∂(P.map D) := by
        rw [hprod, hL, lintegral_prod_symm _ hHf.aemeasurable]
    _ = ∫⁻ ω, ∫⁻ l, Hf (l, D ω) ∂(P.map L0) ∂P := lintegral_map' hin.aemeasurable hfg.snd
    _ = ∫⁻ ω, ∫⁻ ω', Hf (L0 ω', D ω) ∂P ∂P := by
        refine lintegral_congr fun ω => ?_
        exact lintegral_map' (hHf.comp (measurable_id.prodMk measurable_const)).aemeasurable hL0m
    _ = ∫⁻ ω, ∫⁻ ω', G' ω ω' ∂P ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hr] with ω h
        exact (lintegral_congr_ae h).symm

/-- `trInt` reads the field `y` only through `coordsFull y` (`evalReg` and `coordChange` read
`avgReg`, which reads `coordsFull`). -/
theorem trInt_congr_coordsFull (δ : ℝ) (Ψ : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞)
    (Φ : (ℕ → ℝ) → ℝ≥0∞) (v : ℝ → ℝ) (d : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) {y y' : FieldSample}
    (h : CoordsFull.coordsFull y = CoordsFull.coordsFull y') :
    trInt κ t δ ϖ Ψ Φ v d y = trInt κ t δ ϖ Ψ Φ v d y' := by
  have e1 : evalReg y = evalReg y' := funext (evalReg_congr_coordsFull h)
  have e2 : coordChange y = coordChange y' := by
    funext F Q μ
    simp only [coordChange, e1]
  unfold trInt
  rw [e1, e2, coordsFull_addConst_congr h]

/-- **E1-TR from a measurable representation (TR-MEAS).** If the integrand `trInt` is, on the
left, a.s. a measurable function `Hf` of `(lawData (N Y_t), (V^t, W⁰))` and, on the right, for
a.e. `ω` and a.e. `ω'`, the same function of `(lawData (N (𝔥₀ + X)) ω', (V^t, W⁰) ω)`, then E1-TR
holds (in exactly the form of `handoff/E1-PLAN.md`). -/
theorem e1_tr_of_rep (hReg : Blueprint.RevCouplingBoundaryMeasureRegular)
    (hκ : 0 < κ) (hκ4 : κ < 4) (ht : 0 ≤ t) (htT : t < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) (hϖ : IsNormalizer ϖ)
    (δ : ℝ) (Ψ : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞) (Φ : (ℕ → ℝ) → ℝ≥0∞)
    (Hf : ((ℕ → ℝ) × (TestFun H → ℝ)) × ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) → ℝ≥0∞) (hHf : Measurable Hf)
    (hl : ∀ᵐ ω ∂P, trInt κ t δ ϖ Ψ Φ (Vr κ T B ω) (Vstop κ T t B ω, W0p κ T B ω)
      (Yf κ T t B X ω) = Hf (lawData (fun ω => nrm (Yf κ T t B X ω)) ω,
        (Vstop κ T t B ω, W0p κ T B ω)))
    (hr : ∀ᵐ ω ∂P, ∀ᵐ ω' ∂P, trInt κ t δ ϖ Ψ Φ (Vr κ T B ω) (Vstop κ T t B ω, W0p κ T B ω)
      (ofFun (h0rev κ) + X ω') = Hf (lawData (fun ω => nrm (ofFun (h0rev κ) + X ω)) ω',
        (Vstop κ T t B ω, W0p κ T B ω))) :
    ∫⁻ ω, ∫⁻ x in Icc (-δ) 0, {x | IsLive (Vr κ T B ω) t x}.indicator (fun x =>
        Ψ x (Vstop κ T t B ω, W0p κ T B ω) *
          Φ (CoordsFull.coordsFull (addConst (Yf κ T t B X ω) (-(mReg κ T B X ϖ ω))))) x
        ∂nuPalm κ T B X ϖ ω ∂P =
      ∫⁻ ω, ∫⁻ ω', ∫⁻ x in Icc (-δ) 0, Ψ x (Vstop κ T t B ω, W0p κ T B ω) *
          Φ (CoordsFull.coordsFull (addConst (ofFun (h0rev κ) + X ω')
            (-(mFix κ (Vr κ T B ω) t ϖ (X ω')))))
        ∂qBoundaryMeasureOn (Real.sqrt κ) (addConst (hFix κ (Vr κ T B ω) t (X ω'))
            (-(mFix κ (Vr κ T B ω) t ϖ (X ω')))) (liveNeg (Vr κ T B ω) t) ∂P ∂P := by
  rw [lintegral_lhs_eq_trInt hReg hκ hκ4 ht htT hB hX hind hϖ δ Ψ Φ]
  simp only [rhs_integrand_eq]
  exact lintegral_transfer_of_rep hκ ht htT hB hX hind Hf hHf hl hr

/-- `trInt` reads the driver only on `[0,t]` (`revMap v t`, `ϖ_t`, `q_t`, and the live set,
`liveNeg_congr_drive`). -/
theorem trInt_congr_drive (δ : ℝ) (Ψ : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞)
    (Φ : (ℕ → ℝ) → ℝ≥0∞) {v v' : ℝ → ℝ} (hv : Continuous v) (hv' : Continuous v') (ht : 0 ≤ t)
    (h : EqOn v v' (Icc 0 t)) (d : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) (y : FieldSample) :
    trInt κ t δ ϖ Ψ Φ v d y = trInt κ t δ ϖ Ψ Φ v' d y := by
  have hrev : revMap v t = revMap v' t := funext fun z => ReverseFlow.revMap_congr_drive z h
  unfold trInt varpiT qt
  rw [hrev, liveNeg_congr_drive hv hv' ht h]

/-- The driver on `[0,t]` read off the stopped path `V^t` (first component of the path data). -/
def stopDrive (d : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) : ℝ → ℝ := fun s => d.1 s.toNNReal

/-- `trInt` at the reversed driver equals `trInt` at the driver read off `V^t`. -/
theorem trInt_eq_stopDrive (δ : ℝ) (Ψ : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞)
    (Φ : (ℕ → ℝ) → ℝ≥0∞) (ht : 0 ≤ t) {ω : Ω} (hc : Continuous fun s => B s ω) (y : FieldSample) :
    trInt κ t δ ϖ Ψ Φ (Vr κ T B ω) (Vstop κ T t B ω, W0p κ T B ω) y =
      trInt κ t δ ϖ Ψ Φ (stopDrive (Vstop κ T t B ω, W0p κ T B ω))
        (Vstop κ T t B ω, W0p κ T B ω) y := by
  have hV : Continuous (Vr κ T B ω) := continuous_vrev (drive_continuous hc) T
  have hS : Continuous (stopDrive (Vstop κ T t B ω, W0p κ T B ω)) := by
    unfold stopDrive Vstop
    exact hV.comp ((NNReal.continuous_coe.comp continuous_real_toNNReal).min continuous_const)
  refine trInt_congr_drive δ Ψ Φ hV hS ht (fun s hs => ?_) _ y
  simp only [stopDrive, Vstop, Real.coe_toNNReal _ hs.1, min_eq_left hs.2]

end E1
end QuantumZipper
