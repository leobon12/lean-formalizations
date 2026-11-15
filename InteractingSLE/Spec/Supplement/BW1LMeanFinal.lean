/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1LMeanChain
import InteractingSLE.Spec.Supplement.GB6LMeanFinal

/-!
# BW1's union mean, part 3: `BW1LineMeanStatement` from Theorems 1.2–1.3

Packet PROVE-BW1-LINEMEAN. **`bw1LineMeanStatement_of_thm12_thm13`**: Theorem 1.4's named input (L3) for Proposition
BW1, `BW1Safe.BW1LineMeanStatement` (the union mean identification at BW1's physical lines), follows from Theorems
1.2–1.3. Hence **`bw1Statement_of_thm12_thm13`**: Proposition BW1 (`BW1.BW1Statement`) from Theorems 1.2–1.3 and the
canonical driver codes (`BW1Safe.bw1Statement_of_mean`).

Steps (for a counterflow time `s`, a version `B` of the physical union and a local-set mean `g` of `B s`), as in
GB6's (L3) (`Supp8.GB6LMean.gb6LineMeanStatement_of_thm12_thm13`):

* the mean of the TERMINAL retained set on the record event (`BW1LMean.ae_eqOn_bRetMean`, from the staged law);
* the union mean of `R(A) ∪ K_s` with a relative chain `Wr` generating every relative hull up to `a(s)`
  (`BW1LMean.ae_eqOn_unionMean_bw`), transferred to `B s` (`Supp8.GB6LMean.ae_mean_eq_of_ae_eq`; both sets are marked
  local for `σ(rec) ∨ 𝒩 ∨ 𝓕^cf_s`) — `ae_rep_unionMean_bw`; at `s = 0` the retained mean transferred to `B 0` —
  `ae_rep_retMean_bw`;
* on the live event before the stop: `Wr = R` on `[0, a(s)]` (`eqOn_of_hullsUpTo` with the version's hull clause), the
  typed word (`eqOn_bheProc_of_cfFlowed`, BW1's word being GB6's, `bwRelWord_eq_gb6WordOfRec`) and the transport
  identity `chartTransport_eq_couplingMean` (deterministic).

R48: BW1 serves Theorem 1.4; Theorems 1.2–1.3 enter only as the hypotheses `h12 h13` (through
`Exist.Param12.hasFieldDeterminedHistories` and `exists_bw1_retained_marks`). No `*_of_param` result is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.BW1LMean

open Exist.StagedLaw BW1Ver LocalSets
open Supp8.GB6 (relMap relInv relClock firstContactTime sphereInv gb6WordOfRec)
open Supp8.Q3Stop (wordType)
open Supp8.Q3Rel (invHull relLog relBad IsRelConfigOff)
open Supp8.Q3Chain
open Supp8.GB6LMean (HullsUpTo)

/-! ### The union mean for every version of the physical union -/

section Rep

/-- **The union mean represented on the complement of every version `B` of the physical union** (counterflow time
`t > 0`; BW1's form of `Supp8.GB6LMean.ae_rep_unionMean`). With the retained set marked local together with the
counterflow hull (marks `ℳ`) and the retained mean known on the good samples `D` (`hret`): almost surely on `D` there
are a relative chain `Wr` generating every relative hull up to `a(t)`, a bounded harmonic extension `G` of the record
word's flowed counterflow data, and a harmonic representative `wU` of the local-set mean of `B` with the candidate
formula off `B`. -/
theorem ae_rep_unionMean_bw {κ : ℝ} (hκ : 0 < κ) {Ω : Type u} {ℳ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {rec : Ω → RecData} {Ar γ : Ω → ℝ≥0 → ℂ}
    (β : Ω → Restart.BoundaryWord) {b' : ℝ → ℝ} {J' : Finset ℝ} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ}
    {Bc : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h' : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling (16 / κ) (flowLineXL b' J' 0) (flowLineXR b' J' 0) (flowLineRhoL (16 / κ) b' J' 0 0)
      (flowLineRhoR (16 / κ) b' J' 0 0) P 𝓕 W VL VR Bc ζ h')
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hW : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (cfData (16 / κ) b' J')
      (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h' u₀) P)
    (t : ℝ≥0) (ht0 : 0 < t) (D : Set Ω)
    (hD : ∀ ω ∈ D, IsGoodSample (rec ω) (Ar ω) (W · ω) (γ ω) ∧
      (t : ℝ≥0∞) < contactT (γ ω) (Ar ω) (recS (rec ω)))
    {A : Ω → Set ℂ} (hAeq : ∀ ω ∈ D, A ω = invHull (rdrv (rec ω)) (recS (rec ω)))
    (hunbA : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A ω)) z))
    (hAm : Measurable[mΩ, hittingSigma] A) (hAc : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω)) (hℳ : ℳ ≤ mΩ)
    (hlocU : WholeField.IsHistoryAvoidanceLocal ℳ
      (fun ω => A ω ∪ Sec5.GlueCond.hullAt t (LawUnique.killedHistory W VL VR ζ ω))
      (WholeField.centredField h' u₀) P)
    (hUℳ : Measurable[ℳ, hittingSigma]
      (fun ω => A ω ∪ Sec5.GlueCond.hullAt t (LawUnique.killedHistory W VL VR ζ ω)))
    (hdA : MeasurableSpace.comap A hittingSigma ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField h' u₀) inferInstance) P)
    (hlA : IsLocalSet A (WholeField.centredField h' u₀) P)
    (hret : ∀ g₁ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean A (WholeField.centredField h' u₀) P g₁ →
      ∀ᵐ ω ∂P, ω ∈ D →
        ∀ G₀ : ℂ → ℝ, IsBoundedHarmonicExtension (cfData (16 / κ) (β ω).fn (β ω).jumps)
            (cfJumps (β ω).fn (β ω).jumps) G₀ →
          ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A ω) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
            EqOn (fun z => w₁ z + u₀ z)
              (fun z => G₀ (relMap (rdrv (rec ω)) (recS (rec ω)) z) -
                chiC (16 / κ) * (relLog (rdrv (rec ω)) (recS (rec ω)) z).im)
              (H \ A ω))
    {B : Ω → Set ℂ} (hBm : Measurable[mΩ, hittingSigma] B) (hBc : ∀ᵐ ω ∂P, B ω ⊆ H ∧ IsOpen (H \ B ω))
    (hBeq : ∀ᵐ ω ∂P, B ω = A ω ∪ fwdHull (fun r : ℝ => W r.toNNReal ω) t)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean B (WholeField.centredField h' u₀) P g) :
    ∀ᵐ ω ∂P, ω ∈ D →
      ∃ (Wr : ℝ → ℝ) (G wU : ℂ → ℝ), Continuous Wr ∧ Wr 0 = 0 ∧
        HullsUpTo (rdrv (rec ω)) (recS (rec ω)) (fun x : ℝ => W x.toNNReal ω) Wr t ∧
        IsBoundedHarmonicExtension
          (cfFlowedData (16 / κ) (β ω).fn (β ω).jumps Wr
            (relClock (rdrv (rec ω)) (recS (rec ω)) (fun x : ℝ => W x.toNNReal ω) t))
          (cfFlowedJumps (β ω).fn (β ω).jumps Wr
            (relClock (rdrv (rec ω)) (recS (rec ω)) (fun x : ℝ => W x.toNNReal ω) t)) G ∧
        InnerProductSpace.HarmonicOnNhd wU (H \ B ω) ∧
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ B ω → g ω φ = ∫ z, wU z * φ z) ∧
        EqOn (fun z => wU z + u₀ z)
          (fun z => G (fwdMap Wr (relClock (rdrv (rec ω)) (recS (rec ω)) (fun x : ℝ => W x.toNNReal ω) t)
              (relMap (rdrv (rec ω)) (recS (rec ω)) z)) -
            chiC (16 / κ) *
              ((logDerivFwd Wr (relClock (rdrv (rec ω)) (recS (rec ω)) (fun x : ℝ => W x.toNNReal ω) t)
                (relMap (rdrv (rec ω)) (recS (rec ω)) z)).im +
                (relLog (rdrv (rec ω)) (recS (rec ω)) z).im))
          (H \ B ω) := by
  classical
  have hk : 0 < 16 / κ := by positivity
  have hX := hC.2.2.2.1
  set K : Ω → Set ℂ := fun ω => Sec5.GlueCond.hullAt t (LawUnique.killedHistory W VL VR ζ ω) with hKdef
  have hKm : Measurable[mΩ, hittingSigma] K := Supp8.RelSafeS.measurable_cfHull hX t
  have hKeq : ∀ᵐ ω ∂P, K ω = fwdHull (fun r : ℝ => W r.toNNReal ω) t := Supp8.RelSafeS.ae_cfHull_eq hC hζ t
  have hUm : Measurable[mΩ, hittingSigma] (fun ω => A ω ∪ K ω) := hUℳ.mono hℳ le_rfl
  have hUB : ∀ᵐ ω ∂P, A ω ∪ K ω = B ω := by
    filter_upwards [hKeq, hBeq] with ω hK hB
    rw [hB, hK]
  have hUc : ∀ᵐ ω ∂P, A ω ∪ K ω ⊆ H ∧ IsOpen (H \ (A ω ∪ K ω)) := by
    filter_upwards [hUB, hBc] with ω h1 h2
    rw [h1]
    exact h2
  have hlU : IsLocalSet (fun ω => A ω ∪ K ω) (WholeField.centredField h' u₀) P :=
    ((isLocalSet_tfae hh0 hUm hUc).out 4 1).2 hlocU.isAvoidanceLocal
  -- the three local-set means
  obtain ⟨gU, hgU⟩ := isGermConditionalLaw_iff.1 (hlocU.isAvoidanceLocal.isGermConditionalLaw hh0 hUm hUc)
  have hAc' : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω) := Eventually.of_forall hAc
  obtain ⟨g₁, hg₁⟩ := isGermConditionalLaw_iff.1
    (IsAvoidanceLocal.isGermConditionalLaw hh0 hAm hAc' (((isLocalSet_tfae hh0 hAm hAc').out 4 1).1 hlA))
  have hlocK := Supp8.RelSafeS.isHistoryAvoidanceLocal_cfHull hC hk hζ hu₀ t
  have hKc : ∀ᵐ ω ∂P, K ω ⊆ H ∧ IsOpen (H \ K ω) := by
    filter_upwards [hKeq, hW] with ω hK hWω
    rw [hK]
    exact ⟨(QuantumZipper.fwdHull_mono.2 _),
      QuantumZipper.FwdHolo.isOpen_compl_fwdHull (hWω.1.comp continuous_real_toNNReal) t.coe_nonneg⟩
  obtain ⟨g₂, hg₂⟩ := isGermConditionalLaw_iff.1 (hlocK.isAvoidanceLocal.isGermConditionalLaw hh0 hKm hKc)
  -- the union mean with the earlier hull identities
  have hmain := ae_eqOn_unionMean_bw hκ β hC hζ hW hu₀ hh0 t ht0 D hD hAeq hunbA hKeq hAm hKm hdA hlA hlU hgU hg₁
    hg₂ (hret g₁ hg₁)
  -- the transfer to `B`
  have htr := Supp8.GB6LMean.ae_mean_eq_of_ae_eq hh0 hUm hBm hBc hUB hℳ hlocU hUℳ hgU hg
  filter_upwards [hmain, htr, hUB, hgU.2.1] with ω hω htrω hUBω hharm hωD
  obtain ⟨Wr, G, hWr, hWr0, hHU, hG, hU⟩ := hω hωD
  obtain ⟨wU, hwU, hrepU⟩ := hharm
  have hwU' : InnerProductSpace.HarmonicOnNhd wU (H \ B ω) := by rw [← hUBω]; exact hwU
  have hrepU' : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ B ω → gU ω φ = ∫ z, wU z * φ z :=
    fun φ hφ => hrepU φ (by rw [hUBω]; exact hφ)
  refine ⟨Wr, G, wU, hWr, hWr0, hHU, hG, hwU', fun φ hφ => by rw [htrω φ hφ, hrepU' φ hφ], ?_⟩
  have h1 := hU wU hwU (fun φ hφ => hrepU φ hφ)
  rw [hUBω] at h1
  exact h1

/-- **The retained mean represented on the complement of every version `B` of the retained set** (counterflow time
`0`; BW1's form of `Supp8.GB6LMean.ae_rep_retMean`). -/
theorem ae_rep_retMean_bw {κ : ℝ} {Ω : Type u} {ℳ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {rec : Ω → RecData} (β : Ω → Restart.BoundaryWord)
    {h' : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ}
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h' u₀) P) (D : Set Ω)
    {A : Ω → Set ℂ} (hAm : Measurable[mΩ, hittingSigma] A) (hAc : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω)) (hℳ : ℳ ≤ mΩ)
    (hlocA : WholeField.IsHistoryAvoidanceLocal ℳ A (WholeField.centredField h' u₀) P)
    (hAℳ : Measurable[ℳ, hittingSigma] A)
    (hret : ∀ g₁ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean A (WholeField.centredField h' u₀) P g₁ →
      ∀ᵐ ω ∂P, ω ∈ D →
        ∀ G₀ : ℂ → ℝ, IsBoundedHarmonicExtension (cfData (16 / κ) (β ω).fn (β ω).jumps)
            (cfJumps (β ω).fn (β ω).jumps) G₀ →
          ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A ω) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
            EqOn (fun z => w₁ z + u₀ z)
              (fun z => G₀ (relMap (rdrv (rec ω)) (recS (rec ω)) z) -
                chiC (16 / κ) * (relLog (rdrv (rec ω)) (recS (rec ω)) z).im)
              (H \ A ω))
    {B : Ω → Set ℂ} (hBm : Measurable[mΩ, hittingSigma] B) (hBc : ∀ᵐ ω ∂P, B ω ⊆ H ∧ IsOpen (H \ B ω))
    (hBeq : ∀ᵐ ω ∂P, B ω = A ω)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean B (WholeField.centredField h' u₀) P g) :
    ∀ᵐ ω ∂P, ω ∈ D → ∃ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ B ω) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ B ω → g ω φ = ∫ z, w₁ z * φ z) ∧
      ∀ G₀ : ℂ → ℝ, IsBoundedHarmonicExtension (cfData (16 / κ) (β ω).fn (β ω).jumps)
          (cfJumps (β ω).fn (β ω).jumps) G₀ →
        EqOn (fun z => w₁ z + u₀ z)
          (fun z => G₀ (relMap (rdrv (rec ω)) (recS (rec ω)) z) -
            chiC (16 / κ) * (relLog (rdrv (rec ω)) (recS (rec ω)) z).im) (H \ B ω) := by
  have hAc' : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω) := Eventually.of_forall hAc
  obtain ⟨g₁, hg₁⟩ := isGermConditionalLaw_iff.1 (hlocA.isAvoidanceLocal.isGermConditionalLaw hh0 hAm hAc')
  have hAB : ∀ᵐ ω ∂P, A ω = B ω := by
    filter_upwards [hBeq] with ω hω using hω.symm
  have htr := Supp8.GB6LMean.ae_mean_eq_of_ae_eq hh0 hAm hBm hBc hAB hℳ hlocA hAℳ hg₁ hg
  filter_upwards [htr, hret g₁ hg₁, hBeq, hg₁.2.1] with ω htrω hretω hBω hharm hωD
  obtain ⟨w₁, hw₁, hrep₁⟩ := hharm
  refine ⟨w₁, by rw [hBω]; exact hw₁, fun φ hφ => by rw [htrω φ hφ, hrep₁ φ (by rw [← hBω]; exact hφ)],
    fun G₀ hG₀ => ?_⟩
  rw [hBω]
  exact hretω hωD G₀ hG₀ w₁ hw₁ hrep₁

end Rep

/-! ### The main theorem -/

section Main

open Exist Exist.Staged BW1Life BW1Safe Supp8.RelSafeS Supp8.RelSafe Restart Supp8.GB6LMean WholeField

/-- BW1's typed marks are GB6's typed marks of the shifted data word. -/
theorem bTypedL_eq {κ : ℝ} (hκ : 0 < κ) (θ : ℝ) (c₀ : BoundaryWord) (w : Supp8.Q3Stop.WordType) :
    bTypedL κ θ c₀ w = typedL κ θ (BoundaryWord.shiftW 0 c₀) w := funext fun y => by
  simp only [bTypedL, typedL, BW1In.bwRelWord_eq_gb6WordOfRec hκ]

theorem bTypedR_eq {κ : ℝ} (hκ : 0 < κ) (θ : ℝ) (c₀ : BoundaryWord) (w : Supp8.Q3Stop.WordType) :
    bTypedR κ θ c₀ w = typedR κ θ (BoundaryWord.shiftW 0 c₀) w := funext fun y => by
  simp only [bTypedR, typedR, BW1In.bwRelWord_eq_gb6WordOfRec hκ]

/-- **Theorem 1.4's named input (L3) for Proposition BW1, the union mean identification, from Theorems 1.2–1.3.** -/
theorem bw1LineMeanStatement_of_thm12_thm13 (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) : BW1LineMeanStatement.{u} := by
  intro κ b jumps Ω mΩ _ P _ h W' ζ' θ t gw2 rest E hset r TS hTS hFTS c₀ hc₀J hc₀ R V ℓ hver hhull m w Wd GT
    hWdm hWdc hWd0 hWdW hGTm hGTae hGT b' J' h' hb' hT hcfl u₀ hu₀ hh0 B hBm hBc hBeq hBloc s g hg ψ
  classical
  have hset' := hset
  obtain ⟨hκ, hκ4, hb, hh, hcf, hζ', hθ, hS⟩ := hset'
  set spec := bwSpec gw2 θ t rest with hspec
  set rec := bwRec κ b jumps spec E with hrecdef
  have hEm' : ∀ j, Measurable (StagedReg.regHist spec E j) := StagedReg.measurable_regHist hS.1
  have hreg' : ∀ j ω, IsRegularDriver (StagedReg.regHist spec E j ω) := fun j ω =>
    StagedReg.isRegularDriver_regHist j ω
  have hrec : Measurable rec := measurable_pastMap_one_last hb hEm' hreg'
  have hk : 0 < 16 / κ := by positivity
  -- the version with hulls and the good event
  have hGTgood : ∀ ω ∈ GT, BGood rec Wd ω := fun ω hω => (hGT ω hω).2.1
  have hGF : ∀ᵐ ω ∂P, ω ∈ GT → ω ∈ bwEvent κ b jumps spec E r := by
    filter_upwards [hFTS] with ω hω hG
    exact hω.2 (hGT ω hG).1
  have hv : IsBVer P rec Wd GT (R m) (V m) :=
    isBVer_of_version hver hhull hGF (fun ω hω => ⟨(hGT ω hω).2.2.1, (hGT ω hω).2.2.2⟩) m
  have hFGT : ∀ᵐ ω ∂P, ω ∈ bLive κ θ c₀ rec TS w → ω ∈ GT := by
    filter_upwards [hGTae] with ω hω hL
    exact hω hL.1
  -- the counterflow frame: data, centring, coupling
  have hG' : IsGFFWithBoundaryData P h' b' J' :=
    Theorem14.GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hk hb' hcfl
  obtain ⟨uo, huo, -⟩ :=
    PiecewiseConstant.existsUnique_isBoundedHarmonicExtension c₀.isPiecewiseConstantBoundaryData
  have huob : IsBoundedHarmonicExtension b jumps uo := by
    have h1 : IsBoundedHarmonicExtension c₀.fn jumps uo := by rw [← hc₀J]; exact huo
    exact (Restart.isBoundedHarmonicExtension_congr (fun y hy => hc₀ y hy) uo).1 h1
  have hcen := Supp8.Q3Chain.centredField_eq_reflect hκ hb hh hb' hG' hT huob hu₀
  have hcfl' := hcfl
  obtain ⟨hcfF, 𝓕c, VLc, VRc, Bc, htrc, hCc⟩ := hcfl'
  have e3 : hcfF = h' := funext fun ω => Theorem14.GW2Cone.eq_of_isTranslateAddConst_zero (zero_mul _) (htrc ω)
  rw [e3] at hCc
  have hXc := hCc.2.2.2.1
  have hh₀m : Measurable (centredField h' u₀) := hh0.measurable
  -- determination of the counterflow (Theorems 1.2–1.3)
  have hdetc := Exist.Param12.hasFieldDeterminedHistories h12 h13 hk (Theorem15.isOrderedForceWord_flowLine b' J' 0)
    P 𝓕c W' VLc VRc Bc ζ' h' hCc
  have hcomap' : MeasurableSpace.comap h' inferInstance ≤
      aeSigma (MeasurableSpace.comap (centredField h' u₀) inferInstance) P :=
    KernelTower.comap_le_aeSigma_comap (measurable_add_dist _)
      (Eventually.of_forall fun ω => (sub_add_cancel (h' ω)
        (SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀)).symm)
  have h𝓕c : ∀ s', drivingFiltration P hXc s' ≤
      aeSigma (MeasurableSpace.comap (centredField h' u₀) inferInstance) P := fun s' =>
    (Supp8.Q3Chain.drivingFiltration_le_aeSigma hdetc hXc s').trans (Supp8.Q3Chain.aeSigma_le_of_le hcomap')
  -- the retained set: marked local, and its mean
  obtain ⟨hrecd, hlocR⟩ := exists_bw1_retained_marks h12 h13 hset hc₀ huo hh0 (fun ω => hcen ω) hTS hFTS
  set A : Ω → Set ℂ := fun ω => bRetOfRec TS (rec ω) with hAdef
  have hAm : Measurable[mΩ, hittingSigma] A := (measurable_bRetOfRec hTS).comp hrec
  have hAℋ : Measurable[MeasurableSpace.comap rec inferInstance ⊔ Ito.nullSets P, hittingSigma] A :=
    ((measurable_bRetOfRec hTS).comp (comap_measurable rec)).mono le_sup_left le_rfl
  have hAc : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω) := fun ω =>
    ⟨bRetOfRec_subset_H TS _, isOpen_H_diff_bRetOfRec TS _⟩
  have hℳle : MeasurableSpace.comap rec inferInstance ⊔ Ito.nullSets P ≤ mΩ :=
    sup_le hrec.comap_le (Ito.nullSets_le P)
  have hret := fun (g₁ : Ω → DistOn upperHalfPlaneOpens)
      (hg₁ : IsLocalSetMean A (centredField h' u₀) P g₁) =>
    ae_eqOn_bRetMean h12 h13 hset hTS hFTS hc₀J hc₀ hb' hT hcfl hu₀ hh0 hg₁
  have hRc := hv.cont
  have hR0 := hv.zero
  -- the physical counterflow driver
  have hW'c : ∀ᵐ ω ∂P, Continuous (fun s' => W' s' ω) ∧ W' 0 ω = 0 := by
    filter_upwards [hWdW] with ω hω
    have e : (fun s' => W' s' ω) = fun s' => Wd s' ω := funext fun s' => (hω s').symm
    rw [e, ← hω 0]
    exact ⟨hWdc ω, hWd0 ω⟩
  have eTL := bTypedL_eq hκ θ c₀ w
  have eTR := bTypedR_eq hκ θ c₀ w
  have hRpc : ∀ ω, Continuous fun x : ℝ => R m x.toNNReal ω := fun ω => (hRc ω).comp continuous_real_toNNReal
  have hRp0 : ∀ ω, (fun x : ℝ => R m x.toNNReal ω) 0 = 0 := fun ω => by simp only [Real.toNNReal_zero, hR0 ω]
  by_cases hs0 : s = 0
  · -- the counterflow time `0`: the retained mean
    subst hs0
    have hBeq0 : ∀ᵐ ω ∂P, B 0 ω = A ω := by
      filter_upwards [hBeq 0] with ω hB
      have hWc : Continuous fun x : ℝ => Wd x.toNNReal ω := (hWdc ω).comp continuous_real_toNNReal
      rw [hB, NNReal.coe_zero, QuantumZipper.RS.fwdHull_zero_eq_empty hWc, union_empty]
      exact relClosureH_eq_self (hAc ω).1 (hAc ω).2
    have hrep0 := ae_rep_retMean_bw (κ := κ) (fun ω => bwRelWord κ θ c₀ (rec ω)) hh0 (rec ⁻¹' TS) hAm hAc hℳle
      hlocR hAℋ (fun g₁ hg₁ => hret g₁ hg₁) (hBm 0) (Eventually.of_forall (hBc 0)) hBeq0 hg
    filter_upwards [hrep0, hFGT, hBeq0, ae_compl_union_eq_relChart_bw hGTgood hv 0] with ω hrepω hGTω hB0 hshape
      hlive hlt hψ
    have hrecTS : rec ω ∈ TS := hlive.1
    have hωGT : ω ∈ GT := hGTω hlive
    obtain ⟨w₁, hw₁, hrep₁, hv₁⟩ := hrepω hrecTS
    set β := bwRelWord κ θ c₀ (rec ω) with hβ
    obtain ⟨G₀, hG₀⟩ := Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData (16 / κ)
      (flowLineRhoL (16 / κ) β.fn β.jumps 0 0) (flowLineRhoR (16 / κ) β.fn β.jumps 0 0)
      (flowLineXL β.fn β.jumps 0) (flowLineXR β.fn β.jumps 0)
    have hG₀' : IsBoundedHarmonicExtension (cfData (16 / κ) β.fn β.jumps) (cfJumps β.fn β.jumps) G₀ := by
      rw [coe_cfJumps]
      exact hG₀
    have hQ : (min (bClock rec Wd GT 0 ω) (V m ω)).toNNReal = 0 := by
      rw [min_bClock_zero hGTgood ω, ENNReal.toNNReal_zero]
    have hsh := hshape hωGT hlt
    rw [hQ] at hψ hsh ⊢
    have hO : H \ B 0 ω = (relChart (rec ω)).2.1 ''
        (H \ fwdHull (fun x : ℝ => R m x.toNNReal ω) ((0 : ℝ≥0) : ℝ)) := by
      have hWc : Continuous fun x : ℝ => Wd x.toNNReal ω := (hWdc ω).comp continuous_real_toNNReal
      rw [← hsh, NNReal.coe_zero, QuantumZipper.RS.fwdHull_zero_eq_empty hWc, union_empty, hB0, hAdef]
      simp only [bRetOfRec_of_mem hrecTS]
    have hwt : wordType (16 / κ) (gb6WordOfRec κ θ (BoundaryWord.shiftW 0 c₀) (rec ω)) = w := by
      rw [← BW1In.bwRelWord_eq_gb6WordOfRec hκ]
      exact hlive.2
    have hG0f : IsBoundedHarmonicExtension
        (cfFlowedData (16 / κ) (gb6WordOfRec κ θ (BoundaryWord.shiftW 0 c₀) (rec ω)).fn
          (gb6WordOfRec κ θ (BoundaryWord.shiftW 0 c₀) (rec ω)).jumps (fun x : ℝ => R m x.toNNReal ω)
          ((0 : ℝ≥0) : ℝ))
        (cfFlowedJumps (gb6WordOfRec κ θ (BoundaryWord.shiftW 0 c₀) (rec ω)).fn
          (gb6WordOfRec κ θ (BoundaryWord.shiftW 0 c₀) (rec ω)).jumps (fun x : ℝ => R m x.toNNReal ω)
          ((0 : ℝ≥0) : ℝ)) G₀ := by
      rw [← BW1In.bwRelWord_eq_gb6WordOfRec hκ, NNReal.coe_zero]
      exact bhe_cfFlowed_zero (hRpc ω) (hRp0 ω) hG₀'
    have hGG := eqOn_bheProc_of_cfFlowed (Hc := bwRelField κ b jumps spec h E) (V := V m) (rec := rec) hwt (hRc ω)
      (hR0 ω) 0 (G := G₀) hG0f
    rw [← eTL, ← eTR] at hGG
    have hL0 : ∀ y, logDerivFwd (fun x : ℝ => R m x.toNNReal ω) 0 y = 0 := fun y => by
      simp [QuantumZipper.logDerivFwd]
    refine chartTransport_eq_couplingMean κ (r := rec ω) (s := recS (rec ω)) rfl (fun x _ => rfl) hO hw₁ hu₀.1 hrep₁
      (Wr := fun x : ℝ => R m x.toNNReal ω) (G := G₀) ?_ (fun _ _ => rfl) (hRpc ω) hGG hψ
    intro z hz
    rw [hv₁ G₀ hG₀' hz]
    simp only [NNReal.coe_zero, fwdMap_zero_time (W := fun x : ℝ => R m x.toNNReal ω) (hRp0 ω), hL0,
      Complex.zero_im, zero_add]
    rfl
  · -- a positive counterflow time: the union mean
    have hs0' : 0 < s := pos_iff_ne_zero.2 hs0
    have hKℳ : Measurable[drivingFiltration P hXc s, hittingSigma]
        (fun ω => Sec5.GlueCond.hullAt s (LawUnique.killedHistory W' VLc VRc ζ' ω)) :=
      ((Sec5.CrossCond.measurable_hullAt_stopSigma s).comp (comap_measurable _)).mono
        (WangWu.comap_stopSigma_le hXc s) le_rfl
    have hlocU : IsHistoryAvoidanceLocal
        ((MeasurableSpace.comap rec inferInstance ⊔ Ito.nullSets P) ⊔ drivingFiltration P hXc s)
        (fun ω => A ω ∪ Sec5.GlueCond.hullAt s (LawUnique.killedHistory W' VLc VRc ζ' ω)) (centredField h' u₀) P :=
      Theorem14.WalkLaw.isHistoryAvoidanceLocal_union_of_det hh₀m
        (ℋ₁ := MeasurableSpace.comap rec inferInstance ⊔ Ito.nullSets P) (ℋ₂ := drivingFiltration P hXc s)
        (A₁ := A) (A₂ := fun ω => Sec5.GlueCond.hullAt s (LawUnique.killedHistory W' VLc VRc ζ' ω))
        (fun U hUH => le_sup_left (a := MeasurableSpace.comap rec inferInstance) _
          ⟨_, measurable_bRetOfRec hTS (measurableSet_avoid U.isOpen hUH), rfl⟩)
        (fun U hUH => measurableSet_avoid_cfHull hXc s U.isOpen hUH) (sup_le hrecd nullSets_le_aeSigma) (h𝓕c s)
        hlocR (isHistoryAvoidanceLocal_cfHull hCc hk hζ' hu₀ s)
    have hUℳ : Measurable[(MeasurableSpace.comap rec inferInstance ⊔ Ito.nullSets P) ⊔ drivingFiltration P hXc s,
        hittingSigma] (fun ω => A ω ∪ Sec5.GlueCond.hullAt s (LawUnique.killedHistory W' VLc VRc ζ' ω)) :=
      @measurable_union_hitting Ω ((MeasurableSpace.comap rec inferInstance ⊔ Ito.nullSets P) ⊔
        drivingFiltration P hXc s) _ _ (hAℋ.mono le_sup_left le_rfl) (hKℳ.mono le_sup_right le_rfl)
    have hdA : MeasurableSpace.comap A hittingSigma ≤
        aeSigma (MeasurableSpace.comap (centredField h' u₀) inferInstance) P :=
      hAℋ.comap_le.trans (sup_le hrecd nullSets_le_aeSigma)
    have hlA : IsLocalSet A (centredField h' u₀) P :=
      ((isLocalSet_tfae hh0 hAm (Eventually.of_forall hAc)).out 4 1).2 hlocR.isAvoidanceLocal
    have hunion : ∀ {ω : Ω} {V' : ℝ → ℝ}, Continuous V' →
        A ω ∪ fwdHull V' s ⊆ H ∧ IsOpen (H \ (A ω ∪ fwdHull V' s)) := fun {ω V'} hV' => by
      refine ⟨union_subset (hAc ω).1 (QuantumZipper.fwdHull_mono.2 _), ?_⟩
      have e : H \ (A ω ∪ fwdHull V' s) = (H \ A ω) ∩ (H \ fwdHull V' s) := by
        ext z
        simp only [Set.mem_sdiff, mem_union, mem_inter_iff, not_or]
        tauto
      rw [e]
      exact (hAc ω).2.inter (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hV' s.coe_nonneg)
    have hBeqW : ∀ᵐ ω ∂P, B s ω = A ω ∪ fwdHull (fun x : ℝ => W' x.toNNReal ω) s := by
      filter_upwards [hBeq s, hWdW] with ω hB hW
      have hWp : (fun x : ℝ => W' x.toNNReal ω) = fun x : ℝ => Wd x.toNNReal ω := funext fun x => (hW _).symm
      have hWc : Continuous fun x : ℝ => Wd x.toNNReal ω := (hWdc ω).comp continuous_real_toNNReal
      rw [hB, hWp]
      exact relClosureH_eq_self (hunion hWc).1 (hunion hWc).2
    -- the good samples before the contact
    set D : Set Ω := {ω | ω ∈ GT ∧ (s : ℝ≥0∞) < bTc rec Wd ω} with hDdef
    have hD : ∀ ω ∈ D,
        IsGoodSample (rec ω) (fun v => Supp8.GB6.ReadD.recordTrace v (rec ω)) (W' · ω) (phTr Wd ω) ∧
          (s : ℝ≥0∞) < contactT (phTr Wd ω) (fun v => Supp8.GB6.ReadD.recordTrace v (rec ω)) (recS (rec ω)) := by
      intro ω hω
      have e : (fun s' => W' s' ω) = fun s' => Wd s' ω := funext fun s' => (hGT ω hω.1).2.2.1 s'
      rw [e]
      exact ⟨hGTgood ω hω.1, hω.2⟩
    have hAeq : ∀ ω ∈ D, A ω = invHull (rdrv (rec ω)) (recS (rec ω)) := fun ω hω => by
      simp only [hAdef, bRetOfRec_of_mem (hGT ω hω.1).1]
    have hrepU := ae_rep_unionMean_bw hκ (fun ω => bwRelWord κ θ c₀ (rec ω)) hCc hζ' hW'c hu₀ hh0 s hs0' D hD hAeq
      (Eventually.of_forall fun ω => not_isBounded_lowerUnion_bRetOfRec TS _) hAm hAc
      (sup_le hℳle ((drivingFiltration P hXc).le s)) hlocU hUℳ hdA hlA
      (fun g₁ hg₁ => by
        filter_upwards [hret g₁ hg₁] with ω hω hωD
        exact hω (hGT ω hωD.1).1)
      (hBm s) (Eventually.of_forall (hBc s)) hBeqW hg
    filter_upwards [hrepU, hFGT, hv.ae, ae_compl_union_eq_relChart_bw hGTgood hv s, hBeq s]
      with ω hrepω hGTω hverω hshape hBt hlive hlt hψ
    have hrecTS : rec ω ∈ TS := hlive.1
    have hωGT : ω ∈ GT := hGTω hlive
    obtain ⟨-, hgood, hW'eq, -⟩ := hGT ω hωGT
    obtain ⟨-, hreachV, hhullV⟩ := hverω hωGT
    have htc : (s : ℝ≥0∞) < bTc rec Wd ω := lt_bTc_of_lt_stop hGTgood hωGT hreachV hlt
    have hωD : ω ∈ D := ⟨hωGT, htc⟩
    -- the clock at `s`
    have hphys := bClock_eq_rclk hGTgood hωGT htc
    obtain ⟨ha0, hsm, hac⟩ := hgood.clock_regular
    have hnn : 0 ≤ rclk (rec ω) (Wd · ω) s := by
      have h0T : ((0 : ℝ≥0) : ℝ≥0∞) < bTc rec Wd ω := lt_of_le_of_lt bot_le htc
      have := hsm.monotoneOn h0T htc (bot_le : (0 : ℝ≥0) ≤ s)
      rw [ha0] at this
      exact this
    have hlt' : ENNReal.ofReal (rclk (rec ω) (Wd · ω) s) < V m ω := by
      rw [hphys] at hlt
      exact lt_of_not_ge fun h => lt_irrefl _ (by rwa [min_eq_right h] at hlt)
    have hmin : min (bClock rec Wd GT s ω) (V m ω) = ENNReal.ofReal (rclk (rec ω) (Wd · ω) s) := by
      rw [hphys]
      exact min_eq_left hlt'.le
    have hreal : (((min (bClock rec Wd GT s ω) (V m ω)).toNNReal : ℝ≥0) : ℝ) = rclk (rec ω) (Wd · ω) s := by
      rw [hmin, ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_ofReal hnn]
    -- the union representation, read with the physical driver
    obtain ⟨Wr, G, wU, hWr, hWr0, hHU, hGb, hwU, hrep, hvU⟩ := hrepω hωD
    have hWp : (fun x : ℝ => W' x.toNNReal ω) = fun x : ℝ => Wd x.toNNReal ω := funext fun x => hW'eq _
    rw [hWp] at hHU hGb hvU
    -- `Wr = R` up to `a(s)`
    have hHR : ∀ t' : ℝ≥0, t' ≤ s →
        relMap (rdrv (rec ω)) (recS (rec ω)) '' fwdHull (fun x : ℝ => Wd x.toNNReal ω) t' =
        fwdHull (fun x : ℝ => R m x.toNNReal ω)
          (relClock (rdrv (rec ω)) (recS (rec ω)) (fun x : ℝ => Wd x.toNNReal ω) t') := fun t' ht' => by
      have ht'c : (t' : ℝ≥0∞) < bTc rec Wd ω := lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht') htc
      have hle : ENNReal.ofReal (rclk (rec ω) (Wd · ω) t') ≤ V m ω :=
        le_trans (ENNReal.ofReal_le_ofReal (hsm.monotoneOn ht'c htc ht')) hlt'.le
      exact (hhullV t' ht'c hle).symm
    have hWR := eqOn_of_hullsUpTo hWr hWr0 (hRpc ω) (hRp0 ω) ha0
      (hac.mono fun t' ht' => lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht'.2) htc) hHU hHR
    -- the typed word
    have hGR := bhe_cfFlowed_congr hWr hWr0 (hRpc ω) (hRp0 ω) hnn hWR hGb
    have hwt : wordType (16 / κ) (gb6WordOfRec κ θ (BoundaryWord.shiftW 0 c₀) (rec ω)) = w := by
      rw [← BW1In.bwRelWord_eq_gb6WordOfRec hκ]
      exact hlive.2
    have hGR' : IsBoundedHarmonicExtension
        (cfFlowedData (16 / κ) (gb6WordOfRec κ θ (BoundaryWord.shiftW 0 c₀) (rec ω)).fn
          (gb6WordOfRec κ θ (BoundaryWord.shiftW 0 c₀) (rec ω)).jumps (fun x : ℝ => R m x.toNNReal ω)
          (((min (bClock rec Wd GT s ω) (V m ω)).toNNReal : ℝ≥0) : ℝ))
        (cfFlowedJumps (gb6WordOfRec κ θ (BoundaryWord.shiftW 0 c₀) (rec ω)).fn
          (gb6WordOfRec κ θ (BoundaryWord.shiftW 0 c₀) (rec ω)).jumps (fun x : ℝ => R m x.toNNReal ω)
          (((min (bClock rec Wd GT s ω) (V m ω)).toNNReal : ℝ≥0) : ℝ)) G := by
      rw [← BW1In.bwRelWord_eq_gb6WordOfRec hκ, hreal]
      exact hGR
    have hGG := eqOn_bheProc_of_cfFlowed (Hc := bwRelField κ b jumps spec h E) (V := V m) (rec := rec) hwt (hRc ω)
      (hR0 ω) (min (bClock rec Wd GT s ω) (V m ω)).toNNReal (G := G) hGR'
    rw [← eTL, ← eTR] at hGG
    -- the shape of the union
    have hO : H \ B s ω = (relChart (rec ω)).2.1 ''
        (H \ fwdHull (fun x : ℝ => R m x.toNNReal ω) (min (bClock rec Wd GT s ω) (V m ω)).toNNReal) := by
      have hWc : Continuous fun x : ℝ => Wd x.toNNReal ω := (hWdc ω).comp continuous_real_toNNReal
      rw [← hshape hωGT hlt, hBt, relClosureH_eq_self (hunion hWc).1 (hunion hWc).2, hAdef]
      simp only [bRetOfRec_of_mem hrecTS]
    refine chartTransport_eq_couplingMean κ (r := rec ω) (s := recS (rec ω)) rfl (fun x _ => rfl) hO hwU hu₀.1 hrep
      (Wr := Wr) (G := G) ?_ (by rw [hreal]; exact hWR) (hRpc ω) hGG hψ
    rw [hreal]
    exact hvU

/-- **Proposition BW1 from Theorems 1.2–1.3 and the canonical driver codes** (`BW1Safe.bw1Statement_of_mean` with its
named input (L3) discharged by `bw1LineMeanStatement_of_thm12_thm13`). -/
theorem bw1Statement_of_thm12_thm13 (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hT13₀ : Exist.Theorem13Statement.{0}) (hcode : Restart.CanonicalDriverCodeStatement) : BW1.BW1Statement.{u} :=
  bw1Statement_of_mean h12p h12 h13 hT13₀ hcode (bw1LineMeanStatement_of_thm12_thm13 h12 h13)

/-- **BW1's relative safe law (S)/(L) for versions with hull identities from Theorems 1.2–1.3**
(`BW1Safe.bw1RelSafeLawHStatement_of_mean` with (L3) discharged). -/
theorem bw1RelSafeLawHStatement_of_thm12_thm13 (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) : BW1RelSafeLawHStatement.{u} :=
  bw1RelSafeLawHStatement_of_mean h12 h13 (bw1LineMeanStatement_of_thm12_thm13 h12 h13)

end Main

end InteractingSLE.Theorem14.BW1LMean
