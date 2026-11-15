/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CondGen
import InteractingSLE.Spec.Supplement.Q3StopK2
import InteractingSLE.Spec.Supplement.GB6HullIdRule
import InteractingSLE.Spec.Supplement.HullDetGen
import InteractingSLE.Spec.Supplement.SB2DrvCells

/-!
# SB2(1) at announced stops, part 1: the stopped identification from K2's inputs at a record-path stop

Packet PROVE-T14-SB2DRV (round 15, decision D4 = option (B): SB2(1)'s version half at announced stops strictly
before the lifetime). The consumer step of D4: K2 at each stop gives a stopped hull coupling, the regular-stop form
of Aux. lemma 54 (`Aux54.stoppedHullExtendRStatement`, R79) extends it, and Theorem 1.2 identifies the driver with
the canonical driver code before the stop. The stop is a **record-path rule** `V = ρ(rec, W)` with a `𝒢`-measurable
record, announced by finite record-path rules `ρs n` (the shape of BW1's and GB6's relative versions,
`IsBW1RelVersion`, and of the physical-time rules `GW2SxTime.timeCapRule`): under each regular conditional law given
`𝒢` the record is frozen, so the stop is a Galmarino rule of the killed driver history (`HullId.histRule`) and the
announcing rules are kernel stops (`Q3Stop.isKernelStop_of_pathRule`).

* `isStoppingTime_recPathRule`: a record-path rule of an adapted driver with an initial record is a stopping time;
* `isStoppedHullCoupling_flowLineWord_of_truncWord`: a coupling through a stop read with the flow-line word;
* `continuous_of_frozen_agree`: a process equal to a continuous driver through a stop and frozen after it is
  continuous;
* **`ae_isStopDrvMatch_driverCode_of_stopped`**: a regular Galmarino-stopped coupling of a flow-line word matches the
  canonical driver code `driverCode h12p` before its stop (universe `u`);
* **`ae_isStopDrvMatch_of_hasSafeLaw_rule`**: the stopped driver match from K2's (S) and (L) at a record-path stop
  below the continuation threshold (no input (E));
* **`ae_isStopDrvMatch_of_hasSafeLaw_rule_on`**: the same on a live event `F ∈ 𝒢`.

**R48.** Theorems 1.2–1.3 are hypotheses; this serves Theorem 1.4 only. No source theorem is replaced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Cond

open Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Sec7.PocketTraversal Exist.Staged Sec2.Assembly
open Exist.StagedLaw (RecData)
open Supp8.GB6.RelDrv (IsStopDrvMatch measurableSet_isStopDrvMatch)
open Supp8.GB6.HullId (IsPathRule histRule)
open LawUnique (HistorySpace killedHistory)

/-! ### Record-path rules as stopping times -/

section Rule

/-- A path read through `min · t` and a record, measurable for one σ-algebra. -/
theorem measurable_rec_stopPath {Ω : Type*} {m : MeasurableSpace Ω} {rec : Ω → RecData} (hrec : Measurable[m] rec)
    {f : Ω → ℝ≥0 → ℝ} (hf : ∀ u, Measurable[m] fun ω => f ω u) : Measurable[m] fun ω => (rec ω, f ω) :=
  hrec.prodMk (measurable_pi_iff.mpr hf)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **A record-path rule of an adapted driver with an initial record is a stopping time.** -/
theorem isStoppingTime_recPathRule {𝓗 : Filtration ℝ≥0 mΩ} {rec : Ω → RecData} (hrec : Measurable[𝓗 0] rec)
    {W : ℝ≥0 → Ω → ℝ} (hWa : StronglyAdapted 𝓗 W) {ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρm : Measurable ρ)
    (hρ : IsPathRule ρ) :
    IsStoppingTime 𝓗 fun ω => (ρ (rec ω, fun u => W u ω) : WithTop ℝ≥0) := by
  intro t
  have hpath : Measurable[𝓗 t] fun ω => (rec ω, fun u => W (min u t) ω) :=
    measurable_rec_stopPath (hrec.mono (𝓗.mono (zero_le (a := t))) le_rfl) fun u =>
      (hWa (min u t)).measurable.mono (𝓗.mono (min_le_right u t)) le_rfl
  have hS : MeasurableSet[𝓗 t] {ω | ρ (rec ω, fun u => W (min u t) ω) ≤ (t : ℝ≥0∞)} :=
    measurableSet_le (hρm.comp hpath) measurable_const
  have e : {ω | ρ (rec ω, fun u => W u ω) ≤ (t : ℝ≥0∞)} =
      {ω | ρ (rec ω, fun u => W (min u t) ω) ≤ (t : ℝ≥0∞)} := by
    ext ω
    simp only [mem_ofPred_eq]
    constructor
    · intro h
      rw [hρ (rec ω) (fun u => W u ω) (fun u => W (min u t) ω) fun u hu => by
        rw [min_eq_left (ENNReal.coe_le_coe.1 (hu.trans h))]]
      exact h
    · intro h
      rw [hρ (rec ω) (fun u => W (min u t) ω) (fun u => W u ω) fun u hu => by
        rw [min_eq_left (ENNReal.coe_le_coe.1 (hu.trans h))]]
      exact h
  change MeasurableSet[𝓗 t] {ω | ρ (rec ω, fun u => W u ω) ≤ (t : ℝ≥0∞)}
  rw [e]
  exact hS

end Rule

/-! ### Couplings through a stop -/

section Coupling

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

omit mΩ in
/-- **A process equal to a continuous driver through a stop and frozen after it is continuous.** -/
theorem continuous_of_frozen_agree {w w' : ℝ≥0 → ℝ} (hw : Continuous w) {e : ℝ≥0∞}
    (hag : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ e → w' t = w t)
    (hfrz : ∀ T : ℝ≥0, (T : ℝ≥0∞) = e → ∀ t : ℝ≥0, T ≤ t → w' t = w' T) : Continuous w' := by
  induction e using ENNReal.recTopCoe with
  | top => exact hw.congr fun t => (hag t le_top).symm
  | coe T =>
    have e : w' = fun t => w (min t T) := funext fun t => by
      rcases le_total t T with h | h
      · rw [min_eq_left h]
        exact hag t (ENNReal.coe_le_coe.2 h)
      · rw [min_eq_right h, hfrz T rfl t h]
        exact hag T le_rfl
    rw [e]
    exact hw.comp (continuous_id.min continuous_const)

/-- **A coupling through a stop read with the flow-line word** (`CondDriverBridge.coupling_flowLineWord_of_truncWord`
for couplings through a stop). -/
theorem isStoppedHullCoupling_flowLineWord_of_truncWord {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Q : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {e : Ω → ℝ≥0∞} {X : Ω → DistOn upperHalfPlaneOpens}
    (hnL : flowLineNL b J 0 = nL) (hnR : flowLineNR b J 0 = nR)
    (hw : truncWord nL nR (padFL κ θ b J) = ((xL, xR), (ρL, ρR)))
    (hC : StoppedExtend.IsStoppedHullCoupling κ xL xR ρL ρR Q 𝓕 W VL VR B e X) :
    ∃ (VL' : Fin (flowLineNL b J 0) → ℝ≥0 → Ω → ℝ) (VR' : Fin (flowLineNR b J 0) → ℝ≥0 → Ω → ℝ),
      StoppedExtend.IsStoppedHullCoupling κ (flowLineXL b J 0) (flowLineXR b J 0) (flowLineRhoL κ b J 0 θ)
        (flowLineRhoR κ b J 0 θ) Q 𝓕 W VL' VR' B e X := by
  subst hnL hnR
  rw [truncWord_padFL] at hw
  simp only [Prod.mk.injEq] at hw
  obtain ⟨⟨e1, e2⟩, e3, e4⟩ := hw
  rw [e1, e2, e3, e4]
  exact ⟨VL, VR, hC⟩

end Coupling

/-! ### The stopped match with the canonical driver code, universe `u` -/

section Match

variable (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (θ : ℝ)

/-- **A regular Galmarino-stopped coupling of a flow-line word matches the canonical driver code before its stop**
(universe `u`): Aux. lemma 54 in its regular-stop form (R79) extends the coupling to a full optional hull coupling on
an extension `Q ⊗ₘ K`, which is a flow-line driver of the unshifted field; Theorem 1.2's determination
(`ae_driverCodeMatch_of_isFlowLineDriver_univ`) matches its driver with `driverCode h12p`, and the extension agrees
with the coupling through the stop. -/
theorem ae_isStopDrvMatch_driverCode_of_stopped (h13 : Exist.Theorem13Statement.{u}) (c : BoundaryWord)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {Hc X : Ω → DistOn upperHalfPlaneOpens}
    (hX : ∀ ω, IsTranslateAddConst 0 (θ * chiC κ) (Hc ω) (X ω)) {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin (flowLineNL c.fn c.jumps 0) → ℝ≥0 → Ω → ℝ}
    {VR : Fin (flowLineNR c.fn c.jumps 0) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {e : Ω → ℝ≥0∞}
    (hSC : StoppedExtend.IsStoppedHullCoupling κ (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
      (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) Q 𝓕 W VL VR B e X)
    {R : HistorySpace (flowLineNL c.fn c.jumps 0) (flowLineNR c.fn c.jumps 0) → ℝ≥0∞} (hRm : Measurable R)
    (hRG : StoppedExtendWF.IsHistGalmarino R) (hRe : ∀ᵐ ω ∂Q, e ω = R (killedHistory W VL VR e ω))
    (hreg : Aux54.IsRegularStop (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) Q W VL VR e)
    {Wb : ℝ≥0 → Ω → ℝ} (hWb : ∀ t, Measurable (Wb t)) (hHc : Measurable Hc) (he : Measurable e)
    (hagb : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ e ω → W t ω = Wb t ω) :
    ∀ᵐ ω ∂Q, IsStopDrvMatch (driverCode h12p hκ θ (c, Hc ω)) (fun t => Wb t ω) (e ω) := by
  obtain ⟨C, mC, K, hK, 𝓕', W', VL', VR', B', ζ', hC, hag⟩ :=
    Aux54.stoppedHullExtendRStatement.{u} hκ _ _ _ _ (Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0) R hRm
      hRG Q 𝓕 W VL VR B e X hSC hRe hreg
  have hmap : (Q ⊗ₘ K).map Prod.fst = Q := by
    rw [← Measure.fst, Measure.fst_compProd]
  have hfl : IsFlowLineDriver κ c.fn c.jumps θ (Q ⊗ₘ K) (fun p => Hc p.1) W' ζ' :=
    ⟨fun p => X p.1, 𝓕', VL', VR', B', fun p => hX p.1, hC⟩
  have hdet := ae_driverCodeMatch_of_isFlowLineDriver_univ h12p hκ θ h13 c hfl
  have hSm : MeasurableSet {ω | IsStopDrvMatch (driverCode h12p hκ θ (c, Hc ω)) (fun t => Wb t ω) (e ω)} :=
    measurableSet_isStopDrvMatch ((measurable_driverCode h12p hκ θ).comp (measurable_const.prodMk hHc)) hWb he
  have hfst : AEMeasurable (Prod.fst : Ω × C → Ω) (Q ⊗ₘ K) := measurable_fst.aemeasurable
  have hagbE : ∀ᵐ p ∂(Q ⊗ₘ K), ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ e p.1 → W t p.1 = Wb t p.1 :=
    ae_of_ae_map hfst (by rw [hmap]; exact hagb)
  rw [← hmap]
  refine (ae_map_iff hfst hSm).2 ?_
  filter_upwards [hdet, hag, hagbE] with p hp hagp hbp
  obtain ⟨hL, -, hd⟩ := hp
  refine ⟨hL ▸ hagp.1, fun n k hnk => ?_⟩
  have hlt : (dyad n k : ℝ≥0∞) < ζ' p := lt_of_lt_of_le hnk hagp.1
  show Wb (dyad n k) p.1 = (driverCode h12p hκ θ (c, Hc p.1)).1 n k
  rw [← hbp _ hnk.le, ← (hagp.2 _ hnk.le hlt).1]
  exact hd n k hlt

end Match

/-! ### The stopped match from K2's inputs at a record-path stop -/

section Main

variable {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {nL nR : ℕ} {κ θ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **The stopped driver match from K2's (S) and (L) at a record-path stop** (no input (E)). The setting of
`isCondFlowLineDriverOn_of_hasSafeLaw_ann`, with the lifetime a stop `V = ρ(rec, W)` below the continuation threshold
instead of the threshold itself: `rec` is a `𝒢`-measurable record, `ρ` a measurable record-path rule, and `V` is
announced by finite measurable record-path rules `ρs n`, nondecreasing in `n`. Then almost surely `V` is at most the
lifetime of the canonical driver code of (word, chart field) and `W` is that code at the dyadic times before `V`.

Proof: (S) gives the coupling characteristic function (`Aux79.isCouplingCharFun_of_hasSafeLaw`), the announcing rules
an announcing sequence of `V` in the usual augmentation, hence (E-stop) on `Ω × (ℕ → ℝ)`
(`StoppedK2.isRandomWordEvolutionUpTo_prod_of_isCouplingCharFun`); the announcing rules are kernel stops there
(`Q3Stop.isKernelStop_of_pathRule`), so the stopped K2 with kernel stops (`Q3Stop.ae_isStoppedHullCoupling_kk_prod`)
gives a coupling through `V` under almost every conditional law, frozen after `V`. Under such a law the record is
frozen, so `V` is the Galmarino history rule `histRule ρ (rec p₀)` of the killed history and the stop is regular
(`Aux54.isRegularStop_of_frozen`); `ae_isStopDrvMatch_driverCode_of_stopped` concludes, and the match integrates
back to `P`. -/
theorem ae_isStopDrvMatch_of_hasSafeLaw_rule (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) {𝓗 : Filtration ℝ≥0 mΩ} (h𝒢 : 𝒢 ≤ 𝓗 0)
    {cw : Ω → BoundaryWord} (hcw : Measurable[𝒢] cw)
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} (hxL : Measurable[𝒢] xL) (hxR : Measurable[𝒢] xR)
    (hxL0 : ∀ ω i, xL ω i ≤ 0) (hxR0 : ∀ ω j, 0 ≤ xR ω j) (hxLa : ∀ ω, Antitone (xL ω))
    (hxRm : ∀ ω, Monotone (xR ω))
    (hword : ∀ᵐ ω ∂P, flowLineNL (cw ω).fn (cw ω).jumps 0 = nL ∧ flowLineNR (cw ω).fn (cw ω).jumps 0 = nR ∧
      truncWord nL nR (padFL κ θ (cw ω).fn (cw ω).jumps) = ((xL ω, xR ω), (ρL, ρR)))
    {W : ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω)
    (hWa : StronglyAdapted 𝓗 W) {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {c : Ω → Chart}
    (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hlc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hint : ∀ φ : TestOn upperHalfPlaneOpens,
      Integrable (fun ω => Chart.chartTransport (hc ω) 1 (θ * chiC κ) (chiC κ) (h ω) φ) P)
    {rec : Ω → RecData} (hrec : Measurable[𝒢] rec) {ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρm : Measurable ρ)
    (hρ : IsPathRule ρ) {ρs : ℕ → RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρsm : ∀ n, Measurable (ρs n))
    (hρs : ∀ n, IsPathRule (ρs n)) (hρsfin : ∀ n x, ρs n x ≠ ⊤) (hρsmono : ∀ x, Monotone fun n => ρs n x)
    {V : Ω → ℝ≥0∞} (hVρ : ∀ ω, V ω = ρ (rec ω, fun u => W u ω))
    (hann : ∀ᵐ ω ∂P, (∀ n, ρs n (rec ω, fun u => W u ω) < V ω) ∧ ⨆ n, ρs n (rec ω, fun u => W u ω) = V ω)
    (hVthr : ∀ᵐ ω ∂P, V ω ≤ FCDet.thr ρL ρR W xL xR ω)
    (hlaw : HasSafeLaw κ ρL ρR P 𝓗 univ V W (geomLW W xL) (geomRW W xR)
      fun ω => Chart.chartTransport (hc ω) 1 (θ * chiC κ) (chiC κ) (h ω))
    (hmem : HasSafeMembers P 𝓗 univ V W fun ω => Chart.chartTransport (hc ω) 1 (θ * chiC κ) (chiC κ) (h ω)) :
    ∀ᵐ ω ∂P, IsStopDrvMatch (driverCode h12p hκ θ (cw ω, Chart.chartTransport (hc ω) 1 0 (chiC κ) (h ω)))
      (fun t => W t ω) (V ω) := by
  classical
  have h𝒢m : 𝒢 ≤ mΩ := h𝒢.trans (𝓗.le 0)
  set X : Ω → DistOn upperHalfPlaneOpens := fun ω => Chart.chartTransport (hc ω) 1 (θ * chiC κ) (chiC κ) (h ω)
    with hXdef
  set Hc : Ω → DistOn upperHalfPlaneOpens := fun ω => Chart.chartTransport (hc ω) 1 0 (chiC κ) (h ω) with hHcdef
  have hX : Measurable X := Chart.measurable_chartTransport_random' hc hdom hfwd hliftm hlc hhm 1 _ _
  have hHc : Measurable Hc := Chart.measurable_chartTransport_random' hc hdom hfwd hliftm hlc hhm 1 0 _
  have hWm : ∀ t, Measurable (W t) := fun t => (hWa t).measurable.mono (𝓗.le t) le_rfl
  have hrec0 : Measurable[𝓗 0] rec := hrec.mono h𝒢 le_rfl
  have hcwm : Measurable cw := hcw.mono h𝒢m le_rfl
  have hxL₀ : Measurable[𝓗 0] xL := hxL.mono h𝒢 le_rfl
  have hxR₀ : Measurable[𝓗 0] xR := hxR.mono h𝒢 le_rfl
  -- the stop
  have hVst : IsStoppingTime 𝓗 fun ω => (V ω : WithTop ℝ≥0) := by
    have e : (fun ω => (V ω : WithTop ℝ≥0)) = fun ω => (ρ (rec ω, fun u => W u ω) : WithTop ℝ≥0) :=
      funext fun ω => hVρ ω
    rw [e]
    exact isStoppingTime_recPathRule hrec0 hWa hρm hρ
  have hVm : ∀ t : ℝ≥0, MeasurableSet[𝓗 t] {ω | V ω ≤ t} := fun t => hVst t
  have hVmeas : Measurable V := by
    refine measurable_of_Iic fun t => ?_
    induction t using ENNReal.recTopCoe with
    | top => simp only [Iic_top, preimage_univ, MeasurableSet.univ]
    | coe t => exact 𝓗.le t _ (hVm t)
  have hWa₀ : AdaptedBefore 𝓗 V W := MartChar.adaptedBefore_of_stronglyAdapted hVm hWa
  have hVLa₀ : ∀ i, AdaptedBefore 𝓗 V (geomLW W xL i) := fun i =>
    MartChar.adaptedBefore_of_stronglyAdapted hVm (stronglyAdapted_geomLW hWa hWc hxL₀ i)
  have hVRa₀ : ∀ j, AdaptedBefore 𝓗 V (geomRW W xR j) := fun j =>
    MartChar.adaptedBefore_of_stronglyAdapted hVm (stronglyAdapted_geomRW hWa hWc hxR₀ j)
  have hXψ : ∀ ψ : TestOn upperHalfPlaneOpens, Measurable fun ω => X ω ψ := fun ψ =>
    ((measurable_pi_apply ψ).comp (Measurable.of_comap_le le_rfl)).comp hX
  have hcf := Aux79.isCouplingCharFun_of_hasSafeLaw X hXψ hlaw
    (ae_of_all _ (FCDet.isForceReg_thr hW0 hWc xL xR V)) (ae_of_all _ fun ω h => absurd (mem_univ ω) h) hWa₀
    hVLa₀ hVRa₀
  -- the announcing sequence in the usual augmentation
  have hU : ∀ t, 𝓗 t ≤ usualAugmentation 𝓗 P t := Ito.le_usualAugmentation 𝓗 P
  set T : ℕ → Ω → ℝ≥0 := fun n ω => (ρs n (rec ω, fun u => W u ω)).toNNReal with hTdef
  have hTcoe : ∀ n ω, ((T n ω : ℝ≥0) : ℝ≥0∞) = ρs n (rec ω, fun u => W u ω) := fun n ω =>
    ENNReal.coe_toNNReal (hρsfin n _)
  have hTst : ∀ n, IsStoppingTime 𝓗 fun ω => ((T n ω : ℝ≥0) : WithTop ℝ≥0) := fun n => by
    have e : (fun ω => ((T n ω : ℝ≥0) : WithTop ℝ≥0)) =
        fun ω => (ρs n (rec ω, fun u => W u ω) : WithTop ℝ≥0) := funext fun ω => hTcoe n ω
    rw [e]
    exact isStoppingTime_recPathRule hrec0 hWa (hρsm n) (hρs n)
  have hTann : Coupling.IsAnnouncingSeq (usualAugmentation 𝓗 P) P V T := by
    refine ⟨fun n t => hU t _ (hTst n t), fun ω n m hnm => ?_, fun n => ?_, ?_⟩
    · exact ENNReal.toNNReal_mono (hρsfin m _) (hρsmono _ hnm)
    · filter_upwards [hann] with ω hω
      rw [hTcoe]
      exact hω.1 n
    · filter_upwards [hann] with ω hω t ht
      rw [← hω.2] at ht
      obtain ⟨n, hn⟩ := lt_iSup_iff.1 ht
      refine ⟨n, ?_⟩
      rw [← ENNReal.coe_le_coe, hTcoe]
      exact hn.le
  have hWaU : StronglyAdapted (usualAugmentation 𝓗 P) W := fun t => (hWa t).mono (hU t)
  have hVstU : IsStoppingTime (usualAugmentation 𝓗 P) fun ω => (V ω : WithTop ℝ≥0) := fun t =>
    hU t _ (hVst t)
  have : (usualAugmentation 𝓗 P).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  -- (E-stop) on the enlargement
  obtain ⟨P₀, hP₀, 𝓦, B, hE, -, -⟩ := StoppedK2.isRandomWordEvolutionUpTo_prod_of_isCouplingCharFun
    (𝒢 := 𝒢) hκ (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0) (h𝒢.trans (hU 0))
    MeasurableSet.univ hxL hxR hxL0 hxR0 hxLa hxRm hW0 hWc hWaU hVstU hTann hint hcf
    (hVthr.mono fun ω h _ => h)
  -- the stopped K2 with kernel stops
  have hm' : 𝒢.comap Prod.fst ≤ (inferInstance : MeasurableSpace (Ω × (ℕ → ℝ))) :=
    (MeasurableSpace.comap_mono h𝒢m).trans measurable_fst.comap_le
  have hcw' : Measurable[𝒢.comap Prod.fst] fun p : Ω × (ℕ → ℝ) => cw p.1 :=
    hcw.comp (Measurable.of_comap_le le_rfl)
  have hrec' : Measurable[𝒢.comap Prod.fst] fun p : Ω × (ℕ → ℝ) => rec p.1 :=
    hrec.comp (Measurable.of_comap_le le_rfl)
  have hkst : ∀ n, Supp8.Q3Stop.IsKernelStop (𝒢.comap Prod.fst) (P.prod P₀) (Prod.fst ⁻¹' univ)
      (fun t p => W t p.1) (fun i t p => geomLW W xL i t p.1) (fun j t p => geomRW W xR j t p.1)
      (fun p => V p.1) fun p => (ρs n (rec p.1, fun u => W u p.1) : WithTop ℝ≥0) := fun n =>
    Supp8.Q3Stop.isKernelStop_of_pathRule (P := P.prod P₀) hm' hrec' (hρsm n) (hρs n)
      (fun t => (hWm t).comp measurable_fst) ⟨univ, MeasurableSet.univ, rfl⟩
      (ConverseBefore.ae_fst_of_ae (P₀ := P₀) (hann.mono fun ω h _ => h.1 n))
  have hV0P : ∀ᵐ ω ∂P, ω ∈ univ → 0 < V ω := hann.mono fun ω h _ => lt_of_le_of_lt zero_le (h.1 0)
  have hσVP : ∀ᵐ ω ∂P, ω ∈ univ → ∀ n, ρs n (rec ω, fun u => W u ω) < V ω := hann.mono fun ω h _ n => h.1 n
  have hlimP : ∀ᵐ ω ∂P, ω ∈ univ → Tendsto (fun n => ρs n (rec ω, fun u => W u ω)) atTop (𝓝 (V ω)) := by
    filter_upwards [hann] with ω h _
    rw [← h.2]
    exact tendsto_atTop_iSup fun n m hnm => hρsmono _ hnm
  have hK := Supp8.Q3Stop.ae_isStoppedHullCoupling_kk_prod (P₀ := P₀) (F := univ) (ΘL := xL) (ΘR := xR)
    (σ := fun n p => (ρs n (rec p.1, fun u => W u p.1) : WithTop ℝ≥0)) hE
    (ae_of_all _ fun ω _ _ => ⟨(hWc ω).continuousOn, fun i => (isForcePath_geomLW hWc xL ω i).1.continuousOn,
      fun j => (isForcePath_geomRW hWc xR ω j).1.continuousOn⟩) hX
    hV0P h𝒢 hWa₀ hVLa₀ hVRa₀ hlaw hmem hkst (fun p n m hnm => hρsmono _ hnm)
    (ConverseBefore.ae_fst_of_ae (P₀ := P₀) hσVP) (ConverseBefore.ae_fst_of_ae (P₀ := P₀) hlimP)
  -- the match under almost every conditional law
  set G : Ω → PCode × ℝ≥0∞ := fun ω => driverCode h12p hκ θ (cw ω, Hc ω) with hGdef
  have hGm : Measurable G := (measurable_driverCode h12p hκ θ).comp (hcwm.prodMk hHc)
  have hQm : MeasurableSet {ω | IsStopDrvMatch (G ω) (fun t => W t ω) (V ω)} :=
    measurableSet_isStopDrvMatch hGm hWm hVmeas
  have hkm : ∀ᵐ p₀ ∂(P.prod P₀), ∀ᵐ p ∂(condExpKernel (P.prod P₀) (𝒢.comap Prod.fst) p₀),
      p ∈ Prod.fst ⁻¹' {ω | IsStopDrvMatch (G ω) (fun t => W t ω) (V ω)} := by
    filter_upwards [hK, Sec7.Lemma725RefK2.ae_ae_condExpKernel_eq_self (P := P.prod P₀) hm' hcw',
      Sec7.Lemma725RefK2.ae_ae_condExpKernel_eq_self (P := P.prod P₀) hm' hrec',
      ConverseBefore.ae_fst_of_ae (P₀ := P₀) hword] with p₀ hp₀ hfc₀ hfr₀ hw₀
    obtain ⟨𝓕', W', VL', VR', B', hSC, hag, hfrz⟩ := hp₀ (mem_univ _)
    obtain ⟨hn1, hn2, htw⟩ := hw₀
    obtain ⟨VL'', VR'', hSC'⟩ := isStoppedHullCoupling_flowLineWord_of_truncWord (θ := θ) hn1 hn2 htw hSC
    have hRe : ∀ᵐ p ∂(condExpKernel (P.prod P₀) (𝒢.comap Prod.fst) p₀),
        V p.1 = histRule ρ (rec p₀.1) (killedHistory W' VL'' VR'' (fun p => V p.1) p) := by
      filter_upwards [hag, hfrz, hfr₀] with p hp hfp hrp
      have hcont' : Continuous fun t => W' t p :=
        continuous_of_frozen_agree (hWc p.1) (fun t ht => (hp t ht).1) hfp
      have h0 : W' 0 p = 0 := by rw [(hp 0 zero_le).1, hW0]
      have hVr : V p.1 = ρ (rec p₀.1, fun u => W u p.1) := by rw [hVρ p.1, hrp]
      have hρe : V p.1 = ρ (rec p₀.1, fun t => W' t p) := by
        rw [hρ (rec p₀.1) (fun u => W u p.1) (fun t => W' t p) fun u hu =>
          ((hp u (by rw [hVr]; exact hu)).1).symm]
        exact hVr
      exact (Supp8.GB6.HullId.histRule_killedHistory (r := rec p₀.1) (W := W') (VL := VL'') (VR := VR'')
        (e := fun p => V p.1) hρ hcont' h0 hρe).symm
    have hreg := Aux54.isRegularStop_of_frozen hSC' hfrz
    have hmatch := ae_isStopDrvMatch_driverCode_of_stopped h12p hκ θ h13 (cw p₀.1)
      (Q := condExpKernel (P.prod P₀) (𝒢.comap Prod.fst) p₀) (Hc := fun p => Hc p.1) (X := fun p => X p.1)
      (𝓕 := 𝓕') (W := W') (VL := VL'') (VR := VR'') (B := B') (e := fun p => V p.1)
      (R := histRule ρ (rec p₀.1))
      (fun p => CondDriverBridge.isTranslateAddConst_chartTransport (hc p.1) _ _ _) hSC'
      (Supp8.GB6.HullId.measurable_histRule hρm (rec p₀.1)) (Supp8.GB6.HullId.isHistGalmarino_histRule hρ _)
      hRe hreg (Wb := fun t p => W t p.1) (fun t => (hWm t).comp measurable_fst) (hHc.comp measurable_fst)
      (hVmeas.comp measurable_fst) (hag.mono fun p hp t ht => (hp t ht).1)
    filter_upwards [hmatch, hfc₀] with p hp hcp
    show IsStopDrvMatch (driverCode h12p hκ θ (cw p.1, Hc p.1)) (fun t => W t p.1) (V p.1)
    rw [hcp]
    exact hp
  exact ConverseBefore.ae_of_ae_fst (P₀ := P₀) (q := fun ω => IsStopDrvMatch (G ω) (fun t => W t ω) (V ω))
    (Sec5.Lemma56Stages.ae_of_ae_condExpKernel hm' (measurable_fst hQm) hkm)

/-- **The same on a live event `F ∈ 𝒢`, with integrability on `F` only**: all inputs are asked on `F`. Proof: the
unconditioned form under `P[·|F]` (`BW1Chain.hasSafeLaw_cond`, `BW1Chain.hasSafeMembers_cond`). -/
theorem ae_isStopDrvMatch_of_hasSafeLaw_rule_on (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) {𝓗 : Filtration ℝ≥0 mΩ} (h𝒢 : 𝒢 ≤ 𝓗 0)
    {F : Set Ω} (hF : MeasurableSet[𝒢] F) {cw : Ω → BoundaryWord} (hcw : Measurable[𝒢] cw)
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} (hxL : Measurable[𝒢] xL) (hxR : Measurable[𝒢] xR)
    (hxL0 : ∀ ω i, xL ω i ≤ 0) (hxR0 : ∀ ω j, 0 ≤ xR ω j) (hxLa : ∀ ω, Antitone (xL ω))
    (hxRm : ∀ ω, Monotone (xR ω))
    (hword : ∀ᵐ ω ∂P, ω ∈ F → flowLineNL (cw ω).fn (cw ω).jumps 0 = nL ∧
      flowLineNR (cw ω).fn (cw ω).jumps 0 = nR ∧
      truncWord nL nR (padFL κ θ (cw ω).fn (cw ω).jumps) = ((xL ω, xR ω), (ρL, ρR)))
    {W : ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω)
    (hWa : StronglyAdapted 𝓗 W) {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {c : Ω → Chart}
    (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hlc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hint : ∀ φ : TestOn upperHalfPlaneOpens,
      IntegrableOn (fun ω => Chart.chartTransport (hc ω) 1 (θ * chiC κ) (chiC κ) (h ω) φ) F P)
    {rec : Ω → RecData} (hrec : Measurable[𝒢] rec) {ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρm : Measurable ρ)
    (hρ : IsPathRule ρ) {ρs : ℕ → RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρsm : ∀ n, Measurable (ρs n))
    (hρs : ∀ n, IsPathRule (ρs n)) (hρsfin : ∀ n x, ρs n x ≠ ⊤) (hρsmono : ∀ x, Monotone fun n => ρs n x)
    {V : Ω → ℝ≥0∞} (hVρ : ∀ ω, V ω = ρ (rec ω, fun u => W u ω))
    (hann : ∀ᵐ ω ∂P, ω ∈ F →
      (∀ n, ρs n (rec ω, fun u => W u ω) < V ω) ∧ ⨆ n, ρs n (rec ω, fun u => W u ω) = V ω)
    (hVthr : ∀ᵐ ω ∂P, ω ∈ F → V ω ≤ FCDet.thr ρL ρR W xL xR ω)
    (hlaw : HasSafeLaw κ ρL ρR P 𝓗 F V W (geomLW W xL) (geomRW W xR)
      fun ω => Chart.chartTransport (hc ω) 1 (θ * chiC κ) (chiC κ) (h ω))
    (hmem : HasSafeMembers P 𝓗 F V W fun ω => Chart.chartTransport (hc ω) 1 (θ * chiC κ) (chiC κ) (h ω)) :
    ∀ᵐ ω ∂P, ω ∈ F → IsStopDrvMatch (driverCode h12p hκ θ (cw ω, Chart.chartTransport (hc ω) 1 0 (chiC κ) (h ω)))
      (fun t => W t ω) (V ω) := by
  have h𝒢m : 𝒢 ≤ mΩ := h𝒢.trans (𝓗.le 0)
  have hFm : MeasurableSet F := h𝒢m _ hF
  by_cases hPF : P F = 0
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hPF] with ω h1 h2 using absurd h2 h1
  have : IsProbabilityMeasure (ProbabilityTheory.cond P F) := ProbabilityTheory.cond_isProbabilityMeasure hPF
  have hF0 : MeasurableSet[𝓗 0] F := h𝒢 _ hF
  exact BW1Chain.ae_of_ae_cond hFm (ae_isStopDrvMatch_of_hasSafeLaw_rule (P := ProbabilityTheory.cond P F) h12p h13
    hκ h𝒢 hcw hxL hxR hxL0 hxR0 hxLa hxRm (BW1Chain.ae_cond_of_ae hFm hword) hW0 hWc hWa hhm hc hdom hfwd
    hliftm hlc (fun φ => Lv.integrable_cond_of_integrableOn (hint φ)) hrec hρm hρ hρsm hρs hρsfin hρsmono hVρ
    (BW1Chain.ae_cond_of_ae hFm hann) (BW1Chain.ae_cond_of_ae hFm hVthr) (BW1Chain.hasSafeLaw_cond hF0 hlaw)
    (BW1Chain.hasSafeMembers_cond hF0 hmem))

end Main

end InteractingSLE.Theorem14.SB.Cond
