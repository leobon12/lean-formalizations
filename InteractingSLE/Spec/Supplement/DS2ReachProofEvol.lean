/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.DS2ReachProofGood
import InteractingSLE.Spec.Sec2.GirsanovCut
import QuantumZipper.Proofs.RS.TransienceCanon

/-!
# DS2 in reach form, V: the stopped state path and the Brownian path of one evolution

Packet PROVE-T14-DS. For an integrated `SLE_κ(ρ)` evolution of a DS1 word started in the outer closed buffer:

* `EvolData`: a continuous version `b` of its Brownian motion and a measurable conull set `G` of outcomes whose paths
  are good (`GoodPath`); `exists_evolData` constructs it;
* `fR`, `bR`: the stopped state path in `C([0, T], ℝ × ℝ^{n_L} × ℝ^{n_R})` and the Brownian path in `C([0, T], ℝ)`;
  `EvolData.aemeasurable_fR`, `measurable_bR`;
* `EvolData.law`: the joint law of `(fR, bR)`, a probability measure on the product of path spaces;
* `EvolData.map_bR_eq`: the law of the Brownian path does not depend on the evolution;
* `EvolData.measure_reachEvent_eq`: the reach event has the probability the joint law gives the reach set.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Finset ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp12

namespace DSReach

open DS2
open scoped PathMeas

section Paths

variable {nL nR : ℕ} {Ω : Type*}

/-- The **stopped state path** of the processes `(W, V^L, V^R)` at `ω`, stopped at the exit from the closed
buffer. -/
def fR (mL mR : ℕ) (R g : ℝ) (T : ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : C(Set.Icc (0 : ℝ≥0) T, SState nL nR) :=
  stopPath (cBuf mL mR R g) T (stOf (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω)) (ζ ω) 0

/-- The **Brownian path** on `[0, T]` of a process with continuous paths. -/
def bR (T : ℝ≥0) (b : ℝ≥0 → Ω → ℝ) (hb : ∀ ω, Continuous (b · ω)) (ω : Ω) : C(Set.Icc (0 : ℝ≥0) T, ℝ) :=
  ⟨fun t => b t ω, (hb ω).comp continuous_subtype_val⟩

/-- The exit time from the closed buffer at `ω`. -/
def τR (mL mR : ℕ) (R g : ℝ) (T : ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0 :=
  exitTime (cBuf mL mR R g) T (stOf (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω)) (ζ ω)

/-- **Occupation integral up to the exit**: `∫_{(0, T]} 1{s ≤ τ} φ(gp(f s)) ds` for a functional `gp` of the
state and the stopped path `f`. -/
def occ (mL mR : ℕ) (R g : ℝ) (T : ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (φ : ℝ → ℝ≥0∞) (gp : SState nL nR → ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ s in Ioc (0 : ℝ) T, {s : ℝ | s ≤ τR mL mR R g T W VL VR ζ ω}.indicator
    (fun s => φ (gp (pathAt (fR mL mR R g T W VL VR ζ ω) s.toNNReal))) s

theorem measurable_bR [MeasurableSpace Ω] (T : ℝ≥0) {b : ℝ≥0 → Ω → ℝ} (hb : ∀ ω, Continuous (b · ω))
    (hbm : ∀ t, Measurable (b t)) : Measurable (bR T b hb) :=
  measurable_to_pathSpace _ fun t => hbm t

end Paths

section Evol

variable {κ : ℝ} {nL nR : ℕ} {mL mR : ℕ} {Rw ε R g : ℝ} {T : ℝ≥0} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Data of one evolution**: a continuous version `b` of the Brownian motion and a measurable conull set `G` of
good outcomes, with the killed state measurable at every fixed time. -/
structure EvolData (κ : ℝ) (mL mR : ℕ) (Rw ε R g : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) where
  b : ℝ≥0 → Ω → ℝ
  meas_b : ∀ t, Measurable (b t)
  cont_b : ∀ ω, Continuous (b · ω)
  brown : IsPreBrownianReal b P
  G : Set Ω
  meas_G : MeasurableSet G
  null_G : P Gᶜ = 0
  good : ∀ ω ∈ G, GoodPath κ mL mR Rw ε R g xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
    (fun j t => VR j t ω) (fun t => b t ω) (ζ ω)
  kill : ∀ q : ℝ≥0, Measurable fun ω =>
    if (q : ℝ≥0∞) < ζ ω then stOf (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) q else 0
  meas_ζ : ∀ q : ℝ≥0, MeasurableSet {ω | (q : ℝ≥0∞) < ζ ω}

/-- **Construction of the data of an evolution** of a DS1 word started in the outer closed buffer. -/
theorem exists_evolData {𝓕 : MeasureTheory.Filtration ℝ≥0 ‹MeasurableSpace Ω›} {B : ℝ≥0 → Ω → ℝ}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hw : IsDS1Word mL mR Rw ε xL xR ρL ρR)
    (h0 : ((0 : ℝ), xL, xR) ∈ cBuf (nL := nL) (nR := nR) mL mR R g) :
    Nonempty (EvolData κ mL mR Rw ε R g xL xR ρL ρR P W VL VR ζ) := by
  obtain ⟨hB, hW, hVL, hVR, hpath⟩ := hE
  obtain ⟨b, hbm, hbc, -, hbB, hbeq⟩ := QuantumZipper.RS.exists_good_version0 hB.1
  set G₀ : Set Ω := {ω | GoodPath κ mL mR Rw ε R g xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
    (fun j t => VR j t ω) (fun t => b t ω) (ζ ω)} with hG₀
  have hG₀ae : ∀ᵐ ω ∂P, ω ∈ G₀ := by
    filter_upwards [hpath, hbeq] with ω hp hb
    have e : (fun t => b t ω) = fun t => B t ω := funext hb
    exact ⟨e ▸ hp, hbc ω, hw, h0⟩
  obtain ⟨N, hNsup, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hG₀ae)
  have hmono : ∀ (q : ℝ≥0) (X : ℝ≥0 → Ω → ℝ), AdaptedBefore 𝓕 ζ X → Measurable (Girsanov.killed ζ X q) :=
    fun q X hX => (Girsanov.measurable_killed hX q).mono (𝓕.le q) le_rfl
  refine ⟨⟨b, hbm, hbc, hbB.toIsPreBrownianReal, Nᶜ, hNm.compl, by rwa [compl_compl],
    fun ω hω => ?_, fun q => ?_, fun q => ?_⟩⟩
  · by_contra hcon
    exact hω (hNsup hcon)
  · have e : (fun ω => if (q : ℝ≥0∞) < ζ ω then
        stOf (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) q else 0) =
        fun ω => ((Girsanov.killed ζ W q ω, fun i => Girsanov.killed ζ (VL i) q ω,
          fun j => Girsanov.killed ζ (VR j) q ω) : SState nL nR) := by
      funext ω
      by_cases h : (q : ℝ≥0∞) < ζ ω
      · simp only [h, ↓reduceIte, stOf, Girsanov.killed_of_lt h]
      · simp only [h, ↓reduceIte, Girsanov.killed]
        rfl
    rw [e]
    exact (hmono q W hW).prodMk ((measurable_pi_iff.2 fun i => hmono q (VL i) (hVL i)).prodMk
      (measurable_pi_iff.2 fun j => hmono q (VR j) (hVR j)))
  · have := hW q univ MeasurableSet.univ
    simp only [Set.mem_univ, and_true] at this
    exact 𝓕.le q _ this

namespace EvolData

variable (D : EvolData κ mL mR Rw ε R g xL xR ρL ρR P W VL VR ζ)

theorem ae_mem_G : ∀ᵐ ω ∂P, ω ∈ D.G :=
  (measure_eq_zero_iff_ae_notMem.1 D.null_G).mono fun _ hω => not_not.1 hω

/-- The Brownian path of the data. -/
def bP (T : ℝ≥0) : Ω → C(Set.Icc (0 : ℝ≥0) T, ℝ) := bR T D.b D.cont_b

theorem measurable_bP (T : ℝ≥0) : Measurable (D.bP T) := measurable_bR T D.cont_b D.meas_b

open Classical in
/-- **The stopped state path is measurable on the good set.** -/
theorem measurable_fR_piecewise (hε : 0 < ε) (hg : 0 < g) (T : ℝ≥0) :
    Measurable fun ω => if ω ∈ D.G then fR mL mR R g T W VL VR ζ ω else ContinuousMap.const _ 0 :=
  measurable_stopPath_piecewise (isClosed_cBuf mL mR R g) D.meas_G D.kill D.meas_ζ
    fun ω hω => (D.good ω hω).stop hε hg

theorem fR_ae_eq (T : ℝ≥0) [DecidablePred (· ∈ D.G)] :
    (fR mL mR R g T W VL VR ζ) =ᵐ[P] fun ω => if ω ∈ D.G then fR mL mR R g T W VL VR ζ ω
      else ContinuousMap.const _ 0 := by
  filter_upwards [D.ae_mem_G] with ω hω
  simp only [hω, ↓reduceIte]

include D in
theorem aemeasurable_fR (hε : 0 < ε) (hg : 0 < g) (T : ℝ≥0) :
    AEMeasurable (fR mL mR R g T W VL VR ζ) P := by
  classical
  exact (D.measurable_fR_piecewise hε hg T).aemeasurable.congr (D.fR_ae_eq T).symm

theorem aemeasurable_pair (hε : 0 < ε) (hg : 0 < g) (T : ℝ≥0) :
    AEMeasurable (fun ω => (fR mL mR R g T W VL VR ζ ω, D.bP T ω)) P :=
  (D.aemeasurable_fR hε hg T).prodMk (D.measurable_bP T).aemeasurable

/-- The **joint law** of the stopped state path and the Brownian path. -/
def law (T : ℝ≥0) : Measure (C(Set.Icc (0 : ℝ≥0) T, SState nL nR) × C(Set.Icc (0 : ℝ≥0) T, ℝ)) :=
  P.map fun ω => (fR mL mR R g T W VL VR ζ ω, D.bP T ω)

theorem isProbabilityMeasure_law [IsProbabilityMeasure P] (hε : 0 < ε) (hg : 0 < g) (T : ℝ≥0) :
    IsProbabilityMeasure (D.law T) := by
  have _ := hε; have _ := hg
  rw [law]; infer_instance

theorem law_snd (hε : 0 < ε) (hg : 0 < g) (T : ℝ≥0) :
    (D.law T).map Prod.snd = P.map (D.bP T) := by
  rw [law, AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable (D.aemeasurable_pair hε hg T)]
  rfl

/-- **The law of the Brownian path does not depend on the evolution.** -/
theorem map_bP_eq [IsProbabilityMeasure P] {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {κ' : ℝ} {mL' mR' : ℕ} {Rw' ε' R' g' : ℝ} {nL' nR' : ℕ}
    {xL' : Fin nL' → ℝ} {xR' : Fin nR' → ℝ} {ρL' : Fin nL' → ℝ} {ρR' : Fin nR' → ℝ}
    {W' : ℝ≥0 → Ω' → ℝ} {VL' : Fin nL' → ℝ≥0 → Ω' → ℝ} {VR' : Fin nR' → ℝ≥0 → Ω' → ℝ} {ζ' : Ω' → ℝ≥0∞}
    (D' : EvolData κ' mL' mR' Rw' ε' R' g' xL' xR' ρL' ρR' P' W' VL' VR' ζ') (T : ℝ≥0) :
    P.map (D.bP T) = P'.map (D'.bP T) := by
  have hres : Measurable fun f : QuantumZipper.RS.CPath =>
      (⟨fun t => f.1 t, f.2.comp continuous_subtype_val⟩ : C(Set.Icc (0 : ℝ≥0) T, ℝ)) :=
    measurable_to_pathSpace _ fun t => QuantumZipper.RS.measurable_canonBM t
  have e1 : D.bP T = (fun f : QuantumZipper.RS.CPath =>
      (⟨fun t => f.1 t, f.2.comp continuous_subtype_val⟩ : C(Set.Icc (0 : ℝ≥0) T, ℝ))) ∘
        QuantumZipper.RS.toCPath D.b D.cont_b := rfl
  have e2 : D'.bP T = (fun f : QuantumZipper.RS.CPath =>
      (⟨fun t => f.1 t, f.2.comp continuous_subtype_val⟩ : C(Set.Icc (0 : ℝ≥0) T, ℝ))) ∘
        QuantumZipper.RS.toCPath D'.b D'.cont_b := rfl
  rw [e1, e2, ← Measure.map_map hres (QuantumZipper.RS.measurable_toCPath D.meas_b D.cont_b),
    ← Measure.map_map hres (QuantumZipper.RS.measurable_toCPath D'.meas_b D'.cont_b)]
  congr 1
  exact QuantumZipper.RS.map_toCPath_eq D.brown D'.brown D.meas_b D'.meas_b D.cont_b D'.cont_b

/-- **The reach event in terms of the joint law**: for a buffer `Bf` inside the outer open buffer,
`P(reach) = law(reachSet × univ)`. -/
theorem measure_reachEvent_eq (hε : 0 < ε) (hg : 0 < g) (T : ℝ≥0) {O Bf : Set (SState nL nR)}
    (hO : IsOpen O) (hB : IsOpen Bf) (hBf : Bf ⊆ oBuf mL mR R g) :
    P (reachEvent T O Bf W VL VR ζ) = D.law T (reachSet T O Bf ×ˢ univ) := by
  rw [law, Measure.map_apply_of_aemeasurable (D.aemeasurable_pair hε hg T)
    ((isOpen_reachSet T hO hB).measurableSet.prod MeasurableSet.univ)]
  refine measure_congr ?_
  filter_upwards [D.ae_mem_G] with ω hω
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true, eq_iff_iff]
  rw [fR, mem_reachSet_stopPath_iff ((D.good ω hω).stop hε hg) 0
    (hBf.trans (oBuf_subset_interior_cBuf mL mR R g))]
  rfl

open Classical in
include D in
theorem aemeasurable_occ (hε : 0 < ε) (hg : 0 < g) (T : ℝ≥0) {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ)
    {gp : SState nL nR → ℝ} (hgp : Continuous gp) :
    AEMeasurable (occ mL mR R g T W VL VR ζ φ gp) P := by
  set τ' : Ω → ℝ≥0 := fun ω => if ω ∈ D.G then τR mL mR R g T W VL VR ζ ω else 0
  have hτ' : Measurable τ' := measurable_exitTime_piecewise (isClosed_cBuf mL mR R g) D.meas_G D.kill D.meas_ζ
    fun ω hω => ((D.good ω hω).stop (T := T) hε hg).1
  set f' : Ω → C(Set.Icc (0 : ℝ≥0) T, SState nL nR) := fun ω =>
    if ω ∈ D.G then fR mL mR R g T W VL VR ζ ω else ContinuousMap.const _ 0
  have hf' : Measurable f' := D.measurable_fR_piecewise hε hg T
  set F : Ω × ℝ → ℝ≥0∞ := fun q => {q : Ω × ℝ | q.2 ≤ τ' q.1}.indicator
    (fun q => φ (gp (pathAt (f' q.1) q.2.toNNReal))) q
  have hFm : Measurable F := by
    have h1 : Measurable fun q : Ω × ℝ => pathAt (f' q.1) q.2.toNNReal :=
      continuous_pathAt_uncurry.measurable.comp ((hf'.comp measurable_fst).prodMk
        (measurable_real_toNNReal.comp measurable_snd))
    exact (hφ.comp (hgp.measurable.comp h1)).indicator
      (measurableSet_le measurable_snd (measurable_coe_nnreal_real.comp (hτ'.comp measurable_fst)))
  have hm : Measurable fun ω => ∫⁻ s in Ioc (0 : ℝ) T, F (ω, s) := hFm.lintegral_prod_right'
  refine hm.aemeasurable.congr ?_
  filter_upwards [D.ae_mem_G] with ω hω
  refine lintegral_congr fun s => ?_
  simp only [F, τ', f', Set.indicator, Set.mem_ofPred_eq, hω, ↓reduceIte]

/-- The nearest right gap `V^{R,0} − W` of a state. -/
def gpR (hnR : 0 < nR) (p : SState nL nR) : ℝ := p.2.2 ⟨0, hnR⟩ - p.1

/-- The nearest left gap `W − V^{L,0}` of a state. -/
def gpL (hnL : 0 < nL) (p : SState nL nR) : ℝ := p.1 - p.2.1 ⟨0, hnL⟩

theorem continuous_gpR (hnR : 0 < nR) : Continuous (gpR (nL := nL) hnR) :=
  ((continuous_apply _).comp (continuous_snd.comp continuous_snd)).sub continuous_fst

theorem continuous_gpL (hnL : 0 < nL) : Continuous (gpL (nR := nR) hnL) :=
  continuous_fst.sub ((continuous_apply _).comp (continuous_fst.comp continuous_snd))

/-- On a good outcome, before the exit the stopped path is the state. -/
theorem pathAt_fR_of_le (hε : 0 < ε) (hg : 0 < g) {ω : Ω} (hω : ω ∈ D.G) {T : ℝ≥0} {s : ℝ≥0}
    (hs : s ≤ τR mL mR R g T W VL VR ζ ω) :
    pathAt (fR mL mR R g T W VL VR ζ ω) s =
      stOf (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) s := by
  have hsT : s ≤ T := hs.trans exitTime_le
  rw [pathAt_of_le _ hsT]
  exact stopPath_apply_of_le ((D.good ω hω).stop hε hg) 0 hs

/-- On a good outcome, a time before the exit is alive with far gaps `≥ g/2`. -/
theorem isAlive_of_le (hε : 0 < ε) (hg : 0 < g) {ω : Ω} (hω : ω ∈ D.G) {T : ℝ≥0} {s : ℝ≥0}
    (hs : s ≤ τR mL mR R g T W VL VR ζ ω) : DS1.IsAlive mL mR (g / 2) W VL VR ζ s ω := by
  have hstop := (D.good ω hω).stop (T := T) hε hg
  refine ⟨lt_of_le_of_lt (by exact_mod_cast hs) hstop.2, fun u hu => ?_⟩
  have hmem := (D.good ω hω).stOf_mem_cBuf_of_le hε hg (hu.trans hs)
  exact ⟨fun j hj => hmem.2.1 j hj, fun i hi => hmem.2.2 i hi⟩

/-- **The occupation integral up to the exit is at most DS1's alive integral** (right gap). -/
theorem occ_gpR_le (hε : 0 < ε) (hg : 0 < g) (hnR : 0 < nR) (T : ℝ≥0) (φ : ℝ → ℝ≥0∞) {ω : Ω}
    (hω : ω ∈ D.G) :
    occ mL mR R g T W VL VR ζ φ (gpR hnR) ω ≤
      ∫⁻ s in Ioc (0 : ℝ) T, {s : ℝ | DS1.IsAlive mL mR (g / 2) W VL VR ζ s.toNNReal ω}.indicator
        (fun s => φ (VR ⟨0, hnR⟩ s.toNNReal ω - W s.toNNReal ω)) s := by
  refine lintegral_mono fun s => ?_
  by_cases hs : s ≤ τR mL mR R g T W VL VR ζ ω
  · have hs' : s.toNNReal ≤ τR mL mR R g T W VL VR ζ ω := Real.toNNReal_le_iff_le_coe.2 hs
    rw [Set.indicator_of_mem (show s ∈ {s : ℝ | s ≤ τR mL mR R g T W VL VR ζ ω} from hs),
      Set.indicator_of_mem (show s ∈ {s : ℝ | DS1.IsAlive mL mR (g / 2) W VL VR ζ s.toNNReal ω} from
        D.isAlive_of_le hε hg hω hs'), D.pathAt_fR_of_le hε hg hω hs']
    rfl
  · rw [Set.indicator_of_notMem (show s ∉ {s : ℝ | s ≤ τR mL mR R g T W VL VR ζ ω} from hs)]
    exact bot_le

/-- **The occupation integral up to the exit is at most DS1's alive integral** (left gap). -/
theorem occ_gpL_le (hε : 0 < ε) (hg : 0 < g) (hnL : 0 < nL) (T : ℝ≥0) (φ : ℝ → ℝ≥0∞) {ω : Ω}
    (hω : ω ∈ D.G) :
    occ mL mR R g T W VL VR ζ φ (gpL hnL) ω ≤
      ∫⁻ s in Ioc (0 : ℝ) T, {s : ℝ | DS1.IsAlive mL mR (g / 2) W VL VR ζ s.toNNReal ω}.indicator
        (fun s => φ (W s.toNNReal ω - VL ⟨0, hnL⟩ s.toNNReal ω)) s := by
  refine lintegral_mono fun s => ?_
  by_cases hs : s ≤ τR mL mR R g T W VL VR ζ ω
  · have hs' : s.toNNReal ≤ τR mL mR R g T W VL VR ζ ω := Real.toNNReal_le_iff_le_coe.2 hs
    rw [Set.indicator_of_mem (show s ∈ {s : ℝ | s ≤ τR mL mR R g T W VL VR ζ ω} from hs),
      Set.indicator_of_mem (show s ∈ {s : ℝ | DS1.IsAlive mL mR (g / 2) W VL VR ζ s.toNNReal ω} from
        D.isAlive_of_le hε hg hω hs'), D.pathAt_fR_of_le hε hg hω hs']
    rfl
  · rw [Set.indicator_of_notMem (show s ∉ {s : ℝ | s ≤ τR mL mR R g T W VL VR ζ ω} from hs)]
    exact bot_le

/-- `ofReal ∫₀^τ φ ≤ ∫⁻_{(0,T]} 1{s ≤ τ} ofReal φ` for nonnegative `φ` and `τ ≤ T`. -/
theorem ofReal_intervalIntegral_le {τ T : ℝ≥0} (hτT : τ ≤ T) {F G : ℝ → ℝ} (hF : ∀ s, 0 ≤ F s)
    (hFG : ∀ s : ℝ, 0 < s → s ≤ (τ : ℝ) → F s = G s) :
    ENNReal.ofReal (∫ u in (0 : ℝ)..τ, F u) ≤
      ∫⁻ s in Ioc (0 : ℝ) T, {s : ℝ | s ≤ τ}.indicator (fun s => ENNReal.ofReal (G s)) s := by
  rw [intervalIntegral.integral_of_le τ.coe_nonneg]
  have hle : ENNReal.ofReal (∫ u in Ioc (0 : ℝ) τ, F u) ≤ ∫⁻ u in Ioc (0 : ℝ) τ, ENNReal.ofReal (F u) := by
    by_cases hI : Integrable F (volume.restrict (Ioc (0 : ℝ) τ))
    · rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hF) hI.aestronglyMeasurable]
      exact ENNReal.ofReal_toReal_le
    · rw [integral_undef hI, ENNReal.ofReal_zero]
      exact bot_le
  refine hle.trans ?_
  rw [← lintegral_indicator measurableSet_Ioc, ← lintegral_indicator measurableSet_Ioc]
  refine lintegral_mono fun s => ?_
  by_cases hs : s ∈ Ioc (0 : ℝ) τ
  · have hsT : s ∈ Ioc (0 : ℝ) T := ⟨hs.1, hs.2.trans (by exact_mod_cast hτT)⟩
    rw [Set.indicator_of_mem hs, Set.indicator_of_mem hsT,
      Set.indicator_of_mem (show s ∈ {s : ℝ | s ≤ τ} from hs.2), hFG s hs.1 hs.2]
  · rw [Set.indicator_of_notMem hs]
    exact bot_le

/-- **The truncated inverse-gap integral of the modulus is bounded by the occupation integral** (right gap). -/
theorem ofReal_iR_le_occ (hε : 0 < ε) (hg : 0 < g) (hnR : 0 < nR) (T : ℝ≥0) (δ : ℝ) {ω : Ω}
    (hω : ω ∈ D.G) :
    ENNReal.ofReal ((D.good ω hω).iR hnR T δ) ≤
      occ mL mR R g T W VL VR ζ (fun x => ENNReal.ofReal (invCut δ x)) (gpR hnR) ω := by
  refine ofReal_intervalIntegral_le exitTime_le (fun _ => invCut_nonneg _ _) fun s _ hs => ?_
  have hs' : s.toNNReal ≤ τR mL mR R g T W VL VR ζ ω := Real.toNNReal_le_iff_le_coe.2 hs
  simp only [D.pathAt_fR_of_le hε hg hω hs']
  rfl

/-- **The truncated inverse-gap integral of the modulus is bounded by the occupation integral** (left gap). -/
theorem ofReal_iL_le_occ (hε : 0 < ε) (hg : 0 < g) (hnL : 0 < nL) (T : ℝ≥0) (δ : ℝ) {ω : Ω}
    (hω : ω ∈ D.G) :
    ENNReal.ofReal ((D.good ω hω).iL hnL T δ) ≤
      occ mL mR R g T W VL VR ζ (fun x => ENNReal.ofReal (invCut δ x)) (gpL hnL) ω := by
  refine ofReal_intervalIntegral_le exitTime_le (fun _ => invCut_nonneg _ _) fun s _ hs => ?_
  have hs' : s.toNNReal ≤ τR mL mR R g T W VL VR ζ ω := Real.toNNReal_le_iff_le_coe.2 hs
  simp only [D.pathAt_fR_of_le hε hg hω hs']
  rfl

end EvolData

end Evol

end DSReach

end Supp12

end InteractingSLE
