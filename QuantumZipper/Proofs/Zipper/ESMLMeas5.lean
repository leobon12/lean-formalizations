import QuantumZipper.Proofs.Zipper.ESMLMeas3
import QuantumZipper.Proofs.Zipper.ESMLMeas4
import QuantumZipper.Proofs.Zipper.ESMCompl
import QuantumZipper.Proofs.Zipper.B1Full
import QuantumZipper.Proofs.Zipper.E1TransferM4Main

/-!
# ESM-LMEAS-5: measurability of the path functional `lenMinusSur`

Fifth part of the ESM-LMEAS task (node **E-SM**, obligation `hLad` of
`ESM.lintegral_levelTime_strongMarkov_lenA`, decision D21). `ESMLMeas3` defines the
deterministic path functional `lenMinusSur κ s hs γ a` of the data
`(x, f) : FieldSample × C(I[0,s], ℝ)` whose value at `(X ω, pathC s B ω)` is a.s. equal to the
intrinsic left length `L⁻_s` (`ae_lenMinus_eq_surrogate`), and reduces the adaptedness of `L⁻_s`
to the measurability of that deterministic functional (`measurable_lenMinus_of_surrogate`).
Here we prove that measurability:

* `measurable_revPath` (step ib): `f ↦ revPath s hs f` is Borel measurable on
  `C(I[0,s], ℝ)` — pointwise evaluation at a fixed point of `C(I[0,s], ℝ)` is measurable
  (`ContinuousMap.measurable_eval`, `Continuous.measurable`), and
  `revPath s hs f u = f (s - u) - f s` (`revPath_apply`), so
  `ContinuousMap.measurable_iff_eval` reduces the claim to a difference of two measurable
  evaluation maps.
* `measurable_coordsFull_unzipFieldPath` / `measurable_unzipFieldCoord` (step ia): the circle
  coordinates of the path–surrogate field are measurable, by
  `B1Full.measurable_unzip_apply` (measurability of the unzipped field at a fixed folded
  circle, whose measure is carried by `ℍ`) and `measurable_fromCoords` (the coordinate
  reconstruction `fromCoords` is measurable).
* `measurable_nuSur`: the `BCert`-gated boundary measure of the surrogate field is a Giry
  measurable family, by composition with `E1.M4.measurable_qBoundaryMeasure_bCert`.
* `measurable_measure_Icc_zero_of_finite` (step ic): for a Giry measurable family `ν` of
  measures on `ℝ`, a measurable left endpoint `b` and finite mass on the windows
  `Icc (-N) N`, the map `p ↦ ν p (Icc (b p) 0)` is measurable. This is the pattern of
  `B5.measurable_RP` (`B5VHccMeas.lean`): exhaust the window by the increasing family
  `Icc (b p) 0 ∩ Icc (-N) N`, write each `ν p (S) = ∫⁻ y in Icc (-N) N, S.indicator 1 (p,y)`,
  and use `Measurable.iSup` with `E1.M4.measurable_setLIntegral_of_measurable_measure`.
  (A finiteness hypothesis on the windows is unavoidable: the statement without it is false,
  e.g. for the constant family `ν p =` counting measure on `ℚ`, which is measurable and gives
  `ν p (Icc 0 1) = ∞`; `measurable_setLIntegral_of_measurable_measure` itself needs it.)
* `nuSur_Icc_lt_top` and `measurable_nuSur_Icc_zero`: the finiteness on windows holds for
  `nuSur κ s hs γ` (junk `0` off the certificate; on it, the boundary measure is finite on
  compacts by `E1.M4.exists_isVagueLimitR_of_bCert`), whence the endpoint map is measurable.
* `measurable_lenMinusSur`: `Measurable (lenMinusSur κ s hs γ a)` for measurable
  `a : C(I[0,s], ℝ) → ℝ × ℝ`, by `measurable_nuSur_Icc_zero` at `b p = (a p.2).1`.

The measurability plumbing is **own bookkeeping** (as in `E1TransferM4Main`, `B5VHccMeas`); the
mathematical source of the surrounding statements is Sheffield, arXiv:1012.4797, proof of
Lemma 5.6 (pp. 66–68).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace ESM

open F1 CoordsFull CharFun

/-! ## 1. Measurability of the time-reversed path (step ib) -/

/-- **Step ib**: the time-reversed path depends measurably on the path. On
`C(I[0,s], ℝ)` (Borel σ-algebra of the compact-open topology) the claim reduces, by
`ContinuousMap.measurable_iff_eval`, to the measurability of
`f ↦ revPath s hs f u = f ⟨s - u, _⟩ - f ⟨s, _⟩` for each `u : I[0,s]`, i.e. to a difference
of two evaluation maps. -/
theorem measurable_revPath (s : ℝ) (hs : 0 ≤ s) : Measurable (revPath s hs) :=
  ContinuousMap.measurable_iff_eval.2 fun _ =>
    (continuous_eval_const _).measurable.sub (continuous_eval_const _).measurable

/-! ## 2. Measurability of the path–surrogate field (step ia) -/

/-- The path–surrogate field evaluated at a single folded circle is measurable: piece it
together from the measurability of the unzipped field at that fixed measure
(`B1Full.measurable_unzip_apply`, whose hypothesis `foldedCircle w r Hᶜ = 0` holds for positive
radius, `foldedCircle_compl_H_eq_zero`) and of the time-reversed path `measurable_revPath`. -/
theorem measurable_unzipFieldPath_apply (κ s : ℝ) (hs : 0 ≤ s) (i : ℕ) :
    Measurable fun p : FieldSample × C(Icc (0 : ℝ) s, ℝ) =>
      unzipFieldPath κ s hs p (foldedCircle (fullIndex i).1 (fullIndex i).2) := by
  have hμ : foldedCircle (fullIndex i).1 (fullIndex i).2 Hᶜ = 0 :=
    foldedCircle_compl_H_eq_zero _ (UnzipFull.fullIndex_radius_pos i)
  have hq : Measurable fun p : FieldSample × C(Icc (0 : ℝ) s, ℝ) =>
      (revPath s hs p.2, p.1) :=
    ((measurable_revPath s hs).comp measurable_snd).prodMk measurable_fst
  have hmain : Measurable ((fun q : C(Icc (0 : ℝ) s, ℝ) × FieldSample =>
      coordChange (ofFun (h0rev κ) + q.2) (revMap (Wof κ s hs q.1) s) (Qc (Real.sqrt κ))
        (foldedCircle (fullIndex i).1 (fullIndex i).2)) ∘
      fun p : FieldSample × C(Icc (0 : ℝ) s, ℝ) => (revPath s hs p.2, p.1)) :=
    (B1Full.measurable_unzip_apply κ s hs
      (foldedCircle (fullIndex i).1 (fullIndex i).2) hμ).comp hq
  have hgoal : (fun p : FieldSample × C(Icc (0 : ℝ) s, ℝ) =>
      unzipFieldPath κ s hs p (foldedCircle (fullIndex i).1 (fullIndex i).2)) =
      ((fun q : C(Icc (0 : ℝ) s, ℝ) × FieldSample =>
      coordChange (ofFun (h0rev κ) + q.2) (revMap (Wof κ s hs q.1) s) (Qc (Real.sqrt κ))
        (foldedCircle (fullIndex i).1 (fullIndex i).2)) ∘
      fun p : FieldSample × C(Icc (0 : ℝ) s, ℝ) => (revPath s hs p.2, p.1)) := by
    funext p
    rfl
  rw [hgoal]
  exact hmain

/-- The circle coordinates `coordsFull` of the path–surrogate field are measurable. -/
theorem measurable_coordsFull_unzipFieldPath (κ s : ℝ) (hs : 0 ≤ s) :
    Measurable fun p : FieldSample × C(Icc (0 : ℝ) s, ℝ) => coordsFull (unzipFieldPath κ s hs p) := by
  refine measurable_pi_iff.mpr fun i => ?_
  have hgoal : (fun p : FieldSample × C(Icc (0 : ℝ) s, ℝ) =>
      coordsFull (unzipFieldPath κ s hs p) i) =
      fun p => unzipFieldPath κ s hs p (foldedCircle (fullIndex i).1 (fullIndex i).2) := by
    funext p
    rfl
  rw [hgoal]
  exact measurable_unzipFieldPath_apply κ s hs i

/-- The coordinate reconstruction `fromCoords` is measurable: for fixed `μ`, either `μ` is one
of the enumerated folded circles and `fromCoords c μ = c (Nat.find h)` is a coordinate, or
`fromCoords c μ = 0`. -/
theorem measurable_fromCoords {α : Type*} [MeasurableSpace α] {c : α → (ℕ → ℝ)}
    (hc : Measurable c) : Measurable fun p : α => fromCoords (c p) := by
  classical
  refine measurable_pi_iff.mpr fun μ => ?_
  by_cases h : ∃ i, foldedCircle (fullIndex i).1 (fullIndex i).2 = μ
  · simp only [fromCoords, dite_eq_left h]
    exact (measurable_pi_apply (Nat.find h)).comp hc
  · simp only [fromCoords, dite_eq_right h]
    exact measurable_const

/-- **Step ia**: the coordinate reconstruction of the path–surrogate of the unzipped field is
a measurable `FieldSample`-valued function of `(x, f)`. -/
theorem measurable_unzipFieldCoord (κ s : ℝ) (hs : 0 ≤ s) :
    Measurable fun p : FieldSample × C(Icc (0 : ℝ) s, ℝ) => unzipFieldCoord κ s hs p := by
  have hgoal : (fun p : FieldSample × C(Icc (0 : ℝ) s, ℝ) => unzipFieldCoord κ s hs p) =
      fun p => fromCoords (coordsFull (unzipFieldPath κ s hs p)) := by
    funext p
    rfl
  rw [hgoal]
  exact measurable_fromCoords (measurable_coordsFull_unzipFieldPath κ s hs)

/-! ## 3. Measurability of the gated boundary measure -/

/-- The `BCert`-gated boundary measure of the surrogate field is Giry measurable, by
composition of `measurable_unzipFieldCoord` with
`E1.M4.measurable_qBoundaryMeasure_bCert`. -/
theorem measurable_nuSur (κ s : ℝ) (hs : 0 ≤ s) (γ : ℝ) :
    Measurable fun p : FieldSample × C(Icc (0 : ℝ) s, ℝ) => nuSur κ s hs γ p := by
  classical
  have h : Measurable fun x : FieldSample =>
      if E1.M4.BCert γ x then qBoundaryMeasure γ x else 0 :=
    E1.M4.measurable_qBoundaryMeasure_bCert γ
  have hgoal : (fun p : FieldSample × C(Icc (0 : ℝ) s, ℝ) => nuSur κ s hs γ p) =
      (fun x : FieldSample => if E1.M4.BCert γ x then qBoundaryMeasure γ x else 0) ∘
        unzipFieldCoord κ s hs := by
    funext p
    rfl
  rw [hgoal]
  exact h.comp (measurable_unzipFieldCoord κ s hs)

/-! ## 4. Measurability of `p ↦ ν p (Icc (b p) 0)` (step ic) -/

/-- **Step ic**. For a Giry measurable family of measures `ν` on `ℝ`, a measurable left
endpoint `b` and finite mass on the windows `Icc (-N) N`, the map `p ↦ ν p (Icc (b p) 0)` is
measurable. Pattern of `B5.measurable_RP`: exhaust the window by the increasing sets
`Icc (b p) 0 ∩ Icc (-N) N`, and integrate the indicator of the measurable set
`S = {(p, y) | b p ≤ y ≤ 0}` (`Measurable.iSup` +
`E1.M4.measurable_setLIntegral_of_measurable_measure`).

The finiteness hypothesis is needed: without it the statement is false (take a measurable
constant family of measures that is infinite on intervals, e.g. counting measure on `ℚ`). -/
theorem measurable_measure_Icc_zero_of_finite {δ : Type*} [MeasurableSpace δ] {ν : δ → Measure ℝ}
    (hν : Measurable ν) {b : δ → ℝ} (hb : Measurable b)
    (hfin : ∀ (p : δ) (N : ℕ), ν p (Set.Icc (-(N : ℝ)) N) < ⊤) :
    Measurable fun p => ν p (Set.Icc (b p) 0) := by
  set S : Set (δ × ℝ) := {q | b q.1 ≤ q.2 ∧ q.2 ≤ 0} with hS
  have hSm : MeasurableSet S :=
    (measurableSet_le (hb.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  have hsec : ∀ (p : δ) (y : ℝ), S.indicator (1 : δ × ℝ → ℝ≥0∞) (p, y) =
      (Icc (b p) 0).indicator (1 : ℝ → ℝ≥0∞) y := by
    intro p y
    by_cases hy : y ∈ Icc (b p) 0
    · rw [indicator_of_mem hy, indicator_of_mem (show (p, y) ∈ S from hy)]; rfl
    · rw [indicator_of_notMem hy, indicator_of_notMem (show (p, y) ∉ S from hy)]
  have hstep : ∀ (p : δ) (N : ℕ),
      ∫⁻ y in Icc (-(N : ℝ)) N, S.indicator 1 (p, y) ∂ν p =
        ν p (Icc (b p) 0 ∩ Icc (-(N : ℝ)) N) := by
    intro p N
    rw [show (∫⁻ y in Icc (-(N : ℝ)) N, S.indicator (1 : δ × ℝ → ℝ≥0∞) (p, y) ∂ν p) =
        ∫⁻ y in Icc (-(N : ℝ)) N, (Icc (b p) 0).indicator (1 : ℝ → ℝ≥0∞) y ∂ν p from
      lintegral_congr fun y => hsec p y]
    rw [setLIntegral_indicator measurableSet_Icc (1 : ℝ → ℝ≥0∞)]
    exact setLIntegral_one _
  have e : ∀ p : δ, ν p (Icc (b p) 0) = ⨆ N : ℕ,
      ∫⁻ y in Icc (-(N : ℝ)) N, S.indicator 1 (p, y) ∂ν p := by
    intro p
    rw [show (⨆ N : ℕ, ∫⁻ y in Icc (-(N : ℝ)) N, S.indicator 1 (p, y) ∂ν p) =
        ⨆ N : ℕ, ν p (Icc (b p) 0 ∩ Icc (-(N : ℝ)) N) from
      iSup_congr fun N => hstep p N]
    have hU : Icc (b p) 0 = ⋃ N : ℕ, Icc (b p) 0 ∩ Icc (-(N : ℝ)) N := by
      ext y
      simp only [mem_iUnion, mem_inter_iff, mem_Icc]
      constructor
      · intro hy
        obtain ⟨N, hN⟩ := exists_nat_ge |y|
        exact ⟨N, hy, neg_le_of_abs_le hN, le_of_abs_le hN⟩
      · rintro ⟨N, hy, -⟩
        exact hy
    rw [← Monotone.measure_iUnion, ← hU]
    intro N N' h
    exact inter_subset_inter_right _
      (Icc_subset_Icc (neg_le_neg (by exact_mod_cast h)) (by exact_mod_cast h))
  rw [show (fun p => ν p (Icc (b p) 0)) = _ from funext e]
  exact Measurable.iSup fun N => E1.M4.measurable_setLIntegral_of_measurable_measure hν
    measurableSet_Icc (fun p => hfin p N) (measurable_one.indicator hSm)

/-! ## 5. The concrete endpoint maps and `lenMinusSur` -/

/-- `nuSur κ s hs γ p` is finite on every interval: off the certificate it is `0`, and on it
the boundary measure is finite on compacts (`E1.M4.exists_isVagueLimitR_of_bCert` gives a vague
limit, which is a finite measure on compacts). Same argument as `B5.gM_Icc_lt_top`. -/
theorem nuSur_Icc_lt_top (κ s : ℝ) (hs : 0 ≤ s) (γ : ℝ)
    (p : FieldSample × C(Icc (0 : ℝ) s, ℝ)) (a b : ℝ) :
    nuSur κ s hs γ p (Set.Icc a b) < ⊤ := by
  unfold nuSur
  split_ifs with h
  · have := (E1.M4.isVagueLimitR_qBoundaryMeasure (E1.M4.exists_isVagueLimitR_of_bCert h)).1
    exact measure_Icc_lt_top
  · simp [Measure.coe_zero]

/-- The endpoint map of the `BCert`-gated boundary measure of the surrogate field is
measurable: `measurable_measure_Icc_zero_of_finite` with the finiteness `nuSur_Icc_lt_top`. -/
theorem measurable_nuSur_Icc_zero (κ s : ℝ) (hs : 0 ≤ s) (γ : ℝ)
    {b : FieldSample × C(Icc (0 : ℝ) s, ℝ) → ℝ} (hb : Measurable b) :
    Measurable fun p => nuSur κ s hs γ p (Set.Icc (b p) 0) :=
  measurable_measure_Icc_zero_of_finite (measurable_nuSur κ s hs γ) hb
    fun p _ => nuSur_Icc_lt_top κ s hs γ p _ _

/-- **Measurability of the deterministic path functional `lenMinusSur`**: the endpoint is
`(a p.2).1`, and `lenMinusSur κ s hs γ a p = nuSur κ s hs γ p (Icc ((a p.2).1) 0)`. Together
with `ae_lenMinus_eq_surrogate` and `measurable_lenMinus_of_surrogate` this gives the
adaptedness of `L⁻_s`. -/
theorem measurable_lenMinusSur (κ s : ℝ) (hs : 0 ≤ s) (γ : ℝ)
    {a : C(Icc (0 : ℝ) s, ℝ) → ℝ × ℝ} (ha : Measurable a) :
    Measurable (lenMinusSur κ s hs γ a) := by
  have hb : Measurable fun p : FieldSample × C(Icc (0 : ℝ) s, ℝ) => (a p.2).1 :=
    (ha.comp measurable_snd).fst
  have hgoal : lenMinusSur κ s hs γ a =
      fun p => nuSur κ s hs γ p (Set.Icc ((a p.2).1) 0) := by
    funext p
    rfl
  rw [hgoal]
  exact measurable_nuSur_Icc_zero κ s hs γ hb

/-! ## The adaptedness obligation `hLad` of `ESM.lintegral_levelTime_strongMarkov_lenA_compl`

`hLad : ∀ s, Measurable[complFiltration hB hX s] (lenMinus κ B X s ∘ ofCompl P)`, proved from
the measurable reader `ESM.sideReader` (input 1, `ae_sideImages_eq_sideReader`), the boundary
certificate of the surrogate field (input 2, `ae_bCert_unzipFieldCoord`) and the measurability of
the deterministic functional (input 3, `measurable_lenMinusSur`), on the completed space
`(NullMeasurableSpace Ω P, P.completion)`, where `complFiltration` lives. -/

set_option maxHeartbeats 1000000 in
/-- **`hLad` from the two a.e. inputs.** Given the side-image identity (`hside` of
`ESM.ae_lenMinus_eq_surrogate`) and the boundary certificate of the surrogate field (`hgood` of
the same lemma) at time `s`, the intrinsic left length is `complFiltration`-adapted. The third
input `hcoord` is `ae_coordsFull_unzipFieldPath`, which needs no extra hypothesis. -/
theorem hLad_lenMinus_of_aes {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hBc : ∀ ω : Ω, Continuous fun u : ℝ≥0 => B u ω) {κ : ℝ} (s : ℝ≥0)
    (hside : ∀ᵐ ω ∂P, sideImages (drive κ (clampB s B) ω) (s : ℝ) =
      sideReader κ (s : ℝ) s.2 (pathC (s : ℝ) B hBc ω))
    (hgood : ∀ᵐ ω ∂P, E1.M4.BCert (Real.sqrt κ)
      (unzipFieldCoord κ (s : ℝ) s.2 (X ω, pathC (s : ℝ) B hBc ω))) :
    Measurable[complFiltration hB hX s] (lenMinus κ B X s ∘ ofCompl P) := by
  set B' : ℝ≥0 → NullMeasurableSpace Ω P → ℝ := fun t ω' => B t (ofCompl P ω') with hB'
  set X' : NullMeasurableSpace Ω P → FieldSample := fun ω' => X (ofCompl P ω') with hX'
  have hBc' : ∀ ω' : NullMeasurableSpace Ω P, Continuous fun u : ℝ≥0 => B' u ω' :=
    fun ω' => hBc _
  have hBcplt : IsBrownianReal B' P.completion := isBrownianReal_completion hB
  have hXcplt : IsFreeGFFModConstH X' P.completion := isFreeGFFModConstH_completion hX
  have hindcplt : IndepFun (pathOf B') X' P.completion := indepFun_completion hind
  have hsur : Measurable (lenMinusSur κ (s : ℝ) s.2 (Real.sqrt κ)
      (sideReader κ (s : ℝ) s.2)) :=
    measurable_lenMinusSur κ (s : ℝ) s.2 (Real.sqrt κ) (measurable_sideReader κ (s : ℝ) s.2)
  have hside' : ∀ᵐ ω' ∂P.completion, sideImages (drive κ (clampB s B') ω') (s : ℝ) =
      sideReader κ (s : ℝ) s.2 (pathC (s : ℝ) B' hBc' ω') :=
    ae_completion_iff.2 (hside.mono fun ω hω => by simpa only [hB', hX'] using hω)
  have hgood' : ∀ᵐ ω' ∂P.completion, E1.M4.BCert (Real.sqrt κ)
      (unzipFieldCoord κ (s : ℝ) s.2 (X' ω', pathC (s : ℝ) B' hBc' ω')) :=
    ae_completion_iff.2 (hgood.mono fun ω hω => by simpa only [hB', hX'] using hω)
  have hcoord : ∀ᵐ ω' ∂P.completion, coordsFull (coordChange (ofFun (h0rev κ) + X' ω')
      (fwdMapInv (drive κ (clampB s B') ω') (s : ℝ)) (Qc (Real.sqrt κ))) =
      coordsFull (unzipFieldPath κ (s : ℝ) s.2 (X' ω', pathC (s : ℝ) B' hBc' ω')) := by
    have hsN : ((s : ℝ).toNNReal) = s := Subtype.coe_injective (Real.coe_toNNReal _ s.2)
    simpa only [hsN] using
      ae_coordsFull_unzipFieldPath (κ := κ) (s := (s : ℝ)) hBcplt hBc' s.2
  have hae : lenMinus κ B' X' s =ᵐ[P.completion]
      fun ω' => lenMinusSur κ (s : ℝ) s.2 (Real.sqrt κ) (sideReader κ (s : ℝ) s.2)
        (X' ω', pathC (s : ℝ) B' hBc' ω') :=
    ae_lenMinus_eq_surrogate (κ := κ) hBcplt hBc' s hside' hgood' hcoord
  have hXx : Measurable[xSigma X'] X' :=
    measurable_iff_comap_le.mpr le_rfl
  have hXm : Measurable[complFiltration hB hX s] X' :=
    Measurable.mono hXx
      (le_trans le_sup_left (le_augSigma P.completion (rawSigma B' X' s))) le_rfl
  -- the stopped path is measurable for the past σ-algebra `σ(B u, u ≤ s)`
  -- the driver clamped at `s` is `m`-adapted and has continuous paths
  set B'' : ℝ≥0 → NullMeasurableSpace Ω P → ℝ := fun t ω' => B' (min t s) ω' with hB''
  have hB''m : ∀ t : ℝ≥0, Measurable[complFiltration hB hX s] (B'' t) := by
    intro t
    have := ((complFiltration_spec hB hX hind).1 (min t s)).mono
      ((complFiltration hB hX).mono' (min_le_right t s)) le_rfl
    simpa only [hB'', hB', Function.comp_def] using this
  have hB''c : ∀ ω' : NullMeasurableSpace Ω P, Continuous fun t : ℝ≥0 => B'' t ω' := by
    intro ω'
    simpa only [hB'', clampB_apply] using continuous_clampB hBc' s ω'
  -- the stopped path is measurable for the filtration
  have hpath : Measurable[complFiltration hB hX s] (pathC (s : ℝ) B'' hB''c) := by
    refine measurable_iff_comap_le.mpr ?_
    rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval]
    simp only [MeasurableSpace.comap_iSup]
    refine iSup_le fun u => ?_
    rw [MeasurableSpace.comap_comp]
    exact measurable_iff_comap_le.mp (hB''m u.1.toNNReal)
  have hpathEq : pathC (s : ℝ) B'' hB''c = pathC (s : ℝ) B' hBc' := by
    funext ω'
    refine ContinuousMap.ext fun x => ?_
    show B'' x.1.toNNReal ω' = B' x.1.toNNReal ω'
    rw [hB'']
    show B' (min x.1.toNNReal s) ω' = B' x.1.toNNReal ω'
    have hle : x.1.toNNReal ≤ s := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ x.2.1]
      exact x.2.2
    rw [min_eq_left hle]
  have hpath' : Measurable[complFiltration hB hX s] (pathC (s : ℝ) B' hBc') :=
    hpathEq ▸ hpath

  have hmain : Measurable[complFiltration hB hX s] (lenMinus κ B' X' s) :=
    measurable_lenMinus_of_surrogate (κ := κ) hBc' s hXm hpath'
      (fun N hN => null_measurableSet_augSigma P.completion _ hN) hsur hae
  show Measurable[complFiltration hB hX s] (fun ω' => lenMinus κ B X s (ofCompl P ω'))
  exact hmain

/-- **`hLad` for `s > 0`**, from `E1.ae_bCert_h0f` (which requires `0 < s`) for the certificate
and `RS.ae_real_alive` for the side images. -/
theorem hLad_lenMinus_pos {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hReg : Blueprint.RevCouplingBoundaryMeasureRegular) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hBc : ∀ ω : Ω, Continuous fun u : ℝ≥0 => B u ω) :
    ∀ s : ℝ≥0, 0 < (s : ℝ) →
      Measurable[complFiltration hB hX s] (lenMinus κ B X s ∘ ofCompl P) :=
  fun s hs => hLad_lenMinus_of_aes hB hX hind hBc s
    (ae_sideImages_eq_sideReader (κ := κ) hB hBc hκ hκ4.le s)
    (ae_bCert_unzipFieldCoord (κ := κ) hReg hκ hκ4 hB hX hind hBc hs)

/-- **`hLad` at `s = 0`, given the boundary certificate of the time-`0` field.** The side-image
input at `s = 0` is unconditional (`ESM.ae_sideImages_eq_sideReader` with `κ ≤ 4`); the only
remaining input is `E1.M4.BCert` of the *unzipped-at-time-`0`* field
(`coordChange (𝔥₀ + X) id (Qc √κ)`, i.e. `evalReg (𝔥₀ + X)`), for which no certificate is available
in the repository: `E1.ae_bCert_h0f` requires `0 < T`. -/
theorem hLad_lenMinus_zero_of_bCert {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hBc : ∀ ω : Ω, Continuous fun u : ℝ≥0 => B u ω)
    (h0bCert : ∀ᵐ ω ∂P, E1.M4.BCert (Real.sqrt κ)
      (unzipFieldCoord κ 0 le_rfl (X ω, pathC 0 B hBc ω))) :
    Measurable[complFiltration hB hX 0] (lenMinus κ B X 0 ∘ ofCompl P) :=
  hLad_lenMinus_of_aes hB hX hind hBc 0
    (ae_sideImages_eq_sideReader (κ := κ) hB hBc hκ hκ4 0) h0bCert

end ESM
end QuantumZipper
