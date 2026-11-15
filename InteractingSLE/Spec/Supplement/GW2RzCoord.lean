/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RzChain
import InteractingSLE.Spec.Dimension.TraceBridge

/-!
# GW2 at a root `x`: measurable relative driver coordinates (decision D8, layer 2)

Packet PROVE-GW2-ROOTX, round 3. J31's capacity reader at a good horizon `v` (a protected root arc, the counterflow
and the explored curve regular, `0 < v` before the root-`x` first contact) is the re-centred chain driver below the
horizon's capacity (`reader_eq_chain`, from `GW2RzChain.exists_recentred_chain` and BUF's
`GW2Bf.capacityDriverRead_eq_of_hull`). Two good horizons' readers agree on their overlap (`reader_compat`; the
record readers do not see later live data, `forwardHull_prefix_eq`, `forwardCapacity_prefix_eq'`). So the readers on
the good separated horizon events form a CoordB driver atlas (`driverAtlas_readers`), and CoordB's gluing gives:

* `recPair`, `contactX` (the first contact of `x + γ` with the retained prefix), `clockX` (ROOT2's capacity reader at
  the time), `hullX` (the forward hull re-centred at `relBase`), `measurable_recPair`;
* `atlasDrv`, `atlasLif`, **`driverAtlas_readers`**;
* **`exists_coordX`**: a measurable driver `D` from `0`, continuous before a measurable life `L`, adapted, such that
  almost surely on the arc event (`x‖α‖ < 1` on `[0, s]`) every relative time before `L` is the clock of a time
  before contact, and before contact the clock is below `L` and `D`'s hull at the clock is the re-centred relative
  hull. This is GB6's `SourceC.RelativeDriverCoordinates` at a root `x`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.GW2Rz

open Exist Staged StagedLaw Restart Supp8.GB6 Supp8.GB6.CoordB GW2TipSystem

section Prefix

variable {x : ℝ} {s : ℝ≥0} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e)
include he

/-- The forward hull of an earlier time does not see a later live record. -/
theorem forwardHull_prefix_eq (r : RecData) {v v' t : ℝ≥0} (hv' : (v' : ℝ≥0∞) < e.2) (hvv : v ≤ v')
    (htv : t ≤ v) :
    RootH29.forwardHull x s t (r, recOf (v : ℝ≥0∞) e) = RootH29.forwardHull x s t (r, recOf (v' : ℝ≥0∞) e) := by
  have hv : (v : ℝ≥0∞) < e.2 := (ENNReal.coe_le_coe.2 hvv).trans_lt hv'
  unfold RootH29.forwardHull RootH29.translatedHull
  rw [RootZ21.fwdHull_record_of_le_of_live he hv htv, RootZ21.fwdHull_record_of_le_of_live he hv' (htv.trans hvv)]

theorem forwardCapacity_prefix_eq' (r : RecData) {v v' t : ℝ≥0} (hv' : (v' : ℝ≥0∞) < e.2) (hvv : v ≤ v')
    (htv : t ≤ v) :
    RootH29.forwardCapacity x s t (r, recOf (v : ℝ≥0∞) e) =
      RootH29.forwardCapacity x s t (r, recOf (v' : ℝ≥0∞) e) := by
  unfold RootH29.forwardCapacity
  rw [forwardHull_prefix_eq he r hv' hvv htv]

end Prefix

section Reader

variable {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
  {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) ⊤ α)
  (hW : Continuous (W · ω)) (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤)
  {s : ℝ≥0} (hs : 0 < s) {x : ℝ} (hx : 0 ≤ x) (harc : ∀ u ∈ Icc 0 s, x * ‖α u‖ < 1)
  {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) {γ : ℝ≥0 → ℂ}
  (hγ : IsGeneratingTrace e.1 e.2 γ)

include hα hW hW0 hζ hs hx harc he hγ

/-- **J31's capacity reader at a good horizon is the re-centred chain driver** below the horizon's capacity, and the
capacity reader is a strictly increasing continuous clock from `0` on the horizon. -/
theorem reader_eq_chain {v : ℝ≥0}
    (hv : (v : ℝ≥0∞) < min
      (firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
        ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)) e.2) (hv0 : 0 < v) :
    ∃ R : ℝ≥0 → ℝ, Continuous R ∧ R 0 = 0 ∧
      RootH29.forwardCapacity x s 0 (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) = 0 ∧
      StrictMonoOn (fun t => RootH29.forwardCapacity x s t (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)) (Icc 0 v) ∧
      ContinuousOn (fun t => RootH29.forwardCapacity x s t (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)) (Icc 0 v) ∧
      (∀ t ∈ Icc 0 v, fwdHull (fun r : ℝ => R r.toNNReal)
          (RootH29.forwardCapacity x s t (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)) =
        (fun z : ℂ => z + ((-GW2Bf.relBase x s (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) : ℝ) : ℂ)) ''
          RootH29.forwardHull x s t (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)) ∧
      ∀ u : ℝ≥0, (u : ℝ) < RootH29.forwardCapacity x s v (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) →
        RootJ31.capacityDriverRead x s v u (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) = R u := by
  obtain ⟨R, hRc, hR0, hR⟩ := exists_recentred_chain W ζ ω hα hW hW0 hζ hs hx harc he hγ hv hv0
  obtain ⟨-, -, h0, hm, hc, -⟩ := RootI30.exists_reader_chain W ζ ω hα hW hW0 hζ hs hx harc he hγ hv
  exact ⟨R, hRc, hR0, h0, hm, hc, hR, fun u hu =>
    GW2Bf.capacityDriverRead_eq_of_hull W ζ ω hα hW hW0 hζ hs hx harc he hγ hv hRc hR0 hR hu⟩

/-- **The readers of two good horizons agree below the earlier horizon's capacity.** -/
theorem reader_compat {v v' : ℝ≥0} (hvv : v ≤ v') (hv0 : 0 < v)
    (hv' : (v' : ℝ≥0∞) < min
      (firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
        ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)) e.2) {u : ℝ≥0}
    (hu : (u : ℝ) < RootH29.forwardCapacity x s v (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)) :
    RootJ31.capacityDriverRead x s v u (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) =
      RootJ31.capacityDriverRead x s v' u (cfRec s W ζ ω, recOf (v' : ℝ≥0∞) e) := by
  have hv : (v : ℝ≥0∞) < min
      (firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
        ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)) e.2 := (ENNReal.coe_le_coe.2 hvv).trans_lt hv'
  have he2 : (v' : ℝ≥0∞) < e.2 := hv'.trans_le (min_le_right _ _)
  obtain ⟨R', hR'c, hR'0, -, hm', -, hR'hull, hR'eq⟩ :=
    reader_eq_chain W ζ ω hα hW hW0 hζ hs hx harc he hγ hv' (hv0.trans_le hvv)
  have hhull : ∀ t ∈ Icc 0 v, fwdHull (fun r : ℝ => R' r.toNNReal)
      (RootH29.forwardCapacity x s t (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)) =
      (fun z : ℂ => z + ((-GW2Bf.relBase x s (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) : ℝ) : ℂ)) ''
        RootH29.forwardHull x s t (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) := by
    intro t ht
    rw [forwardCapacity_prefix_eq' he _ he2 hvv ht.2,
      forwardHull_prefix_eq he _ he2 hvv ht.2]
    exact hR'hull t ⟨ht.1, ht.2.trans hvv⟩
  rw [GW2Bf.capacityDriverRead_eq_of_hull W ζ ω hα hW hW0 hζ hs hx harc he hγ hv hR'c hR'0 hhull hu]
  refine (hR'eq u ?_).symm
  rw [forwardCapacity_prefix_eq' he _ he2 hvv le_rfl] at hu
  exact hu.trans_le (hm'.monotoneOn ⟨zero_le, hvv⟩ ⟨zero_le, le_rfl⟩ hvv)

end Reader

/-! ### The measurable atlas of readers -/

section Atlas

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **The record pair of an explored driver at a horizon**: the counterflow record and the explored record read up to
the horizon. -/
def recPair (s : ℝ≥0) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (w : ℝ≥0 → Ω → ℝ) (v : ℝ≥0) (ω : Ω) :
    RecData × RecData :=
  (cfRec s W' ζ' ω, recOf (v : ℝ≥0∞) (fun t => w t ω, ⊤))

/-- **The first contact at a root `x`** of the translated explored curve `x + γ` with the retained prefix. -/
def contactX (x : ℝ) (s : ℝ≥0) (γ α : Ω → ℝ≥0 → ℂ) (ω : Ω) : ℝ≥0∞ :=
  firstContactTime (fun t => sphereInv (((x : ℂ) + γ ω t : ℂ) : OnePoint ℂ))
    ((fun u => (α ω u : OnePoint ℂ)) '' Icc 0 s)

/-- **The relative clock at a root `x`**: ROOT2's capacity reader with the horizon at the time. -/
def clockX (x : ℝ) (s : ℝ≥0) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (w : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  RootH29.forwardCapacity x s t (recPair s W' ζ' w t ω)

/-- **The re-centred relative hull at a root `x`**: the forward hull, translated by minus the root's chart image. -/
def hullX (x : ℝ) (s : ℝ≥0) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (w : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : Set ℂ :=
  (fun z : ℂ => z + ((-GW2Bf.relBase x s (recPair s W' ζ' w t ω) : ℝ) : ℂ)) ''
    RootH29.forwardHull x s t (recPair s W' ζ' w t ω)

theorem measurable_recPair {s : ℝ≥0} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hrec : Measurable (cfRec s W' ζ'))
    {w : ℝ≥0 → Ω → ℝ} (hwm : ∀ t, Measurable (w t)) (hwc : ∀ ω, Continuous (w · ω)) (hw0 : ∀ ω, w 0 ω = 0)
    (v : ℝ≥0) : Measurable (recPair s W' ζ' w v) :=
  hrec.prodMk (measurable_recOf ((measurable_pi_iff.2 hwm).prodMk measurable_const)
    (fun ω => Gm.isRegularDriver_top (hwc ω) (hw0 ω)) _)

/-- **The local readers and their lives on the good separated horizon events** (the atlas data). -/
def atlasDrv (x : ℝ) (s : ℝ≥0) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (w : ℝ≥0 → Ω → ℝ) (E : ℕ → Set Ω)
    (T : ℕ → ℝ≥0) (n : ℕ) (u : ℝ≥0) : Ω → ℝ :=
  (E n).indicator fun ω => RootJ31.capacityDriverRead x s (T n) u (recPair s W' ζ' w (T n) ω)

/-- The life of a local reader. -/
def atlasLif (x : ℝ) (s : ℝ≥0) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (w : ℝ≥0 → Ω → ℝ) (E : ℕ → Set Ω)
    (T : ℕ → ℝ≥0) (n : ℕ) : Ω → ℝ≥0∞ :=
  (E n).indicator fun ω => ENNReal.ofReal (RootH29.forwardCapacity x s (T n) (recPair s W' ζ' w (T n) ω))

/-- **The atlas of readers is a driver atlas** (CoordB's `DriverAtlas`), on events where the per-sample hypotheses of
`reader_eq_chain` hold at each horizon. -/
theorem driverAtlas_readers {x : ℝ} {s : ℝ≥0} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {α : Ω → ℝ≥0 → ℂ}
    {w : ℝ≥0 → Ω → ℝ} {γ : Ω → ℝ≥0 → ℂ} (hrec : Measurable (cfRec s W' ζ')) (hwm : ∀ t, Measurable (w t))
    (hwc : ∀ ω, Continuous (w · ω)) (hw0 : ∀ ω, w 0 ω = 0) (hs : 0 < s) (hx : 0 ≤ x)
    {E : ℕ → Set Ω} (hE : ∀ n, MeasurableSet (E n)) {T : ℕ → ℝ≥0} (hT : ∀ n, 0 < T n)
    (hgood : ∀ n ω, ω ∈ E n → (IsGeneratingTrace (W' · ω) ⊤ (α ω) ∧ Continuous (W' · ω) ∧ W' 0 ω = 0 ∧
      ζ' ω = ⊤) ∧ IsGeneratingTrace (w · ω) ⊤ (γ ω) ∧ (∀ u ∈ Icc 0 s, x * ‖α ω u‖ < 1) ∧
      (T n : ℝ≥0∞) < contactX x s γ α ω) :
    CoordB.DriverAtlas (atlasDrv x s W' ζ' w E T) (atlasLif x s W' ζ' w E T) := by
  have hpm := fun v => measurable_recPair hrec hwm hwc hw0 v
  -- the per-sample facts at a horizon
  have hfacts : ∀ n ω, ω ∈ E n → ∃ R : ℝ≥0 → ℝ, Continuous R ∧ R 0 = 0 ∧
      0 < RootH29.forwardCapacity x s (T n) (recPair s W' ζ' w (T n) ω) ∧
      ∀ u : ℝ≥0, (u : ℝ) < RootH29.forwardCapacity x s (T n) (recPair s W' ζ' w (T n) ω) →
        RootJ31.capacityDriverRead x s (T n) u (recPair s W' ζ' w (T n) ω) = R u := by
    intro n ω hω
    obtain ⟨⟨hα, hW, hW0, hζ⟩, hγ, harc, hTc⟩ := hgood n ω hω
    have hv : (T n : ℝ≥0∞) < min (contactX x s γ α ω) (fun t => w t ω, (⊤ : ℝ≥0∞)).2 := by
      rw [min_top_right]; exact hTc
    obtain ⟨R, hRc, hR0, h0, hm, -, -, hReq⟩ := reader_eq_chain W' ζ' ω hα hW hW0 hζ hs hx harc
      (Gm.isRegularDriver_top (hwc ω) (hw0 ω)) hγ hv (hT n)
    refine ⟨R, hRc, hR0, ?_, hReq⟩
    have := hm ⟨le_rfl, zero_le⟩ ⟨zero_le, le_rfl⟩ (hT n)
    exact h0 ▸ this
  refine ⟨fun n u => ?_, fun n => ?_, fun n ω => ?_, fun n ω => ?_, fun n k ω u hn hk => ?_⟩
  · exact (RootJ31.measurable_capacityDriverRead_random (hpm (T n)) measurable_const x s (T n)).indicator (hE n)
  · exact (ENNReal.measurable_ofReal.comp
      (RootH29.measurable_forwardCapacity_random x s (hpm (T n)) measurable_const)).indicator (hE n)
  · by_cases hω : ω ∈ E n
    · obtain ⟨R, hRc, -, -, hReq⟩ := hfacts n ω hω
      refine (hRc.continuousOn (s := {u : ℝ≥0 | (u : ℝ≥0∞) < atlasLif x s W' ζ' w E T n ω})).congr ?_
      intro u hu
      simp only [atlasLif, indicator_of_mem hω, mem_ofPred_eq] at hu
      simp only [atlasDrv, indicator_of_mem hω]
      refine hReq u ?_
      exact ENNReal.coe_lt_ofReal.1 hu
    · have he : (fun u => atlasDrv x s W' ζ' w E T n u ω) = fun _ => 0 := by
        funext u; simp only [atlasDrv, indicator_of_notMem hω]
      rw [he]; exact continuousOn_const
  · by_cases hω : ω ∈ E n
    · obtain ⟨R, -, hR0, hpos, hReq⟩ := hfacts n ω hω
      simp only [atlasDrv, indicator_of_mem hω]
      rw [hReq 0 (by simpa using hpos), hR0]
    · simp only [atlasDrv, indicator_of_notMem hω]
  · -- compatibility
    have hωn : ω ∈ E n := by
      by_contra h
      simp only [atlasLif, indicator_of_notMem h] at hn
      exact not_lt_zero hn
    have hωk : ω ∈ E k := by
      by_contra h
      simp only [atlasLif, indicator_of_notMem h] at hk
      exact not_lt_zero hk
    simp only [atlasLif, indicator_of_mem hωn, indicator_of_mem hωk] at hn hk
    simp only [atlasDrv, indicator_of_mem hωn, indicator_of_mem hωk]
    have hn' : (u : ℝ) < RootH29.forwardCapacity x s (T n) (recPair s W' ζ' w (T n) ω) := by
      exact ENNReal.coe_lt_ofReal.1 hn
    have hk' : (u : ℝ) < RootH29.forwardCapacity x s (T k) (recPair s W' ζ' w (T k) ω) := by
      exact ENNReal.coe_lt_ofReal.1 hk
    rcases le_total (T n) (T k) with hnk | hkn
    · obtain ⟨⟨hα, hW, hW0, hζ⟩, hγ, harc, hTc⟩ := hgood k ω hωk
      have hv' : (T k : ℝ≥0∞) < min (contactX x s γ α ω) (fun t => w t ω, (⊤ : ℝ≥0∞)).2 := by
        rw [min_top_right]; exact hTc
      exact reader_compat W' ζ' ω hα hW hW0 hζ hs hx harc (Gm.isRegularDriver_top (hwc ω) (hw0 ω)) hγ hnk
        (hT n) hv' hn'
    · obtain ⟨⟨hα, hW, hW0, hζ⟩, hγ, harc, hTc⟩ := hgood n ω hωn
      have hv' : (T n : ℝ≥0∞) < min (contactX x s γ α ω) (fun t => w t ω, (⊤ : ℝ≥0∞)).2 := by
        rw [min_top_right]; exact hTc
      exact (reader_compat W' ζ' ω hα hW hW0 hζ hs hx harc (Gm.isRegularDriver_top (hwc ω) (hw0 ω)) hγ hkn
        (hT k) hv' hk').symm

/-- **Root-`x` relative driver coordinates**: a measurable driver `D` from `0`, continuous before a measurable
life `L`, such that almost surely on the arc event every relative time before `L` is the root-`x` clock of a time
before the root-`x` first contact, and at every such time the clock is below `L` and the hull of `D` at the clock is
the re-centred relative hull (CoordB's atlas of J31's readers on good separated horizons). -/
theorem exists_coordX {P : Measure Ω} {x : ℝ} {s : ℝ≥0} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {α : Ω → ℝ≥0 → ℂ} {w : ℝ≥0 → Ω → ℝ} {γ : Ω → ℝ≥0 → ℂ} (hrec : Measurable (cfRec s W' ζ'))
    (hwm : ∀ t, Measurable (w t)) (hwc : ∀ ω, Continuous (w · ω)) (hw0 : ∀ ω, w 0 ω = 0) (hs : 0 < s)
    (hx : 0 ≤ x) {Γ A : Ω → ℝ≥0 → ℂ} (hΓc : ∀ ω, Continuous (Γ ω)) (hΓm : ∀ t, Measurable fun ω => Γ ω t)
    (hAc : ∀ ω, Continuous (A ω)) (hAm : ∀ t, Measurable fun ω => A ω t) {Arc : Set Ω}
    (hArc : MeasurableSet Arc)
    (hgood : ∀ᵐ ω ∂P, (IsGeneratingTrace (W' · ω) ⊤ (α ω) ∧ Continuous (W' · ω) ∧ W' 0 ω = 0 ∧ ζ' ω = ⊤) ∧
      IsGeneratingTrace (w · ω) ⊤ (γ ω) ∧ (ω ∈ Arc → ∀ u ∈ Icc 0 s, x * ‖α ω u‖ < 1) ∧
      Γ ω = γ ω ∧ ∀ u ≤ s, A ω u = α ω u) :
    ∃ (D : ℝ≥0 → Ω → ℝ) (L : Ω → ℝ≥0∞), (∀ t, Measurable (D t)) ∧ Measurable L ∧
      (∀ ω, ContinuousOn (D · ω) {t | (t : ℝ≥0∞) < L ω}) ∧ (∀ ω, D 0 ω = 0) ∧
      AdaptedBefore (Filtration.const ℝ≥0 mΩ le_rfl) L D ∧
      ∀ᵐ ω ∂P, ω ∈ Arc →
        (∀ u : ℝ≥0, (u : ℝ≥0∞) < L ω → ∃ t : ℝ≥0, (t : ℝ≥0∞) < contactX x s γ α ω ∧
          (u : ℝ) < clockX x s W' ζ' w t ω) ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX x s γ α ω →
          0 ≤ clockX x s W' ζ' w t ω ∧ ENNReal.ofReal (clockX x s W' ζ' w t ω) < L ω ∧
          fwdHull (fun r : ℝ => D r.toNNReal ω) (clockX x s W' ζ' w t ω) = hullX x s W' ζ' w t ω ∧
          ∃ v : ℝ≥0, t < v ∧ (v : ℝ≥0∞) < contactX x s γ α ω ∧ ∃ R : ℝ≥0 → ℝ, Continuous R ∧ R 0 = 0 ∧
            (∀ t' ∈ Icc 0 v, fwdHull (fun r : ℝ => R r.toNNReal)
                (RootH29.forwardCapacity x s t' (recPair s W' ζ' w v ω)) =
              (fun z : ℂ => z + ((-GW2Bf.relBase x s (recPair s W' ζ' w v ω) : ℝ) : ℂ)) ''
                RootH29.forwardHull x s t' (recPair s W' ζ' w v ω)) ∧
            ∀ u : ℝ≥0, (u : ℝ) < RootH29.forwardCapacity x s v (recPair s W' ζ' w v ω) → D u ω = R u := by
  classical
  obtain ⟨G, hGm, hGae, hG⟩ := Supp8.GB6.SourceC.exists_measurable_good hgood
  obtain ⟨T, hT, hcover⟩ := Supp8.GB6.SourceC.exists_prefix_times
  -- the contact in the measurable versions
  have hxΓc : ∀ ω, Continuous fun t => (x : ℂ) + Γ ω t := fun ω => continuous_const.add (hΓc ω)
  have hxΓm : ∀ t, Measurable fun ω => (x : ℂ) + Γ ω t := fun t => measurable_const.add (hΓm t)
  have hcont : ∀ ω ∈ G, contactX x s γ α ω = firstContactTime (fun t => sphereInv (((x : ℂ) + Γ ω t : ℂ) :
      OnePoint ℂ)) ((fun u => (A ω u : OnePoint ℂ)) '' Icc 0 s) := by
    intro ω hω
    obtain ⟨-, -, -, hΓ, hA⟩ := hG ω hω
    unfold contactX
    rw [hΓ, Supp8.GB6.SourceC.firstContactTime_eq_of_prefix_eq hA]
  let E : ℕ → Set Ω := fun n => G ∩ Arc ∩ {ω | (T n : ℝ≥0∞) < firstContactTime
    (fun t => sphereInv (((x : ℂ) + Γ ω t : ℂ) : OnePoint ℂ)) ((fun u => (A ω u : OnePoint ℂ)) '' Icc 0 s)}
  have hEm : ∀ n, MeasurableSet (E n) := fun n => (hGm.inter hArc).inter
    (Supp8.GB6.SourceC.measurableSet_lt_firstContactTime hxΓc hAc hxΓm hAm (T n) s)
  have hgood' : ∀ n ω, ω ∈ E n → (IsGeneratingTrace (W' · ω) ⊤ (α ω) ∧ Continuous (W' · ω) ∧ W' 0 ω = 0 ∧
      ζ' ω = ⊤) ∧ IsGeneratingTrace (w · ω) ⊤ (γ ω) ∧ (∀ u ∈ Icc 0 s, x * ‖α ω u‖ < 1) ∧
      (T n : ℝ≥0∞) < contactX x s γ α ω := by
    intro n ω ⟨⟨hωG, hωA⟩, hωT⟩
    obtain ⟨h1, h2, h3, -, -⟩ := hG ω hωG
    exact ⟨h1, h2, h3 hωA, (hcont ω hωG) ▸ hωT⟩
  have hatlas := driverAtlas_readers (α := α) (γ := γ) hrec hwm hwc hw0 hs hx hEm hT hgood'
  obtain ⟨D, hDm, hDn, hDc, hD0, hLm, hDa⟩ := CoordB.exists_driver_of_atlas hatlas
  refine ⟨D, CoordB.atlasLife (atlasLif x s W' ζ' w E T), hDm, hLm, hDc, hD0, hDa, ?_⟩
  filter_upwards [hGae] with ω hωG hωA
  refine ⟨fun u hu => ?_, fun t ht => ?_⟩
  · obtain ⟨n, hn⟩ := (CoordB.lt_atlasLife_iff u ω).1 hu
    have hωn : ω ∈ E n := by
      by_contra h
      simp only [atlasLif, indicator_of_notMem h] at hn
      exact not_lt_zero hn
    simp only [atlasLif, indicator_of_mem hωn] at hn
    exact ⟨T n, (hgood' n ω hωn).2.2.2, ENNReal.coe_lt_ofReal.1 hn⟩
  · obtain ⟨n, htn, hnc⟩ := hcover (contactX x s γ α ω) t ht
    have hωn : ω ∈ E n := ⟨⟨hωG, hωA⟩, by
      show (T n : ℝ≥0∞) < _
      rw [← hcont ω hωG]; exact hnc⟩
    obtain ⟨⟨hα, hW, hW0, hζ⟩, hγ, harc, hTc⟩ := hgood' n ω hωn
    have he := Gm.isRegularDriver_top (hwc ω) (hw0 ω)
    have hv : (T n : ℝ≥0∞) < min (contactX x s γ α ω) (fun t => w t ω, (⊤ : ℝ≥0∞)).2 := by
      rw [min_top_right]; exact hTc
    obtain ⟨R, hRc, hR0, h0, hm, -, hRhull, hReq⟩ := reader_eq_chain W' ζ' ω hα hW hW0 hζ hs hx harc he hγ hv (hT n)
    have hclock : clockX x s W' ζ' w t ω =
        RootH29.forwardCapacity x s t (recPair s W' ζ' w (T n) ω) :=
      forwardCapacity_prefix_eq' he _ ENNReal.coe_lt_top htn.le le_rfl
    have hat : 0 ≤ RootH29.forwardCapacity x s t (recPair s W' ζ' w (T n) ω) := by
      rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h | h
      · rw [← h]; exact h0.ge
      · exact le_of_lt (lt_of_eq_of_lt h0.symm (hm ⟨le_rfl, zero_le⟩ ⟨zero_le, htn.le⟩ h))
    have hlt : RootH29.forwardCapacity x s t (recPair s W' ζ' w (T n) ω) <
        RootH29.forwardCapacity x s (T n) (recPair s W' ζ' w (T n) ω) :=
      hm ⟨zero_le, htn.le⟩ ⟨zero_le, le_rfl⟩ htn
    have hlif : atlasLif x s W' ζ' w E T n ω =
        ENNReal.ofReal (RootH29.forwardCapacity x s (T n) (recPair s W' ζ' w (T n) ω)) := by
      simp only [atlasLif, indicator_of_mem hωn]
    refine ⟨hclock ▸ hat, ?_, ?_, T n, htn, hTc, R, hRc, hR0, hRhull, fun u hu => ?_⟩
    rotate_left 2
    · have hul : (u : ℝ≥0∞) < atlasLif x s W' ζ' w E T n ω := by
        rw [hlif]; exact ENNReal.coe_lt_ofReal.2 hu
      rw [hDn n ω u hul]
      simp only [atlasDrv, indicator_of_mem hωn]
      exact hReq u hu
    · rw [hclock]
      refine lt_of_lt_of_le ?_ (le_iSup (fun k => atlasLif x s W' ζ' w E T k ω) n)
      rw [hlif]
      exact (ENNReal.ofReal_lt_ofReal_iff (hat.trans_lt hlt)).2 hlt
    · -- the hull: `D` is `R` below the horizon's capacity
      obtain ⟨b, hab, hbT⟩ := exists_between hlt
      have heq : ∀ r ∈ Icc (0 : ℝ) b, D r.toNNReal ω = R r.toNNReal := by
        intro r hr
        have hrT : ((r.toNNReal : ℝ≥0) : ℝ) < RootH29.forwardCapacity x s (T n) (recPair s W' ζ' w (T n) ω) := by
          rw [Real.coe_toNNReal _ hr.1]; exact hr.2.trans_lt hbT
        have hrl : (r.toNNReal : ℝ≥0∞) < atlasLif x s W' ζ' w E T n ω := by
          rw [hlif]; exact ENNReal.coe_lt_ofReal.2 hrT
        rw [hDn n ω _ hrl]
        simp only [atlasDrv, indicator_of_mem hωn]
        exact hReq _ hrT
      rw [hclock, fwdHull_eq_of_eqOn hat hab heq]
      refine (hRhull t ⟨zero_le, htn.le⟩).trans ?_
      unfold hullX recPair
      rw [forwardHull_prefix_eq he _ ENNReal.coe_lt_top htn.le le_rfl]
      rfl

end Atlas

end InteractingSLE.Theorem14.GW2Rz
