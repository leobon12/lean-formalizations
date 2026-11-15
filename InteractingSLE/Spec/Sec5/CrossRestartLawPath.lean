/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartLawTopo
import InteractingSLE.Spec.Restart.ClockMeasCap

/-!
# The chart capacity clock read on a countable grid

Packet PROVE-SEC5-H, layer (iv). SEC5-G's chart capacity clock `restartClock t = hcap(Φ(K′_t))/2` is defined through
the image of a hull. Before the exit it equals half the grid capacity `hcapHit` of the chart path on the countable
grid `ratGrid t` of times in `[0, t]` (`IsRestartData.restartClock_eq_hcapHit_ratGrid`), which is a measurable
function of countably many values of the chart path.

* `ratGrid t`: the countable set `{r⁺ ∧ t : r ∈ ℚ}`, dense in `[0, t]`;
* `hcapHit_closure`, `hcapHit_image_ratGrid`: `hcapHit` does not see closures, so it can be read on a dense set;
* `IsRestartData.restartClock_eq_hcapHit`: `restartClock t₀ = hcapHit(Φ γ′([0, t₀]))/2` for `t₀` before the exit;
* the restart objects in measurable form: the countable trace condition `IsTraceGoodQ` (it implies the trace condition
  `IsTraceGood` of `CrossRestartLawTopo.lean` for continuous traces), the exit `lawExit`, the clock `lawClock`, the
  lifetime `lawLife`, the inverse clock `lawInv` and the chart path `lawPath`; `isRestartData_lawExit`;
* **`lawPath_eq_restartChartPath`** and **`isCounterflowChartContinuation_lawPath`**: they are SEC5-G's canonical
  objects and give the pathwise continuation when the lifetime is infinite.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal ENNReal

open QuantumZipper (H)
open QuantumZipper.CA (realMobius)

namespace InteractingSLE

namespace Sec5

namespace CrossRestart

open ConformalImage ConformalImageFull

/-! ### A countable dense grid of times -/

/-- The countable grid `{r⁺ ∧ t : r ∈ ℚ}` of times in `[0, t]`. -/
def ratGrid (t : ℝ≥0) : Set ℝ≥0 := range fun r : ℚ => (r : ℝ).toNNReal ⊓ t

theorem countable_ratGrid (t : ℝ≥0) : (ratGrid t).Countable := countable_range _

theorem ratGrid_subset_Icc (t : ℝ≥0) : ratGrid t ⊆ Icc 0 t := by
  rintro _ ⟨r, rfl⟩
  exact ⟨zero_le, inf_le_right⟩

theorem mem_ratGrid_self (t : ℝ≥0) : t ∈ ratGrid t := by
  refine ⟨(⌈(t : ℝ)⌉₊ : ℚ), ?_⟩
  simp only [Rat.cast_natCast]
  refine inf_eq_right.2 ?_
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (Nat.cast_nonneg _)]
  exact Nat.le_ceil _

theorem closure_ratGrid (t : ℝ≥0) : closure (ratGrid t) = Icc 0 t := by
  refine le_antisymm (closure_minimal (ratGrid_subset_Icc t) isClosed_Icc) ?_
  set g : ℝ → ℝ≥0 := fun x => x.toNNReal ⊓ t with hg
  have hgc : Continuous g := continuous_real_toNNReal.inf continuous_const
  have hR : ratGrid t = g '' range ((↑) : ℚ → ℝ) := by
    rw [ratGrid, ← range_comp]
    rfl
  intro s hs
  have hs' : s = g s := by
    rw [hg]
    simp only [Real.toNNReal_coe]
    exact (inf_eq_left.2 hs.2).symm
  rw [hR, hs']
  refine image_closure_subset_closure_image hgc ⟨(s : ℝ), ?_, rfl⟩
  rw [Rat.denseRange_cast.closure_range]
  exact mem_univ _

/-! ### `hcapHit` does not see closures -/

theorem hcapHit_closure (K : Set ℂ) : WholeField.hcapHit (closure K) = WholeField.hcapHit K := by
  classical
  unfold WholeField.hcapHit
  refine iInf_congr fun n => iInf_congr fun s => ?_
  have hO : IsOpen (H \ WholeField.gridUnion n s) :=
    QuantumZipper.isOpen_H.sdiff (WholeField.isClosed_gridUnion n s)
  by_cases h : Disjoint K (H \ WholeField.gridUnion n s)
  · have h' : Disjoint (closure K) (H \ WholeField.gridUnion n s) := h.closure_left hO
    simp only [h, h', ↓reduceIte]
  · have h' : ¬ Disjoint (closure K) (H \ WholeField.gridUnion n s) := fun h' =>
      h (h'.mono_left subset_closure)
    simp only [h, h', ↓reduceIte]

/-- On a path continuous on `[0, t]`, the grid capacity of the values on the grid is that of the whole prefix. -/
theorem hcapHit_image_ratGrid {Γ : ℝ≥0 → ℂ} {t : ℝ≥0} (hc : ContinuousOn Γ (Icc 0 t)) :
    WholeField.hcapHit (Γ '' ratGrid t) = WholeField.hcapHit (Γ '' Icc 0 t) := by
  rw [← hcapHit_closure (Γ '' ratGrid t)]
  congr 1
  refine le_antisymm (closure_minimal (image_mono (ratGrid_subset_Icc t))
    (isCompact_Icc.image_of_continuousOn hc).isClosed) ?_
  rw [← closure_ratGrid t] at hc ⊢
  exact hc.image_closure

/-! ### The chart capacity clock is the grid capacity of the chart path -/

section Clock

variable {q : ℝ} {U : ℝ → ℝ} {σ x₁ : ℝ} {w' : ℝ≥0 → ℝ} {ζ' : ℝ≥0∞} {γ' : ℝ≥0 → ℂ} {T : ℝ≥0∞}

theorem restartPath_zero : restartPath q U σ x₁ γ' 0 = 0 := by simp [restartPath]

theorem restartPath_of_ne_zero {t : ℝ≥0} (ht : t ≠ 0) :
    restartPath q U σ x₁ γ' t = restartMap q U σ x₁ (γ' t) := by simp [restartPath, ht]

theorem restartPath_image_Icc (t₀ : ℝ≥0) :
    restartPath q U σ x₁ γ' '' Icc 0 t₀ = insert 0 (restartMap q U σ x₁ '' (γ' '' Ioc 0 t₀)) := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    by_cases h0 : t = 0
    · rw [h0, restartPath_zero]; exact mem_insert _ _
    · exact mem_insert_of_mem _ ⟨γ' t, ⟨t, ⟨pos_iff_ne_zero.2 h0, ht.2⟩, rfl⟩, (restartPath_of_ne_zero h0).symm⟩
  · rintro (rfl | ⟨_, ⟨t, ht, rfl⟩, rfl⟩)
    · exact ⟨0, ⟨le_rfl, zero_le⟩, restartPath_zero⟩
    · exact ⟨t, Ioc_subset_Icc_self ht, restartPath_of_ne_zero ht.1.ne'⟩

/-- **The image hull is the filling of the chart path** before the exit: `Φ(K′_{t₀}) = fill(Φ γ′([0, t₀]))`. -/
theorem IsRestartData.restartMap_image_cfHull (hd : IsRestartData q U σ x₁ w' ζ' γ' T) {t₀ : ℝ≥0}
    (ht₀ : (t₀ : ℝ≥0∞) < T) :
    restartMap q U σ x₁ '' cfHull w' t₀ = fillH (restartPath q U σ x₁ γ' '' Icc 0 t₀) := by
  have hpc : ContinuousOn (restartPath q U σ x₁ γ') (Icc 0 t₀) :=
    hd.continuousOn_restartPath.mono fun t ht => lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht.2) ht₀
  have hcomp : IsCompact (restartPath q U σ x₁ γ' '' Icc 0 t₀) := isCompact_Icc.image_of_continuousOn hpc
  have hal := hd.alive t₀ ht₀
  have hIocH : γ' '' Icc 0 t₀ ∩ H = γ' '' Ioc 0 t₀ := by
    ext z
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hzH⟩
      have h0 : t ≠ 0 := fun h => zero_notMem_H_restart (by rw [h, hd.trace.1] at hzH; exact hzH)
      exact ⟨t, ⟨pos_iff_ne_zero.2 h0, ht.2⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, Ioc_subset_Icc_self ht, rfl⟩, hal.mem t ht.1 ht.2⟩
  rcases eq_zero_or_pos t₀ with rfl | ht₀pos
  · -- at time `0` both sides are empty
    have hfill := hd.trace.2.2 0 (lt_of_lt_of_le ht₀ hd.exit_le)
    have hcf : cfHull w' ((0 : ℝ≥0) : ℝ) = ∅ := by
      have h1 := (isFilling_iff_inter_H_eq_fillH (isCompact_Icc.image_of_continuousOn
        (hd.trace.2.1.mono fun t ht => le_trans (ENNReal.coe_le_coe.2 ht.2)
          (lt_of_lt_of_le ht₀ hd.exit_le).le)).isBounded
        (isCompact_Icc.image_of_continuousOn (hd.trace.2.1.mono fun t ht => le_trans
          (ENNReal.coe_le_coe.2 ht.2) (lt_of_lt_of_le ht₀ hd.exit_le).le)).isClosed).1 hfill
      rw [inter_eq_left.2 ((QuantumZipper.fwdHull_mono (W := fun s : ℝ => w' s.toNNReal)).2 _)] at h1
      have h2 : fillH (γ' '' Icc 0 (0 : ℝ≥0)) = ∅ := by
        refine fillH_eq_empty_of_disjoint ?_
        rw [Icc_self, image_singleton, hd.trace.1, closure_singleton]
        exact Set.disjoint_singleton_left.2 zero_notMem_H_restart
      exact h1.trans h2
    have h3 : fillH (restartPath q U σ x₁ γ' '' Icc 0 (0 : ℝ≥0)) = ∅ := by
      refine fillH_eq_empty_of_disjoint ?_
      rw [Icc_self, image_singleton, restartPath_zero, closure_singleton]
      exact Set.disjoint_singleton_left.2 zero_notMem_H_restart
    rw [hcf, image_empty, h3]
  -- the restart on the horizon `t₀` (as in `IsRestartData.exists_on`), keeping the filling conjunct
  obtain ⟨t₂, ht₀t₂, ht₂T⟩ := exists_real_btwn_of_lt ht₀
  have ht₂ζ : ENNReal.ofReal t₂ < ζ' := lt_of_lt_of_le ht₂T hd.exit_le
  have ht₂ : 0 ≤ t₂ := (NNReal.coe_nonneg t₀).trans ht₀t₂.le
  set W : ℝ → ℝ := frozenDrive w' t₂ with hWdef
  have hW : Continuous W := continuous_frozenDrive_of_lt hd.drv_cont ht₂ζ
  have hW0 : W 0 = 0 := by rw [hWdef, frozenDrive_zero ht₂, hd.drv_zero]
  have hK : ∀ t : ℝ, 0 ≤ t → t ≤ t₀ → QuantumZipper.fwdHull W t = cfHull w' t := fun t ht htt₀ =>
    fwdHull_eq_of_eqOn ht (lt_of_le_of_lt htt₀ ht₀t₂) fun r hr => frozenDrive_eq hr
  obtain ⟨r, hr, hd1⟩ := hal.far₁
  obtain ⟨r₃, hr₃, hd3⟩ := hal.far₃
  rw [← hK t₀ t₀.2 le_rfl] at hd1 hd3
  have hd2 := hal.far₂
  rw [← hK t₀ t₀.2 le_rfl] at hd2
  have hγc : ContinuousOn (fun s : ℝ => γ' s.toNNReal) (Icc 0 (t₀ : ℝ)) := by
    refine hd.trace.2.1.comp continuous_real_toNNReal.continuousOn fun s hs => ?_
    show ((s.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ζ'
    refine le_trans (ENNReal.coe_le_coe.2 ?_) (ht₀.le.trans hd.exit_le)
    exact Real.toNNReal_le_iff_le_coe.2 hs.2
  have hγH : ∀ t ∈ Ioc (0 : ℝ) t₀, γ' t.toNNReal ∈ H := fun t ht =>
    hal.mem _ (Real.toNNReal_pos.2 ht.1) (Real.toNNReal_le_iff_le_coe.2 ht.2)
  have hγK : ∀ t ∈ Ioc (0 : ℝ) t₀, IsFilling (QuantumZipper.fwdHull W t)
      ((fun s : ℝ => γ' s.toNNReal) '' Icc 0 t) := by
    intro t ht
    have htT : ((t.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ' := by
      refine lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 ht.2))
        (lt_of_lt_of_le ht₀ hd.exit_le)
    have hfill := hd.trace.2.2 t.toNNReal htT
    rw [Real.coe_toNNReal _ ht.1.le] at hfill
    rw [hK t ht.1.le ht.2, image_toNNReal_Icc γ' ht.1.le]
    exact hfill
  have hγ0 : (fun s : ℝ => γ' s.toNNReal) 0 = 0 := by simpa using hd.trace.1
  obtain ⟨τ, W', -, -, -, -, -, hKτ, hfillτ, -, -⟩ :=
    exists_loewner_restartMap_trace hW hW0 t₀.2 hd.q_pos hr hd1 hd.U_cont hd.U_zero hd.σ_nonneg hd2
      hd.x₁_eq hr₃ hd3 hγ0 hγc hγH hγK
  have htI : (t₀ : ℝ) ∈ Ioc (0 : ℝ) t₀ := ⟨by exact_mod_cast ht₀pos, le_rfl⟩
  have hF := hfillτ t₀ htI
  rw [image_toNNReal_Icc γ' (NNReal.coe_nonneg t₀), Real.toNNReal_coe, hIocH] at hF
  have hKeq : QuantumZipper.fwdHull W' (τ t₀) = restartMap q U σ x₁ '' cfHull w' t₀ := by
    rw [hKτ t₀ (Ioc_subset_Icc_self htI), hK t₀ t₀.2 le_rfl]
  rw [hKeq] at hF
  -- the filling of `A` is the filling of `insert 0 A`
  have hF' : IsFilling (restartMap q U σ x₁ '' cfHull w' t₀) (restartPath q U σ x₁ γ' '' Icc 0 t₀) := by
    rw [restartPath_image_Icc]
    have hHA : ∀ A : Set ℂ, H \ insert 0 A = H \ A := fun A => by
      ext z
      simp only [Set.mem_sdiff, mem_insert_iff, not_or]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, fun h0 => zero_notMem_H_restart (h0 ▸ h.1), h.2⟩⟩
    unfold IsFilling at hF ⊢
    rwa [hHA]
  have h1 := (isFilling_iff_inter_H_eq_fillH hcomp.isBounded hcomp.isClosed).1 hF'
  rwa [inter_eq_left.2 (by rw [← hKeq]; exact (QuantumZipper.fwdHull_mono (W := W')).2 _)] at h1

/-- **The chart capacity clock is half the grid capacity of the chart path** before the exit. -/
theorem IsRestartData.restartClock_eq_hcapHit (hd : IsRestartData q U σ x₁ w' ζ' γ' T) {t₀ : ℝ≥0}
    (ht₀ : (t₀ : ℝ≥0∞) < T) :
    restartClock q U σ x₁ w' t₀ =
      (WholeField.hcapHit (restartPath q U σ x₁ γ' '' ratGrid t₀)).toReal / 2 := by
  have hpc : ContinuousOn (restartPath q U σ x₁ γ') (Icc 0 t₀) :=
    hd.continuousOn_restartPath.mono fun t ht => lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht.2) ht₀
  rw [hcapHit_image_ratGrid hpc, Restart.hcapHit_image_eq hpc (by rw [restartPath_zero]; simp)]
  obtain ⟨τ, hτ0, hτm, -, hτ, -⟩ := hd.exists_on ht₀
  have hnn : 0 ≤ restartClock q U σ x₁ w' t₀ := by
    rw [hτ t₀ le_rfl, ← hτ0]
    exact hτm.monotoneOn ⟨le_rfl, t₀.2⟩ ⟨t₀.2, le_rfl⟩ t₀.2
  rw [restartClock, hd.restartMap_image_cfHull ht₀] at hnn ⊢
  rw [ENNReal.toReal_ofReal (by linarith)]

end Clock

/-! ### The restart objects in measurable form, for one sample -/

section Law

/-- The nonnegative real of a rational. -/
abbrev qnn (r : ℚ) : ℝ≥0 := (r : ℝ).toNNReal

/-- **The trace condition at time `r`**: `r` is before the counterflow lifetime, the counterflow prefix `γ′([0, r])`
is attached to `ℝ` at `0`, and its `E`-image misses the flow-line segment `η([0, s])`. -/
def IsTraceGood (q : ℝ) (η : ℝ≥0 → ℂ) (s : ℝ≥0) (ζ' : ℝ≥0∞) (γ' : ℝ≥0 → ℂ) (r : ℝ≥0) : Prop :=
  (r : ℝ≥0∞) < ζ' ∧ IsAttachedPath γ' r ∧
    Disjoint (η '' Icc 0 s) (realMobius 0 (-(1 + q)) 1 1 '' (γ' '' Icc 0 r))

/-- **The trace condition in countable form** at time `r`: `r` is before the counterflow lifetime, the counterflow
starts at `0`, on every `[r/(k + 1), r]` its grid values have imaginary parts bounded below, and the grid values of
the flow-line segment and of the `E`-image of the counterflow prefix stay at a positive distance. For traces continuous
on the relevant intervals it implies `IsTraceGood` (`IsTraceGoodQ.isTraceGood`). -/
def IsTraceGoodQ (q : ℝ) (η : ℝ≥0 → ℂ) (s : ℝ≥0) (ζ' : ℝ≥0∞) (γ' : ℝ≥0 → ℂ) (r : ℝ≥0) : Prop :=
  (r : ℝ≥0∞) < ζ' ∧ γ' 0 = 0 ∧
    (∀ k : ℕ, ∃ m : ℕ, ∀ t ∈ ratGrid r, 0 < t → (r : ℝ) / ((k : ℝ) + 1) ≤ t →
      1 / ((m : ℝ) + 1) ≤ (γ' t).im) ∧
    ∃ m : ℕ, ∀ a ∈ ratGrid s, ∀ b ∈ ratGrid r,
      1 / ((m : ℝ) + 1) ≤ ‖η a - realMobius 0 (-(1 + q)) 1 1 (γ' b)‖

/-- **The exit time in measurable form**: the supremum of the rational times at which the countable trace condition
holds. -/
def lawExit (q : ℝ) (η : ℝ≥0 → ℂ) (s : ℝ≥0) (ζ' : ℝ≥0∞) (γ' : ℝ≥0 → ℂ) : ℝ≥0∞ :=
  ⨆ (r : ℚ) (_ : IsTraceGoodQ q η s ζ' γ' (qnn r)), (qnn r : ℝ≥0∞)

/-- **The chart capacity clock in measurable form**: half the grid capacity of the chart path on the rational grid. -/
def lawClock (q : ℝ) (U : ℝ → ℝ) (σ x₁ : ℝ) (γ' : ℝ≥0 → ℂ) (t : ℝ≥0) : ℝ :=
  (WholeField.hcapHit (restartPath q U σ x₁ γ' '' ratGrid t)).toReal / 2

/-- **The chart capacity lifetime in measurable form**. -/
def lawLife (q : ℝ) (U : ℝ → ℝ) (σ x₁ : ℝ) (η : ℝ≥0 → ℂ) (s : ℝ≥0) (ζ' : ℝ≥0∞) (γ' : ℝ≥0 → ℂ) : ℝ≥0∞ :=
  ⨆ (r : ℚ) (_ : (qnn r : ℝ≥0∞) < lawExit q η s ζ' γ'), ENNReal.ofReal (lawClock q U σ x₁ γ' (qnn r))

/-- **The inverse clock in measurable form**: the infimum of the rational times before the exit at which the clock
has reached `u`. -/
def lawInv (q : ℝ) (U : ℝ → ℝ) (σ x₁ : ℝ) (η : ℝ≥0 → ℂ) (s : ℝ≥0) (ζ' : ℝ≥0∞) (γ' : ℝ≥0 → ℂ)
    (u : ℝ≥0) : ℝ≥0∞ :=
  ⨅ (r : ℚ) (_ : (qnn r : ℝ≥0∞) < lawExit q η s ζ' γ' ∧ (u : ℝ) ≤ lawClock q U σ x₁ γ' (qnn r)),
    (qnn r : ℝ≥0∞)

/-- The dyadic time just above `t` at level `n`. -/
def dyadicUp (n : ℕ) (t : ℝ≥0) : ℝ≥0 := (⌈(t : ℝ) * 2 ^ n⌉₊ : ℝ≥0) / 2 ^ n

/-- The limit of a sequence when it converges, `0` otherwise. -/
def limOr0 (f : ℕ → ℂ) : ℂ :=
  open scoped Classical in if h : ∃ l, Tendsto f atTop (𝓝 l) then h.choose else 0

/-- **The chart path in chart capacity time, in measurable form**: the chart path at the inverse clock, read as a
limit from the dyadic times above it. -/
def lawPath (q : ℝ) (U : ℝ → ℝ) (σ x₁ : ℝ) (η : ℝ≥0 → ℂ) (s : ℝ≥0) (ζ' : ℝ≥0∞) (γ' : ℝ≥0 → ℂ)
    (u : ℝ≥0) : ℂ :=
  limOr0 fun n => restartPath q U σ x₁ γ' (dyadicUp n (lawInv q U σ x₁ η s ζ' γ' u).toNNReal)

variable {q : ℝ} {U : ℝ → ℝ} {σ x₁ : ℝ} {w' : ℝ≥0 → ℝ} {ζ' : ℝ≥0∞} {γ' : ℝ≥0 → ℂ}
  {η : ℝ≥0 → ℂ} {s : ℝ≥0}

theorem IsTraceGood.mono {r r' : ℝ≥0} (h : IsTraceGood q η s ζ' γ' r) (hr : r' ≤ r) :
    IsTraceGood q η s ζ' γ' r' :=
  ⟨lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) h.1,
    ⟨h.2.1.cont.mono (Icc_subset_Icc_right hr), h.2.1.zero, fun t ht htr => h.2.1.mem t ht (htr.trans hr)⟩,
    h.2.2.mono_right (image_mono (image_mono (Icc_subset_Icc_right hr)))⟩

/-- The countable lower bound on the imaginary parts makes a continuous path from `0` attached. -/
theorem isAttachedPath_of_grid {γ : ℝ≥0 → ℂ} {r : ℝ≥0} (hc : ContinuousOn γ (Icc 0 r)) (h0 : γ 0 = 0)
    (hQ : ∀ k : ℕ, ∃ m : ℕ, ∀ t ∈ ratGrid r, 0 < t → (r : ℝ) / ((k : ℝ) + 1) ≤ t →
      1 / ((m : ℝ) + 1) ≤ (γ t).im) : IsAttachedPath γ r := by
  refine ⟨hc, h0, fun t ht htr => ?_⟩
  have ht' : (0 : ℝ) < t := ht
  obtain ⟨k, hk⟩ := exists_nat_gt ((r : ℝ) / t)
  have hcl : (r : ℝ) / ((k : ℝ) + 1) < t := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ ht'] at hk
    nlinarith
  obtain ⟨m, hm⟩ := hQ k
  set c : ℝ≥0 := ((r : ℝ) / ((k : ℝ) + 1)).toNNReal with hcdef
  have hct : c < t := by
    rw [hcdef, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ (by positivity)]
    exact hcl
  -- the closed set where the bound holds contains the grid points beyond `c`
  have hclosed : IsClosed (Icc 0 r ∩ (fun s => (γ s).im) ⁻¹' Ici (1 / ((m : ℝ) + 1))) :=
    (continuous_im.comp_continuousOn hc).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hsub : ratGrid r ∩ Ioi c ⊆ Icc 0 r ∩ (fun s => (γ s).im) ⁻¹' Ici (1 / ((m : ℝ) + 1)) := by
    rintro x ⟨hxg, hxc⟩
    refine ⟨ratGrid_subset_Icc r hxg, ?_⟩
    have hx0 : 0 < x := lt_of_le_of_lt zero_le hxc
    have hxc' : (r : ℝ) / ((k : ℝ) + 1) ≤ x := by
      have : (c : ℝ) < x := hxc
      rw [hcdef, Real.coe_toNNReal _ (by positivity)] at this
      exact this.le
    exact hm x hxg hx0 hxc'
  have htcl : t ∈ closure (ratGrid r ∩ Ioi c) := by
    have h1 : t ∈ Ioi c ∩ closure (ratGrid r) := ⟨hct, by rw [closure_ratGrid]; exact ⟨zero_le, htr⟩⟩
    have h2 := (isOpen_Ioi (a := c)).inter_closure h1
    rwa [inter_comm] at h2
  have hmem := closure_minimal hsub hclosed htcl
  have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  exact lt_of_lt_of_le hpos hmem.2

/-- The countable positive distance makes the two images disjoint. -/
theorem disjoint_of_grid {η : ℝ≥0 → ℂ} {s : ℝ≥0} {f : ℝ≥0 → ℂ} {r : ℝ≥0} (hη : ContinuousOn η (Icc 0 s))
    (hf : ContinuousOn f (Icc 0 r))
    (hQ : ∃ m : ℕ, ∀ a ∈ ratGrid s, ∀ b ∈ ratGrid r, 1 / ((m : ℝ) + 1) ≤ ‖η a - f b‖) :
    Disjoint (η '' Icc 0 s) (f '' Icc 0 r) := by
  obtain ⟨m, hm⟩ := hQ
  set F : ℝ≥0 × ℝ≥0 → ℝ := fun p => ‖η p.1 - f p.2‖ with hF
  have hFc : ContinuousOn F (Icc 0 s ×ˢ Icc 0 r) :=
    ((hη.comp continuousOn_fst fun p hp => hp.1).sub (hf.comp continuousOn_snd fun p hp => hp.2)).norm
  have hclosed : IsClosed (Icc 0 s ×ˢ Icc 0 r ∩ F ⁻¹' Ici (1 / ((m : ℝ) + 1))) :=
    hFc.preimage_isClosed_of_isClosed (isClosed_Icc.prod isClosed_Icc) isClosed_Ici
  have hsub : ratGrid s ×ˢ ratGrid r ⊆ Icc 0 s ×ˢ Icc 0 r ∩ F ⁻¹' Ici (1 / ((m : ℝ) + 1)) :=
    fun p hp => ⟨⟨ratGrid_subset_Icc s hp.1, ratGrid_subset_Icc r hp.2⟩, hm p.1 hp.1 p.2 hp.2⟩
  have hcl : closure (ratGrid s ×ˢ ratGrid r) = Icc 0 s ×ˢ Icc 0 r := by
    rw [closure_prod_eq, closure_ratGrid, closure_ratGrid]
  rw [Set.disjoint_left]
  rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
  have hp : (a, b) ∈ closure (ratGrid s ×ˢ ratGrid r) := by rw [hcl]; exact ⟨ha, hb⟩
  have hmem := (closure_minimal hsub hclosed hp).2
  have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  have : F (a, b) = 0 := by simp [hF, hab]
  have h2 : (1 / ((m : ℝ) + 1)) ≤ F (a, b) := hmem
  linarith

/-- **The countable trace condition gives the trace condition** for traces continuous on the relevant intervals. -/
theorem IsTraceGoodQ.isTraceGood {q : ℝ} {η : ℝ≥0 → ℂ} {s : ℝ≥0} {ζ' : ℝ≥0∞} {γ' : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsTraceGoodQ q η s ζ' γ' r) (hγc : ContinuousOn γ' (Icc 0 r)) (hηc : ContinuousOn η (Icc 0 s)) :
    IsTraceGood q η s ζ' γ' r := by
  obtain ⟨hζ, h0, hH, hd⟩ := h
  have hA := isAttachedPath_of_grid hγc h0 hH
  have hmc : ContinuousOn (fun t => realMobius 0 (-(1 + q)) 1 1 (γ' t)) (Icc 0 r) := by
    intro t ht
    refine ContinuousAt.comp_continuousWithinAt (continuousAt_mob ?_) (hγc t ht)
    by_cases h0' : t = 0
    · rw [h0', hA.zero]; norm_num
    · exact ne_neg_one_of_mem_H (hA.mem t (pos_iff_ne_zero.2 h0') ht.2)
  refine ⟨hζ, hA, ?_⟩
  rw [image_image]
  exact disjoint_of_grid hηc hmc hd

theorem isTraceGood_of_lt_lawExit (hγc : ContinuousOn γ' {t | (t : ℝ≥0∞) ≤ ζ'}) (hηc : ContinuousOn η (Icc 0 s))
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < lawExit q η s ζ' γ') : IsTraceGood q η s ζ' γ' t := by
  rw [lawExit, lt_iSup_iff] at ht
  obtain ⟨r, hr⟩ := ht
  rw [lt_iSup_iff] at hr
  obtain ⟨hg, htr⟩ := hr
  refine (hg.isTraceGood (hγc.mono fun x hx => ?_) hηc).mono (ENNReal.coe_le_coe.1 htr.le)
  exact (ENNReal.coe_le_coe.2 hx.2).trans hg.1.le

theorem lawExit_le : lawExit q η s ζ' γ' ≤ ζ' := iSup₂_le fun _ hr => hr.1.le

theorem le_dyadicUp (n : ℕ) (t : ℝ≥0) : t ≤ dyadicUp n t := by
  rw [dyadicUp, ← NNReal.coe_le_coe, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_two,
    le_div_iff₀ (by positivity)]
  exact Nat.le_ceil _

theorem dyadicUp_le (n : ℕ) (t : ℝ≥0) : (dyadicUp n t : ℝ) ≤ t + 1 / 2 ^ n := by
  rw [dyadicUp, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_two,
    div_le_iff₀ (by positivity), add_mul, one_div, inv_mul_cancel₀ (by positivity)]
  exact (Nat.ceil_lt_add_one (by positivity)).le

theorem tendsto_dyadicUp (t : ℝ≥0) : Tendsto (fun n => dyadicUp n t) atTop (𝓝 t) := by
  rw [← NNReal.tendsto_coe]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => le_dyadicUp n t)
    (fun n => dyadicUp_le n t)
  have h : Tendsto (fun n : ℕ => (1 : ℝ) / 2 ^ n) atTop (𝓝 0) := by
    simp only [one_div]
    exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  simpa using (tendsto_const_nhds (x := (t : ℝ))).add h

theorem limOr0_eq {f : ℕ → ℂ} {l : ℂ} (h : Tendsto f atTop (𝓝 l)) : limOr0 f = l := by
  have hex : ∃ l, Tendsto f atTop (𝓝 l) := ⟨l, h⟩
  rw [limOr0, dite_eq_left_of_eq_true (eq_true hex)]
  exact tendsto_nhds_unique hex.choose_spec h

/-- **The restart data with the measurable exit**: if the flow-line segment `η([0, s])` is attached at `0` with
hull `K^U_s` and tip `η(s)`, the boundary value `x₁` is the image of the counterflow start, the counterflow is a
generating trace with a driver continuous before its lifetime, and the measurable exit is positive, then the data
`IsRestartData` hold up to the measurable exit (every time before it is alive by `isRestartAlive_of_attached`). -/
theorem isRestartData_lawExit (hq : 0 < q) (hU : Continuous U) (hU0 : U 0 = 0) (hη : IsAttachedPath η s)
    (hK₁ : QuantumZipper.fwdHull U s = fillH (η '' Icc 0 s))
    (htip : Tendsto (QuantumZipper.fwdMapInv U s) (𝓝[H] 0) (𝓝 (η s)))
    (hx₁ : (x₁ : ℂ) = bdryVal U (-1 - q) s) (htr : IsGeneratingTrace w' ζ' γ')
    (hw'c : ContinuousOn w' {t | (t : ℝ≥0∞) < ζ'}) (hw'0 : w' 0 = 0) (hpos : 0 < lawExit q η s ζ' γ') :
    IsRestartData q U s x₁ w' ζ' γ' (lawExit q η s ζ' γ') := by
  refine ⟨hq, hU, hU0, NNReal.coe_nonneg s, hx₁, htr, hw'c, hw'0, lawExit_le, hpos, fun t ht => ?_⟩
  have hg := isTraceGood_of_lt_lawExit htr.2.1 hη.cont ht
  have hK₂ : cfHull w' t = fillH (γ' '' Icc 0 t) :=
    fwdHull_eq_fillH_of_isFilling hg.2.1.isCompact_image (htr.2.2 t hg.1)
  exact isRestartAlive_of_attached hq hU hU0 hη hK₁ htip hg.2.1 hK₂ hg.2.2

end Law

/-! ### The measurable-form chart path is SEC5-G's canonical chart path -/

section Ident

variable {q : ℝ} {U : ℝ → ℝ} {x₁ : ℝ} {w' : ℝ≥0 → ℝ} {ζ' : ℝ≥0∞} {γ' : ℝ≥0 → ℂ} {η : ℝ≥0 → ℂ}
  {s : ℝ≥0}

theorem lawClock_eq_restartClock {σ : ℝ} {T : ℝ≥0∞} (hd : IsRestartData q U σ x₁ w' ζ' γ' T) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < T) : lawClock q U σ x₁ γ' t = restartClock q U σ x₁ w' t :=
  (hd.restartClock_eq_hcapHit ht).symm

/-- An infinite measurable chart capacity lifetime makes the chart capacity clock unbounded before the exit. -/
theorem exists_le_restartClock_of_lawLife (hd : IsRestartData q U s x₁ w' ζ' γ' (lawExit q η s ζ' γ'))
    (hL : lawLife q U s x₁ η s ζ' γ' = ⊤) (u : ℝ) :
    ∃ t : ℝ≥0, (t : ℝ≥0∞) < lawExit q η s ζ' γ' ∧ u ≤ restartClock q U s x₁ w' t := by
  have h : ENNReal.ofReal u < lawLife q U s x₁ η s ζ' γ' := by rw [hL]; exact ENNReal.ofReal_lt_top
  rw [lawLife, lt_iSup_iff] at h
  obtain ⟨r, hr⟩ := h
  rw [lt_iSup_iff] at hr
  obtain ⟨hrT, hlt⟩ := hr
  refine ⟨qnn r, hrT, ?_⟩
  rw [← lawClock_eq_restartClock hd hrT]
  exact (ENNReal.ofReal_lt_ofReal_iff'.1 hlt).1.le

/-- **The measurable inverse clock is the inverse of the exhausting chart capacity clock.** -/
theorem lawInv_eq_clockInv (ha : IsExhaustingClock (restartClock q U s x₁ w') (lawExit q η s ζ' γ'))
    (hcl : ∀ t : ℝ≥0, (t : ℝ≥0∞) < lawExit q η s ζ' γ' →
      lawClock q U s x₁ γ' t = restartClock q U s x₁ w' t) (u : ℝ≥0) :
    lawInv q U s x₁ η s ζ' γ' u =
      (clockInv (restartClock q U s x₁ w') (lawExit q η s ζ' γ') u : ℝ≥0∞) := by
  set T := lawExit q η s ζ' γ' with hT
  set t₀ := clockInv (restartClock q U s x₁ w') T u with ht₀def
  obtain ⟨ht₀T, ht₀u⟩ := ha.clockInv_spec u
  have hiff : ∀ r : ℚ, (qnn r : ℝ≥0∞) < T → ((u : ℝ) ≤ lawClock q U s x₁ γ' (qnn r) ↔ t₀ ≤ qnn r) := by
    intro r hr
    rw [hcl _ hr, ← ht₀u]
    exact ha.mono.le_iff_le ht₀T hr
  apply le_antisymm
  · by_contra hlt
    push Not at hlt
    obtain ⟨c, hc1, hc2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (lt_min hlt ht₀T)
    have hc1' : (t₀ : ℝ) < c := by exact_mod_cast ENNReal.coe_lt_coe.1 hc1
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hc1'
    have hr0 : (0 : ℝ) ≤ r := (NNReal.coe_nonneg t₀).trans hr1.le
    have hqr : ((qnn r : ℝ≥0) : ℝ) = r := Real.coe_toNNReal _ hr0
    have hrc : (qnn r : ℝ≥0∞) < c := by
      rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, hqr]
      exact hr2
    have hrT : (qnn r : ℝ≥0∞) < T := hrc.trans (lt_of_lt_of_le hc2 (min_le_right _ _))
    have ht₀r : t₀ ≤ qnn r := by
      rw [← NNReal.coe_le_coe, hqr]
      exact hr1.le
    have hle : lawInv q U s x₁ η s ζ' γ' u ≤ (qnn r : ℝ≥0∞) :=
      iInf₂_le r ⟨hrT, (hiff r hrT).2 ht₀r⟩
    exact absurd (hle.trans_lt (hrc.trans (lt_of_lt_of_le hc2 (min_le_left _ _)))) (lt_irrefl _)
  · exact le_iInf₂ fun r hr => ENNReal.coe_le_coe.2 ((hiff r hr.1).1 hr.2)

/-- **The measurable chart path is the canonical chart path** of SEC5-G when the measurable chart capacity lifetime
is infinite. -/
theorem lawPath_eq_restartChartPath (hd : IsRestartData q U s x₁ w' ζ' γ' (lawExit q η s ζ' γ'))
    (hL : lawLife q U s x₁ η s ζ' γ' = ⊤) :
    lawPath q U s x₁ η s ζ' γ' = restartChartPath q U s x₁ w' γ' (lawExit q η s ζ' γ') := by
  have ha := hd.isExhaustingClock (exists_le_restartClock_of_lawLife hd hL)
  funext u
  have hinv := lawInv_eq_clockInv ha (fun t ht => lawClock_eq_restartClock hd ht) u
  rw [lawPath, hinv, ENNReal.toNNReal_coe, restartChartPath]
  have ht₀ := (ha.clockInv_spec u).1
  refine limOr0_eq ?_
  have hO : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < lawExit q η s ζ' γ'} :=
    isOpen_lt ENNReal.continuous_coe continuous_const
  have hc := hd.continuousOn_restartPath.continuousAt (hO.mem_nhds ht₀)
  exact hc.tendsto.comp (tendsto_dyadicUp _)

/-- **The pathwise restart with the measurable chart path**: under the restart data up to the measurable exit and
an infinite measurable chart capacity lifetime, the completed counterflow continues the measurable chart path in the
restart chart of `ℍ ∖ A` with tip `η(s)` (SEC5-G's `IsRestartData.isCounterflowChartContinuation`), and the
measurable chart path is continuous. -/
theorem isCounterflowChartContinuation_lawPath {A : Set ℂ} {Q : ℝ}
    (hd : IsRestartData q U s x₁ w' ζ' γ' (lawExit q η s ζ' γ'))
    (hA : A ∩ H ⊆ QuantumZipper.fwdHull U s) (hA₁ : ((-1 - q : ℝ) : ℂ) ∉ A)
    (htip : Tendsto (QuantumZipper.fwdMapInv U s) (𝓝[H] 0) (𝓝 (η s)))
    (hL : lawLife q U s x₁ η s ζ' γ' = ⊤) :
    MarkovOther.IsCounterflowChartContinuation A (η s) (Sec4.stripCounterflowPath q γ') Q
        (lawPath q U s x₁ η s ζ' γ') ⊤ ∧ Continuous (lawPath q U s x₁ η s ζ' γ') := by
  rw [lawPath_eq_restartChartPath hd hL]
  exact hd.isCounterflowChartContinuation hA hA₁ htip (exists_le_restartClock_of_lawLife hd hL)

end Ident

end CrossRestart

end Sec5

end InteractingSLE
