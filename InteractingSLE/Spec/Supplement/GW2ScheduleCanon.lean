/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2ScheduleRun
import InteractingSLE.Spec.Exist.StagedAssembly
import InteractingSLE.Spec.Exist.StagedLaw2Word
import InteractingSLE.Spec.Exist.StagedLawStep

/-!
# The canonical schedule construction, jointly measurable in the field and the switching times

Packet PROVE-T14-TIP3. Lemma GB9a (`source/spec/p481-528.md` L1110, p. 527): "The independent finite-force theorem and
GB7 construct its continuous simple trace for every finite original capacity time. The retained transition kernels
make this construction jointly measurable in a finite vector of switching times." Lemma GW2 (p. 621): "run successive
canonical conditional pieces through the proposed ordered time tuple […]. The construction is measurable in the field
and the time tuple."

**The construction.** For a root `x₀`, angles `θ`, own times `Δ` and a field sample `f`, the canonical state before
instruction `k` is a pair `(word, field)`:

* initially the boundary word `c₀` of the original data translated to the root, and `f` read in the root chart;
* the `k`-th piece is the **field-determined** flow-line driver of the current field at angle `θ k` for the current
  word (`wordDrv`, from Theorem 1.2 in its word-measurable form `Theorem12ParamStatement`);
* the next word is the single-stage word `βA (word, θ k, record)` and the next field is the current field read in the
  record chart of the stopped piece (`recField`).

Everything is a deterministic function of `(Δ, f)`, so the canonical pieces of the field `h ω` are jointly measurable in
the own times and `ω` (`measurable_canonState`, `measurable_canonDrive`). The only analytic input is that the record of
a regular driver stopped at a *variable* time is measurable (`measurable_recOf_joint`): a regular driver is
right-continuous, so its value at a measurable time is a limit of its values at dyadic upper approximations.

## Main definitions and results

* `wordDrv`, `canonState`, `canonDrive`, `canonRec`;
* `IsRegularDriver.continuousWithinAt_Ici`, `measurable_eval_regular`, `measurable_recOf_joint`;
* `measurable_canonState`, `measurable_canonDrive`, `measurable_canonRec`, `isRegularDriver_canonDrive`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2Schedule

open Exist Staged StagedLaw Restart LQGMetric

/-! ### Evaluating a regular driver at a measurable time -/

/-- **A regular driver is right-continuous** (continuous before its lifetime, constant from it on). -/
theorem _root_.InteractingSLE.Exist.Staged.IsRegularDriver.continuousWithinAt_Ici {e : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (he : IsRegularDriver e) (s : ℝ≥0) : ContinuousWithinAt e.1 (Ici s) s := by
  by_cases hs : (s : ℝ≥0∞) < e.2
  · have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < e.2} := isOpen_lt ENNReal.continuous_coe continuous_const
    exact ((he.1 s hs).continuousAt (hopen.mem_nhds hs)).continuousWithinAt
  · have hconst : ∀ t ∈ Ici s, e.1 t = e.1 e.2.toNNReal := fun t ht =>
      he.2.2.1 t ((not_lt.1 hs).trans (ENNReal.coe_le_coe.2 ht))
    exact (continuousWithinAt_const (b := e.1 e.2.toNNReal)).congr hconst (hconst s (mem_Ici.2 le_rfl))

/-- The dyadic upper approximation `⌈x 2ⁿ⌉ / 2ⁿ`. -/
def dyadUp (n : ℕ) (x : ℝ≥0) : ℝ≥0 := ((⌈(x : ℝ) * 2 ^ n⌉₊ : ℝ) / 2 ^ n).toNNReal

theorem coe_dyadUp (n : ℕ) (x : ℝ≥0) : (dyadUp n x : ℝ) = (⌈(x : ℝ) * 2 ^ n⌉₊ : ℝ) / 2 ^ n :=
  Real.coe_toNNReal _ (by positivity)

theorem le_dyadUp (n : ℕ) (x : ℝ≥0) : x ≤ dyadUp n x := by
  rw [← NNReal.coe_le_coe, coe_dyadUp, le_div_iff₀ (by positivity)]
  exact Nat.le_ceil _

theorem dyadUp_le (n : ℕ) (x : ℝ≥0) : (dyadUp n x : ℝ) ≤ x + 1 / 2 ^ n := by
  rw [coe_dyadUp, div_le_iff₀ (by positivity), add_mul, one_div, inv_mul_cancel₀ (by positivity)]
  exact (Nat.ceil_lt_add_one (by positivity)).le

theorem tendsto_dyadUp (x : ℝ≥0) : Tendsto (fun n => dyadUp n x) atTop (𝓝[≥] x) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => le_dyadUp n x⟩
  rw [← NNReal.tendsto_coe]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => le_dyadUp n x)
    (fun n => dyadUp_le n x)
  have : Tendsto (fun n : ℕ => (1 : ℝ) / 2 ^ n) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    refine h.congr fun n => ?_
    rw [one_div_pow]
  simpa only [add_zero] using tendsto_const_nhds.add this

/-- **A regular driver evaluated at a measurable time is measurable.** -/
theorem measurable_eval_regular {α : Type*} [MeasurableSpace α] {F : α → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hF : Measurable F) (hreg : ∀ a, IsRegularDriver (F a)) {s : α → ℝ≥0} (hs : Measurable s) :
    Measurable fun a => (F a).1 (s a) := by
  have hev : ∀ c : ℝ≥0, Measurable fun a => (F a).1 c := fun c =>
    (measurable_pi_apply c).comp (measurable_fst.comp hF)
  have hn : ∀ n : ℕ, Measurable fun a => (F a).1 (dyadUp n (s a)) := by
    intro n
    set g : α × ℕ → ℝ := fun p => (F p.1).1 (((p.2 : ℝ) / 2 ^ n).toNNReal) with hg
    have hgm : Measurable g := measurable_from_prod_countable_left fun m =>
      show Measurable fun a => (F a).1 (((m : ℝ) / 2 ^ n).toNNReal) from hev _
    have hceil : Measurable fun a => ⌈(s a : ℝ) * 2 ^ n⌉₊ :=
      ((measurable_coe_nnreal_real.comp hs).mul_const _).nat_ceil
    exact hgm.comp (measurable_id.prodMk hceil)
  refine measurable_of_tendsto_metrizable hn (tendsto_pi_nhds.2 fun a => ?_)
  exact ((hreg a).continuousWithinAt_Ici (s a)).tendsto.comp (tendsto_dyadUp (s a))

/-- **The record of a regular driver stopped at a measurable time is measurable.** -/
theorem measurable_recOf_joint {α : Type*} [MeasurableSpace α] {F : α → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hF : Measurable F) (hreg : ∀ a, IsRegularDriver (F a)) {T : α → ℝ≥0∞} (hT : Measurable T) :
    Measurable fun a => recOf (T a) (F a) := by
  have hζ : Measurable fun a => (F a).2 := measurable_snd.comp hF
  refine Measurable.prodMk (measurable_pi_iff.2 fun q => ?_) (Measurable.prodMk ?_ ?_)
  · change Measurable fun a => (F a).1 (min ((((q : ℝ).toNNReal : ℝ≥0)) : ℝ≥0∞) (min (T a) (F a).2)).toNNReal
    exact measurable_eval_regular hF hreg (ENNReal.measurable_toNNReal.comp (measurable_const.min (hT.min hζ)))
  · exact hT.min hζ
  · have hm : MeasurableSet {a | (F a).2 ≤ T a} := measurableSet_le hζ hT
    have e : (fun a => (retOf (T a) (F a)).2.2) = fun a => if (F a).2 ≤ T a then true else false := by
      funext a
      simp only [retOf]
      split_ifs with h <;> simp [h]
    change Measurable fun a => (retOf (T a) (F a)).2.2
    rw [e]
    exact Measurable.ite hm measurable_const measurable_const

/-! ### The canonical construction -/

section Canon

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})

/-- The number of left marks of the flow-line word of a boundary word. -/
def wNL (c : BoundaryWord) : ℕ := flowLineNL c.fn c.jumps 0

/-- The number of right marks of the flow-line word of a boundary word. -/
def wNR (c : BoundaryWord) : ℕ := flowLineNR c.fn c.jumps 0

/-- The padded angle-`θ` flow-line word of a boundary word. -/
def wPad (κ θ : ℝ) (c : BoundaryWord) : PadWord := padFL κ θ c.fn c.jumps

/-- **The field-determined flow-line driver**: the angle-`θ` flow line of a field `f` whose boundary word is `c`, read
off `f` by Theorem 1.2 (the same map as `Staged.exists_flowDrv_condKernel`). -/
def wordDrv (θ : ℝ) (c : BoundaryWord) (f : DistOn upperHalfPlaneOpens) : (ℝ≥0 → ℝ) × ℝ≥0∞ :=
  stagedDrv h12p hκ wNL wNR (wPad κ θ) c (flowField 0 (θ * QuantumZipper.chiC κ) f)

theorem isRegularDriver_wordDrv (θ : ℝ) (c : BoundaryWord) (f : DistOn upperHalfPlaneOpens) :
    IsRegularDriver (wordDrv hκ h12p θ c f) :=
  stagedDrv_regular h12p hκ _ _ _ _ _

theorem measurable_wordDrv (θ : ℝ) :
    Measurable fun q : BoundaryWord × DistOn upperHalfPlaneOpens => wordDrv hκ h12p θ q.1 q.2 := by
  have hw := wordMeasStatement
  exact (measurable_stagedDrv h12p hκ hw.1 hw.2.1 (hw.2.2 κ θ)).comp
    (measurable_fst.prodMk ((measurable_flowField 0 _).comp measurable_snd))

variable (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (c₀ : BoundaryWord) (x₀ : ℝ) (θ : ℕ → ℝ)

/-- One step of the canonical construction at instruction `k`: run the field-determined piece of the state `p` for own
time `t`, then pass to the single-stage word and to the field read in the record chart of the stopped piece. -/
def canonStep (θk : ℝ) (t : ℝ≥0∞) (p : BoundaryWord × DistOn upperHalfPlaneOpens) :
    BoundaryWord × DistOn upperHalfPlaneOpens :=
  (βA (p.1, θk, recOf t (wordDrv hκ h12p θk p.1 p.2)), recField κ (recOf t (wordDrv hκ h12p θk p.1 p.2)) p.2)

/-- **The canonical state** (boundary word, field read in the current chart) before instruction `k`, for own times
`Δ` and the field sample `f`. -/
def canonState (Δ : ℕ → ℝ≥0∞) (f : DistOn upperHalfPlaneOpens) : ℕ → BoundaryWord × DistOn upperHalfPlaneOpens
  | 0 => (BoundaryWord.shiftW x₀ c₀, flowField x₀ 0 f)
  | k + 1 => canonStep hκ h12p βA (θ k) (Δ k) (canonState Δ f k)

/-- **The canonical `k`-th piece**: the field-determined driver of the canonical state. -/
def canonDrive (Δ : ℕ → ℝ≥0∞) (f : DistOn upperHalfPlaneOpens) (k : ℕ) : (ℝ≥0 → ℝ) × ℝ≥0∞ :=
  wordDrv hκ h12p (θ k) (canonState hκ h12p βA c₀ x₀ θ Δ f k).1 (canonState hκ h12p βA c₀ x₀ θ Δ f k).2

/-- The record of the canonical `k`-th piece stopped at own time `Δ k`. -/
def canonRec (Δ : ℕ → ℝ≥0∞) (f : DistOn upperHalfPlaneOpens) (k : ℕ) : RecData :=
  recOf (Δ k) (canonDrive hκ h12p βA c₀ x₀ θ Δ f k)

theorem canonState_succ (Δ : ℕ → ℝ≥0∞) (f : DistOn upperHalfPlaneOpens) (k : ℕ) :
    canonState hκ h12p βA c₀ x₀ θ Δ f (k + 1) =
      (βA ((canonState hκ h12p βA c₀ x₀ θ Δ f k).1, θ k, canonRec hκ h12p βA c₀ x₀ θ Δ f k),
        recField κ (canonRec hκ h12p βA c₀ x₀ θ Δ f k) (canonState hκ h12p βA c₀ x₀ θ Δ f k).2) := rfl

theorem isRegularDriver_canonDrive (Δ : ℕ → ℝ≥0∞) (f : DistOn upperHalfPlaneOpens) (k : ℕ) :
    IsRegularDriver (canonDrive hκ h12p βA c₀ x₀ θ Δ f k) :=
  isRegularDriver_wordDrv hκ h12p _ _ _

/-- The canonical state before instruction `k` only depends on the own times of the earlier pieces. -/
theorem canonState_congr {Δ Δ' : ℕ → ℝ≥0∞} (f : DistOn upperHalfPlaneOpens) :
    ∀ {k : ℕ}, (∀ j < k, Δ j = Δ' j) →
      canonState hκ h12p βA c₀ x₀ θ Δ f k = canonState hκ h12p βA c₀ x₀ θ Δ' f k
  | 0, _ => rfl
  | k + 1, h => by
    have ih := canonState_congr (Δ := Δ) (Δ' := Δ') f fun j hj => h j (Nat.lt_succ_of_lt hj)
    change canonStep hκ h12p βA (θ k) (Δ k) _ = canonStep hκ h12p βA (θ k) (Δ' k) _
    rw [ih, h k (Nat.lt_succ_self k)]

theorem canonDrive_congr {Δ Δ' : ℕ → ℝ≥0∞} (f : DistOn upperHalfPlaneOpens) {k : ℕ} (h : ∀ j < k, Δ j = Δ' j) :
    canonDrive hκ h12p βA c₀ x₀ θ Δ f k = canonDrive hκ h12p βA c₀ x₀ θ Δ' f k := by
  simp only [canonDrive, canonState_congr hκ h12p βA c₀ x₀ θ f h]

/-- A measurable map of three measurable arguments. -/
theorem measurable_apply_triple {α X Y Z V : Type*} [MeasurableSpace α] [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] [MeasurableSpace V] {g : X × Y × Z → V} (hg : Measurable g) {x : α → X} {y : α → Y}
    {z : α → Z} (hx : Measurable x) (hy : Measurable y) (hz : Measurable z) :
    Measurable fun a => g (x a, y a, z a) :=
  hg.comp (hx.prodMk (hy.prodMk hz))

/-- **One step of the canonical construction is measurable** in the own time and the state. -/
theorem measurable_canonStep (hβA : Measurable βA) (θk : ℝ) :
    Measurable fun q : ℝ≥0∞ × (BoundaryWord × DistOn upperHalfPlaneOpens) => canonStep hκ h12p βA θk q.1 q.2 := by
  have hd : Measurable fun q : ℝ≥0∞ × (BoundaryWord × DistOn upperHalfPlaneOpens) => wordDrv hκ h12p θk q.2.1 q.2.2 :=
    (measurable_wordDrv hκ h12p θk).comp measurable_snd
  have hr : Measurable fun q : ℝ≥0∞ × (BoundaryWord × DistOn upperHalfPlaneOpens) =>
      recOf q.1 (wordDrv hκ h12p θk q.2.1 q.2.2) :=
    measurable_recOf_joint hd (fun _ => isRegularDriver_wordDrv hκ h12p _ _ _) measurable_fst
  exact (measurable_apply_triple hβA (measurable_fst.comp measurable_snd) measurable_const hr).prodMk
    (measurable_recField_comp κ hr (measurable_snd.comp measurable_snd))

/-- **The canonical state is jointly measurable in the own times and the field.** -/
theorem measurable_canonState (hβA : Measurable βA) :
    ∀ k : ℕ, Measurable fun p : (ℕ → ℝ≥0∞) × DistOn upperHalfPlaneOpens =>
      canonState hκ h12p βA c₀ x₀ θ p.1 p.2 k
  | 0 => measurable_const.prodMk ((measurable_flowField x₀ 0).comp measurable_snd)
  | k + 1 => (measurable_canonStep hκ h12p βA hβA (θ k)).comp
      (((measurable_pi_apply k).comp measurable_fst).prodMk (measurable_canonState hβA k))

theorem measurable_canonDrive (hβA : Measurable βA) (k : ℕ) :
    Measurable fun p : (ℕ → ℝ≥0∞) × DistOn upperHalfPlaneOpens => canonDrive hκ h12p βA c₀ x₀ θ p.1 p.2 k :=
  (measurable_wordDrv hκ h12p (θ k)).comp (measurable_canonState hκ h12p βA c₀ x₀ θ hβA k)

theorem measurable_canonRec (hβA : Measurable βA) (k : ℕ) :
    Measurable fun p : (ℕ → ℝ≥0∞) × DistOn upperHalfPlaneOpens => canonRec hκ h12p βA c₀ x₀ θ p.1 p.2 k :=
  measurable_recOf_joint (measurable_canonDrive hκ h12p βA c₀ x₀ θ hβA k)
    (fun _ => isRegularDriver_canonDrive hκ h12p βA c₀ x₀ θ _ _ _) ((measurable_pi_apply k).comp measurable_fst)

end Canon

end GW2Schedule

end Theorem14

end InteractingSLE
