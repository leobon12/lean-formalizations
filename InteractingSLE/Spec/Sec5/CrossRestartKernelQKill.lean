/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketTraversal
import InteractingSLE.Spec.Sec5.CrossRestartKernelCfSide
import InteractingSLE.Spec.Sec5.CrossRestartKernelCfBase
import InteractingSLE.WangWu.ReverseContactMartWord

/-!
# Lemma 4.7 in the chart `Q`: killed non-simple curves and their killed words

Packet PROVE-CFRESTART4, item D1 of PROVE-CFRESTART3's route (specification p. 118: the counterflow `η′` given the flow
line prefix `η([0, τ])`, mapped by the chart of `𝒮 ∖ η([0, τ])`; Lemma 4.5 at `κ′ = 16/κ`). The image of the
counterflow (parameter `16/κ > 4`) in the flow line's chart is **not simple**, so WangWu's killed-arc chain
(`WangWu.IsKilledArc`, whose local drivers are *defined* through the hull identity `K = γ((0, u])`) does not apply.

This file gives the non-simple replacement, through the canonical driver of curves with local drivers
(`Sec7.PocketTraversal.IsDrivenCurve`, PROVE-STRIPSYS10):

* `IsKilledCurve γ P`: on an initial interval `P = [0, u₀)` of `[0, ∞)` (open at its right end), `γ` is continuous from
  `0`, lies in `ℍ` at positive times, and on every `[0, S]`, `S ∈ P`, its capacity clock is a continuous strictly
  increasing clock of a continuous driver whose hulls are the **filled** prefixes `fill(γ([0, u]))`;
* `kcTime P` (an increasing homeomorphism `[0, ∞) → P`) and `kcCurve γ P = γ ∘ kcTime P`, which is a driven curve
  (**`IsKilledCurve.isDrivenCurve`**) with the same filled prefixes and capacity clock;
* the killed word: `kcLife` (terminal capacity), `kcW` (the canonical driver `segDriver`, killed), `kcVL`, `kcVR`
  (geometric images of real marks), `kcTr` (the trace in capacity time);
* **`isKilledWord_kc`**: the deterministic clauses of `ImgDrv.IsKilledWord` (strict separation of the marks at positive
  times from the trace staying in `ℍ`, `CrossRestart.chartAR_pos_of_mem_H` on a frozen global trace);
* **`IsKilledCurve.isGeneratingTrace_kcTr`**, `IsKilledCurve.kcTr_capClock`: the trace generates the killed chain
  before the terminal capacity and passes through `γ(u)` at the capacity time of `u`.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossRestart.KernelQ

open Sec7.Lemma71C (capClock capLife capInv segDrv segDriver exists_lt_capClock_of_lt_capLife)
open Sec7.PocketTraversal (IsDrivenCurve capTrace)
open WangWu.ImgWord (IsLocCont kImg)

/-! ### Killed non-simple curves -/

/-- **A killed (possibly non-simple) curve**: `γ` is continuous from `0` on an initial interval `P` of `[0, ∞)` that is
open at its right end, lies in `ℍ` at positive times of `P`, and on every `[0, S]`, `S ∈ P`, its capacity clock is a
continuous strictly increasing clock of a continuous driver started at `0` whose hulls are the filled prefixes. -/
structure IsKilledCurve (γ : ℝ → ℂ) (P : Set ℝ) : Prop where
  zero_mem : (0 : ℝ) ∈ P
  nonneg : ∀ u ∈ P, 0 ≤ u
  icc : ∀ S ∈ P, Icc 0 S ⊆ P
  exists_gt : ∀ S ∈ P, ∃ S' ∈ P, S < S'
  zero : γ 0 = 0
  cont : ContinuousOn γ P
  mem_H : ∀ u ∈ P, 0 < u → γ u ∈ H
  localDriver : ∀ S ∈ P, 0 < S → ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ capClock γ 0 = 0 ∧
    StrictMonoOn (capClock γ) (Icc 0 S) ∧ ContinuousOn (capClock γ) (Icc 0 S) ∧
    ∀ t ∈ Icc 0 S, 0 ≤ capClock γ t ∧ fwdHull W (capClock γ t) = fillH (γ '' Icc 0 t)

/-! ### The time change onto `P` -/

open scoped Classical in
/-- **The time change** `[0, ∞) → P`: `t ↦ u₀ t/(1 + t)` when `P = [0, u₀)` is bounded, the identity otherwise. -/
def kcTime (P : Set ℝ) (t : ℝ) : ℝ := if BddAbove P then sSup P * (t / (1 + t)) else t

/-- **The time-changed curve** `γ ∘ kcTime P`, defined on `[0, ∞)`. -/
def kcCurve (γ : ℝ → ℂ) (P : Set ℝ) (t : ℝ) : ℂ := γ (kcTime P t)

variable {γ : ℝ → ℂ} {P : Set ℝ}

namespace IsKilledCurve

theorem pos_of_mem (hγ : IsKilledCurve γ P) {u : ℝ} (hu : u ∈ P) (hne : u ≠ 0) : 0 < u :=
  lt_of_le_of_ne (hγ.nonneg u hu) (Ne.symm hne)

/-- `P` contains every nonnegative time below one of its points. -/
theorem mem_of_le (hγ : IsKilledCurve γ P) {S u : ℝ} (hS : S ∈ P) (hu0 : 0 ≤ u) (huS : u ≤ S) : u ∈ P :=
  hγ.icc S hS ⟨hu0, huS⟩

/-- A bounded `P` is `[0, sup P)`. -/
theorem mem_iff_of_bddAbove (hγ : IsKilledCurve γ P) (hb : BddAbove P) {u : ℝ} :
    u ∈ P ↔ 0 ≤ u ∧ u < sSup P := by
  constructor
  · intro hu
    obtain ⟨S', hS', huS'⟩ := hγ.exists_gt u hu
    exact ⟨hγ.nonneg u hu, huS'.trans_le (le_csSup hb hS')⟩
  · rintro ⟨hu0, hu⟩
    obtain ⟨S, hS, huS⟩ := exists_lt_of_lt_csSup ⟨0, hγ.zero_mem⟩ hu
    exact hγ.mem_of_le hS hu0 huS.le

/-- An unbounded `P` is `[0, ∞)`. -/
theorem mem_iff_of_not_bddAbove (hγ : IsKilledCurve γ P) (hb : ¬ BddAbove P) {u : ℝ} : u ∈ P ↔ 0 ≤ u := by
  refine ⟨hγ.nonneg u, fun hu0 => ?_⟩
  rw [not_bddAbove_iff] at hb
  obtain ⟨S, hS, huS⟩ := hb u
  exact hγ.mem_of_le hS hu0 huS.le

theorem sSup_pos (hγ : IsKilledCurve γ P) (hb : BddAbove P) : 0 < sSup P := by
  obtain ⟨S, hS, hS0⟩ := hγ.exists_gt 0 hγ.zero_mem
  exact hS0.trans_le (le_csSup hb hS)

end IsKilledCurve

theorem kcTime_zero (P : Set ℝ) : kcTime P 0 = 0 := by
  unfold kcTime
  split_ifs <;> simp

theorem div_one_add_lt_one {t : ℝ} (ht : 0 ≤ t) : t / (1 + t) < 1 := by
  rw [div_lt_one (by linarith)]
  linarith

theorem strictMonoOn_div_one_add : StrictMonoOn (fun t : ℝ => t / (1 + t)) (Ici 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) ≤ a := ha
  have hb' : (0 : ℝ) ≤ b := hb
  simp only
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

namespace IsKilledCurve

variable (hγ : IsKilledCurve γ P)
include hγ

theorem kcTime_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ kcTime P t := by
  unfold kcTime
  split_ifs with hb
  · exact mul_nonneg (hγ.sSup_pos hb).le (div_nonneg ht (by linarith))
  · exact ht

theorem kcTime_mem {t : ℝ} (ht : 0 ≤ t) : kcTime P t ∈ P := by
  by_cases hb : BddAbove P
  · rw [hγ.mem_iff_of_bddAbove hb]
    refine ⟨hγ.kcTime_nonneg ht, ?_⟩
    simp only [kcTime, hb, ↓reduceIte]
    have hpos := hγ.sSup_pos hb
    have h1 := div_one_add_lt_one ht
    nlinarith
  · rw [hγ.mem_iff_of_not_bddAbove hb]
    exact hγ.kcTime_nonneg ht

theorem strictMonoOn_kcTime : StrictMonoOn (kcTime P) (Ici 0) := by
  intro a ha b hb hab
  unfold kcTime
  split_ifs with hbd
  · exact mul_lt_mul_of_pos_left (strictMonoOn_div_one_add ha hb hab) (hγ.sSup_pos hbd)
  · exact hab

omit hγ in
theorem continuousOn_kcTime : ContinuousOn (kcTime P) (Ici 0) := by
  unfold kcTime
  split_ifs
  · refine continuousOn_const.mul (continuousOn_id.div (continuousOn_const.add continuousOn_id) ?_)
    intro t ht
    have : (0 : ℝ) ≤ t := ht
    show (1 : ℝ) + t ≠ 0
    linarith
  · exact continuousOn_id

/-- Every point of `P` is reached by the time change. -/
theorem exists_kcTime_eq {u : ℝ} (hu : u ∈ P) : ∃ t, 0 ≤ t ∧ kcTime P t = u := by
  by_cases hb : BddAbove P
  · obtain ⟨hu0, hus⟩ := (hγ.mem_iff_of_bddAbove hb).1 hu
    set c := sSup P with hc
    have hcu : 0 < c - u := by linarith
    refine ⟨u / (c - u), div_nonneg hu0 hcu.le, ?_⟩
    simp only [kcTime, hb, ↓reduceIte]
    rw [← hc]
    have h1 : 1 + u / (c - u) = c / (c - u) := by field_simp; ring
    have hc0 : c ≠ 0 := by rw [hc]; exact (hγ.sSup_pos hb).ne'
    rw [h1, div_div_div_cancel_right₀ hcu.ne']
    field_simp
  · exact ⟨u, hγ.nonneg u hu, by simp only [kcTime, hb, ↓reduceIte]⟩

/-- The time change maps `[0, t]` onto `[0, kcTime P t]`. -/
theorem image_kcTime_Icc {t : ℝ} (ht : 0 ≤ t) : kcTime P '' Icc 0 t = Icc 0 (kcTime P t) := by
  apply Subset.antisymm
  · rintro _ ⟨s, hs, rfl⟩
    refine ⟨hγ.kcTime_nonneg hs.1, ?_⟩
    exact hγ.strictMonoOn_kcTime.monotoneOn hs.1 ht hs.2
  · intro u hu
    have hsub : Icc 0 (kcTime P t) ⊆ kcTime P '' Icc 0 t := by
      have := intermediate_value_Icc ht ((continuousOn_kcTime (P := P)).mono fun s hs => hs.1)
      rwa [kcTime_zero] at this
    exact hsub hu

theorem image_kcCurve_Icc {t : ℝ} (ht : 0 ≤ t) : kcCurve γ P '' Icc 0 t = γ '' Icc 0 (kcTime P t) := by
  rw [← hγ.image_kcTime_Icc ht, image_image]
  rfl

/-- The capacity clock of the time-changed curve. -/
theorem capClock_kcCurve {t : ℝ} (ht : 0 ≤ t) : capClock (kcCurve γ P) t = capClock γ (kcTime P t) := by
  simp only [capClock, hγ.image_kcCurve_Icc ht]

/-- **The time-changed curve is a driven curve** (`Sec7.PocketTraversal.IsDrivenCurve`). -/
theorem isDrivenCurve : IsDrivenCurve (kcCurve γ P) where
  continuousOn := by
    refine hγ.cont.comp (continuousOn_kcTime (P := P)) fun t ht => hγ.kcTime_mem ht
  zero := by simp only [kcCurve, kcTime_zero, hγ.zero]
  localDriver := by
    intro S hS
    have hS' : kcTime P S ∈ P := hγ.kcTime_mem hS.le
    have hS'0 : 0 < kcTime P S := by
      have := hγ.strictMonoOn_kcTime (a := 0) (b := S) self_mem_Ici hS.le hS
      rwa [kcTime_zero] at this
    obtain ⟨W, hW, hW0, hc0, hm, hc, hK⟩ := hγ.localDriver _ hS' hS'0
    have hmaps : MapsTo (kcTime P) (Icc 0 S) (Icc 0 (kcTime P S)) := fun t ht =>
      ⟨hγ.kcTime_nonneg ht.1, hγ.strictMonoOn_kcTime.monotoneOn ht.1 hS.le ht.2⟩
    have heq : EqOn (capClock (kcCurve γ P)) (capClock γ ∘ kcTime P) (Icc 0 S) := fun t ht =>
      hγ.capClock_kcCurve ht.1
    refine ⟨W, hW, hW0, by rw [hγ.capClock_kcCurve le_rfl, kcTime_zero, hc0], ?_, ?_, ?_⟩
    · refine StrictMonoOn.congr ?_ heq.symm
      exact fun a ha b hb hab => hm (hmaps ha) (hmaps hb)
        (hγ.strictMonoOn_kcTime ha.1 hb.1 hab)
    · exact (hc.comp ((continuousOn_kcTime (P := P)).mono fun t ht => ht.1) hmaps).congr heq
    · intro t ht
      rw [heq ht]
      obtain ⟨h1, h2⟩ := hK _ (hmaps ht)
      refine ⟨h1, ?_⟩
      rw [Function.comp_apply, h2, hγ.image_kcCurve_Icc ht.1]

end IsKilledCurve

/-! ### The killed word -/

/-- **The terminal capacity** of a killed curve (that of its time change). -/
def kcLife (γ : ℝ → ℂ) (P : Set ℝ) : WithTop ℝ≥0 := capLife (kcCurve γ P)

open scoped Classical in
/-- **The killed driver**: the canonical driver of the time-changed curve before the terminal capacity, `0` after. -/
def kcW (γ : ℝ → ℂ) (P : Set ℝ) (t : ℝ≥0) : ℝ :=
  if (t : WithTop ℝ≥0) < kcLife γ P then segDriver (kcCurve γ P) t else 0

/-- The killed driver read on `ℝ`. -/
def kcPath (γ : ℝ → ℂ) (P : Set ℝ) (r : ℝ) : ℝ := kcW γ P r.toNNReal

/-- The geometric images of right marks under the killed driver (raw form). -/
def kcVRr (γ : ℝ → ℂ) (P : Set ℝ) {n : ℕ} (xR : Fin n → ℝ) (j : Fin n) (t : ℝ≥0) : ℝ := kImg (kcPath γ P) (xR j) t

/-- The geometric images of left marks under the killed driver (raw form, through the reflected flow). -/
def kcVLr (γ : ℝ → ℂ) (P : Set ℝ) {n : ℕ} (xL : Fin n → ℝ) (i : Fin n) (t : ℝ≥0) : ℝ :=
  -kImg (fun r => -kcPath γ P r) (-xL i) t

open scoped Classical in
/-- **The images of right marks** before the terminal capacity, `0` afterwards. -/
def kcVR (γ : ℝ → ℂ) (P : Set ℝ) {n : ℕ} (xR : Fin n → ℝ) (j : Fin n) (t : ℝ≥0) : ℝ :=
  if (t : WithTop ℝ≥0) < kcLife γ P then kcVRr γ P xR j t else 0

open scoped Classical in
/-- **The images of left marks** before the terminal capacity, `0` afterwards. -/
def kcVL (γ : ℝ → ℂ) (P : Set ℝ) {n : ℕ} (xL : Fin n → ℝ) (i : Fin n) (t : ℝ≥0) : ℝ :=
  if (t : WithTop ℝ≥0) < kcLife γ P then kcVLr γ P xL i t else 0

/-- **The trace of the killed chain in capacity time.** -/
def kcTr (γ : ℝ → ℂ) (P : Set ℝ) : ℝ≥0 → ℂ := capTrace (kcCurve γ P)

theorem lt_kcLife_iff {t : ℝ≥0} :
    (t : WithTop ℝ≥0) < kcLife γ P ↔ (t : ℝ≥0∞) < capLife (kcCurve γ P) := Iff.rfl

theorem lt_kcLife_iff_ofReal {t : ℝ≥0} :
    (t : WithTop ℝ≥0) < kcLife γ P ↔ ENNReal.ofReal (t : ℝ) < capLife (kcCurve γ P) := by
  rw [ENNReal.ofReal_coe_nnreal]; exact Iff.rfl

theorem kcW_of_lt {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) < kcLife γ P) :
    kcW γ P t = segDriver (kcCurve γ P) t := by
  simp only [kcW, ht, ↓reduceIte]

theorem kcPath_coe (t : ℝ≥0) : kcPath γ P t = kcW γ P t := by simp [kcPath]

theorem kcPath_eq_kcW : (fun t : ℝ≥0 => kcPath γ P t) = kcW γ P := funext kcPath_coe

theorem kcVR_of_lt {n : ℕ} (xR : Fin n → ℝ) (j : Fin n) {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) < kcLife γ P) :
    kcVR γ P xR j t = kcVRr γ P xR j t := by
  simp only [kcVR, ht, ↓reduceIte]

theorem kcVL_of_lt {n : ℕ} (xL : Fin n → ℝ) (i : Fin n) {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) < kcLife γ P) :
    kcVL γ P xL i t = kcVLr γ P xL i t := by
  simp only [kcVL, ht, ↓reduceIte]

namespace IsKilledCurve

variable (hγ : IsKilledCurve γ P)
include hγ

/-- A capacity time `r ≤ capClock (kcCurve γ P) n` is before the terminal capacity. -/
theorem lt_kcLife_of_le_capClock {n : ℕ} {r : ℝ} (hr : r ≤ capClock (kcCurve γ P) n) :
    ((r.toNNReal : ℝ≥0) : WithTop ℝ≥0) < kcLife γ P := by
  rw [lt_kcLife_iff]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine lt_of_le_of_lt ?_ (hγ.isDrivenCurve.ofReal_capClock_lt hn)
  exact ENNReal.coe_le_coe.2 (Real.toNNReal_le_toNNReal hr)

/-- **The killed driver is locally continuous before the terminal capacity**: it agrees with a local driver on
`[0, capClock n]` beyond every capacity time before the terminal one. -/
theorem exists_eqOn_localDriver {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) < kcLife γ P) :
    ∃ c : ℝ, (t : ℝ) < c ∧ ∃ w : ℝ → ℝ, Continuous w ∧ w 0 = 0 ∧ EqOn (kcPath γ P) w (Icc 0 c) := by
  have hD := hγ.isDrivenCurve
  obtain ⟨n, hn0, hn⟩ := hD.exists_pos_lt_capClock t.coe_nonneg (lt_kcLife_iff_ofReal.1 ht)
  obtain ⟨W, hW, hW0, -, -, -, hK⟩ := hD.localDriver n hn0
  refine ⟨_, hn, W, hW, hW0, fun r hr => ?_⟩
  have hlt := hγ.lt_kcLife_of_le_capClock hr.2
  show kcW γ P r.toNNReal = W r
  rw [kcW_of_lt hlt]
  show segDrv (kcCurve γ P) (r.toNNReal : ℝ) = W r
  rw [Real.coe_toNNReal _ hr.1]
  exact hD.segDrv_eq hn0 hW hW0 (fun s hs => (hK s hs).2) hr.1 hr.2

theorem isLocCont : IsLocCont (kcPath γ P) (kcLife γ P) := fun t ht => by
  obtain ⟨c, htc, w, hw, -, hEq⟩ := hγ.exists_eqOn_localDriver ht
  exact ⟨c, htc, w, hw, hEq⟩

theorem zero_lt_kcLife : (0 : WithTop ℝ≥0) < kcLife γ P := by
  have h := hγ.lt_kcLife_of_le_capClock (n := 0) (r := 0) (by
    rw [Nat.cast_zero, hγ.isDrivenCurve.capClock_zero])
  simpa using h

theorem kcW_zero : kcW γ P 0 = 0 := by
  rw [kcW_of_lt hγ.zero_lt_kcLife]
  exact hγ.isDrivenCurve.segDriver_spec.1

theorem continuousOn_kcW : ContinuousOn (kcW γ P) {t | (t : WithTop ℝ≥0) < kcLife γ P} := by
  rw [← kcPath_eq_kcW]
  exact hγ.isLocCont.continuousOn

/-- **A frozen global trace** through every capacity time before the terminal one: a continuous driver agreeing with
the killed driver on `[0, t]` and a Loewner trace of it on `[0, ∞)` that lies in `ℍ` on `(0, t]`. -/
theorem exists_frozenTrace {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) < kcLife γ P) :
    ∃ (V : ℝ → ℝ) (α : ℝ → ℂ), Continuous V ∧ V 0 = 0 ∧ IsLoewnerTrace V α ∧
      EqOn (kcPath γ P) V (Icc 0 (t : ℝ)) ∧ ∀ s ∈ Ioc (0 : ℝ) t, α s ∈ H := by
  have hD := hγ.isDrivenCurve
  obtain ⟨T, htT, hTL⟩ := exists_between (lt_kcLife_iff.1 ht)
  have hgen := hD.isGeneratingTrace hTL
  have hw : ContinuousOn (segDriver (kcCurve γ P)) {s : ℝ≥0 | (s : ℝ≥0∞) < T} :=
    hD.segDriver_spec.2.1.mono fun s hs => lt_trans hs hTL
  obtain ⟨V, α, hV, hV0, hVα, hVeq, hαeq, -⟩ :=
    exists_frozen_isLoewnerTrace hgen hw hD.segDriver_spec.1 htT
  refine ⟨V, α, hV, hV0, hVα, fun s hs => ?_, fun s hs => ?_⟩
  · have hst : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hs.2
    have hlt : ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) < kcLife γ P :=
      lt_of_le_of_lt (WithTop.coe_le_coe.2 hst) ht
    rw [hVeq s ⟨hs.1, hs.2⟩]
    show kcW γ P s.toNNReal = _
    rw [kcW_of_lt hlt]
  · rw [hαeq s ⟨hs.1.le, hs.2⟩]
    have hs' : ENNReal.ofReal s < capLife (kcCurve γ P) := by
      refine lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hs.2) ?_
      rw [ENNReal.ofReal_coe_nnreal]
      exact lt_kcLife_iff.1 ht
    obtain ⟨hi0, hic⟩ := hD.capInv_spec hs.1.le hs'
    have hipos : 0 < capInv (kcCurve γ P) s := by
      refine lt_of_le_of_ne hi0 fun h => ?_
      rw [← h, hD.capClock_zero] at hic
      exact hs.1.ne hic
    show kcCurve γ P (capInv (kcCurve γ P) (s.toNNReal : ℝ)) ∈ H
    rw [Real.coe_toNNReal _ hs.1.le]
    have hpos : 0 < kcTime P (capInv (kcCurve γ P) s) := by
      have := hγ.strictMonoOn_kcTime (a := 0) self_mem_Ici hi0 hipos
      rwa [kcTime_zero] at this
    exact hγ.mem_H _ (hγ.kcTime_mem hi0) hpos

/-- **Strict separation on the right** at positive times before the terminal capacity (the trace stays in `ℍ`). -/
theorem kcW_lt_kcVRr {n : ℕ} {xR : Fin n → ℝ} (hx : ∀ j, 0 ≤ xR j) {t : ℝ≥0} (ht0 : 0 < t)
    (ht : (t : WithTop ℝ≥0) < kcLife γ P) (j : Fin n) : kcW γ P t < kcVRr γ P xR j t := by
  obtain ⟨V, α, hV, hV0, hVα, hEq, hαH⟩ := hγ.exists_frozenTrace ht
  have hpos := CrossRestart.chartAR_pos_of_mem_H hVα hαH hV hV0 (show (0 : ℝ) < t from ht0)
  unfold WangWu.chartAR at hpos
  have hm := MartChar.RealFlow.rightImg_mono_index hV t.coe_nonneg (hx j)
  rw [← kcPath_coe, kcVRr, kImg, Sec7.Lemma71B.rightImg_congr hV t.coe_nonneg hEq, hEq ⟨t.coe_nonneg, le_rfl⟩]
  linarith

/-- **Strict separation on the left.** -/
theorem kcVLr_lt_kcW {n : ℕ} {xL : Fin n → ℝ} (hx : ∀ i, xL i ≤ 0) {t : ℝ≥0} (ht0 : 0 < t)
    (ht : (t : WithTop ℝ≥0) < kcLife γ P) (i : Fin n) : kcVLr γ P xL i t < kcW γ P t := by
  obtain ⟨V, α, hV, hV0, hVα, hEq, hαH⟩ := hγ.exists_frozenTrace ht
  have hneg := CrossRestart.chartAL_neg_of_mem_H hVα hαH hV hV0 (show (0 : ℝ) < t from ht0)
  unfold WangWu.chartAL at hneg
  have hVn : Continuous fun s => -V s := hV.neg
  have hEq' : EqOn (fun r => -kcPath γ P r) (fun r => -V r) (Icc 0 (t : ℝ)) := fun r hr => by
    simp only [hEq hr]
  have hm := MartChar.RealFlow.rightImg_mono_index hVn t.coe_nonneg (neg_nonneg.2 (hx i))
  rw [← kcPath_coe, kcVLr, kImg, Sec7.Lemma71B.rightImg_congr hVn t.coe_nonneg hEq',
    hEq ⟨t.coe_nonneg, le_rfl⟩]
  linarith

theorem kcW_le_kcVRr {n : ℕ} (xR : Fin n → ℝ) {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) < kcLife γ P) (j : Fin n) :
    kcW γ P t ≤ kcVRr γ P xR j t := by
  rw [← kcPath_coe]
  exact hγ.isLocCont.le_kImg ht (xR j)

theorem kcVLr_le_kcW {n : ℕ} (xL : Fin n → ℝ) {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) < kcLife γ P) (i : Fin n) :
    kcVLr γ P xL i t ≤ kcW γ P t := by
  have := hγ.isLocCont.neg.le_kImg ht (-xL i)
  rw [← kcPath_coe]
  unfold kcVLr
  linarith

/-! #### The capacity clock on `P` -/

theorem capClock_zero : capClock γ 0 = 0 := by
  obtain ⟨S, hS, hS0⟩ := hγ.exists_gt 0 hγ.zero_mem
  exact (hγ.localDriver S hS hS0).choose_spec.2.2.1

theorem strictMonoOn_capClock : StrictMonoOn (capClock γ) P := by
  intro a ha b hb hab
  have hb0 : 0 < b := lt_of_le_of_lt (hγ.nonneg a ha) hab
  obtain ⟨-, -, -, -, hm, -, -⟩ := hγ.localDriver b hb hb0
  exact hm ⟨hγ.nonneg a ha, hab.le⟩ ⟨hb0.le, le_rfl⟩ hab

theorem continuousOn_capClock : ContinuousOn (capClock γ) P := by
  intro t ht
  obtain ⟨S, hS, htS⟩ := hγ.exists_gt t ht
  have hS0 : 0 < S := lt_of_le_of_lt (hγ.nonneg t ht) htS
  obtain ⟨-, -, -, -, -, hc, -⟩ := hγ.localDriver S hS hS0
  have hnhds : Icc 0 S ∈ 𝓝[P] t :=
    mem_nhdsWithin.2 ⟨Iio S, isOpen_Iio, htS, fun u hu => ⟨hγ.nonneg u hu.2, le_of_lt hu.1⟩⟩
  exact (hc t ⟨hγ.nonneg t ht, htS.le⟩).mono_of_mem_nhdsWithin hnhds

theorem capClock_nonneg {u : ℝ} (hu : u ∈ P) : 0 ≤ capClock γ u := by
  rw [← hγ.capClock_zero]
  exact hγ.strictMonoOn_capClock.monotoneOn hγ.zero_mem hu (hγ.nonneg u hu)

/-- **The terminal capacity is the supremum of the clock on `P`.** -/
theorem lt_kcLife_iff_exists {t : ℝ≥0} :
    (t : WithTop ℝ≥0) < kcLife γ P ↔ ∃ S ∈ P, (t : ℝ) < capClock γ S := by
  have hD := hγ.isDrivenCurve
  constructor
  · intro ht
    obtain ⟨n, hn⟩ := exists_lt_capClock_of_lt_capLife (lt_kcLife_iff_ofReal.1 ht)
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    exact ⟨kcTime P n, hγ.kcTime_mem hn0, by rwa [← hγ.capClock_kcCurve hn0]⟩
  · rintro ⟨S, hS, htS⟩
    obtain ⟨t₀, ht₀, rfl⟩ := hγ.exists_kcTime_eq hS
    rw [← hγ.capClock_kcCurve ht₀] at htS
    rw [lt_kcLife_iff_ofReal]
    exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg t.coe_nonneg).2 htS)
      (hD.ofReal_capClock_lt ht₀).le

theorem lt_kcLife {S : ℝ} (hS : S ∈ P) : (((capClock γ S).toNNReal : ℝ≥0) : WithTop ℝ≥0) < kcLife γ P := by
  obtain ⟨S', hS', hSS'⟩ := hγ.exists_gt S hS
  refine hγ.lt_kcLife_iff_exists.2 ⟨S', hS', ?_⟩
  rw [Real.coe_toNNReal _ (hγ.capClock_nonneg hS)]
  exact hγ.strictMonoOn_capClock hS hS' hSS'

/-! #### The trace in capacity time -/

/-- **The trace passes through `γ(u)` at the capacity time of `u`.** -/
theorem kcTr_capClock {u : ℝ} (hu : u ∈ P) : kcTr γ P (capClock γ u).toNNReal = γ u := by
  obtain ⟨t, ht, rfl⟩ := hγ.exists_kcTime_eq hu
  have hD := hγ.isDrivenCurve
  rw [← hγ.capClock_kcCurve ht]
  show kcCurve γ P (capInv (kcCurve γ P) ((capClock (kcCurve γ P) t).toNNReal : ℝ)) = γ (kcTime P t)
  rw [Real.coe_toNNReal _ (hD.capClock_nonneg ht), hD.capInv_eq ht]
  rfl

/-- **The trace generates the killed chain** on `[0, T]` for every `T` below the terminal capacity. -/
theorem isGeneratingTrace_kcTr {T : ℝ≥0∞} (hT : T < kcLife γ P) : IsGeneratingTrace (kcW γ P) T (kcTr γ P) := by
  refine Sec7.IsGeneratingTrace.congr_lt (hγ.isDrivenCurve.isGeneratingTrace hT) fun t ht => ?_
  exact kcW_of_lt (lt_trans ht hT)

/-- The trace lies in `ℍ` at positive times before the terminal capacity. -/
theorem kcTr_mem_H {t : ℝ≥0} (ht0 : 0 < t) (ht : (t : WithTop ℝ≥0) < kcLife γ P) : kcTr γ P t ∈ H := by
  have hD := hγ.isDrivenCurve
  have hs' : ENNReal.ofReal (t : ℝ) < capLife (kcCurve γ P) := lt_kcLife_iff_ofReal.1 ht
  obtain ⟨hi0, hic⟩ := hD.capInv_spec t.coe_nonneg hs'
  have hipos : 0 < capInv (kcCurve γ P) t := by
    refine lt_of_le_of_ne hi0 fun h => ?_
    rw [← h, hD.capClock_zero] at hic
    exact (show (0 : ℝ) < t from ht0).ne hic
  have hpos : 0 < kcTime P (capInv (kcCurve γ P) t) := by
    have := hγ.strictMonoOn_kcTime (a := 0) self_mem_Ici hi0 hipos
    rwa [kcTime_zero] at this
  exact hγ.mem_H _ (hγ.kcTime_mem hi0) hpos

end IsKilledCurve

/-! ### The killed word of a family of killed curves -/

/-- **The killed word of a family of killed curves**: the killed drivers with the images of left marks `xL ≤ 0`
(antitone in the index) and right marks `xR ≥ 0` (monotone in the index) satisfy the deterministic clauses of Lemma
2.11's killed form (`ImgDrv.IsKilledWord`), killed at the terminal capacities. -/
theorem isKilledWord_kcr {Ω : Type*} {nL nR : ℕ} {γ : Ω → ℝ → ℂ} {P : Ω → Set ℝ}
    (hγ : ∀ ω, IsKilledCurve (γ ω) (P ω)) {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
    (hxL : ∀ ω i, xL ω i ≤ 0) (hxR : ∀ ω j, 0 ≤ xR ω j) (hxLa : ∀ ω, Antitone (xL ω))
    (hxRm : ∀ ω, Monotone (xR ω)) :
    WangWu.ImgDrv.IsKilledWord (fun t ω => kcW (γ ω) (P ω) t) (fun i t ω => kcVLr (γ ω) (P ω) (xL ω) i t)
      (fun j t ω => kcVRr (γ ω) (P ω) (xR ω) j t) (fun ω => kcLife (γ ω) (P ω)) where
  w_zero ω := (hγ ω).kcW_zero
  contW ω := (hγ ω).continuousOn_kcW
  ordL ω t i ht := (hγ ω).kcVLr_le_kcW (xL ω) ht i
  ordR ω t j ht := (hγ ω).kcW_le_kcVRr (xR ω) ht j
  pathL ω i := by
    have h := WangWu.ImgWord.isForcePathBefore_neg
      ((hγ ω).isLocCont.neg.isForcePathBefore (-xL ω i) fun t ht0 ht => by
        have := (hγ ω).kcVLr_lt_kcW (hxL ω) ht0 ht i
        rw [← kcPath_coe] at this
        unfold kcVLr at this
        show -kcPath (γ ω) (P ω) t < _
        linarith)
    simp only [neg_neg, kcPath_coe] at h
    exact h
  pathR ω j := by
    have h := (hγ ω).isLocCont.isForcePathBefore (xR ω j) fun t ht0 ht => by
      have := (hγ ω).kcW_lt_kcVRr (hxR ω) ht0 ht j
      rwa [← kcPath_coe] at this
    simp only [kcPath_coe] at h
    exact h
  antiL ω i a ha b hb hab := by
    have := (hγ ω).isLocCont.neg.kImg_mono_time hb hab (-xL ω i)
    show -kImg _ _ _ ≤ -kImg _ _ _
    linarith
  monoR ω j a ha b hb hab := (hγ ω).isLocCont.kImg_mono_time hb hab (xR ω j)
  idxL ω t ht a b hab := by
    have := (hγ ω).isLocCont.neg.kImg_mono_index ht (neg_le_neg (hxLa ω hab))
    show -kImg _ _ _ ≤ -kImg _ _ _
    linarith
  idxR ω t ht a b hab := (hγ ω).isLocCont.kImg_mono_index ht (hxRm ω hab)
  mergeL ω i j s t hst ht heq := by
    have heq' : kImg (fun r => -kcPath (γ ω) (P ω) r) (-xL ω i) s =
        kImg (fun r => -kcPath (γ ω) (P ω) r) (-xL ω j) s := neg_inj.1 heq
    show -kImg _ _ _ = -kImg _ _ _
    rw [(hγ ω).isLocCont.neg.kImg_merge hst ht heq']
  mergeR ω i j s t hst ht heq := (hγ ω).isLocCont.kImg_merge hst ht heq
  sepL ω t ht0 ht i := (hγ ω).kcVLr_lt_kcW (hxL ω) ht0 ht i
  sepR ω t ht0 ht j := (hγ ω).kcW_lt_kcVRr (hxR ω) ht0 ht j

/-- **The killed word of a family of killed curves**, with the marks set to `0` after the killing. -/
theorem isKilledWord_kc {Ω : Type*} {nL nR : ℕ} {γ : Ω → ℝ → ℂ} {P : Ω → Set ℝ}
    (hγ : ∀ ω, IsKilledCurve (γ ω) (P ω)) {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
    (hxL : ∀ ω i, xL ω i ≤ 0) (hxR : ∀ ω j, 0 ≤ xR ω j) (hxLa : ∀ ω, Antitone (xL ω))
    (hxRm : ∀ ω, Monotone (xR ω)) :
    WangWu.ImgDrv.IsKilledWord (fun t ω => kcW (γ ω) (P ω) t) (fun i t ω => kcVL (γ ω) (P ω) (xL ω) i t)
      (fun j t ω => kcVR (γ ω) (P ω) (xR ω) j t) (fun ω => kcLife (γ ω) (P ω)) :=
  (isKilledWord_kcr hγ hxL hxR hxLa hxRm).congr_marks (fun ω i _ ht => kcVL_of_lt (xL ω) i ht)
    fun ω j _ ht => kcVR_of_lt (xR ω) j ht

end InteractingSLE.Sec5.CrossRestart.KernelQ
