import InteractingSLE.Spec.Sec2.OneForceLip
import Mathlib.Analysis.ODE.Gronwall

/-!
# The real Loewner flow of a continuous driver

Packet PROVE-SEC2-MART2 (step R3 of `planning/handoffs/PROVE-SEC2-MART.md`). Specification §2.3,
paragraph before Theorem 2.4 and the paragraph "Geometric force endpoints" (`source/spec/p001-048.md`,
L815, L940–L951): the images of real points under the Loewner flow of a continuous driver `w`.

For `y` with `y > w 0`, the centred real flow `X = g(y) − w` solves `X_t = y − w_t + ∫₀ᵗ 2/X_s ds` while
`X > 0`. Solutions are built from PROVE-SEC2-ONE's global Lipschitz solutions `OneForce.lipSol` for the
regularized drift `2/max(X, ε)` (`regFlow`). A point is *alive* at `t` if a positive solution exists on
`[0, t]` (`Alive`); `cflow w y t` is its value and `gImg w y t = w t + cflow w y t` the image `g_t(y)`.

## Main results

* `isPosSol_unique`, `cflow_eq_of_isPosSol`: positive solutions are unique;
* `Alive.of_le`: the alive points form an up-set; `alive_of_forall_lt`: points above the driver are
  alive;
* `cflow_lt_of_lt`, `cflow_sub_le_of_lt`: the flow preserves the order of alive points and is
  `1`-Lipschitz (`(g(y') − g(y))' = −2(g(y') − g(y))/(X X') ≤ 0`);
* `gImg_mono`, `hasDerivAt_gImg`: `g_t(y)` is non-decreasing with `∂ₜ g = 2/(g − w)`;
* `Alive.of_forall_le_cflow`: a point stays alive as long as its centred flow is bounded below.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace MartChar

namespace RealFlow

/-! ### A backward Grönwall inequality -/

/-- If `|D'| ≤ K |D|` on `(0, t]`, then `|D 0| ≤ |D t| e^{K t}`. -/
lemma abs_le_abs_mul_exp_of_hasDerivAt {D d : ℝ → ℝ} {K t : ℝ} (ht : 0 ≤ t)
    (hDc : ContinuousOn D (Icc 0 t)) (hD : ∀ u ∈ Ioc 0 t, HasDerivAt D (d u) u)
    (hb : ∀ u ∈ Ioc 0 t, |d u| ≤ K * |D u|) : |D 0| ≤ |D t| * Real.exp (K * t) := by
  set f : ℝ → ℝ := fun s => D (t - s) with hf
  have hfc : ContinuousOn f (Icc 0 t) := by
    refine hDc.comp (continuous_const.sub continuous_id).continuousOn fun s hs => ?_
    exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hfd : ∀ s ∈ Ico (0 : ℝ) t, HasDerivWithinAt f (-d (t - s)) (Ici s) s := fun s hs => by
    have hu : t - s ∈ Ioc 0 t := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have := (hD (t - s) hu).comp_const_sub t s
    exact this.hasDerivWithinAt
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le (f := f) (f' := fun s => -d (t - s))
    (δ := |D t|) (K := K) (ε := 0) hfc hfd (by simp [hf]) (fun s hs => by
      have hu : t - s ∈ Ioc 0 t := ⟨by linarith [hs.2], by linarith [hs.1]⟩
      simp only [Real.norm_eq_abs, abs_neg, add_zero, hf]
      exact hb _ hu) t ⟨ht, le_rfl⟩
  rw [gronwallBound_ε0, sub_zero] at hg
  simpa [hf, Real.norm_eq_abs] using hg

/-! ### The regularized flow -/

variable {w : ℝ → ℝ}

/-- The regularized centred Loewner flow from `y`: `X = y − w + ∫ 2/max(X, ε)`. -/
def regFlow (w : ℝ → ℝ) (ε y : ℝ) : ℝ → ℝ :=
  OneForce.lipSol (Bessel.regDrift 2 ε) y (fun t => -w t)

lemma lipData_regDrift_two (hw : Continuous w) {ε : ℝ} (hε : 0 < ε) :
    OneForce.LipData (Bessel.regDrift 2 ε) (fun t => -w t) :=
  ⟨⟨_, Bessel.lipschitzWith_regDrift zero_le_two hε⟩,
    ⟨2 / ε, fun y => Bessel.abs_regDrift_le zero_le_two hε y⟩, hw.neg⟩

lemma regFlow_eq (hw : Continuous w) {ε : ℝ} (hε : 0 < ε) (y : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    regFlow w ε y t = y + -w t + ∫ s in (0 : ℝ)..t, Bessel.regDrift 2 ε (regFlow w ε y s) :=
  OneForce.lipSol_eq (lipData_regDrift_two hw hε) y ht

lemma continuousOn_regFlow (hw : Continuous w) {ε : ℝ} (hε : 0 < ε) (y : ℝ) :
    ContinuousOn (regFlow w ε y) (Ici 0) :=
  OneForce.continuousOn_lipSol_Ici (lipData_regDrift_two hw hε) y

/-- The difference of two regularized flows is differentiable at positive times. -/
lemma hasDerivAt_regFlow_sub (hw : Continuous w) {ε : ℝ} (hε : 0 < ε) (y y' : ℝ) {u : ℝ}
    (hu : 0 < u) :
    HasDerivAt (fun s => regFlow w ε y' s - regFlow w ε y s)
      (Bessel.regDrift 2 ε (regFlow w ε y' u) - Bessel.regDrift 2 ε (regFlow w ε y u)) u := by
  have h := lipData_regDrift_two hw hε
  have hmem : Icc (0 : ℝ) (u + 1) ∈ 𝓝 u := Icc_mem_nhds hu (by linarith)
  have h1 := (OneForce.lipUnc_hasDerivWithinAt h (T := u + 1) (by linarith) y' u
    ⟨hu.le, by linarith⟩).hasDerivAt hmem
  have h2 := (OneForce.lipUnc_hasDerivWithinAt h (T := u + 1) (by linarith) y u
    ⟨hu.le, by linarith⟩).hasDerivAt hmem
  have heq : (fun s => regFlow w ε y' s - regFlow w ε y s)
      = fun s => OneForce.lipUnc (Bessel.regDrift 2 ε) y' (fun t => -w t) s
        - OneForce.lipUnc (Bessel.regDrift 2 ε) y (fun t => -w t) s := by
    funext s
    simp only [regFlow, OneForce.lipSol]
    ring
  rw [heq]
  exact h1.sub h2

/-- **The regularized flow preserves strict order.** -/
lemma regFlow_lt_regFlow (hw : Continuous w) {ε : ℝ} (hε : 0 < ε) {y y' : ℝ} (hyy : y < y')
    {t : ℝ} (ht : 0 ≤ t) : regFlow w ε y t < regFlow w ε y' t := by
  set D : ℝ → ℝ := fun s => regFlow w ε y' s - regFlow w ε y s with hD
  have hDc : ContinuousOn D (Icc 0 t) :=
    ((continuousOn_regFlow hw hε y').sub (continuousOn_regFlow hw hε y)).mono
      fun s hs => hs.1
  have hD0 : D 0 = y' - y := by
    simp only [hD, regFlow_eq hw hε _ le_rfl, intervalIntegral.integral_same]
    ring
  have hne : ∀ s ∈ Icc 0 t, D s ≠ 0 := fun s hs h0 => by
    have hb := abs_le_abs_mul_exp_of_hasDerivAt (D := D) (K := 2 / ε ^ 2) hs.1
      (hDc.mono (Icc_subset_Icc_right hs.2))
      (fun u hu => hasDerivAt_regFlow_sub hw hε y y' hu.1) (fun u _ => by
        have hL := (Bessel.lipschitzWith_regDrift zero_le_two hε).dist_le_mul
          (regFlow w ε y' u) (regFlow w ε y u)
        rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)] at hL
        simpa [hD] using hL)
    rw [h0, abs_zero, zero_mul, hD0] at hb
    have : 0 < |y' - y| := abs_pos.2 (sub_ne_zero.2 hyy.ne')
    linarith
  by_contra hle
  push Not at hle
  have hDt : D t ≤ 0 := by simp only [hD]; linarith
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' ht hDc ⟨hDt, by rw [hD0]; linarith⟩
  exact hne s hs hs0

/-! ### Positive solutions and alive points -/

/-- A positive solution of the centred real Loewner equation from `y` on `[0, t]`. -/
def IsPosSol (w : ℝ → ℝ) (y t : ℝ) (X : ℝ → ℝ) : Prop :=
  ContinuousOn X (Icc 0 t) ∧ ∀ s ∈ Icc 0 t, 0 < X s ∧ X s = y - w s + ∫ r in (0 : ℝ)..s, 2 / X r

/-- `y` is not swallowed by time `t`: a positive solution exists on `[0, t]`. -/
def Alive (w : ℝ → ℝ) (y t : ℝ) : Prop := ∃ X, IsPosSol w y t X

lemma IsPosSol.mono {y t s : ℝ} {X : ℝ → ℝ} (hX : IsPosSol w y t X) (hst : s ≤ t) :
    IsPosSol w y s X :=
  ⟨hX.1.mono (Icc_subset_Icc_right hst), fun r hr => hX.2 r ⟨hr.1, hr.2.trans hst⟩⟩

lemma IsPosSol.exists_pos_le {y t : ℝ} {X : ℝ → ℝ} (hX : IsPosSol w y t X) (ht : 0 ≤ t) :
    ∃ ε > 0, ∀ s ∈ Icc 0 t, ε ≤ X s := by
  obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 ht) hX.1
  exact ⟨X s₀, (hX.2 s₀ hs₀).1, fun s hs => hmin hs⟩

/-- A positive solution bounded below by `ε` is the regularized flow. -/
lemma IsPosSol.eqOn_regFlow (hw : Continuous w) {ε y t : ℝ} (hε : 0 < ε) {X : ℝ → ℝ}
    (hX : IsPosSol w y t X) (ht : 0 ≤ t) (hεX : ∀ s ∈ Icc 0 t, ε ≤ X s) :
    EqOn (regFlow w ε y) X (Icc 0 t) := by
  refine OneForce.eqOn_lipSol (lipData_regDrift_two hw hε) ht hX.1 fun s hs => ?_
  rw [(hX.2 s hs).2]
  have : ∫ r in (0 : ℝ)..s, 2 / X r = ∫ r in (0 : ℝ)..s, Bessel.regDrift 2 ε (X r) := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hs.1] at hr
    exact (Bessel.regDrift_of_le (hεX r ⟨hr.1, hr.2.trans hs.2⟩)).symm
  rw [this]
  ring

/-- The regularized flow is a positive solution while it stays above `ε`. -/
lemma isPosSol_regFlow (hw : Continuous w) {ε y t : ℝ} (hε : 0 < ε)
    (h : ∀ s ∈ Icc 0 t, ε ≤ regFlow w ε y s) : IsPosSol w y t (regFlow w ε y) := by
  refine ⟨(continuousOn_regFlow hw hε y).mono fun s hs => hs.1, fun s hs =>
    ⟨hε.trans_le (h s hs), ?_⟩⟩
  rw [regFlow_eq hw hε y hs.1]
  have : ∫ r in (0 : ℝ)..s, Bessel.regDrift 2 ε (regFlow w ε y r)
      = ∫ r in (0 : ℝ)..s, 2 / regFlow w ε y r := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hs.1] at hr
    exact Bessel.regDrift_of_le (h r ⟨hr.1, hr.2.trans hs.2⟩)
  rw [this]
  ring

/-- **Uniqueness of positive solutions.** -/
lemma isPosSol_unique (hw : Continuous w) {y t : ℝ} {X X' : ℝ → ℝ} (hX : IsPosSol w y t X)
    (hX' : IsPosSol w y t X') (ht : 0 ≤ t) : EqOn X X' (Icc 0 t) := by
  obtain ⟨ε, hε, hεX⟩ := hX.exists_pos_le ht
  obtain ⟨ε', hε', hεX'⟩ := hX'.exists_pos_le ht
  have h1 := hX.eqOn_regFlow hw (lt_min hε hε') ht fun s hs => (min_le_left _ _).trans (hεX s hs)
  have h2 := hX'.eqOn_regFlow hw (lt_min hε hε') ht fun s hs =>
    (min_le_right _ _).trans (hεX' s hs)
  exact fun s hs => (h1 hs).symm.trans (h2 hs)

lemma Alive.mono {y t s : ℝ} (h : Alive w y t) (hst : s ≤ t) : Alive w y s :=
  ⟨h.choose, h.choose_spec.mono hst⟩

/-- Alive points, through the regularized flows with `ε = 1/(n+1)`. -/
lemma alive_iff_regFlow (hw : Continuous w) {y t : ℝ} (ht : 0 ≤ t) :
    Alive w y t ↔ ∃ n : ℕ, ∀ s ∈ Icc 0 t,
      1 / ((n : ℝ) + 1) ≤ regFlow w (1 / ((n : ℝ) + 1)) y s := by
  constructor
  · rintro ⟨X, hX⟩
    obtain ⟨ε, hε, hεX⟩ := hX.exists_pos_le ht
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have heq := hX.eqOn_regFlow hw hpos ht fun s hs => hn.le.trans (hεX s hs)
    exact ⟨n, fun s hs => by rw [heq hs]; exact hn.le.trans (hεX s hs)⟩
  · rintro ⟨n, hn⟩
    exact ⟨_, isPosSol_regFlow hw (by positivity) hn⟩

open Classical in
/-- The centred flow `X_t = g_t(y) − w_t` of an alive point (junk `0` otherwise). -/
def cflow (w : ℝ → ℝ) (y t : ℝ) : ℝ := if h : Alive w y t then h.choose t else 0

/-- The flow of an alive point is the value of any positive solution. -/
lemma cflow_eq_of_isPosSol (hw : Continuous w) {y t s : ℝ} {X : ℝ → ℝ} (hX : IsPosSol w y t X)
    (hs : s ∈ Icc 0 t) : cflow w y s = X s := by
  classical
  have hA : Alive w y s := ⟨X, hX.mono hs.2⟩
  rw [cflow, dite_eq_left_of_eq_true (eq_true hA)]
  exact isPosSol_unique hw hA.choose_spec (hX.mono hs.2) hs.1 ⟨hs.1, le_rfl⟩

lemma Alive.isPosSol (hw : Continuous w) {y t : ℝ} (h : Alive w y t) :
    IsPosSol w y t (cflow w y) := by
  obtain ⟨X, hX⟩ := h
  have heq : EqOn (cflow w y) X (Icc 0 t) := fun s hs => cflow_eq_of_isPosSol hw hX hs
  refine ⟨hX.1.congr heq, fun s hs => ?_⟩
  rw [heq hs]
  refine ⟨(hX.2 s hs).1, ?_⟩
  rw [(hX.2 s hs).2]
  congr 1
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le hs.1] at hr
  rw [heq ⟨hr.1, hr.2.trans hs.2⟩]

lemma Alive.cflow_pos (hw : Continuous w) {y t s : ℝ} (h : Alive w y t) (hs : s ∈ Icc 0 t) :
    0 < cflow w y s :=
  ((h.isPosSol hw).2 s hs).1

/-- The regularized flow is the centred flow while it stays above `ε`. -/
lemma cflow_eq_regFlow (hw : Continuous w) {ε y t s : ℝ} (hε : 0 < ε)
    (h : ∀ r ∈ Icc 0 t, ε ≤ regFlow w ε y r) (hs : s ∈ Icc 0 t) :
    cflow w y s = regFlow w ε y s :=
  cflow_eq_of_isPosSol hw (isPosSol_regFlow hw hε h) hs

/-- **Alive points form an up-set.** -/
lemma Alive.of_le (hw : Continuous w) {y y' t : ℝ} (h : Alive w y t) (hyy : y ≤ y')
    (ht : 0 ≤ t) : Alive w y' t := by
  rcases hyy.eq_or_lt with rfl | hlt
  · exact h
  obtain ⟨n, hn⟩ := (alive_iff_regFlow hw ht).1 h
  refine (alive_iff_regFlow hw ht).2 ⟨n, fun s hs => ?_⟩
  exact (hn s hs).trans (regFlow_lt_regFlow hw (by positivity) hlt hs.1).le

/-- **Points above the driver are alive.** -/
lemma alive_of_forall_lt (hw : Continuous w) {y t : ℝ} (ht : 0 ≤ t)
    (h : ∀ s ∈ Icc 0 t, w s < y) : Alive w y t := by
  obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 ht)
    (continuous_const.sub hw).continuousOn (f := fun s => y - w s)
  set m := y - w s₀ with hm
  have hm0 : 0 < m := by have := h s₀ hs₀; linarith
  refine ⟨_, isPosSol_regFlow hw hm0 fun s hs => ?_⟩
  rw [regFlow_eq hw hm0 y hs.1]
  have hI : 0 ≤ ∫ r in (0 : ℝ)..s, Bessel.regDrift 2 m (regFlow w m y r) :=
    intervalIntegral.integral_nonneg hs.1 fun r _ => Bessel.regDrift_nonneg zero_le_two hm0 _
  have := hmin hs
  simp only [mem_ofPred_eq] at this
  linarith

/-! ### Order, the `1`-Lipschitz property, and the uncentred image -/

/-- **Order and contraction.** For alive `y < y'`, `0 < X^{y'} − X^{y} ≤ y' − y` on `[0, t]`. -/
lemma cflow_lt_and_sub_le (hw : Continuous w) {y y' t : ℝ} (h : Alive w y t) (hyy : y < y')
    (ht : 0 ≤ t) {s : ℝ} (hs : s ∈ Icc 0 t) :
    cflow w y s < cflow w y' s ∧ cflow w y' s - cflow w y s ≤ y' - y := by
  obtain ⟨n, hn⟩ := (alive_iff_regFlow hw ht).1 h
  set ε : ℝ := 1 / ((n : ℝ) + 1) with hε
  have hε0 : 0 < ε := by positivity
  have hlt : ∀ r ∈ Icc 0 t, regFlow w ε y r < regFlow w ε y' r := fun r hr =>
    regFlow_lt_regFlow hw hε0 hyy hr.1
  have hn' : ∀ r ∈ Icc 0 t, ε ≤ regFlow w ε y' r := fun r hr => (hn r hr).trans (hlt r hr).le
  rw [cflow_eq_regFlow hw hε0 hn hs, cflow_eq_regFlow hw hε0 hn' hs]
  refine ⟨hlt s hs, ?_⟩
  set D : ℝ → ℝ := fun r => regFlow w ε y' r - regFlow w ε y r with hD
  have hDc : ContinuousOn D (Icc 0 t) :=
    ((continuousOn_regFlow hw hε0 y').sub (continuousOn_regFlow hw hε0 y)).mono
      fun r hr => hr.1
  have hanti : AntitoneOn D (Icc 0 t) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 t) hDc
      (f' := fun u => Bessel.regDrift 2 ε (regFlow w ε y' u) - Bessel.regDrift 2 ε (regFlow w ε y u))
      (fun u hu => ?_)
      (fun u hu => ?_)
    · rw [interior_Icc] at hu
      exact (hasDerivAt_regFlow_sub hw hε0 y y' hu.1).hasDerivWithinAt
    · rw [interior_Icc] at hu
      have hu' : u ∈ Icc 0 t := Ioo_subset_Icc_self hu
      rw [Bessel.regDrift_of_le (hn' u hu'), Bessel.regDrift_of_le (hn u hu')]
      have h1 := hε0.trans_le (hn u hu')
      have h2 := hlt u hu'
      rw [sub_nonpos]
      exact div_le_div_of_nonneg_left zero_le_two h1 h2.le
  have h0 : D 0 = y' - y := by
    simp only [hD, regFlow_eq hw hε0 _ le_rfl, intervalIntegral.integral_same]
    ring
  have := hanti ⟨le_rfl, ht⟩ hs hs.1
  simp only [hD] at this h0
  linarith

/-- The image `g_t(y) = w_t + X_t` of an alive point. -/
def gImg (w : ℝ → ℝ) (y t : ℝ) : ℝ := w t + cflow w y t

lemma Alive.gImg_eq (hw : Continuous w) {y t s : ℝ} (h : Alive w y t) (hs : s ∈ Icc 0 t) :
    gImg w y s = y + ∫ r in (0 : ℝ)..s, 2 / cflow w y r := by
  rw [gImg, ((h.isPosSol hw).2 s hs).2]
  ring

lemma Alive.lt_gImg (hw : Continuous w) {y t s : ℝ} (h : Alive w y t) (hs : s ∈ Icc 0 t) :
    w s < gImg w y s := by
  have := h.cflow_pos hw hs
  rw [gImg]
  linarith

lemma Alive.continuousOn_inv (hw : Continuous w) {y t : ℝ} (h : Alive w y t) :
    ContinuousOn (fun r => 2 / cflow w y r) (Icc 0 t) :=
  continuousOn_const.div (h.isPosSol hw).1 fun _r hr => (h.cflow_pos hw hr).ne'

/-- `g(y)` is non-decreasing in time. -/
lemma Alive.gImg_mono (hw : Continuous w) {y t s s' : ℝ} (h : Alive w y t) (hs : 0 ≤ s)
    (hss : s ≤ s') (hst : s' ≤ t) : gImg w y s ≤ gImg w y s' := by
  rw [h.gImg_eq hw ⟨hs, hss.trans hst⟩, h.gImg_eq hw ⟨hs.trans hss, hst⟩]
  have hint : IntervalIntegrable (fun r => 2 / cflow w y r) volume 0 t :=
    (h.continuousOn_inv hw).intervalIntegrable_of_Icc (hs.trans (hss.trans hst))
  have hsub1 : uIcc (0 : ℝ) s ⊆ uIcc 0 t := by
    rw [uIcc_of_le hs, uIcc_of_le (hs.trans (hss.trans hst))]
    exact Icc_subset_Icc_right (hss.trans hst)
  have hsub2 : uIcc s s' ⊆ uIcc 0 t := by
    rw [uIcc_of_le hss, uIcc_of_le (hs.trans (hss.trans hst))]
    exact Icc_subset_Icc hs hst
  have h1 : IntervalIntegrable (fun r => 2 / cflow w y r) volume 0 s := hint.mono_set hsub1
  have h2 : IntervalIntegrable (fun r => 2 / cflow w y r) volume s s' := hint.mono_set hsub2
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have : 0 ≤ ∫ r in s..s', 2 / cflow w y r := intervalIntegral.integral_nonneg hss fun _r hr =>
    (div_pos two_pos (h.cflow_pos hw ⟨hs.trans hr.1, hr.2.trans hst⟩)).le
  linarith

/-- **The Loewner equation** `∂ₜ g_t(y) = 2/(g_t(y) − w_t)` at interior times. -/
lemma Alive.hasDerivAt_gImg (hw : Continuous w) {y T u : ℝ} (h : Alive w y T) (hu : u ∈ Ioo 0 T) :
    HasDerivAt (fun s => gImg w y s) (2 / cflow w y u) u := by
  have hmem : Icc 0 T ∈ 𝓝 u := Icc_mem_nhds hu.1 hu.2
  have hcont : ContinuousAt (fun r => 2 / cflow w y r) u :=
    (h.continuousOn_inv hw).continuousAt hmem
  have hint : IntervalIntegrable (fun r => 2 / cflow w y r) volume 0 u :=
    ((h.continuousOn_inv hw).mono (Icc_subset_Icc_right hu.2.le)).intervalIntegrable_of_Icc hu.1.le
  have hmeas : StronglyMeasurableAtFilter (fun r => 2 / cflow w y r) (𝓝 u) volume :=
    (h.continuousOn_inv hw).stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc u
      |>.filter_mono (by rw [nhdsWithin_eq_nhds.2 hmem])
  have hd := (intervalIntegral.integral_hasDerivAt_right hint hmeas hcont).const_add y
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [hmem] with s hs
  exact h.gImg_eq hw hs

/-- **Continuation.** A point alive at `s` whose centred flow stays `≥ c > 0` at every later time
`u ≤ t` at which it is alive is alive at `t`. -/
lemma Alive.of_forall_le_cflow (hw : Continuous w) {y s t c : ℝ} (h : Alive w y s) (hs : 0 ≤ s)
    (hc : 0 < c) (hbound : ∀ u ∈ Icc s t, Alive w y u → c ≤ cflow w y u) :
    Alive w y t := by
  obtain ⟨n, hn⟩ := (alive_iff_regFlow hw hs).1 h
  set ε : ℝ := min (1 / ((n : ℝ) + 1)) (c / 2) with hεdef
  have hε : 0 < ε := lt_min (by positivity) (by linarith)
  have hεc : ε < c := (min_le_right _ _).trans_lt (by linarith)
  set X := regFlow w ε y with hX
  have hXc : ContinuousOn X (Ici 0) := continuousOn_regFlow hw hε y
  -- on `[0, s]` the regularized flow is the centred flow
  have hpos_s : IsPosSol w y s (cflow w y) := h.isPosSol hw
  have hcs : ∀ r ∈ Icc 0 s, ε ≤ cflow w y r := fun r hr => by
    rw [cflow_eq_regFlow hw (by positivity) hn hr]
    exact (min_le_left _ _).trans (hn r hr)
  have hXs : ∀ r ∈ Icc 0 s, ε ≤ X r := fun r hr => by
    rw [hX, hpos_s.eqOn_regFlow hw hε hs hcs hr]
    exact hcs r hr
  suffices hall : ∀ r ∈ Icc 0 t, ε ≤ X r from ⟨_, isPosSol_regFlow hw hε hall⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨b₀, hb₀, hb₀X⟩ := hcon
  set B := {r | r ∈ Icc 0 t ∧ X r < ε} with hB
  have hBne : B.Nonempty := ⟨b₀, hb₀, hb₀X⟩
  have hBbdd : BddBelow B := ⟨0, fun r hr => hr.1.1⟩
  set τ := sInf B with hτ
  have hBs : ∀ b ∈ B, s < b := fun b hb => by
    by_contra hle
    push Not at hle
    exact absurd (hXs b ⟨hb.1.1, hle⟩) (not_le.2 hb.2)
  have hsτ : s ≤ τ := le_csInf hBne fun b hb => (hBs b hb).le
  have hτt : τ ≤ t := (csInf_le hBbdd ⟨hb₀, hb₀X⟩).trans hb₀.2
  have hbelow : ∀ r ∈ Icc 0 τ, r < τ → ε ≤ X r := fun r hr hrτ => by
    by_contra hlt
    push Not at hlt
    exact absurd (csInf_le hBbdd ⟨⟨hr.1, hr.2.trans hτt⟩, hlt⟩) (not_le.2 hrτ)
  have hXτ : ε ≤ X τ := by
    rcases hsτ.eq_or_lt with heq | hlt
    · rw [← heq]; exact hXs s ⟨hs, le_rfl⟩
    · have hcw : ContinuousWithinAt X (Ioo s τ) τ :=
        (hXc τ (hs.trans hsτ)).mono fun r hr => (hs.trans hr.1.le)
      have : NeBot (𝓝[Ioo s τ] τ) := by
        rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo hlt.ne]
        exact ⟨hlt.le, le_rfl⟩
      exact ge_of_tendsto hcw (eventually_nhdsWithin_of_forall fun r hr =>
        hbelow r ⟨hs.trans hr.1.le, hr.2.le⟩ hr.2)
  have hall_τ : ∀ r ∈ Icc 0 τ, ε ≤ X r := fun r hr => by
    rcases hr.2.lt_or_eq with hlt | heq
    · exact hbelow r hr hlt
    · rw [heq]; exact hXτ
  have hAτ : Alive w y τ := ⟨_, isPosSol_regFlow hw hε hall_τ⟩
  have hcτ : c ≤ X τ := by
    rw [hX, ← cflow_eq_regFlow hw hε hall_τ ⟨hs.trans hsτ, le_rfl⟩]
    exact hbound τ ⟨hsτ, hτt⟩ hAτ
  -- `X > ε` just after `τ`, contradicting `τ = inf B`
  have hev : ∀ᶠ r in 𝓝[≥] τ, ε < X r := by
    have hcw : ContinuousWithinAt X (Ici τ) τ :=
      (hXc τ (hs.trans hsτ)).mono fun r hr => (hs.trans hsτ).trans hr
    exact hcw (lt_mem_nhds (hεc.trans_le hcτ))
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhdsWithin_iff.1 hev
  obtain ⟨b, hbB, hbτ⟩ := exists_lt_of_csInf_lt hBne (show τ < τ + δ by linarith)
  have hτb : τ ≤ b := csInf_le hBbdd hbB
  have hball : b ∈ Metric.ball τ δ ∩ Ici τ := by
    refine ⟨?_, hτb⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith)]
    linarith
  have : ε < X b := hsub hball
  exact absurd hbB.2 (not_lt.2 this.le)

end RealFlow

end MartChar

end InteractingSLE
