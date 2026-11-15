/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.CriticalAux
import InteractingSLE.Stochastic.LocalTime.Stopped

/-!
# The critical case of Aux. lemma 3: the localized path

Packet PROVE-SEC2-TERM2. Specification pp. 27–28 (`source/spec/p001-048.md` L612–L648). Fix a
path of Definition 2.1 with left side total `∑ ρ^{i,L} = −2`, outermost left index `o`, and put
`Q = W − V^out`. By (N4), `Q = √κ b + gapAffine(V)` before the lifetime, where `gapAffine` is an
affine function of the force coordinates only (`gap_eq_gapAffine`). Replacing the force coordinates
by their extensions through the lifetime (`lowerExtPath`, `upperExtPath`) gives `gapExt`, which
is defined at every time and continuous up to and including a finite lifetime at which the force
coordinates stay bounded.

The localization of the source ("stop on reaching `Q ≥ M`, `|b| ≥ C`, or time `q + H`; in
addition stop at `Q ≤ ε` and at `σ_n ∨ q`") is the predicate `CritAlive`: before the lifetime, at
every rational time of `[q, u]`, `ε < Q < M`, `V^out > −n`, every right coordinate is `< n`, and
the driver is at distance `> 1` from every right force point (so the right drift `b^R` of (N5) is
bounded by `∑ |ρ^{j,R}|`). The lower bound `V^out > −n` replaces the announcing sequence `σ_n`:
a critical escape drives `V^out` to `−∞`, so it is stopped strictly before the lifetime, while the
paths that stay alive up to the lifetime have bounded coordinates and use the extension.

Main results, for the lifetime `ρ` of `CritAlive` on `[q, t]` (`q` a rational time):

* `isTanakaPath_crit`: the clamped extended gap satisfies on `[q, ρ]` the pathwise hypotheses
  `IsTanakaPath` of the expectation-form Itô formula, with drift `μ_Q = gapOutDrift` and the
  deterministic bound `critBound`;
* `integral_xlogxReg'_mul_ge`: the bound
  `∫_q^ρ F'(X) μ_Q ≥ −(K₁ + (κ/4) ∫_q^ρ F''(X) + C' (t − q))` of (N7)–(N8), with `K₁, C'`
  independent of `ε` and `n` (`critK₁`, `critC'`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology InteractingSLE.LocalTime
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

/-- The affine part of (N4) in the critical case (Specification p. 26):
`Q = √κ b − ½ ∑ ρ^{i,L} Δᵢ + ½ ∑ ρ^{i,L} x^{i,L} − ½ ∑ ρ^{j,R} (V^{j,R} − x^{j,R})`. -/
def gapAffine {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (o : Fin nL) (vl : Fin nL → ℝ) (vr : Fin nR → ℝ) : ℝ :=
  -(1 / 2) * (∑ i, ρL i * (vl i - vl o)) + (1 / 2) * (∑ i, ρL i * xL i)
    - (1 / 2) * (∑ j, ρR j * (vr j - xR j))

/-- The gap `Q = W − V^out` through (N4), with the force coordinates extended through the
lifetime. -/
def gapExt (a : ℝ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) (o : Fin nL) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ)
    (b : ℝ≥0 → ℝ) (ζ₀ : ℝ≥0∞) (u : ℝ≥0) : ℝ :=
  Real.sqrt a * b u + gapAffine xL xR ρL ρR o (fun i => lowerExtPath ζ₀ (vL i) (xL i) u)
    (fun j => upperExtPath ζ₀ (vR j) (xR j) u)

/-- The localization of the critical case: alive at `u` if `u < q`, or if `u` is before the
lifetime and at every rational time `r ∈ [q, u]`: `ε < Q_r < M`, `V^out_r > −n`, and for every
right index `V^{j,R}_r < n` and `W_r < V^{j,R}_r − 1` (with `W = Q + V^out`). -/
def CritAlive {nR : ℕ} (q : ℝ≥0) (ζ₀ : ℝ≥0∞) (ε M : ℝ) (n : ℕ) (Qb vo : ℝ≥0 → ℝ)
    (vr : Fin nR → ℝ≥0 → ℝ) (u : ℝ≥0) : Prop :=
  u < q ∨ ((u : ℝ≥0∞) < ζ₀ ∧ ∀ r : ℚ, q ≤ ratTime r → ratTime r ≤ u →
    ε < Qb (ratTime r) ∧ Qb (ratTime r) < M ∧ -(n : ℝ) < vo (ratTime r) ∧
      ∀ j, vr j (ratTime r) < n ∧ Qb (ratTime r) + vo (ratTime r) < vr j (ratTime r) - 1)

theorem CritAlive.anti {nR : ℕ} {q : ℝ≥0} {ζ₀ : ℝ≥0∞} {ε M : ℝ} {n : ℕ} {Qb vo : ℝ≥0 → ℝ}
    {vr : Fin nR → ℝ≥0 → ℝ} :
    ∀ u v : ℝ≥0, u ≤ v → CritAlive q ζ₀ ε M n Qb vo vr v → CritAlive q ζ₀ ε M n Qb vo vr u := by
  intro u v huv hv
  by_cases huq : u < q
  · exact Or.inl huq
  · rcases hv with hvq | ⟨hvζ, hv⟩
    · exact absurd (lt_of_le_of_lt huv hvq) huq
    · exact Or.inr ⟨lt_of_le_of_lt (by exact_mod_cast huv) hvζ,
        fun r hr1 hr2 => hv r hr1 (hr2.trans huv)⟩

/-- The deterministic bound `N` of the Tanaka hypotheses: `M + ∑ |ρ^{i,L}| |x^{i,L} − x^{out}|/2
+ (∑ |ρ^{j,R}|) H`. -/
def critBound {nL nR : ℕ} (xL : Fin nL → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (o : Fin nL)
    (M H : ℝ) : ℝ :=
  M + (∑ i, |ρL i| * (|xL i - xL o| / 2)) + (∑ j, |ρR j|) * H

/-- The spread constant `K₁ = ½ ∑ |ρ^{i,L}| ((1 + log M) |x^{i,L} − x^{out}| + 1)` of (N7). -/
def critK₁ {nL : ℕ} (xL : Fin nL → ℝ) (ρL : Fin nL → ℝ) (o : Fin nL) (M : ℝ) : ℝ :=
  ∑ i, |ρL i| * (((1 + Real.log M) * |xL i - xL o| + 1) / 2)

/-- The drift constant `C' = C (1 + log M) + 4C²/κ` of (N8), with `C = ∑ |ρ^{j,R}|`. -/
def critC' {nR : ℕ} (κ : ℝ) (ρR : Fin nR → ℝ) (M : ℝ) : ℝ :=
  (∑ j, |ρR j|) * (1 + Real.log M) + 4 * (∑ j, |ρR j|) ^ 2 / κ

/-- Integral of a finite sum plus a constant, bounded termwise. -/
theorem integral_sum_add_const_le {u v : ℝ} {m : ℕ} {f : Fin m → ℝ → ℝ}
    (hf : ∀ i, IntervalIntegrable (f i) volume u v) {B : Fin m → ℝ}
    (hB : ∀ i, ∫ x in u..v, f i x ≤ B i) (C : ℝ) :
    ∫ x in u..v, ((∑ i, f i x) + C) ≤ (∑ i, B i) + C * (v - u) := by
  have hsum : IntervalIntegrable (fun x => ∑ i, f i x) volume u v := by
    have := IntervalIntegrable.sum Finset.univ fun i _ => hf i
    rwa [Finset.sum_fn] at this
  rw [intervalIntegral.integral_add hsum intervalIntegrable_const,
    intervalIntegral.integral_finsetSum fun i _ => hf i, intervalIntegral.integral_const,
    smul_eq_mul, mul_comm (v - u)]
  have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hB i
  linarith

theorem gapOutDrift_coe_toNNReal {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (o : Fin nL) (r : ℝ) :
    gapOutDrift ρL ρR w vL vR o (r.toNNReal : ℝ) = gapOutDrift ρL ρR w vL vR o r := by
  simp only [gapOutDrift, driverDrift, Real.toNNReal_coe]

namespace IsForcePath

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ₀ : ℝ≥0∞} {o : Fin nL}

section Basic

variable (h : IsForcePath xL xR ρL ρR w vL vR ζ₀)
include h

/-- **(N4) in the critical case** (Specification p. 26): `Q = √κ b + gapAffine(V)` before `ζ`. -/
theorem gap_eq_gapAffine (hw : DriverEq a ρL ρR w vL vR b ζ₀) (hS : ∑ i, ρL i = -2)
    {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ₀) :
    w s - vL o s = Real.sqrt a * b s +
      gapAffine xL xR ρL ρR o (fun i => vL i s) (fun j => vR j s) := by
  have hN1 := h.w_eq_N1 hw hs
  have e : ∑ i, ρL i * (vL i s - xL i) =
      ∑ i, ρL i * (vL i s - vL o s) + (∑ i, ρL i) * vL o s - ∑ i, ρL i * xL i := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [gapAffine]
  rw [hN1, e, hS]
  ring

theorem lowerExtPath_vL_eq {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ₀) (i : Fin nL) :
    lowerExtPath ζ₀ (vL i) (xL i) s = vL i s :=
  lowerExtPath_eq_of_lt (h.antitoneOn_vL i) (h.continuousOn_vL i) (fun _ ht => h.vL_le_xL ht i) hs

theorem upperExtPath_vR_eq {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ₀) (j : Fin nR) :
    upperExtPath ζ₀ (vR j) (xR j) s = vR j s :=
  upperExtPath_eq_of_lt (h.monotoneOn_vR j) (h.continuousOn_vR j) (fun _ ht => h.xR_le_vR ht j) hs

/-- Before the lifetime the extended gap is `Q = W − V^out`. -/
theorem gapExt_eq (hw : DriverEq a ρL ρR w vL vR b ζ₀) (hS : ∑ i, ρL i = -2)
    {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ₀) :
    gapExt a xL xR ρL ρR o vL vR b ζ₀ s = w s - vL o s := by
  rw [h.gap_eq_gapAffine hw hS hs, gapExt]
  simp only [h.lowerExtPath_vL_eq hs, h.upperExtPath_vR_eq hs]

theorem continuousOn_lowerExtPath_vL (i : Fin nL) :
    ContinuousOn (lowerExtPath ζ₀ (vL i) (xL i)) {t | (t : ℝ≥0∞) < ζ₀} :=
  continuousOn_lowerExtPath_lt (h.antitoneOn_vL i) (h.continuousOn_vL i)
    (fun _ ht => h.vL_le_xL ht i)

theorem continuousOn_upperExtPath_vR (j : Fin nR) :
    ContinuousOn (upperExtPath ζ₀ (vR j) (xR j)) {t | (t : ℝ≥0∞) < ζ₀} :=
  continuousOn_upperExtPath_lt (h.monotoneOn_vR j) (h.continuousOn_vR j)
    (fun _ ht => h.xR_le_vR ht j)

omit h in
/-- `gapExt` is continuous on any set on which the extended coordinates are. -/
theorem continuousOn_gapExt_of {S : Set ℝ≥0} (hb : Continuous b)
    (hL : ∀ i, ContinuousOn (lowerExtPath ζ₀ (vL i) (xL i)) S)
    (hR : ∀ j, ContinuousOn (upperExtPath ζ₀ (vR j) (xR j)) S) :
    ContinuousOn (gapExt a xL xR ρL ρR o vL vR b ζ₀) S := by
  unfold gapExt gapAffine
  refine (continuousOn_const.mul hb.continuousOn).add ?_
  refine ((continuousOn_const.mul ?_).add continuousOn_const).sub (continuousOn_const.mul ?_)
  · exact continuousOn_finsetSum _ fun i _ => continuousOn_const.mul ((hL i).sub (hL o))
  · exact continuousOn_finsetSum _ fun j _ => continuousOn_const.mul ((hR j).sub continuousOn_const)

theorem continuousOn_gapExt_lt (hb : Continuous b) :
    ContinuousOn (gapExt a xL xR ρL ρR o vL vR b ζ₀) {t | (t : ℝ≥0∞) < ζ₀} :=
  continuousOn_gapExt_of hb h.continuousOn_lowerExtPath_vL h.continuousOn_upperExtPath_vR

/-- `Q > 0` before the lifetime when the left side total is `−2`: `Q = 0` would make the whole
left group collide, which is the threshold condition. -/
theorem gap_out_pos (hS : ∑ i, ρL i = -2) (ho : ∀ i, i ≤ o) {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ₀) :
    0 < w s - vL o s := by
  rcases lt_or_eq_of_le (sub_nonneg.2 (h.vL_le_w hs o)) with hlt | heq
  · exact hlt
  · exfalso
    refine h.not_threshold hs (Or.inl ?_)
    have hall : ∀ i, vL i s = w s := fun i =>
      le_antisymm (h.vL_le_w hs i) (by
        have := h.antitone_vL hs (ho i); linarith)
    rw [Finset.filter_true_of_mem fun i _ => hall i, hS]

end Basic

end IsForcePath

/-! ### The alive interval (generic) -/

namespace CritAlive

variable {nR : ℕ} {ζ₀ : ℝ≥0∞} {ε M : ℝ} {n : ℕ} {Qb vo : ℝ≥0 → ℝ} {vr : Fin nR → ℝ≥0 → ℝ}
  {q₀ : ℚ} {t : ℝ≥0}

/-- The closed form of the localization conditions. -/
def CondLe {nR : ℕ} (ε M : ℝ) (n : ℕ) (Q vo : ℝ) (vr : Fin nR → ℝ) : Prop :=
  ε ≤ Q ∧ Q ≤ M ∧ -(n : ℝ) ≤ vo ∧ ∀ j, vr j ≤ n ∧ Q + vo ≤ vr j - 1

variable (hA : CritAlive (ratTime q₀) ζ₀ ε M n Qb vo vr (ratTime q₀))
include hA

theorem lt_lifetime_of_alive : ((ratTime q₀ : ℝ≥0) : ℝ≥0∞) < ζ₀ := by
  rcases hA with h | h
  · exact absurd h (lt_irrefl _)
  · exact h.1

omit hA in
theorem lt_of_mem_Ico {u : ℝ≥0}
    (hu : u ∈ Ico (ratTime q₀) (lifetimeOf (CritAlive (ratTime q₀) ζ₀ ε M n Qb vo vr) (ratTime q₀) t)) :
    (u : ℝ≥0∞) < ζ₀ := by
  rcases of_lt_lifetimeOf CritAlive.anti hu.1 hu.2 with h | h
  · exact absurd hu.1 (not_le.2 h)
  · exact h.1

theorem lifetime_le :
    ((lifetimeOf (CritAlive (ratTime q₀) ζ₀ ε M n Qb vo vr) (ratTime q₀) t : ℝ≥0) : ℝ≥0∞) ≤ ζ₀ := by
  set ρ := lifetimeOf (CritAlive (ratTime q₀) ζ₀ ε M n Qb vo vr) (ratTime q₀) t
  by_contra hcon
  push Not at hcon
  have hne : ζ₀ ≠ ⊤ := ne_top_of_lt hcon
  set T := ζ₀.toNNReal
  have hT : (T : ℝ≥0∞) = ζ₀ := ENNReal.coe_toNNReal hne
  rw [← hT] at hcon
  have hqT : ratTime q₀ ≤ T := by
    have := hA.lt_lifetime_of_alive
    rw [← hT] at this
    exact (ENNReal.coe_lt_coe.1 this).le
  have := lt_of_mem_Ico (u := T) ⟨hqT, ENNReal.coe_lt_coe.1 hcon⟩
  rw [hT] at this
  exact lt_irrefl _ this

omit hA in
theorem cond_of_lt {r : ℚ} (hr1 : ratTime q₀ < ratTime r)
    (hr2 : ratTime r < lifetimeOf (CritAlive (ratTime q₀) ζ₀ ε M n Qb vo vr) (ratTime q₀) t) :
    ε < Qb (ratTime r) ∧ Qb (ratTime r) < M ∧ -(n : ℝ) < vo (ratTime r) ∧
      ∀ j, vr j (ratTime r) < n ∧ Qb (ratTime r) + vo (ratTime r) < vr j (ratTime r) - 1 := by
  rcases of_lt_lifetimeOf CritAlive.anti hr1.le hr2 with h | h
  · exact absurd hr1 (not_lt.2 h.le)
  · exact h.2 r hr1.le le_rfl

theorem cond_start :
    ε < Qb (ratTime q₀) ∧ Qb (ratTime q₀) < M ∧ -(n : ℝ) < vo (ratTime q₀) ∧
      ∀ j, vr j (ratTime q₀) < n ∧ Qb (ratTime q₀) + vo (ratTime q₀) < vr j (ratTime q₀) - 1 := by
  rcases hA with h | h
  · exact absurd h (lt_irrefl _)
  · exact h.2 q₀ le_rfl le_rfl

/-- The localization conditions hold in closed form at every point of `[q, ρ]` at which the
functions are continuous within `[q, ρ]`. -/
theorem condLe_of_continuousWithinAt {u : ℝ≥0}
    (hu : u ∈ Icc (ratTime q₀) (lifetimeOf (CritAlive (ratTime q₀) ζ₀ ε M n Qb vo vr) (ratTime q₀) t))
    (hQ : ContinuousWithinAt Qb (Icc (ratTime q₀)
      (lifetimeOf (CritAlive (ratTime q₀) ζ₀ ε M n Qb vo vr) (ratTime q₀) t)) u)
    (hvo : ContinuousWithinAt vo (Icc (ratTime q₀)
      (lifetimeOf (CritAlive (ratTime q₀) ζ₀ ε M n Qb vo vr) (ratTime q₀) t)) u)
    (hvr : ∀ j, ContinuousWithinAt (vr j) (Icc (ratTime q₀)
      (lifetimeOf (CritAlive (ratTime q₀) ζ₀ ε M n Qb vo vr) (ratTime q₀) t)) u) :
    CondLe ε M n (Qb u) (vo u) (fun j => vr j u) := by
  set ρ := lifetimeOf (CritAlive (ratTime q₀) ζ₀ ε M n Qb vo vr) (ratTime q₀) t
  rcases eq_or_lt_of_le (hu.1.trans hu.2) with hqρ | hqρ
  · have hu' : u = ratTime q₀ := le_antisymm (hu.2.trans hqρ.symm.le) hu.1
    subst hu'
    obtain ⟨h1, h2, h3, h4⟩ := hA.cond_start
    exact ⟨h1.le, h2.le, h3.le, fun j => ⟨(h4 j).1.le, (h4 j).2.le⟩⟩
  · have hc := fun (r : ℚ) (hr1 : ratTime q₀ < ratTime r) (hr2 : ratTime r < ρ) =>
      cond_of_lt (Qb := Qb) (vo := vo) (vr := vr) hr1 hr2
    refine ⟨?_, ?_, ?_, fun j => ⟨?_, ?_⟩⟩
    · exact (mem_of_forall_ratTime (C := Ici ε) hqρ hu hQ isClosed_Ici fun r h1 h2 =>
        (hc r h1 h2).1.le : _)
    · exact (mem_of_forall_ratTime (C := Iic M) hqρ hu hQ isClosed_Iic fun r h1 h2 =>
        (hc r h1 h2).2.1.le : _)
    · exact (mem_of_forall_ratTime (C := Ici (-(n : ℝ))) hqρ hu hvo isClosed_Ici fun r h1 h2 =>
        (hc r h1 h2).2.2.1.le : _)
    · exact (mem_of_forall_ratTime (C := Iic (n : ℝ)) hqρ hu (hvr j) isClosed_Iic fun r h1 h2 =>
        ((hc r h1 h2).2.2.2 j).1.le : _)
    · have hg : ContinuousWithinAt (fun s => Qb s + vo s - vr j s) (Icc (ratTime q₀) ρ) u :=
        (hQ.add hvo).sub (hvr j)
      have := mem_of_forall_ratTime (C := Iic (-1)) hqρ hu hg isClosed_Iic fun r h1 h2 => by
        have := ((hc r h1 h2).2.2.2 j).2
        simp only [mem_Iic]; linarith
      simp only [mem_Iic] at this
      linarith

end CritAlive

/-- A real time of `[q, u]` with `u < ρ`, as an element of `ℝ≥0` in `[q, ρ)`. -/
theorem toNNReal_mem_Ico {q u ρ : ℝ≥0} (hu : u ∈ Ico q ρ) {r : ℝ} (hr : r ∈ Icc (q : ℝ) u) :
    r.toNNReal ∈ Ico q ρ ∧ ((r.toNNReal : ℝ) = r) := by
  have hr0 : 0 ≤ r := (NNReal.coe_nonneg _).trans hr.1
  refine ⟨⟨(Real.le_toNNReal_iff_coe_le hr0).2 hr.1, ?_⟩, Real.coe_toNNReal _ hr0⟩
  exact lt_of_le_of_lt (Real.toNNReal_le_iff_le_coe.2 hr.2) hu.2

/-- A real time `u ∈ [q, ρ)` as an element of `ℝ≥0`. -/
theorem toNNReal_mem_Ico' {q ρ : ℝ≥0} {u : ℝ} (hq : (q : ℝ) ≤ u) (hρ : u < ρ) :
    u.toNNReal ∈ Ico q ρ ∧ ((u.toNNReal : ℝ) = u) := by
  have hu0 : 0 ≤ u := (NNReal.coe_nonneg _).trans hq
  refine ⟨⟨(Real.le_toNNReal_iff_coe_le hu0).2 hq, ?_⟩, Real.coe_toNNReal _ hu0⟩
  rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hu0]; exact hρ

/-- `|μ_Q| ≤ ∑ |ρ^{i,L}| δᵢ + ∑ |ρ^{j,R}|` in the critical case, when every `δᵢ ≥ 0` and
`|b^R| ≤ ∑ |ρ^{j,R}|`. -/
theorem abs_gapOutDrift_le_of {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ}
    {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {o : Fin nL} (hS : ∑ i, ρL i = -2) {r : ℝ}
    (hδ : ∀ i, 0 ≤ spreadRate w vL o i r) (hR : |rightDrift ρR w vR r| ≤ ∑ j, |ρR j|) :
    |gapOutDrift ρL ρR w vL vR o r| ≤ (∑ i, |ρL i| * spreadRate w vL o i r) + ∑ j, |ρR j| := by
  rw [gapOutDrift_eq_of_sum_eq o hS r]
  refine (abs_add_le _ _).trans (add_le_add ?_ hR)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  rw [abs_mul, abs_of_nonneg (hδ i)]

/-- The localization predicate of the critical case for a path (`CritAlive` with the extended gap,
the extended outermost left coordinate and the extended right coordinates). -/
def critAlivePath (a : ℝ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) (o : Fin nL) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ)
    (b : ℝ≥0 → ℝ) (ζ₀ : ℝ≥0∞) (q : ℝ≥0) (ε M : ℝ) (n : ℕ) : ℝ≥0 → Prop :=
  CritAlive q ζ₀ ε M n (gapExt a xL xR ρL ρR o vL vR b ζ₀) (lowerExtPath ζ₀ (vL o) (xL o))
    (fun j => upperExtPath ζ₀ (vR j) (xR j))

namespace IsForcePath

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ₀ : ℝ≥0∞} {o : Fin nL}

section Alive

variable (h : IsForcePath xL xR ρL ρR w vL vR ζ₀) (hw : DriverEq a ρL ρR w vL vR b ζ₀)
  (hS : ∑ i, ρL i = -2) (ho : ∀ i, i ≤ o) (hb : Continuous b) {q₀ : ℚ} {t : ℝ≥0} {ε M : ℝ}
  {n : ℕ} (hA : critAlivePath a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) ε M n (ratTime q₀))
include h hw hS ho hb hA

omit hw hS ho in
/-- The localization conditions in closed form on `[q, ρ)` (before the lifetime). -/
theorem condLe_of_mem_Ico {u : ℝ≥0} (hu : u ∈ Ico (ratTime q₀)
    (lifetimeOf (critAlivePath a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) ε M n) (ratTime q₀) t)) :
    CritAlive.CondLe ε M n (gapExt a xL xR ρL ρR o vL vR b ζ₀ u) (lowerExtPath ζ₀ (vL o) (xL o) u)
      (fun j => upperExtPath ζ₀ (vR j) (xR j) u) := by
  have huζ : (u : ℝ≥0∞) < ζ₀ := CritAlive.lt_of_mem_Ico hu
  have hn : {s : ℝ≥0 | (s : ℝ≥0∞) < ζ₀} ∈ 𝓝 u := (isOpen_setOf_coe_lt ζ₀).mem_nhds huζ
  exact CritAlive.condLe_of_continuousWithinAt hA (Ico_subset_Icc_self hu)
    ((h.continuousOn_gapExt_lt hb).continuousAt hn).continuousWithinAt
    ((h.continuousOn_lowerExtPath_vL o).continuousAt hn).continuousWithinAt
    fun j => ((h.continuousOn_upperExtPath_vR j).continuousAt hn).continuousWithinAt

omit ho in
/-- The bounds of the localization on `[q, u] ⊆ [q, ρ)` for the actual coordinates:
`ε ≤ Q ≤ M`, `V^out ≥ −n`, `V^{j,R} ≤ n`, `W ≤ V^{j,R} − 1`. -/
theorem bounds_of_mem_Ico {u : ℝ≥0} (hu : u ∈ Ico (ratTime q₀)
    (lifetimeOf (critAlivePath a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) ε M n) (ratTime q₀) t)) :
    (u : ℝ≥0∞) < ζ₀ ∧ ε ≤ w u - vL o u ∧ w u - vL o u ≤ M ∧ -(n : ℝ) ≤ vL o u ∧
      ∀ j, vR j u ≤ n ∧ w u ≤ vR j u - 1 := by
  have huζ : (u : ℝ≥0∞) < ζ₀ := CritAlive.lt_of_mem_Ico hu
  obtain ⟨h1, h2, h3, h4⟩ := h.condLe_of_mem_Ico hb hA hu
  rw [h.gapExt_eq hw hS huζ] at h1 h2 h4
  rw [h.lowerExtPath_vL_eq huζ] at h3 h4
  refine ⟨huζ, h1, h2, h3, fun j => ⟨?_, ?_⟩⟩
  · have := (h4 j).1; dsimp only at this; rwa [h.upperExtPath_vR_eq huζ] at this
  · have := (h4 j).2; dsimp only at this; rw [h.upperExtPath_vR_eq huζ] at this; linarith

/-- The extended coordinates are continuous on `[q, ρ]`, also when `ρ` is the lifetime. -/
theorem continuousOn_ext_Icc :
    (∀ i, ContinuousOn (lowerExtPath ζ₀ (vL i) (xL i)) (Icc (ratTime q₀)
      (lifetimeOf (critAlivePath a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) ε M n) (ratTime q₀) t))) ∧
    ∀ j, ContinuousOn (upperExtPath ζ₀ (vR j) (xR j)) (Icc (ratTime q₀)
      (lifetimeOf (critAlivePath a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) ε M n) (ratTime q₀) t)) := by
  set ρ := lifetimeOf (critAlivePath a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) ε M n) (ratTime q₀) t
    with hρ
  rcases lt_or_eq_of_le (show (ρ : ℝ≥0∞) ≤ ζ₀ from CritAlive.lifetime_le hA) with hlt | heq
  · have hsub : Icc (ratTime q₀) ρ ⊆ {s : ℝ≥0 | (s : ℝ≥0∞) < ζ₀} := fun s hs =>
      lt_of_le_of_lt (by exact_mod_cast hs.2) hlt
    exact ⟨fun i => (h.continuousOn_lowerExtPath_vL i).mono hsub,
      fun j => (h.continuousOn_upperExtPath_vR j).mono hsub⟩
  · have hqζ := CritAlive.lt_lifetime_of_alive hA
    have hqρ : ratTime q₀ < ρ := by rw [← heq] at hqζ; exact_mod_cast hqζ
    have hT : 0 < ρ := lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ ratTime q₀) hqρ
    have hset : {s : ℝ≥0 | (s : ℝ≥0∞) < ζ₀} = Iio ρ := by rw [← heq]; exact setOf_lt_coe_eq_Iio ρ
    have hsub : Icc (ratTime q₀) ρ ⊆ Icc 0 ρ :=
      Icc_subset_Icc (zero_le : (0 : ℝ≥0) ≤ ratTime q₀) le_rfl
    have hlt : ∀ s : ℝ≥0, s < ρ → (s : ℝ≥0∞) < ζ₀ := fun s hs => by
      rw [← heq]; exact_mod_cast hs
    -- bounds before the lifetime
    have hlow : ∀ s : ℝ≥0, ratTime q₀ ≤ s → s < ρ → -(n : ℝ) ≤ vL o s ∧ ∀ j, vR j s ≤ n :=
      fun s hs1 hs2 => by
        obtain ⟨-, -, -, h3, h4⟩ := h.bounds_of_mem_Ico hw hS hb hA ⟨hs1, hs2⟩
        exact ⟨h3, fun j => (h4 j).1⟩
    refine ⟨fun i => ?_, fun j => ?_⟩
    · have hbdd : BddBelow (vL i '' Iio ρ) := by
        refine ⟨min (vL i (ratTime q₀)) (-(n : ℝ)), ?_⟩
        rintro _ ⟨s, hs, rfl⟩
        rcases le_or_gt s (ratTime q₀) with hsq | hsq
        · exact (min_le_left _ _).trans (h.vL_le_of_le hsq (hlt _ hqρ) i)
        · exact (min_le_right _ _).trans ((hlow s hsq.le hs).1.trans
            (h.antitone_vL (hlt s hs) (ho i)))
      have := continuousOn_lowerExtPath_Icc (v := vL i) (d := xL i) hT
        (by rw [← hset]; exact h.antitoneOn_vL i) (by rw [← hset]; exact h.continuousOn_vL i)
        (fun s hs => h.vL_le_xL (hlt s hs) i) hbdd
      rw [heq] at this
      exact this.mono hsub
    · have hbdd : BddAbove (vR j '' Iio ρ) := by
        refine ⟨max (vR j (ratTime q₀)) (n : ℝ), ?_⟩
        rintro _ ⟨s, hs, rfl⟩
        rcases le_or_gt s (ratTime q₀) with hsq | hsq
        · exact (h.le_vR_of_le hsq (hlt _ hqρ) j).trans (le_max_left _ _)
        · exact ((hlow s hsq.le hs).2 j).trans (le_max_right _ _)
      have := continuousOn_upperExtPath_Icc (v := vR j) (d := xR j) hT
        (by rw [← hset]; exact h.monotoneOn_vR j) (by rw [← hset]; exact h.continuousOn_vR j)
        (fun s hs => h.xR_le_vR (hlt s hs) j) hbdd
      rw [heq] at this
      exact this.mono hsub

/-- The extended gap is continuous on `[q, ρ]`. -/
theorem continuousOn_gapExt_Icc :
    ContinuousOn (gapExt a xL xR ρL ρR o vL vR b ζ₀) (Icc (ratTime q₀)
      (lifetimeOf (critAlivePath a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) ε M n) (ratTime q₀) t)) :=
  continuousOn_gapExt_of hb (h.continuousOn_ext_Icc hw hS ho hb hA).1
    (h.continuousOn_ext_Icc hw hS ho hb hA).2

/-- The localization conditions in closed form on `[q, ρ]`. -/
theorem condLe_of_mem_Icc {u : ℝ≥0} (hu : u ∈ Icc (ratTime q₀)
    (lifetimeOf (critAlivePath a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) ε M n) (ratTime q₀) t)) :
    CritAlive.CondLe ε M n (gapExt a xL xR ρL ρR o vL vR b ζ₀ u) (lowerExtPath ζ₀ (vL o) (xL o) u)
      (fun j => upperExtPath ζ₀ (vR j) (xR j) u) :=
  CritAlive.condLe_of_continuousWithinAt hA hu (h.continuousOn_gapExt_Icc hw hS ho hb hA u hu)
    ((h.continuousOn_ext_Icc hw hS ho hb hA).1 o u hu)
    fun j => (h.continuousOn_ext_Icc hw hS ho hb hA).2 j u hu

theorem clampIcc_gapExt_eq {u : ℝ≥0} (hu : u ∈ Icc (ratTime q₀)
    (lifetimeOf (critAlivePath a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) ε M n) (ratTime q₀) t)) :
    clampIcc ε M (gapExt a xL xR ρL ρR o vL vR b ζ₀ u) = gapExt a xL xR ρL ρR o vL vR b ζ₀ u :=
  clampIcc_eq (h.condLe_of_mem_Icc hw hS ho hb hA hu).1 (h.condLe_of_mem_Icc hw hS ho hb hA hu).2.1

/-- The pointwise facts behind (N5)–(N8) on `[q, u]`, `u ∈ [q, ρ)`: for almost every `r`, every
spread rate `δᵢ ≥ 0`, the right drift is bounded by `∑ |ρ^{j,R}|`, and `ε ≤ Q ≤ M`. -/
theorem ae_drift_facts {u : ℝ≥0} (hu : u ∈ Ico (ratTime q₀)
    (lifetimeOf (critAlivePath a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) ε M n) (ratTime q₀) t)) :
    ∀ᵐ r ∂(volume.restrict (Icc (ratTime q₀ : ℝ) u)),
      (∀ i, 0 ≤ spreadRate w vL o i r) ∧ |rightDrift ρR w vR r| ≤ ∑ j, |ρR j| ∧
        ε ≤ w r.toNNReal - vL o r.toNNReal ∧ w r.toNNReal - vL o r.toNNReal ≤ M := by
  refine (ae_restrict_iff' measurableSet_Icc).2 ?_
  filter_upwards [ae_all_iff.2 fun i => measure_eq_zero_iff_ae_notMem.1 (h.volume_collisionL i)]
    with r hr hrI
  obtain ⟨hs, hr0⟩ := toNNReal_mem_Ico hu hrI
  obtain ⟨hsζ, h1, h2, -, h4⟩ := h.bounds_of_mem_Ico hw hS hb hA hs
  refine ⟨fun i => ?_, ?_, h1, h2⟩
  · have hne : w r.toNNReal ≠ vL i r.toNNReal := fun he =>
      hr i ⟨(NNReal.coe_nonneg _).trans hrI.1, hsζ, he⟩
    exact spreadRate_nonneg (lt_of_le_of_ne (h.vL_le_w hsζ i) (Ne.symm hne))
      (h.antitone_vL hsζ (ho i))
  · unfold rightDrift
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    have hd : 1 ≤ |w r.toNNReal - vR j r.toNNReal| := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith [(h4 j).2])]
      linarith [(h4 j).2]
    rw [abs_div]
    exact div_le_self (abs_nonneg _) hd

omit hw hS ho hb hA in
/-- `μ_Q` is interval integrable on `[s, u]` for `s ≤ u < ζ`. -/
theorem intervalIntegrable_gapOutDrift {s u : ℝ≥0} (hsu : s ≤ u) (hu : (u : ℝ≥0∞) < ζ₀) :
    IntervalIntegrable (gapOutDrift ρL ρR w vL vR o) volume s u := by
  have hsub : uIcc (s : ℝ) u ⊆ uIcc 0 (u : ℝ) := by
    rw [uIcc_of_le (show (s : ℝ) ≤ u from hsu), uIcc_of_le (NNReal.coe_nonneg u)]
    exact Icc_subset_Icc (NNReal.coe_nonneg s) le_rfl
  exact ((h.intervalIntegrable_driverDrift hu).sub (h.intervalIntegrable_forceL hu o)).mono_set hsub

omit hw hS ho hb hA in
/-- `r ↦ (w − V^out)(r)` is continuous on `[s, u]`, `u < ζ`. -/
theorem continuousOn_gap_real {s u : ℝ≥0} (hu : (u : ℝ≥0∞) < ζ₀) :
    ContinuousOn (fun r : ℝ => w r.toNNReal - vL o r.toNNReal) (Icc (s : ℝ) u) := by
  have hmaps : MapsTo Real.toNNReal (Icc (s : ℝ) u) {t : ℝ≥0 | (t : ℝ≥0∞) < ζ₀} := fun r hr =>
    lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hr.2) hu
  exact (h.continuousOn_w.comp continuous_real_toNNReal.continuousOn hmaps).sub
    ((h.continuousOn_vL o).comp continuous_real_toNNReal.continuousOn hmaps)

omit hw hS ho hA hb in
theorem continuousOn_clamp_real {s u : ℝ≥0} (hb : Continuous b) (hu : (u : ℝ≥0∞) < ζ₀) :
    ContinuousOn (fun r : ℝ => clampIcc ε M (gapExt a xL xR ρL ρR o vL vR b ζ₀ r.toNNReal))
      (Icc (s : ℝ) u) := by
  have hmaps : MapsTo Real.toNNReal (Icc (s : ℝ) u) {t : ℝ≥0 | (t : ℝ≥0∞) < ζ₀} := fun r hr =>
    lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hr.2) hu
  exact (continuous_clampIcc ε M).comp_continuousOn
    ((h.continuousOn_gapExt_lt hb).comp continuous_real_toNNReal.continuousOn hmaps)

/-- **The drift bound before the lifetime**: `∫_q^u |μ_Q| ≤ ∑ |ρ^{i,L}| (x^{i,L} − x^{out})/2 +
(∑ |ρ^{j,R}|)(u − q)` for `u ∈ [q, ρ)`. -/
theorem integral_abs_gapOutDrift_le {u : ℝ≥0} (hu : u ∈ Ico (ratTime q₀)
    (lifetimeOf (critAlivePath a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) ε M n) (ratTime q₀) t)) :
    ∫ r in (ratTime q₀ : ℝ)..u, |gapOutDrift ρL ρR w vL vR o r| ≤
      (∑ i, |ρL i| * ((xL i - xL o) / 2)) + (∑ j, |ρR j|) * ((u : ℝ) - ratTime q₀) := by
  have hqu : (ratTime q₀ : ℝ) ≤ u := hu.1
  have huζ : (u : ℝ≥0∞) < ζ₀ := CritAlive.lt_of_mem_Ico hu
  have hqζ : ((ratTime q₀ : ℝ≥0) : ℝ≥0∞) < ζ₀ := lt_of_le_of_lt (by exact_mod_cast hu.1) huζ
  have hsub : uIcc (ratTime q₀ : ℝ) u ⊆ uIcc 0 (u : ℝ) := by
    rw [uIcc_of_le hqu, uIcc_of_le (NNReal.coe_nonneg u)]
    exact Icc_subset_Icc (NNReal.coe_nonneg _) le_rfl
  have hdi := h.intervalIntegrable_gapOutDrift (o := o) hu.1 huζ
  have hδ : ∀ i, IntervalIntegrable (fun r => |ρL i| * spreadRate w vL o i r) volume
      (ratTime q₀ : ℝ) u := fun i =>
    ((h.intervalIntegrable_spreadRate huζ o i).mono_set hsub).const_mul _
  have hg : IntervalIntegrable (fun r => (∑ i, |ρL i| * spreadRate w vL o i r) + ∑ j, |ρR j|)
      volume (ratTime q₀ : ℝ) u := by
    have := IntervalIntegrable.sum Finset.univ fun i _ => hδ i
    rw [Finset.sum_fn] at this
    exact this.add intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_ae_restrict hqu hdi.abs hg (by
    filter_upwards [h.ae_drift_facts hw hS ho hb hA hu] with r hr
    exact abs_gapOutDrift_le_of hS hr.1 hr.2.1)
  refine hmono.trans (integral_sum_add_const_le hδ (fun i => ?_) _)
  rw [intervalIntegral.integral_const_mul, h.integral_spreadRate o i hu.1 huζ]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h1 := h.vL_sub_vL_le hqζ (ho i)
  have h2 := sub_nonneg.2 (h.antitone_vL huζ (ho i))
  linarith

/-- **(N7)–(N8) before the lifetime**: for `u ∈ [q, ρ)`,
`∫_q^u (|F'(X)| |μ_Q| − (κ/4) F''(X)) ≤ K₁ + C' (u − q)`, where `X` is the clamped extended gap,
`F = xlogxReg ε` (so `F'(X) = 1 + log Q`, `F''(X) = 1/Q` there), `K₁ = critK₁`, `C' = critC'`. -/
theorem integral_xlogx_drift_le (ha : 0 < a) (hε : 0 < ε) (hε1 : ε ≤ 1) (hM : 1 ≤ M) {u : ℝ≥0}
    (hu : u ∈ Ico (ratTime q₀)
      (lifetimeOf (critAlivePath a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) ε M n) (ratTime q₀) t)) :
    ∫ r in (ratTime q₀ : ℝ)..u,
      (|xlogxReg' ε (clampIcc ε M (gapExt a xL xR ρL ρR o vL vR b ζ₀ r.toNNReal))| *
          |gapOutDrift ρL ρR w vL vR o r| -
        a / 4 * xlogxReg'' ε (clampIcc ε M (gapExt a xL xR ρL ρR o vL vR b ζ₀ r.toNNReal))) ≤
      critK₁ xL ρL o M + critC' a ρR M * ((u : ℝ) - ratTime q₀) := by
  have hqu : (ratTime q₀ : ℝ) ≤ u := hu.1
  have huζ : (u : ℝ≥0∞) < ζ₀ := CritAlive.lt_of_mem_Ico hu
  have hqζ : ((ratTime q₀ : ℝ≥0) : ℝ≥0∞) < ζ₀ := lt_of_le_of_lt (by exact_mod_cast hu.1) huζ
  have hsub : uIcc (ratTime q₀ : ℝ) u ⊆ uIcc 0 (u : ℝ) := by
    rw [uIcc_of_le hqu, uIcc_of_le (NNReal.coe_nonneg u)]
    exact Icc_subset_Icc (NNReal.coe_nonneg _) le_rfl
  have hdi := h.intervalIntegrable_gapOutDrift (o := o) hu.1 huζ
  have hX := h.continuousOn_clamp_real (a := a) (o := o) (s := ratTime q₀) (ε := ε) (M := M) hb huζ
  rw [← uIcc_of_le hqu] at hX
  have hQc := h.continuousOn_gap_real (o := o) (s := ratTime q₀) huζ
  rw [← uIcc_of_le hqu] at hQc
  -- integrability of the left side
  have hL1 : IntervalIntegrable (fun r => |xlogxReg' ε (clampIcc ε M
      (gapExt a xL xR ρL ρR o vL vR b ζ₀ r.toNNReal))| * |gapOutDrift ρL ρR w vL vR o r|)
      volume (ratTime q₀ : ℝ) u :=
    hdi.abs.continuousOn_mul ((continuous_xlogxReg' hε).abs.comp_continuousOn hX)
  have hL2 : IntervalIntegrable (fun r => a / 4 * xlogxReg'' ε (clampIcc ε M
      (gapExt a xL xR ρL ρR o vL vR b ζ₀ r.toNNReal))) volume (ratTime q₀ : ℝ) u :=
    (((continuous_xlogxReg'' hε).comp_continuousOn hX).intervalIntegrable).const_mul _
  -- the spread terms
  have hpos : ∀ r ∈ uIcc (ratTime q₀ : ℝ) u, w r.toNNReal - vL o r.toNNReal ≠ 0 := fun r hr => by
    rw [uIcc_of_le hqu] at hr
    obtain ⟨hs, -⟩ := toNNReal_mem_Ico hu hr
    exact (lt_of_lt_of_le hε (h.bounds_of_mem_Ico hw hS hb hA hs).2.1).ne'
  have hF : ContinuousOn (fun r : ℝ => |1 + Real.log (w r.toNNReal - vL o r.toNNReal)|)
      (uIcc (ratTime q₀ : ℝ) u) :=
    (continuousOn_const.add (hQc.log hpos)).abs
  have hf : ∀ i, IntervalIntegrable (fun r => |ρL i| *
      (|1 + Real.log (w r.toNNReal - vL o r.toNNReal)| * spreadRate w vL o i r))
      volume (ratTime q₀ : ℝ) u := fun i =>
    (((h.intervalIntegrable_spreadRate huζ o i).mono_set hsub).continuousOn_mul hF).const_mul _
  have hg : IntervalIntegrable (fun r => (∑ i, |ρL i| *
      (|1 + Real.log (w r.toNNReal - vL o r.toNNReal)| * spreadRate w vL o i r)) + critC' a ρR M)
      volume (ratTime q₀ : ℝ) u := by
    have := IntervalIntegrable.sum Finset.univ fun i _ => hf i
    rw [Finset.sum_fn] at this
    exact this.add intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_ae_restrict hqu (hL1.sub hL2) hg (by
    filter_upwards [h.ae_drift_facts hw hS ho hb hA hu, ae_restrict_mem measurableSet_Icc]
      with r hr hrI
    obtain ⟨hδ, hR, hQε, hQM⟩ := hr
    obtain ⟨hs, -⟩ := toNNReal_mem_Ico hu hrI
    have hsζ : (r.toNNReal : ℝ≥0∞) < ζ₀ := CritAlive.lt_of_mem_Ico hs
    set Q := w r.toNNReal - vL o r.toNNReal with hQ
    have hQpos : 0 < Q := lt_of_lt_of_le hε hQε
    have hXQ : clampIcc ε M (gapExt a xL xR ρL ρR o vL vR b ζ₀ r.toNNReal) = Q := by
      rw [h.gapExt_eq hw hS hsζ]; exact clampIcc_eq hQε hQM
    simp only [hXQ, xlogxReg'_eq hε hQε, xlogxReg''_eq hQε]
    have hd := abs_gapOutDrift_le_of hS hδ hR
    have hC0 : 0 ≤ ∑ j, |ρR j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    have hkey := mul_abs_one_add_log_le ha hC0 hM hQpos hQM
    have hlog0 := abs_nonneg (1 + Real.log Q)
    have e1 : |1 + Real.log Q| * ((∑ i, |ρL i| * spreadRate w vL o i r) + ∑ j, |ρR j|) =
        (∑ i, |ρL i| * (|1 + Real.log Q| * spreadRate w vL o i r)) +
          (∑ j, |ρR j|) * |1 + Real.log Q| := by
      rw [mul_add, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => by ring
      · exact mul_comm _ _
    have e2 : a / (4 * Q) = a / 4 * Q⁻¹ := by rw [← div_eq_mul_inv, div_div]
    have h3 := mul_le_mul_of_nonneg_left hd hlog0
    rw [e1] at h3
    unfold critC'
    rw [e2] at hkey
    linarith)
  rw [intervalIntegral.integral_sub hL1 hL2] at hmono ⊢
  refine hmono.trans (integral_sum_add_const_le hf (fun i => ?_) _)
  rw [intervalIntegral.integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have hN7 := h.integral_abs_one_add_log_mul_spreadRate_le (ho i) hu.1 huζ hε hε1 hM
    fun r hr1 hr2 => by
      obtain ⟨-, h1, h2, -⟩ := h.bounds_of_mem_Ico hw hS hb hA ⟨hr1, lt_of_le_of_lt hr2 hu.2⟩
      exact ⟨h1, h2⟩
  have h1 := h.vL_sub_vL_le hqζ (ho i)
  have hlogM := Real.log_nonneg hM
  have h2 : (1 + Real.log M) * (vL i (ratTime q₀) - vL o (ratTime q₀)) ≤
      (1 + Real.log M) * |xL i - xL o| :=
    mul_le_mul_of_nonneg_left (h1.trans (le_abs_self _)) (by linarith)
  linarith

/-- `μ_Q` is interval integrable on `[q, ρ]`, also when `ρ` is the lifetime. -/
theorem intervalIntegrable_drift_Icc (hqt : ratTime q₀ ≤ t) :
    IntervalIntegrable (gapOutDrift ρL ρR w vL vR o) volume (ratTime q₀ : ℝ)
      (lifetimeOf (critAlivePath a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) ε M n) (ratTime q₀) t) := by
  set ρ := lifetimeOf (critAlivePath a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) ε M n) (ratTime q₀) t
  rcases eq_or_lt_of_le (show ratTime q₀ ≤ ρ from le_lifetimeOf _ _ _) with heq | hlt
  · rw [← heq]
  refine intervalIntegrable_of_forall_lt (show (ratTime q₀ : ℝ) < ρ from hlt)
    (K := (∑ i, |ρL i| * ((xL i - xL o) / 2)) + (∑ j, |ρR j|) * ((t : ℝ) - ratTime q₀))
    (fun u hu1 hu2 => ?_) (fun u hu1 hu2 => ?_)
  · obtain ⟨hu, hu'⟩ := toNNReal_mem_Ico' hu1 hu2
    have := h.intervalIntegrable_gapOutDrift (o := o) hu.1 (CritAlive.lt_of_mem_Ico hu)
    rwa [hu'] at this
  · obtain ⟨hu, hu'⟩ := toNNReal_mem_Ico' hu1 hu2
    have := h.integral_abs_gapOutDrift_le hw hS ho hb hA hu
    rw [hu'] at this
    have hut : u ≤ t := hu2.le.trans (by exact_mod_cast lifetimeOf_le hqt)
    have hC0 : 0 ≤ ∑ j, |ρR j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    nlinarith

omit hw hS hb in
/-- `x^{out} ≤ x^{i,L}` (the spreads at time `0`). -/
theorem xL_out_le (i : Fin nL) : xL o ≤ xL i := by
  have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ₀ :=
    lt_of_le_of_lt (by exact_mod_cast (zero_le : (0 : ℝ≥0) ≤ ratTime q₀))
      (CritAlive.lt_lifetime_of_alive hA)
  have := h.antitone_vL h0 (ho i)
  simpa [h.vL_zero] using this

/-- `∫_q^ρ |μ_Q| ≤ ∑ |ρ^{i,L}| (x^{i,L} − x^{out})/2 + (∑ |ρ^{j,R}|)(t − q)`. -/
theorem integral_abs_drift_Icc_le (hqt : ratTime q₀ ≤ t) :
    ∫ r in (ratTime q₀ : ℝ)..(lifetimeOf (critAlivePath a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) ε M n)
      (ratTime q₀) t), |gapOutDrift ρL ρR w vL vR o r| ≤
      (∑ i, |ρL i| * ((xL i - xL o) / 2)) + (∑ j, |ρR j|) * ((t : ℝ) - ratTime q₀) := by
  set ρ := lifetimeOf (critAlivePath a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) ε M n) (ratTime q₀) t
  have hqρ : ratTime q₀ ≤ ρ := le_lifetimeOf _ _ _
  have hC0 : 0 ≤ ∑ j, |ρR j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hqt' : (ratTime q₀ : ℝ) ≤ t := hqt
  have hK : 0 ≤ (∑ i, |ρL i| * ((xL i - xL o) / 2)) + (∑ j, |ρR j|) * ((t : ℝ) - ratTime q₀) := by
    have : 0 ≤ ∑ i, |ρL i| * ((xL i - xL o) / 2) := Finset.sum_nonneg fun i _ =>
      mul_nonneg (abs_nonneg _) (by linarith [h.xL_out_le ho hA i])
    nlinarith
  refine intervalIntegral_le_of_forall_lt (show (ratTime q₀ : ℝ) ≤ ρ from hqρ)
    (h.intervalIntegrable_drift_Icc hw hS ho hb hA hqt).abs hK fun u hu1 hu2 => ?_
  obtain ⟨hu, hu'⟩ := toNNReal_mem_Ico' hu1 hu2
  have := h.integral_abs_gapOutDrift_le hw hS ho hb hA hu
  rw [hu'] at this
  have hut : u ≤ t := hu2.le.trans (by exact_mod_cast lifetimeOf_le hqt)
  nlinarith

/-- **The integrated equation of the extended gap on `[q, ρ]`**, including at `ρ = ζ`:
`Q̄_u = Q̄_q + √κ (b_u − b_q) + ∫_q^u μ_Q`. -/
theorem gapExt_eq_add (hqt : ratTime q₀ ≤ t) {u : ℝ≥0} (hu : u ∈ Icc (ratTime q₀)
    (lifetimeOf (critAlivePath a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) ε M n) (ratTime q₀) t)) :
    gapExt a xL xR ρL ρR o vL vR b ζ₀ u = gapExt a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) +
      Real.sqrt a * (b u - b (ratTime q₀)) +
      ∫ r in (ratTime q₀ : ℝ)..u, gapOutDrift ρL ρR w vL vR o r := by
  set ρ := lifetimeOf (critAlivePath a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) ε M n) (ratTime q₀) t
  have hqζ := CritAlive.lt_lifetime_of_alive hA
  have hIco : ∀ v ∈ Ico (ratTime q₀) ρ, gapExt a xL xR ρL ρR o vL vR b ζ₀ v =
      gapExt a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) + Real.sqrt a * (b v - b (ratTime q₀)) +
      ∫ r in (ratTime q₀ : ℝ)..v, gapOutDrift ρL ρR w vL vR o r := fun v hv => by
    have hvζ := CritAlive.lt_of_mem_Ico hv
    rw [h.gapExt_eq hw hS hvζ, h.gapExt_eq hw hS hqζ]
    have := h.gap_out_sub hw o hv.1 hvζ
    linarith
  rcases eq_or_lt_of_le (hu.1.trans hu.2) with heq | hlt
  · have : u = ratTime q₀ := le_antisymm (hu.2.trans heq.symm.le) hu.1
    subst this
    simp
  · have hint := h.intervalIntegrable_drift_Icc hw hS ho hb hA hqt
    have hprim : ContinuousOn (fun v : ℝ => ∫ r in (ratTime q₀ : ℝ)..v,
        gapOutDrift ρL ρR w vL vR o r) (uIcc (ratTime q₀ : ℝ) ρ) :=
      intervalIntegral.continuousOn_primitive_interval' hint left_mem_uIcc
    have hmaps : MapsTo (fun v : ℝ≥0 => (v : ℝ)) (Icc (ratTime q₀) ρ) (uIcc (ratTime q₀ : ℝ) ρ) :=
      fun v hv => by
        rw [uIcc_of_le (show (ratTime q₀ : ℝ) ≤ ρ from hlt.le)]
        exact ⟨hv.1, hv.2⟩
    have hg : ContinuousOn (fun v : ℝ≥0 => gapExt a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) +
        Real.sqrt a * (b v - b (ratTime q₀)) +
        ∫ r in (ratTime q₀ : ℝ)..v, gapOutDrift ρL ρR w vL vR o r) (Icc (ratTime q₀) ρ) :=
      (continuousOn_const.add (continuousOn_const.mul (hb.continuousOn.sub continuousOn_const))).add
        (hprim.comp NNReal.continuous_coe.continuousOn hmaps)
    have hcl : Icc (ratTime q₀) ρ ⊆ closure (Ico (ratTime q₀) ρ) := by
      rw [closure_Ico hlt.ne]
    exact EqOn.of_subset_closure hIco (h.continuousOn_gapExt_Icc hw hS ho hb hA) hg
      Ico_subset_Icc_self hcl hu

/-- The clamped extended gap is continuous on `[q, ρ]` (as a function of real time). -/
theorem continuousOn_clamp_Icc_real :
    ContinuousOn (fun r : ℝ => clampIcc ε M (gapExt a xL xR ρL ρR o vL vR b ζ₀ r.toNNReal))
      (uIcc (ratTime q₀ : ℝ)
        (lifetimeOf (critAlivePath a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) ε M n) (ratTime q₀) t)) := by
  set ρ := lifetimeOf (critAlivePath a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) ε M n) (ratTime q₀) t
  have hqρ : (ratTime q₀ : ℝ) ≤ ρ := (le_lifetimeOf _ _ _ : ratTime q₀ ≤ ρ)
  have hmaps : MapsTo Real.toNNReal (uIcc (ratTime q₀ : ℝ) ρ) (Icc (ratTime q₀) ρ) := fun r hr => by
    rw [uIcc_of_le hqρ] at hr
    have hr0 : 0 ≤ r := (NNReal.coe_nonneg _).trans hr.1
    exact ⟨(Real.le_toNNReal_iff_coe_le hr0).2 hr.1, Real.toNNReal_le_iff_le_coe.2 hr.2⟩
  exact (continuous_clampIcc ε M).comp_continuousOn
    ((h.continuousOn_gapExt_Icc hw hS ho hb hA).comp continuous_real_toNNReal.continuousOn hmaps)

/-- **(N7)–(N8) up to `ρ`** (including `ρ = ζ`). -/
theorem integral_xlogx_drift_Icc_le (ha : 0 < a) (hε : 0 < ε) (hε1 : ε ≤ 1) (hM : 1 ≤ M)
    (hqt : ratTime q₀ ≤ t) :
    ∫ r in (ratTime q₀ : ℝ)..(lifetimeOf (critAlivePath a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) ε M n)
        (ratTime q₀) t),
      (|xlogxReg' ε (clampIcc ε M (gapExt a xL xR ρL ρR o vL vR b ζ₀ r.toNNReal))| *
          |gapOutDrift ρL ρR w vL vR o r| -
        a / 4 * xlogxReg'' ε (clampIcc ε M (gapExt a xL xR ρL ρR o vL vR b ζ₀ r.toNNReal))) ≤
      critK₁ xL ρL o M + critC' a ρR M * ((t : ℝ) - ratTime q₀) := by
  set ρ := lifetimeOf (critAlivePath a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) ε M n) (ratTime q₀) t
  have hqρ : (ratTime q₀ : ℝ) ≤ ρ := (le_lifetimeOf _ _ _ : ratTime q₀ ≤ ρ)
  have hX := h.continuousOn_clamp_Icc_real hw hS ho hb hA (t := t)
  have hint := h.intervalIntegrable_drift_Icc hw hS ho hb hA hqt
  have hL : IntervalIntegrable (fun r => |xlogxReg' ε (clampIcc ε M
      (gapExt a xL xR ρL ρR o vL vR b ζ₀ r.toNNReal))| * |gapOutDrift ρL ρR w vL vR o r| -
      a / 4 * xlogxReg'' ε (clampIcc ε M (gapExt a xL xR ρL ρR o vL vR b ζ₀ r.toNNReal)))
      volume (ratTime q₀ : ℝ) ρ :=
    (hint.abs.continuousOn_mul ((continuous_xlogxReg' hε).abs.comp_continuousOn hX)).sub
      ((((continuous_xlogxReg'' hε).comp_continuousOn hX).intervalIntegrable).const_mul _)
  have hlogM := Real.log_nonneg hM
  have hC0 : 0 ≤ ∑ j, |ρR j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hK1 : 0 ≤ critK₁ xL ρL o M := Finset.sum_nonneg fun i _ =>
    mul_nonneg (abs_nonneg _) (by
      have : 0 ≤ (1 + Real.log M) * |xL i - xL o| := mul_nonneg (by linarith) (abs_nonneg _)
      linarith)
  have hC' : 0 ≤ critC' a ρR M := by unfold critC'; positivity
  have hqt' : (ratTime q₀ : ℝ) ≤ t := hqt
  refine intervalIntegral_le_of_forall_lt hqρ hL (by nlinarith) fun u hu1 hu2 => ?_
  obtain ⟨hu, hu'⟩ := toNNReal_mem_Ico' hu1 hu2
  have := h.integral_xlogx_drift_le hw hS ho hb hA ha hε hε1 hM hu
  rw [hu'] at this
  have hut : u ≤ t := hu2.le.trans (by exact_mod_cast lifetimeOf_le hqt)
  nlinarith

/-- **The drift term of Itô's formula is bounded below** (Specification (N8)), when alive at `q`:
`∫_q^ρ F'(X) μ_Q ≥ −(K₁ + (κ/4) ∫_q^ρ F''(X) + C' (t − q))`. -/
theorem integral_xlogxReg'_mul_ge_of_alive (ha : 0 < a) (hε : 0 < ε) (hε1 : ε ≤ 1) (hM : 1 ≤ M)
    (hqt : ratTime q₀ ≤ t) :
    -(critK₁ xL ρL o M + a / 4 * (∫ r in (ratTime q₀ : ℝ)..(lifetimeOf
        (critAlivePath a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) ε M n) (ratTime q₀) t),
          xlogxReg'' ε (clampIcc ε M (gapExt a xL xR ρL ρR o vL vR b ζ₀ r.toNNReal))) +
        critC' a ρR M * ((t : ℝ) - ratTime q₀)) ≤
      ∫ r in (ratTime q₀ : ℝ)..(lifetimeOf
        (critAlivePath a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) ε M n) (ratTime q₀) t),
          xlogxReg' ε (clampIcc ε M (gapExt a xL xR ρL ρR o vL vR b ζ₀ r.toNNReal)) *
            gapOutDrift ρL ρR w vL vR o r := by
  set ρ := lifetimeOf (critAlivePath a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) ε M n) (ratTime q₀) t
  have hqρ : (ratTime q₀ : ℝ) ≤ ρ := (le_lifetimeOf _ _ _ : ratTime q₀ ≤ ρ)
  have hX := h.continuousOn_clamp_Icc_real hw hS ho hb hA (t := t)
  have hint := h.intervalIntegrable_drift_Icc hw hS ho hb hA hqt
  have h1 : IntervalIntegrable (fun r => |xlogxReg' ε (clampIcc ε M
      (gapExt a xL xR ρL ρR o vL vR b ζ₀ r.toNNReal))| * |gapOutDrift ρL ρR w vL vR o r|)
      volume (ratTime q₀ : ℝ) ρ :=
    hint.abs.continuousOn_mul ((continuous_xlogxReg' hε).abs.comp_continuousOn hX)
  have h2 : IntervalIntegrable (fun r => xlogxReg'' ε (clampIcc ε M
      (gapExt a xL xR ρL ρR o vL vR b ζ₀ r.toNNReal))) volume (ratTime q₀ : ℝ) ρ :=
    ((continuous_xlogxReg'' hε).comp_continuousOn hX).intervalIntegrable
  have hbound := h.integral_xlogx_drift_Icc_le hw hS ho hb hA ha hε hε1 hM hqt
  rw [intervalIntegral.integral_sub h1 (h2.const_mul _), intervalIntegral.integral_const_mul]
    at hbound
  have habs := intervalIntegral.abs_integral_le_integral_abs (μ := volume) (a := (ratTime q₀ : ℝ))
    (b := (ρ : ℝ)) (f := fun r => xlogxReg' ε (clampIcc ε M
      (gapExt a xL xR ρL ρR o vL vR b ζ₀ r.toNNReal)) * gapOutDrift ρL ρR w vL vR o r) hqρ
  simp only [abs_mul] at habs
  have := neg_abs_le (∫ r in (ratTime q₀ : ℝ)..ρ, xlogxReg' ε (clampIcc ε M
      (gapExt a xL xR ρL ρR o vL vR b ζ₀ r.toNNReal)) * gapOutDrift ρL ρR w vL vR o r)
  linarith

/-- **The Tanaka hypotheses of the critical localization** (when alive at `q`): on `[q, ρ]` the
clamped extended gap `X` satisfies `X_u = X_q + √κ (b_u − b_q) + ∫_q^u μ_Q`, is continuous,
`|X| ≤ N`, and `∫_q^ρ |μ_Q| ≤ N`. -/
theorem isTanakaPath_crit_of_alive (hε : 0 < ε) (hεM : ε ≤ M) (hqt : ratTime q₀ ≤ t) {N : ℝ}
    (hNM : M ≤ N) (hN : critBound xL ρL ρR o M ((t : ℝ) - ratTime q₀) ≤ N) :
    IsTanakaPath (Real.sqrt a) 0 N (ratTime q₀)
      (lifetimeOf (critAlivePath a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) ε M n) (ratTime q₀) t)
      (fun u => clampIcc ε M (gapExt a xL xR ρL ρR o vL vR b ζ₀ u)) b (fun _ => 0)
      (fun u => gapOutDrift ρL ρR w vL vR o u) := by
  set ρ := lifetimeOf (critAlivePath a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) ε M n) (ratTime q₀) t
  have hqρ : ratTime q₀ ≤ ρ := le_lifetimeOf _ _ _
  have hfun : (fun r : ℝ => gapOutDrift ρL ρR w vL vR o (r.toNNReal : ℝ)) =
      gapOutDrift ρL ρR w vL vR o := funext (gapOutDrift_coe_toNNReal ρL ρR w vL vR o)
  have hint := h.intervalIntegrable_drift_Icc hw hS ho hb hA hqt
  have hN0 : 0 ≤ N := (le_of_lt hε).trans (hεM.trans hNM)
  refine ⟨(continuous_clampIcc ε M).comp_continuousOn (h.continuousOn_gapExt_Icc hw hS ho hb hA),
    hb.continuousOn, continuousOn_const, ?_, ?_, monotoneOn_const, fun _ _ _ _ _ _ => rfl, ?_, ?_,
    by simpa using hN0⟩
  · show IntervalIntegrable (fun r : ℝ => gapOutDrift ρL ρR w vL vR o (r.toNNReal : ℝ)) volume _ _
    rw [hfun]; exact hint
  · intro u hu
    show clampIcc ε M (gapExt a xL xR ρL ρR o vL vR b ζ₀ u) =
      clampIcc ε M (gapExt a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀)) + Real.sqrt a * (b u - b (ratTime q₀))
        + (∫ r in (ratTime q₀ : ℝ)..u, gapOutDrift ρL ρR w vL vR o (r.toNNReal : ℝ)) + 0 * (0 - 0)
    rw [hfun, h.clampIcc_gapExt_eq hw hS ho hb hA hu,
      h.clampIcc_gapExt_eq hw hS ho hb hA ⟨le_rfl, hqρ⟩, h.gapExt_eq_add hw hS ho hb hA hqt hu]
    ring
  · intro u _
    rw [abs_of_pos (lt_of_lt_of_le hε (le_clampIcc ε M _))]
    exact (clampIcc_le hεM _).trans hNM
  · show ∫ r in (ratTime q₀ : ℝ)..ρ, |gapOutDrift ρL ρR w vL vR o (r.toNNReal : ℝ)| ≤ N
    simp only [gapOutDrift_coe_toNNReal]
    refine (h.integral_abs_drift_Icc_le hw hS ho hb hA hqt).trans (le_trans ?_ hN)
    have hsum : ∑ i, |ρL i| * ((xL i - xL o) / 2) ≤ ∑ i, |ρL i| * (|xL i - xL o| / 2) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (le_abs_self _) (by norm_num)) (abs_nonneg _)
    unfold critBound
    linarith

end Alive

/-- **The Tanaka hypotheses of the critical localization**, in general: if the path is not alive
at `q`, the lifetime is `q` and the hypotheses hold trivially. -/
theorem isTanakaPath_crit (h : IsForcePath xL xR ρL ρR w vL vR ζ₀)
    (hw : DriverEq a ρL ρR w vL vR b ζ₀) (hS : ∑ i, ρL i = -2) (ho : ∀ i, i ≤ o)
    (hb : Continuous b) {q₀ : ℚ} {t : ℝ≥0} {ε M : ℝ} {n : ℕ} (hε : 0 < ε) (hεM : ε ≤ M)
    (hqt : ratTime q₀ ≤ t) {N : ℝ} (hNM : M ≤ N)
    (hN : critBound xL ρL ρR o M ((t : ℝ) - ratTime q₀) ≤ N) :
    IsTanakaPath (Real.sqrt a) 0 N (ratTime q₀)
      (lifetimeOf (critAlivePath a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) ε M n) (ratTime q₀) t)
      (fun u => clampIcc ε M (gapExt a xL xR ρL ρR o vL vR b ζ₀ u)) b (fun _ => 0)
      (fun u => gapOutDrift ρL ρR w vL vR o u) := by
  by_cases hA : critAlivePath a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) ε M n (ratTime q₀)
  · exact h.isTanakaPath_crit_of_alive hw hS ho hb hA hε hεM hqt hNM hN
  · have hρ : lifetimeOf (critAlivePath a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) ε M n)
        (ratTime q₀) t = ratTime q₀ := lifetimeOf_eq_of_not CritAlive.anti hA
    rw [hρ]
    refine isTanakaPath_singleton ?_ ((le_of_lt hε).trans (hεM.trans hNM))
    rw [abs_of_pos (lt_of_lt_of_le hε (le_clampIcc ε M _))]
    exact (clampIcc_le hεM _).trans hNM

end IsForcePath

namespace IsForcePath

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ₀ : ℝ≥0∞} {o : Fin nL}

/-- **The drift term of Itô's formula is bounded below** (Specification (N8)), for every path:
`∫_q^ρ F'(X) μ_Q ≥ −(K₁ + (κ/4) ∫_q^ρ F''(X) + C' (t − q))`. -/
theorem integral_xlogxReg'_mul_ge (h : IsForcePath xL xR ρL ρR w vL vR ζ₀)
    (hw : DriverEq a ρL ρR w vL vR b ζ₀) (hS : ∑ i, ρL i = -2) (ho : ∀ i, i ≤ o)
    (hb : Continuous b) {q₀ : ℚ} {t : ℝ≥0} {ε M : ℝ} {n : ℕ} (ha : 0 < a) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hM : 1 ≤ M) (hqt : ratTime q₀ ≤ t) :
    -(critK₁ xL ρL o M + a / 4 * (∫ r in (ratTime q₀ : ℝ)..(lifetimeOf
        (critAlivePath a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) ε M n) (ratTime q₀) t),
          xlogxReg'' ε (clampIcc ε M (gapExt a xL xR ρL ρR o vL vR b ζ₀ r.toNNReal))) +
        critC' a ρR M * ((t : ℝ) - ratTime q₀)) ≤
      ∫ r in (ratTime q₀ : ℝ)..(lifetimeOf
        (critAlivePath a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) ε M n) (ratTime q₀) t),
          xlogxReg' ε (clampIcc ε M (gapExt a xL xR ρL ρR o vL vR b ζ₀ r.toNNReal)) *
            gapOutDrift ρL ρR w vL vR o r := by
  by_cases hA : critAlivePath a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) ε M n (ratTime q₀)
  · exact h.integral_xlogxReg'_mul_ge_of_alive hw hS ho hb hA ha hε hε1 hM hqt
  · have hρ : lifetimeOf (critAlivePath a xL xR ρL ρR o vL vR b ζ₀ (ratTime q₀) ε M n)
        (ratTime q₀) t = ratTime q₀ := lifetimeOf_eq_of_not CritAlive.anti hA
    rw [hρ, intervalIntegral.integral_same, intervalIntegral.integral_same, mul_zero, add_zero]
    have hlogM := Real.log_nonneg hM
    have hK1 : 0 ≤ critK₁ xL ρL o M := Finset.sum_nonneg fun i _ =>
      mul_nonneg (abs_nonneg _) (by
        have : 0 ≤ (1 + Real.log M) * |xL i - xL o| := mul_nonneg (by linarith) (abs_nonneg _)
        linarith)
    have hC' : 0 ≤ critC' a ρR M := by unfold critC'; positivity
    have hqt' : (ratTime q₀ : ℝ) ≤ t := hqt
    nlinarith

end IsForcePath

end Sec2

end InteractingSLE
