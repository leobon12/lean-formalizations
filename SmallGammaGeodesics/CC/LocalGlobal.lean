import LQGMetric.Metric.InternalLimitC

/-!
# Local-to-global comparison through curve lengths (track CC, packet CC8a, target T2)

Plan: `planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D13** step 5 and **D15**
step 3 ([3] = Gwynne–Miller arXiv:1905.00384, proof of Prop 3.6, Step 3): a comparison
`d ≤ C·D` between close points of every compact subset of `V` gives `d ≤ C·D(·,·;V)` on `V`.
This generalizes the length comparisons `LQGMetric.DFGPS.T12.curveLength_le_mul_of_local`
(Lebesgue-number partition) and `LQGMetric.LM.t17_eVariationOn_le_mul` from a `ContMetric` to a
function `d : ℂ → ℂ → ℝ≥0∞` with the triangle inequality, as needed for `d = D^ϕ`.

We chain the triangle inequality of `d` along a fine partition of a curve and compare each piece
with its `D`-length. So `d` need not be a length metric, nor continuous, nor symmetric:

* `le_mul_curveLength_of_local`: if `d ≤ C·D` holds for points of `P([a,b])` at Euclidean distance
  `≤ ρ`, then `d(P a, P b) ≤ C · len(P|_{[a,b]}; D)`. The steps of the partition have length
  `≤ ρ` by uniform continuity of `P`.
* `le_mul_pathLength_of_local`: the same for a path in `V` (its range is a compact subset of `V`).
* `le_mul_internal_of_local` (**T2**): `d(x,y) ≤ C · D(x,y;V)` for all `x, y`, if `0 < C`.
* `le_mul_internal_of_local_of_ne_top`: the same for `0 ≤ C` when `D(x,y;V) < ∞`.

**Remark on T2 as written in the packet** (`C ≥ 0`). That form is false for `C = 0`. In `ℝ≥0∞`,
`0 · ∞ = 0`. Take `V = B(0,1) ∪ B(3,1)`, `D` Euclidean, and `d(x,y) = 0` if `x, y` lie in the same
component of `V` (or both outside `V`), `1` otherwise. Then `d` satisfies the triangle inequality,
is continuous on `V × V`, and satisfies the local hypothesis with `C = 0` and `ρ = 1/2`. But
`d(0,3) = 1 > 0 = 0 · D(0,3;V)`. With `0 < C`, as in every consumer (`ConfBiLipLE` has `0 < C`, and
`ConfImprove` has `C_δ ≥ 1 + δ`), the statement holds. The packet's other hypotheses (`d` continuous
on `V × V`, `D` a length metric, `V` open) are not needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric LQGMetric.MetricGeometry

variable (D : ContMetric) {d : ℂ → ℂ → ℝ≥0∞}

/-- `ofReal (C · D(x,y)) ≤ ofReal C · len(P|_{[s,t]}; D)` for `x = P s`, `y = P t` -/
lemma ofReal_mul_dist_le_curveLength {C : ℝ} (hC : 0 ≤ C) (P : ℝ → ℂ) {s t : ℝ} (hst : s ≤ t) :
    ENNReal.ofReal (C * D.1 (P s, P t)) ≤ ENNReal.ofReal C * curveLength (D.pt ∘ P) s t := by
  rw [ENNReal.ofReal_mul hC, ← ContMetric.edist_pt]
  exact mul_le_mul_right (edist_le_curveLength (D.pt ∘ P) hst) _

/-- **Local-to-global along a curve**: if `d ≤ C·D` for points of `P([a,b])` at Euclidean
distance `≤ ρ`, then `d(P a, P b) ≤ C · len(P|_{[a,b]}; D)`. Only the triangle inequality of `d` is
used. -/
theorem le_mul_curveLength_of_local (htri : ∀ x y z, d x z ≤ d x y + d y z) {C ρ : ℝ}
    (hC : 0 ≤ C) (hρ : 0 < ρ) {P : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hP : ContinuousOn P (Icc a b))
    (hloc : ∀ x ∈ P '' Icc a b, ∀ y ∈ P '' Icc a b, ‖x - y‖ ≤ ρ →
      d x y ≤ ENNReal.ofReal (C * D.1 (x, y))) :
    d (P a) (P b) ≤ ENNReal.ofReal C * curveLength (D.pt ∘ P) a b := by
  -- uniform continuity of `P` on `[a, b]` at Euclidean scale `ρ`
  obtain ⟨δ, hδ, hPδ⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hP) ρ hρ
  have hloc' : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → t - s < δ →
      d (P s) (P t) ≤ ENNReal.ofReal C * curveLength (D.pt ∘ P) s t := by
    intro s hs t ht hst hts
    have hd : dist s t < δ := by
      rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]; exact hts
    have hn : ‖P s - P t‖ ≤ ρ := by
      have := hPδ s hs t ht hd
      rw [dist_eq_norm] at this
      exact this.le
    exact (hloc _ (mem_image_of_mem P hs) _ (mem_image_of_mem P ht) hn).trans
      (ofReal_mul_dist_le_curveLength D hC P hst)
  -- induction on the number `n` of steps of length `< δ`
  have main : ∀ n : ℕ, ∀ t ∈ Icc a b, t - a ≤ n * (δ / 2) →
      d (P a) (P t) ≤ ENNReal.ofReal C * curveLength (D.pt ∘ P) a t := by
    intro n
    induction n with
    | zero =>
      intro t ht hn
      have hta : t = a := le_antisymm (by simp only [CharP.cast_eq_zero, zero_mul] at hn; linarith)
        ht.1
      rw [hta]
      exact hloc' a ⟨le_rfl, hab⟩ a ⟨le_rfl, hab⟩ le_rfl (by linarith)
    | succ n ih =>
      intro t ht hn
      set s := max a (t - δ / 2) with hs
      have has : a ≤ s := le_max_left _ _
      have hst : s ≤ t := max_le ht.1 (by linarith)
      have hsI : s ∈ Icc a b := ⟨has, hst.trans ht.2⟩
      have hts : t - s < δ := by
        have : t - δ / 2 ≤ s := le_max_right _ _
        linarith
      have hsn : s - a ≤ n * (δ / 2) := by
        rcases le_total a (t - δ / 2) with h | h
        · rw [hs, max_eq_right h]; push_cast at hn; linarith
        · rw [hs, max_eq_left h, sub_self]; positivity
      calc d (P a) (P t) ≤ d (P a) (P s) + d (P s) (P t) := htri _ _ _
        _ ≤ ENNReal.ofReal C * curveLength (D.pt ∘ P) a s +
              ENNReal.ofReal C * curveLength (D.pt ∘ P) s t :=
          add_le_add (ih s hsI hsn) (hloc' s hsI t ht hst hts)
        _ = ENNReal.ofReal C * curveLength (D.pt ∘ P) a t := by
          rw [← mul_add, curveLength_add _ has hst]
  obtain ⟨n, hn⟩ := exists_nat_ge ((b - a) / (δ / 2))
  exact main n b ⟨hab, le_rfl⟩ (by rwa [div_le_iff₀ (by linarith)] at hn)

/-- **Local-to-global along a path in `V`**: if, on every compact `K ⊆ V`, `d ≤ C·D` holds for
points at Euclidean distance `≤ ρ_K`, then `d(x, y) ≤ C · len(γ; D)` for every path `γ` from `x`
to `y` in `V`. -/
theorem le_mul_pathLength_of_local (htri : ∀ x y z, d x z ≤ d x y + d y z) {V : Set ℂ} {C : ℝ}
    (hC : 0 ≤ C)
    (hloc : ∀ K : Set ℂ, IsCompact K → K ⊆ V → ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ K, ∀ y ∈ K,
      ‖x - y‖ ≤ ρ → d x y ≤ ENNReal.ofReal (C * D.1 (x, y)))
    {x y : ℂ} (γ : Path (D.pt x) (D.pt y)) (hγ : ∀ t, γ t ∈ D.pt '' V) :
    d x y ≤ ENNReal.ofReal C * pathLength γ := by
  set P : ℝ → ℂ := D.unpt ∘ γ.extend with hPdef
  have hPc : Continuous P := D.continuous_unpt.comp γ.continuous_extend
  have hK : IsCompact (P '' Icc 0 1) := isCompact_Icc.image hPc
  have hKV : P '' Icc 0 1 ⊆ V := by
    rintro _ ⟨t, ht, rfl⟩
    have h1 : γ.extend t ∈ D.pt '' V := by
      rw [Path.extend_apply _ ht]; exact hγ _
    obtain ⟨z, hz, hzt⟩ := h1
    have : P t = z := by simp only [hPdef, Function.comp_apply, ← hzt]; rfl
    rw [this]; exact hz
  obtain ⟨ρ, hρ, hloc'⟩ := hloc _ hK hKV
  have h := le_mul_curveLength_of_local D htri hC hρ zero_le_one hPc.continuousOn hloc'
  have hP0 : P 0 = x := by simp only [hPdef, Function.comp_apply, Path.extend_zero]; rfl
  have hP1 : P 1 = y := by simp only [hPdef, Function.comp_apply, Path.extend_one]; rfl
  rw [hP0, hP1] at h
  exact h

/-- **T2 (local-to-global, CC0 D13.5 / [3] Prop 3.6 Step 3)**: for `d : ℂ → ℂ → ℝ≥0∞` with the
triangle inequality, a continuous metric `D`, a set `V` and `C > 0`: if for every compact `K ⊆ V`
there is `ρ > 0` with `d(x,y) ≤ C·D(x,y)` for `x, y ∈ K`, `‖x − y‖ ≤ ρ`, then
`d(x,y) ≤ C · D(x,y;V)` for all `x, y` (if `x ∉ V` or `y ∉ V`, the right side is `∞`).
The packet's form has `C ≥ 0`, which is false for `C = 0` (see the module docstring).
Continuity of `d`, the length property of `D` and openness of `V` are not needed. -/
theorem le_mul_internal_of_local (htri : ∀ x y z, d x z ≤ d x y + d y z) {V : Set ℂ} {C : ℝ}
    (hC : 0 < C)
    (hloc : ∀ K : Set ℂ, IsCompact K → K ⊆ V → ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ K, ∀ y ∈ K,
      ‖x - y‖ ≤ ρ → d x y ≤ ENNReal.ofReal (C * D.1 (x, y)))
    (x y : ℂ) : d x y ≤ ENNReal.ofReal C * D.internal V x y := by
  unfold ContMetric.internal internalEDist
  rw [ENNReal.mul_iInf_of_ne (ENNReal.ofReal_pos.2 hC).ne' ENNReal.ofReal_ne_top]
  exact le_iInf fun γ => le_mul_pathLength_of_local D htri hC.le hloc γ.1 γ.2

/-- **T2 for `C ≥ 0`**, under the extra hypothesis `D(x,y;V) < ∞` (some path in `V` of finite
`D`-length joins `x` and `y`). The extra hypothesis is needed only when `C = 0`. -/
theorem le_mul_internal_of_local_of_ne_top (htri : ∀ x y z, d x z ≤ d x y + d y z) {V : Set ℂ}
    {C : ℝ} (hC : 0 ≤ C)
    (hloc : ∀ K : Set ℂ, IsCompact K → K ⊆ V → ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ K, ∀ y ∈ K,
      ‖x - y‖ ≤ ρ → d x y ≤ ENNReal.ofReal (C * D.1 (x, y)))
    {x y : ℂ} (hxy : D.internal V x y ≠ ⊤) : d x y ≤ ENNReal.ofReal C * D.internal V x y := by
  rcases hC.lt_or_eq with hC0 | hC0
  · exact le_mul_internal_of_local D htri hC0 hloc x y
  · -- `C = 0`: a path of finite length exists, and it gives `d x y ≤ 0`
    have hne : Nonempty {γ : Path (D.pt x) (D.pt y) // ∀ t, γ t ∈ D.pt '' V} := by
      by_contra hem
      rw [not_nonempty_iff] at hem
      exact hxy (by unfold ContMetric.internal internalEDist; exact iInf_of_empty _)
    obtain ⟨γ⟩ := hne
    have h := le_mul_pathLength_of_local D htri hC hloc γ.1 γ.2
    rw [← hC0, ENNReal.ofReal_zero, zero_mul] at h ⊢
    exact h

end SmallGammaGeodesics.CC
