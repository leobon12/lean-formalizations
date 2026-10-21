import SmallGammaGeodesics.CC.ConfMetric
import LQGMetric.Metric.WeylPathLength

/-!
# Weyl scaling preserves a length domination (track CC, packet CC11, deterministic core)

Source: `planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D16** (the reversal step
"Weyl-scale both sides by `e^{ξ f}` on `U`; this is monotone, since lengths compare") and **D2.5**,
for Gwynne–Miller arXiv:1905.00384 ([3]), last paragraph of the proof of Thm 1.3 (with the sign
erratum ER3 of CC0 §2.2).

Write `A = e^{ξ g}·A₁` and `B = e^{ξ f}·B₀` for four continuous metrics on `ℂ`, in the form used
by the Weyl axiom (`ofReal (A.1 (x, y)) = weylScale ξ g A₁ x y`). The results:

* `curveLength_le_of_edist_le`: if `d(F a, F b) ≤ len(G; [a, b])` for all `a ≤ b` in `[s, t]`, then
  `len(F; [s, t]) ≤ len(G; [s, t])` (partition sums and additivity of length);
* `exists_partition_lt`: a partition of `[s, t]` into consecutive pieces shorter than `δ`;
* **`curveLength_weyl_transport_le`**: let `P` and `Q` be continuous on `[s, t]`, with
  `A₁(Q a, Q b) ≤ len(P; B₀; [a, b])` for all `a ≤ b` and `g ∘ Q = f ∘ P` on `[s, t]`. Then
  `len(Q; A; [s, t]) ≤ len(P; B; [s, t])`. On a piece of `[s, t]` on which `ξ f ∘ P` stays within
  `ε` of a value `c`, the local bounds of LQGMetric (`curveLength_weyl_le`, `le_curveLength_weyl`)
  give `len(Q; A) ≤ e^{c+ε} len(Q; A₁) ≤ e^{c+ε} len(P; B₀) ≤ e^{2ε} len(P; B)`; uniform continuity
  of `ξ f ∘ P`, a fine partition and additivity give the bound with the factor `e^{2ε}` on
  `[s, t]`, and `ε → 0` removes it;
* **`internal_le_of_reverse`** (the pathwise reversal step of D16): for `IsConfNbhd ϕ W V`, a left
  inverse `ψ` of `ϕ` on `W`, `U = ϕ '' V`, `g = f ∘ ϕ` on `V`, and the one-sided inequality
  `A₁(ψ u, ψ v; V) ≤ B₀(u, v; U)` on `U × U`, we get `A(z, w; V) ≤ B(ϕ z, ϕ w; U)` on `V × V`.
  Each path `P` in `U` from `ϕ z` to `ϕ w` is pulled back to the path `Q = ψ ∘ P` in `V`, and
  `A(z, w; V) ≤ len(Q; A) ≤ len(P; B)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric LQGMetric.MetricGeometry

/-! ## 1. Lengths dominated piece by piece; fine partitions -/

/-- If the distance between the values of `F` at any two times `a ≤ b` of `[s, t]` is at most the
length of `G` on `[a, b]`, then the length of `F` on `[s, t]` is at most that of `G`. -/
theorem curveLength_le_of_edist_le {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    {F : ℝ → X} {G : ℝ → Y} {s t : ℝ}
    (h : ∀ a ∈ Icc s t, ∀ b ∈ Icc s t, a ≤ b → edist (F a) (F b) ≤ curveLength G a b) :
    curveLength F s t ≤ curveLength G s t := by
  show eVariationOn F (Icc s t) ≤ curveLength G s t
  refine iSup_le fun p => ?_
  obtain ⟨n, u, hu, hus⟩ := p
  calc ∑ i ∈ Finset.range n, edist (F (u (i + 1))) (F (u i))
      ≤ ∑ i ∈ Finset.range n, curveLength G (u i) (u (i + 1)) :=
        Finset.sum_le_sum fun i _ => by
          rw [edist_comm]
          exact h _ (hus i) _ (hus (i + 1)) (hu (Nat.le_succ i))
    _ = curveLength G (u 0) (u n) := sum_curveLength_eq G hu n
    _ ≤ curveLength G s t := curveLength_mono G (hus 0).1 (hus n).2

/-- A partition `s = u 0 ≤ u 1 ≤ … ≤ u n = t` of `[s, t]` with all steps shorter than `δ`. -/
theorem exists_partition_lt {s t δ : ℝ} (hst : s ≤ t) (hδ : 0 < δ) :
    ∃ (n : ℕ) (u : ℕ → ℝ), Monotone u ∧ u 0 = s ∧ u n = t ∧ (∀ i, u i ∈ Icc s t) ∧
      ∀ i, u (i + 1) - u i < δ := by
  set n : ℕ := ⌈(t - s) / δ⌉₊ + 1 with hn
  have hn0 : (0 : ℝ) < n := by
    rw [hn]
    positivity
  set k : ℝ := (t - s) / n with hk
  have hk0 : 0 ≤ k := div_nonneg (sub_nonneg.2 hst) hn0.le
  have hkδ : k < δ := by
    have h1 : (t - s) / δ < n := by
      rw [hn, Nat.cast_add, Nat.cast_one]
      exact (Nat.le_ceil _).trans_lt (lt_add_one _)
    rw [div_lt_iff₀ hδ] at h1
    rw [hk, div_lt_iff₀ hn0]
    linarith
  refine ⟨n, fun i => min (s + i * k) t, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have hij' : (i : ℝ) ≤ j := Nat.cast_le.2 hij
    exact min_le_min_right _ (by nlinarith)
  · simp only [Nat.cast_zero, zero_mul, add_zero]
    exact min_eq_left hst
  · show min (s + (n : ℝ) * k) t = t
    rw [hk, mul_div_cancel₀ _ hn0.ne', add_sub_cancel, min_self]
  · intro i
    refine ⟨le_min ?_ hst, min_le_right _ _⟩
    have : 0 ≤ (i : ℝ) * k := mul_nonneg (Nat.cast_nonneg i) hk0
    linarith
  · intro i
    have h1 : min (s + ((i + 1 : ℕ) : ℝ) * k) t ≤ min (s + (i : ℝ) * k) t + k := by
      rw [← min_add_add_right]
      refine min_le_min (le_of_eq ?_) (le_add_of_nonneg_right hk0)
      push_cast
      ring
    show min (s + ((i + 1 : ℕ) : ℝ) * k) t - min (s + (i : ℝ) * k) t < δ
    linarith

/-! ## 2. Weyl scaling preserves a length domination -/

/-- **Weyl scaling preserves a length domination along a pair of paths.** Let `A = e^{ξ g}·A₁` and
`B = e^{ξ f}·B₀`. If `P, Q` are continuous on `[s, t]`, `A₁(Q a, Q b) ≤ len(P; B₀; [a, b])` for all
`a ≤ b` in `[s, t]`, and `g ∘ Q = f ∘ P` on `[s, t]`, then
`len(Q; A; [s, t]) ≤ len(P; B; [s, t])`. -/
theorem curveLength_weyl_transport_le {ξ : ℝ} {f g : C(ℂ, ℝ)} {A₁ B₀ : ContMetric}
    (A B : ContMetric)
    (hA : ∀ x y : ℂ, ENNReal.ofReal (A.1 (x, y)) = weylScale ξ g A₁ x y)
    (hB : ∀ x y : ℂ, ENNReal.ofReal (B.1 (x, y)) = weylScale ξ f B₀ x y)
    {P Q : ℝ → ℂ} {s t : ℝ} (hst : s ≤ t)
    (hP : ContinuousOn P (Icc s t)) (hQ : ContinuousOn Q (Icc s t))
    (hcomp : ∀ a ∈ Icc s t, ∀ b ∈ Icc s t, a ≤ b →
      edist (A₁.pt (Q a)) (A₁.pt (Q b)) ≤ curveLength (B₀.pt ∘ P) a b)
    (hgf : ∀ τ ∈ Icc s t, g (Q τ) = f (P τ)) :
    curveLength (A.pt ∘ Q) s t ≤ curveLength (B.pt ∘ P) s t := by
  -- the base lengths compare on every subinterval
  have hlen : ∀ a b : ℝ, s ≤ a → b ≤ t →
      curveLength (A₁.pt ∘ Q) a b ≤ curveLength (B₀.pt ∘ P) a b := by
    intro a b ha hb
    refine curveLength_le_of_edist_le fun x hx y hy hxy => ?_
    exact hcomp x ⟨ha.trans hx.1, hx.2.trans hb⟩ y ⟨ha.trans hy.1, hy.2.trans hb⟩ hxy
  -- the bound with the factor `e^{2ε}`
  have key : ∀ ε : ℝ, 0 < ε → curveLength (A.pt ∘ Q) s t ≤
      ENNReal.ofReal (Real.exp (2 * ε)) * curveLength (B.pt ∘ P) s t := by
    intro ε hε
    have hfc : Continuous fun x : ℂ => ξ * f x := continuous_const.mul f.continuous
    have huc : UniformContinuousOn ((fun x : ℂ => ξ * f x) ∘ P) (Icc s t) :=
      isCompact_Icc.uniformContinuousOn_of_continuous (hfc.comp_continuousOn hP)
    obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1 huc ε hε
    obtain ⟨n, u, hu, hu0, hun, humem, hstep⟩ := exists_partition_lt hst hδ
    rw [← hu0, ← hun, ← sum_curveLength_eq (A.pt ∘ Q) hu n,
      ← sum_curveLength_eq (B.pt ∘ P) hu n, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hi : u i ≤ u (i + 1) := hu (Nat.le_succ i)
    have hsub : Icc (u i) (u (i + 1)) ⊆ Icc s t := Icc_subset_Icc (humem i).1 (humem (i + 1)).2
    set c : ℝ := ξ * f (P (u i)) with hc
    -- on the piece, `ξ f ∘ P` stays within `ε` of `c`
    have hclose : ∀ τ ∈ Icc (u i) (u (i + 1)), c - ε < ξ * f (P τ) ∧ ξ * f (P τ) < c + ε := by
      intro τ hτ
      have hd : dist (u i) τ < δ := by
        rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hτ.1)]
        have := hstep i
        linarith [hτ.2]
      have h := hδ' (u i) (humem i) τ (hsub hτ) hd
      rw [Real.dist_eq] at h
      have h' := abs_lt.1 h
      simp only [Function.comp_apply] at h'
      constructor <;> linarith [h'.1, h'.2]
    -- upper bound on the `A`-length
    have h1 : curveLength (A.pt ∘ Q) (u i) (u (i + 1)) ≤
        ENNReal.ofReal (Real.exp (c + ε)) * curveLength (A₁.pt ∘ Q) (u i) (u (i + 1)) := by
      refine curveLength_weyl_le A hA hi
        ((ContMetric.continuous_pt A₁).comp_continuousOn (hQ.mono hsub))
        (V := Q '' Icc (u i) (u (i + 1))) (fun τ hτ => mem_image_of_mem Q hτ) ?_
      rintro _ ⟨τ, hτ, rfl⟩
      rw [hgf τ (hsub hτ)]
      exact (hclose τ hτ).2.le
    -- lower bound on the `B`-length
    have h2 : ENNReal.ofReal (Real.exp (c - ε)) * curveLength (B₀.pt ∘ P) (u i) (u (i + 1)) ≤
        curveLength (B.pt ∘ P) (u i) (u (i + 1)) := by
      refine le_curveLength_weyl B hB
        ((ContMetric.continuous_pt B₀).comp_continuousOn (hP.mono hsub))
        (V := {x : ℂ | c - ε < ξ * f x}) (isOpen_lt continuous_const hfc)
        (fun τ hτ => (hclose τ hτ).1) ?_
      exact fun x hx => le_of_lt hx
    have hexp : ENNReal.ofReal (Real.exp (c + ε)) =
        ENNReal.ofReal (Real.exp (2 * ε)) * ENNReal.ofReal (Real.exp (c - ε)) := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      ring
    calc curveLength (A.pt ∘ Q) (u i) (u (i + 1))
        ≤ ENNReal.ofReal (Real.exp (c + ε)) * curveLength (A₁.pt ∘ Q) (u i) (u (i + 1)) := h1
      _ ≤ ENNReal.ofReal (Real.exp (c + ε)) * curveLength (B₀.pt ∘ P) (u i) (u (i + 1)) := by
          gcongr
          exact hlen _ _ (humem i).1 (humem (i + 1)).2
      _ = ENNReal.ofReal (Real.exp (2 * ε)) *
            (ENNReal.ofReal (Real.exp (c - ε)) * curveLength (B₀.pt ∘ P) (u i) (u (i + 1))) := by
          rw [hexp, mul_assoc]
      _ ≤ ENNReal.ofReal (Real.exp (2 * ε)) * curveLength (B.pt ∘ P) (u i) (u (i + 1)) := by
          gcongr
  -- let `ε → 0`
  by_cases hfin : curveLength (B.pt ∘ P) s t = ⊤
  · rw [hfin]
    exact le_top
  have hcont : Continuous fun ε : ℝ => ENNReal.ofReal (Real.exp (2 * ε)) :=
    ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have h0 : Tendsto (fun ε : ℝ => ENNReal.ofReal (Real.exp (2 * ε))) (𝓝[>] 0) (𝓝 1) := by
    have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa only [mul_zero, Real.exp_zero, ENNReal.ofReal_one] using this
  have htend : Tendsto (fun ε : ℝ => ENNReal.ofReal (Real.exp (2 * ε)) *
      curveLength (B.pt ∘ P) s t) (𝓝[>] 0) (𝓝 (curveLength (B.pt ∘ P) s t)) := by
    simpa only [one_mul] using ENNReal.Tendsto.mul_const h0 (Or.inr hfin)
  exact ge_of_tendsto htend (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)

/-! ## 3. The pathwise reversal step -/

/-- **The pathwise reversal step** (CC0 D16). Let `A = e^{ξ g}·A₁` and `B = e^{ξ f}·B₀`, let
`IsConfNbhd ϕ W V` with a left inverse `ψ` of `ϕ` on `W`, and let `g = f ∘ ϕ` on `V`. If
`A₁(ψ u, ψ v; V) ≤ B₀(u, v; ϕ(V))` for all `u, v ∈ ϕ(V)`, then `A(z, w; V) ≤ B(ϕ z, ϕ w; ϕ(V))` for
all `z, w ∈ V`. -/
theorem internal_le_of_reverse {ξ : ℝ} {f g : C(ℂ, ℝ)} {A A₁ B B₀ : ContMetric}
    (hA : ∀ x y : ℂ, ENNReal.ofReal (A.1 (x, y)) = weylScale ξ g A₁ x y)
    (hB : ∀ x y : ℂ, ENNReal.ofReal (B.1 (x, y)) = weylScale ξ f B₀ x y)
    {ϕ ψ : ℂ → ℂ} {W V : Set ℂ} (hϕ : IsConfNbhd ϕ W V) (hψ : ∀ z ∈ W, ψ (ϕ z) = z)
    (hgf : ∀ x ∈ V, g x = f (ϕ x))
    (hle : ∀ u ∈ ϕ '' V, ∀ v ∈ ϕ '' V, A₁.internal V (ψ u) (ψ v) ≤ B₀.internal (ϕ '' V) u v)
    {z w : ℂ} (hz : z ∈ V) (hw : w ∈ V) :
    A.internal V z w ≤ B.internal (ϕ '' V) (ϕ z) (ϕ w) := by
  show A.internal V z w ≤ internalEDist (B.pt '' (ϕ '' V)) (B.pt (ϕ z)) (B.pt (ϕ w))
  unfold internalEDist
  refine le_iInf fun γ' => ?_
  obtain ⟨γ, hγU⟩ := γ'
  -- the path in `U = ϕ '' V`, as a map `ℝ → ℂ`
  set P : ℝ → ℂ := fun τ => B.unpt (γ.extend τ) with hPdef
  have hPc : Continuous P := B.continuous_unpt.comp γ.continuous_extend
  have hPU : ∀ τ, P τ ∈ ϕ '' V := fun τ =>
    B.mem_image_pt.1 (hγU (projIcc 0 1 zero_le_one τ))
  have hPW : ∀ τ, P τ ∈ ϕ '' W := fun τ => image_mono hϕ.subset (hPU τ)
  -- its pull-back to `V`
  set Q : ℝ → ℂ := fun τ => ψ (P τ) with hQdef
  have hψc : ContinuousOn ψ (ϕ '' W) :=
    continuousOn_leftInv hϕ.isOpen_W hϕ.differentiableOn hϕ.injOn hψ
  have hQc : Continuous Q := hψc.comp_continuous hPc hPW
  have hQV : ∀ τ, Q τ ∈ V := by
    intro τ
    obtain ⟨v, hv, hve⟩ := hPU τ
    show ψ (P τ) ∈ V
    rw [← hve, hψ v (hϕ.subset hv)]
    exact hv
  have hP0 : P 0 = ϕ z := by
    show B.unpt (γ.extend 0) = ϕ z
    rw [Path.extend_zero]
    rfl
  have hP1 : P 1 = ϕ w := by
    show B.unpt (γ.extend 1) = ϕ w
    rw [Path.extend_one]
    rfl
  have hQ0 : Q 0 = z := by
    show ψ (P 0) = z
    rw [hP0, hψ z (hϕ.subset hz)]
  have hQ1 : Q 1 = w := by
    show ψ (P 1) = w
    rw [hP1, hψ w (hϕ.subset hw)]
  -- the one-sided inequality along the path
  have hcomp : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, a ≤ b →
      edist (A₁.pt (Q a)) (A₁.pt (Q b)) ≤ curveLength (B₀.pt ∘ P) a b := by
    intro a _ b _ hab
    calc edist (A₁.pt (Q a)) (A₁.pt (Q b)) ≤ A₁.internal V (Q a) (Q b) :=
          edist_le_internalEDist _ _ _
      _ ≤ B₀.internal (ϕ '' V) (P a) (P b) := hle _ (hPU a) _ (hPU b)
      _ ≤ curveLength (B₀.pt ∘ P) a b :=
          internalEDist_le_curveLength hab
            ((ContMetric.continuous_pt B₀).comp_continuousOn hPc.continuousOn)
            fun τ _ => mem_image_of_mem B₀.pt (hPU τ)
  have hgf' : ∀ τ ∈ Icc (0 : ℝ) 1, g (Q τ) = f (P τ) := by
    intro τ _
    rw [hgf _ (hQV τ)]
    show f (ϕ (ψ (P τ))) = f (P τ)
    rw [apply_leftInv hψ (hPW τ)]
  have hlen := curveLength_weyl_transport_le A B hA hB zero_le_one hPc.continuousOn
    hQc.continuousOn hcomp hgf'
  calc A.internal V z w = internalEDist (A.pt '' V) (A.pt (Q 0)) (A.pt (Q 1)) := by
        rw [hQ0, hQ1]
        rfl
    _ ≤ curveLength (A.pt ∘ Q) 0 1 :=
        internalEDist_le_curveLength zero_le_one
          ((ContMetric.continuous_pt A).comp_continuousOn hQc.continuousOn)
          fun τ _ => mem_image_of_mem A.pt (hQV τ)
    _ ≤ curveLength (B.pt ∘ P) 0 1 := hlen
    _ = pathLength γ := rfl

end SmallGammaGeodesics.CC
