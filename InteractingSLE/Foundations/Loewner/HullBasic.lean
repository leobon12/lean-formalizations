import InteractingSLE.Foundations.Complex.RiemannMap

/-!
# Compact `ℍ`-hulls and mapping-out functions: definitions, filling, uniqueness

Design `planning/INFRA-GEO.md` §3–§4, packet GEO-HCAP-A (first part of
`InteractingSLE.Foundations.Loewner.Hull`, which collects the whole API). Carriers:
`QuantumZipper.H` for the upper half-plane, `SupercriticalConformalCovariance.IsConformalBijection`
for conformal maps.

## Main definitions

* `IsHPHull A`: `A` is a compact `ℍ`-hull (G. F. Lawler, *Conformally invariant processes in the
  plane*, AMS 2005 ([Law05]), §3.4): `A ⊆ ℍ` bounded, relatively closed in `ℍ`, `ℍ \ A` simply
  connected; `HPHull` is the subtype.
* `fillH A`: the filling in `ℍ` of a set `A`.
* `IsMapOut A g`: `g` is the mapping-out function of `A` (conformal bijection `ℍ \ A → ℍ` with
  `g z − z → 0` at `∞`).

## Main results

* `H_diff_fillH`: for bounded `A`, `ℍ \ fillH A` is the unbounded component of `ℍ \ closure A`;
* `isHPHull_fillH_of_isPreconnected`: the filling of a bounded `A` with `A ∪ {Im ≤ 0}`
  preconnected is a compact `ℍ`-hull. **Design correction:** the design's `isHPHull_fillH`
  (boundedness only) is false; `not_isHPHull_fillH_closedBall` is the counterexample (a closed disc
  inside `ℍ`);
* `IsMapOut.exists_norm_le`: properness, `‖g z‖ ≤ ‖z‖ + C`;
* `IsMapOut.eqOn`: uniqueness of the mapping-out function (`g₂ ∘ g₁⁻¹` is a real Möbius
  automorphism of `ℍ` fixing `∞` to first order, hence the identity).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper (H Hbar)

namespace InteractingSLE

/-! ### Definitions -/

/-- A **compact `ℍ`-hull** ([Law05] §3.4): `A ⊆ ℍ` bounded, relatively closed in `ℍ`, with
`ℍ \ A` simply connected. -/
def IsHPHull (A : Set ℂ) : Prop :=
  A ⊆ H ∧ Bornology.IsBounded A ∧ IsOpen (H \ A) ∧ IsSimplyConnected (H \ A)

/-- Compact `ℍ`-hulls, as a subtype (the carrier of `hcap`). -/
def HPHull : Type := {A : Set ℂ // IsHPHull A}

/-- The **filling** in `ℍ` of a set `A ⊆ ℍ̄` (Specification p. 3, "`K_t` is the filling of its
range"; p. 24, "take their filled hulls"): the points of `ℍ` in `closure A` or in a bounded
component of `ℍ \ closure A`. For bounded `A` its complement in `ℍ` is the unique unbounded
component of `ℍ \ closure A`. -/
def fillH (A : Set ℂ) : Set ℂ :=
  {z ∈ H | z ∈ closure A ∨ Bornology.IsBounded (connectedComponentIn (H \ closure A) z)}

/-- `g` is the **mapping-out function** of `A`: a conformal bijection `ℍ \ A → ℍ` with the
hydrodynamic normalization `g z − z → 0` as `z → ∞` (Specification (1.6); [Law05] Ch. 3). -/
def IsMapOut (A : Set ℂ) (g : ℂ → ℂ) : Prop :=
  IsConformalBijection g (H \ A) H ∧
    Tendsto (fun z => g z - z) (Bornology.cobounded ℂ ⊓ 𝓟 (H \ A)) (𝓝 0)

/-! ### Elementary facts -/

theorem isPreconnected_lowerHalf : IsPreconnected {z : ℂ | z.im ≤ 0} :=
  (convex_halfSpace_le (f := fun z : ℂ => z.im) (Complex.imLm.isLinear) 0).isPreconnected

theorem isClosed_lowerHalf : IsClosed {z : ℂ | z.im ≤ 0} :=
  isClosed_le continuous_im continuous_const

theorem not_isBounded_lowerHalf : ¬ Bornology.IsBounded {z : ℂ | z.im ≤ 0} := by
  intro h
  obtain ⟨R, hR⟩ := h.subset_closedBall 0
  have : ((R + 1 : ℝ) : ℂ) ∈ {z : ℂ | z.im ≤ 0} := by simp
  have h1 := hR this
  rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] at h1
  have := le_abs_self (R + 1)
  linarith

theorem compl_H : Hᶜ = {z : ℂ | z.im ≤ 0} := by
  ext z; simp [QuantumZipper.H, not_lt]

/-- The complement of `ℍ \ A` is `A ∪ {Im ≤ 0}`. -/
theorem compl_H_diff (A : Set ℂ) : (H \ A)ᶜ = A ∪ {z : ℂ | z.im ≤ 0} := by
  ext z
  constructor
  · intro h
    by_cases hz : z ∈ H
    · by_contra hA
      exact h ⟨hz, fun hzA => hA (Or.inl hzA)⟩
    · have hz' : ¬ (0 < z.im) := hz
      exact Or.inr (show z.im ≤ 0 from not_lt.1 hz')
  · rintro (h | h) ⟨hzH, hzA⟩
    · exact hzA h
    · exact absurd (show 0 < z.im from hzH) (not_lt.2 (show z.im ≤ 0 from h))

/-! ### The filling of a bounded set -/

section Fill

variable {C : Set ℂ} {R : ℝ}

/-- If `C ⊆ B(0, R)`, every point of `ℍ` outside `B(0, R)` lies in the component of `(R + 1) i`
in `ℍ \ C` (join it to the half-plane `{Im > R}` by a vertical ray). -/
theorem mem_connectedComponentIn_of_le_norm (hR : 0 < R) (hCR : C ⊆ ball 0 R) {z : ℂ}
    (hz : z ∈ H) (hzR : R ≤ ‖z‖) :
    z ∈ connectedComponentIn (H \ C) (((R + 1 : ℝ) : ℂ) * I) := by
  have hzim : 0 < z.im := hz
  set T : Set ℂ := ((fun t : ℝ => z + (t : ℂ) * I) '' Ici 0) ∪ {w : ℂ | R < w.im} with hTdef
  have hray : ∀ t : ℝ, 0 ≤ t → R ≤ ‖z + (t : ℂ) * I‖ := by
    intro t ht
    refine hzR.trans ?_
    have h1 : ‖z‖ ^ 2 ≤ ‖z + (t : ℂ) * I‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, normSq_apply, normSq_apply]
      simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
        add_im, mul_im, add_zero]
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1
  have hT : IsPreconnected T := by
    refine IsPreconnected.union (z + ((R + 1 : ℝ) : ℂ) * I) ⟨R + 1, ?_, rfl⟩ ?_
      (isPreconnected_Ici.image _ (by fun_prop)) ?_
    · show (0 : ℝ) ≤ R + 1; linarith
    · show R < (z + ((R + 1 : ℝ) : ℂ) * I).im
      simp; linarith
    · exact (convex_halfSpace_gt (f := fun w : ℂ => w.im) Complex.imLm.isLinear R).isPreconnected
  have hTF : T ⊆ H \ C := by
    rintro w (⟨t, ht, rfl⟩ | hw)
    · refine ⟨?_, fun hC => ?_⟩
      · show 0 < (z + (t : ℂ) * I).im
        simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
        exact add_pos_of_pos_of_nonneg hzim ht
      · have := mem_ball_zero_iff.1 (hCR hC)
        linarith [hray t ht]
    · have hw' : R < w.im := hw
      refine ⟨show 0 < w.im by linarith, fun hC => ?_⟩
      have h1 := mem_ball_zero_iff.1 (hCR hC)
      have h2 := Complex.abs_im_le_norm w
      linarith [le_abs_self w.im]
  have h0T : ((R + 1 : ℝ) : ℂ) * I ∈ T := Or.inr (by simp)
  have hzT : z ∈ T := Or.inl ⟨0, mem_Ici.2 le_rfl, by simp⟩
  exact hT.subset_connectedComponentIn h0T hTF hzT

/-- The half-plane `{Im > R}` lies in the component of `(R + 1) i`. -/
theorem setOf_lt_im_subset_connectedComponentIn (hR : 0 < R) (hCR : C ⊆ ball 0 R) :
    {w : ℂ | R < w.im} ⊆ connectedComponentIn (H \ C) (((R + 1 : ℝ) : ℂ) * I) := by
  intro w hw
  have hw' : R < w.im := hw
  refine mem_connectedComponentIn_of_le_norm hR hCR (show 0 < w.im by linarith) ?_
  linarith [Complex.abs_im_le_norm w, le_abs_self w.im]

theorem not_isBounded_setOf_lt_im (R : ℝ) : ¬ Bornology.IsBounded {w : ℂ | R < w.im} := by
  intro h
  obtain ⟨M, hM⟩ := h.subset_closedBall 0
  have hmem : ((max R M + 1 : ℝ) : ℂ) * I ∈ {w : ℂ | R < w.im} := by
    show R < (((max R M + 1 : ℝ) : ℂ) * I).im
    simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    linarith [le_max_left R M]
  have h1 := mem_closedBall_zero_iff.1 (hM hmem)
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at h1
  linarith [le_max_right R M, le_abs_self (max R M + 1)]

/-- An unbounded component of `ℍ \ C` is the component of `(R + 1) i`. -/
theorem connectedComponentIn_eq_of_not_isBounded (hR : 0 < R) (hCR : C ⊆ ball 0 R) {z : ℂ}
    (hb : ¬ Bornology.IsBounded (connectedComponentIn (H \ C) z)) :
    connectedComponentIn (H \ C) z =
      connectedComponentIn (H \ C) (((R + 1 : ℝ) : ℂ) * I) := by
  have hsub : ¬ connectedComponentIn (H \ C) z ⊆ ball 0 R := fun h =>
    hb (Metric.isBounded_ball.subset h)
  obtain ⟨w, hw, hwR⟩ := not_subset.1 hsub
  have hwF : w ∈ H \ C := connectedComponentIn_subset _ _ hw
  have hw0 := mem_connectedComponentIn_of_le_norm hR hCR hwF.1
    (not_lt.1 fun h => hwR (mem_ball_zero_iff.2 h))
  rw [connectedComponentIn_eq hw, ← connectedComponentIn_eq hw0]

theorem not_isBounded_connectedComponentIn_of_lt (hR : 0 < R) (hCR : C ⊆ ball 0 R) :
    ¬ Bornology.IsBounded (connectedComponentIn (H \ C) (((R + 1 : ℝ) : ℂ) * I)) := fun h =>
  not_isBounded_setOf_lt_im R (h.subset (setOf_lt_im_subset_connectedComponentIn hR hCR))

end Fill

section FillH

variable {A : Set ℂ} {R : ℝ}

/-- For bounded `A ⊆ B(0, R)`, `ℍ \ fillH A` is the unbounded component of `ℍ \ closure A`. -/
theorem H_diff_fillH (hR : 0 < R) (hAR : closure A ⊆ ball 0 R) :
    H \ fillH A = connectedComponentIn (H \ closure A) (((R + 1 : ℝ) : ℂ) * I) := by
  ext z
  constructor
  · rintro ⟨hz, hzf⟩
    have hzC : z ∉ closure A := fun h => hzf ⟨hz, Or.inl h⟩
    have hb : ¬ Bornology.IsBounded (connectedComponentIn (H \ closure A) z) := fun h =>
      hzf ⟨hz, Or.inr h⟩
    rw [← connectedComponentIn_eq_of_not_isBounded hR hAR hb]
    exact mem_connectedComponentIn ⟨hz, hzC⟩
  · intro hz
    have hzF : z ∈ H \ closure A := connectedComponentIn_subset _ _ hz
    refine ⟨hzF.1, fun hzf => ?_⟩
    rcases hzf.2 with h | h
    · exact hzF.2 h
    · rw [← connectedComponentIn_eq hz] at h
      exact not_isBounded_connectedComponentIn_of_lt hR hAR h

theorem fillH_subset_H (A : Set ℂ) : fillH A ⊆ H := fun _ hz => hz.1

theorem fillH_subset_ball (hR : 0 < R) (hAR : closure A ⊆ ball 0 R) : fillH A ⊆ ball 0 R := by
  intro z hz
  by_contra hzR
  have hzR' : R ≤ ‖z‖ := not_lt.1 fun h => hzR (mem_ball_zero_iff.2 h)
  have h0 := mem_connectedComponentIn_of_le_norm hR hAR hz.1 hzR'
  have : z ∈ H \ fillH A := by
    rw [H_diff_fillH hR hAR]; exact h0
  exact this.2 hz

theorem exists_closure_subset_ball (hA : Bornology.IsBounded A) :
    ∃ R, 0 < R ∧ closure A ⊆ ball 0 R := by
  obtain ⟨R, hR, hAR⟩ := hA.closure.subset_ball_lt 0 0
  exact ⟨R, hR, hAR⟩

/-- **The filling is a compact `ℍ`-hull** (corrected form of the design's `isHPHull_fillH`):
if `A` is bounded and `A ∪ {Im ≤ 0}` is preconnected (for instance, `A` is a connected set meeting
`ℝ`, such as the range of a curve started on `ℝ`, or a union of such sets), then `fillH A` is a
compact `ℍ`-hull. Without the connectedness hypothesis the statement is false
(`not_isHPHull_fillH_closedBall`). -/
theorem isHPHull_fillH_of_isPreconnected (hA : Bornology.IsBounded A)
    (hc : IsPreconnected (A ∪ {z : ℂ | z.im ≤ 0})) : IsHPHull (fillH A) := by
  obtain ⟨R, hR, hAR⟩ := exists_closure_subset_ball hA
  set z₀ : ℂ := ((R + 1 : ℝ) : ℂ) * I with hz₀def
  set U₀ := connectedComponentIn (H \ closure A) z₀ with hU₀def
  have hU : H \ fillH A = U₀ := H_diff_fillH hR hAR
  have hFo : IsOpen (H \ closure A) := QuantumZipper.isOpen_H.sdiff isClosed_closure
  have hz₀U : z₀ ∈ U₀ := setOf_lt_im_subset_connectedComponentIn hR hAR
    (show R < (((R + 1 : ℝ) : ℂ) * I).im by simp)
  have hz₀ : z₀ ∈ H \ closure A := connectedComponentIn_subset _ _ hz₀U
  have hUo : IsOpen U₀ := hFo.connectedComponentIn
  have hUc : IsConnected U₀ := isConnected_connectedComponentIn_iff.2 hz₀
  refine ⟨fillH_subset_H A, Metric.isBounded_ball.subset (fillH_subset_ball hR hAR), ?_, ?_⟩
  · rw [hU]; exact hUo
  rw [hU]
  refine isSimplyConnected_of_forall_not_isBounded hUo hUc fun a ha => ?_
  set L : Set ℂ := {z : ℂ | z.im ≤ 0} with hLdef
  set P : Set ℂ := closure A ∪ L with hPdef
  have hP : IsPreconnected P := by
    have := hc.closure
    rwa [closure_union, isClosed_lowerHalf.closure_eq] at this
  have hU₀sub : U₀ ⊆ H \ closure A := connectedComponentIn_subset _ _
  have hPU : P ⊆ U₀ᶜ := by
    rintro z (hz | hz) hzU
    · exact (hU₀sub hzU).2 hz
    · exact absurd (show 0 < z.im from (hU₀sub hzU).1) (not_lt.2 hz)
  -- a preconnected `S ⊆ U₀ᶜ` containing `a` and `L` makes the component unbounded
  have key : ∀ S : Set ℂ, IsPreconnected S → a ∈ S → S ⊆ U₀ᶜ → L ⊆ S →
      ¬ Bornology.IsBounded (connectedComponentIn U₀ᶜ a) := by
    intro S hS haS hSU hLS hb
    exact not_isBounded_lowerHalf
      (hb.subset (hLS.trans (hS.subset_connectedComponentIn haS hSU)))
  by_cases haP : a ∈ P
  · exact key P hP haP hPU subset_union_right
  · have haL : a ∉ L := fun h => haP (Or.inr h)
    have haC : a ∉ closure A := fun h => haP (Or.inl h)
    have haF : a ∈ H \ closure A := ⟨show 0 < a.im from not_le.1 haL, haC⟩
    set W := connectedComponentIn (H \ closure A) a with hWdef
    have hWU : W ⊆ U₀ᶜ := by
      intro w hwW hwU
      apply ha
      have h1 : W = connectedComponentIn (H \ closure A) w := connectedComponentIn_eq hwW
      have h2 : U₀ = connectedComponentIn (H \ closure A) w := connectedComponentIn_eq hwU
      rw [h2, ← h1]
      exact mem_connectedComponentIn haF
    have hcWU : closure W ⊆ U₀ᶜ := closure_minimal hWU hUo.isClosed_compl
    have hWc : IsPreconnected (closure W) := isPreconnected_connectedComponentIn.closure
    have haW : a ∈ closure W := subset_closure (mem_connectedComponentIn haF)
    obtain ⟨b, hbW, hbP⟩ : (closure W ∩ P).Nonempty := by
      by_contra hne
      rw [not_nonempty_iff_eq_empty] at hne
      have hsub : closure W ⊆ H \ closure A := by
        intro z hz
        have hzP : z ∉ P := fun h => (eq_empty_iff_forall_notMem.1 hne) z ⟨hz, h⟩
        exact ⟨show 0 < z.im from not_le.1 fun h => hzP (Or.inr h), fun h => hzP (Or.inl h)⟩
      have hcl : closure W ⊆ W := hWc.subset_connectedComponentIn haW hsub
      have hclo : IsClopen W :=
        ⟨closure_subset_iff_isClosed.1 hcl, hFo.connectedComponentIn⟩
      have huniv := hclo.eq_univ ⟨a, mem_connectedComponentIn haF⟩
      have h0 : (0 : ℂ) ∈ W := huniv ▸ mem_univ _
      exact absurd (show 0 < (0 : ℂ).im from (connectedComponentIn_subset _ _ h0).1) (by simp)
    exact key (closure W ∪ P) (hWc.union b hbW hbP hP) (Or.inl haW)
      (union_subset hcWU hPU) (subset_union_right.trans subset_union_right)

/-- **The design's `isHPHull_fillH` is false**: the filling of the closed disc `B̄(2i, 1)` (a
bounded set) is the disc itself, and `ℍ` minus a disc is not simply connected. -/
theorem not_isHPHull_fillH_closedBall : ¬ IsHPHull (fillH (closedBall (2 * I) 1)) := by
  set A : Set ℂ := closedBall (2 * I) 1 with hAdef
  rintro ⟨-, -, hUo, hsc⟩
  have hAc : closure A = A := isClosed_closedBall.closure_eq
  have h2I : (2 : ℂ) * I ∈ A := mem_closedBall_self zero_le_one
  have h2IH : (2 : ℂ) * I ∈ H := show (0 : ℝ) < ((2 : ℂ) * I).im by simp
  have h2If : (2 : ℂ) * I ∈ fillH A := ⟨h2IH, Or.inl (subset_closure h2I)⟩
  -- points of the filling have `Im ≥ 1`
  have hfill : ∀ z ∈ fillH A, 1 ≤ z.im := by
    intro z hz
    by_contra hlt
    rw [not_le] at hlt
    have hzA : z ∉ closure A := by
      rw [hAc]
      intro hzA
      have h1 : ‖z - 2 * I‖ ≤ 1 := by rw [← dist_eq_norm]; exact hzA
      have h2 := Complex.abs_im_le_norm (z - 2 * I)
      have h3 : (z - 2 * I).im = z.im - 2 := by simp
      rw [h3] at h2
      linarith [neg_abs_le (z.im - 2)]
    set T : Set ℂ := {w : ℂ | 0 < w.im} ∩ {w : ℂ | w.im < 1} with hTdef
    have hTc : IsPreconnected T :=
      ((convex_halfSpace_gt (f := fun w : ℂ => w.im) Complex.imLm.isLinear 0).inter
        (convex_halfSpace_lt (f := fun w : ℂ => w.im) Complex.imLm.isLinear 1)).isPreconnected
    have hTF : T ⊆ H \ closure A := by
      rintro w ⟨hw0, hw1⟩
      refine ⟨hw0, ?_⟩
      rw [hAc]
      intro hwA
      have h1 : ‖w - 2 * I‖ ≤ 1 := by rw [← dist_eq_norm]; exact hwA
      have h2 := Complex.abs_im_le_norm (w - 2 * I)
      have h3 : (w - 2 * I).im = w.im - 2 := by simp
      rw [h3] at h2
      have hw1' : w.im < 1 := hw1
      linarith [neg_abs_le (w.im - 2)]
    have hzT : z ∈ T := ⟨hz.1, hlt⟩
    have hTsub := hTc.subset_connectedComponentIn hzT hTF
    rcases hz.2 with h | h
    · exact hzA h
    · apply not_isBounded_setOf_lt_im (0 : ℝ)
      -- the strip is unbounded: it contains `x + i/2` for all real `x`
      have hstrip : ¬ Bornology.IsBounded T := by
        intro hb
        obtain ⟨M, hM⟩ := hb.subset_closedBall 0
        have hmem : ((|M| + 1 : ℝ) : ℂ) + (1 / 2 : ℂ) * I ∈ T := by
          refine ⟨show (0 : ℝ) < _ by simp, show _ < (1 : ℝ) by norm_num⟩
        have h1 := mem_closedBall_zero_iff.1 (hM hmem)
        have h2 := Complex.abs_re_le_norm (((|M| + 1 : ℝ) : ℂ) + (1 / 2 : ℂ) * I)
        have h3 : (((|M| + 1 : ℝ) : ℂ) + (1 / 2 : ℂ) * I).re = |M| + 1 := by simp
        rw [h3, abs_of_pos (by positivity)] at h2
        linarith [le_abs_self M]
      exact absurd (h.subset hTsub) hstrip
  have hcomp := not_isBounded_connectedComponentIn_compl_of_isSimplyConnected hUo hsc
    (a := 2 * I) (fun h => h.2 h2If)
  apply hcomp
  set Q := connectedComponentIn (H \ fillH A)ᶜ ((2 : ℂ) * I) with hQdef
  have hQ : IsPreconnected Q := isPreconnected_connectedComponentIn
  have hQsub : Q ⊆ (H \ fillH A)ᶜ := connectedComponentIn_subset _ _
  rw [compl_H_diff] at hQsub
  have hsplit : Q ⊆ {w : ℂ | 1 / 2 < w.im} ∪ {w : ℂ | w.im < 1 / 2} := by
    intro w hw
    rcases hQsub hw with h | h
    · exact Or.inl (show 1 / 2 < w.im by linarith [hfill w h])
    · exact Or.inr (show w.im < 1 / 2 by linarith [show w.im ≤ 0 from h])
  have hdisj : Disjoint {w : ℂ | 1 / 2 < w.im} {w : ℂ | w.im < 1 / 2} := by
    rw [Set.disjoint_left]
    intro w h1 h2
    exact lt_asymm (show 1 / 2 < w.im from h1) h2
  have h2IQ : (2 : ℂ) * I ∈ Q := mem_connectedComponentIn (fun h => h.2 h2If)
  rcases hQ.subset_or_subset (isOpen_lt continuous_const continuous_im)
      (isOpen_lt continuous_im continuous_const) hdisj hsplit with h | h
  · have hQf : Q ⊆ fillH A := by
      intro w hw
      rcases hQsub hw with h' | h'
      · exact h'
      · exact absurd (show 1 / 2 < w.im from h hw) (by linarith [show w.im ≤ 0 from h'])
    have hb : closure A ⊆ ball 0 4 := by
      rw [hAc]
      intro w hw
      rw [mem_ball_zero_iff]
      have h1 : ‖w - 2 * I‖ ≤ 1 := by rw [← dist_eq_norm]; exact hw
      have h2 : ‖w‖ ≤ ‖w - 2 * I‖ + ‖(2 : ℂ) * I‖ := by
        calc ‖w‖ = ‖(w - 2 * I) + 2 * I‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      have h3 : ‖(2 : ℂ) * I‖ = 2 := by simp
      linarith
    exact Metric.isBounded_ball.subset (hQf.trans (fillH_subset_ball (by norm_num) hb))
  · exact absurd (show ((2 : ℂ) * I).im < 1 / 2 from h h2IQ) (by simp; norm_num)

end FillH

/-! ### Mapping-out functions: properness and uniqueness -/

theorem eventually_cobounded_inf_principal_iff {S : Set ℂ} {P : ℂ → Prop} :
    (∀ᶠ z in Bornology.cobounded ℂ ⊓ 𝓟 S, P z) ↔ ∃ R, ∀ z ∈ S, R ≤ ‖z‖ → P z := by
  rw [eventually_inf_principal, Filter.hasBasis_cobounded_norm.eventually_iff]
  constructor
  · rintro ⟨R, -, hR⟩
    exact ⟨R, fun z hz hzR => hR hzR hz⟩
  · rintro ⟨R, hR⟩
    exact ⟨R, trivial, fun z hzR hz => hR z hz hzR⟩

theorem IsHPHull.isOpen {A : Set ℂ} (hA : IsHPHull A) : IsOpen (H \ A) := hA.2.2.1

theorem IsHPHull.isConnected {A : Set ℂ} (hA : IsHPHull A) : IsConnected (H \ A) :=
  hA.2.2.2.isPathConnected.isConnected

theorem IsHPHull.exists_subset_ball {A : Set ℂ} (hA : IsHPHull A) :
    ∃ R, 0 < R ∧ A ⊆ ball 0 R :=
  hA.2.1.subset_ball_lt 0 0

/-- A preconnected set covered by two disjoint open sets and meeting the second one lies in it. -/
private theorem subset_of_isPreconnected_of_inter {E U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : Disjoint U V) (hE : IsPreconnected E) (hEsub : E ⊆ U ∪ V) (hne : (E ∩ V).Nonempty) :
    E ⊆ V := by
  rcases hE.subset_or_subset hU hV hUV hEsub with h | h
  · obtain ⟨w, hwE, hwV⟩ := hne
    exact absurd hwV (Set.disjoint_left.1 hUV (h hwE))
  · exact h

/-- **Properness of mapping-out functions**: `‖g z‖ ≤ ‖z‖ + C` on `ℍ \ A`. (Near `∞` this is the
normalization; on the bounded part, the image avoids the three half-planes
`{Im > R + 1}`, `{Re > R + 1}`, `{Re < −R − 1}` of `ℍ`, which are connected and are reached from
`∞`.) -/
theorem IsMapOut.exists_norm_le {A : Set ℂ} {g : ℂ → ℂ} (hA : IsHPHull A) (hg : IsMapOut A g) :
    ∃ C, ∀ z ∈ H \ A, ‖g z‖ ≤ ‖z‖ + C := by
  obtain ⟨R₀, hR₀⟩ := eventually_cobounded_inf_principal_iff.1
    (hg.2.eventually (Metric.ball_mem_nhds (0 : ℂ) one_pos))
  obtain ⟨R₁, hR₁, hAR₁⟩ := hA.exists_subset_ball
  set R : ℝ := |R₀| + R₁ with hRdef
  have hR : 0 < R := by positivity
  have hRR₀ : R₀ ≤ R := by linarith [le_abs_self R₀]
  have hAR : A ⊆ ball 0 R := hAR₁.trans (ball_subset_ball (by linarith [abs_nonneg R₀]))
  set S := H \ A with hSdef
  have hS : IsOpen S := hA.isOpen
  have hnear : ∀ z ∈ S, R ≤ ‖z‖ → ‖g z - z‖ < 1 := fun z hz hzR => by
    simpa [dist_eq_norm] using hR₀ z hz (hRR₀.trans hzR)
  have hgd := hg.1.1
  have hinj := hg.1.2.injOn
  set I₀ : Set ℂ := S ∩ ball 0 R with hI₀
  set O : Set ℂ := H ∩ (closedBall 0 R)ᶜ with hO
  have hOS : O ⊆ S := fun z hz => ⟨hz.1, fun hzA => by
    have h1 := mem_ball_zero_iff.1 (hAR hzA)
    have h2 : z ∉ closedBall 0 R := hz.2
    rw [mem_closedBall_zero_iff, not_le] at h2
    linarith⟩
  have hIo : IsOpen (g '' I₀) := QuantumZipper.CA.isOpen_image_of_injOn hS hgd hinj
    (hS.inter isOpen_ball) inter_subset_left
  have hOo : IsOpen (g '' O) := QuantumZipper.CA.isOpen_image_of_injOn hS hgd hinj
    (QuantumZipper.isOpen_H.inter isClosed_closedBall.isOpen_compl) hOS
  have hdisj : Disjoint (g '' I₀) (g '' O) := by
    rw [Set.disjoint_left]
    rintro _ ⟨z, hz, rfl⟩ ⟨z', hz', hzz'⟩
    have := hinj (hOS hz') hz.1 hzz'
    subst this
    exact hz'.2 (ball_subset_closedBall hz.2)
  -- every point of `ℍ` of norm `≥ R + 1` is in `g '' I₀ ∪ g '' O`
  have hcover : ∀ w ∈ H, R + 1 ≤ ‖w‖ → w ∈ g '' I₀ ∪ g '' O := by
    intro w hw hwR
    obtain ⟨z, hz, rfl⟩ := hg.1.2.surjOn hw
    rcases lt_trichotomy ‖z‖ R with h | h | h
    · exact Or.inl ⟨z, ⟨hz, mem_ball_zero_iff.2 h⟩, rfl⟩
    · have h1 := hnear z hz h.ge
      have h2 : ‖g z‖ ≤ ‖g z - z‖ + ‖z‖ := by
        calc ‖g z‖ = ‖(g z - z) + z‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      linarith
    · refine Or.inr ⟨z, ⟨hz.1, ?_⟩, rfl⟩
      rw [mem_compl_iff, mem_closedBall_zero_iff, not_le]; exact h
  -- the three half-planes
  have hhalf : ∀ E : Set ℂ, Convex ℝ E → E ⊆ H → (∀ w ∈ E, R + 1 ≤ ‖w‖) →
      (∃ z ∈ O, g z ∈ E) → E ⊆ g '' O := by
    intro E hEc hEH hEn ⟨z, hzO, hzE⟩
    exact subset_of_isPreconnected_of_inter hIo hOo hdisj hEc.isPreconnected
      (fun w hw => hcover w (hEH hw) (hEn w hw)) ⟨g z, hzE, z, hzO, rfl⟩
  have hgz : ∀ z ∈ O, ‖g z - z‖ < 1 := fun z hz =>
    hnear z (hOS hz) (le_of_lt (by
      have h2 : z ∉ closedBall 0 R := hz.2
      rwa [mem_closedBall_zero_iff, not_le] at h2))
  have hre : ∀ z ∈ O, |(g z).re - z.re| < 1 := fun z hz => by
    have := Complex.abs_re_le_norm (g z - z); rw [sub_re] at this; linarith [hgz z hz]
  have him : ∀ z ∈ O, |(g z).im - z.im| < 1 := fun z hz => by
    have := Complex.abs_im_le_norm (g z - z); rw [sub_im] at this; linarith [hgz z hz]
  have hOmem : ∀ z : ℂ, 0 < z.im → R < ‖z‖ → z ∈ O := fun z h1 h2 =>
    ⟨h1, by rw [mem_compl_iff, mem_closedBall_zero_iff, not_le]; exact h2⟩
  have him_le : ∀ w : ℂ, w.im ≤ ‖w‖ := fun w => (le_abs_self _).trans (Complex.abs_im_le_norm w)
  have hre_le : ∀ w : ℂ, w.re ≤ ‖w‖ := fun w => (le_abs_self _).trans (Complex.abs_re_le_norm w)
  have hnre_le : ∀ w : ℂ, -w.re ≤ ‖w‖ := fun w =>
    (neg_le_abs _).trans (Complex.abs_re_le_norm w)
  -- `E₁ = {Im > R + 1}`
  have hE₁ : {w : ℂ | R + 1 < w.im} ⊆ g '' O := by
    refine hhalf _ (convex_halfSpace_gt (f := fun w : ℂ => w.im) Complex.imLm.isLinear _)
      (fun w hw => show 0 < w.im by have : R + 1 < w.im := hw; linarith)
      (fun w hw => by have : R + 1 < w.im := hw; linarith [him_le w]) ?_
    set z : ℂ := ((2 * R + 2 : ℝ) : ℂ) * I
    have hzim : z.im = 2 * R + 2 := by simp [z]
    have hzO : z ∈ O := hOmem z (by rw [hzim]; linarith) (by
      have : ‖z‖ = 2 * R + 2 := by
        simp only [z, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        exact abs_of_pos (by linarith)
      rw [this]; linarith)
    refine ⟨z, hzO, show R + 1 < (g z).im from ?_⟩
    have := him z hzO; rw [hzim] at this; linarith [neg_abs_le ((g z).im - (2 * R + 2))]
  -- `E₂ = {Im > 0, Re > R + 1}` and `E₃ = {Im > 0, Re < −R − 1}`
  have hE₂ : {w : ℂ | 0 < w.im ∧ R + 1 < w.re} ⊆ g '' O := by
    refine hhalf _ ((convex_halfSpace_gt (f := fun w : ℂ => w.im) Complex.imLm.isLinear 0).inter
      (convex_halfSpace_gt (f := fun w : ℂ => w.re) Complex.reLm.isLinear _))
      (fun w hw => hw.1) (fun w hw => by linarith [hw.2, hre_le w]) ?_
    set z : ℂ := ((2 * R + 2 : ℝ) : ℂ) + I
    have hzre : z.re = 2 * R + 2 := by simp [z]
    have hzim : z.im = 1 := by simp [z]
    have hzO : z ∈ O := hOmem z (by rw [hzim]; norm_num) (by
      have := Complex.abs_re_le_norm z; rw [hzre, abs_of_pos (by linarith)] at this; linarith)
    refine ⟨z, hzO, hg.1.2.mapsTo (hOS hzO), ?_⟩
    have := hre z hzO; rw [hzre] at this; linarith [neg_abs_le ((g z).re - (2 * R + 2))]
  have hE₃ : {w : ℂ | 0 < w.im ∧ w.re < -(R + 1)} ⊆ g '' O := by
    refine hhalf _ ((convex_halfSpace_gt (f := fun w : ℂ => w.im) Complex.imLm.isLinear 0).inter
      (convex_halfSpace_lt (f := fun w : ℂ => w.re) Complex.reLm.isLinear _))
      (fun w hw => hw.1) (fun w hw => by linarith [hw.2, hnre_le w]) ?_
    set z : ℂ := ((-(2 * R + 2) : ℝ) : ℂ) + I
    have hzre : z.re = -(2 * R + 2) := by simp [z]
    have hzim : z.im = 1 := by simp [z]
    have hzO : z ∈ O := hOmem z (by rw [hzim]; norm_num) (by
      have := Complex.abs_re_le_norm z
      rw [hzre, abs_of_neg (by linarith)] at this; linarith)
    refine ⟨z, hzO, hg.1.2.mapsTo (hOS hzO), ?_⟩
    have := hre z hzO; rw [hzre] at this; linarith [le_abs_self ((g z).re - -(2 * R + 2))]
  refine ⟨2 * R + 3, fun z hz => ?_⟩
  by_cases hzR : R ≤ ‖z‖
  · have h1 := hnear z hz hzR
    have h2 : ‖g z‖ ≤ ‖g z - z‖ + ‖z‖ := by
      calc ‖g z‖ = ‖(g z - z) + z‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    linarith
  · rw [not_le] at hzR
    have hzI : z ∈ I₀ := ⟨hz, mem_ball_zero_iff.2 hzR⟩
    have hnot : g z ∉ g '' O := fun h => Set.disjoint_left.1 hdisj ⟨z, hzI, rfl⟩ h
    have hgH : 0 < (g z).im := hg.1.2.mapsTo hz
    have h1 : (g z).im ≤ R + 1 := not_lt.1 fun h => hnot (hE₁ h)
    have h2 : (g z).re ≤ R + 1 := not_lt.1 fun h => hnot (hE₂ ⟨hgH, h⟩)
    have h3 : -(R + 1) ≤ (g z).re := not_lt.1 fun h => hnot (hE₃ ⟨hgH, h⟩)
    have h4 := Complex.norm_le_abs_re_add_abs_im (g z)
    rw [abs_of_pos hgH] at h4
    have h5 : |(g z).re| ≤ R + 1 := abs_le.2 ⟨h3, h2⟩
    linarith [norm_nonneg z]

/-- `y ↦ (y : ℂ)⁻¹` tends to `0` as `y → +∞`. -/
theorem tendsto_ofReal_inv_atTop : Tendsto (fun y : ℝ => ((y : ℂ))⁻¹) atTop (𝓝 0) := by
  have := (continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
  simpa [Function.comp_def] using this

/-- A real Möbius map `w ↦ (a w + b)/(c w + d)` (`ad − bc > 0`) with `m(iy) − iy → 0` as
`y → +∞` is the identity on `ℍ`. -/
theorem eqOn_id_of_tendsto_realMobius {a b c d : ℝ} (hdet : 0 < a * d - b * c)
    (hlim : Tendsto (fun y : ℝ => QuantumZipper.CA.realMobius a b c d ((y : ℂ) * I) - (y : ℂ) * I)
      atTop (𝓝 0)) :
    EqOn (QuantumZipper.CA.realMobius a b c d) id H := by
  set ε : ℝ → ℂ := fun y => QuantumZipper.CA.realMobius a b c d ((y : ℂ) * I) - (y : ℂ) * I
    with hεdef
  have hyH : ∀ y : ℝ, 0 < y → (y : ℂ) * I ∈ H := fun y hy => show 0 < ((y : ℂ) * I).im by simpa
  have hid : ∀ y : ℝ, 0 < y →
      ((y : ℂ) * I + ε y) * ((c : ℂ) * ((y : ℂ) * I) + d) = a * ((y : ℂ) * I) + b := by
    intro y hy
    have hden := QuantumZipper.CA.realMobius_denom_ne_zero hdet (hyH y hy)
    have h1 : (y : ℂ) * I + ε y = QuantumZipper.CA.realMobius a b c d ((y : ℂ) * I) := by
      simp only [hεdef]; ring
    rw [h1, QuantumZipper.CA.realMobius, div_mul_cancel₀ _ hden]
  clear_value ε
  have hpos : ∀ᶠ y : ℝ in atTop, 0 < y := eventually_gt_atTop 0
  have hinv := tendsto_ofReal_inv_atTop
  -- `c = 0`
  have hc : c = 0 := by
    have hT : Tendsto (fun y : ℝ => ((d : ℂ) + ε y * c - a) * I * ((y : ℂ))⁻¹ +
        (ε y * d - b) * (((y : ℂ))⁻¹) ^ 2) atTop (𝓝 0) := by
      have := ((((tendsto_const_nhds (x := (d : ℂ))).add (hlim.mul_const (c : ℂ))).sub
        (tendsto_const_nhds (x := (a : ℂ)))).mul_const I).mul hinv |>.add
        (((hlim.mul_const (d : ℂ)).sub (tendsto_const_nhds (x := (b : ℂ)))).mul (hinv.pow 2))
      simpa using this
    have hEq : (fun y : ℝ => ((d : ℂ) + ε y * c - a) * I * ((y : ℂ))⁻¹ +
        (ε y * d - b) * (((y : ℂ))⁻¹) ^ 2) =ᶠ[atTop] fun _ => (c : ℂ) := by
      filter_upwards [hpos] with y hy
      have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.2 hy.ne'
      have hP : (c : ℂ) * (y : ℂ) ^ 2 = ((d : ℂ) + ε y * c - a) * I * y + (ε y * d - b) := by
        linear_combination (-1 : ℂ) * hid y hy + ((c : ℂ) * (y : ℂ) ^ 2) * I_sq
      field_simp
      linear_combination (-1 : ℂ) * hP
    have := tendsto_nhds_unique (hT.congr' hEq) tendsto_const_nhds
    exact_mod_cast this.symm
  subst hc
  simp only [ofReal_zero, zero_mul, zero_add] at hid
  have hd : d ≠ 0 := by rintro rfl; simp at hdet
  -- `a = d`
  have had : a = d := by
    have hT : Tendsto (fun y : ℝ => ((b : ℂ) - ε y * d) * ((y : ℂ))⁻¹) atTop (𝓝 0) := by
      have := ((tendsto_const_nhds (x := (b : ℂ))).sub (hlim.mul_const (d : ℂ))).mul hinv
      simpa using this
    have hEq : (fun y : ℝ => ((b : ℂ) - ε y * d) * ((y : ℂ))⁻¹) =ᶠ[atTop]
        fun _ => ((d : ℂ) - a) * I := by
      filter_upwards [hpos] with y hy
      have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.2 hy.ne'
      have hP : ((d : ℂ) - a) * I * y = (b : ℂ) - ε y * d := by
        linear_combination hid y hy
      field_simp
      linear_combination -hP
    have h1 := tendsto_nhds_unique (hT.congr' hEq) tendsto_const_nhds
    have h2 : ((d : ℂ) - a) = 0 := by
      rcases mul_eq_zero.1 h1.symm with h | h
      · exact h
      · exact absurd h I_ne_zero
    have h3 : (d : ℂ) = a := sub_eq_zero.1 h2
    exact_mod_cast h3.symm
  subst had
  -- `b = 0`
  have hb : b = 0 := by
    have hT : Tendsto (fun y : ℝ => ε y * a) atTop (𝓝 0) := by
      simpa using hlim.mul_const (a : ℂ)
    have hEq : (fun y : ℝ => ε y * a) =ᶠ[atTop] fun _ => (b : ℂ) := by
      filter_upwards [hpos] with y hy
      linear_combination hid y hy
    have := tendsto_nhds_unique (hT.congr' hEq) tendsto_const_nhds
    exact_mod_cast this.symm
  subst hb
  intro w _
  have ha0 : (a : ℂ) ≠ 0 := ofReal_ne_zero.2 hd
  simp only [QuantumZipper.CA.realMobius, ofReal_zero, add_zero, zero_mul, zero_add, id]
  field_simp

/-- **Uniqueness of the mapping-out function** ([Law05] §3.4): two mapping-out functions of a
compact `ℍ`-hull agree on `ℍ \ A`. (`g₂ ∘ g₁⁻¹` is a conformal automorphism of `ℍ`, hence a real
Möbius map, and the normalization at `∞` forces the identity.) -/
theorem IsMapOut.eqOn {A : Set ℂ} {g₁ g₂ : ℂ → ℂ} (hA : IsHPHull A) (h₁ : IsMapOut A g₁)
    (h₂ : IsMapOut A g₂) : EqOn g₁ g₂ (H \ A) := by
  set S := H \ A with hSdef
  have hS : IsOpen S := hA.isOpen
  set e := QuantumZipper.CA.univalentOPH hS h₁.1.1 h₁.1.2.injOn with he
  have himg : g₁ '' S = H := h₁.1.2.image_eq
  have hsd : DifferentiableOn ℂ e.symm H := by
    have := QuantumZipper.CA.differentiableOn_univalentOPH_symm hS h₁.1.1 h₁.1.2.injOn
    rwa [himg] at this
  have hleft : ∀ z ∈ S, e.symm (g₁ z) = z := fun z hz =>
    QuantumZipper.CA.univalentOPH_symm_apply_apply hS h₁.1.1 h₁.1.2.injOn hz
  have hright : ∀ w ∈ H, g₁ (e.symm w) = w := fun w hw =>
    QuantumZipper.CA.univalentOPH_apply_symm_apply hS h₁.1.1 h₁.1.2.injOn (himg.symm ▸ hw)
  have hsS : ∀ w ∈ H, e.symm w ∈ S := fun w hw => by
    have : w ∈ e.target := by rw [QuantumZipper.CA.univalentOPH_target, himg]; exact hw
    exact e.map_target this
  set m : ℂ → ℂ := fun w => g₂ (e.symm w) with hmdef
  have hmd : DifferentiableOn ℂ m H := h₂.1.1.comp hsd hsS
  have hmb : BijOn m H H := by
    refine ⟨fun w hw => h₂.1.2.mapsTo (hsS w hw), fun w hw w' hw' hww' => ?_, fun v hv => ?_⟩
    · have := h₂.1.2.injOn (hsS w hw) (hsS w' hw') hww'
      rw [← hright w hw, ← hright w' hw', this]
    · obtain ⟨z, hz, rfl⟩ := h₂.1.2.surjOn hv
      exact ⟨g₁ z, h₁.1.2.mapsTo hz, by simp only [hmdef, hleft z hz]⟩
  obtain ⟨a, b, c, d, hdet, hm⟩ := QuantumZipper.CA.exists_realMobius_of_bijOn_H hmd hmb
  -- `e.symm (iy) → ∞` in `ℍ \ A`
  obtain ⟨C, hC⟩ := h₁.exists_norm_le hA
  have hyH : ∀ y : ℝ, 0 < y → (y : ℂ) * I ∈ H := fun y hy => show 0 < ((y : ℂ) * I).im by simpa
  have hφ : Tendsto (fun y : ℝ => e.symm ((y : ℂ) * I)) atTop (Bornology.cobounded ℂ ⊓ 𝓟 S) := by
    refine tendsto_inf.2 ⟨tendsto_norm_atTop_iff_cobounded.1 ?_, tendsto_principal.2 ?_⟩
    · refine tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_right atTop (-C) tendsto_id)
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
      have h1 := hC _ (hsS _ (hyH y hy))
      rw [hright _ (hyH y hy), norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hy] at h1
      simp only [id]
      linarith
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
      exact hsS _ (hyH y hy)
  have hlim : Tendsto (fun y : ℝ => QuantumZipper.CA.realMobius a b c d ((y : ℂ) * I) -
      (y : ℂ) * I) atTop (𝓝 0) := by
    have := (h₂.2.comp hφ).sub (h₁.2.comp hφ)
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    simp only [Function.comp_def]
    rw [← hm (hyH y hy), hright _ (hyH y hy)]
    ring
  have hid := eqOn_id_of_tendsto_realMobius hdet hlim
  intro z hz
  have h1 := hm (h₁.1.2.mapsTo hz)
  rw [hid (h₁.1.2.mapsTo hz)] at h1
  simp only [hmdef, hleft z hz, id] at h1
  exact h1.symm

end InteractingSLE
