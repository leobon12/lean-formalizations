/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ChartMeasHull
import InteractingSLE.Spec.ZhanGT4.DualA15CofinalHull

/-!
# Zhan's A.1.5: dyadic enclosures of two disjoint compact prefixes

Packet PROVE-ZHAN-GT4-A15F. Source: Astra, *Follow-up proofs*, §A.1.3 (L300–L304: "Choose deterministic disjoint closed
hull enclosures `H₁`, `H₂`, each containing a relative neighborhood of its source, with positive separation from the
other enclosure and all nonseed finite force marks. Choose the enclosures from a countable family of polygonal crosscut
hulls") and §A.1.5 (L423: "Any pair of disjoint compact prefixes is contained in a member of the countable enclosure
family"); R38.

The enclosures are fillings of finite unions of closed dyadic squares: `encl₁ n I = fill(⋃_{k ∈ I} Q_{n,k})` for the
curve started at `0`, and `encl₂ x₂ n I = fill(x₂ + ⋃_{k ∈ I} Q_{n,k})` (the grid translated to the source `x₂`, so
that the source is a grid vertex). A compact set `C` is approximated from outside by its dyadic covers `C_n`; the
closures of their fillings shrink into `Ĉ = C ∪ closure(fill C)`:

* **`notMem_closure_fillH_dyadicCover`**: a point outside `Ĉ` is eventually outside `closure (fill C_n)` (a half-disc
  around it lies in the unbounded component of `ℍ \ C_n` once `C_n` is close to `C`);
* `exists_disjoint_of_antitone`: two decreasing sequences of compact sets with disjoint intersections are eventually
  disjoint;
* `ball_zero_subset_dyadicCover`: a dyadic cover of a set containing `0` contains the ball of radius `2⁻ⁿ` at `0`;
* `fillH_closure_union_real`: for a compact `ℍ`-hull `A` (a Loewner hull), `fill(closure A ∪ {x}) = A`, so
  `Ĉ = closure A ∪ {x}` for the prefix `C = closure A ∪ {x}` of a curve started at `x`.

**`exists_goodEncl`**: two compact sets `C₁ ∋ 0`, `C₂ ∋ x₂` (each preconnected with the lower half-plane) with
`Ĉ₁ ∩ Ĉ₂ = ∅` and no mark in `Ĉ₁ ∪ Ĉ₂` lie in an enclosure pair of the countable family that is good (`GoodEncl`:
both fillings are compact `ℍ`-hulls, `2δ`-separated, avoiding a ball of radius `2d` around a rational protected point
`q ∈ (0, x₂)` and around every mark, and containing relative neighbourhoods of the sources), with rational `δ, q, d`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H fwdHull)
open Restart (dyadicSquare dyadicIdx dyadicCover lowerHalf)

/-! ### The fillings of the dyadic covers shrink to `C ∪ closure (fill C)` -/

/-- **A point outside `C ∪ closure (fill C)` is eventually outside the closures of the fillings of the dyadic
covers.** -/
theorem notMem_closure_fillH_dyadicCover {K : Set ℂ} (hK : IsCompact K) {x : ℂ}
    (hx : x ∉ K ∪ closure (fillH K)) : ∀ᶠ n in atTop, x ∉ closure (fillH (dyadicCover n K)) := by
  have hUo : IsOpen (K ∪ closure (fillH K))ᶜ := (hK.isClosed.union isClosed_closure).isOpen_compl
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hUo x hx
  have hnear : ∀ n, 2 / (2 : ℝ) ^ n < ε / 2 → ∀ z ∈ ball x (ε / 2), z ∉ dyadicCover n K := by
    intro n hn z hz hzD
    obtain ⟨w, hwK, hzw⟩ := Restart.exists_mem_norm_sub_le_of_mem_dyadicCover hzD
    have hxw : w ∈ ball x ε := by
      rw [mem_ball, dist_eq_norm] at hz ⊢
      calc ‖w - x‖ = ‖(z - x) - (z - w)‖ := by ring_nf
        _ ≤ ‖z - x‖ + ‖z - w‖ := norm_sub_le _ _
        _ < ε := by linarith
    exact hεU hxw (Or.inl hwK)
  obtain ⟨n₀, hn₀⟩ := Restart.exists_lt_two_div_pow (half_pos hε)
  have hev : ∀ᶠ n in atTop, 2 / (2 : ℝ) ^ n < ε / 2 := by
    filter_upwards [eventually_ge_atTop n₀] with n hn
    refine lt_of_le_of_lt ?_ hn₀
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_right₀ (by norm_num) hn)
  by_cases hO : (ball x (ε / 2) ∩ H).Nonempty
  · obtain ⟨y, hyb, hyH⟩ := hO
    have hyF : y ∈ H \ fillH K := ⟨hyH, fun h => hεU (ball_subset_ball (half_le_self hε.le) hyb)
      (Or.inr (subset_closure h))⟩
    filter_upwards [Restart.eventually_mem_H_diff_fillH_dyadicCover hK hyF, hev] with n hyn hn
    have hDc : IsClosed (dyadicCover n K) := (Restart.isCompact_dyadicCover hK.isBounded n).isClosed
    obtain ⟨R, hR, hRD⟩ := exists_closure_subset_ball (Restart.isCompact_dyadicCover hK.isBounded n).isBounded
    have hcomp := H_diff_fillH hR hRD
    have hOF : ball x (ε / 2) ∩ H ⊆ H \ closure (dyadicCover n K) := fun z hz =>
      ⟨hz.2, by rw [hDc.closure_eq]; exact hnear n hn z hz.1⟩
    have hOc : IsPreconnected (ball x (ε / 2) ∩ H) :=
      ((convex_ball x (ε / 2)).inter (convex_halfSpace_gt (f := fun z : ℂ => z.im)
        Complex.imLm.isLinear 0)).isPreconnected
    have hsub : ball x (ε / 2) ∩ H ⊆ H \ fillH (dyadicCover n K) := by
      have hy' : y ∈ connectedComponentIn (H \ closure (dyadicCover n K)) (((R + 1 : ℝ) : ℂ) * Complex.I) := by
        rw [← hcomp]; exact hyn
      rw [hcomp, connectedComponentIn_eq hy']
      exact hOc.subset_connectedComponentIn ⟨hyb, hyH⟩ hOF
    intro hxcl
    obtain ⟨z, hzF, hzx⟩ := Metric.mem_closure_iff.1 hxcl (ε / 2) (half_pos hε)
    have hzb : z ∈ ball x (ε / 2) := by rw [mem_ball, dist_comm]; exact hzx
    exact (hsub ⟨hzb, hzF.1⟩).2 hzF
  · refine Eventually.of_forall fun n hxcl => hO ?_
    obtain ⟨z, hzF, hzx⟩ := Metric.mem_closure_iff.1 hxcl (ε / 2) (half_pos hε)
    exact ⟨z, by rw [mem_ball, dist_comm]; exact hzx, hzF.1⟩

/-- **Two decreasing sequences of compact sets with disjoint intersections are eventually disjoint.** -/
theorem exists_disjoint_of_antitone {X Y : ℕ → Set ℂ} (hX : Antitone X) (hY : Antitone Y)
    (hXc : ∀ n, IsCompact (X n)) (hYc : ∀ n, IsCompact (Y n))
    (h : ∀ x, (∀ n, x ∈ X n) → (∀ n, x ∈ Y n) → False) : ∃ n, Disjoint (X n) (Y n) := by
  by_contra hne
  push Not at hne
  have hne' : ∀ n, (X n ∩ Y n).Nonempty := fun n => not_disjoint_iff_nonempty_inter.1 (hne n)
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed (fun n => X n ∩ Y n)
    (fun n => inter_subset_inter (hX (Nat.le_succ n)) (hY (Nat.le_succ n))) hne'
    ((hXc 0).inter_right (hYc 0).isClosed) fun n => (hXc n).isClosed.inter (hYc n).isClosed
  rw [mem_iInter] at hx
  exact h x (fun n => (hx n).1) fun n => (hx n).2

/-- A dyadic cover of a set containing `0` contains the ball of radius `2⁻ⁿ` around `0`. -/
theorem ball_zero_subset_dyadicCover {K : Set ℂ} (h0 : (0 : ℂ) ∈ K) (n : ℕ) :
    ball (0 : ℂ) (1 / 2 ^ n) ⊆ dyadicCover n K := by
  intro z hz
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  rw [mem_ball_zero_iff] at hz
  have hre : |(2 : ℝ) ^ n * z.re| < 1 := by
    rw [abs_mul, abs_of_pos hp]
    calc 2 ^ n * |z.re| ≤ 2 ^ n * ‖z‖ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm z) hp.le
      _ < 2 ^ n * (1 / 2 ^ n) := mul_lt_mul_of_pos_left hz hp
      _ = 1 := by field_simp
  have him : |(2 : ℝ) ^ n * z.im| < 1 := by
    rw [abs_mul, abs_of_pos hp]
    calc 2 ^ n * |z.im| ≤ 2 ^ n * ‖z‖ := mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm z) hp.le
      _ < 2 ^ n * (1 / 2 ^ n) := mul_lt_mul_of_pos_left hz hp
      _ = 1 := by field_simp
  have key : ∀ y : ℝ, |y| < 1 → ((⌊y⌋ : ℤ) : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ ((⌊y⌋ : ℤ) : ℝ) + 1 := by
    intro y hy
    rw [abs_lt] at hy
    have h1 : ((⌊y⌋ : ℤ) : ℝ) ≤ y := Int.floor_le y
    have h2 : y < ((⌊y⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one y
    have h3 : ⌊y⌋ ≤ 0 := by
      have : ((⌊y⌋ : ℤ) : ℝ) < 1 := by linarith
      exact_mod_cast Int.lt_add_one_iff.1 (by exact_mod_cast this)
    have h4 : (-1 : ℤ) ≤ ⌊y⌋ := by
      have h5 : ((-2 : ℤ) : ℝ) < ((⌊y⌋ : ℤ) : ℝ) := by push_cast; linarith
      have := Int.cast_lt.1 h5
      omega
    have h6 : ((-1 : ℤ) : ℝ) ≤ ((⌊y⌋ : ℤ) : ℝ) := Int.cast_le.2 h4
    push_cast at h6
    refine ⟨by exact_mod_cast h3, by linarith⟩
  have h0Q : (0 : ℂ) ∈ dyadicSquare n (Restart.dyadicIndexOf n z) := by
    obtain ⟨a1, a2⟩ := key _ hre
    obtain ⟨b1, b2⟩ := key _ him
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Restart.dyadicIndexOf, Complex.zero_re, Complex.zero_im, mul_zero] <;>
      assumption
  exact mem_biUnion (show Restart.dyadicIndexOf n z ∈ dyadicIdx n K from ⟨0, h0Q, h0⟩)
    (Restart.mem_dyadicSquare_indexOf n z)

/-! ### Translation along `ℝ` -/

/-- The filling commutes with real translations. -/
theorem fillH_image_add (x : ℝ) (A : Set ℂ) :
    fillH ((fun z : ℂ => z + x) '' A) = (fun z : ℂ => z + x) '' fillH A := by
  have h := fillH_image_affHomeo (r := 1) one_pos (x := x) A
  have e : ⇑(affHomeo 1 one_pos x) = fun z : ℂ => z + x := by
    rw [coe_affHomeo]; funext z; simp
  rwa [e] at h

/-! ### The filling of a Loewner prefix -/

/-- For a compact `ℍ`-hull `A` and a real point `x`, `fill(closure A ∪ {x}) = A`. -/
theorem fillH_closure_union_real {A : Set ℂ} (hA : IsHPHull A) (x : ℝ) :
    fillH (closure A ∪ {(x : ℂ)}) = A := by
  have hcl : closure (closure A ∪ {(x : ℂ)}) = closure A ∪ {(x : ℂ)} :=
    (isClosed_closure.union isClosed_singleton).closure_eq
  have hxH : (x : ℂ) ∉ H := fun h => by
    have : 0 < ((x : ℂ)).im := h
    simp at this
  have hdiff : H \ (closure A ∪ {(x : ℂ)}) = H \ closure A := by
    ext z
    constructor
    · rintro ⟨hz, hz'⟩
      exact ⟨hz, fun h => hz' (Or.inl h)⟩
    · rintro ⟨hz, hz'⟩
      refine ⟨hz, ?_⟩
      rintro (h | h)
      · exact hz' h
      · rw [mem_singleton_iff] at h
        exact hxH (h ▸ hz)
  calc fillH (closure A ∪ {(x : ℂ)}) = fillH A := by
        ext z
        simp only [fillH, mem_ofPred_eq, hcl, hdiff]
        refine and_congr_right fun hz => or_congr_left ⟨fun h => ?_, fun h => Or.inl h⟩
        rcases h with h | h
        · exact h
        · rw [mem_singleton_iff] at h
          exact absurd (h ▸ hz) hxH
    _ = A := hA.fillH_eq

/-- Compact and closed disjoint sets are uniformly separated. -/
theorem exists_pos_le_norm_sub_of_disjoint {X Y : Set ℂ} (hX : IsCompact X) (hY : IsClosed Y) (hXY : Disjoint X Y) :
    ∃ δ > 0, ∀ a ∈ Y, ∀ z ∈ X, δ ≤ ‖a - z‖ := by
  obtain ⟨δ, hδ, hdis⟩ := hXY.exists_thickenings hX hY
  refine ⟨δ, hδ, fun a ha z hz => not_lt.1 fun hlt => Set.disjoint_left.1 hdis
    (mem_thickening_iff.2 ⟨z, hz, by rw [dist_eq_norm]; exact hlt⟩) (self_subset_thickening hδ Y ha)⟩

/-- The translated form of `notMem_closure_fillH_dyadicCover` (the grid moved to `x₂`). -/
theorem notMem_closure_fillH_dyadicCover_add {K : Set ℂ} (hK : IsCompact K) (x₂ : ℝ) {x : ℂ}
    (hx : x ∉ (fun z : ℂ => z + x₂) '' K ∪ closure (fillH ((fun z : ℂ => z + x₂) '' K))) :
    ∀ᶠ n in atTop, x ∉ closure (fillH ((fun z : ℂ => z + x₂) '' dyadicCover n K)) := by
  set e := Homeomorph.addRight (x₂ : ℂ) with he
  have hcoe : ⇑e = fun z : ℂ => z + x₂ := rfl
  have hmem : ∀ S : Set ℂ, x ∈ (fun z : ℂ => z + x₂) '' S ↔ x - x₂ ∈ S := fun S => by
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
    · intro h
      exact ⟨x - x₂, h, by ring⟩
  have hx' : x - x₂ ∉ K ∪ closure (fillH K) := by
    rintro (h | h)
    · exact hx (Or.inl ((hmem K).2 h))
    · refine hx (Or.inr ?_)
      rw [fillH_image_add, ← hcoe, ← e.image_closure, hcoe]
      exact (hmem _).2 h
  filter_upwards [notMem_closure_fillH_dyadicCover hK hx'] with n hn hxn
  rw [fillH_image_add, ← hcoe, ← e.image_closure, hcoe] at hxn
  exact hn ((hmem _).1 hxn)

/-! ### The countable family of enclosure pairs -/

/-- An index of the enclosure family: the dyadic level, the squares of curve `1`, the squares of curve `2` (in the
grid translated to `x₂`), the cap of the exit times, and rational `δ` (separation), `q` (protected point), `d`
(protection radius). -/
abbrev CofIdx : Type := ℕ × Finset (ℤ × ℤ) × Finset (ℤ × ℤ) × ℕ × ℚ × ℚ × ℚ

/-- The union of the level-`n` dyadic squares indexed by `I`. -/
def sqUnion (n : ℕ) (I : Finset (ℤ × ℤ)) : Set ℂ := ⋃ k ∈ I, dyadicSquare n k

namespace CofIdx

/-- The enclosure of curve `1` (started at `0`). -/
def encl₁ (i : CofIdx) : Set ℂ := fillH (sqUnion i.1 i.2.1)

/-- The enclosure of curve `2` (started at `x₂`): the filling of the squares translated by `x₂`. -/
def encl₂ (x₂ : ℝ) (i : CofIdx) : Set ℂ := fillH ((fun z : ℂ => z + x₂) '' sqUnion i.1 i.2.2.1)

/-- The cap of the exit times. -/
def cap (i : CofIdx) : ℝ≥0 := (i.2.2.2.1 : ℝ≥0)

/-- The separation parameter `δ`. -/
def sep (i : CofIdx) : ℝ := (i.2.2.2.2.1 : ℝ)

/-- The protected point `q`. -/
def prot (i : CofIdx) : ℝ := (i.2.2.2.2.2.1 : ℝ)

/-- The protection radius `d`. -/
def rad (i : CofIdx) : ℝ := (i.2.2.2.2.2.2 : ℝ)

end CofIdx

/-- **A good enclosure pair** for the configuration (`x₂`, marks `p`): both fillings are compact `ℍ`-hulls (the square
unions are preconnected with the lower half-plane), `2δ`-separated, at distance `2d` from the protected point
`0 < q < x₂` and from every mark, and containing relative neighbourhoods of the two sources. -/
structure GoodEncl {nm : ℕ} (x₂ : ℝ) (p : Fin nm → ℝ) (i : CofIdx) : Prop where
  conn₁ : IsPreconnected (sqUnion i.1 i.2.1 ∪ lowerHalf)
  conn₂ : IsPreconnected ((fun z : ℂ => z + x₂) '' sqUnion i.1 i.2.2.1 ∪ lowerHalf)
  cap_pos : 0 < i.cap
  sep_pos : 0 < i.sep
  sep : ∀ a ∈ i.encl₂ x₂, ∀ z ∈ i.encl₁, 2 * i.sep ≤ ‖a - z‖
  rad_pos : 0 < i.rad
  prot_pos : 0 < i.prot
  prot_lt : i.prot < x₂
  protH : Disjoint (ball (i.prot : ℂ) (2 * i.rad)) (i.encl₁ ∪ i.encl₂ x₂)
  markH : ∀ m, Disjoint (ball (p m : ℂ) (2 * i.rad)) (i.encl₁ ∪ i.encl₂ x₂)
  nbhd₁ : ∃ ε > 0, ball (0 : ℂ) ε ∩ H ⊆ i.encl₁
  nbhd₂ : ∃ ε > 0, ball (x₂ : ℂ) ε ∩ H ⊆ i.encl₂ x₂

theorem isCompact_sqUnion (n : ℕ) (I : Finset (ℤ × ℤ)) : IsCompact (sqUnion n I) :=
  I.finite_toSet.isCompact_biUnion fun k _ => Restart.isCompact_dyadicSquare n k

namespace GoodEncl

variable {nm : ℕ} {x₂ : ℝ} {p : Fin nm → ℝ} {i : CofIdx}

theorem isHPHull₁ (h : GoodEncl x₂ p i) : IsHPHull i.encl₁ :=
  isHPHull_fillH_of_isPreconnected (isCompact_sqUnion _ _).isBounded h.conn₁

theorem isHPHull₂ (h : GoodEncl x₂ p i) : IsHPHull (i.encl₂ x₂) :=
  isHPHull_fillH_of_isPreconnected
    (((isCompact_sqUnion _ _).image (continuous_id.add continuous_const)).isBounded) h.conn₂

theorem mem_closure_encl₂ (h : GoodEncl x₂ p i) : (x₂ : ℂ) ∈ closure (i.encl₂ x₂) := by
  obtain ⟨ε, hε, hsub⟩ := h.nbhd₂
  rw [Metric.mem_closure_iff]
  intro r hr
  refine ⟨(x₂ : ℂ) + ((min ε r / 2 : ℝ) : ℂ) * Complex.I, hsub ⟨?_, ?_⟩, ?_⟩
  · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith [min_le_left ε r]
  · show 0 < ((x₂ : ℂ) + ((min ε r / 2 : ℝ) : ℂ) * Complex.I).im
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.I_re, mul_zero, add_zero, zero_add]
    positivity
  · rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith [min_le_right ε r]

theorem zero_mem_closure_encl₁ (h : GoodEncl x₂ p i) : (0 : ℂ) ∈ closure i.encl₁ := by
  obtain ⟨ε, hε, hsub⟩ := h.nbhd₁
  rw [Metric.mem_closure_iff]
  intro r hr
  refine ⟨((min ε r / 2 : ℝ) : ℂ) * Complex.I, hsub ⟨?_, ?_⟩, ?_⟩
  · rw [mem_ball, dist_eq_norm, sub_zero, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith [min_le_left ε r]
  · show 0 < (((min ε r / 2 : ℝ) : ℂ) * Complex.I).im
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re,
      mul_zero, add_zero]
    positivity
  · rw [dist_eq_norm, zero_sub, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith [min_le_right ε r]

/-- The closures of the two enclosures of a good pair are `2δ`-separated. -/
theorem sep_closure (h : GoodEncl x₂ p i) :
    ∀ a ∈ closure (i.encl₂ x₂), ∀ z ∈ closure i.encl₁, 2 * i.sep ≤ ‖a - z‖ := by
  have hcl : IsClosed {w : ℂ × ℂ | 2 * i.sep ≤ ‖w.1 - w.2‖} :=
    isClosed_le continuous_const (continuous_fst.sub continuous_snd).norm
  have hsub : i.encl₂ x₂ ×ˢ i.encl₁ ⊆ {w : ℂ × ℂ | 2 * i.sep ≤ ‖w.1 - w.2‖} := fun w hw => h.sep _ hw.1 _ hw.2
  intro a ha z hz
  have : (a, z) ∈ closure (i.encl₂ x₂ ×ˢ i.encl₁) := by rw [closure_prod_eq]; exact ⟨ha, hz⟩
  exact hcl.closure_subset_iff.2 hsub this

/-- The closures of the two enclosures of a good pair are disjoint. -/
theorem disjoint_closure (h : GoodEncl x₂ p i) : Disjoint (closure i.encl₁) (closure (i.encl₂ x₂)) :=
  Set.disjoint_left.2 fun z hz₁ hz₂ => by
    have := h.sep_closure z hz₂ z hz₁
    rw [sub_self, norm_zero] at this
    linarith [h.sep_pos]

/-- No mark lies in the closure of either enclosure of a good pair. -/
theorem mark_notMem_closure (h : GoodEncl x₂ p i) (m : Fin nm) :
    (p m : ℂ) ∉ closure i.encl₁ ∪ closure (i.encl₂ x₂) := by
  have hd := (h.markH m).closure_right isOpen_ball
  rw [closure_union] at hd
  exact fun hm => Set.disjoint_left.1 hd (mem_ball_self (by linarith [h.rad_pos])) hm

end GoodEncl

/-- The lower half-plane is invariant under real translations. -/
theorem image_add_lowerHalf (c : ℝ) : (fun z : ℂ => z + c) '' lowerHalf = lowerHalf := by
  ext z
  simp only [mem_image, Restart.lowerHalf, mem_ofPred_eq]
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro hz
    exact ⟨z - c, by simpa using hz, by ring⟩

/-- **Two compact prefixes with disjoint fill-closures lie in a good enclosure pair of the family**, with any
prescribed positive cap. -/
theorem exists_goodEncl {nm : ℕ} {x₂ : ℝ} (hx₂ : 0 < x₂) {p : Fin nm → ℝ} {C₁ C₂ : Set ℂ} (hC₁ : IsCompact C₁)
    (hC₂ : IsCompact C₂) (h0 : (0 : ℂ) ∈ C₁) (hx : (x₂ : ℂ) ∈ C₂) (hc₁ : IsPreconnected (C₁ ∪ lowerHalf))
    (hc₂ : IsPreconnected (C₂ ∪ lowerHalf))
    (hdisj : Disjoint (C₁ ∪ closure (fillH C₁)) (C₂ ∪ closure (fillH C₂)))
    (hp : ∀ m, (p m : ℂ) ∉ (C₁ ∪ closure (fillH C₁)) ∪ (C₂ ∪ closure (fillH C₂))) (N : ℕ) (hN : 0 < N) :
    ∃ i : CofIdx, GoodEncl x₂ p i ∧ i.cap = N ∧ C₁ ∩ H ⊆ i.encl₁ ∧ C₂ ∩ H ⊆ i.encl₂ x₂ := by
  set C₂' : Set ℂ := (fun z : ℂ => z - x₂) '' C₂ with hC₂'
  have hC₂'c : IsCompact C₂' := hC₂.image (continuous_id.sub continuous_const)
  have heC₂' : (fun z : ℂ => z + x₂) '' C₂' = C₂ := by
    rw [hC₂', image_image]
    simp
  have hmemC₂' : ∀ z, z ∈ C₂ → z - x₂ ∈ C₂' := fun z hz => ⟨z, hz, rfl⟩
  have h0' : (0 : ℂ) ∈ C₂' := by simpa using hmemC₂' _ hx
  have hĈ₁ : IsClosed (C₁ ∪ closure (fillH C₁)) := hC₁.isClosed.union isClosed_closure
  have hĈ₂ : IsClosed (C₂ ∪ closure (fillH C₂)) := hC₂.isClosed.union isClosed_closure
  -- the protected rational point
  obtain ⟨q, hq0, hqx, hqĈ⟩ : ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) < x₂ ∧
      ((q : ℝ) : ℂ) ∉ (C₁ ∪ closure (fillH C₁)) ∪ (C₂ ∪ closure (fillH C₂)) := by
    have hfc : Continuous fun t : ℝ => (t : ℂ) := Complex.continuous_ofReal
    obtain ⟨t₀, ht₀, ht₀Ĉ⟩ : ∃ t₀ ∈ Icc (0 : ℝ) x₂,
        (t₀ : ℂ) ∉ (C₁ ∪ closure (fillH C₁)) ∪ (C₂ ∪ closure (fillH C₂)) := by
      by_contra hall
      push Not at hall
      obtain ⟨t, -, ht1, ht2⟩ := isPreconnected_closed_iff.1 isPreconnected_Icc _ _ (hĈ₁.preimage hfc)
        (hĈ₂.preimage hfc) (fun t ht => hall t ht)
        ⟨0, left_mem_Icc.2 hx₂.le, Or.inl (by simpa using h0)⟩ ⟨x₂, right_mem_Icc.2 hx₂.le, Or.inl hx⟩
      exact Set.disjoint_left.1 hdisj ht1 ht2
    have hpos : 0 < t₀ := lt_of_le_of_ne ht₀.1 fun h => ht₀Ĉ (Or.inl (Or.inl (by rw [← h]; simpa using h0)))
    have hlt : t₀ < x₂ := lt_of_le_of_ne ht₀.2 fun h => ht₀Ĉ (Or.inr (Or.inl (by rw [h]; exact hx)))
    obtain ⟨ε, hε, hεb⟩ := Metric.isOpen_iff.1 (hĈ₁.union hĈ₂).isOpen_compl (t₀ : ℂ) ht₀Ĉ
    have hε' : 0 < min ε (min t₀ (x₂ - t₀)) := lt_min hε (lt_min hpos (by linarith))
    have h1 := min_le_left ε (min t₀ (x₂ - t₀))
    have h2 := min_le_right ε (min t₀ (x₂ - t₀))
    have h3 := min_le_left t₀ (x₂ - t₀)
    have h4 := min_le_right t₀ (x₂ - t₀)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn
      (show t₀ - min ε (min t₀ (x₂ - t₀)) < t₀ + min ε (min t₀ (x₂ - t₀)) by linarith)
    refine ⟨q, by linarith, by linarith, fun hq => hεb ?_ hq⟩
    rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  -- the dyadic covers and the closures of their fillings
  have hbdd : ∀ D : Set ℂ, Bornology.IsBounded D → IsCompact (closure (fillH D)) := fun D hD => by
    obtain ⟨R, hR, hDR⟩ := exists_closure_subset_ball hD
    exact (Metric.isBounded_ball.subset (fillH_subset_ball hR hDR)).isCompact_closure
  have hD₁b : ∀ m, Bornology.IsBounded (dyadicCover m C₁) := fun m =>
    (Restart.isCompact_dyadicCover hC₁.isBounded m).isBounded
  have hD₂b : ∀ m, Bornology.IsBounded ((fun z : ℂ => z + x₂) '' dyadicCover m C₂') := fun m =>
    ((Restart.isCompact_dyadicCover hC₂'c.isBounded m).image (continuous_id.add continuous_const)).isBounded
  have hXa : Antitone fun m => closure (fillH (dyadicCover m C₁)) := fun _ _ hab =>
    closure_mono (Restart.fillH_dyadicCover_antitone hab)
  have hYa : Antitone fun m => closure (fillH ((fun z : ℂ => z + x₂) '' dyadicCover m C₂')) := fun _ _ hab =>
    closure_mono (fillH_mono (image_mono (Restart.dyadicCover_antitone hab)))
  have hB₁ : ∀ x, x ∉ C₁ ∪ closure (fillH C₁) → ∀ᶠ m in atTop, x ∉ closure (fillH (dyadicCover m C₁)) :=
    fun x hx => notMem_closure_fillH_dyadicCover hC₁ hx
  have hB₂ : ∀ x, x ∉ C₂ ∪ closure (fillH C₂) →
      ∀ᶠ m in atTop, x ∉ closure (fillH ((fun z : ℂ => z + x₂) '' dyadicCover m C₂')) :=
    fun x hx => notMem_closure_fillH_dyadicCover_add hC₂'c x₂ (by rw [heC₂']; exact hx)
  obtain ⟨m₀, hm₀⟩ := exists_disjoint_of_antitone hXa hYa (fun m => hbdd _ (hD₁b m)) (fun m => hbdd _ (hD₂b m))
    fun x hxX hxY => by
      by_cases h1 : x ∈ C₁ ∪ closure (fillH C₁)
      · by_cases h2 : x ∈ C₂ ∪ closure (fillH C₂)
        · exact Set.disjoint_left.1 hdisj h1 h2
        · obtain ⟨m, hm⟩ := (hB₂ x h2).exists
          exact hm (hxY m)
      · obtain ⟨m, hm⟩ := (hB₁ x h1).exists
        exact hm (hxX m)
  have hsepev : ∀ᶠ m in atTop, Disjoint (closure (fillH (dyadicCover m C₁)))
      (closure (fillH ((fun z : ℂ => z + x₂) '' dyadicCover m C₂'))) := by
    filter_upwards [eventually_ge_atTop m₀] with m hm
    exact hm₀.mono (hXa hm) (hYa hm)
  have hmarkev : ∀ᶠ m in atTop, ∀ j, (p j : ℂ) ∉ closure (fillH (dyadicCover m C₁)) ∧
      (p j : ℂ) ∉ closure (fillH ((fun z : ℂ => z + x₂) '' dyadicCover m C₂')) := by
    rw [eventually_all]
    intro j
    exact (hB₁ _ fun h => hp j (Or.inl h)).and (hB₂ _ fun h => hp j (Or.inr h))
  have hqev : ∀ᶠ m in atTop, ((q : ℝ) : ℂ) ∉ closure (fillH (dyadicCover m C₁)) ∧
      ((q : ℝ) : ℂ) ∉ closure (fillH ((fun z : ℂ => z + x₂) '' dyadicCover m C₂')) :=
    (hB₁ _ fun h => hqĈ (Or.inl h)).and (hB₂ _ fun h => hqĈ (Or.inr h))
  obtain ⟨m, hmsep, hmmark, hmq⟩ := (hsepev.and (hmarkev.and hqev)).exists
  -- the rational separation `δ` and protection radius `d`
  obtain ⟨δ₀, hδ₀, hδsep⟩ := exists_pos_le_norm_sub_of_disjoint (hbdd _ (hD₁b m)) isClosed_closure hmsep
  obtain ⟨δ, hδ1, hδ2⟩ := exists_rat_btwn (show (0 : ℝ) < δ₀ / 2 by positivity)
  have hPc : IsCompact (insert ((q : ℝ) : ℂ) (range fun j => (p j : ℂ))) :=
    ((Set.finite_range _).insert _).isCompact
  have hPdis : Disjoint (insert ((q : ℝ) : ℂ) (range fun j => (p j : ℂ)))
      (closure (fillH (dyadicCover m C₁)) ∪ closure (fillH ((fun z : ℂ => z + x₂) '' dyadicCover m C₂'))) := by
    rw [Set.disjoint_left]
    rintro z (rfl | ⟨j, rfl⟩) (hz | hz)
    exacts [hmq.1 hz, hmq.2 hz, (hmmark j).1 hz, (hmmark j).2 hz]
  obtain ⟨ρ, hρ, hρsep⟩ := exists_pos_le_norm_sub_of_disjoint hPc (isClosed_closure.union isClosed_closure) hPdis
  obtain ⟨d, hd1, hd2⟩ := exists_rat_btwn (show (0 : ℝ) < ρ / 2 by positivity)
  -- the index
  set I₁ := (Restart.dyadicIdx_finite hC₁.isBounded m).toFinset with hI₁
  set I₂ := (Restart.dyadicIdx_finite hC₂'c.isBounded m).toFinset with hI₂
  have hsq₁ : sqUnion m I₁ = dyadicCover m C₁ := by
    ext z
    simp only [sqUnion, dyadicCover, hI₁, Set.Finite.mem_toFinset, mem_iUnion, exists_prop]
  have hsq₂ : sqUnion m I₂ = dyadicCover m C₂' := by
    ext z
    simp only [sqUnion, dyadicCover, hI₂, Set.Finite.mem_toFinset, mem_iUnion, exists_prop]
  have hE₁ : CofIdx.encl₁ (m, I₁, I₂, N, δ, q, d) = fillH (dyadicCover m C₁) := by
    show fillH (sqUnion m I₁) = _
    rw [hsq₁]
  have hE₂ : CofIdx.encl₂ x₂ (m, I₁, I₂, N, δ, q, d) = fillH ((fun z : ℂ => z + x₂) '' dyadicCover m C₂') := by
    show fillH ((fun z : ℂ => z + x₂) '' sqUnion m I₂) = _
    rw [hsq₂]
  have hfar : ∀ z ∈ closure (fillH (dyadicCover m C₁)) ∪
      closure (fillH ((fun z : ℂ => z + x₂) '' dyadicCover m C₂')),
      ∀ w ∈ insert ((q : ℝ) : ℂ) (range fun j => (p j : ℂ)), ‖z - w‖ < 2 * (d : ℝ) → False :=
    fun z hz w hw hlt => by
      have := hρsep z hz w hw
      linarith
  have hball : ∀ w ∈ insert ((q : ℝ) : ℂ) (range fun j => (p j : ℂ)),
      Disjoint (ball w (2 * (d : ℝ))) (CofIdx.encl₁ (m, I₁, I₂, N, δ, q, d) ∪
        CofIdx.encl₂ x₂ (m, I₁, I₂, N, δ, q, d)) := by
    intro w hw
    rw [hE₁, hE₂, Set.disjoint_left]
    rintro z hzb (hz | hz)
    · refine hfar z (Or.inl (subset_closure hz)) w hw ?_
      rwa [mem_ball, dist_eq_norm] at hzb
    · refine hfar z (Or.inr (subset_closure hz)) w hw ?_
      rwa [mem_ball, dist_eq_norm] at hzb
  have hmemD₂ : ∀ z : ℂ, z - (x₂ : ℂ) ∈ dyadicCover m C₂' → z ∈ (fun z : ℂ => z + x₂) '' dyadicCover m C₂' :=
    fun z hz => ⟨z - x₂, hz, by ring⟩
  refine ⟨(m, I₁, I₂, N, δ, q, d), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, ?_, ?_⟩
  · show IsPreconnected (sqUnion m I₁ ∪ lowerHalf)
    rw [hsq₁]
    exact Restart.isPreconnected_dyadicCover_union hc₁ Restart.zero_mem_lowerHalf m
  · show IsPreconnected ((fun z : ℂ => z + x₂) '' sqUnion m I₂ ∪ lowerHalf)
    have hc₂' : IsPreconnected (C₂' ∪ lowerHalf) := by
      have := hc₂.image (fun z : ℂ => z - x₂) (continuous_id.sub continuous_const).continuousOn
      rwa [image_union, ← hC₂', show (fun z : ℂ => z - x₂) '' lowerHalf = lowerHalf by
        simpa [sub_eq_add_neg] using image_add_lowerHalf (-x₂)] at this
    have := (Restart.isPreconnected_dyadicCover_union hc₂' Restart.zero_mem_lowerHalf m).image
      (fun z : ℂ => z + x₂) (continuous_id.add continuous_const).continuousOn
    rwa [image_union, image_add_lowerHalf, ← hsq₂] at this
  · show (0 : ℝ≥0) < (N : ℝ≥0)
    exact_mod_cast hN
  · show (0 : ℝ) < (δ : ℝ)
    exact hδ1
  · intro a ha z hz
    rw [hE₂] at ha
    rw [hE₁] at hz
    have := hδsep a (subset_closure ha) z (subset_closure hz)
    show 2 * (δ : ℝ) ≤ ‖a - z‖
    linarith
  · show (0 : ℝ) < (d : ℝ)
    exact hd1
  · exact hq0
  · exact hqx
  · exact hball _ (mem_insert _ _)
  · intro j
    exact hball _ (mem_insert_of_mem _ ⟨j, rfl⟩)
  · refine ⟨1 / 2 ^ m, by positivity, fun z hz => ?_⟩
    rw [hE₁]
    exact mem_fillH_of_mem_closure hz.2 (subset_closure (ball_zero_subset_dyadicCover h0 m hz.1))
  · refine ⟨1 / 2 ^ m, by positivity, fun z hz => ?_⟩
    rw [hE₂]
    refine mem_fillH_of_mem_closure hz.2 (subset_closure (hmemD₂ z (ball_zero_subset_dyadicCover h0' m ?_)))
    have hz1 := hz.1
    rw [mem_ball, dist_eq_norm] at hz1
    rw [mem_ball, dist_eq_norm, sub_zero]
    exact hz1
  · intro z hz
    rw [hE₁]
    exact mem_fillH_of_mem_closure hz.2 (subset_closure (Restart.subset_dyadicCover m hz.1))
  · intro z hz
    rw [hE₂]
    exact mem_fillH_of_mem_closure hz.2 (subset_closure (hmemD₂ z (Restart.subset_dyadicCover m
      (hmemC₂' z hz.1))))

/-- **Two disjoint compact prefixes of curves started at `0` and `x₂` lie in a good enclosure pair**: for compact
`ℍ`-hulls `A₁`, `A₂` (Loewner hulls) whose prefixes `closure A₁ ∪ {0}` and `closure A₂ ∪ {x₂}` are disjoint and contain
no mark, some good index with the prescribed cap has `A₁ ⊆ encl₁` and `A₂ ⊆ encl₂`. -/
theorem exists_goodEncl_prefix {nm : ℕ} {x₂ : ℝ} (hx₂ : 0 < x₂) {p : Fin nm → ℝ} {A₁ A₂ : Set ℂ}
    (hA₁ : IsHPHull A₁) (hA₂ : IsHPHull A₂) (hdisj : Disjoint (closure A₁ ∪ {0}) (closure A₂ ∪ {(x₂ : ℂ)}))
    (hp : ∀ m, (p m : ℂ) ∉ (closure A₁ ∪ {0}) ∪ (closure A₂ ∪ {(x₂ : ℂ)})) (N : ℕ) (hN : 0 < N) :
    ∃ i : CofIdx, GoodEncl x₂ p i ∧ i.cap = N ∧ A₁ ⊆ i.encl₁ ∧ A₂ ⊆ i.encl₂ x₂ := by
  have hpre : ∀ {A : Set ℂ} (hA : IsHPHull A) (x : ℝ),
      IsCompact (closure A ∪ {(x : ℂ)}) ∧ IsPreconnected ((closure A ∪ {(x : ℂ)}) ∪ lowerHalf) ∧
        (closure A ∪ {(x : ℂ)}) ∪ closure (fillH (closure A ∪ {(x : ℂ)})) = closure A ∪ {(x : ℂ)} := by
    intro A hA x
    refine ⟨hA.2.1.isCompact_closure.union isCompact_singleton, ?_, ?_⟩
    · have hxL : (x : ℂ) ∈ lowerHalf := show ((x : ℂ)).im ≤ 0 by simp
      have e : (closure A ∪ {(x : ℂ)}) ∪ lowerHalf = closure (A ∪ lowerHalf) := by
        rw [closure_union, Restart.lowerHalf, isClosed_lowerHalf.closure_eq, union_assoc,
          singleton_union, insert_eq_of_mem (show (x : ℂ) ∈ {z : ℂ | z.im ≤ 0} from hxL)]
      rw [e]
      exact (IsHPHull.isPreconnected_union_lowerHalf hA).closure
    · rw [fillH_closure_union_real hA x]
      exact union_eq_left.2 subset_union_left
  obtain ⟨hK₁, hc₁, he₁⟩ := hpre hA₁ 0
  obtain ⟨hK₂, hc₂, he₂⟩ := hpre hA₂ x₂
  simp only [Complex.ofReal_zero] at hK₁ hc₁ he₁
  obtain ⟨i, hi, hcap, h₁, h₂⟩ := exists_goodEncl hx₂ hK₁ hK₂ (Or.inr rfl) (Or.inr rfl) hc₁ hc₂
    (by rw [he₁, he₂]; exact hdisj) (by rw [he₁, he₂]; exact hp) N hN
  exact ⟨i, hi, hcap, fun z hz => h₁ ⟨Or.inl (subset_closure hz), hA₁.1 hz⟩,
    fun z hz => h₂ ⟨Or.inl (subset_closure hz), hA₂.1 hz⟩⟩

end InteractingSLE.ZhanGT4
