/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71KChart
import InteractingSLE.Spec.Sec7.Lemma71FInfty
import InteractingSLE.Spec.Sec7.Prop74BShift

/-!
# Proposition 7.4's pocket: the inverse of a two-point pocket chart on `ℍ̄` and its boundary correspondence

Packet PROVE-PROP74B, item (b) (`planning/handoffs/PROVE-PROP74.md`, "How to discharge it"). Specification §7.1 setup
(p. 222: "Let `ψ : C → ℍ` be a conformal transformation which sends `x₀` to `0` and `y₀` to `∞`"), Remark 6.14
(p. 217: "Its Jordan boundary homeomorphism"), and the deterministic normalization lemma of supplement §2.3 (p. 453:
"Let `φ : C → ℍ` send `x₀` to zero and `y₀` to infinity, with the left side sent to the negative half-line").

* **The inverse chart on `ℍ̄`** (deterministic, `pocketInv`, `pocketInv_props`): for a conformal bijection
  `f : C → ℍ` of a domain `C ⊆ ℍ` written as `f = Ψ ∘ cayley` with a boundary map `Ψ` continuous and injective on
  `E = cl(cayley C) ∖ {q}`, `ℍ̄`-valued and tending to `∞` at `q`, the map `G = cayleyInv ∘ (Ψ|_E)⁻¹` is continuous
  and injective on `ℍ̄`, equals `f⁻¹` on `ℍ`, and `Ψ (cayley (G w)) = w` (`Ψ(E) = ℍ̄` by compactness of
  `cl(cayley C)`).
* **The boundary correspondence** (`pocketInv_boundary`): on a marked pocket between two ordered simple proper
  curves, `G` sends the negative half-line into the left wall and the positive half-line into the right
  wall, given the **orientation** of the boundary map (`PocketChartOrientationStatement`, a named deterministic input:
  the open right-wall arc goes to the positive half-line); real points go to the pocket frontier, which lies on the
  two walls (WangWu's `pocket_props`), and the positive half-line is covered by the right-wall arc (intermediate value
  theorem); `image_pocketInv_image`: `G (Ψ (cayley Γ ∩ E)) = Γ ∩ G (ℍ̄)` for `Γ ⊆ ℍ̄`.

Conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric Function
open scoped NNReal ENNReal Real
open QuantumZipper (H Hbar chiC)
open QuantumZipper.CA (cayley cayleyInv)
open SupercriticalConformalCovariance (IsConformalBijection)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Sec7.Prop74B

/-! ### The inverse of a boundary map -/

section Inverse

variable {C : Set ℂ} {f Ψ : ℂ → ℂ} {q : ℂ}

theorem mem_Hbar_of_mem_H {z : ℂ} (hz : z ∈ H) : z ∈ Hbar :=
  show (0 : ℝ) ≤ z.im from le_of_lt (show (0 : ℝ) < z.im from hz)

theorem isCompact_closure_cayley_image (hCH : C ⊆ H) : IsCompact (closure (cayley '' C)) :=
  ((isBounded_ball (x := (0 : ℂ)) (r := 1)).subset
    (image_subset_iff.2 fun _ hz => QuantumZipper.CA.cayley_mem_ball (hCH hz))).isCompact_closure

/-- Points of `E = cl(cayley C) ∖ {q}` close to `q` have `|Ψ| > M`. -/
theorem exists_pos_lt_norm (hΨinf : Tendsto (fun x => ‖Ψ x‖) (𝓝[closure (cayley '' C) \ {q}] q) atTop) (M : ℝ) :
    ∃ r > 0, ∀ y ∈ closure (cayley '' C) \ {q}, dist y q < r → M < ‖Ψ y‖ := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhdsWithin_iff.1 (hΨinf.eventually_gt_atTop M)
  exact ⟨r, hr, fun y hy hyq => hsub ⟨mem_ball.2 hyq, hy⟩⟩

/-- **The points of `E` where `|Ψ| ≤ M` form a compact set** `cl(cayley C) ∖ B(q, r)`. -/
theorem exists_isCompact_of_norm_le (hCH : C ⊆ H)
    (hΨinf : Tendsto (fun x => ‖Ψ x‖) (𝓝[closure (cayley '' C) \ {q}] q) atTop) (M : ℝ) :
    ∃ K : Set ℂ, IsCompact K ∧ K ⊆ closure (cayley '' C) \ {q} ∧
      ∀ y ∈ closure (cayley '' C) \ {q}, ‖Ψ y‖ ≤ M → y ∈ K := by
  obtain ⟨r, hr, hM⟩ := exists_pos_lt_norm hΨinf M
  refine ⟨closure (cayley '' C) \ ball q r, (isCompact_closure_cayley_image hCH).diff isOpen_ball,
    fun y hy => ⟨hy.1, fun hyq => hy.2 (by rw [mem_singleton_iff.1 hyq]; exact mem_ball_self hr)⟩,
    fun y hy hyM => ⟨hy.1, fun hyb => absurd (hM y hy (mem_ball.1 hyb)) (not_lt.2 hyM)⟩⟩

variable (hCH : C ⊆ H) (hf : IsConformalBijection f C H) (hqC : ∀ x ∈ C, cayley x ≠ q)
  (hΨc : ContinuousOn Ψ (closure (cayley '' C) \ {q})) (hΨi : InjOn Ψ (closure (cayley '' C) \ {q}))
  (hΨH : MapsTo Ψ (closure (cayley '' C) \ {q}) Hbar)
  (hΨinf : Tendsto (fun x => ‖Ψ x‖) (𝓝[closure (cayley '' C) \ {q}] q) atTop)
  (hΨf : ∀ x ∈ C, f x = Ψ (cayley x))
include hCH hf hqC hΨc hΨH hΨinf hΨf

/-- **The boundary map is onto `ℍ̄`**: `Ψ(E) = ℍ̄`. It contains `Ψ(cayley C) = f(C) = ℍ`, and a point `w ∈ ℍ̄` is a
limit of points of `ℍ ∩ B(w, 1)`, which are values of `Ψ` on the compact set `{|Ψ| ≤ |w| + 1}` of `E`. -/
theorem image_boundaryMap_eq_Hbar : Ψ '' (closure (cayley '' C) \ {q}) = Hbar := by
  refine Subset.antisymm hΨH.image_subset fun w hw => ?_
  obtain ⟨K, hK, hKE, hKM⟩ := exists_isCompact_of_norm_le hCH hΨinf (‖w‖ + 1)
  have hsub : H ∩ ball w 1 ⊆ Ψ '' K := by
    rintro z ⟨hzH, hzw⟩
    obtain ⟨x, hx, rfl⟩ := hf.2.surjOn hzH
    have hyE : cayley x ∈ closure (cayley '' C) \ {q} := ⟨subset_closure ⟨x, hx, rfl⟩, hqC x hx⟩
    refine ⟨cayley x, hKM _ hyE ?_, (hΨf x hx).symm⟩
    rw [← hΨf x hx]
    have h1 : ‖f x‖ ≤ ‖w‖ + dist (f x) w := by
      rw [dist_eq_norm]
      linarith [norm_sub_norm_le (f x) w]
    linarith [mem_ball.1 hzw]
  have hwcl : w ∈ closure (H ∩ ball w 1) := by
    have hw' : w ∈ ball w 1 ∩ closure H := ⟨mem_ball_self one_pos, QuantumZipper.CA.Car.closure_H_eq_Hbar ▸ hw⟩
    rw [inter_comm]
    exact isOpen_ball.inter_closure hw'
  have hcl : IsClosed (Ψ '' K) := (hK.image_of_continuousOn (hΨc.mono hKE)).isClosed
  obtain ⟨y, hy, rfl⟩ := hcl.closure_subset (closure_mono hsub hwcl)
  exact ⟨y, hKE hy, rfl⟩

theorem invFunOn_boundaryMap_spec {w : ℂ} (hw : w ∈ Hbar) :
    invFunOn Ψ (closure (cayley '' C) \ {q}) w ∈ closure (cayley '' C) \ {q} ∧
      Ψ (invFunOn Ψ (closure (cayley '' C) \ {q}) w) = w := by
  have hw' : w ∈ Ψ '' (closure (cayley '' C) \ {q}) := by
    rw [image_boundaryMap_eq_Hbar hCH hf hqC hΨc hΨH hΨinf hΨf]; exact hw
  exact ⟨invFunOn_mem hw', invFunOn_eq hw'⟩

include hΨi in
/-- **The inverse of the boundary map is continuous on `ℍ̄`** (`Lemma71E.tendsto_inv_of_isCompact` on the compact set
`{|Ψ| ≤ |w| + 1}` of `E`). -/
theorem continuousOn_invFunOn_boundaryMap : ContinuousOn (invFunOn Ψ (closure (cayley '' C) \ {q})) Hbar := by
  intro w hw
  obtain ⟨K, hK, hKE, hKM⟩ := exists_isCompact_of_norm_le hCH hΨinf (‖w‖ + 1)
  have hspec := fun {z : ℂ} (hz : z ∈ Hbar) => invFunOn_boundaryMap_spec hCH hf hqC hΨc hΨH hΨinf hΨf hz
  have hev : ∀ᶠ z in 𝓝[Hbar] w, z ∈ Hbar ∩ ball w 1 :=
    inter_mem_nhdsWithin Hbar (ball_mem_nhds w one_pos)
  have hnorm : ∀ z ∈ Hbar ∩ ball w 1, ‖z‖ ≤ ‖w‖ + 1 := fun z hz => by
    have h1 := norm_sub_norm_le z w
    have h2 : ‖z - w‖ < 1 := by rw [← dist_eq_norm]; exact mem_ball.1 hz.2
    linarith
  have hpK : invFunOn Ψ (closure (cayley '' C) \ {q}) w ∈ K :=
    hKM _ (hspec hw).1 (by rw [(hspec hw).2]; linarith)
  exact Lemma71E.tendsto_inv_of_isCompact hK (hΨc.mono hKE) (hΨi.mono hKE) nhdsWithin_le_nhds hpK (hspec hw).2
    (hev.mono fun z hz => hKM _ (hspec hz.1).1 (by rw [(hspec hz.1).2]; exact hnorm z hz))
    (hev.mono fun z hz => (hspec hz.1).2)

/-- **The extended inverse chart** `G = cayleyInv ∘ (Ψ|_E)⁻¹` of a boundary map `Ψ` on `E`. -/
def pocketInv (Ψ : ℂ → ℂ) (E : Set ℂ) (w : ℂ) : ℂ := cayleyInv (invFunOn Ψ E w)

include hΨi in
/-- **The extended inverse chart on `ℍ̄`**: continuous and injective on `ℍ̄`, the inverse of `f` on `ℍ`, with values in
`cl C`, and `Ψ (cayley (G w)) = w`. Here `1 ∈ cl(cayley C)` only if `q = 1` (a pocket reaching `∞` closes there). -/
theorem pocketInv_props (hq1 : (1 : ℂ) ∈ closure (cayley '' C) → q = 1) :
    ContinuousOn (pocketInv Ψ (closure (cayley '' C) \ {q})) Hbar ∧
      InjOn (pocketInv Ψ (closure (cayley '' C) \ {q})) Hbar ∧
      (∀ w ∈ H, ∀ z ∈ C, f z = w → pocketInv Ψ (closure (cayley '' C) \ {q}) w = z) ∧
      ∀ w ∈ Hbar, pocketInv Ψ (closure (cayley '' C) \ {q}) w ∈ closure C ∧
        cayley (pocketInv Ψ (closure (cayley '' C) \ {q}) w) = invFunOn Ψ (closure (cayley '' C) \ {q}) w ∧
        Ψ (cayley (pocketInv Ψ (closure (cayley '' C) \ {q}) w)) = w := by
  set E := closure (cayley '' C) \ {q} with hE
  have hspec := fun {z : ℂ} (hz : z ∈ Hbar) => invFunOn_boundaryMap_spec hCH hf hqC hΨc hΨH hΨinf hΨf hz
  have hne1 : ∀ {y : ℂ}, y ∈ E → y ≠ 1 := fun hy h1 => hy.2 (by rw [h1, hq1 (h1 ▸ hy.1)]; rfl)
  have hcont := continuousOn_invFunOn_boundaryMap hCH hf hqC hΨc hΨi hΨH hΨinf hΨf
  have hcc : ∀ {w : ℂ}, w ∈ Hbar → cayley (pocketInv Ψ E w) = invFunOn Ψ E w := fun hw =>
    QuantumZipper.CA.cayley_cayleyInv (hne1 (hspec hw).1)
  have hCcl : cayleyInv '' (cayley '' C) = C := by
    rw [image_image]
    exact (image_congr fun z hz => WangWu.cayleyInv_cayley_of_mem_Hbar (mem_Hbar_of_mem_H (hCH hz))).trans (image_id C)
  refine ⟨fun w hw => ?_, fun w₁ hw₁ w₂ hw₂ h => ?_, fun w hw z hz hfz => ?_, fun w hw => ⟨?_, hcc hw, ?_⟩⟩
  · exact ((QuantumZipper.CA.differentiableAt_cayleyInv (hne1 (hspec hw).1)).continuousAt).comp_continuousWithinAt
      (hcont w hw)
  · have h1 := congrArg cayley h
    rw [hcc hw₁, hcc hw₂] at h1
    rw [← (hspec hw₁).2, ← (hspec hw₂).2, h1]
  · have hzE : cayley z ∈ E := ⟨subset_closure ⟨z, hz, rfl⟩, hqC z hz⟩
    have hwE := hspec (mem_Hbar_of_mem_H hw)
    have h1 : invFunOn Ψ E w = cayley z := hΨi hwE.1 hzE (by rw [hwE.2, ← hΨf z hz, hfz])
    change cayleyInv (invFunOn Ψ E w) = z
    rw [h1]
    exact WangWu.cayleyInv_cayley_of_mem_Hbar (mem_Hbar_of_mem_H (hCH hz))
  · have h1 : ContinuousWithinAt cayleyInv (cayley '' C) (invFunOn Ψ E w) :=
      (QuantumZipper.CA.differentiableAt_cayleyInv (hne1 (hspec hw).1)).continuousAt.continuousWithinAt
    have h2 := h1.mem_closure_image (hspec hw).1.1
    rwa [hCcl] at h2
  · rw [hcc hw]
    exact (hspec hw).2

end Inverse

/-! ### The boundary correspondence on a marked pocket -/

open Lemma71K (IsMarkedPocket wallPt)

/-- **Named input: the two-point pocket chart preserves orientation** (deterministic; supplement §2.3, p. 453: "Let
`φ : C → ℍ` send `x₀` to zero and `y₀` to infinity, with the left side sent to the negative half-line"; IG I §7.1,
p. 222; the frozen `IsComponentChart`'s docstring: "Since `fwd` preserves orientation"). Let `R` (right wall) and `L`
(left wall) be simple proper curves from `0` with `L` on the closed left side of `R`, let `C` be a component between
them which is a marked pocket `[a, b]` of `R` (opening point `R̃ a`, closing point `R̃ b` in the Cayley picture), and
let `f : C → ℍ` be a conformal bijection with a boundary map `Ψ` (`f = Ψ ∘ cayley`, continuous and injective on
`cl(cayley C) ∖ {R̃ b}` with values in `ℍ̄`, `Ψ (R̃ a) = 0`, `|Ψ| → ∞` at `R̃ b`). Then `Ψ` sends the open right-wall
arc `R̃((a, b))` to the positive half-line. (Traversed from `x₀` to `y₀`, the right wall has `C` on its left, and so
has `(0, ∞)` the half-plane; a conformal map preserves orientation.) Not proved here: it needs the orientation of
holomorphic boundary correspondences (an argument principle or degree argument), which no available library has. -/
def PocketChartOrientationStatement : Prop :=
  ∀ R L : ℝ≥0 → ℂ, Lemma71I.IsSimpleProper R → Lemma71I.IsSimpleProper L → range L ⊆ closedLeftSide R →
    ∀ C : Set ℂ, C ∈ betweenComponents (range R) (range L) → ∀ a b : ℝ, IsMarkedPocket R C a b →
    ∀ f Ψ : ℂ → ℂ, IsConformalBijection f C H →
      ContinuousOn Ψ (closure (cayley '' C) \ {wallPt R b}) → InjOn Ψ (closure (cayley '' C) \ {wallPt R b}) →
      MapsTo Ψ (closure (cayley '' C) \ {wallPt R b}) Hbar → Ψ (wallPt R a) = 0 →
      Tendsto (fun x => ‖Ψ x‖) (𝓝[closure (cayley '' C) \ {wallPt R b}] (wallPt R b)) atTop →
      (∀ x ∈ C, f x = Ψ (cayley x)) → ∀ s ∈ Ioo a b, 0 < (Ψ (wallPt R s)).re

/-- A point of `ℍ̄` whose Cayley image is a point of the disc crosscut of a curve in `ℍ̄` lies on the curve. -/
theorem mem_range_of_cayley_eq_toDisc {γ : ℝ≥0 → ℂ} (hγ : ∀ t, 0 ≤ (γ t).im) {z : ℂ} (hz : z ∈ Hbar) {s : ℝ}
    (h : cayley z = WangWu.toDisc (Lemma71I.realPath γ) s) : z ∈ range γ := by
  by_cases hs : s < 1
  · rw [WangWu.toDisc_of_lt hs] at h
    have h1 := congrArg cayleyInv h
    rw [WangWu.cayleyInv_cayley_of_mem_Hbar hz,
      WangWu.cayleyInv_cayley_of_mem_Hbar (show (0 : ℝ) ≤ (Lemma71I.realPath γ (WangWu.arcTime s)).im from
        hγ _)] at h1
    exact ⟨_, h1.symm⟩
  · have h1 : WangWu.toDisc (Lemma71I.realPath γ) s = 1 := by simp [WangWu.toDisc, hs]
    exact absurd (h.trans h1) (QuantumZipper.CA.cayley_ne_one (QuantumZipper.CA.add_I_ne_zero_of_im_nonneg hz))

/-- The Cayley image of a point of a curve in `ℍ̄` is a point of its disc crosscut, at a time of `[0, 1)`. -/
theorem cayley_eq_wallPt {γ : ℝ≥0 → ℂ} (t : ℝ≥0) :
    cayley (γ t) = wallPt γ (WangWu.discTime t) ∧ WangWu.discTime t ∈ Ico (0 : ℝ) 1 := by
  refine ⟨?_, WangWu.discTime_mem_Ico t.coe_nonneg⟩
  rw [wallPt, WangWu.toDisc_discTime _ t.coe_nonneg, Lemma71I.realPath_coe]

/-- A component between two curves lies in `ℍ` off both curves. -/
theorem subset_of_mem_betweenComponents {R L : Set ℂ} {C : Set ℂ} (hC : C ∈ betweenComponents R L) :
    C ⊆ H \ (R ∪ L) := by
  obtain ⟨z, -, -, -, rfl⟩ := hC
  exact connectedComponentIn_subset _ _

theorem norm_eq_re_of_im_eq_zero {z : ℂ} (him : z.im = 0) (hre : 0 < z.re) : ‖z‖ = z.re := by
  have e : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [him])
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hre, Complex.ofReal_re]

/-- **The image of a curve under the boundary map, pulled back by the inverse chart**: for `Γ ⊆ ℍ̄`,
`G (Ψ (cayley Γ ∩ E)) = Γ ∩ G (ℍ̄)`, since `G ∘ Ψ = cayleyInv` on `E`. -/
theorem image_pocketInv_image {Ψ : ℂ → ℂ} {E : Set ℂ}
    (hspec : ∀ w ∈ Hbar, invFunOn Ψ E w ∈ E ∧ Ψ (invFunOn Ψ E w) = w) (hΨi : InjOn Ψ E)
    (hE1 : ∀ y ∈ E, y ≠ 1) (hΨH : MapsTo Ψ E Hbar) {Γ : Set ℂ} (hΓ : Γ ⊆ Hbar) :
    pocketInv Ψ E '' (Ψ '' (cayley '' Γ ∩ E)) = Γ ∩ pocketInv Ψ E '' Hbar := by
  have key : ∀ y ∈ E, pocketInv Ψ E (Ψ y) = cayleyInv y := fun y hy => by
    have h1 := hspec (Ψ y) (hΨH hy)
    change cayleyInv (invFunOn Ψ E (Ψ y)) = cayleyInv y
    rw [hΨi h1.1 hy h1.2]
  ext z
  constructor
  · rintro ⟨_, ⟨y, ⟨⟨g, hg, rfl⟩, hyE⟩, rfl⟩, rfl⟩
    rw [key _ hyE, WangWu.cayleyInv_cayley_of_mem_Hbar (hΓ hg)]
    refine ⟨hg, Ψ (cayley g), hΨH hyE, ?_⟩
    rw [key _ hyE, WangWu.cayleyInv_cayley_of_mem_Hbar (hΓ hg)]
  · rintro ⟨hzΓ, w, hw, rfl⟩
    have h1 := hspec w hw
    have hcz : cayley (pocketInv Ψ E w) = invFunOn Ψ E w :=
      QuantumZipper.CA.cayley_cayleyInv (hE1 _ h1.1)
    refine ⟨Ψ (invFunOn Ψ E w), ⟨invFunOn Ψ E w, ⟨⟨pocketInv Ψ E w, hzΓ, hcz⟩, h1.1⟩, rfl⟩, ?_⟩
    rw [h1.2]

section Boundary

variable {R L : ℝ≥0 → ℂ} {C : Set ℂ} {a b : ℝ} {f Ψ : ℂ → ℂ}

/-- **The extended inverse chart of a marked pocket and its boundary correspondence.** On a marked pocket `[a, b]` of
the right wall `R`, between `R` and the left wall `L`, the inverse `G` of a two-point chart `f = Ψ ∘ cayley` is
continuous and injective on `ℍ̄`, inverts `f` on `ℍ`, sends the negative half-line into `L` and the positive half-line
into `R`, given the orientation `hor` of `Ψ` on the open right-wall arc. -/
theorem pocketInv_boundary (hR : Lemma71I.IsSimpleProper R) (hL : Lemma71I.IsSimpleProper L)
    (hLR : range L ⊆ closedLeftSide R) (hCo : IsOpen C) (hC : C ∈ betweenComponents (range R) (range L))
    (hM : IsMarkedPocket R C a b) (hf : IsConformalBijection f C H)
    (hΨc : ContinuousOn Ψ (closure (cayley '' C) \ {wallPt R b}))
    (hΨi : InjOn Ψ (closure (cayley '' C) \ {wallPt R b}))
    (hΨH : MapsTo Ψ (closure (cayley '' C) \ {wallPt R b}) Hbar) (hΨ0 : Ψ (wallPt R a) = 0)
    (hΨinf : Tendsto (fun x => ‖Ψ x‖) (𝓝[closure (cayley '' C) \ {wallPt R b}] (wallPt R b)) atTop)
    (hΨf : ∀ x ∈ C, f x = Ψ (cayley x)) (hor : ∀ s ∈ Ioo a b, 0 < (Ψ (wallPt R s)).re) :
    ContinuousOn (pocketInv Ψ (closure (cayley '' C) \ {wallPt R b})) Hbar ∧
      InjOn (pocketInv Ψ (closure (cayley '' C) \ {wallPt R b})) Hbar ∧
      (∀ w ∈ H, ∀ z ∈ C, f z = w → pocketInv Ψ (closure (cayley '' C) \ {wallPt R b}) w = z) ∧
      (∀ x : ℝ, x < 0 → pocketInv Ψ (closure (cayley '' C) \ {wallPt R b}) x ∈ range L) ∧
      (∀ x : ℝ, 0 < x → pocketInv Ψ (closure (cayley '' C) \ {wallPt R b}) x ∈ range R) ∧
      ∀ Γ ⊆ Hbar, pocketInv Ψ (closure (cayley '' C) \ {wallPt R b}) ''
          (Ψ '' (cayley '' Γ ∩ (closure (cayley '' C) \ {wallPt R b}))) =
        Γ ∩ pocketInv Ψ (closure (cayley '' C) \ {wallPt R b}) '' Hbar := by
  set q := wallPt R b with hq
  set U := cayley '' C with hU
  set E := closure U \ {q} with hE
  set G := pocketInv Ψ E with hG
  have hCsub := subset_of_mem_betweenComponents hC
  have hCH : C ⊆ H := fun z hz => (hCsub hz).1
  have hRim : ∀ t, 0 ≤ (R t).im := hR.isProperCurve.2.2.1
  have hLim : ∀ t, 0 ≤ (L t).im := hL.isProperCurve.2.2.1
  have hqC : ∀ x ∈ C, cayley x ≠ q := fun x hx h =>
    (hCsub hx).2 (Or.inl (mem_range_of_cayley_eq_toDisc hRim (mem_Hbar_of_mem_H (hCH hx)) h))
  obtain ⟨ha0, hab, hb1, hI, -, -, -, -⟩ := hM
  have hq1 : (1 : ℂ) ∈ closure U → q = 1 := fun h1 => by
    have hmem : (1 : ℝ) ∈ {s ∈ Icc (0 : ℝ) 1 | wallPt R s ∈ closure U} :=
      ⟨⟨zero_le_one, le_rfl⟩, by rw [wallPt, WangWu.toDisc_one]; exact h1⟩
    rw [hI] at hmem
    have hb : b = 1 := le_antisymm hb1 hmem.2
    rw [hq, hb, wallPt, WangWu.toDisc_one]
  obtain ⟨hGc, hGi, hGinv, hGcl⟩ := pocketInv_props hCH hf hqC hΨc hΨi hΨH hΨinf hΨf hq1
  have hspec := fun {z : ℂ} (hz : z ∈ Hbar) => invFunOn_boundaryMap_spec hCH hf hqC hΨc hΨH hΨinf hΨf hz
  have hRd := (Lemma71I.IsSimpleProper.isProperArc hR).isDiscCrosscut_toDisc
  have hLd := (Lemma71I.IsSimpleProper.isProperArc hL).isDiscCrosscut_toDisc
  -- the Cayley image of `G x`, for real `x`
  have hxH : ∀ x : ℝ, (x : ℂ) ∈ Hbar := fun x => show (0 : ℝ) ≤ (x : ℂ).im by simp
  have hGE : ∀ x : ℝ, cayley (G x) ∈ E ∧ Ψ (cayley (G x)) = x := fun x => by
    obtain ⟨-, h1, h2⟩ := hGcl x (hxH x)
    exact ⟨h1 ▸ (hspec (hxH x)).1, h2⟩
  have hGHbar : ∀ x : ℝ, G x ∈ Hbar := fun x =>
    (closure_mono hCH).trans QuantumZipper.CA.Car.closure_H_eq_Hbar.le (hGcl x (hxH x)).1
  -- a real point goes to the frontier of the pocket, hence to one of the walls
  have hwalls : ∀ x : ℝ, G x ∈ range R ∪ range L := fun x => by
    have hUo : IsOpen U := Lemma71F.isOpen_cayley_image hCo hCH
    have hnU : cayley (G x) ∉ U := by
      rintro ⟨z, hz, hzx⟩
      have h1 : Ψ (cayley z) ∈ H := (hΨf z hz) ▸ hf.2.mapsTo hz
      rw [hzx, (hGE x).2] at h1
      exact lt_irrefl (0 : ℝ) (by simpa using (show (0 : ℝ) < (x : ℂ).im from h1))
    have hfr : cayley (G x) ∈ frontier U := by
      rw [hUo.frontier_eq]
      exact ⟨(hGE x).1.1, hnU⟩
    have hC' := hC
    rw [← Lemma71I.arcRange_realPath R, ← Lemma71I.arcRange_realPath L] at hC'
    have hord := Lemma71I.disjoint_rightSideOf_of_subset_closedLeftSide hR.isProperCurve hR.2.2.1 hLR
    rw [← Lemma71I.arcRange_realPath R, ← Lemma71I.arcRange_realPath L] at hord
    obtain ⟨a₁, b₁, hg, hCU⟩ := WangWu.exists_contactGap_of_mem_betweenComponents
      (Lemma71I.IsSimpleProper.isProperArc hR) (Lemma71I.IsSimpleProper.isProperArc hL) hord hC'
    have hord' := (WangWu.disjoint_rightSideOf_iff (Lemma71I.IsSimpleProper.isProperArc hR)
      (Lemma71I.IsSimpleProper.isProperArc hL)).1 hord
    obtain ⟨-, -, -, hfrU, -⟩ := WangWu.pocket_props hRd hLd hord' hg
    rw [hU, hCU, hfrU] at hfr
    rcases hfr with ⟨s, -, hs⟩ | ⟨s, -, hs⟩
    · exact Or.inl (mem_range_of_cayley_eq_toDisc hRim (hGHbar x) hs.symm)
    · exact Or.inr (mem_range_of_cayley_eq_toDisc hLim (hGHbar x) hs.symm)
  -- the wall times in the closed pocket
  have hwallI : ∀ s ∈ Icc (0 : ℝ) 1, wallPt R s ∈ closure U → s ∈ Icc a b := fun s hs h => by
    have hmem : s ∈ {s ∈ Icc (0 : ℝ) 1 | wallPt R s ∈ closure U} := ⟨hs, h⟩
    rwa [hI] at hmem
  have hIcc : Icc a b ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc ha0 hb1
  have hwE : ∀ s ∈ Ico a b, wallPt R s ∈ E := fun s hs => by
    have hsI : s ∈ Icc a b := Ico_subset_Icc_self hs
    have hmem : s ∈ {s ∈ Icc (0 : ℝ) 1 | wallPt R s ∈ closure U} := by rw [hI]; exact hsI
    refine ⟨hmem.2, fun hsq => hs.2.ne ?_⟩
    exact hRd.inj (hIcc hsI) (hIcc (right_mem_Icc.2 hab.le)) hsq
  have hE1 : ∀ y ∈ E, y ≠ 1 := fun y hy h1 => hy.2 (by rw [h1, hq1 (h1 ▸ hy.1)]; rfl)
  refine ⟨hGc, hGi, hGinv, fun x hx => ?_, fun x hx => ?_,
    fun Γ hΓ => image_pocketInv_image (fun w hw => hspec hw) hΨi hE1 hΨH hΓ⟩
  · -- negative points: not on the right wall
    rcases hwalls x with hRx | hLx
    · exfalso
      obtain ⟨t, ht⟩ := hRx
      obtain ⟨e1, hs01⟩ := cayley_eq_wallPt (γ := R) t
      rw [ht] at e1
      have hsI := hwallI _ (Ico_subset_Icc_self hs01) (e1 ▸ (hGE x).1.1)
      have hΨs : Ψ (wallPt R (WangWu.discTime t)) = x := e1 ▸ (hGE x).2
      rcases eq_or_lt_of_le hsI.1 with hsa | hsa
      · rw [← hsa, hΨ0] at hΨs
        exact hx.ne (by exact_mod_cast hΨs.symm)
      rcases eq_or_lt_of_le hsI.2 with hsb | hsb
      · exact (hGE x).1.2 (by rw [e1, hsb]; rfl)
      · have h1 := hor _ ⟨hsa, hsb⟩
        rw [hΨs, Complex.ofReal_re] at h1
        exact absurd hx (not_lt.2 h1.le)
    · exact hLx
  · -- positive points: the intermediate value theorem along the open right-wall arc
    have hreal : ∀ s ∈ Ico a b, (Ψ (wallPt R s)).im = 0 := fun s hs => by
      have h0 : 0 ≤ (Ψ (wallPt R s)).im := hΨH (hwE s hs)
      refine le_antisymm (not_lt.1 fun hpos => ?_) h0
      obtain ⟨z, hz, hzw⟩ := hf.2.surjOn (show Ψ (wallPt R s) ∈ H from hpos)
      have hzE : cayley z ∈ E := ⟨subset_closure ⟨z, hz, rfl⟩, hqC z hz⟩
      have h1 : wallPt R s = cayley z := hΨi (hwE s hs) hzE (by rw [← hΨf z hz, hzw])
      exact (hCsub hz).2 (Or.inl (mem_range_of_cayley_eq_toDisc hRim (mem_Hbar_of_mem_H (hCH hz)) h1.symm))
    have hcont : ContinuousOn (fun s => Ψ (wallPt R s)) (Ico a b) :=
      hΨc.comp (hRd.cont.mono (Ico_subset_Icc_self.trans hIcc)) hwE
    have hbI : b ∈ Icc (0 : ℝ) 1 := hIcc (right_mem_Icc.2 hab.le)
    have hlimq : Tendsto (fun s => wallPt R s) (𝓝[Ioo a b] b) (𝓝[E] q) :=
      tendsto_nhdsWithin_iff.2 ⟨((hRd.cont b hbI).tendsto).mono_left
        (nhdsWithin_mono b (Ioo_subset_Icc_self.trans hIcc)),
        eventually_nhdsWithin_of_forall fun s hs => hwE s (Ioo_subset_Ico_self hs)⟩
    have htend : Tendsto (fun s => ‖Ψ (wallPt R s)‖) (𝓝[Ioo a b] b) atTop := hΨinf.comp hlimq
    have := right_nhdsWithin_Ioo_neBot hab
    obtain ⟨s₁, hs₁x, hs₁I⟩ := ((htend.eventually_gt_atTop x).and self_mem_nhdsWithin).exists
    have hg₁ : (Ψ (wallPt R s₁)).re = ‖Ψ (wallPt R s₁)‖ :=
      (norm_eq_re_of_im_eq_zero (hreal s₁ (Ioo_subset_Ico_self hs₁I)) (hor s₁ hs₁I)).symm
    have hIVT := intermediate_value_Icc hs₁I.1.le
      ((Complex.continuous_re.comp_continuousOn hcont).mono (Icc_subset_Ico_right hs₁I.2))
    obtain ⟨s, hs, hsx⟩ := hIVT ⟨by simp only [Function.comp, hΨ0, Complex.zero_re]; exact hx.le,
      by simp only [Function.comp]; rw [hg₁]; exact hs₁x.le⟩
    simp only [Function.comp] at hsx
    have hsa : a ≠ s := fun h => by
      rw [← h, hΨ0, Complex.zero_re] at hsx
      exact hx.ne hsx
    have hsI : s ∈ Ico a b := ⟨hs.1, hs.2.trans_lt hs₁I.2⟩
    have hΨs : Ψ (wallPt R s) = x := Complex.ext (by rw [hsx, Complex.ofReal_re])
      (by rw [hreal s hsI, Complex.ofReal_im])
    have h1 : cayley (G x) = wallPt R s := hΨi (hGE x).1 (hwE s hsI) (by rw [(hGE x).2, hΨs])
    exact mem_range_of_cayley_eq_toDisc hRim (hGHbar x) h1

end Boundary

end InteractingSLE.Sec7.Prop74B
