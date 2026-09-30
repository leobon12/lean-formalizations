import QuantumZipper.Proofs.Zipper.F1Side2
import QuantumZipper.Proofs.RS.RealAlive

/-!
# F1d input (b): existence of the side-image limits, unconditionally for `W = drive κ B`

E-branch node F1d. `F1Side2.lean` proves that the real forward flow is strictly order preserving
(`isForwardSol_lt_of_lt`). This file deduces that the two one-sided limits of
`x ↦ (fwdMap W t x).re` at `0` exist as soon as every real `x ≠ 0` is alive at time `t`:

* `tendsto_nhdsLT_of_monotoneOn`, `tendsto_nhdsGT_of_monotoneOn`: a monotone function on
  `(−∞,a)` (resp. `(a,∞)`) that is bounded above (resp. below) converges to its supremum
  (resp. infimum) at `a⁻` (resp. `a⁺`). The boundedness hypothesis is necessary
  (`f x = 1/x` on `(−∞,0)` is monotone with no limit in `ℝ` at `0⁻`).
* `exists_tendsto_sideImages_of_alive`: if every real `x ≠ 0` is alive at time `t` then both
  one-sided limits of `x ↦ (fwdMap W t x).re` exist. The values `fwdMap W t x` are strictly
  increasing in `x` (`isForwardSol_lt_of_lt`); monotonicity plus the two *finite* bounds
  `fwdMap W t x < fwdMap W t 1` (`x < 0`) and `fwdMap W t (−1) < fwdMap W t x` (`x > 0`) force
  the limits to exist.
* `ae_sideImages_reflect_drive`: **the unconditional almost-sure form** for the forward flow
  driven by `W = drive κ B`, `0 < κ ≤ 4`: a.s. the side images of `−W` are the reflected,
  exchanged side images of `W`. The aliveness hypothesis is exactly `RS.ae_real_alive`
  (Rohde–Schramm, *Basic properties of SLE*, Lemma 6.2, pp. 23–24; Kemppainen,
  *Schramm–Loewner Evolution*, Prop. 5.1, pp. 78–80, and Prop. 5.2, p. 80), which covers
  `0 < κ ≤ 4`; `F1.sideImages_reflect_swap` then gives the identity.

The monotone-convergence lemmas are elementary ("own elementary proof"; they are the standard
`Tendsto`-form of `sSup`/`sInf` along a monotone family), and the general form of the
side-image identity is Sheffield, arXiv:1012.4797, §5.4, p. 72 ("by symmetry"), formalized in
`F1Side.lean`.
-/

noncomputable section

open Complex Filter MeasureTheory Set ProbabilityTheory
open scoped Topology ENNReal ComplexConjugate NNReal

namespace QuantumZipper
namespace F1

/-! ## Step 4: one-sided limits of monotone functions -/

/-- **Left limit of a monotone function.** A function that is monotone on `(-∞,a)` and bounded
above there converges to its supremum as `x → a⁻`. The boundedness hypothesis is necessary:
`f x = 1/x` on `(-∞,0)` is monotone but has no limit in `ℝ` at `0⁻`. -/
theorem tendsto_nhdsLT_of_monotoneOn {f : ℝ → ℝ} {a B : ℝ} (hmono : MonotoneOn f (Iio a))
    (hB : ∀ x ∈ Iio a, f x ≤ B) :
    Tendsto f (𝓝[<] a) (𝓝 (sSup (f '' Iio a))) := by
  have hbdd : BddAbove (f '' Iio a) := ⟨B, by rintro y ⟨x, hx, rfl⟩; exact hB x hx⟩
  refine tendsto_order.2 ⟨fun l hl => ?_, fun u hu => ?_⟩
  · have hne : (f '' Iio a).Nonempty := ⟨f (a - 1), a - 1, by simp, rfl⟩
    obtain ⟨y, ⟨x₀, hx₀, rfl⟩, hl₀⟩ := (lt_csSup_iff hbdd hne).1 hl
    filter_upwards [Ioo_mem_nhdsLT (show x₀ < a from hx₀)] with x hx
    exact hl₀.trans_le (hmono hx₀ (mem_Iio.2 hx.2) hx.1.le)
  · filter_upwards [self_mem_nhdsWithin] with x (hx : x < a)
    exact lt_of_le_of_lt (le_csSup hbdd ⟨x, hx, rfl⟩) hu

/-- **Right limit of a monotone function.** A function that is monotone on `(a,∞)` and bounded
below there converges to its infimum as `x → a⁺` (dual of `tendsto_nhdsLT_of_monotoneOn`; the
boundedness hypothesis is again necessary, e.g. `f x = 1/x` on `(0,∞)` at `0⁺`). -/
theorem tendsto_nhdsGT_of_monotoneOn {f : ℝ → ℝ} {a B : ℝ} (hmono : MonotoneOn f (Ioi a))
    (hB : ∀ x ∈ Ioi a, B ≤ f x) :
    Tendsto f (𝓝[>] a) (𝓝 (sInf (f '' Ioi a))) := by
  have hbdd : BddBelow (f '' Ioi a) := ⟨B, by rintro y ⟨x, hx, rfl⟩; exact hB x hx⟩
  refine tendsto_order.2 ⟨fun l hl => ?_, fun u hu => ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with x (hx : a < x)
    exact hl.trans_le (csInf_le hbdd ⟨x, hx, rfl⟩)
  · have hne : (f '' Ioi a).Nonempty := ⟨f (a + 1), a + 1, by simp, rfl⟩
    obtain ⟨y, ⟨x₀, hx₀, rfl⟩, hx₀u⟩ := (csInf_lt_iff hbdd hne).1 hu
    filter_upwards [Ioo_mem_nhdsGT (show a < x₀ from hx₀)] with x hx
    exact lt_of_le_of_lt (hmono (mem_Ioi.2 hx.1) hx₀ hx.2.le) hx₀u

/-! ## Step 5: the side images exist -/

/-- **Existence of the side images from aliveness.** If every real `x ≠ 0` is alive at time `t`
(a forward solution from `x` exists on `[0,t]`), then both one-sided limits of
`x ↦ (fwdMap W t x).re` at `0` exist (and are finite), so the `limUnder`s in `sideImages W t`
are not junk. -/
theorem exists_tendsto_sideImages_of_alive {W : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (halive : ∀ x : ℝ, x ≠ 0 → ∃ u, IsForwardSol W (x : ℂ) t u) :
    ∃ a b : ℝ,
      Tendsto (fun x : ℝ => (fwdMap W t x).re) (𝓝[<] (0 : ℝ)) (𝓝 a) ∧
      Tendsto (fun x : ℝ => (fwdMap W t x).re) (𝓝[>] (0 : ℝ)) (𝓝 b) := by
  set g : ℝ → ℝ := fun x => (fwdMap W t x).re with hg
  have hval : ∀ x : ℝ, x ≠ 0 → ∃ u, IsForwardSol W (x : ℂ) t u ∧ g x = (u t).re := by
    intro x hx
    obtain ⟨u, hu⟩ := halive x hx
    exact ⟨u, hu, by
      simp only [hg]
      rw [fwdMap_eq_of_isForwardSol hu ⟨ht, le_rfl⟩]⟩
  have hmono : ∀ x y : ℝ, x ≠ 0 → y ≠ 0 → x < y → g x < g y := by
    intro x y hx hy hxy
    obtain ⟨u₁, hu₁, hg₁⟩ := hval x hx
    obtain ⟨u₂, hu₂, hg₂⟩ := hval y hy
    rw [hg₁, hg₂]
    exact isForwardSol_lt_of_lt ht hxy hu₁ hu₂ t ⟨ht, le_rfl⟩
  refine ⟨sSup (g '' Iio (0 : ℝ)), sInf (g '' Ioi (0 : ℝ)), ?_, ?_⟩
  · refine tendsto_nhdsLT_of_monotoneOn (B := g 1) (fun x hx y hy hxy => ?_) (fun x hx => ?_)
    · rcases lt_or_eq_of_le hxy with hlt | heq
      · exact (hmono x y (ne_of_lt hx) (ne_of_lt hy) hlt).le
      · rw [heq]
    · exact (hmono x 1 (ne_of_lt hx) one_ne_zero (show x < 1 from (mem_Iio.1 hx).trans zero_lt_one)).le
  · refine tendsto_nhdsGT_of_monotoneOn (B := g (-1)) (fun x hx y hy hxy => ?_) (fun x hx => ?_)
    · rcases lt_or_eq_of_le hxy with hlt | heq
      · exact (hmono x y (ne_of_gt hx) (ne_of_gt hy) hlt).le
      · rw [heq]
    · exact (hmono (-1) x (by norm_num) (ne_of_gt hx) (show (-1 : ℝ) < x from (by norm_num : (-1 : ℝ) < 0).trans (mem_Ioi.1 hx))).le

/-! ## Almost-sure forms -/

section Ae

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Almost-sure existence of the side-image limits from almost-sure aliveness: the pointwise
statement `exists_tendsto_sideImages_of_alive` transferred to an a.e. statement. -/
theorem ae_exists_tendsto_sideImages_of_alive {W : Ω → ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (halive : ∀ᵐ ω ∂P, ∀ x : ℝ, x ≠ 0 → ∃ u, IsForwardSol (W ω) (x : ℂ) t u) :
    ∀ᵐ ω ∂P, ∃ a b : ℝ,
      Tendsto (fun x : ℝ => (fwdMap (W ω) t x).re) (𝓝[<] (0 : ℝ)) (𝓝 a) ∧
      Tendsto (fun x : ℝ => (fwdMap (W ω) t x).re) (𝓝[>] (0 : ℝ)) (𝓝 b) := by
  filter_upwards [halive] with ω h
  exact exists_tendsto_sideImages_of_alive ht h

/-- **Almost-sure side-image identity from almost-sure aliveness.** `F1Side.lean`'s
`ae_sideImages_reflect` with its existence hypothesis discharged by
`ae_exists_tendsto_sideImages_of_alive`: the only input left is that every real `x ≠ 0` is alive
at time `t` a.s. -/
theorem ae_sideImages_reflect_of_alive {W : Ω → ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (halive : ∀ᵐ ω ∂P, ∀ x : ℝ, x ≠ 0 → ∃ u, IsForwardSol (W ω) (x : ℂ) t u) :
    ∀ᵐ ω ∂P, sideImages (-(W ω)) t =
      (-(sideImages (W ω) t).2, -(sideImages (W ω) t).1) :=
  ae_sideImages_reflect W ht (ae_exists_tendsto_sideImages_of_alive ht halive)

end Ae

/-- **Unconditional almost-sure side-image identity for `W = drive κ B`, `0 < κ ≤ 4`.** For a
Brownian motion `B` and `κ ∈ (0,4]`, almost surely the side images of the reflected driver `−W`
are the exchanged, reflected side images of `W`: this is the `hside` hypothesis of
`F1.unzipLengths_reflect_of`, now unconditional. The aliveness input is `RS.ae_real_alive`
(Rohde–Schramm, *Basic properties of SLE*, Lemma 6.2, pp. 23–24; Kemppainen,
*Schramm–Loewner Evolution*, Prop. 5.1, pp. 78–80); reflection invariance of the side images is
`F1.sideImages_reflect_swap`. -/
theorem ae_sideImages_reflect_drive {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {κ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ ≤ 4) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, sideImages (-(drive κ B ω)) t =
      (-(sideImages (drive κ B ω) t).2, -(sideImages (drive κ B ω) t).1) := by
  refine ae_sideImages_reflect_of_alive ht ?_
  filter_upwards [RS.ae_real_alive hB hκ hκ4] with ω h x hx
  exact h x hx t ht

end F1
end QuantumZipper
