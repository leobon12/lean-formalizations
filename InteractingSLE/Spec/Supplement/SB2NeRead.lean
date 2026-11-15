/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NeWord
import InteractingSLE.Spec.Supplement.SB2JbTop
import InteractingSLE.Spec.Supplement.SB2VtSeed

/-!
# F2b′'s relative bad set read back to the original real line

Packet PROVE-AUX61-NOJUMP (round 22, component F), deterministic. Let `Φ⁰ = Mo.hullChart (fill X) 0` be a right entry
chart of `X` at `R` with offset `x₀` (`IsRightEntryChart`), `fill X` free right of `R`, and `g` a continuous
extension of `Φ⁰⁻¹` to `ℍ̄`.

* **`inv_of_fwd`**, **`eq_of_inv_eq`**: at a free real point `x`, `g` reads back the forward limit, and it is the only
  real point read back to `x`;
* **`entry_eq`**: the entry `e` of D34's clause (`Nb.HeightClause`: `g e = R`, `g` real and strictly increasing on
  `[e, ∞)`) is the entry value `x₀`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)

namespace InteractingSLE.Theorem14.SB.Ne

section Entry

variable {X : Set ℂ} {g : ℂ → ℂ}

theorem tendsto_g_H (hgc : ContinuousOn g {z | 0 ≤ z.im}) (q : ℂ) (hq : 0 ≤ q.im) :
    Tendsto g (𝓝[H] q) (𝓝 (g q)) :=
  (hgc q hq).tendsto.mono_left (nhdsWithin_mono _ fun z (hz : 0 < z.im) => le_of_lt hz)

theorem tendsto_inv_hullChart (hA : IsHPHull (fillH X)) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g (Mo.hullChart (fillH X) 0).2.1 H) (q : ℂ) (hq : 0 ≤ q.im) :
    Tendsto (Mo.hullChart (fillH X) 0).2.1 (𝓝[H] q) (𝓝[H] (g q)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨(tendsto_g_H hgc q hq).congr' (eventually_nhdsWithin_of_forall fun z hz => hgi hz),
    ?_⟩
  exact eventually_nhdsWithin_of_forall fun z hz => (hullChart_inv_mem hA 0 hz).1

/-- **Only one real point is read back to a point with a forward limit.** -/
theorem eq_of_inv_eq (hA : IsHPHull (fillH X)) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g (Mo.hullChart (fillH X) 0).2.1 H) {y w x : ℝ}
    (hw : Tendsto (Mo.hullChart (fillH X) 0).1 (𝓝[H] (x : ℂ)) (𝓝 (w : ℂ))) (hy : g (y : ℂ) = x) : y = w := by
  have h1 := tendsto_inv_hullChart hA hgc hgi (y : ℂ) (by simp)
  rw [hy] at h1
  have h3 : Tendsto (fun v => v) (𝓝[H] (y : ℂ)) (𝓝 (w : ℂ)) :=
    (hw.comp h1).congr' (eventually_nhdsWithin_of_forall fun v hv => (Mo.isConformal_hullChart hA 0).2.2 v hv)
  have : (𝓝[H] (y : ℂ)).NeBot := GW1P.neBot_nhdsWithin_H (show (0 : ℝ) ≤ ((y : ℝ) : ℂ).im by simp)
  exact_mod_cast tendsto_nhds_unique (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id) h3

/-- **At a free real point the extension reads back the forward limit.** -/
theorem inv_of_fwd (hA : IsHPHull (fillH X)) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g (Mo.hullChart (fillH X) 0).2.1 H) {x w : ℝ}
    (hfree : ∃ r > 0, Disjoint (ball (x : ℂ) r) (fillH X))
    (hw : Tendsto (Mo.hullChart (fillH X) 0).1 (𝓝[H] (x : ℂ)) (𝓝 (w : ℂ))) : g (w : ℂ) = x := by
  obtain ⟨r, hr, hd⟩ := hfree
  have hev : ∀ᶠ z in 𝓝[H] (x : ℂ), z ∈ H \ fillH X := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds (x : ℂ) hr)] with z hzH hzb
    exact ⟨hzH, Set.disjoint_left.1 hd hzb⟩
  have h1 : Tendsto (Mo.hullChart (fillH X) 0).1 (𝓝[H] (x : ℂ)) (𝓝[{z | 0 ≤ z.im}] (w : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hw, hev.mono fun z hz =>
      show 0 ≤ ((Mo.hullChart (fillH X) 0).1 z).im from le_of_lt (hullChart_fwd_spec hA 0 hz).1⟩
  have h2 := (hgc (w : ℂ) (show (0 : ℝ) ≤ ((w : ℝ) : ℂ).im by simp)).tendsto.comp h1
  have h3 : Tendsto (fun z => z) (𝓝[H] (x : ℂ)) (𝓝 (g w)) :=
    h2.congr' (hev.mono fun z hz => by
      show g ((Mo.hullChart (fillH X) 0).1 z) = z
      rw [hgi (hullChart_fwd_spec hA 0 hz).1]
      exact (hullChart_fwd_spec hA 0 hz).2)
  have : (𝓝[H] (x : ℂ)).NeBot := GW1P.neBot_nhdsWithin_H (show (0 : ℝ) ≤ ((x : ℝ) : ℂ).im by simp)
  exact tendsto_nhds_unique h3 (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)

/-- **D34's entry is the right entry value.** -/
theorem entry_eq (hA : IsHPHull (fillH X)) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g (Mo.hullChart (fillH X) 0).2.1 H) {R x₀ : ℝ}
    (hrc : IsRightEntryChart X R ((Mo.hullChart (fillH X) 0).recenter x₀))
    (hfree : ∀ x : ℝ, R < x → ∃ r > 0, Disjoint (ball (x : ℂ) r) (fillH X)) {e : ℝ} (he : g (e : ℂ) = R)
    (hreal : ∀ y : ℝ, e < y → (g (y : ℂ)).im = 0) (hmono : StrictMonoOn (fun y : ℝ => (g (y : ℂ)).re) (Ici e)) :
    x₀ = e := by
  obtain ⟨-, ⟨e', he'1, he'2⟩, -, -⟩ := hrc
  have hfw : ∀ x : ℝ, R < x →
      Tendsto (Mo.hullChart (fillH X) 0).1 (𝓝[H] (x : ℂ)) (𝓝 (((e' x + x₀ : ℝ)) : ℂ)) := fun x hx => by
    have h := (he'1 x hx).add_const ((x₀ : ℝ) : ℂ)
    have e1 : (fun z => ((Mo.hullChart (fillH X) 0).recenter x₀).1 z + ((x₀ : ℝ) : ℂ)) =
        (Mo.hullChart (fillH X) 0).1 := funext fun z => by simp [Chart.recenter]
    rw [e1] at h
    convert h using 2
    push_cast; ring
  have hgw : ∀ x : ℝ, R < x → g (((e' x + x₀ : ℝ)) : ℂ) = x := fun x hx =>
    inv_of_fwd hA hgc hgi (hfree x hx) (hfw x hx)
  have hlim : Tendsto (fun x => e' x + x₀) (𝓝[>] R) (𝓝 x₀) := by simpa using he'2.add_const x₀
  have hgt : ∀ q ∈ Hbar, Tendsto (Mo.hullChart (fillH X) 0).2.1 (𝓝[H] q) (𝓝 (g q)) := fun q hq =>
    (tendsto_g_H hgc q hq).congr' (eventually_nhdsWithin_of_forall fun z hz => hgi hz)
  obtain ⟨C, hC⟩ := Lk.hullChart_ext_bounded hA hgt
  have hR : (g (e : ℂ)).re = R := by rw [he]; simp
  rcases lt_trichotomy x₀ e with hlt | heq | hgt'
  · exfalso
    have hev : ∀ᶠ x in 𝓝[>] R, R < x ∧ e' x + x₀ < e := by
      filter_upwards [self_mem_nhdsWithin, hlim (Iio_mem_nhds hlt)] with x hx1 hx2 using ⟨hx1, hx2⟩
    obtain ⟨x, hxR, hxe⟩ := hev.exists
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (show (0 : ℝ) ≤ (0 : ℂ).im by simp))
    set Y : ℝ := max e x + C + 1 with hYdef
    have heY : e ≤ Y := by have := le_max_left e x; linarith
    have hφc : ContinuousOn (fun y : ℝ => (g (y : ℂ)).re) (Icc e Y) :=
      Complex.continuous_re.comp_continuousOn
        (hgc.comp Complex.continuous_ofReal.continuousOn fun y _ => show (0 : ℝ) ≤ ((y : ℝ) : ℂ).im by simp)
    have hY : x ≤ (g (Y : ℂ)).re := by
      have h := hC (Y : ℂ) (show (0 : ℝ) ≤ ((Y : ℝ) : ℂ).im by simp)
      have h2 := Complex.abs_re_le_norm (g (Y : ℂ) - (Y : ℂ))
      simp only [Complex.sub_re, Complex.ofReal_re] at h2
      have := le_max_right e x
      have := neg_abs_le ((g (Y : ℂ)).re - Y)
      linarith
    obtain ⟨y', hy', hy'x⟩ := intermediate_value_Icc heY hφc ⟨by rw [hR]; exact hxR.le, hY⟩
    have hy'e : e < y' := by
      refine lt_of_le_of_ne hy'.1 fun h => ?_
      subst h
      simp only at hy'x
      rw [hR] at hy'x
      linarith
    have hgy' : g (y' : ℂ) = x := Complex.ext (by simpa using hy'x) (by simp [hreal y' hy'e])
    have := eq_of_inv_eq hA hgc hgi (hfw x hxR) hgy'
    linarith
  · exact heq
  · exfalso
    have hw : Tendsto (fun x => (((e' x + x₀ : ℝ)) : ℂ)) (𝓝[>] R) (𝓝[{z | 0 ≤ z.im}] (x₀ : ℂ)) :=
      tendsto_nhdsWithin_iff.2 ⟨(Complex.continuous_ofReal.tendsto _).comp hlim,
        Eventually.of_forall fun x => show (0 : ℝ) ≤ ((e' x + x₀ : ℝ) : ℂ).im by simp⟩
    have h1 := (hgc (x₀ : ℂ) (show (0 : ℝ) ≤ ((x₀ : ℝ) : ℂ).im by simp)).tendsto.comp hw
    have h2 : Tendsto (fun x => g (((e' x + x₀ : ℝ)) : ℂ)) (𝓝[>] R) (𝓝 (R : ℂ)) :=
      ((Complex.continuous_ofReal.tendsto R).mono_left nhdsWithin_le_nhds).congr'
        (eventually_nhdsWithin_of_forall fun x hx => (hgw x hx).symm)
    have h3 : g (x₀ : ℂ) = R := tendsto_nhds_unique h1 h2
    have h4 := hmono (show e ∈ Ici e from le_refl e) (show x₀ ∈ Ici e from hgt'.le) hgt'
    simp only [hR, h3, Complex.ofReal_re] at h4
    exact lt_irrefl _ h4

end Entry


/-! ### The read-back of the relative bad set -/

section Read

open Exist.StagedLaw PiecewiseConstantBoundaryData

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The original right-bad real points right of `R`** for B's flow (angle `−π/2`). -/
def origBadR (κ : ℝ) (b : ℝ → ℝ) (R : ℝ) : Set ℝ :=
  {x | R < x ∧ Sec4.cumWeightRight κ (rightLim b x + -(Real.pi / 2) * chiC κ) ≤ -2}

variable {g : ℂ → ℂ} {R x₀ : ℝ} {β : Restart.BoundaryWord} {Fy : Finset ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ}
  {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **A bad relative point is read back into the closure of the original right-bad points**: right-bad relative
points read original heights through the free ray; left-bad relative points do not exist (D34's left clause). -/
theorem readback_bad (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hR : g (x₀ : ℂ) = R) (hreal : ∀ y : ℝ, x₀ < y → (g (y : ℂ)).im = 0)
    (hmono : StrictMonoOn (fun y : ℝ => (g (y : ℂ)).re) (Ici x₀))
    (hFy : ∀ y : ℝ, x₀ < y → y ∉ Fy → (g (y : ℂ)).re ∉ jumps → β.fn y = b (g (y : ℂ)).re)
    (hleft : ∀ y : ℝ, y < x₀ → y ∉ β.jumps → -2 < Sec4.cumWeightLeft κ (β.fn y + -(Real.pi / 2) * chiC κ))
    (hft : Restart.FCDet.IsFlowType κ (-(Real.pi / 2)) (BoundaryWord.shiftW x₀ β) xL xR ρL ρR) {z : ℂ}
    (hz : z ∈ Vr.badSet xL xR ρL ρR) : ∃ x : ℝ, g (z + x₀) = x ∧ x ∈ closure (origBadR κ b R) := by
  classical
  obtain ⟨him, hz'⟩ := hz
  set y := z.re with hydef
  have hze : z + (x₀ : ℂ) = ((y + x₀ : ℝ) : ℂ) := Complex.ext (by simp [hydef]) (by simp [him])
  have hRe : (g (x₀ : ℂ)).re = R := by rw [hR]; simp
  rcases hz' with ⟨hy, hw⟩ | ⟨hy, hw⟩
  · obtain ⟨y₁, hy₁, hwr⟩ := Vt.wR_eq_of_isFlowType hκ hft hy
    set f : ℝ → ℝ := fun y'' => (g ((y'' + x₀ : ℝ) : ℂ)).re with hfdef
    have hinj : InjOn f (Ioi 0) := fun a ha a' ha' he =>
      by
        have h1 := hmono.injOn (show a + x₀ ∈ Ici x₀ by simp only [mem_Ici]; linarith [mem_Ioi.1 ha])
          (show a' + x₀ ∈ Ici x₀ by simp only [mem_Ici]; linarith [mem_Ioi.1 ha']) he
        linarith
    have hT : (Ioi (0 : ℝ) ∩ f ⁻¹' (jumps : Set ℝ)).Finite :=
      Set.Finite.of_finite_image ((jumps.finite_toSet).subset (image_subset_iff.2 fun _ h => h.2))
        (hinj.mono inter_subset_left)
    set E : Finset ℝ := (BoundaryWord.shiftW x₀ β).jumps ∪ Fy.image (· - x₀) with hE
    have hev : ∀ᶠ y'' in 𝓝[>] y, ∃ x ∈ origBadR κ b R, g ((y'' + x₀ : ℝ) : ℂ) = (x : ℂ) := by
      have h1 : ∀ᶠ y'' in 𝓝[>] y, y'' < y₁ := (gt_mem_nhds hy₁).filter_mono nhdsWithin_le_nhds
      have h2 : ∀ᶠ y'' in 𝓝[>] y, y'' ∉ ((E : Set ℝ) ∪ (Ioi (0 : ℝ) ∩ f ⁻¹' (jumps : Set ℝ))) :=
        (GW1W.eventually_notMem_of_finite (E.finite_toSet.union hT) y).filter_mono
          (nhdsWithin_mono _ fun z hz => ne_of_gt hz)
      filter_upwards [self_mem_nhdsWithin, h1, h2] with y'' hy'' hy''₁ hS
      have hpos : 0 < y'' := lt_of_le_of_lt hy hy''
      have hcwJ : y'' ∉ (BoundaryWord.shiftW x₀ β).jumps := fun h =>
        hS (Or.inl (Finset.mem_coe.2 (Finset.mem_union_left _ h)))
      have hFy' : y'' + x₀ ∉ Fy := fun h =>
        hS (Or.inl (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_image.2 ⟨y'' + x₀, h, by ring⟩))))
      have hJ : f y'' ∉ jumps := fun h => hS (Or.inr ⟨hpos, h⟩)
      have hgt : x₀ < y'' + x₀ := by linarith
      have hgx : g ((y'' + x₀ : ℝ) : ℂ) = ((f y'' : ℝ) : ℂ) :=
        Complex.ext (by simp [hfdef]) (by rw [Complex.ofReal_im]; exact hreal _ hgt)
      have hxR : R < f y'' := by
        have := hmono (show x₀ ∈ Ici x₀ from le_refl x₀) (show y'' + x₀ ∈ Ici x₀ from hgt.le) hgt
        simp only [hRe] at this
        exact this
      have hfn : β.fn (y'' + x₀) = b (f y'') := hFy _ hgt hFy' hJ
      have hwr' := hwr y'' hy'' hy''₁ hcwJ
      rw [BoundaryWord.fn_shiftW, hfn] at hwr'
      refine ⟨f y'', ⟨hxR, ?_⟩, hgx⟩
      rw [rightLim_eq_of_notMem hb hJ, ← hwr']
      exact hw
    obtain ⟨x, hx, hcl⟩ := Vt.exists_real_mem_closure_of_tendsto
      (Vt.tendsto_g_real (m := x₀) hgc (𝓝[>] y) nhdsWithin_le_nhds) hev
    exact ⟨x, by rw [hze]; exact hx, hcl⟩
  · exfalso
    obtain ⟨y₁, hy₁, hwl⟩ := Vt.wL_eq_of_isFlowType hκ hft hy
    obtain ⟨y'', ⟨h1, h2⟩, hn⟩ := (Set.Ioo_infinite hy₁).exists_notMem_finset
      ((BoundaryWord.shiftW x₀ β).jumps ∪ β.jumps.image (· - x₀))
    have hwl' := hwl y'' h1 h2 fun h => hn (Finset.mem_union_left _ h)
    rw [BoundaryWord.fn_shiftW] at hwl'
    have hl := hleft (y'' + x₀) (by linarith) fun h =>
      hn (Finset.mem_union_right _ (Finset.mem_image.2 ⟨y'' + x₀, h, by ring⟩))
    linarith

/-- **The closure of the relative bad set is read back into the closure of the original right-bad points.** -/
theorem readback_closure (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hR : g (x₀ : ℂ) = R) (hreal : ∀ y : ℝ, x₀ < y → (g (y : ℂ)).im = 0)
    (hmono : StrictMonoOn (fun y : ℝ => (g (y : ℂ)).re) (Ici x₀))
    (hFy : ∀ y : ℝ, x₀ < y → y ∉ Fy → (g (y : ℂ)).re ∉ jumps → β.fn y = b (g (y : ℂ)).re)
    (hleft : ∀ y : ℝ, y < x₀ → y ∉ β.jumps → -2 < Sec4.cumWeightLeft κ (β.fn y + -(Real.pi / 2) * chiC κ))
    (hft : Restart.FCDet.IsFlowType κ (-(Real.pi / 2)) (BoundaryWord.shiftW x₀ β) xL xR ρL ρR) {z : ℂ}
    (hz : z ∈ closure (Vr.badSet xL xR ρL ρR)) : ∃ x : ℝ, g (z + x₀) = x ∧ x ∈ closure (origBadR κ b R) := by
  set gr : ℂ → ℂ := fun w => g (w + x₀) with hgr
  have hgrc : ContinuousOn gr {z | 0 ≤ z.im} :=
    hgc.comp (continuous_id.add continuous_const).continuousOn fun w (hw : 0 ≤ w.im) =>
      show 0 ≤ (w + (x₀ : ℂ)).im by simpa using hw
  have hreal' : closure (Vr.badSet xL xR ρL ρR) ⊆ {w : ℂ | 0 ≤ w.im} :=
    closure_minimal (fun w hw => le_of_eq (Vr.badSet_subset_real hw).symm)
      (isClosed_le continuous_const Complex.continuous_im)
  set C : Set ℂ := ((↑) : ℝ → ℂ) '' closure (origBadR κ b R) with hC
  have hCc : IsClosed C := Complex.isometry_ofReal.isClosedEmbedding.isClosedMap _ isClosed_closure
  have hsub : gr '' Vr.badSet xL xR ρL ρR ⊆ C := by
    rintro _ ⟨z', hz', rfl⟩
    obtain ⟨x, hx, hcl⟩ := readback_bad hκ hb hgc hR hreal hmono hFy hleft hft hz'
    exact ⟨x, hcl, hx.symm⟩
  have himg := (hgrc.mono hreal').image_closure (s := Vr.badSet xL xR ρL ρR)
  obtain ⟨x, hx, hxe⟩ := closure_minimal hsub hCc (himg ⟨z, hz, rfl⟩)
  exact ⟨x, hxe.symm, hx⟩

end Read

end InteractingSLE.Theorem14.SB.Ne
