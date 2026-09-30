import QuantumZipper.Proofs.Zipper.FieldLawlerSubExcDefs
import QuantumZipper.Proofs.Thm18.LWExc3Key
import QuantumZipper.Proofs.Thm18.LWExc2Refl

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-EXCLOWER, normalized case, part A: the strip near `[0, ∞)` and `∂_y h` from below

For a crosscut `η` of `ℍ` from `−1` to `a ≤ −1` (no bound on `diam η`):
* `flSub_strip`: `closure η ∩ {Re ≥ −1/2}` stays at height `≥ ε > 0` (compactness);
* `flSub_strip_mem`: the strip `{0 < Im < ε, Re > −1/2}` lies in `H_η` (it is convex, misses `η`,
  and is unbounded);
* `flSub_yDer_ge`: a local version of `lwExc2_yDer_ge` (LWExc2Lower.lean) with the hypothesis
  `diam η ≤ 1/2` replaced by what its proof uses: near `x`, `ℍ` lies in `H_η` and `ℝ` is off
  `closure η`. It rests on the reflection principle (Ahlfors, *Complex Analysis*, Ch. 4 §6.5,
  Thm 24, `harmReflectStmt_holds`).
Own elementary arguments (generalizing the repository's proof of Lawler–Werness Lemma 4.3).
-/

noncomputable section

open MeasureTheory Filter Set Metric Complex
open scoped Topology ENNReal

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

/-- The closure of `η` stays away from `ℝ` on `{Re ≥ −1/2}`. -/
theorem flSub_strip {η : ℝ → ℂ} {a : ℝ} (hη : IsCrosscutH η)
    (h0 : Tendsto η (𝓝[>] 0) (𝓝 (-1 : ℂ))) (h1 : Tendsto η (𝓝[<] 1) (𝓝 (a : ℂ)))
    (ha : a ≤ -1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ w ∈ closure (arcH η), -1 / 2 ≤ w.re → ε ≤ w.im := by
  set K : Set ℂ := closure (arcH η) ∩ {w | -1 / 2 ≤ w.re} with hK
  have hKc : IsCompact K :=
    (lwExc_arc_isBounded hη).closure.isCompact_closure.inter_right
      (isClosed_le continuous_const Complex.continuous_re) |>.of_isClosed_subset
      (isClosed_closure.inter (isClosed_le continuous_const Complex.continuous_re))
      (fun w hw => ⟨subset_closure hw.1, hw.2⟩)
  have hclim : ∀ w ∈ closure (arcH η), 0 ≤ w.im := by
    intro w hw
    have hsub : closure (arcH η) ⊆ {v : ℂ | 0 ≤ v.im} :=
      closure_minimal (fun v hv => by
        obtain ⟨s, hs, rfl⟩ := hv
        exact le_of_lt (show 0 < (η s).im from hη.2.2.1 hs)) (isClosed_le continuous_const Complex.continuous_im)
    exact hsub hw
  rcases K.eq_empty_or_nonempty with hE | hne
  · refine ⟨1, one_pos, fun w hw hwr => ?_⟩
    have : w ∈ K := ⟨hw, hwr⟩
    rw [hE] at this; simp at this
  · obtain ⟨w0, hw0K, hmin⟩ := hKc.exists_isMinOn hne Complex.continuous_im.continuousOn
    have hpos : 0 < w0.im := by
      rcases (hclim w0 hw0K.1).lt_or_eq with hp | hz
      · exact hp
      · exfalso
        have hre : -1 / 2 ≤ w0.re := hw0K.2
        refine lw3_real_not_mem_closure hη h0 h1 hz.symm ?_ ?_ hw0K.1
        · intro he; rw [he] at hre; norm_num at hre
        · intro he; rw [he] at hre; simp at hre; linarith
    exact ⟨w0.im, hpos, fun w hw hwr => hmin ⟨hw, hwr⟩⟩

/-- The strip `{0 < Im < ε, Re > −1/2}` lies in `H_η`. -/
theorem flSub_strip_mem {η : ℝ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hstr : ∀ w ∈ closure (arcH η), -1 / 2 ≤ w.re → ε ≤ w.im) {w : ℂ}
    (hwre : -1 / 2 < w.re) (hwim : 0 < w.im) (hwε : w.im < ε) : w ∈ hullComp η := by
  set Q : Set ℂ := {v | (0 : ℝ) < Complex.imLm v} ∩ {v | Complex.imLm v < ε} ∩
    {v | (-1 / 2 : ℝ) < Complex.reLm v} with hQ
  have hQc : Convex ℝ Q :=
    ((convex_halfSpace_gt Complex.imLm.isLinear 0).inter
      (convex_halfSpace_lt Complex.imLm.isLinear ε)).inter
      (convex_halfSpace_gt Complex.reLm.isLinear (-1 / 2))
  have hmemQ : ∀ v : ℂ, v ∈ Q ↔ (0 < v.im ∧ v.im < ε) ∧ -1 / 2 < v.re := fun v => by
    simp [hQ]
  have hQS : Q ⊆ H \ arcH η := by
    intro v hv
    obtain ⟨⟨hvi, hvε⟩, hvr⟩ := (hmemQ v).1 hv
    refine ⟨hvi, fun hva => ?_⟩
    have := hstr v (subset_closure hva) hvr.le
    linarith
  have hwQ : w ∈ Q := (hmemQ w).2 ⟨⟨hwim, hwε⟩, hwre⟩
  have hsub := hQc.isPreconnected.subset_connectedComponentIn hwQ hQS
  refine ⟨hQS hwQ, fun hb => ?_⟩
  obtain ⟨R, hR⟩ := (hb.subset hsub).subset_closedBall 0
  set v : ℂ := ((|R| + 1 : ℝ) : ℂ) + ((ε / 2 : ℝ) : ℂ) * I with hv
  have hvQ : v ∈ Q := (hmemQ _).2 ⟨⟨by simp [hv]; linarith, by simp [hv]; linarith⟩,
    by simp [hv]; linarith [abs_nonneg R]⟩
  have h1 := hR hvQ
  rw [mem_closedBall, dist_zero_right] at h1
  have h2 : |R| + 1 ≤ ‖v‖ := by
    have h4 := Complex.abs_re_le_norm v
    have h5 : v.re = |R| + 1 := by simp [hv]
    rw [h5, abs_of_pos (by positivity)] at h4
    exact h4
  linarith [le_abs_self R]

/-- **`∂_y h(x)` from below**, local form of `lwExc2_yDer_ge`: if near the real point `x`
(ball of radius `ρ`) the upper half-plane lies in `H_η` and the real line misses `closure η`,
then `h(x + iy) ≥ y c` for `0 < y < ρ` gives `c ≤ ∂_y h(x)`. -/
theorem flSub_yDer_ge {η : ℝ → ℂ} {h : ℂ → ℝ}
    (hm : IsHarmMeas (hullComp η) (arcH η) h) {x c ρ : ℝ} (hr0 : 0 < ρ)
    (hsubU : H ∩ ball (x : ℂ) ρ ⊆ hullComp η)
    (hna : ∀ w ∈ ball (x : ℂ) ρ, w.im = 0 → w ∉ closure (arcH η))
    (hb : ∀ y : ℝ, 0 < y → y < ρ → y * c ≤ h ((x : ℂ) + (y : ℂ) * I)) : c ≤ yDer h x := by
  have hR := harmReflectStmt_holds
  set r := ρ with hrdef
  set v : ℂ → ℝ := fun z => if 0 < z.im then h z else 0 with hv
  have hHo : IsOpen (H ∩ ball (x : ℂ) r) :=
    (isOpen_lt continuous_const Complex.continuous_im).inter isOpen_ball
  have hveq : EqOn v h (H ∩ ball (x : ℂ) r) := fun w hw => by
    simp only [hv, if_pos (show 0 < w.im from hw.1)]
  have hvharm : InnerProductSpace.HarmonicOnNhd v (H ∩ ball (x : ℂ) r) := by
    intro w hw
    refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp (hm.harm w (hsubU hw))
    filter_upwards [hHo.mem_nhds hw] with u hu
    exact (hveq hu).symm
  have hvcont : ContinuousOn v (Hbar ∩ ball (x : ℂ) r) := by
    intro w ⟨hwH, hwB⟩
    have hwH' : 0 ≤ w.im := hwH
    rcases hwH'.lt_or_eq with hpos | hzero
    · have hwU : w ∈ H ∩ ball (x : ℂ) r := ⟨hpos, hwB⟩
      have hca : ContinuousAt v w :=
        ((hvharm w hwU).1.continuousAt.congr (by
          filter_upwards [hHo.mem_nhds hwU] with u hu; rfl))
      exact hca.continuousWithinAt
    · have hwU : w ∉ hullComp η := fun hU => by
        have : 0 < w.im := (lwExc_hullComp_subset_H η hU); linarith
      have hwcl : w ∈ closure (hullComp η) := by
        refine mem_closure_of_tendsto (f := fun y : ℝ => w + (y : ℂ) * I) (b := 𝓝[>] (0 : ℝ))
          ?_ ?_
        · have : Tendsto (fun y : ℝ => w + (y : ℂ) * I) (𝓝 0) (𝓝 (w + ((0 : ℝ) : ℂ) * I)) :=
            (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).tendsto 0
          simpa using this.mono_left nhdsWithin_le_nhds
        · have ht : Tendsto (fun y : ℝ => w + (y : ℂ) * I) (𝓝[>] 0) (𝓝 w) := by
            have : Tendsto (fun y : ℝ => w + (y : ℂ) * I) (𝓝 0) (𝓝 (w + ((0 : ℝ) : ℂ) * I)) :=
              (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).tendsto 0
            simpa using this.mono_left nhdsWithin_le_nhds
          filter_upwards [self_mem_nhdsWithin, ht (isOpen_ball.mem_nhds hwB)] with y (hy : 0 < y)
            hyB
          exact hsubU ⟨show 0 < (w + (y : ℂ) * I).im by simp [← hzero, hy], hyB⟩
      have hwfr : w ∈ frontier (hullComp η) :=
        ⟨hwcl, fun hi => hwU (interior_subset hi)⟩
      have hwna : w ∉ closure (arcH η) := hna w hwB hzero.symm
      have ht := hm.zero w hwfr hwna
      have hvw : v w = 0 := by simp [hv, ← hzero]
      rw [ContinuousWithinAt, hvw]
      rw [Metric.tendsto_nhdsWithin_nhds] at ht ⊢
      intro ε hε
      obtain ⟨δ, hδ, hδs⟩ := ht ε hε
      obtain ⟨δ', hδ', hδ'B⟩ := Metric.isOpen_iff.1 isOpen_ball w hwB
      refine ⟨min δ δ', lt_min hδ hδ', fun u hu hdu => ?_⟩
      by_cases hui : 0 < u.im
      · have huU : u ∈ hullComp η := hsubU ⟨hui, hu.2⟩
        simp only [hv, if_pos hui]
        exact hδs huU (lt_of_lt_of_le hdu (min_le_left _ _))
      · simp [hv, if_neg hui, hε]
  have hvzero : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → v z = 0 := fun z _ hz => by
    simp [hv, hz]
  obtain ⟨ρ', hρ, hρr, V, hVh, hVeq⟩ := hR v x r hr0 hvharm hvcont hvzero
  have hxB : (x : ℂ) ∈ ball (x : ℂ) ρ' := mem_ball_self hρ
  have hVx : V x = 0 := by
    rw [hVeq ⟨show (0 : ℝ) ≤ ((x : ℂ)).im by simp, hxB⟩]
    exact hvzero _ (mem_ball_self hr0) (by simp)
  have hVd : HasFDerivAt V (fderiv ℝ V x) (x : ℂ) :=
    ((hVh x hxB).1.differentiableAt (by norm_num)).hasFDerivAt
  have hpath : HasDerivAt (fun y : ℝ => (x : ℂ) + (y : ℂ) * I) I 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const I).const_add (x : ℂ)
    convert h1 using 1 <;> first | rfl | simp
  have hVd' : HasFDerivAt V (fderiv ℝ V x) ((x : ℂ) + ((0 : ℝ) : ℂ) * I) := by
    rw [show (x : ℂ) + ((0 : ℝ) : ℂ) * I = x by simp]; exact hVd
  have hcomp : HasDerivAt (fun y : ℝ => V ((x : ℂ) + (y : ℂ) * I)) (fderiv ℝ V x I) 0 :=
    hVd'.comp_hasDerivAt (0 : ℝ) hpath
  have hslope := hcomp.tendsto_slope.mono_left (nhdsGT_le_nhdsNE (0 : ℝ))
  have hev : (fun y : ℝ => h ((x : ℂ) + (y : ℂ) * I) / y) =ᶠ[𝓝[>] 0]
      slope (fun y : ℝ => V ((x : ℂ) + (y : ℂ) * I)) 0 := by
    filter_upwards [self_mem_nhdsWithin, (Ioo_mem_nhdsGT hρ : Ioo (0 : ℝ) ρ' ∈ 𝓝[>] 0)]
      with y (hy : 0 < y) hyr
    have hyB : (x : ℂ) + (y : ℂ) * I ∈ ball (x : ℂ) ρ' := by
      rw [mem_ball, dist_eq_norm]; simp [abs_of_pos hy]; exact hyr.2
    have hyH : (x : ℂ) + (y : ℂ) * I ∈ H := by simp [H, hy]
    rw [slope_def_field, hVeq ⟨H_subset_Hbar hyH, hyB⟩,
      hveq ⟨hyH, ball_subset_ball hρr hyB⟩]
    simp [hVx]
  have hlim : Tendsto (fun y : ℝ => h ((x : ℂ) + (y : ℂ) * I) / y) (𝓝[>] 0)
      (𝓝 (fderiv ℝ V x I)) := hslope.congr' hev.symm
  have hyD : yDer h x = fderiv ℝ V x I := by
    unfold yDer
    rw [if_pos ⟨_, hlim⟩, hlim.limUnder_eq]
  rw [hyD]
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin, (Ioo_mem_nhdsGT hr0 : Ioo (0 : ℝ) r ∈ 𝓝[>] 0)]
    with y (hy : 0 < y) hy1
  rw [le_div_iff₀ hy]; linarith [hb y hy hy1.2]

end FieldLawler
end QuantumZipper
