import QuantumZipper.Proofs.Zipper.FieldLawler2Max
import QuantumZipper.Common.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Maximum principles with finitely many exceptional boundary points

Packet GEO-STEP (`planning/INFRA-GEO.md` §4). Lindelöf's maximum principle
(Garnett–Marshall, *Harmonic Measure*, Ch. I, Lemma 1.1) on unbounded open sets without a
boundary condition at `∞`, for bounded harmonic functions, via a positive harmonic barrier
tending to `+∞` at `∞`.

* `InteractingSLE.harmonic_le_zero_of_barrier`: the general statement, from QZ's
  `QuantumZipper.FieldLawler.fl2_harm_le_zero_off_finite` applied to `f − ε b`.
* `InteractingSLE.le_zero_of_harmonicOnNhd_H`, `InteractingSLE.eqOn_of_tendsto_sub_H`: the
  upper half-plane `ℍ`, with the barrier `log ‖z + i‖`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H Hbar)

namespace InteractingSLE

/-- **Lindelöf's maximum principle with a barrier.** Let `U ⊆ ℂ` be open, `f` harmonic on `U` and
bounded above, with `limsup f ≤ 0` at every frontier point of `U` outside the finite set `E`.
If `U` carries a nonnegative harmonic function `b` tending to `+∞` at `∞`, then `f ≤ 0` on `U`
(no condition on `f` at `∞` is needed). -/
theorem harmonic_le_zero_of_barrier {U : Set ℂ} {f b : ℂ → ℝ} (E : Finset ℂ) (hU : IsOpen U)
    (hf : InnerProductSpace.HarmonicOnNhd f U) (hbd : BddAbove (f '' U))
    (hfr : ∀ x₀ ∈ frontier U, x₀ ∉ E → ∀ ε > 0, ∀ᶠ y in 𝓝[U] x₀, f y ≤ ε)
    (hb : InnerProductSpace.HarmonicOnNhd b U) (hb0 : ∀ y ∈ U, 0 ≤ b y)
    (hbinf : ∀ M : ℝ, ∃ R : ℝ, ∀ y ∈ U, R ≤ ‖y‖ → M ≤ b y) :
    ∀ y ∈ U, f y ≤ 0 := by
  obtain ⟨M, hM⟩ := hbd
  have hMU : ∀ y ∈ U, f y ≤ M := fun y hy => hM ⟨y, hy, rfl⟩
  -- for every `ε > 0`, `f ≤ ε b` on `U`
  have key : ∀ ε : ℝ, 0 < ε → ∀ y ∈ U, f y ≤ ε * b y := by
    intro ε hε
    have hg : InnerProductSpace.HarmonicOnNhd (f - ε • b) U := hf.sub (hb.const_smul)
    have hle := QuantumZipper.FieldLawler.fl2_harm_le_zero_off_finite E hU hg ?_ ?_ ?_
    · intro y hy
      have := hle y hy
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
      linarith
    · refine ⟨M, ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [hMU y hy, hb0 y hy]
    · intro x₀ hx₀ hx₀E ε' hε'
      have h1 := hfr x₀ hx₀ hx₀E ε' hε'
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h1
      obtain ⟨δ, hδ, hδ'⟩ := h1
      refine ⟨δ, hδ, fun y hy hyd => ?_⟩
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [hδ' hyd hy, hb0 y hy]
    · intro ε' hε'
      obtain ⟨R, hR⟩ := hbinf (M / ε)
      refine ⟨R, fun y hy hRy => ?_⟩
      have h1 := hR y hy hRy
      have h2 : M ≤ ε * b y := by
        rw [div_le_iff₀ hε] at h1
        linarith
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linarith [hMU y hy]
  intro y hy
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hb1 : 0 < b y + 1 := by linarith [hb0 y hy]
  have h1 := key (δ / (b y + 1)) (div_pos hδ hb1) y hy
  have h2 : δ / (b y + 1) * b y ≤ δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hb1]
    nlinarith [hb0 y hy]
  linarith

/-- The barrier `log ‖z + i‖` on `ℍ`. -/
private theorem harmonicOnNhd_log_norm_add_I :
    InnerProductSpace.HarmonicOnNhd (fun z : ℂ => Real.log ‖z + I‖) H := by
  intro z hz
  have hz' : z + I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp only [add_im, I_im, zero_im] at this
    have hz0 : 0 < z.im := hz
    linarith
  exact (analyticAt_id.add analyticAt_const).harmonicAt_log_norm hz'

private theorem one_le_norm_add_I {z : ℂ} (hz : z ∈ H) : 1 ≤ ‖z + I‖ := by
  have hz0 : 0 < z.im := hz
  calc (1 : ℝ) ≤ |(z + I).im| := by
        simp only [add_im, I_im]
        rw [abs_of_pos (by linarith)]
        linarith
    _ ≤ ‖z + I‖ := Complex.abs_im_le_norm _

/-- **Lindelöf's maximum principle on `ℍ`** (bounded version, finitely many exceptional boundary
points): a harmonic function on `ℍ`, bounded above, with `limsup ≤ 0` at every real point outside
the finite set `E`, is `≤ 0` on `ℍ`. -/
theorem le_zero_of_harmonicOnNhd_H {f : ℂ → ℝ} (E : Finset ℝ)
    (hf : InnerProductSpace.HarmonicOnNhd f H) (hbd : BddAbove (f '' H))
    (hfr : ∀ t : ℝ, t ∉ E → ∀ ε > 0, ∀ᶠ z in 𝓝[H] (t : ℂ), f z ≤ ε) :
    ∀ z ∈ H, f z ≤ 0 := by
  have hHo : IsOpen H := isOpen_lt continuous_const Complex.continuous_im
  refine harmonic_le_zero_of_barrier (E.image ((↑) : ℝ → ℂ)) hHo hf hbd ?_
    harmonicOnNhd_log_norm_add_I
    (fun y hy => Real.log_nonneg (one_le_norm_add_I hy)) ?_
  · intro x₀ hx₀ hx₀E
    have him : x₀.im = 0 := by
      have : x₀ ∈ frontier {z : ℂ | 0 < z.im} := hx₀
      rw [Complex.frontier_setOfPred_lt_im] at this
      exact this
    have hx : ((x₀.re : ℝ) : ℂ) = x₀ := Complex.ext (by simp) (by simp [him])
    have hre : x₀.re ∉ E := by
      intro h
      exact hx₀E (Finset.mem_image.2 ⟨x₀.re, h, hx⟩)
    rw [← hx]
    exact hfr x₀.re hre
  · intro M
    refine ⟨Real.exp M + 1, fun y hy hRy => ?_⟩
    have h1 : Real.exp M ≤ ‖y + I‖ := by
      have := norm_sub_norm_le y (-I)
      simp only [sub_neg_eq_add, norm_neg, Complex.norm_I] at this
      linarith
    exact (Real.le_log_iff_exp_le ((Real.exp_pos M).trans_le h1)).2 h1

/-- Two bounded harmonic functions on `ℍ` whose difference tends to `0` at every real point
outside a finite set agree on `ℍ`. -/
theorem eqOn_of_tendsto_sub_H {u w : ℂ → ℝ} (E : Finset ℝ)
    (hu : InnerProductSpace.HarmonicOnNhd u H) (hw : InnerProductSpace.HarmonicOnNhd w H)
    (hub : Bornology.IsBounded (u '' H)) (hwb : Bornology.IsBounded (w '' H))
    (hlim : ∀ t : ℝ, t ∉ E → Tendsto (fun z => u z - w z) (𝓝[H] (t : ℂ)) (𝓝 0)) :
    EqOn u w H := by
  obtain ⟨Cu, hCu⟩ := isBounded_iff_forall_norm_le.1 hub
  obtain ⟨Cw, hCw⟩ := isBounded_iff_forall_norm_le.1 hwb
  have bu : ∀ z ∈ H, |u z| ≤ Cu := fun z hz => hCu _ ⟨z, hz, rfl⟩
  have bw : ∀ z ∈ H, |w z| ≤ Cw := fun z hz => hCw _ ⟨z, hz, rfl⟩
  have h1 := le_zero_of_harmonicOnNhd_H E (hu.sub hw) ?_ ?_
  have h2 := le_zero_of_harmonicOnNhd_H E (hw.sub hu) ?_ ?_
  · intro z hz
    have a := h1 z hz
    have b := h2 z hz
    simp only [Pi.sub_apply] at a b
    linarith
  · refine ⟨Cu + Cw, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    simp only [Pi.sub_apply]
    linarith [abs_le.1 (bu z hz), abs_le.1 (bw z hz)]
  · intro t ht ε hε
    have := (hlim t ht).neg
    rw [neg_zero] at this
    filter_upwards [this.eventually (gt_mem_nhds hε)] with z hz
    simp only [Pi.sub_apply]
    linarith
  · refine ⟨Cu + Cw, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    simp only [Pi.sub_apply]
    linarith [abs_le.1 (bu z hz), abs_le.1 (bw z hz)]
  · intro t ht ε hε
    filter_upwards [(hlim t ht).eventually (gt_mem_nhds hε)] with z hz
    simp only [Pi.sub_apply]
    linarith

end InteractingSLE
