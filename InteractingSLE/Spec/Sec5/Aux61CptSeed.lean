/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61CptMirror
import InteractingSLE.Spec.Sec5.Aux61NjGerm
import InteractingSLE.Spec.Sec5.Aux61CmpSeedCollar

/-!
# Seed accesses on a fixed chart interval (deterministic)

Packet PROVE-AUX61-CAPTURE (rulings R103, R103a). `exists_seedAccessNP`: let `F_r` be the inverse own Loewner map at the
restart and `c` the retained chart, whose domain is a component of `ℍ ∖ (K ∪ η[0, r])`. If

* `F_r(ℍ ∩ B(0, δ))` misses `K` and its real boundary values miss the target `1` (the free own collar),
* some smaller collar maps into the chart domain and `c ∘ F_r → 0` at `0` (the current access of the geometry), and
* on the chart half-disc `ℍ ∩ B(0, ε)` the own forward map of the inverse chart has modulus `≤ δ' < δ`,

then every real chart point `b` with `|b| < ε` is reached through the collar: there is a real `t`, `|t| ≤ δ'`, of the
sign of `b`, with `SeedAccessNP W r c t b` (NOJUMP's pinch-free seed access). The collar maps into the domain by
connectivity, `c ∘ F_r` reflects across `(−δ, δ)` (`Aux61Cmp.exists_isPosReflect_collar`), and `t` is a limit point of
`F_r⁻¹ ∘ c⁻¹` at `b` (compactness of `B̄(0, δ')`). The reflection is increasing on the real segment
(`IsPosReflect.strictMonoOn_re`).

Deterministic; R48/R77 respected. Nothing here replaces a source theorem.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open scoped NNReal ComplexConjugate

namespace InteractingSLE.Sec5.Aux61Cpt
open WangWu Aux61TwoS Aux61Cmp Aux61Restart

/-- **The real restriction of a positive reflection is strictly increasing.** -/
theorem IsPosReflect.strictMonoOn_re {Ξ G : ℂ → ℂ} {v r : ℝ} (h : IsPosReflect Ξ G v r) :
    StrictMonoOn (fun x : ℝ => (G x).re) (Ioo (v - r) (v + r)) := by
  have hmem : ∀ x ∈ Ioo (v - r) (v + r), ((x : ℝ) : ℂ) ∈ ball (v : ℂ) r := fun x hx => by
    rw [mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  have hd : ∀ x ∈ Ioo (v - r) (v + r), HasDerivAt (fun y : ℝ => (G y).re) (deriv G x).re x := fun x hx =>
    ((h.diff.differentiableAt (isOpen_ball.mem_nhds (hmem x hx))).hasDerivAt).real_of_complex
  refine strictMonoOn_of_deriv_pos (convex_Ioo _ _) (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    fun x hx => ?_
  rw [interior_Ioo] at hx
  rw [(hd x hx).deriv]
  exact (h.deriv_pos (hmem x hx)).2

section Seed

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {r : ℝ}
  (hW : Continuous W) (hW0 : W 0 = 0) (hη : IsLoewnerTrace W η) (hr : 0 < r)
  {c : Chart} (hc : c.IsConformal) (hsub : (c.dom : Set ℂ) ⊆ H \ fwdHull W r)
  (hB : IsHPHull (stripTargetHull (c.dom : Set ℂ))) {a ξ : ℝ}
  (hscale : EqOn c.1 (fun z => (a : ℂ) *
      (ConformalImage.mapOut (stripTargetHull (c.dom : Set ℂ)) (stripRightRetarget z) - ξ)) c.dom)

include hW hW0 hη hr hc hsub hB hscale in
/-- **Seed accesses on a fixed chart interval.** -/
theorem exists_seedAccessNP {K : Set ℂ} {b' : ℂ}
    (hdom : (c.dom : Set ℂ) = restartComponent K η r b')
    (hhull : fwdHull W r = η '' Ioc 0 r) (hη0 : η 0 = 0)
    {δ δ' ε : ℝ} (hδ : 0 < δ) (hδ' : δ' < δ)
    (hK : ∀ z ∈ H ∩ ball (0 : ℂ) δ, fwdMapInv W r z ∉ K)
    (hone : ∀ x : ℝ, |x| < δ → extendFrom H (fwdMapInv W r) x ≠ 1)
    (hcol₀ : ∃ δ₀ > 0, MapsTo (fwdMapInv W r) (ball 0 δ₀ ∩ H) c.dom)
    (hcur : Tendsto (fun z => c.1 (fwdMapInv W r z)) (𝓝[H] 0) (𝓝 0))
    (hseed : ∀ ζ ∈ H ∩ ball (0 : ℂ) ε, ‖fwdMap W r (c.2.1 ζ)‖ ≤ δ') :
    ∀ b : ℝ, |b| < ε → ∃ t : ℝ, |t| ≤ δ' ∧ (0 < b → 0 < t) ∧ (b < 0 → t < 0) ∧ (b = 0 → t = 0) ∧
      Aux61Nj.SeedAccessNP W r c t b := by
  -- the free collar maps into the chart domain
  have hcol : MapsTo (fwdMapInv W r) (ball 0 δ ∩ H) c.dom := by
    obtain ⟨δ₀, hδ₀, hcol₀⟩ := hcol₀
    set m : ℝ := min δ δ₀ / 2 with hm
    have hm0 : 0 < m := by rw [hm]; exact half_pos (lt_min hδ hδ₀)
    have hz₀ : (m : ℂ) * I ∈ ball (0 : ℂ) δ₀ ∩ H := by
      refine ⟨?_, ?_⟩
      · rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
          Real.norm_eq_abs, abs_of_pos hm0]
        linarith [min_le_right δ δ₀]
      · change (0 : ℝ) < ((m : ℂ) * I).im
        simp [hm0]
    have hz₀' : (m : ℂ) * I ∈ ball (0 : ℂ) δ ∩ H := by
      refine ⟨?_, hz₀.2⟩
      rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs, abs_of_pos hm0]
      linarith [min_le_left δ δ₀]
    have hU : IsPreconnected (fwdMapInv W r '' (ball (0 : ℂ) δ ∩ H)) :=
      ((convex_ball (0 : ℂ) δ).inter (convex_halfSpace_im_gt (r := 0))).isPreconnected.image _
        ((QuantumZipper.RS.differentiableOn_fwdMapInv hW hW0 hr.le).continuousOn.mono inter_subset_right)
    have hUsub : fwdMapInv W r '' (ball (0 : ℂ) δ ∩ H) ⊆ retainedDomain K η r := by
      rintro _ ⟨z, hz, rfl⟩
      have hzc := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 hr.le hz.2
      refine ⟨hzc.1, ?_⟩
      rintro (hK' | ⟨u, hu, hηu⟩)
      · exact hK z ⟨hz.2, hz.1⟩ hK'
      · rcases hu.1.eq_or_lt with hu0 | hu0
        · rw [← hu0, hη0] at hηu
          have : (0 : ℝ) < (fwdMapInv W r z).im := hzc.1
          rw [← hηu, Complex.zero_im] at this
          exact lt_irrefl _ this
        · exact hzc.2 (by rw [hhull]; exact ⟨u, ⟨hu0, hu.2⟩, hηu⟩)
    have hw : fwdMapInv W r ((m : ℂ) * I) ∈ connectedComponentIn (retainedDomain K η r) b' := by
      rw [← restartComponent, ← hdom]; exact hcol₀ hz₀
    intro z hz
    have h1 := hU.subset_connectedComponentIn (mem_image_of_mem _ hz₀') hUsub
    rw [← connectedComponentIn_eq hw, ← restartComponent, ← hdom] at h1
    exact h1 (mem_image_of_mem _ hz)
  obtain ⟨G, hG⟩ := Aux61Cmp.exists_isPosReflect_collar hW hW0 hη hr hc hsub hB hscale hδ hcol hone
  have h0B : ((0 : ℝ) : ℂ) ∈ ball (0 : ℂ) δ := by simpa using hδ
  have hG0 : G ((0 : ℝ) : ℂ) = 0 := by
    have := GlueImg.nhdsWithin_H_neBot 0
    have h1 := hG.tendsto h0B
    rw [Complex.ofReal_zero] at h1 ⊢
    exact tendsto_nhds_unique h1 hcur
  have hmono := Aux61Cpt.IsPosReflect.strictMonoOn_re hG
  have hIoo : ∀ x : ℝ, |x| < δ → x ∈ Ioo ((0 : ℝ) - δ) (0 + δ) := fun x hx => by
    rw [abs_lt] at hx; exact ⟨by linarith, by linarith⟩
  intro b hb
  -- a sequence of chart points tending to `b`
  set e : ℝ := ε - |b| with he
  have he0 : 0 < e := by rw [he]; linarith
  let ζ : ℕ → ℂ := fun n => (b : ℂ) + ((e / ((n : ℝ) + 2) : ℝ) : ℂ) * I
  have hζH : ∀ n, ζ n ∈ H ∩ ball (0 : ℂ) ε := by
    intro n
    have hpos : 0 < e / ((n : ℝ) + 2) := div_pos he0 (by positivity)
    have hle : e / ((n : ℝ) + 2) < e := div_lt_self he0 (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    refine ⟨?_, ?_⟩
    · change (0 : ℝ) < (ζ n).im
      simp only [ζ, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, Complex.I_re,
        Complex.ofReal_re, mul_one, mul_zero, zero_add, add_zero]
      exact hpos
    · rw [mem_ball, dist_zero_right]
      calc ‖ζ n‖ ≤ ‖(b : ℂ)‖ + ‖((e / ((n : ℝ) + 2) : ℝ) : ℂ) * I‖ := norm_add_le _ _
        _ = |b| + e / ((n : ℝ) + 2) := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, abs_of_pos hpos]
        _ < ε := by linarith
  have hζlim : Tendsto ζ atTop (𝓝 (b : ℂ)) := by
    have h1 : Tendsto (fun n : ℕ => e / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have h2 : Tendsto ζ atTop (𝓝 ((b : ℂ) + ((0 : ℝ) : ℂ) * I)) :=
      tendsto_const_nhds.add (((Complex.continuous_ofReal.tendsto 0).comp h1).mul_const I)
    rwa [Complex.ofReal_zero, zero_mul, add_zero] at h2
  have hmemB : ∀ z : ℂ, ‖z‖ < δ → z ∈ ball ((0 : ℝ) : ℂ) δ := fun z hz => by
    rw [Complex.ofReal_zero, mem_ball, dist_zero_right]; exact hz
  -- the own coordinates of the sequence lie in a compact half-disc
  let x : ℕ → ℂ := fun n => fwdMap W r (c.2.1 (ζ n))
  have hxD : ∀ n, c.2.1 (ζ n) ∈ H \ fwdHull W r := fun n => hsub (hc.inv_mem_dom (hζH n).1)
  have hxH : ∀ n, x n ∈ H := fun n => QuantumZipper.FwdHolo.mapsTo_fwdMap hW hr.le (hxD n)
  have hxK : ∀ n, x n ∈ closedBall (0 : ℂ) δ' := fun n => by
    rw [mem_closedBall, dist_zero_right]; exact hseed _ (hζH n)
  have hGx : ∀ n, G (x n) = ζ n := by
    intro n
    rw [hG.eqOn ⟨hxH n, hmemB _ (lt_of_le_of_lt (hseed _ (hζH n)) hδ')⟩]
    change c.1 (fwdMapInv W r (fwdMap W r (c.2.1 (ζ n)))) = ζ n
    rw [QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hr.le (hxD n)]
    exact hc.2.2 _ (hζH n).1
  obtain ⟨a', ha'K, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : ℂ) δ').tendsto_subseq hxK
  have ha'n : ‖a'‖ ≤ δ' := by rwa [mem_closedBall, dist_zero_right] at ha'K
  have ha'B := hmemB a' (lt_of_le_of_lt ha'n hδ')
  have hGc : ContinuousAt G a' := (hG.diff.differentiableAt (isOpen_ball.mem_nhds ha'B)).continuousAt
  have hGa : G a' = b := by
    have h1 := hGc.tendsto.comp hlim
    have h2 : Tendsto (G ∘ x ∘ φ) atTop (𝓝 (b : ℂ)) :=
      (hζlim.comp hφ.tendsto_atTop).congr fun n => by
        simp only [Function.comp_apply]; rw [hGx]
    exact tendsto_nhds_unique h1 h2
  have him0 : 0 ≤ a'.im :=
    ge_of_tendsto' ((Complex.continuous_im.tendsto _).comp hlim) fun n => le_of_lt (hxH (φ n))
  have him : a'.im = 0 := by
    by_contra hne
    have hpos : 0 < a'.im := lt_of_le_of_ne him0 (Ne.symm hne)
    have h := hG.conf.2.2.2.1 ⟨hpos, ha'B⟩
    rw [hGa] at h
    have h' : (0 : ℝ) < ((b : ℝ) : ℂ).im := h
    rw [Complex.ofReal_im] at h'
    exact lt_irrefl _ h'
  set t : ℝ := a'.re with htdef
  have hat : a' = (t : ℂ) := Complex.ext (by simp [htdef]) (by simp [him])
  have htle : |t| ≤ δ' := by
    have h := ha'n
    rwa [hat, Complex.norm_real, Real.norm_eq_abs] at h
  have htδ : |t| < δ := lt_of_le_of_lt htle hδ'
  have hft : (G (t : ℂ)).re = b := by rw [← hat, hGa, Complex.ofReal_re]
  have hf0 : (G ((0 : ℝ) : ℂ)).re = 0 := by rw [hG0, Complex.zero_re]
  have ht0 := hIoo t htδ
  have h00 := hIoo 0 (by simpa using hδ)
  refine ⟨t, htle, fun hb0 => ?_, fun hb0 => ?_, fun hb0 => ?_, δ, hδ, htδ, hcol, hone, ?_⟩
  · by_contra hle
    have := (hmono.le_iff_le ht0 h00).2 (not_lt.1 hle)
    rw [hft, hf0] at this
    linarith
  · by_contra hle
    have := (hmono.le_iff_le h00 ht0).2 (not_lt.1 hle)
    rw [hft, hf0] at this
    linarith
  · exact hmono.injOn ht0 h00 (show (G (t : ℂ)).re = (G ((0 : ℝ) : ℂ)).re by rw [hft, hf0, hb0])
  · have h := hG.tendsto (hmemB _ (by rw [Complex.norm_real, Real.norm_eq_abs]; exact htδ))
    rw [← hat, hGa] at h
    rw [hat] at h
    exact h

end Seed

end InteractingSLE.Sec5.Aux61Cpt
