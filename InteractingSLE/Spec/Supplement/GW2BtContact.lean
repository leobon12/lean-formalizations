/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BtCanon

/-!
# The contact clause at a root `x` (deterministic)

Packet PROVE-GW2-BUF (round 17; the root-`x` contact clause, step 2). This is the root-`x` successor of round 11's
`gapVanishes_contact_gb6`. The explored curve is `x + γ` and the counterflow `(W, α)` starts at `0`. Its relative
chart has the base point `c₀ = relBdry x` (real). A canonical driver `Wc` has the re-centred relative hulls before
the root-`x` contact `T_c`, the clock is bounded before `T_c` with supremum `L` (`contactLifeX`), and `ηc` lives to
`L`. Then:

* either `V̂^{0,L} < 0`, `junctionR − c₀ ≤ Re ηc(L)`, and every mark `y ≤ Re ηc(L)` has `GapVanishes Wc y L`;
* or the mirror statement holds on the left (`junctionL − c₀`).

Proof: round 11's argument. Interior relative times increase to `L`; at the corresponding times the points
`x + γ t` have relative images `ηc + c₀` (`canonicalX_eq_relBdry`). They accumulate at the counterflow prefix (the
contact), so `contact_side_H` puts the limit on a side. The earlier real values of `ηc + c₀` are inside the junctions
(`lt_junctionR_of_relBdry_eq`), so the alive-tip argument (`gapVanishes_of_canonical_off`) applies to `ηc`, with the
junctions moved by `c₀`.

* `contactLifeX`, **`gapVanishes_contactX`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Theorem14.GW2Bh

open Exist Staged StagedLaw MartChar.RealFlow Supp8 Supp8.GB6 Supp8.GB6.CoordB Supp8.Q3Rel Restart GW2TipSystem

/-- **The relative life at the root-`x` contact**: the supremum of the root-`x` clock before the contact. -/
def contactLifeX (x : ℝ) (s : ℝ≥0) (cf : RecData) (w : ℝ≥0 → ℝ) (γ α : ℝ≥0 → ℂ) : ℝ :=
  sSup ((fun t => RootH29.forwardCapacity x s t (cf, recOf (t : ℝ≥0∞) (w, ⊤))) ''
    {t : ℝ≥0 | (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
      ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)})

section Sample

variable {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
  {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) ⊤ α)
  (hW : Continuous (W · ω)) (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤)
  {s : ℝ≥0} (hs : 0 < s) {x : ℝ} (hx : 0 ≤ x) (harc : ∀ u ∈ Icc 0 s, x * ‖α u‖ < 1)
  {w : ℝ≥0 → ℝ} (hwc : Continuous w) (hw0 : w 0 = 0) {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace w ⊤ γ)

include hα hW hW0 hζ hs hx harc hwc hw0 hγ

/-- **The contact clause at a root `x`.** -/
theorem gapVanishes_contactX (htr : Tendsto (fun t => ‖γ t‖) atTop atTop) {Wc : ℝ≥0 → ℝ}
    (hWc : Continuous Wc) (hWc0 : Wc 0 = 0) {ζc : ℝ≥0∞} {ηc : ℝ≥0 → ℂ} (hη : IsGeneratingTrace Wc ζc ηc)
    (hK : ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
        ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) →
      fwdHull (fun r : ℝ => Wc r.toNNReal)
          (RootH29.forwardCapacity x s t (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤))) =
        (fun z : ℂ => z + ((-GW2Bf.relBase x s (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤)) : ℝ) : ℂ)) ''
          RootH29.forwardHull x s t (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤)))
    (hbdd : ∃ M : ℝ, ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime
        (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ)) ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) →
      RootH29.forwardCapacity x s t (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤)) ≤ M)
    (hLζ : ENNReal.ofReal (contactLifeX x s (cfRec s W ζ ω) w γ α) ≤ ζc) :
    (baseL (rp (W · ω)) s < 0 ∧
        junctionR (rp (W · ω)) s - (relBdry (rp (W · ω)) s x).re ≤
          (ηc (contactLifeX x s (cfRec s W ζ ω) w γ α).toNNReal).re ∧
        ∀ y : ℝ, y ≤ (ηc (contactLifeX x s (cfRec s W ζ ω) w γ α).toNNReal).re →
          GapVanishes (rp Wc) y (contactLifeX x s (cfRec s W ζ ω) w γ α)) ∨
      (0 < baseR (rp (W · ω)) s ∧
        (ηc (contactLifeX x s (cfRec s W ζ ω) w γ α).toNNReal).re ≤
          junctionL (rp (W · ω)) s - (relBdry (rp (W · ω)) s x).re ∧
        ∀ y : ℝ, (ηc (contactLifeX x s (cfRec s W ζ ω) w γ α).toNNReal).re ≤ y →
          GapVanishes (fun r => -rp Wc r) (-y) (contactLifeX x s (cfRec s W ζ ω) w γ α)) := by
  have hU := continuous_rp hW
  have hU0 : rp (W · ω) 0 = 0 := by simp [rp, hW0]
  have hWc' := continuous_rp hWc
  have hWc0' : rp Wc 0 = 0 := by simp [rp, hWc0]
  obtain ⟨ha0, hsm, hac⟩ := GW2Rz.clock_props W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ
  have hTc : 0 < firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
      ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) := GW2Rz.contact_pos (W := W) (ω := ω) hα hx harc hγ
  set Tc := firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
    ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) with hTcdef
  set a := fun t : ℝ≥0 => RootH29.forwardCapacity x s t (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤)) with hadef
  set L := contactLifeX x s (cfRec s W ζ ω) w γ α with hLdef
  replace ha0 : a 0 = 0 := ha0
  have h0Tc : ((0 : ℝ≥0) : ℝ≥0∞) < Tc := by rw [ENNReal.coe_zero]; exact hTc
  obtain ⟨M, hM⟩ := hbdd
  set A : Set ℝ := a '' {t : ℝ≥0 | (t : ℝ≥0∞) < Tc} with hAdef
  have hLA : L = sSup A := rfl
  have hAne : A.Nonempty := ⟨a 0, 0, h0Tc, rfl⟩
  have hAbdd : BddAbove A := ⟨M, by rintro _ ⟨t, ht, rfl⟩; exact hM t ht⟩
  have hle : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → a t ≤ L := fun t ht => le_csSup hAbdd ⟨t, ht, rfl⟩
  have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → a t < L := by
    intro t ht
    obtain ⟨t', htt', ht'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
    exact (hsm ht ht' (ENNReal.coe_lt_coe.1 htt')).trans_le (hle t' ht')
  have hL0 : 0 < L := by have := hlt 0 h0Tc; rw [ha0] at this; exact this
  have hexists : ∀ u ∈ Ico 0 L, ∃ t : ℝ≥0, (t : ℝ≥0∞) < Tc ∧ a t = u := by
    intro u hu
    obtain ⟨_, ⟨t', ht', rfl⟩, hut'⟩ := exists_lt_of_lt_csSup hAne (show u < sSup A from hu.2)
    have hcont : ContinuousOn a (Icc 0 t') :=
      hac.mono fun t ht => lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht.2) ht'
    obtain ⟨t, ht, hteq⟩ := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ t') hcont
      ⟨by rw [ha0]; exact hu.1, hut'.le⟩
    exact ⟨t, lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht.2) ht', hteq⟩
  obtain ⟨hηL, hcL⟩ := isLoewnerTraceLT_canonical hη hL0 hLζ
  have hlife : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → (((a t).toNNReal : ℝ≥0) : ℝ≥0∞) < ζc := fun t ht =>
    ((ENNReal.ofReal_lt_ofReal_iff hL0).2 (hlt t ht)).trans_le hLζ
  set c₀ := relBdry (rp (W · ω)) s x with hc₀def
  have hB : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc →
      (x : ℂ) + γ t ∈ relSafe (rp (W · ω)) s ∧ ηc (a t).toNNReal = relBdry (rp (W · ω)) s ((x : ℂ) + γ t) - c₀ := by
    intro t ht
    obtain ⟨h1, h2⟩ := canonicalX_eq_relBdry W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hWc hWc0 hη hK hlife ht
    rw [relSafe_record_eq s hW0 hW hζ] at h1
    rw [relBdry_record_eq s hW0 hW hζ] at h2
    exact ⟨h1, h2⟩
  have hsafe0 : (x : ℂ) ∈ relSafe (rp (W · ω)) s := by
    have h := (hB 0 h0Tc).1
    rwa [hγ.1, add_zero] at h
  have hc₀im : c₀.im = 0 := im_relBdry_of_real hU hU0 s.coe_nonneg hsafe0.2
  have hc₀re : c₀ = ((c₀.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hc₀im])
  -- interior relative times increasing to `L`
  have hseq : ∀ n : ℕ, ∃ t : ℝ≥0, (t : ℝ≥0∞) < Tc ∧ L - 1 / ((n : ℝ) + 1) < a t ∧ ηc (a t).toNNReal ∈ H := by
    intro n
    set lo : ℝ := max (L - 1 / ((n : ℝ) + 1)) (L / 2) with hlodef
    have hlo0 : 0 < lo := lt_max_of_lt_right (half_pos hL0)
    have hloL : lo < L := max_lt (by have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                                     linarith) (by linarith)
    obtain ⟨_, ⟨t', ht', rfl⟩, hlo⟩ := exists_lt_of_lt_csSup hAne (show lo < sSup A from hloL)
    have hat'0 : 0 ≤ a t' := hlo0.le.trans hlo.le
    have hxy : lo.toNNReal < (a t').toNNReal := (Real.toNNReal_lt_toNNReal_iff (hlo0.trans hlo)).2 hlo
    have hy : (((a t').toNNReal : ℝ≥0) : ℝ≥0∞) < ζc := hlife t' ht'
    obtain ⟨z, hz, hzH⟩ := Supp9D.exists_mem_H_of_isGeneratingTrace hη hWc.continuousOn hWc0 hxy hy
    have hz1 : lo < (z : ℝ) := by
      have := hz.1
      rwa [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hlo0.le] at this
    have hz2 : (z : ℝ) < a t' := by
      have := hz.2
      rwa [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hat'0] at this
    have hcont : ContinuousOn a (Icc 0 t') :=
      hac.mono fun t ht => lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht.2) ht'
    obtain ⟨t, ht, hteq⟩ := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ t') hcont
      ⟨by rw [ha0]; exact z.coe_nonneg, hz2.le⟩
    refine ⟨t, lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht.2) ht', ?_, ?_⟩
    · rw [hteq]; linarith [le_max_left (L - 1 / ((n : ℝ) + 1)) (L / 2)]
    · rw [hteq, Real.toNNReal_coe]; exact hzH
  choose tn htnT htnL htnH using hseq
  have hv : Tendsto (fun n => a (tn n)) atTop (𝓝 L) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n : ℕ => L - 1 / ((n : ℝ) + 1)) (h := fun _ => L)
      ?_ tendsto_const_nhds (fun n => (htnL n).le) (fun n => hle _ (htnT n))
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub L
    simpa using this
  -- the physical points
  set P : ℕ → ℂ := fun n => (x : ℂ) + γ (tn n) with hPdef
  have hPsafe : ∀ n, P n ∈ relSafe (rp (W · ω)) s := fun n => (hB _ (htnT n)).1
  have hPH : ∀ n, P n ∈ H := fun n => by
    have h1 := (hB _ (htnT n)).2
    have h2 := htnH n
    rw [h1] at h2
    have h3 : relBdry (rp (W · ω)) s (P n) ∈ H := by
      change 0 < (relBdry (rp (W · ω)) s (P n)).im
      change 0 < (relBdry (rp (W · ω)) s (P n) - c₀).im at h2
      rw [Complex.sub_im, hc₀im, sub_zero] at h2
      exact h2
    exact (relBdry_mem_H_iff hU hU0 s.coe_nonneg (hPsafe n)).1 h3
  have hPA : ∀ n, -(P n)⁻¹ ∉ fwdHull (rp (W · ω)) s := fun n hK' =>
    (hPsafe n).2 (subset_closure ⟨-(P n)⁻¹, hK', GB6.neg_inv_neg_inv _⟩)
  have hrel : ∀ n, relMap (rp (W · ω)) s (P n) = ηc (a (tn n)).toNNReal + c₀ := fun n => by
    rw [(hB _ (htnT n)).2, relBdry_eq hU s.coe_nonneg (hPH n) (hPsafe n).2]
    ring
  have hL' : Tendsto (fun n => relMap (rp (W · ω)) s (P n)) atTop (𝓝 (ηc L.toNNReal + c₀)) := by
    have hcw : ContinuousWithinAt (fun u : ℝ => ηc u.toNNReal) (Icc 0 L) L := hcL L ⟨hL0.le, le_rfl⟩
    have hvI : Tendsto (fun n => a (tn n)) atTop (𝓝[Icc 0 L] L) := by
      refine tendsto_nhdsWithin_iff.2 ⟨hv, Eventually.of_forall fun n => ⟨?_, hle _ (htnT n)⟩⟩
      have := htnL n
      have h1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      by_contra hneg
      rw [not_le] at hneg
      rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ tn n) with h | h
      · rw [← h, ha0] at hneg; exact lt_irrefl _ hneg
      · have := hsm h0Tc (htnT n) h; rw [ha0] at this; linarith
    have := ((hcw.tendsto.comp hvI).add_const c₀)
    exact this.congr fun n => (hrel n).symm
  -- `t_n → T_c`
  have hsnTc : ∀ T' : ℝ≥0, (T' : ℝ≥0∞) < Tc → ∀ᶠ n in atTop, T' < tn n := by
    intro T' hT'
    filter_upwards [hv.eventually (lt_mem_nhds (hlt T' hT'))] with n hn
    by_contra hle'
    rw [not_lt] at hle'
    have := hsm.monotoneOn (htnT n) hT' hle'
    linarith
  have hγc : Continuous γ := by
    have := hγ.2.1
    simp only [le_top, ofPred_true] at this
    exact continuousOn_univ.1 this
  have hαc : ContinuousOn α (Icc 0 s) := hα.2.1.mono fun t _ => show ((t : ℝ≥0) : ℝ≥0∞) ≤ ⊤ from le_top
  obtain ⟨zs, hzs, hzsA⟩ : ∃ zs, Tendsto (fun n => -(P n)⁻¹) atTop (𝓝 zs) ∧ zs ∈ α '' Icc 0 s := by
    rcases eq_top_or_lt_top Tc with hTop | hfin
    · have hsninf : Tendsto tn atTop atTop := by
        rw [Filter.tendsto_atTop]
        intro T'
        exact (hsnTc T' (by rw [hTop]; exact ENNReal.coe_lt_top)).mono fun n h => h.le
      have hn := htr.comp hsninf
      have hPn : Tendsto (fun n => ‖P n‖) atTop atTop := by
        refine tendsto_atTop_mono (fun n => ?_) (tendsto_atTop_add_const_right _ (-‖(x : ℂ)‖) hn)
        have h1 : ‖γ (tn n)‖ - ‖(x : ℂ)‖ ≤ ‖γ (tn n) + (x : ℂ)‖ := by
          simpa using norm_sub_norm_le (γ (tn n)) (-(x : ℂ))
        have h2 : ‖P n‖ = ‖γ (tn n) + (x : ℂ)‖ := by simp only [hPdef, add_comm]
        show ‖γ (tn n)‖ + -‖(x : ℂ)‖ ≤ ‖P n‖
        linarith
      refine ⟨0, ?_, ⟨0, ⟨le_rfl, zero_le⟩, hα.1⟩⟩
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have e : (fun n => ‖-(P n)⁻¹‖) = fun n => (‖P n‖)⁻¹ := by
        funext n; simp only [norm_neg, norm_inv]
      rw [e]
      exact tendsto_inv_atTop_zero.comp hPn
    · obtain ⟨T, hT⟩ : ∃ T : ℝ≥0, Tc = T := ⟨Tc.toNNReal, (ENNReal.coe_toNNReal hfin.ne).symm⟩
      have hsnT' : Tendsto tn atTop (𝓝 T) := by
        refine tendsto_order.2 ⟨fun b hb => hsnTc b (by rw [hT]; exact_mod_cast hb), fun b hb =>
          Eventually.of_forall fun n => lt_trans ?_ hb⟩
        have := htnT n; rw [hT] at this; exact_mod_cast this
      have hAcl : IsClosed ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s) := by
        rw [← image_image (fun z : ℂ => (z : OnePoint ℂ)) α]
        exact ((isCompact_Icc.image_of_continuousOn hαc).image OnePoint.continuous_coe).isClosed
      have hηs : Continuous fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ) :=
        continuous_sphereInv.comp (OnePoint.continuous_coe.comp (continuous_const.add hγc))
      obtain ⟨t₀, ht₀, hαt₀⟩ := firstContactTime_mem hηs hAcl (T := T) hT
      have hγT : (x : ℂ) + γ T ≠ 0 := by
        intro h0
        have h00 : sphereInv ((0 : ℂ) : OnePoint ℂ) = OnePoint.infty := by simp [sphereInv_coe]
        simp only at hαt₀
        rw [h0, h00] at hαt₀
        exact OnePoint.coe_ne_infty _ hαt₀
      simp only at hαt₀
      rw [sphereInv_coe_of_ne hγT] at hαt₀
      have heq : α t₀ = -((x : ℂ) + γ T)⁻¹ := OnePoint.coe_injective hαt₀
      refine ⟨α t₀, ?_, ⟨t₀, ht₀, rfl⟩⟩
      rw [heq]
      exact ((continuousAt_inv₀ hγT).neg.tendsto).comp
        (((continuous_const.add hγc).tendsto T).comp hsnT')
  obtain ⟨hLim, hside⟩ := contact_side_H hW hW0 hα hPH hPA hzs hzsA hL'
  have him : (ηc L.toNNReal).im = 0 := by
    rw [Complex.add_im, hc₀im, add_zero] at hLim
    exact hLim
  have hLre : (ηc L.toNNReal + c₀).re = (ηc L.toNNReal).re + c₀.re := Complex.add_re _ _
  -- the earlier real chart values
  have hreal : ∀ u ∈ Ico 0 L, ∀ r : ℝ, (fun u : ℝ => ηc u.toNNReal) u = r →
      ∃ t : ℝ≥0, (t : ℝ≥0∞) < Tc ∧ relBdry (rp (W · ω)) s ((x : ℂ) + γ t) = ((r + c₀.re : ℝ) : ℂ) := by
    intro u hu r h
    obtain ⟨t, ht, hteq⟩ := hexists u hu
    refine ⟨t, ht, ?_⟩
    have h1 := (hB t ht).2
    rw [hteq] at h1
    have h2 : relBdry (rp (W · ω)) s ((x : ℂ) + γ t) = (fun u : ℝ => ηc u.toNNReal) u + c₀ := by
      simp only at h1 ⊢
      rw [h1]; ring
    rw [h2, h, hc₀re]
    simp [Complex.ofReal_re]
  rcases hside with ⟨hbL, hjR⟩ | ⟨hbR, hjL⟩
  · left
    have hc₀lt : c₀.re < junctionR (rp (W · ω)) s :=
      lt_junctionR_of_relBdry_eq hU hU0 s.coe_nonneg hsafe0 hc₀re hbL
    refine ⟨hbL, by rw [hLre] at hjR; linarith, fun y hy => ?_⟩
    refine gapVanishes_of_canonical_off hWc' hWc0' hL0 (fun _ _ => rfl) hηL hcL him (x₀ :=
      junctionR (rp (W · ω)) s - c₀.re) (by linarith) (by rw [hLre] at hjR; linarith) ?_ hy
    intro u hu r hr h
    obtain ⟨t, ht, hrel'⟩ := hreal u hu r h
    have := lt_junctionR_of_relBdry_eq hU hU0 s.coe_nonneg (hB t ht).1 hrel' hbL
    linarith
  · right
    have hc₀lt : junctionL (rp (W · ω)) s < c₀.re :=
      junctionL_lt_of_relBdry_eq hU hU0 s.coe_nonneg hsafe0 hc₀re hbR
    refine ⟨hbR, by rw [hLre] at hjL; linarith, fun y hy => ?_⟩
    refine gapVanishes_neg_of_canonical_off hWc' hWc0' hL0 (fun _ _ => rfl) hηL hcL him (x₀ :=
      junctionL (rp (W · ω)) s - c₀.re) (by linarith) (by rw [hLre] at hjL; linarith) ?_ hy
    intro u hu r hr h
    obtain ⟨t, ht, hrel'⟩ := hreal u hu r h
    have := junctionL_lt_of_relBdry_eq hU hU0 s.coe_nonneg (hB t ht).1 hrel' hbR
    linarith

end Sample

end InteractingSLE.Theorem14.GW2Bh
