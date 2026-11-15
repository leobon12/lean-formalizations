/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import QuantumZipper.Proofs.GFF.K3.C5Cov
import LQGMetric.Statement.Field
import InteractingSLE.Frozen.Spec.upperHalfPlaneOpens

/-!
# Aux. lemma 50 for `κ ≥ 8`: the Green kernel of the active domain, for every pair of tests

Packet PROVE-AUX50C. Specification Aux. lemma 50, (HGV2)–(HGV5) (`source/spec/p193-240.md` L819–L870,
pp. 236–238): the covariance exhaustion compares the conditional covariance `G_{D_t}(φ, ψ)` of the whole field given
the hull germ at `t` with the Loewner Green kernel `G_ℍ(f_t a, f_t b)`, **for tests `φ, ψ` that may meet the hull**
(on a positive-area trace no test avoids it).

QuantumZipper's C2 (`K3.dualNormSq_eq_kerInt`) identifies the dual Dirichlet norm on `D_s = ℍ ∖ K_s` of any bounded
density with bounded support, with the conformal kernel integral `∬ 1_{D_s} u(a) 1_{D_s} u(b) G_ℍ(f_s a, f_s b)`.
By polarization (the proof of `K3.dualCov_compl_image_eq`, with C2 in place of C5′) and the splitting `ρ = ρ⁺ − ρ⁻`
(the proof of `K3.zeroGFFTestCov_compl_image_eq`):

* **`zeroGFFTestCov_actDom_eq`**: `zeroGFFTestCov (ℍ ∖ K_s) φ ψ = ∬ φ(a) ψ(b) G_s(a, b)` for all tests `φ, ψ` on `ℍ`,
  with `G_s(a, b) = aGreen W s a b = 1_{D_s}(a) 1_{D_s}(b) G_ℍ(f_s a, f_s b)`;
* the kernel facts used by the variance exhaustion: `aGreen` is nonnegative, antitone in time
  (`aGreen_antitone`), bounded by the time-`0` kernel `G_ℍ(a, b)` (`aGreen_le_zero`), and equals QuantumZipper's
  retained kernel `V_T` when both points are alive at `T` (`aGreen_eq_VT`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Function
open scoped ENNReal NNReal Classical

namespace InteractingSLE

namespace Aux50Ge8

open QuantumZipper QuantumZipper.K3

variable {W : ℝ → ℝ} {s : ℝ}

/-- The active domain `D_s = ℍ ∖ K_s`. -/
abbrev actDom (W : ℝ → ℝ) (s : ℝ) : Set ℂ := H \ fwdHull W s

/-- **The Green kernel of the active domain, extended by zero**: `G_s(a, b) = G_ℍ(f_s a, f_s b)` when `a` and `b`
are alive at `s`, and `0` otherwise. -/
def aGreen (W : ℝ → ℝ) (s : ℝ) (a b : ℂ) : ℝ :=
  if a ∈ actDom W s ∧ b ∈ actDom W s then (vtKer W s a b).toReal else 0

theorem aGreen_nonneg (W : ℝ → ℝ) (s : ℝ) (a b : ℂ) : 0 ≤ aGreen W s a b := by
  unfold aGreen; split_ifs
  · exact ENNReal.toReal_nonneg
  · exact le_rfl

theorem aGreen_comm (W : ℝ → ℝ) (s : ℝ) (a b : ℂ) : aGreen W s a b = aGreen W s b a := by
  unfold aGreen
  rw [vtKer_comm]
  by_cases h : a ∈ actDom W s ∧ b ∈ actDom W s
  · simp only [h, and_self, ↓reduceIte]
  · have h' : ¬ (b ∈ actDom W s ∧ a ∈ actDom W s) := fun h' => h h'.symm
    simp only [h, h', ↓reduceIte]

theorem aGreen_of_not_mem_left {a b : ℂ} (ha : a ∉ actDom W s) : aGreen W s a b = 0 := by
  unfold aGreen; exact ite_eq_right_iff.2 fun h => absurd h.1 ha

theorem aGreen_of_not_mem_right {a b : ℂ} (hb : b ∉ actDom W s) : aGreen W s a b = 0 := by
  unfold aGreen; exact ite_eq_right_iff.2 fun h => absurd h.2 hb

theorem mem_actDom_iff {a : ℂ} : a ∈ actDom W s ↔ a ∈ H ∧ ENNReal.ofReal s < swallowTime W a := by
  unfold actDom fwdHull
  simp only [Set.mem_sdiff, mem_ofPred_eq, not_and, not_le]
  exact ⟨fun h => ⟨h.1, h.2 h.1⟩, fun h => ⟨h.1, fun _ => h.2⟩⟩

theorem isOpen_actDom (hW : Continuous W) (hW0 : W 0 = 0) (hs : 0 ≤ s) : IsOpen (actDom W s) :=
  (isConformalOnto_fwdMap hW hW0 hs).isOpen

theorem actDom_subset_H : actDom W s ⊆ H := sdiff_subset

/-- On the active domain the conformal kernel of C2 is the time-`s` kernel. -/
theorem confKer_eq_vtKer {a b : ℂ} (ha : a ∈ actDom W s) (hb : b ∈ actDom W s) :
    confKer (fwdMap W s) (actDom W s) (a, b) = vtKer W s a b := by
  unfold confKer vtKer
  rw [confMod_eqOn ha, confMod_eqOn hb]

/-! ### The kernel integral of C2 -/

section KerInt

variable {g g₁ g₂ g₁' : ℂ → ℝ≥0∞}

theorem kerDens_comm (p : ℂ × ℂ) :
    kerDens (fwdMap W s) (actDom W s) g₁ g₂ p.swap = kerDens (fwdMap W s) (actDom W s) g₂ g₁ p := by
  unfold kerDens confKer
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [greenH_symm]
  ring

theorem kerInt_comm : kerInt (fwdMap W s) (actDom W s) g₁ g₂ = kerInt (fwdMap W s) (actDom W s) g₂ g₁ := by
  unfold kerInt
  rw [← lintegral_prod_swap]
  exact lintegral_congr fun p => kerDens_comm p

theorem kerInt_add_left (hW : Continuous W) (hW0 : W 0 = 0) (hs : 0 ≤ s) (hm1 : Measurable g₁)
    (hm2 : Measurable g₂) :
    kerInt (fwdMap W s) (actDom W s) (g₁ + g₁') g₂ =
      kerInt (fwdMap W s) (actDom W s) g₁ g₂ + kerInt (fwdMap W s) (actDom W s) g₁' g₂ := by
  unfold kerInt
  rw [← lintegral_add_left (measurable_kerDens (isConformalOnto_fwdMap hW hW0 hs) hm1 hm2)]
  refine lintegral_congr fun p => ?_
  unfold kerDens
  simp only [indicator_add', Pi.add_apply]
  ring

theorem kerInt_add_right (hW : Continuous W) (hW0 : W 0 = 0) (hs : 0 ≤ s) (hm1 : Measurable g₁)
    (hm2 : Measurable g₂) {g₂' : ℂ → ℝ≥0∞} :
    kerInt (fwdMap W s) (actDom W s) g₁ (g₂ + g₂') =
      kerInt (fwdMap W s) (actDom W s) g₁ g₂ + kerInt (fwdMap W s) (actDom W s) g₁ g₂' := by
  rw [kerInt_comm, kerInt_add_left hW hW0 hs hm2 hm1, kerInt_comm, kerInt_comm (g₁ := g₂')]

theorem kerInt_lt_top (hW : Continuous W) (hW0 : W 0 = 0) (hs : 0 ≤ s) {M : ℝ≥0∞} {R : ℝ}
    (hu : BddDens g M R) : kerInt (fwdMap W s) (actDom W s) g g < ⊤ := by
  rw [← dualNormSq_eq_kerInt (isConformalOnto_fwdMap hW hW0 hs) sdiff_subset hu]
  exact dualNormSq_withDensity_lt_top (isConformalOnto_fwdMap hW hW0 hs) sdiff_subset hu

theorem kerInt_cross_lt_top (hW : Continuous W) (hW0 : W 0 = 0) (hs : 0 ≤ s) {M₁ M₂ : ℝ≥0∞}
    {R₁ R₂ : ℝ} (hu₁ : BddDens g₁ M₁ R₁) (hu₂ : BddDens g₂ M₂ R₂) :
    kerInt (fwdMap W s) (actDom W s) g₁ g₂ < ⊤ := by
  have h := kerInt_lt_top hW hW0 hs (hu₁.add hu₂)
  rw [kerInt_add_left hW hW0 hs hu₁.meas (hu₁.add hu₂).meas,
    kerInt_add_right hW hW0 hs hu₁.meas hu₁.meas] at h
  exact lt_of_le_of_lt (le_trans le_add_self le_self_add) h

/-- **C2, covariance form**, by polarization of `K3.dualNormSq_eq_kerInt`. -/
theorem dualCov_actDom_eq (hW : Continuous W) (hW0 : W 0 = 0) (hs : 0 ≤ s) {M₁ M₂ : ℝ≥0∞} {R₁ R₂ : ℝ}
    (hu₁ : BddDens g₁ M₁ R₁) (hu₂ : BddDens g₂ M₂ R₂) :
    dualCov (actDom W s) (zeroSpace (actDom W s)) (volume.withDensity g₁) (volume.withDensity g₂) =
      (kerInt (fwdMap W s) (actDom W s) g₁ g₂).toReal := by
  have hφ := isConformalOnto_fwdMap hW hW0 hs
  have hDH : actDom W s ⊆ H := sdiff_subset
  unfold dualCov
  rw [← withDensity_add_left hu₁.meas, dualNormSq_eq_kerInt hφ hDH hu₁, dualNormSq_eq_kerInt hφ hDH hu₂,
    dualNormSq_eq_kerInt hφ hDH (hu₁.add hu₂)]
  have hf12 := kerInt_lt_top hW hW0 hs (hu₁.add hu₂)
  have hexp : kerInt (fwdMap W s) (actDom W s) (g₁ + g₂) (g₁ + g₂) =
      kerInt (fwdMap W s) (actDom W s) g₁ g₁ + kerInt (fwdMap W s) (actDom W s) g₁ g₂ +
        (kerInt (fwdMap W s) (actDom W s) g₁ g₂ + kerInt (fwdMap W s) (actDom W s) g₂ g₂) := by
    rw [kerInt_add_left hW hW0 hs hu₁.meas (hu₁.add hu₂).meas, kerInt_add_right hW hW0 hs hu₁.meas hu₁.meas,
      kerInt_add_right hW hW0 hs hu₂.meas hu₁.meas, kerInt_comm (g₁ := g₂) (g₂ := g₁)]
  rw [hexp] at hf12 ⊢
  obtain ⟨hab, hbc⟩ := ENNReal.add_lt_top.1 hf12
  obtain ⟨ha, hb⟩ := ENNReal.add_lt_top.1 hab
  obtain ⟨-, hc⟩ := ENNReal.add_lt_top.1 hbc
  rw [ENNReal.toReal_add hab.ne hbc.ne, ENNReal.toReal_add ha.ne hb.ne, ENNReal.toReal_add hb.ne hc.ne]
  ring

/-- A finite kernel integral of bounded densities is the integral of the real kernel density. -/
theorem kerDens_integral_toReal (hW : Continuous W) (hW0 : W 0 = 0) (hs : 0 ≤ s) (hm1 : Measurable g₁)
    (hm2 : Measurable g₂) (hfin : kerInt (fwdMap W s) (actDom W s) g₁ g₂ ≠ ⊤) :
    Integrable (fun q : ℂ × ℂ => (kerDens (fwdMap W s) (actDom W s) g₁ g₂ q).toReal)
      ((volume : Measure ℂ).prod volume) ∧
    ∫ q, (kerDens (fwdMap W s) (actDom W s) g₁ g₂ q).toReal ∂((volume : Measure ℂ).prod volume) =
      (kerInt (fwdMap W s) (actDom W s) g₁ g₂).toReal := by
  have hmeas := measurable_kerDens (isConformalOnto_fwdMap hW hW0 hs) hm1 hm2
  refine ⟨integrable_toReal_of_lintegral_ne_top hmeas.aemeasurable hfin, ?_⟩
  rw [integral_toReal hmeas.aemeasurable (ae_lt_top hmeas hfin)]
  rfl

end KerInt

/-! ### The covariance of two tests -/

theorem bddDens_ofReal_test (φ : LQGMetric.TestOn upperHalfPlaneOpens) :
    ∃ M R, BddDens (fun z => ENNReal.ofReal (φ z)) M R :=
  bddDens_ofReal_of_hasCompactSupport φ.continuous φ.hasCompactSupport

theorem bddDens_ofReal_neg_test (φ : LQGMetric.TestOn upperHalfPlaneOpens) :
    ∃ M R, BddDens (fun z => ENNReal.ofReal (-φ z)) M R :=
  bddDens_ofReal_of_hasCompactSupport φ.continuous.neg φ.hasCompactSupport.neg

/-- The real kernel density of two real densities, through their positive and negative parts. -/
theorem kerDens_toReal_eq (a b : ℂ) (f g : ℂ → ℝ) :
    (kerDens (fwdMap W s) (actDom W s) (fun z => ENNReal.ofReal (f z)) (fun z => ENNReal.ofReal (g z))
        (a, b)).toReal =
      max (f a) 0 * (max (g b) 0 * aGreen W s a b) := by
  unfold kerDens
  by_cases ha : a ∈ actDom W s
  · by_cases hb : b ∈ actDom W s
    · simp only [indicator_of_mem ha, indicator_of_mem hb, ENNReal.toReal_mul, ENNReal.toReal_ofReal']
      rw [confKer_eq_vtKer ha hb, aGreen]
      simp only [ha, hb, and_self, ↓reduceIte]
    · simp [indicator_of_notMem hb, aGreen_of_not_mem_right hb]
  · simp [indicator_of_notMem ha, aGreen_of_not_mem_left ha]

/-- **The covariance on the active domain of any two tests on `ℍ` is the Green-kernel integral**:
`zeroGFFTestCov (ℍ ∖ K_s) φ ψ = ∬ φ(a) ψ(b) G_s(a, b)`. -/
theorem zeroGFFTestCov_actDom_eq (hW : Continuous W) (hW0 : W 0 = 0) (hs : 0 ≤ s)
    (φ ψ : LQGMetric.TestOn upperHalfPlaneOpens) :
    zeroGFFTestCov (actDom W s) φ ψ = ∫ a, ∫ b, φ a * ψ b * aGreen W s a b := by
  obtain ⟨M₁, R₁, hp⟩ := bddDens_ofReal_test φ
  obtain ⟨M₂, R₂, hm⟩ := bddDens_ofReal_neg_test φ
  obtain ⟨M₃, R₃, hq⟩ := bddDens_ofReal_test ψ
  obtain ⟨M₄, R₄, hn⟩ := bddDens_ofReal_neg_test ψ
  have I13 := kerDens_integral_toReal hW hW0 hs hp.meas hq.meas (kerInt_cross_lt_top hW hW0 hs hp hq).ne
  have I14 := kerDens_integral_toReal hW hW0 hs hp.meas hn.meas (kerInt_cross_lt_top hW hW0 hs hp hn).ne
  have I23 := kerDens_integral_toReal hW hW0 hs hm.meas hq.meas (kerInt_cross_lt_top hW hW0 hs hm hq).ne
  have I24 := kerDens_integral_toReal hW hW0 hs hm.meas hn.meas (kerInt_cross_lt_top hW hW0 hs hm hn).ne
  set D := actDom W s with hD
  set k : (ℂ → ℝ≥0∞) → (ℂ → ℝ≥0∞) → ℂ × ℂ → ℝ := fun u v q => (kerDens (fwdMap W s) D u v q).toReal
    with hk
  have hcov : zeroGFFTestCov D φ ψ =
      (kerInt (fwdMap W s) D (fun z => ENNReal.ofReal (φ z)) fun z => ENNReal.ofReal (ψ z)).toReal
      - (kerInt (fwdMap W s) D (fun z => ENNReal.ofReal (φ z)) fun z => ENNReal.ofReal (-ψ z)).toReal
      - (kerInt (fwdMap W s) D (fun z => ENNReal.ofReal (-φ z)) fun z => ENNReal.ofReal (ψ z)).toReal
      + (kerInt (fwdMap W s) D (fun z => ENNReal.ofReal (-φ z)) fun z => ENNReal.ofReal (-ψ z)).toReal := by
    unfold zeroGFFTestCov testMeasPos testMeasNeg
    rw [dualCov_actDom_eq hW hW0 hs hp hq, dualCov_actDom_eq hW hW0 hs hp hn,
      dualCov_actDom_eq hW hW0 hs hm hq, dualCov_actDom_eq hW hW0 hs hm hn]
  set F : ℂ × ℂ → ℝ := fun q => φ q.1 * ψ q.2 * aGreen W s q.1 q.2 with hF
  have hsplit : F = (((k (fun z => ENNReal.ofReal (φ z)) fun z => ENNReal.ofReal (ψ z))
      - (k (fun z => ENNReal.ofReal (φ z)) fun z => ENNReal.ofReal (-ψ z)))
      - (k (fun z => ENNReal.ofReal (-φ z)) fun z => ENNReal.ofReal (ψ z)))
      + (k (fun z => ENNReal.ofReal (-φ z)) fun z => ENNReal.ofReal (-ψ z)) := by
    funext q
    simp only [hk, Pi.add_apply, Pi.sub_apply, hF]
    rw [kerDens_toReal_eq q.1 q.2 (fun z => φ z) (fun z => ψ z),
      kerDens_toReal_eq q.1 q.2 (fun z => φ z) (fun z => -ψ z),
      kerDens_toReal_eq q.1 q.2 (fun z => -φ z) (fun z => ψ z),
      kerDens_toReal_eq q.1 q.2 (fun z => -φ z) (fun z => -ψ z)]
    conv_lhs => rw [← max_zero_sub_max_neg_zero_eq_self (φ q.1), ← max_zero_sub_max_neg_zero_eq_self (ψ q.2)]
    ring
  have hFint : Integrable F ((volume : Measure ℂ).prod volume) := by
    rw [hsplit]; exact ((I13.1.sub I14.1).sub I23.1).add I24.1
  calc zeroGFFTestCov D φ ψ = ∫ q, F q ∂((volume : Measure ℂ).prod volume) := by
        rw [hcov, hsplit, integral_add' ((I13.1.sub I14.1).sub I23.1) I24.1,
          integral_sub' (I13.1.sub I14.1) I23.1, integral_sub' I13.1 I14.1,
          I13.2, I14.2, I23.2, I24.2]
    _ = ∫ a, ∫ b, F (a, b) := integral_prod F hFint
    _ = ∫ a, ∫ b, φ a * ψ b * aGreen W s a b := rfl

/-- The double integral of the kernel against two tests is integrable on the product. -/
theorem integrable_test_aGreen (hW : Continuous W) (hW0 : W 0 = 0) (hs : 0 ≤ s)
    (φ ψ : LQGMetric.TestOn upperHalfPlaneOpens) :
    Integrable (fun q : ℂ × ℂ => φ q.1 * ψ q.2 * aGreen W s q.1 q.2) ((volume : Measure ℂ).prod volume) := by
  obtain ⟨M₁, R₁, hp⟩ := bddDens_ofReal_test φ
  obtain ⟨M₂, R₂, hm⟩ := bddDens_ofReal_neg_test φ
  obtain ⟨M₃, R₃, hq⟩ := bddDens_ofReal_test ψ
  obtain ⟨M₄, R₄, hn⟩ := bddDens_ofReal_neg_test ψ
  have I13 := kerDens_integral_toReal hW hW0 hs hp.meas hq.meas (kerInt_cross_lt_top hW hW0 hs hp hq).ne
  have I14 := kerDens_integral_toReal hW hW0 hs hp.meas hn.meas (kerInt_cross_lt_top hW hW0 hs hp hn).ne
  have I23 := kerDens_integral_toReal hW hW0 hs hm.meas hq.meas (kerInt_cross_lt_top hW hW0 hs hm hq).ne
  have I24 := kerDens_integral_toReal hW hW0 hs hm.meas hn.meas (kerInt_cross_lt_top hW hW0 hs hm hn).ne
  refine (((I13.1.sub I14.1).sub I23.1).add I24.1).congr (Eventually.of_forall fun q => ?_)
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [kerDens_toReal_eq q.1 q.2 (fun z => φ z) (fun z => ψ z),
    kerDens_toReal_eq q.1 q.2 (fun z => φ z) (fun z => -ψ z),
    kerDens_toReal_eq q.1 q.2 (fun z => -φ z) (fun z => ψ z),
    kerDens_toReal_eq q.1 q.2 (fun z => -φ z) (fun z => -ψ z)]
  conv_rhs => rw [← max_zero_sub_max_neg_zero_eq_self (φ q.1), ← max_zero_sub_max_neg_zero_eq_self (ψ q.2)]
  ring

/-! ### Monotonicity, domination, and the retained kernel -/

theorem actDom_anti {s t : ℝ} (hst : s ≤ t) : actDom W t ⊆ actDom W s :=
  fun _ hz => ⟨hz.1, fun h => hz.2 ⟨h.1, h.2.trans (ENNReal.ofReal_le_ofReal hst)⟩⟩

theorem mem_vtIdx_of_mem_actDom {s t T : ℝ} {a b : ℂ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T)
    (ha : a ∈ actDom W t) (hb : b ∈ actDom W t) : s ∈ vtIdx W T a b :=
  ⟨hs, hst.trans htT, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hst) (mem_actDom_iff.1 ha).2,
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hst) (mem_actDom_iff.1 hb).2⟩

/-- **The kernel decreases in time** (domain monotonicity, QuantumZipper's FD-3 `vtKer_antitoneOn`). -/
theorem aGreen_antitone (hW : Continuous W) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (a b : ℂ) :
    aGreen W t a b ≤ aGreen W s a b := by
  by_cases h : a ∈ actDom W t ∧ b ∈ actDom W t
  · obtain ⟨ha, hb⟩ := h
    have ha' := actDom_anti hst ha
    have hb' := actDom_anti hst hb
    unfold aGreen
    simp only [ha, hb, ha', hb', and_self, ↓reduceIte]
    have h1 : s ∈ vtIdx W t a b := mem_vtIdx_of_mem_actDom hs hst le_rfl ha hb
    have h2 : t ∈ vtIdx W t a b := mem_vtIdx_of_mem_actDom (hs.trans hst) le_rfl le_rfl ha hb
    refine ENNReal.toReal_mono ENNReal.ofReal_ne_top ?_
    exact vtKer_antitoneOn hW ha.1 hb.1 h1 h2 hst
  · rcases not_and_or.1 h with h | h
    · rw [aGreen_of_not_mem_left h]; exact aGreen_nonneg W s a b
    · rw [aGreen_of_not_mem_right h]; exact aGreen_nonneg W s a b

/-- **The retained kernel at alive points**: if `a` and `b` are alive at `T ≥ 0`, `G_T(a, b) = V_T(a, b)`. -/
theorem aGreen_eq_VT (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {a b : ℂ} (ha : a ∈ actDom W T)
    (hb : b ∈ actDom W T) : aGreen W T a b = VT W T a b := by
  unfold aGreen VT
  simp only [ha, hb, and_self, ↓reduceIte]
  rw [VTe_eq_vtKer_of_lt hW ha.1 hb.1 hT (mem_actDom_iff.1 ha).2 (mem_actDom_iff.1 hb).2]

/-- Every point of `ℍ` is alive at time `0`. -/
theorem mem_actDom_zero (hW : Continuous W) {a : ℂ} (ha : a ∈ H) : a ∈ actDom W 0 :=
  mem_actDom_iff.2 ⟨ha, by rw [ENNReal.ofReal_zero]; exact swallowTime_pos hW ha⟩

theorem VT_nonneg (W : ℝ → ℝ) (T : ℝ) (a b : ℂ) : 0 ≤ VT W T a b := ENNReal.toReal_nonneg

/-- **The retained kernel is bounded by the time-`0` kernel.** -/
theorem VT_le_aGreen_zero (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {a b : ℂ} (ha : a ∈ H) (hb : b ∈ H) :
    VT W T a b ≤ aGreen W 0 a b := by
  have ha0 := mem_actDom_zero hW ha
  have hb0 := mem_actDom_zero hW hb
  unfold aGreen VT
  simp only [ha0, hb0, and_self, ↓reduceIte]
  refine ENNReal.toReal_mono ENNReal.ofReal_ne_top (iInf₂_le _ ?_)
  exact mem_vtIdx_of_mem_actDom le_rfl le_rfl hT ha0 hb0

/-- The kernel at any time `s ≥ 0` is bounded by the time-`0` kernel. -/
theorem aGreen_le_zero (hW : Continuous W) {s : ℝ} (hs : 0 ≤ s) (a b : ℂ) : aGreen W s a b ≤ aGreen W 0 a b :=
  aGreen_antitone hW le_rfl hs a b

/-- **The dominating function**: `|φ(a)| |ψ(b)| G_0(a, b)` is integrable on `ℂ × ℂ`. -/
theorem integrable_abs_test_aGreen_zero (hW : Continuous W) (hW0 : W 0 = 0)
    (φ ψ : LQGMetric.TestOn upperHalfPlaneOpens) :
    Integrable (fun q : ℂ × ℂ => |φ q.1| * |ψ q.2| * aGreen W 0 q.1 q.2) ((volume : Measure ℂ).prod volume) := by
  obtain ⟨M₁, R₁, hp⟩ := bddDens_ofReal_of_hasCompactSupport φ.continuous.abs φ.hasCompactSupport.abs
  obtain ⟨M₂, R₂, hq⟩ := bddDens_ofReal_of_hasCompactSupport ψ.continuous.abs ψ.hasCompactSupport.abs
  have I := kerDens_integral_toReal hW hW0 le_rfl hp.meas hq.meas
    (kerInt_cross_lt_top hW hW0 le_rfl hp hq).ne
  refine I.1.congr (Eventually.of_forall fun q => ?_)
  simp only
  rw [kerDens_toReal_eq q.1 q.2 (fun z => |φ z|) (fun z => |ψ z|), max_eq_left (abs_nonneg _),
    max_eq_left (abs_nonneg _)]
  ring

end Aux50Ge8

end InteractingSLE
