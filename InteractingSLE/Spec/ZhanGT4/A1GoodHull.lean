/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Loewner.HullRightCont
import InteractingSLE.Spec.ZhanGT4.A2Part3PCFinGeom
import InteractingSLE.Spec.ZhanGT4.D9Clear
import InteractingSLE.Spec.ZhanGT4.D9Two
import InteractingSLE.Spec.ZhanGT4.A2TipSepCore
import InteractingSLE.Spec.Supplement.LP3Flow

/-!
# Zhan's A.1: right-continuity of the CLOSED Loewner hulls

Packet PROVE-A1-GOODTIME. The landed right-continuity of hulls (`HullRightCont.exists_pos_disjoint_fwdHull`) covers
compact sets inside `ℍ`. The good-time predicate `A1Ref.IsGoodTime` of A.1's image chains is phrased with the CLOSURES
of the hulls (`A2X.contactTime`), so real boundary points matter. This file proves:

* `exists_isForwardSol_real_small`: a nonzero real point is alive for a short time (tamed real flow);
* **`exists_isForwardSol_real_gt`**: a real forward solution extends beyond its horizon (restart + glue);
* **`exists_ball_disjoint_closure_fwdHull_beyond`**: a real point off the closed hull at a positive time `T` has a
  disc missing every closed hull up to a time `R > T`;
* **`exists_pos_disjoint_closure_fwdHull`**: **a compact set off the closed hull `closure K_T` (`T > 0`) is off
  `closure K_{T+δ}` for some `δ > 0`** (finitely many discs around its real points; the rest is a compact subset of
  `ℍ`, where the landed right-continuity applies and `closure K ∩ ℍ = K`);
* `exists_pos_disjoint_closure_fwdHull_of_isClosed`: the same for a closed set (the hulls up to `T + 1` are bounded).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Good

open QuantumZipper (H IsForwardSol fwdHull)

/-! ### Real forward solutions extend -/

/-- **A positive real point is alive for a short time** (any continuous driver started at `0`): the tamed real flow
stays above half its start for a short time. -/
theorem exists_isForwardSol_real_small_pos {B : ℝ → ℝ} (hB : Continuous B) (hB0 : B 0 = 0) {a : ℝ} (ha : 0 < a) :
    ∃ ε > 0, ∃ v, IsForwardSol B (a : ℂ) ε v := by
  have hc : 0 < a / 2 := half_pos ha
  set f := QuantumZipper.RS.realTamed B (a / 2) a with hf
  have hf0 : f 0 = a := by
    have h := QuantumZipper.RS.realTamed_eq hB hc a (le_refl (0 : ℝ))
    rw [hB0, intervalIntegral.integral_same] at h
    rw [hf, h]; ring
  have hcont : ContinuousWithinAt f (Icc 0 1) 0 :=
    QuantumZipper.RS.continuousOn_realTamed hB hc zero_le_one a 0 ⟨le_rfl, zero_le_one⟩
  have hev : ∀ᶠ t in 𝓝[Icc 0 1] (0 : ℝ), a / 2 < f t :=
    hcont.eventually (lt_mem_nhds (by rw [hf0]; linarith))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hev)
  set ε' := min (ε / 2) 1 with hε'
  have hε'pos : 0 < ε' := lt_min (half_pos hε) one_pos
  refine ⟨ε', hε'pos, _, QuantumZipper.RS.isForwardSol_realTamed hB hc hε'pos.le fun t ht => ?_⟩
  have hd : dist t 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    exact ht.2.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hε))
  exact (hball hd ⟨ht.1, ht.2.trans (min_le_right _ _)⟩).le

/-- **A nonzero real point is alive for a short time** (reflection for negative points). -/
theorem exists_isForwardSol_real_small {B : ℝ → ℝ} (hB : Continuous B) (hB0 : B 0 = 0) {a : ℝ} (ha : a ≠ 0) :
    ∃ ε > 0, ∃ v, IsForwardSol B (a : ℂ) ε v := by
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have hB' : Continuous fun t => -B t := hB.neg
    obtain ⟨ε, hε, v, hv⟩ := exists_isForwardSol_real_small_pos hB' (by simp [hB0]) (neg_pos.2 hneg)
    have h := QuantumZipper.RS.isForwardSol_neg hv
    simp only [neg_neg, Complex.ofReal_neg] at h
    exact ⟨ε, hε, _, h⟩
  · exact exists_isForwardSol_real_small_pos hB hB0 hpos

/-- **A real forward solution extends beyond its horizon**: restart at `T` from the (real, nonzero) value and glue. -/
theorem exists_isForwardSol_real_gt {W : ℝ → ℝ} (hW : Continuous W) {x T : ℝ} (hT : 0 ≤ T) {u : ℝ → ℂ}
    (hu : IsForwardSol W (x : ℂ) T u) : ∃ T' > T, ∃ v, IsForwardSol W (x : ℂ) T' v := by
  have hreal := LP.LP3.eq_ofReal_re_of_isForwardSol hW hu ⟨hT, le_rfl⟩
  have hne : (u T).re ≠ 0 := by
    intro h0
    apply (hu.2 T ⟨hT, le_rfl⟩).1
    rw [hreal, h0, Complex.ofReal_zero]
  obtain ⟨ε, hε, w, hw⟩ := exists_isForwardSol_real_small (B := fun r => W (T + r) - W T)
    (by fun_prop) (by simp) hne
  obtain ⟨v, hv, -⟩ := LP.LP3.exists_isForwardSol_glue hW hT hε.le hu hw
  exact ⟨T + ε, by linarith, v, hv⟩

/-! ### Discs at real points -/

/-- **A real point off the closed hull at a positive time keeps a disc off the closed hulls a little longer.** -/
theorem exists_ball_disjoint_closure_fwdHull_beyond {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 < T) {x : ℝ}
    (hx : (x : ℂ) ∉ closure (fwdHull W T)) :
    ∃ ε > 0, ∃ R > T, ∀ s : ℝ≥0, (s : ℝ) ≤ R → Disjoint (ball (x : ℂ) ε) (closure (fwdHull W s)) := by
  have hx0 : x ≠ W 0 := by
    rintro rfl
    exact hx (start_mem_closure_fwdHull hW hT)
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, ball (x : ℂ) r ⊆ (closure (fwdHull W T))ᶜ :=
    Metric.isOpen_iff.1 isClosed_closure.isOpen_compl _ hx
  have hd : Disjoint (ball (x : ℂ) r) (fwdHull W T) :=
    Set.disjoint_left.2 fun z hz hzK => hball hz (subset_closure hzK)
  obtain ⟨u, hu⟩ := exists_isForwardSol_of_disjoint_ball_gen hW hx0 hT.le hr hd
  obtain ⟨R, hRT, v, hv⟩ := exists_isForwardSol_real_gt hW hT.le hu
  obtain ⟨ε, hε, hdisj⟩ := A2X.P3.exists_ball_disjoint_closure_fwdHull_of_isForwardSol hW
    (hT.le.trans hRT.le) hv
  exact ⟨ε, hε, R, hRT, hdisj⟩

/-! ### Right-continuity of the closed hulls -/

/-- **Right-continuity of the closed hulls on compact sets.** For a continuous driver, `T > 0` and a compact `C` off
`closure K_T`, some `δ > 0` has `C` off `closure K_{T+δ}`. -/
theorem exists_pos_disjoint_closure_fwdHull {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 < T) {C : Set ℂ}
    (hC : IsCompact C) (hd : Disjoint C (closure (fwdHull W T))) :
    ∃ δ > 0, Disjoint C (closure (fwdHull W (T + δ))) := by
  set C₀ : Set ℂ := C ∩ {z | z.im = 0} with hC₀
  have hC₀c : IsCompact C₀ := hC.inter_right (isClosed_eq Complex.continuous_im continuous_const)
  have key : ∀ z ∈ C₀, ∃ ε > 0, ∃ R > T, ∀ s : ℝ≥0, (s : ℝ) ≤ R →
      Disjoint (ball z ε) (closure (fwdHull W s)) := by
    intro z hz
    have hzre : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by rw [Complex.ofReal_im]; exact hz.2.symm)
    have hzK : ((z.re : ℝ) : ℂ) ∉ closure (fwdHull W T) := by
      rw [hzre]; exact Set.disjoint_left.1 hd hz.1
    have h := exists_ball_disjoint_closure_fwdHull_beyond hW hT hzK
    rwa [hzre] at h
  choose! ε hε R hR hdisj using key
  obtain ⟨t, htC, hcov⟩ := hC₀c.elim_nhds_subcover (fun z => ball z (ε z))
    fun z hz => ball_mem_nhds z (hε z hz)
  set U : Set ℂ := ⋃ z ∈ t, ball z (ε z) with hU
  have hUo : IsOpen U := isOpen_biUnion fun z _ => isOpen_ball
  set C₂ : Set ℂ := (C \ U) ∩ {z | 0 ≤ z.im} with hC₂
  have hC₂c : IsCompact C₂ :=
    (hC.diff hUo).inter_right (isClosed_le continuous_const Complex.continuous_im)
  have hC₂H : C₂ ⊆ H := by
    rintro z ⟨⟨hzC, hzU⟩, hz0⟩
    rcases (show (0 : ℝ) ≤ z.im from hz0).lt_or_eq with hpos | heq
    · exact hpos
    · exact absurd (hcov ⟨hzC, heq.symm⟩) hzU
  have hC₂d : Disjoint C₂ (fwdHull W T) :=
    Set.disjoint_left.2 fun z hz hzK => Set.disjoint_left.1 hd hz.1.1 (subset_closure hzK)
  obtain ⟨δ₂, hδ₂, hdisj₂⟩ := HullRightCont.exists_pos_disjoint_fwdHull hW hC₂c hC₂H hC₂d
  have hev₁ : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ z ∈ t, T + δ ≤ R z :=
    (Filter.eventually_all_finset t).2 fun z hz => by
      have hpos : 0 < R z - T := sub_pos.2 (hR z (htC z hz))
      filter_upwards [Ioo_mem_nhdsGT hpos] with δ hδ
      linarith [hδ.2]
  have hev₂ : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ≤ δ₂ := by
    filter_upwards [Ioo_mem_nhdsGT hδ₂] with δ hδ using hδ.2.le
  obtain ⟨δ, ⟨h₁, h₂⟩, hδpos⟩ := ((hev₁.and hev₂).and self_mem_nhdsWithin).exists
  have hTδ : 0 ≤ T + δ := by linarith
  refine ⟨δ, hδpos, Set.disjoint_left.2 fun z hzC hzK => ?_⟩
  by_cases hzU : z ∈ U
  · obtain ⟨z', hz't, hzb⟩ := mem_iUnion₂.1 hzU
    have hle : (((T + δ).toNNReal : ℝ≥0) : ℝ) ≤ R z' := by
      rw [Real.coe_toNNReal _ hTδ]; exact h₁ z' hz't
    have h := hdisj z' (htC z' hz't) _ hle
    rw [Real.coe_toNNReal _ hTδ] at h
    exact Set.disjoint_left.1 h hzb hzK
  · have him : 0 ≤ z.im := by
      have hsub : closure (fwdHull W (T + δ)) ⊆ {w : ℂ | 0 ≤ w.im} :=
        closure_minimal (fun w hw => (le_of_lt hw.1 : (0 : ℝ) ≤ w.im))
          (isClosed_le continuous_const Complex.continuous_im)
      exact hsub hzK
    have hz₂ : z ∈ C₂ := ⟨⟨hzC, hzU⟩, him⟩
    have hzK' : z ∈ fwdHull W (T + δ) :=
      A2TipSep.closure_fwdHull_inter_H_subset hW hTδ hzK (hC₂H hz₂)
    have hzK₂ : z ∈ fwdHull W (T + δ₂) := (QuantumZipper.fwdHull_mono (W := W)).1 (by linarith) hzK'
    exact Set.disjoint_left.1 hdisj₂ hz₂ hzK₂

/-- **Right-continuity of the closed hulls on closed sets.** -/
theorem exists_pos_disjoint_closure_fwdHull_of_isClosed {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 < T)
    {F : Set ℂ} (hF : IsClosed F) (hd : Disjoint F (closure (fwdHull W T))) :
    ∃ δ > 0, Disjoint F (closure (fwdHull W (T + δ))) := by
  set C := F ∩ closure (fwdHull W (T + 1)) with hCdef
  have hCc : IsCompact C :=
    (isBounded_fwdHull hW (T + 1)).isCompact_closure.inter_left hF
  have hCd : Disjoint C (closure (fwdHull W T)) := hd.mono_left inter_subset_left
  obtain ⟨δ, hδ, hdisj⟩ := exists_pos_disjoint_closure_fwdHull hW hT hCc hCd
  refine ⟨min δ 1, lt_min hδ one_pos, Set.disjoint_left.2 fun z hzF hzK => ?_⟩
  have hmono : ∀ {a b : ℝ}, a ≤ b → closure (fwdHull W a) ⊆ closure (fwdHull W b) :=
    fun hab => closure_mono ((QuantumZipper.fwdHull_mono (W := W)).1 hab)
  have h1 : z ∈ closure (fwdHull W (T + 1)) := hmono (by linarith [min_le_right δ 1]) hzK
  have h2 : z ∈ closure (fwdHull W (T + δ)) := hmono (by linarith [min_le_left δ 1]) hzK
  exact Set.disjoint_left.1 hdisj ⟨hzF, h1⟩ h2

end InteractingSLE.ZhanGT4.A1Good
