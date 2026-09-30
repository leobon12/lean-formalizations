import QuantumZipper.Proofs.Zipper.LocRichComapPath
import QuantumZipper.Proofs.Zipper.F1ReadMeasVague
import QuantumZipper.Proofs.Zipper.B5LocF1Side
import QuantumZipper.Proofs.Zipper.B5LocOn
import QuantumZipper.Proofs.LQG.PalmNormLocal

/-!
# LOC-HITSCALE (1): the unzipped left length read from the rich local data

Theorem 1.3, node E6 under D25 (`LocHitScaleStmt`, `LocRichComapMain.lean`). For a horizon
`T : ℕ` and a radius `R'`, the left length at a time `q ∈ [0,T]` is read from the rich local
data `d = locRich R' (x, W)` by

`lenLoc γ κ T R' q hq d = vagueRd γ (ufJ ((π, locField R' d.1), q)) O⁻ 0`,

with `π = pathX κ T d.2` the driver path extracted from the window and `O⁻` the left side image
read by `sideJ` (`F1.vagueRd`: the certificate-free reader of `ν [b, c]` from the approximants).
It is measurable in `d` (`measurable_lenLoc`) and correct (`lenLoc_locRich`) whenever the driver
is continuous, vanishes at `0`, is bounded by `M` on `[0,T]`, all real points are alive at time
`q > 0`, the unzipped field at time `q` has a global boundary limit, and `9M + 9√T + 7 ≤ R'`:
the approximants of the localized and of the true unzipped field agree on `[O⁻ - 1, 1]`, where
the tents of `vagueRd` live (`vagueRd_congr_on`), because `|O^±_q| ≤ 3M + 3√q`
(`abs_sideImages_le`, the estimate of `B5.sideSmallStmt`) and `f_q⁻¹` moves points by at most
`6M + 6√q` (`B5.norm_fwdMapInv_sub_le`).

Also: `iInf_rat_eq`, the infimum of an upward closed set of reals computed along the rationals
(used for the hitting time and the scale).

Own elementary bookkeeping (the paper, Sheffield arXiv:1012.4797 §5.4, pp. 70–72, asserts the
locality without proof); the side-image estimate follows the proof of `B5.sideSmallStmt`
(Lawler, *Conformally Invariant Processes in the Plane*, §4.1–4.2).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper.E6

open D3Plus MeasUnzip CharFun

/-! ## Local agreement of the reader -/

/-- `vagueRd γ · b c` only sees the approximants on `[b - 1, c + 1]`. -/
theorem vagueRd_congr_on {γ : ℝ} {y y' : FieldSample} {b c : ℝ}
    (h : ∀ k, ∀ t ∈ Icc (b - 1) (c + 1), avgReg y k (t : ℂ) = avgReg y' k (t : ℂ)) :
    F1.vagueRd γ y b c = F1.vagueRd γ y' b c := by
  unfold F1.vagueRd
  have e : ∀ n k : ℕ, ∫ t, F1.tent n b c t ∂bdryApprox γ y k =
      ∫ t, F1.tent n b c t ∂bdryApprox γ y' k := by
    intro n k
    refine PalmNorm.integral_eq_of_restrict_eq'
      (PalmNorm.bdryApprox_restrict_eq measurableSet_Icc (h k)) fun t ht => ?_
    by_contra hne
    have h1 := F1.tsupport_tent n b c (subset_tsupport _ hne)
    have h2 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    exact ht ⟨by linarith [h1.1], by linarith [h1.2]⟩
  simp only [e]

/-! ## The side images are bounded by the driver -/

/-- `|O^±_t| ≤ 3M + 3√t` when `|W| ≤ M` on `[0,t]` and all real points are alive at time
`t > 0` (the estimate in the proof of `B5.sideSmallStmt`). -/
theorem abs_sideImages_le {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t M : ℝ}
    (ht : 0 < t) (hM : ∀ r ∈ Icc (0 : ℝ) t, |W r| ≤ M)
    (halive : ∀ x : ℝ, x ≠ 0 → ∃ u, IsForwardSol W (x : ℂ) t u) :
    |(sideImages W t).1| ≤ 3 * M + 3 * Real.sqrt t ∧
      |(sideImages W t).2| ≤ 3 * M + 3 * Real.sqrt t := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, ht.le⟩)
  have hsq0 : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  obtain ⟨o₁, o₂, h₁, h₂⟩ := F1.exists_tendsto_sideImages_of_alive ht.le halive
  have e₁ : (sideImages W t).1 = o₁ := h₁.limUnder_eq
  have e₂ : (sideImages W t).2 = o₂ := h₂.limUnder_eq
  have hb₁ : ∀ᶠ x : ℝ in 𝓝[<] (0 : ℝ), -(3 * M + 3 * Real.sqrt t) ≤ (fwdMap W t (x : ℂ)).re ∧
      (fwdMap W t (x : ℂ)).re ≤ 0 := by
    filter_upwards [Ioo_mem_nhdsLT (show -Real.sqrt t < 0 by linarith)] with x hx
    obtain ⟨f, hf⟩ := halive x hx.2.ne
    rw [F1.fwdMap_eq_of_isForwardSol hf ⟨ht.le, le_rfl⟩]
    have := B5.neg_le_re_of_isForwardSol_neg hW hW0 ht hM hx.2 (by linarith [hx.1]) hf
    exact ⟨this.1, this.2.le⟩
  have hb₂ : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), 0 ≤ (fwdMap W t (x : ℂ)).re ∧
      (fwdMap W t (x : ℂ)).re ≤ 3 * M + 3 * Real.sqrt t := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < Real.sqrt t by linarith)] with x hx
    obtain ⟨f, hf⟩ := halive x hx.1.ne'
    rw [F1.fwdMap_eq_of_isForwardSol hf ⟨ht.le, le_rfl⟩]
    have := B5.re_le_of_isForwardSol_pos hW hW0 ht hM hx.1 (by linarith [hx.2]) hf
    exact ⟨this.2.le, this.1⟩
  have l₁ := ge_of_tendsto h₁ (hb₁.mono fun x hx => hx.1)
  have u₁ := le_of_tendsto h₁ (hb₁.mono fun x hx => hx.2)
  have l₂ := ge_of_tendsto h₂ (hb₂.mono fun x hx => hx.1)
  have u₂ := le_of_tendsto h₂ (hb₂.mono fun x hx => hx.2)
  rw [e₁, e₂]
  exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, by linarith⟩⟩

/-! ## Infima along the rationals -/

open Classical in
/-- The rational infimum with junk value `N`. -/
def ratInf (N : ℕ) (P : ℚ → Prop) : ℝ :=
  ⨅ q : ℚ, if 0 < (q : ℝ) ∧ (q : ℝ) ≤ N ∧ P q then (q : ℝ) else (N : ℝ)

open Classical in
theorem ratInf_bdd (N : ℕ) (P : ℚ → Prop) :
    BddBelow (range fun q : ℚ => if 0 < (q : ℝ) ∧ (q : ℝ) ≤ N ∧ P q then (q : ℝ) else (N : ℝ)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨q, rfl⟩
  dsimp only
  split_ifs with h
  · exact h.1.le
  · exact Nat.cast_nonneg N

open Classical in
theorem ratInf_le_N (N : ℕ) (P : ℚ → Prop) : ratInf N P ≤ N := by
  unfold ratInf
  refine (ciInf_le (ratInf_bdd N P) (N : ℚ)).trans ?_
  split_ifs <;> simp

open Classical in
/-- **The infimum of an upward closed set along the rationals.** -/
theorem iInf_rat_eq {E : Set ℝ} {N : ℕ} {P : ℚ → Prop}
    (hP : ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) ≤ N → (P q ↔ (q : ℝ) ∈ E))
    (h0 : ∀ s ∈ E, 0 ≤ s) (hup : ∀ s ∈ E, ∀ q : ℝ, s < q → q ≤ N → q ∈ E)
    (hne : E.Nonempty) (hle : sInf E ≤ N) : ratInf N P = sInf E := by
  have hb : BddBelow E := ⟨0, h0⟩
  unfold ratInf
  refine le_antisymm (le_of_forall_gt fun c hc => ?_) (le_ciInf fun q => ?_)
  · by_cases hcN : (N : ℝ) < c
    · exact (ratInf_le_N N P).trans_lt hcN
    · obtain ⟨s, hsE, hsc⟩ := exists_lt_of_csInf_lt hne hc
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hsc
      have hqN : (q : ℝ) ≤ N := hq2.le.trans (not_lt.1 hcN)
      have hq0 : 0 < (q : ℝ) := (h0 s hsE).trans_lt hq1
      have hPq : P q := (hP q hq0 hqN).2 (hup s hsE q hq1 hqN)
      refine (ciInf_le (ratInf_bdd N P) q).trans_lt ?_
      simp only [hq0, hqN, hPq, and_self, ite_true]
      exact hq2
  · split_ifs with h
    · exact csInf_le hb ((hP q h.1 h.2.1).1 h.2.2)
    · exact hle

open Classical in
/-- If the rational infimum is below the junk value, some admissible rational is. -/
theorem exists_of_ratInf_lt {N : ℕ} {P : ℚ → Prop} (h : ratInf N P < N) :
    ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) < N ∧ P q := by
  unfold ratInf at h
  obtain ⟨q, hq⟩ := exists_lt_of_ciInf_lt h
  split_ifs at hq with hc
  · exact ⟨q, hc.1, hq, hc.2.2⟩
  · exact absurd hq (lt_irrefl _)

theorem measurable_ratInf {α : Type*} [MeasurableSpace α] (N : ℕ) {P : α → ℚ → Prop}
    (hP : ∀ q : ℚ, MeasurableSet {a | P a q}) : Measurable fun a => ratInf N (P a) := by
  classical
  unfold ratInf
  refine Measurable.iInf fun q => ?_
  by_cases hq : 0 < (q : ℝ) ∧ (q : ℝ) ≤ N
  · simp only [hq, true_and]
    exact Measurable.ite (hP q) measurable_const measurable_const
  · have : ∀ a, ¬ (0 < (q : ℝ) ∧ (q : ℝ) ≤ N ∧ P a q) := fun a h => hq ⟨h.1, h.2.1⟩
    simp only [this, ite_false]
    exact measurable_const

/-! ## The local left length -/

theorem natCast_nonneg' (T : ℕ) : (0 : ℝ) ≤ T := Nat.cast_nonneg T

/-- The left length at time `q` read from the rich local data. -/
def lenLoc (γ κ : ℝ) (T R' : ℕ) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) T) (d : FullData) : ℝ≥0∞ :=
  F1.vagueRd γ (ufJ (natCast_nonneg' T) γ κ ((pathX κ T d.2, locField R' d.1), q))
    (sideJ (natCast_nonneg' T) κ q hq (pathX κ T d.2)).1 0

theorem measurable_pathX_snd (κ : ℝ) (T : ℕ) : Measurable fun d : FullData => pathX κ T d.2 :=
  (measurable_pathX κ T).comp measurable_snd

theorem measurable_ufJ_loc (γ κ : ℝ) (T R' : ℕ) (q : ℝ) :
    Measurable fun d : FullData =>
      ufJ (natCast_nonneg' T) γ κ ((pathX κ T d.2, locField R' d.1), q) := by
  have h1 : Measurable fun d : FullData => ((pathX κ T d.2, locField R' d.1), q) :=
    ((measurable_pathX_snd κ T).prodMk ((measurable_locField R').comp measurable_fst)).prodMk
      measurable_const
  exact (measurable_ufJ (natCast_nonneg' T) γ κ).comp h1

theorem measurable_sideJ_loc (κ : ℝ) (T : ℕ) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) T) :
    Measurable fun d : FullData => (sideJ (natCast_nonneg' T) κ q hq (pathX κ T d.2)).1 :=
  ((measurable_sideJ (natCast_nonneg' T) κ q hq).comp (measurable_pathX_snd κ T)).fst

theorem measurable_lenLoc (γ κ : ℝ) (T R' : ℕ) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) T) :
    Measurable (lenLoc γ κ T R' q hq) := by
  have h2 : Measurable fun d : FullData =>
      (ufJ (natCast_nonneg' T) γ κ ((pathX κ T d.2, locField R' d.1), q),
        (sideJ (natCast_nonneg' T) κ q hq (pathX κ T d.2)).1, (0 : ℝ)) :=
    (measurable_ufJ_loc γ κ T R' q).prodMk ((measurable_sideJ_loc κ T q hq).prodMk measurable_const)
  have h3 := (F1.measurable_vagueRd γ).comp h2
  have e : lenLoc γ κ T R' q hq = (fun p : FieldSample × ℝ × ℝ => F1.vagueRd γ p.1 p.2.1 p.2.2) ∘
      (fun d : FullData =>
      (ufJ (natCast_nonneg' T) γ κ ((pathX κ T d.2, locField R' d.1), q),
        (sideJ (natCast_nonneg' T) κ q hq (pathX κ T d.2)).1, (0 : ℝ))) := by
    funext d; rfl
  rw [e]
  exact h3

end QuantumZipper.E6
