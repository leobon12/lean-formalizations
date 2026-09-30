import QuantumZipper.Proofs.Zipper.BaseFin2Defs
import QuantumZipper.Proofs.Zipper.LogShiftW2Cap
import QuantumZipper.Proofs.Zipper.LocLenB5UPlus
import QuantumZipper.Proofs.Zipper.F2Step3DensUnif
import QuantumZipper.Proofs.Thm18.G4BSideGeom
import QuantumZipper.Proofs.Wire2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# X1-COV: the capacity-piece covering bound `BaseCovStmt`

Task X1-COV (`handoff/X1-BASE.md`, decision D75). Proves `BaseFin2.baseCovStmt_holds`.

**Route (own elementary argument; no published proof of X1 exists, see `BaseFin2Defs.lean`).**
Fix `q > 0`, `W = drive κ B ω`, and the positions `a(r) = (lswPos W q r).1`,
`b(r) = (lswPos W q r).2` (`F1.lswPos`: the chart-`q` preimages of the two sides of `η(r)`).
By the proved `F1.lswPosStmt_holds` (Lawler 2005 §4.1, semigroup + Carathéodory extension),
a.s. `a` is continuous and strictly increasing on `[0,q]`, `b` continuous and strictly decreasing,
and `F_q(a(r)) = F_q(b(r)) = η(r)` for `r ∈ (0,q]`; `a(0) = O⁻_q`, `b(0) = O⁺_q`, and
`a(s) = 0₋^V(q−s)`, `b(s) = 0₊^V(q−s)` (`F1.lswPos_fst_eq_zeroMinus`,
`G4Core.lswPos_snd_eq_zeroPlus`). Hence the one-chart identity `LocLen.b5UniformArcStmt_holds`
reads `L⁻(s) = ν(Ioo (a 0) (a s))`, `L⁺(s) = ν(Ioo (b s) (b 0))`.
Cover `(a 0, a(4^{-N}))` by `[a(4^{-k-1}), a(4^{-k})]`, `k ≥ N` (continuity at `0`); on the
`k`-th piece `x = a(r)` with `r ∈ [4^{-k-1}, 4^{-k}]` (IVT), so `|F_q(x)| = |η(r)| ≥ λ_k`, and the
piece has `ν`-mass `≤ L⁻(4^{-k})` (`ν` atomless, `Wire2.ae_nu0_regular`). Sum over `k`
(`lintegral_iUnion_le`). The right side is the same with `b`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace BaseFin2

/-! ## Deterministic helpers -/

theorem cov_rsq_eq (k : ℕ) : radius k ^ 2 = (4 : ℝ)⁻¹ ^ k := by
  unfold radius; rw [← pow_mul, mul_comm, pow_mul]; norm_num

theorem cov_rsq_pos (k : ℕ) : 0 < radius k ^ 2 := pow_pos (radius_pos k) 2

theorem cov_rsq_anti {m n : ℕ} (h : m ≤ n) : radius n ^ 2 ≤ radius m ^ 2 := by
  rw [cov_rsq_eq, cov_rsq_eq]
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h

theorem cov_tendsto_rsq : Tendsto (fun m : ℕ => radius m ^ 2) atTop (𝓝 0) := by
  simp_rw [cov_rsq_eq]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- Every point of `(a 0, a(4^{-N}))` lies in some piece `[a(4^{-k-N-1}), a(4^{-k-N})]`. -/
theorem cov_exists {a : ℝ → ℝ} {q : ℝ} {N : ℕ} (hN : radius N ^ 2 ≤ q)
    (hc : ContinuousOn a (Icc 0 q)) {x : ℝ} (hx : a 0 < x) (hxN : x < a (radius N ^ 2)) :
    ∃ k : ℕ, x ∈ Icc (a (radius (k + N + 1) ^ 2)) (a (radius (k + N) ^ 2)) := by
  have hq : 0 ≤ q := (cov_rsq_pos N).le.trans hN
  have ht : Tendsto (fun m : ℕ => a (radius m ^ 2)) atTop (𝓝 (a 0)) := by
    have h1 : Tendsto (fun m : ℕ => radius m ^ 2) atTop (𝓝[Icc 0 q] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨cov_tendsto_rsq, ?_⟩
      filter_upwards [eventually_ge_atTop N] with m hm
      exact ⟨(cov_rsq_pos m).le, (cov_rsq_anti hm).trans hN⟩
    exact (hc 0 ⟨le_rfl, hq⟩).tendsto.comp h1
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds hx))
  have hex : ∃ m : ℕ, a (radius (m + N) ^ 2) < x := ⟨n0, hn0 _ (by omega)⟩
  classical
  have hm1 : a (radius (Nat.find hex + N) ^ 2) < x := Nat.find_spec hex
  have hm0 : Nat.find hex ≠ 0 := by
    intro h
    rw [h, zero_add] at hm1
    exact absurd hxN (not_lt.2 hm1.le)
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hjm : ¬ a (radius (j + N) ^ 2) < x := Nat.find_min hex (by omega)
  refine ⟨j, ?_, not_lt.1 hjm⟩
  rw [show j + N + 1 = Nat.find hex + N by omega]
  exact hm1.le

/-- Covering bound for a lower integral. -/
theorem cov_lintegral_le_tsum (ν : Measure ℝ) (f : ℝ → ℝ≥0∞) (U : Set ℝ) (S : ℕ → Set ℝ)
    (hSm : ∀ k, MeasurableSet (S k)) (hU : U ⊆ ⋃ k, S k) (w L : ℕ → ℝ≥0∞)
    (hf : ∀ k, ∀ x ∈ S k, f x ≤ w k) (hL : ∀ k, ν (S k) ≤ L k) :
    ∫⁻ x in U, f x ∂ν ≤ ∑' k, w k * L k := by
  calc ∫⁻ x in U, f x ∂ν ≤ ∫⁻ x in ⋃ k, S k, f x ∂ν := lintegral_mono_set hU
    _ ≤ ∑' k, ∫⁻ x in S k, f x ∂ν := lintegral_iUnion_le S f
    _ ≤ ∑' k, w k * L k := by
      refine ENNReal.tsum_le_tsum fun k => ?_
      calc ∫⁻ x in S k, f x ∂ν ≤ ∫⁻ _ in S k, w k ∂ν :=
            lintegral_mono_ae ((ae_restrict_iff' (hSm k)).2 (Eventually.of_forall (hf k)))
        _ = w k * ν (S k) := setLIntegral_const (S k) (w k)
        _ ≤ w k * L k := by gcongr; exact hL k

theorem cov_ofReal_rpow_neg_le {t p : ℝ} (ht : 0 ≤ t) (hp : 0 < p) {L : ℝ≥0∞}
    (hL : L ≤ ENNReal.ofReal t) : ENNReal.ofReal (t ^ (-p)) ≤ L ^ (-p) := by
  rcases ht.eq_or_lt with h | h
  · subst h
    rw [Real.zero_rpow (neg_neg_of_pos hp).ne]
    simp
  · rw [← ENNReal.ofReal_rpow_of_pos h, ENNReal.rpow_neg, ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv.2 (ENNReal.rpow_le_rpow hL hp.le)

theorem cov_measure_Icc_le_left {ν : Measure ℝ} (hν : ∀ x, ν {x} = 0) {u c v : ℝ} (h : u < c) :
    ν (Icc c v) ≤ ν (Ioo u v) := by
  calc ν (Icc c v) ≤ ν (Ioo u v ∪ {v}) := by
        refine measure_mono fun x hx => ?_
        rcases eq_or_lt_of_le hx.2 with e | e
        · exact Or.inr e
        · exact Or.inl ⟨h.trans_le hx.1, e⟩
    _ ≤ ν (Ioo u v) + ν {v} := measure_union_le _ _
    _ = ν (Ioo u v) := by rw [hν, add_zero]

theorem cov_measure_Icc_le_right {ν : Measure ℝ} (hν : ∀ x, ν {x} = 0) {u c v : ℝ} (h : c < u) :
    ν (Icc v c) ≤ ν (Ioo v u) := by
  calc ν (Icc v c) ≤ ν (Ioo v u ∪ {v}) := by
        refine measure_mono fun x hx => ?_
        rcases eq_or_lt_of_le hx.1 with e | e
        · exact Or.inr e.symm
        · exact Or.inl ⟨e, hx.2.trans_lt h⟩
    _ ≤ ν (Ioo v u) + ν {v} := measure_union_le _ _
    _ = ν (Ioo v u) := by rw [hν, add_zero]

/-- On the `k`-th capacity window, `|F_q(p(r))|^{−κ/2} ≤ λ_k^{−κ/2}`. -/
theorem cov_ptwise {κ : ℝ} (hκ : 0 < κ) {Ω : Type} (B : ℝ≥0 → Ω → ℝ) (ω : Ω) {q : ℝ}
    {p : ℝ → ℝ} (htr : ∀ r ∈ Ioc 0 q, F2.extInv (drive κ B ω) q (p r : ℂ) = sleTrace κ B ω r)
    {k : ℕ} (hk : radius k ^ 2 ≤ q) {r : ℝ} (hr : r ∈ Icc (radius (k + 1) ^ 2) (radius k ^ 2)) :
    ENNReal.ofReal (‖F2.invBdry (drive κ B ω) q (p r)‖ ^ (-(κ / 2))) ≤
      winLam κ B ω k ^ (-(κ / 2)) := by
  have hr0 : r ∈ Ioc 0 q := ⟨(cov_rsq_pos _).trans_le hr.1, hr.2.trans hk⟩
  rw [← F2.extInv_ofReal, htr r hr0]
  exact cov_ofReal_rpow_neg_le (norm_nonneg _) (by positivity)
    (iInf₂_le (f := fun r (_ : r ∈ Icc (radius (k + 1) ^ 2) (radius k ^ 2)) =>
      ENNReal.ofReal ‖sleTrace κ B ω r‖) r hr)

/-! ## The a.s. assembly -/

/-- **`BaseCovStmt` holds.** -/
theorem baseCovStmt_holds : BaseCovStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind q hq
  have hB' : IsBrownianReal (RegUnif.negB B) P := hB.neg
  filter_upwards [F1.lswPosStmt_holds κ hκ hκ4 P B hB, F1.ae_lsw2_driver_facts hκ hκ4 hB,
    F1.ae_lsw2_driver_facts hκ hκ4 hB', LocLen.b5UniformArcStmt_holds κ hκ hκ4 q hq P B X hB hX hind,
    Wire2.ae_nu0_regular (κ := κ) (T := q) (B := B) (X := X) hκ hκ4 hq hB hX hind,
    hB.eval_zero_ae_eq_zero]
    with ω hLsw ⟨hW, hW0, hneg, hK, hal, _⟩ ⟨_, _, _, hK', hal', _⟩ hU hA h0 N hN
  rw [RegUnif.drive_negB] at hK' hal'
  obtain ⟨hac, hbc, ham, hba, htr⟩ := hLsw q hq.le
  set W := drive κ B ω with hWdef
  set a : ℝ → ℝ := fun r => (F1.lswPos W q r).1 with hadef
  set b : ℝ → ℝ := fun r => (F1.lswPos W q r).2 with hbdef
  set ν := qBoundaryMeasure (Real.sqrt κ) (F2.unzY κ (X ω) W q) with hνdef
  have hνat : ∀ x, ν {x} = 0 := by
    intro x; rw [hνdef, ← F2.h0f_eq_unzY]; exact hA.1 x
  have hside : sideImages W q = (a 0, b 0) := by
    rw [← F1.lswPos_zero_drive h0 q]
  have hmem : ∀ k, N ≤ k → radius k ^ 2 ∈ Icc 0 q := fun k hk =>
    ⟨(cov_rsq_pos k).le, (cov_rsq_anti hk).trans hN⟩
  have h0q : (0 : ℝ) ∈ Icc 0 q := ⟨le_rfl, hq.le⟩
  have hzm : ∀ s ∈ Icc 0 q, zeroMinus (B2.Vr κ q B ω) (q - s) = a s := fun s hs =>
    (F1.lswPos_fst_eq_zeroMinus hW hW0 hneg hK hal hq hs).symm
  have hzp : ∀ s ∈ Icc 0 q, zeroPlus (B2.Vr κ q B ω) (q - s) = b s := fun s hs =>
    (Thm18Asm.G4Core.lswPos_snd_eq_zeroPlus hW hW0 hneg hK' hal' hq hs).symm
  have hlen : ∀ k, N ≤ k → (lenArc κ B X ω (radius k ^ 2)).1 = ν (Ioo (a 0) (a (radius k ^ 2))) ∧
      (lenArc κ B X ω (radius k ^ 2)).2 = ν (Ioo (b (radius k ^ 2)) (b 0)) := by
    intro k hk
    obtain ⟨e1, e2⟩ := hU _ (hmem k hk)
    have hq0 : zeroMinus (B2.Vr κ q B ω) q = a 0 := by simpa using hzm 0 h0q
    have hq0' : zeroPlus (B2.Vr κ q B ω) q = b 0 := by simpa using hzp 0 h0q
    rw [F2.h0f_eq_unzY, hq0, hzm _ (hmem k hk)] at e1
    rw [F2.h0f_eq_unzY, hq0', hzp _ (hmem k hk)] at e2
    exact ⟨e1, e2⟩
  have hNm := hmem N le_rfl
  have hNpos := cov_rsq_pos N
  have hδa : 0 < a (radius N ^ 2) - a 0 := sub_pos.2 (ham h0q hNm hNpos)
  have hδb : 0 < b 0 - b (radius N ^ 2) := sub_pos.2 (hba h0q hNm hNpos)
  refine ⟨min (a (radius N ^ 2) - a 0) (b 0 - b (radius N ^ 2)), lt_min hδa hδb, ?_, ?_⟩
  · rw [hside]
    have hs : Ioo (a 0) (a 0 + min (a (radius N ^ 2) - a 0) (b 0 - b (radius N ^ 2))) ⊆
        Ioo (a 0) (a (radius N ^ 2)) := Ioo_subset_Ioo le_rfl (by
      linarith [min_le_left (a (radius N ^ 2) - a 0) (b 0 - b (radius N ^ 2))])
    refine (lintegral_mono_set hs).trans ?_
    refine cov_lintegral_le_tsum ν _ _
      (fun k => Icc (a (radius (k + N + 1) ^ 2)) (a (radius (k + N) ^ 2)))
      (fun k => measurableSet_Icc) (fun x hx => mem_iUnion.2 (cov_exists hN hac hx.1 hx.2))
      (fun k => winLam κ B ω (k + N) ^ (-(κ / 2))) (fun k => (lenArc κ B X ω (radius (k + N) ^ 2)).1)
      ?_ ?_
    · intro k x hx
      have hsub : Icc (radius (k + N + 1) ^ 2) (radius (k + N) ^ 2) ⊆ Icc 0 q := fun r hr =>
        ⟨(cov_rsq_pos _).le.trans hr.1, hr.2.trans (hmem _ (by omega)).2⟩
      obtain ⟨r, hr, rfl⟩ := intermediate_value_Icc (cov_rsq_anti (Nat.le_succ _))
        (hac.mono hsub) hx
      exact cov_ptwise hκ B ω (fun r hr => (htr r hr).1) (hmem _ (by omega)).2 hr
    · intro k
      rw [(hlen _ (by omega)).1]
      exact cov_measure_Icc_le_left hνat (ham h0q (hmem _ (by omega)) (cov_rsq_pos _))
  · rw [hside]
    have hs : Ioo (b 0 - min (a (radius N ^ 2) - a 0) (b 0 - b (radius N ^ 2))) (b 0) ⊆
        Ioo (b (radius N ^ 2)) (b 0) := Ioo_subset_Ioo (by
      linarith [min_le_right (a (radius N ^ 2) - a 0) (b 0 - b (radius N ^ 2))]) le_rfl
    refine (lintegral_mono_set hs).trans ?_
    refine cov_lintegral_le_tsum ν _ _
      (fun k => Icc (b (radius (k + N) ^ 2)) (b (radius (k + N + 1) ^ 2)))
      (fun k => measurableSet_Icc) (fun x hx => ?_)
      (fun k => winLam κ B ω (k + N) ^ (-(κ / 2))) (fun k => (lenArc κ B X ω (radius (k + N) ^ 2)).2)
      ?_ ?_
    · obtain ⟨k, hk⟩ := cov_exists (a := fun r => -b r) hN hbc.neg (x := -x)
        (neg_lt_neg hx.2) (neg_lt_neg hx.1)
      exact mem_iUnion.2 ⟨k, neg_le_neg_iff.1 hk.2, neg_le_neg_iff.1 hk.1⟩
    · intro k x hx
      have hsub : Icc (radius (k + N + 1) ^ 2) (radius (k + N) ^ 2) ⊆ Icc 0 q := fun r hr =>
        ⟨(cov_rsq_pos _).le.trans hr.1, hr.2.trans (hmem _ (by omega)).2⟩
      obtain ⟨r, hr, rfl⟩ := intermediate_value_Icc' (cov_rsq_anti (Nat.le_succ _))
        (hbc.mono hsub) hx
      exact cov_ptwise hκ B ω (fun r hr => (htr r hr).2) (hmem _ (by omega)).2 hr
    · intro k
      rw [(hlen _ (by omega)).2]
      exact cov_measure_Icc_le_right hνat (hba h0q (hmem _ (by omega)) (cov_rsq_pos _))

end BaseFin2
end QuantumZipper
