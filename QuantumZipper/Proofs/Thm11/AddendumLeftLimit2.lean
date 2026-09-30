import QuantumZipper.Proofs.Thm11.AddendumLeftLimit2Sub
import QuantumZipper.Proofs.Thm11.AddendumLeftLimit
import QuantumZipper.Proofs.Thm12.CharFun

/-!
# THM11-AD3 (TASKS R19): left limits of `𝔥_t(a)` at swallowing times, κ ∈ (4,8)

Sheffield, *Conformal weldings of random surfaces* (arXiv:1012.4797), Theorem 1.1 addendum
(§1, p. 12): a point `a` swallowed at time `τ(a)` receives the value
`𝔥_{τ(a)}(a) := lim_{s ↑ τ(a)} 𝔥_s(a)`. The paper gives no proof that the limit exists; we prove
it almost surely (`ae_tendsto_hTfwd_swallow`).

Proof. For levels `δ_i ↓ 0` let `σ_i` be the first time `Im f_t(a) ≤ δ_i` (capped at `T`). The
frozen fields `X_i(t) = 𝔥_{t∧σ_i}(a)` are bounded continuous martingales; with the bounded FD-8
function `g` (κ < 8), `Φ² + g∘arg` is harmonic for the one-point diffusion, so
`E[(X_j − X_i)(T)²] = G_i − G_j` with `G_i = E g(arg Z_{σ_i})` antitone and bounded. Doob's
maximal inequality and Borel–Cantelli along a fast subsequence give a.s. summable oscillations of
`𝔥` on the plates `[σ_{n_k}, σ_{n_{k+1}}]` (`AddendumLeftLimit2Sub`), and on `{τ(a) < T}` the
times `σ_i` increase strictly to `τ(a)` (FD-2 through `alive_of_le_frozenTime`,
`im_isForwardSol_le`). The deterministic Cauchy criterion
`exists_tendsto_nhdsWithin_Iio_of_summable` concludes. Source for the probabilistic step:
Revuz–Yor, *Continuous Martingales and Brownian Motion*, Ch. II, Thm 1.7 (Doob's inequality) and
§2 (L²-bounded martingale convergence); the Lyapunov function is own (FD-8).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm11Add

open FrozenMart Thm11Lyap

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The left limit exists a.s. on `{τ(a) < T}` (good version of `B`). -/
theorem ae_tendsto_fieldAt_of_lt (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous (B · ω)) {κ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) {a : ℂ} (ha : a ∈ H)
    (T : ℝ≥0) : ∀ᵐ ω ∂P, swallowTime (drive κ B ω) a < ENNReal.ofReal T → ∃ ℓ : ℝ,
      Tendsto (fieldAt κ (drive κ B ω) a) (𝓝[<] (swallowTime (drive κ B ω) a).toReal)
        (𝓝 ℓ) := by
  have ha0 : 0 < a.im := ha
  obtain ⟨n, hn, hae⟩ := exists_subseq_ae_cauchy (P := P) hB hBm hBc hκ4 hκ8 ha0 T
  filter_upwards [hae] with ω hω hτT
  obtain ⟨K, hK⟩ := eventually_atTop.1 hω
  have hW := continuous_drive_path (κ := κ) hBc ω
  set W := drive κ B ω with hW_def
  set τ := swallowTime W a with hτ_def
  have hτtop : τ ≠ ⊤ := ne_top_of_lt hτT
  set τr := τ.toReal
  have hτeq : τ = ENNReal.ofReal τr := (ENNReal.ofReal_toReal hτtop).symm
  set s : ℕ → ℝ := fun i => (frozenTime κ (lev a i) (lev a i) T B a ω : ℝ) with hs_def
  have hs_le' : ∀ i, s i ≤ τr := fun i => by
    have := ofReal_frozenTime_le_swallowTime (κ := κ) hBc (lev_pos ha0 i) le_rfl (lev_le ha0 i) T ω
    rw [← hW_def, ← hτ_def, hτeq] at this
    exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).1 this
  have hτT' : τr < T := by
    rw [hτeq] at hτT; exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).1 hτT
  have hsT : ∀ i, frozenTime κ (lev a i) (lev a i) T B a ω < T := fun i => by
    have : s i < (T : ℝ) := (hs_le' i).trans_lt hτT'
    exact_mod_cast this
  have hhit : ∀ i, (fwdMap W (s i) a).im ≤ lev a i := fun i =>
    im_fwdMap_frozenTime_le hBc (lev_pos ha0 i) le_rfl (lev_le ha0 i) ω (hsT i)
  have hge : ∀ i, ∀ r ∈ Icc (0 : ℝ) (s i), lev a i ≤ (fwdMap W r a).im := fun i r hr =>
    ((alive_of_le_frozenTime hBc (lev_pos ha0 i) le_rfl (lev_le ha0 i) (T := T) ω
      le_rfl).2 r hr).2.2
  have hsmono : StrictMono s := by
    refine strictMono_nat_of_lt_succ fun i => ?_
    by_contra hcon
    push Not at hcon
    have h1 := hge i (s (i + 1)) ⟨NNReal.coe_nonneg _, hcon⟩
    have h2 := hhit (i + 1)
    have h3 := lev_lt ha0 (Nat.lt_succ_self i)
    linarith
  have hslt : ∀ i, s i < τr := fun i => (hsmono (Nat.lt_succ_self i)).trans_le (hs_le' (i + 1))
  have htend : Tendsto s atTop (𝓝[<] τr) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_order.2 ⟨fun u hu => ?_,
      fun u hu => Eventually.of_forall fun i => (hslt i).trans hu⟩, Eventually.of_forall hslt⟩
    rcases lt_or_ge u 0 with hu0 | hu0
    · exact Eventually.of_forall fun i => hu0.trans_le (NNReal.coe_nonneg _)
    have hnot : a ∉ fwdHull W u := fun h => by
      have h2 : τ ≤ ENNReal.ofReal u := h.2
      rw [hτeq] at h2
      exact absurd ((ENNReal.ofReal_le_ofReal_iff hu0).1 h2) (not_le.2 hu)
    obtain ⟨v, hv⟩ := exists_isForwardSol_of_not_mem_fwdHull hu0 ha hnot
    have hvim := im_isForwardSol_le hW ha0 hv
    have hpos : 0 < (v u).im := hvim.2 u ⟨hu0, le_rfl⟩
    obtain ⟨i0, hi0⟩ := exists_lev_lt ha0 hpos
    filter_upwards [eventually_ge_atTop i0] with i hi
    by_contra hcon
    push Not at hcon
    have hmem : s i ∈ Icc (0 : ℝ) u := ⟨NNReal.coe_nonneg _, hcon⟩
    have h1 : (v u).im ≤ (v (s i)).im := hvim.1 hmem ⟨hu0, le_rfl⟩ hcon
    have h2 : fwdMap W (s i) a = v (s i) := fwdMap_eq hW ha0 hv hmem
    have h3 := hhit i
    rw [h2] at h3
    have h4 := lev_anti ha0 hi
    linarith
  -- the subsequence of plates
  set σ' : ℕ → ℝ := fun k => s (n (k + K)) with hσ'_def
  have hσmono : StrictMono σ' := fun k l hkl => hsmono (hn (by omega))
  have hσtend : Tendsto σ' atTop (𝓝[<] τr) :=
    htend.comp (hn.tendsto_atTop.comp (tendsto_add_atTop_nat K))
  have hbsum : Summable fun k : ℕ => (1 / 2 : ℝ) ^ (k + K) := by
    have := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).mul_left ((1 / 2 : ℝ) ^ K)
    refine this.congr fun k => ?_
    rw [pow_add]; ring
  refine exists_tendsto_nhdsWithin_Iio_of_summable hσmono (fun k => hslt _) hσtend
    (fun k => by positivity) hbsum fun k t ht => ?_
  set i := n (k + K)
  set j := n (k + K + 1)
  have ht0 : 0 ≤ t := (NNReal.coe_nonneg _).trans ht.1
  have htj : t ≤ s j := by
    have := ht.2; simp only [σ', show k + 1 + K = k + K + 1 by omega] at this; exact this
  have hti : s i ≤ t := ht.1
  have htT : t.toNNReal ≤ T := by
    rw [Real.toNNReal_le_iff_le_coe]; exact htj.trans (hs_le' j) |>.trans hτT'.le
  have hb := hK (k + K) (by omega) t.toNNReal htT
  simp only [fzX] at hb
  rw [frozenField_eq_fieldAt hBc (lev_pos ha0 _) le_rfl (lev_le ha0 _),
    frozenField_eq_fieldAt hBc (lev_pos ha0 _) le_rfl (lev_le ha0 _)] at hb
  have e1 : min t.toNNReal (frozenTime κ (lev a j) (lev a j) T B a ω) = t.toNNReal :=
    min_eq_left ((Real.toNNReal_le_iff_le_coe).2 htj)
  have e2 : min t.toNNReal (frozenTime κ (lev a i) (lev a i) T B a ω) =
      frozenTime κ (lev a i) (lev a i) T B a ω :=
    min_eq_right ((Real.le_toNNReal_iff_coe_le ht0).2 hti)
  rw [e1, e2, Real.coe_toNNReal _ ht0] at hb
  exact hb

/-- **TASKS R19 (THM11-AD3).** For κ ∈ (4,8) and `a ∈ ℍ`, almost surely, if `a` is swallowed
(`τ(a) < ∞`) then `𝔥_s(a) = h0fwd κ (f_s(a)) − χ Im log f_s'(a)` has a limit as `s ↑ τ(a)`. -/
theorem ae_tendsto_hTfwd_swallow (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 4 < κ) (hκ8 : κ < 8)
    {a : ℂ} (ha : a ∈ H) : ∀ᵐ ω ∂P, swallowTime (drive κ B ω) a < ⊤ → ∃ ℓ : ℝ,
      Tendsto (fun s => h0fwd κ (fwdMap (drive κ B ω) s a) -
          chiC κ * (logDerivFwd (drive κ B ω) s a).im)
        (𝓝[<] (swallowTime (drive κ B ω) a).toReal) (𝓝 ℓ) := by
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := CharFun.exists_good_version hB
  have hB' : IsPreBrownianReal B' P :=
    hB.toIsPreBrownianReal.congr fun t => hB'eq.mono fun ω h => (h t).symm
  have hdrive : ∀ᵐ ω ∂P, drive κ B' ω = drive κ B ω :=
    hB'eq.mono fun ω h => funext fun t => by simp [drive, h]
  have hall : ∀ᵐ ω ∂P, ∀ N : ℕ, swallowTime (drive κ B' ω) a <
      ENNReal.ofReal ((N : ℝ≥0) : ℝ) → ∃ ℓ : ℝ, Tendsto (fieldAt κ (drive κ B' ω) a)
        (𝓝[<] (swallowTime (drive κ B' ω) a).toReal) (𝓝 ℓ) :=
    ae_all_iff.2 fun N => ae_tendsto_fieldAt_of_lt hB' hB'm hB'c hκ hκ8 ha N
  filter_upwards [hall, hdrive] with ω h hd hτ
  rw [← hd] at hτ ⊢
  obtain ⟨N, hN⟩ := exists_nat_gt (swallowTime (drive κ B' ω) a).toReal
  refine h N ?_
  rw [← ENNReal.ofReal_toReal hτ.ne]
  exact (ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast (ENNReal.toReal_nonneg.trans_lt hN))).2
    (by simpa using hN)

end Thm11Add
end QuantumZipper
