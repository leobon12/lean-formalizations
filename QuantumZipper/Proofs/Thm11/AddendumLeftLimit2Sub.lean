import QuantumZipper.Proofs.Thm11.AddendumLeftLimit2Ortho
import QuantumZipper.Proofs.Thm11.AddendumLeftLimit2Max
import QuantumZipper.Proofs.Thm11.AddendumLeftLimit2Dynkin
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# THM11-AD3: a.s. uniform Cauchy property of the frozen fields along a subsequence

Levels `δ_i = Im a / 2^{i+1}`, frozen fields `X_i(t)` (taming level `c = δ_i`, horizon `T`).
With `G_i = E[g(arg Z_{σ_i})]` (g the bounded FD-8 function, κ ∈ (4,8)):

* energy identity (`integral_frozenField_sq`): `E[X_i(T)²] = Ψ(a) − G_i`;
* orthogonality (`integral_sq_sub_frozenField`): `E[(X_j(T) − X_i(T))²] = G_i − G_j` (`i ≤ j`),
  so `G` is antitone and bounded below by `−‖g‖`, hence convergent;
* along a subsequence `n` with `G_{n_k} − lim G ≤ 16^{−k}`, Doob's maximal inequality
  (`measure_exists_abs_gt_le`) and Borel–Cantelli give: a.s., eventually in `k`,
  `sup_{t ≤ T} |X_{n_{k+1}}(t) − X_{n_k}(t)| ≤ 2^{−k}`.

This is the L²-bounded martingale convergence argument of Revuz–Yor, *Continuous Martingales
and Brownian Motion*, Ch. II (Thm 1.7 Doob's inequality; Cor. 2.4 convergence), specialised to
the frozen fields; the Lyapunov function `Φ² + g∘arg` is own (from FD-8).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm11Add

open FrozenMart Thm11Lyap

/-- The levels `δ_i = Im a / 2^{i+1}`. -/
def lev (a : ℂ) (i : ℕ) : ℝ := a.im / 2 ^ (i + 1)

theorem lev_pos {a : ℂ} (ha : 0 < a.im) (i : ℕ) : 0 < lev a i := by unfold lev; positivity

theorem lev_le {a : ℂ} (ha : 0 < a.im) (i : ℕ) : lev a i ≤ a.im := by
  unfold lev
  exact div_le_self ha.le (one_le_pow₀ (by norm_num))

theorem lev_lt {a : ℂ} (ha : 0 < a.im) {i j : ℕ} (hij : i < j) : lev a j < lev a i := by
  unfold lev
  exact div_lt_div_of_pos_left ha (by positivity) (pow_lt_pow_right₀ (by norm_num) (by omega))

theorem lev_anti {a : ℂ} (ha : 0 < a.im) {i j : ℕ} (hij : i ≤ j) : lev a j ≤ lev a i := by
  rcases hij.lt_or_eq with h | rfl
  · exact (lev_lt ha h).le
  · exact le_rfl

theorem exists_lev_lt {a : ℂ} (ha : 0 < a.im) {ε : ℝ} (hε : 0 < ε) : ∃ i, lev a i < ε := by
  obtain ⟨i, hi⟩ := exists_pow_lt_of_lt_one (div_pos hε ha) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨i, ?_⟩
  unfold lev
  have h2 : (0 : ℝ) < 2 ^ (i + 1) := by positivity
  rw [div_lt_iff₀ h2]
  have : (1 / 2 : ℝ) ^ i = 1 / 2 ^ i := by rw [one_div_pow]
  rw [this, lt_div_iff₀ ha, one_div, inv_mul_lt_iff₀ (by positivity)] at hi
  nlinarith [pow_succ (2 : ℝ) i, pow_pos (by norm_num : (0 : ℝ) < 2) i]

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The frozen field at level `δ_i` (taming level `δ_i`). -/
abbrev fzX (κ : ℝ) (T : ℝ≥0) (B : ℝ≥0 → Ω → ℝ) (a : ℂ) (i : ℕ) : ℝ≥0 → Ω → ℝ :=
  frozenField κ (lev a i) (lev a i) T B a

/-- `G_i = E[g(arg Z_{σ_i})]`. -/
def gAvg (κ : ℝ) (T : ℝ≥0) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (a : ℂ) (i : ℕ) : ℝ :=
  ∫ ω, gFun κ (Complex.arg (fzZ κ (lev a i) B a
    (frozenTime κ (lev a i) (lev a i) T B a ω) ω)) ∂P

theorem integral_sq_sub_fzX (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous (B · ω)) {κ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) {a : ℂ} (ha : 0 < a.im)
    (T : ℝ≥0) {i j : ℕ} (hij : i ≤ j) :
    ∫ ω, (fzX κ T B a j T ω - fzX κ T B a i T ω) ^ 2 ∂P = gAvg κ T P B a i - gAvg κ T P B a j := by
  have hκ : 0 < κ := by linarith
  set 𝓕 := NonSwallow.bmFilt hBm
  have hBad := NonSwallow.bmFilt_adapted hBm
  have hpast := NonSwallow.bmFilt_le_past hBm
  rw [integral_sq_sub_frozenField hB hBm hBc hκ (lev_pos ha j) (lev_anti ha hij) (lev_le ha i) T,
    (integral_frozenField_sq hB hBc 𝓕 hBad hpast hκ4 hκ8 (lev_pos ha j) le_rfl
      (lev_le ha j) T).2.2,
    (integral_frozenField_sq hB hBc 𝓕 hBad hpast hκ4 hκ8 (lev_pos ha i) le_rfl
      (lev_le ha i) T).2.2]
  unfold gAvg; ring

theorem gAvg_antitone (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous (B · ω)) {κ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) {a : ℂ} (ha : 0 < a.im)
    (T : ℝ≥0) : Antitone (gAvg κ T P B a) := fun i j hij => by
  have h := integral_sq_sub_fzX (P := P) hB hBm hBc hκ4 hκ8 ha T hij
  have h0 : 0 ≤ ∫ ω, (fzX κ T B a j T ω - fzX κ T B a i T ω) ^ 2 ∂P :=
    integral_nonneg fun ω => sq_nonneg _
  linarith

theorem gAvg_ge (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous (B · ω)) {κ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) {a : ℂ} (ha : 0 < a.im)
    (T : ℝ≥0) {C : ℝ} (hC : ∀ θ ∈ Ioo 0 Real.pi, |gFun κ θ| ≤ C) (i : ℕ) :
    -C ≤ gAvg κ T P B a i := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set 𝓕 := NonSwallow.bmFilt hBm
  have hint := (integral_frozenField_sq hB hBc 𝓕 (NonSwallow.bmFilt_adapted hBm)
    (NonSwallow.bmFilt_le_past hBm) hκ4 hκ8 (lev_pos ha i) le_rfl (lev_le ha i) T).1
  have h := integral_mono (integrable_const (-C)) hint fun ω => by
    have him := fzZ_im_ge hBc (lev_pos ha i) (lev_le ha i) (κ := κ) (T := T) ω le_rfl
    exact (abs_le.1 (hC _ (NonSwallow.arg_mem_Ioo_of_im_pos ((lev_pos ha i).trans_le him)))).1
  simpa [gAvg] using h

/-- Pointwise `|x| ≤ (x²/η + η)/2`. -/
theorem abs_le_sq_div_add {x η : ℝ} (hη : 0 < η) : |x| ≤ (x ^ 2 / η + η) / 2 := by
  rw [div_add' _ _ _ hη.ne', div_div, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (|x| - η), sq_abs x]

/-- **Uniform Cauchy property along a subsequence, a.s.** -/
theorem exists_subseq_ae_cauchy (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous (B · ω)) {κ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) {a : ℂ} (ha : 0 < a.im)
    (T : ℝ≥0) : ∃ n : ℕ → ℕ, StrictMono n ∧ ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ∀ t : ℝ≥0, t ≤ T →
      |fzX κ T B a (n (k + 1)) t ω - fzX κ T B a (n k) t ω| ≤ (1 / 2) ^ k := by
  have hκ : 0 < κ := by linarith
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set 𝓕 := NonSwallow.bmFilt hBm
  have hBad := NonSwallow.bmFilt_adapted hBm
  have hpast := NonSwallow.bmFilt_le_past hBm
  obtain ⟨C, hC⟩ := exists_abs_gFun_le hκ4 hκ8
  set G := gAvg κ T P B a
  have hanti : Antitone G := gAvg_antitone hB hBm hBc hκ4 hκ8 ha T
  have hbdd : BddBelow (range G) := ⟨-C, by
    rintro _ ⟨i, rfl⟩; exact gAvg_ge hB hBm hBc hκ4 hκ8 ha T hC i⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  set L := ⨅ i, G i
  have hGL : ∀ i, L ≤ G i := fun i => ciInf_le hbdd i
  have hev : ∀ k : ℕ, ∀ᶠ i in atTop, G i - L < (1 / 16 : ℝ) ^ k := fun k => by
    have := (tendsto_order.1 hlim).2 (L + (1 / 16 : ℝ) ^ k) (lt_add_of_pos_right _ (by positivity))
    filter_upwards [this] with i hi; linarith
  obtain ⟨n, hn, hnG⟩ := extraction_forall_of_eventually hev
  refine ⟨n, hn, ?_⟩
  -- the martingale differences
  have hmart : ∀ i, Martingale (fzX κ T B a i) 𝓕 P := fun i =>
    frozenField_martingale hB hBc 𝓕 hBad hpast hκ (lev_pos ha i) le_rfl (lev_le ha i) T
  have hcont : ∀ i ω, Continuous fun t => fzX κ T B a i t ω := fun i ω =>
    continuous_frozenField hBc (lev_pos ha i) le_rfl (lev_le ha i) T ω
  set D : ℕ → ℝ≥0 → Ω → ℝ := fun k => fzX κ T B a (n (k + 1)) - fzX κ T B a (n k)
  have hD : ∀ k, Martingale (D k) 𝓕 P := fun k => (hmart _).sub (hmart _)
  have hDc : ∀ k ω, Continuous fun t => D k t ω := fun k ω => (hcont _ ω).sub (hcont _ ω)
  have hDb : ∀ k ω, |D k T ω| ≤ fzBound κ (lev a (n (k + 1))) T + fzBound κ (lev a (n k)) T :=
    fun k ω => (abs_sub _ _).trans (add_le_add
      (abs_frozenField_le hBc (lev_pos ha _) (lev_le ha _) T T ω)
      (abs_frozenField_le hBc (lev_pos ha _) (lev_le ha _) T T ω))
  have hDm : ∀ k, StronglyMeasurable (D k T) := fun k =>
    ((hD k).stronglyMeasurable T).mono (𝓕.le T)
  -- second moments
  have hD2 : ∀ k, ∫ ω, D k T ω ^ 2 ∂P ≤ (1 / 16 : ℝ) ^ k := fun k => by
    have e := integral_sq_sub_fzX (P := P) hB hBm hBc hκ4 hκ8 ha T (hn (Nat.lt_succ_self k)).le
    have h1 := hnG k
    have h2 := hGL (n (k + 1))
    simp only [D, Pi.sub_apply]
    rw [e]; linarith
  -- first moments
  have hD1 : ∀ k, ∫ ω, |D k T ω| ∂P ≤ (1 / 4 : ℝ) ^ k := fun k => by
    have hη : (0 : ℝ) < (1 / 4) ^ k := by positivity
    have hsq : Integrable (fun ω => D k T ω ^ 2) P :=
      ItoLite.integrable_of_bound_abs ((hDm k).pow 2) (K := _) fun ω => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hDb k ω) 2
    have hg : Integrable (fun ω => (D k T ω ^ 2 / (1 / 4) ^ k + (1 / 4) ^ k) / 2) P :=
      ((hsq.div_const _).add (integrable_const _)).div_const _
    have h := integral_mono_of_nonneg (Eventually.of_forall fun ω => abs_nonneg (D k T ω)) hg
      (Eventually.of_forall fun ω => abs_le_sq_div_add (x := D k T ω) hη)
    refine h.trans ?_
    rw [integral_div, integral_add (hsq.div_const _) (integrable_const _), integral_div,
      integral_const]
    simp only [probReal_univ, one_smul]
    have h16 : (1 / 16 : ℝ) ^ k = (1 / 4) ^ k * (1 / 4) ^ k := by
      rw [← mul_pow]; norm_num
    have := hD2 k
    rw [h16] at this
    have : (∫ ω, D k T ω ^ 2 ∂P) / (1 / 4) ^ k ≤ (1 / 4) ^ k := by
      rw [div_le_iff₀ hη]; exact this
    linarith
  -- Borel–Cantelli
  set A : ℕ → Set Ω := fun k => {ω | ∃ t ≤ T, (1 / 2 : ℝ) ^ k < |D k t ω|}
  have hA : ∀ k, P (A k) ≤ ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ k) := fun k => by
    refine (measure_exists_abs_gt_le (hD k) (hDc k) T (by positivity : (0 : ℝ) < (1 / 2) ^ k)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rw [div_le_iff₀ (by positivity)]
    have h4 : (1 / 4 : ℝ) ^ k = (1 / 2) ^ k * (1 / 2) ^ k := by rw [← mul_pow]; norm_num
    have := hD1 k
    rw [h4] at this
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k]
  have hsum : Summable fun k : ℕ => 2 * (1 / 2 : ℝ) ^ k :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 2
  have hfin : ∑' k, P (A k) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hA)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hfin] with ω hω
  filter_upwards [hω] with k hk t ht
  by_contra hcon
  exact hk ⟨t, ht, by simpa [D] using not_le.1 hcon⟩

end Thm11Add
end QuantumZipper
