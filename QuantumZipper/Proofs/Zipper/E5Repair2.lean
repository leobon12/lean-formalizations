import QuantumZipper.Proofs.Zipper.E5Repair1
import QuantumZipper.Proofs.Zipper.E5Dens

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# E5 repair, part 2: E5a (germ-density lemma) under a Wiener measure `W` (decision D39)

`LengthMarkov.GermDensity.germDensity_core` and `E5.germDensity_withDensity` assume
`IsBrownianReal (fun t b => b t) W`, which no measure satisfies (`E5Final4.not_isBrownianReal_coord`),
so they are vacuous. This file re-proves them under the repaired hypothesis
`IsPreBrownianReal (fun t b => b t) W` (`W` is Wiener measure on the product path space). The
proofs are the committed ones verbatim, except at the two places that used `IsBrownianReal.cont`:

* the germ-triviality step `tendsto_condDens'` uses Blumenthal's 0-1 law in the form
  `E5.isTrivialSigma_iInf_bmPast_coord` (E5Repair1);
* the Brownian-scaling step replaces `filter_upwards [hW.cont]` by `E5.ae_eq_of_continuous`
  (two measurable functionals agreeing on continuous paths agree `W`-a.e.).

Mathematical source as for the committed versions (Sheffield arXiv:1012.4797, §5.4, proof of
Lemma 5.6, the "zooming in" step; Blumenthal's 0-1 law: Karatzas–Shreve §2.7.A, Theorem 7.17).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace QuantumZipper
namespace E5

open LengthMarkov LengthMarkov.GermDensity GermZeroOne StrongMarkov

section WienerRepair

variable {W : Measure (ℝ≥0 → ℝ)} [IsProbabilityMeasure W]
variable {𝕍 : Type*} [MeasurableSpace 𝕍] {ψ : 𝕍 → (ℝ≥0 → ℝ) → ℝ}

/-- Germ triviality (`tendsto_condDens` under a pre-Brownian coordinate measure). -/
theorem tendsto_condDens' (hW : IsPreBrownianReal (fun t (b : ℝ≥0 → ℝ) => b t) W)
    (hψ : Measurable (fun p : 𝕍 × (ℝ≥0 → ℝ) => ψ p.1 p.2)) (v : 𝕍) (hψ1 : ∫ b, ψ v b ∂W = 1) :
    Tendsto (fun k => ∫ b, |condDens W (epsSeq k) ψ v (pathRestr (epsSeq k) b) - 1| ∂W)
      atTop (𝓝 0) := by
  have hψi : Integrable (ψ v) W := Integrable.of_integral_ne_zero (by rw [hψ1]; exact one_ne_zero)
  have h := tendsto_integral_abs_condExp_sub (P := W)
    (fun n => bmPast_le measurable_coord _) (fun a b h => bmPast_mono (epsSeq_antitone h))
    (isTrivialSigma_iInf_bmPast_coord hW) hψi
  rw [hψ1] at h
  refine h.congr' (Eventually.of_forall fun k => integral_congr_ae ?_)
  filter_upwards [condDens_ae_eq_condExp hW hψ v hψ1 (epsSeq k)] with b hb
  exact congrArg (fun y => |y - 1|) hb.symm

end WienerRepair

section CoreRepair

variable {W : Measure (ℝ≥0 → ℝ)}

/-- **E5a, core form** (a single conditioning variable `V`). -/
theorem germDensity_core' {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hW : IsPreBrownianReal (fun t (b : ℝ≥0 → ℝ) => b t) W)
    {𝕍 : Type*} [MeasurableSpace 𝕍] {V : Ω → 𝕍} (hV : Measurable V)
    {D : Ω → ℝ≥0 → ℝ} (hD : Measurable D) (hDc : ∀ ω, Continuous (D ω))
    {u₀ : ℝ≥0} (hu₀ : 0 < u₀)
    {ψ : 𝕍 → (ℝ≥0 → ℝ) → ℝ} (hψ : Measurable (fun p : 𝕍 × (ℝ≥0 → ℝ) => ψ p.1 p.2))
    (hψ0 : ∀ v b, 0 ≤ ψ v b) (hψ1 : ∀ v, ∫ b, ψ v b ∂W = 1)
    (hlaw : ∀ Φ : 𝕍 × (Set.Iic u₀ → ℝ) → ℝ, Measurable Φ → (∃ C, ∀ p, |Φ p| ≤ C) →
      ∫ ω, Φ (V ω, pathRestr u₀ (D ω)) ∂P =
        ∫ ω, ∫ b, Φ (V ω, pathRestr u₀ b) * ψ (V ω) b ∂W ∂P)
    {a : ℕ → 𝕍 → ℝ≥0} (ha : ∀ n, Measurable (a n)) (hapos : ∀ n v, 0 < a n v)
    (hprob : ∀ ε : ℝ≥0, 0 < ε → Tendsto (fun n => P {ω | ε ≤ a n (V ω)}) atTop (𝓝 0))
    (S : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    ∃ N, ∀ n ≥ N, ∀ Γ : 𝕍 × (Set.Iic S → ℝ) → ℝ, Measurable Γ → (∀ p, |Γ p| ≤ 1) →
      |∫ ω, Γ (V ω, LengthMarkov.GermDensity.rescale S (a n (V ω)) (D ω)) ∂P -
        ∫ ω, ∫ b, Γ (V ω, pathRestr S b) ∂W ∂P| ≤ η := by
  haveI : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  have hW' := hW
  have hψi : ∀ v, Integrable (ψ v) W := fun v =>
    Integrable.of_integral_ne_zero (by rw [hψ1]; exact one_ne_zero)
  -- the germ defect `δ k v`
  set δ : ℕ → 𝕍 → ℝ := fun k v =>
    ∫ b, |condDens W (epsSeq k) ψ v (pathRestr (epsSeq k) b) - 1| ∂W with hδ_def
  have hcdm : ∀ k, Measurable (fun p : 𝕍 × (ℝ≥0 → ℝ) =>
      condDens W (epsSeq k) ψ p.1 (pathRestr (epsSeq k) p.2)) := fun k =>
    (measurable_condDens hψ _).comp
      (measurable_fst.prodMk ((measurable_pathRestr _).comp measurable_snd))
  have hδm : ∀ k, Measurable (δ k) := fun k =>
    ((continuous_abs.measurable.comp ((hcdm k).sub measurable_const)).stronglyMeasurable.integral_prod_right').measurable
  have hδ0 : ∀ k v, 0 ≤ δ k v := fun k v => integral_nonneg fun _ => abs_nonneg _
  have hδ2 : ∀ k v, δ k v ≤ 2 := by
    intro k v
    have hci := integrable_condDens hW' hψ v (hψ1 v) (epsSeq k)
    calc δ k v ≤ ∫ b, (condDens W (epsSeq k) ψ v (pathRestr (epsSeq k) b) + 1) ∂W := by
          refine integral_mono (hci.sub (integrable_const _)).abs (hci.add (integrable_const _))
            fun b => ?_
          have := condDens_nonneg (W := W) hψ0 (epsSeq k) v (pathRestr (epsSeq k) b)
          rw [abs_le]; constructor <;> linarith
      _ = 2 := by
          rw [integral_add hci (integrable_const _), integral_condDens hW' hψ v (hψ1 v)]
          simp; norm_num
  have hδlim : Tendsto (fun k => ∫ ω, δ k (V ω) ∂P) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := P) (F := fun k ω => δ k (V ω))
      (f := fun _ => (0 : ℝ)) (fun _ => 2) (fun k => ((hδm k).comp hV).aestronglyMeasurable)
      (integrable_const _)
      (fun k => Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hδ0 _ _)]; exact hδ2 _ _)
      (Eventually.of_forall fun ω => tendsto_condDens' hW hψ (V ω) (hψ1 (V ω)))
    simpa using this
  -- choose the germ level `c`
  obtain ⟨k, hk1, hk2⟩ := ((hδlim.eventually (gt_mem_nhds (half_pos hη))).and
    (tendsto_epsSeq.eventually (eventually_le_nhds hu₀))).exists
  set c := epsSeq k with hc
  have hc0 : 0 < c := epsSeq_pos k
  set r : ℝ≥0 := min 1 (c / (S + 1)) with hr
  have hr0 : 0 < r := lt_min one_pos (div_pos hc0 (by positivity))
  have hgood : ∀ x : ℝ≥0, x < r → x ^ 2 * S < c := by
    intro x hx
    have hx1' : x < 1 := lt_of_lt_of_le hx (min_le_left _ _)
    have hxr' : x < c / (S + 1) := lt_of_lt_of_le hx (min_le_right _ _)
    have hx1 : (x : ℝ) < 1 := by exact_mod_cast hx1'
    have hxr : (x : ℝ) < (c : ℝ) / ((S : ℝ) + 1) := by exact_mod_cast hxr'
    have hS : (0 : ℝ) ≤ S := S.coe_nonneg
    have hx0 : (0 : ℝ) ≤ x := x.coe_nonneg
    rw [lt_div_iff₀ (by positivity)] at hxr
    rw [← NNReal.coe_lt_coe]
    push_cast
    nlinarith [mul_nonneg (mul_nonneg hx0 (sub_nonneg.2 hx1.le)) hS]
  -- choose `N`
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((hprob r hr0).eventually
    (gt_mem_nhds (ENNReal.ofReal_pos.2 (by linarith : (0 : ℝ) < η / 4))))
  refine ⟨N, fun n hn Γ hΓ hΓ1 => ?_⟩
  set G : Set 𝕍 := {v | a n v < r} with hG
  have hGm : MeasurableSet G := measurableSet_lt (ha n) measurable_const
  set ind : 𝕍 → ℝ := G.indicator 1 with hind_def
  have hindm : Measurable ind := measurable_one.indicator hGm
  have hind01 : ∀ v, 0 ≤ ind v ∧ ind v ≤ 1 := fun v => by
    by_cases hv : v ∈ G <;> simp [ind, hv]
  set Φ : 𝕍 × (ℝ≥0 → ℝ) → ℝ := fun p => Γ (p.1, rescaleLim S (a n p.1) p.2) with hΦ_def
  have hΦm : Measurable Φ := hΓ.comp (measurable_fst.prodMk ((measurable_rescaleLim S).comp
    (((ha n).comp measurable_fst).prodMk measurable_snd)))
  have hΦ1 : ∀ p, |Φ p| ≤ 1 := fun p => hΓ1 _
  have hD_eq : ∀ ω, Γ (V ω, LengthMarkov.GermDensity.rescale S (a n (V ω)) (D ω)) = Φ (V ω, D ω) := fun ω => by
    simp only [Φ, rescaleLim_of_continuous (hDc ω)]
  have hW_eq : ∀ v, ∫ b, Γ (v, pathRestr S b) ∂W = ∫ b, Φ (v, b) ∂W := by
    intro v
    rw [← integral_rescale hW' (hapos n v).ne' (G := fun x => Γ (v, x))
      (hΓ.comp (measurable_const.prodMk measurable_id))]
    refine integral_congr_ae (ae_eq_of_continuous hW' ?_ ?_ fun b hb => ?_)
    · exact hΓ.comp (measurable_const.prodMk
        (measurable_pi_iff.2 fun t => (measurable_pi_apply _).const_mul _))
    · exact hΦm.comp (measurable_const.prodMk measurable_id)
    · simp only [Φ, rescaleLim_of_continuous (b := b) hb]
  -- the two inner integrals
  set IΦ : 𝕍 → ℝ := fun v => ∫ b, Φ (v, b) ∂W with hIΦ_def
  set IΦψ : 𝕍 → ℝ := fun v => ∫ b, Φ (v, b) * ψ v b ∂W with hIΦψ_def
  have hIΦm : Measurable IΦ := hΦm.stronglyMeasurable.integral_prod_right'.measurable
  have hIΦψm : Measurable IΦψ := (hΦm.mul hψ).stronglyMeasurable.integral_prod_right'.measurable
  have hIΦ1 : ∀ v, |IΦ v| ≤ 1 := fun v => by
    have := norm_integral_le_of_norm_le_const (μ := W) (f := fun b => Φ (v, b)) (C := 1)
      (Eventually.of_forall fun b => by rw [Real.norm_eq_abs]; exact hΦ1 _)
    simpa using this
  have hIΦψ1 : ∀ v, |IΦψ v| ≤ 1 := fun v => by
    have := norm_integral_le_of_norm_le (hψi v) (f := fun b => Φ (v, b) * ψ v b)
      (Eventually.of_forall fun b => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hψ0 v b)]
        exact mul_le_of_le_one_left (hψ0 v b) (hΦ1 _))
    rw [hψ1] at this
    simpa using this
  -- pointwise estimate on the good set
  have hpt : ∀ v, |ind v * (IΦψ v - IΦ v)| ≤ δ k v := by
    intro v
    by_cases hv : v ∈ G
    · have hind1 : ind v = 1 := by simp [ind, hv]
      rw [hind1, one_mul]
      set g : (Set.Iic c → ℝ) → ℝ := fun x => Γ (v, rescaleLim S (a n v) (pathExt c x))
      have hgm : Measurable g := hΓ.comp (measurable_const.prodMk ((measurable_rescaleLim S).comp
        (measurable_const.prodMk (measurable_pathExt c))))
      have hgΦ : ∀ b, g (pathRestr c b) = Φ (v, b) := fun b => by
        simp only [g, Φ]
        rw [rescaleLim_congr (fun t ht => pathExt_pathRestr_of_le ht b) (hgood _ hv)]
      have key := integral_mul_eq_condDens hW' hψ v (hψi v) c hgm (C := 1) (fun x => hΓ1 _)
      simp only [hgΦ] at key
      have hci := integrable_condDens hW' hψ v (hψ1 v) c
      have hΦv : Measurable (fun b => Φ (v, b)) := hΦm.comp (measurable_const.prodMk measurable_id)
      have hΦi : Integrable (fun b => Φ (v, b)) W := integrable_of_abs_le hΦv (fun b => hΦ1 _)
      have hΦci : Integrable (fun b => Φ (v, b) * condDens W c ψ v (pathRestr c b)) W :=
        hci.bdd_mul hΦv.aestronglyMeasurable
          (Eventually.of_forall fun b => by rw [Real.norm_eq_abs]; exact hΦ1 _)
      have e : IΦψ v - IΦ v =
          ∫ b, Φ (v, b) * (condDens W c ψ v (pathRestr c b) - 1) ∂W := by
        simp only [IΦψ, IΦ]
        rw [key, ← integral_sub hΦci hΦi]
        exact integral_congr_ae (Eventually.of_forall fun b => by simp only; ring)
      rw [e]
      have := norm_integral_le_of_norm_le ((hci.sub (integrable_const _)).abs)
        (f := fun b => Φ (v, b) * (condDens W c ψ v (pathRestr c b) - 1))
        (Eventually.of_forall fun b => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_of_le_one_left (abs_nonneg _) (hΦ1 _))
      simpa [δ, hc] using this
    · have hind0 : ind v = 0 := by simp [ind, hv]
      rw [hind0, zero_mul, abs_zero]
      exact hδ0 k v
  -- integrability bookkeeping on `P`
  have hF1m : Measurable (fun ω => Φ (V ω, D ω)) := hΦm.comp (hV.prodMk hD)
  have hF1i : Integrable (fun ω => Φ (V ω, D ω)) P := integrable_of_abs_le hF1m fun ω => hΦ1 _
  have hF2i : Integrable (fun ω => IΦ (V ω)) P :=
    integrable_of_abs_le (hIΦm.comp hV) fun ω => hIΦ1 _
  have hindV : Measurable (fun ω => ind (V ω)) := hindm.comp hV
  have hgF1i : Integrable (fun ω => ind (V ω) * Φ (V ω, D ω)) P :=
    integrable_of_abs_le (hindV.mul hF1m) fun ω => by
      rw [abs_mul, abs_of_nonneg (hind01 _).1]
      exact mul_le_one₀ (hind01 _).2 (abs_nonneg _) (hΦ1 _)
  have hgF2i : Integrable (fun ω => ind (V ω) * IΦ (V ω)) P :=
    integrable_of_abs_le (hindV.mul (hIΦm.comp hV)) fun ω => by
      rw [abs_mul, abs_of_nonneg (hind01 _).1]
      exact mul_le_one₀ (hind01 _).2 (abs_nonneg _) (hIΦ1 _)
  have hgF3i : Integrable (fun ω => ind (V ω) * IΦψ (V ω)) P :=
    integrable_of_abs_le (hindV.mul (hIΦψm.comp hV)) fun ω => by
      rw [abs_mul, abs_of_nonneg (hind01 _).1]
      exact mul_le_one₀ (hind01 _).2 (abs_nonneg _) (hIΦψ1 _)
  -- the good part via `hlaw`
  have hgood_eq : ∫ ω, ind (V ω) * Φ (V ω, D ω) ∂P = ∫ ω, ind (V ω) * IΦψ (V ω) ∂P := by
    set Φ' : 𝕍 × (Set.Iic u₀ → ℝ) → ℝ :=
      fun p => ind p.1 * Γ (p.1, rescaleLim S (a n p.1) (pathExt u₀ p.2)) with hΦ'_def
    have hΦ'm : Measurable Φ' := (hindm.comp measurable_fst).mul (hΓ.comp (measurable_fst.prodMk
      ((measurable_rescaleLim S).comp (((ha n).comp measurable_fst).prodMk
        ((measurable_pathExt u₀).comp measurable_snd)))))
    have hΦ'b : ∀ p, |Φ' p| ≤ 1 := fun p => by
      simp only [Φ']
      rw [abs_mul, abs_of_nonneg (hind01 _).1]
      exact mul_le_one₀ (hind01 _).2 (abs_nonneg _) (hΓ1 _)
    have hΦ'eq : ∀ v b, Φ' (v, pathRestr u₀ b) = ind v * Φ (v, b) := by
      intro v b
      simp only [Φ', Φ]
      by_cases hv : v ∈ G
      · rw [rescaleLim_congr (fun t ht => pathExt_pathRestr_of_le ht b)
          (lt_of_lt_of_le (hgood _ hv) hk2)]
      · simp [ind, hv]
    have h := hlaw Φ' hΦ'm ⟨1, hΦ'b⟩
    simp only [hΦ'eq] at h
    rw [h]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [IΦψ]
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun b => by simp only; ring)
  -- assemble
  have e1 : ∫ ω, Γ (V ω, LengthMarkov.GermDensity.rescale S (a n (V ω)) (D ω)) ∂P = ∫ ω, Φ (V ω, D ω) ∂P :=
    integral_congr_ae (Eventually.of_forall hD_eq)
  have e2 : ∫ ω, ∫ b, Γ (V ω, pathRestr S b) ∂W ∂P = ∫ ω, IΦ (V ω) ∂P :=
    integral_congr_ae (Eventually.of_forall fun ω => hW_eq (V ω))
  rw [e1, e2, ← integral_sub hF1i hF2i]
  set Y : Ω → ℝ := fun ω => Φ (V ω, D ω) - IΦ (V ω) with hY_def
  have hYm : Measurable Y := hF1m.sub (hIΦm.comp hV)
  have hY2 : ∀ ω, |Y ω| ≤ 2 := fun ω => by
    simp only [Y]
    calc |Φ (V ω, D ω) - IΦ (V ω)| ≤ |Φ (V ω, D ω)| + |IΦ (V ω)| := abs_sub _ _
      _ ≤ 2 := by linarith [hΦ1 (V ω, D ω), hIΦ1 (V ω)]
  have hi1 : Integrable (fun ω => ind (V ω) * Y ω) P :=
    integrable_of_abs_le (hindV.mul hYm) fun ω => by
      rw [abs_mul, abs_of_nonneg (hind01 _).1]
      exact (mul_le_of_le_one_left (abs_nonneg _) (hind01 _).2).trans (hY2 ω)
  have hi2 : Integrable (fun ω => (1 - ind (V ω)) * Y ω) P :=
    integrable_of_abs_le ((measurable_const.sub hindV).mul hYm) fun ω => by
      rw [abs_mul, abs_of_nonneg (by linarith [(hind01 (V ω)).2])]
      exact (mul_le_of_le_one_left (abs_nonneg _) (by linarith [(hind01 (V ω)).1])).trans
        (hY2 ω)
  have hsplit : ∫ ω, Y ω ∂P =
      ∫ ω, ind (V ω) * Y ω ∂P + ∫ ω, (1 - ind (V ω)) * Y ω ∂P := by
    rw [← integral_add hi1 hi2]
    exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
  -- good part bound
  have hgoodb : |∫ ω, ind (V ω) * Y ω ∂P| ≤ η / 2 := by
    have e : ∫ ω, ind (V ω) * Y ω ∂P = ∫ ω, ind (V ω) * (IΦψ (V ω) - IΦ (V ω)) ∂P := by
      have : ∫ ω, ind (V ω) * Y ω ∂P =
          ∫ ω, ind (V ω) * Φ (V ω, D ω) ∂P - ∫ ω, ind (V ω) * IΦ (V ω) ∂P := by
        rw [← integral_sub hgF1i hgF2i]
        exact integral_congr_ae (Eventually.of_forall fun ω => by simp only [Y]; ring)
      rw [this, hgood_eq, ← integral_sub hgF3i hgF2i]
      exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
    rw [e]
    have hδi : Integrable (fun ω => δ k (V ω)) P :=
      integrable_of_abs_le ((hδm k).comp hV) fun ω => by
        rw [abs_of_nonneg (hδ0 _ _)]; exact hδ2 _ _
    have := norm_integral_le_of_norm_le hδi
      (f := fun ω => ind (V ω) * (IΦψ (V ω) - IΦ (V ω)))
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hpt _)
    rw [Real.norm_eq_abs] at this
    linarith
  -- bad part bound
  have hbadb : |∫ ω, (1 - ind (V ω)) * Y ω ∂P| ≤ η / 2 := by
    have hbad_set : MeasurableSet (V ⁻¹' Gᶜ) := hV hGm.compl
    have hbnd : ∀ ω, ‖(1 - ind (V ω)) * Y ω‖ ≤ 2 * (V ⁻¹' Gᶜ).indicator 1 ω := fun ω => by
      rw [Real.norm_eq_abs]
      by_cases hv : V ω ∈ G
      · have : ω ∉ V ⁻¹' Gᶜ := fun h => h hv
        simp [ind, hv]
      · have : ω ∈ V ⁻¹' Gᶜ := hv
        simp only [ind, Set.indicator_of_notMem hv, Set.indicator_of_mem this, sub_zero,
          one_mul, Pi.one_apply, mul_one]
        exact hY2 ω
    have h1 := norm_integral_le_of_norm_le
      ((integrable_const (μ := P) (1 : ℝ)).indicator hbad_set |>.const_mul 2) (Eventually.of_forall hbnd)
    rw [Real.norm_eq_abs, integral_const_mul, integral_indicator hbad_set, setIntegral_const,
      smul_eq_mul, mul_one] at h1
    have hPr : P.real (V ⁻¹' Gᶜ) ≤ η / 4 := by
      have hset : V ⁻¹' Gᶜ = {ω | r ≤ a n (V ω)} := by
        ext ω; simp [G]
      rw [measureReal_def, hset]
      exact ENNReal.toReal_le_of_le_ofReal (by linarith) (hN n hn).le
    linarith
  rw [hsplit]
  calc |∫ ω, ind (V ω) * Y ω ∂P + ∫ ω, (1 - ind (V ω)) * Y ω ∂P|
      ≤ |∫ ω, ind (V ω) * Y ω ∂P| + |∫ ω, (1 - ind (V ω)) * Y ω ∂P| := abs_add_le _ _
    _ ≤ η / 2 + η / 2 := add_le_add hgoodb hbadb
    _ = η := by ring

end CoreRepair

end E5
end QuantumZipper
