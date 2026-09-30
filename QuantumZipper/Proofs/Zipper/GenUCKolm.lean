import QuantumZipper.Proofs.Probability.KolmN
import QuantumZipper.Proofs.Zipper.RegContMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# GENERIC-UC (1/2): the Kolmogorov step for a finite-parameter family of pushed measures

The engine abstracted from the free-field flow chain (`F1.exists_contMod_flow`, XFlowUCFixMain;
`RegUnif.exists_contMod_US`, UnifUCFixBasic; the SW family core SWCoreN2*): for a free field
`X` (`IsFreeGFFModConstH`) and a family of admissible measures `μ p ρ` of fixed mass, indexed by
`p` in a parameter set `S ⊆ ℝⁿ` carrying a Lipschitz retraction and by a smoothing radius
`ρ ∈ [0,1]`, a Hölder bound on the Neumann energy of `μ p ρ − μ p' ρ'` gives a modification
of `(p, ρ) ↦ X(μ p ρ)` that is continuous for every sample. The dependence on the parameters is
only assumed **Hölder** (any exponent `c > 0`, e.g. the `1/2` or `1/3` time regularity of flow
maps driven by Brownian motion): the Kolmogorov step takes moments of order `2N`,
`N = ⌈(n+1)/c⌉ + 1`. The Lipschitz retraction concerns only the geometry of `S` (e.g. the
`1`-Lipschitz clamp onto a box, `GenUC.isLipRetr_ratBox`), not the maps.

Sources: the Gaussian moment bound `RegCont.lintegral_pow_diff_le` and the `d`-parameter
Kolmogorov–Čentsov theorem `KolmN.exists_continuous_modification_N` (Revuz–Yor, *Continuous
martingales and Brownian motion*, 3rd ed., Ch. I, Thm (2.1)). The encoding of
`S × [0,1]` into `ℝⁿ⁺¹` (retraction on the first `n` coordinates, clamp on the last) is own
bookkeeping, as in D33 / XFLOW-UC.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace GenUC

open RegCont

/-! ### Encoding `ℝⁿ × ℝ ≃ ℝⁿ⁺¹` -/

/-- Clamp to `[0,1]`. -/
def clamp01 (x : ℝ) : ℝ := max 0 (min x 1)

theorem clamp01_mem (x : ℝ) : clamp01 x ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

theorem clamp01_of_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : clamp01 x = x := by
  unfold clamp01; rw [min_eq_left hx.2, max_eq_right hx.1]

theorem abs_clamp01_sub_le (x y : ℝ) : |clamp01 x - clamp01 y| ≤ |x - y| := by
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
  · rw [sub_self, abs_zero]; exact abs_nonneg _
  · exact abs_min_sub_min_le_max _ _ _ _ |>.trans (max_le le_rfl (by simp))

/-- The point `(p, ρ)` as a vector of `ℝⁿ⁺¹`. -/
def embG {n : ℕ} (p : Fin n → ℝ) (ρ : ℝ) : Fin (n + 1) → ℝ :=
  fun i => if h : (i : ℕ) < n then p ⟨i, h⟩ else ρ

/-- The first `n` coordinates. -/
def initG {n : ℕ} (q : Fin (n + 1) → ℝ) : Fin n → ℝ := fun i => q (Fin.castSucc i)

/-- The last coordinate. -/
def lastG {n : ℕ} (q : Fin (n + 1) → ℝ) : ℝ := q (Fin.last n)

theorem initG_embG {n : ℕ} (p : Fin n → ℝ) (ρ : ℝ) : initG (embG p ρ) = p := by
  funext i
  simp [initG, embG]

theorem lastG_embG {n : ℕ} (p : Fin n → ℝ) (ρ : ℝ) : lastG (embG p ρ) = ρ := by
  simp [lastG, embG]

theorem continuous_embG {n : ℕ} :
    Continuous fun z : (Fin n → ℝ) × ℝ => embG z.1 z.2 := by
  refine continuous_pi fun i => ?_
  by_cases h : (i : ℕ) < n
  · simp only [embG, h, dite_true]
    exact (continuous_apply _).comp continuous_fst
  · simp only [embG, h, dite_false]
    exact continuous_snd

theorem norm_initG_sub_le {n : ℕ} (q q' : Fin (n + 1) → ℝ) :
    ‖initG q - initG q'‖ ≤ ‖q - q'‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  have := norm_le_pi_norm (q - q') (Fin.castSucc i)
  simpa [initG] using this

theorem abs_lastG_sub_le {n : ℕ} (q q' : Fin (n + 1) → ℝ) :
    |lastG q - lastG q'| ≤ ‖q - q'‖ := by
  have := norm_le_pi_norm (q - q') (Fin.last n)
  simpa [lastG, Real.norm_eq_abs] using this

/-! ### The hypotheses on the family -/

/-- **The analytic hypotheses on a family of pushed measures.** `μ p ρ` (`p ∈ S`,
`ρ ∈ [0,1]`) are admissible, of the same mass `M`, and the Neumann energy of `μ p ρ − μ p' ρ'`
is `≤ K (dist p p' + |ρ − ρ'|)^c`. -/
structure GenFam {n : ℕ} (S : Set (Fin n → ℝ)) (μ : (Fin n → ℝ) → ℝ → Measure ℂ)
    (M : ℝ≥0∞) (K c : ℝ) : Prop where
  adm : ∀ p ∈ S, ∀ ρ ∈ Icc (0 : ℝ) 1, IsAdmissibleH (μ p ρ)
  mass : ∀ p ∈ S, ∀ ρ ∈ Icc (0 : ℝ) 1, μ p ρ univ = M
  K_nonneg : 0 ≤ K
  c_pos : 0 < c
  energy : ∀ p ∈ S, ∀ p' ∈ S, ∀ ρ ∈ Icc (0 : ℝ) 1, ∀ ρ' ∈ Icc (0 : ℝ) 1,
    |kernelCov2 neumannH (μ p ρ, μ p' ρ') (μ p ρ, μ p' ρ')| ≤ K * (dist p p' + |ρ - ρ'|) ^ c

/-- **A Lipschitz retraction of `ℝⁿ` onto `S`.** -/
structure IsLipRetr {n : ℕ} (S : Set (Fin n → ℝ)) (ret : (Fin n → ℝ) → Fin n → ℝ) (L : ℝ) :
    Prop where
  mem : ∀ q, ret q ∈ S
  fix : ∀ p ∈ S, ret p = p
  L_nonneg : 0 ≤ L
  lip : ∀ q q', dist (ret q) (ret q') ≤ L * dist q q'

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- **GENERIC-UC, Kolmogorov step.** A modification of `(p, ρ) ↦ X(μ p ρ)` on `S × [0,1]`,
jointly continuous in `(p, ρ) ∈ ℝⁿ × ℝ` for every sample. -/
theorem exists_contMod_gen (hX : IsFreeGFFModConstH X P) {n : ℕ} {S : Set (Fin n → ℝ)}
    {μ : (Fin n → ℝ) → ℝ → Measure ℂ} {M : ℝ≥0∞} {K c : ℝ} (hF : GenFam S μ M K c)
    {ret : (Fin n → ℝ) → Fin n → ℝ} {L : ℝ} (hR : IsLipRetr S ret L) :
    ∃ Y : (Fin n → ℝ) → ℝ → Ω → ℝ,
      (∀ ω, Continuous fun z : (Fin n → ℝ) × ℝ => Y z.1 z.2 ω) ∧
      ∀ p ∈ S, ∀ ρ ∈ Icc (0 : ℝ) 1, (fun ω => Y p ρ ω) =ᵐ[P] fun ω => X ω (μ p ρ) := by
  set pt : (Fin (n + 1) → ℝ) → Fin n → ℝ := fun q => ret (initG q) with hpt
  set rh : (Fin (n + 1) → ℝ) → ℝ := fun q => clamp01 (lastG q) with hrh
  have hc := hF.c_pos
  have hK := hF.K_nonneg
  have hL := hR.L_nonneg
  have hEq : ∀ q q' : Fin (n + 1) → ℝ,
      |kernelCov2 neumannH (μ (pt q) (rh q), μ (pt q') (rh q'))
        (μ (pt q) (rh q), μ (pt q') (rh q'))| ≤ (K * (L + 1) ^ c) * ‖q - q'‖ ^ c := by
    intro q q'
    refine (hF.energy _ (hR.mem _) _ (hR.mem _) _ (clamp01_mem _) _ (clamp01_mem _)).trans ?_
    have h0 : dist (pt q) (pt q') ≤ L * ‖q - q'‖ := by
      refine (hR.lip _ _).trans (mul_le_mul_of_nonneg_left ?_ hL)
      rw [dist_eq_norm]; exact norm_initG_sub_le q q'
    have h1 : dist (pt q) (pt q') + |rh q - rh q'| ≤ (L + 1) * ‖q - q'‖ := by
      have := (abs_clamp01_sub_le (lastG q) (lastG q')).trans (abs_lastG_sub_le q q')
      simp only [hrh] at this ⊢
      nlinarith
    have h2 := Real.rpow_le_rpow (add_nonneg dist_nonneg (abs_nonneg _)) h1 hc.le
    calc K * (dist (pt q) (pt q') + |rh q - rh q'|) ^ c
        ≤ K * ((L + 1) * ‖q - q'‖) ^ c := mul_le_mul_of_nonneg_left h2 hK
      _ = (K * (L + 1) ^ c) * ‖q - q'‖ ^ c := by
        rw [Real.mul_rpow (by linarith) (norm_nonneg _)]; ring
  set N : ℕ := ⌈((n + 1 : ℕ) : ℝ) / c⌉₊ + 1 with hN
  have hmc : ((n + 1 : ℕ) : ℝ) < (N : ℝ) * c := by
    have h1 : ((n + 1 : ℕ) : ℝ) / c ≤ (⌈((n + 1 : ℕ) : ℝ) / c⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (((n + 1 : ℕ) : ℝ) / c) * c = ((n + 1 : ℕ) : ℝ) := div_mul_cancel₀ _ hc.ne'
    rw [hN]; push_cast at h1 h2 ⊢
    nlinarith
  set g := gaussianAbsMoment (2 * N) with hg
  have hg0 : 0 ≤ g := gaussianAbsMoment_nonneg _
  have hK3 : 0 ≤ K * (L + 1) ^ c := mul_nonneg hK (Real.rpow_nonneg (by linarith) _)
  obtain ⟨Y, hY, hYZ, -⟩ := KolmN.exists_continuous_modification_N (d := n + 1)
    (Z := fun q ω => X ω (μ (pt q) (rh q))) (P := P)
    (fun q => (hX.measurable_coord _).aemeasurable) (p := 2 * N) (by omega) hmc
    (fun R => ⟨(K * (L + 1) ^ c) ^ N * g, by positivity, fun q _ q' _ => by
      have hA1 := hF.adm _ (hR.mem (initG q)) _ (clamp01_mem (lastG q))
      have hB1 := hF.adm _ (hR.mem (initG q')) _ (clamp01_mem (lastG q'))
      have hmA := hF.mass _ (hR.mem (initG q)) _ (clamp01_mem (lastG q))
      have hmB := hF.mass _ (hR.mem (initG q')) _ (clamp01_mem (lastG q'))
      refine (lintegral_pow_diff_le hX hA1 hB1 (hmA.trans hmB.symm) N (hEq q q')).trans ?_
      refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
      rw [mul_pow, ← Real.rpow_natCast (‖q - q'‖ ^ c), ← Real.rpow_mul (norm_nonneg _), hg,
        mul_comm c]
      ring⟩)
  refine ⟨fun p ρ ω => Y (embG p ρ) ω, fun ω => (hY ω).comp continuous_embG, ?_⟩
  intro p hp ρ hρ
  have h := hYZ (embG p ρ)
  simp only [hpt, hrh, initG_embG, lastG_embG, hR.fix p hp, clamp01_of_mem hρ] at h
  exact h

end GenUC
end QuantumZipper
