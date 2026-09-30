import QuantumZipper.Proofs.Zipper.SWCoreN2Apply

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-N2 (6): the raw distortion values are uniformly small on a countable parameter set

For a finite-parameter family of maps of one boundary class (Lipschitz in the parameter) and a
countable set `D ⊂ K × [a,b]`, almost surely, for every `η > 0`, eventually in `k`, for all
`(q,t) ∈ D`: `|X(fc(t,r_k).map (Ψ q)) − X(fc(Ψ_q(t), r_k ‖Ψ_q'(t)‖))| ≤ η`
(`swcn2_family_raw`). Sheffield–Wang, arXiv:1605.06171, Lemma 3.4 (3.20) and Lemma 3.5 with the
Borel–Cantelli step (p. 16). The Gaussian family is the free field on the admissible pairs
(`IsFreeGFFModConstH.gaussian`), with variance/modulus from `swcn2_family_energy`, and
`swcn2_ae_eventually_small` concludes. Own assembly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal Real

namespace QuantumZipper
namespace SWCore

open RegUnif TwoPoint

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

theorem swcn2_norm_init_le {n : ℕ} (θ : Fin (n + 1) → ℝ) : ‖Fin.init θ‖ ≤ ‖θ‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg θ)).2 fun i => norm_le_pi_norm θ _

theorem swcn2_abs_last_le {n : ℕ} (θ : Fin (n + 1) → ℝ) : |θ (Fin.last n)| ≤ ‖θ‖ := by
  have := norm_le_pi_norm θ (Fin.last n); rwa [Real.norm_eq_abs] at this

set_option maxHeartbeats 2000000 in
/-- **Raw distortion values, uniformly on a countable parameter set.** -/
theorem swcn2_family_raw (hX : IsFreeGFFModConstH X P) {n : ℕ} (Ψ : (Fin n → ℝ) → ℂ → ℂ)
    (K : Set (Fin n → ℝ)) {a b ρ M m L R : ℝ} (hab : a < b) (hρ : 0 < ρ) (hm : 0 < m)
    (hL : 0 ≤ L) (hcl : ∀ q ∈ K, Ψ q ∈ BdryClass a b ρ M m)
    (hlip : ∀ q ∈ K, ∀ q' ∈ K, ∀ z ∈ thickening ρ (segC a b),
      ‖Ψ q z - Ψ q' z‖ ≤ L * ‖q - q'‖) (hR : 0 ≤ R) (hKR : ∀ q ∈ K, ‖q‖ ≤ R)
    {D : Set ((Fin n → ℝ) × ℝ)} (hD : D.Countable) (hDK : D ⊆ K ×ˢ Icc a b) :
    ∀ᵐ ω ∂P, ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ x ∈ D,
      |X ω ((foldedCircle (x.2 : ℂ) (radius k)).map (Ψ x.1)) -
        X ω (foldedCircle (((Ψ x.1 x.2).re : ℝ) : ℂ) (radius k * ‖deriv (Ψ x.1) x.2‖))| ≤ η := by
  classical
  obtain ⟨r₀, hr₀, CV, CE, hCV, hCE, hE⟩ := swcn2_family_energy Ψ K hab hρ hm hL hcl hlip
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, (2⁻¹ : ℝ) ^ k₀ < r₀ := exists_pow_lt_of_lt_one hr₀ (by norm_num)
  have hrk : ∀ k, k₀ ≤ k → radius k ∈ Ioo 0 r₀ := fun k hk =>
    ⟨swcn2_radius_pos k, lt_of_le_of_lt (swcn2_radius_anti hk) hk₀⟩
  set bk : (Fin (n + 1) → ℝ) → (Fin n → ℝ) × ℝ := fun θ => (Fin.init θ, θ (Fin.last n))
    with hbk
  set e : (Fin n → ℝ) × ℝ → Fin (n + 1) → ℝ := fun x => Fin.snoc x.1 x.2 with he
  have hbke : ∀ x, bk (e x) = x := fun x => by
    simp only [hbk, he, Fin.init_snoc, Fin.snoc_last]
  set μ₀ : Measure ℂ := foldedCircle 0 1 with hμ₀
  have hadm0 : IsAdmissibleH μ₀ := D3Plus.isAdmissibleH_foldedCircle' 0 one_pos
  set νf : ℕ → (Fin n → ℝ) × ℝ → Measure ℂ := fun k x =>
    (foldedCircle (x.2 : ℂ) (radius k)).map (Ψ x.1) with hνf
  set σf : ℕ → (Fin n → ℝ) × ℝ → Measure ℂ := fun k x =>
    foldedCircle (((Ψ x.1 x.2).re : ℝ) : ℂ) (radius k * ‖deriv (Ψ x.1) x.2‖) with hσf
  have hgood : ∀ k x, k₀ ≤ k → x ∈ K ×ˢ Icc a b →
      IsAdmissibleH (νf k x) ∧ IsAdmissibleH (σf k x) ∧ νf k x univ = σf k x univ := by
    intro k x hk hx
    obtain ⟨⟨hA, hmass, hpos, -⟩, -⟩ := hE (radius k) (hrk k hk) x.1 hx.1 x.2 hx.2
    exact ⟨hA, D3Plus.isAdmissibleH_foldedCircle' _ hpos, by rw [hmass, measure_univ]⟩
  set pairOf : ℕ → (Fin (n + 1) → ℝ) → WedgeTK.BPair := fun k θ =>
    if h : k₀ ≤ k ∧ bk θ ∈ K ×ˢ Icc a b then
      ⟨(νf k (bk θ), σf k (bk θ)), hgood k (bk θ) h.1 h.2⟩
    else ⟨(μ₀, μ₀), hadm0, hadm0, rfl⟩ with hpair
  set Z : ℕ → (Fin (n + 1) → ℝ) → Ω → ℝ := fun k θ ω =>
    X ω (pairOf k θ).1.1 - X ω (pairOf k θ).1.2 with hZ
  have hmass1 : ∀ k θ, (pairOf k θ).1.1 univ = 1 := by
    intro k θ
    simp only [hpair]
    split_ifs with h
    · obtain ⟨⟨-, hmass, -, -⟩, -⟩ := hE (radius k) (hrk k h.1) (bk θ).1 h.2.1 (bk θ).2 h.2.2
      exact hmass
    · exact measure_univ
  have hG : ∀ k, IsGaussianProcess (Z k) P := fun k => hX.gaussian.comp_right (pairOf k)
  have hc : ∀ k θ, ∫ ω, Z k θ ω ∂P = 0 := fun k θ =>
    hX.centered _ _ (pairOf k θ).2.1 (pairOf k θ).2.2.1 (pairOf k θ).2.2.2
  have hZm : ∀ k θ, Measurable (Z k θ) := fun k θ =>
    (hX.measurable_coord _).sub (hX.measurable_coord _)
  set D' : Set (Fin (n + 1) → ℝ) := e '' D with hD'
  have hD'c : D'.Countable := hD.image e
  set R' : ℝ := max R (max |a| |b|) with hR'
  have hD'R : ∀ θ ∈ D', ‖θ‖ ≤ R' := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' := hDK hx
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [he, Fin.snoc_last, Real.norm_eq_abs]
      refine le_trans ?_ (le_max_right _ _)
      rw [abs_le]
      constructor
      · have := neg_abs_le a; have := le_max_left |a| |b|; linarith [hx'.2.1]
      · have := le_abs_self b; have := le_max_right |a| |b|; linarith [hx'.2.2]
    · simp only [he, Fin.snoc_castSucc]
      exact (norm_le_pi_norm x.1 j).trans ((hKR x.1 hx'.1).trans (le_max_left _ _))
  have hD'good : ∀ θ ∈ D', bk θ ∈ K ×ˢ Icc a b := by
    rintro _ ⟨x, hx, rfl⟩; rw [hbke]; exact hDK hx
  -- variance of `Z k θ`
  have hvarZ : ∀ k θ, Var[Z k θ; P] =
      kernelCov2 neumannH (pairOf k θ).1 (pairOf k θ).1 := fun k θ =>
    swcn2_var_pair hX (pairOf k θ).2.1 (pairOf k θ).2.2.1 (pairOf k θ).2.2.2
  have hzero : kernelCov2 neumannH (μ₀, μ₀) (μ₀, μ₀) = 0 := by unfold kernelCov2; ring
  have hvar : ∀ k, ∀ θ ∈ D', Var[Z k θ; P] ≤ CV * radius k ^ ((1 / 3 : ℝ) / 2) := by
    intro k θ hθ
    rw [hvarZ]
    by_cases hk : k₀ ≤ k
    · have h : k₀ ≤ k ∧ bk θ ∈ K ×ˢ Icc a b := ⟨hk, hD'good θ hθ⟩
      have hp : pairOf k θ = ⟨(νf k (bk θ), σf k (bk θ)), hgood k (bk θ) h.1 h.2⟩ := by
        simp only [hpair, dif_pos h]
      rw [hp]
      obtain ⟨⟨-, -, -, hV⟩, -⟩ := hE (radius k) (hrk k hk) (bk θ).1 (hD'good θ hθ).1
        (bk θ).2 (hD'good θ hθ).2
      exact (le_abs_self _).trans hV
    · have hp : pairOf k θ = ⟨(μ₀, μ₀), hadm0, hadm0, rfl⟩ := by
        simp only [hpair, dif_neg (fun (h : k₀ ≤ k ∧ bk θ ∈ K ×ˢ Icc a b) => hk h.1)]
      rw [hp]; simp only [hzero]
      exact mul_nonneg hCV (Real.rpow_nonneg (swcn2_radius_pos k).le _)
  -- modulus
  have hmod : ∀ k, ∀ θ ∈ D', ∀ θ' ∈ D', ‖θ - θ'‖ ≤ radius k ^ 2 →
      Var[fun ω => Z k θ ω - Z k θ' ω; P] ≤
        Real.sqrt (4 * CE) ^ 2 * (‖θ - θ'‖ / radius k) ^ ((1 / 3 : ℝ) / 2) := by
    intro k θ hθ θ' hθ' hθθ
    rw [Real.sq_sqrt (by positivity)]
    have p1 := (pairOf k θ).2
    have p2 := (pairOf k θ').2
    have hA : MemLp (fun ω => X ω (pairOf k θ).1.1 - X ω (pairOf k θ').1.1) 2 P :=
      SmoothConv.memLp_pair_sc hX p1.1 p2.1 (by rw [hmass1, hmass1])
    have hB : MemLp (fun ω => X ω (pairOf k θ).1.2 - X ω (pairOf k θ').1.2) 2 P :=
      SmoothConv.memLp_pair_sc hX p1.2.1 p2.2.1 (by rw [← p1.2.2, ← p2.2.2, hmass1, hmass1])
    have hsplit : (fun ω => Z k θ ω - Z k θ' ω) = fun ω =>
        (X ω (pairOf k θ).1.1 - X ω (pairOf k θ').1.1) -
          (X ω (pairOf k θ).1.2 - X ω (pairOf k θ').1.2) := by
      funext ω; simp only [hZ]; ring
    rw [hsplit]
    refine (swcn2_var_sub_le hA hB).trans ?_
    rw [swcn2_var_pair hX p1.1 p2.1 (by rw [hmass1, hmass1]),
      swcn2_var_pair hX p1.2.1 p2.2.1 (by rw [← p1.2.2, ← p2.2.2, hmass1, hmass1])]
    have hβnn : 0 ≤ (‖θ - θ'‖ / radius k) ^ ((1 / 3 : ℝ) / 2) :=
      Real.rpow_nonneg (div_nonneg (norm_nonneg _) (swcn2_radius_pos k).le) _
    by_cases hk : k₀ ≤ k
    · have h1 : k₀ ≤ k ∧ bk θ ∈ K ×ˢ Icc a b := ⟨hk, hD'good θ hθ⟩
      have h2 : k₀ ≤ k ∧ bk θ' ∈ K ×ˢ Icc a b := ⟨hk, hD'good θ' hθ'⟩
      have hp1 : pairOf k θ = ⟨(νf k (bk θ), σf k (bk θ)), hgood k (bk θ) h1.1 h1.2⟩ := by
        simp only [hpair, dif_pos h1]
      have hp2 : pairOf k θ' = ⟨(νf k (bk θ'), σf k (bk θ')), hgood k (bk θ') h2.1 h2.2⟩ := by
        simp only [hpair, dif_pos h2]
      rw [hp1, hp2]
      obtain ⟨-, hmodE⟩ := hE (radius k) (hrk k hk) (bk θ).1 (hD'good θ hθ).1
        (bk θ).2 (hD'good θ hθ).2
      have hq : ‖(bk θ).1 - (bk θ').1‖ ≤ ‖θ - θ'‖ := swcn2_norm_init_le (θ - θ')
      have ht : |(bk θ).2 - (bk θ').2| ≤ ‖θ - θ'‖ := swcn2_abs_last_le (θ - θ')
      obtain ⟨hν, hσ⟩ := hmodE (bk θ').1 (hD'good θ' hθ').1 (bk θ').2 (hD'good θ' hθ').2
        ‖θ - θ'‖ hq ht hθθ
      simp only [hνf, hσf]
      have a1 := (le_abs_self _).trans hν
      have a2 := (le_abs_self _).trans hσ
      linarith
    · have hp1 : pairOf k θ = ⟨(μ₀, μ₀), hadm0, hadm0, rfl⟩ := by
        simp only [hpair, dif_neg (fun (h : k₀ ≤ k ∧ bk θ ∈ K ×ˢ Icc a b) => hk h.1)]
      have hp2 : pairOf k θ' = ⟨(μ₀, μ₀), hadm0, hadm0, rfl⟩ := by
        simp only [hpair, dif_neg (fun (h : k₀ ≤ k ∧ bk θ' ∈ K ×ˢ Icc a b) => hk h.1)]
      rw [hp1, hp2]; simp only [hzero]
      have := mul_nonneg hCE hβnn
      linarith
  have hmain := swcn2_ae_eventually_small Z (D := fun _ => D') (fun _ => hD'c)
    (le_trans hR (le_max_left _ _)) (fun _ => hD'R) hG hc hZm (V := CV) (β₀ := (1 / 3 : ℝ) / 2)
    (L := Real.sqrt (4 * CE)) (β := (1 / 3 : ℝ) / 2) (by norm_num) (by norm_num) (by norm_num)
    (Real.sqrt_nonneg _) hCV hvar hmod
  filter_upwards [hmain] with ω hω η hη
  filter_upwards [hω η hη, eventually_ge_atTop k₀] with k hk hk₀' x hx
  have hθ : e x ∈ D' := ⟨x, hx, rfl⟩
  have h := hk (e x) hθ
  have hgx : k₀ ≤ k ∧ bk (e x) ∈ K ×ˢ Icc a b := ⟨hk₀', by rw [hbke]; exact hDK hx⟩
  have hp : pairOf k (e x) = ⟨(νf k (bk (e x)), σf k (bk (e x))),
      hgood k (bk (e x)) hgx.1 hgx.2⟩ := by simp only [hpair, dif_pos hgx]
  simp only [hZ, hp, hbke, hνf, hσf] at h
  exact h

end SWCore
end QuantumZipper
