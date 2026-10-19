import HigherDimLFPP.Field.Bands
import HigherDimLFPP.Field.WhiteNoise
import LQGDimension.Gaussian.MaxInequality
import GaussianLQG.Probability.Gaussian

/-!
# Lemma 3.4(d): expected maxima of prefix pairings, the fixed-prefix form of (3.15) (packet P-F3b)

Source: `source/higher-dimensional-lfpp-limit.pdf`, §3.3, Lemma 3.4(d), (3.15)–(3.16); planning
audit HA2 (`planning/audits/HA2-section-3.md`), finding HA2-14 and Details D8(d) (HA2's
`Lemma34dFixed`); HA4 (`planning/audits/HA4-section-5.md`), finding HA4-5, Details D4 (K5) and D6
(Step 2): Lemma 5.3 consumes, for each **fixed** `x`, only
`E max_j |⟨H_{a,b}, ν_j|_{z₁ ≤ x}⟩| ≤ √(C b) √(2 log 2J)` — "uniformly in `x`" is outside the
expectation, so the printed (3.15), with the supremum over prefixes inside the expectation, is not
needed and is not formalized here.

* `Bands.signK`, `Bands.sgn`: the sign kernel of HA2 (`E sup |X| = E sup_{(t, s)} s X_t`).
* `Bands.gEM_signK_le`: for a kernel `C` that is positive semidefinite on a finite set `F` with
  diagonal `≤ σ²`, the lattice expected maximum of the sign-doubled family is
  `≤ σ √(2 log (2 |F|))` (LQGDimension's finite maximal inequality
  `GaussianMax.integral_iSup_inner_le_sqrt` on Gram vectors).
* `bandLemma34d_max`: for positive measures `η_i ≤ ν_i` of mass `≤ 1`, `ν_i` coupled within `a`
  with measures `ν'_i` having the growth bound (3.4) at scale `1`,
  `E max_{i ∈ F} |⟨H_{a,b}, η_i⟩| ≤ √(C b) √(2 log (2 |F|))` in the lattice convention; the
  constant depends only on `d, κ, B` (from (3.16), `bandLemma34d_var`).
* `bandLemma34dFixed`: the fixed-prefix form, HA2's `Lemma34dFixed` with `b ≤ 1` dropped
  (HA2-14), for `η_j = ν_j|_{z₁ ≤ x}` (`Bands.prefixM`), uniformly in `x`.
* `bandLemma34d_max_wn`, `bandLemma34dFixed_wn`: the same bounds for the pairings
  `W(bandVecM κ (a, b) η_j 0)` of an actual white noise `W` (`IsWhiteNoise`), by
  `GaussianLQG.integral_iSup_abs_le`.
* `bandLemma34d`: (3.16) and both fixed-prefix bounds with **one** constant `C(d, κ, B)`.
* `Bands.integral_iSup_abs_eq_gEM`: for a white noise, `E max_{i ∈ F} |W(v_i)|` equals the
  lattice expected maximum of the sign-doubled Gram family (converts every lattice bound into a
  bound for an actual white noise).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal

namespace HigherDimLFPP

namespace Bands

/-- The sign kernel `signK s s' = ±1` (HA2's `signK`): the covariance of `(s X_t)_{(t, s)}` is
`signK s s' · Cov(X_t, X_{t'})`, and `E max_{(t, s)} s X_t = E max_t |X_t|`. -/
def signK (s s' : Bool) : ℝ := if s = s' then 1 else -1

/-- The sign `±1` of a Boolean. -/
def sgn (s : Bool) : ℝ := if s then 1 else -1

theorem signK_eq_mul (s s' : Bool) : signK s s' = sgn s * sgn s' := by
  cases s <;> cases s' <;> norm_num [signK, sgn]

theorem signK_self (s : Bool) : signK s s = 1 := by
  cases s <;> norm_num [signK]

/-- **Sign-doubled finite maximum** (lattice form of `E max_{i ∈ F} |X_i| ≤ σ √(2 log 2|F|)`):
if `C` is positive semidefinite on `F` and `C i i ≤ σ²` on `F`, then the expected maximum of the
centered Gaussian family indexed by `F × Bool` with covariance `signK s s' · C i i'` is at most
`σ √(2 log (2 |F|))`. -/
theorem gEM_signK_le {ι : Type*} (F : Finset ι) (C : ι → ι → ℝ) (hC : LQGDimension.PSDOn F C)
    {σ : ℝ} (hσ : 0 ≤ σ) (hdiag : ∀ i ∈ F, C i i ≤ σ ^ 2) :
    LQGDimension.gaussianExpectedMax (F ×ˢ (Finset.univ : Finset Bool))
      (fun p q => signK p.2 q.2 * C p.1 q.1) 0 ≤
        σ * Real.sqrt (2 * Real.log (2 * F.card)) := by
  classical
  obtain ⟨x, hx⟩ := LQGDimension.exists_gram_of_psdOn F C hC
  set S : Finset (ι × Bool) := F ×ˢ (Finset.univ : Finset Bool) with hSdef
  set u : ι × Bool → EuclideanSpace ℝ F := fun p => sgn p.2 • x p.1 with hu
  have hgram : ∀ p ∈ S, ∀ q ∈ S, signK p.2 q.2 * C p.1 q.1 = ⟪u p, u q⟫ := by
    intro p hp q hq
    rw [hSdef, Finset.mem_product] at hp hq
    simp only [hu, real_inner_smul_left, real_inner_smul_right, hx p.1 hp.1 q.1 hq.1,
      signK_eq_mul]
    ring
  rw [LQGDimension.gaussianExpectedMax_congr S 0 hgram,
    LQGDimension.gaussianExpectedMax_gram_eq_vecExpectedMax]
  unfold LQGDimension.vecExpectedMax
  simp only [Pi.zero_apply, add_zero]
  have hnorm : ∀ p ∈ S, ‖u p‖ ≤ σ := by
    intro p hp
    have h1 : ‖u p‖ ^ 2 = C p.1 p.1 := by
      rw [← real_inner_self_eq_norm_sq, ← hgram p hp p hp, signK_self, one_mul]
    rw [hSdef, Finset.mem_product] at hp
    have h2 : ‖u p‖ ^ 2 ≤ σ ^ 2 := h1 ▸ hdiag p.1 hp.1
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hσ two_ne_zero).1 h2
  rcases F.eq_empty_or_nonempty with hF | hF
  · have hS : S = ∅ := by rw [hSdef, hF, Finset.empty_product]
    have hE : IsEmpty ↥S := by rw [hS]; infer_instance
    simp only [Real.iSup_of_isEmpty, integral_zero, hF, Finset.card_empty, Nat.cast_zero,
      mul_zero, Real.log_zero, Real.sqrt_zero, le_refl]
  have hcard : S.card = 2 * F.card := by
    rw [hSdef, Finset.card_product, Finset.card_univ, Fintype.card_bool, mul_comm]
  rcases hσ.lt_or_eq with hσ' | hσ'
  · have hcard' : 1 < S.card := by
      rw [hcard]
      have := hF.card_pos
      omega
    have hint : Integrable (fun y => ⨆ p : ↥S, ⟪u p, y⟫) (stdGaussian (EuclideanSpace ℝ F)) := by
      have := LQGDimension.integrable_iSup_inner_add S u 0
      simpa only [Pi.zero_apply, add_zero] using this
    have h := LQGDimension.GaussianMax.integral_iSup_inner_le_sqrt S hcard' u hσ' hnorm hint
    rw [hcard] at h
    push_cast at h
    exact h
  · subst hσ'
    have hne : Nonempty ↥S := by
      obtain ⟨i, hi⟩ := hF
      exact ⟨⟨(i, true), by rw [hSdef, Finset.mem_product]; exact ⟨hi, Finset.mem_univ _⟩⟩⟩
    have hz : (fun y => ⨆ p : ↥S, ⟪u p, y⟫) = fun _ => (0 : ℝ) := by
      funext y
      have : ∀ p : ↥S, ⟪u p, y⟫ = 0 := fun p => by
        rw [norm_le_zero_iff.1 (hnorm p p.2), inner_zero_left]
      simp only [this, ciSup_const]
    rw [hz, integral_zero, zero_mul]

/-- `sgn s * a ≤ |a|`. -/
theorem sgn_mul_le_abs (s : Bool) (a : ℝ) : sgn s * a ≤ |a| := by
  cases s
  · simp only [sgn, Bool.false_eq_true, ↓reduceIte, neg_mul, one_mul]
    exact neg_le_abs a
  · simp only [sgn, ↓reduceIte, one_mul]
    exact le_abs_self a

/-- **Sign-doubling for a white noise**: for every white noise `W` and every finite family of
vectors `v_i ∈ L²(ℝ × ℝ^d)`, `E max_{i ∈ F} |W(v_i)|` equals the lattice expected maximum of the
sign-doubled Gram family `(signK s s' ⟪v_i, v_{i'}⟫)`.  This converts every lattice bound of
this file into a bound for the pairings of an actual white noise. -/
theorem integral_iSup_abs_eq_gEM {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} (hW : IsWhiteNoise P W) {ι : Type*} (F : Finset ι) (v : ι → WN d) :
    ∫ ω, (⨆ i : F, |W (v i) ω|) ∂P =
      LQGDimension.gaussianExpectedMax (F ×ˢ (Finset.univ : Finset Bool))
        (fun p q => signK p.2 q.2 * ⟪v p.1, v q.1⟫) 0 := by
  classical
  set S : Finset (ι × Bool) := F ×ˢ (Finset.univ : Finset Bool) with hSdef
  set w : ι × Bool → WN d := fun p => sgn p.2 • v p.1 with hw
  have hgram : ∀ p ∈ S, ∀ q ∈ S, signK p.2 q.2 * ⟪v p.1, v q.1⟫ = ⟪w p, w q⟫ := by
    intro p _ q _
    simp only [hw, real_inner_smul_left, real_inner_smul_right, signK_eq_mul]
    ring
  rw [LQGDimension.gaussianExpectedMax_congr S 0 hgram,
    ← hW.integral_iSup_eq_gaussianExpectedMax S w 0]
  have hae : ∀ᵐ ω ∂P, ∀ p : ↥S, W (w p) ω = sgn (p : ι × Bool).2 * W (v (p : ι × Bool).1) ω := by
    rw [ae_all_iff]
    intro p
    exact hW.smul_ae _ _
  refine (integral_congr_ae ?_).symm
  filter_upwards [hae] with ω hω
  simp only [Pi.zero_apply, add_zero, hω]
  rcases isEmpty_or_nonempty ↥F with hF | hF
  · have hS : IsEmpty ↥S := by
      refine ⟨fun p => ?_⟩
      have hp : (p : ι × Bool) ∈ F ×ˢ (Finset.univ : Finset Bool) := p.2
      exact hF.false ⟨_, (Finset.mem_product.1 hp).1⟩
    simp only [Real.iSup_of_isEmpty]
  · have hSne : Nonempty ↥S := by
      obtain ⟨i₀⟩ := hF
      exact ⟨⟨((i₀ : ι), true), Finset.mem_product.2 ⟨i₀.2, Finset.mem_univ _⟩⟩⟩
    have hb1 : BddAbove (Set.range fun i : ↥F => |W (v i) ω|) := (Set.finite_range _).bddAbove
    have hb2 : BddAbove (Set.range fun p : ↥S => sgn (p : ι × Bool).2 * W (v (p : ι × Bool).1) ω) :=
      (Set.finite_range _).bddAbove
    refine le_antisymm (ciSup_le fun p => ?_) (ciSup_le fun i => ?_)
    · have hp : (p : ι × Bool) ∈ F ×ˢ (Finset.univ : Finset Bool) := p.2
      exact (sgn_mul_le_abs _ _).trans (le_ciSup hb1 ⟨_, (Finset.mem_product.1 hp).1⟩)
    · have hmem : ∀ s : Bool, ((i : ι), s) ∈ S := fun s =>
        Finset.mem_product.2 ⟨i.2, Finset.mem_univ _⟩
      rcases le_total 0 (W (v i) ω) with h | h
      · have := le_ciSup hb2 ⟨_, hmem true⟩
        simp only [sgn, ↓reduceIte, one_mul] at this
        rw [abs_of_nonneg h]
        exact this
      · have := le_ciSup hb2 ⟨_, hmem false⟩
        simp only [sgn, Bool.false_eq_true, ↓reduceIte, neg_mul, one_mul] at this
        rw [abs_of_nonpos h]
        exact this

end Bands

variable {d : ℕ} {κ : Rd d → ℝ}

/-- **Lemma 3.4(d), expected maxima for fixed sub-measures** (HA2 D8(d), HA4 (K5)): for every
`B` there is `C = C(d, κ, B)` such that for `0 < a ≤ b`, every finite family `F` and measures
`η_i ≤ ν_i` with `η_i(ℝ^d) ≤ 1`, where `ν_i` is coupled within `a` with `ν'_i` having the growth
bound (3.4) at scale `1`, the lattice expected maximum of `(± ⟨H_{a,b}, η_i⟩)_{i ∈ F}` is
`≤ √(C b) √(2 log (2 |F|))`. -/
theorem bandLemma34d_max (hκ : IsLFPPKernel κ) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b : ℝ), 0 < a → a ≤ b → ∀ {ι : Type*} (F : Finset ι)
      (ν ν' η : ι → Measure (Rd d)), (∀ i, IsFiniteMeasure (ν i)) →
      (∀ i, IsFiniteMeasure (ν' i)) → (∀ i, IsFiniteMeasure (η i)) →
      (∀ i, GrowthBound (ν' i) B 1) → (∀ i, CoupledWithin (ν i) (ν' i) a) →
      (∀ i, η i ≤ ν i) → (∀ i, (η i).real univ ≤ 1) →
      LQGDimension.gaussianExpectedMax (F ×ˢ (Finset.univ : Finset Bool))
        (fun p q => Bands.signK p.2 q.2 * scaleCov κ (Ioo a b) (η p.1) 0 (η q.1) 0) 0 ≤
          Real.sqrt (C * b) * Real.sqrt (2 * Real.log (2 * F.card)) := by
  obtain ⟨C, hC0, hC⟩ := bandLemma34d_var hκ B
  refine ⟨C, hC0, fun a b ha hab ι F ν ν' η hν hν' hη hg hc hle h1 => ?_⟩
  have hb0 : 0 ≤ b := ha.le.trans hab
  refine Bands.gEM_signK_le F _ (psdOn_scaleCov (Ioo a b) F η fun _ => 0) (Real.sqrt_nonneg _)
    fun i _ => ?_
  have := hν i
  have := hν' i
  have := hη i
  obtain ⟨-, hvar⟩ := hC a b ha hab (ν i) (ν' i) (hg i) (hc i) (η i) (hle i)
  rw [Real.sq_sqrt (mul_nonneg hC0 hb0)]
  calc scaleCov κ (Ioo a b) (η i) 0 (η i) 0 ≤ C * b * (η i).real univ := hvar
    _ ≤ C * b * 1 := mul_le_mul_of_nonneg_left (h1 i) (mul_nonneg hC0 hb0)
    _ = C * b := mul_one _

/-- **Lemma 3.4(d), fixed-prefix form** (HA2's `Lemma34dFixed`, with the unused `b ≤ 1` dropped;
the form consumed by Lemma 5.3, HA4 D6): for every `B` there is `C = C(d, κ, B)` such that for
`0 < a ≤ b`, every `J` and probability measures `ν_j` coupled within `a` with probability
measures `ν'_j` having the growth bound (3.4) at scale `1`, uniformly in the prefix level `x`,
`E max_{j < J} |⟨H_{a,b}, ν_j|_{z₁ ≤ x}⟩| ≤ √(C b) √(2 log (2J))` (lattice convention). -/
theorem bandLemma34dFixed (hκ : IsLFPPKernel κ) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b : ℝ), 0 < a → a ≤ b → ∀ (J : ℕ) (ν ν' : Fin J → Measure (Rd d)),
      (∀ j, IsProbabilityMeasure (ν j)) → (∀ j, IsProbabilityMeasure (ν' j)) →
      (∀ j, GrowthBound (ν' j) B 1) → (∀ j, CoupledWithin (ν j) (ν' j) a) → ∀ x : ℝ,
      LQGDimension.gaussianExpectedMax
        ((Finset.univ : Finset (Fin J)) ×ˢ (Finset.univ : Finset Bool))
        (fun p q => Bands.signK p.2 q.2 * scaleCov κ (Ioo a b) (Bands.prefixM (ν p.1) x) 0
          (Bands.prefixM (ν q.1) x) 0) 0 ≤
        Real.sqrt (C * b) * Real.sqrt (2 * Real.log (2 * J)) := by
  obtain ⟨C, hC0, hC⟩ := bandLemma34d_max hκ B
  refine ⟨C, hC0, fun a b ha hab J ν ν' hν hν' hg hc x => ?_⟩
  have h := hC a b ha hab (Finset.univ : Finset (Fin J)) ν ν' (fun j => Bands.prefixM (ν j) x)
    (fun j => by have := hν j; infer_instance) (fun j => by have := hν' j; infer_instance)
    (fun j => by have := hν j; infer_instance) hg hc (fun j => Bands.prefixM_le (ν j) x)
    (fun j => by
      have := hν j
      have h1 := Bands.prefixM_real_univ_le (ν j) x
      rwa [probReal_univ (μ := ν j)] at h1)
  rwa [Finset.card_univ, Fintype.card_fin] at h

/-- **Lemma 3.4(d), white-noise form**: with the constant of `bandLemma34d_max`, for every white
noise `W` (`IsWhiteNoise`), every finite type `ι` and measures `η_i ≤ ν_i` as there,
`E max_i |W(bandVecM κ (a, b) η_i 0)| ≤ √(C b) √(2 log (2 |ι|))`. -/
theorem bandLemma34d_max_wn (hκ : IsLFPPKernel κ) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b : ℝ), 0 < a → a ≤ b →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ), IsWhiteNoise P W →
      ∀ {ι : Type*} [Fintype ι] (ν ν' η : ι → Measure (Rd d)), (∀ i, IsFiniteMeasure (ν i)) →
      (∀ i, IsFiniteMeasure (ν' i)) → (∀ i, IsFiniteMeasure (η i)) →
      (∀ i, GrowthBound (ν' i) B 1) → (∀ i, CoupledWithin (ν i) (ν' i) a) →
      (∀ i, η i ≤ ν i) → (∀ i, (η i).real univ ≤ 1) →
      ∫ ω, (⨆ i, |W (bandVecM κ (Ioo a b) (η i) 0) ω|) ∂P ≤
        Real.sqrt (C * b) * Real.sqrt (2 * Real.log (2 * Fintype.card ι)) := by
  obtain ⟨C, hC0, hC⟩ := bandLemma34d_var hκ B
  refine ⟨C, hC0, fun a b ha hab Ω _ P W hW ι _ ν ν' η hν hν' hη hg hc hle h1 => ?_⟩
  have hb0 : 0 ≤ b := ha.le.trans hab
  refine GaussianLQG.integral_iSup_abs_le (fun i => hW.hasLaw_single _) (Real.sqrt_nonneg _)
    fun i => ?_
  have := hν i
  have := hν' i
  have := hη i
  obtain ⟨-, hvar⟩ := hC a b ha hab (ν i) (ν' i) (hg i) (hc i) (η i) (hle i)
  rw [Real.coe_toNNReal _ (sq_nonneg _), Real.sq_sqrt (mul_nonneg hC0 hb0), ← scaleCov_self]
  calc scaleCov κ (Ioo a b) (η i) 0 (η i) 0 ≤ C * b * (η i).real univ := hvar
    _ ≤ C * b * 1 := mul_le_mul_of_nonneg_left (h1 i) (mul_nonneg hC0 hb0)
    _ = C * b := mul_one _

/-- **Lemma 3.4(d), fixed-prefix form for a white noise** (HA4 (K5)): with the constant of
`bandLemma34d_max_wn`, uniformly in `x`,
`E max_{j < J} |⟨H_{a,b}, ν_j|_{z₁ ≤ x}⟩| ≤ √(C b) √(2 log (2J))`. -/
theorem bandLemma34dFixed_wn (hκ : IsLFPPKernel κ) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b : ℝ), 0 < a → a ≤ b →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ), IsWhiteNoise P W →
      ∀ (J : ℕ) (ν ν' : Fin J → Measure (Rd d)),
      (∀ j, IsProbabilityMeasure (ν j)) → (∀ j, IsProbabilityMeasure (ν' j)) →
      (∀ j, GrowthBound (ν' j) B 1) → (∀ j, CoupledWithin (ν j) (ν' j) a) → ∀ x : ℝ,
      ∫ ω, (⨆ j, |W (bandVecM κ (Ioo a b) (Bands.prefixM (ν j) x) 0) ω|) ∂P ≤
        Real.sqrt (C * b) * Real.sqrt (2 * Real.log (2 * J)) := by
  obtain ⟨C, hC0, hC⟩ := bandLemma34d_max_wn hκ B
  refine ⟨C, hC0, fun a b ha hab Ω _ P W hW J ν ν' hν hν' hg hc x => ?_⟩
  have h := hC a b ha hab P W hW ν ν' (fun j => Bands.prefixM (ν j) x)
    (fun j => by have := hν j; infer_instance) (fun j => by have := hν' j; infer_instance)
    (fun j => by have := hν j; infer_instance) hg hc (fun j => Bands.prefixM_le (ν j) x)
    (fun j => by
      have := hν j
      have h1 := Bands.prefixM_real_univ_le (ν j) x
      rwa [probReal_univ (μ := ν j)] at h1)
  rwa [Fintype.card_fin] at h

/-- **Lemma 3.4(d), combined** (HA2 D8(d); HA4 (K2), (K5)): for every `B` there is **one**
constant `C = C(d, κ, B)` such that for all `0 < a ≤ b`:
* (3.16): for every finite `ν` coupled within `a` with a finite `ν'` having the growth bound (3.4)
  at scale `1` and every positive finite `η ≤ ν`, `Var⟨H_{a,b}, η⟩ ≤ C b η(ℝ^d)`;
* the fixed-prefix form of (3.15): for probability measures `ν_j` (`j < J`) coupled within `a`
  with probability measures `ν'_j` having the growth bound, uniformly in `x`,
  `E max_j |⟨H_{a,b}, ν_j|_{z₁ ≤ x}⟩| ≤ √(C b) √(2 log (2J))`, both in the lattice convention
  and for every white noise `W`. -/
theorem bandLemma34d (hκ : IsLFPPKernel κ) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b : ℝ), 0 < a → a ≤ b →
      (∀ (ν ν' : Measure (Rd d)) [IsFiniteMeasure ν] [IsFiniteMeasure ν'],
        GrowthBound ν' B 1 → CoupledWithin ν ν' a →
        ∀ (η : Measure (Rd d)) [IsFiniteMeasure η], η ≤ ν →
          IsPairable κ (Ioo a b) η 0 ∧ scaleCov κ (Ioo a b) η 0 η 0 ≤ C * b * η.real univ) ∧
      ∀ (J : ℕ) (ν ν' : Fin J → Measure (Rd d)),
        (∀ j, IsProbabilityMeasure (ν j)) → (∀ j, IsProbabilityMeasure (ν' j)) →
        (∀ j, GrowthBound (ν' j) B 1) → (∀ j, CoupledWithin (ν j) (ν' j) a) → ∀ x : ℝ,
        LQGDimension.gaussianExpectedMax
            ((Finset.univ : Finset (Fin J)) ×ˢ (Finset.univ : Finset Bool))
            (fun p q => Bands.signK p.2 q.2 * scaleCov κ (Ioo a b) (Bands.prefixM (ν p.1) x) 0
              (Bands.prefixM (ν q.1) x) 0) 0 ≤
          Real.sqrt (C * b) * Real.sqrt (2 * Real.log (2 * J)) ∧
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ), IsWhiteNoise P W →
          ∫ ω, (⨆ j, |W (bandVecM κ (Ioo a b) (Bands.prefixM (ν j) x) 0) ω|) ∂P ≤
            Real.sqrt (C * b) * Real.sqrt (2 * Real.log (2 * J)) := by
  obtain ⟨C, hC0, hC⟩ := bandLemma34d_var hκ B
  refine ⟨C, hC0, fun a b ha hab => ⟨hC a b ha hab, fun J ν ν' hν hν' hg hc x => ?_⟩⟩
  have hb0 : 0 ≤ b := ha.le.trans hab
  have hvar : ∀ j, scaleCov κ (Ioo a b) (Bands.prefixM (ν j) x) 0 (Bands.prefixM (ν j) x) 0 ≤
      Real.sqrt (C * b) ^ 2 := by
    intro j
    have := hν j
    have := hν' j
    obtain ⟨-, hv⟩ := hC a b ha hab (ν j) (ν' j) (hg j) (hc j) (Bands.prefixM (ν j) x)
      (Bands.prefixM_le (ν j) x)
    have h1 : (Bands.prefixM (ν j) x).real univ ≤ 1 := by
      have h1 := Bands.prefixM_real_univ_le (ν j) x
      rwa [probReal_univ (μ := ν j)] at h1
    rw [Real.sq_sqrt (mul_nonneg hC0 hb0)]
    calc scaleCov κ (Ioo a b) (Bands.prefixM (ν j) x) 0 (Bands.prefixM (ν j) x) 0
        ≤ C * b * (Bands.prefixM (ν j) x).real univ := hv
      _ ≤ C * b * 1 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hC0 hb0)
      _ = C * b := mul_one _
  refine ⟨?_, fun P W hW => ?_⟩
  · have h := Bands.gEM_signK_le (Finset.univ : Finset (Fin J)) _
      (psdOn_scaleCov (κ := κ) (Ioo a b) Finset.univ (fun j => Bands.prefixM (ν j) x) fun _ => 0)
      (Real.sqrt_nonneg _) fun j _ => hvar j
    rwa [Finset.card_univ, Fintype.card_fin] at h
  · have h := GaussianLQG.integral_iSup_abs_le
      (fun j : Fin J => hW.hasLaw_single (bandVecM κ (Ioo a b) (Bands.prefixM (ν j) x) 0))
      (Real.sqrt_nonneg (C * b)) fun j => by
        rw [Real.coe_toNNReal _ (sq_nonneg _), ← scaleCov_self]
        exact hvar j
    rwa [Fintype.card_fin] at h

end HigherDimLFPP
