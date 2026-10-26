import SupercriticalConformalCovariance.BiLip.Sample
import SupercriticalConformalCovariance.Cover.Subsequence

/-!
# Lemma 2.1, steps 4 and 6: good covers and the single almost-sure event

Paper l. 133–138 and 145–148. On one probability space carry the source field `h` (a whole-plane GFF,
l. 40) and a realization `(g₀, k)` of the target field on `V`. The good events of the two directions are
* `F₁ z r = {e(around A_{r,2r}(z)) < K · D_h(across A_{r/2,r}(z))}` (for `e ≤ K d`), and
* `F₂ z r = {D_h(around A_{r,2r}(z)) < K · e(across A_{r/2,r}(z))}` (for `d ≤ K e`).
If, for every compact `L ⊆ U` and small `r`, both are annulus-local events (`AEEventIn` of `localSigma`, the
transported locality of l. 136–138) of probability at least the `p` of the covering lemma for display (10) (from (4)), then along the
deterministic sequence `ε_j = 2^{-(j+1)}` the good covers occur almost surely on every compact `L ⊆ U` for
all large `j` (`goodCovers_everyCompact`, Borel–Cantelli), and on that single event both
comparisons hold for every pair of points (`sample_e_le`, `sample_d_le`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalConformalCovariance.BiLip

open SupercriticalLQGUniqueness (LSCMetric weylScale)
open SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier (forget)
open SupercriticalConformalCovariance.Cover (coverFamily coverEvent localSigma goodCovers_everyCompact summable_two_pow
  tendsto_two_pow)
open LQGMetric (DistC IsWholePlaneGFF addFun)
open LQGMetric.Blueprint (AEEventIn)

/-- the good event of `e ≤ K d` at `(z, r)`: `e(around A_{9ρ/8,15ρ/8}(φ z)) < K D_h(across A_{r/2,r}(z))` -/
def goodEvent₁ {Ω : Type} (D : DistC → LSCMetric) (ξ : ℝ) {V : Set ℂ} (φ : ℂ → ℂ)
    (h g₀ : Ω → DistC) (k : Ω → C(V, ℝ)) (K : ℝ≥0∞) (z : ℂ) (r : ℝ) : Set Ω :=
  {ω | goodPair₁ (D (h ω)) (D (g₀ ω)) ξ (k ω) φ K z r}

/-- the good event of `d ≤ K e` at `(z, r)`: `D_h(around A_{r,2r}(z)) < K e(across cl A_{5ρ/8,7ρ/8}(φ z))` -/
def goodEvent₂ {Ω : Type} (D : DistC → LSCMetric) (ξ : ℝ) {V : Set ℂ} (φ : ℂ → ℂ)
    (h g₀ : Ω → DistC) (k : Ω → C(V, ℝ)) (K : ℝ≥0∞) (z : ℂ) (r : ℝ) : Set Ω :=
  {ω | goodPair₂ (D (h ω)) (D (g₀ ω)) ξ (k ω) φ K z r}

/-- The sample properties used: `(ℂ, D_h) → ℂ` and `(ℂ, D_{g₀}) → ℂ` continuous, `D_{g₀}` a length space,
and Weyl scaling of `D_{g₀}` by every continuous function. They hold almost surely for GFFs plus continuous
functions and a strong LQG metric (`ae_sample_of_isGFFPlusCont`). -/
def IsGoodSample (D : DistC → LSCMetric) (ξ : ℝ) (h g₀ : DistC) : Prop :=
  Continuous (forget (D h)) ∧ Continuous (forget (D g₀)) ∧ (D g₀).IsLengthSpace ∧
    ∀ F : C(ℂ, ℝ), weylScale ξ F (D g₀) = (D (addFun g₀ F)).1

/-- **Lemma 2.1, probabilistic assembly** (steps 4 and 6). There is `p ∈ (0, 1)` (the covering lemma for display (10)'s, for the
rate `q = 1`) such that, if the good events of both directions are annulus-local with probability `≥ p` on
small scales around every compact `L ⊆ U`, then almost surely `e ≤ K d` and `d ≤ K e` on `U × U`. -/
theorem bilip_assembly :
    ∃ p : ℝ, 0 < p ∧ p < 1 ∧
      ∀ (D : DistC → LSCMetric) (ξ : ℝ), 0 ≤ ξ → ∀ {U V : Set ℂ}, IsOpen U → IsOpen V →
      ∀ {φ : ℂ → ℂ}, DifferentiableOn ℂ φ U → InjOn φ U → φ '' U = V →
      ContinuousOn (Function.invFunOn φ U) V →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h g₀ : Ω → DistC) (k : Ω → C(V, ℝ)), IsWholePlaneGFF h P →
        (∀ᵐ ω ∂P, IsGoodSample D ξ (h ω) (g₀ ω)) →
      ∀ {K : ℝ≥0∞}, K ≠ 0 → K ≠ ∞ →
      (∀ L : Set ℂ, IsCompact L → L ⊆ U → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ z ∈ L, ∀ r ∈ Ioc (0 : ℝ) r₀,
        (AEEventIn P (localSigma h z r) (goodEvent₁ D ξ φ h g₀ k K z r) ∧
          ENNReal.ofReal p ≤ P (goodEvent₁ D ξ φ h g₀ k K z r)) ∧
        (AEEventIn P (localSigma h z r) (goodEvent₂ D ξ φ h g₀ k K z r) ∧
          ENNReal.ofReal p ≤ P (goodEvent₂ D ξ φ h g₀ k K z r))) →
      ∀ᵐ ω ∂P, ∀ u ∈ U, ∀ v ∈ U,
        eT (D (g₀ ω)) ξ (k ω) φ u v ≤ K * pathInf (D (h ω)) U u v ∧
          pathInf (D (h ω)) U u v ≤ K * eT (D (g₀ ω)) ξ (k ω) φ u v := by
  obtain ⟨p, hp0, hp1, H⟩ := goodCovers_everyCompact 1 one_pos
  refine ⟨p, hp0, hp1, ?_⟩
  intro D ξ hξ U V hU hV φ hφd hinj hφV hψc Ω _ P _ h g₀ k hh hsample K hK0 hKtop hloc
  have hφU : MapsTo φ U V := fun x hx => hφV ▸ mem_image_of_mem φ hx
  have hψV : MapsTo (Function.invFunOn φ U) V U := fun y hy => by
    rw [← hφV] at hy; exact Function.invFunOn_mem hy
  have hφψ : ∀ y ∈ V, φ (Function.invFunOn φ U y) = y := fun y hy => by
    rw [← hφV] at hy; exact Function.invFunOn_eq hy
  have hψφ : ∀ x ∈ U, Function.invFunOn φ U (φ x) = x := fun x hx => hinj.leftInvOn_invFunOn hx
  have hψc' : ContinuousOn (Function.invFunOn φ U) (φ '' U) := hφV ▸ hψc
  set ε : ℕ → ℝ := fun j => (2 : ℝ)⁻¹ ^ (j + 1) with hεdef
  have hεpos : ∀ j, 0 < ε j := fun j => pow_pos (by norm_num) _
  have hsum : Summable (fun j => ε j ^ (1 : ℝ)) := summable_two_pow one_pos
  have hcov₁ := H P h hh U hU (goodEvent₁ D ξ φ h g₀ k K)
    (fun L hL hLU => by
      obtain ⟨r₀, hr₀, hz⟩ := hloc L hL hLU
      exact ⟨r₀, hr₀, fun z hz' r hr => (hz z hz' r hr).1⟩) ε hεpos tendsto_two_pow hsum
  have hcov₂ := H P h hh U hU (goodEvent₂ D ξ φ h g₀ k K)
    (fun L hL hLU => by
      obtain ⟨r₀, hr₀, hz⟩ := hloc L hL hLU
      exact ⟨r₀, hr₀, fun z hz' r hr => (hz z hz' r hr).2⟩) ε hεpos tendsto_two_pow hsum
  filter_upwards [hsample, hcov₁, hcov₂] with ω hs hω₁ hω₂
  obtain ⟨hf₁, hf₀, hL₀, hW⟩ := hs
  have hE : ∀ (F : C(ℂ, ℝ)) (q : ℂ × ℂ), (D (addFun (g₀ ω) F)) q = weylScale ξ F (D (g₀ ω)) q :=
    fun F q => (congrFun (hW F) q).symm
  intro u hu v hv
  refine ⟨sample_e_le ξ hξ hU hV hφd hinj hφU hψc' (D (h ω)) hf₁ (D (g₀ ω)) hf₀ hL₀
      (fun F => D (addFun (g₀ ω) F)) hE (k ω) hK0 hKtop ε hεpos tendsto_two_pow
      (fun L hL hLU => hω₁ L hL hLU) u hu v hv,
    sample_d_le ξ hU hV hφd hinj hψV hψc hφψ hψφ (D (h ω)) hf₁ (D (g₀ ω)) hf₀ (k ω) hK0 hKtop ε
      hεpos tendsto_two_pow (fun L hL hLU => hω₂ L hL hLU) u hu v hv⟩

end SupercriticalConformalCovariance.BiLip
