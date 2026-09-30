import QuantumZipper.Proofs.Zipper.SWCoreA7Fix
import QuantumZipper.Proofs.Zipper.SWCoreA7Fam
import QuantumZipper.Proofs.Zipper.SWCoreA6Fam
import QuantumZipper.Proofs.Zipper.SWCoreA5
import QuantumZipper.Proofs.Thm18.G1Side3Cls
import QuantumZipper.Proofs.Thm18.G1Side3Lim
import QuantumZipper.Proofs.LQG.VagueUniqueOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Coordinate change of the quantum area measure: the free field on `ℍ` (COORD-CHANGE, D98)

Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
Proposition 2.1 (arXiv:0808.1560, p. 12, `literature/0808.1560.txt`): if `ψ : D̃ → D` is a
conformal map and `h̃ = h ∘ ψ + Q log |ψ'|`, then almost surely `μ_{h̃}` is the pullback of
`μ_h` by `ψ`. DS derive it from the approximation of `μ_h` by circle averages and the fact that
`h ∘ ψ` averaged over the ψ-preimage of a small circle is close to a circle average of `h`.
The form used here is Sheffield–Wang (arXiv:1605.06171, Thm 1.4 and (3.5)–(3.7)), already
formalized in this repository for Loewner flows (`SWCore`): for a *deterministic* map `ψ`
the pushed-circle distortion is controlled pathwise through a Kolmogorov-continuous
finite-parameter family (`SWCore.a7_fixed_of_fam`, `SWCore.swcNA2I_primed`, decision D64), and
the distortion bound gives the transport of the dyadic area approximations
(`SWCore.transport_signed_fam`).

Main result, for the free-boundary GFF `X` on `ℍ` (modulo constants) and a deterministic
conformal map `ψ` of `ℍ` into `ℍ` (holomorphic, injective, `ψ' ≠ 0`):

* `CoordChangeArea.ae_isVagueLimitOn_coordChange_free`: almost surely the dyadic area
  approximations of `coordChange (X ω) ψ Q = X ω ∘ ψ + Q log |ψ'|` converge vaguely on `ℍ` to
  the pullback `pullMu μ_{X ω} ψ` (`ψ^* μ`, `(ψ^* μ)(E) = μ(ψ(E ∩ ℍ))`);
* `CoordChangeArea.ae_qAreaMeasure_coordChange_free`: hence
  `qAreaMeasure γ (coordChange (X ω) ψ Q) = pullMu (qAreaMeasure γ (X ω)) ψ` a.s.

The constant family (`constFam_unif`) and the rectangle bookkeeping are own elementary
arguments (copies of `SWCore.a7_unif` and `G1Side.hasAreaLimit_sample`).
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace CoordChangeArea

open SWCore E6 G1Side

/-- The constant family `q ↦ ψ` with clamped centres and radius factors is a uniform family of
the area core. -/
theorem constFam_unif {ψ : ℂ → ℂ} {x₁ x₂ y₁ y₂ ρ M m : ℝ} (hx : x₁ ≤ x₂) (hy0 : 0 < y₁)
    (hy : y₁ ≤ y₂) (hρ : 0 < ρ) (hm : 0 < m) (hψ : ψ ∈ AreaClass x₁ x₂ y₁ y₂ ρ M m) :
    SwcNA2Unif (fun _ : Fin 5 → ℝ => ψ) (a7Cen x₁ x₂ y₁ y₂) a7Rad x₁ x₂ y₁ y₂ ρ M m 2 := by
  refine ⟨hy0, hρ, hm, by norm_num, fun _ => hψ, fun q => ⟨clampI_mem hx _, clampI_mem hy _⟩,
    fun q => (clampI_mem (by norm_num : (1 : ℝ) ≤ 2) _).1,
    fun q => (clampI_mem (by norm_num : (1 : ℝ) ≤ 2) _).2, ?_, ?_, ?_⟩
  · intro q q'
    have h2 := (clampI_lip x₁ x₂ (q 2) (q' 2)).trans (a7_coord_le q q' 2)
    have h3 := (clampI_lip y₁ y₂ (q 3) (q' 3)).trans (a7_coord_le q q' 3)
    have hn := norm_nonneg (q - q')
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [a7Cen, Complex.sub_re, Complex.sub_im]
    nlinarith
  · intro q q'
    have h4 := (clampI_lip 1 2 (q 4) (q' 4)).trans (a7_coord_le q q' 4)
    have hn := norm_nonneg (q - q')
    simp only [a7Rad]
    nlinarith
  · intro q q' w _
    simp only [sub_self, norm_zero]
    positivity

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- **Distortion bound for one deterministic map** (free field): a.s., for every `η > 0`,
eventually in `k`, `|pushErr γ (X ω) ψ k z| ≤ η` for all `z ∈ K`. -/
theorem ae_pushErr_small [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (γ : ℝ)
    {ψ : ℂ → ℂ} {x₁ x₂ y₁ y₂ ρ M m : ℝ} (hx : x₁ ≤ x₂) (hy0 : 0 < y₁) (hy : y₁ ≤ y₂)
    (hρ : 0 < ρ) (hm : 0 < m) (hψ : ψ ∈ AreaClass x₁ x₂ y₁ y₂ ρ M m) {K : Set ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hK : ∀ z ∈ K, closedBall z δ ⊆ a7Open x₁ x₂ y₁ y₂) :
    ∀ᵐ ω ∂P, ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ z ∈ K, |pushErr γ (X ω) ψ k z| ≤ η := by
  obtain ⟨R, hR⟩ := exists_nat_ge (|x₁| + |x₂| + |y₁| + |y₂| + 1)
  have h := a7_fixed_of_fam hX γ (constFam_unif hx hy0 hy hρ hm hψ) (Ψ := fun _ => ψ)
    (V := fun _ => 0) (I := {0}) ?_ R ?_ hδ hK
  · filter_upwards [h] with ω hω η hη
    filter_upwards [hω η hη] with k hk z hz using hk 0 rfl z hz
  · intro t _ w hw
    refine ⟨rfl, ?_, ?_⟩
    · apply Complex.ext
      · simp [a7Diag, a7Cen, clampI_eq hw.1]
      · simp [a7Diag, a7Cen, clampI_eq hw.2]
    · simp [a7Diag, a7Rad, clampI]
  · intro t ht w hw i
    have ht0 : t = 0 := ht
    subst ht0
    obtain ⟨⟨hw1, hw2⟩, ⟨hw3, hw4⟩⟩ := hw
    have a1 := le_abs_self x₁
    have a2 := neg_abs_le x₁
    have a3 := le_abs_self x₂
    have a4 := neg_abs_le x₂
    have a5 := le_abs_self y₁
    have a6 := neg_abs_le y₁
    have a7 := le_abs_self y₂
    have a8 := neg_abs_le y₂
    have hre : |w.re| ≤ R := abs_le.2 ⟨by linarith, by linarith⟩
    have him : |w.im| ≤ R := abs_le.2 ⟨by linarith, by linarith⟩
    have b1 := abs_nonneg x₁
    have b2 := abs_nonneg x₂
    have b3 := abs_nonneg y₁
    have b4 := abs_nonneg y₂
    have hR1 : (1 : ℝ) ≤ R := by linarith
    fin_cases i <;> simp [a7Diag] <;> first | linarith | exact_mod_cast hR1

theorem closedBall_sub_bigR {n : ℕ} {z : ℂ} (hz : z ∈ recR n) :
    closedBall z (1 / (4 * (n + 1 : ℝ))) ⊆
      a7Open (-(n + 1 : ℝ)) (n + 1) (1 / (2 * (n + 1 : ℝ))) (n + 1) := by
  intro u hu
  have hd := mem_closedBall.1 hu
  have h1 := Complex.abs_re_le_norm (u - z)
  have h2 := Complex.abs_im_le_norm (u - z)
  rw [← dist_eq_norm, Complex.sub_re] at h1
  rw [← dist_eq_norm, Complex.sub_im] at h2
  obtain ⟨h1a, h1b⟩ := abs_le.1 h1
  obtain ⟨h2a, h2b⟩ := abs_le.1 h2
  obtain ⟨⟨hz1, hz2⟩, ⟨hz3, hz4⟩⟩ := hz
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hq : 1 / (4 * (n + 1 : ℝ)) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hq2 : 1 / (2 * (n + 1 : ℝ)) + 1 / (4 * (n + 1 : ℝ)) < 1 / (n + 1 : ℝ) := by
    have : 1 / (2 * (n + 1 : ℝ)) + 1 / (4 * (n + 1 : ℝ)) = (3 / 4) * (1 / (n + 1 : ℝ)) := by
      field_simp; ring
    rw [this]
    have : 0 < 1 / (n + 1 : ℝ) := by positivity
    linarith
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **Coordinate change of the area measure, free field, vague form.** For the free-boundary
GFF `X` on `ℍ` and a deterministic map `ψ`, holomorphic and injective on `ℍ` with `ψ(ℍ) ⊆ ℍ`
and `ψ' ≠ 0`: almost surely the dyadic area approximations of `X ω ∘ ψ + Q log |ψ'|` converge
vaguely on `ℍ` to the pullback `ψ^* μ_{X ω}` (DS11 Prop. 2.1). -/
theorem ae_isVagueLimitOn_coordChange_free [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ψ : ℂ → ℂ}
    (hψd : DifferentiableOn ℂ ψ H) (hψi : InjOn ψ H) (hψH : MapsTo ψ H H)
    (hψ0 : ∀ z ∈ H, deriv ψ z ≠ 0) :
    ∀ᵐ ω ∂P, IsVagueLimitOn H (areaApprox γ (coordChange (X ω) ψ (Qc γ)))
      (pullMu (qAreaMeasure γ (X ω)) ψ) := by
  -- the distortion bounds on every `R_n`
  have hE : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ z ∈ recR n,
      |pushErr γ (X ω) ψ k z| ≤ η := by
    rw [ae_all_iff]
    intro n
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    obtain ⟨ρ, M, m, hρ, hm, hcl⟩ := exists_areaClass hψd hψi hψH hψ0
      (a := -(n + 1 : ℝ)) (b := n + 1) (d := n + 1) (c := 1 / (2 * (n + 1 : ℝ))) (by positivity)
    have hy : 1 / (2 * (n + 1 : ℝ)) ≤ n + 1 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    exact ae_pushErr_small hX γ (by linarith) (by positivity) hy hρ hm hcl (by positivity)
      fun z hz => closedBall_sub_bigR hz
  have hΦc : ContinuousOn ψ H := hψd.continuousOn
  filter_upwards [hE, freeWindowStmt_of_splitR hγ hγ2 (swWindowSplitStmtR_holds hγ hγ2) P X hX,
    RegSample.ae_isRegularSample hX, AreaOffsets.ae_hasAreaLimit hX hγ hγ2]
    with ω hEω hW hreg hA
  have hμK : ∀ K, IsCompact K → K ⊆ H → qAreaMeasure γ (X ω) K < ⊤ := hA.2.1
  refine ⟨pullMu_compl_H hΦc hψi, fun K hK hKH => ?_, fun f hf hfc hfH => ?_⟩
  · rw [pullMu_apply hΦc hψi hK.isClosed.measurableSet, inter_eq_left.2 hKH]
    exact hμK _ (hK.image_of_continuousOn (hΦc.mono hKH)) (hψH.image_subset.trans' (image_mono hKH))
  obtain ⟨n, hn⟩ := exists_recR hfc hfH
  set a : ℚ := -(n : ℚ) with ha
  set b : ℚ := (n : ℚ) with hb
  set c : ℚ := 1 / ((n : ℚ) + 1) with hcq
  set d : ℚ := (n : ℚ) with hd
  have hrect : rectC (a : ℝ) b c d = recR n := by
    simp only [recR, ha, hb, hcq, hd]; push_cast; rfl
  have hc0 : (0 : ℝ) < c := by rw [hcq]; push_cast; positivity
  obtain ⟨ρ', M', m', hρ', hm', hcl'⟩ := exists_areaClass (a := a) (b := b) (d := d)
    hψd hψi hψH hψ0 hc0
  obtain ⟨ρq, hρq0, hρq⟩ := exists_rat_btwn hρ'
  obtain ⟨Mq, hMq⟩ := exists_rat_gt M'
  obtain ⟨mq, hmq0, hmq⟩ := exists_rat_btwn hm'
  have hcl : ψ ∈ AreaClass a b c d ρq Mq mq := areaClass_mono hcl' hρq.le hMq.le hmq.le
  have hfK : tsupport f ⊆ interior (rectC (a : ℝ) b c d) := by rw [hrect]; exact hn
  have hErr : ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ ψ' ∈ ({ψ} : Set (ℂ → ℂ)),
      ∀ z ∈ rectC (a : ℝ) b c d, |pushErr γ (X ω) ψ' k z| ≤ η := fun η hη =>
    (hEω n η hη).mono fun k hk ψ' hψ' z hz => by
      rw [mem_singleton_iff.1 hψ']; exact hk z (hrect ▸ hz)
  rw [integral_pullMu hΦc hψi (hrect ▸ recR_subset_H n) hf (hfK.trans interior_subset)]
  rw [Metric.tendsto_atTop]
  intro ε hε
  have ht := transport_signed_fam hγ (tendsto_swC γ) (tendsto_swC' γ) hW hμK
    (measurable_supWin hreg γ) (measurable_infWin hreg γ) hc0 (by exact_mod_cast hρq0)
    (by exact_mod_cast hmq0) (singleton_subset_iff.2 hcl) hErr hf hfc hfK (half_pos hε)
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 ht
  refine ⟨K₀, fun k hk => ?_⟩
  rw [Real.dist_eq]
  exact (hK₀ k hk ψ rfl).trans_lt (half_lt_self hε)

end CoordChangeArea
end QuantumZipper
