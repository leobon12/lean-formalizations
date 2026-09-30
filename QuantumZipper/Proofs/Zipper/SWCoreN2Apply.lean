import QuantumZipper.Proofs.Zipper.SWCoreN2Adm
import QuantumZipper.Proofs.GFF.SmoothingConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-N2 (5): boundary distortion, uniformly over a finite-parameter family of class maps

Task SWC-N (`handoff/SW-CORE.md` §5), restricted form (orchestrator's allowance): a family
`q ↦ Ψ q` of maps of one boundary class, indexed by a bounded parameter set `Kp ⊂ ℝⁿ`, Lipschitz
in `q` in sup norm on the `ρ`-thickening. For the free boundary GFF `X`, almost surely, for every
`η > 0`, eventually in `k`, for every `θ = (q, t)` in a countable set `D ⊂ Kp × [a,b]`,

  `|X(fc(t, r_k).map (Ψ q)) − X(fc(Ψ q (t), r_k ‖(Ψ q)'(t)‖))| ≤ η`     (`swcn2_family_dist`).

This is the pathwise, family-uniform form of Sheffield–Wang, arXiv:1605.06171, Lemma 3.4 (3.20)
with the Borell–TIS/Borel–Cantelli step of Lemma 3.5 (p. 16), for the raw Gaussian values on a
countable parameter set; the passage to all parameters and to the regularized values `evalReg`
is the pathwise identification (continuity of the regularized family, task SWC-N (c)).
Proof: the Gaussian family `Z k θ = X(ν_{k,θ}) − X(σ_{k,θ})` has variance `≤ C r_k^{1/6}`
(`swcv_class_var`) and modulus `≲ (‖θ − θ'‖/r_k)^{1/6}` for `‖θ − θ'‖ ≤ r_k²`
(`swcv_class_modulus`, `swcn2_round_modulus`, `swcn2_deriv_sub_le`), so
`swcn2_ae_eventually_small` applies. Own assembly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal Real

namespace QuantumZipper
namespace SWCore

open RegUnif TwoPoint

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

/-- `Var(A − B) ≤ 2 Var A + 2 Var B`. -/
theorem swcn2_var_sub_le {A B : Ω → ℝ} (hA : MemLp A 2 P) (hB : MemLp B 2 P) :
    Var[fun ω => A ω - B ω; P] ≤ 2 * Var[A; P] + 2 * Var[B; P] := by
  have h1 := variance_fun_sub hA hB
  have h2 := variance_fun_add hA hB
  have h3 := variance_nonneg (fun ω => A ω + B ω) P
  rw [h2] at h3
  rw [h1]
  have := variance_nonneg A P
  have := variance_nonneg B P
  linarith

/-- The variance of an admissible balanced pair is its Neumann energy. -/
theorem swcn2_var_pair (hX : IsFreeGFFModConstH X P) {μ ν : Measure ℂ} (hμ : IsAdmissibleH μ)
    (hν : IsAdmissibleH ν) (hm : μ univ = ν univ) :
    Var[fun ω => X ω μ - X ω ν; P] = kernelCov2 neumannH (μ, ν) (μ, ν) := by
  have hmeas : AEMeasurable (fun ω => X ω μ - X ω ν) P :=
    ((hX.measurable_coord μ).sub (hX.measurable_coord ν)).aemeasurable
  rw [← covariance_self hmeas]
  exact hX.covariance_eq (μ, ν) (μ, ν) hμ hν hm hμ hν hm

theorem swcn2_radius_anti {k₀ k : ℕ} (h : k₀ ≤ k) : radius k ≤ radius k₀ := by
  unfold radius; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h

theorem swcn2_radius_pos (k : ℕ) : 0 < radius k := by unfold radius; positivity

set_option maxHeartbeats 2000000 in
/-- **Energy bounds over a family** (deterministic): admissibility, pushed-vs-round variance, and
the moduli of the pushed and of the round semicircles in the parameters, for increments `≤ r²`. -/
theorem swcn2_family_energy {n : ℕ} (Ψ : (Fin n → ℝ) → ℂ → ℂ) (Kp : Set (Fin n → ℝ))
    {a b ρ M m L : ℝ} (hab : a < b) (hρ : 0 < ρ) (hm : 0 < m) (hL : 0 ≤ L)
    (hcl : ∀ q ∈ Kp, Ψ q ∈ BdryClass a b ρ M m)
    (hlip : ∀ q ∈ Kp, ∀ q' ∈ Kp, ∀ z ∈ thickening ρ (segC a b),
      ‖Ψ q z - Ψ q' z‖ ≤ L * ‖q - q'‖) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∃ CV CE : ℝ, 0 ≤ CV ∧ 0 ≤ CE ∧ ∀ r ∈ Ioo 0 r₀,
      ∀ q ∈ Kp, ∀ t ∈ Icc a b,
        (IsAdmissibleH ((foldedCircle (t : ℂ) r).map (Ψ q)) ∧
          ((foldedCircle (t : ℂ) r).map (Ψ q)) univ = 1 ∧
          0 < r * ‖deriv (Ψ q) t‖ ∧
          |kernelCov2 neumannH ((foldedCircle (t : ℂ) r).map (Ψ q),
              foldedCircle (((Ψ q t).re : ℝ) : ℂ) (r * ‖deriv (Ψ q) t‖))
              ((foldedCircle (t : ℂ) r).map (Ψ q),
                foldedCircle (((Ψ q t).re : ℝ) : ℂ) (r * ‖deriv (Ψ q) t‖))| ≤
            CV * r ^ ((1 / 3 : ℝ) / 2)) ∧
        ∀ q' ∈ Kp, ∀ t' ∈ Icc a b, ∀ e : ℝ, ‖q - q'‖ ≤ e → |t - t'| ≤ e → e ≤ r ^ 2 →
          |kernelCov2 neumannH ((foldedCircle (t : ℂ) r).map (Ψ q),
              (foldedCircle (t' : ℂ) r).map (Ψ q'))
              ((foldedCircle (t : ℂ) r).map (Ψ q), (foldedCircle (t' : ℂ) r).map (Ψ q'))| ≤
            CE * (e / r) ^ ((1 / 3 : ℝ) / 2) ∧
          |kernelCov2 neumannH (foldedCircle (((Ψ q t).re : ℝ) : ℂ) (r * ‖deriv (Ψ q) t‖),
              foldedCircle (((Ψ q' t').re : ℝ) : ℂ) (r * ‖deriv (Ψ q') t'‖))
              (foldedCircle (((Ψ q t).re : ℝ) : ℂ) (r * ‖deriv (Ψ q) t‖),
                foldedCircle (((Ψ q' t').re : ℝ) : ℂ) (r * ‖deriv (Ψ q') t'‖))| ≤
            CE * (e / r) ^ ((1 / 3 : ℝ) / 2) := by
  obtain ⟨rA, hrA, hA⟩ := swcn2_push_admissible a b ρ M m hab hρ hm
  obtain ⟨rV, hrV, CV, hCV, hV⟩ := swcv_class_var a b ρ M m hab hρ hm
  obtain ⟨rM, hrM, CM, hCM, hMod⟩ := swcv_class_modulus a b ρ M m hab hρ hm
  obtain ⟨rB, hrB, CB, hCB, hB⟩ := swcv_ball_facts a b ρ M m hab hρ hm
  set K2 : ℝ := (|M| + 1) / (ρ / 4) / (ρ / 4) with hK2
  have hK20 : 0 ≤ K2 := by positivity
  set C3 : ℝ := 2 * CB + L + K2 + 2 * L / ρ with hC3
  have hC30 : 0 ≤ C3 := by positivity
  set hK : ℝ := holderK (12 / (1 / 2) + 1) 2 with hhK
  have hhK0 : 0 ≤ hK := holderK_nonneg (by norm_num) (by norm_num)
  set β : ℝ := (1 / 3 : ℝ) / 2 with hβ
  have hβ0 : 0 < β := by norm_num
  set CE : ℝ := CM * (L + 1) ^ β + 2 * hK * (C3 / m) ^ β with hCE
  have hCE0 : 0 ≤ CE := by positivity
  set r₀ : ℝ := min (min (min rA rV) (min rM rB)) (min (min (ρ / 4) 1)
    (min (1 / (L + 1)) (m / (2 * C3 + 1)))) with hr₀
  have hr₀0 : 0 < r₀ := by
    refine lt_min (lt_min (lt_min hrA hrV) (lt_min hrM hrB)) (lt_min (lt_min (by linarith)
      one_pos) (lt_min (by positivity) (by positivity)))
  refine ⟨r₀, hr₀0, CV, CE, hCV, hCE0, fun r hr q hq t ht => ?_⟩
  have hr0 := hr.1
  have hrr : r < r₀ := hr.2
  have hrA' : r < rA := by
    refine lt_of_lt_of_le hrr ?_; simp only [hr₀]
    exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hrV' : r < rV := by
    refine lt_of_lt_of_le hrr ?_; simp only [hr₀]
    exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hrM' : r < rM := by
    refine lt_of_lt_of_le hrr ?_; simp only [hr₀]
    exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrB' : r < rB := by
    refine lt_of_lt_of_le hrr ?_; simp only [hr₀]
    exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hrρ : r < ρ / 4 := by
    refine lt_of_lt_of_le hrr ?_; simp only [hr₀]
    exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hr1 : r < 1 := by
    refine lt_of_lt_of_le hrr ?_; simp only [hr₀]
    exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hrL : r < 1 / (L + 1) := by
    refine lt_of_lt_of_le hrr ?_; simp only [hr₀]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrm : r < m / (2 * C3 + 1) := by
    refine lt_of_lt_of_le hrr ?_; simp only [hr₀]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hr2r : r ^ 2 ≤ r := by nlinarith
  have hψ := hcl q hq
  obtain ⟨⟨hmD, hDC⟩, hLip, -⟩ := hB (Ψ q) hψ t ht r ⟨hr0, hrB'⟩
  obtain ⟨hDre, -⟩ := swcv_deriv_real hψ hρ hab ht
  have hnormD : ‖deriv (Ψ q) t‖ = (deriv (Ψ q) t).re := by
    rw [hDre, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re,
      abs_of_pos (lt_of_lt_of_le hm hmD)]
  have hDpos : 0 < ‖deriv (Ψ q) t‖ := by rw [hnormD]; linarith
  refine ⟨⟨(hA (Ψ q) hψ t ht r ⟨hr0, hrA'⟩).1, (hA (Ψ q) hψ t ht r ⟨hr0, hrA'⟩).2,
    mul_pos hr0 hDpos, hV (Ψ q) hψ t ht r ⟨hr0, hrV'⟩⟩,
    fun q' hq' t' ht' e hqe hte her => ⟨?_, ?_⟩⟩
  · -- pushed modulus
    have hψ' := hcl q' hq'
    have he0 : 0 ≤ e := (norm_nonneg _).trans hqe
    have her' : e ≤ r := her.trans hr2r
    have hLe : L * e ≤ r := by
      have h1 : L * e ≤ L * r ^ 2 := mul_le_mul_of_nonneg_left her hL
      have h2 : L * r ^ 2 ≤ r := by
        have : r * (L + 1) < 1 := by rw [lt_div_iff₀ (by positivity)] at hrL; linarith
        nlinarith
      linarith
    have hδ : ∀ z ∈ closedBall (t' : ℂ) r, ‖Ψ q z - Ψ q' z‖ ≤ L * e := fun z hz => by
      have hz' : z ∈ thickening ρ (segC a b) := swcv_ball_sub ht'
        (by rw [mem_ball]; rw [mem_closedBall] at hz; linarith)
      exact (hlip q hq q' hq' z hz').trans (mul_le_mul_of_nonneg_left hqe hL)
    have h := hMod (Ψ q) hψ (Ψ q') hψ' t ht t' ht' r ⟨hr0, hrM'⟩ (hte.trans her')
      (L * e) (by positivity) hLe hδ
    refine h.trans ?_
    have hmono : ((L * e + |t - t'|) / r) ^ β ≤ ((L + 1) * (e / r)) ^ β := by
      refine Real.rpow_le_rpow (by positivity) ?_ hβ0.le
      rw [div_le_iff₀ hr0]
      have : (L + 1) * (e / r) * r = L * e + e := by field_simp
      rw [this]; linarith
    calc CM * ((L * e + |t - t'|) / r) ^ β ≤ CM * ((L + 1) * (e / r)) ^ β :=
          mul_le_mul_of_nonneg_left hmono hCM
      _ = CM * (L + 1) ^ β * (e / r) ^ β := by
          rw [Real.mul_rpow (by positivity) (by positivity)]; ring
      _ ≤ CE * (e / r) ^ β := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [hCE]; have : 0 ≤ 2 * hK * (C3 / m) ^ β := by positivity
          linarith
  · -- round modulus
    have hψ' := hcl q' hq'
    have he0 : 0 ≤ e := (norm_nonneg _).trans hqe
    have htt' : |t - t'| < ρ / 4 := lt_of_le_of_lt (hte.trans (her.trans hr2r)) hrρ
    have hδ : ∀ z ∈ thickening ρ (segC a b), ‖Ψ q z - Ψ q' z‖ ≤ L * e := fun z hz =>
      (hlip q hq q' hq' z hz).trans (mul_le_mul_of_nonneg_left hqe hL)
    have hder := swcn2_deriv_sub_le hρ hψ hψ' hδ ht ht' htt'
    have ht'B : (t' : ℂ) ∈ closedBall (t : ℂ) r := by
      rw [mem_closedBall, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_sub_comm]
      exact hte.trans (her.trans hr2r)
    have hs : |(Ψ q t).re - (Ψ q' t').re| ≤ (2 * CB + L) * e := by
      have h1 := (hLip (t : ℂ) (mem_closedBall_self hr0.le) (t' : ℂ) ht'B).2
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h1
      have h2 : ‖Ψ q t' - Ψ q' t'‖ ≤ L * e := hδ _ (swcv_ball_sub ht' (mem_ball_self hρ))
      have h3 : ‖Ψ q t - Ψ q' t'‖ ≤ 2 * CB * e + L * e := by
        calc ‖Ψ q t - Ψ q' t'‖ = ‖(Ψ q t - Ψ q t') + (Ψ q t' - Ψ q' t')‖ := by ring_nf
          _ ≤ ‖Ψ q t - Ψ q t'‖ + ‖Ψ q t' - Ψ q' t'‖ := norm_add_le _ _
          _ ≤ 2 * CB * e + L * e := by
              have : 2 * (deriv (Ψ q) t).re * |t - t'| ≤ 2 * CB * e := by
                have := mul_le_mul hDC hte (abs_nonneg _) hCB
                nlinarith
              linarith
      calc |(Ψ q t).re - (Ψ q' t').re| = |(Ψ q t - Ψ q' t').re| := by rw [Complex.sub_re]
        _ ≤ ‖Ψ q t - Ψ q' t'‖ := Complex.abs_re_le_norm _
        _ ≤ (2 * CB + L) * e := by linarith
    have hρd : |r * ‖deriv (Ψ q) t‖ - r * ‖deriv (Ψ q') t'‖| ≤ (K2 + 2 * L / ρ) * e := by
      have emul : r * ‖deriv (Ψ q) t‖ - r * ‖deriv (Ψ q') t'‖ =
          r * (‖deriv (Ψ q) t‖ - ‖deriv (Ψ q') t'‖) := by ring
      rw [emul, abs_mul, abs_of_pos hr0]
      have h1 : |‖deriv (Ψ q) t‖ - ‖deriv (Ψ q') t'‖| ≤ ‖deriv (Ψ q) t - deriv (Ψ q') t'‖ :=
        abs_norm_sub_norm_le _ _
      have h2 : K2 * |t - t'| + L * e / (ρ / 2) ≤ (K2 + 2 * L / ρ) * e := by
        have : K2 * |t - t'| ≤ K2 * e := mul_le_mul_of_nonneg_left hte hK20
        have e2 : L * e / (ρ / 2) = 2 * L / ρ * e := by field_simp
        rw [e2]; linarith
      have h3 : |‖deriv (Ψ q) t‖ - ‖deriv (Ψ q') t'‖| ≤ (K2 + 2 * L / ρ) * e :=
        h1.trans (hder.trans h2)
      have h4 : r * |‖deriv (Ψ q) t‖ - ‖deriv (Ψ q') t'‖| ≤ 1 * ((K2 + 2 * L / ρ) * e) :=
        mul_le_mul hr1.le h3 (abs_nonneg _) zero_le_one
      linarith
    have hsum : |(Ψ q t).re - (Ψ q' t').re| + |r * ‖deriv (Ψ q) t‖ - r * ‖deriv (Ψ q') t'‖| ≤
        C3 * e := by
      have hC3e : (2 * CB + L) * e + (K2 + 2 * L / ρ) * e = C3 * e := by simp only [hC3]; ring
      linarith
    have hrD : r * m ≤ r * ‖deriv (Ψ q) t‖ := by
      exact le_of_le_of_eq (mul_le_mul_of_nonneg_left hmD hr0.le)
        (congrArg (r * ·) hnormD.symm)
    have hsmall : |(Ψ q t).re - (Ψ q' t').re| + |r * ‖deriv (Ψ q) t‖ - r * ‖deriv (Ψ q') t'‖| ≤
        r * ‖deriv (Ψ q) t‖ / 2 := by
      have h1 : C3 * e ≤ C3 * r ^ 2 := mul_le_mul_of_nonneg_left her hC30
      have h2 : C3 * r ≤ m / 2 := by
        have : r * (2 * C3 + 1) < m := by rw [lt_div_iff₀ (by positivity)] at hrm; exact hrm
        nlinarith
      have h3 : C3 * r ^ 2 ≤ r * m / 2 := by nlinarith
      linarith
    have h := swcn2_round_modulus (mul_pos hr0 hDpos) hsmall
    refine h.trans ?_
    have hmono : ((|(Ψ q t).re - (Ψ q' t').re| + |r * ‖deriv (Ψ q) t‖ - r * ‖deriv (Ψ q') t'‖|) /
        (r * ‖deriv (Ψ q) t‖)) ^ β ≤ (C3 / m * (e / r)) ^ β := by
      refine Real.rpow_le_rpow (by positivity) ?_ hβ0.le
      rw [div_le_iff₀ (mul_pos hr0 hDpos)]
      have hx : C3 / m * (e / r) * (r * m) = C3 * e := by field_simp
      have : C3 / m * (e / r) * (r * m) ≤ C3 / m * (e / r) * (r * ‖deriv (Ψ q) t‖) :=
        mul_le_mul_of_nonneg_left hrD (by positivity)
      linarith
    calc 2 * (hK * ((|(Ψ q t).re - (Ψ q' t').re| + |r * ‖deriv (Ψ q) t‖ -
            r * ‖deriv (Ψ q') t'‖|) / (r * ‖deriv (Ψ q) t‖)) ^ β)
        ≤ 2 * (hK * (C3 / m * (e / r)) ^ β) := by gcongr
      _ = 2 * hK * (C3 / m) ^ β * (e / r) ^ β := by
          rw [Real.mul_rpow (by positivity) (by positivity)]; ring
      _ ≤ CE * (e / r) ^ β := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have : 0 ≤ CM * (L + 1) ^ β := by positivity
          rw [hCE]; exact le_add_of_nonneg_left this

end SWCore
end QuantumZipper
