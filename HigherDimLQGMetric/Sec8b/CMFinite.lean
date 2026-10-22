import HigherDimLQGMetric.Sec8.Cover
import HigherDimLQGMetric.Sec8.Perturb
import HigherDimLQGMetric.LogEnergy.CM
import HigherDimLQGMetric.LogEnergy.Affine
import HigherDimLQGMetric.LogEnergy.QuantCM

/-!
# Section 8: a uniform Cameron–Martin bound for finite trap shifts

The finite list of smooth bumps is chosen before the scale and centre. Affine
invariance gives one bound at all positive radii and translations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)
open Set

variable {d : ℕ}

/-- A finite trap family has one Cameron–Martin bound at every radius and centre. -/
theorem s7b_exists_cm_uniform (hd : 1 ≤ d) {J : ℕ}
    (f : ℕ → C(Rd d, ℝ))
    (hf : ∀ j < J, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f j) ∧
      HasCompactSupport (f j)) :
    ∃ M0 : ℝ, 0 ≤ M0 ∧
      ∀ j < J, ∀ r : ℝ, 0 < r → ∀ z : Rd d,
        IsCMBounded (bumpAt (f j) r z) M0 := by
  classical
  have hex : ∀ j : Fin J, ∃ C : ℝ, 0 ≤ C ∧ IsCMBounded (f j.1) C := by
    intro j
    exact exists_isCMBounded hd (hf j.1 j.2).1 (hf j.1 j.2).2
  choose C hC using hex
  let M0 : ℝ := ∑ j : Fin J, C j
  have hM0 : 0 ≤ M0 := Finset.sum_nonneg fun j _ => (hC j).1
  refine ⟨M0, hM0, ?_⟩
  intro j hj r hr z
  have hjC : C ⟨j, hj⟩ ≤ M0 :=
    Finset.single_le_sum (fun i hi => (hC i).1) (Finset.mem_univ _)
  have hb : IsCMBounded (bumpAt (f j) r z) (C ⟨j, hj⟩) := by
    change IsCMBounded (fun x => (f j) (r⁻¹ • (x - z))) (C ⟨j, hj⟩)
    exact (hC ⟨j, hj⟩).2.comp_affine (f j).continuous hr z
  exact hb.mono hjC

/-- The perturbation of a labeled set of at most `k` sites costs at most `k M0`. -/
theorem s7b_cm_F_Z {f : ℕ → C(Rd d, ℝ)} {J : ℕ} {M0 : ℝ}
    (hM0 : 0 ≤ M0)
    (hcm : ∀ j < J, ∀ r : ℝ, 0 < r → ∀ z : Rd d,
      IsCMBounded (bumpAt (f j) r z) M0)
    {r : ℝ} (hr : 0 < r) {Z : Finset (Rd d × ℕ)}
    (hJ : ∀ q ∈ Z, q.2 < J) {k : ℕ} (hk : Z.card ≤ k) :
    IsCMBounded (F_Z f r Z) (k * M0) := by
  have hsum : IsCMBounded (fun x => ∑ q ∈ Z, bumpAt (f q.2) r q.1 x)
      (∑ _q ∈ Z, M0) :=
    IsCMBounded.sum Z
      (fun q _ => (bumpAt (f q.2) r q.1).continuous)
      (fun q hq => hcm q.2 (hJ q hq) r hr q.1)
  have hcard : (∑ _q ∈ Z, M0) = Z.card * M0 := by simp
  have hle : Z.card * M0 ≤ k * M0 := by
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hM0
  have hbase : IsCMBounded (F_Z f r Z) (Z.card * M0) := by
    have heq : (F_Z f r Z : Rd d → ℝ) =
        (fun x => ∑ q ∈ Z, bumpAt (f q.2) r q.1 x) := by
      funext x
      simp only [F_Z, ContinuousMap.sum_apply]
    rw [heq]
    rw [hcard] at hsum
    exact hsum
  exact hbase.mono hle

/-- The uniform finite-shift estimate for the actual trap data of Lemma 7.2. -/
theorem s7b_trap_cm {ξ cs Cs : ℝ} {D Dt : DistRd d → ContMetric d}
    (hd : 1 ≤ d) (T : Sec8TrapData d ξ cs Cs D Dt) :
    ∃ M0 : ℝ, 0 ≤ M0 ∧ ∀ {r : ℝ}, 0 < r →
      ∀ {Z : Finset (Rd d × ℕ)},
        (∀ q ∈ Z, q.2 < T.J) → ∀ {k : ℕ}, Z.card ≤ k →
          IsCMBounded (F_Z T.f r Z) (k * M0) := by
  obtain ⟨M0, hM0, hcm⟩ := s7b_exists_cm_uniform hd T.f
    (fun j hj => ⟨(T.bumps j hj).1, (T.bumps j hj).2.1⟩)
  refine ⟨M0, hM0, ?_⟩
  intro r hr Z hJ k hk
  exact s7b_cm_F_Z hM0 hcm hr hJ hk

end HigherDimLQGMetric
