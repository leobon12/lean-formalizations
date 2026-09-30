import QuantumZipper.Proofs.Zipper.UnifUCFixBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# UNIF-RC3-FIX (decision D33): `FixedUCStmt` from `IdentStmt` and `DetUnifStmt`

**Main result** `fixedUCStmt_of_id_det : IdentStmt κ T → DetUnifStmt κ T → FixedUCStmt κ T P X`
(for a free GFF modulo constants `X` under a probability measure `P`).

Proof. Fix a Hölder driver `W`, `d`, `k`. `exists_contMod_US` (E1, E2 and the three-parameter
Kolmogorov–Čentsov step) gives `Y` with `q ↦ Y q ω` continuous for every `ω` and
`Y (embP p ρ) = X(muUS p ρ)` a.s. for each `(p, ρ) ∈ tri T × [0,1]`. On the countably many
`(p, j) ∈ triQ T × ℕ`, a.s. simultaneously: `PhiW j p = X(muUS p 2^{-j}) + detJ p j` (`IdentStmt`)
and `X(muUS p 2^{-j}) = Y(embP p 2^{-j})`. For such `ω`, `Y(·, ω)` is uniformly continuous on
the compact box `[-1, T+1]³ ⊇ embP(tri T × [0,1])`, so the random part is uniformly Cauchy in `j`
(`2^{-j} → 0`), and the deterministic part is uniformly Cauchy by `DetUnifStmt`.

Sources: Revuz–Yor, 3rd ed., Ch. I, Thm (2.1); Duplantier–Sheffield, Invent. Math. 185 (2011),
Prop. 3.1. The gluing (countable a.s. identification, Heine–Cantor) is an own elementary step,
as in `JointModRandom`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace RegUnif

open RegCont TwoPoint GFFExist B2

theorem dist_embP_le (p : ℝ × ℝ) (ρ ρ' : ℝ) : dist (embP p ρ) (embP p ρ') ≤ |ρ - ρ'| := by
  refine (dist_pi_le_iff (abs_nonneg _)).2 fun i => ?_
  fin_cases i
  · simp [embP]
  · simp [embP]
  · simp [embP, Real.dist_eq]

theorem embP_mem_box {T : ℝ} {p : ℝ × ℝ} (hp : p ∈ tri T) {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) :
    embP p ρ ∈ Set.pi univ (fun _ : Fin 3 => Icc (-1 : ℝ) (T + 1)) := by
  have hT : 0 ≤ T := hp.1.trans (by linarith [hp.2.1, hp.2.2])
  intro i _
  fin_cases i
  · show -1 ≤ p.1 ∧ p.1 ≤ T + 1
    exact ⟨by linarith [hp.1], by linarith [hp.2.1, hp.2.2]⟩
  · show -1 ≤ p.2 ∧ p.2 ≤ T + 1
    exact ⟨by linarith [hp.2.1], by linarith [hp.1, hp.2.2]⟩
  · show -1 ≤ ρ ∧ ρ ≤ T + 1
    exact ⟨by linarith [hρ.1], by linarith [hρ.2]⟩

theorem radius_mem_Icc (j : ℕ) : radius j ∈ Icc (0 : ℝ) 1 :=
  ⟨(radius_pos j).le, by unfold radius; exact pow_le_one₀ (by norm_num) (by norm_num)⟩

/-- **UNIF-RC3-FIX: uniform Cauchy for a fixed Hölder driver**, from `IdentStmt` and
`DetUnifStmt`. -/
theorem fixedUCStmt_of_id_det {κ T : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P)
    (hID : IdentStmt κ T) (hDET : DetUnifStmt κ T) : FixedUCStmt κ T P X := by
  intro W a CH hWH d k
  have hWH' := hWH
  obtain ⟨hW, hW0, -, -, -, -⟩ := hWH'
  by_cases hT : 0 ≤ T
  swap
  · filter_upwards with ω n
    refine ⟨0, fun j _ j' _ p hp => absurd ?_ hT⟩
    have hp' := triQ_subset_tri T hp
    linarith [hp'.1, hp'.2.1, hp'.2.2]
  obtain ⟨Y, hYc, hYZ⟩ := exists_contMod_US (W := W) hX hWH hT d k
  have : Countable (triQ T) := (countable_triQ T).to_subtype
  have hgood : ∀ᵐ ω ∂P, ∀ x : triQ T × ℕ,
      PhiW κ W d k x.2 (X ω) x.1 = X ω (muUS W d k x.1 (radius x.2)) + detJ κ W d k x.1 x.2 ∧
        Y (embP x.1 (radius x.2)) ω = X ω (muUS W d k x.1 (radius x.2)) := by
    refine ae_all_iff.2 fun x => ?_
    have hx : (x.1 : ℝ × ℝ) ∈ tri T := triQ_subset_tri T x.1.2
    have h2 := hYZ (embP x.1 (radius x.2))
    rw [piT_embP hx, rhoP_embP _ (radius_mem_Icc x.2)] at h2
    filter_upwards [hID P X hX W hW hW0 d k x.1 hx x.2, h2] with ω h1 h2
    exact ⟨h1, h2⟩
  have hdet := Metric.tendstoUniformlyOn_iff.1 (hDET W hW hW0 d k)
  filter_upwards [hgood] with ω hω n
  set ε : ℝ := 1 / ((n : ℝ) + 1) with hε
  have hε0 : 0 < ε := by positivity
  set Kc : Set (Fin 3 → ℝ) := Set.pi univ (fun _ : Fin 3 => Icc (-1 : ℝ) (T + 1)) with hKc
  have hKcc : IsCompact Kc := isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨η, hη, hU⟩ := Metric.uniformContinuousOn_iff.1
    (hKcc.uniformContinuousOn_of_continuous (hYc ω).continuousOn) (ε / 2) (by positivity)
  have hrad : Tendsto radius atTop (𝓝 0) := by
    unfold radius
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (hrad.eventually (gt_mem_nhds hη))
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 (hdet (ε / 4) (by positivity))
  refine ⟨max N1 N2, fun j hj j' hj' p hp => ?_⟩
  have hpT := triQ_subset_tri T hp
  have e1 : PhiW κ W d k j (X ω) p = X ω (muUS W d k p (radius j)) + detJ κ W d k p j :=
    (hω (⟨p, hp⟩, j)).1
  have e2 : PhiW κ W d k j' (X ω) p = X ω (muUS W d k p (radius j')) + detJ κ W d k p j' :=
    (hω (⟨p, hp⟩, j')).1
  have e3 : Y (embP p (radius j)) ω = X ω (muUS W d k p (radius j)) := (hω (⟨p, hp⟩, j)).2
  have e4 : Y (embP p (radius j')) ω = X ω (muUS W d k p (radius j')) := (hω (⟨p, hp⟩, j')).2
  -- the random part
  have r1 := hN1 j (le_of_max_le_left hj)
  have r2 := hN1 j' (le_of_max_le_left hj')
  have hj0 := radius_pos j
  have hj0' := radius_pos j'
  have hd : dist (embP p (radius j)) (embP p (radius j')) < η := by
    refine (dist_embP_le p _ _).trans_lt ?_
    rw [abs_lt]; constructor <;> linarith
  have hY := hU _ (embP_mem_box hpT (radius_mem_Icc j)) _ (embP_mem_box hpT (radius_mem_Icc j'))
    hd
  rw [Real.dist_eq, e3, e4] at hY
  -- the deterministic part
  have d1 := hN2 j (le_of_max_le_right hj) p hpT
  have d2 := hN2 j' (le_of_max_le_right hj') p hpT
  rw [Real.dist_eq] at d1 d2
  rw [e1, e2]
  have hdd : |detJ κ W d k p j - detJ κ W d k p j'| < ε / 2 := by
    rw [abs_lt] at d1 d2 ⊢; constructor <;> linarith
  rw [abs_lt] at hY hdd
  rw [abs_le]; constructor <;> linarith

end RegUnif
end QuantumZipper
