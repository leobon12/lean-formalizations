import QuantumZipper.Proofs.Zipper.XFlowUCTr
import QuantumZipper.Proofs.Zipper.UnifUCFix

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# XFLOW-UC: the fixed-driver `Γ⁰` node from Gaussian and deterministic inputs

**Main result** `xFlowFixedUCQAllStmt_of : FlowEnergyStmt → FlowAdmStmt → FlowIdentStmt →
FlowDetStmt → XFlowFixedUCQAllStmt`.

This is the D33 step `RegUnif.fixedUCStmt_of_id_det` / `RegUnif.exists_contMod_US`
(`UnifUCFix*.lean`) with the circle parameters `(d, r)` free: the Gaussian family
`(p, ρ) ↦ X(μ_{p,ρ})`, `μ_{p,ρ} = (ψ_u)_* (ν_p ⋆ fc(·, ρ))`, on `flowBox m × [0,1]` is
parametrized by `ℝ⁶` through the coordinatewise clamp (a `2`-Lipschitz retraction, `ptQ`,
`rhQ`), the energy Hölder bound `FlowEnergyStmt` gives the Gaussian moment bound
(`RegCont.lintegral_pow_diff_le`), and the six-parameter Kolmogorov–Čentsov theorem
`KolmN.exists_continuous_modification_N` (Revuz–Yor, 3rd ed., Ch. I, Thm (2.1)) a continuous
modification `Y`. On the countably many rational box points and scales,
`Φ^y_j = X(μ_{p,2^{-j}}) + det_j` (`FlowIdentStmt`, Duplantier–Sheffield, Invent. Math. 185
(2011), Prop. 3.1), the random part is uniformly Cauchy by uniform continuity of `Y` on a compact
cube, and the deterministic part by `FlowDetStmt`. Own bookkeeping, as in D33.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace F1

open RegCont TwoPoint GFFExist RegUnif

/-- The circle-smoothed pushed circle in free-field coordinates,
`μ_{p,ρ} = (ψ_u)_* (ν_p ⋆ fc(·, ρ))` (the D33 `muUS` with a general circle). -/
def flowMu (W : ℝ → ℝ) (p : ℝ × ℝ × ℂ × ℝ) (ρ : ℝ) : Measure ℂ :=
  (bindFc (flowNu W p) ρ).map (fwdMapInv W p.1)

/-- The deterministic part at scale `2^{-j}` (the D33 `detJ` with a general circle). -/
def flowDetJ (κ : ℝ) (W : ℝ → ℝ) (p : ℝ × ℝ × ℂ × ℝ) (j : ℕ) : ℝ :=
  ∫ z, (∫ v, PsiU κ W p.1 v ∂foldedCircle z (radius j)) ∂flowNu W p

/-- **(Energy node.)** For a Hölder driver on `[0, 2m+2]`, the Neumann energy of
`μ_{p,ρ} − μ_{p',ρ'}` is Hölder in `(p, ρ) ∈ flowBox m × [0,1]` (the D33 moduli E1
`energyRadStmt_holds`, E2 `energyParStmt_holds`, plus the circle modulus in `(d, r)`). -/
def FlowEnergyStmt : Prop :=
  ∀ m : ℕ, ∀ W : ℝ → ℝ, ∀ a CH : ℝ, HolderDrv W (2 * (m : ℝ) + 2) a CH →
    ∃ K c : ℝ, 0 ≤ K ∧ 0 < c ∧ ∀ p ∈ flowBox m, ∀ p' ∈ flowBox m,
      ∀ ρ ∈ Icc (0 : ℝ) 1, ∀ ρ' ∈ Icc (0 : ℝ) 1,
        |kernelCov2 neumannH (flowMu W p ρ, flowMu W p' ρ') (flowMu W p ρ, flowMu W p' ρ')| ≤
          K * (dist p p' + |ρ - ρ'|) ^ c

/-- **(Admissibility node.)** The measures `μ_{p,ρ}` are admissible probability measures (the
D33 `admissible_muUS` with a general circle). -/
def FlowAdmStmt : Prop :=
  ∀ W : ℝ → ℝ, Continuous W → W 0 = 0 → ∀ p ∈ flowPar, ∀ ρ ∈ Icc (0 : ℝ) 1,
    IsAdmissibleH (flowMu W p ρ) ∧ flowMu W p ρ univ = 1

/-- **(Identity node.)** At fixed parameters, a.s. `Φ^y_j(p) = X(μ_{p,2^{-j}}) + det_j(p)` (the
D33 `IdentStmt` with a general circle). -/
def FlowIdentStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → FieldSample),
    IsFreeGFFModConstH X P → ∀ W : ℝ → ℝ, Continuous W → W 0 = 0 → ∀ p ∈ flowPar, ∀ j : ℕ,
      ∀ᵐ ω ∂P, flowPhiY κ (X ω) W j p = X ω (flowMu W p (radius j)) + flowDetJ κ W p j

/-- **(Deterministic node.)** `det_j → ∫ Ψ_u dν_p` uniformly on every box (the D33
`DetUnifStmt` with a general circle). -/
def FlowDetStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ W : ℝ → ℝ, Continuous W → W 0 = 0 → ∀ m : ℕ,
    TendstoUniformlyOn (fun j p => flowDetJ κ W p j)
      (fun p => ∫ v, PsiU κ W p.1 v ∂flowNu W p) atTop (flowBox m)

/-! ## The clamp retraction of `ℝ⁶` onto `flowBox m × [0,1]` -/

/-- Clamp to `[a, b]`. -/
def clampF (a b x : ℝ) : ℝ := max a (min x b)

theorem clampF_mem {a b : ℝ} (hab : a ≤ b) (x : ℝ) : clampF a b x ∈ Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩

theorem clampF_of_mem {a b x : ℝ} (hx : x ∈ Icc a b) : clampF a b x = x := by
  unfold clampF; rw [min_eq_left hx.2, max_eq_right hx.1]

theorem abs_clampF_sub_le (a b x y : ℝ) : |clampF a b x - clampF a b y| ≤ |x - y| := by
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
  · rw [sub_self, abs_zero]; exact abs_nonneg _
  · refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le le_rfl ?_)
    rw [sub_self, abs_zero]; exact abs_nonneg _

/-- The box point of a vector of `ℝ⁶`. -/
def ptQ (m : ℕ) (q : Fin 6 → ℝ) : ℝ × ℝ × ℂ × ℝ :=
  (clampF 0 ((m : ℝ) + 1) (q 0), clampF 0 ((m : ℝ) + 1) (q 1),
    ⟨clampF (-((m : ℝ) + 1)) ((m : ℝ) + 1) (q 2), clampF 0 ((m : ℝ) + 1) (q 3)⟩,
    clampF (1 / ((m : ℝ) + 2)) ((m : ℝ) + 2) (q 4))

/-- The smoothing radius of a vector of `ℝ⁶`. -/
def rhQ (q : Fin 6 → ℝ) : ℝ := clampF 0 1 (q 5)

/-- The embedding of `flowBox m × [0,1]` into `ℝ⁶`. -/
def embQ (p : ℝ × ℝ × ℂ × ℝ) (ρ : ℝ) : Fin 6 → ℝ :=
  ![p.1, p.2.1, p.2.2.1.re, p.2.2.1.im, p.2.2.2, ρ]

theorem ptQ_mem (m : ℕ) (q : Fin 6 → ℝ) : ptQ m q ∈ flowBox m := by
  have h1 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
  have h2 : 1 / ((m : ℝ) + 2) ≤ (m : ℝ) + 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  exact ⟨clampF_mem h1 _, clampF_mem h1 _, clampF_mem (by linarith) _, clampF_mem h1 _,
    clampF_mem h2 _⟩

theorem rhQ_mem (q : Fin 6 → ℝ) : rhQ q ∈ Icc (0 : ℝ) 1 := clampF_mem zero_le_one _

theorem ptQ_embQ {m : ℕ} {p : ℝ × ℝ × ℂ × ℝ} (hp : p ∈ flowBox m) (ρ : ℝ) :
    ptQ m (embQ p ρ) = p := by
  obtain ⟨u, s, d, r⟩ := p
  simp only [ptQ, embQ, Matrix.cons_val_zero, Matrix.cons_val_one]
  have e2 : (![u, s, d.re, d.im, r, ρ] : Fin 6 → ℝ) 2 = d.re := rfl
  have e3 : (![u, s, d.re, d.im, r, ρ] : Fin 6 → ℝ) 3 = d.im := rfl
  have e4 : (![u, s, d.re, d.im, r, ρ] : Fin 6 → ℝ) 4 = r := rfl
  rw [e2, e3, e4, clampF_of_mem hp.1, clampF_of_mem hp.2.1, clampF_of_mem hp.2.2.1,
    clampF_of_mem hp.2.2.2.1, clampF_of_mem hp.2.2.2.2]

theorem rhQ_embQ (p : ℝ × ℝ × ℂ × ℝ) {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) : rhQ (embQ p ρ) = ρ := by
  have e : (embQ p ρ) 5 = ρ := rfl
  rw [rhQ, e, clampF_of_mem hρ]

theorem abs_coord6_le (q q' : Fin 6 → ℝ) (i : Fin 6) : |q i - q' i| ≤ ‖q - q'‖ := by
  have := norm_le_pi_norm (q - q') i
  rwa [Pi.sub_apply, Real.norm_eq_abs] at this

theorem dist_ptQ_le (m : ℕ) (q q' : Fin 6 → ℝ) : dist (ptQ m q) (ptQ m q') ≤ 2 * ‖q - q'‖ := by
  have hn := norm_nonneg (q - q')
  have c0 := (abs_clampF_sub_le 0 ((m : ℝ) + 1) (q 0) (q' 0)).trans (abs_coord6_le q q' 0)
  have c1 := (abs_clampF_sub_le 0 ((m : ℝ) + 1) (q 1) (q' 1)).trans (abs_coord6_le q q' 1)
  have c2 := (abs_clampF_sub_le (-((m : ℝ) + 1)) ((m : ℝ) + 1) (q 2) (q' 2)).trans
    (abs_coord6_le q q' 2)
  have c3 := (abs_clampF_sub_le 0 ((m : ℝ) + 1) (q 3) (q' 3)).trans (abs_coord6_le q q' 3)
  have c4 := (abs_clampF_sub_le (1 / ((m : ℝ) + 2)) ((m : ℝ) + 2) (q 4) (q' 4)).trans
    (abs_coord6_le q q' 4)
  have hd : dist (ptQ m q).2.2.1 (ptQ m q').2.2.1 ≤ 2 * ‖q - q'‖ := by
    rw [Complex.dist_eq]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.sub_re, Complex.sub_im]
    change |clampF (-((m : ℝ) + 1)) ((m : ℝ) + 1) (q 2) -
      clampF (-((m : ℝ) + 1)) ((m : ℝ) + 1) (q' 2)| +
      |clampF 0 ((m : ℝ) + 1) (q 3) - clampF 0 ((m : ℝ) + 1) (q' 3)| ≤ 2 * ‖q - q'‖
    linarith
  rw [Prod.dist_eq, Prod.dist_eq, Prod.dist_eq]
  refine max_le ?_ (max_le ?_ (max_le hd ?_))
  · rw [Real.dist_eq]; exact c0.trans (by linarith)
  · rw [Real.dist_eq]; exact c1.trans (by linarith)
  · rw [Real.dist_eq]; exact c4.trans (by linarith)

theorem abs_rhQ_sub_le (q q' : Fin 6 → ℝ) : |rhQ q - rhQ q'| ≤ ‖q - q'‖ :=
  (abs_clampF_sub_le 0 1 (q 5) (q' 5)).trans (abs_coord6_le q q' 5)

theorem dist_embQ_le (p : ℝ × ℝ × ℂ × ℝ) (ρ ρ' : ℝ) :
    dist (embQ p ρ) (embQ p ρ') ≤ |ρ - ρ'| := by
  refine (dist_pi_le_iff (abs_nonneg _)).2 fun i => ?_
  fin_cases i
  · simp [embQ]
  · simp [embQ]
  · simp [embQ]
  · simp [embQ]
  · simp [embQ]
  · simp [embQ, Real.dist_eq]

theorem embQ_mem_cube {m : ℕ} {p : ℝ × ℝ × ℂ × ℝ} (hp : p ∈ flowBox m) {ρ : ℝ}
    (hρ : ρ ∈ Icc (0 : ℝ) 1) :
    embQ p ρ ∈ Set.pi univ (fun _ : Fin 6 => Icc (-((m : ℝ) + 3)) ((m : ℝ) + 3)) := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hr1 : p.2.2.2 ≤ (m : ℝ) + 2 := hp.2.2.2.2.2
  have hr0 : 0 < p.2.2.2 := lt_of_lt_of_le (by positivity) hp.2.2.2.2.1
  intro i _
  fin_cases i
  · show -((m : ℝ) + 3) ≤ p.1 ∧ p.1 ≤ (m : ℝ) + 3
    exact ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
  · show -((m : ℝ) + 3) ≤ p.2.1 ∧ p.2.1 ≤ (m : ℝ) + 3
    exact ⟨by linarith [hp.2.1.1], by linarith [hp.2.1.2]⟩
  · show -((m : ℝ) + 3) ≤ p.2.2.1.re ∧ p.2.2.1.re ≤ (m : ℝ) + 3
    exact ⟨by linarith [hp.2.2.1.1], by linarith [hp.2.2.1.2]⟩
  · show -((m : ℝ) + 3) ≤ p.2.2.1.im ∧ p.2.2.1.im ≤ (m : ℝ) + 3
    exact ⟨by linarith [hp.2.2.2.1.1], by linarith [hp.2.2.2.1.2]⟩
  · show -((m : ℝ) + 3) ≤ p.2.2.2 ∧ p.2.2.2 ≤ (m : ℝ) + 3
    exact ⟨by linarith, by linarith⟩
  · show -((m : ℝ) + 3) ≤ ρ ∧ ρ ≤ (m : ℝ) + 3
    exact ⟨by linarith [hρ.1], by linarith [hρ.2]⟩

end F1
end QuantumZipper
