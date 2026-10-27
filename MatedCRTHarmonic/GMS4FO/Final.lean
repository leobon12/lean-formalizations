import MatedCRTHarmonic.GMS4FO.Assembly
import MatedCRTHarmonic.BundleSec4.Final

/-!
# [18] Proposition 4.10 for the γ-cone of the frozen coupling

Source: [18, Proposition 4.10].

* `le_cond_sum_of_forall_slice`: averaging a per-root bound over the marked root `z₀ ∼ λ[· | B_κ(0)]`;
* `target_subset_three`: for `|z₀| < κ`, failure of the source estimate for `(D, f)` forces failure of one of the
  three recentred good events ([18] (4.43)–(4.44), `globalGood_of_three`);
* `prop410Bad_le_at_mesh`: at a dyadic mesh `ε` (small enough), with `κ = ε^{α₀/(4q)}`,
  `P[∫_D f u^ε_* > A₀ ∫_D f + ε^α] ≤ 3 · E[μ_{h₀}(𝔻)/π]^{p}^{1/p} · (C₀^{1/q} ε^{α₀/(2q)})`;
* **`prop410At_of_inputs`**: `BundleSec4.Prop410At P η (3/4) 100` from the two named inputs `ZeroConeCase0At D (13/16)`
  and `Lemma43Measurable D`; the companion map conclusion and `exists_cellModel_of_matingOfTrees_of_inputs`:
  both conditional mated-CRT map conclusions from the two inputs, for every coupling.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4FO

open MatedCRTHarmonic LQGMetric LQGMetric.Blueprint MatedCRTHarmonic.MatedCRT

/-! ### Averaging over the marked root -/

/-- A bound valid for every root in `B_κ(0)` holds for the conditional rooted law. -/
theorem le_cond_sum_of_forall_slice {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {n : ℕ} (S : Fin n → Set (Ω × ℂ))
    {a : ℝ≥0∞} (h : ∀ z ∈ ball (0 : ℂ) κ, a ≤ ∑ j, P ((fun ω => (ω, z)) ⁻¹' S j)) :
    a ≤ ∑ j, (Canon.rootedLaw P)[|GMSCase1.smallRootEvent Ω κ] (S j) := by
  have hcond : (Canon.rootedLaw P)[|GMSCase1.smallRootEvent Ω κ] =
      P.prod (Canon.rootMeasure[|ball (0 : ℂ) κ]) :=
    GMSCase.prod_cond_univ_prod P Canon.rootMeasure (ball (0 : ℂ) κ)
  have hmass : Canon.rootMeasure (ball (0 : ℂ) κ) = ENNReal.ofReal (κ ^ 2) :=
    GMS4.GMSA.normalizedLebesgueOnRootingDisk_ball κ hκ0.le hκ1
  have hne : Canon.rootMeasure (ball (0 : ℂ) κ) ≠ 0 := by
    rw [hmass]
    exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have : IsProbabilityMeasure (Canon.rootMeasure[|ball (0 : ℂ) κ]) := cond_isProbabilityMeasure hne
  rw [hcond]
  have hT : ∀ j, (P.prod (Canon.rootMeasure[|ball (0 : ℂ) κ])) (S j) =
      ∫⁻ z, P ((fun ω => (ω, z)) ⁻¹' toMeasurable (P.prod (Canon.rootMeasure[|ball (0 : ℂ) κ])) (S j))
        ∂(Canon.rootMeasure[|ball (0 : ℂ) κ]) := fun j => by
    rw [← measure_toMeasurable (S j), Measure.prod_apply_symm (measurableSet_toMeasurable _ _)]
  simp_rw [hT]
  rw [← lintegral_finsetSum _ (fun j _ => measurable_measure_prodMk_right (measurableSet_toMeasurable _ _))]
  calc a = ∫⁻ _z, a ∂(Canon.rootMeasure[|ball (0 : ℂ) κ]) := by
        rw [lintegral_const, measure_univ, mul_one]
    _ ≤ _ := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_cond_mem (μ := Canon.rootMeasure) (measurableSet_ball (x := (0 : ℂ)) (ε := κ))]
        with z hz
      refine (h z hz).trans (Finset.sum_le_sum fun j _ => measure_mono ?_)
      exact preimage_mono (subset_toMeasurable _ _)

/-! ### The three recentred test pairs -/

/-- The tolerance of [18] (4.44) with `L = M = 100 ε^{−β}`, `κ = ε^ξ`, `vol D ≤ 2` and `vol B_κ(∂D) ≤ 100 κ`. -/
def tolTotal (ε α₀ β ξ A₀ : ℝ) : ℝ :=
  ε ^ α₀ * (100 * ε ^ (-β)) + 100 * ε ^ (-β) * ε ^ ξ * (A₀ * 2 + ε ^ α₀ * 1) +
    100 * ε ^ (-β) * (A₀ * (100 * ε ^ ξ) + ε ^ α₀ * 1)

/-- The three deterministic test domains of (4.44): `D`, `D`, `B_κ(∂D)`. -/
def pairDom (Dm : Set ℂ) (κ : ℝ) : Fin 3 → Set ℂ := ![Dm, Dm, thickening κ (frontier Dm)]

/-- The three test functions of (4.44): `f`, `1`, `1`. -/
def pairFun (f : ℂ → ℝ) : Fin 3 → ℂ → ℝ := ![f, fun _ => 1, fun _ => 1]

/-- Their sup bounds. -/
def pairBd (M : ℝ) : Fin 3 → ℝ := ![M, 1, 1]

theorem continuousOn_of_lipschitz {Dm : Set ℂ} {f : ℂ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ z ∈ Dm, ∀ w ∈ Dm, |f z - f w| ≤ L * dist z w) : ContinuousOn f Dm := by
  refine Metric.continuousOn_iff.2 fun z hz e he => ?_
  refine ⟨e / (L + 1), by positivity, fun w hw hwz => ?_⟩
  have hL1 : 0 < L + 1 := by linarith
  calc dist (f w) (f z) = |f w - f z| := Real.dist_eq _ _
    _ ≤ L * dist w z := hlip w hw z hz
    _ ≤ (L + 1) * dist w z := mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
    _ < (L + 1) * (e / (L + 1)) := mul_lt_mul_of_pos_left hwz hL1
    _ = e := by field_simp

theorem pairDom_subset {Dm : Set ℂ} (hDsub : Dm ⊆ ball (0 : ℂ) (3 / 4)) {κ : ℝ} (hκ : κ ≤ 1 / 32)
    (j : Fin 3) : pairDom Dm κ j ⊆ ball (0 : ℂ) (13 / 16) := by
  have h1 : Dm ⊆ ball (0 : ℂ) (13 / 16) := hDsub.trans (ball_subset_ball (by norm_num))
  fin_cases j
  · exact h1
  · exact h1
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.1 hx
    have hycl : y ∈ closedBall (0 : ℂ) (3 / 4) :=
      (closure_mono hDsub |>.trans closure_ball_subset_closedBall) (frontier_subset_closure hy)
    rw [mem_closedBall, dist_zero_right] at hycl
    rw [mem_ball, dist_zero_right]
    calc ‖x‖ ≤ ‖x - y‖ + ‖y‖ := norm_le_norm_sub_add x y
      _ < κ + 3 / 4 := by rw [← dist_eq_norm]; linarith
      _ ≤ 13 / 16 := by linarith

theorem isOpen_pairDom {Dm : Set ℂ} (hDo : IsOpen Dm) (κ : ℝ) (j : Fin 3) : IsOpen (pairDom Dm κ j) := by
  fin_cases j
  · exact hDo
  · exact hDo
  · exact isOpen_thickening

theorem continuousOn_pairFun {Dm : Set ℂ} {f : ℂ → ℝ} (hf : ContinuousOn f Dm) (κ : ℝ) (j : Fin 3) :
    ContinuousOn (pairFun f j) (pairDom Dm κ j) := by
  fin_cases j
  · exact hf
  · exact continuousOn_const
  · exact continuousOn_const

theorem pairFun_bounds {Dm : Set ℂ} {f : ℂ → ℝ} {M : ℝ} (hfb : ∀ z ∈ Dm, 0 ≤ f z ∧ f z ≤ M) (κ : ℝ)
    (j : Fin 3) : ∀ z ∈ pairDom Dm κ j, 0 ≤ pairFun f j z ∧ pairFun f j z ≤ pairBd M j := by
  fin_cases j
  · exact hfb
  · intro z _; norm_num [pairFun, pairBd]
  · intro z _; norm_num [pairFun, pairBd]

/-- **Failure of the source estimate forces failure of one recentred good event** ([18] (4.43)–(4.44)). -/
theorem exists_fail_of_target {c : C(ℝ, ℂ)} {ε : ℝ} (hε : 0 ≤ ε) {Dm : Set ℂ} (hDo : IsOpen Dm)
    {f : ℂ → ℝ} {M κ A₀ α₀ tol r : ℝ} {R : Set ℂ} (hM : 0 ≤ M) (hκ : 0 ≤ κ) (hA₀ : 0 ≤ A₀)
    (hfM : ∀ z ∈ Dm, f z ≤ M) (hlip : ∀ z ∈ Dm, ∀ w ∈ Dm, |f z - f w| ≤ M * dist z w)
    {z₀ : ℂ} (hz₀ : ‖z₀‖ < κ) (hVD : volume Dm ≤ ENNReal.ofReal 2)
    (hVT : volume (thickening κ (frontier Dm)) ≤ ENNReal.ofReal (100 * κ)) (hα₀ε : 0 ≤ ε ^ α₀)
    (htol : ε ^ α₀ * M + M * κ * (A₀ * 2 + ε ^ α₀ * 1) + M * (A₀ * (100 * κ) + ε ^ α₀ * 1) ≤ tol)
    (hbad : ¬ ((∫⁻ z in Dm, ENNReal.ofReal (f z) * GMS4b.uStar ε c z) ≤
      ENNReal.ofReal A₀ * (∫⁻ z in Dm, ENNReal.ofReal (f z)) + ENNReal.ofReal tol)) :
    ∃ j : Fin 3, ¬ GlobalGood c ε ((fun z => z - z₀) '' pairDom Dm κ j)
      (fun u => pairFun f j (u + z₀)) A₀ (ε ^ α₀ * pairBd M j) ((fun z => z - z₀) '' R) r := by
  by_contra hall
  push Not at hall
  have hU : AEMeasurable (fun u => GMS4b.uStar ε c u) volume := by
    have h := GMS4b.measurable_uStar hε
    have e : Measurable ((fun p : C(ℝ, ℂ) × ℂ => GMS4b.uStar ε p.1 p.2) ∘ fun u => (c, u)) :=
      h.comp (measurable_const.prodMk measurable_id)
    exact e.aemeasurable
  have hgood := globalGood_of_three (η := c) (R := (∅ : Set ℂ)) hDo hM hκ hM hA₀ (by norm_num)
    (by positivity) (mul_nonneg hα₀ε hM) (by simpa using hα₀ε) (by simpa using hα₀ε) hfM hlip hz₀ hU hVD hVT
    htol (empty_subset _) (hall 0) (hall 1) (hall 2)
  exact hbad hgood.2

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

theorem volume_le_two {Dm : Set ℂ} (hDsub : Dm ⊆ ball (0 : ℂ) (3 / 4)) : volume Dm ≤ ENNReal.ofReal 2 := by
  refine (measure_mono hDsub).trans ?_
  rw [Complex.volume_ball, ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_coe_nnreal,
    NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have := Real.pi_lt_d2
  nlinarith

theorem closedBall_subset_of_mem {z : ℂ} (hz : z ∈ ball (0 : ℂ) (13 / 16)) {r : ℝ} (hr : 4 * r ≤ 1 / 32) :
    closedBall z (4 * r) ⊆ ball (0 : ℂ) (7 / 8) := by
  intro w hw
  rw [mem_closedBall] at hw
  rw [mem_ball, dist_zero_right] at hz ⊢
  calc ‖w‖ ≤ ‖w - z‖ + ‖z‖ := norm_le_norm_sub_add w z
    _ = dist w z + ‖z‖ := by rw [dist_eq_norm]
    _ < 7 / 8 := by linarith

/-- **[18] Proposition 4.10 at one dyadic mesh** (for small meshes), from the two named inputs. -/
theorem prop410Bad_le_at_mesh (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) [Fact (0 < 2 * Real.pi * igChi γ)] (hL : Lemma43Measurable D)
    {q α₀ A₀ C₀ : ℝ} (hA₀ : 0 ≤ A₀) (hC₀ : 0 ≤ C₀)
    (h0 : ∀ k : ℕ, 1 ≤ k → ∀ (Dm : Set ℂ) (g : ℂ → ℝ) (M : ℝ), IsOpen Dm →
      Dm ⊆ ball (0 : ℂ) (13 / 16) → ContinuousOn g Dm → (∀ z ∈ Dm, 0 ≤ g z ∧ g z ≤ M) →
        P {ω | ¬ GlobalGood (η₀ ω) (CellFamily.mesh k) Dm g A₀ (CellFamily.mesh k ^ α₀ * M)
          (ball (0 : ℂ) (13 / 16)) (CellFamily.mesh k ^ q)} ≤ ENNReal.ofReal (C₀ * CellFamily.mesh k ^ α₀))
    {p q' : ℝ} (hpq : p.HolderConjugate q') {k : ℕ} (hk : 1 ≤ k) {β α : ℝ} {Dm : Set ℂ}
    {f : ℂ → ℝ} (hadm : GMS4.Prop210Admissible (CellFamily.mesh k) (3 / 4) 100 β Dm f)
    (hκs : CellFamily.mesh k ^ (α₀ / (4 * q')) ≤ 1 / 32) (hrs : 4 * CellFamily.mesh k ^ q ≤ 1 / 32)
    (htol : tolTotal (CellFamily.mesh k) α₀ β (α₀ / (4 * q')) A₀ ≤ CellFamily.mesh k ^ α) :
    P (BundleSec4.Prop410Bad η (CellFamily.mesh k) Dm f A₀ (CellFamily.mesh k ^ α)) ≤
      3 * (GMSCase1.case1Moment D hγ p ^ (1 / p) *
        ENNReal.ofReal (C₀ ^ (1 / q') * CellFamily.mesh k ^ (α₀ / (2 * q')))) := by
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨hε0, hε1, -, -, -, -, hDo, -, hDsub, hthick, hfb, hlip⟩ := hadm
  have hq'0 : 0 < q' := hpq.symm.pos
  have hκ0 : 0 < CellFamily.mesh k ^ (α₀ / (4 * q')) := Real.rpow_pos_of_pos hε0 _
  have hκ1 : CellFamily.mesh k ^ (α₀ / (4 * q')) ≤ 1 := hκs.trans (by norm_num)
  have hr0 : 0 ≤ CellFamily.mesh k ^ q := (Real.rpow_pos_of_pos hε0 _).le
  have hM0 : 0 ≤ 100 * CellFamily.mesh k ^ (-β) := by positivity
  have hα₀ε : 0 ≤ CellFamily.mesh k ^ α₀ := (Real.rpow_pos_of_pos hε0 _).le
  have hRV : ∀ z ∈ ball (0 : ℂ) (13 / 16), closedBall z (4 * CellFamily.mesh k ^ q) ⊆ ball (0 : ℂ) (7 / 8) :=
    fun z hz => closedBall_subset_of_mem hz hrs
  have hfM : ∀ z ∈ Dm, f z ≤ 100 * CellFamily.mesh k ^ (-β) := fun z hz => (hfb z hz).2
  have hfc : ContinuousOn f Dm := continuousOn_of_lipschitz hM0 hlip
  have hVT : volume (thickening (CellFamily.mesh k ^ (α₀ / (4 * q'))) (frontier Dm)) ≤
      ENNReal.ofReal (100 * CellFamily.mesh k ^ (α₀ / (4 * q'))) :=
    hthick _ ⟨hκ0, lt_of_le_of_lt hκs (by norm_num)⟩
  -- the three local failure events on `Ω × ℂ`
  let S : Fin 3 → Set (Ω × ℂ) := fun j => {v | (restrictTo (ballO (0 : ℂ) (7 / 8))
    (GMSCase1.wpField X₀ v.1 + CellScaling.ofFunC (fun w => -γ * Real.log ‖w - v.2‖)), ηL v.1) ∈
      failSet γ (ballO (0 : ℂ) (7 / 8)) (CellFamily.mesh k) (pairDom Dm (CellFamily.mesh k ^ (α₀ / (4 * q'))) j)
        (pairFun f j) A₀ (CellFamily.mesh k ^ α₀ * pairBd (100 * CellFamily.mesh k ^ (-β)) j)
        (ball (0 : ℂ) (13 / 16)) (CellFamily.mesh k ^ q)}
  -- step A: one root
  have hA : ∀ z₀ ∈ ball (0 : ℂ) (CellFamily.mesh k ^ (α₀ / (4 * q'))),
      P (BundleSec4.Prop410Bad η (CellFamily.mesh k) Dm f A₀ (CellFamily.mesh k ^ α)) ≤
        ∑ j, P ((fun ω => (ω, z₀)) ⁻¹' S j) := by
    intro z₀ hz₀
    have hz₀' : ‖z₀‖ < CellFamily.mesh k ^ (α₀ / (4 * q')) := by rwa [mem_ball, dist_zero_right] at hz₀
    have hsub : BundleSec4.Prop410Bad η (CellFamily.mesh k) Dm f A₀ (CellFamily.mesh k ^ α) ⊆
        ⋃ j : Fin 3, {ω | ¬ GlobalGood (η ω) (CellFamily.mesh k)
          ((fun z => z - z₀) '' pairDom Dm (CellFamily.mesh k ^ (α₀ / (4 * q'))) j)
          (fun u => pairFun f j (u + z₀)) A₀ (CellFamily.mesh k ^ α₀ * pairBd (100 * CellFamily.mesh k ^ (-β)) j)
          ((fun z => z - z₀) '' ball (0 : ℂ) (13 / 16)) (CellFamily.mesh k ^ q)} := by
      intro ω hω
      obtain ⟨j, hj⟩ := exists_fail_of_target (c := η ω) (R := ball (0 : ℂ) (13 / 16))
        (r := CellFamily.mesh k ^ q) hε0.le hDo hM0 hκ0.le hA₀ hfM hlip hz₀' (volume_le_two hDsub) hVT hα₀ε
        (htol.trans' (le_of_eq (by unfold tolTotal; ring))) hω
      exact mem_iUnion.2 ⟨j, hj⟩
    refine (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans
      (Finset.sum_le_sum fun j _ => ?_))
    have hnz : ‖z₀‖ + 15 / 16 ≤ 1 := by linarith
    have hr01 : 7 / 8 + ‖z₀‖ ≤ 15 / 16 := by linarith
    exact cone_le_case2 D hγ hL (r₀ := 7 / 8) (by norm_num) hnz hr01 hε0
      hr0 (pairDom_subset hDsub hκs j) hRV ((isOpen_pairDom hDo _ j).measurableSet)
  -- step B: average over the root
  have hB := le_cond_sum_of_forall_slice P hκ0 hκ1 S hA
  refine hB.trans ?_
  -- step C: Cases 0–2 for each pair
  have hC : ∀ j : Fin 3, (Canon.rootedLaw P)[|GMSCase1.smallRootEvent Ω (CellFamily.mesh k ^ (α₀ / (4 * q')))]
      (S j) ≤ GMSCase1.case1Moment D hγ p ^ (1 / p) *
        ENNReal.ofReal (C₀ ^ (1 / q') * CellFamily.mesh k ^ (α₀ / (2 * q'))) := by
    intro j
    have hbad0 := (zeroCone_failSet_le D hγ (V := ballO (0 : ℂ) (7 / 8)) isBounded_ball hε0 hr0
      (pairDom_subset hDsub hκs j) hRV ((isOpen_pairDom hDo _ j).measurableSet)
      (g := pairFun f j) (A := A₀) (tol := CellFamily.mesh k ^ α₀ * pairBd (100 * CellFamily.mesh k ^ (-β)) j)).trans
      (h0 k hk _ _ _ (isOpen_pairDom hDo _ j) (pairDom_subset hDsub hκs j) (continuousOn_pairFun hfc _ j)
        (pairFun_bounds hfb _ j))
    have h := case2_smallRoot_failSet_le D hγ hL (V₀ := ballO (0 : ℂ) (7 / 8))
      (ball_subset_ball (by norm_num)) hpq hκ0.le hκ1 hbad0
    rw [mul_div_assoc, GMSCase1.case1_rate_div_eq hC₀ hε0 hq'0] at h
    exact h
  calc ∑ j, (Canon.rootedLaw P)[|GMSCase1.smallRootEvent Ω (CellFamily.mesh k ^ (α₀ / (4 * q')))] (S j)
      ≤ ∑ _j : Fin 3, GMSCase1.case1Moment D hγ p ^ (1 / p) *
          ENNReal.ofReal (C₀ ^ (1 / q') * CellFamily.mesh k ^ (α₀ / (2 * q'))) :=
        Finset.sum_le_sum fun j _ => hC j
    _ = _ := by simp

end Coupling

/-! ### Numerics -/

theorem mesh_rpow_eq (k : ℕ) (x : ℝ) : CellFamily.mesh k ^ x = ((2 : ℝ) ^ (-x)) ^ k := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  rw [CellFamily.mesh, ← Real.rpow_intCast, ← Real.rpow_mul h2, ← Real.rpow_natCast, ← Real.rpow_mul h2]
  congr 1
  push_cast
  ring

theorem eventually_mesh_rpow_le {x c : ℝ} (hx : 0 < x) (hc : 0 < c) :
    ∀ᶠ k : ℕ in atTop, CellFamily.mesh k ^ x ≤ c := by
  have h0 : 0 ≤ (2 : ℝ) ^ (-x) := by positivity
  have h1 : (2 : ℝ) ^ (-x) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1
  filter_upwards [ht.eventually (eventually_le_nhds hc)] with k hk
  rw [mesh_rpow_eq]
  exact hk

/-- The tolerance of (4.44) is `O(ε^{3ξ/4})` when `β = ξ/4 ≤ α₀/4`. -/
theorem tolTotal_le {ε α₀ ξ A₀ : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hξ0 : 0 ≤ ξ) (hξα : ξ ≤ α₀) :
    tolTotal ε α₀ (ξ / 4) ξ A₀ ≤ (300 + 10200 * A₀) * ε ^ (3 * ξ / 4) := by
  have hea : ε ^ (-(ξ / 4)) * ε ^ ξ = ε ^ (3 * ξ / 4) := by
    rw [← Real.rpow_add hε0]; congr 1; ring
  have hαe : ε ^ α₀ * ε ^ (-(ξ / 4)) ≤ ε ^ (3 * ξ / 4) := by
    rw [← Real.rpow_add hε0]
    exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by linarith)
  have hα1 : ε ^ α₀ ≤ 1 := Real.rpow_le_one hε0.le hε1 (by linarith [hξα, hξ0])
  have hα0 : 0 ≤ ε ^ α₀ := (Real.rpow_pos_of_pos hε0 _).le
  have ha0 : 0 ≤ ε ^ (3 * ξ / 4) := (Real.rpow_pos_of_pos hε0 _).le
  have key : tolTotal ε α₀ (ξ / 4) ξ A₀ = 100 * (ε ^ α₀ * ε ^ (-(ξ / 4))) +
      100 * (ε ^ (-(ξ / 4)) * ε ^ ξ) * (A₀ * 2 + ε ^ α₀) +
      10000 * A₀ * (ε ^ (-(ξ / 4)) * ε ^ ξ) + 100 * (ε ^ α₀ * ε ^ (-(ξ / 4))) := by
    unfold tolTotal; ring
  rw [key, hea]
  nlinarith [mul_le_mul_of_nonneg_left hα1 ha0]

theorem mesh_anti {k k₀ : ℕ} (h : k ≤ k₀) : CellFamily.mesh k₀ ≤ CellFamily.mesh k := by
  unfold CellFamily.mesh
  exact zpow_le_zpow_right₀ (by norm_num) (by omega)

/-! ### The final theorem -/

section Final

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- **[18] Proposition 4.10 at `(ρ, C) = (3/4, 100)` for the γ-cone curve `η` of the frozen coupling**, from the two
named inputs: (4.40) for the 0-cone at radius `13/16` and the measurable form of Lemma 4.3. -/
theorem prop410At_of_inputs (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (h0 : ZeroConeCase0At D (13 / 16)) (hL : Lemma43Measurable D) :
    BundleSec4.Prop410At P η (3 / 4) 100 := by
  have : Fact (0 < 2 * Real.pi * igChi γ) := ⟨GMSCase.igPeriod_pos D⟩
  have hP : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨q, α₀, A₀, C₀, hq, hα₀, hA₀, hC₀, h0⟩ := h0
  obtain ⟨p, hp1, hp4⟩ := GMSCase1.exists_case1_exponent hγ
  have hpq : p.HolderConjugate p.conjExponent := Real.HolderConjugate.conjExponent hp1
  set q' := p.conjExponent with hq'def
  have hq'0 : 0 < q' := hpq.symm.pos
  have hq'1 : 1 < q' := hpq.symm.lt
  have hMfin : GMSCase1.case1Moment D hγ p ^ (1 / p) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity)
      (GMSCase1.case1Moment_lt_top D hγ (by linarith) hp4).ne
  set ξ := α₀ / (4 * q') with hξdef
  have hξ : 0 < ξ := by positivity
  have hξα : ξ ≤ α₀ := by
    rw [hξdef, div_le_iff₀ (by positivity)]
    nlinarith
  have h2ξ : α₀ / (2 * q') = 2 * ξ := by rw [hξdef]; field_simp; ring
  set K := 300 + 10200 * A₀ with hK
  have hK0 : 0 < K := by positivity
  -- small meshes
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 ((eventually_mesh_rpow_le hξ (by norm_num : (0 : ℝ) < 1 / 32)).and
    ((eventually_mesh_rpow_le hq (by norm_num : (0 : ℝ) < 1 / 128)).and
      (eventually_mesh_rpow_le (by positivity : 0 < ξ / 2) (inv_pos.2 hK0))))
  set Mreal := (GMSCase1.case1Moment D hγ p ^ (1 / p)).toReal with hMreal
  set Cfail := max (3 * Mreal * C₀ ^ (1 / q')) ((CellFamily.mesh k₀ ^ (ξ / 4))⁻¹) with hCfail
  have hCinv : 0 ≤ (CellFamily.mesh k₀ ^ (ξ / 4))⁻¹ :=
    (inv_pos.2 (Real.rpow_pos_of_pos (BundleSec4.bundle_mesh_pos k₀) _)).le
  refine ⟨ξ / 4, A₀, ξ / 4, Cfail, by positivity, by positivity, hA₀,
    le_max_of_le_right hCinv, fun k Dm f hadm => ?_⟩
  have hε0 : 0 < CellFamily.mesh k := hadm.1
  have hε1 : CellFamily.mesh k < 1 := hadm.2.1
  have hk1 : 1 ≤ k := by
    by_contra hk
    have : k = 0 := by omega
    subst this
    simp [CellFamily.mesh] at hε1
  rcases le_or_gt k₀ k with hk | hk
  · obtain ⟨hκs, hrs, hKs⟩ := hk₀ k hk
    have htol : tolTotal (CellFamily.mesh k) α₀ (ξ / 4) ξ A₀ ≤ CellFamily.mesh k ^ (ξ / 4) := by
      refine (tolTotal_le hε0 hε1.le hξ.le hξα).trans ?_
      have hsplit : CellFamily.mesh k ^ (3 * ξ / 4) = CellFamily.mesh k ^ (ξ / 2) * CellFamily.mesh k ^ (ξ / 4) := by
        rw [← Real.rpow_add hε0]; congr 1; ring
      rw [hsplit, ← mul_assoc]
      have h1 : K * CellFamily.mesh k ^ (ξ / 2) ≤ 1 := by
        have := mul_le_mul_of_nonneg_left hKs hK0.le
        rwa [mul_inv_cancel₀ hK0.ne'] at this
      calc K * CellFamily.mesh k ^ (ξ / 2) * CellFamily.mesh k ^ (ξ / 4)
          ≤ 1 * CellFamily.mesh k ^ (ξ / 4) :=
            mul_le_mul_of_nonneg_right h1 (Real.rpow_pos_of_pos hε0 _).le
        _ = CellFamily.mesh k ^ (ξ / 4) := one_mul _
    have hbound := prop410Bad_le_at_mesh D hγ hL hA₀ hC₀ h0 hpq hk1 hadm hκs (by linarith) htol
    refine hbound.trans ?_
    rw [h2ξ, ← ENNReal.ofReal_toReal hMfin, ← hMreal, ← ENNReal.ofReal_mul (by positivity),
      show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hpow : CellFamily.mesh k ^ (2 * ξ) ≤ CellFamily.mesh k ^ (ξ / 4) :=
      Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (by linarith)
    have hM0 : 0 ≤ Mreal := ENNReal.toReal_nonneg
    have hC0' : 0 ≤ C₀ ^ (1 / q') := Real.rpow_nonneg hC₀ _
    calc 3 * (Mreal * (C₀ ^ (1 / q') * CellFamily.mesh k ^ (2 * ξ)))
        = 3 * Mreal * C₀ ^ (1 / q') * CellFamily.mesh k ^ (2 * ξ) := by ring
      _ ≤ Cfail * CellFamily.mesh k ^ (ξ / 4) :=
        mul_le_mul (le_max_left _ _) hpow (Real.rpow_pos_of_pos hε0 _).le
          (le_max_of_le_right hCinv)
  · -- the finitely many large meshes: the bound exceeds one
    have hmesh : CellFamily.mesh k₀ ≤ CellFamily.mesh k := mesh_anti hk.le
    have hpos : 0 < CellFamily.mesh k₀ ^ (ξ / 4) := Real.rpow_pos_of_pos (BundleSec4.bundle_mesh_pos k₀) _
    have hge : CellFamily.mesh k₀ ^ (ξ / 4) ≤ CellFamily.mesh k ^ (ξ / 4) :=
      Real.rpow_le_rpow (BundleSec4.bundle_mesh_pos k₀).le hmesh (by positivity)
    calc P (BundleSec4.Prop410Bad η (CellFamily.mesh k) Dm f A₀ (CellFamily.mesh k ^ (ξ / 4))) ≤ 1 := prob_le_one
      _ = ENNReal.ofReal ((CellFamily.mesh k₀ ^ (ξ / 4))⁻¹ * CellFamily.mesh k₀ ^ (ξ / 4)) := by
        rw [inv_mul_cancel₀ hpos.ne', ENNReal.ofReal_one]
      _ ≤ ENNReal.ofReal (Cfail * CellFamily.mesh k ^ (ξ / 4)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul (le_max_right _ _) hge hpos.le
          (le_max_of_le_right hCinv))

end Final

/-- The two named inputs for every frozen coupling. -/
def InputsForAllBundles : Prop :=
  ∀ (γ : ℝ) (_ : γ ∈ Ioo (0 : ℝ) 2) (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω)
    (P : Measure Ω) (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
    (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2)
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm),
      ZeroConeCase0At D (13 / 16) ∧ Lemma43Measurable D

/-- **the target `Prop410AtForAllBundles` from the two named inputs.** -/
theorem prop410AtForAllBundles_of_inputs (h : InputsForAllBundles) : BundleSec4.Prop410AtForAllBundles :=
  fun γ hγ Ω mΩ hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D =>
    prop410At_of_inputs D hγ (h γ hγ Ω mΩ hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D).1
      (h γ hγ Ω mΩ hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D).2

/-- **`exists_cellModel_of_matingOfTrees` (frozen v3 type) from the two named inputs.** -/
theorem exists_cellModel_of_matingOfTrees_of_inputs (h : InputsForAllBundles) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → MatedCRT.MatingOfTreesInput γ → MatedCRT.CellModelExists γ :=
  BundleSec4.exists_cellModel_of_matingOfTrees_of_prop410AtForAllBundles (prop410AtForAllBundles_of_inputs h)

end MatedCRTHarmonic.GMS4FO
