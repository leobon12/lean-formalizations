import MatedCRTHarmonic.GMSMain.T13Path

/-!
# The Dirichlet energy of the discrete harmonic extension of (1.6), deterministic form

Source: [18] (1.5)–(1.7) and Theorem 1.3, the proof of
Theorem 3.2 from Lemma 3.3 (`[18]`, Dirichlet's principle) using the energy estimate.

For a cellular embedding `H` of `G`, an open bounded `D` and `f` continuous on `D̄`:

* `IsGMSDirichletSolution H D f fε` — `fε` has the boundary values (1.6),
  `fε(x) = sup_{z ∈ H_x ∩ ∂D} f(z)` for `x ∈ V(∂D)`, and is discrete harmonic at the interior vertices
  `x ∈ V(D) \ V(∂D)` (the defining properties of [18]'s `f_ε`, `[18]`);
* `t13_exists_refPoint` — each cell meeting `D̄` has a point of `D̄` at which `f` attains the boundary value (1.6);
* **`t13_energy_le_of_lipschitz`** — if `f` is `L`-Lipschitz on `D̄`, then
  `Energy(fε; G(D)) ≤ 2 L² ∑_{x ∈ V(D)} deg(x) diam(H_x)²` (Dirichlet's principle with reference points in `D̄`,
  the edge estimate `|f(p x) − f(p y)| ≤ L (diam H_x + diam H_y)`);
* `t13_sum_le_lintegral_uDens` — `∑_{x ∈ S} diam(H_x)² deg(x) ≤ ∫_Ω u^ε` when the cells of `S` lie in `Ω`;
* **`t13_energy_le_on_event`** — on the event of [18] Lemma 2.7 on `B_{ρ₁}(0)` (diameters `≤ δ`) and of
  [18] Proposition 2.10 for the single test `(B_{ρ₁}(0), 1)`, with `D ⊂ B_ρ(0)`, `ρ + δ ≤ ρ₁ ≤ 1`:
  `Energy(fε; G(D)) ≤ 2 L² (4A + η)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal Classical

namespace MatedCRTHarmonic.GMSMain

open MatedCRTHarmonic GMS3 LFMultigraph Harmonic

variable {V E : Type*} {G : LFMultigraph V E} {o : V} (H : CellularEmbedding G o)

/-- **[18]'s discrete harmonic function `f_ε`**: the boundary values (1.6)
`fε(x) = sup_{z ∈ H_x ∩ ∂D} f(z)` on `V(∂D)` and discrete harmonicity on `V(D) \ V(∂D)`. -/
def IsGMSDirichletSolution (D : Set ℂ) (f : ℂ → ℝ) (fε : V → ℝ) : Prop :=
  (∀ x ∈ vFin H D, (H.cell x ∩ frontier D).Nonempty → fε x = sSup (f '' (H.cell x ∩ frontier D))) ∧
    ∀ x ∈ vFin H D, ¬ (H.cell x ∩ frontier D).Nonempty → lap G fε x = 0

/-- A reference point of a cell meeting `D̄`: in `H_x ∩ D̄`, and a maximizer of `f` on `H_x ∩ ∂D` when this set is
nonempty. -/
theorem t13_exists_refPoint {D : Set ℂ} {f : ℂ → ℝ} (hfc : ContinuousOn f (closure D))
    (x : V) (hx : (H.cell x ∩ closure D).Nonempty) :
    ∃ z ∈ H.cell x ∩ closure D,
      ((H.cell x ∩ frontier D).Nonempty → f z = sSup (f '' (H.cell x ∩ frontier D))) := by
  by_cases hb : (H.cell x ∩ frontier D).Nonempty
  · have hK : IsCompact (H.cell x ∩ frontier D) := (H.isCompact_cell x).inter_right isClosed_frontier
    have hfK : ContinuousOn f (H.cell x ∩ frontier D) :=
      hfc.mono (inter_subset_right.trans frontier_subset_closure)
    obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn hb hfK
    refine ⟨z, ⟨hz.1, frontier_subset_closure hz.2⟩, fun _ => ?_⟩
    refine (IsGreatest.csSup_eq ⟨mem_image_of_mem f hz, ?_⟩).symm
    rintro _ ⟨w, hw, rfl⟩
    exact hmax hw
  · obtain ⟨z, hz⟩ := hx
    exact ⟨z, hz, fun h => absurd h hb⟩

/-- **The Dirichlet energy of `f_ε` for an `L`-Lipschitz `f` on `D̄`** (Dirichlet's principle with reference points
in `D̄` and the edge estimate). -/
theorem t13_energy_le_of_lipschitz {D : Set ℂ} (hDo : IsOpen D) (hDb : Bornology.IsBounded D)
    {f : ℂ → ℝ} (hfc : ContinuousOn f (closure D)) {L : ℝ} (hL : 0 ≤ L)
    (hfL : ∀ z ∈ closure D, ∀ w ∈ closure D, |f z - f w| ≤ L * dist z w)
    {fε : V → ℝ} (hsol : IsGMSDirichletSolution H D f fε) :
    energy G (vFin H D) fε ≤ 2 * L ^ 2 * ∑ x ∈ vFin H D, (G.deg x : ℝ) * cellDiam H x ^ 2 := by
  -- reference points
  let p : V → ℂ := fun x =>
    if hx : (H.cell x ∩ closure D).Nonempty then (t13_exists_refPoint H hfc x hx).choose
    else (cell_nonempty H x).choose
  have hp : ∀ x, p x ∈ H.cell x := by
    intro x
    by_cases hx : (H.cell x ∩ closure D).Nonempty
    · simp only [p, dite_eq_left hx]
      exact (t13_exists_refPoint H hfc x hx).choose_spec.1.1
    · simp only [p, dite_eq_right hx]
      exact (cell_nonempty H x).choose_spec
  have hxcl : ∀ x ∈ vFin H D, (H.cell x ∩ closure D).Nonempty := by
    intro x hx
    obtain ⟨z, hz⟩ := (mem_vFin H hDb).1 hx
    exact ⟨z, hz.1, subset_closure hz.2⟩
  have hpcl : ∀ x ∈ vFin H D, p x ∈ closure D := by
    intro x hx
    simp only [p, dite_eq_left (hxcl x hx)]
    exact (t13_exists_refPoint H hfc x (hxcl x hx)).choose_spec.1.2
  have hpbd : ∀ x ∈ vFin H D, (H.cell x ∩ frontier D).Nonempty →
      f (p x) = sSup (f '' (H.cell x ∩ frontier D)) := by
    intro x hx hb
    simp only [p, dite_eq_left (hxcl x hx)]
    exact (t13_exists_refPoint H hfc x (hxcl x hx)).choose_spec.2 hb
  -- Dirichlet's principle
  have hDir : energy G (vFin H D) fε ≤ energy G (vFin H D) (f ∘ p) :=
    energy_le_of_lap_eq_zero H hDo hDb (f ∘ p) fε hsol.2
      fun x hx hb => (hsol.1 x hx hb).trans (hpbd x hx hb).symm
  -- the edge estimate
  set φ : V → ℝ := fun x => 2 * L ^ 2 * cellDiam H x ^ 2 with hφ
  have hφ0 : ∀ x ∈ vFin H D, 0 ≤ φ x := fun x _ => by positivity
  have hedge : energy G (vFin H D) (f ∘ p) ≤
      ∑ e ∈ edgesIn G (vFin H D), (φ (G.src e) + φ (G.tgt e)) := by
    unfold energy
    refine Finset.sum_le_sum fun e he => ?_
    rw [mem_edgesIn] at he
    simp only [Function.comp]
    by_cases hloop : G.src e = G.tgt e
    · rw [hloop, sub_self, sq, mul_zero]
      exact add_nonneg (hφ0 _ (hloop ▸ he.1)) (hφ0 _ he.2)
    · have hadj := adj_of_edge G hloop
      have hd := dist_le_cellDiam_add_of_adj H hadj (hp (G.src e)) (hp (G.tgt e))
      have hf := hfL _ (hpcl _ he.1) _ (hpcl _ he.2)
      have hdx := cellDiam_nonneg H (G.src e)
      have hdy := cellDiam_nonneg H (G.tgt e)
      have habs : |f (p (G.src e)) - f (p (G.tgt e))| ≤
          L * (cellDiam H (G.src e) + cellDiam H (G.tgt e)) :=
        hf.trans (mul_le_mul_of_nonneg_left hd hL)
      have hsq : (f (p (G.src e)) - f (p (G.tgt e))) ^ 2 ≤
          (L * (cellDiam H (G.src e) + cellDiam H (G.tgt e))) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) habs 2
      refine hsq.trans ?_
      simp only [hφ]
      nlinarith [sq_nonneg (cellDiam H (G.src e) - cellDiam H (G.tgt e)), sq_nonneg L,
        mul_nonneg (sq_nonneg L) (sq_nonneg (cellDiam H (G.src e) - cellDiam H (G.tgt e)))]
  calc energy G (vFin H D) fε ≤ energy G (vFin H D) (f ∘ p) := hDir
    _ ≤ ∑ e ∈ edgesIn G (vFin H D), (φ (G.src e) + φ (G.tgt e)) := hedge
    _ ≤ ∑ x ∈ vFin H D, (G.deg x : ℝ) * φ x := sum_edgesIn_add_le G _ hφ0
    _ = 2 * L ^ 2 * ∑ x ∈ vFin H D, (G.deg x : ℝ) * cellDiam H x ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [hφ]
        ring

/-- `∑_{x ∈ S} diam(H_x)² deg(x) ≤ ∫_Ω u^ε` when every cell of `S` lies in `Ω` ([18] (3.5)). -/
theorem t13_sum_le_lintegral_uDens (S : Finset V) {Ω : Set ℂ} (hS : ∀ x ∈ S, H.cell x ⊆ Ω) :
    ∑ x ∈ S, ENNReal.ofReal (cellDiam H x ^ 2 * G.deg x) ≤ ∫⁻ z in Ω, uDens H z := by
  calc ∑ x ∈ S, ENNReal.ofReal (cellDiam H x ^ 2 * G.deg x)
      = ∑ x ∈ S, ∫⁻ z in H.cell x, uDens H z :=
        Finset.sum_congr rfl fun x _ => (setLIntegral_cell_uDens H x).symm
    _ = ∫⁻ z in ⋃ x ∈ S, H.cell x, uDens H z := (setLIntegral_biUnion_cell H S _).symm
    _ ≤ ∫⁻ z in Ω, uDens H z := lintegral_mono_set (iUnion₂_subset hS)

/-- **Deterministic core of [18] Theorem 1.3**: on the Lemma 2.7 event on `B_{ρ₁}(0)` (cell diameters `≤ δ`) and the
Proposition 2.10 bound for `(B_{ρ₁}(0), 1)` (`∫_{B_{ρ₁}} u^ε ≤ A area + η`), for `D ⊂ B_ρ(0)` open,
`ρ + δ ≤ ρ₁ ≤ 1`, `f` `L`-Lipschitz on `D̄`, the function `f_ε` has `Energy(f_ε; G(D)) ≤ 2L²(4A + η)`. -/
theorem t13_energy_le_on_event {D : Set ℂ} (hDo : IsOpen D) {ρ ρ₁ δ A η : ℝ}
    (hDsub : D ⊆ ball (0 : ℂ) ρ) (hρδ : ρ + δ ≤ ρ₁) (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ ≤ 1) (hδ : 0 ≤ δ) (hA : 0 ≤ A) (hη : 0 ≤ η)
    {f : ℂ → ℝ} (hfc : ContinuousOn f (closure D)) {L : ℝ} (hL : 0 ≤ L)
    (hfL : ∀ z ∈ closure D, ∀ w ∈ closure D, |f z - f w| ≤ L * dist z w)
    (h27 : CellDiamBound H ρ₁ δ) (h210 : Prop210Bound H (ball (0 : ℂ) ρ₁) (fun _ => 1) A η)
    {fε : V → ℝ} (hsol : IsGMSDirichletSolution H D f fε) :
    energy G (vFin H D) fε ≤ 2 * L ^ 2 * (4 * A + η) := by
  have hDb : Bornology.IsBounded D := isBounded_ball.subset hDsub
  refine (t13_energy_le_of_lipschitz H hDo hDb hfc hL hfL hsol).trans
    (mul_le_mul_of_nonneg_left ?_ (by positivity))
  -- the cells of `V(D)` lie in `B_{ρ₁}(0)`
  have hcells : ∀ x ∈ vFin H D, H.cell x ⊆ ball (0 : ℂ) ρ₁ := by
    intro x hx z hz
    obtain ⟨w, hwx, hwD⟩ := (mem_vFin H hDb).1 hx
    have hw := hDsub hwD
    have hdiam : cellDiam H x ≤ δ :=
      h27 x ⟨w, hwx, (ball_subset_ball (by linarith)) hw⟩
    have hzw := (dist_le_cellDiam H hz hwx).trans hdiam
    rw [mem_ball, dist_zero_right] at hw ⊢
    calc ‖z‖ ≤ ‖z - w‖ + ‖w‖ := norm_le_norm_sub_add z w
      _ < δ + ρ := by rw [← dist_eq_norm]; linarith
      _ ≤ ρ₁ := by linarith
  have hsum := t13_sum_le_lintegral_uDens H (vFin H D) hcells
  have h1 : (∫⁻ z in ball (0 : ℂ) ρ₁, uDens H z) ≤
      ENNReal.ofReal A * volume (ball (0 : ℂ) ρ₁) + ENNReal.ofReal η := by
    have := h210
    unfold Prop210Bound at this
    simpa only [ENNReal.ofReal_one, one_mul, setLIntegral_const, Measure.restrict_apply_univ]
      using this
  have hvol : volume (ball (0 : ℂ) ρ₁) ≤ ENNReal.ofReal 4 := by
    rw [Complex.volume_ball, ← ENNReal.ofReal_pow hρ₁0, ← ENNReal.ofReal_coe_nnreal,
      NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := Real.pi_lt_d2
    have h2 : ρ₁ ^ 2 ≤ 1 := by nlinarith
    nlinarith [Real.pi_pos]
  have htot : ∑ x ∈ vFin H D, ENNReal.ofReal (cellDiam H x ^ 2 * G.deg x) ≤
      ENNReal.ofReal (4 * A + η) := by
    refine hsum.trans (h1.trans ?_)
    rw [ENNReal.ofReal_add (by positivity) hη, ENNReal.ofReal_mul (by norm_num), mul_comm (ENNReal.ofReal 4)]
    gcongr
  rw [← ENNReal.ofReal_sum_of_nonneg fun x _ => by
    have := cellDiam_nonneg H x
    positivity] at htot
  have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 htot
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun x _ => by ring)) this

end MatedCRTHarmonic.GMSMain
