import QuantumZipper.Proofs.LQG.AreaExistenceTRL

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SW-WINSPLIT (1): the window version of the planar two-radius core bound

Source: S. Sheffield, M. Wang, *Field-measure correspondence in Liouville quantum gravity almost
surely commutes with all conformal maps simultaneously*, arXiv:1605.06171, §3.1: proof of
Lemma 3.1 (pp. 7–8: the conditional second moment (3.1), the thick-point set (3.2) and the two
one-point estimates on p. 8) and proof of Theorem 1.1 (p. 9: the same estimate for the window
measures `μ̄_{k,N}`, "using the tower property of conditional expectation as in the proof of
Lemma 3.1").

In SW's window step the centred factor is not a Gaussian tilt `1 − e^{γΔ − γ²w/2}` but
`C(N) · sup_{t ≤ s} e^{γ B_t − γ² t/2} − 1` (a function of the circle-average Brownian motion
inside the window, independent of the coarse value `h_{2^{-k/N}}(z)`, with mean `0` by the choice
of `C(N)`). The only properties used are: mean `0`, a second-moment bound `Q`, independence of
the coarse value, and independence of everything at the other point once the two points are
`δ` apart. `WinHypC` records exactly these (with the Gaussian coarse value `U` as in
`TwoRadiusC.TRLHypC`), and `winC_core_bound` is `TwoRadiusC.trlC_core_bound` with the tilt
replaced by the abstract factor `G`, in the split form SW use for Borel–Cantelli:

* `E (∫_S good)^2 ≤ Mg · D` (the `L²` part, SW (3.1) and the display after (3.2)),
* `E ∫_S |bad| ≤ Mb |S|` (the thick-point `L¹` part, SW p. 8),
* a.s. `|∫_S f A G| ≤ |∫_S good| + ∫_S |bad|`.

The continuous-index (Fubini) form instead of SW's grid-average-plus-Jensen is the repository's
standing adaptation of the two-radius lemma (`TwoRadiusC`, DEVIATIONS.md L-M4).
-/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace QuantumZipper.E6

open TwoRadius

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Hypotheses of the window core bound: Gaussian coarse value `U t` (variance `≤ 2 L t + K` in the
`γ/2`-normalization of `TwoRadius`), centred window factor `G t` with `E G² ≤ Q`, `G t ⊥ U t`, and
`G t ⊥ (U t, U u, G u)` for `‖t − u‖ ≥ δ`. -/
structure WinHypC (P : Measure Ω) (S : Set ℂ) (δ K Q : ℝ) (L : ℂ → ℝ) (v : ℂ → ℝ≥0)
    (U G : ℂ → Ω → ℝ) : Prop where
  measU : Measurable (fun p : ℂ × Ω => U p.1 p.2)
  measG : Measurable (fun p : ℂ × Ω => G p.1 p.2)
  measL : Measurable L
  lawU : ∀ t ∈ S, HasLaw (U t) (gaussianReal 0 (v t)) P
  varU : ∀ t ∈ S, (v t : ℝ) ≤ 2 * L t + K
  memG : ∀ t ∈ S, MemLp (G t) 2 P
  meanG : ∀ t ∈ S, ∫ ω, G t ω ∂P = 0
  sqG : ∀ t ∈ S, ∫ ω, G t ω ^ 2 ∂P ≤ Q
  indep : ∀ t ∈ S, IndepFun (G t) (U t) P
  decor : ∀ t ∈ S, ∀ u ∈ S, δ ≤ ‖t - u‖ →
    IndepFun (G t) (fun ω => (U t ω, U u ω, G u ω)) P

/-- The window density difference `f t · e^{-(γ²/4) L t + (γ/2) U t} · G t`. -/
noncomputable def wD (γ : ℝ) (f L : ℂ → ℝ) (U G : ℂ → Ω → ℝ) (t : ℂ) (ω : Ω) : ℝ :=
  f t * (exp (-(γ ^ 2 / 4) * L t + γ / 2 * U t ω) * G t ω)

/-- Good part (on `{U t ≤ α L t}`). -/
noncomputable def wG (γ α : ℝ) (f L : ℂ → ℝ) (U G : ℂ → Ω → ℝ) (t : ℂ) (ω : Ω) : ℝ :=
  f t * goodA γ α (L t) (U t ω) * G t ω

/-- Bad (thick-point) part (on `{U t > α L t}`, SW (3.2)). -/
noncomputable def wB (γ α : ℝ) (f L : ℂ → ℝ) (U G : ℂ → Ω → ℝ) (t : ℂ) (ω : Ω) : ℝ :=
  f t * badA γ α (L t) (U t ω) * G t ω

theorem wD_eq (γ α : ℝ) (f L : ℂ → ℝ) (U G : ℂ → Ω → ℝ) (t : ℂ) (ω : Ω) :
    wD γ f L U G t ω = wG γ α f L U G t ω + wB γ α f L U G t ω := by
  unfold wD wG wB
  rw [← goodA_add_badA γ α (L t) (U t ω)]
  ring

section Pointwise

variable {P : Measure Ω} {S : Set ℂ} {δ K Q : ℝ} {L f : ℂ → ℝ} {v : ℂ → ℝ≥0}
  {U G : ℂ → Ω → ℝ} {γ α : ℝ}

theorem WinHypC.measurable_U (h : WinHypC P S δ K Q L v U G) (t : ℂ) : Measurable (U t) :=
  h.measU.comp (measurable_const.prodMk measurable_id)

theorem WinHypC.measurable_G (h : WinHypC P S δ K Q L v U G) (t : ℂ) : Measurable (G t) :=
  h.measG.comp (measurable_const.prodMk measurable_id)

theorem measurable_wG (hf : Measurable f) (h : WinHypC P S δ K Q L v U G) :
    Measurable (fun p : ℂ × Ω => wG γ α f L U G p.1 p.2) := by
  unfold wG
  exact ((hf.comp measurable_fst).mul ((measurable_goodA₂ γ α).comp
    ((h.measL.comp measurable_fst).prodMk h.measU))).mul h.measG

theorem measurable_wB (hf : Measurable f) (h : WinHypC P S δ K Q L v U G) :
    Measurable (fun p : ℂ × Ω => wB γ α f L U G p.1 p.2) := by
  unfold wB
  exact ((hf.comp measurable_fst).mul ((measurable_badA₂ γ α).comp
    ((h.measL.comp measurable_fst).prodMk h.measU))).mul h.measG

theorem measurable_wG_t (hf : Measurable f) (h : WinHypC P S δ K Q L v U G) (t : ℂ) :
    Measurable (wG γ α f L U G t) :=
  (measurable_wG hf h).comp (measurable_const.prodMk measurable_id)

variable [IsProbabilityMeasure P]

theorem WinHypC.integrable_sq (h : WinHypC P S δ K Q L v U G) {t : ℂ} (ht : t ∈ S) :
    Integrable (fun ω => G t ω ^ 2) P :=
  (memLp_two_iff_integrable_sq (h.measurable_G t).aestronglyMeasurable).1 (h.memG t ht)

/-- `E|G| ≤ (1 + Q)/2`. -/
theorem WinHypC.integral_abs_le (h : WinHypC P S δ K Q L v U G) {t : ℂ} (ht : t ∈ S) :
    ∫ ω, |G t ω| ∂P ≤ (1 + Q) / 2 := by
  calc ∫ ω, |G t ω| ∂P ≤ ∫ ω, (1 + G t ω ^ 2) / 2 ∂P :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
          (((integrable_const 1).add (h.integrable_sq ht)).div_const 2)
          (ae_of_all _ fun ω => abs_le_half_one_add_sq _)
    _ = (1 + ∫ ω, G t ω ^ 2 ∂P) / 2 := by
        rw [integral_div, integral_add (integrable_const 1) (h.integrable_sq ht)]; simp
    _ ≤ (1 + Q) / 2 := by linarith [h.sqG t ht]

theorem integral_wG_sq_le {θ M : ℝ} (hθ : 0 ≤ θ) (h : WinHypC P S δ K Q L v U G)
    {t : ℂ} (ht : t ∈ S) (hM : |f t| ≤ M) :
    ∫ ω, wG γ α f L U G t ω ^ 2 ∂P
      ≤ M ^ 2 * (Q * (exp ((γ - θ) ^ 2 * K / 2) *
          exp ((-(γ ^ 2 / 2) + θ * α + (γ - θ) ^ 2) * L t))) := by
  have h1 := (h.indep t ht).integral_fun_comp_mul_comp (h.measurable_G t).aemeasurable
    (h.measurable_U t).aemeasurable
    ((measurable_id.pow_const 2).aestronglyMeasurable)
    (((measurable_goodA γ α (L t)).pow_const 2).aestronglyMeasurable)
    (f := fun d : ℝ => d ^ 2) (g := fun x => goodA γ α (L t) x ^ 2)
  have hA : ∫ ω, goodA γ α (L t) (U t ω) ^ 2 ∂P
      = ∫ x, goodA γ α (L t) x ^ 2 ∂(gaussianReal 0 (v t)) :=
    (h.lawU t ht).integral_comp (f := fun x => goodA γ α (L t) x ^ 2)
      ((measurable_goodA γ α (L t)).pow_const 2).aestronglyMeasurable
  have hAb := integral_goodA_sq_le (γ := γ) (α := α) (L := L t) (K := K) hθ (h.varU t ht)
  have hf2 : f t ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hM 2
  calc ∫ ω, wG γ α f L U G t ω ^ 2 ∂P
      = ∫ ω, f t ^ 2 * (G t ω ^ 2 * goodA γ α (L t) (U t ω) ^ 2) ∂P := by
        congr 1 with ω; unfold wG; ring
    _ = f t ^ 2 * ((∫ ω, G t ω ^ 2 ∂P) * ∫ ω, goodA γ α (L t) (U t ω) ^ 2 ∂P) := by
        rw [integral_const_mul]; congr 1
    _ ≤ _ := by
        rw [hA]
        have i1 : 0 ≤ ∫ ω, G t ω ^ 2 ∂P := integral_nonneg fun _ => sq_nonneg _
        have i2 : 0 ≤ ∫ x, goodA γ α (L t) x ^ 2 ∂(gaussianReal 0 (v t)) :=
          integral_nonneg fun _ => sq_nonneg _
        exact mul_le_mul hf2 (mul_le_mul (h.sqG t ht) hAb i2 (i1.trans (h.sqG t ht)))
          (mul_nonneg i1 i2) (sq_nonneg _)

theorem integral_abs_wB_le {θ M : ℝ} (hθ : 0 ≤ θ) (h : WinHypC P S δ K Q L v U G)
    {t : ℂ} (ht : t ∈ S) (hM : |f t| ≤ M) :
    ∫ ω, |wB γ α f L U G t ω| ∂P
      ≤ M * ((1 + Q) / 2 * (exp ((γ / 2 + θ) ^ 2 * K / 2) *
          exp ((-(γ ^ 2 / 4) - θ * α + (γ / 2 + θ) ^ 2) * L t))) := by
  have h1 := (h.indep t ht).integral_fun_comp_mul_comp (h.measurable_G t).aemeasurable
    (h.measurable_U t).aemeasurable
    (continuous_abs.measurable.aestronglyMeasurable)
    ((measurable_badA γ α (L t)).aestronglyMeasurable)
    (f := fun d : ℝ => |d|) (g := fun x => badA γ α (L t) x)
  have hA : ∫ ω, badA γ α (L t) (U t ω) ∂P = ∫ x, badA γ α (L t) x ∂(gaussianReal 0 (v t)) :=
    (h.lawU t ht).integral_comp (f := fun x => badA γ α (L t) x)
      (measurable_badA γ α (L t)).aestronglyMeasurable
  have hAb := integral_badA_le (γ := γ) (α := α) (L := L t) (K := K) hθ (h.varU t ht)
  have hYb := h.integral_abs_le ht
  calc ∫ ω, |wB γ α f L U G t ω| ∂P
      = ∫ ω, |f t| * (|G t ω| * badA γ α (L t) (U t ω)) ∂P := by
        congr 1 with ω; unfold wB
        rw [abs_mul, abs_mul, abs_of_nonneg (badA_nonneg _ _ _ _)]; ring
    _ = |f t| * ((∫ ω, |G t ω| ∂P) * ∫ ω, badA γ α (L t) (U t ω) ∂P) := by
        rw [integral_const_mul]; congr 1
    _ ≤ _ := by
        rw [hA]
        have i1 : 0 ≤ ∫ ω, |G t ω| ∂P := integral_nonneg fun _ => abs_nonneg _
        have i2 : 0 ≤ ∫ x, badA γ α (L t) x ∂(gaussianReal 0 (v t)) :=
          integral_nonneg fun _ => badA_nonneg _ _ _ _
        exact mul_le_mul hM (mul_le_mul hYb hAb i2 (i1.trans hYb)) (mul_nonneg i1 i2)
          ((abs_nonneg _).trans hM)

theorem memLp_wG (hγ : 0 ≤ γ) (hf : Measurable f) (h : WinHypC P S δ K Q L v U G)
    {t : ℂ} (ht : t ∈ S) : MemLp (wG γ α f L U G t) 2 P := by
  rw [memLp_two_iff_integrable_sq (measurable_wG_t hf h t).aestronglyMeasurable]
  set E := exp (γ / 2 * (α - γ / 2) * L t)
  refine Integrable.mono' ((h.integrable_sq ht).const_mul (f t ^ 2 * E ^ 2))
    ((measurable_wG_t hf h t).pow_const 2).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h0 := goodA_nonneg γ α (L t) (U t ω)
  have h1 : goodA γ α (L t) (U t ω) ≤ E := goodA_le hγ
  calc wG γ α f L U G t ω ^ 2
      = f t ^ 2 * goodA γ α (L t) (U t ω) ^ 2 * G t ω ^ 2 := by unfold wG; ring
    _ ≤ f t ^ 2 * E ^ 2 * G t ω ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 2)
          (sq_nonneg _)) (sq_nonneg _)
    _ = _ := by ring

theorem integrable_wB (h : WinHypC P S δ K Q L v U G) {t : ℂ} (ht : t ∈ S) :
    Integrable (wB γ α f L U G t) P := by
  have hind : IndepFun (badA γ α (L t) ∘ U t) (G t) P :=
    (h.indep t ht).symm.comp (measurable_badA γ α (L t)) measurable_id
  have hiA : Integrable (badA γ α (L t) ∘ U t) P :=
    (h.lawU t ht).integrable_comp (integrable_badA_gaussianReal γ α (L t) (v t))
  have hiG : Integrable (G t) P := (h.memG t ht).integrable one_le_two
  refine ((hind.integrable_mul hiA hiG).const_mul (f t)).congr (ae_of_all _ fun ω => ?_)
  simp only [Pi.mul_apply, Function.comp_apply, wB]
  ring

omit [IsProbabilityMeasure P] in
/-- Decorrelation of the good part beyond distance `δ` (SW: conditional independence of the
windows given the coarse values, (3.1)). -/
theorem integral_wG_mul_eq_zero (h : WinHypC P S δ K Q L v U G)
    {t u : ℂ} (ht : t ∈ S) (hu : u ∈ S) (htu : δ ≤ ‖t - u‖) :
    ∫ ω, wG γ α f L U G t ω * wG γ α f L U G u ω ∂P = 0 := by
  let g : ℝ × ℝ × ℝ → ℝ := fun q =>
    f t * goodA γ α (L t) q.1 * (f u * goodA γ α (L u) q.2.1 * q.2.2)
  have hg : Measurable g := by
    exact (measurable_const.mul ((measurable_goodA γ α (L t)).comp measurable_fst)).mul
      ((measurable_const.mul ((measurable_goodA γ α (L u)).comp
        (measurable_fst.comp measurable_snd))).mul (measurable_snd.comp measurable_snd))
  have h1 := (h.decor t ht u hu htu).integral_fun_comp_mul_comp
    (h.measurable_G t).aemeasurable
    ((h.measurable_U t).prodMk ((h.measurable_U u).prodMk (h.measurable_G u))).aemeasurable
    measurable_id.aestronglyMeasurable hg.aestronglyMeasurable (f := fun d : ℝ => d)
  calc ∫ ω, wG γ α f L U G t ω * wG γ α f L U G u ω ∂P
      = ∫ ω, G t ω * g (U t ω, U u ω, G u ω) ∂P := by
        congr 1 with ω; simp only [g, wG]; ring
    _ = (∫ ω, G t ω ∂P) * ∫ ω, g (U t ω, U u ω, G u ω) ∂P := h1
    _ = 0 := by rw [h.meanG t ht, zero_mul]

end Pointwise

section Main

variable {P : Measure Ω} [IsProbabilityMeasure P] {S : Set ℂ} {δ K Q : ℝ} {L f : ℂ → ℝ}
  {v : ℂ → ℝ≥0} {U G : ℂ → Ω → ℝ} {γ α : ℝ}

/-- **Window core bound** (SW (3.1)–(3.2) and p. 8, for the window factor of p. 9), split form:
the good part has second moment `≤ Mg · D` (`D` bounds the near-diagonal measure), the bad part
has first moment `≤ Mb |S|`, and pathwise the density difference is bounded by their sum. -/
theorem winC_core_bound (hγ : 0 ≤ γ) {θg θb Lmin Lmax M D : ℝ} (hθg : 0 ≤ θg)
    (hθb : 0 ≤ θb) (hQ : 0 ≤ Q)
    (hcg : 0 ≤ -(γ ^ 2 / 2) + θg * α + (γ - θg) ^ 2)
    (hcb : -(γ ^ 2 / 4) - θb * α + (γ / 2 + θb) ^ 2 ≤ 0)
    (hS : MeasurableSet S) (hSf : volume S < ∞) (hf : Measurable f) (hM : ∀ t, |f t| ≤ M)
    (h : WinHypC P S δ K Q L v U G) (hLmin : ∀ t ∈ S, Lmin ≤ L t)
    (hLmax : ∀ t ∈ S, L t ≤ Lmax)
    (hD : ((volume.restrict S).prod (volume.restrict S)).real
      {p : ℂ × ℂ | ‖p.1 - p.2‖ < δ} ≤ D) :
    ∫ ω, (∫ t in S, wG γ α f L U G t ω) ^ 2 ∂P
        ≤ M ^ 2 * (Q * (exp ((γ - θg) ^ 2 * K / 2) *
            exp ((-(γ ^ 2 / 2) + θg * α + (γ - θg) ^ 2) * Lmax))) * D ∧
      ∫ ω, (∫ t in S, |wB γ α f L U G t ω|) ∂P
        ≤ M * ((1 + Q) / 2 * (exp ((γ / 2 + θb) ^ 2 * K / 2) *
            exp ((-(γ ^ 2 / 4) - θb * α + (γ / 2 + θb) ^ 2) * Lmin))) * volume.real S ∧
      (∀ᵐ ω ∂P, |∫ t in S, wD γ f L U G t ω|
        ≤ |∫ t in S, wG γ α f L U G t ω| + ∫ t in S, |wB γ α f L U G t ω|) ∧
      Integrable (fun ω => (∫ t in S, wG γ α f L U G t ω) ^ 2) P ∧
      Integrable (fun ω => ∫ t in S, |wB γ α f L U G t ω|) P ∧
      (∀ᵐ ω ∂P, Integrable (fun t => wG γ α f L U G t ω) (volume.restrict S) ∧
        Integrable (fun t => wB γ α f L U G t ω) (volume.restrict S)) := by
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hSf.ne
  set Mg := M ^ 2 * (Q * (exp ((γ - θg) ^ 2 * K / 2) *
            exp ((-(γ ^ 2 / 2) + θg * α + (γ - θg) ^ 2) * Lmax))) with hMg
  set Mb := M * ((1 + Q) / 2 * (exp ((γ / 2 + θb) ^ 2 * K / 2) *
            exp ((-(γ ^ 2 / 4) - θb * α + (γ / 2 + θb) ^ 2) * Lmin))) with hMb
  set Gd := wG γ α f L U G with hGd
  set B := wB γ α f L U G with hB
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hMg0 : 0 ≤ Mg := by positivity
  have hG2 : ∀ t ∈ S, ∫ ω, Gd t ω ^ 2 ∂P ≤ Mg := by
    intro t ht
    refine (integral_wG_sq_le hθg h ht (hM t)).trans ?_
    rw [hMg]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (exp_le_exp.2 (mul_le_mul_of_nonneg_left (hLmax t ht) hcg)) (exp_pos _).le)
      hQ) (sq_nonneg _)
  have hB1 : ∀ t ∈ S, ∫ ω, |B t ω| ∂P ≤ Mb := by
    intro t ht
    refine (integral_abs_wB_le hθb h ht (hM t)).trans ?_
    rw [hMb]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (exp_le_exp.2 (mul_le_mul_of_nonpos_left (hLmin t ht) hcb)) (exp_pos _).le)
      (by positivity)) hM0
  have hGL2 : ∀ t ∈ S, MemLp (Gd t) 2 P := fun t ht => memLp_wG hγ hf h ht
  have hGsq : ∀ t ∈ S, Integrable (fun ω => Gd t ω ^ 2) P := fun t ht =>
    (memLp_two_iff_integrable_sq (measurable_wG_t hf h t).aestronglyMeasurable).1 (hGL2 t ht)
  have hGGint1 : ∀ t ∈ S, ∀ u ∈ S, Integrable (fun ω => Gd t ω * Gd u ω) P := by
    intro t ht u hu
    refine Integrable.mono' (((hGsq t ht).add (hGsq u hu)).div_const 2)
      ((measurable_wG_t hf h t).mul (measurable_wG_t hf h u)).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs]; exact abs_mul_le_half_add_sq _ _
  have hcross : ∀ t ∈ S, ∀ u ∈ S, ∫ ω, |Gd t ω * Gd u ω| ∂P ≤ Mg := by
    intro t ht u hu
    calc ∫ ω, |Gd t ω * Gd u ω| ∂P ≤ ∫ ω, (Gd t ω ^ 2 + Gd u ω ^ 2) / 2 ∂P :=
          integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
            (((hGsq t ht).add (hGsq u hu)).div_const 2)
            (ae_of_all _ fun ω => abs_mul_le_half_add_sq _ _)
      _ = ((∫ ω, Gd t ω ^ 2 ∂P) + ∫ ω, Gd u ω ^ 2 ∂P) / 2 := by
          rw [integral_div, integral_add (hGsq t ht) (hGsq u hu)]
      _ ≤ Mg := by linarith [hG2 t ht, hG2 u hu]
  have hcross0 : ∀ t ∈ S, ∀ u ∈ S, δ ≤ ‖t - u‖ → ∫ ω, Gd t ω * Gd u ω ∂P = 0 :=
    fun t ht u hu htu => integral_wG_mul_eq_zero h ht hu htu
  have hSS : ∀ᵐ p ∂((volume.restrict S).prod (volume.restrict S)), p.1 ∈ S ∧ p.2 ∈ S := by
    rw [Measure.prod_restrict]
    exact (ae_restrict_mem (hS.prod hS)).mono fun p hp => hp
  have hGint : Integrable (fun p : ℂ × Ω => Gd p.1 p.2) ((volume.restrict S).prod P) := by
    rw [integrable_prod_iff (measurable_wG hf h).aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem hS] with t ht
      exact (hGL2 t ht).integrable one_le_two
    · refine Integrable.mono' (integrable_const ((1 + Mg) / 2))
        (measurable_wG hf h).aestronglyMeasurable.norm.integral_prod_right' ?_
      filter_upwards [ae_restrict_mem hS] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      calc ∫ ω, ‖Gd t ω‖ ∂P ≤ ∫ ω, (1 + Gd t ω ^ 2) / 2 ∂P :=
            integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
              (((integrable_const 1).add (hGsq t ht)).div_const 2)
              (ae_of_all _ fun ω => show ‖Gd t ω‖ ≤ (1 + Gd t ω ^ 2) / 2 by
                rw [Real.norm_eq_abs]; exact abs_le_half_one_add_sq _)
        _ = (1 + ∫ ω, Gd t ω ^ 2 ∂P) / 2 := by
            rw [integral_div, integral_add (integrable_const 1) (hGsq t ht)]; simp
        _ ≤ (1 + Mg) / 2 := by linarith [hG2 t ht]
  have hBint : Integrable (fun p : ℂ × Ω => B p.1 p.2) ((volume.restrict S).prod P) := by
    rw [integrable_prod_iff (measurable_wB hf h).aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem hS] with t ht
      exact integrable_wB h ht
    · refine Integrable.mono' (integrable_const Mb)
        (measurable_wB hf h).aestronglyMeasurable.norm.integral_prod_right' ?_
      filter_upwards [ae_restrict_mem hS] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      simpa only [Real.norm_eq_abs] using hB1 t ht
  have hGGmeas : Measurable (fun q : (ℂ × ℂ) × Ω => Gd q.1.1 q.2 * Gd q.1.2 q.2) :=
    ((measurable_wG hf h).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      ((measurable_wG hf h).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hGGint : Integrable (fun q : (ℂ × ℂ) × Ω => Gd q.1.1 q.2 * Gd q.1.2 q.2)
      (((volume.restrict S).prod (volume.restrict S)).prod P) := by
    rw [integrable_prod_iff hGGmeas.aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · filter_upwards [hSS] with p hp
      exact hGGint1 p.1 hp.1 p.2 hp.2
    · refine Integrable.mono' (integrable_const Mg)
        hGGmeas.aestronglyMeasurable.norm.integral_prod_right' ?_
      filter_upwards [hSS] with p hp
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      simpa only [Real.norm_eq_abs] using hcross p.1 hp.1 p.2 hp.2
  set X : Ω → ℝ := fun ω => ∫ t in S, Gd t ω with hX
  have hBabs : Integrable (fun p : ℂ × Ω => |B p.1 p.2|) ((volume.restrict S).prod P) :=
    hBint.abs
  have hX2eq' : ∀ ω, X ω ^ 2 = ∫ p, Gd p.1 ω * Gd p.2 ω
      ∂((volume.restrict S).prod (volume.restrict S)) := by
    intro ω
    rw [sq, hX]
    exact (integral_prod_mul (fun t => Gd t ω) (fun t => Gd t ω)).symm
  have hX2int : Integrable (fun ω => X ω ^ 2) P :=
    hGGint.integral_prod_right.congr (ae_of_all _ fun ω => (hX2eq' ω).symm)
  refine ⟨?_, ?_, ?_, hX2int, hBabs.integral_prod_right,
    (hGint.prod_left_ae.and hBint.prod_left_ae)⟩
  · have hX2eq : ∀ ω, X ω ^ 2 = ∫ p, Gd p.1 ω * Gd p.2 ω
        ∂((volume.restrict S).prod (volume.restrict S)) := by
      intro ω
      rw [sq, hX]
      exact (integral_prod_mul (fun t => Gd t ω) (fun t => Gd t ω)).symm
    have hN : MeasurableSet {p : ℂ × ℂ | ‖p.1 - p.2‖ < δ} :=
      measurableSet_lt (continuous_fst.sub continuous_snd).norm.measurable measurable_const
    calc ∫ ω, X ω ^ 2 ∂P
        = ∫ ω, ∫ p, Gd p.1 ω * Gd p.2 ω ∂((volume.restrict S).prod (volume.restrict S)) ∂P := by
          congr 1 with ω; exact hX2eq ω
      _ = ∫ p, ∫ ω, Gd p.1 ω * Gd p.2 ω ∂P
            ∂((volume.restrict S).prod (volume.restrict S)) :=
          (integral_integral_swap hGGint).symm
      _ ≤ ∫ p, {p : ℂ × ℂ | ‖p.1 - p.2‖ < δ}.indicator (fun _ => Mg) p
            ∂((volume.restrict S).prod (volume.restrict S)) := by
          refine integral_mono_ae hGGint.integral_prod_left
            ((integrable_const Mg).indicator hN) ?_
          filter_upwards [hSS] with p hp
          by_cases hpN : p ∈ {p : ℂ × ℂ | ‖p.1 - p.2‖ < δ}
          · rw [Set.indicator_of_mem hpN]
            have hn : |∫ ω, Gd p.1 ω * Gd p.2 ω ∂P| ≤ ∫ ω, |Gd p.1 ω * Gd p.2 ω| ∂P := by
              simpa only [Real.norm_eq_abs] using
                norm_integral_le_integral_norm (μ := P) (fun ω => Gd p.1 ω * Gd p.2 ω)
            exact (le_abs_self _).trans (hn.trans (hcross p.1 hp.1 p.2 hp.2))
          · rw [Set.indicator_of_notMem hpN]
            simp only [Set.mem_ofPred_eq, not_lt] at hpN
            exact (hcross0 p.1 hp.1 p.2 hp.2 hpN).le
      _ = ((volume.restrict S).prod (volume.restrict S)).real
            {p : ℂ × ℂ | ‖p.1 - p.2‖ < δ} * Mg := by
          rw [integral_indicator_const _ hN, smul_eq_mul]
      _ ≤ D * Mg := mul_le_mul_of_nonneg_right hD hMg0
      _ = Mg * D := mul_comm _ _
  · calc ∫ ω, (∫ t in S, |B t ω|) ∂P = ∫ t in S, ∫ ω, |B t ω| ∂P :=
          (integral_integral_swap hBabs).symm
      _ ≤ ∫ _t in S, Mb := by
          refine integral_mono_ae hBabs.integral_prod_left (integrable_const _) ?_
          filter_upwards [ae_restrict_mem hS] with t ht
          exact hB1 t ht
      _ = Mb * volume.real S := by
          rw [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_comm]
  · filter_upwards [hGint.prod_left_ae, hBint.prod_left_ae] with ω h1 h2
    have e : ∫ t in S, wD γ f L U G t ω = X ω + ∫ t in S, B t ω := by
      rw [hX]
      simp only
      rw [← integral_add h1 h2]
      congr 1 with t
      exact wD_eq γ α f L U G t ω
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (μ := volume.restrict S) (fun t => B t ω)

end Main

end QuantumZipper.E6
