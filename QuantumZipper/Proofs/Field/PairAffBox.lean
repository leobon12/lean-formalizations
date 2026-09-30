import QuantumZipper.Proofs.Field.PairAffMoment
import QuantumZipper.Proofs.Field.PairLim

/-!
# PAIR-AFF, part 3: a continuous modification in (radius, translation, dilation)

For a free boundary GFF modulo constants `X`, `η` with `PairLim.Setup M R δ η` and `0 < b₀`,
the three-parameter family `q ↦ X ω (qμ q)` (`PairAffMoment`) has a modification `W` continuous
in `q ∈ ℝ³` (`KolmD.exists_continuous_modification_D`, `d = 3`, moment bound
`Setup.momentBound3`), and almost surely, **simultaneously** for all `s ∈ (0, δ')`, `t ∈ ℝ`,
`b ∈ (b₀, b₁)`,

  `∫ evalReg (X ω) (fc(u, s)) d(η ∘ aff(t,b)⁻¹)(u) = W (s, t, b) ω`

(`exists_aff_modification`). Route as in `PairLim.ae_tendsto_integral_evalReg_fc`: stochastic
Fubini at each rational triple (`Setup.ae_integral_witness_eq` for the affine image), joint
continuity of the regular-version integrals in `(s, t, b)` (dominated convergence), and density
of the rational triples.

Source: Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
§3.1, Prop. 3.1; Revuz–Yor, *Continuous martingales and Brownian motion*, Ch. I, Thm. (2.1)
(Kolmogorov criterion, here in dimension 3).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Real Topology

namespace QuantumZipper
namespace PairLim

open SmoothConv KolmD WedgeTK

variable {M : ℝ≥0} {R δ : ℝ} {η : Measure ℂ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- The embedding `(s, t, b) ↦ ![s, t, b]`. -/
def vec3 (p : ℝ × ℝ × ℝ) : Fin 3 → ℝ := ![p.1, p.2.1, p.2.2]

theorem continuous_vec3 : Continuous vec3 := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact continuous_fst
  · exact continuous_snd.fst
  · exact continuous_snd.snd

theorem qs_vec3 {s t b : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ δ) : qs δ (vec3 (s, t, b)) = s := by
  simp [qs, vec3, abs_of_nonneg h0, min_eq_left h1]

theorem qν_vec3 {b₀ b₁ s t b : ℝ} (h0 : b₀ ≤ b) (h1 : b ≤ b₁) :
    qν η b₀ b₁ (vec3 (s, t, b)) = η.map (aff t b) := by
  simp [qν, qb, vec3, min_eq_left h1, max_eq_right h0]

theorem Setup.integral_map_aff_witness (hS : Setup M R δ η) {t b b₀ : ℝ} (hb₀ : 0 < b₀)
    (hb : b₀ ≤ b) {F : ℂ × ℝ → ℝ} (hF : ContinuousOn F (Hbar ×ˢ Ioi 0)) {s : ℝ} (hs : 0 < s) :
    ∫ u, F (u, s) ∂(η.map (aff t b)) = ∫ w, F (aff t b w, s) ∂η := by
  have hνH : (η.map (aff t b)).restrict Hbar = η.map (aff t b) :=
    Measure.restrict_eq_self_of_ae_mem ((hS.map_aff hb₀ hb).good.ae_mem.mono fun w hw => hw.2)
  have hc : ContinuousOn (fun u => F (u, s)) Hbar :=
    hF.comp (continuousOn_id.prodMk continuousOn_const) fun u hu => ⟨hu, hs⟩
  have hm : AEStronglyMeasurable (fun u => F (u, s)) (η.map (aff t b)) := by
    rw [← hνH]; exact hc.aestronglyMeasurable isClosed_Hbar.measurableSet
  exact integral_map (measurable_aff t b).aemeasurable hm

/-- **Joint continuity** of `(s, t, b) ↦ ∫ F(t + b w, s) dη(w)` for `F` continuous on
`Hbar × (0, ∞)`. -/
theorem Setup.continuousOn_integral_aff (hS : Setup M R δ η) {F : ℂ × ℝ → ℝ}
    (hF : ContinuousOn F (Hbar ×ˢ Ioi 0)) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => ∫ w, F (aff p.2.1 p.2.2 w, p.1) ∂η)
      (Ioi 0 ×ˢ (univ ×ˢ Ioi 0)) := by
  have := hS.good.isFiniteMeasure
  set K := Metric.closedBall (0 : ℂ) R ∩ Hbar
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_right isClosed_Hbar
  have hηK : η.restrict K = η := Measure.restrict_eq_self_of_ae_mem hS.good.ae_mem
  intro p hp
  obtain ⟨hp1, -, hp3⟩ := hp
  have hp1 : 0 < p.1 := hp1
  have hp3 : 0 < p.2.2 := hp3
  set V : Set (ℝ × ℝ × ℝ) := Icc (p.1 / 2) (p.1 + 1) ×ˢ
    (Icc (p.2.1 - 1) (p.2.1 + 1) ×ˢ Icc (p.2.2 / 2) (p.2.2 + 1))
  have hVc : IsCompact V := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hVn : V ∈ 𝓝 p := prod_mem_nhds (Icc_mem_nhds (by linarith) (by linarith))
    (prod_mem_nhds (Icc_mem_nhds (by linarith) (by linarith))
      (Icc_mem_nhds (by linarith) (by linarith)))
  set g : ℂ × (ℝ × ℝ × ℝ) → ℂ × ℝ := fun x => (aff x.2.2.1 x.2.2.2 x.1, x.2.1)
  have hg : Continuous g := by
    simp only [g, aff]; fun_prop
  have hmaps : MapsTo g (K ×ˢ V) (Hbar ×ˢ Ioi 0) := by
    rintro ⟨w, r⟩ ⟨hw, hr⟩
    refine ⟨?_, ?_⟩
    · show (0 : ℝ) ≤ (aff r.2.1 r.2.2 w).im
      have h1 : (0 : ℝ) ≤ w.im := hw.2
      have h2 : 0 ≤ r.2.2 := by linarith [hr.2.2.1]
      simp only [aff, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        zero_mul, add_zero, zero_add]
      positivity
    · show 0 < r.1
      linarith [hr.1.1]
  have hc : ContinuousOn (F ∘ g) (K ×ˢ V) := hF.comp hg.continuousOn hmaps
  obtain ⟨C, hC⟩ := (hK.prod hVc).exists_bound_of_continuousOn hc
  have hV : ContinuousOn (fun p : ℝ × ℝ × ℝ => ∫ w, F (aff p.2.1 p.2.2 w, p.1) ∂η) V := by
    refine continuousOn_of_dominated (bound := fun _ => C) (fun r hr => ?_) (fun r hr => ?_)
      (integrable_const C) ?_
    · have h : ContinuousOn (fun w => F (g (w, r))) K :=
        hc.comp (continuousOn_id.prodMk continuousOn_const) fun w hw => ⟨hw, hr⟩
      rw [← hηK]; exact h.aestronglyMeasurable (hK.isClosed.measurableSet)
    · filter_upwards [hS.good.ae_mem] with w hw
      exact hC (w, r) ⟨hw, hr⟩
    · filter_upwards [hS.good.ae_mem] with w hw
      exact hc.comp (continuousOn_const.prodMk continuousOn_id) fun r hr => ⟨hw, hr⟩
  exact (hV.continuousAt hVn).continuousWithinAt

/-- **Continuous modification in (radius, translation, dilation).** -/
theorem exists_aff_modification [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    (hS : Setup M R δ η) {b₀ b₁ : ℝ} (hb₀ : 0 < b₀) :
    ∃ W : (Fin 3 → ℝ) → Ω → ℝ, (∀ ω, Continuous fun q => W q ω) ∧
      (∀ q, (fun ω => W q ω) =ᵐ[P]
        fun ω => X ω (smooth (qν η b₀ b₁ q) (qs (min (b₀ * δ) 1) q))) ∧
      ∀ᵐ ω ∂P, ∀ s ∈ Ioo 0 (min (b₀ * δ) 1), ∀ t : ℝ, ∀ b ∈ Ioo b₀ b₁,
        ∫ u, evalReg (X ω) (foldedCircle u s) ∂(η.map (aff t b)) = W (vec3 (s, t, b)) ω := by
  have := hS.good.isFiniteMeasure
  set δ' := min (b₀ * δ) 1 with hδ'
  set Z : (Fin 3 → ℝ) → Ω → ℝ := fun q ω => X ω (smooth (qν η b₀ b₁ q) (qs δ' q)) with hZ
  have hZm : ∀ q, AEMeasurable (Z q) P := fun q => (hX.measurable_coord _).aemeasurable
  obtain ⟨W, hWc, hWV, -⟩ := exists_continuous_modification_D (d := 3) (by norm_num) hZm
    fun R' => ⟨_, mul_nonneg (pow_nonneg (Lq_nonneg _ _ _ _) 8) (gaussianAbsMoment_nonneg 16),
      hS.momentBound3 hX (b₁ := b₁) hb₀ R'⟩
  refine ⟨W, hWc, hWV, ?_⟩
  obtain ⟨G, hG⟩ := exists_isRegVersion hX
  have hQ : ∀ᵐ ω ∂P, ∀ r : ℚ × ℚ × ℚ, 0 < (r.1 : ℝ) → (r.1 : ℝ) ≤ δ' →
      b₀ ≤ (r.2.2 : ℝ) → (r.2.2 : ℝ) ≤ b₁ →
      ∫ u, G ω (u, r.1) ∂(η.map (aff r.2.1 r.2.2)) = W (vec3 (r.1, r.2.1, r.2.2)) ω := by
    rw [ae_all_iff]; intro r
    by_cases hr : 0 < (r.1 : ℝ) ∧ (r.1 : ℝ) ≤ δ' ∧ b₀ ≤ (r.2.2 : ℝ) ∧ (r.2.2 : ℝ) ≤ b₁
    · obtain ⟨h1, h2, h3, h4⟩ := hr
      filter_upwards [(hS.map_aff (t := r.2.1) hb₀ h3).ae_integral_witness_eq hX hG h1,
        hWV (vec3 (r.1, r.2.1, r.2.2))] with ω e1 e2 _ _ _ _
      rw [e1, e2]
      simp only [hZ, qs_vec3 h1.le h2, qν_vec3 (η := η) (s := (r.1 : ℝ)) (t := (r.2.1 : ℝ)) h3 h4]
    · exact ae_of_all _ fun ω h1 h2 h3 h4 => absurd ⟨h1, h2, h3, h4⟩ hr
  filter_upwards [hQ, hG.reg] with ω hq hreg
  set U : Set (ℝ × ℝ × ℝ) := Ioo 0 δ' ×ˢ (univ ×ˢ Ioo b₀ b₁)
  have hUo : IsOpen U := isOpen_Ioo.prod (isOpen_univ.prod isOpen_Ioo)
  set Φ : ℝ × ℝ × ℝ → ℝ := fun p => ∫ w, G ω (aff p.2.1 p.2.2 w, p.1) ∂η
  set Ψ : ℝ × ℝ × ℝ → ℝ := fun p => W (vec3 p) ω
  have hΨ : Continuous Ψ := (hWc ω).comp continuous_vec3
  have hΦ : ContinuousOn Φ U := (hS.continuousOn_integral_aff (hG.cont ω)).mono
    fun p hp => ⟨hp.1.1, trivial, hb₀.trans hp.2.2.1⟩
  have hdense : DenseRange fun r : ℚ × ℚ × ℚ => ((r.1 : ℝ), (r.2.1 : ℝ), (r.2.2 : ℝ)) :=
    Rat.denseRange_cast.prodMap (Rat.denseRange_cast.prodMap Rat.denseRange_cast)
  have hEq : EqOn Φ Ψ U := by
    refine EqOn.of_subset_closure (s := U ∩ range fun r : ℚ × ℚ × ℚ =>
      ((r.1 : ℝ), (r.2.1 : ℝ), (r.2.2 : ℝ))) ?_ hΦ hΨ.continuousOn inter_subset_left
      (hdense.open_subset_closure_inter hUo)
    rintro _ ⟨hp, r, rfl⟩
    obtain ⟨⟨h1, h2⟩, -, h3, h4⟩ := hp
    simp only [Φ, Ψ]
    rw [← hS.integral_map_aff_witness hb₀ h3.le (hG.cont ω) h1]
    exact hq r h1 h2.le h3.le h4.le
  intro s hs t b hb
  have hSb := hS.map_aff (t := t) hb₀ hb.1.le
  rw [integral_congr_ae (hSb.good.ae_mem.mono fun u hu => hreg.evalReg_fc_of_mem hu.2 hs.1),
    hS.integral_map_aff_witness hb₀ hb.1.le (hG.cont ω) hs.1]
  exact hEq (show (s, t, b) ∈ U from ⟨hs, trivial, hb⟩)

end PairLim
end QuantumZipper
