import QuantumZipper.Proofs.Thm18.G1RCCircle
import QuantumZipper.Proofs.LQG.GoodMeasurableReg
import QuantumZipper.Proofs.LQG.RegularClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-REST-UNIF, free part: uniform smoothing limits on compact parameter sets

`G1RC.exists_smoothing_limit` (G1RCEval.lean) identifies, a.s. and for **every** parameter `q`,
the limit of the circle-smoothed pairings `∫ G(Φ q θ, t) dm(θ)` of a regular version `G` of the
free field as `t → 0⁺`. Its proof shows more: a.s. these pairings are the values at `(q, t)`,
`t > 0`, of the continuous modification `Y` of the `(n+1)`-parameter family, which is jointly
continuous **down to `t = 0`**. By uniform continuity of `Y` on the compact sets
`K × [0, 1]` (Heine–Cantor), the convergence is uniform in `q ∈ K`
(`G1RC.exists_smoothing_limit_unif`).

Specialized to the pushed folded circles (`G1RC.ae_unif_pushed`): a.s., for every scale
`S > 0` and every box `m`, `∫ G(S ψ z, t) dfc(q)(z)` converges as `t → 0⁺` uniformly in
`q ∈ GoodMeas.kbox m`.

Source: Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
Prop. 3.1 (continuous modification of the circle-average process, arXiv:0808.1560 p. 18), with
Revuz–Yor, Ch. I, Thm (2.1), through `G1RC.exists_modification_family`; the uniformity step
is Heine–Cantor (`IsCompact.uniformContinuousOn_of_continuous`); bookkeeping is own.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set Function
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1RC

open KolmD KolmG CircleFubini WedgeTK

variable {n : ℕ} {Θ : Type*} [TopologicalSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
variable {m : Measure Θ} [IsProbabilityMeasure m] {Φ : (Fin n → ℝ) → Θ → ℂ} {S : Set Θ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample} {G : Ω → ℂ × ℝ → ℝ}

/-- **Uniform smoothing limit on compact parameter sets.** -/
theorem exists_smoothing_limit_unif (hΦ : Continuous (uncurry Φ)) (hΦH : ∀ q θ, Φ q θ ∈ Hbar)
    (hS : IsCompact S) (hmS : m Sᶜ = 0)
    {β : ℝ} (hβ : 0 < β) (hB : FamilyBounds (smoothFam m Φ) β) (hX : IsFreeGFFModConstH X P)
    (hG : IsRegVersion X P G) :
    ∃ Y₀ : (Fin n → ℝ) → Ω → ℝ, ∀ᵐ ω ∂P, ∀ K : Set (Fin n → ℝ), IsCompact K →
      ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, 0 < t → t < η → ∀ q ∈ K,
        |(∫ θ, G ω (Φ q θ, t) ∂m) - Y₀ q ω| < ε := by
  obtain ⟨Y, hYc, hYV, -⟩ := exists_modification_family hβ hB hX
  refine ⟨fun q ω => Y (Fin.snoc q 0) ω, ?_⟩
  set U : Set (Fin (n + 1) → ℝ) := {p | 0 < p (Fin.last n)} with hU
  set L : Ω → (Fin (n + 1) → ℝ) → ℝ := fun ω p =>
    ∫ θ, G ω (Φ (Fin.init p) θ, p (Fin.last n)) ∂m with hL
  obtain ⟨D, hDc, hDU, hUD⟩ := TopologicalSpace.exists_countable_dense_subset U
  have hpt : ∀ p ∈ D, ∀ᵐ ω ∂P, L ω p = Y p ω := by
    intro p hp
    have hp' : 0 < p (Fin.last n) := hDU hp
    have hc := continuous_Phi hΦ (Fin.init p)
    have hsub : Φ (Fin.init p) '' S ⊆ Hbar := by rintro _ ⟨θ, -, rfl⟩; exact hΦH _ θ
    filter_upwards [ae_integral_G_eq hX hG hp' (m.map (Φ (Fin.init p))) (hS.image hc)
      hsub (map_compl_image hΦ hS hmS _), hYV p] with ω h1 h2
    simp only [L]
    rw [← integral_map_Phi hΦ hΦH hS hmS _ (hG.continuousOn_slice ω hp'), h1, h2,
      smoothFam_of_pos m Φ hp']
  have hall : ∀ᵐ ω ∂P, ∀ p ∈ D, L ω p = Y p ω :=
    (eventually_countable_ball hDc).2 hpt
  filter_upwards [hall] with ω hω K hK ε hε
  have hEq : EqOn (L ω) (fun p => Y p ω) U :=
    Set.EqOn.of_subset_closure hω (continuousOn_smoothed hΦ hΦH hS hmS hG ω)
      (hYc ω).continuousOn hDU hUD
  set f : ℝ × (Fin n → ℝ) → ℝ := fun x => Y (Fin.snoc x.2 x.1) ω with hf
  have hfc : Continuous f :=
    (hYc ω).comp ((continuous_snd).finSnoc (A := fun _ => ℝ) continuous_fst)
  have huc : UniformContinuousOn f (Icc (0 : ℝ) 1 ×ˢ K) :=
    (isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hfc.continuousOn
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff.1 huc ε hε
  refine ⟨min δ 1, lt_min hδ one_pos, fun t ht htη q hq => ?_⟩
  have ht1 : t ≤ 1 := (htη.trans_le (min_le_right _ _)).le
  have htU : (Fin.snoc q t : Fin (n + 1) → ℝ) ∈ U := by simp [U, ht]
  have e1 := hEq htU
  simp only [L, Fin.init_snoc, Fin.snoc_last] at e1
  have hd : dist ((t, q) : ℝ × (Fin n → ℝ)) (0, q) < δ := by
    rw [Prod.dist_eq, dist_self, Real.dist_eq, sub_zero, abs_of_pos ht]
    exact max_lt (htη.trans_le (min_le_left _ _)) hδ
  have := hδf (t, q) ⟨⟨ht.le, ht1⟩, hq⟩ (0, q) ⟨⟨le_rfl, zero_le_one⟩, hq⟩ hd
  simp only [f, Real.dist_eq] at this
  rw [e1]
  exact this

/-- `fc(d, r)` as the image of the normalized angle measure. -/
theorem foldedCircle_eq_map_circM (d : ℂ) (r : ℝ) :
    foldedCircle d r = circM.map (fun θ => foldH (circleMap d r θ)) := by
  unfold foldedCircle
  rw [circleUnif_eq_map, Measure.map_map continuous_foldH'.measurable
    (continuous_circleMap d r).measurable]
  rfl

theorem continuousOn_qOf_kbox (s : ℝ) (M : ℕ) :
    ContinuousOn (fun q : ℂ × ℝ => qOf q.1 q.2 s) (GoodMeas.kbox M) := by
  have hl : ContinuousOn (fun q : ℂ × ℝ => Real.log q.2) (GoodMeas.kbox M) :=
    Real.continuousOn_log.comp continuous_snd.continuousOn fun q hq =>
      (GoodMeas.kbox_subset M hq).2.ne'
  refine continuousOn_pi.2 fun i => ?_
  fin_cases i
  · exact (Complex.continuous_re.comp continuous_fst).continuousOn
  · exact (Complex.continuous_im.comp continuous_fst).continuousOn
  · exact hl
  · exact continuousOn_const

/-- **Uniform smoothing limit of the pushed folded circles on the compact boxes.** -/
theorem ae_unif_pushed {ψ : ℂ → ℂ} (hψc : ContinuousOn ψ Hbar)
    (hψH : MapsTo ψ Hbar Hbar) {β : ℝ} (hβ : 0 < β) (hB : PushFamBounds ψ β)
    (hX : IsFreeGFFModConstH X P) (hG : IsRegVersion X P G) :
    ∃ V : ℂ × ℝ → ℝ → Ω → ℝ, ∀ᵐ ω ∂P, ∀ s : ℝ, 0 < s → ∀ M : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, 0 < t → t < η → ∀ q ∈ GoodMeas.kbox M,
        |(∫ z, G ω ((s : ℂ) * ψ z, t) ∂foldedCircle q.1 q.2) - V q s ω| < ε := by
  obtain ⟨Y₀, hY⟩ := exists_smoothing_limit_unif (continuous_pushPhi hψc)
    (pushPhi_mem_Hbar hψH) isCompact_Icc circM_compl hβ hB hX hG
  refine ⟨fun q s ω => Y₀ (qOf q.1 q.2 s) ω, ?_⟩
  filter_upwards [hY] with ω hω s hs M ε hε
  obtain ⟨η, hη, hηY⟩ := hω _ ((GoodMeas.isCompact_kbox M).image_of_continuousOn
    (continuousOn_qOf_kbox s M)) ε hε
  refine ⟨η, hη, fun t ht htη q hq => ?_⟩
  have hr : 0 < q.2 := (GoodMeas.kbox_subset M hq).2
  have key := hηY t ht htη _ ⟨q, hq, rfl⟩
  have hgc : ContinuousOn (fun z => G ω ((s : ℂ) * ψ z, t)) Hbar :=
    (hG.cont ω).comp ((continuousOn_const.mul hψc).prodMk continuousOn_const) fun z hz =>
      ⟨show 0 ≤ ((s : ℂ) * ψ z).im by
        rw [Complex.im_ofReal_mul]; exact mul_nonneg hs.le (hψH hz), ht⟩
  have hint := RegClosure.integrable_fc hgc q.1 hr.le
  have e : ∫ z, G ω ((s : ℂ) * ψ z, t) ∂foldedCircle q.1 q.2 =
      ∫ θ, G ω (pushPhi ψ (qOf q.1 q.2 s) θ, t) ∂circM := by
    rw [pushPhi_qOf ψ q.1 hr hs]
    rw [foldedCircle_eq_map_circM] at hint ⊢
    exact integral_map (continuous_foldH'.comp (continuous_circleMap _ _)).aemeasurable
      hint.aestronglyMeasurable
  rw [e]
  exact key

end G1RC
end Thm18Asm
end QuantumZipper
