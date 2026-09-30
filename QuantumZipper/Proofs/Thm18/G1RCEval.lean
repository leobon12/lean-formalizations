import QuantumZipper.Proofs.Thm18.G1RCKolm
import QuantumZipper.Proofs.LQG.WedgeToolkit

/-!
# G1-RC, part 2: the regularized pairings of the GFF along a continuous family of measures

For the random canonical scale in RC2 and for RC3 at every folded circle (DECISIONS.md D32) we
must identify, **simultaneously for all parameters**, the limit of the circle-smoothed pairings
`∫ G(u, t) dμ_q(u)` (`t → 0⁺`) of a regular version `G` of the free-boundary GFF `X`, for a family
`μ_q = m.map (Φ q)` of pushforwards of a fixed probability measure `m`, carried by a compact set `S`, by a
jointly continuous `Φ` with values in `Hbar` (e.g. `Φ (d, r, s) θ = s ψ(fold(d + r e^{iθ}))`).

The smoothing radius is added as a last parameter (`G1RC.smoothFam`: `μ_q * fc(·, t)` for `t > 0`,
`μ_q` for `t ≤ 0`). If that `(n+1)`-parameter family has the Kolmogorov bounds
`G1RC.FamilyBounds` (G1RCKolm.lean), then (`G1RC.exists_smoothing_limit`):

* there is `Y₀ : (Fin n → ℝ) → Ω → ℝ`, continuous in `q` for every `ω`, a modification of
  `q ↦ X(μ_q)`;
* almost surely, for **every** `q`, `∫ G(u, t) dμ_q(u) → Y₀(q)` as `t → 0⁺`.

Proof: the continuous modification `Y` of the `(n+1)`-parameter family (DS11 Prop 3.1 with
Revuz–Yor I.(2.1), `exists_modification_family`) agrees a.s. with `(q, t) ↦ ∫ G(·, t) dμ_q` at
countably many points with `t > 0` by stochastic Fubini (`WedgeTK.ae_integral_G_eq`), hence on
all of `{t > 0}` by continuity of both sides; the `t → 0⁺` limit is continuity of `Y` at the face
`t = 0`. Source: Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1 and its proof
(arXiv:0808.1560, p. 18); the density/continuity bookkeeping is an own elementary argument
(as in `G1Kolm.exists_modification_map`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set Function
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1RC

open KolmD KolmG CircleFubini WedgeTK

variable {n : ℕ} {Θ : Type*} [TopologicalSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]

/-- The family `q ↦ m.map (Φ q)` with the smoothing radius `t` as the last parameter
(`t ≤ 0`: no smoothing). -/
def smoothFam (m : Measure Θ) (Φ : (Fin n → ℝ) → Θ → ℂ) (p : Fin (n + 1) → ℝ) : Measure ℂ :=
  if 0 < p (Fin.last n) then
    (m.map (Φ (Fin.init p))).bind fun w => foldedCircle w (p (Fin.last n))
  else m.map (Φ (Fin.init p))

theorem smoothFam_snoc_zero (m : Measure Θ) (Φ : (Fin n → ℝ) → Θ → ℂ) (q : Fin n → ℝ) :
    smoothFam m Φ (Fin.snoc q 0 : Fin (n + 1) → ℝ) = m.map (Φ q) := by
  simp [smoothFam]

theorem smoothFam_of_pos (m : Measure Θ) (Φ : (Fin n → ℝ) → Θ → ℂ) {p : Fin (n + 1) → ℝ}
    (hp : 0 < p (Fin.last n)) :
    smoothFam m Φ p = (m.map (Φ (Fin.init p))).bind fun w => foldedCircle w (p (Fin.last n)) :=
  if_pos hp

variable {m : Measure Θ} [IsProbabilityMeasure m] {Φ : (Fin n → ℝ) → Θ → ℂ} {S : Set Θ}

theorem continuous_Phi (hΦ : Continuous (uncurry Φ)) (q : Fin n → ℝ) : Continuous (Φ q) :=
  hΦ.comp (continuous_const.prodMk continuous_id)

/-- The pushed measures are carried by the compact set `Φ q '' S ⊆ Hbar`. -/
theorem map_compl_image (hΦ : Continuous (uncurry Φ)) (hS : IsCompact S) (hmS : m Sᶜ = 0)
    (q : Fin n → ℝ) : (m.map (Φ q)) (Φ q '' S)ᶜ = 0 := by
  have hc := continuous_Phi hΦ q
  rw [Measure.map_apply hc.measurable (hS.image hc).isClosed.measurableSet.compl]
  refine measure_mono_null (fun θ hθ hθS => hθ ⟨θ, hθS, rfl⟩) hmS

/-- Integrals against the pushed measure of functions continuous on `Hbar`. -/
theorem integral_map_Phi (hΦ : Continuous (uncurry Φ)) (hΦH : ∀ q θ, Φ q θ ∈ Hbar)
    (hS : IsCompact S) (hmS : m Sᶜ = 0)
    (q : Fin n → ℝ) {g : ℂ → ℝ} (hg : ContinuousOn g Hbar) :
    ∫ u, g u ∂(m.map (Φ q)) = ∫ θ, g (Φ q θ) ∂m := by
  have hc := continuous_Phi hΦ q
  have hK : IsCompact (Φ q '' S) := hS.image hc
  have hsub : Φ q '' S ⊆ Hbar := by rintro _ ⟨θ, -, rfl⟩; exact hΦH q θ
  have hae : ∀ᵐ u ∂(m.map (Φ q)), u ∈ Φ q '' S := ae_iff.2 (by
    simpa [compl_def] using map_compl_image (m := m) hΦ hS hmS q)
  have hr : (m.map (Φ q)).restrict (Φ q '' S) = m.map (Φ q) :=
    Measure.restrict_eq_self_of_ae_mem hae
  have hsm : AEStronglyMeasurable g (m.map (Φ q)) := by
    rw [← hr]
    exact (hg.mono hsub).aestronglyMeasurable_of_isCompact hK hK.isClosed.measurableSet
  exact integral_map hc.aemeasurable hsm

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample} {G : Ω → ℂ × ℝ → ℝ}

/-- Continuity of the smoothed pairings on `{t > 0}`. -/
theorem continuousOn_smoothed (hΦ : Continuous (uncurry Φ)) (hΦH : ∀ q θ, Φ q θ ∈ Hbar)
    (hS : IsCompact S) (hmS : m Sᶜ = 0) (hG : IsRegVersion X P G) (ω : Ω) :
    ContinuousOn (fun p : Fin (n + 1) → ℝ =>
      ∫ θ, G ω (Φ (Fin.init p) θ, p (Fin.last n)) ∂m) {p | 0 < p (Fin.last n)} := by
  intro p₀ hp₀
  have hp₀' : 0 < p₀ (Fin.last n) := hp₀
  have hτ : 0 < p₀ (Fin.last n) / 2 := half_pos hp₀
  set τ := p₀ (Fin.last n) / 2
  set f : (Fin (n + 1) → ℝ) → Θ → ℝ := fun p θ =>
    G ω (Φ (Fin.init p) θ, max (p (Fin.last n)) τ) with hf
  have hfc : Continuous (uncurry f) := by
    have hm : Continuous fun x : (Fin (n + 1) → ℝ) × Θ =>
        ((Φ (Fin.init x.1) x.2, max (x.1 (Fin.last n)) τ) : ℂ × ℝ) := by
      refine Continuous.prodMk ?_ ?_
      · have hinit : Continuous fun p : Fin (n + 1) → ℝ => (Fin.init p : Fin n → ℝ) :=
          continuous_pi fun i => continuous_apply _
        exact hΦ.comp ((hinit.comp continuous_fst).prodMk continuous_snd)
      · exact ((continuous_apply _).comp continuous_fst).max continuous_const
    exact (hG.cont ω).comp_continuous hm fun x =>
      ⟨hΦH _ _, lt_of_lt_of_le hτ (le_max_right _ _)⟩
  have hcont := continuous_parametric_integral_of_continuous (μ := m) hfc hS
  have hmr : m.restrict S = m := Measure.restrict_eq_self_of_ae_mem (ae_iff.2 (by
    simpa [compl_def] using hmS))
  simp only [hmr] at hcont
  refine (hcont.continuousAt.congr ?_).continuousWithinAt
  have hopen : IsOpen {p : Fin (n + 1) → ℝ | τ < p (Fin.last n)} :=
    isOpen_lt continuous_const (continuous_apply _)
  filter_upwards [hopen.mem_nhds (show τ < p₀ (Fin.last n) by simp only [τ]; linarith [hp₀'])]
    with p hp
  simp only [f, max_eq_left hp.le]

/-- **Smoothing limit along a continuous family, for all parameters at once.** -/
theorem exists_smoothing_limit (hΦ : Continuous (uncurry Φ)) (hΦH : ∀ q θ, Φ q θ ∈ Hbar)
    (hS : IsCompact S) (hmS : m Sᶜ = 0)
    {β : ℝ} (hβ : 0 < β) (hB : FamilyBounds (smoothFam m Φ) β) (hX : IsFreeGFFModConstH X P)
    (hG : IsRegVersion X P G) :
    ∃ Y₀ : (Fin n → ℝ) → Ω → ℝ, (∀ ω, Continuous fun q => Y₀ q ω) ∧
      (∀ q, (fun ω => Y₀ q ω) =ᵐ[P] fun ω => X ω (m.map (Φ q))) ∧
      ∀ᵐ ω ∂P, ∀ q, Tendsto (fun t => ∫ u, G ω (u, t) ∂(m.map (Φ q))) (𝓝[>] 0)
        (𝓝 (Y₀ q ω)) := by
  obtain ⟨Y, hYc, hYV, -⟩ := exists_modification_family hβ hB hX
  have hsn : ∀ q : Fin n → ℝ, Continuous fun t : ℝ => (Fin.snoc q t : Fin (n + 1) → ℝ) :=
    fun q => continuous_const.finSnoc (A := fun _ => ℝ) continuous_id
  refine ⟨fun q ω => Y (Fin.snoc q 0) ω, fun ω => (hYc ω).comp
    (continuous_id.finSnoc (A := fun _ => ℝ) continuous_const), fun q => ?_, ?_⟩
  · filter_upwards [hYV (Fin.snoc q 0)] with ω h
    rw [h, smoothFam_snoc_zero]
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
  filter_upwards [hall] with ω hω q
  have hEq : EqOn (L ω) (fun p => Y p ω) U :=
    Set.EqOn.of_subset_closure hω (continuousOn_smoothed hΦ hΦH hS hmS hG ω)
      (hYc ω).continuousOn hDU hUD
  have hlim : Tendsto (fun t : ℝ => Y (Fin.snoc q t) ω) (𝓝[>] 0) (𝓝 (Y (Fin.snoc q 0) ω)) :=
    (((hYc ω).comp (hsn q)).tendsto 0).mono_left nhdsWithin_le_nhds
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  have htU : (Fin.snoc q t : Fin (n + 1) → ℝ) ∈ U := by simp [U, ht]
  have := hEq htU
  simp only [L, Fin.init_snoc, Fin.snoc_last] at this
  show Y (Fin.snoc q t) ω = ∫ u, G ω (u, t) ∂(m.map (Φ q))
  rw [integral_map_Phi hΦ hΦH hS hmS q (hG.continuousOn_slice ω ht)]
  exact this.symm

end G1RC
end Thm18Asm
end QuantumZipper
