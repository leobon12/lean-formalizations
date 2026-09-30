import QuantumZipper.Proofs.GFF.K3.MixedM7AsmMain
import QuantumZipper.Proofs.Section5.Prop17PalmCMain

/-!
# Proposition 1.6, node C′ input: the D3⁺ setup at a boundary point from the M7 coupling

`prop16_markovSetup_at`: for `x ∈ (c, d)`, a half-disc `ball x r ∩ H ⊆ D`, `0 < r' < r` and an
admissible probability measure `ρ₀` giving no mass to `ball x r`, the half-disc coupling M7
(`K3.mixedFreeCouplingHalfDisc_holds`, proved), translated by `x`, gives

* a mixed GFF `Y` on `D` (free on `[c, d]`),
* D3⁺ data forming a `D3Plus.Setup γ γ r' ρ₀' P₀ X' Ξ g'` with `X' = palmCField X x` (the free
  field translated by `x`), `ρ₀' = palmCRho ρ₀ x` and `g' ω z = g ω (z + x)`,
* and, for every admissible `μ` carried by `closedBall 0 r'`, almost surely
  `Y (μ(· − x)) = X' μ − μ(ℂ) X' ρ₀' + ∫ g' dμ`.

This is the Markov part of `Prop16Asm.Prop16NodeCMarkovMaskStmt`; the remaining parts (local
niceness of `Y`, the Green-kernel identification of the Palm shift `(γ/2) G_D(x, ·)` near `x`,
and the local area limit of the zoomed Palm field) are not treated here.

Sources: Sheffield, *Gaussian free fields for mathematicians*, PTRF 139 (2007), Thm 2.17 (domain
Markov property, via M7); Sheffield, arXiv:1012.4797, proof of Prop. 1.6 (p. 25). Translation
bookkeeping: own elementary arguments (as `Prop17PalmCSetup.lean`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric InnerProductSpace
open scoped Topology ENNReal NNReal Laplacian

namespace QuantumZipper

namespace Prop16Asm

open K3 S5.FieldLaw.Raw

/-- Harmonicity is invariant under translation. -/
theorem harmonicAt_comp_add_const_mm {f : ℂ → ℝ} {z a : ℂ} (h : HarmonicAt f (z + a)) :
    HarmonicAt (fun w => f (w + a)) z := by
  have hΔ : Δ (fun w => f (w + a)) = fun w => Δ f (w + a) := by
    rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
      laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    funext w
    simp only [iteratedFDeriv_comp_add_right]
  refine ⟨h.1.comp z (contDiffAt_id.add contDiffAt_const), ?_⟩
  rw [hΔ]
  exact h.2.comp_tendsto ((continuous_id.add continuous_const).tendsto z)

theorem foldH_add_real_mm (z : ℂ) (x : ℝ) : foldH (z + x) = foldH z + x := by
  unfold foldH
  have e : (z + (x : ℂ)).im = z.im := by simp
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (e ▸ h1) h2
  · exact absurd (e ▸ h2) h1
  · simp [map_add, Complex.conj_ofReal]

theorem map_map_add_neg_mm (ρ : Measure ℂ) (x : ℝ) :
    (palmCRho ρ x).map (· + (x : ℂ)) = ρ := by
  rw [palmCRho, Measure.map_map (measurable_add_const _) (measurable_add_const _)]
  have e : ((· + (x : ℂ)) ∘ (· + ((-x : ℝ) : ℂ))) = id := by
    funext z; simp
  rw [e, Measure.map_id]

theorem map_add_real_apply_mm (μ : Measure ℂ) (x : ℝ) {s : Set ℂ} (hs : MeasurableSet s) :
    μ.map (· + (x : ℂ)) s = μ ((· + (x : ℂ)) ⁻¹' s) :=
  Measure.map_apply (measurable_add_const _) hs

theorem preimage_ball_add_mm (x : ℝ) (r : ℝ) :
    (· + (x : ℂ)) ⁻¹' ball (x : ℂ) r = ball (0 : ℂ) r := by
  ext z; simp [mem_ball, dist_eq_norm]

theorem preimage_ball_sub_mm (x : ℝ) (r : ℝ) :
    (· + ((-x : ℝ) : ℂ)) ⁻¹' ball (0 : ℂ) r = ball (x : ℂ) r := by
  ext z; simp [mem_ball, dist_eq_norm, sub_eq_add_neg]

theorem preimage_closedBall_add_mm (x : ℝ) (r : ℝ) :
    (· + (x : ℂ)) ⁻¹' closedBall (x : ℂ) r = closedBall (0 : ℂ) r := by
  ext z; simp [mem_closedBall, dist_eq_norm]

/-- The increment σ-algebra of the translated free field is contained in that of the field. -/
theorem freeIncrSigma_palmCField_le {Ω : Type*} [MeasurableSpace Ω] (X : Ω → FieldSample)
    (x : ℝ) : freeIncrSigma (palmCField X x) ≤ freeIncrSigma X := by
  let f : {p : Measure ℂ × Measure ℂ //
      IsAdmissibleH p.1 ∧ IsAdmissibleH p.2 ∧ p.1 Set.univ = p.2 Set.univ} →
      {p : Measure ℂ × Measure ℂ //
      IsAdmissibleH p.1 ∧ IsAdmissibleH p.2 ∧ p.1 Set.univ = p.2 Set.univ} :=
    fun p => ⟨(p.1.1.map (· + (x : ℂ)), p.1.2.map (· + (x : ℂ))),
      isAdmissibleH_map_add_real p.2.1 x, isAdmissibleH_map_add_real p.2.2.1 x, by
        rw [map_add_real_univ, map_add_real_univ]; exact p.2.2.2⟩
  have hg : Measurable (fun φ : {p : Measure ℂ × Measure ℂ //
      IsAdmissibleH p.1 ∧ IsAdmissibleH p.2 ∧ p.1 Set.univ = p.2 Set.univ} → ℝ =>
        fun p => φ (f p)) :=
    measurable_pi_iff.2 fun p => measurable_pi_apply (f p)
  unfold freeIncrSigma
  have e : (fun ω (p : {p : Measure ℂ × Measure ℂ //
      IsAdmissibleH p.1 ∧ IsAdmissibleH p.2 ∧ p.1 Set.univ = p.2 Set.univ}) =>
        palmCField X x ω p.1.1 - palmCField X x ω p.1.2) =
      (fun φ p => φ (f p)) ∘ (fun ω (p : {p : Measure ℂ × Measure ℂ //
        IsAdmissibleH p.1 ∧ IsAdmissibleH p.2 ∧ p.1 Set.univ = p.2 Set.univ}) =>
          X ω p.1.1 - X ω p.1.2) := rfl
  rw [e, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_iff_comap_le.1 hg)

/-- The outside σ-algebra at `(x, r)` is contained in that of the translated field at `(0, r)`. -/
theorem outsideSigma_le_palmCField {Ω : Type*} [MeasurableSpace Ω] (X : Ω → FieldSample)
    (x r : ℝ) : outsideSigma X x r ≤ outsideSigma (palmCField X x) 0 r := by
  refine iSup_le fun p => ?_
  have hμ := isAdmissibleH_map_add_real p.2.1 (-x)
  have hν := isAdmissibleH_map_add_real p.2.2.1 (-x)
  have hB : ∀ m : Measure ℂ, m (ball (x : ℂ) r) = 0 →
      m.map (· + ((-x : ℝ) : ℂ)) (ball ((0 : ℝ) : ℂ) r) = 0 := fun m hm => by
    rw [Complex.ofReal_zero, map_add_real_apply_mm _ _ measurableSet_ball, preimage_ball_sub_mm]
    exact hm
  have h := measurable_outsideSigma (X := palmCField X x) (t := 0) (r := r) hμ hν
    (by rw [map_add_real_univ, map_add_real_univ]; exact p.2.2.2.1) (hB _ p.2.2.2.2.1)
    (hB _ p.2.2.2.2.2)
  have e : ∀ m : Measure ℂ, (m.map (· + ((-x : ℝ) : ℂ))).map (· + (x : ℂ)) = m := fun m =>
    map_map_add_neg_mm m x
  simp only [palmCField, e] at h
  exact measurable_iff_comap_le.1 h

/-- **The D3⁺ setup at a boundary point from the M7 coupling.** -/
theorem prop16_markovSetup_at {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : Set ℂ} {c d : ℝ}
    (hgeom : Prop16Geometry D c d) {x r r' : ℝ} (hx : x ∈ Ioo c d) (hr' : 0 < r')
    (hr'r : r' < r) (hsub : ball (x : ℂ) r ∩ H ⊆ D) {ρ₀ : Measure ℂ} (hρ₀ : IsAdmissibleH ρ₀)
    (hρ₀1 : ρ₀ Set.univ = 1) (hρ₀B : ρ₀ (ball (x : ℂ) r) = 0) :
    ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (Y X : Ω₀ → FieldSample)
      (g : Ω₀ → ℂ → ℝ) (E' : Type) (_ : MeasurableSpace E') (Ξ : Ω₀ → E'),
      IsProbabilityMeasure P₀ ∧ IsMixedGFF D (realSet (Icc c d)) Y P₀ ∧
      D3Plus.Setup γ γ r' (palmCRho ρ₀ x) P₀ (palmCField X x) Ξ (fun ω z => g ω (z + x)) ∧
      ∀ μ : Measure ℂ, IsAdmissibleH μ → μ (closedBall (0 : ℂ) r')ᶜ = 0 →
        ∀ᵐ ω ∂P₀, Y ω (μ.map (· + (x : ℂ))) = palmCField X x ω μ -
          (μ Set.univ).toReal * palmCField X x ω (palmCRho ρ₀ x) + ∫ z, g ω (z + x) ∂μ := by
  obtain ⟨Ω₀, mΩ, P₀, Y, X, g, E', mE, Ξ, hP, hY, hX, hΞ, hind, hharm, hmeas, hid⟩ :=
    mixedFreeCouplingHalfDisc_holds D c d x r r' ρ₀ hgeom hx hr' hr'r hsub hρ₀ hρ₀1 hρ₀B
  have hXρ : ∀ ω, palmCField X x ω (palmCRho ρ₀ x) = X ω ρ₀ := fun ω => by
    simp only [palmCField, map_map_add_neg_mm]
  refine ⟨Ω₀, mΩ, P₀, Y, X, g, E', mE, Ξ, hP, hY, ?_, fun μ hμ hμr => ?_⟩
  · exact
      { hγ := hγ
        hγ2 := hγ2
        hα := gamma_lt_Qc' hγ hγ2
        hr := hr'
        hX := isFreeGFFModConstH_translate hX x
        hΞ := hΞ
        hind := indep_of_indep_of_le_right hind (freeIncrSigma_palmCField_le X x)
        hρ := isAdmissibleH_map_add_real hρ₀ (-x)
        hρ1 := by rw [palmCRho, map_add_real_univ, hρ₀1]
        hρB := by
          rw [palmCRho, map_add_real_apply_mm _ _ measurableSet_ball, preimage_ball_sub_mm]
          exact measure_mono_null (ball_subset_ball hr'r.le) hρ₀B
        harm := fun ω z hz => by
          have hz' : z + (x : ℂ) ∈ closedBall (x : ℂ) r' := by
            rw [mem_closedBall, dist_eq_norm, add_sub_cancel_right]
            exact (mem_ball_zero_iff.1 hz).le
          have h := harmonicAt_comp_add_const_mm (a := (x : ℂ)) (hharm ω _ hz')
          simp only [← foldH_add_real_mm] at h ⊢
          exact h
        gmeas := fun z => (hmeas (z + x)).mono (sup_le_sup_left
          ((outsideSigma_le_palmCField X x r).trans (outsideSigma_anti_radius _ 0 hr'r.le)) _)
          le_rfl }
  · have hμ1 : IsAdmissibleH (μ.map (· + (x : ℂ))) := isAdmissibleH_map_add_real hμ x
    have hμ1r : μ.map (· + (x : ℂ)) (closedBall (x : ℂ) r')ᶜ = 0 := by
      rw [map_add_real_apply_mm _ _ isClosed_closedBall.measurableSet.compl, preimage_compl,
        preimage_closedBall_add_mm]
      exact hμr
    filter_upwards [hid _ hμ1 hμ1r] with ω h
    rw [h, map_add_real_univ, hXρ]
    have e : (fun z : ℂ => z + (x : ℂ)) = ⇑(Homeomorph.addRight (x : ℂ)).toMeasurableEquiv := rfl
    rw [e, integral_map_equiv]
    rfl

end Prop16Asm

end QuantumZipper
