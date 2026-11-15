/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCLocality
import InteractingSLE.Spec.Restart.FCAux79Side

/-!
# The marked Gaussian kernel on a later first-contact box

Aux. 77 supplies the kernel of the centred field on every complementary component
of a capped shifted union. Here that component is identified with the image of the
continuation's Loewner domain, and the deterministic harmonic mean is added back.
The conditioning remains the actual marked sigma-algebra of the capped line.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Restart.FCPlumb

open FCAux79 LocalSets WholeField Sec6 DomainMarkov

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- The germs and the two labelled killed histories at a capped shifted line. -/
@[instance_reducible]
def shMarkedSigma (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞)
    (h : Ω → DistOn upperHalfPlaneOpens) (t : ℝ≥0) : MeasurableSpace Ω :=
  germSigma (shUnion η₁ η₂ t 0) h ⊔
    MeasurableSpace.comap (shHist η₁ η₂ ζ₁ ζ₂ t 0) inferInstance

theorem shMarkedSigma_le {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hc₁ : ∀ ω, Continuous (η₁ ω)) (hc₂ : ∀ ω, Continuous (η₂ ω))
    (hm₁ : ∀ s, Measurable fun ω => η₁ ω s) (hm₂ : ∀ s, Measurable fun ω => η₂ ω s)
    (hζ₁ : Measurable ζ₁) (hζ₂ : Measurable ζ₂) (hh : Measurable h) (t : ℝ≥0) :
    shMarkedSigma η₁ η₂ ζ₁ ζ₂ h t ≤ mΩ :=
  sup_le (germSigma_le (measurable_shUnion hc₁ hc₂ hm₁ hm₂ t 0) hh)
    (measurable_shHist hm₁ hm₂ hζ₁ hζ₂ t 0).comap_le

section Kernel

variable {P : Measure Ω} [IsProbabilityMeasure P] {d : PairData Ω}
  {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}

omit [IsProbabilityMeasure P] in
/-- The capped marked kernel, uncentred and read in the continuation chart on the active component.
This does not identify that component with the whole complement of the shifted union. -/
theorem ae_condExp_cexp_eq_lineBox (hd : d.IsMeasGood) {u₀ : ℂ → ℝ}
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₂ ω → d.η₂ ω s = η₂ ω s)
    (m : ℕ) (t : ℝ≥0) {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ}
    (hc₁ : ∀ ω, Continuous (ηc₁ ω)) (hc₂ : ∀ ω, Continuous (ηc₂ ω))
    (hag₁ : ∀ᵐ ω ∂P, ∀ s, ηc₁ ω s = η₁ ω (capTime m (d.ζ₁ ω) s))
    (hag₂ : ∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime m (d.ζ₂ ω) s))
    {g : Ω → DistOn upperHalfPlaneOpens}
    (hlaw : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
      ∀ z₀ ∈ H \ shUnion ηc₁ ηc₂ t 0 ω,
        tsupport φ ⊆ connectedComponentIn (H \ shUnion ηc₁ ηc₂ t 0 ω) z₀ →
        P[fun ω' => Complex.exp (Complex.I * (centredField h u₀ ω' φ : ℂ)) |
          shMarkedSigma ηc₁ ηc₂ (fun ω => cutLife (d.ζ₁ ω) m)
            (fun ω => cutLife (d.ζ₂ ω) m) (centredField h u₀) t] ω =
          Complex.exp (Complex.I * (g ω φ : ℂ)) *
            ((Real.exp (-(1 / 2) *
              zeroGFFTestCov (connectedComponentIn (H \ shUnion ηc₁ ηc₂ t 0 ω) z₀) φ φ) : ℝ) : ℂ))
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ω ∈ lineBox d t m →
      ∀ (x₁ x₂ : ℝ) (W : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (ζc : ℝ≥0∞) (Q : ℝ≥0),
        IsFCLine d ω x₁ x₂ t W γ ζc Q →
        tsupport φ ⊆ d.inv ω '' (H \ fwdHull (fun s : ℝ => W s.toNNReal) Q) →
        P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) |
          shMarkedSigma ηc₁ ηc₂ (fun ω => cutLife (d.ζ₁ ω) m)
            (fun ω => cutLife (d.ζ₂ ω) m) (centredField h u₀) t] ω =
          Complex.exp (Complex.I *
            ((g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) φ : ℂ) -
            (((1 / 2 : ℝ) * zeroGFFTestCov
              (d.inv ω '' (H \ fwdHull (fun s : ℝ => W s.toNNReal) Q)) φ φ : ℝ) : ℂ)) := by
  let S := SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀
  let 𝒦 := shMarkedSigma ηc₁ ηc₂ (fun ω => cutLife (d.ζ₁ ω) m)
    (fun ω => cutLife (d.ζ₂ ω) m) (centredField h u₀) t
  let _ : MeasurableSpace Ω := mΩ
  have hsplit : (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) =
      Complex.exp (Complex.I * (S φ : ℂ)) •
        fun ω' => Complex.exp (Complex.I * (centredField h u₀ ω' φ : ℂ)) := by
    funext ω'
    simp only [Pi.smul_apply, smul_eq_mul, centredField, ← Complex.exp_add]
    congr 1
    rw [sub_apply]
    push_cast
    ring
  have hsplitCE := condExp_smul (μ := P) (Complex.exp (Complex.I * (S φ : ℂ)))
    (fun ω' => Complex.exp (Complex.I * (centredField h u₀ ω' φ : ℂ))) 𝒦
  have hcmp := ae_retHist_eq_fcHist hd hc₁ hc₂ m hae hag₁ hag₂
  filter_upwards [hlaw φ, hsplitCE, hcmp, hae, hag₁, hag₂]
    with ω hker hce hcmpω hωa hcap₁ hcap₂ hbox x₁ x₂ W γ ζc Q hl hsupp
  have hA := shUnion_eq_lineK (η₁ := η₁) (η₂ := η₂) m t hbox.1 hbox.2 hl.le_life
    hωa.2.1 hωa.2.2 hcap₁ hcap₂ (hcmpω.2 hbox.1)
  have hdom := image_inv_compl_eq_lineDomain hd hl
  have hz : d.inv ω (QuantumZipper.fwdMapInv (fun s : ℝ => W s.toNNReal) Q Complex.I) ∈
      lineDomain d t ω := (hl.inv_mem hd (show Complex.I ∈ H by norm_num [H])).1
  have hcc := lineDomain_eq_connectedComponentIn hd hl.mem_E hl.le_life hz
  have hcc' : connectedComponentIn (H \ shUnion ηc₁ ηc₂ t 0 ω)
      (d.inv ω (QuantumZipper.fwdMapInv (fun s : ℝ => W s.toNNReal) Q Complex.I)) =
      lineDomain d t ω := by
    rw [hA, H_diff_inter_H]
    exact hcc.symm
  have hz' : d.inv ω (QuantumZipper.fwdMapInv (fun s : ℝ => W s.toNNReal) Q Complex.I) ∈
      H \ shUnion ηc₁ ηc₂ t 0 ω := by
    rw [hA, H_diff_inter_H]
    exact HalfPlaneSep.H_diff_fillH_subset_H_diff (hl.isCompact_lineK hd).isClosed hz
  have hsupp' : tsupport φ ⊆ connectedComponentIn (H \ shUnion ηc₁ ηc₂ t 0 ω)
      (d.inv ω (QuantumZipper.fwdMapInv (fun s : ℝ => W s.toNNReal) Q Complex.I)) := by
    rw [hcc', ← hdom]
    exact hsupp
  rw [hsplit, hce, Pi.smul_apply, smul_eq_mul, hker _ hz' hsupp', hcc', ← hdom,
    add_apply, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end Kernel

section FlowLines

variable {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
  {x₁ x₂ θ₁ θ₂ : ℝ} {h : Ω → DistOn upperHalfPlaneOpens}
  {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- The per-box active-component kernels, obtained from Aux. 77 with no kernel hypothesis.
One capped pair works at every physical line; the local-set mean is selected afterwards at each line.
The capped marked sigma-algebra is explicit, so this theorem does not assert an unproved change of conditioning. -/
theorem exists_fcBoxKernel (hL75 : Theorem15.Lemma75Statement.{u})
    (hL77 : Supp10.Lemma77Statement.{u}) (hA56 : RetainedRangeEntranceStatement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁) (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω s = η₂ ω s)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (m : ℕ) :
    ∃ ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ,
      (∀ ω, Continuous (ηc₁ ω)) ∧ (∀ ω, Continuous (ηc₂ ω)) ∧
      (∀ s, Measurable fun ω => ηc₁ ω s) ∧ (∀ s, Measurable fun ω => ηc₂ ω s) ∧
      (∀ᵐ ω ∂P, ∀ s, ηc₁ ω s = η₁ ω (capTime m (ζ₁ ω) s)) ∧
      (∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime m (ζ₂ ω) s)) ∧
      ∀ t : ℝ≥0, ∃ g : Ω → DistOn upperHalfPlaneOpens,
        IsLocalSetMean (shUnion ηc₁ ηc₂ t 0) (centredField h u₀) P g ∧
        ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ lineBox d t m →
          ∀ (W : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (ζc : ℝ≥0∞) (Q : ℝ≥0),
            IsFCLine d ω x₁ x₂ t W γ ζc Q →
            tsupport φ ⊆ d.inv ω '' (H \ fwdHull (fun s : ℝ => W s.toNNReal) Q) →
            P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) |
              shMarkedSigma ηc₁ ηc₂ (fun ω => cutLife (ζ₁ ω) m)
                (fun ω => cutLife (ζ₂ ω) m) (centredField h u₀) t] ω =
              Complex.exp (Complex.I *
                ((g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) φ : ℂ) -
                (((1 / 2 : ℝ) * zeroGFFTestCov
                  (d.inv ω '' (H \ fwdHull (fun s : ℝ => W s.toNNReal) Q)) φ φ : ℝ) : ℂ)) := by
  subst hζ₁ hζ₂
  obtain ⟨ηc₁, ηc₂, hc₁, hc₂, hm₁, hm₂, -, -, hag₁, hag₂, hlines⟩ :=
    exists_capped_shUnion_local_kernels hL75 hL77 hA56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hu₀ m
  refine ⟨ηc₁, ηc₂, hc₁, hc₂, hm₁, hm₂, hag₁, hag₂, fun t => ?_⟩
  obtain ⟨-, -, g, hg, hker⟩ := hlines t 0
  refine ⟨g, hg, fun φ => ?_⟩
  filter_upwards [ae_condExp_cexp_eq_lineBox hd hae m t hc₁ hc₂ hag₁ hag₂ hker φ]
    with ω hω hbox W γ ζc Q hl hsupp
  exact hω hbox x₁ x₂ W γ ζc Q hl hsupp

/-- Aux. 79's word mean on the same later boxes, with the flowed marks expressed as K2's geometric processes.
Together with `exists_fcBoxKernel`, this gives the kernel and its identified mean for the same capped local-set mean.
The remaining side-orientation input is exactly `IsFCSideSign`. -/
theorem ae_lineBox_mean_word_geom (hL75 : Theorem15.Lemma75Statement.{u})
    (hL77 : Supp10.Lemma77Statement.{u}) (hA56 : RetainedRangeEntranceStatement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁) (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω s = η₂ ω s)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {c₀ : BoundaryWord}
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (hc₀J : c₀.jumps = jumps)
    (hc₀b : ∀ y ∉ jumps, c₀.fn y = b y)
    (hsign : ∀ (ω : Ω) (t : ℝ≥0) (W : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (ζc : ℝ≥0∞) (Q : ℝ≥0),
      IsFCLine d ω x₁ x₂ t W γ ζc Q → IsFCSideSign d ω x₁ t W γ Q)
    (m : ℕ) (t : ℝ≥0) {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ}
    (hc₁ : ∀ ω, Continuous (ηc₁ ω)) (hc₂ : ∀ ω, Continuous (ηc₂ ω))
    (hm₁ : ∀ s, Measurable fun ω => ηc₁ ω s) (hm₂ : ∀ s, Measurable fun ω => ηc₂ ω s)
    (hag₁ : ∀ᵐ ω ∂P, ∀ s, ηc₁ ω s = η₁ ω (capTime m (ζ₁ ω) s))
    (hag₂ : ∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime m (ζ₂ ω) s))
    {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (shUnion ηc₁ ηc₂ t 0) (centredField h u₀) P g)
    {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (W : ℝ≥0 → Ω → ℝ) (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ) :
    ∀ᵐ ω ∂P, ω ∈ lineBox d t m →
      ∀ (γ : ℝ≥0 → ℂ) (ζc : ℝ≥0∞) (Q : ℝ≥0),
        IsFCLine d ω x₁ x₂ t (fun s => W s ω) γ ζc Q →
        (∀ i, xL ω i ≤ 0) → (∀ j, 0 ≤ xR ω j) →
        (∃ S : Set ℝ, S.Finite ∧ ∀ x ∉ S, forceBoundaryData κ ρL ρR (xL ω) (xR ω) x =
          (d.word c₀ (-sleLambda κ - θ₂ * QuantumZipper.chiC κ)
            (sleLambda κ - θ₁ * QuantumZipper.chiC κ) ω).fn x + θ₁ * QuantumZipper.chiC κ) →
        ∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ fwdHull (fun s : ℝ => W s.toNNReal ω) Q →
          Chart.chartTransport (hd.isConformal_chart ω) 1 (θ₁ * QuantumZipper.chiC κ)
            (QuantumZipper.chiC κ)
            (g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) ψ =
              ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) Q
                (bheProc κ ρL ρR W (Sec7.PocketTraversal.geomLW W xL)
                  (Sec7.PocketTraversal.geomRW W xR) ω Q) z * ψ z := by
  have hmean := ae_chartTransport_lineMean_word hL75 hL77 hA56 hκ hκ4 hb hx hθ hh hη₁ hη₂
    hd hζ₁ hζ₂ hae hu₀ hc₀ hc₀J hc₀b hsign m t hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg
  filter_upwards [hmean] with ω hω hbox γ ζc Q hl hxL hxR hdata ψ hsupp
  exact hω hbox.1 hbox.2 (fun s => W s ω) γ ζc Q hl ρL ρR (xL ω) (xR ω) hxL hxR hdata ψ hsupp

end FlowLines

end InteractingSLE.Restart.FCPlumb
