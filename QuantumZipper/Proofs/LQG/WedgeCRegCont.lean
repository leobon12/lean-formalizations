import QuantumZipper.Proofs.Zipper.F1B4dPath
import QuantumZipper.Proofs.Section5.Prop17RawAS

/-!
# WEDGE-CREG (3), per test function: continuum limits of the wedge pairings

`F1.WedgeContPairStmt γ α` asks, almost surely, for **all** test functions `ρ` and all `b > 0` at
once, that `r ↦ ∫ evalReg W (fc(b·(−ū), r)) ρ^±(u) du` converge as `r → 0⁺`, where
`W = wedgeField (lateralPart X) A Q` is the reference wedge field.

This file proves the **per-test-function** form (`ae_contPair_wedge`): for each `ρ : TestFun H`,
almost surely, for all `b > 0` simultaneously, the limits exist. The quantifier over `ρ` stays
outside the almost-sure event: an event for all (uncountably many) `ρ` at once would need an a.s.
bound of the free field in a negative Sobolev/Hölder dual norm, which the repository does not
have (see the report of task WEDGE-CREG).

Route: the pairing is the continuum pairing of `W` with the dilation by `b` of the reflected
measure `(ρ^± ∘ (−·̄)) du` (`map_withDensity_negConj`); away from the real axis `W` is
raw-represented by the regular witness of `X + ofFun (gT …)` (`S5.FieldLaw.Raw.rawRep_wedgeField`),
and PAIR-AFF gives, a.s., continuum limits for all dilations at once
(`PairLim.ae_tendstoLocallyUniformlyOn_affPair`, `S5.FieldLaw.Raw.tendsto_wedgeWitness`).

Sources: Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
§3.1, Prop. 3.1 (continuity of the circle-average process), through PAIR-AFF; the bookkeeping
here is an own elementary argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ComplexConjugate NNReal

namespace QuantumZipper
namespace WedgeCReg

open PairLim S5.FieldLaw.Raw

variable {M : ℝ≥0} {R δ : ℝ} {η : Measure ℂ}

/-! ## 1. Deterministic part -/

/-- For a `GoodRad` sample, a continuous radial path and a PAIR-LIM measure `η` whose affine
images all have continuum limits, the circle-regularized pairings of the wedge field with every
dilation `aff 0 b` of `η` converge as `r → 0⁺`. -/
theorem tendsto_wedge_aff {x : FieldSample} {F : ℂ × ℝ → ℝ} {A : ℝ → ℝ} {Q : ℝ}
    (hGR : WedgeTK.GoodRad x F) (hA : Continuous A) (hS : Setup M R δ η)
    (hPA : ∀ t B : ℝ, 0 < B → ∃ L, Tendsto (fun s => affPair x η s (t, B)) (𝓝[>] 0) (𝓝 L))
    {b : ℝ} (hb : 0 < b) :
    ∃ L, Tendsto (fun r => ∫ u, evalReg (wedgeField (lateralPart x) A Q)
      (foldedCircle (aff 0 b u) r) ∂η) (𝓝[>] 0) (𝓝 L) := by
  have := hS.good.isFiniteMeasure
  have hρ₀ : 0 < b * δ / 2 := by have := hS.pos; positivity
  have hR := rawRep_wedgeField hGR hA Q hρ₀
  have hreg := isRegularWith_wedgeWitness hGR hA Q hρ₀
  obtain ⟨L, hL⟩ := hPA 0 b hb
  refine ⟨_, (tendsto_wedgeWitness (Q := Q) hGR hA hS hρ₀ hb hL).congr' ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (half_pos hρ₀)] with r hr
  refine integral_congr_ae (hS.im.mono fun u hu => ?_)
  have hw : b * δ / 2 + r < (aff 0 b u).im := by
    rw [im_aff]
    have := mul_le_mul_of_nonneg_left hu hb.le
    linarith [hr.2]
  beta_reduce
  rw [hR.evalReg_fc hreg one_pos hρ₀.le (half_pos hρ₀) hr.1 hw]
  simp only [aff, Complex.ofReal_zero, Complex.ofReal_one, zero_add, one_mul, add_zero]

/-! ## 2. Reflection of density measures -/

theorem map_withDensity_negConj (g : ℂ → ℝ) :
    (volume.withDensity fun z => ENNReal.ofReal (g z)).map (fun u => -conj u) =
      volume.withDensity fun z => ENNReal.ofReal (g (-conj z)) := by
  ext s hs
  rw [Measure.map_apply F1.negConj_emb.measurable hs,
    withDensity_apply _ (F1.negConj_emb.measurable hs), withDensity_apply _ hs]
  have := GoodTransforms.measurePreserving_neg_conj.setLIntegral_comp_preimage_emb
    F1.negConj_emb (fun z => ENNReal.ofReal (g (-conj z))) s
  simpa using this

theorem integral_withDensity_negConj (φ : ℂ → ℝ) (g : ℂ → ℝ) :
    ∫ u, φ (-conj u) ∂(volume.withDensity fun z => ENNReal.ofReal (g z)) =
      ∫ v, φ v ∂(volume.withDensity fun z => ENNReal.ofReal (g (-conj z))) := by
  rw [← map_withDensity_negConj, F1.negConj_emb.integral_map]

/-- `z ↦ −z̄` as a homeomorphism. -/
def negConjH : ℂ ≃ₜ ℂ := (Homeomorph.neg ℂ).trans Complex.conjCLE.toHomeomorph

theorem negConjH_apply (z : ℂ) : negConjH z = -conj z := by simp [negConjH]

/-- A test function on `ℍ` composed with `z ↦ −z̄` is again one. -/
theorem testFun_negConj {g : ℂ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgH : tsupport g ⊆ H) :
    Continuous (fun z => g (-conj z)) ∧ HasCompactSupport (fun z => g (-conj z)) ∧
      tsupport (fun z => g (-conj z)) ⊆ H := by
  have e : (fun z => g (-conj z)) = g ∘ negConjH := by funext z; simp [negConjH_apply]
  rw [e]
  refine ⟨hg.comp negConjH.continuous, hgc.comp_homeomorph negConjH, ?_⟩
  rw [tsupport_comp_eq_preimage]
  intro z hz
  have h1 : negConjH z ∈ H := hgH hz
  rw [negConjH_apply] at h1
  show 0 < z.im
  have h2 : 0 < (-conj z).im := h1
  simpa using h2

/-! ## 3. Almost surely, for each test function -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- **WEDGE-CREG (3), per test function.** For a free field `X`, an a.s. continuous radial path
`A`, any `Q` and each test function `ρ` on `ℍ`: almost surely, for every `b > 0` and both signed
parts `f ∈ {ρ, −ρ}`, the pairings `r ↦ ∫ evalReg W (fc(b·(−ū), r)) f⁺(u) du` of the wedge field
`W = wedgeField (lateralPart X) A Q` converge as `r → 0⁺`. -/
theorem ae_contPair_wedge [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {A : ℝ → Ω → ℝ} (hA : ∀ᵐ ω ∂P, Continuous fun t => A t ω) (Q : ℝ) (ρ : TestFun H) :
    ∀ᵐ ω ∂P, ∀ b : ℝ, 0 < b → ∀ f ∈ ({ρ.1, -ρ.1} : Set (ℂ → ℝ)), ∃ L : ℝ,
      Tendsto (fun r => ∫ u, evalReg (wedgeField (lateralPart (X ω)) (fun t => A t ω) Q)
        (foldedCircle ((b : ℂ) * -conj u) r)
          ∂(volume.withDensity fun z => ENNReal.ofReal (f z))) (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨hs, hc, hH⟩ := ρ.2
  obtain ⟨c1, s1, t1⟩ := testFun_negConj hs.continuous hc hH
  obtain ⟨c2, s2, t2⟩ := testFun_negConj hs.continuous.neg hc.neg
    (by rw [tsupport_neg]; exact hH)
  obtain ⟨M₁, R₁, δ₁, h₁⟩ := exists_setup_withDensity c1 s1 t1
  obtain ⟨M₂, R₂, δ₂, h₂⟩ := exists_setup_withDensity c2 s2 t2
  obtain ⟨Gv, hGv⟩ := WedgeTK.exists_isRegVersion hX
  filter_upwards [hGv.ae_good, hA, ae_tendstoLocallyUniformlyOn_affPair hX h₁,
    ae_tendstoLocallyUniformlyOn_affPair hX h₂] with ω hg hcA hp1 hp2 b hb f hf
  have key : ∀ g : ℂ → ℝ, ∀ {M : ℝ≥0} {R δ : ℝ},
      Setup M R δ (volume.withDensity fun z => ENNReal.ofReal (g (-conj z))) →
      (∀ t B : ℝ, 0 < B → ∃ L, Tendsto (fun s => affPair (X ω)
        (volume.withDensity fun z => ENNReal.ofReal (g (-conj z))) s (t, B)) (𝓝[>] 0) (𝓝 L)) →
      ∃ L : ℝ, Tendsto (fun r => ∫ u, evalReg (wedgeField (lateralPart (X ω))
        (fun t => A t ω) Q) (foldedCircle ((b : ℂ) * -conj u) r)
          ∂(volume.withDensity fun z => ENNReal.ofReal (g z))) (𝓝[>] 0) (𝓝 L) := by
    intro g M R δ hS hP
    obtain ⟨L, hL⟩ := tendsto_wedge_aff hg hcA hS hP hb (Q := Q)
    refine ⟨L, hL.congr fun r => ?_⟩
    rw [← integral_withDensity_negConj
      (fun v => evalReg (wedgeField (lateralPart (X ω)) (fun t => A t ω) Q)
        (foldedCircle (aff 0 b v) r))]
    simp only [aff, Complex.ofReal_zero, zero_add]
  rcases hf with rfl | hf
  · exact key _ h₁ fun t B hB =>
      ⟨_, hp1.2.tendsto_at (show (t, B) ∈ (univ : Set ℝ) ×ˢ Ioi (0 : ℝ) from ⟨trivial, hB⟩)⟩
  · rw [Set.mem_singleton_iff] at hf
    subst hf
    exact key _ h₂ fun t B hB =>
      ⟨_, hp2.2.tendsto_at (show (t, B) ∈ (univ : Set ℝ) ×ˢ Ioi (0 : ℝ) from ⟨trivial, hB⟩)⟩

/-- The same for the reference wedge (`A` an `α`-wedge radial process). -/
theorem ae_contPair_wedgeRef {γ α : ℝ} {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ}
    (hX : IsFreeGFFModConstH X P') (hA : IsWedgeProcess α (Qc γ) A P') (ρ : TestFun H) :
    ∀ᵐ ω ∂P', ∀ b : ℝ, 0 < b → ∀ f ∈ ({ρ.1, -ρ.1} : Set (ℂ → ℝ)), ∃ L : ℝ,
      Tendsto (fun r => ∫ u, evalReg (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))
        (foldedCircle ((b : ℂ) * -conj u) r)
          ∂(volume.withDensity fun z => ENNReal.ofReal (f z))) (𝓝[>] 0) (𝓝 L) :=
  ae_contPair_wedge hX (WedgeCan4.ae_continuous_wedgeProcess hA) _ ρ

end WedgeCReg
end QuantumZipper
