import InteractingSLE.Spec.Sec7.Lemma71Capacity
import InteractingSLE.Spec.Sec7.TwoForceMain3Prop73
import InteractingSLE.Spec.Sec2.MartingaleFinalGeom
import InteractingSLE.Spec.Sec7.TwoForceWeights

/-!
# Lemma 7.1: from the mapped pocket driver to the embedded reference evolution

Packet PROVE-LEMMA71. Specification §7.1, Lemma 7.1 and its proof (`source/spec/p193-240.md` L576–L606,
pp. 223–225), the remark after Lemma 7.2 (L640, p. 227: "the embedded construction therefore covers every
admissible two-seed pair"), Theorem 2.4 (`source/spec/p001-048.md`, anchors `thm-2.4`, `thm-2.4-proof`, p. 35).

The last steps of the proof of Lemma 7.1 are: "The means in all the remaining components are those of the
three-curve result in Remark 6.7. In particular, in the active component they have the two seed heights (CPF2) …
Their time continuity is Proposition 6.5. The martingale characterization, Theorem 2.4, and integrated driving
uniqueness therefore give the stated conditional SLE law. … The global continuity and target transience of `γ`,
together with the Jordan boundary homeomorphism, give the endpoint assertions. Its terminal capacity cannot be
finite." (p. 225.)

This file proves these steps from their inputs.

* `thresholdTime_eq_top_of_fin_one`: with one force point on each side and weights `> −2` the continuation
  threshold never holds, so the lifetime given by Theorem 2.4 is `∞`.
* `HasTwoSeedMartingaleMeans κ rL rR P 𝓖 W`: the hypothesis of Theorem 2.4 for the two-seed word `(0⁻; 0⁺)` with
  weights `(rL; rR)`: every coupling mean of the Loewner chain of `W`, with the force points at the geometric images
  of the two seeds, is a local martingale before its point is swallowed.
* **`exists_isIntegratedSLEEvolution_of_twoSeedMartingaleMeans`**: Theorem 2.4's converse
  (`MartChar.isIntegratedSLEEvolution_geom_of_couplingMean`) applied to the mapped driver; with a transient
  generating trace this is exactly the reference evolution of Lemma 7.1.
* **`ae_transientTrace_of_fwdHull_eq`**: the endpoint assertions: if, almost surely, the mapped segment `γ` is a
  continuous simple path in `ℍ̄` from `0` to `∞` whose real-boundary times have empty interior, and the global
  driving process `W` generates its filled prefixes, then `W` almost surely has a continuous generating trace on
  `[0, ∞)` tending to `∞` (`Lemma71Capacity`; the terminal capacity is infinite).
* `Lemma71MappedSegmentStatement` (**named input**): the embedded three-curve construction of §7.1 at the level of
  the mapped pocket segment; see its docstring for the source of each clause.
* **`lemma71TraceReferenceStatement_of_mappedSegment`**: `Lemma71TraceReferenceStatement` (PROVE-SEC7-A4) from the
  named input. Conditional helper: it replaces no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

universe v

namespace InteractingSLE.Sec7.Lemma71

/-! ### The continuation threshold of two seeds with weights `> −2` -/

theorem neg_two_lt_sum_filter_fin_one {ρ : Fin 1 → ℝ} (hρ : -2 < ρ 0) (p : Fin 1 → Prop)
    [DecidablePred p] : -2 < ∑ i ∈ Finset.univ.filter p, ρ i := by
  rw [Finset.sum_filter, Fin.sum_univ_one]
  split_ifs <;> linarith

/-- With one force point on each side and weights `> −2`, the threshold condition never holds. -/
theorem not_thresholdCondition_of_fin_one {ρL ρR : Fin 1 → ℝ} (hL : -2 < ρL 0) (hR : -2 < ρR 0)
    (w : ℝ) (vL vR : Fin 1 → ℝ) : ¬ ForceWord.ThresholdCondition ρL ρR w vL vR := by
  rintro (h | h)
  · exact absurd h (not_le.2 (neg_two_lt_sum_filter_fin_one hL _))
  · exact absurd h (not_le.2 (neg_two_lt_sum_filter_fin_one hR _))

/-- With one force point on each side and weights `> −2`, the continuation threshold `T_*` of Theorem 2.4's
converse is `∞`. -/
theorem thresholdTime_eq_top_of_fin_one {ρL ρR : Fin 1 → ℝ} (hL : -2 < ρL 0) (hR : -2 < ρR 0)
    (w : ℝ≥0 → ℝ) (vL vR : Fin 1 → ℝ≥0 → ℝ) : MartChar.thresholdTime ρL ρR w vL vR = ⊤ := by
  have hempty : MartChar.thresholdSet ρL ρR w vL vR = ∅ :=
    eq_empty_iff_forall_notMem.2 fun t ht => not_thresholdCondition_of_fin_one hL hR _ _ _ ht
  simp only [MartChar.thresholdTime, hempty, Set.not_nonempty_empty, ↓reduceIte]

/-! ### Theorem 2.4 for the mapped driver -/

section Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The hypothesis of Theorem 2.4 for the two-seed word.** For the driver `W` and the force points at the
geometric images of the seeds `0⁻`, `0⁺` (`MartChar.geomL`, `MartChar.geomR`), with weights `(rL; rR)`: every
coupling mean `𝔥_t(z)`, `z ∈ ℍ`, for every choice of the bounded harmonic extensions of the force-word data, is a
local martingale in `𝓖` before `z` is swallowed. In Lemma 7.1 these are the means of the mapped field `h_ψ` given
the outer curves and the middle prefix: "in the active component they have the two seed heights (CPF2), with the
inherited logarithmic-derivative branch" (Remark 6.7), and "their time continuity is Proposition 6.5" (p. 225). -/
def HasTwoSeedMartingaleMeans (κ rL rR : ℝ) (P : Measure Ω) (𝓖 : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ u : Ω → ℝ≥0 → ℂ → ℝ,
    (∀ ω t, IsBoundedHarmonicExtension
      (forceBoundaryData κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
        (fun i => MartChar.geomL W LP.twoSeedXL i t ω - W t ω)
        (fun i => MartChar.geomR W LP.twoSeedXR i t ω - W t ω))
      (forceJumpSet (fun i => MartChar.geomL W LP.twoSeedXL i t ω - W t ω)
        (fun i => MartChar.geomR W LP.twoSeedXR i t ω - W t ω)) (u ω t)) →
    ∀ z ∈ H, MartChar.IsLocalMartingaleBefore 𝓖 P
      (fun ω => (QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z : WithTop ℝ≥0))
      (fun t ω => couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u ω t) z)

theorem isOrderedForceWord_twoSeed : IsOrderedForceWord LP.twoSeedXL LP.twoSeedXR :=
  ⟨fun _ _ _ => le_rfl, fun _ => le_rfl, fun _ _ _ => le_rfl, fun _ => le_rfl⟩

/-- **Theorem 2.4's converse for the mapped driver** (proof of Lemma 7.1, p. 225: "The martingale
characterization, Theorem 2.4, and integrated driving uniqueness therefore give the stated conditional SLE law").
A continuous adapted driver `W`, `W₀ = 0`, whose two-seed coupling means are local martingales, is with the
geometric force points and the Brownian motion of the martingale characterization an integrated
`SLE_κ(rL; rR)` evolution of the two-seed word. Its lifetime is `∞`, and a transient generating trace of the driver
is the trace assertion of the reference statement. -/
theorem exists_isIntegratedSLEEvolution_of_twoSeedMartingaleMeans {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓖 : Filtration ℝ≥0 mΩ} {κ rL rR : ℝ} (hκ : 0 < κ) (hL : -2 < rL)
    (hR : -2 < rR) {W : ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0)
    (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓖 W)
    (hmart : HasTwoSeedMartingaleMeans κ rL rR P 𝓖 W)
    (htr : ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η ∧
      Tendsto (fun t => ‖η t‖) atTop atTop) :
    ∃ (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓖 W VL VR B ζ ∧
        LP.HasTransientGeneratingTrace P W ζ := by
  have hE := MartChar.isIntegratedSLEEvolution_geom_of_couplingMean (ρL := fun _ : Fin 1 => rL)
    (ρR := fun _ : Fin 1 => rR) hκ isOrderedForceWord_twoSeed hW0 hWc hWa hmart
  refine ⟨_, _, _, _, hE, ?_⟩
  filter_upwards [htr] with ω hω
  obtain ⟨η, hη, hinf⟩ := hω
  rw [thresholdTime_eq_top_of_fin_one (ρL := fun _ : Fin 1 => rL) (ρR := fun _ : Fin 1 => rR) hL hR]
  exact ⟨η, hη, fun _ => hinf⟩

/-- **The endpoint assertions of Lemma 7.1** (p. 225: "The global continuity and target transience of `γ`, together
with the Jordan boundary homeomorphism, give the endpoint assertions. Its terminal capacity cannot be finite."). If,
almost surely, the mapped segment `γ` is a continuous simple path in `ℍ̄` from `0` tending to `∞` whose real-boundary
times have empty interior, and the global driving process `W` generates every filled prefix of `γ` as one of its
Loewner hulls, then `W` almost surely has a continuous generating trace on `[0, ∞)` tending to `∞` (the capacity
reparametrization of `γ`). -/
theorem ae_transientTrace_of_fwdHull_eq {P : Measure Ω} {γ : Ω → ℝ → ℂ} {W : ℝ≥0 → Ω → ℝ}
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω)
    (hγ : ∀ᵐ ω ∂P, ContinuousOn (γ ω) (Ici 0) ∧ InjOn (γ ω) (Ici 0) ∧ MapsTo (γ ω) (Ici 0) Hbar ∧
      γ ω 0 = 0 ∧ Tendsto (fun t => ‖γ ω t‖) atTop atTop ∧
      interior {u ∈ Ici (0 : ℝ) | 0 < u ∧ (γ ω u).im = 0} = ∅)
    (hK : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → ∃ s, 0 ≤ s ∧
      QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω) s = fillH (γ ω '' Icc 0 t)) :
    ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η ∧
      Tendsto (fun t => ‖η t‖) atTop atTop := by
  filter_upwards [hγ, hK] with ω ⟨hc, hinj, hH, h0, hinf, hR⟩ hKω
  have hWc' : Continuous fun s : ℝ => W s.toNNReal ω := (hWc ω).comp continuous_real_toNNReal
  have hW0' : (fun s : ℝ => W s.toNNReal ω) 0 = 0 := by
    simp only [Real.toNNReal_zero, hW0]
  obtain ⟨e, -, hη, hinfη⟩ :=
    exists_isGeneratingTrace_of_fwdHull_eq hWc' hW0' hc hinj hH h0 hinf hR hKω
  have hfun : (fun s : ℝ≥0 => (fun s : ℝ => W s.toNNReal ω) s) = fun t => W t ω := by
    funext s
    simp only [Real.toNNReal_coe]
  rw [hfun] at hη
  exact ⟨_, hη, hinfη⟩

end Martingale

/-! ### The named input and the reference statement -/

/-- **Named input: the embedded three-curve construction of §7.1, at the level of the mapped pocket segment**
(Specification §7.1: the setup and Figure 7.1, pp. 221–222; Lemma 7.1 and its proof, pp. 223–225; Remark 6.14,
pp. 217–218). Fix `0 < κ < 4` and angles `θ₁ < 0 < θ₂`. Take the probability space of a GFF `h` on `ℍ` with boundary
data `−a`, `b` (`a, b` large, so that Proposition 5.5 applies) carrying its flow lines `η_{θ₁}`, `η`, `η_{θ₂}`
("Setup", p. 221), a pocket `C` between the outer curves with first and last outer points `x₀`, `y₀`, and its map
`ψ : C → ℍ`, `x₀ ↦ 0`, `y₀ ↦ ∞`, with the inherited height convention (p. 222). On it there are:
* a filtration `𝓖` that retains the complete outer curves and the middle prefix (p. 224: "In the filtration
  retaining the complete outer curves");
* the mapped segment `γ = ψ(η|_{[σ_C, τ_C]})` in its own time on `[0, ∞)`. Almost surely it is a continuous simple
  path in `ℍ̄` from `0` that tends to `∞`, and its real-boundary times have empty interior (Remark 6.14, p. 217:
  "Its Jordan boundary homeomorphism makes `ψ(η_C)` a continuous simple path from zero to infinity" and "the mapped
  segment does not spend a nontrivial interval on `ℝ`"; the contact-order and traversal steps of the proof of
  Lemma 7.1, p. 224; `Lemma71Pocket.lean` proves this clause from the pocket data);
* the globally defined driving process `W` of the mapped segment: continuous, `W₀ = 0`, adapted to `𝓖`. Almost
  surely every filled prefix of `γ` is one of its Loewner hulls (Remark 6.14 with Proposition 6.12, p. 218: "a
  continuous Loewner driver up to the terminal capacity time of `ψ(η_C)`"; p. 225: "the globally defined admissible
  two-seed driving process"; pathwise, such a `W` exists iff the capacities of the prefixes are unbounded,
  `exists_global_driver_iff`);
* the martingale property of its two-seed coupling means with the seed weights (CPF2) `ρᴸ = θ₂χ/λ − 2`,
  `ρᴿ = −θ₁χ/λ − 2` (`HasTwoSeedMartingaleMeans`; p. 225: Lemma 6.2's history locality, Remark 6.7's three-curve
  means with the seed heights (CPF2), Proposition 6.5's time continuity).

The proof of `lemma71TraceReferenceStatement_of_mappedSegment` uses each clause. -/
def Lemma71MappedSegmentStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ θ₁ θ₂ : ℝ, θ₁ < 0 → 0 < θ₂ →
    ∃ (Ω : Type v) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓖 : Filtration ℝ≥0 mΩ) (γ : Ω → ℝ → ℂ) (W : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ContinuousOn (γ ω) (Ici 0) ∧ InjOn (γ ω) (Ici 0) ∧ MapsTo (γ ω) (Ici 0) Hbar ∧
        γ ω 0 = 0 ∧ Tendsto (fun t => ‖γ ω t‖) atTop atTop ∧
        interior {u ∈ Ici (0 : ℝ) | 0 < u ∧ (γ ω u).im = 0} = ∅) ∧
      (∀ ω, W 0 ω = 0) ∧ (∀ ω, Continuous fun t => W t ω) ∧ StronglyAdapted 𝓖 W ∧
      (∀ᵐ ω ∂P, ∀ t, 0 ≤ t → ∃ s, 0 ≤ s ∧
        QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω) s = fillH (γ ω '' Icc 0 t)) ∧
      HasTwoSeedMartingaleMeans κ (cpf2RhoL κ θ₂) (cpf2RhoR κ θ₁) P 𝓖 W

/-- **Lemma 7.1's reference evolution from the mapped pocket segment** (the trace part of Lemma 7.1 with the remark
after Lemma 7.2, p. 227: "As `θ₁ < 0 < θ₂` vary, (CPF2) ranges over every pair `ρᴸ, ρᴿ > −2` … The embedded
construction therefore covers every admissible two-seed pair"). From the named input `Lemma71MappedSegmentStatement`:
the angles with the given weights exist (`exists_angles_cpf2_eq`); Theorem 2.4's converse makes the mapped driver
with its geometric force points an integrated two-seed `SLE_κ(ρᴸ; ρᴿ)` evolution with lifetime `∞`; and the capacity
reparametrization of the mapped segment is its transient generating trace. Conditional helper: it replaces no source
theorem. -/
theorem lemma71TraceReferenceStatement_of_mappedSegment (h : Lemma71MappedSegmentStatement.{v}) :
    Lemma71TraceReferenceStatement.{v} := by
  intro κ hκ hκ4 rL rR hL hR
  obtain ⟨θ₁, θ₂, hθ₁, hθ₂, hρL, hρR⟩ := exists_angles_cpf2_eq hκ hκ4 hL hR
  obtain ⟨Ω, mΩ, P, hP, 𝓖, γ, W, hγ, hW0, hWc, hWa, hK, hmart⟩ := h κ hκ hκ4 θ₁ θ₂ hθ₁ hθ₂
  rw [hρL, hρR] at hmart
  obtain ⟨VL, VR, B, ζ, hE, htr⟩ := exists_isIntegratedSLEEvolution_of_twoSeedMartingaleMeans hκ hL hR
    hW0 hWc hWa hmart (ae_transientTrace_of_fwdHull_eq hW0 hWc hγ hK)
  exact ⟨Ω, mΩ, P, hP, 𝓖, W, VL, VR, B, ζ, hE, htr⟩

end InteractingSLE.Sec7.Lemma71
