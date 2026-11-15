/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB7aCmpPath
import InteractingSLE.Spec.Supplement.CollarActivity
import InteractingSLE.Spec.Sec4.Aux25Term
import InteractingSLE.Spec.Sec2.CriticalLifetime

/-!
# GB7a's pathwise comparison input, proved; Lemma GB7a; interface 4 from Lemma G7 alone

Packet PROVE-GB7A3. Main results:

* `GB7a.gb7aCmpInput : GB7a.GB7aCmpInput` — **the pathwise half of Lemma GB7a's proof** (named input of
  PROVE-GB7A2): almost surely, a visit of the open interval between a right mark `k` and the next right mark
  produces the comparison picture `RightCmp` at a rational restart time (`GB7a.rightCmpPath_of_visit`, with
  injectivity of the trace from Aux. lemma 25 (`Theorem15.aux25Statement`) and the convergence of the state at a
  finite lifetime from Aux. lemma 3 (`IsIntegratedSLEEvolution.ae_tendsto_threshold`)); the left side is the right
  side of the reflected evolution and the reflected trace `−η̄`;
* `Supp8.gb7aFlowStatement : Supp8.GB7aFlowStatement` — **Lemma GB7a for one flow line** (supplement §8.7,
  p. 523), with the comparison of Aux. lemmas 61–64 (`GB7a.measure_eq_zero_of_evolution`, PROVE-GB7A2);
* `Supp7.g7GB7aFirstHitStatement_of_g7` — Theorem 1.5's interface 4 (`Theorem15D5.G7GB7aFirstHitStatement`) from
  Lemma G7 at the retained pair (`Supp7.G7RetainedPairStatement`) alone.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace GB7a

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- The reflected force word is ordered. -/
theorem isOrderedForceWord_reflect (hord : IsOrderedForceWord xL xR) : IsOrderedForceWord (-xR) (-xL) :=
  ⟨fun _ _ hij => neg_le_neg (hord.2.2.1 hij), fun i => neg_nonpos.2 (hord.2.2.2 i),
    fun _ _ hij => neg_le_neg (hord.1 hij), fun i => neg_nonneg.2 (hord.2.1 i)⟩

/-- **The comparison picture from a visit, left side (one path)**: the right side for the reflected path and
the reflected trace `−η̄`. -/
theorem leftCmpPath_of_visit (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ)
    (hord : IsOrderedForceWord xL xR) (hη : IsGeneratingTrace w ζ η)
    (hinj : InjOn η {t | (t : ℝ≥0∞) ≤ ζ})
    (hlimζ : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ → ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
      Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)))
    {k : Fin nL} {a : ℝ} (hnext : ∀ j, xL j < xL k → xL j ≤ a)
    (hvis : ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ∧ ∃ y ∈ Ioo a (xL k), η t = y) :
    ∃ q : ℚ, RightCmpPath ρR ρL (fun t => -w t) (fun i t => -vR i t) (fun i t => -vL i t) ζ k none
      (∑ i ∈ univ.filter (fun i => xL k ≤ xL i), ρL i) (q : ℝ).toNNReal := by
  have hinj' : InjOn (fun t => LP.reflectC (η t)) {t | (t : ℝ≥0∞) ≤ ζ} := fun s hs t ht hst => by
    have := congrArg LP.reflectC hst
    simp only [LP.reflectC_reflectC] at this
    exact hinj hs ht this
  have hlim' : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ → ∃ (w₀ : ℝ) (vL₀ : Fin nR → ℝ) (vR₀ : Fin nL → ℝ),
      Tendsto (fun t => ((-w) t, fun i => (fun i => -vR i) i t, fun i => (fun i => -vL i) i t)) (𝓝[<] T)
        (𝓝 (w₀, vL₀, vR₀)) := by
    intro T hT hζ
    obtain ⟨w₀, vL₀, vR₀, hl⟩ := hlimζ T hT hζ
    refine ⟨-w₀, -vR₀, -vL₀, ?_⟩
    have hc : Continuous fun z : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) => (-z.1, -z.2.2, -z.2.1) := by
      fun_prop
    exact (hc.tendsto _).comp hl
  have hvis' : ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ∧ ∃ y ∈ Ioo ((-xL) k) (-a), LP.reflectC (η t) = y := by
    obtain ⟨t, ht, y, hy, he⟩ := hvis
    refine ⟨t, ht, -y, ⟨by simp only [Pi.neg_apply]; linarith [hy.2], by linarith [hy.1]⟩, ?_⟩
    rw [he]
    simp [LP.reflectC]
  have hnext' : ∀ j, (-xL) k < (-xL) j → -a ≤ (-xL) j := fun j hj => by
    simp only [Pi.neg_apply, neg_lt_neg_iff] at hj
    simp only [Pi.neg_apply, neg_le_neg_iff]
    exact hnext j hj
  obtain ⟨q, hq⟩ := rightCmpPath_of_visit h.reflect (isOrderedForceWord_reflect hord)
    (LP.isGeneratingTrace_reflect hη) hinj' hlim' hnext' hvis'
  have e : univ.filter (fun i => (-xL) i ≤ (-xL) k) = univ.filter (fun i => xL k ≤ xL i) :=
    Finset.filter_congr fun i _ => by simp only [Pi.neg_apply, neg_le_neg_iff]
  rw [e] at hq
  exact ⟨q, hq⟩

/-- **The pathwise half of Lemma GB7a's proof** (named input of PROVE-GB7A2, now a theorem). -/
theorem gb7aCmpInput : GB7aCmpInput.{u} := by
  intro κ hκ hκ4 nL nR xL xR ρL ρR hord Ω mΩ P _ 𝓕 W VL VR B ζ hE η hη
  have hinj := Theorem15.aux25Statement κ hκ hκ4 xL xR ρL ρR hord P 𝓕 W VL VR B ζ hE
  have hlim := hE.ae_tendsto_threshold hκ
  have hpath := hE.2.2.2.2
  refine ⟨fun k a' _ hnext => ?_, fun k a _ hnext => ?_⟩
  · filter_upwards [hinj, hlim, hpath, hη] with ω h1 h2 h3 h4 hvis
    obtain ⟨q, hq⟩ := rightCmpPath_of_visit h3.isForcePath hord h4 (h1 _ h4)
      (fun T hT hζ => let ⟨w₀, vL₀, vR₀, hl, _⟩ := h2 T hT hζ; ⟨w₀, vL₀, vR₀, hl⟩) hnext hvis
    exact ⟨q, rightCmp_iff.2 hq⟩
  · filter_upwards [hinj, hlim, hpath, hη] with ω h1 h2 h3 h4 hvis
    obtain ⟨q, hq⟩ := leftCmpPath_of_visit h3.isForcePath hord h4 (h1 _ h4)
      (fun T hT hζ => let ⟨w₀, vL₀, vR₀, hl, _⟩ := h2 T hT hζ; ⟨w₀, vL₀, vR₀, hl⟩) hnext hvis
    exact ⟨q, rightCmp_iff.2 hq⟩

end GB7a

namespace Supp8

/-- **Lemma GB7a for one flow line** (supplement §8.7, p. 523): unconditional. -/
theorem gb7aFlowStatement : GB7aFlowStatement.{u} :=
  gb7aFlowStatement_of_cmpInput GB7a.gb7aCmpInput

end Supp8

namespace Supp7

/-- **Theorem 1.5's interface 4 from Lemma G7 alone**: `G7 + GB7a ⟹ G7GB7aFirstHitStatement`, with GB7a proved. -/
theorem g7GB7aFirstHitStatement_of_g7 (hG7 : G7RetainedPairStatement.{u}) :
    Theorem15D5.G7GB7aFirstHitStatement.{u} :=
  g7GB7aFirstHitStatement_of_g7_gb7a hG7 Supp8.gb7aFlowStatement.{0}

end Supp7

end InteractingSLE
