/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Q3ChainWord

/-!
# GB6's relative configuration with its actual words

Packet PROVE-Q3-REL3, item (A) of `planning/handoffs/PROVE-Q3-REL2.md` §4.1 completed. PROVE-Q3-REL2's
`Q3Kernel.ae_exists_isRelConfigOff_gb6` gives GB6's relative configuration (`Q3Rel.IsRelConfigOff`) for **any** words
satisfying the word clauses. Here the words are GB6's actual ones:

* the initial word `β₀` is the counterflow force data of the chart field's word `β = gb6WordOfRec κ θ c r`
  (`cfData (16/κ) β.fn β.jumps`, jump set `cfJumps`; off its jumps it is `β.fn`, `Sec4.forceBoundaryData_flowLine`);
* the counterflow word `βE` at the physical time `t` is the counterflow's own force data at its flowed marks
  (`cfFlowedData (16/κ) b' J' W t`; by `Q3Chain.ae_gap_eq_markPos` this is the coupling's force data at `t`);
* the relative word `βu` at the relative time `u = a(t)` is `β`'s force data at the marks flowed by the relative driver
  (`cfFlowedData (16/κ) β.fn β.jumps Wr u` — the force data of the relative coupling once its marks are the flowed
  marks).

**`ae_exists_isRelConfigOff_gb6_words`**: almost surely on GB6's interior-tip event, for all counterflow times
`0 < t < t₁ < T_c`, every choice of bounded harmonic extensions of these three words and the candidate mean gives
`IsRelConfigOff` with `χ = χ(16/κ)` and `λ = π/√(16/κ)`. Only the means remain (the bounded harmonic extensions exist
by the frozen companion `existsUnique_isBoundedHarmonicExtension_forceBoundaryData`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd)

universe u

namespace InteractingSLE.Supp8.Q3Chain

open GB6 (relMap relInv relClock firstContactTime sphereInv gb6WordOfRec gb6Rec)
open Q3Rel (invHull relLog relBad IsRelConfigOff)

/-- **GB6's relative configuration with its actual words, almost surely** (`0 < κ < 4`). Setting of
`Q3Kernel.ae_exists_isRelConfigOff_gb6`; `c` any boundary word (the flow's data), `(b', J')` the counterflow's boundary
data. Almost surely on `{s < ζα, α(s) ∈ ℍ}` there is a frozen flow driver `U` (equal to `Wα` on `[0, t₂]`, `t₂ > s`)
such that for all counterflow times `0 < t < t₁ < T_c` there is a relative chain `(Wr, ηr)` at `u = a(t) > 0` with
`Ψ(K'_t) = K̃_u`, for which every triple of bounded harmonic extensions `G₀`, `GE`, `G` of GB6's three words and the
candidate mean `v` form an `IsRelConfigOff`. -/
theorem ae_exists_isRelConfigOff_gb6_words {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {J : Finset ℝ}
    {θ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {Wα W : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {α γ : Ω → ℝ≥0 → ℂ}
    (hF : IsFlowLineDriver κ b J θ P h Wα ζα) (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    (hW : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω))
    (b' : ℝ → ℝ) (J' : Finset ℝ) (c : Restart.BoundaryWord) (s : ℝ≥0) :
    ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      ∃ (U : ℝ → ℝ) (t₂ : ℝ), (s : ℝ) < t₂ ∧ (∀ r ∈ Icc (0 : ℝ) t₂, U r = Wα r.toNNReal ω) ∧
        ∀ t t₁ : ℝ≥0, 0 < t → t < t₁ →
          (t₁ : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ ω t : OnePoint ℂ))
            ((fun t => (α ω t : OnePoint ℂ)) '' Icc 0 s) →
          ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ), Continuous Wr ∧ Wr 0 = 0 ∧ IsLoewnerTrace Wr ηr ∧
            0 < relClock U s (fun r : ℝ => W r.toNNReal ω) t ∧
            relMap U s '' fwdHull (fun r : ℝ => W r.toNNReal ω) t =
              fwdHull Wr (relClock U s (fun r : ℝ => W r.toNNReal ω) t) ∧
            ∀ G₀ GE G v : ℂ → ℝ,
              IsBoundedHarmonicExtension
                (cfData (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
                  (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps)
                (cfJumps (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
                  (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps) G₀ →
              IsBoundedHarmonicExtension (cfFlowedData (16 / κ) b' J' (fun r : ℝ => W r.toNNReal ω) t)
                (cfFlowedJumps b' J' (fun r : ℝ => W r.toNNReal ω) t) GE →
              IsBoundedHarmonicExtension
                (cfFlowedData (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
                  (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps Wr
                  (relClock U s (fun r : ℝ => W r.toNNReal ω) t))
                (cfFlowedJumps (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
                  (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps Wr
                  (relClock U s (fun r : ℝ => W r.toNNReal ω) t)) G →
              (∀ z, v z = G (fwdMap Wr (relClock U s (fun r : ℝ => W r.toNNReal ω) t) (relMap U s z)) -
                QuantumZipper.chiC (16 / κ) *
                  ((logDerivFwd Wr (relClock U s (fun r : ℝ => W r.toNNReal ω) t) (relMap U s z)).im +
                    (relLog U s z).im)) →
              IsRelConfigOff (invHull U s) (relMap U s) (relInv U s) (relLog U s) (relBad U s)
                (fun r : ℝ => W r.toNNReal ω) Wr (fun r : ℝ => γ ω r.toNNReal) ηr t
                (relClock U s (fun r : ℝ => W r.toNNReal ω) t) (QuantumZipper.chiC (16 / κ))
                (Real.pi / Real.sqrt (16 / κ))
                (cfData (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
                  (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps)
                (cfFlowedData (16 / κ) b' J' (fun r : ℝ => W r.toNNReal ω) t)
                (cfFlowedData (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
                  (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps Wr
                  (relClock U s (fun r : ℝ => W r.toNNReal ω) t))
                (cfJumps (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
                  (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps)
                (cfFlowedJumps b' J' (fun r : ℝ => W r.toNNReal ω) t)
                (cfFlowedJumps (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
                  (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps Wr
                  (relClock U s (fun r : ℝ => W r.toNNReal ω) t)) G₀ GE G v := by
  filter_upwards [Q3Kernel.ae_exists_isRelConfigOff_gb6 hκ hκ4 hF hα hW s, hW] with ω hω hWω hs hsH
  obtain ⟨U, t₂, hst₂, hUeq, hcfg⟩ := hω hs hsH
  refine ⟨U, t₂, hst₂, hUeq, fun t t₁ ht0 htt₁ ht₁ => ?_⟩
  obtain ⟨Wr, ηr, hWr, hWr0, hηr, hu, hK, hall⟩ := hcfg t t₁ ht0 htt₁ ht₁
  refine ⟨Wr, ηr, hWr, hWr0, hηr, hu, hK, fun G₀ GE G v hG₀ hGE hG hv => ?_⟩
  have hWc : Continuous fun r : ℝ => W r.toNNReal ω := hWω.1.comp continuous_real_toNNReal
  have hWc0 : (fun r : ℝ => W r.toNNReal ω) 0 = 0 := by simp [hWω.2.1]
  have hη := isLoewnerTrace_of_isGeneratingTrace hWω.2.2
  exact hall _ _ _ _ _ _ _ _ G₀ GE G v hG₀ hGE hG
    (isSideWord_cfFlowedData hη hWc hWc0 t.2 (16 / κ))
    (isSideWord_cfFlowedData hηr hWr hWr0 hu.le (16 / κ))
    (isFlowedWord_cfFlowedData hηr hWr hWr0 hu (16 / κ)) hv

end InteractingSLE.Supp8.Q3Chain
