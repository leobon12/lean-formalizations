/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ColCovTop
import InteractingSLE.Spec.Sec7.WallOrdReflInf
import InteractingSLE.Spec.Sec7.ColCovNoReturn
import InteractingSLE.Spec.Supplement.GW4Completion

/-!
# The outer collars' `K_s`-landing at the late pockets, PROVED

Packet PROVE-COLLAR-COVER (second round). PROVE-WALL-ORDER proved `R5Lift.R7OuterRefl(Inf)` on every reverse-contained
R.7 pocket test whose exceptional set contains R5-WALL's `outerExc(Inf)` (`WallOrd.r7OuterRefl_of_cfg`,
`WallOrd.r7OuterReflInf_of_cfg`). A late side test's pocket is such a test (`ready_bounded_facts`,
`ready_inf_facts`), and `colCovExc ⊇ lateOuterExc`, so:

* **`lateOuterRefl_of_subset`**: `LateOuterRefl i d X` for every `X ⊇ lateOuterExc`;
* **`lateOuterRefl_colCovExc`**: `LateOuterRefl i d (colCovExc d)` — the collar cover's outer input, with no input;
* **`colCovReflInput_holds`**: the tops' `ColCovReflInput`, PROVED;
* **`sideCollarInputExc_of_source_seed`**: the tops' collar input from SIDE-COLLAR2's source input and the
  seed-interval landings alone;
* **`colCovSeedInput_of_counterflowNoReturn`**: the seed input from the project's named no-return input
  `Theorem14.GW4Ident.CounterflowNoReturnStatement` (ruling R59; PROVE-CFNORETURN3 owns its R48-safe supply), read
  through the word context's generating trace of the counterflow;
* **`sideCollarInputExc_of_source_noReturn`**: the tops' collar input from the source input and the no-return.

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.ColCov

open Wire Wire.Current Wire.Current.SideTest

variable {Ω : Type} [MeasurableSpace Ω]

/-- **`LateOuterRefl` for every exceptional set containing the attachments** (WALL-ORDER's
`r7OuterRefl(Inf)_of_cfg` at the late pockets). -/
theorem lateOuterRefl_of_subset {i : BothLow} {d : WordObjects Ω} (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ seed ω, Continuous (d.leftWall seed ω)) {X : SideTest Ω → ℝ≥0 → Ω → Set ℂ}
    (hX : ∀ j q ω, lateOuterExc j d q ω ⊆ X j q ω) : LateOuterRefl i d X := by
  intro j hj q _
  refine ⟨fun hIf => ?_, fun hIf => ?_⟩
  · obtain ⟨hcfg, hψ, hc, hdom, heq⟩ := ready_bounded_facts (i := i) hj hRc (hLc j.seed) hIf
    refine WallOrd.r7OuterRefl_of_cfg hcfg hψ hc hdom heq fun ω _ => ?_
    have h := hX j q ω
    simp only [lateOuterExc, hIf, Bool.false_eq_true, ↓reduceIte] at h
    exact h
  · obtain ⟨hcfg, hψ, hc, hdom, heq⟩ := ready_inf_facts (i := i) hj hRc (hLc j.seed) hIf
    refine WallOrd.r7OuterReflInf_of_cfg hcfg hψ hc hdom heq fun ω _ => ?_
    have h := hX j q ω
    simp only [lateOuterExc, hIf, ↓reduceIte] at h
    exact h

/-- **The collar cover's outer input holds** (`X = colCovExc`). -/
theorem lateOuterRefl_colCovExc {i : BothLow} {d : WordObjects Ω} (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ seed ω, Continuous (d.leftWall seed ω)) : LateOuterRefl i d (colCovExc d) :=
  lateOuterRefl_of_subset hRc hLc fun _ _ _ => subset_union_right

/-- **The tops' `ColCovReflInput`, PROVED** (walls' continuity from the word context's wall versions). -/
theorem colCovReflInput_holds : ColCovReflInput := by
  intro Ωw _ _ baseWord _ hWordb hC index
  exact lateOuterRefl_colCovExc (hC.hWordvα index).continuous (fun q => (hC.hWordvL index q).continuous)

/-- **The tops' collar input from the source input and the seed-interval landings.** -/
theorem sideCollarInputExc_of_source_seed (hSrc : ColCovSourceInput) (hSeed : ColCovSeedInput) :
    T12Asm3.SideCollarInputExc :=
  sideCollarInputExc_of_colCov hSrc hSeed colCovReflInput_holds

/-- **The seed input from the counterflow's no-return** (`CounterflowNoReturnStatement` at universe `0`, ruling R59):
every word's counterflow is a centred counterflow of its GFF with infinite lifetime (`IsTwoAngleStripSystem`), and
the word's curve is a generating trace of its driver (`PhysCtx.hWordηtr`), so it is nonzero at positive times. -/
theorem colCovSeedInput_of_counterflowNoReturn (hnr : Theorem14.GW4Ident.CounterflowNoReturnStatement.{0}) :
    ColCovSeedInput := by
  refine colCovSeedInput_of_noReturn fun Ωw _ _ baseWord _ hWordb hC index => ?_
  have hS := hC.wordT index
  have h := hnr _ hS.kappa_pos hS.kappa_lt_four _ _ hS.boundaryData _ _ hS.gff _ _ hS.counterflow hS.lifetime
  filter_upwards [h, hC.hWordηtr index] with ω hω htr t ht
  have hne := hω _ htr t.toNNReal (Real.toNNReal_pos.2 ht)
  simpa only [Real.coe_toNNReal _ ht.le] using hne

/-- **The tops' collar input from the source input and the counterflow's no-return.** -/
theorem sideCollarInputExc_of_source_noReturn (hSrc : ColCovSourceInput)
    (hnr : Theorem14.GW4Ident.CounterflowNoReturnStatement.{0}) : T12Asm3.SideCollarInputExc :=
  sideCollarInputExc_of_source_seed hSrc (colCovSeedInput_of_counterflowNoReturn hnr)

end InteractingSLE.Sec7.ColCov
