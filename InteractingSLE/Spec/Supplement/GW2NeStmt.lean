/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NeEnd
import InteractingSLE.Spec.Supplement.GW2NiUncTrans
import InteractingSLE.Spec.Supplement.GW2NiFin

/-!
# `UncEndStatement` is proved

Packet PROVE-GW2-NEARIMG2, decision D56. Almost surely, on the good counterflow records, the uncapped joined driver of
an angle whose explored curve never touches the retained prefix has a canonical relative driver (`IsCanonUX`):

* the counterflow facts and the arc bound come from the good set of a candidate of the angle (`schedGTX_spec`), the
  retained tip `α(s) ∈ ℍ` from GB6's record event (`gb6TS`, part of `goodX`);
* the uncapped driver is regular with a transient generating trace (`uncRegStatement`, time-ordered histories);
* `exists_canon_of_noContact` (one sample, `GW2NeEnd`).

The death and the history's success are not needed: the hull identity holds at every clock value.

So `StageLawUXStatement` follows from the capped stage law and the versions' exhaustion alone
(`stageLawUXStatement_of_stageLawX`), and for RELDET's death family from the capped stage law alone
(`stageLawUXStatement_of_deathFamily`).

* `alpha_ne_zero_of_gb6TS`, **`uncEndStatement`**, `stageLawUXStatement_of_stageLawX`,
  `stageLawUXStatement_of_deathFamily`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2Ni

open Exist Staged StagedLaw Supp8.GB6 GW2TipSystem GW2Rz

/-- **The retained tip is off `0` on GB6's record event**: the record's trace at `s` is the counterflow's tip, which
lies in `ℍ`. -/
theorem alpha_ne_zero_of_gb6TS {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω} {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace (W · ω) ⊤ α) (hW : Continuous (W · ω)) (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤)
    {s : ℝ≥0} (hrec : cfRec s W ζ ω ∈ gb6TS s) : α s ≠ 0 := by
  have hsζ : (s : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
  have hpre := Supp8.GB6.GaugeE.record_prefix_eq s hW0 hW.continuousOn hsζ
  have htr : LP.traceAt s (fun t : ℝ≥0 => rdrv (cfRec s W ζ ω) t) = α s := by
    rw [← LP.traceAt_eq_of_isGeneratingTrace hα hW.continuousOn hW0 (ENNReal.coe_lt_top : (s : ℝ≥0∞) < ⊤)]
    refine LP.traceAt_congr fun t ht => ?_
    have h : rdrv (cfRec s W ζ ω) t = Ito.rpath (W · ω) t := hpre ⟨t.coe_nonneg, NNReal.coe_le_coe.2 ht⟩
    rw [h]
    simp only [Ito.rpath, Real.toNNReal_coe]
  have hH : α s ∈ H := htr ▸ hrec.2.1
  exact ne_zero_of_mem_H hH

/-- **`UncEndStatement`** (D56): on the good counterflow records, when the uncapped explored curve never touches the
retained prefix, the uncapped joined driver has a canonical relative driver. -/
theorem uncEndStatement (h13 : Exist.Theorem13Statement.{u}) : UncEndStatement.{u} := by
  intro Ω _ _ c r l i hg hord
  filter_upwards [uncRegStatement h13 Ω c r l i hord, (schedGTX_spec h13 c r l (angCand i 0)).2.2]
    with ξ hU hGT hgx _ _ hcont
  obtain ⟨hUc, hU0, hUη, htr⟩ := hU
  have hξ : ξ ∈ schedGTX h13 c r l (angCand i 0) := hGT.2 hgx
  obtain ⟨-, ⟨hα, hW, hW0, hζ⟩, harc, -, -⟩ := (schedGTX_spec h13 c r l (angCand i 0)).1 ξ hξ
  have hαs : c.α ξ c.s ≠ 0 := alpha_ne_zero_of_gb6TS hα hW hW0 hζ hgx.1
  obtain ⟨Wc, hWc, hWc0, hK, htrc, M, hM⟩ :=
    exists_canon_of_noContact c.W c.ζ ξ hα hW hW0 hζ hg.2 hg.1 harc hUc hU0 hUη hcont hαs htr
  exact ⟨Wc, hWc, hWc0, fun t _ _ => hK t, htrc, M, fun t _ => hM t⟩

/-- **The uncapped stage law from the capped one** (D50 with D56 closed): `UncEndStatement` is no longer an input. -/
theorem stageLawUXStatement_of_stageLawX (h13 : Exist.Theorem13Statement.{u}) (ver : GW2Rv.SchedVerXFamily.{u})
    (hlaw : GW2Bh.StageLawXStatement h13 ver) (hexh : ExhStopStatement ver) : StageLawUXStatement.{u} :=
  stageLawUXStatement_of_capped h13 ver hlaw hexh (uncEndStatement h13)

/-- **The uncapped stage law for RELDET's death family**, from its capped stage law alone. -/
theorem stageLawUXStatement_of_deathFamily (h13 : Exist.Theorem13Statement.{u})
    (hlaw : GW2Bh.StageLawXStatement h13 (GW2Rd.schedVerXDeathFamily h13)) : StageLawUXStatement.{u} :=
  stageLawUXStatement_of_stageLawX h13 _ hlaw (exhStopStatement_deathFamily h13)

end InteractingSLE.Theorem14.GW2Ni
