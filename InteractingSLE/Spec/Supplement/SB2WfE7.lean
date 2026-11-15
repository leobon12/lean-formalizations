/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WfRel
import InteractingSLE.Spec.Supplement.SB2WfAe
import InteractingSLE.Spec.Supplement.SB2VhLife
import InteractingSLE.Spec.Supplement.SB2VrRad
import InteractingSLE.Spec.Supplement.SB2WdInd
import InteractingSLE.Spec.Supplement.SB2WfSwal

/-!
# E7 from the junction fact

Packet PROVE-T14-SB2WORD (round 3, decision D18). The lifetime reconstruction E7 (`Vh.SB2RemainderLifeStatement`)
follows from one fact about the lower walk alone:

* **`SB2JunctionStatement`** (the junction fact): almost surely at a launch, every relative point `r` right of the
  entry whose right neighbourhood in the launch word is an old lower side (height `−λ + (π/2)χ`) is read back through
  the inverse launch chart to a real point `p` with `L ≤ p` (`L` the leftmost real point of the prefix) which, right
  of `u`, is not a bad point of the upper flow. These are the bases and the left touch points of the walk's pieces;
  the source excludes them from the bad set by the restart rule and by the boundary-hitting criterion of the staged
  pieces. Points `p ∈ [L, u)` are excluded inside E7: `L` is visited by the flow, and `(L, u)` is swallowed by the
  flow when it first visits `L` (`gen_end_ne_of_mem_closure_fill`).
* **`sb2RemainderLifeStatement_of_junction`**: E7. `Vg ≤ thr` is the first direction (`ae_le_thr_of_good`, with NOJUMP's
  `Vr.ae_notMem_closure_badSet`: the flow stays off the closed bad set before `ζ`). Conversely at a finite `Vg` the flow
  ends at a bad point (`Vr.ae_tip_bad_of_isFlowLine`), read back from the relative tip (`readback`); the relative tip
  is then real, not at the entry (the flow does not revisit `L`), and by the second clause (`rel_bad_left`,
  `rel_bad_right`) or the junction fact it is a bad relative point, so the threshold comes by `Vg`
  (`thr_le_of_bad_left`, `thr_le_of_bad_right`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Wf

open Exist Exist.Staged Exist.StagedLaw Restart GW1W Lv Supp8.Q3Stop Restart.DomainMarkov.K2
  Sec7.PocketTraversal
open PiecewiseConstantBoundaryData (rightLim)

/-- **The junction fact** (supplement pp. 631–633): almost surely at a launch of the lower walk, every relative point
`r` right of the entry at which the launch word continues with the old lower-side height `−λ + (π/2)χ` is read back
through the inverse launch chart to a real point `p` at or right of the prefix's leftmost real point which, right of
the upper seed `u`, is not a bad point of the upper flow. -/
def SB2JunctionStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞),
    SB2LaunchProblem κ b jumps P h E k u ψ η ζ →
    ∀ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ b jumps P h (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) β Y →
    ∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E (k + 1) →
      ∀ g : ℂ → ℂ, ContinuousOn g {z | 0 ≤ z.im} → EqOn g (Lv.launchChart κ b jumps E (k + 1) ω₀).2.1 H →
      ∀ r : ℝ, launchEntry κ b jumps E (k + 1) u ω₀ < r →
        (∃ ε > 0, ∀ y ∈ Ioo r (r + ε), y ∉ (β ω₀).jumps →
          (β ω₀).fn y = -sleLambda κ - -(Real.pi / 2) * chiC κ) →
        ∀ p : ℝ, g (r : ℂ) = p → realMin (lowerPrefix κ b jumps E (k + 1) u ω₀) ≤ p ∧
          (u < p → -2 < Sec4.cumWeightRight κ (rightLim b p + ψ * chiC κ))

/-- **The flow does not end in `[L, u)`** (pathwise): `L` is visited at `t_L < ζ` and is then not bad, and every
point of `(L, u)` is swallowed by the flow at `t_L` (strictly between the real trace points `L` and `u`), so it is
not the endpoint unless visited before (`gen_end_ne_of_mem_closure_fill`). -/
theorem not_mem_Ico_of_flow {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {u L p : ℝ} {w : ℝ≥0 → ℝ} {B : Set ℂ}
    (hη0 : η 0 = u) (hηc : ContinuousOn η {t | (t : ℝ≥0∞) ≤ ζ})
    (hg : IsGeneratingTrace w ζ (fun t => η t - u))
    (hpath : ContinuousOn w {t | (t : ℝ≥0∞) < ζ} ∧ w 0 = 0) (hv : firstVisit η ζ L < ζ)
    (hnot : 0 < ζ → ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → η t - u ∉ closure B) (hζ0 : 0 < ζ) {σT : ℝ≥0}
    (hζT : ζ = (((firstVisit η ζ L).toNNReal + σT : ℝ≥0) : ℝ≥0∞))
    (hbad : η ((firstVisit η ζ L).toNNReal + σT) - u ∈ B)
    (hzp : η ((firstVisit η ζ L).toNNReal + σT) = (p : ℂ)) (hLp : L ≤ p) (hpu : p < u) : False := by
  set tL := (firstVisit η ζ L).toNNReal with htL
  set Tz : ℝ≥0 := tL + σT with hTz
  obtain ⟨-, -, hηL⟩ := Lw.firstVisit_spec hηc (hv.trans_le le_top)
  have htLζ : (tL : ℝ≥0∞) < ζ := by
    rw [htL, ENNReal.coe_toNNReal (hv.trans_le le_top).ne]; exact hv
  -- no visit to `p` before the end
  have hnv : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → η t ≠ (p : ℂ) := by
    intro t ht he
    refine hnot hζ0 t ht ?_
    rw [he, ← hzp]
    exact subset_closure hbad
  rcases hLp.lt_or_eq with hLlt | hLeq
  swap
  · refine hnv tL htLζ ?_
    rw [hηL, hLeq]
  -- the swallowed interval
  have hTz : (Tz : ℝ≥0∞) = ζ := hζT.symm
  have hgT : IsGeneratingTrace w (Tz : ℝ≥0∞) (fun t => η t - u) := by rw [hTz]; exact hg
  have hwT : ContinuousOn w {r | (r : ℝ≥0∞) < (Tz : ℝ≥0∞)} := by rw [hTz]; exact hpath.1
  have htLT : tL < Tz := by
    have := htLζ
    rw [← hTz] at this
    exact ENNReal.coe_lt_coe.1 this
  set ηs : ℝ → ℂ := fun r => η r.toNNReal - u with hηs
  have hcs : ContinuousOn ηs (Icc 0 (tL : ℝ)) := by
    refine hg.2.1.comp continuous_real_toNNReal.continuousOn fun r hr => ?_
    show ((r.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ζ
    exact (ENNReal.coe_le_coe.2 ((Real.toNNReal_le_iff_le_coe).2 hr.2)).trans htLζ.le
  have hHbar : MapsTo ηs (Icc 0 (tL : ℝ)) Hbar := by
    intro r hr
    have hlt : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ :=
      (ENNReal.coe_le_coe.2 ((Real.toNNReal_le_iff_le_coe).2 hr.2)).trans_lt htLζ
    have h1 := Restart.IsGeneratingTrace.mem_closure_self hg hpath.1 hpath.2 hlt
    have h2 : ηs r ∈ closure H := closure_mono sdiff_subset h1
    rwa [closure_H] at h2
  have hu₁ : ((tL : ℝ)) ∈ Icc (0 : ℝ) tL := ⟨tL.coe_nonneg, le_rfl⟩
  have hu₂ : (0 : ℝ) ∈ Icc (0 : ℝ) tL := ⟨le_rfl, tL.coe_nonneg⟩
  have hv1 : ηs tL = ((L - u : ℝ) : ℂ) := by
    have e1 : ηs tL = η tL - u := by simp only [hηs, Real.toNNReal_coe]
    rw [e1, hηL]; push_cast; ring
  have hv2 : ηs 0 = 0 := by simp [hηs, hη0]
  have hpA : ((p - u : ℝ) : ℂ) ∉ (fun t => η t - u) '' Icc 0 tL := by
    rintro ⟨t, ht, he⟩
    have he' : η t = (p : ℂ) := by
      have := congrArg (· + (u : ℂ)) he
      simp only [sub_add_cancel] at this
      rw [this]; push_cast; ring
    exact hnv t ((ENNReal.coe_le_coe.2 ht.2).trans_lt htLζ) he'
  have himg : (fun t => η t - u) '' Icc 0 tL = ηs '' Icc 0 (tL : ℝ) := by
    rw [hηs, image_toNNReal_Icc (fun t => η t - u) tL.coe_nonneg, Real.toNNReal_coe]
  have hpK : ((p - u : ℝ) : ℂ) ∈ closure (fillH ((fun t => η t - u) '' Icc 0 tL)) := by
    rw [himg]
    refine YuanCharacterisation.mem_closure_fillH_of_lt_of_lt hcs hHbar hu₁ hu₂ (by rw [hv1]; simp)
      (by rw [hv2]; simp) (by rw [hv1]; simp; linarith) (by rw [hv2]; simp; linarith) ?_
    rw [← himg]
    exact hpA
  have hne := gen_end_ne_of_mem_closure_fill hgT hwT hpath.2 htLT hpA hpK
  apply hne
  show η Tz - u = ((p - u : ℝ) : ℂ)
  rw [hzp]; push_cast; ring

/-- **E7 from the junction fact.** -/
theorem sb2RemainderLifeStatement_of_junction (hJ : SB2JunctionStatement.{u}) :
    Vh.SB2RemainderLifeStatement.{u} := by
  intro κ b jumps Ω _ _ P _ h E k u ψ η ζ HP I u₀ D w _hw
  set ws : ExplSpec := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hwsdef
  have hκ := HP.kappa_pos
  have hκ4 := HP.kappa_lt_four
  have hb := HP.boundary
  obtain ⟨β, Y, hW, hβ⟩ := sb2StageActiveWord2Statement κ hκ hκ4 b jumps hb P h HP.field HP.admissible E
    HP.staged HP.pieces_regular HP.drivers_regular k
  have hws := isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := -(Real.pi / 2))
    ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hRL := regLaunches_of_stagedPiecesRegular (HP.pieces_regular ws hws)
  obtain ⟨_, _, Wp, _, _, _, -, hcoup, hgenη⟩ := HP.flow
  filter_upwards [ae_le_thr_of_good HP I D.event w, hβ u HP.seed_nonpos, ae_word_eq_shift HP I hW, hW.2.2.1,
    hJ κ b jumps P h E k u ψ η ζ HP β Y hW, Vr.ae_tip_bad_of_isFlowLine HP.flow,
    Vr.ae_notMem_closure_badSet hκ hκ4 hb HP.field HP.flow, hgenη, hRL, hcoup.1.2.2.2.2] with ω hle hβω heqω hTω
    hJω htipω hnotω hgω hRLω hpathω
  intro hF hT hcell W Vg Γ hWc hW0 hΓ hlink
  set m := launchEntry κ b jumps E (k + 1) u ω with hmdef
  set L := realMin (lowerPrefix κ b jumps E (k + 1) u ω) with hLdef
  -- the launch chart and a continuous boundary extension of its inverse
  obtain ⟨⟨c₀, θ₀⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hF
  have hc₀ : Lv.launchChart κ b jumps E (k + 1) ω =
      stChart (ExplState.run κ b jumps ws (fun j => E ws j ω) (k + 1)) := by
    rw [launchChart_eq hcθ, (eq_launch_of_launches _ _ hcθ).2.2]
  have hcc' := SB.LuM.isConformal_runChart_of_reg ws hRLω (k + 1)
  have hcc : (Lv.launchChart κ b jumps E (k + 1) ω).IsConformal := by rw [hc₀]; exact hcc'
  obtain ⟨g, hgc, hgi, -, -⟩ := SB.Lw.exists_bdryMap_of_hasProperBdryExt hcc'
    (GW1P.isClosed_pieces_run (κ := κ) (b := b) (jumps := jumps) ws (fun j => E ws j ω) hRLω (k + 1)).1
  rw [← hc₀] at hgi
  -- the physical flow
  have hηc : ContinuousOn (η ω) {t | (t : ℝ≥0∞) ≤ ζ ω} := by
    refine (hgω.2.1.add (continuousOn_const (c := (u : ℂ)))).congr fun t _ => ?_
    simp only [Pi.add_apply, sub_add_cancel]
  have hη0 : η ω 0 = u := sub_eq_zero.1 hgω.1
  have hζ0 : 0 < ζ ω := lt_of_le_of_lt zero_le hT
  -- reading the relative trace back
  obtain ⟨σ, hσ0, -, hV0, hiff, hrb, hζeq⟩ := readback hWc hW0 hΓ hgc hgi hηc hlink hT
  set tL := (firstVisit (η ω) (ζ ω) L).toNNReal with htL
  have htLζ : (tL : ℝ≥0∞) < ζ ω := by
    rw [htL, ENNReal.coe_toNNReal (hT.trans_le le_top).ne]; exact hT
  -- first direction
  have hgood : ∀ s : ℝ≥0, (s : ℝ≥0∞) < Vg → ∀ x : ℝ, g (Γ s + (m : ℂ)) = x →
      x ∉ closure (badSet κ ψ u b) := by
    intro s hs x hx hcl
    have e := (hrb s hs.le).2
    have hlt := (hiff s).1 hs
    refine hnotω hζ0 (tL + σ s) hlt ?_
    rw [← e, hx]
    have h1 := flowBad_of_mem_closure_badSet (ψ := ψ) hκ hb hcl
    convert h1 using 1
    push_cast
    ring
  have hle' := hle hF hcell g hgc hgi W Vg Γ hWc hW0 hΓ hgood
  refine le_antisymm hle' ?_
  -- second direction
  rcases eq_or_ne Vg ⊤ with htop | hfin
  · rw [htop]; exact le_top
  obtain ⟨T, rfl⟩ : ∃ T : ℝ≥0, Vg = T := ⟨Vg.toNNReal, (ENNReal.coe_toNNReal hfin).symm⟩
  have hT0 : 0 < T := ENNReal.coe_pos.1 hV0
  have hζT := hζeq T rfl
  have hζt : ζ ω ≠ ⊤ := by rw [hζT]; exact ENNReal.coe_ne_top
  have hbad := htipω hζ0 hζt
  rw [hζT, ENNReal.toNNReal_coe] at hbad
  obtain ⟨hTim, e⟩ := hrb T le_rfl
  set z := η ω (tL + σ T) with hz
  have hzim : z.im = 0 := by
    have h1 := hbad.1
    simpa using h1
  set p : ℝ := z.re with hp
  have hzp : z = (p : ℂ) := Complex.ext (by simp [hp]) (by simp [hzim])
  have hpu : p ≠ u := by
    intro hpu
    have h0 : η ω 0 - (u : ℂ) = z - (u : ℂ) := by rw [hη0, hzp, hpu, sub_self]
    refine hnotω hζ0 0 hζ0 ?_
    rw [h0]
    exact subset_closure hbad
  have hbad' : Vq.IsBadPoint (flowLineXL b jumps u) (flowLineXR b jumps u) (flowLineRhoL κ b jumps u ψ)
      (flowLineRhoR κ b jumps u ψ) (((p - u : ℝ) : ℂ)) := by
    have h1 : (((p - u : ℝ) : ℂ)) = z - (u : ℂ) := by rw [hzp]; push_cast; ring
    rw [h1]
    exact hbad
  have hpb : p ∈ badSet κ ψ u b := mem_badSet_of_flowBad hκ hb hpu hbad'
  -- the relative tip at `T` is real
  have hΓim : (Γ T).im = 0 := by
    by_contra hne
    have hpos : 0 < (Γ T).im := lt_of_le_of_ne hTim (Ne.symm hne)
    have hH : Γ T + (m : ℂ) ∈ H := by
      show 0 < (Γ T + (m : ℂ)).im
      simpa using hpos
    have h1 := hcc.2.1 hH
    rw [← hgi hH, e, hzp] at h1
    have h2 : (0 : ℝ) < ((p : ℂ)).im := h1
    simp at h2
  set y : ℝ := (Γ T).re with hy
  have hΓy : Γ T = (y : ℂ) := Complex.ext (by simp [hy]) (by simp [hΓim])
  have hgy : g ((y + m : ℝ) : ℂ) = p := by
    have h1 : ((y + m : ℝ) : ℂ) = Γ T + (m : ℂ) := by rw [hΓy]; push_cast; ring
    rw [h1, e, hzp]
  have hcw := heqω hF
  have hft : FCDet.IsFlowType κ ψ (I.word ω) (cellXL κ ψ I.word w ω) (cellXR κ ψ I.word w ω) (typedRhoL w)
      (typedRhoR w) :=
    FCDet.isFlowType_of_mem_typeSet (mem_typeSet_of_mem_wordTypeCell hcell)
  have hSC := (hβω hF).2
  rcases lt_trichotomy y 0 with hyneg | hy0 | hypos
  · exact thr_le_of_bad_left hWc hW0 hΓ hT0 le_rfl hΓim hyneg
      (rel_bad_left hκ hb hcc hgc hgi hSC hcw hft hyneg hgy hpb)
  · exfalso
    have e0 := (hrb 0 zero_le).2
    rw [hΓ.1, zero_add, hσ0, add_zero] at e0
    have h1 : η ω tL = z := by
      rw [← e0, ← e, hΓy, hy0, Complex.ofReal_zero, zero_add]
    refine hnotω hζ0 tL htLζ ?_
    rw [h1]
    exact subset_closure hbad
  · by_cases hlow : ∃ ε > 0, ∀ y'' ∈ Ioo (y + m) (y + m + ε), y'' ∉ (β ω).jumps →
        (β ω).fn y'' = -sleLambda κ - -(Real.pi / 2) * chiC κ
    · obtain ⟨hLp, hright⟩ := hJω hF g hgc hgi (y + m) (by linarith) hlow p hgy
      exfalso
      rcases hpb with ⟨hup, hbadR⟩ | ⟨hpu', -⟩
      · exact absurd hbadR (not_le.2 (hright hup))
      · exact not_mem_Ico_of_flow hη0 hηc hgω ⟨hpathω.2.2.2.1, hpathω.1⟩ hT hnotω hζ0 hζT hbad hzp hLp hpu'
    · exact thr_le_of_bad_right hWc hW0 hΓ hT0 le_rfl hΓim hypos
        (rel_bad_right hκ hb hcc hgc hgi hSC hcw hft hypos hgy hpb hlow)

end InteractingSLE.Theorem14.SB.Wf
