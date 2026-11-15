/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NtFrz
import InteractingSLE.Spec.Supplement.GW2RvInst
import InteractingSLE.Spec.Supplement.GW2SdoWord

/-!
# GW2's `noThreshold`: no threshold after the candidate's own cap (the root-`x` instance)

Packet PROVE-GW2-NOTHR (round 2, decision D38, the after-cap part). On ROOTX's corrected root-`x` instance
`GW2Rv.schedInstSX` (any good set, any announced root-`x` version with finite stop, any choice), almost surely on the
instance's record event: at every stage time `u` below the cap whose clock lies beyond the clock of `T + cap` (the
history time plus the candidate's cap, before the root-`x` contact), the stage driver has no continuation threshold,
for any force word. The explored driver is frozen after `T + cap` (`GW2Nt.schedW_frozen`), so its trace there is the
interior slit (`GW2Nt.schedTr_mem_of_frozen`), and an interior point gives no threshold
(`GW2Nt.not_threshold_of_interiorX`).

* **`ae_not_threshold_afterCapX`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2Nt

open Restart Exist.StagedLaw Supp8.GB6 GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rd GW2Rv
  GW2Sde GW2Sdh GW2Sdi MartChar.RealFlow Sec5.Prop513Schedule

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **No threshold after the candidate's own cap** on the corrected root-`x` instance. -/
theorem ae_not_threshold_afterCapX (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (a : ℕ) (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s) (hord : TimeOrdered 0 (historyProgram c r l)) {GT : Set Ω}
    (hGT : (∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω) ∧
      MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (hV : ∀ ω, V ω ≠ ⊤) (ch : SchedChoice Ω) :
    ∀ᵐ ω ∂c.P, (schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1) ω ∈ (schedInstSX c r l a GT hA ch).E →
      ∀ u : ℝ≥0, (u : ℝ≥0∞) < (schedInstSX c r l a GT hA ch).capX c (rootPt r.1) ω →
      ((historyTime c r l + candidateCap c r a : ℝ≥0) : ℝ≥0∞) <
        contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω →
      clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l + candidateCap c r a) ω <
        ((stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) ω : ℝ≥0) : ℝ) + u →
      ∀ {nL nR : ℕ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ}, (∀ i, xL i ≤ 0) → (∀ j, 0 ≤ xR j) →
        ¬ ForceWord.ThresholdCondition ρL ρR ((schedInstSX c r l a GT hA ch).drvX c (rootPt r.1) u ω)
          (fun i => -rightImg (fun v : ℝ => -(schedInstSX c r l a GT hA ch).drvX c (rootPt r.1) v.toNNReal ω)
            (-xL i) u)
          (fun j => rightImg (fun v : ℝ => (schedInstSX c r l a GT hA ch).drvX c (rootPt r.1) v.toNNReal ω)
            (xR j) u) := by
  set I := schedInstSX c r l a GT hA ch with hI
  set x := rootPt r.1 with hxdef
  set T := historyTime c r l with hT
  set A : ℝ≥0 := historyTime c r l + candidateCap c r a with hAdef
  have hv : IsRelVersionX x c.s c.P c.W c.ζ I.W I.γ c.α I.R I.V := hA.1.1
  have hρ := hA.1.2.choose_spec
  have hfin : ∀ᵐ ω ∂c.P, I.srecX c r l x ω ∈ I.E →
      stgStartMX x c.s c.W c.ζ I.W I.GT I.V I.T ω ≠ ⊤ :=
    Eventually.of_forall fun ω _ => ne_top_of_le_ne_top (hV ω) (min_le_right _ _)
  have hEgood := StageInst.E_good_of_recordX I hv hρ.2.1 hρ.2.2 inter_subset_right hfin
  filter_upwards [hEgood, hGT.2.2, hv.2.2.2.2.2.2] with ω hEg hGTω hvω hEω u hu hAc hAu nL nR xL ρL xR ρR hxL hxR
  obtain ⟨hgood, hSV⟩ := hEg hEω
  have hω : ω ∈ GT := hGTω.2 hgood
  obtain ⟨-, hcof, hhull⟩ := hvω hgood
  have hold : oldSuccess c r l ω := (augRec_mem_succRec_iff c r l _ ω).1 hEω.1.2
  obtain ⟨⟨hwc, hw0, hγ⟩, ⟨hα, hW, hW0, hζ⟩, harc, -, -⟩ := hGT.1 ω hω
  obtain ⟨h0, hmono, hcont⟩ := clock_props c.W c.ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ
  have hcl0 : clockX x c.s c.W c.ζ (schedW c r l a) 0 ω = 0 := h0
  have hTA : T ≤ A := le_self_add
  have hTc : (T : ℝ≥0∞) < contactX x c.s (schedTr c r l a) c.α ω := (ENNReal.coe_le_coe.2 hTA).trans_lt hAc
  -- the stage start is the clock at `T`
  have hTV : ENNReal.ofReal (clockX x c.s c.W c.ζ (schedW c r l a) T ω) < V ω := by
    have h1 : stgStartMX x c.s c.W c.ζ (schedW c r l a) GT V T ω < V ω := hSV
    unfold stgStartMX at h1
    rw [physClockX_eq_clockX hGT.1 hs hx hω hTc] at h1
    exact (min_lt_iff.1 h1).resolve_right (lt_irrefl _)
  set S := stgStartX x c.s c.W c.ζ (schedW c r l a) GT V T ω with hSdef
  have hS0 : stgStartX x c.s c.W c.ζ (schedW c r l a) GT V T ω =
      (clockX x c.s c.W c.ζ (schedW c r l a) T ω).toNNReal :=
    GW2Sdo.stgStartX_eq_clockX hGT.1 hs hx hω hTc hTV
  have hclT0 : 0 ≤ clockX x c.s c.W c.ζ (schedW c r l a) T ω := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ T) with h | h
    · rw [← h, hcl0]
    · have := hmono (show ((0 : ℝ≥0) : ℝ≥0∞) < contactX x c.s (schedTr c r l a) c.α ω from
        (ENNReal.coe_le_coe.2 zero_le).trans_lt hTc) hTc h
      change clockX x c.s c.W c.ζ (schedW c r l a) 0 ω < clockX x c.s c.W c.ζ (schedW c r l a) T ω at this
      linarith
  have hS : (S : ℝ) = clockX x c.s c.W c.ζ (schedW c r l a) T ω := by
    rw [hSdef, hS0, Real.coe_toNNReal _ hclT0]
  -- the cofinal time and the physical time of `S + u`
  have hSuV : ((S + u : ℝ≥0) : ℝ≥0∞) < V ω := by
    have hSV' : (S : ℝ≥0∞) < V ω := by
      rw [← ENNReal.ofReal_coe_nnreal, hS]
      exact hTV
    have h2 : (u : ℝ≥0∞) < V ω - S := hu
    rw [ENNReal.coe_add]
    exact lt_tsub_iff_left.mp h2
  obtain ⟨t', ht'c, ht'0⟩ := hcof (S + u) hSuV
  have ht' : (S : ℝ) + u < clockX x c.s c.W c.ζ (schedW c r l a) t' ω := by
    have h := ht'0
    rw [NNReal.coe_add] at h
    exact h
  have hAt' : clockX x c.s c.W c.ζ (schedW c r l a) A ω < clockX x c.s c.W c.ζ (schedW c r l a) t' ω :=
    lt_trans hAu ht'
  have hAt'le : A < t' := by
    by_contra hle
    have := hmono.monotoneOn ht'c hAc (not_lt.1 hle)
    exact absurd hAt' (not_lt.2 this)
  have hcontI : ∀ p q : ℝ≥0, (q : ℝ≥0∞) < contactX x c.s (schedTr c r l a) c.α ω →
      ContinuousOn (fun t => clockX x c.s c.W c.ζ (schedW c r l a) t ω) (Icc p q) := fun p q hq =>
    hcont.mono fun t ht => (ENNReal.coe_le_coe.2 ht.2).trans_lt hq
  obtain ⟨τ, ⟨hAτ, hτt'⟩, hτ0⟩ := intermediate_value_Ioo hAt'le.le (hcontI A t' ht'c)
    (show ((S : ℝ) + u) ∈ Ioo _ _ from ⟨hAu, ht'⟩)
  have hτ : clockX x c.s c.W c.ζ (schedW c r l a) τ ω = (S : ℝ) + u := hτ0
  have hτc : (τ : ℝ≥0∞) < contactX x c.s (schedTr c r l a) c.α ω :=
    (ENNReal.coe_lt_coe.2 hτt').trans ht'c
  -- a horizon after `τ` below the stop
  obtain ⟨b, hb1, hb2⟩ := exists_between (lt_min hSuV (show ((S + u : ℝ≥0) : ℝ≥0∞) <
    ENNReal.ofReal (clockX x c.s c.W c.ζ (schedW c r l a) t' ω) by
      rw [← ENNReal.ofReal_coe_nnreal]
      rw [NNReal.coe_add]
      exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (by positivity) ht')).2 ht'))
  have hbtop : b ≠ ⊤ := ne_top_of_lt (lt_of_lt_of_le hb2 (min_le_right _ _))
  have hb2' : b < ENNReal.ofReal (clockX x c.s c.W c.ζ (schedW c r l a) t' ω) := lt_of_lt_of_le hb2 (min_le_right _ _)
  have hbV : b < V ω := lt_of_lt_of_le hb2 (min_le_left _ _)
  have hby1 : ((S : ℝ) + u) < b.toReal := by
    have := (ENNReal.toReal_lt_toReal (ENNReal.coe_ne_top) hbtop).2 hb1
    rwa [ENNReal.coe_toReal, NNReal.coe_add] at this
  have hby2 : b.toReal < clockX x c.s c.W c.ζ (schedW c r l a) t' ω := by
    have h := ENNReal.toReal_lt_of_lt_ofReal hb2'
    exact h
  obtain ⟨v, ⟨hτv, hvt'⟩, hvb0⟩ := intermediate_value_Ioo hτt'.le (hcontI τ t' ht'c)
    (show b.toReal ∈ Ioo _ _ from ⟨by rw [hτ]; exact hby1, hby2⟩)
  have hvb : clockX x c.s c.W c.ζ (schedW c r l a) v ω = b.toReal := hvb0
  have hvc : (v : ℝ≥0∞) < contactX x c.s (schedTr c r l a) c.α ω := (ENNReal.coe_lt_coe.2 hvt').trans ht'c
  have hvV : ENNReal.ofReal (clockX x c.s c.W c.ζ (schedW c r l a) v ω) ≤ V ω := by
    rw [hvb, ENNReal.ofReal_toReal hbtop]
    exact hbV.le
  -- the explored point at `τ` is interior
  have hmemA := schedTr_mem_of_frozen c r l a hord hold hγ hAτ
  have hmem : schedTr c r l a ω τ ∈ H \ fwdHull (fun q : ℝ => schedW c r l a q.toNNReal ω) (T : ℝ) :=
    ⟨hmemA.1, fun hK => hmemA.2 ((QuantumZipper.fwdHull_mono).1 (NNReal.coe_le_coe.2 hTA) hK)⟩
  have hver : VersionAtX x c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V ω :=
    ⟨hv.2.1 ω, hv.2.2.1 ω, hhull⟩
  have hSu : ((S + u : ℝ≥0) : ℝ) = clockX x c.s c.W c.ζ (schedW c r l a) τ ω := by
    rw [hτ, NNReal.coe_add]
  exact not_threshold_of_interiorX hGT.1 hs hx hω hver (hTA.trans_lt hAτ) hτv hvc hvV hS hSu hmem hxL hxR

end InteractingSLE.Theorem14.GW2Nt
