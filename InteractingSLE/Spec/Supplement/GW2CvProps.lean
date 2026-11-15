/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2CvCover

/-!
# GW2's root cover: what a cover event guarantees, and the cover itself

Packet PROVE-GW2-COVER. Lemma GW2's proof, "An initial positive interior prefix always exists"
(`source/spec/p577-624.md` L1001–L1010).

* **`ae_coverEvent_spec`**: almost surely on the cover event of a root `r`, the counterflow tip
  `α(s)` is interior, the root piece has a generating trace `γ` with an interior physical tip
  `v + γ(q₀)` at its root time `q₀`, `q₀` precedes both its lifetime and the first contact of the
  physical trace `−1/(v + γ)` with `α([0, s])`, and `v ‖α‖ < 1` on `[0, s]` (the arc `[0, v]` is
  untouched by the counterflow). For the zero root this contains the protected event of
  `RootE26`/`RootD25` (`ae_coverEvent_spec_zero`).
* `exists_small_root`: there are admissible roots with arbitrarily small root points (GW1's ambient
  bounds, `exists_root_angle`, the first low right arc).
* **`ae_exists_mem_coverEvent`**: almost surely on `{α(s) ∈ ℍ}` some cover event occurs.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H chiC)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootCv

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric RootC24 Supp8.GB6
open PiecewiseConstantBoundaryData (leftLim rightLim)

variable {Ω : Type u} [MeasurableSpace Ω]

/-! ### Reading the two records -/

/-- On the regular counterflow sample, the counterflow record reads the actual trace up to `s`. -/
theorem physicalTipRead_cfRec {c : SourceData Ω} {ω : Ω} (hW : Continuous fun t => c.W t ω)
    (hW0 : c.W 0 ω = 0) (hζ : c.ζ ω = ⊤) (hα : IsGeneratingTrace (c.W · ω) ⊤ (c.α ω)) {u : ℝ≥0}
    (hu : u ≤ c.s) : RootA22.physicalTipRead (cfRec c.s c.W c.ζ ω, u) = c.α ω u := by
  have hcfE := GW2JointKernel.cfE_eq c.s hζ hW0 hW
  have hαg : IsGeneratingTrace (GW2JointKernel.cfE c.s c.W c.ζ ω).1
      (GW2JointKernel.cfE c.s c.W c.ζ ω).2 (c.α ω) := by
    rw [hcfE]; exact hα
  have hv : (c.s : ℝ≥0∞) < (GW2JointKernel.cfE c.s c.W c.ζ ω).2 := by
    rw [hcfE]; exact ENNReal.coe_lt_top
  exact RootA22.physicalTipRead_recOf_eq (e := GW2JointKernel.cfE c.s c.W c.ζ ω)
    (StagedReg.isRegularDriver_regularize _ _) hαg hv hu

/-- Before its cutoff, the root record reads the actual trace of the root piece. -/
theorem physicalTipRead_rootRec (c : SourceData Ω) (x : RootIdx c.Θ c.Q) {ω : Ω} {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf x []) 0 ω).1
      (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf x []) 0 ω).2 γ)
    (hq : ((rootEntry x).2 : ℝ≥0∞) < (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf x []) 0 ω).2)
    {t : ℝ≥0} (ht : t ≤ (rootEntry x).2) :
    RootA22.physicalTipRead (stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf x []) 0 ω, t) = γ t := by
  rw [stopRec_root_eq]
  exact RootA22.physicalTipRead_recOf_eq (isRegularDriver_canonFam c.hκ c.h12p c.βA c.c₀ _ _ _ c.h 0 ω)
    hγ hq ht

/-! ### The guarantees of a cover event -/

variable [StandardBorelSpace Ω]

/-- **What a cover event guarantees** (almost surely): an admissible root, an interior counterflow
tip, a generating root trace with an interior physical tip `v + γ(q₀)`, the root time strictly before
the lifetime and the first inversion contact of the physical root trace `v + γ` with `α([0, s])`,
and `v ‖α‖ < 1` on `[0, s]`. -/
theorem ae_coverEvent_spec (h13 : Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) :
    let E := canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 []) 0
    let γ := GW2aSingle.chosenTrace (fun t ω => (E ω).1 t) (fun ω => (E ω).2)
    ∀ᵐ ω ∂c.P, ω ∈ coverEvent c r →
      RootSeedOK c r.1 ∧ c.α ω c.s ∈ H ∧ IsGeneratingTrace (E ω).1 (E ω).2 (γ ω) ∧
      (rootPt r.1 : ℂ) + γ ω (rootEntry r.1).2 ∈ H ∧
      ((rootEntry r.1).2 : ℝ≥0∞) < min
        (firstContactTime (fun t => sphereInv (((rootPt r.1 : ℂ) + γ ω t : ℂ) : OnePoint ℂ))
          ((fun u => (c.α ω u : OnePoint ℂ)) '' Icc 0 c.s)) (E ω).2 ∧
      ∀ u ∈ Icc 0 c.s, rootPt r.1 * ‖c.α ω u‖ < 1 := by
  intro E γ
  have hgen := GW2aSingle.ae_chosenTrace h13 c.hκ (isFlowLineDriver_root h13 c r.1)
  filter_upwards [hgen, c.hα, GW2Later.ae_counterflow_regular h13 c.hκ c.hcf c.hζ, c.hζ]
    with ω hgω hαω hreg hζω
  rintro ⟨hok, hflag, hsH, htip, n, hsep⟩
  obtain ⟨_, _, hW, hW0, _⟩ := hreg
  set q₀ : ℝ≥0 := (rootEntry r.1).2 with hq₀
  have hq : (q₀ : ℝ≥0∞) < (E ω).2 := by
    have hf : (stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 []) 0 ω).2.2 = false := hflag
    rw [stopRec_root_eq] at hf
    exact (recOf_flag_eq_false_iff _ _).1 hf
  have hγg : IsGeneratingTrace (E ω).1 (E ω).2 (γ ω) := hgω.1
  have hαc : Continuous (c.α ω) := continuousOn_univ.1 (hαω.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hγf : Continuous fun t => γ ω (min t q₀) :=
    hγg.2.1.comp_continuous (continuous_id.min continuous_const)
      fun t => (ENNReal.coe_le_coe.2 (min_le_right t q₀)).trans hq.le
  have hαf : Continuous fun u => c.α ω (min u c.s) := hαc.comp (continuous_id.min continuous_const)
  have hrat : ∀ t u : ℚ, 1 / ((n : ℝ) + 1) ≤
      ‖((rootPt r.1 : ℂ) + γ ω (min (t : ℝ).toNNReal q₀)) * c.α ω (min (u : ℝ).toNNReal c.s) + 1‖ ∧
      rootPt r.1 * ‖c.α ω (min (u : ℝ).toNNReal c.s)‖ ≤ 1 - 1 / ((n : ℝ) + 1) := by
    intro t u
    have h := hsep t u
    simp only [tipAt, rootRecs] at h
    rwa [physicalTipRead_rootRec c r.1 hγg hq (min_le_right _ _),
      physicalTipRead_cfRec hW hW0 hζω hαω (min_le_right _ _)] at h
  have hall := sep_of_rat hγf hαf hrat
  have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hsep' : ∀ t ≤ q₀, ∀ u ∈ Icc 0 c.s,
      1 / ((n : ℝ) + 1) ≤ ‖((rootPt r.1 : ℂ) + γ ω t) * c.α ω u + 1‖ := by
    intro t ht u hu
    have h := (hall t u).1
    rwa [min_eq_left ht, min_eq_left hu.2] at h
  have hγat : ContinuousAt (γ ω) q₀ :=
    hγg.2.1.continuousAt (Filter.mem_of_superset
      ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds hq)
        fun t (ht : (t : ℝ≥0∞) < (E ω).2) => show (t : ℝ≥0∞) ≤ (E ω).2 from ht.le)
  refine ⟨hok, ?_, hγg, ?_, lt_min (lt_firstContactTime_of_sep hγat hαc.continuousOn hδ hsep') hq,
    fun u hu => ?_⟩
  · have hsH' : RootA22.physicalTipRead (cfRec c.s c.W c.ζ ω, c.s) ∈ H := hsH
    rwa [physicalTipRead_cfRec hW hW0 hζω hαω le_rfl] at hsH'
  · have htip' : (rootPt r.1 : ℂ) + RootA22.physicalTipRead
        (stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 []) 0 ω, q₀) ∈ H := htip
    rwa [physicalTipRead_rootRec c r.1 hγg hq le_rfl] at htip'
  · have h := (hall 0 u).2
    rw [min_eq_left hu.2] at h
    linarith

/-- **The zero-root form** of `ae_coverEvent_spec`: the interior root tip and literally the protected
event used by `RootE26.ae_initial_exists_protected_cutoff` and `RootD25.ae_initial_physical_regular`. -/
theorem ae_coverEvent_spec_zero (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (hroot : rootPt r.1 = 0) :
    let E := canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec 0 [rootEntry r.1]) 0
    let γ := GW2aSingle.chosenTrace (fun t ω => (E ω).1 t) (fun ω => (E ω).2)
    ∀ᵐ ω ∂c.P, ω ∈ coverEvent c r →
      c.α ω c.s ∈ H ∧ γ ω (rootEntry r.1).2 ∈ H ∧ ((rootEntry r.1).2 : ℝ≥0∞) < min
        (firstContactTime (fun t => sphereInv (γ ω t : OnePoint ℂ))
          ((fun u => (c.α ω u : OnePoint ℂ)) '' Icc 0 c.s)) (E ω).2 := by
  have hspec : schedSpecOf r.1 [] = schedSpec 0 [rootEntry r.1] := by
    simp only [schedSpecOf, entryList, List.map_nil, schedOf_nil, hroot]
  have h := ae_coverEvent_spec h13 c r
  simp only [hspec, hroot, Complex.ofReal_zero, zero_add] at h
  filter_upwards [h] with ω hω hmem
  obtain ⟨-, hsH, -, htip, hlt, -⟩ := hω hmem
  exact ⟨hsH, htip, hlt⟩

/-! ### The cover -/

omit [StandardBorelSpace Ω] in
/-- **Admissible roots with arbitrarily small root points** (Lemma GW2's proof): the root `0` with an
admissible angle when the lower extreme is initially admissible, and otherwise rational points of
the first low right arc. -/
theorem exists_small_root (h13₀ : Theorem13Statement.{0}) (c : SourceData Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : RootIdx c.Θ c.Q, RootSeedOK c x ∧ 0 ≤ rootPt x ∧ rootPt x < ε := by
  obtain ⟨hLa, hRa⟩ := GW1Conn.ambient_bounds (BR3Ref.gw0ForwardStatement_of_theorem13 h13₀) c.hκ c.hκ4
    c.hb c.hh c.hcf c.hζ
  obtain ⟨hL0, hR0⟩ := GW1Conn.root_bounds c.hb hLa hRa
  obtain ⟨q₁, hq₁⟩ := c.hQd.nonempty
  rcases exists_root_angle c.hκ c.hκ4 c.hΘd hL0 hR0 with ⟨-, θ, hθ, -, hadm⟩ | ⟨hlow, θ, hθ, -, hadm⟩
  · refine ⟨(none, ⟨θ, hθ⟩, ⟨q₁, hq₁⟩), ⟨?_, Or.inl rfl⟩, le_rfl, hε⟩
    exact hadm
  · obtain ⟨a₀, ha₀, ha₀J⟩ := exists_pos_jumpFree c.jumps
    obtain ⟨v, hv0, hv⟩ := exists_rat_btwn (lt_min ha₀ hε)
    have hv0' : (0 : ℝ) < v := by exact_mod_cast hv0
    have hJ : ∀ y ∈ c.jumps, y ∉ Ioc 0 (v : ℝ) := fun y hy hyv =>
      ha₀J y hy ⟨hyv.1, hyv.2.trans_lt (hv.trans_le (min_le_left _ _))⟩
    obtain ⟨hl, hr⟩ := lims_eq_of_jumpFree c.hb hv0' hJ
    refine ⟨(some v, ⟨θ, hθ⟩, ⟨q₁, hq₁⟩), ⟨?_, Or.inr ⟨hv0', hJ, hlow⟩⟩, hv0'.le,
      hv.trans_le (min_le_right _ _)⟩
    change ExplState.IsAdmissibleSeed c.κ (leftLim c.b v) (rightLim c.b v) θ
    rw [hl, hr]
    exact hadm

/-- **GW2's root cover** (Lemma GW2's proof, "An initial positive interior prefix always exists"):
almost surely, whenever the counterflow tip `α(s)` is interior, some root's cover event occurs. -/
theorem ae_exists_mem_coverEvent (h13 : Theorem13Statement.{u}) (h13₀ : Theorem13Statement.{0})
    (c : SourceData Ω) :
    ∀ᵐ ω ∂c.P, c.α ω c.s ∈ H → ∃ r : ScaledRootIdx c.Θ c.Q, ω ∈ coverEvent c r := by
  have : Countable c.Θ := c.hΘc.to_subtype
  have : Countable c.Q := c.hQc.to_subtype
  let E : RootIdx c.Θ c.Q → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun x =>
    canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf x []) 0
  have hroots : ∀ᵐ ω ∂c.P, ∀ x : RootIdx c.Θ c.Q,
      IsGeneratingTrace (E x ω).1 (E x ω).2
        (GW2aSingle.chosenTrace (fun t ω => (E x ω).1 t) (fun ω => (E x ω).2) ω) ∧
      (RootSeedOK c x → 0 < (E x ω).2) := by
    rw [ae_all_iff]
    intro x
    have hgen := GW2aSingle.ae_chosenTrace h13 c.hκ (isFlowLineDriver_root h13 c x)
    by_cases hx : RootSeedOK c x
    · filter_upwards [hgen, ae_root_life_pos h13 c x hx] with ω h1 h2 using ⟨h1.1, fun _ => h2⟩
    · filter_upwards [hgen] with ω h1 using ⟨h1.1, fun h => absurd h hx⟩
  filter_upwards [hroots, c.hα, GW2Later.ae_counterflow_regular h13 c.hκ c.hcf c.hζ, c.hζ]
    with ω hr hαω hreg hζω
  intro hsH
  obtain ⟨_, _, hW, hW0, _⟩ := hreg
  have hαc : Continuous (c.α ω) := continuousOn_univ.1 (hαω.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  obtain ⟨M₀, hM₀⟩ := ((isCompact_Icc.image_of_continuousOn
    (hαc.continuousOn (s := Icc 0 c.s))).isBounded).subset_closedBall 0
  set M : ℝ := |M₀| with hM
  have hM0 : 0 ≤ M := abs_nonneg _
  have hαM : ∀ u ∈ Icc 0 c.s, ‖c.α ω u‖ ≤ M := fun u hu => by
    have := hM₀ ⟨u, hu, rfl⟩
    rw [mem_closedBall_zero_iff] at this
    exact this.trans (le_abs_self _)
  obtain ⟨x₁, hok, hx0, hxε⟩ := exists_small_root h13₀ c (show (0 : ℝ) < 1 / (4 * (M + 1)) by positivity)
  obtain ⟨hgen₁, hlife₁⟩ := hr x₁
  have hT₁ := hlife₁ hok
  set γ₁ := GW2aSingle.chosenTrace (fun t ω => (E x₁ ω).1 t) (fun ω => (E x₁ ω).2) ω
  have hγ0 : ContinuousAt γ₁ 0 :=
    hgen₁.2.1.continuousAt (Filter.mem_of_superset
      ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds
        (show ((0 : ℝ≥0) : ℝ≥0∞) < (E x₁ ω).2 by simpa only [ENNReal.coe_zero] using hT₁))
      fun t (ht : (t : ℝ≥0∞) < (E x₁ ω).2) => show (t : ℝ≥0∞) ≤ (E x₁ ω).2 from ht.le)
  have hxM : rootPt x₁ * (M + 1) ≤ 1 / 4 := by
    have := (lt_div_iff₀ (show (0 : ℝ) < 4 * (M + 1) by positivity)).1 hxε
    linarith
  obtain ⟨t₀, ht₀, hsmall⟩ := exists_small_sep hγ0 hgen₁.1 hM0 hαM hx0 hxM
  obtain ⟨b, hb0, hb⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp
    (lt_min (ENNReal.coe_pos.mpr ht₀) hT₁)
  have hreg₁ : IsRegularDriver (E x₁ ω) := isRegularDriver_canonFam c.hκ c.h12p c.βA c.c₀ _ _ _ c.h 0 ω
  obtain ⟨q, hqQ, -, hqb', hqH⟩ := exists_mem_tip_mem_H hgen₁ hreg₁.1 hreg₁.2.1 c.hQd
    (ENNReal.coe_pos.mp hb0) (hb.le.trans (min_le_right _ _))
  have hqb : (q : ℝ≥0∞) < min (t₀ : ℝ≥0∞) (E x₁ ω).2 := (ENNReal.coe_lt_coe.mpr hqb').trans hb
  have hqt : q ≤ t₀ := ENNReal.coe_le_coe.1 (hqb.le.trans (min_le_left _ _))
  have hqT : (q : ℝ≥0∞) < (E x₁ ω).2 := hqb.trans_le (min_le_right _ _)
  let x : RootIdx c.Θ c.Q := (x₁.1, x₁.2.1, ⟨q, hqQ⟩)
  have hEx : E x ω = E x₁ ω := canonSpecFam_root_congr c x x₁ rfl rfl ω
  have hγx : IsGeneratingTrace (E x ω).1 (E x ω).2 γ₁ := by rw [hEx]; exact hgen₁
  have hqx : ((rootEntry x).2 : ℝ≥0∞) < (E x ω).2 := by rw [hEx]; exact hqT
  refine ⟨(x, 0), hok, ?_, ?_, ?_, 1, ?_⟩
  · change (stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf x []) 0 ω).2.2 = false
    rw [stopRec_root_eq, recOf_flag_eq_false_iff]
    change (q : ℝ≥0∞) < (E x ω).2
    rw [hEx]
    exact hqT
  · change RootA22.physicalTipRead (cfRec c.s c.W c.ζ ω, c.s) ∈ H
    rwa [physicalTipRead_cfRec hW hW0 hζω hαω le_rfl]
  · change (rootPt x : ℂ) + RootA22.physicalTipRead
      (stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf x []) 0 ω, (rootEntry x).2) ∈ H
    rw [physicalTipRead_rootRec c x hγx hqx le_rfl]
    exact (ofReal_add_mem_H_iff _ _).2 hqH
  · intro t u
    simp only [tipAt, rootRecs]
    rw [physicalTipRead_rootRec c x hγx hqx (min_le_right _ _),
      physicalTipRead_cfRec hW hW0 hζω hαω (min_le_right _ _)]
    have hs := hsmall (min (t : ℝ).toNNReal q) ((min_le_right _ _).trans hqt)
      (min (u : ℝ).toNNReal c.s) ⟨zero_le, min_le_right _ _⟩
    have hx : rootPt x = rootPt x₁ := rfl
    rw [hx]
    norm_num
    exact ⟨hs.1, by linarith [hs.2]⟩

end InteractingSLE.Theorem14.GW2TipSystem.RootCv
