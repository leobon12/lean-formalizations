/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LwWitness
import InteractingSLE.Spec.Supplement.SB2KRight
import InteractingSLE.Spec.Supplement.StagedRegularize
import InteractingSLE.Spec.Supplement.BR3Ref
import InteractingSLE.Spec.Supplement.GW1ConnectorFirst

/-!
# SB2(2)'s word half PROVED (ruling R99)

Packet PROVE-T14-SB2LOW. `Lz.SB2LowerWordAdmStatement` (PROVE-T14-SB2FIN5, `SB2KRight`) asks, at almost every launch
of the upper schedule program and for every launch witness `(b', jumps', h')`, with `m = −e_R`:
(a) the relative data are admissible for the lower flow (angle `−π/2`) left of the upper tip, and
(b) SB2(2)'s active word `Lu.IsActiveHighWord` on `(m, 0)` (= `(0, e_R)` in the launch chart): every height there is
a side height `±λ − ψχ` of a schedule angle, a low height, or an original bridge height.

Proof (supplement p. 632, "For the second assertion reflect this construction"): the word of the launch witness is
the explicit staged word (`exists_witness_upper`, invariant `UInv`); its data are pinned by GFF uniqueness
(`ae_eq_fn_of_witness`); in the launch chart the right entry `e_R` is at most the image of every untouched real point
`x ≥ 0` (`upper_bdry_facts`: the boundary values right of `R` increase and agree with the chart's real profile; every
real point of the upper prefix is at most `max (recR, 0)`, `realMax_upperPrefix_le`), so a point of `(0, e_R)` is a
middle point (side height) or the image of an untouched bridge point `x ∈ (u, 0)` (`word_of_uInv`). The families are
first regularized at every sample (`StagedReg.regFam_spec`). The only input beyond the statement's binders is GW1's
ambient bound `b − (π/2)χ < λ` on `(−∞, 0)`, which the complete counterflow gives through Theorem 1.3 at universe `0`
(`GW1Conn.ambient_bounds`, `BR3Ref.gw0ForwardStatement_of_theorem13`; Theorem 1.4 may use Theorem 1.3, R48).

* **`sb2LowerWordAdmStatement_of_gw0`**, **`sb2LowerWordAdmStatement_of_theorem13`**: the word half;
* **`sb2LowerWordStatement_of_theorem13`**: with FIN5's `e_R ≥ 0`, SB2(2)'s whole word half `Lz.SB2LowerWordStatement`;
* **`sb2LowerLaunchEntryAdmStatement_of_law`**: R99's target from Theorem 1.3 and the law half only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (IsForwardSol chiC fwdMap H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lh

open Exist Exist.StagedLaw Exist.Staged Restart GW1W

/-! ### Avoiding finitely many points on one side -/

theorem exists_lt_near {z : ℝ} {P : ℝ → Prop} (hP : ∀ᶠ z' in 𝓝[<] z, P z') (F : Finset ℝ) :
    ∃ z', z' < z ∧ z' ∉ F ∧ P z' := by
  obtain ⟨z', ⟨h1, h2⟩, h3⟩ := ((hP.and self_mem_nhdsWithin).and
    ((eventually_notMem_of_finite F.finite_toSet z).filter_mono (nhdsWithin_mono _ fun w hw => ne_of_lt hw))).exists
  exact ⟨z', h2, h3, h1⟩

theorem exists_gt_near {z : ℝ} {P : ℝ → Prop} (hP : ∀ᶠ z' in 𝓝[>] z, P z') (F : Finset ℝ) :
    ∃ z', z < z' ∧ z' ∉ F ∧ P z' := by
  obtain ⟨z', ⟨h1, h2⟩, h3⟩ := ((hP.and self_mem_nhdsWithin).and
    ((eventually_notMem_of_finite F.finite_toSet z).filter_mono
      (nhdsWithin_mono _ fun w hw => ne_of_gt hw))).exists
  exact ⟨z', h2, h3, h1⟩

/-! ### The right entry value in the launch chart -/

/-- **The boundary values right of `R`** in a run chart with regular pieces (hull model and boundary map): they agree
with the chart's real profile right of the record, they increase, and they tend to the right entry value at `R⁺`. -/
theorem upper_bdry_facts {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₀ : ℝ} (spec : ExplSpec)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ)
    (hnot : stStatus (ExplState.run κ b jumps spec D n) ≠ GW1Conn.stDone)
    (hS : UState x₀ (ExplState.run κ b jumps spec D n)) {A : Set ℂ} (hAc : IsCompact A)
    (hAf : fillH A = fillH (SB.prefixPhysSet κ b jumps spec D n)) {R : ℝ}
    (hRA : ∀ y : ℝ, (y : ℂ) ∈ A → y ≤ R) :
    (∀ x, R < x → stRecR (ExplState.run κ b jumps spec D n) < x →
        Lx.bdryValue (stChart (ExplState.run κ b jumps spec D n)) x =
          rProf (stChart (ExplState.run κ b jumps spec D n)) x) ∧
      (∀ x, R < x → Lx.rightEntry (stChart (ExplState.run κ b jumps spec D n)) R ≤
          Lx.bdryValue (stChart (ExplState.run κ b jumps spec D n)) x) ∧
      Tendsto (Lx.bdryValue (stChart (ExplState.run κ b jumps spec D n))) (𝓝[>] R)
        (𝓝 (Lx.rightEntry (stChart (ExplState.run κ b jumps spec D n)) R)) := by
  set c := stChart (ExplState.run κ b jumps spec D n) with hcdef
  set a := stRecR (ExplState.run κ b jumps spec D n) with hadef
  obtain ⟨M, hK⟩ := Lw.exists_hullModel_fill spec D hreg n hnot
  have hcc : c.IsConformal := (GW2aCont.isConformal_runChart (κ := κ) (b := b) (jumps := jumps) spec D n
    fun j _ c θ h => hreg j c θ h).1
  obtain ⟨g, hgc, hgi, -, -⟩ := Lw.exists_bdryMap_of_hasProperBdryExt hcc
    (GW1P.isClosed_pieces_run (κ := κ) (b := b) (jumps := jumps) spec D hreg n).1
  have hfree : ∀ x : ℝ, R < x → ∃ ρ > 0, Disjoint (Metric.ball (x : ℂ) ρ) M.hull := fun x hx => by
    obtain ⟨ρ, hρ, hd⟩ := Lx.exists_ball_disjoint_fillH_right hAc fun y hy => lt_of_le_of_lt (hRA y hy) hx
    rw [hAf, ← hK] at hd
    exact ⟨ρ, hρ, hd⟩
  obtain ⟨he, hcont, hinv⟩ := Lx.bdryValue_facts_right hcc M hgc hgi hfree
  obtain ⟨-, hc, hm, -, hcontc, -⟩ := hS
  have heq : ∀ x, R < x → a < x → Lx.bdryValue c x = rProf c x := by
    intro x hR hr
    have := GW1P.neBot_nhdsWithin_H (Lw.ofReal_mem_Hbar x)
    have h1 := (hcontc x hr).mono_right nhdsWithin_le_nhds
    rw [hc.eq_ofReal x] at h1
    exact_mod_cast tendsto_nhds_unique (he x hR) h1
  have hinj : InjOn (Lx.bdryValue c) (Ioi R) := fun x hx y hy hxy => by
    have h1 := hinv x hx
    rw [hxy, hinv y hy] at h1
    exact_mod_cast h1.symm
  have hsm : StrictMonoOn (Lx.bdryValue c) (Ioi R) := by
    intro x₁ hx₁ x₂ hx₂ h12
    set z : ℝ := max x₂ (a + 1) + 1 with hz
    have hx₂z : x₂ < z := by have := le_max_left x₂ (a + 1); linarith
    have hsub : Icc x₁ z ⊆ Ioi R := fun w hw => lt_of_lt_of_le hx₁ hw.1
    rcases ContinuousOn.strictMonoOn_of_injOn_Icc' (h12.trans hx₂z).le (hcont.mono hsub) (hinj.mono hsub) with
      hmono | hanti
    · exact hmono ⟨le_rfl, (h12.trans hx₂z).le⟩ ⟨h12.le, hx₂z.le⟩ h12
    · exfalso
      have hza : a + 1 ≤ max x₂ (a + 1) := le_max_right _ _
      have hzx : x₂ ≤ max x₂ (a + 1) := le_max_left _ _
      have hRx₂ : R < x₂ := hx₂
      have hpz : z - 1 / 2 < z := by linarith
      have hp1 : x₁ ≤ z - 1 / 2 := by linarith
      have h1 := hanti ⟨hp1, hpz.le⟩ ⟨(h12.trans hx₂z).le, le_rfl⟩ hpz
      rw [heq _ (by linarith) (by linarith), heq _ (by linarith) (by linarith)] at h1
      have h2 := hm.1 (show a < z - 1 / 2 by linarith) (show a < z by linarith) hpz
      linarith
  obtain ⟨f, hf, hlim⟩ := Lx.isRightEntryValue_runChart spec D hreg n hnot hAc hAf hRA
  have hlim' : Tendsto (Lx.bdryValue c) (𝓝[>] R) (𝓝 (Lx.rightEntry c R)) := by
    refine hlim.congr' (eventually_nhdsWithin_of_forall fun x hx => ?_)
    have h1 := Lx.tendsto_bdryValue (hf x hx) (by simp)
    rw [h1.1, Complex.ofReal_re]
  refine ⟨heq, fun x hx => ?_, hlim'⟩
  refine le_of_tendsto hlim' ?_
  filter_upwards [Ioo_mem_nhdsGT hx] with z hz
  exact (hsm hz.1 hx hz.2).le

/-! ### The word conclusion in the launch chart (deterministic) -/

/-- **SB2(2)'s word in the launch chart**: from the upper invariant and the position of the right entry value `e`,
the word is admissible for the lower flow left of the tip, and every height on `(0, e)` is a side height or an
original bridge height. -/
theorem word_of_uInv {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₀ : ℝ} {l : List (ℝ × ℝ≥0)} {β : BoundaryWord}
    {s : ExplState} (hI : UInv κ b jumps x₀ l β s) {R e : ℝ} (hRle : R ≤ max (stRecR s) 0)
    (heq : ∀ x, R < x → stRecR s < x → Lx.bdryValue (stChart s) x = rProf (stChart s) x)
    (hmono : ∀ x, R < x → e ≤ Lx.bdryValue (stChart s) x)
    (hlim : Tendsto (Lx.bdryValue (stChart s)) (𝓝[>] R) (𝓝 e)) :
    (∀ y, y ≤ 0 → y ∉ β.jumps → β.fn y + -(Real.pi / 2) * chiC κ < sleLambda κ) ∧
      ∀ y ∈ Ioo 0 e, y ∉ β.jumps → SideH κ l (β.fn y) ∨ β.fn y ∈ Lu.bridgeHeights b jumps x₀ := by
  obtain ⟨hS, hO, hM, hL⟩ := hI
  obtain ⟨-, -, hm, -, -, hx₀, -, -⟩ := hS
  set m := rProf (stChart s) with hmdef
  set a := stRecR s with hadef
  have hstar : ∀ x, a < x → 0 ≤ x → e ≤ m x := by
    intro x hxa hx0
    rcases lt_or_ge R x with hRx | hxR
    · rw [← heq x hRx hxa]
      exact hmono x hRx
    · have hxR' : R = x := le_antisymm (hRle.trans (max_le hxa.le hx0)) hxR
      rw [← hxR'] at hxa ⊢
      have h1 : Tendsto m (𝓝[>] R) (𝓝 (m R)) :=
        (hm.2.1.continuousAt (Ioi_mem_nhds hxa)).tendsto.mono_left nhdsWithin_le_nhds
      have h2 : Tendsto m (𝓝[>] R) (𝓝 e) :=
        hlim.congr' (eventually_nhdsWithin_of_forall fun z hz => heq z hz (hxa.trans hz))
      exact (tendsto_nhds_unique h2 h1).le
  refine ⟨fun y hy hyJ => ?_, fun y hy hyJ => ?_⟩
  · rcases hy.lt_or_eq with hy | rfl
    · exact hL y hy hyJ
    · obtain ⟨z, hz, hzJ, hfz⟩ := exists_lt_near
        ((β.isPiecewiseConstantBoundaryData 0 hyJ).filter_mono nhdsWithin_le_nhds) β.jumps
      rw [← hfz]
      exact hL z hz hzJ
  · by_cases hmid : ∀ x, a < x → y < m x
    · exact Or.inl (hM y hy.1 hyJ hmid)
    · push Not at hmid
      obtain ⟨x, hxa, hxy⟩ := hmid
      set F : Finset ℝ := β.jumps ∪ (jumps.filter fun z => a < z).image m with hF
      have hev : ∀ᶠ y' in 𝓝[>] y, β.fn y' = β.fn y ∧ y' < e :=
        ((β.isPiecewiseConstantBoundaryData y hyJ).filter_mono nhdsWithin_le_nhds).and
          (Filter.eventually_of_mem (Ioo_mem_nhdsGT hy.2) fun z hz => hz.2)
      obtain ⟨y', hyy', hy'F, hfy, hy'e⟩ := exists_gt_near hev F
      obtain ⟨x', hx'a, hmx'⟩ := (exists_eq_iff_exists_lt hm).2 ⟨x, hxa, lt_of_le_of_lt hxy hyy'⟩
      have hx'J : x' ∉ jumps := fun hJ => hy'F (by
        rw [hF, Finset.mem_union]
        exact Or.inr (Finset.mem_image.2 ⟨x', Finset.mem_filter.2 ⟨hJ, hx'a⟩, hmx'⟩))
      have hy'J : y' ∉ β.jumps := fun hJ => hy'F (by rw [hF, Finset.mem_union]; exact Or.inl hJ)
      have hval : β.fn y' = b x' := by
        rw [← hmx']
        exact hO x' hx'a hx'J (show m x' ∉ β.jumps by rw [hmx']; exact hy'J)
      have hx'0 : x' < 0 := by
        by_contra h0
        push Not at h0
        have := hstar x' hx'a h0
        rw [hmx'] at this
        linarith
      exact Or.inr ⟨x', ⟨⟨lt_of_le_of_lt hx₀ hx'a, hx'0⟩, hx'J⟩, hval.symm.trans hfy⟩

/-! ### The largest real point of the upper prefix -/

/-- **The largest real point of the upper prefix** is at least `0` (the bridge) and at most `max (recR, 0)`: every
real point of a launched piece is at most the right record (`UState`). -/
theorem realMax_upperPrefix_le {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {x₀ : ℝ} {l : List (ℝ × ℝ≥0)} {k : ℕ} {ω : Ω} (hx₀ : x₀ ≤ 0)
    (hS : UState x₀ (ExplState.run κ b jumps (Lu.upperSpec x₀ l) (fun j => E (Lu.upperSpec x₀ l) j ω) k))
    (hAc : IsCompact (upperPrefix κ b jumps E x₀ l k ω)) :
    0 ≤ realMax (upperPrefix κ b jumps E x₀ l k ω) ∧
      realMax (upperPrefix κ b jumps E x₀ l k ω) ≤
        max (stRecR (ExplState.run κ b jumps (Lu.upperSpec x₀ l) (fun j => E (Lu.upperSpec x₀ l) j ω) k)) 0 := by
  obtain ⟨-, -, -, -, -, hu, harc, hphys⟩ := hS
  have h0 : ((0 : ℝ) : ℂ) ∈ upperPrefix κ b jumps E x₀ l k ω := Or.inr ⟨0, ⟨hx₀, le_rfl⟩, rfl⟩
  refine ⟨Lx.le_realMax_of_mem hAc h0, csSup_le ⟨0, h0⟩ fun y hy => ?_⟩
  rcases hy with hy | ⟨z, hz, hzy⟩
  · simp only [SB.prefixPhysSet, mem_union, mem_singleton_iff, mem_iUnion, exists_prop] at hy
    rcases hy with (h1 | ⟨p, hp, hz⟩) | ⟨a, ha, -⟩
    · have : y = x₀ := by exact_mod_cast h1
      rw [this]
      exact hu.trans (le_max_left _ _)
    · have := hphys p hp (y : ℂ) hz (by simp)
      simp only [Complex.ofReal_re] at this
      exact this.trans (le_max_left _ _)
    · change a ∈ (ExplState.run κ b jumps (Lu.upperSpec x₀ l) (fun j => E (Lu.upperSpec x₀ l) j ω) k).2.1 at ha
      rw [harc] at ha
      exact absurd ha (by simp)
  · have : z = y := by exact_mod_cast hzy
    rw [← this]
    exact hz.2.trans (le_max_right _ _)

end InteractingSLE.Theorem14.SB.Lh
