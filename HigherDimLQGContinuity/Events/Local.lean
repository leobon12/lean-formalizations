import HigherDimLQGContinuity.Events.Measurability
import HigherDimLQGMetric.Events.ShellCoverLocal
import HigherDimLFPP.Paths.DistOn

/-!
# Lemma `a:lem-local`: locality and measurability of the local events (packet P5b)

Packet P5b, target `local_events_aeEventIn`. Source: blueprint Part A, Lemma `a:lem-local` ([C] p. 6, l. 278–288;
§2.1, l. 188–191), **with the domain correction EB20** (Part B `b:err-domain`, ruling N13, packet P5b): the blueprint's
domain `ann 0 ½ (s + 1)` does not contain the inspection annulus `A = ann 0 ½ (7/2)` for the pin `s = 1`; its proof gives
the domain `V_s = ann 0 ½ max(7/2, s + 1)`, which contains `A ∪ ∂B_s`.

**Statement.** For `D`, `E` strong at positive parameters and a pin `s > 1/2` (the blueprint has `s ∈ [1, 10]`), each of
`H↓(D, E; b)`, `H↑(D, E; b)`, `PairRefs(D, E; 𝓡)` satisfies `AEEventIn 𝐏ₛ (fieldSigma0 id V_s)`.

**Proof.** (1) The three events are null-measurable for `𝐏ₛ` (module `Events.Measurability`: chain formula, rational
times, Lusin). (2) Each event depends only on the `A`-internal profiles of `ρ^D_g`, `ρ^E_g` (`IsWitness.of_internal_eq`,
`LocalRefs.of_internal_eq` of packet P5a; saturation lemmas below). (3) The locality lemma `p5b_aeEventIn_of_profile`
(module `Events.Profile`) with `V = A`, `J = V_s`.

Also: `p5b_aeEventIn_mono` (enlarging the domain), the variant `local_events_aeEventIn_of_subset` for every open domain
`J ⊇ A ∪ ∂B_s` (e.g. Part B's `ann 0 ½ 4` at the pin `s = 1`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ## Closure properties of `AEEventIn` -/

section Closure

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B B' : Set Ω}

theorem p5b_aeEventIn_compl (h : AEEventIn P m B) : AEEventIn P m Bᶜ := by
  obtain ⟨F, hF, hBF⟩ := h
  exact ⟨Fᶜ, hF.compl, hBF.compl⟩

theorem p5b_aeEventIn_union (h : AEEventIn P m B) (h' : AEEventIn P m B') : AEEventIn P m (B ∪ B') := by
  obtain ⟨F, hF, hBF⟩ := h
  obtain ⟨F', hF', hBF'⟩ := h'
  exact ⟨F ∪ F', hF.union hF', hBF.union hBF'⟩

theorem p5b_aeEventIn_inter (h : AEEventIn P m B) (h' : AEEventIn P m B') : AEEventIn P m (B ∩ B') := by
  obtain ⟨F, hF, hBF⟩ := h
  obtain ⟨F', hF', hBF'⟩ := h'
  exact ⟨F ∩ F', hF.inter hF', hBF.inter hBF'⟩

end Closure

/-- `AEEventIn` for the mean-zero pairings in `V` passes to every larger domain. -/
theorem p5b_aeEventIn_mono {P : Measure (DistRd d)} {V U : Set (Rd d)} (hVU : V ⊆ U)
    {B : Set (DistRd d)} (h : AEEventIn P (fieldSigma0 id V) B) : AEEventIn P (fieldSigma0 id U) B := by
  obtain ⟨F, hF, hBF⟩ := h
  exact ⟨F, shellCover_fieldSigma0_mono id hVU F hF, hBF⟩

/-! ## The events depend only on the `A`-internal profiles -/

section Saturation

variable {D E : DistRd d → ContMetric d} {g₁ g₂ : DistRd d}

theorem p5b_hdown_saturated
    (hDeq : ∀ u ∈ annA d, ∀ v ∈ annA d, (rho D g₁).internal (annA d) u v = (rho D g₂).internal (annA d) u v)
    (hEeq : ∀ u ∈ annA d, ∀ v ∈ annA d, (rho E g₁).internal (annA d) u v = (rho E g₂).internal (annA d) u v)
    {b : ℝ} (h : g₁ ∈ Hdown D E b) : g₂ ∈ Hdown D E b := by
  obtain ⟨γ, hγ, hle⟩ := h
  have h0 : γ 0 ∈ annA d := annK_subset_annA (hγ.mem_annK 0)
  have h1 : γ 1 ∈ annA d := annK_subset_annA (hγ.mem_annK 1)
  refine ⟨γ, hγ.of_internal_eq fun z hz w hw => (hEeq z hz w hw).symm, ?_⟩
  rw [← hDeq _ h0 _ h1, ← hEeq _ h0 _ h1]
  exact hle

theorem p5b_hup_saturated
    (hDeq : ∀ u ∈ annA d, ∀ v ∈ annA d, (rho D g₁).internal (annA d) u v = (rho D g₂).internal (annA d) u v)
    (hEeq : ∀ u ∈ annA d, ∀ v ∈ annA d, (rho E g₁).internal (annA d) u v = (rho E g₂).internal (annA d) u v)
    {b : ℝ} (h : g₁ ∈ Hup D E b) : g₂ ∈ Hup D E b := by
  obtain ⟨γ, hγ, hlt⟩ := h
  have h0 : γ 0 ∈ annA d := annK_subset_annA (hγ.mem_annK 0)
  have h1 : γ 1 ∈ annA d := annK_subset_annA (hγ.mem_annK 1)
  refine ⟨γ, hγ.of_internal_eq fun z hz w hw => (hDeq z hz w hw).symm, ?_⟩
  rw [← hDeq _ h0 _ h1, ← hEeq _ h0 _ h1]
  exact hlt

theorem p5b_pairRefs_saturated
    (hDeq : ∀ u ∈ annA d, ∀ v ∈ annA d, (rho D g₁).internal (annA d) u v = (rho D g₂).internal (annA d) u v)
    (hEeq : ∀ u ∈ annA d, ∀ v ∈ annA d, (rho E g₁).internal (annA d) u v = (rho E g₂).internal (annA d) u v)
    {H₀ σ₀ β₀ m M : ℝ} (h : g₁ ∈ PairRefs D E H₀ σ₀ β₀ m M) : g₂ ∈ PairRefs D E H₀ σ₀ β₀ m M :=
  ⟨h.1.of_internal_eq fun z hz w hw => (hDeq z hz w hw).symm,
    h.2.of_internal_eq fun z hz w hw => (hEeq z hz w hw).symm⟩

end Saturation

/-! ## Geometry of the domain -/

theorem p5b_annA_nonempty (hd : 1 ≤ d) : (annA d).Nonempty := by
  refine ⟨HigherDimLFPP.e₁ d, ?_⟩
  rw [mem_annA_iff, HigherDimLFPP.norm_e₁ (by omega)]
  norm_num

theorem p5b_annA_subset_localDomain (s : ℝ) :
    annA d ⊆ ann (0 : Rd d) (1 / 2) (max (7 / 2) (s + 1)) := by
  intro x hx
  rw [mem_annA_iff] at hx
  exact ⟨by simpa using hx.1, by simpa using lt_max_of_lt_left hx.2⟩

theorem p5b_sphere_subset_localDomain {s : ℝ} (hs : 1 / 2 < s) :
    sphere (0 : Rd d) s ⊆ ann (0 : Rd d) (1 / 2) (max (7 / 2) (s + 1)) := by
  intro x hx
  have hn : ‖x‖ = s := by simpa using hx
  refine ⟨by simpa [hn] using hs, ?_⟩
  have : ‖x - 0‖ < s + 1 := by rw [sub_zero, hn]; linarith
  exact lt_max_of_lt_right this

/-! ## Lemma `a:lem-local` -/

/-- **Lemma `a:lem-local`** for every open domain `J` containing `A` and the pin sphere `∂B_s`. -/
theorem local_events_aeEventIn_of_subset (hd : 2 ≤ d) {ξ η : ℝ} (hξ : 0 < ξ) (hη : 0 < η)
    {D E : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ (distExp d ξ) D) (hE : IsStrongExpMetric d η (distExp d η) E)
    {s : ℝ} (hs : 0 < s) {J : Set (Rd d)} (hJ : IsOpen J) (hAJ : annA d ⊆ J)
    (hSJ : sphere (0 : Rd d) s ⊆ J) (b H₀ σ₀ β₀ m M : ℝ) :
    AEEventIn (pinLaw d s) (fieldSigma0 id J) (Hdown D E b) ∧
      AEEventIn (pinLaw d s) (fieldSigma0 id J) (Hup D E b) ∧
      AEEventIn (pinLaw d s) (fieldSigma0 id J) (PairRefs D E H₀ σ₀ β₀ m M) := by
  have := isProbabilityMeasure_pinLaw hd s
  have hlD := p5b_ae_isLength_rho hd hD hs
  have hlE := p5b_ae_isLength_rho hd hE hs
  have hAne := p5b_annA_nonempty (d := d) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · exact p5b_aeEventIn_of_profile hd hξ hη hD hE hs isOpen_annA hAne hJ hAJ hSJ
      (p5b_nullMeasurableSet_hdown hD.measurable hE.measurable _ hlD hlE b)
      (fun _ _ _ _ _ _ hDeq hEeq => p5b_hdown_saturated hDeq hEeq)
  · exact p5b_aeEventIn_of_profile hd hξ hη hD hE hs isOpen_annA hAne hJ hAJ hSJ
      (p5b_nullMeasurableSet_hup hD.measurable hE.measurable _ hlD hlE b)
      (fun _ _ _ _ _ _ hDeq hEeq => p5b_hup_saturated hDeq hEeq)
  · exact p5b_aeEventIn_of_profile hd hξ hη hD hE hs isOpen_annA hAne hJ hAJ hSJ
      (p5b_nullMeasurableSet_pairRefs hD.measurable hE.measurable _ hlD hlE H₀ σ₀ β₀ m M)
      (fun _ _ _ _ _ _ hDeq hEeq => p5b_pairRefs_saturated hDeq hEeq)

/-- **Lemma `a:lem-local`** (blueprint Part A; [C] p. 6, l. 278–288), with the domain correction EB20: for `D`, `E`
strong at positive parameters and every pin `s > 1/2` (in particular `s ∈ [1, 10]`), the events `H↓(D, E; b)`,
`H↑(D, E; b)` and `PairRefs(D, E; 𝓡)` are, under `𝐏ₛ = pinLaw d s`, almost surely equal to events of the mean-zero
pairings supported in `ann 0 ½ max(7/2, s + 1)`. -/
theorem local_events_aeEventIn (hd : 2 ≤ d) {ξ η : ℝ} (hξ : 0 < ξ) (hη : 0 < η)
    {D E : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ (distExp d ξ) D) (hE : IsStrongExpMetric d η (distExp d η) E)
    {s : ℝ} (hs : 1 / 2 < s) (b H₀ σ₀ β₀ m M : ℝ) :
    AEEventIn (pinLaw d s) (fieldSigma0 id (ann (0 : Rd d) (1 / 2) (max (7 / 2) (s + 1))))
        (Hdown D E b) ∧
      AEEventIn (pinLaw d s) (fieldSigma0 id (ann (0 : Rd d) (1 / 2) (max (7 / 2) (s + 1))))
        (Hup D E b) ∧
      AEEventIn (pinLaw d s) (fieldSigma0 id (ann (0 : Rd d) (1 / 2) (max (7 / 2) (s + 1))))
        (PairRefs D E H₀ σ₀ β₀ m M) :=
  local_events_aeEventIn_of_subset hd hξ hη hD hE (by linarith) (isOpen_ann _ _ _)
    (p5b_annA_subset_localDomain s) (p5b_sphere_subset_localDomain hs) b H₀ σ₀ β₀ m M

/-- The good local events of Lemma 3.2 and Proposition 3.3 (`E_loc = (H↑(D, E; b) ∪ PairRefsᶜ)ᶜ`, and its
`H↓`-analogue) are `AEEventIn 𝐏ₛ (fieldSigma0 id V_s)`. -/
theorem local_good_aeEventIn (hd : 2 ≤ d) {ξ η : ℝ} (hξ : 0 < ξ) (hη : 0 < η)
    {D E : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ (distExp d ξ) D) (hE : IsStrongExpMetric d η (distExp d η) E)
    {s : ℝ} (hs : 1 / 2 < s) (b H₀ σ₀ β₀ m M : ℝ) :
    AEEventIn (pinLaw d s) (fieldSigma0 id (ann (0 : Rd d) (1 / 2) (max (7 / 2) (s + 1))))
        (Hup D E b ∪ (PairRefs D E H₀ σ₀ β₀ m M)ᶜ)ᶜ ∧
      AEEventIn (pinLaw d s) (fieldSigma0 id (ann (0 : Rd d) (1 / 2) (max (7 / 2) (s + 1))))
        (Hdown D E b ∩ PairRefs D E H₀ σ₀ β₀ m M) := by
  obtain ⟨hdn, hup, href⟩ := local_events_aeEventIn hd hξ hη hD hE hs b H₀ σ₀ β₀ m M
  exact ⟨p5b_aeEventIn_compl (p5b_aeEventIn_union hup (p5b_aeEventIn_compl href)),
    p5b_aeEventIn_inter hdn href⟩

end HigherDimLQGContinuity
