import HigherDimLQGContinuity.SiteEvents.PinLocal

/-! The whole-site event and its locality in the unit annulus. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false
noncomputable section

namespace HigherDimLQGContinuity

open MeasureTheory Set Metric
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The site references, a successful seed at every edge, and the pin cap at every seed. -/
def siteEvent {ι : Type} (D E : DistRd d → ContMetric d)
    (F : Finset ι) (c : ι → Rd d) (L : ℝ) (Ntr : ℕ)
    (v H₀ σ₀ β₀ m M Hsd σsd Hup σ Hlo β mc A0 Kpin : ℝ) : Set (DistRd d) :=
  {g | SiteRefs Hup σ Hlo β mc A0 (rho D g) ∧
    (∀ e ∈ F, ∃ j ∈ Finset.range Ntr,
      recentre 1 (seedTrialRadius L j) (c e) g ∈
        seedTrialEvent D E v H₀ σ₀ β₀ m M Hsd σsd) ∧
    (∀ e ∈ F, ∀ j ∈ Finset.range Ntr,
      |sphereAvg g (seedTrialRadius L j) (c e)| ≤ Kpin)}

private theorem q10_aeEventIn_finset_all {Ω ι : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {μ : Measure Ω} (F : Finset ι) (B : ι → Set Ω)
    (hB : ∀ i ∈ F, AEEventIn μ m (B i)) :
    AEEventIn μ m {ω | ∀ i ∈ F, ω ∈ B i} := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      simpa using (show AEEventIn μ m (Set.univ : Set Ω) from
        ⟨Set.univ, MeasurableSet.univ, Filter.EventuallyEq.rfl⟩)
  | @insert i F hi ih =>
      have hset : {ω : Ω | ∀ k ∈ insert i F, ω ∈ B k} =
          B i ∩ {ω | ∀ k ∈ F, ω ∈ B k} := by
        ext ω
        simp only [mem_ofPred_eq, Finset.mem_insert, mem_inter_iff]
        constructor
        · intro h
          exact ⟨h i (Or.inl rfl), fun k hk => h k (Or.inr hk)⟩
        · rintro ⟨h₁, h₂⟩ k hk
          rcases hk with rfl | hk
          · exact h₁
          · exact h₂ k hk
      rw [hset]
      exact p5b_aeEventIn_inter (hB i (Finset.mem_insert_self _ _))
        (ih (fun k hk => hB k (Finset.mem_insert_of_mem hk)))

private theorem q10_aeEventIn_finset_exists {Ω ι : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {μ : Measure Ω} (F : Finset ι) (B : ι → Set Ω)
    (hB : ∀ i ∈ F, AEEventIn μ m (B i)) :
    AEEventIn μ m {ω | ∃ i ∈ F, ω ∈ B i} := by
  classical
  have h := q10_aeEventIn_finset_all F (fun i => (B i)ᶜ)
    (fun i hi => p5b_aeEventIn_compl (hB i hi))
  have heq : {ω : Ω | ∃ i ∈ F, ω ∈ B i} =
      {ω | ∀ i ∈ F, ω ∈ (B i)ᶜ}ᶜ := by
    ext ω
    simp
  rw [heq]
  exact p5b_aeEventIn_compl h

private theorem q10_siteC_subset_ann4 :
    siteC d ⊆ ann (0 : Rd d) (1 / 2) 4 := by
  intro x hx
  change (3 / 2 : ℝ) ≤ ‖x - 0‖ ∧ ‖x - 0‖ ≤ 5 / 2 at hx
  change (1 / 2 : ℝ) < ‖x - 0‖ ∧ ‖x - 0‖ < 4
  constructor <;> linarith [hx.1, hx.2]

private theorem q10_seed_sphere_subset_siteC {ι : Type}
    (F : Finset ι) (c : ι → Rd d) {L : ℝ} (hL : 0 < L)
    (hbox : ∀ e ∈ F, closedBall (c e) L ⊆ siteC d)
    {e : ι} (he : e ∈ F) (j : ℕ) :
    sphere (c e) (seedTrialRadius L j) ⊆ siteC d := by
  intro x hx
  apply hbox e he
  rw [mem_closedBall]
  have hr : seedTrialRadius L j ≤ L / 32 := seedTrialRadius_le hL.le j
  rw [mem_sphere] at hx
  linarith

private theorem q10_seed_affine_subset_ann4 {ι : Type}
    (F : Finset ι) (c : ι → Rd d) {L : ℝ} (hL : 0 < L)
    (hbox : ∀ e ∈ F, closedBall (c e) L ⊆ siteC d)
    {e : ι} (he : e ∈ F) (j : ℕ) :
    affinePt (seedTrialRadius L j) (c e) ''
      ann (0 : Rd d) (1 / 2) 4 ⊆ ann (0 : Rd d) (1 / 2) 4 := by
  have hr := seedTrialRadius_pos hL j
  have hgeom := S6a.image_ann_affine_eq hr (c e) (1 / 2) 4
  change ((fun x : Rd d => seedTrialRadius L j • x + c e) ''
      ann (0 : Rd d) (1 / 2) 4) ⊆ _
  rw [hgeom]
  intro x hx
  apply q10_siteC_subset_ann4
  apply hbox e he
  rw [mem_closedBall]
  have hrle := seedTrialRadius_le hL.le j
  have hx' : dist x (c e) < 4 * seedTrialRadius L j := by
    simpa only [dist_eq_norm, mul_comm] using hx.2
  linarith

/-- The whole-site event is observable in the unit annulus. -/
theorem siteEvent_aeEventIn (hd : 2 ≤ d) {ξ η : ℝ} (hξ : 0 < ξ) (hη : 0 < η)
    {D E : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ (distExp d ξ) D)
    (hE : IsStrongExpMetric d η (distExp d η) E)
    {ι : Type} (F : Finset ι) (c : ι → Rd d) {L : ℝ} (hL : 0 < L)
    (hbox : ∀ e ∈ F, closedBall (c e) L ⊆ siteC d) (Ntr : ℕ)
    {v H₀ σ₀ β₀ m M Hsd σsd Hup σ Hlo β mc A0 Kpin : ℝ}
    (hHsd : 0 ≤ Hsd) (hσsd : 0 ≤ σsd) (hHup : 0 ≤ Hup) (hσ : 0 ≤ σ) :
    AEEventIn (pinLaw d 1) (fieldSigma0 id (ann (0 : Rd d) (1 / 2) 4))
      (siteEvent D E F c L Ntr v H₀ σ₀ β₀ m M Hsd σsd Hup σ Hlo β mc A0 Kpin) := by
  let U : Set (Rd d) := ann (0 : Rd d) (1 / 2) 4
  let T := seedTrialEvent D E v H₀ σ₀ β₀ m M Hsd σsd
  have hbase : AEEventIn (pinLaw d 1) (fieldSigma0 id U) T :=
    seedTrial_base_local hd hξ hη hD hE hHsd hσsd
  have htrial (e : ι) (he : e ∈ F) (j : ℕ) :
      AEEventIn (pinLaw d 1) (fieldSigma0 id U)
        {g | recentre 1 (seedTrialRadius L j) (c e) g ∈ T} :=
    p4_aeEventIn_recentre hd one_pos one_pos (seedTrialRadius_pos hL j)
      (c e) (q10_seed_affine_subset_ann4 F c hL hbox he j) hbase
  have hcap (e : ι) (he : e ∈ F) (j : ℕ) :
      AEEventIn (pinLaw d 1) (fieldSigma0 id U)
        {g | |sphereAvg g (seedTrialRadius L j) (c e)| ≤ Kpin} :=
    q10_pinCap_aeEventIn hd (isOpen_ann _ _ _) (seedTrialRadius_pos hL j)
      (c e) ((q10_seed_sphere_subset_siteC F c hL hbox he j).trans
        q10_siteC_subset_ann4) q10_pinSphere_subset_ann4 Kpin
  have hsuccess : AEEventIn (pinLaw d 1) (fieldSigma0 id U)
      {g | ∀ e ∈ F, ∃ j ∈ Finset.range Ntr,
        recentre 1 (seedTrialRadius L j) (c e) g ∈ T} :=
    q10_aeEventIn_finset_all (Ω := DistRd d) F _ (fun e he =>
      q10_aeEventIn_finset_exists (Ω := DistRd d) (Finset.range Ntr) _
        (fun j _ => htrial e he j))
  have hcaps : AEEventIn (pinLaw d 1) (fieldSigma0 id U)
      {g | ∀ e ∈ F, ∀ j ∈ Finset.range Ntr,
        |sphereAvg g (seedTrialRadius L j) (c e)| ≤ Kpin} :=
    q10_aeEventIn_finset_all (Ω := DistRd d) F _ (fun e he =>
      q10_aeEventIn_finset_all (Ω := DistRd d) (Finset.range Ntr) _
        (fun j _ => hcap e he j))
  have href : AEEventIn (pinLaw d 1) (fieldSigma0 id U)
      {g | SiteRefs Hup σ Hlo β mc A0 (rho D g)} :=
    siteRefs_aeEventIn hd hξ hD hHup hσ
  have hset : siteEvent D E F c L Ntr v H₀ σ₀ β₀ m M Hsd σsd
      Hup σ Hlo β mc A0 Kpin =
      {g | SiteRefs Hup σ Hlo β mc A0 (rho D g)} ∩
        ({g | ∀ e ∈ F, ∃ j ∈ Finset.range Ntr,
          recentre 1 (seedTrialRadius L j) (c e) g ∈ T} ∩
         {g | ∀ e ∈ F, ∀ j ∈ Finset.range Ntr,
          |sphereAvg g (seedTrialRadius L j) (c e)| ≤ Kpin}) := by
    ext g
    simp only [siteEvent, mem_inter_iff, mem_ofPred_eq]
    tauto
  rw [hset]
  exact p5b_aeEventIn_inter href (p5b_aeEventIn_inter hsuccess hcaps)

end HigherDimLQGContinuity
