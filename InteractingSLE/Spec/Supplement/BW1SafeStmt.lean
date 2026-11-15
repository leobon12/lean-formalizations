/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1VerMain
import InteractingSLE.Spec.Supplement.BW1InMain

/-!
# Proposition BW1's relative safe law for versions with hull identities: the statements and the wiring

Packet PROVE-BW1-SAFELAW. `BW1In.BW1RelSafeLawStatement` asks K2's (S) and (L) for EVERY version of BW1's relative
exploration (`BW1Life.IsBW1RelVersion`), whose pathwise clause relates the relative driver to the physical
counterflow only through the radial limits at the tips (`Chart.tipAt`). K2's lines step needs the HULLS of the
relative driver (the relative hull at the clock value is the image of the physical hull), and passing from continuous
radial limits to the hulls is Rohde–Schramm's Theorem 4.1 with POINTWISE radial limits, which is not available
(QuantumZipper's `RS.gen_no_path` assumes uniform radial convergence). The version that is actually constructed
(`BW1Ver.bw1RelVersionStatement`, GB6's coordinate driver frozen at the gauge stops) has the hull identities, exactly
as GB6's versions do (`IsGB6RelVersion`). This file states:

* **`IsBW1VersionHulls`**: GB6's range and hull clauses for BW1 (relative clock `BW1Ver.rclk`, contact time `T`);
* **`BW1RelVersionHStatement`**: measurable exhausting versions with the hull identities (proved in
  `BW1SafeVer` from Theorem 1.3, by the construction of `bw1RelVersionStatement`);
* **`BW1RelSafeLawHStatement`**: K2's (S) and (L) for every version with the hull identities;
* **`bw1Statement_of_inputsH`**: Proposition BW1 from these two (the proof of `BW1Life.bw1Statement_of_inputs`
  with the version passed with its hull identities; the threshold clause is `ae_canonStp_le_thr_bw`, the
  integrability clause `BW1In.integrable_canonFld_bw`, the endpoint `BW1In.bw1EndpointStatement`).

R48: BW1 serves Theorem 1.4; Theorems 1.2–1.3 may be used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.BW1Safe

open Exist Exist.StagedLaw Exist.Staged Restart BW1Life Supp8.GB6 Supp8.Q3Stop

/-- **The hull clauses of a BW1 relative version** (GB6's `IsGB6RelVersion` clauses for BW1): almost surely on the
threshold event, every relative time before the stop is below a value of the relative clock `a(t) = hcap(Ψ K'_t)/2`
at a physical time before the contact, and at every physical time `t` before the contact with `a(t)` not after the
stop, the relative hull of `R m` at `a(t)` is the image of the physical hull under the relative map of the record. -/
def IsBW1VersionHulls {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (rec : Ω → RecData) (F : Set Ω)
    (W' : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0∞) (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞) : Prop :=
  ∀ m, ∀ᵐ ω ∂P, ω ∈ F →
    (∀ u : ℝ≥0, (u : ℝ≥0∞) < V m ω → ∃ t : ℝ≥0, (t : ℝ≥0∞) < T ω ∧ (u : ℝ) < BW1Ver.rclk (rec ω) (W' · ω) t) ∧
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < T ω → ENNReal.ofReal (BW1Ver.rclk (rec ω) (W' · ω) t) ≤ V m ω →
      fwdHull (Ito.rpath (R m · ω)) (BW1Ver.rclk (rec ω) (W' · ω) t) =
        relMap (rdrv (rec ω)) (BW1Ver.recS (rec ω)) '' fwdHull (Ito.rpath (W' · ω)) t

/-- **Measurable exhausting versions with hull identities** (`BW1Life.BW1RelVersionStatement` with
`IsBW1VersionHulls`). -/
def BW1RelVersionHStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ)
    (ζ' : Ω → ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) (gw2 : Bool) (rest : List Instr) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞),
    IsBW1Setting κ b jumps P h W' ζ' θ t gw2 rest E → ∀ r : Bool,
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞) (ℓ : Ω → ℝ≥0 → ℝ≥0),
      IsBW1RelVersion P (bwRec κ b jumps (bwSpec gw2 θ t rest) E) (bwEvent κ b jumps (bwSpec gw2 θ t rest) E r)
        (bwChart κ b jumps (bwSpec gw2 θ t rest) E) W' (bwContact κ b jumps (bwSpec gw2 θ t rest) W' E) R V ℓ ∧
      IsBW1VersionHulls P (bwRec κ b jumps (bwSpec gw2 θ t rest) E) (bwEvent κ b jumps (bwSpec gw2 θ t rest) E r)
        W' (bwContact κ b jumps (bwSpec gw2 θ t rest) W' E) R V

/-- **Named input: BW1's relative safe law, K2's (S) and (L), for versions with hull identities**
(`BW1In.BW1RelSafeLawStatement` with the extra hypothesis `IsBW1VersionHulls`). -/
def BW1RelSafeLawHStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ)
    (ζ' : Ω → ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) (gw2 : Bool) (rest : List Instr) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞),
    IsBW1Setting κ b jumps P h W' ζ' θ t gw2 rest E → ∀ (r : Bool) (TS : Set RecData), MeasurableSet TS →
    (∀ᵐ ω ∂P, ω ∈ bwEvent κ b jumps (bwSpec gw2 θ t rest) E r ↔ bwRec κ b jumps (bwSpec gw2 θ t rest) E ω ∈ TS) →
    ∀ c₀ : BoundaryWord, c₀.jumps = jumps → (∀ y ∉ jumps, c₀.fn y = b y) →
    ∀ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞) (ℓ : Ω → ℝ≥0 → ℝ≥0),
      IsBW1RelVersion P (bwRec κ b jumps (bwSpec gw2 θ t rest) E) (bwEvent κ b jumps (bwSpec gw2 θ t rest) E r)
        (bwChart κ b jumps (bwSpec gw2 θ t rest) E) W' (bwContact κ b jumps (bwSpec gw2 θ t rest) W' E) R V ℓ →
      IsBW1VersionHulls P (bwRec κ b jumps (bwSpec gw2 θ t rest) E) (bwEvent κ b jumps (bwSpec gw2 θ t rest) E r)
        W' (bwContact κ b jumps (bwSpec gw2 θ t rest) W' E) R V →
      ∀ (m : ℕ) (w : WordType),
        Restart.DomainMarkov.K2.HasSafeLaw (16 / κ) (typedRhoL w) (typedRhoR w)
          ((P.map fun ω => (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω,
            Supp8.GB6.RelDrv.relVar (bwRelField κ b jumps (bwSpec gw2 θ t rest) h E) (R m) (V m) ω))[|
              typeEvent (16 / κ) w (bwRelWord κ θ c₀) TS]) canonFilt univ canonStp canonDrv
          (Sec7.PocketTraversal.geomLW canonDrv fun y => typedXL (16 / κ) w (bwRelWord κ θ c₀ y.1))
          (Sec7.PocketTraversal.geomRW canonDrv fun y => typedXR (16 / κ) w (bwRelWord κ θ c₀ y.1)) canonFld ∧
        Restart.DomainMarkov.K2.HasSafeMembers
          ((P.map fun ω => (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω,
            Supp8.GB6.RelDrv.relVar (bwRelField κ b jumps (bwSpec gw2 θ t rest) h E) (R m) (V m) ω))[|
              typeEvent (16 / κ) w (bwRelWord κ θ c₀) TS]) canonFilt univ canonStp canonDrv canonFld

/-- The tip-form statement implies the hull-form one. -/
theorem bw1RelSafeLawHStatement_of_law (hL : BW1In.BW1RelSafeLawStatement.{u}) : BW1RelSafeLawHStatement.{u} :=
  fun κ b jumps _ _ _ P _ h W' ζ' θ t gw2 rest E hset r TS hTS hFTS c₀ hc₀J hc₀ R V ℓ hver _ m w =>
    hL κ b jumps P h W' ζ' θ t gw2 rest E hset r TS hTS hFTS c₀ hc₀J hc₀ R V ℓ hver m w

/-- **The full relative safe law of one version with hull identities** (`HasRelSafe`: the threshold clause is
`ae_canonStp_le_thr_bw`, the integrability clause `BW1In.integrable_canonFld_bw`). -/
theorem hasRelSafe_of_lawH (hT13₀ : Exist.Theorem13Statement.{0}) (hL : BW1RelSafeLawHStatement.{u}) {κ : ℝ}
    {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {θ : ℝ}
    {t : ℝ≥0∞} {gw2 : Bool} {rest : List Instr} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hset : IsBW1Setting κ b jumps P h W' ζ' θ t gw2 rest E) {r : Bool} {TS : Set RecData}
    (hTS : MeasurableSet TS)
    (hFTS : ∀ᵐ ω ∂P, ω ∈ bwEvent κ b jumps (bwSpec gw2 θ t rest) E r ↔ bwRec κ b jumps (bwSpec gw2 θ t rest) E ω ∈ TS)
    {c₀ : BoundaryWord} (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y)
    {R : ℕ → ℝ≥0 → Ω → ℝ} {V : ℕ → Ω → ℝ≥0∞} {ℓ : Ω → ℝ≥0 → ℝ≥0}
    (hver : IsBW1RelVersion P (bwRec κ b jumps (bwSpec gw2 θ t rest) E) (bwEvent κ b jumps (bwSpec gw2 θ t rest) E r)
      (bwChart κ b jumps (bwSpec gw2 θ t rest) E) W' (bwContact κ b jumps (bwSpec gw2 θ t rest) W' E) R V ℓ)
    (hhull : IsBW1VersionHulls P (bwRec κ b jumps (bwSpec gw2 θ t rest) E)
      (bwEvent κ b jumps (bwSpec gw2 θ t rest) E r) W' (bwContact κ b jumps (bwSpec gw2 θ t rest) W' E) R V)
    (m : ℕ) (w : WordType) :
    HasRelSafe (16 / κ) w (bwRelWord κ θ c₀) TS
      (P.map fun ω => (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω,
        Supp8.GB6.RelDrv.relVar (bwRelField κ b jumps (bwSpec gw2 θ t rest) h E) (R m) (V m) ω)) := by
  have hset' := hset
  obtain ⟨hκ, hκ4, hb, hh, hcf, hζ', hθ, hS⟩ := hset'
  obtain ⟨hambL, hambR⟩ := GW1Conn.ambient_bounds (BR3Ref.gw0ForwardStatement_of_theorem13 hT13₀) hκ hκ4 hb hh hcf
    hζ'
  have hbL : ∀ y, y < 0 → y ∉ c₀.jumps → c₀.fn y + -(Real.pi / 2) * chiC κ < sleLambda κ := fun y hy hyJ => by
    rw [hc₀J] at hyJ; rw [hc₀ y hyJ]; exact hambL y hy hyJ
  have hbR : ∀ y, 0 < y → y ∉ c₀.jumps → -sleLambda κ < c₀.fn y + Real.pi / 2 * chiC κ := fun y hy hyJ => by
    rw [hc₀J] at hyJ; rw [hc₀ y hyJ]; exact hambR y hy hyJ
  obtain ⟨hlaw, hmem⟩ := hL κ b jumps P h W' ζ' θ t gw2 rest E hset r TS hTS hFTS c₀ hc₀J hc₀ R V ℓ hver hhull m w
  exact ⟨hlaw, hmem, ae_canonStp_le_thr_bw hκ hκ4 hθ hbL hbR _ TS w,
    fun φ => BW1In.integrable_canonFld_bw hset hTS hFTS hc₀J hc₀ (hver.1 m) (hver.2.2.2.2.1 m) w φ⟩

/-- **Proposition BW1 from versions with hull identities and their safe law** (the proof of
`BW1Life.bw1Statement_of_inputs`, the endpoint being `BW1In.bw1EndpointStatement`). -/
theorem bw1Statement_of_inputsH (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hT13₀ : Exist.Theorem13Statement.{0})
    (hcode : Restart.CanonicalDriverCodeStatement) (hV : BW1RelVersionHStatement.{u})
    (hL : BW1RelSafeLawHStatement.{u}) : BW1.BW1Statement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω mΩ _ P _ h hh W' ζ' hcf hζ' θ hθ t gw2 rest E hS r
  have hset : IsBW1Setting κ b jumps P h W' ζ' θ t gw2 rest E := ⟨hκ, hκ4, hb, hh, hcf, hζ', hθ, hS⟩
  obtain ⟨c₀, hc₀J, hc₀⟩ := Restart.BoundaryWord.exists_fn_eq hb
  obtain ⟨F, hF⟩ := hcode (16 / κ) 0 (GW4Traverse.sixteen_div_pos hκ)
  obtain ⟨hWm, hζm, hcond, hreg⟩ := condCounterflow_first (spec := bwSpec gw2 θ t rest) h12p h13 hT13₀ hκ hκ4 hb hh
    hcf hζ' hθ rfl rfl hS hc₀J hc₀
  obtain ⟨R, V, ℓ, hver, hhull⟩ := hV κ b jumps P h W' ζ' θ t gw2 rest E hset r
  obtain ⟨TS, hTS, hFTS⟩ := exists_recordEvent h13 hκ hb hh hS r
  have hsafe := fun m w => hasRelSafe_of_lawH hT13₀ hL hset hTS hFTS hc₀J hc₀ hver hhull m w
  have heq := ae_bwDrv_eq_of_relSafe h12p h13 hκ hb hh hS hc₀J hc₀ hF hTS hFTS hver hsafe
  have hFM : bwEvent κ b jumps (bwSpec gw2 θ t rest) E r ⊆ {ω | min t (E 0 ω).2 ≠ ⊤} := fun ω hω =>
    finStop_of_mem_bwEvent hω
  have hcondF := hcond.mono hFM
  have hregF := hreg.mono fun ω hω hFω => hω (hFM hFω)
  have hend := BW1In.bw1EndpointStatement h13 hT13₀ κ b jumps P h W' ζ' θ t gw2 rest E hset r R V ℓ hver _ _ hWm hζm
    hcondF hregF heq
  refine ⟨_, _, ℓ, hcondF, hver.2.2.2.2.2.1, ?_⟩
  filter_upwards [hregF, hend, hver.2.2.2.2.2.2.2, heq] with ω hr he hv hq hFω
  obtain ⟨hζ, -, -⟩ := hr hFω
  obtain ⟨hsup, hT, htip⟩ := he hFω
  obtain ⟨-, hmono, hcont, himg, htipR⟩ := hv hFω
  have huniv : {s : ℝ≥0 | (s : ℝ≥0∞) < ⨆ m, V m ω} = univ :=
    eq_univ_of_forall fun s => by rw [mem_ofPred_eq, hsup]; exact ENNReal.coe_lt_top
  rw [huniv] at hmono hcont himg
  refine ⟨hζ, hT, htip, continuousOn_univ.1 hcont, strictMonoOn_univ.1 hmono, ?_, fun s z => ?_⟩
  · rw [← image_univ]; exact himg
  · obtain ⟨m, hm⟩ : ∃ m, (s : ℝ≥0∞) < V m ω := lt_iSup_iff.1 (by rw [hsup]; exact ENNReal.coe_lt_top)
    rw [← htipR m s hm z]
    exact tipAt_congr_of_lt _ hm (fun u hu => hq hFω m u hu) z

end InteractingSLE.Theorem14.BW1Safe
