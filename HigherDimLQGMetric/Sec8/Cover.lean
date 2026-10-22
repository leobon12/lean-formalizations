import HigherDimLQGMetric.Sec6.Defs
import HigherDimLQGMetric.Events.ShellCover
import HigherDimLQGMetric.Freq.ScaleCount

/-!
# Section 7: the common covering event

This file applies the rounded-centre shell cover to the finite union of trap
configuration events.  The numerical threshold returned by `ShellCover` is
raised to a positive number before using `TrapFamily`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set
open HigherDimLFPP (Rd)
open HigherDimLFPP.DGZ (latPt)
open scoped ENNReal

variable {d : ℕ}

/-- A center is good when one of the finitely many trap configurations occurs. -/
def trapSiteEvent (D Dt : DistRd d → ContMetric d) (ξ Q : ℝ)
    (J : ℕ) (N : ℕ → Set (Config d)) (r : ℝ) (z : Rd d) : Set (DistRd d) :=
  {g | ∃ j < J, config (D g) (Dt g) (sNorm ξ Q g r z) r z ∈ N j}

theorem measurableSet_trapConfigs {J : ℕ} {N : ℕ → Set (Config d)}
    (hN : ∀ j < J, MeasurableSet (N j)) :
    MeasurableSet {c : Config d | ∃ j < J, c ∈ N j} := by
  have heq : {c : Config d | ∃ j < J, c ∈ N j} =
      ⋃ j : Fin J, N j.1 := by
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨j, hj, hc⟩
      exact ⟨⟨j, hj⟩, hc⟩
    · rintro ⟨j, hc⟩
      exact ⟨j.1, j.2, hc⟩
  rw [heq]
  exact MeasurableSet.iUnion fun j => hN j.1 j.2

/-- The trap union is shell-local, as required by the covering lemma. -/
theorem trapSiteEvent_shellLocal {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hh : IsWholeSpaceLGF h P) {D Dt : DistRd d → ContMetric d}
    {ξ Q : ℝ} (hLoc : ConfigLocal d ξ Q D Dt)
    {J : ℕ} {N : ℕ → Set (Config d)} (hN : ∀ j < J, MeasurableSet (N j)) :
    IsShellLocal P h (fun z r => h ⁻¹' trapSiteEvent D Dt ξ Q J N r z) := by
  intro z r hr
  exact hLoc P h hh r z hr _ (measurableSet_trapConfigs hN)

/-- The finite trap data selected in Proposition 6.2, retained for the
perturbation counting argument. -/
structure Sec8TrapData (d : ℕ) (ξ cs Cs : ℝ)
    (D Dt : DistRd d → ContMetric d) where
  m : ℕ
  V : Set (Rd d)
  J : ℕ
  f : ℕ → C(Rd d, ℝ)
  N : ℕ → Set (Config d)
  a : ℝ
  b : ℝ
  c : ℝ
  g : ℝ
  H : ℝ
  Mf : ℝ
  c' : ℝ
  openV : IsOpen V
  closureV : closure V ⊆ ann 0 1 3
  sphereV : Metric.sphere (0 : Rd d) 2 ⊆ V
  bumps : ∀ j < J, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f j) ∧
    HasCompactSupport (f j) ∧ tsupport (f j) ⊆ ann 0 1 3 ∧
    (∀ x, 0 ≤ f j x) ∧ (∀ x, 0 < f j x ↔ x ∈ V) ∧ (∀ x, f j x ≤ Mf)
  constants : 0 < a ∧ 0 < b ∧ 0 < c ∧ g = a ∧
    H = a * Real.exp (ξ * Mf) ∧ c' < Cs ∧ 2 * b < g / 2
  measurableN : ∀ j < J, MeasurableSet (N j)
  traps : ∀ D₀ Dt₀ : ContMetric d, D₀.IsLength → Dt₀.IsLength →
      (∀ x y, cs * D₀.1 (x, y) ≤ Dt₀.1 (x, y) ∧
        Dt₀.1 (x, y) ≤ Cs * D₀.1 (x, y)) →
      ∀ (s r : ℝ) (z : Rd d) (j : ℕ), 0 < s → 0 < r → j < J →
        config D₀ Dt₀ s r z ∈ N j →
          TrapProps ξ V f J a b c g H c' D₀ Dt₀ s r z j

/-- Lemma 7.2 after the trap family has been selected. `hProb` is exactly
Proposition 6.2(P), and `hCor` is Corollary 6.3 at its resulting shift `m`.
The output retains the actual set of admissible scales for later counting. -/
theorem lemma72_cover
    {D Dt : DistRd d → ContMetric d} {ξ Q : ℝ}
    {cs c0 c1 aL A₀L ℓL β₀L pstar : ℝ}
    {m J : ℕ} {N : ℕ → Set (Config d)} {p p' : ℝ}
    (hpp' : p ≤ p')
    (hCover : ∀ L C₀ : ℝ, 0 < L → 0 ≤ C₀ → ∃ C ε₁ : ℝ, 0 < ε₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsWholeSpaceLGF h P →
      ∀ E : Rd d → ℝ → Set Ω, IsShellLocal P h E →
      ∀ R ε : ℝ, 0 < R → 0 < ε → ε < ε₁ → ∀ T : Finset ℤ,
        (∀ j ∈ T, j ∈ scaleWin ε R) →
        (2 / 3 : ℝ) * Real.logb 64 ε⁻¹ - C₀ ≤ T.card →
        (∀ j ∈ T, ∀ z : Rd d, ENNReal.ofReal p ≤ P (E z ((64 : ℝ) ^ j))) →
        P {ω | ¬ ∀ x ∈ Metric.ball (0 : Rd d) (L * R),
          ∃ j ∈ T, ∃ k : Fin d → ℤ,
            ‖x - latPt ((64 : ℝ) ^ j / (100 * d)) k‖ < (64 : ℝ) ^ j / 2 ∧
            ω ∈ E (latPt ((64 : ℝ) ^ j / (100 * d)) k) ((64 : ℝ) ^ j)} ≤
          ENNReal.ofReal (C * ε ^ (1 : ℝ)))
    (hLoc : ConfigLocal d ξ Q D Dt)
    (hN : ∀ j < J, MeasurableSet (N j))
    (hCor : Cor63 d ξ Q D Dt cs c0 c1 aL A₀L ℓL β₀L pstar m)
    (hProb : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsWholeSpaceLGF h P → ∀ r : ℝ, 0 < r →
      ENNReal.ofReal pstar ≤ P (h ⁻¹' WitEvent Dt D ξ Q cs⁻¹ aL A₀L ℓL β₀L c1⁻¹
        ((64 : ℝ)⁻¹ ^ m * r) 0) →
      ∀ z : Rd d, ENNReal.ofReal p' ≤
        P (h ⁻¹' trapSiteEvent D Dt ξ Q J N r z)) :
    ∃ C ε₁ : ℝ, 0 < ε₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsWholeSpaceLGF h P →
      ∀ R : ℝ, 0 < R →
        ENNReal.ofReal pstar ≤ P (h ⁻¹' WitEvent Dt D ξ Q cs⁻¹ aL A₀L ℓL β₀L c0⁻¹ R 0) →
      ∀ ε : ℝ, 0 < ε → ε < ε₁ →
        P {ω | ¬ ∀ x ∈ Metric.ball (0 : Rd d) (5 * R),
          ∃ j ∈ scaleWin ε R, ∃ k : Fin d → ℤ,
            ‖x - latPt ((64 : ℝ) ^ j / (100 * d)) k‖ < (64 : ℝ) ^ j / 2 ∧
            h ω ∈ trapSiteEvent D Dt ξ Q J N ((64 : ℝ) ^ j)
              (latPt ((64 : ℝ) ^ j / (100 * d)) k)} ≤
          ENNReal.ofReal (C * ε) := by
  obtain ⟨C, εc, hεc, hCover⟩ := hCover 5 1 (by norm_num) (by norm_num)
  obtain ⟨ε₀, hε₀, hCor⟩ := hCor
  refine ⟨C, min εc (min ε₀ (1 / 64)), by positivity, ?_⟩
  intro Ω _ P _ h hh R hR hW ε hε hε1
  have hεc' : ε < εc := lt_of_lt_of_le hε1 (min_le_left _ _)
  have hε₀' : ε < ε₀ :=
    lt_of_lt_of_le (lt_of_lt_of_le hε1 (min_le_right _ _)) (min_le_left _ _)
  have hεsmall : ε < (1 / 64 : ℝ) :=
    lt_of_lt_of_le (lt_of_lt_of_le hε1 (min_le_right _ _)) (min_le_right _ _)
  let Tset : Set ℤ := {j ∈ scaleWin ε R |
    ENNReal.ofReal pstar ≤ P (h ⁻¹' WitEvent Dt D ξ Q cs⁻¹ aL A₀L ℓL β₀L c1⁻¹
      ((64 : ℝ)⁻¹ ^ m * (64 : ℝ) ^ j) 0)}
  have hTfin : Tset.Finite :=
    (s4c_scaleWin_finite hε hR).subset (fun j hj => hj.1)
  let T : Finset ℤ := hTfin.toFinset
  have hTmem (j : ℤ) : j ∈ T ↔ j ∈ Tset := hTfin.mem_toFinset
  have hTw : ∀ j ∈ T, j ∈ scaleWin ε R := by
    intro j hj
    exact (hTmem j).mp hj |>.1
  have hcount0 := hCor P h hh R hR hW ε hε hε₀'
  have hcount1 := s4c_scaleWin_count hε hεsmall hR
  have hTcard : (2 / 3 : ℝ) * Real.logb 64 ε⁻¹ - 1 ≤ (T.card : ℝ) := by
    have heq : Tset.ncard = T.card := Set.ncard_eq_toFinset_card Tset hTfin
    rw [heq] at hcount0
    linarith only [hcount0, hcount1]
  have hprob : ∀ j ∈ T, ∀ z : Rd d,
      ENNReal.ofReal p ≤ P (h ⁻¹' trapSiteEvent D Dt ξ Q J N ((64 : ℝ) ^ j) z) := by
    intro j hj z
    have hw := ((hTmem j).mp hj).2
    have hb := hProb P h hh ((64 : ℝ) ^ j)
      (zpow_pos (by norm_num) j) hw z
    exact (ENNReal.ofReal_le_ofReal hpp').trans hb
  have hloc := trapSiteEvent_shellLocal P h hh hLoc hN
  have hraw := hCover P h hh (fun z r => h ⁻¹' trapSiteEvent D Dt ξ Q J N r z)
    hloc R ε hR hε hεc' T hTw hTcard hprob
  calc
    P {ω | ¬ ∀ x ∈ Metric.ball (0 : Rd d) (5 * R),
        ∃ j ∈ scaleWin ε R, ∃ k : Fin d → ℤ,
          ‖x - latPt ((64 : ℝ) ^ j / (100 * d)) k‖ < (64 : ℝ) ^ j / 2 ∧
          h ω ∈ trapSiteEvent D Dt ξ Q J N ((64 : ℝ) ^ j)
            (latPt ((64 : ℝ) ^ j / (100 * d)) k)}
      ≤ P {ω | ¬ ∀ x ∈ Metric.ball (0 : Rd d) (5 * R),
          ∃ j ∈ T, ∃ k : Fin d → ℤ,
            ‖x - latPt ((64 : ℝ) ^ j / (100 * d)) k‖ < (64 : ℝ) ^ j / 2 ∧
            h ω ∈ trapSiteEvent D Dt ξ Q J N ((64 : ℝ) ^ j)
              (latPt ((64 : ℝ) ^ j / (100 * d)) k)} := by
          apply measure_mono
          intro ω hbad hgood
          apply hbad
          intro x hx
          obtain ⟨j, hj, k, hk, hsite⟩ := hgood x hx
          exact ⟨j, hTw j hj, k, hk, hsite⟩
    _ ≤ ENNReal.ofReal (C * ε) := by simpa only [Real.rpow_one, Set.mem_preimage] using hraw

/-- **[S] Lemma 7.2.** The trap data are chosen once, before the LGF, macro
scale, endpoints, and perturbation size. The covering constants are uniform
over all LGF realizations and all macro scales satisfying (19). -/
theorem lemma72 (hd : 3 ≤ d) {ξ Q : ℝ} (_hξ : 0 < ξ)
    (_hQ : Real.sqrt (2 * d) < Q)
    {D Dt : DistRd d → ContMetric d}
    {cs Cs c0 c1 aL A₀L ℓL β₀L pstar : ℝ}
    (hTrap : TrapFamily d ξ Q D Dt cs Cs c1 aL A₀L ℓL β₀L pstar)
    (hLoc : ConfigLocal d ξ Q D Dt)
    (hCor : ∀ m : ℕ, Cor63 d ξ Q D Dt cs c0 c1 aL A₀L ℓL β₀L pstar m) :
    ∃ T : Sec8TrapData d ξ cs Cs D Dt, ∃ C ε₁ : ℝ, 0 < ε₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsWholeSpaceLGF h P →
      ∀ R : ℝ, 0 < R →
        ENNReal.ofReal pstar ≤ P (h ⁻¹' WitEvent Dt D ξ Q cs⁻¹ aL A₀L ℓL β₀L c0⁻¹ R 0) →
      ∀ ε : ℝ, 0 < ε → ε < ε₁ →
        P {ω | ¬ ∀ x ∈ Metric.ball (0 : Rd d) (5 * R),
          ∃ j ∈ scaleWin ε R, ∃ k : Fin d → ℤ,
            ‖x - latPt ((64 : ℝ) ^ j / (100 * d)) k‖ < (64 : ℝ) ^ j / 2 ∧
            h ω ∈ trapSiteEvent D Dt ξ Q T.J T.N ((64 : ℝ) ^ j)
              (latPt ((64 : ℝ) ^ j / (100 * d)) k)} ≤
          ENNReal.ofReal (C * ε) := by
  obtain ⟨p, hp1, hCover⟩ := shellCover (d := d) (by omega) (2 / 3) 1
    (by norm_num) (by norm_num)
  let p' : ℝ := max p (1 / 2)
  have hp'0 : 0 < p' := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (le_max_right _ _)
  have hp'1 : p' < 1 := max_lt hp1 (by norm_num)
  obtain ⟨m, V, J, f, N, a, b, c, g, H, Mf, c',
    hOpen, hClosure, hSphere, hf, ha, hb, hc, hg, hH, hc', h2b, hN, hP, hT⟩ :=
    hTrap p' hp'0 hp'1
  let T : Sec8TrapData d ξ cs Cs D Dt :=
    { m := m, V := V, J := J, f := f, N := N,
      a := a, b := b, c := c, g := g, H := H, Mf := Mf, c' := c',
      openV := hOpen, closureV := hClosure, sphereV := hSphere,
      bumps := hf, constants := ⟨ha, hb, hc, hg, hH, hc', h2b⟩,
      measurableN := hN, traps := hT }
  have hProb : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsWholeSpaceLGF h P → ∀ r : ℝ, 0 < r →
      ENNReal.ofReal pstar ≤ P (h ⁻¹' WitEvent Dt D ξ Q cs⁻¹ aL A₀L ℓL β₀L c1⁻¹
        ((64 : ℝ)⁻¹ ^ m * r) 0) →
      ∀ z : Rd d, ENNReal.ofReal p' ≤
        P (h ⁻¹' trapSiteEvent D Dt ξ Q J N r z) := by
    intro Ω _ P _ h hh r hr hw z
    change ENNReal.ofReal p' ≤ P {ω | ∃ j < J,
      config (D (h ω)) (Dt (h ω)) (sNorm ξ Q (h ω) r z) r z ∈ N j}
    exact hP P h hh r hr hw z
  obtain ⟨C, ε₁, hε₁, hcov⟩ := lemma72_cover (d := d) (D := D) (Dt := Dt)
    (ξ := ξ) (Q := Q) (cs := cs) (c0 := c0) (c1 := c1) (aL := aL)
    (A₀L := A₀L) (ℓL := ℓL) (β₀L := β₀L) (pstar := pstar)
    (m := m) (J := J) (N := N) (p := p) (p' := p')
    (le_max_left p (1 / 2)) hCover hLoc hN (hCor m) hProb
  exact ⟨T, C, ε₁, hε₁, hcov⟩

end HigherDimLQGMetric
