import HigherDimLQGMetric.Sec8b.Lemma84Sampling

/-! A pigeonhole fiber is a valid labeled class for Lemma 8.3. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Classical Set Metric unitInterval
open HigherDimLFPP (Rd)
open HigherDimLFPP.DGZ (latPt)

variable {d : ℕ}

theorem S7bSample.class_eq (a : S7bSample d)
    (c : ℤ × (Fin d → ℤ) × ℤ) (h : a.class = c) :
    a.scale = c.1 ∧ a.colour = c.2.1 ∧ a.bin = c.2.2 := by
  rcases c with ⟨j, col, i⟩
  simpa only [S7bSample.class, Prod.mk.injEq] using h

/-- Sites in a class fiber have distinct centers, so taking their image
preserves the number of sampled radii. -/
theorem s7b_class_fiber_card {θ ε R : ℝ}
    (hε : 0 < ε) (hR : 0 < R)
    (P : C(unitInterval, Rd d)) (x : Rd d)
    (a : Fin (s7b_sampleCount θ ε) → S7bSample d)
    (hrad : ∀ l, ‖P (a l).time - x‖ = s7b_sampleRadius θ ε R l.1)
    (hclose : ∀ l, ‖P (a l).time - (a l).center‖ < (a l).radius / 2)
    (hscale : ∀ l, (a l).radius ≤ ε * R)
    (c : ℤ × (Fin d → ℤ) × ℤ) :
    ((Finset.univ.filter (fun l : Fin (s7b_sampleCount θ ε) =>
        (a l).class = c)).image (fun l => ((a l).center, (a l).label))).card =
      (Finset.univ.filter (fun l : Fin (s7b_sampleCount θ ε) =>
        (a l).class = c)).card := by
  classical
  have hinj := s7b_sample_centers_injective hε hR P x a hrad hclose hscale
  apply Finset.card_image_of_injOn
  intro l _ m _ heq
  exact hinj (congrArg Prod.fst heq)

/-- A fiber of common scale, color, and bin is an actual labeled set
satisfying (C2) and (C3). -/
theorem s7b_class_sites {ξ Q cs Cs B ε R θ : ℝ}
    {D Dt : DistRd d → ContMetric d}
    (T : Sec8TrapData d ξ cs Cs D Dt) (g : DistRd d)
    (hε : 0 < ε) (hR : 0 < R)
    (x y : Rd d) (P : C(unitInterval, Rd d))
    (a : Fin (s7b_sampleCount θ ε) → S7bSample d)
    (ha : ∀ l : Fin (s7b_sampleCount θ ε),
      ‖P (a l).time - x‖ = s7b_sampleRadius θ ε R l.1 ∧
      (a l).scale ∈ scaleWin ε R ∧ (a l).label < T.J ∧
      (a l).bin ∈ s7b_binIndices (ε ^ B) (ε ^ (-B)) ∧
      ‖P (a l).time - (a l).center‖ < (a l).radius / 2 ∧
      ‖(a l).center‖ < 5 * R ∧
      x ∉ closedBall (a l).center (4 * (a l).radius) ∧
      y ∉ closedBall (a l).center (4 * (a l).radius) ∧
      config (D g) (Dt g)
        (sNorm ξ Q g (a l).radius (a l).center)
        (a l).radius (a l).center ∈ T.N (a l).label ∧
      (a l).q * macroS ξ Q g R ≤
        sNorm ξ Q g (a l).radius (a l).center ∧
      sNorm ξ Q g (a l).radius (a l).center ≤
        2 * (a l).q * macroS ξ Q g R)
    (c : ℤ × (Fin d → ℤ) × ℤ) {n : ℕ}
    (hn : n ≤ (Finset.univ.filter (fun l : Fin (s7b_sampleCount θ ε) =>
      (a l).class = c)).card) :
    let r := (64 : ℝ) ^ c.1
    let q := (2 : ℝ) ^ c.2.2
    ∃ s : Finset (Rd d × ℕ), n ≤ s.card ∧
      IsSec8LabeledSet d T.J r R x y c.2.1 s ∧
      sec8C2 D Dt ξ Q q R r T.J T.N s g ∧
      (∀ site ∈ s, ∃ t : unitInterval, P t ∈ ball site.1 r) := by
  classical
  dsimp only
  let r : ℝ := (64 : ℝ) ^ c.1
  let q : ℝ := (2 : ℝ) ^ c.2.2
  let fiber : Finset (Fin (s7b_sampleCount θ ε)) :=
    Finset.univ.filter fun l => (a l).class = c
  let site : Fin (s7b_sampleCount θ ε) → Rd d × ℕ :=
    fun l => ((a l).center, (a l).label)
  let s : Finset (Rd d × ℕ) := fiber.image site
  have hclass (l : Fin (s7b_sampleCount θ ε)) (hl : l ∈ fiber) :=
    (a l).class_eq c (Finset.mem_filter.mp hl).2
  have hradius (l : Fin (s7b_sampleCount θ ε)) (hl : l ∈ fiber) :
      (a l).radius = r := by
    simp only [S7bSample.radius, r, (hclass l hl).1]
  have hq (l : Fin (s7b_sampleCount θ ε)) (hl : l ∈ fiber) :
      (a l).q = q := by
    simp only [S7bSample.q, q, (hclass l hl).2.2]
  have hcenterInj : Function.Injective (fun l => (a l).center) :=
    s7b_sample_centers_injective hε hR P x a
      (fun l => (ha l).1)
      (fun l => (ha l).2.2.2.2.1)
      (fun l => (ha l).2.1.2)
  have hcard : s.card = fiber.card :=
    s7b_class_fiber_card hε hR P x a
      (fun l => (ha l).1)
      (fun l => (ha l).2.2.2.2.1)
      (fun l => (ha l).2.1.2) c
  refine ⟨s, hcard ▸ hn, ?_, ?_, ?_⟩
  · constructor
    · intro u hu
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨_, _, hLabel, _, _, hNorm, hX, hY, _, _, _⟩ := ha l
      have hcl := hclass l hl
      refine ⟨(a l).index, ?_, ?_, hNorm, ?_, ?_, hLabel⟩
      · simp [site, S7bSample.center, S7bSample.radius, hcl.1]
      · simpa only [S7bSample.colour] using hcl.2.1
      · simpa only [hradius l hl] using hX
      · simpa only [hradius l hl] using hY
    · intro u hu v hv hcent
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hv
      have hlm : l = m := hcenterInj hcent
      simp only [site, hlm]
  · intro u hu
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨_, _, hLabel, _, _, _, _, _, hCfg, hLo, hHi⟩ := ha l
    refine ⟨hLabel, ?_, ?_, ?_⟩
    · simpa [site, S7bSample.radius, (hclass l hl).1] using hCfg
    · simpa [site, S7bSample.radius, S7bSample.q,
        (hclass l hl).1, (hclass l hl).2.2] using hLo
    · simpa [site, S7bSample.radius, S7bSample.q,
        (hclass l hl).1, (hclass l hl).2.2] using hHi
  · intro u hu
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨_, hWin, _, _, hClose, _, _, _, _, _, _⟩ := ha l
    have hrpos : 0 < (a l).radius :=
      lt_of_lt_of_le (by positivity : 0 < ε ^ 2 * R) hWin.1
    refine ⟨(a l).time, ?_⟩
    change ‖P (a l).time - (a l).center‖ < r
    rw [← hradius l hl]
    linarith only [hClose, hrpos]

end HigherDimLQGMetric
