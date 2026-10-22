import HigherDimLQGMetric.Sec8b.Lemma84Sites
import HigherDimLQGMetric.Sec8b.Lemma84Count

/-! Equally spaced radial samples used in Lemma 8.4. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric unitInterval
open HigherDimLFPP (Rd)

/-- Number of radial samples from radius `θR/4` to radius `θR/2`. -/
def s7b_sampleCount (θ ε : ℝ) : ℕ := ⌈θ / (80 * ε)⌉₊

def s7b_sampleRadius (θ ε R : ℝ) (l : ℕ) : ℝ :=
  θ * R / 4 + 20 * ε * R * l

/-- Every sample level lies in the required annular range and below the
endpoint separation. -/
theorem s7b_sampleRadius_bounds {θ ε R η : ℝ}
    (hθ : 0 < θ) (hε : 0 < ε) (hR : 0 < R)
    (hθη : θ ≤ η) {l : ℕ} (hl : l < s7b_sampleCount θ ε) :
    θ * R / 4 ≤ s7b_sampleRadius θ ε R l ∧
      s7b_sampleRadius θ ε R l ≤ θ * R / 2 ∧
      0 ≤ s7b_sampleRadius θ ε R l ∧
      s7b_sampleRadius θ ε R l ≤ η * R := by
  have hlreal : (l : ℝ) < θ / (80 * ε) := by
    simpa only [s7b_sampleCount] using (Nat.lt_ceil.mp hl)
  have hden : 0 < 80 * ε := by positivity
  have hbound : (l : ℝ) * (80 * ε) < θ :=
    (lt_div_iff₀ hden).mp hlreal
  have hpart : 20 * ε * R * (l : ℝ) < θ * R / 4 := by
    have hmul := mul_lt_mul_of_pos_right hbound (show 0 < R / 4 by positivity)
    nlinarith only [hmul]
  have hθR : θ * R ≤ η * R :=
    mul_le_mul_of_nonneg_right hθη hR.le
  have hnonneg : 0 ≤ 20 * ε * R * (l : ℝ) := by positivity
  dsimp only [s7b_sampleRadius]
  constructor
  · linarith only [hnonneg]
  constructor
  · linarith only [hpart]
  constructor
  · nlinarith only [hθ, hR, hnonneg]
  · linarith only [hpart, hθR, mul_pos hθ hR]

/-- Consecutive radial levels are separated by exactly `20 ε R`. -/
theorem s7b_sampleRadius_gap (θ ε R : ℝ) (l : ℕ) :
    s7b_sampleRadius θ ε R l + 20 * ε * R =
      s7b_sampleRadius θ ε R (l + 1) := by
  dsimp only [s7b_sampleRadius]
  push_cast
  ring

/-- The five finite choices attached to one radial sample. -/
structure S7bSample (d : ℕ) where
  time : unitInterval
  scale : ℤ
  index : Fin d → ℤ
  label : ℕ
  bin : ℤ

def S7bSample.radius {d : ℕ} (a : S7bSample d) : ℝ := (64 : ℝ) ^ a.scale

def S7bSample.center {d : ℕ} (a : S7bSample d) : Rd d :=
  HigherDimLFPP.DGZ.latPt (a.radius / (100 * d)) a.index

def S7bSample.q {d : ℕ} (a : S7bSample d) : ℝ := (2 : ℝ) ^ a.bin

def S7bSample.colour {d : ℕ} (a : S7bSample d) : Fin d → ℤ :=
  sec8Color d a.index

def S7bSample.class {d : ℕ} (a : S7bSample d) :
    ℤ × (Fin d → ℤ) × ℤ := (a.scale, a.colour, a.bin)

/-- The finite scale, color, and dyadic-bin classes for one `ε,R`. -/
def s7b_classSet (d : ℕ) {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R)
    (B : ℝ) : Finset (ℤ × (Fin d → ℤ) × ℤ) :=
  (s4c_scaleWin_finite hε hR).toFinset.product
    ((sec8Colors d).product (s7b_binIndices (ε ^ B) (ε ^ (-B))))

theorem s7b_sample_class_mem {d : ℕ} {ε R B : ℝ}
    (hε : 0 < ε) (hR : 0 < R)
    (hd : 1 ≤ d) (a : S7bSample d)
    (hj : a.scale ∈ scaleWin ε R)
    (hi : a.bin ∈ s7b_binIndices (ε ^ B) (ε ^ (-B))) :
    a.class ∈ s7b_classSet d hε hR B := by
  change (a.scale, (a.colour, a.bin)) ∈
    (s4c_scaleWin_finite hε hR).toFinset.product
      ((sec8Colors d).product (s7b_binIndices (ε ^ B) (ε ^ (-B))))
  exact Finset.mem_product.mpr
    ⟨(s4c_scaleWin_finite hε hR).mem_toFinset.mpr hj,
      Finset.mem_product.mpr ⟨sec8Color_mem_colors hd a.index, hi⟩⟩

/-- Every radial level gets a covering site, trap label, and dyadic bin. The
choice is simultaneous because the index set is finite. -/
theorem s7b_choose_samples {d : ℕ} {ξ Q cs Cs B ε R η θ : ℝ}
    {D Dt : DistRd d → ContMetric d}
    (T : Sec8TrapData d ξ cs Cs D Dt) (g : DistRd d)
    (hR : 0 < R) (hε : 0 < ε) (hεθ : ε < θ / 18)
    (hθ : 0 < θ) (hθη : θ ≤ η) (hθ1 : θ ≤ 1)
    (x y : Rd d) (hx : ‖x‖ < 3 * R) (hxy : η * R ≤ ‖x - y‖)
    (P : C(unitInterval, Rd d)) (hP0 : P 0 = x) (hP1 : P 1 = y)
    (hcover : g ∈ sec8CoverEvent D Dt ξ Q T.J T.N ε R)
    (hbin : g ∈ sec8BinEvent d ξ Q B ε R) :
    ∃ a : Fin (s7b_sampleCount θ ε) → S7bSample d,
      ∀ l : Fin (s7b_sampleCount θ ε),
        ‖P (a l).time - x‖ = s7b_sampleRadius θ ε R l.1 ∧
        (a l).scale ∈ scaleWin ε R ∧
        (a l).label < T.J ∧
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
          2 * (a l).q * macroS ξ Q g R := by
  classical
  have hex (l : Fin (s7b_sampleCount θ ε)) :
      ∃ a : S7bSample d,
        ‖P a.time - x‖ = s7b_sampleRadius θ ε R l.1 ∧
        a.scale ∈ scaleWin ε R ∧ a.label < T.J ∧
        a.bin ∈ s7b_binIndices (ε ^ B) (ε ^ (-B)) ∧
        ‖P a.time - a.center‖ < a.radius / 2 ∧
        ‖a.center‖ < 5 * R ∧
        x ∉ closedBall a.center (4 * a.radius) ∧
        y ∉ closedBall a.center (4 * a.radius) ∧
        config (D g) (Dt g) (sNorm ξ Q g a.radius a.center)
          a.radius a.center ∈ T.N a.label ∧
        a.q * macroS ξ Q g R ≤ sNorm ξ Q g a.radius a.center ∧
        sNorm ξ Q g a.radius a.center ≤ 2 * a.q * macroS ξ Q g R := by
    have hb := s7b_sampleRadius_bounds hθ hε hR hθη l.2
    obtain ⟨t, ht⟩ := s7b_exists_radius_hit P x y hP0 hP1
      hb.2.2.1 (hb.2.2.2.trans (by simpa only [norm_sub_rev] using hxy))
    obtain ⟨j, hj, k, label, hlabel, i, hi, hclose, hz, hxout, hyout,
      hcfg, hslo, hshi⟩ := s7b_sample_site T g hR hε hεθ hθ hθη hθ1
        x y hx hxy P t (ht ▸ hb.1) (ht ▸ hb.2.1) hcover hbin
    refine ⟨⟨t, j, k, label, i⟩, ht, hj, hlabel, hi,
      hclose, hz, hxout, hyout, hcfg, hslo, hshi⟩
  exact ⟨fun l => Classical.choose (hex l), fun l => Classical.choose_spec (hex l)⟩

/-- Sampled centers are all distinct, even before taking a color class. -/
theorem s7b_sample_centers_injective {d : ℕ} {θ ε R : ℝ}
    (hε : 0 < ε) (hR : 0 < R)
    (P : C(unitInterval, Rd d)) (x : Rd d)
    (a : Fin (s7b_sampleCount θ ε) → S7bSample d)
    (hrad : ∀ l, ‖P (a l).time - x‖ = s7b_sampleRadius θ ε R l.1)
    (hclose : ∀ l, ‖P (a l).time - (a l).center‖ < (a l).radius / 2)
    (hscale : ∀ l, (a l).radius ≤ ε * R) :
    Function.Injective (fun l => (a l).center) := by
  have hsep (l m : Fin (s7b_sampleCount θ ε)) (hlm : l.1 < m.1) :
      18 * (ε * R) < ‖(a l).center - (a m).center‖ := by
    have hgap : s7b_sampleRadius θ ε R l.1 + 20 * (ε * R) ≤
        s7b_sampleRadius θ ε R m.1 := by
      have hcast : ((l.1 : ℝ) + 1) ≤ (m.1 : ℝ) := by exact_mod_cast hlm
      have hmul := mul_le_mul_of_nonneg_left hcast
        (show 0 ≤ 20 * ε * R by positivity)
      dsimp only [s7b_sampleRadius]
      nlinarith only [hmul]
    have hcl : ‖P (a l).time - (a l).center‖ < (ε * R) / 2 :=
      lt_of_lt_of_le (hclose l) (div_le_div_of_nonneg_right (hscale l) (by norm_num))
    have hcm : ‖P (a m).time - (a m).center‖ < (ε * R) / 2 :=
      lt_of_lt_of_le (hclose m) (div_le_div_of_nonneg_right (hscale m) (by norm_num))
    exact s7b_centers_separated (mul_pos hε hR) (hrad l) (hrad m)
      hgap hcl hcm
  intro l m heq
  change (a l).center = (a m).center at heq
  rcases lt_trichotomy l.1 m.1 with hlm | hval | hml
  · have hs := hsep l m hlm
    rw [heq, sub_self, norm_zero] at hs
    exact False.elim ((not_lt_of_ge (by positivity : 0 ≤ 18 * (ε * R))) hs)
  · exact Fin.ext hval
  · have hs := hsep m l hml
    rw [heq, sub_self, norm_zero] at hs
    exact False.elim ((not_lt_of_ge (by positivity : 0 ≤ 18 * (ε * R))) hs)

/-- The finite pigeonhole step selecting one common scale, color, and bin. -/
theorem s7b_pigeonhole_samples {d : ℕ} {ε R B θ : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (hθ : 0 < θ)
    (hd : 1 ≤ d)
    (a : Fin (s7b_sampleCount θ ε) → S7bSample d)
    (hscale : ∀ l, (a l).scale ∈ scaleWin ε R)
    (hbin : ∀ l, (a l).bin ∈ s7b_binIndices (ε ^ B) (ε ^ (-B)))
    {n : ℕ}
    (hcount : (s7b_classSet d hε hR B).card * n ≤ s7b_sampleCount θ ε) :
    ∃ c ∈ s7b_classSet d hε hR B,
      n ≤ (Finset.univ.filter (fun l : Fin (s7b_sampleCount θ ε) =>
        (a l).class = c)).card := by
  classical
  have hmem : ∀ l : Fin (s7b_sampleCount θ ε),
      (a l).class ∈ s7b_classSet d hε hR B :=
    fun l => s7b_sample_class_mem hε hR hd (a l) (hscale l) (hbin l)
  have hLpos : 0 < s7b_sampleCount θ ε := by
    rw [s7b_sampleCount, Nat.ceil_pos]
    positivity
  have hnonempty : (s7b_classSet d hε hR B).Nonempty :=
    ⟨(a ⟨0, hLpos⟩).class, hmem _⟩
  simpa only [Finset.card_univ, Fintype.card_fin] using
    (Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := Finset.univ) (t := s7b_classSet d hε hR B)
      (f := fun l : Fin (s7b_sampleCount θ ε) => (a l).class)
      (n := n) (fun l _ => hmem l) hnonempty (by
        simpa only [Finset.card_univ, Fintype.card_fin] using hcount))

end HigherDimLQGMetric
