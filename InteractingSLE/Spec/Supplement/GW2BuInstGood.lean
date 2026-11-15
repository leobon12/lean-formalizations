/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BuJunc

/-!
# Every version of a candidate is eventually good (almost surely on alive histories)

Packet PROVE-GW2-BUF (round 18; the instance layer). Take a candidate's root-`x` versions and the owners' inputs:
* the stage law in version form (`StageLawXStatement`);
* the death threshold (`DeathThrXStatement`);
* decision D27's exhaustion below the death (RELDET's `schedVerXDeath_exhausts_death` form).

The candidate's word map is GEOM2's base word raised by `θa`. Then, almost surely on an alive history: for every near
family decoded at a version's record, presenting the stage word at some index, with its outermost labels controlled,
eventually every version's cell exit plus its stage start is below its cap.

Proof at one sample: the common stage data (`ae_inst_common`); the canonical driver; the clock below the life
(`clock_lt_life`) and the exhaustion below `min (L, d)` (`exhausts_below_min`). When the contact comes first, the
root-`x` contact clause holds (`ae_gapVanishes_contactX_versions_at`) at GEOM2's root bounds, which are its junctions
(`root_bounds_eq_junctions`). Otherwise the death threshold holds. Then `exit_add_lt_life_of_flow` and
`eventually_good` apply.

* **`ae_eventually_good_instX`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Exist Staged StagedLaw Restart Supp8 Supp8.GB6 GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootN4 GW2Rz
  GW2Rd GW2Rv GW2Wm GW2Schedule Sec5.Prop513Schedule GW2JDetR11 GW2Sdh GW2Sde

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **Every version of a candidate is eventually good**, almost surely on alive histories. -/
theorem ae_eventually_good_instX (h13 : Exist.Theorem13Statement.{u}) (gap : RootCv.GapFamily.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hg : GoodRoot c r)
    (hord : GW2Sdx.HistOrdered c r l) (ver : SchedVerXFamily.{u}) (ch : SchedChoiceFamily.{u})
    (hlaw : StageLawXStatement h13 ver) (hdeath : DeathThrXStatement h13 ver ch)
    (hD27 : ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → RootJ31.oldSuccess c r l ω →
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω →
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) < deathClockX c r l a ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) <
          (ver Ω c r l a).V n ω)
    (c' : BoundaryWord) (θa : ℝ)
    (hβ : ∀ y, (ch Ω c r l a).β y = upW (θa * chiC c.κ) (baseWordX c.κ c' (rootPt r.1) c.s
      (RootJ31.historyProgram c r l) ((entryList l).length + 1) (GW2Ru.length_historyProgram c r l) y))
    (n : ℕ) (shape : RecData → NearShape) (posL posR : RecData → ℕ → ℝ) {scale c₂ : ℝ≥0} (hc₂ : 0 < c₂)
    (hsc : Real.sqrt scale = (c₂ : ℝ)⁻¹) (flip : Bool) :
    ∀ᵐ ξ ∂c.P, ξ ∈ ((GW2Sdz.J32S gap Ω c).experiment r).data.alive ((GW2Sdz.J32S gap Ω c).G r) l →
      ∀ (f : NearCrossingFamily.{u} c.κ) (m j₀ : ℕ),
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ξ) <
        (ver Ω c r l a).V j₀ ξ →
      famShapeB f = shape ((instX h13 ver ch Ω c r l a j₀ hg.1).srecX c r l (rootPt r.1) ξ) →
      (∀ i : Fin f.nL, f.xL i = posL ((instX h13 ver ch Ω c r l a j₀ hg.1).srecX c r l (rootPt r.1) ξ) i) →
      (∀ j : Fin f.nR, f.xR j = posR ((instX h13 ver ch Ω c r l a j₀ hg.1).srecX c r l (rootPt r.1) ξ) j) →
      GW2Sdf.PresentsO c.κ (upW (θa * chiC c.κ) (baseWordX c.κ c' (rootPt r.1) c.s (RootJ31.historyProgram c r l)
          ((entryList l).length + 1) (GW2Ru.length_historyProgram c r l)
          ((instX h13 ver ch Ω c r l a j₀ hg.1).srecX c r l (rootPt r.1) ξ))) scale flip f.xL (f.ρLs m) f.xR
          (f.ρRs m) →
      f.mL ≤ f.nL - 1 → f.mR ≤ f.nR - 1 →
      ∀ᶠ j in atTop, cellStop (cellOf n shape posL posR) posL posR (c₂ ^ 2) (GW2Sdy.nearSign flip * c₂)
          (((n : ℝ≥0) + 1) / c₂ ^ 2) ((instX h13 ver ch Ω c r l a j hg.1).srecX c r l (rootPt r.1) ξ,
            fun t => (instX h13 ver ch Ω c r l a j hg.1).drvX c (rootPt r.1) t ξ) +
          (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) ((ver Ω c r l a).V j)
            (RootJ31.historyTime c r l) ξ : ℝ≥0∞) < (ver Ω c r l a).V j ξ := by
  obtain ⟨hx, hs⟩ := hg
  filter_upwards [ae_inst_common h13 gap c r l a ⟨hx, hs⟩ ver c.κ c', hlaw Ω c r l a ⟨hx, hs⟩ hord,
    hdeath Ω c r l a ⟨hx, hs⟩ hord, hD27,
    ae_gapVanishes_contactX_versions_at h13 c r l a hx hs (fun k => ((ver Ω c r l a).isA hx k).1.1)]
    with ξ hcomm hlawξ hdeathξ hD27ξ hconξ halive f m j₀ hj₀ hsh hL hR hP hmL hmR
  obtain ⟨hξ, hold, -, hcf, hTc, hS, hrecs, hbase⟩ := hcomm halive
  obtain ⟨⟨hwc, hw0, hγ⟩, ⟨hα, hW, hW0, hζ⟩, harc, -, -⟩ := (schedGTX_spec h13 c r l a).1 ξ hξ
  obtain ⟨Wc, hcanon⟩ := hlawξ hξ hold
  obtain ⟨hWc, hWc0, hagree, ⟨ζc, ηc, hη, hLζ⟩, M, hM⟩ := hcanon
  -- the clock
  obtain ⟨ha0, hsm, hac⟩ := GW2Rz.clock_props c.W c.ζ ξ hα hW hW0 hζ hs hx harc hwc hw0 hγ
  have hTc0 := GW2Rz.contact_pos (W := c.W) (ω := ξ) hα hx harc hγ
  set L := contactLifeX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ) (schedW c r l a · ξ) (schedTr c r l a ξ) (c.α ξ)
    with hLdef
  set clT := clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ξ with hclT
  have hclT0 : 0 ≤ clT := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ RootJ31.historyTime c r l) with h | h
    · rw [hclT, ← h]; exact ha0.ge
    · have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ :=
        lt_of_le_of_lt (by exact_mod_cast zero_le) hTc
      exact le_of_lt (lt_of_eq_of_lt ha0.symm (hsm h0 hTc h))
  have hSL : clT < L := clock_lt_life hsm hM hTc
  have hL0 : 0 < L := lt_of_le_of_lt hclT0 hSL
  set d := deathClockX c r l a ξ with hddef
  have hexmin : ∀ q : ℝ≥0∞, q < min (ENNReal.ofReal L) d → ∀ᶠ k in atTop, q < (ver Ω c r l a).V k ξ :=
    exhausts_below_min ha0 hTc0 hac hM fun t ht htd => hD27ξ hcf hold t ht htd
  -- the root bounds and the junctions
  obtain ⟨hxR_eq, hxL_eq, hxR_pos, hxL_neg⟩ :=
    root_bounds_eq_junctions c.W c.ζ ξ hα hW hW0 hζ hx harc hwc hw0 hγ hcf.1
  set xR := labelL (rdrv (cfRec c.s c.W c.ζ ξ)) (rtime (cfRec c.s c.W c.ζ ξ)) 0 -
    GW2Rz.baseRead (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ) with hxRdef
  set xL := labelR (rdrv (cfRec c.s c.W c.ζ ξ)) (rtime (cfRec c.s c.W c.ζ ξ)) 0 -
    GW2Rz.baseRead (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ) with hxLdef
  have hjR₀ : ∀ z ∈ (rootWordX c.κ c' (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ)).jumps, 0 < z → z ≤ xR :=
    fun z hz _ => (rootWordX_label_bounds hcf.1.2.2.1 hcf.1.2.2.2 hz).2
  have hjL₀ : ∀ z ∈ (rootWordX c.κ c' (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ)).jumps, z < 0 → xL ≤ z :=
    fun z hz _ => (rootWordX_label_bounds hcf.1.2.2.1 hcf.1.2.2.2 hz).1
  -- the contact clause, when the contact comes first
  have hcon : ENNReal.ofReal L ≤ d →
      GapVanishes (rp Wc) xR L ∨ GapVanishes (fun q => -rp Wc q) (-xL) L := by
    intro hLd
    have hexfull : ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
        ∃ k, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) < (ver Ω c r l a).V k ξ :=
      fun t ht => (hD27ξ hcf hold t ht (((ENNReal.ofReal_lt_ofReal_iff hL0).2
        (clock_lt_life hsm hM ht)).trans_le hLd)).exists
    rcases hconξ hξ hexfull Wc ζc ηc hWc hWc0 hη hagree ⟨M, hM⟩ hLζ with ⟨-, hjR, hgap⟩ | ⟨-, hjL, hgap⟩
    · exact Or.inl (hgap xR (by rw [hxR_eq]; exact hjR))
    · exact Or.inr (hgap xL (by rw [hxL_eq]; exact hjL))
  -- the stage data at `j₀`
  set S₀ := stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) ((ver Ω c r l a).V j₀)
    (RootJ31.historyTime c r l) ξ with hS₀def
  have hS₀ : S₀ = clT.toNNReal := hS j₀ hj₀
  have hS₀V : (S₀ : ℝ≥0∞) < (ver Ω c r l a).V j₀ ξ := by
    rw [hS₀]
    exact hj₀
  set N := (entryList l).length + 1 with hNdef
  set b := trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) ((ver Ω c r l a).V j₀)
    (RootJ31.historyProgram c r l) N (RootJ31.historyTime c r l) ξ with hbdef
  have hbN : b N = S₀ := trueBdX_of_le _ _ le_rfl (Nat.succ_ne_zero _)
  have hTj : ∀ k < N, schedTime 0 (RootJ31.historyProgram c r l) k ≤ RootJ31.historyTime c r l := fun k hk =>
    GW2Ru.schedTime_le_historyTime c r l hord (by rw [GW2Ru.length_historyProgram]; exact hk.le)
  have hbmono : Monotone b := monotone_trueBdX (schedGTX_spec h13 c r l a).1 hs hx ((ver Ω c r l a).fin j₀ ξ)
    hord (GW2Ru.length_historyProgram c r l) hTj
  have hb0 : b 0 = 0 := trueBdX_zero _ _ _
  have hb' : baseWordX c.κ c' (rootPt r.1) c.s (RootJ31.historyProgram c r l) N (GW2Ru.length_historyProgram c r l)
      ((instX h13 ver ch Ω c r l a j₀ hx).srecX c r l (rootPt r.1) ξ) =
      GW2JDetR5.stageWord (κ := c.κ) (rootWordX c.κ c' (rootPt r.1) c.s) (progAngle (RootJ31.historyProgram c r l)) N
        (pastOf (cfRec c.s c.W c.ζ ξ) (fun u => (ver Ω c r l a).R j₀ u ξ) b N) := hbase j₀
  rw [hb'] at hP
  have hbN' : ((b N : ℝ≥0) : ℝ) = clT := by rw [hbN, hS₀, Real.coe_toNNReal _ hclT0]
  -- the death
  have hdeath' : d < ENNReal.ofReal L → ∃ u : ℝ≥0, ((b N : ℝ≥0) : ℝ≥0∞) + u = d ∧
      StageThreshold c.κ (upW (θa * chiC c.κ) (GW2JDetR5.stageWord (κ := c.κ) (rootWordX c.κ c' (rootPt r.1) c.s)
        (progAngle (RootJ31.historyProgram c r l)) N
        (pastOf (cfRec c.s c.W c.ζ ξ) (fun u => (ver Ω c r l a).R j₀ u ξ) b N))) (stgDrv Wc (b N)) u := by
    intro hdL
    obtain ⟨u, hu, hthr⟩ := hdeathξ hξ hold Wc ⟨hWc, hWc0, hagree, ⟨ζc, ηc, hη, hLζ⟩, M, hM⟩ hdL j₀ hS₀V
    refine ⟨u, by rw [hbN]; exact hu, ?_⟩
    rw [hβ, hb'] at hthr
    rw [hbN]
    exact hthr
  have hag : ∀ q : ℝ≥0, q ≤ b N → (ver Ω c r l a).R j₀ q ξ = Wc q := fun q hq =>
    hagree j₀ q (lt_of_le_of_lt (by rw [hbN] at hq; exact_mod_cast hq) hS₀V)
  -- the initial state is in the cell
  obtain ⟨-, hin0⟩ := cellOf_spec f n hsh hL hR
  have hlabL : ∀ i, f.xL i ≤ 0 := fun i => by
    by_cases h : f.xL i = 0
    · exact h.le
    · exact (f.hxL i h).trans (neg_nonpos.2 f.hη.le)
  have hlabR : ∀ j, 0 ≤ f.xR j := fun j => by
    by_cases h : f.xR j = 0
    · exact h.ge
    · exact f.hη.le.trans (f.hxR j h)
  have h0 : GW2Sdg.imgState f.xL f.xR (scaledPath (c₂ ^ 2) (GW2Sdy.nearSign flip * c₂) (stgDrv Wc (b N))) 0 ∈
      cellBuf (famShapeB f, (cellOf n shape posL posR
        ((instX h13 ver ch Ω c r l a j₀ hx).srecX c r l (rootPt r.1) ξ)).2.1,
        (cellOf n shape posL posR ((instX h13 ver ch Ω c r l a j₀ hx).srecX c r l (rootPt r.1) ξ)).2.2) := by
    rw [imgState_zero f.xL f.xR hlabL hlabR (by simp [scaledPath, stgDrv_zero])]
    exact hin0
  have hcap : (0 : ℝ≥0) < ((n : ℝ≥0) + 1) / c₂ ^ 2 := div_pos (by positivity) (pow_pos hc₂ 2)
  have hfl := exit_add_lt_life_of_flow f (cellOf n shape posL posR) posL posR hsh hL hR hc₂ hsc flip m
    (rootWordX c.κ c' (rootPt r.1) c.s) (progAngle (RootJ31.historyProgram c r l)) (cfRec c.s c.W c.ζ ξ)
    (((ver Ω c r l a).isA hx j₀).1.1.2.1 ξ) (((ver Ω c r l a).isA hx j₀).1.1.2.2.1 ξ) hbmono hb0 N hP hmL hmR
    hcap hWc hag h0 (by rw [hxR_eq]; exact hxR_pos.le) (by rw [hxL_eq]; exact hxL_neg.le) hjR₀ hjL₀
    (by rw [hbN']; exact hSL) hcon hdeath'
  -- eventually good
  have hEpath : Supp8.GB6.HullId.IsPathRule (cellStop (cellOf n shape posL posR) posL posR (c₂ ^ 2)
      (GW2Sdy.nearSign flip * c₂) (((n : ℝ≥0) + 1) / c₂ ^ 2)) := isPathRule_cellStop _ posL posR (pow_pos hc₂ 2) _ _
  have hbNe : ((b N : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal clT := by rw [hbN, hS₀]; rfl
  refine eventually_good hEpath (Wc := Wc) (S := b N) (R := fun k u => (ver Ω c r l a).R k u ξ)
    (V := fun k => (ver Ω c r l a).V k ξ)
    (recs := fun k => (instX h13 ver ch Ω c r l a k hx).srecX c r l (rootPt r.1) ξ)
    (starts := fun k => stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
      ((ver Ω c r l a).V k) (RootJ31.historyTime c r l) ξ) (fun k q hq => hagree k q hq) (fun k hk => ?_)
    (fun k hk => ?_) hfl hexmin
  · rw [hbNe] at hk
    change augRec (stageEncRec c r l) _ ξ = augRec (stageEncRec c r l) _ ξ
    simp only [augRec]
    exact congrArg (fun p => pairEnc (stageEncRec c r l ξ, p)) (hrecs k j₀ hk hj₀)
  · rw [hbNe] at hk
    rw [hS k hk, hbN, hS₀]

end InteractingSLE.Theorem14.GW2Bh
