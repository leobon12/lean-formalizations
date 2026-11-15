/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RjTip

/-!
# Window certificates make a decoded past split-free (decision D33)

PROVE-GW2-ROOTX round 9, deterministic. The decoded past `pastOf cf R b N` has the windows `R` on `[b j, b (j+1)]`. A
**window certificate** at `j ≥ 1` is a global Loewner chain `(U, η)` equal to the stage-1 driver `R(b₁ + ·) − R(b₁)` up
to `b (j+1) − b₁`, whose trace is interior at `b (j+1) − b₁` (the test), and whose window chart at `b j − b₁` neither
hits `(junctionL j, junctionR j) \ {0}` nor returns to `0` on the window.

* **`splitFreePast_of_certs`**: certificates at every `1 ≤ j < N` make the past split-free;
* **`junction_signs_of_certs`**: with `N ≥ 2` and a last window of positive length, `junctionL N < 0 < junctionR N`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE.Theorem14.GW2Rj

open Restart Exist.StagedLaw MartChar.RealFlow GW2Rq GW2Wm

/-- **A window certificate** at `j`. -/
def WinCert (R : ℝ≥0 → ℝ) (b : ℕ → ℝ≥0) (cf : RecData) (j : ℕ) : Prop :=
  ∃ (U : ℝ → ℝ) (η : ℝ → ℂ), Continuous U ∧ U 0 = 0 ∧ IsLoewnerTrace U η ∧
    (∀ t : ℝ, 0 ≤ t → (b 1 : ℝ) + t ≤ b (j + 1) → U t = GW2Bh.rp R (b 1 + t) - GW2Bh.rp R (b 1)) ∧
    η ((b (j + 1) : ℝ) - b 1) ∈ H ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ (b (j + 1) : ℝ) - b j → ∀ z : ℝ, GW2Sdp.junctionL j (pastOf cf R b j) < z →
      z < GW2Sdp.junctionR j (pastOf cf R b j) → z ≠ 0 →
        loewnerTip (shiftDrive U ((b j : ℝ) - b 1)) t ≠ (z : ℂ)) ∧
    (∀ t : ℝ, 0 < t → t ≤ (b (j + 1) : ℝ) - b j → loewnerTip (shiftDrive U ((b j : ℝ) - b 1)) t ≠ 0)

variable {R : ℝ≥0 → ℝ} (hR : Continuous R) {b : ℕ → ℝ≥0} (hb : Monotone b) (cf : RecData)
include hR hb

/-- The window record's driver is the certificate's window driver. -/
theorem rdrv_window_eq {j : ℕ} (hj : 1 ≤ j) {U : ℝ → ℝ}
    (hU : ∀ t : ℝ, 0 ≤ t → (b 1 : ℝ) + t ≤ b (j + 1) → U t = GW2Bh.rp R (b 1 + t) - GW2Bh.rp R (b 1)) :
    ∀ v ∈ Icc (0 : ℝ) ((b (j + 1) - b j : ℝ≥0) : ℝ),
      rdrv (recOf (((b (j + 1) - b j : ℝ≥0)) : ℝ≥0∞) (fun u => GW2Rd.stgDrv R (b j) u, ⊤)) v =
        shiftDrive U ((b j : ℝ) - b 1) v := by
  intro v hv
  have hjj : b j ≤ b (j + 1) := hb (Nat.le_succ j)
  have h1j : (b 1 : ℝ) ≤ b j := NNReal.coe_le_coe.2 (hb hj)
  have hv2 : v ≤ (b (j + 1) : ℝ) - b j := by rw [← NNReal.coe_sub hjj]; exact hv.2
  rw [GW2Bh.rdrv_stage_eq hR (b j) (b (j + 1) - b j) hv]
  have e1 : (b 1 : ℝ) + ((b j : ℝ) - b 1 + v) = b j + v := by ring
  have e2 : (b 1 : ℝ) + ((b j : ℝ) - b 1) = b j := by ring
  show GW2Bh.rp R (b j + v) - GW2Bh.rp R (b j) = U ((b j : ℝ) - b 1 + v) - U ((b j : ℝ) - b 1)
  rw [hU _ (by linarith [hv.1]) (by linarith), hU _ (by linarith) (by linarith), e1, e2]
  ring

/-- **Certificates make the decoded past split-free**, with interior window tips. -/
theorem splitFreePast_of_certs {N : ℕ} (hcert : ∀ j, 1 ≤ j → j < N → WinCert R b cf j) :
    ∀ n, n ≤ N → SplitFreePast n (pastOf cf R b n) ∧
      ∀ j, 1 ≤ j → j < n → b j < b (j + 1) →
        0 < markPos (rdrv (recOf (((b (j + 1) - b j : ℝ≥0)) : ℝ≥0∞) (fun u => GW2Rd.stgDrv R (b j) u, ⊤)))
            (rtime (recOf (((b (j + 1) - b j : ℝ≥0)) : ℝ≥0∞) (fun u => GW2Rd.stgDrv R (b j) u, ⊤))) 0 ∧
          markPosL (rdrv (recOf (((b (j + 1) - b j : ℝ≥0)) : ℝ≥0∞) (fun u => GW2Rd.stgDrv R (b j) u, ⊤)))
            (rtime (recOf (((b (j + 1) - b j : ℝ≥0)) : ℝ≥0∞) (fun u => GW2Rd.stgDrv R (b j) u, ⊤))) 0 < 0
  | 0, _ => ⟨trivial, fun j _ hjn => absurd hjn (Nat.not_lt_zero j)⟩
  | n + 1, hn => by
    obtain ⟨ih, ihpos⟩ := splitFreePast_of_certs hcert n (Nat.le_of_succ_le hn)
    -- the window `n + 1` of the past
    have hwin : SplitFree (recOf (((b (n + 1) - b n : ℝ≥0)) : ℝ≥0∞) (fun u => GW2Rd.stgDrv R (b n) u, ⊤))
          (GW2Sdp.junctionL n (pastOf cf R b n)) (GW2Sdp.junctionR n (pastOf cf R b n)) ∧
        (1 ≤ n → b n < b (n + 1) →
          0 < markPos (rdrv (recOf (((b (n + 1) - b n : ℝ≥0)) : ℝ≥0∞) (fun u => GW2Rd.stgDrv R (b n) u, ⊤)))
              (rtime (recOf (((b (n + 1) - b n : ℝ≥0)) : ℝ≥0∞) (fun u => GW2Rd.stgDrv R (b n) u, ⊤))) 0 ∧
            markPosL (rdrv (recOf (((b (n + 1) - b n : ℝ≥0)) : ℝ≥0∞) (fun u => GW2Rd.stgDrv R (b n) u, ⊤)))
              (rtime (recOf (((b (n + 1) - b n : ℝ≥0)) : ℝ≥0∞) (fun u => GW2Rd.stgDrv R (b n) u, ⊤))) 0 < 0) := by
      rcases Nat.eq_zero_or_pos n with hn0 | hn1
      · subst hn0
        refine ⟨⟨Or.inr rfl, Or.inr rfl⟩, fun h => absurd h (by norm_num)⟩
      obtain ⟨U, η, hUc, hU0, hη, hU, hH, hav, hret⟩ := hcert n hn1 (Nat.lt_of_succ_le hn)
      have hnn : b n ≤ b (n + 1) := hb (Nat.le_succ n)
      have h1n : (b 1 : ℝ) ≤ b n := NNReal.coe_le_coe.2 (hb hn1)
      have ha : (0 : ℝ) ≤ (b n : ℝ) - b 1 := by linarith
      have hT : (((b (n + 1) - b n : ℝ≥0)) : ℝ) = (b (n + 1) : ℝ) - b n := NNReal.coe_sub hnn
      have hrt := GW2Bh.rtime_stage (fun u => GW2Rd.stgDrv R (b n) u) (b (n + 1) - b n)
      have hrd := rdrv_window_eq hR hb hn1 hU
      have hUn : ∀ t : ℝ, 0 ≤ t → (b 1 : ℝ) + t ≤ b n →
          U t = GW2Bh.rp R (b 1 + t) - GW2Bh.rp R (b 1) := fun t ht htn =>
        hU t ht (htn.trans (NNReal.coe_le_coe.2 hnn))
      have hjL := junctionL_le_baseL hR hb cf hUc hUn n hn1 le_rfl
      have hjR := baseR_le_junctionR hR hb cf hUc hUn n hn1 le_rfl
      have hH' : 0 < b (n + 1) - b n → η ((b n : ℝ) - b 1 + ((b (n + 1) - b n : ℝ≥0) : ℝ)) ∈ H := fun _ => by
        rw [hT]
        have e : (b n : ℝ) - b 1 + ((b (n + 1) : ℝ) - b n) = (b (n + 1) : ℝ) - b 1 := by ring
        rw [e]
        exact hH
      have hav' : ∀ t : ℝ, 0 ≤ t → t ≤ ((b (n + 1) - b n : ℝ≥0) : ℝ) → ∀ z : ℝ,
          GW2Sdp.junctionL n (pastOf cf R b n) < z → z < GW2Sdp.junctionR n (pastOf cf R b n) → z ≠ 0 →
            loewnerTip (shiftDrive U ((b n : ℝ) - b 1)) t ≠ (z : ℂ) := fun t ht htT =>
        hav t ht (htT.trans_eq hT)
      have hret' : ∀ t : ℝ, 0 < t → t ≤ ((b (n + 1) - b n : ℝ≥0) : ℝ) →
          loewnerTip (shiftDrive U ((b n : ℝ) - b 1)) t ≠ 0 := fun t ht htT => hret t ht (htT.trans_eq hT)
      obtain ⟨hsf, htip⟩ := splitFree_window hrt hUc hU0 hη ha hrd
        (junctionL_nonpos (R := R) (b := b) cf n) (junctionR_nonneg (R := R) (b := b) cf n) hjL hjR hav' hret' hH'
      refine ⟨hsf, fun _ hlt => ?_⟩
      have hT0 : 0 < b (n + 1) - b n := tsub_pos_of_lt hlt
      exact markPos_zero_pos_window hrt hT0 hUc hU0 hη ha hrd (htip hT0)
    refine ⟨⟨ih, hwin.1⟩, fun j hj hjn hlt => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hjn with hjn' | rfl
    · exact ihpos j hj hjn' hlt
    · exact hwin.2 hj hlt

/-- **The final junction signs.** -/
theorem junction_signs_of_certs {N : ℕ} (hN : 2 ≤ N) (hcert : ∀ j, 1 ≤ j → j < N → WinCert R b cf j)
    (hlast : b (N - 1) < b N) :
    GW2Sdp.junctionL N (pastOf cf R b N) < 0 ∧ 0 < GW2Sdp.junctionR N (pastOf cf R b N) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hM : 1 ≤ M := by omega
  simp only [Nat.add_sub_cancel] at hlast
  obtain ⟨-, hpos⟩ := splitFreePast_of_certs hR hb cf hcert (M + 1) le_rfl
  obtain ⟨hp, hn⟩ := hpos M hM (Nat.lt_succ_self M) hlast
  set r := recOf (((b (M + 1) - b M : ℝ≥0)) : ℝ≥0∞) (fun u => GW2Rd.stgDrv R (b M) u, ⊤) with hr
  have hrt : (0 : ℝ) ≤ rtime r := by rw [hr, GW2Bh.rtime_stage]; exact NNReal.coe_nonneg _
  have hjR := junctionR_nonneg (R := R) (b := b) cf M
  have hjL := junctionL_nonpos (R := R) (b := b) cf M
  change markPosL (rdrv r) (rtime r) (GW2Sdp.junctionL M (pastOf cf R b M)) < 0 ∧
    0 < markPos (rdrv r) (rtime r) (GW2Sdp.junctionR M (pastOf cf R b M))
  constructor
  · unfold markPosL at hn ⊢
    have h := Sec7.StripSideHeightProb.markPos_mono (w := fun s => -rdrv r s) (continuous_rdrv r).neg
      (by simp [rdrv_zero]) hrt (le_refl (0 : ℝ)) (neg_nonneg.2 hjL)
    rw [neg_zero] at hn
    linarith
  · exact hp.trans_le (Sec7.StripSideHeightProb.markPos_mono (continuous_rdrv r) (rdrv_zero r) hrt le_rfl hjR)

end InteractingSLE.Theorem14.GW2Rj
