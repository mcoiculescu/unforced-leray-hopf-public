import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_6_1_5
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VcSmooth
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VcJetSup.SpatialJetBound.VecJet
import UnforcedLeray.Lib.Train.VortexBounds

/-!
Task `PartII-b:G4/3/6/1/5/2`.  `VcSpatialJetBound` (SP 2205): spatial smoothness of `Vc ν c s` for
every `s ≥ 0` (`s > 0` from `vcSmooth_proof`, `s = 0` is the datum `datum_contDiff`), then
`Train.Vc_bounds j 0` for the coordinate words and `norm_jet_vec_le` / `cjw_norm_le_sum` for the
passage from words to the jet norm, with `width ≥ 1`.
-/

set_option autoImplicit false

open Set
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Train UnforcedLeray.Short.PartI

/-- `Vc ν c s` is `C^∞` in space for every age `s ≥ 0`. -/
theorem vc_contDiff_space {ν c s : ℝ} (hν : 0 < ν) (hc : 0 < c) (hs : 0 ≤ s) :
    ContDiff ℝ ∞ (Vc ν c s) := by
  rcases hs.eq_or_lt with h0 | h0
  · subst h0
    rw [Vc_zero]
    exact datum_contDiff hc.ne'
  · have h := vcSmooth_proof ν c hν hc
    have hf : ContDiffOn ℝ ∞ (fun z : UnforcedLeray.Cyl.Plane => (s, z)) univ :=
      (contDiff_const.prodMk contDiff_id).contDiffOn
    have := h.comp hf (fun z _ => ⟨h0, mem_univ z⟩)
    exact contDiffOn_univ.1 this

theorem vcSpatialJetBound_proof : UnforcedLeray.Short.IIb.VcSpatialJetBound := by
  intro j
  obtain ⟨C, b, hC, hb, hB⟩ := Vc_bounds j 0
  refine ⟨2 * (2 ^ j * C), by positivity, ?_⟩
  intro ν c s hν hc hs hw z
  have hw1 : 1 ≤ width ν s := by
    unfold width; nlinarith
  have hcomp : ∀ k : Fin 2,
      ‖iteratedFDeriv ℝ j (fun x => Vc ν c s x k) z‖ ≤ 2 ^ j * C := by
    intro k
    have hsm := contDiff_comp_proj (vc_contDiff_space hν hc hs) k
    refine (cjw_norm_le_sum _ hsm j z).trans ?_
    have hcard : (wordsOfLength j).card ≤ 2 ^ j := by
      unfold wordsOfLength
      refine Finset.card_image_le.trans ?_
      simp
    have hterm : ∀ w ∈ wordsOfLength j,
        |UnforcedLeray.B0151.derivWord w (fun x => Vc ν c s x k) z| ≤ C := by
      intro w hwm
      have hlen : w.length = j := by
        unfold wordsOfLength at hwm
        obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hwm
        simp
      have h1 := (hB ν c s hc hw1 hw).1 w hlen k z
      simp only [pow_zero, one_mul] at h1
      refine h1.trans ?_
      have : width ν s ^ (-(3 + (j : ℝ)) / 2) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hw1 (by
          have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
          have : -(3 + (j : ℝ)) / 2 ≤ 0 := by linarith
          exact this)
      nlinarith
    calc ∑ w ∈ wordsOfLength j, |UnforcedLeray.B0151.derivWord w (fun x => Vc ν c s x k) z|
        ≤ ∑ w ∈ wordsOfLength j, C := Finset.sum_le_sum hterm
      _ = (wordsOfLength j).card * C := by simp
      _ ≤ 2 ^ j * C := by
        refine mul_le_mul_of_nonneg_right ?_ hC
        exact_mod_cast hcard
  have := norm_jet_vec_le (Vc ν c s) (vc_contDiff_space hν hc hs) j z
  have h0 := hcomp 0
  have h1 := hcomp 1
  show ‖iteratedFDeriv ℝ j (Vc ν c s) z‖ ≤ _
  linarith

end UnforcedLeray.Short.IIb
