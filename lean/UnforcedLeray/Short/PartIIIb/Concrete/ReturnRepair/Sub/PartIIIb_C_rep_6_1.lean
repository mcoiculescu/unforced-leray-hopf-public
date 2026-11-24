import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_6_1.NewtonW
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_9
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.StreamCut
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_6

/-!
# `JetEps1W`: the `ε = 1` jet bound with the cut moment (`PartIII-b:C/rep/6/1`)

Source: `the November 2 reference manuscript` lines 4917-4937, 5400-5413.

Copy of `jetEps1_of` (`SourceL/Sub/PartIII-b_C_srcL_9.lean`) with `oldN0` replaced by `oldN0w`,
using the cut Newton bound `NewtonVRegionBoundW` (`Sub/PartIII-b_C_rep_6_1/NewtonW.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem jetEps1W_of {K : Set ℝ} {χo χy : ℝ → ℝ} (hV : NewtonVRegionBoundW χo)
    (hS : StreamCutJet χy) : JetEps1W K χo χy := by
  obtain ⟨C, hC⟩ := hV
  obtain ⟨C0, hC0⟩ := hS
  refine ⟨C0 * ∑ m ∈ Finset.range 8, (|C m| + |C m|), ?_⟩
  intro c ν μ h _ M hM s hs j hj
  have hN0 := rj6_oldN0w_nonneg c ν h.nu_pos h.chiO M
  have hmu0 : 0 ≤ μ := h.mu_pos.le
  have hmu1 : 0 ≤ μ + 1 := by linarith
  obtain ⟨h1, h1b⟩ := hC c ν μ h.c_pos h.nu_pos h.chiO hmu0 M hM
  obtain ⟨h2, h2b⟩ := hC c ν (μ + 1) h.c_pos h.nu_pos h.chiO hmu1 M hM
  have hY : ∀ μ' : ℝ, youngW c ν 1 μ' χo M = newtonV c ν μ' χo M := by
    intro μ'; funext y; simp [youngW]
  set S : ℝ := ∑ m ∈ Finset.range 8, (|C m| + |C m|) with hSdef
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun m _ => by positivity
  set Z : Vec3 → Vec3 := newtonV c ν μ χo M - newtonV c ν (μ + 1) χo M with hZ
  have hopen : IsOpen {w : Vec3 | ν * (11 / 12) < eucSq w} := by
    unfold eucSq
    exact isOpen_lt continuous_const (by fun_prop)
  have hZs : ContDiffOn ℝ 7 Z {w | ν * (11 / 12) < eucSq w} := h1.sub h2
  have hZb : ∀ m : ℕ, m ≤ 7 → ∀ w : Vec3, ν * (11 / 12) < eucSq w →
      ‖iteratedFDeriv ℝ m Z w‖ ≤ (S * oldN0w c ν χo M) * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) := by
    intro m hm w hw
    have hat1 : ContDiffAt ℝ 7 (newtonV c ν μ χo M) w := h1.contDiffAt (hopen.mem_nhds hw)
    have hat2 : ContDiffAt ℝ 7 (newtonV c ν (μ + 1) χo M) w := h2.contDiffAt (hopen.mem_nhds hw)
    have hmle : (m : WithTop ℕ∞) ≤ 7 := by exact_mod_cast hm
    rw [hZ, iteratedFDeriv_sub_apply (hat1.of_le hmle) (hat2.of_le hmle)]
    have hp : 0 ≤ (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
    have hb1 := h1b m hm w hw
    have hb2 := h2b m hm w hw
    have hSm : |C m| + |C m| ≤ S :=
      Finset.single_le_sum (f := fun m => |C m| + |C m|) (fun m _ => by positivity)
        (Finset.mem_range.2 (by omega))
    have hCm : C m + C m ≤ S := le_trans (add_le_add (le_abs_self _) (le_abs_self _)) hSm
    calc ‖iteratedFDeriv ℝ m (newtonV c ν μ χo M) w - iteratedFDeriv ℝ m (newtonV c ν (μ + 1) χo M) w‖
        ≤ ‖iteratedFDeriv ℝ m (newtonV c ν μ χo M) w‖ + ‖iteratedFDeriv ℝ m (newtonV c ν (μ + 1) χo M) w‖ :=
          norm_sub_le _ _
      _ ≤ C m * oldN0w c ν χo M * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) +
          C m * oldN0w c ν χo M * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) := add_le_add hb1 hb2
      _ = (C m + C m) * (oldN0w c ν χo M * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m)) := by ring
      _ ≤ S * (oldN0w c ν χo M * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m)) :=
          mul_le_mul_of_nonneg_right hCm (mul_nonneg hN0 hp)
      _ = (S * oldN0w c ν χo M) * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) := by ring
  have hL : Lpt c ν 1 μ χo χy M = fun s : ℝ => if 0 < s then
        (fun i j => fderiv ℝ (streamCut ν 1 χy Z) ![(1 : ℝ)⁻¹ / Real.sqrt s, 0, 0] (Pi.single j 1) i)
        else (0 : Mat3) := by
    funext s'
    simp only [Lpt, Xmt, hY, hZ]
  rw [hL]
  have := hC0 ν (S * oldN0w c ν χo M) h.nu_pos (mul_nonneg hSnn hN0) Z hZs hZb h.chiY s hs j hj
  calc _ ≤ C0 * (S * oldN0w c ν χo M) * s ^ (5 / 2 : ℝ) := this
    _ = C0 * S * s ^ (5 / 2 : ℝ) * oldN0w c ν χo M := by ring

/-- **`jetEps1W`** (`PartIII-b:C/rep/6/1`): the `ε = 1` jet bound with the cut moment, for all
`K, χ_o, χ_y`. -/
theorem jetEps1W : ∀ (K : Set ℝ) (χo χy : ℝ → ℝ), UnforcedLeray.Short.PartIIIb.Concrete.JetEps1W K χo χy :=
  fun K χo χy => jetEps1W_of (newtonVRegionBoundW χo) (streamCutJet χy)

end UnforcedLeray.Short.PartIIIb.Concrete
