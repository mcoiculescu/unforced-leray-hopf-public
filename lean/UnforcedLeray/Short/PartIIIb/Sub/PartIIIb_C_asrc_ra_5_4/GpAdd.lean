import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# `gp54_add`: `GP54` is closed under addition

Source of record: `the November 2 reference manuscript` lines 4963-4981, 4978.
Both summands are `C^n` on the open set `Ioi 0 ×ˢ univ`, so the iterated derivative of the sum is
the sum of the iterated derivatives; the Gaussian-type bounds add with constant `Cf + Cg`, the
polynomial exponent `Nf + Ng` (which dominates both) and the common exponential factor.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gp54_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (κ ν : ℝ) (n : ℕ)
    (f g : ℝ × (ℝ × ℝ) → E) (hf : GP54 κ ν n f) (hg : GP54 κ ν n g) :
    GP54 κ ν n (fun p => f p + g p) := by
  obtain ⟨hfC, hfB⟩ := hf
  obtain ⟨hgC, hgB⟩ := hg
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  refine ⟨hfC.add hgC, ?_⟩
  intro s0 s1 hs0 hs01
  obtain ⟨Cf, Nf, hCf, hfb⟩ := hfB s0 s1 hs0 hs01
  obtain ⟨Cg, Ng, hCg, hgb⟩ := hgB s0 s1 hs0 hs01
  refine ⟨Cf + Cg, Nf + Ng, add_nonneg hCf hCg, ?_⟩
  intro m hm s hs x
  have hsU : (0 : ℝ) < s := lt_of_lt_of_le hs0 hs.1
  have hx : (s, x) ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := ⟨hsU, mem_univ x⟩
  have hmN : (m : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) := by exact_mod_cast hm
  have hfa : ContDiffAt ℝ (m : WithTop ℕ∞) f (s, x) :=
    (hfC.contDiffAt (hU.mem_nhds hx)).of_le hmN
  have hga : ContDiffAt ℝ (m : WithTop ℕ∞) g (s, x) :=
    (hgC.contDiffAt (hU.mem_nhds hx)).of_le hmN
  have hsum : iteratedFDeriv ℝ m (fun p => f p + g p) (s, x)
      = iteratedFDeriv ℝ m f (s, x) + iteratedFDeriv ℝ m g (s, x) :=
    iteratedFDeriv_add_apply hfa hga
  have hsq : (0 : ℝ) ≤ sq2 x := by
    unfold sq2; positivity
  have hq1 : (1 : ℝ) ≤ 1 + sq2 x := by linarith
  have hE : (0 : ℝ) ≤ Real.exp (-(sq2 x) / (κ * ageA ν s1)) := (Real.exp_pos _).le
  have hP1 : (1 + sq2 x) ^ Nf ≤ (1 + sq2 x) ^ (Nf + Ng) :=
    pow_le_pow_right₀ hq1 (Nat.le_add_right Nf Ng)
  have hP2 : (1 + sq2 x) ^ Ng ≤ (1 + sq2 x) ^ (Nf + Ng) :=
    pow_le_pow_right₀ hq1 (Nat.le_add_left Ng Nf)
  have hbf := hfb m hm s hs x
  have hbg := hgb m hm s hs x
  rw [hsum]
  calc ‖iteratedFDeriv ℝ m f (s, x) + iteratedFDeriv ℝ m g (s, x)‖
      ≤ ‖iteratedFDeriv ℝ m f (s, x)‖ + ‖iteratedFDeriv ℝ m g (s, x)‖ := norm_add_le _ _
    _ ≤ Cf * (1 + sq2 x) ^ Nf * Real.exp (-(sq2 x) / (κ * ageA ν s1))
          + Cg * (1 + sq2 x) ^ Ng * Real.exp (-(sq2 x) / (κ * ageA ν s1)) :=
        add_le_add hbf hbg
    _ ≤ Cf * (1 + sq2 x) ^ (Nf + Ng) * Real.exp (-(sq2 x) / (κ * ageA ν s1))
          + Cg * (1 + sq2 x) ^ (Nf + Ng) * Real.exp (-(sq2 x) / (κ * ageA ν s1)) :=
        add_le_add
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP1 hCf) hE)
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP2 hCg) hE)
    _ = (Cf + Cg) * (1 + sq2 x) ^ (Nf + Ng) * Real.exp (-(sq2 x) / (κ * ageA ν s1)) := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
