import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AffineLiftReg.GaussBound

/-!
# `PartIII-b:C/asrc/ra/5/4` task 1 : the Gaussian `exp(-|x|²/(κ a))` is in `GP54`

Source of record: `the November 2 reference manuscript` lines 4963-4981, 4978.
Smoothness on `s > 0` from `ContDiffOn` of `exp` and of the quotient with nonvanishing
denominator `κ a(s)`, `a(s) = 1 + ν s > 0`; the derivative bounds are `gauss_iterated_bound`
with `N = n`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gp54_exp (κ ν : ℝ) (hκ : 0 < κ) (hν : 0 < ν) (n : ℕ) : GP54 κ ν n (fun p : ℝ × (ℝ × ℝ) => Real.exp (-(sq2 p.2) / (κ * ageA ν p.1))) := by
  refine ⟨?_, ?_⟩
  · have hden : ∀ p ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)), κ * ageA ν p.1 ≠ 0 := by
      intro p hp
      have h0 : 0 < p.1 := hp.1
      have ha : 0 < ageA ν p.1 := by unfold ageA; nlinarith [mul_pos hν h0]
      exact mul_ne_zero hκ.ne' ha.ne'
    have h1 : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (fun p : ℝ × (ℝ × ℝ) => κ * ageA ν p.1)
        (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
      unfold ageA; fun_prop
    have h2 : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (fun p : ℝ × (ℝ × ℝ) => -(sq2 p.2))
        (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
      unfold sq2; fun_prop
    have h3 := h2.div h1 (fun p hp => hden p hp)
    exact Real.contDiff_exp.comp_contDiffOn h3
  · intro s0 s1 hs0 hs01
    obtain ⟨C, hC0, hb⟩ := gauss_iterated_bound κ ν s0 s1 hκ hν hs0 hs01 n
    exact ⟨C, n, hC0, hb⟩

end UnforcedLeray.Short.PartIIIb.Concrete
