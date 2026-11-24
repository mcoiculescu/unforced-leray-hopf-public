import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_4_org_4.Defs
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# `PartIII-b:C/asrc/ra/9/4/org/4/1/8` leaf: continuity in `x` of the lattice sums

Source `the November 2 reference manuscript`
line 4978: locally uniform Gaussian convergence. Each summand is continuous in `x`; on the open
slab `{|x.1| < R}` the summands are dominated by a fixed summable sequence (`pdc_genv_unif`),
so the sum is continuous there (`continuousOn_tsum`), hence at every point.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem psiASliceCont : PsiASliceCont := by
  intro hV hS ν s hν hs hνs M D
  obtain ⟨K3, hK3, B3⟩ := hV
  obtain ⟨K5, hK5, B5⟩ := hS
  have hνs' : ν * s ≤ 5 / 2 := by linarith
  have hcT : Continuous (fun y : ℝ × ℝ => psiT ν s M y) := by
    unfold psiT qM merApply sq2
    fun_prop
  have hcS : Continuous (fun y : ℝ × ℝ => psiTS ν s M D y) := by
    unfold psiTS qM merApply sq2
    fun_prop
  have hxj : ∀ j : ℤ, Continuous (fun x : ℝ × ℝ => xj ν j x) := fun j => by
    unfold xj
    exact (continuous_fst.sub continuous_const).prodMk continuous_snd
  constructor
  · rw [continuous_iff_continuousAt]
    intro x0
    obtain ⟨R, hR⟩ : ∃ R : ℝ, R = |x0.1| + 1 := ⟨_, rfl⟩
    have hU : IsOpen {x : ℝ × ℝ | |x.1| < R} :=
      isOpen_lt (continuous_abs.comp continuous_fst) continuous_const
    have hx0 : x0 ∈ {x : ℝ × ℝ | |x.1| < R} := by
      show |x0.1| < R
      rw [hR]
      linarith
    obtain ⟨u, hu, hub⟩ := pdc_genv_unif hν R
    have hbd : ∀ j : ℤ, ∀ x ∈ {x : ℝ × ℝ | |x.1| < R},
        ‖psiT ν s M (xj ν j x)‖ ≤ K3 * frob M * u j := by
      intro j x hx
      have hx' : |x.1| ≤ R := (show |x.1| < R from hx).le
      rw [Real.norm_eq_abs]
      have h1 := B3 ν s hν hs.le hνs' M (xj ν j x)
      have h2 := hub x hx' j
      have h3 : 0 ≤ K3 * frob M := mul_nonneg hK3 (pdc_frob_nonneg M)
      exact h1.trans (mul_le_mul_of_nonneg_left h2 h3)
    have hon : ContinuousOn (fun x : ℝ × ℝ => ∑' j : ℤ, psiT ν s M (xj ν j x))
        {x : ℝ × ℝ | |x.1| < R} :=
      continuousOn_tsum (fun j => (hcT.comp (hxj j)).continuousOn)
        (hu.mul_left (K3 * frob M)) hbd
    exact hon.continuousAt (hU.mem_nhds hx0)
  · rw [continuous_iff_continuousAt]
    intro x0
    obtain ⟨R, hR⟩ : ∃ R : ℝ, R = |x0.1| + 1 := ⟨_, rfl⟩
    have hU : IsOpen {x : ℝ × ℝ | |x.1| < R} :=
      isOpen_lt (continuous_abs.comp continuous_fst) continuous_const
    have hx0 : x0 ∈ {x : ℝ × ℝ | |x.1| < R} := by
      show |x0.1| < R
      rw [hR]
      linarith
    obtain ⟨u, hu, hub⟩ := pdc_genv_unif hν R
    have hC0 : 0 ≤ K5 * (frob M + frob (s • D)) / s :=
      div_nonneg (mul_nonneg hK5 (add_nonneg (pdc_frob_nonneg _) (pdc_frob_nonneg _))) hs.le
    have hbd : ∀ j : ℤ, ∀ x ∈ {x : ℝ × ℝ | |x.1| < R},
        ‖psiTS ν s M D (xj ν j x)‖ ≤ K5 * (frob M + frob (s • D)) / s * u j := by
      intro j x hx
      have hx' : |x.1| ≤ R := (show |x.1| < R from hx).le
      rw [Real.norm_eq_abs]
      have h1 := B5 ν s hν hs.le hνs' M D (xj ν j x)
      have h2 := hub x hx' j
      have h3 : |psiTS ν s M D (xj ν j x)|
          ≤ K5 * (frob M + frob (s • D)) / s * genvT (xj ν j x) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hs]
        linarith
      exact h3.trans (mul_le_mul_of_nonneg_left h2 hC0)
    have hon : ContinuousOn (fun x : ℝ × ℝ => ∑' j : ℤ, psiTS ν s M D (xj ν j x))
        {x : ℝ × ℝ | |x.1| < R} :=
      continuousOn_tsum (fun j => (hcS.comp (hxj j)).continuousOn)
        (hu.mul_left (K5 * (frob M + frob (s • D)) / s)) hbd
    exact hon.continuousAt (hU.mem_nhds hx0)

end UnforcedLeray.Short.PartIIIb.Concrete
