import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_4.Defs

/-!
# `PartIII-b:C/asrc/ra/9/4/org/1` : vanishing of `gradRem` for `s > 1.1/ν`

Source of record: `the November 2 reference manuscript`, lines 4978, 5039-5043.
For `s > 1.1/ν` one has `ν s > 1.1`, so `PsiA = 0` on an open neighbourhood of `(s, x)` in the
chart, hence `sΨ_A` is eventually zero there, its `dS` and `dEta` vanish, and `gradRem = 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gradRemVanish (as : ℝ) (χf : ℝ → ℝ) : GradRemVanish as χf := by
  intro hχ p μ A hA s hs x
  have hν : 0 < p.ν := p.ν_pos
  have hopen : IsOpen {z : Chart | (11 / 10 : ℝ) / p.ν < z.1} :=
    isOpen_lt continuous_const continuous_fst
  have hmem : ((s, x) : Chart) ∈ {z : Chart | (11 / 10 : ℝ) / p.ν < z.1} := hs
  have hEv : sPsiChart p χf A =ᶠ[𝓝 ((s, x) : Chart)] fun _ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds hmem] with z hz
    have h1 : (11 / 10 : ℝ) ≤ p.ν * z.1 := by
      have := (div_lt_iff₀ hν).1 hz
      linarith [mul_comm p.ν z.1]
    simp [sPsiChart, PsiA_eq_zero hχ A h1 z.2]
  have hfd : fderiv ℝ (sPsiChart p χf A) ((s, x) : Chart) = 0 := by
    rw [hEv.fderiv_eq]
    exact fderiv_const_apply (0 : ℝ)
  have hS : UnforcedLeray.Axi.dS (sPsiChart p χf A) ((s, x) : Chart) = 0 := by
    unfold UnforcedLeray.Axi.dS
    rw [hfd]; simp
  have hE : UnforcedLeray.Axi.dEta (sPsiChart p χf A) ((s, x) : Chart) = 0 := by
    unfold UnforcedLeray.Axi.dEta
    rw [hfd]; simp
  simp only [gradRem, hS, hE]
  ext i
  fin_cases i <;> simp

end UnforcedLeray.Short.PartIIIb.Concrete
