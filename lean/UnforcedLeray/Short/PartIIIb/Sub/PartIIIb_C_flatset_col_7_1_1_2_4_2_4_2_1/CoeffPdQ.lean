import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.FlatLerayDefs

/-!
# `CoeffPdQ` (organize task `PartIII-b:C/flatset/col/7/1/1/2/4/2/4/2/1/1/5`)

Source of record `the November 2 reference manuscript`
lines 1713-1716 (`q`-frequencies): one integration by parts in `q` over `[0, c]`,
`(∂_q g)^(n) = i k_n g^(n)`, where the boundary terms cancel by periodicity.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.Short.PartIIa

/-- Integration by parts for a complex exponential weight `e^{κ q}` with `e^{κ c} = 1`
and a `c`-periodic-type endpoint identity `v c = v 0`. -/
private theorem cpq_ibp_exp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (c : ℝ)
    (κ : ℂ) (hκ : Complex.exp (κ * (c : ℂ)) = 1) (v v' : ℝ → E)
    (hv : ∀ q : ℝ, HasDerivAt v (v' q) q) (hv'c : Continuous v') (hvper : v c = v 0) :
    ∫ q in (0 : ℝ)..c, Complex.exp (κ * (q : ℂ)) • v' q
      = -(κ • ∫ q in (0 : ℝ)..c, Complex.exp (κ * (q : ℂ)) • v q) := by
  have hu : ∀ q : ℝ, HasDerivAt (fun q : ℝ => Complex.exp (κ * (q : ℂ)))
      (κ * Complex.exp (κ * (q : ℂ))) q := by
    intro q
    have h := (((hasDerivAt_id' (x := q)).ofReal_comp).const_mul κ).cexp
    exact h.congr_deriv (by push_cast; ring)
  have hvc : Continuous v := continuous_iff_continuousAt.2 fun q => (hv q).continuousAt
  have hu'c : Continuous (fun q : ℝ => κ * Complex.exp (κ * (q : ℂ))) :=
    continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  have hIBP := intervalIntegral.integral_smul_deriv_eq_deriv_smul (a := 0) (b := c)
    (u := fun q : ℝ => Complex.exp (κ * (q : ℂ)))
    (u' := fun q : ℝ => κ * Complex.exp (κ * (q : ℂ))) (v := v) (v' := v')
    (fun q _ => hu q) (fun q _ => hv q)
    (hu'c.intervalIntegrable _ _) (hv'c.intervalIntegrable _ _)
  have hb : Complex.exp (κ * ((c : ℝ) : ℂ)) • v c - Complex.exp (κ * ((0 : ℝ) : ℂ)) • v 0 = 0 := by
    rw [hκ, hvper]
    simp
  rw [hIBP, hb, zero_sub]
  congr 1
  rw [← intervalIntegral.integral_smul]
  congr 1
  funext q
  exact mul_smul κ _ _

theorem coeffPdQ : CoeffPdQ := by
  intro c hc g hg n x
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℂ, κ = -(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / (c : ℂ)) :=
    ⟨_, rfl⟩
  have hE : ∀ q : ℝ, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ)))
      = Complex.exp (κ * (q : ℂ)) := by
    intro q
    congr 1
    rw [hκdef]
    ring
  have hκc : Complex.exp (κ * (c : ℂ)) = 1 := by
    have h : κ * (c : ℂ) = ((-n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [hκdef, neg_mul, div_mul_cancel₀ _ hc']
      push_cast
      ring
    rw [h, Complex.exp_int_mul_two_pi_mul_I]
  -- `g` is differentiable, and its `q`-slice has derivative `∂_q g`
  have hgd : Differentiable ℝ g := hg.smooth.differentiable (by simp)
  have hv : ∀ q : ℝ, HasDerivAt (fun q : ℝ => g (x.1, q, x.2)) (pdQ g (x.1, q, x.2)) q := by
    intro q
    have hφ : HasDerivAt (fun q : ℝ => ((x.1, q, x.2) : Profile)) ((0 : ℝ), (1 : ℝ), (0 : ℝ)) q :=
      (hasDerivAt_const q x.1).prodMk ((hasDerivAt_id' (x := q)).prodMk (hasDerivAt_const q x.2))
    exact (hgd (x.1, q, x.2)).hasFDerivAt.comp_hasDerivAt q hφ
  have hv'c : Continuous (fun q : ℝ => pdQ g (x.1, q, x.2)) := by
    have h1 : Continuous (fderiv ℝ g) := hg.smooth.continuous_fderiv (by simp)
    have h2 : Continuous (fun q : ℝ => ((x.1, q, x.2) : Profile)) := by fun_prop
    exact (h1.comp h2).clm_apply (continuous_const : Continuous fun _ : ℝ => ((0 : ℝ), (1 : ℝ), (0 : ℝ)))
  have hvper : g (x.1, c, x.2) = g (x.1, 0, x.2) := by
    simpa using hg.periodic (x.1, 0, x.2)
  have hIBP : ∫ q in (0 : ℝ)..c, Complex.exp (κ * (q : ℂ)) • pdQ g (x.1, q, x.2)
      = -(κ • ∫ q in (0 : ℝ)..c, Complex.exp (κ * (q : ℂ)) • g (x.1, q, x.2)) :=
    cpq_ibp_exp c κ hκc (fun q : ℝ => g (x.1, q, x.2)) (fun q : ℝ => pdQ g (x.1, q, x.2)) hv hv'c hvper
  have hIk : Complex.I * (nzk c n : ℂ) = -κ := by
    rw [hκdef, nzk]
    push_cast
    ring
  unfold nzCoeff
  simp only [hE]
  rw [hIBP, hIk]
  module

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray
