import UnforcedLeray.Short.PartIIIb.Tasks
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Proof of `T_newtonD2` (source: `the November 2 reference manuscript`, lines 4863-4866)

`F x = (3 x₃² - |x|²) / (4π |x|⁵)` is `∂₃₃N` for `N = 1/(4π|x|)`. The claim is
`D²F(r,0,0) = (4π r⁵)⁻¹ diag(-12, 3, 9)`.

Route. `F` is `C²` near `x₀ = (r,0,0)`, so its second derivative there is symmetric
(`ContDiffAt.isSymmSndFDerivAt`). For a direction `u`, `D²F(x₀)[u,u]` is the second derivative at `0`
of the line restriction `t ↦ F(x₀ + t u)` (`bridge_second`). On the line, `F` is the explicit quotient
`pL / DL`, and `line_second` evaluates its second derivative by the quotient rule. Polarization with
the symmetry then gives every entry.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology

namespace UnforcedLeray.Short.PartIIIb

/-- Numerator `3 y₃² - |y|²` of `F` on the line `y = (r,0,0) + t (a,b,c)`. -/
def pL (r a b c t : ℝ) : ℝ := -r ^ 2 - 2 * r * a * t + (2 * c ^ 2 - a ^ 2 - b ^ 2) * t ^ 2

/-- `|y|²` on the same line. -/
def qL (r a b c t : ℝ) : ℝ := r ^ 2 + 2 * r * a * t + (a ^ 2 + b ^ 2 + c ^ 2) * t ^ 2

/-- Denominator `4π |y|⁵` on the same line. -/
def DL (r a b c t : ℝ) : ℝ := 4 * Real.pi * (qL r a b c t) ^ (5 / 2 : ℝ)

lemma hasDerivAt_pL (r a b c t : ℝ) :
    HasDerivAt (fun s => pL r a b c s)
      (-2 * r * a + 2 * (2 * c ^ 2 - a ^ 2 - b ^ 2) * t) t := by
  have h := ((hasDerivAt_const t (-r ^ 2)).sub ((hasDerivAt_id' t).const_mul (2 * r * a))).add
    ((hasDerivAt_pow 2 t).const_mul (2 * c ^ 2 - a ^ 2 - b ^ 2))
  refine h.congr_deriv ?_
  norm_num
  ring

lemma hasDerivAt_qL (r a b c t : ℝ) :
    HasDerivAt (fun s => qL r a b c s) (2 * r * a + 2 * (a ^ 2 + b ^ 2 + c ^ 2) * t) t := by
  have h := (((hasDerivAt_id' t).const_mul (2 * r * a)).const_add (r ^ 2)).add
    ((hasDerivAt_pow 2 t).const_mul (a ^ 2 + b ^ 2 + c ^ 2))
  refine h.congr_deriv ?_
  norm_num
  ring

lemma hasDerivAt_DL (r a b c t : ℝ) :
    HasDerivAt (fun s => DL r a b c s)
      (4 * Real.pi * ((2 * r * a + 2 * (a ^ 2 + b ^ 2 + c ^ 2) * t) * (5 / 2 : ℝ) *
        (qL r a b c t) ^ ((5 / 2 : ℝ) - 1))) t :=
  ((hasDerivAt_qL r a b c t).rpow_const (Or.inr (show (1 : ℝ) ≤ 5 / 2 by norm_num))).const_mul
    (4 * Real.pi)

lemma DL_zero_ne (r a b c : ℝ) (hr : 0 < r) : DL r a b c 0 ≠ 0 := by
  have hq : qL r a b c 0 = r ^ 2 := by unfold qL; ring
  unfold DL
  rw [hq]
  exact (mul_pos (mul_pos (by norm_num) Real.pi_pos) (Real.rpow_pos_of_pos (pow_pos hr 2) _)).ne'

lemma rsq_rpow (r : ℝ) (hr : 0 < r) (s : ℝ) : (r ^ 2) ^ s = r ^ (2 * s) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
  norm_num

/-- Second derivative along a line: `D²F(x)[u,u] = (d/dt)² F(x + t u)` at `t = 0`. -/
lemma bridge_second (F : (Fin 3 → ℝ) → ℝ) (x u : Fin 3 → ℝ) (hF : ContDiffAt ℝ 2 F x) :
    fderiv ℝ (fderiv ℝ F) x u u = deriv (deriv (fun t : ℝ => F (x + t • u))) 0 := by
  have hγ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => x + s • u) u t := by
    intro t
    simpa using ((hasDerivAt_id' t).smul_const u).const_add x
  have hγc : Continuous (fun s : ℝ => x + s • u) := by fun_prop
  have hevF : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 F y := hF.eventually (by simp)
  have hevt : ∀ᶠ t in 𝓝 (0 : ℝ), ContDiffAt ℝ 2 F (x + t • u) := by
    have hT : Tendsto (fun s : ℝ => x + s • u) (𝓝 0) (𝓝 x) := by
      simpa using hγc.tendsto 0
    exact hT.eventually hevF
  have hderiv : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (fun s : ℝ => F (x + s • u)) (fderiv ℝ F (x + t • u) u) t := by
    filter_upwards [hevt] with t ht
    have hdiff : DifferentiableAt ℝ F (x + t • u) := ht.differentiableAt (by norm_num)
    exact hdiff.hasFDerivAt.comp_hasDerivAt t (hγ t)
  have hD1 : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hDu : DifferentiableAt ℝ (fun y => fderiv ℝ F y u) x :=
    hD1.clm_apply (differentiableAt_const u)
  have hchain : HasDerivAt (fun s : ℝ => fderiv ℝ F (x + s • u) u)
      (fderiv ℝ (fun y => fderiv ℝ F y u) x u) 0 :=
    hDu.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hγ 0) (by simp)
  have hfd : fderiv ℝ (fun y => fderiv ℝ F y u) x u = fderiv ℝ (fderiv ℝ F) x u u := by
    rw [fderiv_clm_apply hD1 (differentiableAt_const u)]
    simp
  have hEq : deriv (fun s : ℝ => F (x + s • u)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t : ℝ => fderiv ℝ F (x + t • u) u) := by
    filter_upwards [hderiv] with t ht
    exact ht.deriv
  rw [hEq.deriv_eq, hchain.deriv, hfd]

/-- The second derivative of `t ↦ pL(t) / DL(t)` at `0`, with `pL, DL` the line data. -/
lemma line_second (r a b c : ℝ) (hr : 0 < r) :
    deriv (deriv (fun t : ℝ => pL r a b c t / DL r a b c t)) 0 =
      (9 * c ^ 2 + 3 * b ^ 2 - 12 * a ^ 2) / (4 * Real.pi * r ^ 5) := by
  have hD0 : DL r a b c 0 ≠ 0 := DL_zero_ne r a b c hr
  have hdq : ∀ t : ℝ, DL r a b c t ≠ 0 →
      HasDerivAt (fun s => pL r a b c s / DL r a b c s)
        (((-2 * r * a + 2 * (2 * c ^ 2 - a ^ 2 - b ^ 2) * t) * DL r a b c t -
          pL r a b c t * (4 * Real.pi * ((2 * r * a + 2 * (a ^ 2 + b ^ 2 + c ^ 2) * t) * (5 / 2 : ℝ) *
            (qL r a b c t) ^ ((5 / 2 : ℝ) - 1)))) / (DL r a b c t) ^ 2) t :=
    fun t ht => (hasDerivAt_pL r a b c t).div (hasDerivAt_DL r a b c t) ht
  have hDne : ∀ᶠ t in 𝓝 (0 : ℝ), DL r a b c t ≠ 0 :=
    (hasDerivAt_DL r a b c 0).continuousAt.eventually_ne hD0
  have hgeq : deriv (fun s => pL r a b c s / DL r a b c s) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => ((-2 * r * a + 2 * (2 * c ^ 2 - a ^ 2 - b ^ 2) * t) * DL r a b c t -
        pL r a b c t * (4 * Real.pi * ((2 * r * a + 2 * (a ^ 2 + b ^ 2 + c ^ 2) * t) * (5 / 2 : ℝ) *
          (qL r a b c t) ^ ((5 / 2 : ℝ) - 1)))) / (DL r a b c t) ^ 2) := by
    filter_upwards [hDne] with t ht
    exact (hdq t ht).deriv
  rw [hgeq.deriv_eq]
  -- derivative of the numerator `p' DL - p DL'` and of the denominator `DL²` at `0`
  have hlin := ((hasDerivAt_id' (0 : ℝ)).const_mul (2 * (2 * c ^ 2 - a ^ 2 - b ^ 2))).const_add
    (-2 * r * a)
  have hL0 := ((hasDerivAt_id' (0 : ℝ)).const_mul (2 * (a ^ 2 + b ^ 2 + c ^ 2))).const_add
    (2 * r * a)
  have hD1 := ((((hL0.mul_const (5 / 2 : ℝ)).mul
    ((hasDerivAt_qL r a b c 0).rpow_const (Or.inr (show (1 : ℝ) ≤ (5 / 2 : ℝ) - 1 by norm_num))))).const_mul
    (4 * Real.pi))
  have hnum := (hlin.mul (hasDerivAt_DL r a b c 0)).sub ((hasDerivAt_pL r a b c 0).mul hD1)
  have hden := (hasDerivAt_DL r a b c 0).pow 2
  have hq := hnum.div hden (pow_ne_zero 2 hD0)
  refine (hq.deriv).trans ?_
  have hr0 : r ≠ 0 := hr.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, DL, qL, pL]
  norm_num
  simp only [rsq_rpow r hr]
  norm_num
  field_simp
  ring

theorem newtonD2 : UnforcedLeray.Short.PartIIIb.T_newtonD2 := by
  intro r hr F
  have e0 : (![r, 0, 0] : Fin 3 → ℝ) 0 = r := by simp
  have e1 : (![r, 0, 0] : Fin 3 → ℝ) 1 = 0 := by simp
  have e2 : (![r, 0, 0] : Fin 3 → ℝ) 2 = 0 := by simp
  have hQ : (0 : ℝ) < (![r, 0, 0] : Fin 3 → ℝ) 0 ^ 2 + (![r, 0, 0] : Fin 3 → ℝ) 1 ^ 2 +
      (![r, 0, 0] : Fin 3 → ℝ) 2 ^ 2 := by
    rw [e0, e1, e2]
    simpa using pow_pos hr 2
  have hcd : ContDiffAt ℝ 2 F ![r, 0, 0] := by
    have hnum : ContDiffAt ℝ 2
        (fun x : Fin 3 → ℝ => 3 * x 2 ^ 2 - (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2)) ![r, 0, 0] := by
      fun_prop
    have hbase : ContDiffAt ℝ 2
        (fun x : Fin 3 → ℝ => x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) ![r, 0, 0] := by
      fun_prop
    have hden : ContDiffAt ℝ 2
        (fun x : Fin 3 → ℝ => 4 * Real.pi * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) ^ (5 / 2 : ℝ))
        ![r, 0, 0] :=
      contDiffAt_const.mul (hbase.rpow_const_of_ne hQ.ne')
    have hden0 : 4 * Real.pi * ((![r, 0, 0] : Fin 3 → ℝ) 0 ^ 2 + (![r, 0, 0] : Fin 3 → ℝ) 1 ^ 2 +
        (![r, 0, 0] : Fin 3 → ℝ) 2 ^ 2) ^ (5 / 2 : ℝ) ≠ 0 :=
      (mul_pos (by positivity) (Real.rpow_pos_of_pos hQ _)).ne'
    exact hnum.div hden hden0
  have hsymm := ContDiffAt.isSymmSndFDerivAt hcd (by simp)
  have hdiag : ∀ u : Fin 3 → ℝ, fderiv ℝ (fderiv ℝ F) ![r, 0, 0] u u =
      (9 * u 2 ^ 2 + 3 * u 1 ^ 2 - 12 * u 0 ^ 2) / (4 * Real.pi * r ^ 5) := by
    intro u
    have hfun : (fun t : ℝ => F (![r, 0, 0] + t • u)) =
        fun t => pL r (u 0) (u 1) (u 2) t / DL r (u 0) (u 1) (u 2) t := by
      funext t
      have c0 : (![r, 0, 0] + t • u : Fin 3 → ℝ) 0 = r + t * u 0 := by simp
      have c1 : (![r, 0, 0] + t • u : Fin 3 → ℝ) 1 = t * u 1 := by simp
      have c2 : (![r, 0, 0] + t • u : Fin 3 → ℝ) 2 = t * u 2 := by simp
      have hq : (r + t * u 0) ^ 2 + (t * u 1) ^ 2 + (t * u 2) ^ 2 =
          qL r (u 0) (u 1) (u 2) t := by unfold qL; ring
      have hp : 3 * (t * u 2) ^ 2 - ((r + t * u 0) ^ 2 + (t * u 1) ^ 2 + (t * u 2) ^ 2) =
          pL r (u 0) (u 1) (u 2) t := by unfold pL; ring
      show (3 * (![r, 0, 0] + t • u : Fin 3 → ℝ) 2 ^ 2 - ((![r, 0, 0] + t • u : Fin 3 → ℝ) 0 ^ 2 +
          (![r, 0, 0] + t • u : Fin 3 → ℝ) 1 ^ 2 + (![r, 0, 0] + t • u : Fin 3 → ℝ) 2 ^ 2)) /
          (4 * Real.pi * ((![r, 0, 0] + t • u : Fin 3 → ℝ) 0 ^ 2 +
          (![r, 0, 0] + t • u : Fin 3 → ℝ) 1 ^ 2 + (![r, 0, 0] + t • u : Fin 3 → ℝ) 2 ^ 2) ^
            (5 / 2 : ℝ))
          = pL r (u 0) (u 1) (u 2) t / (4 * Real.pi * (qL r (u 0) (u 1) (u 2) t) ^ (5 / 2 : ℝ))
      rw [c0, c1, c2, hp, hq]
    rw [bridge_second F ![r, 0, 0] u hcd, hfun, line_second r (u 0) (u 1) (u 2) hr]
  have hpol : ∀ v w : Fin 3 → ℝ, fderiv ℝ (fderiv ℝ F) ![r, 0, 0] v w =
      (fderiv ℝ (fderiv ℝ F) ![r, 0, 0] (v + w) (v + w) - fderiv ℝ (fderiv ℝ F) ![r, 0, 0] v v -
        fderiv ℝ (fderiv ℝ F) ![r, 0, 0] w w) / 2 := by
    intro v w
    have hs := hsymm w v
    simp only [map_add, add_apply]
    linarith
  intro i j
  rw [hpol (Pi.single i 1) (Pi.single j 1), hdiag, hdiag, hdiag]
  fin_cases i <;> fin_cases j <;> simp <;> ring

end UnforcedLeray.Short.PartIIIb
