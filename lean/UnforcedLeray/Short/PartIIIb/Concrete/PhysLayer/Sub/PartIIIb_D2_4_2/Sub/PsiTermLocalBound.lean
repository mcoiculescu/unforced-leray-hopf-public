import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.Sub.PartIIIb_IIIb_D2_4_2_1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_2.Sub.PsiProfileGaussBound

/-!
# `PsiTermLocalBound` (task `PartIII-b:IIIb-D2/4/2/1/4`)

Source of record: `the November 2 reference manuscript` lines 4963-4991
(the lattice sums `Σ_j Ψ(s, x_j)` and their required derivatives converge by Gaussian decay).

The `j`-th term is the profile composed with the translation by `a_j = (0, (-(j c), 0))`,
`c = cOf ν`, so its derivatives at `y` are the derivatives of the profile at `y + a_j`.
On a neighbourhood of `x = (s, (q₀, η₀))`, `s > 0`, the Gaussian bound (`PsiProfileGaussBound`
at `s₀ = s`) and the inequality `(jc)² ≤ 2u² + 2(u - jc)²` give a summable majorant.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `j ↦ exp(-|j|)` is summable over `ℤ`. -/
theorem psiTL_summable_exp_neg_abs :
    Summable (fun j : ℤ => Real.exp (-|(j : ℝ)|)) := by
  refine Summable.of_nat_of_neg ?_ ?_ <;> simpa using Real.summable_exp_neg_nat

/-- Quadratic decay dominated by `exp(-|j|)` in exponent form: `-B j² ≤ 1/(4B) - |j|`, `B > 0`. -/
theorem psiTL_gauss_le_abs (B : ℝ) (hB : 0 < B) (j : ℤ) :
    -(B * (j : ℝ) ^ 2) ≤ 1 / (4 * B) + -|(j : ℝ)| := by
  have ht : (j : ℝ) ^ 2 = |(j : ℝ)| ^ 2 := (sq_abs _).symm
  rw [ht]
  have hB0 : B ≠ 0 := hB.ne'
  have h4 : 0 < 4 * B := by positivity
  have hw : 1 / (4 * B) * (4 * B) = 1 := by field_simp
  nlinarith [sq_nonneg (2 * B * |(j : ℝ)| - 1), hw, h4]

/-- The `j`-th term is the profile translated by `a_j = (0, (-(j c), 0))`. -/
theorem psiTL_term_eq_shift (ν : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (j : ℤ) :
    psiTerm ν χf A j =
      fun z => psiProfile ν χf A (z + (0, (-((j : ℝ) * cOf ν), 0))) := by
  funext z
  have e : z + (0, (-((j : ℝ) * cOf ν), 0)) = (z.1, (z.2.1 - (j : ℝ) * cOf ν, z.2.2)) := by
    refine Prod.ext ?_ ?_
    · simp
    · refine Prod.ext ?_ ?_ <;> simp [sub_eq_add_neg]
  simp only [psiTerm]
  rw [e]
  rfl

theorem psiTermLocalBound_of (as : ℝ) (χf : ℝ → ℝ) (h3 : PsiProfileGaussBound as χf) :
    PsiTermLocalBound as χf := by
  intro hχ ν hν A hA x hx
  have hx1 : 0 < x.1 := hx.1
  obtain ⟨C, hC⟩ := h3 hχ ν hν A hA x.1 hx1
  have hc : 0 < cOf ν := by unfold cOf; positivity
  have hK : 0 < 1 + 2 * ν * x.1 := by positivity
  have hK0 : (1 + 2 * ν * x.1) ≠ 0 := hK.ne'
  have hB : 0 < cOf ν ^ 2 / (16 * (1 + 2 * ν * x.1)) := by positivity
  refine ⟨fun j : ℤ => |C| * (Real.exp (((|x.2.1| + 1) ^ 2) / (8 * (1 + 2 * ν * x.1)) +
      1 / (4 * (cOf ν ^ 2 / (16 * (1 + 2 * ν * x.1))))) * Real.exp (-|(j : ℝ)|)), ?_, ?_⟩
  · exact (psiTL_summable_exp_neg_abs.mul_left _).mul_left _
  · have hev : ∀ᶠ p in 𝓝 x, (p.1 ∈ Ioo (x.1 / 2) (2 * x.1)) ∧ |p.2.1| < |x.2.1| + 1 := by
      have e1 : ∀ᶠ p in 𝓝 x, p.1 ∈ Ioo (x.1 / 2) (2 * x.1) :=
        continuous_fst.continuousAt.eventually_mem (Ioo_mem_nhds (by linarith) (by linarith))
      have hc2 : ContinuousAt (fun p : Chart => |p.2.1|) x :=
        (continuous_abs.comp (continuous_fst.comp continuous_snd)).continuousAt
      have e2 : ∀ᶠ p in 𝓝 x, |p.2.1| ∈ Iio (|x.2.1| + 1) :=
        hc2.eventually_mem (Iio_mem_nhds (by linarith))
      exact e1.and e2
    refine ⟨{p : Chart | (p.1 ∈ Ioo (x.1 / 2) (2 * x.1)) ∧ |p.2.1| < |x.2.1| + 1}, hev, ?_⟩
    intro j y hy k hk
    have hy' : (y.1 ∈ Ioo (x.1 / 2) (2 * x.1)) ∧ |y.2.1| < |x.2.1| + 1 := hy
    obtain ⟨hy1, hy2⟩ := hy'
    obtain ⟨p, hp⟩ : ∃ p : Chart, p = y + (0, (-((j : ℝ) * cOf ν), 0)) := ⟨_, rfl⟩
    have hp1 : p.1 = y.1 := by rw [hp]; simp
    have hp2 : p.2 = (y.2.1 - (j : ℝ) * cOf ν, y.2.2) := by
      rw [hp]
      refine Prod.ext ?_ ?_ <;> simp [sub_eq_add_neg]
    have hmem : p.1 ∈ Icc (x.1 / 2) (2 * x.1) := by
      rw [hp1]; exact ⟨hy1.1.le, hy1.2.le⟩
    have hG := hC p hmem k hk
    have hd : iteratedFDeriv ℝ k (fun z => psiProfile ν χf A (z + (0, (-((j : ℝ) * cOf ν), 0)))) y =
        iteratedFDeriv ℝ k (psiProfile ν χf A) p := by
      rw [hp]
      exact iteratedFDeriv_comp_add_right k _ _
    rw [psiTL_term_eq_shift, hd]
    have hsq : sq2 p.2 = (y.2.1 - (j : ℝ) * cOf ν) ^ 2 + y.2.2 ^ 2 := by
      rw [hp2]; rfl
    have hkey : ((j : ℝ) * cOf ν) ^ 2 ≤ 2 * y.2.1 ^ 2 + 2 * (y.2.1 - (j : ℝ) * cOf ν) ^ 2 := by
      nlinarith [sq_nonneg (2 * y.2.1 - (j : ℝ) * cOf ν)]
    have hu2 : y.2.1 ^ 2 ≤ (|x.2.1| + 1) ^ 2 := by
      nlinarith [abs_nonneg y.2.1, sq_abs y.2.1, hy2]
    have hsq' : ((j : ℝ) * cOf ν) ^ 2 / 2 - (|x.2.1| + 1) ^ 2 ≤ sq2 p.2 := by
      rw [hsq]; nlinarith [sq_nonneg y.2.2, hkey, hu2]
    have hneg : -(sq2 p.2) ≤ (|x.2.1| + 1) ^ 2 - ((j : ℝ) * cOf ν) ^ 2 / 2 := by
      linarith
    have hdiv : -(sq2 p.2) / (8 * (1 + 2 * ν * x.1)) ≤
        ((|x.2.1| + 1) ^ 2 - ((j : ℝ) * cOf ν) ^ 2 / 2) / (8 * (1 + 2 * ν * x.1)) := by
      gcongr
    have hid : ((|x.2.1| + 1) ^ 2 - ((j : ℝ) * cOf ν) ^ 2 / 2) / (8 * (1 + 2 * ν * x.1)) =
        (|x.2.1| + 1) ^ 2 / (8 * (1 + 2 * ν * x.1)) +
          -((cOf ν ^ 2 / (16 * (1 + 2 * ν * x.1))) * (j : ℝ) ^ 2) := by
      field_simp
      ring
    have hB1 := psiTL_gauss_le_abs (cOf ν ^ 2 / (16 * (1 + 2 * ν * x.1))) hB j
    have hexp : -(sq2 p.2) / (8 * (1 + 2 * ν * x.1)) ≤
        (|x.2.1| + 1) ^ 2 / (8 * (1 + 2 * ν * x.1)) +
          1 / (4 * (cOf ν ^ 2 / (16 * (1 + 2 * ν * x.1)))) + -|(j : ℝ)| := by
      linarith [hdiv, hid, hB1]
    have hE : Real.exp (-(sq2 p.2) / (8 * (1 + 2 * ν * x.1))) ≤
        Real.exp ((|x.2.1| + 1) ^ 2 / (8 * (1 + 2 * ν * x.1)) +
          1 / (4 * (cOf ν ^ 2 / (16 * (1 + 2 * ν * x.1))))) * Real.exp (-|(j : ℝ)|) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr hexp
    have h1 : C * Real.exp (-(sq2 p.2) / (8 * (1 + 2 * ν * x.1))) ≤
        |C| * Real.exp (-(sq2 p.2) / (8 * (1 + 2 * ν * x.1))) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
    have h2 : |C| * Real.exp (-(sq2 p.2) / (8 * (1 + 2 * ν * x.1))) ≤
        |C| * (Real.exp ((|x.2.1| + 1) ^ 2 / (8 * (1 + 2 * ν * x.1)) +
          1 / (4 * (cOf ν ^ 2 / (16 * (1 + 2 * ν * x.1))))) * Real.exp (-|(j : ℝ)|)) :=
      mul_le_mul_of_nonneg_left hE (abs_nonneg C)
    exact hG.trans (h1.trans h2)

theorem psiTermLocalBound_proof (as : ℝ) (χf : ℝ → ℝ) : PsiTermLocalBound as χf :=
  psiTermLocalBound_of as χf (psiProfileGaussBound_proof as χf)

end UnforcedLeray.Short.PartIIIb.Concrete
