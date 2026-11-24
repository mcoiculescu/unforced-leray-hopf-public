import UnforcedLeray.Short.PartIIIb.Concrete.AffineGradPin

/-!
# `PartIII-b:C/grad/3`: `GradCoefBound` from source leaves

Source `the November 2 reference manuscript`:
first line of `ret:general-affine-bounds` 5009-5016 (the `‖∇ĥ_A‖_{Y_2}` term), proof 5063-5079
("`C M(A) s^{5/2}` for both `h^p_A` and `ψ^p_A`", "the same calculation with the physical
spatial Jacobian `s^{-5/2}` bounds the lift and its gradient"), cutoff 4953-4963, ring-chart rules
5036-5039, tensor lift 2681-2689.

The entries of `s⁻¹∇ĥ_A` are `∂_q b, ∂_η b, -ε(𝒦+1)b` and the hoop entry `ε b_r`, with
`b = s^{-1/2}ĥ_A`; `𝒦 = η∂_η + 2s∂_s`, so two conormal derivatives of `A^y` enter
(`(s∂_s)^j A^y`, `j ≤ 2`, inside the `j ≤ 6` sum defining `M(A)`).

Leaves: `GradSupport`, `AyIterBound`, `AyContDiffAt2`, `GradCellBound`, `GradMeas`, `GradL2Conv`.
Proved here: `gradCoefBound_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Support (source 4953-4958, 5063-5079): `χ_f(s) = χ̂_f(νs) = 0` for `s ≥ 1.1/ν`, so `A^y`
vanishes near each `s > 1.1/ν`, hence `h^p_A = ψ^p_A = 0` there with all derivatives, and
`∇ĥ_A = 0`. -/
def GradSupport (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν ε : ℝ), 0 < ν → ∀ (A : ℝ → Mat3) (s : ℝ), (11 / 10) / ν < s →
    ∀ x : ℝ × ℝ, gradAcoef ν ε χf A (s, x) = 0

/-- Conormal size (source 5063-5079): `|(s∂_s)^j A^y(s)| ≤ s^{5/2} M(A)` for `j ≤ 2`,
`0 < s ≤ 1.1/ν` (terms of the `sSup` defining `M(A)`). -/
def AyIterBound (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    ∀ s : ℝ, 0 < s → s ≤ (11 / 10) / ν → ∀ j : ℕ, j ≤ 2 →
      frob (sDerivIter j (Ay ν χf A) s) ≤ s ^ (5 / 2 : ℝ) * affM ν χf A

/-- `A^y = χ_f A` is `C^2` at each `s > 0` for `A ∈ 𝒜` (`C^6`, source 4741-4745). -/
def AyContDiffAt2 (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν : ℝ) (A : ℝ → Mat3), IsAffElem as A → ∀ s : ℝ, 0 < s → ContDiffAt ℝ 2 (Ay ν χf A) s

/-- Gaussian cell norm (source 5063-5079): the normalized `L²` cell norm of the tensor field
`s⁻¹∇ĥ_A (s, ·)` (lattice sums `h^p_A, ψ^p_A` and their `∂_q, ∂_η, 𝒦, 𝒦²` derivatives: Gaussians
times polynomials, uniformly for `a = 1 + νs ∈ [1, 2.1]`, `ν, ε ≤ 1`, `s ≤ 1.1/ν`) is
`≤ K Σ_{j≤2} |(s∂_s)^j A^y(s)|`. -/
def GradCellBound : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (ν ε s : ℝ), 0 < ν → ν ≤ 1 → 0 < ε → ε ≤ 1 → 0 < s → s ≤ (11 / 10) / ν →
    ∀ (χf : ℝ → ℝ) (A : ℝ → Mat3), ContDiffAt ℝ 2 (Ay ν χf A) s →
    ∫⁻ x, ENNReal.ofReal (‖gradAcoef ν ε χf A (s, x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf ν))
      ≤ ENNReal.ofReal (K ^ 2 * (frob (Ay ν χf A s) + frob (sDeriv (Ay ν χf A) s) +
          frob (sDeriv (sDeriv (Ay ν χf A)) s)) ^ 2)

/-- Measurability of `gradAcoef` (differentiability of the lattice sums on `s > 0`). -/
def GradMeas (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν ε : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    AEStronglyMeasurable (gradAcoef ν ε χf A) (gradMeasure (cOf ν))

/-- Conversion (source 5063-5079, `lintegral_ageμ`): a cell bound `D² s^5` on `0 < s ≤ T`
(`T ≥ 1`), zero beyond `T`, gives `‖F‖_{L²(π s^{-1/2} dς)} ≤ D T^3`
(exact value `D √(2π/11) T^{11/4}`). -/
def GradL2Conv : Prop :=
  ∀ (c T D : ℝ) (F : Chart → Ten3), 0 < c → 1 ≤ T → 0 ≤ D →
    AEStronglyMeasurable F (gradMeasure c) →
    (∀ s : ℝ, T < s → ∀ x : ℝ × ℝ, F (s, x) = 0) →
    (∀ s : ℝ, 0 < s → s ≤ T →
      ∫⁻ x, ENNReal.ofReal (‖F (s, x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ c)
        ≤ ENNReal.ofReal (D ^ 2 * s ^ 5)) →
    MemLp F 2 (gradMeasure c) ∧ eLpNorm F 2 (gradMeasure c) ≤ ENNReal.ofReal (D * T ^ 3)

theorem gradCoefBound_of (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf)
    (h1 : GradSupport χf) (h2 : AyIterBound as χf) (h2' : AyContDiffAt2 as χf)
    (h3 : GradCellBound) (h4 : GradMeas as χf) (h5 : GradL2Conv) : GradCoefBound as χf := by
  obtain ⟨K, hK0, hK⟩ := h3
  refine ⟨K * 3 * (11 / 10) ^ 3, 3, by positivity, ?_⟩
  intro ν ε hν hν1 hε hε1 A hA
  have hM := affM_nonneg ν χf A
  set M := affM ν χf A with hMdef
  set T : ℝ := (11 / 10) / ν with hT
  have hT1 : 1 ≤ T := by
    rw [hT, le_div_iff₀ hν]; linarith
  set D : ℝ := K * M * 3 with hD
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hcell : ∀ s : ℝ, 0 < s → s ≤ T →
      ∫⁻ x, ENNReal.ofReal (‖gradAcoef ν ε χf A (s, x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf ν))
        ≤ ENNReal.ofReal (D ^ 2 * s ^ 5) := by
    intro s hs hsT
    have hB0 := h2 hχ ν hν A hA s hs hsT 0 (by norm_num)
    have hB1 := h2 hχ ν hν A hA s hs hsT 1 (by norm_num)
    have hB2 := h2 hχ ν hν A hA s hs hsT 2 (by norm_num)
    simp only [sDerivIter] at hB0 hB1 hB2
    have hc := hK ν ε s hν hν1 hε hε1 hs hsT χf A (h2' hχ ν A hA s hs)
    refine hc.trans (ENNReal.ofReal_le_ofReal ?_)
    have hs52 : (s ^ (5 / 2 : ℝ)) ^ 2 = s ^ 5 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]; norm_num
    have hsum : frob (Ay ν χf A s) + frob (sDeriv (Ay ν χf A) s) +
        frob (sDeriv (sDeriv (Ay ν χf A)) s) ≤ s ^ (5 / 2 : ℝ) * M * 3 := by
      linarith
    have h0 : 0 ≤ frob (Ay ν χf A s) + frob (sDeriv (Ay ν χf A) s) +
        frob (sDeriv (sDeriv (Ay ν χf A)) s) :=
      add_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    have hsq := pow_le_pow_left₀ h0 hsum 2
    have : D ^ 2 * s ^ 5 = K ^ 2 * (s ^ (5 / 2 : ℝ) * M * 3) ^ 2 := by
      rw [hD]; simp only [mul_pow, hs52]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  have hc0 : 0 < cOf ν := by unfold cOf; positivity
  obtain ⟨hm, hn⟩ := h5 (cOf ν) T D (gradAcoef ν ε χf A) hc0 hT1 hD0 (h4 hχ ν ε hν A hA)
    (fun s hs x => h1 hχ ν ε hν A s hs x) hcell
  refine ⟨hm, hn.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hT3 : T ^ 3 = (11 / 10) ^ 3 * ν⁻¹ ^ 3 := by
    rw [hT, div_eq_mul_inv, mul_pow]
  refine le_of_eq ?_
  calc D * T ^ 3 = K * 3 * T ^ 3 * M := by rw [hD]; ring
    _ = K * 3 * (11 / 10) ^ 3 * ν⁻¹ ^ 3 * M := by rw [hT3]; ring

end UnforcedLeray.Short.PartIIIb.Concrete
