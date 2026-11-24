import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.Sub.PartIIIb_C_rep_5_1_2_4_1_2_7_1

/-!
# `PDX0RepCoV` (`PartIII-b:C/rep/5/1/2/4/1/2/7/2`)

Source `the November 2 reference manuscript` 3611-3617 (`sep:resolvent`), 4171.
The `sepRho` integral of the real part of `sepPhi μ - sepPhi (μ+1)` is an iterated integral over
`l ∈ (0,1)` (`integral_prod`); the phase-lag integral is an iterated integral over `σ < τ`
(`integral_prod` on `volume`); the change of variables `σ = τ + 2 log l`
(`integral_image_eq_integral_abs_deriv_smul`) identifies them, since
`2 l⁻¹ · (-(l^{2μ+3} - l^{2μ+5})) = -2 (l^{2μ+2} - l^{2μ+4})`.
Integrability is `pdX0RepIntegrable` (the previous leaf).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The `z`-integral of the `i`-th component of the phase-lag kernel at phase `σ`. -/
def pdCovG (ν μ τ : ℝ) (x : Space) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3)
    (σ : ℝ) : ℝ :=
  ∫ z : Space, (xKer ν μ (τ - σ) (x - pdLam (τ - σ) • z) (T σ z)) i

/-- The real part of the difference of the two `l`-integrands, in the `Gm` form. -/
lemma sepPhi_re_eq {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} (ν μ τ : ℝ) (i : Fin 3)
    {x z : Space} {l : ℝ} (hsupp : ∀ σ z', T σ z' ≠ 0 → ϱ z' < ϱ x) (hl0 : 0 < l) (hl1 : l < 1) :
    (sepPhi ν (μ : ℂ) T τ i (l, z) x - sepPhi ν ((μ : ℂ) + 1) T τ i (l, z) x).re =
      -2 * (l ^ (2 * μ + 2) - l ^ (2 * μ + 4)) *
        ∑ j : Fin 3, ∑ k : Fin 3, T8_1.Gm k i j (ν * (1 - l ^ 2), x - l • z) *
          T (τ + 2 * Real.log l) z j k := by
  rw [sepPhi_eq_gm ν (μ : ℂ) τ i hsupp hl0 hl1, sepPhi_eq_gm ν ((μ : ℂ) + 1) τ i hsupp hl0 hl1]
  have e1 : (l : ℂ) ^ (2 * (μ : ℂ) + 2) = ((l ^ (2 * μ + 2) : ℝ) : ℂ) := by
    rw [show (2 * (μ : ℂ) + 2) = ((2 * μ + 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_cpow hl0.le]
  have e2 : (l : ℂ) ^ (2 * ((μ : ℂ) + 1) + 2) = ((l ^ (2 * μ + 4) : ℝ) : ℂ) := by
    rw [show (2 * ((μ : ℂ) + 1) + 2) = ((2 * μ + 4 : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_cpow hl0.le]
  have hS : ∑ j : Fin 3, ∑ k : Fin 3, ((T8_1.Gm k i j (ν * (1 - l ^ 2), x - l • z) : ℝ) : ℂ) *
      ((T (τ + 2 * Real.log l) z j k : ℝ) : ℂ) =
      ((∑ j : Fin 3, ∑ k : Fin 3, T8_1.Gm k i j (ν * (1 - l ^ 2), x - l • z) *
        T (τ + 2 * Real.log l) z j k : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [e1, e2, hS]
  simp [Complex.mul_re]
  ring

/-- The `i`-th component of `xKer` on the phase-lag ray, in `Gm` form. -/
lemma xKer_comp_gm {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} (ν μ τ : ℝ) (i : Fin 3)
    {x z : Space} {l : ℝ} (hsupp : ∀ σ z', T σ z' ≠ 0 → ϱ z' < ϱ x) (hl0 : 0 < l) (hl1 : l < 1) :
    (xKer ν μ (τ - (τ + 2 * Real.log l)) (x - pdLam (τ - (τ + 2 * Real.log l)) • z)
        (T (τ + 2 * Real.log l) z)) i =
      -(l ^ (2 * μ + 3) - l ^ (2 * μ + 5)) *
        ∑ j : Fin 3, ∑ k : Fin 3, T8_1.Gm k i j (ν * (1 - l ^ 2), x - l • z) *
          T (τ + 2 * Real.log l) z j k := by
  rw [xKer_apply, pdLam_log τ l hl0]
  congr 1
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  by_cases hw : x - l • z = 0
  · have hT := zero_of_eq hsupp hl0 hl1 (sub_eq_zero.mp hw) (τ + 2 * Real.log l)
    rw [hT]
    simp
  · rw [T8_1.Gm_eq k i j (ν * (1 - l ^ 2)) hw]

theorem pdX0RepCoV : PDX0RepCoV := by
  intro ν μ R c g hν hR hc hμ1 hμ2 hg τ x hsupp hfin i
  obtain ⟨hA, hX⟩ := pdX0RepIntegrable ν μ R c g hν hR hc hμ1 hμ2 hg τ x hsupp hfin
  have hdiff : Integrable (fun p : ℝ × Space => sepPhi ν (μ : ℂ) (oldPhys R c g) τ i p x -
      sepPhi ν ((μ : ℂ) + 1) (oldPhys R c g) τ i p x) sepRho :=
    (hA i).1.sub (hA i).2
  have hre : Integrable (fun p : ℝ × Space => (sepPhi ν (μ : ℂ) (oldPhys R c g) τ i p x -
      sepPhi ν ((μ : ℂ) + 1) (oldPhys R c g) τ i p x).re) sepRho :=
    hdiff.re
  -- Step 1: the `sepRho` side as an iterated integral over `l ∈ (0,1)`.
  have hLHS : ∫ p : ℝ × Space, (sepPhi ν (μ : ℂ) (oldPhys R c g) τ i p x -
      sepPhi ν ((μ : ℂ) + 1) (oldPhys R c g) τ i p x).re ∂sepRho =
      ∫ l in Ioo (0 : ℝ) 1, (-2 * (l ^ (2 * μ + 2) - l ^ (2 * μ + 4))) *
        ∫ z : Space, ∑ j : Fin 3, ∑ k : Fin 3,
          T8_1.Gm k i j (ν * (1 - l ^ 2), x - l • z) * oldPhys R c g (τ + 2 * Real.log l) z j k := by
    unfold sepRho
    rw [integral_prod _ hre]
    refine setIntegral_congr_fun measurableSet_Ioo fun l hl => ?_
    have hfun : (fun z : Space => (sepPhi ν (μ : ℂ) (oldPhys R c g) τ i (l, z) x -
        sepPhi ν ((μ : ℂ) + 1) (oldPhys R c g) τ i (l, z) x).re) =
        fun z : Space => -2 * (l ^ (2 * μ + 2) - l ^ (2 * μ + 4)) *
          ∑ j : Fin 3, ∑ k : Fin 3, T8_1.Gm k i j (ν * (1 - l ^ 2), x - l • z) *
            oldPhys R c g (τ + 2 * Real.log l) z j k :=
      funext fun z => sepPhi_re_eq ν μ τ i hsupp hl.1 hl.2
    rw [hfun, integral_const_mul]
  -- Step 2: the phase-lag side as an iterated integral over `σ < τ`.
  have hG : Integrable (fun e : ℝ × Space =>
      if e.1 < τ then (xKer ν μ (τ - e.1) (x - pdLam (τ - e.1) • e.2) (oldPhys R c g e.1 e.2)) i
      else 0) (volume.prod volume) := by
    have hXi : Integrable (fun e : ℝ × Space =>
        (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i)
          (if e.1 < τ then xKer ν μ (τ - e.1) (x - pdLam (τ - e.1) • e.2) (oldPhys R c g e.1 e.2)
            else 0)) volume :=
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i).integrable_comp hX
    have hfun : (fun e : ℝ × Space =>
        (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i)
          (if e.1 < τ then xKer ν μ (τ - e.1) (x - pdLam (τ - e.1) • e.2) (oldPhys R c g e.1 e.2)
            else 0)) =
        fun e : ℝ × Space => if e.1 < τ then
          (xKer ν μ (τ - e.1) (x - pdLam (τ - e.1) • e.2) (oldPhys R c g e.1 e.2)) i else 0 := by
      funext e
      by_cases h : e.1 < τ <;> simp [h]
    rw [hfun] at hXi
    rw [← Measure.volume_eq_prod]
    exact hXi
  have hRHS : ∫ e : ℝ × Space, (if e.1 < τ then
      (xKer ν μ (τ - e.1) (x - pdLam (τ - e.1) • e.2) (oldPhys R c g e.1 e.2)) i else 0) =
      ∫ σ in Iio τ, pdCovG ν μ τ x (oldPhys R c g) i σ := by
    rw [Measure.volume_eq_prod, integral_prod _ hG, ← integral_indicator measurableSet_Iio]
    congr 1
    funext σ
    by_cases hσ : σ < τ
    · simp only [Set.mem_Iio, hσ, if_true, pdCovG, Set.indicator_of_mem]
    · simp [Set.indicator_apply, Set.mem_Iio, hσ]
  -- Step 3: the change of variables `σ = τ + 2 log l`.
  have himg : (fun l : ℝ => τ + 2 * Real.log l) '' Ioo (0 : ℝ) 1 = Iio τ := by
    ext σ
    constructor
    · rintro ⟨l, hl, rfl⟩
      have hlog : Real.log l < 0 := Real.log_neg hl.1 hl.2
      show τ + 2 * Real.log l < τ
      linarith
    · intro hσ
      have hσ' : σ < τ := hσ
      refine ⟨Real.exp ((σ - τ) / 2), ⟨Real.exp_pos _, ?_⟩, ?_⟩
      · rw [Real.exp_lt_one_iff]
        linarith
      · show τ + 2 * Real.log (Real.exp ((σ - τ) / 2)) = σ
        rw [Real.log_exp]
        ring
  have hderiv : ∀ l ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt (fun l : ℝ => τ + 2 * Real.log l) (2 * l⁻¹) (Ioo 0 1) l := by
    intro l hl
    exact (((Real.hasDerivAt_log hl.1.ne').const_mul 2).const_add τ).hasDerivWithinAt
  have hinj : Set.InjOn (fun l : ℝ => τ + 2 * Real.log l) (Ioo 0 1) := by
    intro a ha b hb hab
    have hab' : τ + 2 * Real.log a = τ + 2 * Real.log b := hab
    have h1 : Real.log a = Real.log b := by linarith
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr ha.1) (Set.mem_Ioi.mpr hb.1) h1
  have hCV : ∫ σ in Iio τ, pdCovG ν μ τ x (oldPhys R c g) i σ =
      ∫ l in Ioo (0 : ℝ) 1, |2 * l⁻¹| • pdCovG ν μ τ x (oldPhys R c g) i (τ + 2 * Real.log l) := by
    rw [← himg]
    exact integral_image_eq_integral_abs_deriv_smul (f := fun l : ℝ => τ + 2 * Real.log l)
      (f' := fun l : ℝ => 2 * l⁻¹) measurableSet_Ioo hderiv hinj _
  -- Step 4: the pointwise identity on `(0,1)`.
  have hpt : ∀ l ∈ Ioo (0 : ℝ) 1, |2 * l⁻¹| • pdCovG ν μ τ x (oldPhys R c g) i (τ + 2 * Real.log l) =
      (-2 * (l ^ (2 * μ + 2) - l ^ (2 * μ + 4))) *
        ∫ z : Space, ∑ j : Fin 3, ∑ k : Fin 3,
          T8_1.Gm k i j (ν * (1 - l ^ 2), x - l • z) * oldPhys R c g (τ + 2 * Real.log l) z j k := by
    intro l hl
    have hl0 : 0 < l := hl.1
    have hl1 : l < 1 := hl.2
    have hGl : pdCovG ν μ τ x (oldPhys R c g) i (τ + 2 * Real.log l) =
        ∫ z : Space, -(l ^ (2 * μ + 3) - l ^ (2 * μ + 5)) * ∑ j : Fin 3, ∑ k : Fin 3,
          T8_1.Gm k i j (ν * (1 - l ^ 2), x - l • z) * oldPhys R c g (τ + 2 * Real.log l) z j k := by
      unfold pdCovG
      congr 1
      funext z
      exact xKer_comp_gm ν μ τ i (hsupp := hsupp) hl0 hl1
    have hpos : 0 < 2 * l⁻¹ := mul_pos two_pos (inv_pos.2 hl0)
    have hkey : |2 * l⁻¹| * (-(l ^ (2 * μ + 3) - l ^ (2 * μ + 5))) =
        -2 * (l ^ (2 * μ + 2) - l ^ (2 * μ + 4)) := by
      have h3 : l ^ (2 * μ + 3) = l ^ (2 * μ + 2) * l := by
        rw [show 2 * μ + 3 = (2 * μ + 2) + 1 by ring, Real.rpow_add_one hl0.ne']
      have h5 : l ^ (2 * μ + 5) = l ^ (2 * μ + 4) * l := by
        rw [show 2 * μ + 5 = (2 * μ + 4) + 1 by ring, Real.rpow_add_one hl0.ne']
      rw [abs_of_pos hpos, h3, h5]
      field_simp
    rw [hGl, smul_eq_mul, integral_const_mul, ← mul_assoc, hkey, mul_assoc]
  -- Assemble.
  rw [hLHS, hRHS, hCV]
  refine setIntegral_congr_fun measurableSet_Ioo fun l hl => ?_
  exact (hpt l hl).symm

end UnforcedLeray.Short.PartIIIb.Concrete

end
