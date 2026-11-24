import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.TimeJets.Defs
import UnforcedLeray.Units.B0579

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- A smooth periodic coefficient times a cylinder test is a cylinder test. -/
theorem cw_cyl_mul_coeff {c : ℝ} {a : ℝ × ℝ → ℝ} (ha : ContDiff ℝ ∞ a)
    (hap : ∀ x : ℝ × ℝ, a (x.1 + c, x.2) = a x) {ψ : ℝ × ℝ → ℝ}
    (hψ : UnforcedLeray.B0579.IsCylTest c ψ) :
    UnforcedLeray.B0579.IsCylTest c (fun x => a x * ψ x) where
  smooth := ha.mul hψ.smooth
  periodic x := by
    show a (x.1 + c, x.2) * ψ (x.1 + c, x.2) = a x * ψ x
    rw [hap x, hψ.periodic x]
  band := by
    obtain ⟨R, hR⟩ := hψ.band
    exact ⟨R, fun x hx => by show a x * ψ x = 0; rw [hR x hx, mul_zero]⟩

/-- The `x₁`-derivative of a smooth periodic function is smooth and periodic. -/
theorem cw_pd_smooth_periodic {c : ℝ} {A : ℝ × ℝ → ℝ} (hA : ContDiff ℝ ∞ A)
    (hAp : ∀ x : ℝ × ℝ, A (x.1 + c, x.2) = A x) (j : Fin 2) :
    ContDiff ℝ ∞ (UnforcedLeray.B0579.pd j A) ∧
      ∀ x : ℝ × ℝ, UnforcedLeray.B0579.pd j A (x.1 + c, x.2) = UnforcedLeray.B0579.pd j A x := by
  refine ⟨UnforcedLeray.B0579.contDiff_pd hA j, fun x => ?_⟩
  have hfun : (fun y : ℝ × ℝ => A (y + ((c, 0) : ℝ × ℝ))) = A := by
    funext y
    have hy : y + ((c, 0) : ℝ × ℝ) = (y.1 + c, y.2) := by ext <;> simp
    rw [hy]
    exact hAp y
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := A) (x := x) ((c, 0) : ℝ × ℝ)
  rw [hfun] at h
  have hx : x + ((c, 0) : ℝ × ℝ) = (x.1 + c, x.2) := by ext <;> simp
  rw [hx] at h
  unfold UnforcedLeray.B0579.pd
  rw [← h]

/-- The product rule for `pd` of a product of two differentiable functions. -/
theorem cw_pd_mul {A ψ : ℝ × ℝ → ℝ} (hA : Differentiable ℝ A) (hψ : Differentiable ℝ ψ)
    (j : Fin 2) (x : ℝ × ℝ) :
    UnforcedLeray.B0579.pd j (fun y => A y * ψ y) x =
      UnforcedLeray.B0579.pd j A x * ψ x + A x * UnforcedLeray.B0579.pd j ψ x := by
  unfold UnforcedLeray.B0579.pd
  rw [show (fun y : ℝ × ℝ => A y * ψ y) = A * ψ from rfl, fderiv_mul (hA x) (hψ x)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    Pi.mul_apply]
  ring

/-- `(t^(e/2))² = t^e` for `t > 0`. -/
theorem cw_sq_rpow_half {t : ℝ} (ht : 0 < t) (e : ℝ) : (t ^ (e / 2)) ^ 2 = t ^ e := by
  rw [sq, ← Real.rpow_add ht, show e / 2 + e / 2 = e by ring]

/-- The integrability of `jb^m ‖G‖²` on the cell (the weighted square). -/
theorem cw_tb {c m : ℝ} {G : ℝ × ℝ → ℂ}
    (hG : MemLp G 2 (UnforcedLeray.B0579.cellMeasure c m)) :
    Integrable (fun x => UnforcedLeray.B0579.jb x ^ m * ‖G x‖ ^ 2)
      (volume.restrict (UnforcedLeray.B0579.cell c)) := by
  have hI : Integrable (fun x => ‖G x‖ ^ (2 : ℝ≥0∞).toReal)
      (UnforcedLeray.B0579.cellMeasure c m) :=
    hG.integrable_norm_rpow (by norm_num) (by norm_num)
  unfold UnforcedLeray.B0579.cellMeasure at hI
  rw [integrable_withDensity_iff_integrable_smul (UnforcedLeray.B0579.measurable_density m)] at hI
  refine hI.congr (Eventually.of_forall fun x => ?_)
  simp only [NNReal.smul_def, UnforcedLeray.B0579.coe_density, ENNReal.toReal_ofNat,
    Real.rpow_two, smul_eq_mul]

/-- **Integrability against a cylinder test.** An `L²(C_c, ⟨x⟩^{2m})` field times a test
function, `h` a cylinder test, is integrable on the cell. -/
theorem cw_integrable {c m : ℝ} {g : ℝ × ℝ → ℂ}
    (hg : MemLp g 2 (UnforcedLeray.B0579.cellMeasure c m))
    {h : ℝ × ℝ → ℝ} (hh : UnforcedLeray.B0579.IsCylTest c h) :
    IntegrableOn (fun x => g x * (h x : ℂ)) (UnforcedLeray.B0579.cell c) := by
  obtain ⟨R, hR⟩ := hh.vanish
  obtain ⟨C, hC⟩ := (UnforcedLeray.B0579.isCompact_box c R).exists_bound_of_continuousOn
    hh.continuous.continuousOn
  have hK0 : ∀ x ∈ UnforcedLeray.B0579.cell c, |h x| ≤ max C 0 := by
    intro x hx
    by_cases hxb : x ∈ UnforcedLeray.B0579.box c R
    · have h1 := hC x hxb
      rw [Real.norm_eq_abs] at h1
      exact h1.trans (le_max_left _ _)
    · rw [hR x hx hxb, abs_zero]
      exact le_max_right _ _
  have hK : 0 ≤ max C 0 := le_max_right _ _
  have hI : Integrable (fun x => UnforcedLeray.B0579.jb x ^ m * ‖g x‖ ^ 2)
      (volume.restrict (UnforcedLeray.B0579.cell c)) := cw_tb hg
  have hJ : IntegrableOn (fun x => |h x| * UnforcedLeray.B0579.jb x ^ (-m))
      (UnforcedLeray.B0579.cell c) := by
    refine UnforcedLeray.B0579.integrableOn_cell_of_continuous
      ((hh.continuous.abs).mul (UnforcedLeray.B0579.continuous_jb_rpow (-m)))
      (UnforcedLeray.B0579.isCompact_box c R) ?_
    intro x hx hxb
    rw [hR x hx hxb, abs_zero, zero_mul]
  have hD : Integrable (fun x => (1 / 2 : ℝ) * (max C 0 * (UnforcedLeray.B0579.jb x ^ m *
      ‖g x‖ ^ 2) + |h x| * UnforcedLeray.B0579.jb x ^ (-m)))
      (volume.restrict (UnforcedLeray.B0579.cell c)) :=
    ((hI.const_mul (max C 0)).add hJ).const_mul (1 / 2)
  refine hD.mono' ?_ ?_
  · exact (hg.aestronglyMeasurable.mono_ac
      (UnforcedLeray.B0579.ac_cellMeasure c m)).mul
      (Complex.continuous_ofReal.comp hh.continuous).aestronglyMeasurable
  · refine (ae_restrict_mem (UnforcedLeray.B0579.measurableSet_cell c)).mono fun x hx => ?_
    show ‖g x * (h x : ℂ)‖ ≤ _
    have hjb := UnforcedLeray.B0579.jb_pos x
    have hp : UnforcedLeray.B0579.jb x ^ (m / 2) * UnforcedLeray.B0579.jb x ^ (-m / 2) = 1 := by
      rw [← Real.rpow_add hjb, show m / 2 + -m / 2 = 0 by ring, Real.rpow_zero]
    have hp2 : (UnforcedLeray.B0579.jb x ^ (m / 2)) ^ 2 = UnforcedLeray.B0579.jb x ^ m :=
      cw_sq_rpow_half hjb m
    have hq2 : (UnforcedLeray.B0579.jb x ^ (-m / 2)) ^ 2 = UnforcedLeray.B0579.jb x ^ (-m) :=
      cw_sq_rpow_half hjb (-m)
    have hnorm : ‖g x * (h x : ℂ)‖ = ‖g x‖ * |h x| := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm]
    have hb : 0 ≤ |h x| := abs_nonneg _
    have hbK : |h x| ≤ max C 0 := hK0 x hx
    have key : 2 * (‖g x‖ * |h x|) ≤
        |h x| * (UnforcedLeray.B0579.jb x ^ m * ‖g x‖ ^ 2) + |h x| * UnforcedLeray.B0579.jb x ^ (-m) := by
      rw [← hp2, ← hq2]
      have e : |h x| * (UnforcedLeray.B0579.jb x ^ (m / 2) * ‖g x‖ -
          UnforcedLeray.B0579.jb x ^ (-m / 2)) ^ 2 =
          |h x| * ((UnforcedLeray.B0579.jb x ^ (m / 2)) ^ 2 * ‖g x‖ ^ 2) +
            |h x| * (UnforcedLeray.B0579.jb x ^ (-m / 2)) ^ 2 -
          2 * (‖g x‖ * |h x|) * (UnforcedLeray.B0579.jb x ^ (m / 2) *
            UnforcedLeray.B0579.jb x ^ (-m / 2)) := by ring
      rw [hp, mul_one] at e
      nlinarith [mul_nonneg hb (sq_nonneg (UnforcedLeray.B0579.jb x ^ (m / 2) * ‖g x‖ -
        UnforcedLeray.B0579.jb x ^ (-m / 2)))]
    have A2 : |h x| * (UnforcedLeray.B0579.jb x ^ m * ‖g x‖ ^ 2) ≤
        max C 0 * (UnforcedLeray.B0579.jb x ^ m * ‖g x‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hbK (by
        have := UnforcedLeray.B0579.jb_pos x
        positivity)
    linarith

/-- **The product rule for weak derivatives with a smooth periodic coefficient** (SP 3060:
the weak `c`-cell derivative of `A g` against a cylinder test; `A` smooth and `c`-periodic). The
pieces are cylinder tests (`A ψ`, `∂_jA ψ`, `A ∂_jψ`), integrability against them is
`cw_integrable`, and the identity is the weak formulation of `g` tested with `A ψ`. -/
theorem coeffWeakDeriv : CoeffWeakDeriv := by
  intro c m j A g g' hc hA hAp _hAb _hpdAb hg hg' hw
  obtain ⟨hw1, hw2⟩ := hw
  have hAdiff : Differentiable ℝ A := hA.differentiable (by simp)
  obtain ⟨hpdA_sm, hpdA_per⟩ := cw_pd_smooth_periodic hA hAp j
  refine ⟨fun ψ hψ => ⟨?_, ?_⟩, fun ψ hψ => ?_⟩
  · have I2 : IntegrableOn (fun x => g x * ((A x * UnforcedLeray.B0579.pd j ψ x : ℝ) : ℂ))
        (UnforcedLeray.B0579.cell c) :=
      cw_integrable hg (cw_cyl_mul_coeff hA hAp (hψ.pd j))
    refine I2.congr_fun (fun x _ => ?_) (UnforcedLeray.B0579.measurableSet_cell c)
    push_cast
    ring
  · have I1 : IntegrableOn (fun x => g x * ((UnforcedLeray.B0579.pd j A x * ψ x : ℝ) : ℂ))
        (UnforcedLeray.B0579.cell c) :=
      cw_integrable hg (cw_cyl_mul_coeff hpdA_sm hpdA_per hψ)
    have I3 : IntegrableOn (fun x => g' x * ((A x * ψ x : ℝ) : ℂ))
        (UnforcedLeray.B0579.cell c) :=
      cw_integrable hg' (cw_cyl_mul_coeff hA hAp hψ)
    refine (I1.add I3).congr_fun (fun x _ => ?_) (UnforcedLeray.B0579.measurableSet_cell c)
    simp only [Pi.add_apply]
    push_cast
    ring
  · beta_reduce
    have hψdiff : Differentiable ℝ ψ := hψ.differentiable
    have hχ := cw_cyl_mul_coeff hA hAp hψ
    have I1 : IntegrableOn (fun x => g x * ((UnforcedLeray.B0579.pd j A x * ψ x : ℝ) : ℂ))
        (UnforcedLeray.B0579.cell c) :=
      cw_integrable hg (cw_cyl_mul_coeff hpdA_sm hpdA_per hψ)
    have I2 : IntegrableOn (fun x => g x * ((A x * UnforcedLeray.B0579.pd j ψ x : ℝ) : ℂ))
        (UnforcedLeray.B0579.cell c) :=
      cw_integrable hg (cw_cyl_mul_coeff hA hAp (hψ.pd j))
    have I3 : IntegrableOn (fun x => g' x * ((A x * ψ x : ℝ) : ℂ))
        (UnforcedLeray.B0579.cell c) :=
      cw_integrable hg' hχ
    have hw2' : ∫ x in UnforcedLeray.B0579.cell c,
        g x * ((UnforcedLeray.B0579.pd j (fun y => A y * ψ y) x : ℝ) : ℂ) =
        -∫ x in UnforcedLeray.B0579.cell c, g' x * ((A x * ψ x : ℝ) : ℂ) :=
      hw2 _ hχ
    have hsplit : ∫ x in UnforcedLeray.B0579.cell c,
        g x * ((UnforcedLeray.B0579.pd j (fun y => A y * ψ y) x : ℝ) : ℂ) =
        (∫ x in UnforcedLeray.B0579.cell c,
          g x * ((UnforcedLeray.B0579.pd j A x * ψ x : ℝ) : ℂ)) +
        ∫ x in UnforcedLeray.B0579.cell c,
          g x * ((A x * UnforcedLeray.B0579.pd j ψ x : ℝ) : ℂ) := by
      rw [← integral_add I1 I2]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      show g x * ((UnforcedLeray.B0579.pd j (fun y => A y * ψ y) x : ℝ) : ℂ) = _
      rw [cw_pd_mul hAdiff hψdiff j x]
      push_cast
      ring
    have key : (∫ x in UnforcedLeray.B0579.cell c,
          g x * ((UnforcedLeray.B0579.pd j A x * ψ x : ℝ) : ℂ)) +
        (∫ x in UnforcedLeray.B0579.cell c,
          g x * ((A x * UnforcedLeray.B0579.pd j ψ x : ℝ) : ℂ)) =
        -∫ x in UnforcedLeray.B0579.cell c, g' x * ((A x * ψ x : ℝ) : ℂ) :=
      hsplit.symm.trans hw2'
    have hsum : ∫ x in UnforcedLeray.B0579.cell c,
        ((UnforcedLeray.B0579.pd j A x : ℂ) * g x + (A x : ℂ) * g' x) * (ψ x : ℂ) =
        (∫ x in UnforcedLeray.B0579.cell c,
          g x * ((UnforcedLeray.B0579.pd j A x * ψ x : ℝ) : ℂ)) +
        ∫ x in UnforcedLeray.B0579.cell c, g' x * ((A x * ψ x : ℝ) : ℂ) := by
      rw [← integral_add I1 I3]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [Pi.add_apply]
      push_cast
      ring
    have hL : ∫ x in UnforcedLeray.B0579.cell c,
        (A x : ℂ) * g x * (UnforcedLeray.B0579.pd j ψ x : ℂ) =
        ∫ x in UnforcedLeray.B0579.cell c,
          g x * ((A x * UnforcedLeray.B0579.pd j ψ x : ℝ) : ℂ) := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      push_cast
      ring
    rw [hsum, hL]
    linear_combination key

end UnforcedLeray.Short.IIIa
