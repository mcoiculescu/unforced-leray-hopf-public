import UnforcedLeray.Short.PartIIa.Sub.R02_6

/-!
# Part II-a, task `PartII-a:R02/MeanStress/HmeanMulFluct`: the cell algebra of the mean stress

Source of record: `the November 2 reference manuscript`, lines 397-404 (`sct:mean`,
`g = \overline{v_1 v_2}`, `\overline{v_2} = 0`).
The statement `HmeanMulFluct` is defined in `Short/PartII-a/Sub/R02_6.lean`.

Route. Fix `c > 0`, `η`, and continuous `f, g` on the plane with `\bar g(η) = 0`. Put `A = \bar f(η)`.
* `\tilde g(q, η) = g(q, η) - \bar g(η) = g(q, η)`.
* `\tilde f(q, η) = f(q, η) - A`, because `A` does not depend on `q`.
So `\tilde f \tilde g (q, η) = f(q, η) g(q, η) - A g(q, η)` pointwise. The cell integral of
`g(·, η)` is `c \bar g(η) = 0`, so the term `A g` integrates to zero and the two cell averages agree.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.Short.PartI (hmean hfluct)

theorem hmeanMulFluct : UnforcedLeray.Short.PartIIa.HmeanMulFluct := by
  intro c η hc f g hf hg hgmean
  have hc0 : c ≠ 0 := ne_of_gt hc
  -- the cell integral of `g(·, η)` vanishes, since `\bar g(η) = c⁻¹ ∫ g = 0`
  have hgint : ∫ q in Ioc (-c / 2) (c / 2), g (q, η) = 0 := by
    have h : c⁻¹ • ∫ q in Ioc (-c / 2) (c / 2), g (q, η) = 0 := hgmean
    exact (smul_eq_zero.mp h).resolve_left (inv_ne_zero hc0)
  -- pointwise: the fluctuation of `g` is `g`, the fluctuation of `f` is `f - A`
  have hf' : ∀ q : ℝ, hfluct c f (q, η) = f (q, η) - hmean c f η := fun q => rfl
  have hg' : ∀ q : ℝ, hfluct c g (q, η) = g (q, η) := by
    intro q
    show g (q, η) - hmean c g η = g (q, η)
    rw [hgmean, sub_zero]
  have hpt : ∀ q : ℝ, hfluct c f (q, η) * hfluct c g (q, η)
      = f (q, η) * g (q, η) - hmean c f η * g (q, η) := by
    intro q
    rw [hf' q, hg' q]
    ring
  -- integrability on the cell: the slices `q ↦ f(q, η)`, `q ↦ g(q, η)` are continuous
  have hpair : Continuous fun q : ℝ => (q, η) := continuous_id.prodMk continuous_const
  have hfη : Continuous fun q : ℝ => f (q, η) := hf.comp hpair
  have hgη : Continuous fun q : ℝ => g (q, η) := hg.comp hpair
  have hA : Continuous fun _ : ℝ => hmean c f η := continuous_const
  have hFi : IntegrableOn (fun q : ℝ => f (q, η) * g (q, η)) (Ioc (-c / 2) (c / 2)) :=
    (hfη.mul hgη).integrableOn_Ioc
  have hGi : IntegrableOn (fun q : ℝ => hmean c f η * g (q, η)) (Ioc (-c / 2) (c / 2)) :=
    (hA.mul hgη).integrableOn_Ioc
  -- the cell integral of the fluctuation product equals the cell integral of `f g`
  have hL : ∫ q in Ioc (-c / 2) (c / 2), hfluct c f (q, η) * hfluct c g (q, η)
      = ∫ q in Ioc (-c / 2) (c / 2), f (q, η) * g (q, η) := by
    simp only [hpt]
    rw [integral_sub hFi hGi, integral_const_mul, hgint, mul_zero, sub_zero]
  show c⁻¹ • ∫ q in Ioc (-c / 2) (c / 2), f (q, η) * g (q, η)
      = c⁻¹ • ∫ q in Ioc (-c / 2) (c / 2), hfluct c f (q, η) * hfluct c g (q, η)
  rw [hL]

end UnforcedLeray.Short.PartIIa
