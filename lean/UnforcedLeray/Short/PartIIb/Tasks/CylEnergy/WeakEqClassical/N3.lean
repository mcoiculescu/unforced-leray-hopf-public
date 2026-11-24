import UnforcedLeray.Short.PartIIb.Sub.T22_2
import UnforcedLeray.Verify.B0579Check

/-!


Two functions in `L²(cellMeasure c m)` with equal pairings against every `IsCylTest c` test agree
a.e. on the cell. The proof reduces to `B0579Check.eq_zero_of_forall_test` applied to the
`X c m` element `f₁ - f₂`; integrability of the pairings comes from `B0579.integrableOn_mul_neg`
(the `X_m × X_{-m}` pairing) applied to the test function as an element of `X_{-m}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.B0579

namespace UnforcedLeray.Short.IIb

/-- Integrability of `g · φ` on the cell for `g ∈ L²(cellMeasure c m)` and a test `φ`. -/
theorem cylFund_integrableOn_test {c m : ℝ} {g φ : Plane → ℝ}
    (hg : MemLp g 2 (cellMeasure c m)) (hφ : IsCylTest c φ) :
    IntegrableOn (fun x => g x * φ x) (cell c) := by
  have h := integrableOn_mul_neg c m (hg.toLp g) ((hφ.memLp (-m)).toLp φ)
  refine h.congr_fun_ae ?_
  filter_upwards [ac_cellMeasure c m |>.ae_le (MemLp.coeFn_toLp hg),
    ac_cellMeasure c (-m) |>.ae_le (MemLp.coeFn_toLp (hφ.memLp (-m)))] with x h1 h2
  rw [h1, h2]

/-- **Needed N3: fundamental lemma on the cell** (`CylFundLemma`). -/
theorem cylFundLemma : UnforcedLeray.Short.IIb.CylFundLemma := by
  intro c m hc hm g₁ g₂ h1 h2 hpair
  have hF : (h1.toLp g₁ - h2.toLp g₂ : X c m) = 0 := by
    apply UnforcedLeray.B0579Check.eq_zero_of_forall_test hc
    intro φ hφ
    have hae : ∀ᵐ x ∂(volume.restrict (cell c)),
        ((h1.toLp g₁ - h2.toLp g₂ : X c m) : Plane → ℝ) x = g₁ x - g₂ x := by
      apply (ac_cellMeasure c m).ae_le
      filter_upwards [Lp.coeFn_sub (h1.toLp g₁) (h2.toLp g₂), MemLp.coeFn_toLp h1,
        MemLp.coeFn_toLp h2] with x e a b
      rw [e, Pi.sub_apply, a, b]
    calc ∫ x in cell c, ((h1.toLp g₁ - h2.toLp g₂ : X c m) : Plane → ℝ) x * φ x
        = ∫ x in cell c, (g₁ x * φ x - g₂ x * φ x) := by
          refine integral_congr_ae ?_
          filter_upwards [hae] with x hx
          rw [hx]
          ring
      _ = (∫ x in cell c, g₁ x * φ x) - ∫ x in cell c, g₂ x * φ x :=
          integral_sub (cylFund_integrableOn_test h1 hφ) (cylFund_integrableOn_test h2 hφ)
      _ = 0 := by rw [hpair φ hφ, sub_self]
  have hz2 : ∀ᵐ x ∂(cellMeasure c m), g₁ x = g₂ x := by
    have hz : ∀ᵐ x ∂(cellMeasure c m),
        ((h1.toLp g₁ - h2.toLp g₂ : X c m) : Plane → ℝ) x = 0 := by
      rw [hF]
      filter_upwards [Lp.coeFn_zero ℝ 2 (cellMeasure c m)] with x hx
      exact hx.trans rfl
    filter_upwards [hz, Lp.coeFn_sub (h1.toLp g₁) (h2.toLp g₂), MemLp.coeFn_toLp h1,
      MemLp.coeFn_toLp h2] with x hx e a b
    rw [e, Pi.sub_apply, a, b] at hx
    exact sub_eq_zero.mp hx
  exact (ac_cellMeasure c m).ae_le hz2

end UnforcedLeray.Short.IIb
