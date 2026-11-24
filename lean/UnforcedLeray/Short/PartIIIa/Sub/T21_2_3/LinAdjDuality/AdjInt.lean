import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.AdjWeakSmooth
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_3
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.MovingPhiH1.WeakFromSmooth

/-!
# Part III-a: integrability of the three integrands of the adjoint pairing (`adjWInt`)

Source of record: `the November 2 reference manuscript` (SP) lines 3052-3058.

`ψ` is a cylinder test vanishing for `|η| > R`, so every term of the form `continuous · ψ` is
integrable on the cell. `ladDt` and `ladChi` are continuous on the strip, so their products with `ψ`
are integrable. The third integrand is the difference of the continuous band function
`φ(ν Δψ - v·∇ψ)` and `adjIntegrand`, which is integrable by `IsAdjointWeak.integrable`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

/-- **Leaf** `adjWInt` (SP 3052-3058): integrability of the three integrands on the cell. -/
theorem adjWInt (m : ℝ) : AdjWInt m := by
  intro ν c tr t s g φ hctx ρ hρ ψ uψ hψ hu
  obtain ⟨_, _, ht, _, _, hA, hj⟩ := hctx
  have hρ0 : 0 < ρ := lt_of_le_of_lt ht hρ.1
  have hφs : ContDiff ℝ ∞ (φ ρ) := adjContDiff_slice hj (Ioo_subset_Ico_self hρ)
  obtain ⟨R, hR⟩ := hψ.band
  have hcell : B0579.cell c = UnforcedLeray.Cyl.cell c := by
    unfold B0579.cell UnforcedLeray.Cyl.cell
    rw [neg_div]
  -- the cell integrability of `f · ψ` for a continuous `f`
  have hband : ∀ f : ℝ × ℝ → ℂ, Continuous f → IntegrableOn (fun x => f x * (ψ x : ℂ)) (B0579.cell c) := by
    intro f hf
    have hv : UnforcedLeray.Cyl.VanishesOutside R (fun x => f x * (ψ x : ℂ)) :=
      fun x hx => by simp [hR x hx]
    rw [hcell]
    exact hv.integrableOn_cell (hf.mul (Complex.continuous_ofReal.comp hψ.continuous)) c
  -- the train velocity components are continuous at age `ρ`
  have hvR : ∀ j : Fin 2, Continuous fun x : ℝ × ℝ => tr.v ρ x j := by
    intro j
    have h : ContDiff ℝ ∞ (fun w : ℝ × ℝ => tr.v ρ w j) :=
      (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp
        (UnforcedLeray.B0238.contDiff_Vc tr hρ0.le)
    exact h.continuous
  have hv : ∀ j : Fin 2, Continuous fun x : ℝ × ℝ => ((tr.v ρ x j : ℝ) : ℂ) :=
    fun j => Complex.continuous_ofReal.comp (hvR j)
  -- continuity of `ladChi` at age `ρ`
  have hchi : Continuous (ladChi tr φ ρ) := by
    have hpd : ∀ (Φ : ℝ × ℝ → ℂ) (k : Fin 2), ContDiff ℝ ∞ Φ → ContDiff ℝ ∞ (pdCx k Φ) := by
      intro Φ k hΦ
      exact (hΦ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hlap : Continuous (ladLapCx (φ ρ)) := by
      unfold ladLapCx
      exact (hpd _ 0 (hpd _ 0 hφs)).continuous.add (hpd _ 1 (hpd _ 1 hφs)).continuous
    have htr : Continuous (ladTransport tr ρ (φ ρ)) := by
      unfold ladTransport
      exact ((hv 0).mul (hpd _ 0 hφs).continuous).add ((hv 1).mul (hpd _ 1 hφs).continuous)
    have e : ladChi tr φ ρ = fun x => ladDt φ ρ x + (ν : ℂ) * ladLapCx (φ ρ) x +
        ladTransport tr ρ (φ ρ) x := rfl
    rw [e]
    exact ((continuous_ladDt hj hρ).add (continuous_const.mul hlap)).add htr
  -- the derivatives of the test function vanish outside the band
  have hpdz : ∀ j : Fin 2, ∀ x : ℝ × ℝ, R < |x.2| → B0579.pd j ψ x = 0 := by
    intro j x hx
    show fderiv ℝ ψ x (B0579.dir j) = 0
    exact mpVanishFderiv hR (B0579.dir j) x hx
  have hlapz : ∀ x : ℝ × ℝ, R < |x.2| → lapP ψ x = 0 := by
    intro x hx
    unfold lapP
    have h1 : B0579.pd 0 (B0579.pd 0 ψ) x = 0 := by
      show fderiv ℝ (B0579.pd 0 ψ) x (B0579.dir 0) = 0
      exact mpVanishFderiv (fun y hy => hpdz 0 y hy) (B0579.dir 0) x hx
    have h2 : B0579.pd 1 (B0579.pd 1 ψ) x = 0 := by
      show fderiv ℝ (B0579.pd 1 ψ) x (B0579.dir 1) = 0
      exact mpVanishFderiv (fun y hy => hpdz 1 y hy) (B0579.dir 1) x hx
    rw [h1, h2, add_zero]
  -- the band function `φ (ν Δψ - v·∇ψ)`
  have hGc : Continuous (fun x : ℝ × ℝ => φ ρ x * ((ν * lapP ψ x -
      (tr.v ρ x 0 * B0579.pd 0 ψ x + tr.v ρ x 1 * B0579.pd 1 ψ x) : ℝ) : ℂ)) := by
    have hlapC : Continuous (lapP ψ) := by
      unfold lapP
      exact ((hψ.pd 0).pd 0).continuous.add ((hψ.pd 1).pd 1).continuous
    have hreal : Continuous (fun x : ℝ × ℝ => ν * lapP ψ x -
        (tr.v ρ x 0 * B0579.pd 0 ψ x + tr.v ρ x 1 * B0579.pd 1 ψ x)) :=
      (continuous_const.mul hlapC).sub
        (((hvR 0).mul (hψ.pd 0).continuous).add ((hvR 1).mul (hψ.pd 1).continuous))
    exact (hφs.continuous).mul (Complex.continuous_ofReal.comp hreal)
  have hGv : UnforcedLeray.Cyl.VanishesOutside R (fun x : ℝ × ℝ => φ ρ x * ((ν * lapP ψ x -
      (tr.v ρ x 0 * B0579.pd 0 ψ x + tr.v ρ x 1 * B0579.pd 1 ψ x) : ℝ) : ℂ)) := by
    intro x hx
    simp [hlapz x hx, hpdz 0 x hx, hpdz 1 x hx]
  have hGint : IntegrableOn (fun x : ℝ × ℝ => φ ρ x * ((ν * lapP ψ x -
      (tr.v ρ x 0 * B0579.pd 0 ψ x + tr.v ρ x 1 * B0579.pd 1 ψ x) : ℝ) : ℂ)) (B0579.cell c) := by
    rw [hcell]
    exact hGv.integrableOn_cell hGc c
  -- the third integrand is the difference of `G` and the integrable `adjIntegrand`
  have hadj := hA.integrable ψ uψ hψ hu ρ (Ioo_subset_Icc_self hρ)
  refine ⟨hband _ (continuous_ladDt hj hρ), hband _ hchi, ?_⟩
  refine (hGint.sub hadj).congr_fun (fun x _ => ?_) (B0579.measurableSet_cell c)
  simp only [Pi.sub_apply, adjIntegrand]
  push_cast
  ring

end UnforcedLeray.Short.IIIa
