import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_dec

/-!
# `pepsC0SliceDivFreeZero` (task `PartIII-b:C/flatset/col/7/1/1/2/4/2/3/2/2/2`)

Source `the November 2 reference manuscript` 1650-1656, 1676.

Strategy: for a.e. `σ` the integrand `Σ_i (cgrad 0 Φt)_i(σ,·) Ψ(σ,·)_i` equals
`pd 0 ψ · Ψ_0 + pd 1 ψ · Ψ_1` with `ψ := Φt(σ,·)` a `B0579.IsCylTest`; the strip `(0,c] × ℝ` is
moved to the centred cell by `Cyl.integral_strip_eq_cell` (periodicity in `q`), `Ψ(σ,·) = P0C Φ_σ`
a.e. on the cell, and `IIIa.p0DivFreeC` gives zero.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (P0C)

theorem pepsC0SliceDivFreeZero : PepsC0SliceDivFreeZero := by
  intro c hc Φt Φ Ψ hper σ _hσ hΨ
  set ψ : ℝ × ℝ → ℝ := fun y => Φt.1 (σ, y) with hψdef
  have hψ : UnforcedLeray.B0579.IsCylTest c ψ := by
    refine ⟨?_, ?_, ?_⟩
    · exact Φt.2.smooth.comp (contDiff_const.prodMk contDiff_id)
    · intro x
      exact Φt.2.periodic (σ, x.1, x.2)
    · obtain ⟨_, _, L, _, hb⟩ := Φt.2.band
      refine ⟨L, fun x hx => ?_⟩
      by_contra hne
      exact absurd (hb (σ, x) hne).2 (not_le.mpr hx)
  -- partial derivatives of the profile test in the slice are the cylinder partials of `ψ`
  have hpd0 : ∀ x : ℝ × ℝ, UnforcedLeray.Axi.dQ Φt.1 (σ, x) = UnforcedLeray.B0579.pd 0 ψ x := by
    intro x
    have hd : HasFDerivAt Φt.1 (fderiv ℝ Φt.1 (σ, x)) (σ, x) :=
      ((Φt.2.smooth.differentiable (by simp)) (σ, x)).hasFDerivAt
    have hg : HasFDerivAt (fun y : ℝ × ℝ => (σ, y)) (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) x :=
      hasFDerivAt_prodMk_right σ x
    have hcomp := hd.comp x hg
    have hfun : ψ = Φt.1 ∘ (fun y : ℝ × ℝ => (σ, y)) := rfl
    rw [UnforcedLeray.Axi.dQ, UnforcedLeray.B0579.pd, hfun, hcomp.fderiv]
    simp [UnforcedLeray.B0579.dir]
  have hpd1 : ∀ x : ℝ × ℝ, UnforcedLeray.Axi.dEta Φt.1 (σ, x) = UnforcedLeray.B0579.pd 1 ψ x := by
    intro x
    have hd : HasFDerivAt Φt.1 (fderiv ℝ Φt.1 (σ, x)) (σ, x) :=
      ((Φt.2.smooth.differentiable (by simp)) (σ, x)).hasFDerivAt
    have hg : HasFDerivAt (fun y : ℝ × ℝ => (σ, y)) (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) x :=
      hasFDerivAt_prodMk_right σ x
    have hcomp := hd.comp x hg
    have hfun : ψ = Φt.1 ∘ (fun y : ℝ × ℝ => (σ, y)) := rfl
    rw [UnforcedLeray.Axi.dEta, UnforcedLeray.B0579.pd, hfun, hcomp.fderiv]
    simp [UnforcedLeray.B0579.dir]
  have hc0 : ∀ x : ℝ × ℝ,
      UnforcedLeray.Short.PartIIa.cgrad 0 Φt.1 (σ, x) 0
        = ((UnforcedLeray.B0579.pd 0 ψ x : ℝ) : ℂ) := by
    intro x
    simp only [UnforcedLeray.Short.PartIIa.cgrad, UnforcedLeray.B0226.Deps_zero, hpd0 x]
    simp
  have hc1 : ∀ x : ℝ × ℝ,
      UnforcedLeray.Short.PartIIa.cgrad 0 Φt.1 (σ, x) 1
        = ((UnforcedLeray.B0579.pd 1 ψ x : ℝ) : ℂ) := by
    intro x
    simp only [UnforcedLeray.Short.PartIIa.cgrad, hpd1 x]
    simp
  set G : ℝ × ℝ → ℂ := fun x =>
    ∑ i : Fin 2, UnforcedLeray.Short.PartIIa.cgrad 0 Φt.1 (σ, x) i * Ψ (σ, x) i with hGdef
  have hG : ∀ x : ℝ × ℝ, G x
      = ((UnforcedLeray.B0579.pd 0 ψ x : ℝ) : ℂ) * Ψ (σ, x) 0
        + ((UnforcedLeray.B0579.pd 1 ψ x : ℝ) : ℂ) * Ψ (σ, x) 1 := by
    intro x
    simp only [hGdef]
    rw [Fin.sum_univ_two, hc0, hc1]
  have hGp : UnforcedLeray.Cyl.IsPeriodic c G := by
    rintro ⟨q, η⟩
    have h0 : UnforcedLeray.B0579.pd 0 ψ (q + c, η) = UnforcedLeray.B0579.pd 0 ψ (q, η) :=
      (hψ.pd 0).periodic (q, η)
    have h1 : UnforcedLeray.B0579.pd 1 ψ (q + c, η) = UnforcedLeray.B0579.pd 1 ψ (q, η) :=
      (hψ.pd 1).periodic (q, η)
    show G (q + c, η) = G (q, η)
    rw [hG, hG, h0, h1, hper σ q η]
  have hshift : ∫ x in Ico 0 (0 + c) ×ˢ (univ : Set ℝ), G x
      = ∫ x in UnforcedLeray.Cyl.cell c, G x :=
    UnforcedLeray.Cyl.integral_strip_eq_cell hc hGp 0
  have hset : ∫ x in stripSet c, G x = ∫ x in Ico 0 (0 + c) ×ˢ (univ : Set ℝ), G x := by
    apply setIntegral_congr_set
    unfold stripSet
    rw [zero_add]
    exact Measure.set_prod_ae_eq Ico_ae_eq_Ioc.symm (ae_eq_refl univ)
  have hcell : UnforcedLeray.Cyl.cell c = UnforcedLeray.B0579.cell c := by
    unfold UnforcedLeray.Cyl.cell UnforcedLeray.B0579.cell
    rw [neg_div]
  have hΨ' : (fun y => Ψ (σ, y)) =ᵐ[volume.restrict (UnforcedLeray.B0579.cell c)]
      P0C c (fun y => Φ (σ, y)) := by
    unfold UnforcedLeray.Cyl.cellμ at hΨ
    rw [hcell] at hΨ
    exact hΨ
  calc ∫ x in stripSet c, G x
      = ∫ x in Ico 0 (0 + c) ×ˢ (univ : Set ℝ), G x := hset
    _ = ∫ x in UnforcedLeray.Cyl.cell c, G x := hshift
    _ = ∫ x in UnforcedLeray.B0579.cell c, G x := by rw [hcell]
    _ = ∫ x in UnforcedLeray.B0579.cell c,
          (P0C c (fun y => Φ (σ, y)) x 0 * ((UnforcedLeray.B0579.pd 0 ψ x : ℝ) : ℂ)
            + P0C c (fun y => Φ (σ, y)) x 1 * ((UnforcedLeray.B0579.pd 1 ψ x : ℝ) : ℂ)) := by
        apply integral_congr_ae
        filter_upwards [hΨ'] with x hx
        have hx' : Ψ (σ, x) = P0C c (fun y => Φ (σ, y)) x := hx
        rw [hG x, hx']
        ring
    _ = 0 := UnforcedLeray.Short.IIIa.p0DivFreeC c hc (fun y => Φ (σ, y)) ψ hψ

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
