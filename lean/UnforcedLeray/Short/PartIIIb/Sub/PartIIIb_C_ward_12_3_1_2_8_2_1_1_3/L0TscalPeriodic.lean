import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_1_3

/-!
# `PartIII-b:C/ward/12/3/1/2/8/2/1/1/3`: periodicity of `L0Tscal`

Source `the November 2 reference manuscript`
lines 1393-1400, 1409-1412.  Proves `l0TscalPeriodic` (the Prop `L0TscalPeriodic` of the parent
module): if the smooth `ψ` is `P`-periodic in `τ`, then `L0Tscal ν ψ` is `P`-periodic.  The
operators `∂_τ`, `∂_{y_j}`, `y·∇`, `Δ` are built from fderivatives in the directions `(1,0)` and
`(0,e_j)`, and a translation `p ↦ p + (P,0)` leaves the fderiv of a periodic function invariant.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.L0TscalPeriodicAux

open UnforcedLeray.PhaseSpace

/-- The fderiv of a function invariant under translation by `c` is invariant under `c`. -/
theorem fderiv_shift_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : ℝ × UnforcedLeray.Space → F} {c : ℝ × UnforcedLeray.Space}
    (hG : ∀ p, G (p + c) = G p) (p : ℝ × UnforcedLeray.Space) :
    fderiv ℝ G (p + c) = fderiv ℝ G p := by
  have h1 : (fun q => G (q + c)) = G := funext hG
  have h2 := fderiv_comp_add_right (𝕜 := ℝ) (f := G) c (x := p)
  rw [h1] at h2
  exact h2.symm

theorem dτ_shift {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : ℝ × UnforcedLeray.Space → F} {c : ℝ × UnforcedLeray.Space}
    (hG : ∀ p, G (p + c) = G p) (p : ℝ × UnforcedLeray.Space) :
    dτ G (p + c) = dτ G p := by
  simp only [dτ]
  rw [fderiv_shift_eq hG p]

theorem dy_shift {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : ℝ × UnforcedLeray.Space → F} {c : ℝ × UnforcedLeray.Space}
    (hG : ∀ p, G (p + c) = G p) (j : Fin 3) (p : ℝ × UnforcedLeray.Space) :
    dy j G (p + c) = dy j G p := by
  simp only [dy]
  rw [fderiv_shift_eq hG p]

theorem lapT_shift {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : ℝ × UnforcedLeray.Space → F} {c : ℝ × UnforcedLeray.Space} (hc : c.2 = 0)
    (hG : ∀ p, G (p + c) = G p) (p : ℝ × UnforcedLeray.Space) :
    lapT G (p + c) = lapT G p := by
  simp only [lapT]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact dy_shift (G := dy j G) (c := c) (fun q => dy_shift hG j q) j p

theorem radialT_shift {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : ℝ × UnforcedLeray.Space → F} {c : ℝ × UnforcedLeray.Space} (hc : c.2 = 0)
    (hG : ∀ p, G (p + c) = G p) (p : ℝ × UnforcedLeray.Space) :
    radialT G (p + c) = radialT G p := by
  simp only [radialT, Prod.snd_add, hc, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dy_shift hG j p]

end UnforcedLeray.Short.PartIIIb.Concrete.L0TscalPeriodicAux

open UnforcedLeray.PhaseSpace UnforcedLeray.Short.PartIIIb.Concrete.L0TscalPeriodicAux

theorem l0TscalPeriodic : UnforcedLeray.Short.PartIIIb.Concrete.L0TscalPeriodic := by
  intro P ν ψ _ hper τ y
  have hG : ∀ p : ℝ × UnforcedLeray.Space, ψ (p + ((P, 0) : ℝ × UnforcedLeray.Space)) = ψ p := by
    intro p
    obtain ⟨t, z⟩ := p
    simp only [Prod.mk_add_mk, add_zero]
    exact hper t z
  have hc : ((P, 0) : ℝ × UnforcedLeray.Space).2 = 0 := rfl
  have key : ∀ p : ℝ × UnforcedLeray.Space,
      UnforcedLeray.Short.PartIIIb.Concrete.L0Tscal ν ψ (p + ((P, 0) : ℝ × UnforcedLeray.Space)) =
        UnforcedLeray.Short.PartIIIb.Concrete.L0Tscal ν ψ p := by
    intro p
    simp only [UnforcedLeray.Short.PartIIIb.Concrete.L0Tscal]
    rw [dτ_shift hG p, radialT_shift hc hG p, lapT_shift hc hG p]
    have h0 : ψ (p + ((P, 0) : ℝ × UnforcedLeray.Space)) = ψ p := hG p
    rw [h0]
  have h := key (τ, y)
  simp only [Prod.mk_add_mk, add_zero] at h
  exact h
