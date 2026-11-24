import UnforcedLeray.Short.PartIIb.Sub.R1_7

/-!
# Part II-b, task `PartII-b:R1/7`, leaf `CylAdvFormula`: the cylindrical advection

Proves `UnforcedLeray.Short.IIb.CylAdvFormula` (defined in `Sub/R1_7.lean`, lines 176-181). Source of
record: `the November 2 reference manuscript`, lines 1203-1263 (SP 1263), and
`paper/main.tex` 2867-2888 (B0187: for the no-swirl field `u_r e_r + u_z e_z`, the advection is
`(u_r ∂_r u_r + u_z ∂_z u_r) e_r + (u_r ∂_r u_z + u_z ∂_z u_z) e_z`, with no hoop term).

Proof idea. Let `d(ρ, z) = u_r(ρ, z, t) e_r + u_z(ρ, z, t) e_z` (`cylAdv_merVel`). Off the axis,
`Axi.advection_liftMer` turns `(cylField ur uz t · ∇) cylField ur uz t` into the lift of
`merAdv d d`, where `merAdv d d p = d p 0 • ∂_ρ d p + d p 1 • ∂_z d p`. At `(r, z) = (ϱ x, x₃)` with
`r > 0`, `t > 0`, the partial derivatives of `d` are the one-variable derivatives of the profiles, by
the chain rule along `s ↦ (s, z)` and `s ↦ (r, s)`. The profiles are differentiable at `(r, z)` because
`(r, z, t) ↦ u(r, z, t)` is `C¹` on the open set `meridDomain`.

No hypotheses are added to the statement.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412 UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187
  UnforcedLeray.Short.PartIIa

/-! ## The meridional field -/

/-- The meridional field `(ρ, z) ↦ u_r(ρ, z, t) e_r + u_z(ρ, z, t) e_z` in `ℝ²` coordinates. -/
def cylAdv_merVel (ur uz : ℝ → ℝ → ℝ → ℝ) (t : ℝ) : ℝ × ℝ → Axi.Merid :=
  fun p => ur p.1 p.2 t • Axi.m0 + uz p.1 p.2 t • Axi.m1

theorem cylAdv_merVel_apply_zero (ur uz : ℝ → ℝ → ℝ → ℝ) (t r z : ℝ) :
    cylAdv_merVel ur uz t (r, z) 0 = ur r z t := by
  simp [cylAdv_merVel]

theorem cylAdv_merVel_apply_one (ur uz : ℝ → ℝ → ℝ → ℝ) (t r z : ℝ) :
    cylAdv_merVel ur uz t (r, z) 1 = uz r z t := by
  simp [cylAdv_merVel]

/-! ## Differentiability -/

/-- A `C¹` meridional profile, at fixed `t > 0`, is differentiable in `(r, z)` at each `r > 0`. -/
theorem cylAdv_diff_slice (f : ℝ → ℝ → ℝ → ℝ) (t r z : ℝ) (hr : 0 < r) (ht : 0 < t)
    (hf : MeridSmooth 1 f) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ => f q.1 q.2 t) (r, z) := by
  have hopen : IsOpen meridDomain := by
    have h1 : IsOpen {q : ℝ × ℝ × ℝ | 0 < q.1} := isOpen_lt continuous_const continuous_fst
    have h2 : IsOpen {q : ℝ × ℝ × ℝ | 0 < q.2.2} :=
      isOpen_lt continuous_const (continuous_snd.comp continuous_snd)
    exact h1.inter h2
  have hmem : ((r, z, t) : ℝ × ℝ × ℝ) ∈ meridDomain := ⟨hr, ht⟩
  have hc : ContDiffOn ℝ 1 (fun q : ℝ × ℝ × ℝ => f q.1 q.2.1 q.2.2) meridDomain := hf
  have hD : ContDiffAt ℝ 1 (fun q : ℝ × ℝ × ℝ => f q.1 q.2.1 q.2.2) (r, z, t) :=
    hc.contDiffAt (hopen.mem_nhds hmem)
  have hφ : DifferentiableAt ℝ (fun q : ℝ × ℝ => ((q.1, q.2, t) : ℝ × ℝ × ℝ)) (r, z) := by
    fun_prop
  exact hD.differentiableAt_one.comp (r, z) hφ

theorem cylAdv_merVel_diff (ur uz : ℝ → ℝ → ℝ → ℝ) (t r z : ℝ) (hr : 0 < r) (ht : 0 < t)
    (hur : MeridSmooth 1 ur) (huz : MeridSmooth 1 uz) :
    DifferentiableAt ℝ (cylAdv_merVel ur uz t) (r, z) :=
  ((cylAdv_diff_slice ur t r z hr ht hur).smul_const Axi.m0).add
    ((cylAdv_diff_slice uz t r z hr ht huz).smul_const Axi.m1)

/-- Restriction of a profile to the line `s ↦ (s, z)` is differentiable at `r`. -/
theorem cylAdv_line_fst (f : ℝ → ℝ → ℝ → ℝ) (t r z : ℝ)
    (hu : DifferentiableAt ℝ (fun q : ℝ × ℝ => f q.1 q.2 t) (r, z)) :
    DifferentiableAt ℝ (fun s => f s z t) r :=
  DifferentiableAt.comp (g := fun q : ℝ × ℝ => f q.1 q.2 t)
    (f := fun s : ℝ => ((s, z) : ℝ × ℝ)) r hu (by fun_prop)

/-- Restriction of a profile to the line `s ↦ (r, s)` is differentiable at `z`. -/
theorem cylAdv_line_snd (f : ℝ → ℝ → ℝ → ℝ) (t r z : ℝ)
    (hu : DifferentiableAt ℝ (fun q : ℝ × ℝ => f q.1 q.2 t) (r, z)) :
    DifferentiableAt ℝ (fun s => f r s t) z :=
  DifferentiableAt.comp (g := fun q : ℝ × ℝ => f q.1 q.2 t)
    (f := fun s : ℝ => ((r, s) : ℝ × ℝ)) z hu (by fun_prop)

/-! ## Chain rule along the coordinate lines -/

/-- Partial derivative along `ρ`: `fderiv g (r, z) (1, 0) = deriv (s ↦ g (s, z)) r`. -/
theorem cylAdv_fderiv_fst {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : ℝ × ℝ → F) (r z : ℝ) (hg : DifferentiableAt ℝ g (r, z)) :
    fderiv ℝ g (r, z) (1, 0) = deriv (fun s => g (s, z)) r := by
  have h1 : HasDerivAt (fun s : ℝ => ((s, z) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) r :=
    HasDerivAt.prodMk (hasDerivAt_id' r) (hasDerivAt_const r z)
  exact ((hg.hasFDerivAt).comp_hasDerivAt r h1).deriv.symm

/-- Partial derivative along `z`: `fderiv g (r, z) (0, 1) = deriv (s ↦ g (r, s)) z`. -/
theorem cylAdv_fderiv_snd {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : ℝ × ℝ → F) (r z : ℝ) (hg : DifferentiableAt ℝ g (r, z)) :
    fderiv ℝ g (r, z) (0, 1) = deriv (fun s => g (r, s)) z := by
  have h1 : HasDerivAt (fun s : ℝ => ((r, s) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) z :=
    HasDerivAt.prodMk (hasDerivAt_const z r) (hasDerivAt_id' z)
  exact ((hg.hasFDerivAt).comp_hasDerivAt z h1).deriv.symm

/-- The `ρ`-derivative of the meridional field, in the one-variable derivatives `physR`. -/
theorem cylAdv_dρ (ur uz : ℝ → ℝ → ℝ → ℝ) (t r z : ℝ) (hr : 0 < r) (ht : 0 < t)
    (hur : MeridSmooth 1 ur) (huz : MeridSmooth 1 uz) :
    Axi.dρ (cylAdv_merVel ur uz t) (r, z) =
      physR ur r z t • Axi.m0 + physR uz r z t • Axi.m1 := by
  have hu : DifferentiableAt ℝ (fun q : ℝ × ℝ => ur q.1 q.2 t) (r, z) :=
    cylAdv_diff_slice ur t r z hr ht hur
  have hv : DifferentiableAt ℝ (fun q : ℝ × ℝ => uz q.1 q.2 t) (r, z) :=
    cylAdv_diff_slice uz t r z hr ht huz
  have hd : DifferentiableAt ℝ (cylAdv_merVel ur uz t) (r, z) :=
    cylAdv_merVel_diff ur uz t r z hr ht hur huz
  have hu1 : DifferentiableAt ℝ (fun s => ur s z t) r := cylAdv_line_fst ur t r z hu
  have hv1 : DifferentiableAt ℝ (fun s => uz s z t) r := cylAdv_line_fst uz t r z hv
  have hline : HasDerivAt (fun s => cylAdv_merVel ur uz t (s, z))
      (physR ur r z t • Axi.m0 + physR uz r z t • Axi.m1) r :=
    (hu1.hasDerivAt.smul_const Axi.m0).add (hv1.hasDerivAt.smul_const Axi.m1)
  unfold Axi.dρ
  rw [cylAdv_fderiv_fst _ r z hd]
  exact hline.deriv

/-- The `z`-derivative of the meridional field, in the one-variable derivatives `physZ`. -/
theorem cylAdv_dz (ur uz : ℝ → ℝ → ℝ → ℝ) (t r z : ℝ) (hr : 0 < r) (ht : 0 < t)
    (hur : MeridSmooth 1 ur) (huz : MeridSmooth 1 uz) :
    Axi.dz (cylAdv_merVel ur uz t) (r, z) =
      physZ ur r z t • Axi.m0 + physZ uz r z t • Axi.m1 := by
  have hu : DifferentiableAt ℝ (fun q : ℝ × ℝ => ur q.1 q.2 t) (r, z) :=
    cylAdv_diff_slice ur t r z hr ht hur
  have hv : DifferentiableAt ℝ (fun q : ℝ × ℝ => uz q.1 q.2 t) (r, z) :=
    cylAdv_diff_slice uz t r z hr ht huz
  have hd : DifferentiableAt ℝ (cylAdv_merVel ur uz t) (r, z) :=
    cylAdv_merVel_diff ur uz t r z hr ht hur huz
  have hu1 : DifferentiableAt ℝ (fun s => ur r s t) z := cylAdv_line_snd ur t r z hu
  have hv1 : DifferentiableAt ℝ (fun s => uz r s t) z := cylAdv_line_snd uz t r z hv
  have hline : HasDerivAt (fun s => cylAdv_merVel ur uz t (r, s))
      (physZ ur r z t • Axi.m0 + physZ uz r z t • Axi.m1) z :=
    (hu1.hasDerivAt.smul_const Axi.m0).add (hv1.hasDerivAt.smul_const Axi.m1)
  unfold Axi.dz
  rw [cylAdv_fderiv_snd _ r z hd]
  exact hline.deriv

/-! ## The meridional advection -/

/-- The meridional advection `merAdv d d` of the meridional field at `(r, z)`:
`(u_r ∂_r u_r + u_z ∂_z u_r) m0 + (u_r ∂_r u_z + u_z ∂_z u_z) m1`. -/
theorem cylAdv_merAdv (ur uz : ℝ → ℝ → ℝ → ℝ) (t r z : ℝ) (hr : 0 < r) (ht : 0 < t)
    (hur : MeridSmooth 1 ur) (huz : MeridSmooth 1 uz) :
    Axi.merAdv (cylAdv_merVel ur uz t) (cylAdv_merVel ur uz t) (r, z) =
      (ur r z t * physR ur r z t + uz r z t * physZ ur r z t) • Axi.m0 +
      (ur r z t * physR uz r z t + uz r z t * physZ uz r z t) • Axi.m1 := by
  unfold Axi.merAdv
  rw [cylAdv_merVel_apply_zero, cylAdv_merVel_apply_one, cylAdv_dρ ur uz t r z hr ht hur huz,
    cylAdv_dz ur uz t r z hr ht hur huz]
  module

/-! ## The leaf Prop -/

/-- **Advection of the meridional lift** (`CylAdvFormula`): off the axis, at `t > 0`,
`(u·∇)u = (u_r ∂_r u_r + u_z ∂_z u_r) e_r + (u_r ∂_r u_z + u_z ∂_z u_z) e_z` for the meridional
lift `u = u_r e_r + u_z e_z`, with no hoop term. -/
theorem cylAdvFormula : UnforcedLeray.Short.IIb.CylAdvFormula := by
  unfold CylAdvFormula
  intro ur uz t x ht hx hur huz
  have hr : 0 < Axi.ϱ x := Axi.ϱ_pos hx
  have hcyl : cylField ur uz t = Axi.liftMer (cylAdv_merVel ur uz t) := by
    funext y
    simp [cylField, Axi.liftMer, cylAdv_merVel, Axi.mer]
  have hmer : Axi.mer x = (Axi.ϱ x, x 2) := rfl
  have hd : DifferentiableAt ℝ (cylAdv_merVel ur uz t) (Axi.mer x) := by
    rw [hmer]
    exact cylAdv_merVel_diff ur uz t (Axi.ϱ x) (x 2) hr ht hur huz
  have hadv := Axi.advection_liftMer (cylAdv_merVel ur uz t) hx hd
  rw [hcyl, hadv]
  have hpt := cylAdv_merAdv ur uz t (Axi.ϱ x) (x 2) hr ht hur huz
  simp only [Axi.liftMer, hmer, hpt]
  simp

end UnforcedLeray.Short.IIb

end
