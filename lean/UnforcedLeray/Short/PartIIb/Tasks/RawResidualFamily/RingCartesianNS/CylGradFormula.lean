import UnforcedLeray.Short.PartIIb.Sub.R1_7

/-!
# Part II-b, task `PartII-b:R1/7` leaf `CylGradFormula`: the gradient of the meridional pressure

Source of record: `the November 2 reference manuscript`, line 1263 (SP 1263);
`paper/main.tex` 2867-2888 (B0187: `∇ p(ϱ x, x₃, t) = ∂_r p e_r + ∂_z p e_z`). Target statement:
`Sub/R1_7.lean`, `CylGradFormula`.

Proof: the chain rule `Axi.fderiv_comp_mer_apply` gives the Fréchet derivative of
`x ↦ p(ϱ x, x₃, t)` off the axis in terms of the profile derivatives `Axi.dρ`, `Axi.dz`. The bridge
lemmas below identify those profile derivatives with the one-variable derivatives `physR`, `physZ`
of `B0187`, on the open half plane where the profile is `C¹`. Then the three Cartesian components
are compared.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412 UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187
  UnforcedLeray.Short.PartIIa

/-! ## Bridge lemmas: a partial derivative at a point is a one-variable derivative -/

/-- The first-variable Fréchet derivative of a function differentiable at `p` is the derivative of
its slice `s ↦ F(s, p.2)`. -/
theorem cylGrad_fderiv_fst (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) (hF : DifferentiableAt ℝ F p) :
    fderiv ℝ F p (1, 0) = deriv (fun s => F (s, p.2)) p.1 := by
  have hc : HasDerivAt (fun s : ℝ => (s, p.2)) ((1 : ℝ), (0 : ℝ)) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  exact (hF.hasFDerivAt.comp_hasDerivAt p.1 hc).deriv.symm

/-- The second-variable Fréchet derivative of a function differentiable at `p` is the derivative of
its slice `s ↦ F(p.1, s)`. -/
theorem cylGrad_fderiv_snd (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) (hF : DifferentiableAt ℝ F p) :
    fderiv ℝ F p (0, 1) = deriv (fun s => F (p.1, s)) p.2 := by
  have hc : HasDerivAt (fun s : ℝ => (p.1, s)) ((0 : ℝ), (1 : ℝ)) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  exact (hF.hasFDerivAt.comp_hasDerivAt p.2 hc).deriv.symm

/-! ## Regularity of a physical slice on the half plane -/

/-- For `t > 0`, `(r, z) ↦ p(r, z, t)` is `C¹` on the open half plane `{r > 0}`. -/
theorem cylGrad_contDiffOn {p : ℝ → ℝ → ℝ → ℝ} (hp : MeridSmooth 1 p) {t : ℝ} (ht : 0 < t) :
    ContDiffOn ℝ 1 (fun q : ℝ × ℝ => p q.1 q.2 t) (Ioi 0 ×ˢ univ) := by
  unfold MeridSmooth at hp
  have hφ : ContDiff ℝ 1 (fun q : ℝ × ℝ => ((q.1, q.2, t) : ℝ × ℝ × ℝ)) :=
    contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)
  have hmaps : MapsTo (fun q : ℝ × ℝ => ((q.1, q.2, t) : ℝ × ℝ × ℝ)) (Ioi 0 ×ˢ univ)
      meridDomain :=
    fun q hq => show 0 < q.1 ∧ 0 < t from ⟨hq.1, ht⟩
  exact ContDiffOn.comp hp hφ.contDiffOn hmaps

/-! ## Physical derivatives of a slice: first order -/

/-- The profile `ρ`-derivative of `p(·, ·, t)` at a point of differentiability is the physical
radial derivative `∂_r p`. -/
theorem cylGrad_dRho_eq {p : ℝ → ℝ → ℝ → ℝ} {t : ℝ} {q : ℝ × ℝ}
    (hd : DifferentiableAt ℝ (fun q : ℝ × ℝ => p q.1 q.2 t) q) :
    UnforcedLeray.Axi.dρ (fun q : ℝ × ℝ => p q.1 q.2 t) q = physR p q.1 q.2 t := by
  unfold UnforcedLeray.Axi.dρ
  rw [cylGrad_fderiv_fst _ _ hd]
  rfl

/-- The profile `z`-derivative of `p(·, ·, t)` at a point of differentiability is the physical
axial derivative `∂_z p`. -/
theorem cylGrad_dz_eq {p : ℝ → ℝ → ℝ → ℝ} {t : ℝ} {q : ℝ × ℝ}
    (hd : DifferentiableAt ℝ (fun q : ℝ × ℝ => p q.1 q.2 t) q) :
    UnforcedLeray.Axi.dz (fun q : ℝ × ℝ => p q.1 q.2 t) q = physZ p q.1 q.2 t := by
  unfold UnforcedLeray.Axi.dz
  rw [cylGrad_fderiv_snd _ _ hd]
  rfl

/-! ## The directional derivative of the Cartesian pressure off the axis -/

/-- For `x` off the axis at `t > 0`, `Dπ(x) v = ((x₀v₀ + x₁v₁)/ϱ) ∂_r p + v₃ ∂_z p`. -/
theorem cylGrad_fderiv_apply {p : ℝ → ℝ → ℝ → ℝ} {t : ℝ} {x : Space} (ht : 0 < t)
    (hx : x ∉ Axi.axis) (hp : MeridSmooth 1 p) (v : Space) :
    fderiv ℝ (cylPressure p t) x v =
      (x 0 * v 0 + x 1 * v 1) / Axi.ϱ x * physR p (Axi.ϱ x) (x 2) t +
        v 2 * physZ p (Axi.ϱ x) (x 2) t := by
  have hh : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => p q.1 q.2 t) (Ioi 0 ×ˢ univ) :=
    cylGrad_contDiffOn hp ht
  have hd : DifferentiableAt ℝ (fun q : ℝ × ℝ => p q.1 q.2 t) (Axi.mer x) :=
    Axi.differentiableAt_profile hh one_ne_zero hx
  have h1 := Axi.fderiv_comp_mer_apply hx hd v
  rw [cylGrad_dRho_eq hd, cylGrad_dz_eq hd, Axi.ϱD_apply, smul_eq_mul, smul_eq_mul] at h1
  exact h1

/-! ## The gradient formula -/

/-- **Gradient of the meridional scalar**: off the axis, `∇ p(ϱ x, x₃, t) = ∂_r p e_r + ∂_z p e_z`
(`Axi.fderiv_comp_mer_apply`), for `p` of class `C¹`. This is the leaf Prop `CylGradFormula`. -/
theorem cylGradFormula : UnforcedLeray.Short.IIb.CylGradFormula := by
  unfold CylGradFormula
  intro p t x ht hx hp
  ext j
  fin_cases j
  · simp [cartGrad, cylGrad_fderiv_apply ht hx hp, Axi.coordinateVector_apply, Axi.eR_apply_zero]
    ring
  · simp [cartGrad, cylGrad_fderiv_apply ht hx hp, Axi.coordinateVector_apply, Axi.eR_apply_one]
    ring
  · simp [cartGrad, cylGrad_fderiv_apply ht hx hp, Axi.coordinateVector_apply, Axi.eR_apply_two]

end UnforcedLeray.Short.IIb

end
