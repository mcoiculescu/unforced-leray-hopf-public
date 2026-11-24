import UnforcedLeray.Loc.L12Equivariance.Evolution
import UnforcedLeray.Loc.L12Equivariance.Operators

/-!
# Step L12 `EquivarianceStep`: `𝒪` acts by isometries of `𝒵_β` preserving both maps

`paper/main.tex` lines 563–572 (blueprint unit B1025, equivariance part), the step
`UnforcedLeray.Blueprint.EquivarianceStep` of


> By hypothesis `u_dss`, `U_*` and `b_*` are `𝒪`-invariant. The action commutes with `𝒜_h`,
> `𝔓` and the Navier–Stokes nonlinearity, hence with `𝓑_*`, its evolution, the monodromy and
> its spectral projections, and `𝓡_β`. […] Thus `K_loc` and `G_*` are `𝒪`-invariant. Each
> action is an isometry of `𝒵_β` and preserves both maps (`loc:eq:local-fixed-point`).

**Status: `equivarianceStep : EquivarianceStep` is proved, with no hypothesis.** For
`g ∈ 𝒪` (a linear isometry of `ℝ³` fixing `e₃`) the action on `𝒵_β(τ₀)` is the pointwise
action `w ↦ (τ ↦ g·w(τ))` of the isometry `rotZ g` of `Z = H²_div` (`Rotation.lean`). It
preserves both correction maps because:

* `𝓝(g·f, g·h) = g·𝓝(f,h)` for all `g` (`N_rotZ`): the weak `-𝔓 div` of `Package.lean` is
  equivariant (`IsMinusLerayDiv.rot`, `Fields.lean`) and determines `𝓝` (`IsNonlinearMaps.N_weak`);
* `K_loc(τ) = H_h[u_{0,h} - u_dss](τ)` is invariant at every point (`heatTail_invariant`),
  since the heat kernel is radial and `u_{0,h}` (`IsCompactDatum.symmetric`) and `u_dss`
  (`IsExactBackground.udss_symmetric`) are invariant; hence `𝓒(K_loc(τ), g·f) = g·𝓒(K_loc(τ), f)`
  (`CK_rotZ`) and, with `U_*(τ)` invariant, `G_*(τ)` is invariant (`Gstar_rot`);
* `b̂(τ)` is invariant (`IsRegularMode.symmetric`, `bhat_rot`);
* `𝓡_β(τ₀)` commutes with the pointwise actions (`green_comm`, `Operators.lean`): `g`
  commutes with `S₀` (the literal formula), with `𝓑_*` (its weak characterization), hence with
  `E(τ,s)` (Volterra uniqueness, `Evolution.lean`), with `𝓜`, `P₊` (the commutant clause of
  L6), `𝓜₊⁻¹P₊` and `Π₊`, and the Green solution is unique in `𝒵_β`.

Helper files (`Loc/L12Equivariance/`): `Rotation.lean` (the actions on `L²`, `L²_div`, `H¹_div`,
`H²_div`; rotation of weak derivatives; `𝔓` commutes with rotations), `Fields.lean` (heat flow,
tensors, the weak `-𝔓 div`), `Evolution.lean` (`S₀`, `𝓑_*`, `E`), `Operators.lean` (`P₊`,
`𝓜₊⁻¹P₊`, `Π₊`, uniqueness and commutation of `𝓡_β`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace UnforcedLeray.Blueprint.L12

open SobolevGraph

theorem WeightedX.ext' {τ₀ : ℝ} {F G : WeightedX τ₀} (h : ∀ τ, F τ = G τ) : F = G :=
  BoundedContinuousFunction.ext h

variable {D : BackgroundData} {ld : LinearData} {u₀ : SpatialField} {nm : NonlinearMaps}

/-! ## Invariant data -/

/-- `K_loc(τ) = H_h[u_{0,h} - u_dss](τ)` is `𝒪`-invariant at every point (line 569). -/
theorem heatTail_invariant (hD : IsUnstableBackground D) (hu : IsCompactDatum D u₀)
    {g : Space ≃ₗᵢ[ℝ] Space} (hg : FixesAxis g) (τ : ℝ) :
    rotateField g (heatTail D u₀ τ) = heatTail D u₀ τ := by
  unfold heatTail
  apply heatProfile_invariant
  have h1 : rotateField g (u₀ - D.udss) = rotateField g u₀ - rotateField g D.udss := by
    funext x
    simp only [rotateField, Pi.sub_apply, map_sub]
  rw [h1]
  exact (hu.symmetric g hg).sub (hD.1.udss_symmetric g hg)

/-- `b̂(τ)` is `𝒪`-invariant (line 563). -/
theorem bhat_rot (hld : IsLinearData D ld) {g : Space ≃ₗᵢ[ℝ] Space} (hg : FixesAxis g)
    (τ : ℝ) : rotZ g (ld.bhat τ) = ld.bhat τ := by
  apply Zclass_injective
  rw [Zclass_rotZ]
  apply Lp.ext
  exact (rotL2_ae g _).trans (hld.mode.symmetric τ g hg)

/-! ## The nonlinear maps -/

/-- `𝓝(g·f, g·h) = g·𝓝(f,h)`. -/
theorem N_rotZ (hnm : IsNonlinearMaps D u₀ nm) (g : Space ≃ₗᵢ[ℝ] Space) (f₁ f₂ : Z) :
    nm.N (rotZ g f₁) (rotZ g f₂) = rotX g (nm.N f₁ f₂) := by
  apply L10.Xclass_injective
  rw [Xclass_rotX]
  refine L10.IsMinusLerayDiv.unique (hnm.N_weak _ _) ?_
  have h := IsMinusLerayDiv.rot g (hnm.N_weak f₁ f₂)
  rw [← tensorColumns_rot] at h
  exact L10.IsMinusLerayDiv.congr h
    (fun j => tensorColumns_congr (Zval_rotZ g f₁).symm (Zval_rotZ g f₂).symm j)

/-- `𝓒(K_loc(τ), g·f) = g·𝓒(K_loc(τ), f)` for `τ ≤ 0`, `g ∈ 𝒪`. -/
theorem CK_rotZ (hD : IsUnstableBackground D) (hu : IsCompactDatum D u₀)
    (hnm : IsNonlinearMaps D u₀ nm) {g : Space ≃ₗᵢ[ℝ] Space} (hg : FixesAxis g) {τ : ℝ}
    (hτ : τ ≤ 0) (f : Z) : nm.CK τ (rotZ g f) = rotX g (nm.CK τ f) := by
  apply L10.Xclass_injective
  rw [Xclass_rotX]
  have h1 := hnm.CK_weak τ hτ (rotZ g f)
  have h2 := IsMinusLerayDiv.rot g (hnm.CK_weak τ hτ f)
  rw [← symTensorColumns_rot, heatTail_invariant hD hu hg τ] at h2
  have h3 := L10.IsMinusLerayDiv.congr h2
    (fun j => symTensorColumns_congr (EventuallyEq.refl _ _) (Zval_rotZ g f).symm j)
  have h4 := L10.IsMinusLerayDiv.unique h1 h3
  rw [map_neg] at h4
  exact neg_injective h4

/-- `G_*(τ)` is `𝒪`-invariant for `τ ≤ 0` (line 570). -/
theorem Gstar_rot (hD : IsUnstableBackground D) (hu : IsCompactDatum D u₀)
    (hnm : IsNonlinearMaps D u₀ nm) {g : Space ≃ₗᵢ[ℝ] Space} (hg : FixesAxis g) {τ : ℝ}
    (hτ : τ ≤ 0) : rotX g (nm.Gstar τ) = nm.Gstar τ := by
  apply L10.Xclass_injective
  rw [Xclass_rotX]
  have h1 := hnm.Gstar_weak τ hτ
  have h2 := IsMinusLerayDiv.rot g h1
  rw [rotCols_add, ← symTensorColumns_rot, ← tensorColumns_rot,
    heatTail_invariant hD hu hg τ] at h2
  have hU : rotateField g (D.Ustar τ) =ᵐ[volume] D.Ustar τ := hD.1.Ustar_symmetric τ g hg
  refine L10.IsMinusLerayDiv.unique ?_ h1
  refine L10.IsMinusLerayDiv.congr h2 (fun j => ?_)
  filter_upwards [symTensorColumns_congr hU (EventuallyEq.refl _ (heatTail D u₀ τ)) j]
    with x hx
  simp only [addColumns, Pi.add_apply, hx]

/-! ## The step -/

/-- For every package, linear theory, compact datum, nonlinear maps and correction maps, the
`𝒪`-action is an isometry of `𝒵_β(τ₀)` preserving both maps (lines 563–572). -/
theorem isEquivariantCorrections_of (hD : IsUnstableBackground D) (hld : IsLinearData D ld)
    (hu : IsCompactDatum D u₀) (hnm : IsNonlinearMaps D u₀ nm) {τ₀ : ℝ} (hτ₀ : τ₀ ≤ 0)
    {cm : CorrectionMaps τ₀} (hcm : IsCorrectionMaps D ld nm τ₀ cm) :
    IsEquivariantCorrections cm := by
  intro g hg
  have hP := hD.1.period_pos
  have hE : CommutesWithE ld.ev (rotX g) :=
    E_rotX hD hld.coefficients hld.free hld.evolution hg
  have hR : ∀ F : WeightedX τ₀,
      ld.R τ₀ (liftX τ₀ (rotX g) F) = liftZ τ₀ (rotZ g) (ld.R τ₀ F) := fun F =>
    green_comm hP hld.evolution hld.splitting hld.projections hld.green (rotX g) (rotZ g)
      (ιZ_rotZ g) hE hτ₀ F
  have hτ : ∀ τ : Iic τ₀, (τ : ℝ) ≤ 0 := fun τ => le_trans τ.2 hτ₀
  refine ⟨liftZ τ₀ (rotZ g), norm_liftZ (rotZ g) (norm_rotZ g), ?_, ?_, ?_, ?_⟩
  · intro w₁ w₂
    obtain ⟨F, hF, hBq⟩ := hcm.Bq_spec w₁ w₂
    obtain ⟨F', hF', hBq'⟩ := hcm.Bq_spec (liftZ τ₀ (rotZ g) w₁) (liftZ τ₀ (rotZ g) w₂)
    have e : F' = liftX τ₀ (rotX g) F := by
      apply WeightedX.ext'
      intro τ
      rw [hF', liftX_apply, hF, liftZ_apply, liftZ_apply, N_rotZ hnm, map_smul]
    rw [hBq', e, hR, hBq]
  · intro j w
    obtain ⟨F, hF, hL⟩ := hcm.L_spec j w
    obtain ⟨F', hF', hL'⟩ := hcm.L_spec j (liftZ τ₀ (rotZ g) w)
    have e : F' = liftX τ₀ (rotX g) F := by
      apply WeightedX.ext'
      intro τ
      rw [hF', liftX_apply, hF, liftZ_apply]
      simp only [map_add, map_neg, map_smul]
      rw [CK_rotZ hD hu hnm hg (hτ τ), ← N_rotZ hnm, ← N_rotZ hnm, bhat_rot hld hg]
    rw [hL', e, hR, hL]
  · intro j
    obtain ⟨F, hF, hG⟩ := hcm.G_spec j
    have e : liftX τ₀ (rotX g) F = F := by
      apply WeightedX.ext'
      intro τ
      rw [liftX_apply, hF]
      simp only [map_add, map_sub, map_smul]
      rw [Gstar_rot hD hu hnm hg (hτ τ), ← N_rotZ hnm, ← CK_rotZ hD hu hnm hg (hτ τ),
        bhat_rot hld hg]
    rw [hG, ← hR, e]
  · intro w τ
    exact Zval_rotZ g (w τ)

/-- **Step L12** (`paper/main.tex` lines 563–572, blueprint unit B1025): each `g ∈ 𝒪` acts by
an isometry of `𝒵_β(τ₀)`, given at each phase by `(g·f)(x) = g f(g⁻¹x)`, that preserves both
correction maps of `loc:eq:local-fixed-point`. -/
theorem equivarianceStep : EquivarianceStep := by
  intro D hD ld hld u₀ hu nm hnm τ₀ hτ₀ cm hcm
  exact isEquivariantCorrections_of hD hld hu hnm hτ₀ hcm

end UnforcedLeray.Blueprint.L12
