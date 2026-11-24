import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.Pieces

/-!
# `PartIII-b:C/rep/8/1/1/2/4/org`: the phase-free stream cutoff is the Ward stream cutoff

Source `the November 2 reference manuscript`
lines 4178-4186 (outward primitive `Ψ_Z(r,z) = -∫_r^∞ ρ Z_z(ρ,z) dρ`, stream cutoff
`𝒞_y Z = χ_y Z + (χ_y'/r)Ψ_Z e_z`), 4771-4791 (the zero-width Newton field of the axisymmetric
phase-mean tensor, `W^mt_μ(y) = ε² V_μ(εy)`), 4917-4937 (rotation covariance of `V_μ`).

The receiver cutoff `streamCut` of `Concrete/SourceL.lean` reads the outward primitive along the
ray through `y` (`rayPt`), the Ward cutoff `wardStreamCut` of `PhysLayer.lean` on the half plane
`φ = 0`.  They agree off the axis for a field whose `z`-component is the same along all rays with
the same `(ρ, z)` at the radii where the cutoff derivative can be nonzero (`mtField_streamCut_eq`);
the field `W^mt_μ` has this property by the rotation covariance `newtonVEquivariant`
(`YoungWRayAzi`, `AsmYA/AziDef.lean`, proved in `AsmYA/YoungAzi.lean`).  Hence
`mnYA = 𝒞_y W^mt_μ` off the axis (`GeomY/AsmYA.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace GeomYACut

/-- The radial derivative of the stream cutoff `χ_y(r) = χ̂_y(ν/(εr)²)` off the axis. -/
theorem hasDerivAt_chiYr {ν ε : ℝ} (hε : 0 < ε) {χy : ℝ → ℝ} (hχ : Differentiable ℝ χy) {r : ℝ}
    (hr : 0 < r) :
    HasDerivAt (chiYr ν ε χy) (deriv χy (ν / (ε * r) ^ 2) * (-2 * ν * ε⁻¹ ^ 2 / r ^ 3)) r := by
  have hev : chiYr ν ε χy =ᶠ[𝓝 r] fun x => χy (ν / (ε * x) ^ 2) := by
    filter_upwards [lt_mem_nhds hr] with x hx
    simp [chiYr, hx.ne']
  have hfun : (fun x : ℝ => ν / (ε * x) ^ 2) = fun x => ν * ε⁻¹ ^ 2 * (x ^ 2)⁻¹ := by
    funext x
    rw [div_eq_mul_inv, mul_pow, mul_inv, inv_pow, mul_assoc]
  have hp : HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r := by
    simpa using hasDerivAt_pow 2 r
  have hg0 := (hp.inv (by positivity : r ^ 2 ≠ 0)).const_mul (ν * ε⁻¹ ^ 2)
  have hg : HasDerivAt (fun x : ℝ => ν / (ε * x) ^ 2) (-2 * ν * ε⁻¹ ^ 2 / r ^ 3) r := by
    rw [hfun]
    refine hg0.congr_deriv ?_
    field_simp
  have hc : HasDerivAt (fun x : ℝ => χy (ν / (ε * x) ^ 2))
      (deriv χy (ν / (ε * r) ^ 2) * (-2 * ν * ε⁻¹ ^ 2 / r ^ 3)) r :=
    (hχ _).hasDerivAt.comp r hg
  exact hc.congr_of_eventuallyEq hev

theorem cylR_ofLp (y : Space) : cylR (WithLp.ofLp y) = ϱ y := by
  simp [ϱ, cylR]

theorem toLp_cut (a b : ℝ) (u : Vec3) :
    WithLp.toLp 2 (a • u + b • (![0, 0, 1] : Vec3)) =
      a • WithLp.toLp 2 u + b • coordinateVector 2 := by
  ext i
  fin_cases i <;> simp [coordinateVector]

/-- **The phase-free stream cutoff is the Ward stream cutoff off the axis** (source 4178-4186):
if the `z`-component of `F` is the same on all outward rays at radii `ρ` with `ν < (ερ)²` (where the
cutoff derivative can be nonzero), then `𝒞_y F` read on `Space` is `wardStreamCut ν ε⁻¹ χ_y` of
the phase-free field `F`. -/
theorem mtField_streamCut_eq {ν ε : ℝ} (hν : 0 < ν) (hε : 0 < ε) {χy : ℝ → ℝ}
    (hχ : IsStreamCutoff χy) (F : Vec3 → Vec3)
    (hF : ∀ w : Vec3, 0 < cylR w → ∀ ρ : ℝ, ν < (ε * ρ) ^ 2 →
      F (rayPt w ρ) 2 = F ![ρ, 0, w 2] 2)
    (τ : ℝ) (y : Space) (hy : 0 < ϱ y) :
    mtField (streamCut ν ε χy F) τ y = wardStreamCut ν ε⁻¹ χy (mtField F) τ y := by
  have hdiff : Differentiable ℝ χy := hχ.smooth.differentiable (by simp)
  have hr : cylR (WithLp.ofLp y) = ϱ y := cylR_ofLp y
  have ht : ν * age ε⁻¹ y = ν / (ε * ϱ y) ^ 2 := by
    unfold age
    field_simp
  have hderiv : deriv (chiYr ν ε χy) (ϱ y) =
      deriv χy (ν / (ε * ϱ y) ^ 2) * (-2 * ν * ε⁻¹ ^ 2 / ϱ y ^ 3) :=
    (hasDerivAt_chiYr hε hdiff hy).deriv
  have hval : chiYr ν ε χy (ϱ y) = χy (ν / (ε * ϱ y) ^ 2) := by
    simp [chiYr, hy.ne']
  -- the outward primitives agree where the cutoff derivative may be nonzero
  have hprim : deriv χy (ν / (ε * ϱ y) ^ 2) * streamPsi F (WithLp.ofLp y) =
      deriv χy (ν / (ε * ϱ y) ^ 2) * outPrim (mtField F) τ (ϱ y) (y 2) := by
    by_cases h1 : ν / (ε * ϱ y) ^ 2 ≤ 1
    · congr 1
      unfold streamPsi outPrim
      rw [hr]
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
      have hpos : 0 < (ε * ϱ y) ^ 2 := by positivity
      have hle : ν ≤ (ε * ϱ y) ^ 2 := by rwa [div_le_one hpos] at h1
      have hlt : ν < (ε * ρ) ^ 2 := by
        have hρ' : ϱ y < ρ := hρ
        have : (ε * ϱ y) ^ 2 < (ε * ρ) ^ 2 := by
          have h0 : 0 ≤ ε * ϱ y := by positivity
          have h2 : ε * ϱ y < ε * ρ := mul_lt_mul_of_pos_left hρ' hε
          nlinarith
        linarith
      have hw : 0 < cylR (WithLp.ofLp y) := by rw [hr]; exact hy
      have e := hF (WithLp.ofLp y) hw ρ hlt
      show ρ * F (rayPt (WithLp.ofLp y) ρ) 2 = ρ * (WithLp.toLp 2 (F (WithLp.ofLp !₂[ρ, 0, y 2]))) 2
      rw [e]
    · have hz : deriv χy (ν / (ε * ϱ y) ^ 2) = 0 := by
        have h1' : 1 < ν / (ε * ϱ y) ^ 2 := lt_of_not_ge h1
        have hev : χy =ᶠ[𝓝 (ν / (ε * ϱ y) ^ 2)] fun _ => (0 : ℝ) :=
          Filter.eventually_of_mem (Ioi_mem_nhds h1') (fun s hs => hχ.zero s (le_of_lt hs))
        rw [hev.deriv_eq]
        simp
      rw [hz, zero_mul, zero_mul]
  unfold mtField at hprim
  unfold mtField streamCut wardStreamCut
  rw [toLp_cut, hr, hval, hderiv, ht]
  congr 2
  rw [show deriv χy (ν / (ε * ϱ y) ^ 2) * (-2 * ν * ε⁻¹ ^ 2 / ϱ y ^ 3) / ϱ y *
      streamPsi F (WithLp.ofLp y) =
      (-2 * ν * ε⁻¹ ^ 2 / ϱ y ^ 3) / ϱ y * (deriv χy (ν / (ε * ϱ y) ^ 2) *
        streamPsi F (WithLp.ofLp y)) by ring, hprim]
  ring

end GeomYACut

end UnforcedLeray.Short.PartIIIb.Concrete
