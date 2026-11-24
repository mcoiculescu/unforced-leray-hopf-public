import UnforcedLeray.Short.PartIIb.Sub.R1_7

/-!
# Part II-b, task `PartII-b:R1/7` leaf `CylLapFormula`: the vector Laplacian of the meridional lift

Source of record: `the November 2 reference manuscript`, line 1263 (SP 1263), and
`paper/main.tex` 2883-2886 (B0187: the radial component `(∂_r² + r⁻¹∂_r − r⁻² + ∂_z²) u_r`, the
axial component `(∂_r² + r⁻¹∂_r + ∂_z²) u_z`). Target statement: `Sub/R1_7.lean`, `CylLapFormula`.

Proof: `Axi.vecLap_liftMer` (`Lib/Axisymmetric/Laplacian.lean`) turns the Cartesian vector
Laplacian of the lift into the meridional profile `vecLapMer`. The bridge lemmas below identify the
profile derivatives `Axi.dρ`, `Axi.dz` (Fréchet derivatives in the profile variables) with the
one-variable derivatives `physR`, `physZ` of `B0187`, on the open half plane where the profiles
are `C²`.
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
theorem cylLap_fderiv_fst (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) (hF : DifferentiableAt ℝ F p) :
    fderiv ℝ F p (1, 0) = deriv (fun s => F (s, p.2)) p.1 := by
  have hc : HasDerivAt (fun s : ℝ => (s, p.2)) ((1 : ℝ), (0 : ℝ)) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  exact (hF.hasFDerivAt.comp_hasDerivAt p.1 hc).deriv.symm

/-- The second-variable Fréchet derivative of a function differentiable at `p` is the derivative of
its slice `s ↦ F(p.1, s)`. -/
theorem cylLap_fderiv_snd (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) (hF : DifferentiableAt ℝ F p) :
    fderiv ℝ F p (0, 1) = deriv (fun s => F (p.1, s)) p.2 := by
  have hc : HasDerivAt (fun s : ℝ => (p.1, s)) ((0 : ℝ), (1 : ℝ)) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  exact (hF.hasFDerivAt.comp_hasDerivAt p.2 hc).deriv.symm

/-! ## Regularity of a physical slice on the half plane -/

/-- For `t > 0`, `(r, z) ↦ u(r, z, t)` is `C²` on the open half plane `{r > 0}`. -/
theorem cylLap_contDiffOn {u : ℝ → ℝ → ℝ → ℝ} (hu : MeridSmooth 2 u) {t : ℝ} (ht : 0 < t) :
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ => u p.1 p.2 t) (Ioi 0 ×ˢ univ) := by
  unfold MeridSmooth at hu
  have hφ : ContDiff ℝ 2 (fun p : ℝ × ℝ => ((p.1, p.2, t) : ℝ × ℝ × ℝ)) :=
    contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)
  have hmaps : MapsTo (fun p : ℝ × ℝ => ((p.1, p.2, t) : ℝ × ℝ × ℝ)) (Ioi 0 ×ˢ univ)
      meridDomain :=
    fun _ hp => ⟨hp.1, ht⟩
  exact ContDiffOn.comp hu hφ.contDiffOn hmaps

/-! ## Physical derivatives of a slice: first and second order -/

/-- The profile `ρ`-derivative of `u(·, ·, t)` is the physical radial derivative `∂_r u`. -/
theorem cylLap_dRho_eq {u : ℝ → ℝ → ℝ → ℝ} (hu : MeridSmooth 2 u) {t : ℝ} (ht : 0 < t)
    (p : ℝ × ℝ) (hp : 0 < p.1) :
    Axi.dρ (fun q : ℝ × ℝ => u q.1 q.2 t) p = physR u p.1 p.2 t := by
  have hmem : p ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := ⟨hp, mem_univ _⟩
  have hd : DifferentiableAt ℝ (fun q : ℝ × ℝ => u q.1 q.2 t) p :=
    ((cylLap_contDiffOn hu ht).differentiableOn (by norm_num)).differentiableAt
      (Axi.isOpen_halfPlane.mem_nhds hmem)
  exact cylLap_fderiv_fst (fun q : ℝ × ℝ => u q.1 q.2 t) p hd

/-- The profile `z`-derivative of `u(·, ·, t)` is the physical axial derivative `∂_z u`. -/
theorem cylLap_dz_eq {u : ℝ → ℝ → ℝ → ℝ} (hu : MeridSmooth 2 u) {t : ℝ} (ht : 0 < t)
    (p : ℝ × ℝ) (hp : 0 < p.1) :
    Axi.dz (fun q : ℝ × ℝ => u q.1 q.2 t) p = physZ u p.1 p.2 t := by
  have hmem : p ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := ⟨hp, mem_univ _⟩
  have hd : DifferentiableAt ℝ (fun q : ℝ × ℝ => u q.1 q.2 t) p :=
    ((cylLap_contDiffOn hu ht).differentiableOn (by norm_num)).differentiableAt
      (Axi.isOpen_halfPlane.mem_nhds hmem)
  exact cylLap_fderiv_snd (fun q : ℝ × ℝ => u q.1 q.2 t) p hd

/-- The profile `ρ`-derivative of `∂_ρ u` is the physical second radial derivative
`∂_r² u`. -/
theorem cylLap_dRho_dRho {u : ℝ → ℝ → ℝ → ℝ} (hu : MeridSmooth 2 u) {t : ℝ} (ht : 0 < t)
    (p : ℝ × ℝ) (hp : 0 < p.1) :
    Axi.dρ (Axi.dρ (fun q : ℝ × ℝ => u q.1 q.2 t)) p = physR (physR u) p.1 p.2 t := by
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := Axi.isOpen_halfPlane
  have hmem : p ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := ⟨hp, mem_univ _⟩
  have hF1 : ContDiffOn ℝ 1 (fderiv ℝ (fun q : ℝ × ℝ => u q.1 q.2 t)) (Ioi 0 ×ˢ univ) :=
    (cylLap_contDiffOn hu ht).fderiv_of_isOpen hopen (by norm_num)
  have hD1 : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => Axi.dρ (fun q' : ℝ × ℝ => u q'.1 q'.2 t) q)
      (Ioi 0 ×ˢ univ) :=
    hF1.clm_apply contDiffOn_const
  have hdiffAt : DifferentiableAt ℝ
      (fun q : ℝ × ℝ => Axi.dρ (fun q' : ℝ × ℝ => u q'.1 q'.2 t) q) p :=
    (hD1.differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hmem)
  have hev : (fun q : ℝ × ℝ => Axi.dρ (fun q' : ℝ × ℝ => u q'.1 q'.2 t) q) =ᶠ[𝓝 p]
      (fun q : ℝ × ℝ => physR u q.1 q.2 t) := by
    filter_upwards [hopen.mem_nhds hmem] with q hq
    exact cylLap_dRho_eq hu ht q hq.1
  have hG : DifferentiableAt ℝ (fun q : ℝ × ℝ => physR u q.1 q.2 t) p :=
    hdiffAt.congr_of_eventuallyEq hev.symm
  show fderiv ℝ (fun q : ℝ × ℝ => Axi.dρ (fun q' : ℝ × ℝ => u q'.1 q'.2 t) q) p (1, 0) = _
  rw [hev.fderiv_eq]
  exact cylLap_fderiv_fst (fun q : ℝ × ℝ => physR u q.1 q.2 t) p hG

/-- The profile `z`-derivative of `∂_z u` is the physical second axial derivative `∂_z² u`. -/
theorem cylLap_dz_dz {u : ℝ → ℝ → ℝ → ℝ} (hu : MeridSmooth 2 u) {t : ℝ} (ht : 0 < t)
    (p : ℝ × ℝ) (hp : 0 < p.1) :
    Axi.dz (Axi.dz (fun q : ℝ × ℝ => u q.1 q.2 t)) p = physZ (physZ u) p.1 p.2 t := by
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := Axi.isOpen_halfPlane
  have hmem : p ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := ⟨hp, mem_univ _⟩
  have hF1 : ContDiffOn ℝ 1 (fderiv ℝ (fun q : ℝ × ℝ => u q.1 q.2 t)) (Ioi 0 ×ˢ univ) :=
    (cylLap_contDiffOn hu ht).fderiv_of_isOpen hopen (by norm_num)
  have hD1 : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => Axi.dz (fun q' : ℝ × ℝ => u q'.1 q'.2 t) q)
      (Ioi 0 ×ˢ univ) :=
    hF1.clm_apply contDiffOn_const
  have hdiffAt : DifferentiableAt ℝ
      (fun q : ℝ × ℝ => Axi.dz (fun q' : ℝ × ℝ => u q'.1 q'.2 t) q) p :=
    (hD1.differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hmem)
  have hev : (fun q : ℝ × ℝ => Axi.dz (fun q' : ℝ × ℝ => u q'.1 q'.2 t) q) =ᶠ[𝓝 p]
      (fun q : ℝ × ℝ => physZ u q.1 q.2 t) := by
    filter_upwards [hopen.mem_nhds hmem] with q hq
    exact cylLap_dz_eq hu ht q hq.1
  have hG : DifferentiableAt ℝ (fun q : ℝ × ℝ => physZ u q.1 q.2 t) p :=
    hdiffAt.congr_of_eventuallyEq hev.symm
  show fderiv ℝ (fun q : ℝ × ℝ => Axi.dz (fun q' : ℝ × ℝ => u q'.1 q'.2 t) q) p (0, 1) = _
  rw [hev.fderiv_eq]
  exact cylLap_fderiv_snd (fun q : ℝ × ℝ => physZ u q.1 q.2 t) p hG

/-- The meridional scalar Laplacian `Δ_mer` of a physical slice is the sum of the physical second
derivatives and the first radial derivative over `r`. -/
theorem cylLap_lapMer {u : ℝ → ℝ → ℝ → ℝ} (hu : MeridSmooth 2 u) {t : ℝ} (ht : 0 < t)
    (p : ℝ × ℝ) (hp : 0 < p.1) :
    Axi.lapMer (fun q : ℝ × ℝ => u q.1 q.2 t) p =
      physR (physR u) p.1 p.2 t + physR u p.1 p.2 t / p.1 + physZ (physZ u) p.1 p.2 t := by
  unfold Axi.lapMer
  rw [cylLap_dRho_dRho hu ht p hp, cylLap_dRho_eq hu ht p hp, cylLap_dz_dz hu ht p hp]

/-! ## The target -/

/-- **`CylLapFormula`** (B0187, tex 2883-2886): the Cartesian vector Laplacian of the meridional
lift is the radial and axial cylindrical vector Laplacians, off the axis, for `C²` profiles. -/
theorem cylLapFormula : UnforcedLeray.Short.IIb.CylLapFormula := by
  unfold CylLapFormula
  intro ur uz t x ht hx hur huz
  have hCu : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => ur p.1 p.2 t) (Ioi 0 ×ˢ univ) :=
    cylLap_contDiffOn hur ht
  have hCz : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => uz p.1 p.2 t) (Ioi 0 ×ˢ univ) :=
    cylLap_contDiffOn huz ht
  have hb : ContDiffOn ℝ 2
      (fun p : ℝ × ℝ => ur p.1 p.2 t • Axi.m0 + uz p.1 p.2 t • Axi.m1) (Ioi 0 ×ˢ univ) :=
    (hCu.smul (contDiffOn_const (c := Axi.m0))).add (hCz.smul (contDiffOn_const (c := Axi.m1)))
  have hcyl : cylField ur uz t =
      Axi.liftMer (fun p : ℝ × ℝ => ur p.1 p.2 t • Axi.m0 + uz p.1 p.2 t • Axi.m1) := by
    funext y
    simp [cylField, Axi.liftMer, Axi.mer]
  have hp : 0 < (Axi.mer x).1 := Axi.ϱ_pos hx
  have h0 : Axi.vecLapMer (fun p : ℝ × ℝ => ur p.1 p.2 t • Axi.m0 + uz p.1 p.2 t • Axi.m1)
      (Axi.mer x) 0 = radialVectorLaplacian ur (Axi.ϱ x) (x 2) t := by
    have e : (fun q : ℝ × ℝ => (ur q.1 q.2 t • Axi.m0 + uz q.1 q.2 t • Axi.m1) 0) =
        fun q : ℝ × ℝ => ur q.1 q.2 t := by
      funext q
      simp
    rw [Axi.vecLapMer_apply_zero, e, cylLap_lapMer hur ht (Axi.mer x) hp]
    simp only [radialVectorLaplacian, Axi.mer, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      Axi.m0_zero, Axi.m1_zero, mul_one, mul_zero, add_zero]
    ring
  have h1 : Axi.vecLapMer (fun p : ℝ × ℝ => ur p.1 p.2 t • Axi.m0 + uz p.1 p.2 t • Axi.m1)
      (Axi.mer x) 1 = axialVectorLaplacian uz (Axi.ϱ x) (x 2) t := by
    have e : (fun q : ℝ × ℝ => (ur q.1 q.2 t • Axi.m0 + uz q.1 q.2 t • Axi.m1) 1) =
        fun q : ℝ × ℝ => uz q.1 q.2 t := by
      funext q
      simp
    rw [Axi.vecLapMer_apply_one, e, cylLap_lapMer huz ht (Axi.mer x) hp]
    simp only [axialVectorLaplacian, Axi.mer]
  rw [hcyl, Axi.vecLap_liftMer hb hx]
  unfold Axi.liftMer
  rw [h0, h1]

end UnforcedLeray.Short.IIb
