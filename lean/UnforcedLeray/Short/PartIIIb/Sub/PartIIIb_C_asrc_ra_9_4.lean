import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5

/-!
# `PartIII-b:C/asrc/ra/9/4` : the pressure piece `RAGeoGradLeaf` (source 5039-5043)

Source: `the November 2 reference manuscript`.

With `F = sΨ_A` (`sPsiPhys`), the ring-chart rules `∂_ρ(F∘chart) = √s(∂_ξ F - ε(2s∂_sF + η∂_ηF))`,
`∂_z(F∘chart) = √s ∂_ηF` (`Axi.radial_chain`, `Axi.axial_chain`) give, on `s > 0`,
`coefOf ε⁻¹ (∇_y F) = s ∇_{q,η}Ψ_A - ε(2s∂_sF + η∂_ηF) e_r` (source 5039-5043: this is
`s ∇Ψ_A + εs(𝒦+2)Ψ_A e_r` up to sign, `𝒦 = 2s∂_s + η∂_η`).  So the piece `geoGradPiece` equals the
explicit remainder `gradRem` on `s > 0`.  `rAGeoGrad_of` reduces `RAGeoGradLeaf` to this identity
(`GeoGradChartEq`), the `C¹` regularity `AffPsiC1` of `sΨ_A` (proved in the area `affineLiftReg`),
and the bound `GradRemBound` of the explicit remainder.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)

/-- `sΨ_A` as a function on the chart. -/
def sPsiChart (p : Params) (χf : ℝ → ℝ) (A : ℝ → Mat3) : Chart → ℝ :=
  fun z => z.1 * PsiA p.ν χf A z.1 z.2

/-- The remainder of the pressure completion: `-ε(2s∂_s F + η∂_η F) e_r`, `F = sΨ_A`
(source 5039-5043). -/
def gradRem (p : Params) (_μ : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) : Chart → Merid :=
  fun q => !₂[-(p.ε * (2 * q.1 * UnforcedLeray.Axi.dS (sPsiChart p χf A) q + q.2.2 * UnforcedLeray.Axi.dEta (sPsiChart p χf A) q)), 0]

/-- **The pointwise chart identity** (source 5039-5043): on `s > 0`, where `sΨ_A` is
differentiable, `geoGradPiece = gradRem`. -/
def GeoGradChartEq : Prop :=
  ∀ (p : Params) (μ : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (q : Chart), 0 < q.1 →
    DifferentiableAt ℝ (sPsiChart p χf A) q → geoGradPiece p μ χf A q = gradRem p μ χf A q

/-- **The bound of the explicit remainder** (source 5039-5043, 5076-5079): `gradRem` satisfies
`RAGeoPieceBound` (Gaussian lattice sums; normalized cell norm of
`ε(2s∂_s + η∂_η)(sΨ_A)` is `≤ P_ν ε M(A)(s^{5/2}+s^{7/2})`, zero for `s > 1.1/ν`, measurable
cell sections). -/
def GradRemBound (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  RAGeoPieceBound as χf (fun p μ A => gradRem p μ χf A)

theorem srcMeasure_nonpos (c : ℝ) : srcMeasure c {q : Chart | q.1 ≤ 0} = 0 := by
  have h : (((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).withDensity
      fun s => ENNReal.ofReal (s ^ (-3 / 2 : ℝ))) (Iic 0) = 0 := by
    rw [withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
    have : Iic (0 : ℝ) ∩ Ioi 0 = ∅ := by ext x; simp
    rw [this]; simp
  have e : {q : Chart | q.1 ≤ 0} = Iic (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := by ext q; simp
  rw [e, srcMeasure, Measure.smul_apply, ageμ, Measure.prod_prod, h, zero_mul, smul_zero]

/-- A bound for `g'` transfers to `g` that agrees with it on `s > 0`. -/
theorem RAGeoPieceBound.congr_pos {as : ℝ} {χf : ℝ → ℝ}
    {g g' : Params → ℝ → (ℝ → Mat3) → Chart → Merid}
    (h : RAGeoPieceBound as χf g')
    (heq : IsSourceCutoffC χf → ∀ (p : Params) (μ : ℝ) (A : ℝ → Mat3), IsAffElem as A →
      ∀ q : Chart, 0 < q.1 → g p μ A q = g' p μ A q) :
    RAGeoPieceBound as χf g := by
  intro hχ K hK hKs dm dp hdm
  obtain ⟨C, k, ν₀, hν₀, H⟩ := h hχ K hK hKs dm dp hdm
  refine ⟨C, k, ν₀, hν₀, fun p d hreg hν μ hμ A hA => ?_⟩
  obtain ⟨m, z, sm, b⟩ := H p d hreg hν μ hμ A hA
  have hE := heq hχ p μ A hA
  have hae : g p μ A =ᵐ[srcMeasure p.c] g' p μ A := by
    refine measure_mono_null (fun q hq => ?_) (srcMeasure_nonpos p.c)
    by_contra hpos
    exact hq (hE q (not_le.1 hpos))
  refine ⟨(m.congr hae.symm), fun s hs x => ?_, fun s hs => ?_, fun s hs hsT => ?_⟩
  · rw [hE (s, x) (by have := p.ν_pos; have : 0 < (11 / 10) / p.ν := by positivity
                      exact this.trans hs)]
    exact z s hs x
  · have hsec : ∀ x : ℝ × ℝ, g p μ A (s, x) = g' p μ A (s, x) := fun x => hE (s, x) hs
    have : (fun x : ℝ × ℝ => g p μ A (s, x)) = fun x => g' p μ A (s, x) := funext hsec
    rw [this]; exact sm s hs
  · have hsec : ∀ x : ℝ × ℝ, g p μ A (s, x) = g' p μ A (s, x) := fun x => hE (s, x) hs
    simp only [hsec]; exact b s hs hsT

/-- **`rAGeoGrad` from the pointwise identity, the `C¹` regularity of `sΨ_A` and the remainder
bound.** -/
theorem rAGeoGrad_of (as : ℝ) (χf : ℝ → ℝ) (h1 : GeoGradChartEq) (h2 : AffPsiC1 as χf)
    (h3 : GradRemBound as χf) : RAGeoGradLeaf as χf := by
  refine RAGeoPieceBound.congr_pos h3 ?_
  intro hχ p μ A hA q hq
  refine h1 p μ χf A q hq ?_
  have hc := h2 hχ p.ν p.ν_pos A hA
  have hmem : q ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := ⟨hq, mem_univ _⟩
  exact (hc.differentiableOn one_ne_zero).differentiableAt
    ((isOpen_Ioi.prod isOpen_univ).mem_nhds hmem)

end UnforcedLeray.Short.PartIIIb.Concrete
