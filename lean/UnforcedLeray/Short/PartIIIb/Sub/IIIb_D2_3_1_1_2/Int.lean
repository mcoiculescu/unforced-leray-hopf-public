import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2

/-!
# Integrability of the `sepW` integrand (`PartIII-b:IIIb-D2/3/1/2/3/2/org`)

Source of record: `the November 2 reference manuscript`
3611-3621 (`sep:resolvent`: `W_μ` is a double integral over `(λ, z)`), 4171-4178 (rotation
equivariance of `X₀`).

`IIIa.sepW` is a componentwise Bochner integral, so a matrix `M` mixing the components commutes
with it only when the integrand is integrable (otherwise the junk value `0` of one component and
the integral of the mixed component disagree).  `SepIntegrableAt` is the integrability of the full
integrand on `(0,1) × Space` (`sepRho`); by Fubini it gives the integrability in `z` for a.e.
`l`, and in `l` of the inner integral (`sepW_eq_integral`).  `sepIntegrableAt_of_source` proves it
for a separated source at every `y` off the source disk.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The integrand of `sepW ν μ T · τ` is integrable on `(0,1) × Space` at the point `y`. -/
def SepIntegrableAt (ν : ℝ) (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (y : Space)
    (τ : ℝ) : Prop :=
  ∀ i : Fin 3, Integrable (fun p => sepPhi ν μ T τ i p y) sepRho

/-- For a separated source with finite `Y₂` moment, the integrand is integrable at every `y`
off the source disk (the gap majorant, as in `sepWSmoothOn_of_of`). -/
theorem sepIntegrableAt_of_source (hK : IIIa.SepKernelBounds) (h3 : SepPhiMeasurable)
    (h4 : SepGapPointwise) (h5 : SepGapMajorantIntegrable) (ν : ℝ) (μ : ℂ) (rOut P : ℝ)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (hν : 0 < ν) (hμ : -(1 / 4) < μ.re)
    (hr : 0 ≤ rOut) (hP : 0 < P) (hS : IIIa.IsSepSource P rOut T) (hM : SepMoment P T)
    (τ : ℝ) (y : Space) (hy : rOut < ϱ y) : SepIntegrableAt ν μ T y τ := by
  intro i
  obtain ⟨ε, hε, C, hC0, hb⟩ := h4 hK ν μ rOut P T hν hμ hr hP hS τ i y hy
  have hint : Integrable (fun p => C * sepMajorant μ T τ 0 p) sepRho :=
    (h5 μ P rOut T hμ hP hS hM τ 0 (by norm_num)).const_mul C
  have hm : AEStronglyMeasurable (fun p => sepPhi ν μ T τ i p y) sepRho := by
    have := (continuousMultilinearCurryFin0 ℝ Space ℂ).continuous.comp_aestronglyMeasurable
      (h3 ν μ P rOut T hν hS τ i 0 (by norm_num) y)
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    simp [iteratedFDeriv_zero_eq_comp]
  refine Integrable.mono' hint hm ?_
  filter_upwards [ae_mem_Ioo_sepRho] with p hp
  have := hb y (Metric.mem_ball_self hε) p.1 hp p.2 0 (by norm_num)
  simpa [norm_iteratedFDeriv_zero] using this

/-- **Integrability for separated sources** (3611-3621): the integrand of `sepW` is integrable at
every `y` off the source disk, for every separated source with finite `Y₂` moment. -/
def SepIntegrableOfSource : Prop :=
  ∀ (ν : ℝ) (μ : ℂ) (rOut P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ),
    0 < ν → -(1 / 4) < μ.re → 0 ≤ rOut → 0 < P → IIIa.IsSepSource P rOut T → SepMoment P T →
    ∀ (τ : ℝ) (y : Space), rOut < ϱ y → SepIntegrableAt ν μ T y τ

theorem sepIntegrableOfSource_of (hK : IIIa.SepKernelBounds) (h3 : SepPhiMeasurable)
    (h4 : SepGapPointwise) (h5 : SepGapMajorantIntegrable) : SepIntegrableOfSource :=
  fun ν μ rOut P T hν hμ hr hP hS hM τ y hy =>
    sepIntegrableAt_of_source hK h3 h4 h5 ν μ rOut P T hν hμ hr hP hS hM τ y hy

/-- **`sepW` integrability sees only the a.e. class of the source** (3611-3621; for fixed `τ`,
`l ↦ τ + 2 log l` is a diffeomorphism of `(0,1)` onto `(-∞, τ)`, so null sets of `(τ', z)` pull
back to `sepRho`-null sets of `(l, z)`): if `T₁ = T₂` for a.e. `(τ', z)` then the integrand of `T₁`
is integrable at `(y, τ)` iff that of `T₂` is. -/
def SepIntegrableCongrAE : Prop :=
  ∀ (ν : ℝ) (μ : ℂ) (T₁ T₂ : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ),
    (∀ᵐ x : ℝ × Space ∂volume, T₁ x.1 x.2 = T₂ x.1 x.2) →
      ∀ (y : Space) (τ : ℝ), SepIntegrableAt ν μ T₂ y τ → SepIntegrableAt ν μ T₁ y τ

end UnforcedLeray.Short.PartIIIb.Concrete
