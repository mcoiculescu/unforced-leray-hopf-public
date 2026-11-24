import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T08_1

/-!
# Part II-b, task `PartII-b:T08/1/1`: the weak drift identity `Sb = s ∂_s b` on `s > 0`

Source of record: `the November 2 reference manuscript`, lines 1912-1915.

Target: `driftWeakS_proof : UnforcedLeray.Short.IIb.DriftWeakS`.

Proof outline. Componentwise (`i : Fin 2`) with `u = b · i` smooth:
* the weak identity against a test `φ` reads `∫ g φ = ∫ u · (-(∂_s(sφ)))`;
* integration by parts in `s` gives `∫ g φ = ∫ s ∂_s u · φ`;
* `g - s ∂_s u` is locally integrable on `{s > 0}` (from the test-integrability clause through
  bumps), so the fundamental lemma `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` gives
  a.e. vanishing on `{s > 0}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

namespace DriftWeakSHelp

/-- Lebesgue measure on the chart `Coord = ℝ × (ℝ × ℝ)` is an additive Haar measure (instance
search does not see the defeq `volume = volume.prod volume`, so it is stated explicitly). -/
instance instIsAddHaarVolCoord : Measure.IsAddHaarMeasure (volume : Measure Coord) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- The open half space `{s > 0}`. -/
abbrev Upos : Set Coord := Ioi (0 : ℝ) ×ˢ univ

lemma mem_Upos {x : Coord} : x ∈ Upos ↔ 0 < x.1 := by
  simp [Upos]

/-- A bump at `x` (for `0 < x.1`) with inner radius `x.1/4` and outer radius `x.1/2`. -/
def mkBump (x : Coord) (hx : 0 < x.1) : ContDiffBump x :=
  { rIn := x.1 / 4
    rOut := x.1 / 2
    rIn_pos := by linarith
    rIn_lt_rOut := by linarith }

lemma mkBump_isTest (x : Coord) (hx : 0 < x.1) :
    IsCoordTest (((mkBump x hx : ContDiffBump x)) : Coord → ℝ) := by
  refine ⟨(mkBump x hx).contDiff, (mkBump x hx).hasCompactSupport, ?_⟩
  rw [(mkBump x hx).tsupport_eq]
  intro y hy
  have hy' : dist y x ≤ x.1 / 2 := by
    simpa [mkBump] using hy
  have hd : dist y.1 x.1 ≤ dist y x := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  rw [Real.dist_eq] at hd
  have h1 : |y.1 - x.1| ≤ x.1 / 2 := hd.trans hy'
  have h2 := (abs_le.mp h1).1
  refine ⟨?_, trivial⟩
  show 0 < y.1
  linarith

/-- Local integrability on `{s > 0}` from the integrability clause of test pairings. -/
lemma locInt_of_tests (g : Coord → ℂ)
    (hg : ∀ φ : Coord → ℝ, IsCoordTest φ → Integrable (fun x => g x * (φ x : ℂ))) :
    LocallyIntegrableOn g Upos volume := by
  intro x hx
  have hx' : 0 < x.1 := mem_Upos.1 hx
  have hT := mkBump_isTest x hx'
  have hint := (hg _ hT).integrableOn (s := Metric.closedBall x (mkBump x hx').rIn)
  have hcongr : IntegrableOn g (Metric.closedBall x (mkBump x hx').rIn) volume := by
    refine hint.congr_fun (fun y hy => ?_) measurableSet_closedBall
    have h1 : (mkBump x hx') y = 1 := (mkBump x hx').one_of_mem_closedBall hy
    simp [h1]
  refine ⟨Metric.closedBall x (mkBump x hx').rIn, mem_nhdsWithin_of_mem_nhds ?_, hcongr⟩
  exact Metric.closedBall_mem_nhds x (mkBump x hx').rIn_pos

/-- Integration by parts in `s` for a test: `∫ u · ct φ = ∫ s ∂_s u · φ`. -/
lemma ibp_test (u : Coord → ℂ) (hu : ContDiff ℝ ∞ u) (φ : Coord → ℝ) (hφ : IsCoordTest φ) :
    ∫ x, u x * (coordTranspose vS dZero φ x : ℂ) =
      ∫ x, (x.1 : ℂ) * fderiv ℝ u x (cdir 0) * (φ x : ℂ) := by
  have hψs : ContDiff ℝ ∞ (fun y : Coord => y.1 * φ y) := contDiff_fst.mul hφ.smooth
  have hψc : HasCompactSupport (fun y : Coord => y.1 * φ y) :=
    (hφ.compact.mul_left : HasCompactSupport ((fun y : Coord => y.1) * φ))
  have hct : ∀ x, coordTranspose vS dZero φ x =
      -(fderiv ℝ (fun y : Coord => y.1 * φ y) x (cdir 0)) := by
    intro x
    simp [coordTranspose, cpd, vS, dZero, Fin.sum_univ_three]
  have hcompl : ∀ x, (coordTranspose vS dZero φ x : ℂ) =
      -((fderiv ℝ (fun y : Coord => y.1 * φ y) x (cdir 0) : ℝ) : ℂ) := by
    intro x
    rw [hct x, Complex.ofReal_neg]
  have hD : Continuous (fun x => fderiv ℝ (fun y : Coord => y.1 * φ y) x (cdir 0)) :=
    (hψs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDc : HasCompactSupport (fun x => fderiv ℝ (fun y : Coord => y.1 * φ y) x (cdir 0)) :=
    HasCompactSupport.comp_left (g := fun L : Coord →L[ℝ] ℝ => L (cdir 0))
      (hψc.fderiv (𝕜 := ℝ)) (by simp)
  have h1 : Integrable (fun x => fderiv ℝ (fun y : Coord => y.1 * φ y) x (cdir 0) • u x) :=
    (hD.smul hu.continuous).integrable_of_hasCompactSupport hDc.smul_right
  have h2 : Integrable (fun x => (x.1 * φ x) • fderiv ℝ u x (cdir 0)) :=
    (hψs.continuous.smul ((hu.continuous_fderiv (by simp)).clm_apply continuous_const)
      ).integrable_of_hasCompactSupport hψc.smul_right
  have h3 : Integrable (fun x => (x.1 * φ x) • u x) :=
    (hψs.continuous.smul hu.continuous).integrable_of_hasCompactSupport hψc.smul_right
  haveI : (volume : Measure Coord).IsAddHaarMeasure := instIsAddHaarVolCoord
  have hIBP : ∫ x, (x.1 * φ x) • fderiv ℝ u x (cdir 0) =
      -∫ x, fderiv ℝ (fun y : Coord => y.1 * φ y) x (cdir 0) • u x :=
    integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := volume) (𝕜 := ℝ)
      (f := fun y : Coord => y.1 * φ y) (g := u) (v := cdir 0) h1 h2 h3
      (fun x _ => hψs.differentiable (by simp) x) (fun x _ => hu.differentiable (by simp) x)
  have hL : ∫ x, u x * (coordTranspose vS dZero φ x : ℂ) =
      -∫ x, fderiv ℝ (fun y : Coord => y.1 * φ y) x (cdir 0) • u x := by
    rw [← integral_neg]
    congr 1
    funext x
    rw [hcompl x, Complex.real_smul]
    ring
  rw [hL, ← hIBP]
  congr 1
  funext x
  simp only [Complex.real_smul]
  push_cast
  ring

/-- Scalar weak drift identity on `{s > 0}`. -/
lemma drift_scalar (u g : Coord → ℂ) (hu : ContDiff ℝ ∞ u) (hw : HasWeakFO vS dZero u g) :
    ∀ᵐ x : Coord, 0 < x.1 → g x = (x.1 : ℂ) * fderiv ℝ u x (cdir 0) := by
  have h2c : Continuous (fun x : Coord => (x.1 : ℂ) * fderiv ℝ u x (cdir 0)) :=
    Continuous.mul (Complex.continuous_ofReal.comp continuous_fst)
      ((hu.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hloc : LocallyIntegrableOn (fun x => g x - (x.1 : ℂ) * fderiv ℝ u x (cdir 0)) Upos volume :=
    (locInt_of_tests g (fun φ hφ => (hw.1 φ hφ).2)).sub
      (h2c.locallyIntegrable.locallyIntegrableOn Upos)
  have htest : ∀ φ : Coord → ℝ, IsCoordTest φ →
      ∫ x, (g x - (x.1 : ℂ) * fderiv ℝ u x (cdir 0)) * (φ x : ℂ) = 0 := by
    intro φ hφ
    have hA : Integrable (fun x => g x * (φ x : ℂ)) := (hw.1 φ hφ).2
    have hφc : HasCompactSupport (fun x => (φ x : ℂ)) := hφ.compact.comp_left Complex.ofReal_zero
    have hB : Integrable (fun x => (x.1 : ℂ) * fderiv ℝ u x (cdir 0) * (φ x : ℂ)) :=
      (h2c.mul (Complex.continuous_ofReal.comp hφ.smooth.continuous)).integrable_of_hasCompactSupport
        hφc.mul_left
    have hsub : ∫ x, (g x - (x.1 : ℂ) * fderiv ℝ u x (cdir 0)) * (φ x : ℂ) =
        (∫ x, g x * (φ x : ℂ)) - ∫ x, (x.1 : ℂ) * fderiv ℝ u x (cdir 0) * (φ x : ℂ) := by
      rw [← integral_sub hA hB]
      congr 1
      funext x
      ring
    rw [hsub, hw.2 φ hφ, ibp_test u hu φ hφ, sub_self]
  have hae := (isOpen_Ioi.prod isOpen_univ).ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (by
    intro χ hχs hχc hχU
    have hχt : IsCoordTest χ := ⟨hχs, hχc, hχU⟩
    have hχ := htest χ hχt
    simp only [Complex.real_smul]
    convert hχ using 2
    funext x
    ring)
  filter_upwards [hae] with x hx hpos
  exact sub_eq_zero.1 (hx (mem_Upos.2 hpos))

end DriftWeakSHelp

end UnforcedLeray.Short.IIb

open UnforcedLeray.Short.IIb DriftWeakSHelp in
theorem driftWeakS_proof : UnforcedLeray.Short.IIb.DriftWeakS := by
  intro c b Sb hb hw
  have hsmooth : ContDiff ℝ ∞ b := hb.1
  have hcomp_smooth : ∀ i : Fin 2, ContDiff ℝ ∞ (fun y => b y i) := by
    intro i
    exact ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hsmooth
  have hfd : ∀ (i : Fin 2) (x : Coord) (v : Coord),
      fderiv ℝ (fun y => b y i) x v = fderiv ℝ b x v i := by
    intro i x v
    have hbd : DifferentiableAt ℝ b x := hsmooth.differentiable (by simp) x
    have hL := ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).restrictScalars ℝ).hasFDerivAt.comp
      x hbd.hasFDerivAt
    have hL' : fderiv ℝ (fun y => b y i) x =
        ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).restrictScalars ℝ).comp (fderiv ℝ b x) :=
      hL.fderiv
    rw [hL']
    simp
  have hcomp : ∀ i : Fin 2, ∀ᵐ x : Coord, 0 < x.1 →
      Sb x i = (x.1 : ℂ) * fderiv ℝ (fun y => b y i) x (cdir 0) :=
    fun i => drift_scalar (fun y => b y i) (fun y => Sb y i) (hcomp_smooth i) (hw i)
  have hall : ∀ᵐ x : Coord, ∀ i : Fin 2, 0 < x.1 →
      Sb x i = (x.1 : ℂ) * fderiv ℝ (fun y => b y i) x (cdir 0) :=
    ae_all_iff.2 hcomp
  filter_upwards [hall] with x hx hpos
  ext i
  rw [hx i hpos, hfd]
  simp [Complex.real_smul]
