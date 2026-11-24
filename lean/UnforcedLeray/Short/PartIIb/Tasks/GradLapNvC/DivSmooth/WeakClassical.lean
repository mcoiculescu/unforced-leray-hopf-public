import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_1

/-!
# Part II-b, task `PartII-b:T09/1/1`: the weak first-order identity `g = v·∇b + d b` on `s > 0`

Source of record: `the November 2 reference manuscript`, lines 1639-1668 and
1912-1916 (divergence of the ring lift; `Q_ε`, `∂_η` in the chart).

Target: `divWeakClassical_proof : UnforcedLeray.Short.IIb.DivWeakClassical`.

Proof outline (generalises `driftWeakS_proof`, `Tasks/DriftNvC/Smooth/WeakS.lean`, to general
smooth `v, d`), componentwise `u = b · i`:
* `ibp_dir`: integration by parts in one coordinate direction for compactly supported `f`;
* `ibp_gen`: for a test `φ`, `∫ u · coordTranspose v d φ = ∫ (v·∇u + d u) φ` (three directions);
* `div_scalar`: the weak identity gives `g = v·∇u + d u` a.e. on `s > 0`
  (fundamental lemma on `{s > 0}`);
* the theorem: componentwise, with `ae_all_iff`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

namespace DivWeakClassicalHelp

/-- Lebesgue measure on the chart `Coord = ℝ × (ℝ × ℝ)` is an additive Haar measure. -/
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

/-- The classical scalar expression `v·∇u + d u` (`∂_0, ∂_1, ∂_2 = ∂_s, ∂_q, ∂_η`). -/
def divF (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ) (u : Coord → ℂ) : Coord → ℂ :=
  fun x => (∑ j : Fin 3, (v x j : ℂ) * fderiv ℝ u x (cdir j)) + (d x : ℂ) * u x

/-- Integrability of the three terms of a one-direction integration by parts. -/
lemma dir_int (f : Coord → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (u : Coord → ℂ) (hu : ContDiff ℝ ∞ u) (w : Coord) :
    Integrable (fun x => fderiv ℝ f x w • u x) ∧
    Integrable (fun x => f x • fderiv ℝ u x w) ∧
    Integrable (fun x => f x • u x) := by
  have hDc : HasCompactSupport (fun x => fderiv ℝ f x w) :=
    HasCompactSupport.comp_left (g := fun L : Coord →L[ℝ] ℝ => L w)
      (hfc.fderiv (𝕜 := ℝ)) (by simp)
  have hD : Continuous (fun x => fderiv ℝ f x w) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  refine ⟨?_, ?_, ?_⟩
  · exact (hD.smul hu.continuous).integrable_of_hasCompactSupport hDc.smul_right
  · exact (hf.continuous.smul ((hu.continuous_fderiv (by simp)).clm_apply
      continuous_const)).integrable_of_hasCompactSupport hfc.smul_right
  · exact (hf.continuous.smul hu.continuous).integrable_of_hasCompactSupport hfc.smul_right

/-- Integration by parts in one direction. -/
lemma ibp_dir (f : Coord → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (u : Coord → ℂ) (hu : ContDiff ℝ ∞ u) (w : Coord) :
    ∫ x, fderiv ℝ f x w • u x = -∫ x, f x • fderiv ℝ u x w := by
  obtain ⟨h1, h2, h3⟩ := dir_int f hf hfc u hu w
  haveI : (volume : Measure Coord).IsAddHaarMeasure := instIsAddHaarVolCoord
  have key := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := volume) (𝕜 := ℝ)
    (f := f) (g := u) (v := w) h1 h2 h3
    (fun x _ => hf.differentiable (by simp) x) (fun x _ => hu.differentiable (by simp) x)
  rw [key, neg_neg]

/-- The integration by parts identity against a test: the transpose of `v·∇ + d` is integrated
by parts term by term. -/
lemma ibp_gen (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ) (u : Coord → ℂ) (hu : ContDiff ℝ ∞ u)
    (hv : ∀ j, ContDiff ℝ ∞ (fun x => v x j)) (hd : ContDiff ℝ ∞ d) (φ : Coord → ℝ)
    (hφ : IsCoordTest φ) :
    ∫ x, u x * (coordTranspose v d φ x : ℂ) = ∫ x, divF v d u x * (φ x : ℂ) := by
  have hp0 : ContDiff ℝ ∞ (fun y : Coord => v y 0 * φ y) := (hv 0).mul hφ.smooth
  have hp1 : ContDiff ℝ ∞ (fun y : Coord => v y 1 * φ y) := (hv 1).mul hφ.smooth
  have hp2 : ContDiff ℝ ∞ (fun y : Coord => v y 2 * φ y) := (hv 2).mul hφ.smooth
  have hpc0 : HasCompactSupport (fun y : Coord => v y 0 * φ y) := hφ.compact.mul_left
  have hpc1 : HasCompactSupport (fun y : Coord => v y 1 * φ y) := hφ.compact.mul_left
  have hpc2 : HasCompactSupport (fun y : Coord => v y 2 * φ y) := hφ.compact.mul_left
  have hL : ∀ x, u x * (coordTranspose v d φ x : ℂ) =
      -(fderiv ℝ (fun y : Coord => v y 0 * φ y) x (cdir 0) • u x)
        + -(fderiv ℝ (fun y : Coord => v y 1 * φ y) x (cdir 1) • u x)
        + -(fderiv ℝ (fun y : Coord => v y 2 * φ y) x (cdir 2) • u x)
        + (d x * φ x) • u x := by
    intro x
    simp only [coordTranspose, cpd, Fin.sum_univ_three, Complex.real_smul]
    push_cast
    ring
  have hR : ∀ x, divF v d u x * (φ x : ℂ) =
      ((v x 0 * φ x) • fderiv ℝ u x (cdir 0) + (v x 1 * φ x) • fderiv ℝ u x (cdir 1)
        + (v x 2 * φ x) • fderiv ℝ u x (cdir 2)) + (d x * φ x) • u x := by
    intro x
    simp only [divF, Fin.sum_univ_three, Complex.real_smul]
    push_cast
    ring
  have hA0 : Integrable (fun x => fderiv ℝ (fun y : Coord => v y 0 * φ y) x (cdir 0) • u x) :=
    (dir_int _ hp0 hpc0 u hu (cdir 0)).1
  have hA1 : Integrable (fun x => fderiv ℝ (fun y : Coord => v y 1 * φ y) x (cdir 1) • u x) :=
    (dir_int _ hp1 hpc1 u hu (cdir 1)).1
  have hA2 : Integrable (fun x => fderiv ℝ (fun y : Coord => v y 2 * φ y) x (cdir 2) • u x) :=
    (dir_int _ hp2 hpc2 u hu (cdir 2)).1
  have hC0 : Integrable (fun x => (v x 0 * φ x) • fderiv ℝ u x (cdir 0)) :=
    (dir_int _ hp0 hpc0 u hu (cdir 0)).2.1
  have hC1 : Integrable (fun x => (v x 1 * φ x) • fderiv ℝ u x (cdir 1)) :=
    (dir_int _ hp1 hpc1 u hu (cdir 1)).2.1
  have hC2 : Integrable (fun x => (v x 2 * φ x) • fderiv ℝ u x (cdir 2)) :=
    (dir_int _ hp2 hpc2 u hu (cdir 2)).2.1
  have hB : Integrable (fun x => (d x * φ x) • u x) := by
    have hdc : HasCompactSupport (fun x => d x * φ x) := hφ.compact.mul_left
    exact ((hd.continuous.mul hφ.smooth.continuous).smul hu.continuous).integrable_of_hasCompactSupport
      hdc.smul_right
  have i0 : ∫ x, fderiv ℝ (fun y : Coord => v y 0 * φ y) x (cdir 0) • u x =
      -∫ x, (v x 0 * φ x) • fderiv ℝ u x (cdir 0) :=
    ibp_dir _ hp0 hpc0 u hu (cdir 0)
  have i1 : ∫ x, fderiv ℝ (fun y : Coord => v y 1 * φ y) x (cdir 1) • u x =
      -∫ x, (v x 1 * φ x) • fderiv ℝ u x (cdir 1) :=
    ibp_dir _ hp1 hpc1 u hu (cdir 1)
  have i2 : ∫ x, fderiv ℝ (fun y : Coord => v y 2 * φ y) x (cdir 2) • u x =
      -∫ x, (v x 2 * φ x) • fderiv ℝ u x (cdir 2) :=
    ibp_dir _ hp2 hpc2 u hu (cdir 2)
  have hA0n : Integrable (fun x => -(fderiv ℝ (fun y : Coord => v y 0 * φ y) x (cdir 0) • u x)) :=
    hA0.neg
  have hA1n : Integrable (fun x => -(fderiv ℝ (fun y : Coord => v y 1 * φ y) x (cdir 1) • u x)) :=
    hA1.neg
  have hA2n : Integrable (fun x => -(fderiv ℝ (fun y : Coord => v y 2 * φ y) x (cdir 2) • u x)) :=
    hA2.neg
  have hX1 : Integrable (fun x => -(fderiv ℝ (fun y : Coord => v y 0 * φ y) x (cdir 0) • u x)
      + -(fderiv ℝ (fun y : Coord => v y 1 * φ y) x (cdir 1) • u x)) :=
    hA0n.add hA1n
  have hX : Integrable (fun x => -(fderiv ℝ (fun y : Coord => v y 0 * φ y) x (cdir 0) • u x)
      + -(fderiv ℝ (fun y : Coord => v y 1 * φ y) x (cdir 1) • u x)
      + -(fderiv ℝ (fun y : Coord => v y 2 * φ y) x (cdir 2) • u x)) :=
    hX1.add hA2n
  have hY1 : Integrable (fun x => (v x 0 * φ x) • fderiv ℝ u x (cdir 0)
      + (v x 1 * φ x) • fderiv ℝ u x (cdir 1)) :=
    hC0.add hC1
  have hY : Integrable (fun x => (v x 0 * φ x) • fderiv ℝ u x (cdir 0)
      + (v x 1 * φ x) • fderiv ℝ u x (cdir 1) + (v x 2 * φ x) • fderiv ℝ u x (cdir 2)) :=
    hY1.add hC2
  simp only [hL, hR]
  rw [integral_add hX hB, integral_add hY hB, integral_add hX1 hA2n, integral_add hA0n hA1n,
    integral_neg, integral_neg, integral_neg, integral_add hY1 hC2, integral_add hC0 hC1,
    i0, i1, i2]
  ring

/-- Scalar weak identity on `{s > 0}`. -/
lemma div_scalar (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ) (u g : Coord → ℂ)
    (hu : ContDiff ℝ ∞ u) (hv : ∀ j, ContDiff ℝ ∞ (fun x => v x j)) (hd : ContDiff ℝ ∞ d)
    (hw : HasWeakFO v d u g) :
    ∀ᵐ x : Coord, 0 < x.1 → g x = divF v d u x := by
  have hvc : ∀ j, Continuous (fun x => (v x j : ℂ)) := fun j =>
    Complex.continuous_ofReal.comp (hv j).continuous
  have hDc : ∀ j, Continuous (fun x => fderiv ℝ u x (cdir j)) := fun j =>
    (hu.continuous_fderiv (by simp)).clm_apply continuous_const
  have hFc : Continuous (divF v d u) := by
    unfold divF
    exact (continuous_finsetSum Finset.univ (fun j _ => (hvc j).mul (hDc j))).add
      ((Complex.continuous_ofReal.comp hd.continuous).mul hu.continuous)
  have hloc : LocallyIntegrableOn (fun x => g x - divF v d u x) Upos volume :=
    (locInt_of_tests g (fun φ hφ => (hw.1 φ hφ).2)).sub
      (hFc.locallyIntegrable.locallyIntegrableOn Upos)
  have htest : ∀ φ : Coord → ℝ, IsCoordTest φ →
      ∫ x, (g x - divF v d u x) * (φ x : ℂ) = 0 := by
    intro φ hφ
    have hA : Integrable (fun x => g x * (φ x : ℂ)) := (hw.1 φ hφ).2
    have hφc : HasCompactSupport (fun x => (φ x : ℂ)) := hφ.compact.comp_left Complex.ofReal_zero
    have hB : Integrable (fun x => divF v d u x * (φ x : ℂ)) :=
      (hFc.mul (Complex.continuous_ofReal.comp hφ.smooth.continuous)).integrable_of_hasCompactSupport
        hφc.mul_left
    have hsub : ∫ x, (g x - divF v d u x) * (φ x : ℂ) =
        (∫ x, g x * (φ x : ℂ)) - ∫ x, divF v d u x * (φ x : ℂ) := by
      rw [← integral_sub hA hB]
      congr 1
      funext x
      ring
    rw [hsub, hw.2 φ hφ, ibp_gen v d u hu hv hd φ hφ, sub_self]
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

end DivWeakClassicalHelp

open DivWeakClassicalHelp in
/-- **Leaf `T09/1/1`**: for nice `b`, `HasWeakVec v d b g` forces `g = v·∇b + d b` a.e. on `s > 0`. -/
theorem divWeakClassical_proof : UnforcedLeray.Short.IIb.DivWeakClassical := by
  intro v d c b g hv hd hb hw
  have hsmooth : ContDiff ℝ ∞ b := hb.1
  have hcomp_smooth : ∀ i : Fin 2, ContDiff ℝ ∞ (fun y => b y i) := by
    intro i
    exact ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hsmooth
  have hfd : ∀ (i : Fin 2) (x : Coord) (w : Coord),
      fderiv ℝ (fun y => b y i) x w = fderiv ℝ b x w i := by
    intro i x w
    have hbd : DifferentiableAt ℝ b x := hsmooth.differentiable (by simp) x
    have hL := ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).restrictScalars ℝ).hasFDerivAt.comp
      x hbd.hasFDerivAt
    have hL' : fderiv ℝ (fun y => b y i) x =
        ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).restrictScalars ℝ).comp (fderiv ℝ b x) :=
      hL.fderiv
    rw [hL']
    simp
  have hcomp : ∀ i : Fin 2, ∀ᵐ x : Coord, 0 < x.1 →
      g x i = divF v d (fun y => b y i) x :=
    fun i => div_scalar v d (fun y => b y i) (fun y => g y i) (hcomp_smooth i) hv hd (hw i)
  have hall : ∀ᵐ x : Coord, ∀ i : Fin 2, 0 < x.1 →
      g x i = divF v d (fun y => b y i) x :=
    ae_all_iff.2 hcomp
  filter_upwards [hall] with x hx hpos
  ext i
  rw [hx i hpos]
  simp [classOp, divF, hfd, Finset.sum_apply, Complex.real_smul]

end UnforcedLeray.Short.IIb
