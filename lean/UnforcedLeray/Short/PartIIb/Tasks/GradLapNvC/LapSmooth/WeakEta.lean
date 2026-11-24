import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_5

/-!
# Part II-b, task `PartII-b:T09/5/2` (`LapWeakEta`): the weak `∂_η` identity is the classical one

Source of record: `the November 2 reference manuscript`, lines 1639-1668 and
1912-1916.

Target: `lapWeakEta_proof : UnforcedLeray.Short.IIb.LapWeakEta`.

Proof outline (as `driftWeakS_proof`, `Tasks/DriftNvC/Smooth/WeakS.lean`, with the first-order
operator `v·∇ + d` in place of `s∂_s`):
* integration by parts in each coordinate direction, for a test `φ`:
  `∫ u · (-∑_j ∂_j(v_j φ) + d φ) = ∫ (∑_j v_j ∂_j u + d u) φ`;
* so the weak derivative `g` and the classical `genOp v d u` agree against all tests on `s > 0`;
  du Bois-Reymond on `{s > 0}` gives `g = genOp v d u` a.e. there;
* for `v = vQ ε`, `d = dQ ε`, `genOp` is componentwise `classQ ε b`.
Helpers are self-contained in this file (namespace `LapWeakEtaHelp`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

namespace LapWeakEtaHelp

/-- Lebesgue measure on the chart `Coord` is an additive Haar measure. -/
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

/-- The classical operator `∑_j v_j ∂_j u + d u` for complex-valued `u`. -/
def genOp (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ) (u : Coord → ℂ) (x : Coord) : ℂ :=
  ∑ j : Fin 3, (v x j : ℂ) * fderiv ℝ u x (cdir j) + (d x : ℂ) * u x

lemma fderiv_dir_continuous {ψ : Coord → ℝ} (hψ : ContDiff ℝ ∞ ψ) (j : Fin 3) :
    Continuous (fun x => fderiv ℝ ψ x (cdir j)) :=
  (hψ.continuous_fderiv (by simp)).clm_apply continuous_const

lemma fderiv_dir_compact {ψ : Coord → ℝ} (hψc : HasCompactSupport ψ) (j : Fin 3) :
    HasCompactSupport (fun x => fderiv ℝ ψ x (cdir j)) :=
  HasCompactSupport.comp_left (g := fun L : Coord →L[ℝ] ℝ => L (cdir j))
    (hψc.fderiv (𝕜 := ℝ)) (by simp)

/-- Integration by parts in one coordinate direction, for a smooth compactly supported `ψ`. -/
lemma ibp_dir {ψ : Coord → ℝ} (hψs : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (u : Coord → ℂ) (hu : ContDiff ℝ ∞ u) (j : Fin 3) :
    ∫ x, u x * (fderiv ℝ ψ x (cdir j) : ℂ) = -∫ x, (ψ x : ℂ) * fderiv ℝ u x (cdir j) := by
  have hD := fderiv_dir_continuous hψs j
  have hDc := fderiv_dir_compact hψc j
  have h1 : Integrable (fun x => fderiv ℝ ψ x (cdir j) • u x) :=
    (hD.smul hu.continuous).integrable_of_hasCompactSupport hDc.smul_right
  have h2 : Integrable (fun x => ψ x • fderiv ℝ u x (cdir j)) :=
    (hψs.continuous.smul ((hu.continuous_fderiv (by simp)).clm_apply continuous_const)
      ).integrable_of_hasCompactSupport hψc.smul_right
  have h3 : Integrable (fun x => ψ x • u x) :=
    (hψs.continuous.smul hu.continuous).integrable_of_hasCompactSupport hψc.smul_right
  have hIBP : ∫ x, ψ x • fderiv ℝ u x (cdir j) = -∫ x, fderiv ℝ ψ x (cdir j) • u x :=
    integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := volume) (𝕜 := ℝ)
      (f := ψ) (g := u) (v := cdir j) h1 h2 h3
      (fun x _ => hψs.differentiable (by simp) x) (fun x _ => hu.differentiable (by simp) x)
  have hL : ∫ x, u x * (fderiv ℝ ψ x (cdir j) : ℂ) = ∫ x, fderiv ℝ ψ x (cdir j) • u x := by
    congr 1
    funext x
    rw [Complex.real_smul, mul_comm]
  have hR : ∫ x, (ψ x : ℂ) * fderiv ℝ u x (cdir j) = ∫ x, ψ x • fderiv ℝ u x (cdir j) := by
    simp only [Complex.real_smul]
  rw [hL, hR, hIBP, neg_neg]

/-- The weak identity `∫ g φ = ∫ u · (transpose)` turns into `∫ genOp · φ`. -/
lemma ibp_gen (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ)
    (hv : ∀ j : Fin 3, ContDiff ℝ ∞ (fun x => v x j)) (hd : ContDiff ℝ ∞ d)
    (u : Coord → ℂ) (hu : ContDiff ℝ ∞ u) (φ : Coord → ℝ) (hφ : IsCoordTest φ) :
    ∫ x, u x * (coordTranspose v d φ x : ℂ) = ∫ x, genOp v d u x * (φ x : ℂ) := by
  have hψs : ∀ j : Fin 3, ContDiff ℝ ∞ (fun y : Coord => v y j * φ y) :=
    fun j => (hv j).mul hφ.smooth
  have hψc : ∀ j : Fin 3, HasCompactSupport (fun y : Coord => v y j * φ y) :=
    fun j => (hφ.compact.mul_left : HasCompactSupport ((fun y : Coord => v y j) * φ))
  -- pointwise splitting of the transpose
  have hsplit : ∀ x : Coord, u x * (coordTranspose v d φ x : ℂ) =
      -(∑ j : Fin 3, u x * (fderiv ℝ (fun y : Coord => v y j * φ y) x (cdir j) : ℂ))
        + u x * ((d x * φ x : ℝ) : ℂ) := by
    intro x
    simp only [coordTranspose, cpd, Complex.ofReal_neg, Complex.ofReal_add, Complex.ofReal_mul,
      Complex.ofReal_sum, mul_add, mul_neg, Finset.mul_sum]
  -- integrability of the pieces
  have hA : ∀ j : Fin 3, Integrable
      (fun x => u x * (fderiv ℝ (fun y : Coord => v y j * φ y) x (cdir j) : ℂ)) := by
    intro j
    have hG : HasCompactSupport
        (fun x => (fderiv ℝ (fun y : Coord => v y j * φ y) x (cdir j) : ℂ)) :=
      HasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (fderiv_dir_compact (hψc j) j)
        (by simp)
    have hGc : Continuous
        (fun x => (fderiv ℝ (fun y : Coord => v y j * φ y) x (cdir j) : ℂ)) :=
      Complex.continuous_ofReal.comp (fderiv_dir_continuous (hψs j) j)
    exact (hu.continuous.mul hGc).integrable_of_hasCompactSupport hG.mul_left
  have hDφ : Integrable (fun x => u x * ((d x * φ x : ℝ) : ℂ)) := by
    have hc : HasCompactSupport (fun x : Coord => ((d x * φ x : ℝ) : ℂ)) :=
      HasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (hφ.compact.mul_left) (by simp)
    have hcont : Continuous (fun x : Coord => ((d x * φ x : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (hd.continuous.mul hφ.smooth.continuous)
    exact (hu.continuous.mul hcont).integrable_of_hasCompactSupport hc.mul_left
  -- pieces of the classical side
  have hB : ∀ j : Fin 3, Integrable
      (fun x => ((v x j * φ x : ℝ) : ℂ) * fderiv ℝ u x (cdir j)) := by
    intro j
    have hc : HasCompactSupport (fun x : Coord => ((v x j * φ x : ℝ) : ℂ)) :=
      HasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (hψc j) (by simp)
    have hcont : Continuous (fun x : Coord => ((v x j * φ x : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (hψs j).continuous
    exact (hcont.mul ((hu.continuous_fderiv (by simp)).clm_apply continuous_const)
      ).integrable_of_hasCompactSupport hc.mul_right
  have hD : Integrable (fun x => u x * ((d x * φ x : ℝ) : ℂ)) := hDφ
  -- the classical side as a sum of integrals
  have hRHS : ∫ x, genOp v d u x * (φ x : ℂ) =
      (∑ j : Fin 3, ∫ x, ((v x j * φ x : ℝ) : ℂ) * fderiv ℝ u x (cdir j))
        + ∫ x, u x * ((d x * φ x : ℝ) : ℂ) := by
    rw [← integral_finset_sum _ (fun j _ => hB j), ← integral_add
      (integrable_finset_sum _ (fun j _ => hB j)) hD]
    congr 1
    funext x
    unfold genOp
    push_cast
    rw [add_mul, Finset.sum_mul]
    congr 1
    · apply Finset.sum_congr rfl
      intro j _
      ring
    · ring
  -- the left side, split and integrated by parts
  have hLHS : ∫ x, u x * (coordTranspose v d φ x : ℂ) =
      (∑ j : Fin 3, ∫ x, ((v x j * φ x : ℝ) : ℂ) * fderiv ℝ u x (cdir j))
        + ∫ x, u x * ((d x * φ x : ℝ) : ℂ) := by
    simp_rw [hsplit]
    have hS : Integrable (fun x => -(∑ j : Fin 3, u x * (fderiv ℝ (fun y : Coord => v y j * φ y) x (cdir j) : ℂ))) :=
      (integrable_finset_sum _ (fun j _ => hA j)).neg
    rw [integral_add hS hD,
      integral_neg, integral_finset_sum _ (fun j _ => hA j)]
    have hj : ∀ j : Fin 3, ∫ x, u x * (fderiv ℝ (fun y : Coord => v y j * φ y) x (cdir j) : ℂ)
        = -∫ x, ((v x j * φ x : ℝ) : ℂ) * fderiv ℝ u x (cdir j) :=
      fun j => ibp_dir (hψs j) (hψc j) u hu j
    simp only [hj, Finset.sum_neg_distrib, neg_neg]
  rw [hLHS, hRHS]

/-- Scalar weak identity on `{s > 0}`: the weak `g` equals the classical `genOp` a.e. -/
lemma weak_gen (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ)
    (hv : ∀ j : Fin 3, ContDiff ℝ ∞ (fun x => v x j)) (hd : ContDiff ℝ ∞ d)
    (u g : Coord → ℂ) (hu : ContDiff ℝ ∞ u) (hw : HasWeakFO v d u g) :
    ∀ᵐ x : Coord, 0 < x.1 → g x = genOp v d u x := by
  have hRc : Continuous (genOp v d u) := by
    unfold genOp
    apply Continuous.add
    · apply continuous_finset_sum
      intro j _
      exact (Complex.continuous_ofReal.comp (hv j).continuous).mul
        ((hu.continuous_fderiv (by simp)).clm_apply continuous_const)
    · exact (Complex.continuous_ofReal.comp hd.continuous).mul hu.continuous
  have hloc : LocallyIntegrableOn (fun x => g x - genOp v d u x) Upos volume :=
    (locInt_of_tests g (fun φ hφ => (hw.1 φ hφ).2)).sub
      (hRc.locallyIntegrable.locallyIntegrableOn Upos)
  have htest : ∀ φ : Coord → ℝ, IsCoordTest φ →
      ∫ x, (g x - genOp v d u x) * (φ x : ℂ) = 0 := by
    intro φ hφ
    have hA : Integrable (fun x => g x * (φ x : ℂ)) := (hw.1 φ hφ).2
    have hφc : HasCompactSupport (fun x => (φ x : ℂ)) := hφ.compact.comp_left Complex.ofReal_zero
    have hB : Integrable (fun x => genOp v d u x * (φ x : ℂ)) :=
      (hRc.mul (Complex.continuous_ofReal.comp hφ.smooth.continuous)).integrable_of_hasCompactSupport
        hφc.mul_left
    have hsub : ∫ x, (g x - genOp v d u x) * (φ x : ℂ) =
        (∫ x, g x * (φ x : ℂ)) - ∫ x, genOp v d u x * (φ x : ℂ) := by
      rw [← integral_sub hA hB]
      congr 1
      funext x
      ring
    rw [hsub]
    exact sub_eq_zero.2 ((hw.2 φ hφ).trans (ibp_gen v d hv hd u hu φ hφ))
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

/-- `vEta` has smooth (constant) components. -/
lemma vEta_component_smooth (j : Fin 3) : ContDiff ℝ ∞ (fun x : Coord => vEta x j) := by
  fin_cases j <;> simp [vEta] <;> exact contDiff_const

end LapWeakEtaHelp

open UnforcedLeray.Short.IIb.LapWeakEtaHelp in
theorem lapWeakEta_proof : UnforcedLeray.Short.IIb.LapWeakEta := by
  intro c b Eb hb hE
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
  have hdZ : ContDiff ℝ ∞ dZero := contDiff_const
  have hcomp : ∀ i : Fin 2, ∀ᵐ x : Coord, 0 < x.1 →
      Eb x i = genOp vEta dZero (fun y => b y i) x :=
    fun i => weak_gen vEta dZero (fun j => vEta_component_smooth j) hdZ
      (fun y => b y i) (fun y => Eb y i) (hcomp_smooth i) (hE i)
  have hall : ∀ᵐ x : Coord, ∀ i : Fin 2, 0 < x.1 →
      Eb x i = genOp vEta dZero (fun y => b y i) x :=
    ae_all_iff.2 hcomp
  filter_upwards [hall] with x hx hpos
  ext i
  rw [hx i hpos]
  simp [genOp, classEta, vEta, dZero, hfd, Fin.sum_univ_three]

end UnforcedLeray.Short.IIb
