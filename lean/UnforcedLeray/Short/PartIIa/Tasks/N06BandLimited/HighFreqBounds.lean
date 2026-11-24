import UnforcedLeray.Short.PartIIa.Tasks.N06BandLimited.BoxFourier
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# High-Frequency `L²(Box)` Decay from `HasWeakCellH1` and `HasCellH14` (`HighFreqBounds`)

Defines the physical-wavenumber frequency box `freqSet B N` on `B : BoxParams`, proves the
low-frequency wavenumber bounds (`|ws|, |wq|, |wη| ≤ 2π N`) and high-frequency dichotomy
(`2π N < max(|ws|, |wq|, |wη|)`), and proves the unweighted `L²(B.boxMeas)` projection error bounds:
* `h1_highFreq_bound`: `∫ ‖u - projMerid B N u‖² ∂B.boxMeas ≤ N⁻¹ ^ 2 * cellH1Norm B.c u ds dq deta ^ 2`
  for `HasWeakCellH1`;
* `h14_highFreq_bound`:
  `∫ ‖u - projMerid B N u‖² ∂B.boxMeas ≤ 6 * δ ^ (-3/2) * N ^ (-1/2) * cellH14Norm B.c u ^ 2`
  for `HasCellH14`, with `δ = min (min (1/2) (B.σ / 4)) (B.c / 2)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa.N06Aux

open UnforcedLeray.B0220 UnforcedLeray.B0223

namespace BoxParams

/-! ### 1. Angular wavenumbers and physical-frequency cutoff `freqSet B N` -/

def ws (B : BoxParams) (n : ℤ × ℤ × ℤ) : ℝ := 2 * Real.pi * (n.1 : ℝ) / B.Ts
def wq (B : BoxParams) (n : ℤ × ℤ × ℤ) : ℝ := 2 * Real.pi * (n.2.1 : ℝ) / B.c
def wη (B : BoxParams) (n : ℤ × ℤ × ℤ) : ℝ := 2 * Real.pi * (n.2.2 : ℝ) / B.Tη

def Ms (B : BoxParams) (N : ℝ) : ℕ := ⌊N * B.Ts⌋₊
def Mq (B : BoxParams) (N : ℝ) : ℕ := ⌊N * B.c⌋₊
def Mη (B : BoxParams) (N : ℝ) : ℕ := ⌊N * B.Tη⌋₊

def freqSet (B : BoxParams) (N : ℝ) : Finset (ℤ × ℤ × ℤ) :=
  Finset.Icc (-(B.Ms N : ℤ)) (B.Ms N) ×ˢ
    (Finset.Icc (-(B.Mq N : ℤ)) (B.Mq N) ×ˢ Finset.Icc (-(B.Mη N : ℤ)) (B.Mη N))

private theorem abs_int_le_of_mem_Icc_floor {k : ℤ} {x : ℝ} (hx : 0 ≤ x)
    (hk : k ∈ Finset.Icc (-(⌊x⌋₊ : ℤ)) (⌊x⌋₊ : ℤ)) : |(k : ℝ)| ≤ x := by
  rw [Finset.mem_Icc] at hk
  have h1 : -((⌊x⌋₊ : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
  have h2 : (k : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by exact_mod_cast hk.2
  exact (abs_le.2 ⟨h1, h2⟩).trans (Nat.floor_le hx)

private theorem lt_abs_int_of_notMem_Icc_floor {k : ℤ} (x : ℝ)
    (hk : k ∉ Finset.Icc (-(⌊x⌋₊ : ℤ)) (⌊x⌋₊ : ℤ)) : x < |(k : ℝ)| := by
  rw [Finset.mem_Icc] at hk
  have hlt : x < ((⌊x⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one x
  have hge : ((⌊x⌋₊ : ℕ) : ℝ) + 1 ≤ |(k : ℝ)| := by
    have hor : ((⌊x⌋₊ : ℤ) + 1 ≤ k) ∨ (k ≤ -((⌊x⌋₊ : ℤ) + 1)) := by omega
    rcases hor with hpos | hneg
    · have hcast : ((⌊x⌋₊ : ℕ) : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hpos
      exact hcast.trans (le_abs_self _)
    · have hcast : (k : ℝ) ≤ -(((⌊x⌋₊ : ℕ) : ℝ) + 1) := by exact_mod_cast hneg
      have hneg' : ((⌊x⌋₊ : ℕ) : ℝ) + 1 ≤ -(k : ℝ) := by linarith
      exact hneg'.trans (neg_le_abs _)
  exact hlt.trans_le hge

theorem lowFreq_wavenumber_le (B : BoxParams) {N : ℝ} (hN : 0 ≤ N)
    {n : ℤ × ℤ × ℤ} (hn : n ∈ B.freqSet N) :
    |B.ws n| ≤ 2 * Real.pi * N ∧
    |B.wq n| ≤ 2 * Real.pi * N ∧
    |B.wη n| ≤ 2 * Real.pi * N := by
  unfold freqSet at hn
  rw [Finset.mem_product, Finset.mem_product] at hn
  rcases hn with ⟨hns, hnq, hnη⟩
  have hpi : 0 < 2 * Real.pi := by positivity
  have hs := abs_int_le_of_mem_Icc_floor (mul_nonneg hN B.hTs_pos.le) hns
  have hq := abs_int_le_of_mem_Icc_floor (mul_nonneg hN B.hc.le) hnq
  have hη := abs_int_le_of_mem_Icc_floor (mul_nonneg hN B.hTη_pos.le) hnη
  refine ⟨?_, ?_, ?_⟩
  · unfold ws
    rw [abs_div, abs_mul, abs_of_pos hpi, abs_of_pos B.hTs_pos, div_le_iff₀ B.hTs_pos]
    nlinarith
  · unfold wq
    rw [abs_div, abs_mul, abs_of_pos hpi, abs_of_pos B.hc, div_le_iff₀ B.hc]
    nlinarith
  · unfold wη
    rw [abs_div, abs_mul, abs_of_pos hpi, abs_of_pos B.hTη_pos, div_le_iff₀ B.hTη_pos]
    nlinarith

theorem highFreq_wavenumber_lt (B : BoxParams) (N : ℝ)
    {n : ℤ × ℤ × ℤ} (hn : n ∉ B.freqSet N) :
    2 * Real.pi * N < |B.ws n| ∨
    2 * Real.pi * N < |B.wq n| ∨
    2 * Real.pi * N < |B.wη n| := by
  unfold freqSet at hn
  rw [Finset.mem_product, Finset.mem_product] at hn
  have hpi : 0 < 2 * Real.pi := by positivity
  by_cases h1 : n.1 ∈ Finset.Icc (-(B.Ms N : ℤ)) (B.Ms N)
  · by_cases h2 : n.2.1 ∈ Finset.Icc (-(B.Mq N : ℤ)) (B.Mq N)
    · have h3 : n.2.2 ∉ Finset.Icc (-(B.Mη N : ℤ)) (B.Mη N) := fun h3 => hn ⟨h1, h2, h3⟩
      right; right
      have hlt := lt_abs_int_of_notMem_Icc_floor (N * B.Tη) h3
      unfold wη
      rw [abs_div, abs_mul, abs_of_pos hpi, abs_of_pos B.hTη_pos, lt_div_iff₀ B.hTη_pos]
      nlinarith
    · right; left
      have hlt := lt_abs_int_of_notMem_Icc_floor (N * B.c) h2
      unfold wq
      rw [abs_div, abs_mul, abs_of_pos hpi, abs_of_pos B.hc, lt_div_iff₀ B.hc]
      nlinarith
  · left
    have hlt := lt_abs_int_of_notMem_Icc_floor (N * B.Ts) h1
    unfold ws
    rw [abs_div, abs_mul, abs_of_pos hpi, abs_of_pos B.hTs_pos, lt_div_iff₀ B.hTs_pos]
    nlinarith

/-! ### 2. Mode derivatives and `MeridC` Fourier projection -/

theorem hasFDerivAt_mode3D (B : BoxParams) (n : ℤ × ℤ × ℤ) (p : Profile) :
    HasFDerivAt (B.mode3D n)
      ((I * B.mode3D n p) • (Complex.ofRealCLM.comp (B.phaseCLM n))) p := by
  let L : Profile →L[ℝ] ℂ := I • (Complex.ofRealCLM.comp (B.phaseCLM n))
  have hexp : HasFDerivAt (fun q : Profile => Complex.exp (L q))
      (Complex.exp (L p) • L) p := L.hasFDerivAt.cexp
  have hfun : (fun q : Profile => Complex.exp (L q)) = B.mode3D n := by
    funext q
    simp [L, mode3D, smul_apply, smul_eq_mul]
  have hder : Complex.exp (L p) • L =
      (I * B.mode3D n p) • (Complex.ofRealCLM.comp (B.phaseCLM n)) := by
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [L, smul_apply, ContinuousLinearMap.comp_apply,
      Complex.ofRealCLM_apply, smul_eq_mul, mode3D]
    ring
  rw [hfun, hder] at hexp
  exact hexp

theorem pdS_mode3D (B : BoxParams) (n : ℤ × ℤ × ℤ) (p : Profile) :
    pdS (B.mode3D n) p = I * (B.ws n : ℂ) * B.mode3D n p := by
  unfold pdS
  rw [(B.hasFDerivAt_mode3D n p).fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, phaseCLM_apply, smul_eq_mul, ws]
  push_cast
  ring

theorem pdQ_mode3D (B : BoxParams) (n : ℤ × ℤ × ℤ) (p : Profile) :
    pdQ (B.mode3D n) p = I * (B.wq n : ℂ) * B.mode3D n p := by
  unfold pdQ
  rw [(B.hasFDerivAt_mode3D n p).fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, phaseCLM_apply, smul_eq_mul, wq]
  push_cast
  ring

theorem pdEta_mode3D (B : BoxParams) (n : ℤ × ℤ × ℤ) (p : Profile) :
    pdEta (B.mode3D n) p = I * (B.wη n : ℂ) * B.mode3D n p := by
  unfold pdEta
  rw [(B.hasFDerivAt_mode3D n p).fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, phaseCLM_apply, smul_eq_mul, wη]
  push_cast
  ring

/-- Componentwise Fourier truncation of `u : Profile → MeridC` to `B.freqSet N`. -/
def projMerid (B : BoxParams) (N : ℝ) (u : Profile → MeridC) (p : Profile) : MeridC :=
  !₂[B.trigSum (B.freqSet N) (B.coeff3D (fun q => u q 0)) p,
     B.trigSum (B.freqSet N) (B.coeff3D (fun q => u q 1)) p]

theorem memLp_coord_boxMeas (B : BoxParams) {u : Profile → MeridC}
    (hu : MemLp u 2 (cellMeasure B.c)) (j : Fin 2) :
    MemLp (fun p => u p j) 2 B.boxMeas := by
  have hu_box : MemLp u 2 B.boxMeas := by
    rw [← B.cellMeasure_restrict_boxSet]
    exact hu.restrict B.boxSet
  exact ((EuclideanSpace.proj j : MeridC →L[ℂ] ℂ).restrictScalars ℝ).comp_memLp' hu_box

theorem integral_merid_sub_projMerid_sq (B : BoxParams) (N : ℝ) {u : Profile → MeridC}
    (hu : MemLp u 2 (cellMeasure B.c)) :
    ∫ p, ‖u p - B.projMerid N u p‖ ^ 2 ∂B.boxMeas =
      (∫ p, ‖u p 0 - B.trigSum (B.freqSet N) (B.coeff3D (fun q => u q 0)) p‖ ^ 2 ∂B.boxMeas) +
      (∫ p, ‖u p 1 - B.trigSum (B.freqSet N) (B.coeff3D (fun q => u q 1)) p‖ ^ 2 ∂B.boxMeas) := by
  have hm0 := (B.memLp_coord_boxMeas hu 0).sub
    (B.memLp_trigSum (B.freqSet N) (B.coeff3D (fun q => u q 0)))
  have hm1 := (B.memLp_coord_boxMeas hu 1).sub
    (B.memLp_trigSum (B.freqSet N) (B.coeff3D (fun q => u q 1)))
  have hi0 : Integrable (fun p => ‖u p 0 - B.trigSum (B.freqSet N) (B.coeff3D (fun q => u q 0)) p‖ ^ 2)
      B.boxMeas := (memLp_two_iff_integrable_sq_norm hm0.1).1 hm0
  have hi1 : Integrable (fun p => ‖u p 1 - B.trigSum (B.freqSet N) (B.coeff3D (fun q => u q 1)) p‖ ^ 2)
      B.boxMeas := (memLp_two_iff_integrable_sq_norm hm1.1).1 hm1
  have hpt : ∀ p : Profile,
      ‖u p - B.projMerid N u p‖ ^ 2 =
        ‖u p 0 - B.trigSum (B.freqSet N) (B.coeff3D (fun q => u q 0)) p‖ ^ 2 +
        ‖u p 1 - B.trigSum (B.freqSet N) (B.coeff3D (fun q => u q 1)) p‖ ^ 2 := by
    intro p
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simp [projMerid]
  simp_rw [hpt]
  exact integral_add hi0 hi1

/-! ### 3. Smooth observation-box cutoff and `H¹` high-frequency bound -/

/-- Smooth 1D cutoff in `s`: identically `1` on `(7σ/8, H1 + 1/2)` and supported in `[3σ/4, H1 + 1]`. -/
private def thetaS (B : BoxParams) (s : ℝ) : ℝ :=
  Real.smoothTransition ((8 / B.σ) * (s - 3 * B.σ / 4)) *
    Real.smoothTransition (2 * (B.H1 + 1 - s))

/-- Smooth 1D cutoff in `η`: identically `1` on `(-(L1 + 1/2), L1 + 1/2)` and supported in `[-(L1 + 1), L1 + 1]`. -/
private def thetaEta (B : BoxParams) (η : ℝ) : ℝ :=
  Real.smoothTransition (2 * (η + B.L1 + 1)) *
    Real.smoothTransition (2 * (B.L1 + 1 - η))

private def obsCutoff (B : BoxParams) (p : Profile) : ℝ :=
  B.thetaS p.1 * B.thetaEta p.2.2

private theorem contDiff_obsCutoff (B : BoxParams) : ContDiff ℝ ∞ B.obsCutoff := by
  unfold obsCutoff thetaS thetaEta
  have hs1 : ContDiff ℝ ∞ (fun p : Profile => (8 / B.σ) * (p.1 - 3 * B.σ / 4)) :=
    (contDiff_const (c := 8 / B.σ)).mul (contDiff_fst.sub (contDiff_const (c := 3 * B.σ / 4)))
  have hs2 : ContDiff ℝ ∞ (fun p : Profile => 2 * (B.H1 + 1 - p.1)) :=
    (contDiff_const (c := (2 : ℝ))).mul ((contDiff_const (c := B.H1 + 1)).sub contDiff_fst)
  have hη1 : ContDiff ℝ ∞ (fun p : Profile => 2 * (p.2.2 + B.L1 + 1)) :=
    (contDiff_const (c := (2 : ℝ))).mul
      (((contDiff_snd.comp contDiff_snd).add (contDiff_const (c := B.L1))).add
        (contDiff_const (c := (1 : ℝ))))
  have hη2 : ContDiff ℝ ∞ (fun p : Profile => 2 * (B.L1 + 1 - p.2.2)) :=
    (contDiff_const (c := (2 : ℝ))).mul
      ((contDiff_const (c := B.L1 + 1)).sub (contDiff_snd.comp contDiff_snd))
  exact ((Real.smoothTransition.contDiff.comp hs1).mul (Real.smoothTransition.contDiff.comp hs2)).mul
    ((Real.smoothTransition.contDiff.comp hη1).mul (Real.smoothTransition.contDiff.comp hη2))

private def obsOpen (B : BoxParams) : Set Profile :=
  {p : Profile | 7 * B.σ / 8 < p.1 ∧ p.1 < B.H1 + 1 / 2 ∧
    -(B.L1 + 1 / 2) < p.2.2 ∧ p.2.2 < B.L1 + 1 / 2}

private theorem isOpen_obsOpen (B : BoxParams) : IsOpen B.obsOpen := by
  unfold obsOpen
  refine (isOpen_lt continuous_const continuous_fst).inter ?_
  refine (isOpen_lt continuous_fst continuous_const).inter ?_
  exact (isOpen_lt continuous_const (continuous_snd.comp continuous_snd)).inter
    (isOpen_lt (continuous_snd.comp continuous_snd) continuous_const)

private theorem mem_obsOpen_of_box (B : BoxParams) {p : Profile}
    (hs1 : B.σ ≤ p.1) (hs2 : p.1 ≤ B.H1) (hη : |p.2.2| ≤ B.L1) :
    p ∈ B.obsOpen := by
  rw [abs_le] at hη
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith [B.hσ]
  · linarith
  · linarith
  · linarith

private theorem obsCutoff_eq_one_of_mem_obsOpen (B : BoxParams) {p : Profile}
    (hp : p ∈ B.obsOpen) : B.obsCutoff p = 1 := by
  rcases hp with ⟨hs1, hs2, hη1, hη2⟩
  unfold obsCutoff thetaS thetaEta
  have hσ_pos := B.hσ
  have h1 : 1 ≤ (8 / B.σ) * (p.1 - 3 * B.σ / 4) := by
    rw [div_mul_eq_mul_div, one_le_div hσ_pos]
    linarith
  have h2 : 1 ≤ 2 * (B.H1 + 1 - p.1) := by linarith
  have h3 : 1 ≤ 2 * (p.2.2 + B.L1 + 1) := by linarith
  have h4 : 1 ≤ 2 * (B.L1 + 1 - p.2.2) := by linarith
  rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2,
    Real.smoothTransition.one_of_one_le h3, Real.smoothTransition.one_of_one_le h4]
  ring

private theorem obsCutoff_support (B : BoxParams) {p : Profile}
    (hp : B.obsCutoff p ≠ 0) :
    p.1 ∈ Icc (3 * B.σ / 4) (B.H1 + 1) ∧ |p.2.2| ≤ B.L1 + 1 := by
  unfold obsCutoff thetaS thetaEta at hp
  have hσ_pos := B.hσ
  have hs1 : 3 * B.σ / 4 ≤ p.1 := by
    by_contra hlt
    push Not at hlt
    have hnp : (8 / B.σ) * (p.1 - 3 * B.σ / 4) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    rw [Real.smoothTransition.zero_of_nonpos hnp, zero_mul, zero_mul] at hp
    exact hp rfl
  have hs2 : p.1 ≤ B.H1 + 1 := by
    by_contra hlt
    push Not at hlt
    have hnp : 2 * (B.H1 + 1 - p.1) ≤ 0 := by linarith
    rw [Real.smoothTransition.zero_of_nonpos hnp, mul_zero, zero_mul] at hp
    exact hp rfl
  have hη1 : -(B.L1 + 1) ≤ p.2.2 := by
    by_contra hlt
    push Not at hlt
    have hnp : 2 * (p.2.2 + B.L1 + 1) ≤ 0 := by linarith
    rw [Real.smoothTransition.zero_of_nonpos hnp, zero_mul, mul_zero] at hp
    exact hp rfl
  have hη2 : p.2.2 ≤ B.L1 + 1 := by
    by_contra hlt
    push Not at hlt
    have hnp : 2 * (B.L1 + 1 - p.2.2) ≤ 0 := by linarith
    rw [Real.smoothTransition.zero_of_nonpos hnp, mul_zero, mul_zero] at hp
    exact hp rfl
  exact ⟨⟨hs1, hs2⟩, abs_le.2 ⟨hη1, hη2⟩⟩

private def singleCLM (j : Fin 2) : ℂ →L[ℝ] MeridC :=
  (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (EuclideanSpace.single j (1 : ℂ))).restrictScalars ℝ

private theorem singleCLM_apply (j : Fin 2) (z : ℂ) :
    singleCLM j z = EuclideanSpace.single j z := by
  ext k
  simp [singleCLM, PiLp.single_apply]

private def testMode (B : BoxParams) (n : ℤ × ℤ × ℤ) (j : Fin 2) (p : Profile) : MeridC :=
  singleCLM j ((B.obsCutoff p : ℂ) * B.mode3D n p)

private def pureMode (B : BoxParams) (n : ℤ × ℤ × ℤ) (j : Fin 2) (p : Profile) : MeridC :=
  singleCLM j (B.mode3D n p)

private theorem isMeridTest_testMode (B : BoxParams) (n : ℤ × ℤ × ℤ) (j : Fin 2) :
    IsMeridTest B.c (B.testMode n j) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold testMode
    exact (singleCLM j).contDiff.comp
      ((Complex.ofRealCLM.contDiff.comp B.contDiff_obsCutoff).mul (B.contDiff_mode3D n))
  · intro p
    unfold testMode obsCutoff
    simp only [B.qPeriodic_mode3D n p]
  · refine ⟨3 * B.σ / 4, B.H1 + 1, B.L1 + 1, by linarith [B.hσ], ?_⟩
    intro p hp
    have hcut : B.obsCutoff p ≠ 0 := by
      intro h0
      apply hp
      simp [testMode, h0]
    exact B.obsCutoff_support hcut

private theorem fderiv_testMode_eq_pureMode_of_mem_obsOpen (B : BoxParams)
    (n : ℤ × ℤ × ℤ) (j : Fin 2) {p : Profile} (hp : p ∈ B.obsOpen) :
    fderiv ℝ (B.testMode n j) p = fderiv ℝ (B.pureMode n j) p := by
  have hev : B.testMode n j =ᶠ[𝓝 p] B.pureMode n j := by
    filter_upwards [B.isOpen_obsOpen.mem_nhds hp] with q hq
    simp [testMode, pureMode, B.obsCutoff_eq_one_of_mem_obsOpen hq]
  exact hev.fderiv_eq

private theorem pd_pureMode (B : BoxParams) (n : ℤ × ℤ × ℤ) (j : Fin 2) (p : Profile) :
    pdS (B.pureMode n j) p = EuclideanSpace.single j (I * (B.ws n : ℂ) * B.mode3D n p) ∧
    pdQ (B.pureMode n j) p = EuclideanSpace.single j (I * (B.wq n : ℂ) * B.mode3D n p) ∧
    pdEta (B.pureMode n j) p = EuclideanSpace.single j (I * (B.wη n : ℂ) * B.mode3D n p) := by
  have hf : fderiv ℝ (B.pureMode n j) p = (singleCLM j).comp (fderiv ℝ (B.mode3D n) p) := by
    rw [(B.hasFDerivAt_mode3D n p).fderiv]
    change fderiv ℝ (⇑(singleCLM j) ∘ B.mode3D n) p = _
    exact ((singleCLM j).hasFDerivAt.comp p (B.hasFDerivAt_mode3D n p)).fderiv
  refine ⟨?_, ?_, ?_⟩
  · unfold pdS
    rw [hf, ContinuousLinearMap.comp_apply, singleCLM_apply, ← pdS, B.pdS_mode3D]
  · unfold pdQ
    rw [hf, ContinuousLinearMap.comp_apply, singleCLM_apply, ← pdQ, B.pdQ_mode3D]
  · unfold pdEta
    rw [hf, ContinuousLinearMap.comp_apply, singleCLM_apply, ← pdEta, B.pdEta_mode3D]

/-- Weak derivative Fourier multiplier identities for `HasWeakCellH1`. -/
theorem coeff3D_weakDeriv_eq (B : BoxParams) {U : HSpace B.c MeridC}
    {u ds dq deta : Profile → MeridC}
    (hw : HasWeakCellH1 B.c B.σ B.H1 B.L1 U u ds dq deta)
    (n : ℤ × ℤ × ℤ) (j : Fin 2) :
    B.coeff3D (fun p => ds p j) n = (I * (B.ws n : ℂ)) * B.coeff3D (fun p => u p j) n ∧
    B.coeff3D (fun p => dq p j) n = (I * (B.wq n : ℂ)) * B.coeff3D (fun p => u p j) n ∧
    B.coeff3D (fun p => deta p j) n = (I * (B.wη n : ℂ)) * B.coeff3D (fun p => u p j) n := by
  have h_lhs : ∀ (v : Profile → MeridC),
      (∀ p : Profile, v p ≠ 0 → B.σ ≤ p.1 ∧ p.1 ≤ B.H1 ∧ |p.2.2| ≤ B.L1) →
      starRingEnd ℂ (∫ p, inner ℂ (v p) (B.testMode n j p) ∂(cellMeasure B.c)) =
        ∫ p, starRingEnd ℂ (B.mode3D n p) * v p j ∂B.boxMeas := by
    intro v hv_supp
    rw [← integral_conj]
    have hpt : ∀ p : Profile,
        starRingEnd ℂ (inner ℂ (v p) (B.testMode n j p)) =
          starRingEnd ℂ (B.mode3D n p) * v p j := by
      intro p
      unfold testMode
      rw [singleCLM_apply, EuclideanSpace.inner_single_right]
      by_cases hv0 : v p = 0
      · simp [hv0]
      · obtain ⟨hs1, hs2, hη⟩ := hv_supp p hv0
        have hone := B.obsCutoff_eq_one_of_mem_obsOpen (B.mem_obsOpen_of_box hs1 hs2 hη)
        simp [hone]
    simp_rw [hpt]
    refine B.integral_cellMeasure_eq_boxMeas fun p hp => hv_supp p ?_
    intro hv0
    simp [hv0] at hp
  have h_rhs : ∀ (pd : (Profile → MeridC) → Profile → MeridC) (w : ℝ),
      (∀ p : Profile, p ∈ B.obsOpen →
        pd (B.testMode n j) p = EuclideanSpace.single j (I * (w : ℂ) * B.mode3D n p)) →
      starRingEnd ℂ (-∫ p, inner ℂ (u p) (pd (B.testMode n j) p) ∂(cellMeasure B.c)) =
        (I * (w : ℂ)) * ∫ p, starRingEnd ℂ (B.mode3D n p) * u p j ∂B.boxMeas := by
    intro pd w hpd
    rw [map_neg, ← integral_conj, ← integral_neg]
    have hpt : ∀ p : Profile,
        -starRingEnd ℂ (inner ℂ (u p) (pd (B.testMode n j) p)) =
          (I * (w : ℂ)) * (starRingEnd ℂ (B.mode3D n p) * u p j) := by
      intro p
      by_cases hu0 : u p = 0
      · simp [hu0]
      · obtain ⟨hs1, hs2, hη⟩ := hw.support_u p hu0
        rw [hpd p (B.mem_obsOpen_of_box hs1 hs2 hη), EuclideanSpace.inner_single_right]
        simp only [map_mul, conj_I, conj_ofReal, RingHomCompTriple.comp_apply, RingHom.id_apply]
        ring
    simp_rw [hpt]
    rw [integral_const_mul]
    congr 1
    refine B.integral_cellMeasure_eq_boxMeas fun p hp => hw.support_u p ?_
    intro hu0
    simp [hu0] at hp
  have htest := B.isMeridTest_testMode n j
  refine ⟨?_, ?_, ?_⟩
  · have hibp := congr_arg (starRingEnd ℂ) (hw.ibp_s (B.testMode n j) htest)
    rw [h_lhs ds hw.support_ds, h_rhs pdS (B.ws n) (fun p hp => by
      unfold pdS
      rw [B.fderiv_testMode_eq_pureMode_of_mem_obsOpen n j hp]
      exact (B.pd_pureMode n j p).1)] at hibp
    unfold coeff3D
    rw [hibp, real_smul, real_smul]
    ring
  · have hibp := congr_arg (starRingEnd ℂ) (hw.ibp_q (B.testMode n j) htest)
    rw [h_lhs dq hw.support_dq, h_rhs pdQ (B.wq n) (fun p hp => by
      unfold pdQ
      rw [B.fderiv_testMode_eq_pureMode_of_mem_obsOpen n j hp]
      exact (B.pd_pureMode n j p).2.1)] at hibp
    unfold coeff3D
    rw [hibp, real_smul, real_smul]
    ring
  · have hibp := congr_arg (starRingEnd ℂ) (hw.ibp_eta (B.testMode n j) htest)
    rw [h_lhs deta hw.support_deta, h_rhs pdEta (B.wη n) (fun p hp => by
      unfold pdEta
      rw [B.fderiv_testMode_eq_pureMode_of_mem_obsOpen n j hp]
      exact (B.pd_pureMode n j p).2.2)] at hibp
    unfold coeff3D
    rw [hibp, real_smul, real_smul]
    ring

private theorem boxL2_coord_sum_le_cellL2Norm_sq (B : BoxParams) {v : Profile → MeridC}
    (hv_mem : MemLp v 2 (cellMeasure B.c))
    (hv_supp : ∀ p : Profile, v p ≠ 0 → B.σ ≤ p.1 ∧ p.1 ≤ B.H1 ∧ |p.2.2| ≤ B.L1) :
    (∫ p, ‖v p 0‖ ^ 2 ∂B.boxMeas) + (∫ p, ‖v p 1‖ ^ 2 ∂B.boxMeas) =
      cellL2Norm B.c v ^ 2 := by
  have hm0 := B.memLp_coord_boxMeas hv_mem 0
  have hm1 := B.memLp_coord_boxMeas hv_mem 1
  have hi0 : Integrable (fun p => ‖v p 0‖ ^ 2) B.boxMeas :=
    (memLp_two_iff_integrable_sq_norm hm0.1).1 hm0
  have hi1 : Integrable (fun p => ‖v p 1‖ ^ 2) B.boxMeas :=
    (memLp_two_iff_integrable_sq_norm hm1.1).1 hm1
  rw [← integral_add hi0 hi1]
  have hpt : (fun p : Profile => ‖v p 0‖ ^ 2 + ‖v p 1‖ ^ 2) = fun p => ‖v p‖ ^ 2 := by
    ext p
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  rw [hpt, ← B.integral_cellMeasure_eq_boxMeas (fun p hp => hv_supp p (fun hv0 => by simp [hv0] at hp))]
  unfold cellL2Norm
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]

/-- **Main `H¹` high-frequency decay bound** on `B.boxMeas`. -/
theorem h1_highFreq_bound (B : BoxParams) {U : HSpace B.c MeridC}
    {u ds dq deta : Profile → MeridC}
    (hw : HasWeakCellH1 B.c B.σ B.H1 B.L1 U u ds dq deta)
    {N : ℝ} (hN : 1 ≤ N) :
    ∫ p, ‖u p - B.projMerid N u p‖ ^ 2 ∂B.boxMeas ≤
      N⁻¹ ^ 2 * cellH1Norm B.c u ds dq deta ^ 2 := by
  have hN_pos : 0 < N := by linarith
  have h_coord : ∀ j : Fin 2,
      ∫ p, ‖u p j - B.trigSum (B.freqSet N) (B.coeff3D (fun q => u q j)) p‖ ^ 2 ∂B.boxMeas ≤
        N⁻¹ ^ 2 *
          ((∫ p, ‖ds p j‖ ^ 2 ∂B.boxMeas) +
           (∫ p, ‖dq p j‖ ^ 2 ∂B.boxMeas) +
           (∫ p, ‖deta p j‖ ^ 2 ∂B.boxMeas)) := by
    intro j
    have hu_j := B.memLp_coord_boxMeas hw.memLp_u j
    have hds_j := B.memLp_coord_boxMeas hw.memLp_ds j
    have hdq_j := B.memLp_coord_boxMeas hw.memLp_dq j
    have hdeta_j := B.memLp_coord_boxMeas hw.memLp_deta j
    have htail := B.ofReal_integral_sub_trigSum_sq hu_j (B.freqSet N)
    have hterm : ∀ n : ℤ × ℤ × ℤ,
        (if n ∈ B.freqSet N then (0 : ℝ≥0∞)
          else ENNReal.ofReal (‖B.coeff3D (fun q => u q j) n‖ ^ 2)) ≤
        ENNReal.ofReal (N⁻¹ ^ 2) *
          (ENNReal.ofReal (‖B.coeff3D (fun q => ds q j) n‖ ^ 2) +
           ENNReal.ofReal (‖B.coeff3D (fun q => dq q j) n‖ ^ 2) +
           ENNReal.ofReal (‖B.coeff3D (fun q => deta q j) n‖ ^ 2)) := by
      intro n
      by_cases hn : n ∈ B.freqSet N
      · simp [hn]
      · simp only [hn, ↓reduceIte]
        obtain ⟨hcs, hcq, hcη⟩ := B.coeff3D_weakDeriv_eq hw n j
        have hns : ‖B.coeff3D (fun q => ds q j) n‖ ^ 2 =
            B.ws n ^ 2 * ‖B.coeff3D (fun q => u q j) n‖ ^ 2 := by
          rw [hcs, norm_mul, norm_mul, norm_I, one_mul, Complex.norm_real,
            Real.norm_eq_abs, mul_pow, sq_abs]
        have hnq : ‖B.coeff3D (fun q => dq q j) n‖ ^ 2 =
            B.wq n ^ 2 * ‖B.coeff3D (fun q => u q j) n‖ ^ 2 := by
          rw [hcq, norm_mul, norm_mul, norm_I, one_mul, Complex.norm_real,
            Real.norm_eq_abs, mul_pow, sq_abs]
        have hnη : ‖B.coeff3D (fun q => deta q j) n‖ ^ 2 =
            B.wη n ^ 2 * ‖B.coeff3D (fun q => u q j) n‖ ^ 2 := by
          rw [hcη, norm_mul, norm_mul, norm_I, one_mul, Complex.norm_real,
            Real.norm_eq_abs, mul_pow, sq_abs]
        have hsum_w : N ^ 2 ≤ B.ws n ^ 2 + B.wq n ^ 2 + B.wη n ^ 2 := by
          have hpi2 : 1 ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
          have hN2 : N ≤ 2 * Real.pi * N := le_mul_of_one_le_left hN_pos.le hpi2
          rcases B.highFreq_wavenumber_lt N hn with hs | hq | hη
          · have : N ^ 2 ≤ |B.ws n| ^ 2 := pow_le_pow_left₀ hN_pos.le (hN2.trans hs.le) 2
            rw [sq_abs] at this
            nlinarith [sq_nonneg (B.wq n), sq_nonneg (B.wη n)]
          · have : N ^ 2 ≤ |B.wq n| ^ 2 := pow_le_pow_left₀ hN_pos.le (hN2.trans hq.le) 2
            rw [sq_abs] at this
            nlinarith [sq_nonneg (B.ws n), sq_nonneg (B.wη n)]
          · have : N ^ 2 ≤ |B.wη n| ^ 2 := pow_le_pow_left₀ hN_pos.le (hN2.trans hη.le) 2
            rw [sq_abs] at this
            nlinarith [sq_nonneg (B.ws n), sq_nonneg (B.wq n)]
        rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
          ← ENNReal.ofReal_add (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _),
          ← ENNReal.ofReal_mul (sq_nonneg _)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hns, hnq, hnη]
        have h1 : 1 ≤ N⁻¹ ^ 2 * (B.ws n ^ 2 + B.wq n ^ 2 + B.wη n ^ 2) := by
          calc (1 : ℝ) = N⁻¹ ^ 2 * N ^ 2 := by field_simp
            _ ≤ N⁻¹ ^ 2 * (B.ws n ^ 2 + B.wq n ^ 2 + B.wη n ^ 2) :=
                mul_le_mul_of_nonneg_left hsum_w (sq_nonneg _)
        calc ‖B.coeff3D (fun q => u q j) n‖ ^ 2
            = 1 * ‖B.coeff3D (fun q => u q j) n‖ ^ 2 := (one_mul _).symm
          _ ≤ (N⁻¹ ^ 2 * (B.ws n ^ 2 + B.wq n ^ 2 + B.wη n ^ 2)) *
                ‖B.coeff3D (fun q => u q j) n‖ ^ 2 :=
              mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
          _ = N⁻¹ ^ 2 * (B.ws n ^ 2 * ‖B.coeff3D (fun q => u q j) n‖ ^ 2 +
                B.wq n ^ 2 * ‖B.coeff3D (fun q => u q j) n‖ ^ 2 +
                B.wη n ^ 2 * ‖B.coeff3D (fun q => u q j) n‖ ^ 2) := by ring
    have hle_enn :
        ENNReal.ofReal (∫ p, ‖u p j - B.trigSum (B.freqSet N) (B.coeff3D (fun q => u q j)) p‖ ^ 2 ∂B.boxMeas) ≤
        ENNReal.ofReal
          (N⁻¹ ^ 2 *
            ((∫ p, ‖ds p j‖ ^ 2 ∂B.boxMeas) +
             (∫ p, ‖dq p j‖ ^ 2 ∂B.boxMeas) +
             (∫ p, ‖deta p j‖ ^ 2 ∂B.boxMeas))) := by
      rw [htail]
      calc ENNReal.ofReal B.volBox *
              ∑' n : ℤ × ℤ × ℤ, (if n ∈ B.freqSet N then 0 else ENNReal.ofReal (‖B.coeff3D (fun q => u q j) n‖ ^ 2))
          ≤ ENNReal.ofReal B.volBox *
              ∑' n : ℤ × ℤ × ℤ, ENNReal.ofReal (N⁻¹ ^ 2) *
                (ENNReal.ofReal (‖B.coeff3D (fun q => ds q j) n‖ ^ 2) +
                 ENNReal.ofReal (‖B.coeff3D (fun q => dq q j) n‖ ^ 2) +
                 ENNReal.ofReal (‖B.coeff3D (fun q => deta q j) n‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left (ENNReal.tsum_le_tsum hterm) zero_le
        _ = ENNReal.ofReal B.volBox *
              (ENNReal.ofReal (N⁻¹ ^ 2) *
                ((∑' n, ENNReal.ofReal (‖B.coeff3D (fun q => ds q j) n‖ ^ 2)) +
                 (∑' n, ENNReal.ofReal (‖B.coeff3D (fun q => dq q j) n‖ ^ 2)) +
                 (∑' n, ENNReal.ofReal (‖B.coeff3D (fun q => deta q j) n‖ ^ 2)))) := by
            rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, ENNReal.tsum_add]
        _ = ENNReal.ofReal
              (N⁻¹ ^ 2 *
                ((∫ p, ‖ds p j‖ ^ 2 ∂B.boxMeas) +
                 (∫ p, ‖dq p j‖ ^ 2 ∂B.boxMeas) +
                 (∫ p, ‖deta p j‖ ^ 2 ∂B.boxMeas))) := by
            rw [B.tsum_coeff3D_sq hds_j, B.tsum_coeff3D_sq hdq_j, B.tsum_coeff3D_sq hdeta_j]
            have his : 0 ≤ B.volBox⁻¹ * ∫ p, ‖ds p j‖ ^ 2 ∂B.boxMeas :=
              mul_nonneg (inv_nonneg.2 B.hvolBox_pos.le) (integral_nonneg fun _ => sq_nonneg _)
            have hiq : 0 ≤ B.volBox⁻¹ * ∫ p, ‖dq p j‖ ^ 2 ∂B.boxMeas :=
              mul_nonneg (inv_nonneg.2 B.hvolBox_pos.le) (integral_nonneg fun _ => sq_nonneg _)
            have hiη : 0 ≤ B.volBox⁻¹ * ∫ p, ‖deta p j‖ ^ 2 ∂B.boxMeas :=
              mul_nonneg (inv_nonneg.2 B.hvolBox_pos.le) (integral_nonneg fun _ => sq_nonneg _)
            rw [← ENNReal.ofReal_add his hiq, ← ENNReal.ofReal_add (add_nonneg his hiq) hiη,
              ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul B.hvolBox_pos.le]
            congr 1
            have hv := B.hvolBox_pos.ne'
            field_simp
    have h_rhs_nn : 0 ≤ N⁻¹ ^ 2 *
        ((∫ p, ‖ds p j‖ ^ 2 ∂B.boxMeas) +
         (∫ p, ‖dq p j‖ ^ 2 ∂B.boxMeas) +
         (∫ p, ‖deta p j‖ ^ 2 ∂B.boxMeas)) :=
      mul_nonneg (sq_nonneg _) (add_nonneg
        (add_nonneg (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _))
        (integral_nonneg fun _ => sq_nonneg _))
    exact (ENNReal.ofReal_le_ofReal_iff h_rhs_nn).1 hle_enn
  rw [B.integral_merid_sub_projMerid_sq N hw.memLp_u]
  have h0 := h_coord 0
  have h1 := h_coord 1
  have hsum_eq :
      ((∫ p, ‖ds p 0‖ ^ 2 ∂B.boxMeas) + (∫ p, ‖dq p 0‖ ^ 2 ∂B.boxMeas) + (∫ p, ‖deta p 0‖ ^ 2 ∂B.boxMeas)) +
      ((∫ p, ‖ds p 1‖ ^ 2 ∂B.boxMeas) + (∫ p, ‖dq p 1‖ ^ 2 ∂B.boxMeas) + (∫ p, ‖deta p 1‖ ^ 2 ∂B.boxMeas)) =
      cellL2Norm B.c ds ^ 2 + cellL2Norm B.c dq ^ 2 + cellL2Norm B.c deta ^ 2 := by
    rw [← B.boxL2_coord_sum_le_cellL2Norm_sq hw.memLp_ds hw.support_ds,
      ← B.boxL2_coord_sum_le_cellL2Norm_sq hw.memLp_dq hw.support_dq,
      ← B.boxL2_coord_sum_le_cellL2Norm_sq hw.memLp_deta hw.support_deta]
    ring
  have hnorm_sq : cellL2Norm B.c ds ^ 2 + cellL2Norm B.c dq ^ 2 + cellL2Norm B.c deta ^ 2 ≤
      cellH1Norm B.c u ds dq deta ^ 2 := by
    unfold cellH1Norm
    have a0 := cellL2Norm_nonneg B.c u
    have a1 := cellL2Norm_nonneg B.c ds
    have a2 := cellL2Norm_nonneg B.c dq
    have a3 := cellL2Norm_nonneg B.c deta
    nlinarith
  calc (∫ p, ‖u p 0 - B.trigSum (B.freqSet N) (B.coeff3D (fun q => u q 0)) p‖ ^ 2 ∂B.boxMeas) +
         (∫ p, ‖u p 1 - B.trigSum (B.freqSet N) (B.coeff3D (fun q => u q 1)) p‖ ^ 2 ∂B.boxMeas)
      ≤ N⁻¹ ^ 2 *
          (((∫ p, ‖ds p 0‖ ^ 2 ∂B.boxMeas) + (∫ p, ‖dq p 0‖ ^ 2 ∂B.boxMeas) + (∫ p, ‖deta p 0‖ ^ 2 ∂B.boxMeas)) +
           ((∫ p, ‖ds p 1‖ ^ 2 ∂B.boxMeas) + (∫ p, ‖dq p 1‖ ^ 2 ∂B.boxMeas) + (∫ p, ‖deta p 1‖ ^ 2 ∂B.boxMeas))) := by
        linarith
    _ = N⁻¹ ^ 2 * (cellL2Norm B.c ds ^ 2 + cellL2Norm B.c dq ^ 2 + cellL2Norm B.c deta ^ 2) := by
        rw [hsum_eq]
    _ ≤ N⁻¹ ^ 2 * cellH1Norm B.c u ds dq deta ^ 2 :=
        mul_le_mul_of_nonneg_left hnorm_sq (sq_nonneg _)

/-! ### 4. Translation `MemLp`, shift Fourier multipliers, and `H^{1/4}` high-frequency bound -/

/-- Step-size scale `δ = min (min (1/2) (σ/4)) (c/2)` avoiding box boundary wraparound. -/
def deltaStep (B : BoxParams) : ℝ :=
  min (min (1 / 2 : ℝ) (B.σ / 4)) (B.c / 2)

theorem deltaStep_pos (B : BoxParams) : 0 < B.deltaStep := by
  unfold deltaStep
  refine lt_min (lt_min (by norm_num) ?_) ?_
  · linarith [B.hσ]
  · linarith [B.hc]

theorem deltaStep_le_half (B : BoxParams) : B.deltaStep ≤ 1 / 2 :=
  (min_le_left _ _).trans (min_le_left _ _)

theorem deltaStep_le_sigma_div_four (B : BoxParams) : B.deltaStep ≤ B.σ / 4 :=
  (min_le_left _ _).trans (min_le_right _ _)

theorem deltaStep_le_c_div_two (B : BoxParams) : B.deltaStep ≤ B.c / 2 :=
  min_le_right _ _

private theorem memLp_union_disjoint {E : Type*} [NormedAddCommGroup E]
    {μ : Measure Profile} {A1 A2 : Set Profile}
    (hA1 : MeasurableSet A1) (hA2 : MeasurableSet A2) (hdisj : Disjoint A1 A2)
    {f : Profile → E} (hf1 : MemLp f 2 (μ.restrict A1)) (hf2 : MemLp f 2 (μ.restrict A2)) :
    MemLp f 2 (μ.restrict (A1 ∪ A2)) := by
  rw [← memLp_indicator_iff_restrict (hA1.union hA2)]
  have hi1 : MemLp (A1.indicator f) 2 μ := (memLp_indicator_iff_restrict hA1).2 hf1
  have hi2 : MemLp (A2.indicator f) 2 μ := (memLp_indicator_iff_restrict hA2).2 hf2
  have heq : (A1 ∪ A2).indicator f = fun p => A1.indicator f p + A2.indicator f p := by
    ext p
    by_cases hp1 : p ∈ A1
    · have hp2 : p ∉ A2 := Set.disjoint_left.1 hdisj hp1
      simp [Set.indicator, hp1, hp2]
    · by_cases hp2 : p ∈ A2 <;> simp [Set.indicator, hp1, hp2]
  rw [heq]
  exact hi1.add hi2

private instance isAddRightInvariant_volume_profile :
    (volume : Measure Profile).IsAddRightInvariant where
  map_add_right_eq_self := by
    rintro ⟨a, b, c⟩
    change Measure.map (Prod.map (· + a) (Prod.map (· + b) (· + c)))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure ℝ))) = _
    have hm1 : Measurable (fun x : ℝ => x + a) := (continuous_id.add continuous_const).measurable
    have hm2 : Measurable (fun x : ℝ => x + b) := (continuous_id.add continuous_const).measurable
    have hm3 : Measurable (fun x : ℝ => x + c) := (continuous_id.add continuous_const).measurable
    rw [← Measure.map_prod_map _ _ hm1 (hm2.prodMap hm3),
      ← Measure.map_prod_map _ _ hm2 hm3,
      map_add_right_eq_self (volume : Measure ℝ) a,
      map_add_right_eq_self (volume : Measure ℝ) b,
      map_add_right_eq_self (volume : Measure ℝ) c]
    rfl

private theorem memLp_shift_addRight_subset {E : Type*} [NormedAddCommGroup E]
    (v : Profile) {S T : Set Profile} (hS : MeasurableSet S)
    (hsub : T ⊆ (fun p => p + v) ⁻¹' S)
    {f : Profile → E} (hf : MemLp f 2 (volume.restrict S)) :
    MemLp (fun p => f (p + v)) 2 (volume.restrict T) := by
  have hmp : MeasurePreserving (fun p : Profile => p + v)
      (volume.restrict ((fun p => p + v) ⁻¹' S)) (volume.restrict S) :=
    (measurePreserving_add_right (volume : Measure Profile) v).restrict_preimage hS
  have hcomp : MemLp (f ∘ fun p : Profile => p + v) 2
      (volume.restrict ((fun p => p + v) ⁻¹' S)) :=
    hf.comp_measurePreserving hmp
  exact hcomp.mono_measure (Measure.restrict_mono hsub le_rfl)

theorem memLp_shiftS_cellMeasure (B : BoxParams) {u : Profile → MeridC}
    (hu : MemLp u 2 (cellMeasure B.c)) {h : ℝ} (hh : 0 ≤ h) :
    MemLp (fun p => u (shiftS h p)) 2 (cellMeasure B.c) := by
  have heq : (fun p : Profile => u (shiftS h p)) = fun p => u (p + (h, 0, 0)) := by
    funext p; congr 1; ext <;> simp [shiftS]
  rw [heq]
  refine memLp_shift_addRight_subset (h, 0, 0) (measurableSet_cell B.c) ?_ hu
  rintro ⟨s, q, η⟩ ⟨hs, hq, _⟩
  exact ⟨by dsimp at hs ⊢; rw [mem_Ioi] at hs ⊢; linarith, by simpa using hq, trivial⟩

theorem memLp_shiftEta_cellMeasure (B : BoxParams) {u : Profile → MeridC}
    (hu : MemLp u 2 (cellMeasure B.c)) (h : ℝ) :
    MemLp (fun p => u (shiftEta h p)) 2 (cellMeasure B.c) := by
  have heq : (fun p : Profile => u (shiftEta h p)) = fun p => u (p + (0, 0, h)) := by
    funext p; congr 1; ext <;> simp [shiftEta]
  rw [heq]
  refine memLp_shift_addRight_subset (0, 0, h) (measurableSet_cell B.c) ?_ hu
  rintro ⟨s, q, η⟩ ⟨hs, hq, _⟩
  exact ⟨by simpa using hs, by simpa using hq, trivial⟩

theorem memLp_shiftQ_cellMeasure (B : BoxParams) {u : Profile → MeridC}
    (hu : MemLp u 2 (cellMeasure B.c)) (hper : QPeriodic B.c u)
    {h : ℝ} (hh0 : 0 ≤ h) (hhc : h ≤ B.c) :
    MemLp (fun p => u (shiftQ h p)) 2 (cellMeasure B.c) := by
  set C1 : Set Profile := Ioi 0 ×ˢ (Ioc 0 (B.c - h) ×ˢ univ)
  set C2 : Set Profile := Ioi 0 ×ˢ (Ioc (B.c - h) B.c ×ˢ univ)
  have hC1_meas : MeasurableSet C1 :=
    measurableSet_Ioi.prod (measurableSet_Ioc.prod MeasurableSet.univ)
  have hC2_meas : MeasurableSet C2 :=
    measurableSet_Ioi.prod (measurableSet_Ioc.prod MeasurableSet.univ)
  have hdisj : Disjoint C1 C2 := by
    refine Set.disjoint_left.2 ?_
    rintro ⟨s, q, η⟩ ⟨_, hq1, _⟩ ⟨_, hq2, _⟩
    exact not_lt_of_ge hq1.2 hq2.1
  have hunion : C1 ∪ C2 = cell B.c := by
    ext ⟨s, q, η⟩
    simp only [C1, C2, cell, mem_union, mem_prod, mem_Ioi, mem_Ioc, mem_univ, and_true]
    constructor
    · rintro (⟨hs, hq1, hq2⟩ | ⟨hs, hq1, hq2⟩)
      · exact ⟨hs, hq1, by linarith⟩
      · exact ⟨hs, by linarith, hq2⟩
    · rintro ⟨hs, hq1, hq2⟩
      by_cases hle : q ≤ B.c - h
      · exact Or.inl ⟨hs, hq1, hle⟩
      · exact Or.inr ⟨hs, not_le.1 hle, hq2⟩
  have hm1 : MemLp (fun p => u (shiftQ h p)) 2 (volume.restrict C1) := by
    have heq : (fun p : Profile => u (shiftQ h p)) = fun p => u (p + (0, h, 0)) := by
      funext p; congr 1; ext <;> simp [shiftQ]
    rw [heq]
    refine memLp_shift_addRight_subset (0, h, 0) (measurableSet_cell B.c) ?_ hu
    rintro ⟨s, q, η⟩ ⟨hs, ⟨hq1, hq2⟩, _⟩
    exact ⟨by simpa using hs, ⟨by dsimp at hq1 ⊢; linarith, by dsimp at hq2 ⊢; linarith⟩, trivial⟩
  have hm2 : MemLp (fun p => u (shiftQ h p)) 2 (volume.restrict C2) := by
    have heq : (fun p : Profile => u (shiftQ h p)) = fun p => u (p + (0, h - B.c, 0)) := by
      funext ⟨s, q, η⟩
      have hp := hper (s, q + h - B.c, η)
      have h1' : (s, q + h - B.c + B.c, η) = shiftQ h (s, q, η) :=
        Prod.ext rfl (Prod.ext (by dsimp [shiftQ]; ring) rfl)
      have h2' : ((s, q, η) + (0, h - B.c, 0) : Profile) = (s, q + h - B.c, η) :=
        Prod.ext (add_zero s) (Prod.ext (by dsimp; ring) (add_zero η))
      rw [← h1', hp, h2']
    rw [heq]
    refine memLp_shift_addRight_subset (0, h - B.c, 0) (measurableSet_cell B.c) ?_ hu
    rintro ⟨s, q, η⟩ ⟨hs, ⟨hq1, hq2⟩, _⟩
    exact ⟨by simpa using hs, ⟨by dsimp at hq1 ⊢; linarith, by dsimp at hq2 ⊢; linarith [B.hc]⟩, trivial⟩
  unfold cellMeasure
  rw [← hunion]
  exact memLp_union_disjoint hC1_meas hC2_meas hdisj hm1 hm2

private theorem setIntegral_addRight_eq (v : Profile) {A Bset : Set Profile}
    (hpre : (fun p : Profile => p + v) ⁻¹' Bset = A)
    (g : Profile → ℂ) :
    ∫ p in A, g (p + v) = ∫ y in Bset, g y := by
  rw [← hpre]
  exact (measurePreserving_add_right (volume : Measure Profile) v).setIntegral_preimage_emb
    (MeasurableEquiv.addRight v).measurableEmbedding g Bset

private theorem mode3D_conj_sub_addRight (B : BoxParams) (n : ℤ × ℤ × ℤ) (v y : Profile) :
    starRingEnd ℂ (B.mode3D n (y - v)) =
      Complex.exp (I * (B.phaseCLM n v : ℂ)) * starRingEnd ℂ (B.mode3D n y) := by
  unfold mode3D
  rw [map_sub, Complex.ofReal_sub, mul_sub, Complex.exp_sub, map_div₀,
    ← Complex.exp_conj, ← Complex.exp_conj]
  have hconj_v : starRingEnd ℂ (I * (B.phaseCLM n v : ℂ)) = -(I * (B.phaseCLM n v : ℂ)) := by
    rw [map_mul, conj_I, conj_ofReal, neg_mul]
  rw [hconj_v, Complex.exp_neg, div_inv_eq_mul, mul_comm]

theorem coeff3D_shiftS_sub (B : BoxParams) {f : Profile → ℂ} {h : ℝ}
    (hf : MemLp f 2 B.boxMeas)
    (hf_shift : MemLp (fun p => f (shiftS h p)) 2 B.boxMeas)
    (hsupp : ∀ p : Profile, f p ≠ 0 → B.σ ≤ p.1 ∧ p.1 ≤ B.H1 ∧ |p.2.2| ≤ B.L1)
    (hh0 : 0 ≤ h) (hhσ : h ≤ B.σ / 4) (n : ℤ × ℤ × ℤ) :
    B.coeff3D (fun p => f (shiftS h p) - f p) n =
      (Complex.exp (I * ((B.ws n * h : ℝ) : ℂ)) - 1) * B.coeff3D f n := by
  push_cast
  rw [B.coeff3D_sub (hf_shift.integrable one_le_two) (hf.integrable one_le_two) n]
  suffices hshift_eq :
      B.coeff3D (fun p => f (shiftS h p)) n =
        Complex.exp (I * (B.ws n * h : ℂ)) * B.coeff3D f n by
    rw [hshift_eq]; ring
  set As : Set Profile := Ioc B.as (B.bs - h) ×ˢ (B.Iq ×ˢ B.Iη)
  set Bs : Set Profile := Ioc (B.as + h) B.bs ×ˢ (B.Iq ×ˢ B.Iη)
  have hAs_meas : MeasurableSet As :=
    measurableSet_Ioc.prod (measurableSet_Ioc.prod measurableSet_Ioc)
  have hBs_meas : MeasurableSet Bs :=
    measurableSet_Ioc.prod (measurableSet_Ioc.prod measurableSet_Ioc)
  have hAs_sub : As ⊆ B.boxSet := by
    rintro ⟨s, q, η⟩ ⟨⟨hs1, hs2⟩, hq, hη⟩
    exact ⟨⟨hs1, by linarith⟩, hq, hη⟩
  have hBs_sub : Bs ⊆ B.boxSet := by
    rintro ⟨s, q, η⟩ ⟨⟨hs1, hs2⟩, hq, hη⟩
    exact ⟨⟨by linarith, hs2⟩, hq, hη⟩
  have h1 : ∫ p, starRingEnd ℂ (B.mode3D n p) * f (shiftS h p) ∂B.boxMeas =
      ∫ p in As, starRingEnd ℂ (B.mode3D n p) * f (shiftS h p) := by
    unfold boxMeas
    rw [← integral_indicator B.measurableSet_boxSet, ← integral_indicator hAs_meas]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    by_cases hpAs : p ∈ As
    · simp [Set.indicator, hpAs, hAs_sub hpAs]
    · by_cases hpBox : p ∈ B.boxSet
      · rcases p with ⟨s, q, η⟩
        have ⟨⟨hs1, hs2⟩, hq, hη⟩ := hpBox
        have hgt : B.bs - h < s := by
          by_contra hle
          exact hpAs ⟨⟨hs1, not_lt.1 hle⟩, hq, hη⟩
        have hf0 : f (shiftS h (s, q, η)) = 0 := by
          by_contra hne
          obtain ⟨_, hH1, _⟩ := hsupp _ hne
          unfold shiftS at hH1
          unfold bs at hgt
          linarith
        simp [Set.indicator, hpAs, hpBox, hf0]
      · simp [Set.indicator, hpAs, hpBox]
  have hpre : (fun p : Profile => p + (h, 0, 0)) ⁻¹' Bs = As := by
    ext ⟨s, q, η⟩
    simp only [Bs, As, mem_preimage, mem_prod, mem_Ioc]
    constructor <;> rintro ⟨⟨h1', h2'⟩, hq, hη⟩ <;>
      exact ⟨⟨by dsimp at *; linarith, by dsimp at *; linarith⟩, by simpa using hq, by simpa using hη⟩
  have h2 : ∫ p in As, starRingEnd ℂ (B.mode3D n p) * f (shiftS h p) =
      Complex.exp (I * (B.ws n * h : ℂ)) * ∫ y in Bs, starRingEnd ℂ (B.mode3D n y) * f y := by
    let g : Profile → ℂ := fun y =>
      starRingEnd ℂ (B.mode3D n (y - (h, 0, 0))) * f y
    have hrew : (fun p : Profile => starRingEnd ℂ (B.mode3D n p) * f (shiftS h p)) =
        fun p => g (p + (h, 0, 0)) := by
      ext ⟨s, q, η⟩
      simp [g, shiftS]
    rw [hrew, setIntegral_addRight_eq (h, 0, 0) hpre g]
    have hg_eq : g = fun y =>
        Complex.exp (I * (B.ws n * h : ℂ)) * (starRingEnd ℂ (B.mode3D n y) * f y) := by
      ext y
      dsimp [g]
      rw [B.mode3D_conj_sub_addRight n (h, 0, 0) y]
      have hph : B.phaseCLM n (h, 0, 0) = B.ws n * h := by
        simp [phaseCLM_apply, ws]
      rw [hph]
      push_cast
      ring
    rw [hg_eq, integral_const_mul]
  have h3 : ∫ y in Bs, starRingEnd ℂ (B.mode3D n y) * f y =
      ∫ y, starRingEnd ℂ (B.mode3D n y) * f y ∂B.boxMeas := by
    unfold boxMeas
    rw [← integral_indicator hBs_meas, ← integral_indicator B.measurableSet_boxSet]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    by_cases hyBs : y ∈ Bs
    · simp [Set.indicator, hyBs, hBs_sub hyBs]
    · by_cases hyBox : y ∈ B.boxSet
      · rcases y with ⟨s, q, η⟩
        have ⟨⟨hs1, hs2⟩, hq, hη⟩ := hyBox
        have hle : s ≤ B.as + h := by
          by_contra hgt
          exact hyBs ⟨⟨not_le.1 hgt, hs2⟩, hq, hη⟩
        have hf0 : f (s, q, η) = 0 := by
          by_contra hne
          obtain ⟨hσ_le, _, _⟩ := hsupp _ hne
          unfold as at hle
          linarith [B.hσ]
        simp [Set.indicator, hyBs, hyBox, hf0]
      · simp [Set.indicator, hyBs, hyBox]
  unfold coeff3D
  rw [h1, h2, h3, real_smul, real_smul]
  ring

theorem coeff3D_shiftEta_sub (B : BoxParams) {f : Profile → ℂ} {h : ℝ}
    (hf : MemLp f 2 B.boxMeas)
    (hf_shift : MemLp (fun p => f (shiftEta h p)) 2 B.boxMeas)
    (hsupp : ∀ p : Profile, f p ≠ 0 → B.σ ≤ p.1 ∧ p.1 ≤ B.H1 ∧ |p.2.2| ≤ B.L1)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 2) (n : ℤ × ℤ × ℤ) :
    B.coeff3D (fun p => f (shiftEta h p) - f p) n =
      (Complex.exp (I * ((B.wη n * h : ℝ) : ℂ)) - 1) * B.coeff3D f n := by
  push_cast
  rw [B.coeff3D_sub (hf_shift.integrable one_le_two) (hf.integrable one_le_two) n]
  suffices hshift_eq :
      B.coeff3D (fun p => f (shiftEta h p)) n =
        Complex.exp (I * (B.wη n * h : ℂ)) * B.coeff3D f n by
    rw [hshift_eq]; ring
  set Aη : Set Profile := B.Is ×ˢ (B.Iq ×ˢ Ioc B.aη (B.bη - h))
  set Bη : Set Profile := B.Is ×ˢ (B.Iq ×ˢ Ioc (B.aη + h) B.bη)
  have hAη_meas : MeasurableSet Aη :=
    measurableSet_Ioc.prod (measurableSet_Ioc.prod measurableSet_Ioc)
  have hBη_meas : MeasurableSet Bη :=
    measurableSet_Ioc.prod (measurableSet_Ioc.prod measurableSet_Ioc)
  have hAη_sub : Aη ⊆ B.boxSet := by
    rintro ⟨s, q, η⟩ ⟨hs, hq, ⟨hη1, hη2⟩⟩
    exact ⟨hs, hq, ⟨hη1, by linarith⟩⟩
  have hBη_sub : Bη ⊆ B.boxSet := by
    rintro ⟨s, q, η⟩ ⟨hs, hq, ⟨hη1, hη2⟩⟩
    exact ⟨hs, hq, ⟨by linarith, hη2⟩⟩
  have h1 : ∫ p, starRingEnd ℂ (B.mode3D n p) * f (shiftEta h p) ∂B.boxMeas =
      ∫ p in Aη, starRingEnd ℂ (B.mode3D n p) * f (shiftEta h p) := by
    unfold boxMeas
    rw [← integral_indicator B.measurableSet_boxSet, ← integral_indicator hAη_meas]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    by_cases hpA : p ∈ Aη
    · simp [Set.indicator, hpA, hAη_sub hpA]
    · by_cases hpBox : p ∈ B.boxSet
      · rcases p with ⟨s, q, η⟩
        have ⟨hs, hq, ⟨hη1, hη2⟩⟩ := hpBox
        have hgt : B.bη - h < η := by
          by_contra hle
          exact hpA ⟨hs, hq, ⟨hη1, not_lt.1 hle⟩⟩
        have hf0 : f (shiftEta h (s, q, η)) = 0 := by
          by_contra hne
          obtain ⟨_, _, habs⟩ := hsupp _ hne
          rw [abs_le] at habs
          unfold shiftEta at habs
          unfold bη at hgt
          linarith
        simp [Set.indicator, hpA, hpBox, hf0]
      · simp [Set.indicator, hpA, hpBox]
  have hpre : (fun p : Profile => p + (0, 0, h)) ⁻¹' Bη = Aη := by
    ext ⟨s, q, η⟩
    simp only [Bη, Aη, mem_preimage, mem_prod, mem_Ioc]
    constructor <;> rintro ⟨hs, hq, ⟨h1', h2'⟩⟩ <;>
      exact ⟨by simpa using hs, by simpa using hq, ⟨by dsimp at *; linarith, by dsimp at *; linarith⟩⟩
  have h2 : ∫ p in Aη, starRingEnd ℂ (B.mode3D n p) * f (shiftEta h p) =
      Complex.exp (I * (B.wη n * h : ℂ)) * ∫ y in Bη, starRingEnd ℂ (B.mode3D n y) * f y := by
    let g : Profile → ℂ := fun y =>
      starRingEnd ℂ (B.mode3D n (y - (0, 0, h))) * f y
    have hrew : (fun p : Profile => starRingEnd ℂ (B.mode3D n p) * f (shiftEta h p)) =
        fun p => g (p + (0, 0, h)) := by
      ext ⟨s, q, η⟩
      simp [g, shiftEta]
    rw [hrew, setIntegral_addRight_eq (0, 0, h) hpre g]
    have hg_eq : g = fun y =>
        Complex.exp (I * (B.wη n * h : ℂ)) * (starRingEnd ℂ (B.mode3D n y) * f y) := by
      ext y
      dsimp [g]
      rw [B.mode3D_conj_sub_addRight n (0, 0, h) y]
      have hph : B.phaseCLM n (0, 0, h) = B.wη n * h := by
        simp [phaseCLM_apply, wη]
      rw [hph]
      push_cast
      ring
    rw [hg_eq, integral_const_mul]
  have h3 : ∫ y in Bη, starRingEnd ℂ (B.mode3D n y) * f y =
      ∫ y, starRingEnd ℂ (B.mode3D n y) * f y ∂B.boxMeas := by
    unfold boxMeas
    rw [← integral_indicator hBη_meas, ← integral_indicator B.measurableSet_boxSet]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    by_cases hyB : y ∈ Bη
    · simp [Set.indicator, hyB, hBη_sub hyB]
    · by_cases hyBox : y ∈ B.boxSet
      · rcases y with ⟨s, q, η⟩
        have ⟨hs, hq, ⟨hη1, hη2⟩⟩ := hyBox
        have hle : η ≤ B.aη + h := by
          by_contra hgt
          exact hyB ⟨hs, hq, ⟨not_le.1 hgt, hη2⟩⟩
        have hf0 : f (s, q, η) = 0 := by
          by_contra hne
          obtain ⟨_, _, habs⟩ := hsupp _ hne
          rw [abs_le] at habs
          unfold aη at hle
          linarith
        simp [Set.indicator, hyB, hyBox, hf0]
      · simp [Set.indicator, hyB, hyBox]
  unfold coeff3D
  rw [h1, h2, h3, real_smul, real_smul]
  ring

theorem coeff3D_shiftQ_sub (B : BoxParams) {f : Profile → ℂ} {h : ℝ}
    (hf : MemLp f 2 B.boxMeas)
    (hf_shift : MemLp (fun p => f (shiftQ h p)) 2 B.boxMeas)
    (hper : QPeriodic B.c f)
    (hh0 : 0 ≤ h) (hhc : h ≤ B.c) (n : ℤ × ℤ × ℤ) :
    B.coeff3D (fun p => f (shiftQ h p) - f p) n =
      (Complex.exp (I * ((B.wq n * h : ℝ) : ℂ)) - 1) * B.coeff3D f n := by
  push_cast
  have hint_f : Integrable f B.boxMeas := hf.integrable one_le_two
  have hint_sh : Integrable (fun p => f (shiftQ h p)) B.boxMeas := hf_shift.integrable one_le_two
  rw [B.coeff3D_sub hint_sh hint_f n]
  suffices hshift_eq :
      B.coeff3D (fun p => f (shiftQ h p)) n =
        Complex.exp (I * (B.wq n * h : ℂ)) * B.coeff3D f n by
    rw [hshift_eq]; ring
  set A1 : Set Profile := B.Is ×ˢ (Ioc 0 (B.c - h) ×ˢ B.Iη)
  set A2 : Set Profile := B.Is ×ˢ (Ioc (B.c - h) B.c ×ˢ B.Iη)
  set B1 : Set Profile := B.Is ×ˢ (Ioc h B.c ×ˢ B.Iη)
  set B2 : Set Profile := B.Is ×ˢ (Ioc 0 h ×ˢ B.Iη)
  have hA1_meas : MeasurableSet A1 := measurableSet_Ioc.prod (measurableSet_Ioc.prod measurableSet_Ioc)
  have hA2_meas : MeasurableSet A2 := measurableSet_Ioc.prod (measurableSet_Ioc.prod measurableSet_Ioc)
  have hB1_meas : MeasurableSet B1 := measurableSet_Ioc.prod (measurableSet_Ioc.prod measurableSet_Ioc)
  have hB2_meas : MeasurableSet B2 := measurableSet_Ioc.prod (measurableSet_Ioc.prod measurableSet_Ioc)
  have hA_disj : Disjoint A1 A2 := by
    refine Set.disjoint_left.2 ?_
    rintro ⟨s, q, η⟩ ⟨_, hq1, _⟩ ⟨_, hq2, _⟩
    exact not_lt_of_ge hq1.2 hq2.1
  have hB_disj : Disjoint B2 B1 := by
    refine Set.disjoint_left.2 ?_
    rintro ⟨s, q, η⟩ ⟨_, hq1, _⟩ ⟨_, hq2, _⟩
    exact not_lt_of_ge hq1.2 hq2.1
  have hA_union : A1 ∪ A2 = B.boxSet := by
    ext ⟨s, q, η⟩
    simp only [A1, A2, boxSet, Iq, mem_union, mem_prod, mem_Ioc]
    constructor
    · rintro (⟨hs, ⟨hq1, hq2⟩, hη⟩ | ⟨hs, ⟨hq1, hq2⟩, hη⟩)
      · exact ⟨hs, ⟨hq1, by linarith⟩, hη⟩
      · exact ⟨hs, ⟨by linarith, hq2⟩, hη⟩
    · rintro ⟨hs, ⟨hq1, hq2⟩, hη⟩
      by_cases hle : q ≤ B.c - h
      · exact Or.inl ⟨hs, ⟨hq1, hle⟩, hη⟩
      · exact Or.inr ⟨hs, ⟨not_le.1 hle, hq2⟩, hη⟩
  have hB_union : B2 ∪ B1 = B.boxSet := by
    ext ⟨s, q, η⟩
    simp only [B1, B2, boxSet, Iq, mem_union, mem_prod, mem_Ioc]
    constructor
    · rintro (⟨hs, ⟨hq1, hq2⟩, hη⟩ | ⟨hs, ⟨hq1, hq2⟩, hη⟩)
      · exact ⟨hs, ⟨hq1, by linarith⟩, hη⟩
      · exact ⟨hs, ⟨by linarith, hq2⟩, hη⟩
    · rintro ⟨hs, ⟨hq1, hq2⟩, hη⟩
      by_cases hle : q ≤ h
      · exact Or.inl ⟨hs, ⟨hq1, hle⟩, hη⟩
      · exact Or.inr ⟨hs, ⟨not_le.1 hle, hq2⟩, hη⟩
  have hi_sh := B.integrable_conj_mode3D_mul hint_sh n
  have hi_f := B.integrable_conj_mode3D_mul hint_f n
  have hpre1 : (fun p : Profile => p + (0, h, 0)) ⁻¹' B1 = A1 := by
    ext ⟨s, q, η⟩
    simp only [B1, A1, mem_preimage, mem_prod, mem_Ioc]
    constructor <;> rintro ⟨hs, ⟨h1', h2'⟩, hη⟩ <;>
      exact ⟨by simpa using hs, ⟨by dsimp at *; linarith, by dsimp at *; linarith⟩, by simpa using hη⟩
  have hpre2 : (fun p : Profile => p + (0, h - B.c, 0)) ⁻¹' B2 = A2 := by
    ext ⟨s, q, η⟩
    simp only [B2, A2, mem_preimage, mem_prod, mem_Ioc]
    constructor <;> rintro ⟨hs, ⟨h1', h2'⟩, hη⟩ <;>
      exact ⟨by simpa using hs, ⟨by dsimp at *; linarith, by dsimp at *; linarith⟩, by simpa using hη⟩
  let g : Profile → ℂ := fun y => starRingEnd ℂ (B.mode3D n (y - (0, h, 0))) * f y
  have hg_eq : g = fun y =>
      Complex.exp (I * (B.wq n * h : ℂ)) * (starRingEnd ℂ (B.mode3D n y) * f y) := by
    ext y
    dsimp [g]
    rw [B.mode3D_conj_sub_addRight n (0, h, 0) y]
    have hph : B.phaseCLM n (0, h, 0) = B.wq n * h := by simp [phaseCLM_apply, wq]
    rw [hph]; push_cast; ring
  have hpart1 : ∫ p in A1, starRingEnd ℂ (B.mode3D n p) * f (shiftQ h p) =
      Complex.exp (I * (B.wq n * h : ℂ)) * ∫ y in B1, starRingEnd ℂ (B.mode3D n y) * f y := by
    have hrew : (fun p : Profile => starRingEnd ℂ (B.mode3D n p) * f (shiftQ h p)) =
        fun p => g (p + (0, h, 0)) := by
      ext ⟨s, q, η⟩
      simp [g, shiftQ]
    rw [hrew, setIntegral_addRight_eq (0, h, 0) hpre1 g, hg_eq, integral_const_mul]
  have hpart2 : ∫ p in A2, starRingEnd ℂ (B.mode3D n p) * f (shiftQ h p) =
      Complex.exp (I * (B.wq n * h : ℂ)) * ∫ y in B2, starRingEnd ℂ (B.mode3D n y) * f y := by
    have hrew : (fun p : Profile => starRingEnd ℂ (B.mode3D n p) * f (shiftQ h p)) =
        fun p => g (p + (0, h - B.c, 0)) := by
      ext ⟨s, q, η⟩
      simp only [g, shiftQ, Prod.mk_add_mk, Prod.mk_sub_mk, add_zero, sub_zero]
      have hf_per : f (s, q + h, η) = f (s, q + (h - B.c), η) := by
        have := hper (s, q + (h - B.c), η)
        simpa [add_assoc, sub_add_cancel] using this
      have hm_per : B.mode3D n (s, q, η) = B.mode3D n (s, q + (h - B.c) - h, η) := by
        have := B.qPeriodic_mode3D n (s, q - B.c, η)
        have hpt1 : (s, q - B.c + B.c, η) = (s, q, η) :=
          Prod.ext rfl (Prod.ext (sub_add_cancel _ _) rfl)
        have hpt2 : (s, q + (h - B.c) - h, η) = (s, q - B.c, η) :=
          Prod.ext rfl (Prod.ext (by ring) rfl)
        rw [hpt1] at this
        rw [hpt2, ← this]
      rw [hf_per, hm_per]
    rw [hrew, setIntegral_addRight_eq (0, h - B.c, 0) hpre2 g, hg_eq, integral_const_mul]
  have hi_A1 : IntegrableOn (fun p => starRingEnd ℂ (B.mode3D n p) * f (shiftQ h p)) A1 volume :=
    hi_sh.mono_measure (Measure.restrict_mono (by rw [← hA_union]; exact subset_union_left) le_rfl)
  have hi_A2 : IntegrableOn (fun p => starRingEnd ℂ (B.mode3D n p) * f (shiftQ h p)) A2 volume :=
    hi_sh.mono_measure (Measure.restrict_mono (by rw [← hA_union]; exact subset_union_right) le_rfl)
  have hi_B2 : IntegrableOn (fun y => starRingEnd ℂ (B.mode3D n y) * f y) B2 volume :=
    hi_f.mono_measure (Measure.restrict_mono (by rw [← hB_union]; exact subset_union_left) le_rfl)
  have hi_B1 : IntegrableOn (fun y => starRingEnd ℂ (B.mode3D n y) * f y) B1 volume :=
    hi_f.mono_measure (Measure.restrict_mono (by rw [← hB_union]; exact subset_union_right) le_rfl)
  have hlhs : ∫ p, starRingEnd ℂ (B.mode3D n p) * f (shiftQ h p) ∂B.boxMeas =
      Complex.exp (I * (B.wq n * h : ℂ)) *
        ((∫ y in B1, starRingEnd ℂ (B.mode3D n y) * f y) +
         (∫ y in B2, starRingEnd ℂ (B.mode3D n y) * f y)) := by
    unfold boxMeas
    rw [← hA_union, setIntegral_union hA_disj hA2_meas hi_A1 hi_A2, hpart1, hpart2, ← mul_add]
  have hrhs : ∫ y, starRingEnd ℂ (B.mode3D n y) * f y ∂B.boxMeas =
      (∫ y in B2, starRingEnd ℂ (B.mode3D n y) * f y) +
      (∫ y in B1, starRingEnd ℂ (B.mode3D n y) * f y) := by
    unfold boxMeas
    rw [← hB_union, setIntegral_union hB_disj hB1_meas hi_B2 hi_B1]
  unfold coeff3D
  rw [hlhs, hrhs, real_smul, real_smul]
  ring

/-- Lower bound on the 1D difference-quotient kernel `∫_{0}^{δ} |h|^{-3/2} ‖e^{iwh} - 1‖² dh`
for high wavenumbers `2π N < |w|`. -/
private theorem highFreq_phase_kernel_lower {δ N w : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hN : 1 ≤ N) (hw : 2 * Real.pi * N < |w|) :
    ENNReal.ofReal ((1 / 6 : ℝ) * δ ^ (3 / 2 : ℝ) * N ^ (1 / 2 : ℝ)) ≤
      ∫⁻ h in Ioc 0 δ,
        ENNReal.ofReal (|h| ^ (-(3 / 2 : ℝ)) * ‖Complex.exp (I * ((w * h : ℝ) : ℂ)) - 1‖ ^ 2) := by
  have hN0 : 0 < N := by linarith
  have hpi2 : 1 ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
  have hNw : N < |w| := (le_mul_of_one_le_left hN0.le hpi2).trans_lt hw
  have hw0 : 0 < |w| := hN0.trans hNw
  set r : ℝ := min δ (|w|⁻¹)
  have hr0 : 0 < r := lt_min hδ0 (inv_pos.2 hw0)
  have hr_sub : Ioc 0 r ⊆ Ioc 0 δ := Ioc_subset_Ioc_right (min_le_left _ _)
  have hpt : ∀ h ∈ Ioc 0 r,
      (1 / 4 : ℝ) * w ^ 2 * h ^ (1 / 2 : ℝ) ≤
        |h| ^ (-(3 / 2 : ℝ)) * ‖Complex.exp (I * ((w * h : ℝ) : ℂ)) - 1‖ ^ 2 := by
    intro h ⟨hh0, hhr⟩
    have hwh_le_one : |w| * h ≤ 1 := by
      have hle : h ≤ |w|⁻¹ := hhr.trans (min_le_right _ _)
      calc |w| * h ≤ |w| * |w|⁻¹ := mul_le_mul_of_nonneg_left hle hw0.le
        _ = 1 := mul_inv_cancel₀ hw0.ne'
    have hwh_pi : |w| * h ≤ Real.pi / 2 := by linarith [Real.two_le_pi]
    have hsin_le : (1 / 2 : ℝ) * |w| * h ≤ ‖Complex.exp (I * ((w * h : ℝ) : ℂ)) - 1‖ := by
      have him : (Complex.exp (I * ((w * h : ℝ) : ℂ)) - 1).im = Real.sin (w * h) := by
        rw [mul_comm I _, Complex.sub_im, Complex.exp_ofReal_mul_I_im, Complex.one_im, sub_zero]
      have habs_sin : Real.sin (|w| * h) ≤ |Real.sin (w * h)| := by
        by_cases hw_nn : 0 ≤ w
        · rw [abs_of_nonneg hw_nn]
          exact le_abs_self _
        · push Not at hw_nn
          rw [abs_of_neg hw_nn, neg_mul, Real.sin_neg]
          exact neg_le_abs _
      have hmul_sin := Real.mul_le_sin (mul_nonneg hw0.le hh0.le) hwh_pi
      have hpi4 : (1 / 2 : ℝ) ≤ 2 / Real.pi := by
        rw [div_le_div_iff₀ (by norm_num) Real.pi_pos]
        linarith [Real.pi_lt_four]
      calc (1 / 2 : ℝ) * |w| * h = (1 / 2) * (|w| * h) := by ring
        _ ≤ (2 / Real.pi) * (|w| * h) :=
            mul_le_mul_of_nonneg_right hpi4 (mul_nonneg hw0.le hh0.le)
        _ ≤ Real.sin (|w| * h) := hmul_sin
        _ ≤ |Real.sin (w * h)| := habs_sin
        _ = |(Complex.exp (I * ((w * h : ℝ) : ℂ)) - 1).im| := by rw [him]
        _ ≤ ‖Complex.exp (I * ((w * h : ℝ) : ℂ)) - 1‖ := Complex.abs_im_le_norm _
    have hsq : (1 / 4 : ℝ) * w ^ 2 * h ^ 2 ≤ ‖Complex.exp (I * ((w * h : ℝ) : ℂ)) - 1‖ ^ 2 := by
      have h1 := pow_le_pow_left₀ (by positivity) hsin_le 2
      have habs2 : |w| ^ 2 = w ^ 2 := sq_abs w
      nlinarith
    calc (1 / 4 : ℝ) * w ^ 2 * h ^ (1 / 2 : ℝ)
        = h ^ (-(3 / 2 : ℝ)) * ((1 / 4 : ℝ) * w ^ 2 * h ^ 2) := by
            have hrp : h ^ (-(3 / 2 : ℝ)) * h ^ 2 = h ^ (1 / 2 : ℝ) := by
              rw [← Real.rpow_two, ← Real.rpow_add hh0]
              congr 1; ring
            rw [← hrp]
            ring
      _ ≤ |h| ^ (-(3 / 2 : ℝ)) * ‖Complex.exp (I * ((w * h : ℝ) : ℂ)) - 1‖ ^ 2 := by
            rw [abs_of_pos hh0]
            exact mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hh0.le _)
  have hint_half : IntegrableOn (fun h : ℝ => (1 / 4 : ℝ) * w ^ 2 * h ^ (1 / 2 : ℝ)) (Ioc 0 r) volume := by
    have hi : IntervalIntegrable (fun h : ℝ => h ^ (1 / 2 : ℝ)) volume 0 r :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    have hi' : IntegrableOn (fun h : ℝ => h ^ (1 / 2 : ℝ)) (Ioc 0 r) volume := by
      simpa [uIoc_of_le hr0.le] using hi.1
    exact hi'.const_mul ((1 / 4 : ℝ) * w ^ 2)
  have hint_val : ∫ h in Ioc 0 r, (1 / 4 : ℝ) * w ^ 2 * h ^ (1 / 2 : ℝ) =
      (1 / 6 : ℝ) * w ^ 2 * r ^ (3 / 2 : ℝ) := by
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hr0.le,
      integral_rpow (Or.inl (by norm_num)),
      Real.zero_rpow (by norm_num)]
    ring
  have hlow_r : (1 / 6 : ℝ) * δ ^ (3 / 2 : ℝ) * N ^ (1 / 2 : ℝ) ≤
      (1 / 6 : ℝ) * w ^ 2 * r ^ (3 / 2 : ℝ) := by
    by_cases hcase : δ ≤ |w|⁻¹
    · have hr_eq : r = δ := min_eq_left hcase
      rw [hr_eq]
      have hN_sq : N ^ (1 / 2 : ℝ) ≤ w ^ 2 := by
        calc N ^ (1 / 2 : ℝ) ≤ N ^ (2 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
          _ = N ^ 2 := Real.rpow_two N
          _ ≤ |w| ^ 2 := pow_le_pow_left₀ hN0.le hNw.le 2
          _ = w ^ 2 := sq_abs w
      have hδ_nn : 0 ≤ δ ^ (3 / 2 : ℝ) := Real.rpow_nonneg hδ0.le _
      nlinarith
    · push Not at hcase
      have hr_eq : r = |w|⁻¹ := min_eq_right hcase.le
      rw [hr_eq]
      have hw_rpow : w ^ 2 * (|w|⁻¹) ^ (3 / 2 : ℝ) = |w| ^ (1 / 2 : ℝ) := by
        rw [← sq_abs w, ← Real.rpow_two |w|, Real.inv_rpow hw0.le,
          ← Real.rpow_neg hw0.le, ← Real.rpow_add hw0]
        norm_num
      have hδ_le_one : δ ^ (3 / 2 : ℝ) ≤ 1 := by
        calc δ ^ (3 / 2 : ℝ) ≤ (1 : ℝ) ^ (3 / 2 : ℝ) :=
              Real.rpow_le_rpow hδ0.le (hδ1.trans (by norm_num)) (by norm_num)
          _ = 1 := Real.one_rpow _
      have hN_le_w : N ^ (1 / 2 : ℝ) ≤ |w| ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow hN0.le hNw.le (by norm_num)
      have hN_nn : 0 ≤ N ^ (1 / 2 : ℝ) := Real.rpow_nonneg hN0.le _
      calc (1 / 6 : ℝ) * δ ^ (3 / 2 : ℝ) * N ^ (1 / 2 : ℝ)
          ≤ (1 / 6 : ℝ) * 1 * |w| ^ (1 / 2 : ℝ) := by nlinarith
        _ = (1 / 6 : ℝ) * w ^ 2 * (|w|⁻¹) ^ (3 / 2 : ℝ) := by
          rw [mul_assoc (1 / 6 : ℝ) (w ^ 2), hw_rpow]; ring
  calc ENNReal.ofReal ((1 / 6 : ℝ) * δ ^ (3 / 2 : ℝ) * N ^ (1 / 2 : ℝ))
      ≤ ENNReal.ofReal ((1 / 6 : ℝ) * w ^ 2 * r ^ (3 / 2 : ℝ)) :=
        ENNReal.ofReal_le_ofReal hlow_r
    _ = ENNReal.ofReal (∫ h in Ioc 0 r, (1 / 4 : ℝ) * w ^ 2 * h ^ (1 / 2 : ℝ)) := by
        rw [hint_val]
    _ = ∫⁻ h in Ioc 0 r, ENNReal.ofReal ((1 / 4 : ℝ) * w ^ 2 * h ^ (1 / 2 : ℝ)) := by
        refine ofReal_integral_eq_lintegral_ofReal hint_half ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hh
        exact mul_nonneg (by positivity) (Real.rpow_nonneg hh.1.le _)
    _ ≤ ∫⁻ h in Ioc 0 r,
          ENNReal.ofReal (|h| ^ (-(3 / 2 : ℝ)) * ‖Complex.exp (I * ((w * h : ℝ) : ℂ)) - 1‖ ^ 2) := by
        refine setLIntegral_mono' measurableSet_Ioc fun h hh => ?_
        exact ENNReal.ofReal_le_ofReal (hpt h hh)
    _ ≤ ∫⁻ h in Ioc 0 δ,
          ENNReal.ofReal (|h| ^ (-(3 / 2 : ℝ)) * ‖Complex.exp (I * ((w * h : ℝ) : ℂ)) - 1‖ ^ 2) :=
        lintegral_mono_set hr_sub

/-- Directional spectral Gagliardo bound on `B.boxMeas`. -/
private theorem directional_gagliardo_spectral_bound (B : BoxParams)
    (shift : ℝ → Profile → Profile) (w_fn : (ℤ × ℤ × ℤ) → ℝ)
    {u : Profile → MeridC} (hu_mem : MemLp u 2 (cellMeasure B.c))
    (hshift_mem : ∀ h ∈ Ioc 0 B.deltaStep, MemLp (fun p => u (shift h p)) 2 (cellMeasure B.c))
    (hcoeff : ∀ (j : Fin 2) (h : ℝ), h ∈ Ioc 0 B.deltaStep → ∀ n : ℤ × ℤ × ℤ,
      B.coeff3D (fun p => u (shift h p) j - u p j) n =
        (Complex.exp (I * ((w_fn n * h : ℝ) : ℂ)) - 1) * B.coeff3D (fun p => u p j) n)
    (hint_gag : IntegrableOn
      (fun h : ℝ => |h| ^ (-(3 / 2 : ℝ)) * ∫ p, ‖u (shift h p) - u p‖ ^ 2 ∂(cellMeasure B.c))
      (Icc (-1 : ℝ) 1) volume)
    (j : Fin 2) :
    ENNReal.ofReal B.volBox *
      (∑' n : ℤ × ℤ × ℤ,
        (∫⁻ h in Ioc 0 B.deltaStep,
          ENNReal.ofReal (|h| ^ (-(3 / 2 : ℝ)) * ‖Complex.exp (I * ((w_fn n * h : ℝ) : ℂ)) - 1‖ ^ 2)) *
        ENNReal.ofReal (‖B.coeff3D (fun p => u p j) n‖ ^ 2)) ≤
      ENNReal.ofReal (gagliardoDir14 B.c shift u ^ 2) := by
  set c_n : (ℤ × ℤ × ℤ) → ℝ := fun n => ‖B.coeff3D (fun p => u p j) n‖ ^ 2
  have hmeas_term : ∀ n : ℤ × ℤ × ℤ, Measurable (fun h : ℝ =>
      ENNReal.ofReal (|h| ^ (-(3 / 2 : ℝ)) * ‖Complex.exp (I * ((w_fn n * h : ℝ) : ℂ)) - 1‖ ^ 2) *
        ENNReal.ofReal (c_n n)) := by
    intro n
    have h1 : Measurable (fun h : ℝ => |h| ^ (-(3 / 2 : ℝ))) :=
      (continuous_abs.measurable).pow_const _
    have h2 : Continuous (fun h : ℝ => ‖Complex.exp (I * ((w_fn n * h : ℝ) : ℂ)) - 1‖ ^ 2) := by
      have hc : Continuous (fun h : ℝ => I * ((w_fn n * h : ℝ) : ℂ)) :=
        continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id))
      exact ((Complex.continuous_exp.comp hc).sub continuous_const).norm.pow 2
    exact ((h1.mul h2.measurable).ennreal_ofReal).mul measurable_const
  have hpull_int : ∀ n : ℤ × ℤ × ℤ,
      (∫⁻ h in Ioc 0 B.deltaStep,
        ENNReal.ofReal (|h| ^ (-(3 / 2 : ℝ)) * ‖Complex.exp (I * ((w_fn n * h : ℝ) : ℂ)) - 1‖ ^ 2)) *
        ENNReal.ofReal (c_n n) =
      ∫⁻ h in Ioc 0 B.deltaStep,
        ENNReal.ofReal (|h| ^ (-(3 / 2 : ℝ)) * ‖Complex.exp (I * ((w_fn n * h : ℝ) : ℂ)) - 1‖ ^ 2) *
          ENNReal.ofReal (c_n n) := by
    intro n
    symm
    exact lintegral_mul_const (ENNReal.ofReal (c_n n))
      (((continuous_abs.measurable.pow_const _).mul
        (((Complex.continuous_exp.comp
          (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)))).sub
            continuous_const).norm.pow 2).measurable).ennreal_ofReal)
  rw [tsum_congr hpull_int, ← lintegral_tsum (fun n => (hmeas_term n).aemeasurable),
    ← lintegral_const_mul _ (Measurable.tsum hmeas_term)]
  have hpt_h : ∀ h ∈ Ioc 0 B.deltaStep,
      ENNReal.ofReal B.volBox *
        (∑' n : ℤ × ℤ × ℤ,
          ENNReal.ofReal (|h| ^ (-(3 / 2 : ℝ)) * ‖Complex.exp (I * ((w_fn n * h : ℝ) : ℂ)) - 1‖ ^ 2) *
            ENNReal.ofReal (c_n n)) ≤
      ENNReal.ofReal (|h| ^ (-(3 / 2 : ℝ)) * ∫ p, ‖u (shift h p) - u p‖ ^ 2 ∂(cellMeasure B.c)) := by
    intro h hh
    have hdiff_cell : MemLp (fun p => u (shift h p) - u p) 2 (cellMeasure B.c) :=
      (hshift_mem h hh).sub hu_mem
    have hdiff_j : MemLp (fun p => u (shift h p) j - u p j) 2 B.boxMeas :=
      B.memLp_coord_boxMeas hdiff_cell j
    have hparseval := B.tsum_coeff3D_sq hdiff_j
    have hterm_eq : ∀ n : ℤ × ℤ × ℤ,
        ENNReal.ofReal (|h| ^ (-(3 / 2 : ℝ)) * ‖Complex.exp (I * ((w_fn n * h : ℝ) : ℂ)) - 1‖ ^ 2) *
          ENNReal.ofReal (c_n n) =
        ENNReal.ofReal (|h| ^ (-(3 / 2 : ℝ))) *
          ENNReal.ofReal (‖B.coeff3D (fun p => u (shift h p) j - u p j) n‖ ^ 2) := by
      intro n
      rw [hcoeff j h hh n, norm_mul, mul_pow,
        ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (abs_nonneg h) _) (sq_nonneg _)),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg h) _)]
      congr 1
      dsimp [c_n]
      ring
    simp_rw [hterm_eq]
    rw [ENNReal.tsum_mul_left, hparseval, ← mul_assoc,
      mul_comm (ENNReal.ofReal B.volBox) (ENNReal.ofReal (|h| ^ (-(3 / 2 : ℝ)))),
      mul_assoc, ← ENNReal.ofReal_mul B.hvolBox_pos.le,
      ← mul_assoc, mul_inv_cancel₀ B.hvolBox_pos.ne', one_mul,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg h) _)]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (abs_nonneg h) _))
    have hint_cell : Integrable (fun p => ‖u (shift h p) - u p‖ ^ 2) (cellMeasure B.c) :=
      (memLp_two_iff_integrable_sq_norm hdiff_cell.1).1 hdiff_cell
    have hint_box : Integrable (fun p => ‖u (shift h p) - u p‖ ^ 2) B.boxMeas := by
      rw [← B.cellMeasure_restrict_boxSet]
      exact hint_cell.restrict
    have hi_j : Integrable (fun p => ‖u (shift h p) j - u p j‖ ^ 2) B.boxMeas :=
      (memLp_two_iff_integrable_sq_norm hdiff_j.1).1 hdiff_j
    calc ∫ p, ‖u (shift h p) j - u p j‖ ^ 2 ∂B.boxMeas
        ≤ ∫ p, ‖u (shift h p) - u p‖ ^ 2 ∂B.boxMeas := by
          refine integral_mono hi_j hint_box fun p => ?_
          rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
          fin_cases j <;> simp
      _ = ∫ p in B.boxSet, ‖u (shift h p) - u p‖ ^ 2 ∂(cellMeasure B.c) := by
          rw [B.cellMeasure_restrict_boxSet]
      _ ≤ ∫ p, ‖u (shift h p) - u p‖ ^ 2 ∂(cellMeasure B.c) :=
          setIntegral_le_integral hint_cell (Eventually.of_forall fun _ => sq_nonneg _)
  have hsub_Icc : Ioc 0 B.deltaStep ⊆ Icc (-1 : ℝ) 1 := by
    intro h ⟨hh1, hh2⟩
    exact ⟨by linarith, hh2.trans (B.deltaStep_le_half.trans (by norm_num))⟩
  calc ∫⁻ h in Ioc 0 B.deltaStep,
        ENNReal.ofReal B.volBox *
          (∑' n : ℤ × ℤ × ℤ,
            ENNReal.ofReal (|h| ^ (-(3 / 2 : ℝ)) * ‖Complex.exp (I * ((w_fn n * h : ℝ) : ℂ)) - 1‖ ^ 2) *
              ENNReal.ofReal (c_n n))
      ≤ ∫⁻ h in Ioc 0 B.deltaStep,
          ENNReal.ofReal (|h| ^ (-(3 / 2 : ℝ)) * ∫ p, ‖u (shift h p) - u p‖ ^ 2 ∂(cellMeasure B.c)) :=
        setLIntegral_mono' measurableSet_Ioc hpt_h
    _ ≤ ∫⁻ h in Icc (-1 : ℝ) 1,
          ENNReal.ofReal (|h| ^ (-(3 / 2 : ℝ)) * ∫ p, ‖u (shift h p) - u p‖ ^ 2 ∂(cellMeasure B.c)) :=
        lintegral_mono_set hsub_Icc
    _ = ENNReal.ofReal
          (∫ h in Icc (-1 : ℝ) 1,
            |h| ^ (-(3 / 2 : ℝ)) * ∫ p, ‖u (shift h p) - u p‖ ^ 2 ∂(cellMeasure B.c)) :=
        (ofReal_integral_eq_lintegral_ofReal hint_gag
          (Eventually.of_forall fun h => mul_nonneg (Real.rpow_nonneg (abs_nonneg h) _)
            (integral_nonneg fun _ => sq_nonneg _))).symm
    _ = ENNReal.ofReal (gagliardoDir14 B.c shift u ^ 2) := by
        congr 1
        unfold gagliardoDir14
        rw [← Real.sqrt_eq_rpow, Real.sq_sqrt]
        exact integral_nonneg fun h => mul_nonneg (Real.rpow_nonneg (abs_nonneg h) _)
          (integral_nonneg fun _ => sq_nonneg _)

/-- **Main `H^{1/4}` high-frequency decay bound** on `B.boxMeas`. -/
theorem h14_highFreq_bound (B : BoxParams) {U : HSpace B.c MeridC} {u : Profile → MeridC}
    (hw : HasCellH14 B.c B.σ B.H1 B.L1 U u) {N : ℝ} (hN : 1 ≤ N) :
    ∫ p, ‖u p - B.projMerid N u p‖ ^ 2 ∂B.boxMeas ≤
      12 * B.deltaStep ^ (-(3 / 2 : ℝ)) * N ^ (-(1 / 2 : ℝ)) * cellH14Norm B.c u ^ 2 := by
  have hN0 : 0 < N := by linarith
  have hδ0 : 0 < B.deltaStep := B.deltaStep_pos
  have hδ1 : B.deltaStep ≤ 1 / 2 := B.deltaStep_le_half
  set K : ℝ := (1 / 6 : ℝ) * B.deltaStep ^ (3 / 2 : ℝ) * N ^ (1 / 2 : ℝ)
  have hK_pos : 0 < K := by positivity
  have hK_inv : K⁻¹ = 6 * B.deltaStep ^ (-(3 / 2 : ℝ)) * N ^ (-(1 / 2 : ℝ)) := by
    dsimp [K]
    rw [mul_inv, mul_inv, ← Real.rpow_neg hδ0.le, ← Real.rpow_neg hN0.le]
    ring
  have hsupp_coord : ∀ (j : Fin 2) (p : Profile), u p j ≠ 0 →
      B.σ ≤ p.1 ∧ p.1 ≤ B.H1 ∧ |p.2.2| ≤ B.L1 :=
    fun j p hp => hw.support_u p (fun hu0 => by simp [hu0] at hp)
  have hper_coord : ∀ j : Fin 2, QPeriodic B.c (fun p => u p j) :=
    fun j p => congr_arg (fun v : MeridC => v j) (hw.periodic_u p)
  have h_coord : ∀ j : Fin 2,
      ∫ p, ‖u p j - B.trigSum (B.freqSet N) (B.coeff3D (fun q => u q j)) p‖ ^ 2 ∂B.boxMeas ≤
        6 * B.deltaStep ^ (-(3 / 2 : ℝ)) * N ^ (-(1 / 2 : ℝ)) *
          (gagliardoDir14 B.c shiftS u ^ 2 +
           gagliardoDir14 B.c shiftQ u ^ 2 +
           gagliardoDir14 B.c shiftEta u ^ 2) := by
    intro j
    have hu_j := B.memLp_coord_boxMeas hw.memLp_u j
    have htail := B.ofReal_integral_sub_trigSum_sq hu_j (B.freqSet N)
    have hdir_s := B.directional_gagliardo_spectral_bound shiftS B.ws hw.memLp_u
      (fun h hh => B.memLp_shiftS_cellMeasure hw.memLp_u hh.1.le)
      (fun j' h hh n => B.coeff3D_shiftS_sub (B.memLp_coord_boxMeas hw.memLp_u j')
        (B.memLp_coord_boxMeas (B.memLp_shiftS_cellMeasure hw.memLp_u hh.1.le) j')
        (hsupp_coord j') hh.1.le (hh.2.trans B.deltaStep_le_sigma_div_four) n)
      hw.integrable_s j
    have hdir_q := B.directional_gagliardo_spectral_bound shiftQ B.wq hw.memLp_u
      (fun h hh => B.memLp_shiftQ_cellMeasure hw.memLp_u hw.periodic_u hh.1.le
        (hh.2.trans (B.deltaStep_le_c_div_two.trans (by linarith [B.hc]))))
      (fun j' h hh n => B.coeff3D_shiftQ_sub (B.memLp_coord_boxMeas hw.memLp_u j')
        (B.memLp_coord_boxMeas (B.memLp_shiftQ_cellMeasure hw.memLp_u hw.periodic_u hh.1.le
          (hh.2.trans (B.deltaStep_le_c_div_two.trans (by linarith [B.hc])))) j')
        (hper_coord j') hh.1.le
        (hh.2.trans (B.deltaStep_le_c_div_two.trans (by linarith [B.hc]))) n)
      hw.integrable_q j
    have hdir_η := B.directional_gagliardo_spectral_bound shiftEta B.wη hw.memLp_u
      (fun h _ => B.memLp_shiftEta_cellMeasure hw.memLp_u h)
      (fun j' h hh n => B.coeff3D_shiftEta_sub (B.memLp_coord_boxMeas hw.memLp_u j')
        (B.memLp_coord_boxMeas (B.memLp_shiftEta_cellMeasure hw.memLp_u h) j')
        (hsupp_coord j') hh.1.le (hh.2.trans hδ1) n)
      hw.integrable_eta j
    have hterm : ∀ n : ℤ × ℤ × ℤ,
        ENNReal.ofReal K *
          (if n ∈ B.freqSet N then 0 else ENNReal.ofReal (‖B.coeff3D (fun q => u q j) n‖ ^ 2)) ≤
        ((∫⁻ h in Ioc 0 B.deltaStep,
            ENNReal.ofReal (|h| ^ (-(3 / 2 : ℝ)) * ‖Complex.exp (I * ((B.ws n * h : ℝ) : ℂ)) - 1‖ ^ 2)) *
          ENNReal.ofReal (‖B.coeff3D (fun q => u q j) n‖ ^ 2)) +
        ((∫⁻ h in Ioc 0 B.deltaStep,
            ENNReal.ofReal (|h| ^ (-(3 / 2 : ℝ)) * ‖Complex.exp (I * ((B.wq n * h : ℝ) : ℂ)) - 1‖ ^ 2)) *
          ENNReal.ofReal (‖B.coeff3D (fun q => u q j) n‖ ^ 2)) +
        ((∫⁻ h in Ioc 0 B.deltaStep,
            ENNReal.ofReal (|h| ^ (-(3 / 2 : ℝ)) * ‖Complex.exp (I * ((B.wη n * h : ℝ) : ℂ)) - 1‖ ^ 2)) *
          ENNReal.ofReal (‖B.coeff3D (fun q => u q j) n‖ ^ 2)) := by
      intro n
      by_cases hn : n ∈ B.freqSet N
      · simp [hn]
      · simp only [hn, ↓reduceIte]
        rcases B.highFreq_wavenumber_lt N hn with hs | hq | hη
        · have hlow := highFreq_phase_kernel_lower hδ0 hδ1 hN hs
          calc ENNReal.ofReal K * ENNReal.ofReal (‖B.coeff3D (fun q => u q j) n‖ ^ 2)
              ≤ (∫⁻ h in Ioc 0 B.deltaStep,
                  ENNReal.ofReal (|h| ^ (-(3 / 2 : ℝ)) * ‖Complex.exp (I * ((B.ws n * h : ℝ) : ℂ)) - 1‖ ^ 2)) *
                  ENNReal.ofReal (‖B.coeff3D (fun q => u q j) n‖ ^ 2) :=
                mul_le_mul_of_nonneg_right hlow zero_le
            _ ≤ _ := (le_add_of_nonneg_right zero_le).trans (le_add_of_nonneg_right zero_le)
        · have hlow := highFreq_phase_kernel_lower hδ0 hδ1 hN hq
          calc ENNReal.ofReal K * ENNReal.ofReal (‖B.coeff3D (fun q => u q j) n‖ ^ 2)
              ≤ (∫⁻ h in Ioc 0 B.deltaStep,
                  ENNReal.ofReal (|h| ^ (-(3 / 2 : ℝ)) * ‖Complex.exp (I * ((B.wq n * h : ℝ) : ℂ)) - 1‖ ^ 2)) *
                  ENNReal.ofReal (‖B.coeff3D (fun q => u q j) n‖ ^ 2) :=
                mul_le_mul_of_nonneg_right hlow zero_le
            _ ≤ _ := (le_add_of_nonneg_left zero_le).trans (le_add_of_nonneg_right zero_le)
        · have hlow := highFreq_phase_kernel_lower hδ0 hδ1 hN hη
          calc ENNReal.ofReal K * ENNReal.ofReal (‖B.coeff3D (fun q => u q j) n‖ ^ 2)
              ≤ (∫⁻ h in Ioc 0 B.deltaStep,
                  ENNReal.ofReal (|h| ^ (-(3 / 2 : ℝ)) * ‖Complex.exp (I * ((B.wη n * h : ℝ) : ℂ)) - 1‖ ^ 2)) *
                  ENNReal.ofReal (‖B.coeff3D (fun q => u q j) n‖ ^ 2) :=
                mul_le_mul_of_nonneg_right hlow zero_le
            _ ≤ _ := le_add_of_nonneg_left zero_le
    have hmul_le :
        ENNReal.ofReal K *
          ENNReal.ofReal (∫ p, ‖u p j - B.trigSum (B.freqSet N) (B.coeff3D (fun q => u q j)) p‖ ^ 2 ∂B.boxMeas) ≤
        ENNReal.ofReal
          (gagliardoDir14 B.c shiftS u ^ 2 +
           gagliardoDir14 B.c shiftQ u ^ 2 +
           gagliardoDir14 B.c shiftEta u ^ 2) := by
      rw [htail, ← mul_assoc, mul_comm (ENNReal.ofReal K) (ENNReal.ofReal B.volBox),
        mul_assoc, ← ENNReal.tsum_mul_left]
      calc ENNReal.ofReal B.volBox *
              ∑' n, ENNReal.ofReal K *
                (if n ∈ B.freqSet N then 0 else ENNReal.ofReal (‖B.coeff3D (fun q => u q j) n‖ ^ 2))
          ≤ ENNReal.ofReal B.volBox *
              ∑' n,
                (((∫⁻ h in Ioc 0 B.deltaStep,
                    ENNReal.ofReal (|h| ^ (-(3 / 2 : ℝ)) * ‖Complex.exp (I * ((B.ws n * h : ℝ) : ℂ)) - 1‖ ^ 2)) *
                  ENNReal.ofReal (‖B.coeff3D (fun q => u q j) n‖ ^ 2)) +
                 ((∫⁻ h in Ioc 0 B.deltaStep,
                    ENNReal.ofReal (|h| ^ (-(3 / 2 : ℝ)) * ‖Complex.exp (I * ((B.wq n * h : ℝ) : ℂ)) - 1‖ ^ 2)) *
                  ENNReal.ofReal (‖B.coeff3D (fun q => u q j) n‖ ^ 2)) +
                 ((∫⁻ h in Ioc 0 B.deltaStep,
                    ENNReal.ofReal (|h| ^ (-(3 / 2 : ℝ)) * ‖Complex.exp (I * ((B.wη n * h : ℝ) : ℂ)) - 1‖ ^ 2)) *
                  ENNReal.ofReal (‖B.coeff3D (fun q => u q j) n‖ ^ 2))) :=
            mul_le_mul_of_nonneg_left (ENNReal.tsum_le_tsum hterm) zero_le
        _ = (ENNReal.ofReal B.volBox * ∑' n, _) +
            (ENNReal.ofReal B.volBox * ∑' n, _) +
            (ENNReal.ofReal B.volBox * ∑' n, _) := by
            rw [ENNReal.tsum_add, ENNReal.tsum_add, mul_add, mul_add]
        _ ≤ ENNReal.ofReal (gagliardoDir14 B.c shiftS u ^ 2) +
            ENNReal.ofReal (gagliardoDir14 B.c shiftQ u ^ 2) +
            ENNReal.ofReal (gagliardoDir14 B.c shiftEta u ^ 2) :=
            add_le_add (add_le_add hdir_s hdir_q) hdir_η
        _ = ENNReal.ofReal
              (gagliardoDir14 B.c shiftS u ^ 2 +
               gagliardoDir14 B.c shiftQ u ^ 2 +
               gagliardoDir14 B.c shiftEta u ^ 2) := by
            rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
              ← ENNReal.ofReal_add (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)]
    have hreal :
        K * ∫ p, ‖u p j - B.trigSum (B.freqSet N) (B.coeff3D (fun q => u q j)) p‖ ^ 2 ∂B.boxMeas ≤
          gagliardoDir14 B.c shiftS u ^ 2 +
          gagliardoDir14 B.c shiftQ u ^ 2 +
          gagliardoDir14 B.c shiftEta u ^ 2 := by
      rw [← ENNReal.ofReal_mul hK_pos.le] at hmul_le
      exact (ENNReal.ofReal_le_ofReal_iff
        (add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))).1 hmul_le
    calc ∫ p, ‖u p j - B.trigSum (B.freqSet N) (B.coeff3D (fun q => u q j)) p‖ ^ 2 ∂B.boxMeas
        = K⁻¹ * (K * ∫ p, ‖u p j - B.trigSum (B.freqSet N) (B.coeff3D (fun q => u q j)) p‖ ^ 2 ∂B.boxMeas) := by
          rw [← mul_assoc, inv_mul_cancel₀ hK_pos.ne', one_mul]
      _ ≤ K⁻¹ *
            (gagliardoDir14 B.c shiftS u ^ 2 +
             gagliardoDir14 B.c shiftQ u ^ 2 +
             gagliardoDir14 B.c shiftEta u ^ 2) :=
          mul_le_mul_of_nonneg_left hreal (inv_nonneg.2 hK_pos.le)
      _ = 6 * B.deltaStep ^ (-(3 / 2 : ℝ)) * N ^ (-(1 / 2 : ℝ)) *
            (gagliardoDir14 B.c shiftS u ^ 2 +
             gagliardoDir14 B.c shiftQ u ^ 2 +
             gagliardoDir14 B.c shiftEta u ^ 2) := by rw [hK_inv]
  rw [B.integral_merid_sub_projMerid_sq N hw.memLp_u]
  have h0 := h_coord 0
  have h1 := h_coord 1
  have hnorm_sq :
      gagliardoDir14 B.c shiftS u ^ 2 +
      gagliardoDir14 B.c shiftQ u ^ 2 +
      gagliardoDir14 B.c shiftEta u ^ 2 ≤ cellH14Norm B.c u ^ 2 := by
    unfold cellH14Norm
    have a0 := cellL2Norm_nonneg B.c u
    have a1 := gagliardoDir14_nonneg B.c shiftS u
    have a2 := gagliardoDir14_nonneg B.c shiftQ u
    have a3 := gagliardoDir14_nonneg B.c shiftEta u
    nlinarith
  have hcoef_nn : 0 ≤ 6 * B.deltaStep ^ (-(3 / 2 : ℝ)) * N ^ (-(1 / 2 : ℝ)) := by positivity
  calc (∫ p, ‖u p 0 - B.trigSum (B.freqSet N) (B.coeff3D (fun q => u q 0)) p‖ ^ 2 ∂B.boxMeas) +
         (∫ p, ‖u p 1 - B.trigSum (B.freqSet N) (B.coeff3D (fun q => u q 1)) p‖ ^ 2 ∂B.boxMeas)
      ≤ 2 * (6 * B.deltaStep ^ (-(3 / 2 : ℝ)) * N ^ (-(1 / 2 : ℝ)) *
          (gagliardoDir14 B.c shiftS u ^ 2 +
           gagliardoDir14 B.c shiftQ u ^ 2 +
           gagliardoDir14 B.c shiftEta u ^ 2)) := by linarith
    _ = 12 * B.deltaStep ^ (-(3 / 2 : ℝ)) * N ^ (-(1 / 2 : ℝ)) *
          (gagliardoDir14 B.c shiftS u ^ 2 +
           gagliardoDir14 B.c shiftQ u ^ 2 +
           gagliardoDir14 B.c shiftEta u ^ 2) := by ring
    _ ≤ 12 * B.deltaStep ^ (-(3 / 2 : ℝ)) * N ^ (-(1 / 2 : ℝ)) * cellH14Norm B.c u ^ 2 :=
        mul_le_mul_of_nonneg_left hnorm_sq (by positivity)

end BoxParams

end UnforcedLeray.Short.PartIIa.N06Aux
