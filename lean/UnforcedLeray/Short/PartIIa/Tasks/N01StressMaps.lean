import UnforcedLeray.Short.PartIIa.Sub.N01.Assembly
import UnforcedLeray.Short.PartIIa.Sub.N01.PhaseLift
import UnforcedLeray.Short.PartIIa.Sub.N01.SemigroupConj
import UnforcedLeray.Short.PartIIa.Tasks.N01StressMaps.LerayConj
import UnforcedLeray.Short.PartIIa.Sub.N01.DivScale
import UnforcedLeray.Short.PartIIa.Sub.N01.CartLiftRows
import UnforcedLeray.Short.PartIIa.Sub.N01.CartLiftNorm
import UnforcedLeray.Short.PartIIa.Sub.N01.Completion
import UnforcedLeray.Short.PartIIa.Sub.N01.FlatColumnC
import UnforcedLeray.Short.PartIIa.Sub.N01.FlatVelTransport
import UnforcedLeray.Short.PartIIa.Sub.N01.FlatBlkTransport

/-!
# `PartII-a:N01`: `NearStressMapExists`

Source of record: `the November 2 reference manuscript`,
lines 1675-1689 (`near:free-energy` and the flat age-energy estimate), with 1339-1372, 1546-1567,
1625-1632 (the Cartesian foundation and the transported stress map).

Note: `Sub.N01.LerayConjOrth` and `Sub.N01.ReIm` share helper lemma names (`fderiv_slice` and
`divEps_lin` etc.) with `HeatInt.SlabDivZero.Fundamental` (imported by `FlatColumnC`) and
`Completion`. To avoid environment name collisions without touching leaf files, `phaseLerayConj`
is imported from `Tasks.N01StressMaps.LerayConj` (with `private theorem fderiv_slice'`) and
`tensorTestReIm` is proved here using `Completion.divEps_lin`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile)
open UnforcedLeray.Short.PartIIIb.Concrete (Chart Ten3)
open UnforcedLeray.Short.PartIIIb.NearInst (tv4 ten3Of symRZ)

private def tenOfVals (a : Fin 4 → ℝ) : Ten3 := ten3Of !![a 0, 0, a 1; 0, a 3, 0; a 1, 0, a 2]

private def reTen (x : TensorVal) : Ten3 := tenOfVals (fun j => (x j).re)

private def imTen (x : TensorVal) : Ten3 := tenOfVals (fun j => (x j).im)

private def reVec (x : TensorVal) : TensorVal := WithLp.toLp 2 fun j => (((x j).re : ℝ) : ℂ)

private def imVec (x : TensorVal) : TensorVal := WithLp.toLp 2 fun j => (((x j).im : ℝ) : ℂ)

private theorem tv4_tenOfVals (a : Fin 4 → ℝ) :
    tv4 (tenOfVals a) = WithLp.toLp 2 fun j => ((a j : ℝ) : ℂ) := by
  ext j
  fin_cases j <;> simp [tv4, tenOfVals, symRZ, ten3Of]

private theorem tv4_reTen (x : TensorVal) : tv4 (reTen x) = reVec x := by
  rw [reTen, tv4_tenOfVals]
  rfl

private theorem tv4_imTen (x : TensorVal) : tv4 (imTen x) = imVec x := by
  rw [imTen, tv4_tenOfVals]
  rfl

private theorem reVec_add_imVec (x : TensorVal) : x = reVec x + Complex.I • imVec x := by
  ext j
  simp [reVec, imVec]
  rw [mul_comm]
  exact (Complex.re_add_im (x j)).symm

private theorem reVec_zero : reVec 0 = 0 := by
  ext j
  simp [reVec]

private theorem reVec_norm_le (x : TensorVal) : ‖reVec x‖ ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro j _
  have h1 : ‖(((x j).re : ℝ) : ℂ)‖ ≤ ‖x j‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact Complex.abs_re_le_norm _
  have h0 : 0 ≤ ‖(((x j).re : ℝ) : ℂ)‖ := norm_nonneg _
  show ‖(((x j).re : ℝ) : ℂ)‖ ^ 2 ≤ ‖x j‖ ^ 2
  exact pow_le_pow_left₀ h0 h1 2

private theorem imVec_norm_le (x : TensorVal) : ‖imVec x‖ ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro j _
  have h1 : ‖(((x j).im : ℝ) : ℂ)‖ ≤ ‖x j‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact Complex.abs_im_le_norm _
  have h0 : 0 ≤ ‖(((x j).im : ℝ) : ℂ)‖ := norm_nonneg _
  show ‖(((x j).im : ℝ) : ℂ)‖ ^ 2 ≤ ‖x j‖ ^ 2
  exact pow_le_pow_left₀ h0 h1 2

private theorem imVec_zero : imVec 0 = 0 := by
  ext j
  simp [imVec]

private theorem contDiff_reVec {M : Profile → TensorVal} (hM : ContDiff ℝ ∞ M) :
    ContDiff ℝ ∞ (fun p => reVec (M p)) := by
  unfold reVec
  apply PiLp.contDiff_toLp.comp
  apply contDiff_pi.2
  intro j
  have hj : ContDiff ℝ ∞ (fun p => M p j) :=
    (contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (i := j)).comp hM
  exact Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp hj)

private theorem contDiff_imVec {M : Profile → TensorVal} (hM : ContDiff ℝ ∞ M) :
    ContDiff ℝ ∞ (fun p => imVec (M p)) := by
  unfold imVec
  apply PiLp.contDiff_toLp.comp
  apply contDiff_pi.2
  intro j
  have hj : ContDiff ℝ ∞ (fun p => M p j) :=
    (contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (i := j)).comp hM
  exact Complex.ofRealCLM.contDiff.comp (Complex.imCLM.contDiff.comp hj)

private theorem divEps_split (f g M : Profile → TensorVal) (hM : ∀ p, M p = f p + Complex.I • g p)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (ε : ℝ) (p : Profile) :
    divEps ε M p = divEps ε f p + Complex.I • divEps ε g p := by
  have hMe : M = fun q => f q + Complex.I • g q := funext hM
  subst hMe
  exact divEps_lin f g hf hg Complex.I ε p

theorem tensorTestReIm : TensorTestReIm := by
  intro c hc M hM
  have hsplit : ∀ p, M p = reVec (M p) + Complex.I • imVec (M p) :=
    fun p => reVec_add_imVec (M p)
  refine ⟨fun p => reTen (M p), fun p => imTen (M p), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [tv4_reTen]
    refine ⟨contDiff_reVec hM.smooth, fun p => congrArg reVec (hM.periodic p), ?_⟩
    obtain ⟨s0, s1, L, hs0, hb⟩ := hM.band
    exact ⟨s0, s1, L, hs0, fun p hne => hb p (fun h0 => hne (by rw [h0, reVec_zero]))⟩
  · simp only [tv4_imTen]
    refine ⟨contDiff_imVec hM.smooth, fun p => congrArg imVec (hM.periodic p), ?_⟩
    obtain ⟨s0, s1, L, hs0, hb⟩ := hM.band
    exact ⟨s0, s1, L, hs0, fun p hne => hb p (fun h0 => hne (by rw [h0, imVec_zero]))⟩
  · intro p
    rw [tv4_reTen, tv4_imTen]
    exact hsplit p
  · intro p
    rw [tv4_reTen]
    exact reVec_norm_le (M p)
  · intro p
    rw [tv4_imTen]
    exact imVec_norm_le (M p)
  · intro ε p
    simp only [tv4_reTen, tv4_imTen]
    exact divEps_split (fun q => reVec (M q)) (fun q => imVec (M q)) M hsplit
      ((contDiff_reVec hM.smooth).differentiable (by simp))
      ((contDiff_imVec hM.smooth).differentiable (by simp)) ε p

end UnforcedLeray.Short.PartIIa.N01

namespace UnforcedLeray.Short.PartIIa

theorem nearStressMapExists : NearStressMapExists :=
  N01.nearStressMapExists_of_leaves N01.phaseLiftExists N01.phaseSemigroupConj
    N01.phaseLerayConj N01.phaseDivScale N01.cartLiftRows N01.cartLiftNorm
    N01.tensorTestReIm N01.stressCompletion N01.flatColumnC N01.flatVelTransport
    N01.flatBlkTransport

end UnforcedLeray.Short.PartIIa
