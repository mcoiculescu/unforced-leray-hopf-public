import UnforcedLeray.Lib.PlanarSectorsB.Sector
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Sector sums `⊕ₙ Aₙ` on `L²_M` (INF12 target P7, part 1)


§5, Level P, target **P7** (adapted from NonUniqueEuler `SectorSpace/{DirectSum,Decomposition}`,

P/Infra/SectorSpace/DirectSum.lean}`, rebuilt here on `L²_M` with the Hilbert-sum isometry of
Mathlib's `OrthogonalFamily.linearIsometry` instead of NonUniqueEuler's Sobolev tuples).

Manuscript (`paper/main.tex`): the weighted space `L²_M = H^0_M` (lines 653–660,
`eq:st18-t00003`, unit `B0008`) splits into the angular sectors `w(r)e^{inϑ}` (line 1356, unit
`B0078`; lines 1390–1400, unit `B0083`); decision D7 builds the generator sector by sector.

Main declarations (namespace `UnforcedLeray.Planar`):
* `secProf M n : L2w M →L[ℂ] ProfL2 M` (`f ↦ f_n`, the profile of `P_n f`) and
  `secEmb M n : ProfL2 M →ₗᵢ[ℂ] L2w M` (`w ↦ w(r)e^{inϑ}`), with `secEmb_secProf`
  (`= P_n`), `secProf_secEmb` (`= δ_{mn}`), `norm_secProf`, `hasSum_norm_sq_secProf`
  (Parseval), `orthogonalFamily_secEmb`, `eq_of_secProf` (a function is determined by its
  sector profiles);
* `sectorSum A hA hC : L2w M →L[ℂ] L2w M` for uniformly bounded `Aₙ` (`‖Aₙ‖ ≤ C`):
  `sectorSum A f = ∑' n, (Aₙ f_n)(r)e^{inϑ}` (`hasSum_sectorSum`), `secProf_sectorSum`,
  `norm_sectorSum_le`, `sectorSum_comp`, `sectorSum_one`;
* `massCLM_secEmb`: a sector `n ≠ 0` has zero mass (rotation invariance of `∫`), and
  `massCLM_eq_secEmb_zero`: the mass only sees sector `0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Planar

open UnforcedLeray.Planar.NUE

/-! ### Profiles and embeddings of the sectors -/

/-- The range of `P_n`, the angular sector `n` of `L²_M`. -/
abbrev SecRange (M : ℝ) (n : ℤ) : Submodule ℂ (L2w M) :=
  LinearMap.range (sectorProjW M n : L2w M →ₗ[ℂ] L2w M)

/-- The sector profile `f ↦ f_n`, `P_n f = f_n(r) e^{inϑ}`. -/
def secProf (M : ℝ) (n : ℤ) : L2w M →L[ℂ] ProfL2 M :=
  (sectorIso M n).toLinearIsometry.toContinuousLinearMap.comp
    ((sectorProjW M n).codRestrict (SecRange M n) fun f => ⟨f, rfl⟩)

/-- The sector embedding `w ↦ w(r) e^{inϑ}`. -/
def secEmb (M : ℝ) (n : ℤ) : ProfL2 M →ₗᵢ[ℂ] L2w M :=
  (SecRange M n).subtypeₗᵢ.comp (sectorIso M n).symm.toLinearIsometry

theorem secEmb_apply (M : ℝ) (n : ℤ) (h : ProfL2 M) :
    secEmb M n h = ((sectorIso M n).symm h : L2w M) := rfl

theorem secEmb_mem (M : ℝ) (n : ℤ) (h : ProfL2 M) : secEmb M n h ∈ SecRange M n :=
  ((sectorIso M n).symm h).2

theorem coeFn_secEmb (M : ℝ) (n : ℤ) (h : ProfL2 M) :
    ⇑(secEmb M n h) =ᵐ[wMeasure M] Ang.ofProfile n h :=
  coeFn_sectorIso_symm M n h

theorem secEmb_secProf (M : ℝ) (n : ℤ) (f : L2w M) :
    secEmb M n (secProf M n f) = sectorProjW M n f := by
  show (((sectorIso M n).symm ((sectorIso M n) _) : SecRange M n) : L2w M) = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

theorem norm_secProf (M : ℝ) (n : ℤ) (f : L2w M) : ‖secProf M n f‖ = ‖sectorProjW M n f‖ := by
  rw [← (secEmb M n).norm_map, secEmb_secProf]

theorem sectorProjW_secEmb (M : ℝ) (m n : ℤ) (h : ProfL2 M) :
    sectorProjW M m (secEmb M n h) = if m = n then secEmb M n h else 0 := by
  obtain ⟨g, hg⟩ := secEmb_mem M n h
  have hg' : sectorProjW M n g = secEmb M n h := hg
  rw [← hg']
  have := congrArg (fun T => T g) (sectorProjW_comp (M := M) m n)
  simp only [ContinuousLinearMap.comp_apply] at this
  rw [this]
  split_ifs <;> rfl

theorem secProf_eq_zero_of_proj {M : ℝ} {m : ℤ} {g : L2w M} (h : sectorProjW M m g = 0) :
    secProf M m g = 0 := by
  apply (secEmb M m).injective
  rw [secEmb_secProf, h, map_zero]

theorem secProf_secEmb (M : ℝ) (m n : ℤ) (h : ProfL2 M) :
    secProf M m (secEmb M n h) = if n = m then h else 0 := by
  split_ifs with hnm
  · subst hnm
    apply (secEmb M n).injective
    rw [secEmb_secProf, sectorProjW_secEmb, if_pos rfl]
  · apply secProf_eq_zero_of_proj
    rw [sectorProjW_secEmb, if_neg (Ne.symm hnm)]

theorem secProf_secEmb_self (M : ℝ) (n : ℤ) (h : ProfL2 M) : secProf M n (secEmb M n h) = h := by
  rw [secProf_secEmb, if_pos rfl]

/-- **Parseval**: `‖f‖² = ∑ₙ ‖f_n‖²_{ProfL2 M}`. -/
theorem hasSum_norm_sq_secProf {M : ℝ} (f : L2w M) :
    HasSum (fun n : ℤ => ‖secProf M n f‖ ^ 2) (‖f‖ ^ 2) := by
  simp_rw [norm_secProf]
  exact hasSum_norm_sq_sectorProjW f

theorem hasSum_secEmb_secProf {M : ℝ} (f : L2w M) :
    HasSum (fun n : ℤ => secEmb M n (secProf M n f)) f := by
  simp_rw [secEmb_secProf]
  exact hasSum_sectorProjW f

/-- A function of `L²_M` is determined by its sector profiles. -/
theorem eq_of_secProf {M : ℝ} {f g : L2w M} (h : ∀ n, secProf M n f = secProf M n g) : f = g := by
  have hf := hasSum_secEmb_secProf f
  have hg := hasSum_secEmb_secProf g
  simp_rw [h] at hf
  exact hf.unique hg

/-- The sector embeddings form an orthogonal family. -/
theorem orthogonalFamily_secEmb (M : ℝ) :
    OrthogonalFamily ℂ (fun _ : ℤ => ProfL2 M) (secEmb M) := by
  intro i j hij v w
  have hv : secEmb M i v = sectorProjW M i (secEmb M i v) := by
    rw [sectorProjW_secEmb, if_pos rfl]
  have hw : secEmb M j w = sectorProjW M j (secEmb M j w) := by
    rw [sectorProjW_secEmb, if_pos rfl]
  rw [hv, hw]
  exact inner_sectorProjW_of_ne hij _ _

/-! ### Sector sums -/

section SectorSum

variable {M : ℝ} (A : ℤ → ProfL2 M →L[ℂ] ProfL2 M) {C : ℝ}

theorem summable_norm_sq_secFam (hA : ∀ n, ‖A n‖ ≤ C) (f : L2w M) :
    Summable fun n => ‖A n (secProf M n f)‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((hasSum_norm_sq_secProf f).summable.mul_left (C ^ 2))
  have h1 := (A n).le_of_opNorm_le (hA n) (secProf M n f)
  calc ‖A n (secProf M n f)‖ ^ 2 ≤ (C * ‖secProf M n f‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = C ^ 2 * ‖secProf M n f‖ ^ 2 := by ring

theorem memℓp_secFam (hA : ∀ n, ‖A n‖ ≤ C) (f : L2w M) :
    Memℓp (fun n : ℤ => A n (secProf M n f)) 2 := by
  apply memℓp_gen
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  simp_rw [h2, Real.rpow_two]
  exact summable_norm_sq_secFam A hA f

/-- `f ↦ (Aₙ f_n)ₙ ∈ ℓ²(ℤ; ProfL2 M)`. -/
def secLpLin (hA : ∀ n, ‖A n‖ ≤ C) : L2w M →ₗ[ℂ] lp (fun _ : ℤ => ProfL2 M) 2 where
  toFun f := ⟨fun n => A n (secProf M n f), memℓp_secFam A hA f⟩
  map_add' f g := by
    apply lp.ext
    funext n
    show A n (secProf M n (f + g)) = A n (secProf M n f) + A n (secProf M n g)
    rw [map_add, map_add]
  map_smul' c f := by
    apply lp.ext
    funext n
    simp [lp.coeFn_smul]

theorem secLpLin_apply (hA : ∀ n, ‖A n‖ ≤ C) (f : L2w M) (n : ℤ) :
    (secLpLin A hA f : ∀ _ : ℤ, ProfL2 M) n = A n (secProf M n f) := rfl

theorem norm_secLpLin_le (hA : ∀ n, ‖A n‖ ≤ C) (hC : 0 ≤ C) (f : L2w M) :
    ‖secLpLin A hA f‖ ≤ C * ‖f‖ := by
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  refine lp.norm_le_of_tsum_le (by norm_num) (by positivity) ?_
  simp_rw [h2, Real.rpow_two, secLpLin_apply]
  calc ∑' n, ‖A n (secProf M n f)‖ ^ 2 ≤ ∑' n, C ^ 2 * ‖secProf M n f‖ ^ 2 := by
        refine Summable.tsum_le_tsum (fun n => ?_) (summable_norm_sq_secFam A hA f)
          ((hasSum_norm_sq_secProf f).summable.mul_left _)
        have h1 := (A n).le_of_opNorm_le (hA n) (secProf M n f)
        calc ‖A n (secProf M n f)‖ ^ 2 ≤ (C * ‖secProf M n f‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) h1 2
          _ = C ^ 2 * ‖secProf M n f‖ ^ 2 := by ring
    _ = C ^ 2 * ‖f‖ ^ 2 := by rw [tsum_mul_left, (hasSum_norm_sq_secProf f).tsum_eq]
    _ = (C * ‖f‖) ^ 2 := by ring

/-- **The sector sum** `⊕ₙ Aₙ : f ↦ ∑' n, (Aₙ f_n)(r) e^{inϑ}` of uniformly bounded sector
operators (NonUniqueEuler `sectorSum`, rebuilt on `L²_M`). -/
def sectorSum (hA : ∀ n, ‖A n‖ ≤ C) (hC : 0 ≤ C) : L2w M →L[ℂ] L2w M :=
  (orthogonalFamily_secEmb M).linearIsometry.toContinuousLinearMap.comp
    ((secLpLin A hA).mkContinuous C (norm_secLpLin_le A hA hC))

theorem hasSum_sectorSum (hA : ∀ n, ‖A n‖ ≤ C) (hC : 0 ≤ C) (f : L2w M) :
    HasSum (fun n => secEmb M n (A n (secProf M n f))) (sectorSum A hA hC f) :=
  (orthogonalFamily_secEmb M).hasSum_linearIsometry (secLpLin A hA f)

theorem sectorSum_apply (hA : ∀ n, ‖A n‖ ≤ C) (hC : 0 ≤ C) (f : L2w M) :
    sectorSum A hA hC f = ∑' n, secEmb M n (A n (secProf M n f)) :=
  (hasSum_sectorSum A hA hC f).tsum_eq.symm

/-- The sector profiles of `⊕ₙ Aₙ f` are `Aₙ f_n`. -/
theorem secProf_sectorSum (hA : ∀ n, ‖A n‖ ≤ C) (hC : 0 ≤ C) (f : L2w M) (m : ℤ) :
    secProf M m (sectorSum A hA hC f) = A m (secProf M m f) := by
  have h := (hasSum_sectorSum A hA hC f).mapL (secProf M m)
  simp only [secProf_secEmb] at h
  have h' : HasSum (fun n => if n = m then A n (secProf M n f) else 0) (A m (secProf M m f)) := by
    have := hasSum_single (f := fun n => if n = m then A n (secProf M n f) else 0) m
      (fun n hn => if_neg hn)
    simpa using this
  exact h.unique h'

theorem norm_sectorSum_le (hA : ∀ n, ‖A n‖ ≤ C) (hC : 0 ≤ C) : ‖sectorSum A hA hC‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun f => ?_
  rw [sectorSum, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometry.norm_map, LinearMap.mkContinuous_apply]
  exact norm_secLpLin_le A hA hC f

/-- `‖f‖² = ∑ₙ ‖f_n‖²` gives the norm of a sector sum. -/
theorem norm_sq_eq_tsum (f : L2w M) : ‖f‖ ^ 2 = ∑' n, ‖secProf M n f‖ ^ 2 :=
  (hasSum_norm_sq_secProf f).tsum_eq.symm

end SectorSum

theorem sectorSum_comp {M : ℝ} (A B : ℤ → ProfL2 M →L[ℂ] ProfL2 M) {C D : ℝ}
    (hA : ∀ n, ‖A n‖ ≤ C) (hC : 0 ≤ C) (hB : ∀ n, ‖B n‖ ≤ D) (hD : 0 ≤ D)
    (hAB : ∀ n, ‖A n ∘L B n‖ ≤ C * D) :
    sectorSum A hA hC ∘L sectorSum B hB hD = sectorSum (fun n => A n ∘L B n) hAB (mul_nonneg hC hD) := by
  ext1 f
  apply eq_of_secProf
  intro n
  rw [ContinuousLinearMap.comp_apply, secProf_sectorSum, secProf_sectorSum, secProf_sectorSum,
    ContinuousLinearMap.comp_apply]

theorem sectorSum_one {M : ℝ} (h1 : ∀ n : ℤ, ‖(1 : ProfL2 M →L[ℂ] ProfL2 M)‖ ≤ 1) :
    sectorSum (M := M) (fun _ => 1) h1 zero_le_one = 1 := by
  ext1 f
  apply eq_of_secProf
  intro n
  rw [secProf_sectorSum, ContinuousLinearMap.one_apply, ContinuousLinearMap.one_apply]

/-! ### The mass sees only sector `0` -/

theorem angPhase_rot (n : ℤ) (θ : ℝ) (y : ℂ) :
    Ang.angPhase n (rot θ y) = Complex.exp ((n : ℂ) * θ * Complex.I) * Ang.angPhase n y := by
  unfold Ang.angPhase
  rw [Polar.norm_rot, rot, mul_div_assoc, mul_zpow, ← Complex.exp_int_mul, mul_assoc]

/-- A sector-`n` function has zero integral for `n ≠ 0` (rotation invariance of `∫`). -/
theorem integral_ofProfile_eq_zero {n : ℤ} (hn : n ≠ 0) (h : ℝ → ℂ) :
    ∫ y, Ang.ofProfile n h y = 0 := by
  set θ : ℝ := π / n with hθ
  have hrot : ∫ y, Ang.ofProfile n h (rot θ y) = ∫ y, Ang.ofProfile n h y := by
    have he : MeasurableEmbedding (rot θ) := by
      rw [Polar.rot_eq_rotation]
      exact (rotation (Circle.exp θ)).toHomeomorph.measurableEmbedding
    exact (Polar.measurePreserving_rot θ).integral_comp he _
  have hexp : Complex.exp ((n : ℂ) * θ * Complex.I) = -1 := by
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have : (n : ℂ) * (θ : ℂ) = π := by
      rw [hθ]
      push_cast
      field_simp
    rw [this, Complex.exp_pi_mul_I]
  have hpt : ∀ y, Ang.ofProfile n h (rot θ y) = -Ang.ofProfile n h y := by
    intro y
    rw [Ang.ofProfile, Ang.ofProfile, Polar.norm_rot, angPhase_rot, hexp]
    ring
  simp_rw [hpt, integral_neg] at hrot
  have h2 : (2 : ℂ) * ∫ y, Ang.ofProfile n h y = 0 := by linear_combination -hrot
  simpa using h2

theorem massCLM_secEmb {M : ℝ} (hM : 1 < M) {n : ℤ} (hn : n ≠ 0) (h : ProfL2 M) :
    massCLM hM (secEmb M n h) = 0 := by
  rw [massCLM_apply]
  rw [integral_congr_ae ((volume_ac M).ae_le (coeFn_secEmb M n h))]
  exact integral_ofProfile_eq_zero hn _

/-- The mass of `f ∈ L²_M` is the mass of its sector-`0` part. -/
theorem massCLM_eq_secEmb_zero {M : ℝ} (hM : 1 < M) (f : L2w M) :
    massCLM hM f = massCLM hM (secEmb M 0 (secProf M 0 f)) := by
  have h := (hasSum_secEmb_secProf f).mapL (massCLM hM)
  have h' := hasSum_single (f := fun n => massCLM hM (secEmb M n (secProf M n f))) (0 : ℤ)
    (fun n hn => massCLM_secEmb hM hn _)
  exact h.unique h'

end UnforcedLeray.Planar
