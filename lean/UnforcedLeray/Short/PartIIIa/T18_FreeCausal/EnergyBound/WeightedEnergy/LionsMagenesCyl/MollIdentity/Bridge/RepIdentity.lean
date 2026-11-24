import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_2.Bridge_Sub
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollIdentity.Bridge.RepPair

/-!
# `lmRepIdentity`: the Bochner identity in `L²(cell; ℝ⁴)`

Source: `the November 2 reference manuscript` lines 3541-3552.  Each `χ ∈ LMH c`
lifts to a `ℂ²`-field `lmLift χ ∈ L²(cell)` with `lmReal (lmLift χ x) = χ x`; pairing with `χ`
is the real part of `LMIp (lmLift χ)`, so the real part of the tested identity of `LMWeakDeriv`
gives the identity of `∫ ψ' • U = -∫ ψ • U'` against every `χ`, hence in `LMH c`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open UnforcedLeray.BochnerTime
open scoped ENNReal ContDiff RealInnerProductSpace

namespace UnforcedLeray.Short.IIIa

/-- The `ℂ²` vector with the given real and imaginary parts. -/
def lmSp (v : EuclideanSpace ℝ (Fin 4)) : Fin 2 → ℂ :=
  ![(v 0 : ℂ) + (v 1 : ℂ) * Complex.I, (v 2 : ℂ) + (v 3 : ℂ) * Complex.I]

lemma lmReal_lmSp (v : EuclideanSpace ℝ (Fin 4)) : lmReal (lmSp v) = v := by
  ext i
  fin_cases i <;> simp [lmReal, lmSp]

/-- The `ℂ²`-field representing an element of `LMH c` (through the fixed representative). -/
def lmLift {c : ℝ} (χ : LMH c) : LMSpField := fun x => lmSp ((χ : ℝ × ℝ → EuclideanSpace ℝ (Fin 4)) x)

lemma lmLift_real {c : ℝ} (χ : LMH c) (x : ℝ × ℝ) :
    lmReal (lmLift χ x) = (χ : ℝ × ℝ → EuclideanSpace ℝ (Fin 4)) x := lmReal_lmSp _

lemma lmLift_measurable {c : ℝ} (χ : LMH c) (i : Fin 2) : Measurable fun x => lmLift χ x i := by
  have hm : Measurable (χ : ℝ × ℝ → EuclideanSpace ℝ (Fin 4)) := (Lp.stronglyMeasurable χ).measurable
  have h : ∀ j : Fin 4, Measurable fun x => (χ : ℝ × ℝ → EuclideanSpace ℝ (Fin 4)) x j :=
    fun j => (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℝ).continuous.measurable.comp hm
  fin_cases i
  · simp only [lmLift, lmSp]
    exact ((Complex.measurable_ofReal.comp (h 0)).add
      ((Complex.measurable_ofReal.comp (h 1)).mul measurable_const))
  · simp only [lmLift, lmSp]
    exact ((Complex.measurable_ofReal.comp (h 2)).add
      ((Complex.measurable_ofReal.comp (h 3)).mul measurable_const))

lemma lmLift_cellL2 {c : ℝ} (χ : LMH c) : LMCellL2 c (lmLift χ) := by
  have h : ∀ j : Fin 4, MemLp (fun x => (χ : ℝ × ℝ → EuclideanSpace ℝ (Fin 4)) x j) 2
      (volume.restrict (B0579.cell c)) := fun j =>
    (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℝ).comp_memLp' (Lp.memLp χ)
  intro i
  fin_cases i
  · simp only [lmLift, lmSp]
    exact (Complex.ofRealCLM.comp_memLp' (h 0)).add
      ((Complex.ofRealCLM.comp_memLp' (h 1)).mul_const _)
  · simp only [lmLift, lmSp]
    exact (Complex.ofRealCLM.comp_memLp' (h 2)).add
      ((Complex.ofRealCLM.comp_memLp' (h 3)).mul_const _)

lemma vnorm2_sq_eq (z : Fin 2 → ℂ) : vnorm2 z ^ 2 = ∑ i : Fin 2, ‖z i‖ ^ 2 := by
  unfold vnorm2
  rw [Real.sq_sqrt (by positivity)]

lemma integrable_vnorm2_sq {μ : Measure (ℝ × ℝ)} {f : ℝ × ℝ → Fin 2 → ℂ}
    (hf : ∀ i, MemLp (fun x => f x i) 2 μ) : Integrable (fun x => vnorm2 (f x) ^ 2) μ := by
  simp_rw [vnorm2_sq_eq]
  exact integrable_finsetSum _ fun i _ => (hf i).norm.integrable_sq

lemma norm_conj_sum_le (a b : Fin 2 → ℂ) :
    ‖∑ i : Fin 2, starRingEnd ℂ (a i) * b i‖ ≤ (vnorm2 a ^ 2 + vnorm2 b ^ 2) / 2 := by
  rw [vnorm2_sq_eq, vnorm2_sq_eq, ← Finset.sum_add_distrib, Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, Complex.norm_conj]
  nlinarith [sq_nonneg (‖a i‖ - ‖b i‖)]

/-- a.e. `s > 0`, the slice `u s` is componentwise `L²(cell)`. -/
lemma lm_ae_memLp (c : ℝ) (u : ℝ → LMSpField)
    (hm : ∀ i : Fin 2, Measurable fun p : ℝ × (ℝ × ℝ) => u p.1 p.2 i)
    (hl : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (fun i => u p.1 p.2 i) ^ 2) < ⊤) :
    ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ∀ i : Fin 2,
      MemLp (fun x => u s x i) 2 (volume.restrict (B0579.cell c)) := by
  filter_upwards [ae_Ioi_lt_top c u hm hl] with s hs i
  exact memLp_comp_of_lintegral (fun i => (hm i).comp measurable_prodMk_left) hs i

lemma lm_ae_inner {c : ℝ} {u : ℝ → LMSpField} {U : ℝ → LMH c} (hU : LMRep c u U)
    (hmem : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ∀ i : Fin 2,
      MemLp (fun x => u s x i) 2 (volume.restrict (B0579.cell c)))
    (χ : LMH c) :
    ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ⟪χ, U s⟫ = (LMIp c (lmLift χ) (u s)).re := by
  filter_upwards [hU, hmem] with s hr hm
  have h4 : (LMIp c (lmLift χ) (u s)).re =
      ∫ x in B0579.cell c, (∑ i : Fin 2, starRingEnd ℂ (lmLift χ x i) * u s x i).re := by
    unfold LMIp
    exact (integral_re (integrable_LMIp_integrand (lmLift_cellL2 χ) hm)).symm
  rw [h4, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hr] with x hx
  rw [hx, ← lmLift_real χ x, lmReal_inner]

lemma lm_integrableOn (c : ℝ) (u : ℝ → LMSpField)
    (hm : ∀ i : Fin 2, Measurable fun p : ℝ × (ℝ × ℝ) => u p.1 p.2 i)
    (hl : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (fun i => u p.1 p.2 i) ^ 2) < ⊤)
    (χ : LMH c) (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    IntegrableOn (fun s => LMIp c (lmLift χ) (u s)) (Ioo a b) := by
  have hsub : Ioo a b ⊆ Ioi (0 : ℝ) := fun s hs => lt_trans ha hs.1
  have hk := ae_restrict_of_ae_restrict_of_subset hsub (lm_ae_memLp c u hm hl)
  have hf : Measurable fun p : ℝ × (ℝ × ℝ) =>
      ∑ i : Fin 2, starRingEnd ℂ (lmLift χ p.2 i) * u p.1 p.2 i := by
    apply Finset.measurable_sum
    intro i _
    exact (Complex.continuous_conj.measurable.comp ((lmLift_measurable χ i).comp measurable_snd)).mul
      (hm i)
  have hmeas : AEStronglyMeasurable (fun s => LMIp c (lmLift χ) (u s))
      (volume.restrict (Ioo a b)) :=
    (hf.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (B0579.cell c))).aestronglyMeasurable
  have hχint : Integrable (fun x => vnorm2 (lmLift χ x) ^ 2) (volume.restrict (B0579.cell c)) :=
    integrable_vnorm2_sq (lmLift_cellL2 χ)
  set m : ℝ := ∫ x in B0579.cell c, vnorm2 (lmLift χ x) ^ 2 with hmdef
  have hA := integrable_sqNorm_Ioo c u hm a b hab (hl a b ha hab)
  refine Integrable.mono' (((integrable_const m).add hA).div_const 2) hmeas ?_
  filter_upwards [hk] with s hs
  have hui : Integrable (fun x => vnorm2 (u s x) ^ 2) (volume.restrict (B0579.cell c)) :=
    integrable_vnorm2_sq hs
  have hb : Integrable (fun x => (vnorm2 (lmLift χ x) ^ 2 + vnorm2 (u s x) ^ 2) / 2)
      (volume.restrict (B0579.cell c)) := (hχint.add hui).div_const 2
  have h1 := norm_integral_le_of_norm_le hb
    (Filter.Eventually.of_forall fun x => norm_conj_sum_le (lmLift χ x) (u s x))
  refine h1.trans (le_of_eq ?_)
  rw [integral_div, integral_add hχint hui]
  simp [hmdef]

lemma lm_re_identity {c : ℝ} {u u' : ℝ → LMSpField} (hW : LMWeakDeriv c u u') (χ : LMH c)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (hψt : tsupport ψ ⊆ Ioo a b) :
    ∫ t, deriv ψ t * (LMIp c (lmLift χ) (u t)).re =
      -∫ t, ψ t * (LMIp c (lmLift χ) (u' t)).re := by
  have hIoo : Ioo a b ⊆ Ioi (0 : ℝ) := fun s hs => lt_trans ha hs.1
  have hψI : tsupport ψ ⊆ Ioi (0 : ℝ) := hψt.trans hIoo
  have hid := hW.identity ψ hψ hψc hψI (lmLift χ) (lmLift_cellL2 χ)
  have h1 := integrable_deriv_smul hψ hψc hψt (lm_integrableOn c u hW.measU hW.l2U χ a b ha hab)
  have h2 := integrable_smul hψ hψc hψt (lm_integrableOn c u' hW.measU' hW.l2U' χ a b ha hab)
  have z1 : ∀ s, s ∉ Ioi (0 : ℝ) → ((deriv ψ s : ℝ) : ℂ) * LMIp c (lmLift χ) (u s) = 0 := by
    intro s hs
    have : deriv ψ s = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hs (hIoo (tsupport_deriv_subset_Ioo hψt h))
    simp [this]
  have z2 : ∀ s, s ∉ Ioi (0 : ℝ) → ((ψ s : ℝ) : ℂ) * LMIp c (lmLift χ) (u' s) = 0 := by
    intro s hs
    have : ψ s = 0 := image_eq_zero_of_notMem_tsupport fun h => hs (hψI h)
    simp [this]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero z1,
    setIntegral_eq_integral_of_forall_compl_eq_zero z2] at hid
  simp_rw [Complex.real_smul]  at h1 h2
  have h3 := congrArg Complex.re hid
  rw [Complex.neg_re] at h3
  have e1 := integral_re h1
  have e2 := integral_re h2
  simp only [RCLike.re_to_complex, Complex.re_ofReal_mul] at e1 e2
  rw [← e1, ← e2] at h3
  exact h3

theorem lmRepIdentity_proof : LMRepIdentity := by
  intro c _ u u' hW U U' hU hU' hint a b ha hab ψ hψ hψc hψt
  have hIoo : Ioo a b ⊆ Ioi (0 : ℝ) := fun s hs => lt_trans ha hs.1
  have hm1 := lm_ae_memLp c u hW.measU hW.l2U
  have hm2 := lm_ae_memLp c u' hW.measU' hW.l2U'
  have hL := integrable_deriv_smul hψ hψc hψt (hint a b ha hab).1
  have hR := integrable_smul hψ hψc hψt (hint a b ha hab).2
  apply ext_inner_left ℝ
  intro χ
  rw [inner_neg_right, ← integral_inner hL, ← integral_inner hR]
  simp_rw [real_inner_smul_right]
  have a1 := (ae_restrict_iff' measurableSet_Ioi).1 (lm_ae_inner hU hm1 χ)
  have a2 := (ae_restrict_iff' measurableSet_Ioi).1 (lm_ae_inner hU' hm2 χ)
  have c1 : ∫ t, deriv ψ t * ⟪χ, U t⟫ = ∫ t, deriv ψ t * (LMIp c (lmLift χ) (u t)).re := by
    refine integral_congr_ae ?_
    filter_upwards [a1] with t ht
    by_cases h : t ∈ Ioi (0 : ℝ)
    · rw [ht h]
    · have : deriv ψ t = 0 :=
        image_eq_zero_of_notMem_tsupport fun h' => h (hIoo (tsupport_deriv_subset_Ioo hψt h'))
      simp [this]
  have c2 : ∫ t, ψ t * ⟪χ, U' t⟫ = ∫ t, ψ t * (LMIp c (lmLift χ) (u' t)).re := by
    refine integral_congr_ae ?_
    filter_upwards [a2] with t ht
    by_cases h : t ∈ Ioi (0 : ℝ)
    · rw [ht h]
    · have : ψ t = 0 := image_eq_zero_of_notMem_tsupport fun h' => h (hIoo (hψt h'))
      simp [this]
  rw [c1, c2]
  exact lm_re_identity hW χ a b ha hab ψ hψ hψc hψt

theorem lmRepIdentity : UnforcedLeray.Short.IIIa.LMRepIdentity := lmRepIdentity_proof

end UnforcedLeray.Short.IIIa

#print axioms UnforcedLeray.Short.IIIa.lmRepIdentity
