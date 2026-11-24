import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Asm.StreamCutAlg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Coeff
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Leibniz
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T9

/-!
# `StreamCutHess`: second derivatives of the stream cutoff `𝒞_y Z`

Helper for `HessianBound` (`PartIII-b:C/rep/8/1/2`), source
`the November 2 reference manuscript`
lines 4178-4186, 5404-5413, 5438-5448.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open GeomXAsm

/-- The bound of `StreamCutHessStmt` with a given constant `C₀`. -/
def StreamCutHessWith (χ : ℝ → ℝ) (C₀ : ℝ) : Prop :=
  ∀ (ν R : ℝ) (Z : ℝ → Space → Space) (τ r z : ℝ), 0 < ν → 0 < R → 0 < r →
    ν * (R ^ 2 / r ^ 2) ≤ 1 →
    ContDiffOn ℝ 2 (Z τ) (youngOpen ν R) →
    (∀ r' z', R * Real.sqrt (5 * ν / 6) < r' →
      HasDerivAt (fun r'' => outPrim Z τ r'' z') (r' * Z τ !₂[r', 0, z'] 2) r' ∧
        HasDerivAt (fun z'' => outPrim Z τ r' z'') (-(r' * Z τ !₂[r', 0, z'] 0)) z') →
    hessSize (wardStreamCut ν R χ Z τ) (hpt r z) ≤
      C₀ * (hessSize (Z τ) (hpt r z) + r⁻¹ * gradSize (Z τ) (hpt r z) +
        r⁻¹ ^ 2 * ‖Z τ (hpt r z)‖ + r⁻¹ ^ 4 * |outPrim Z τ r z|)

/-- **Second derivatives of the stream cutoff** (source 4178-4186). -/
def StreamCutHessStmt : Prop :=
  ∀ χ : ℝ → ℝ, IsStreamCutoff χ → ∃ C₀ : ℝ, 0 ≤ C₀ ∧ StreamCutHessWith χ C₀

namespace StreamCutHessAux

open GeomXAsm.StreamCutAlgAux

lemma stream_cutoff_const3 (χ : ℝ → ℝ) (hχ : IsStreamCutoff χ) :
    Differentiable ℝ χ ∧ Differentiable ℝ (deriv χ) ∧ Differentiable ℝ (deriv (deriv χ)) ∧
    ∃ M : ℝ, 1 ≤ M ∧ (∀ t, |deriv χ t| ≤ M) ∧ (∀ t, |deriv (deriv χ) t| ≤ M) ∧
      (∀ t, |deriv (deriv (deriv χ)) t| ≤ M) := by
  obtain ⟨d0, d1, d2, c1, c2, c3⟩ := tcc_smooth χ hχ
  have hv1 : ∀ t, t ∉ Icc (4 / 5 : ℝ) 1 → deriv χ t = 0 := by
    intro t ht
    rw [mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with ht | ht
    · have : χ =ᶠ[𝓝 t] fun _ => (1 : ℝ) :=
        Filter.mem_of_superset (Iio_mem_nhds ht) fun s hs => hχ.one s (le_of_lt hs)
      rw [this.deriv_eq]; simp
    · have : χ =ᶠ[𝓝 t] fun _ => (0 : ℝ) :=
        Filter.mem_of_superset (Ioi_mem_nhds ht) fun s hs => hχ.zero s (le_of_lt hs)
      rw [this.deriv_eq]; simp
  have hv2 : ∀ t, t ∉ Icc (4 / 5 : ℝ) 1 → deriv (deriv χ) t = 0 := by
    intro t ht
    have : deriv χ =ᶠ[𝓝 t] fun _ => (0 : ℝ) :=
      Filter.mem_of_superset (isClosed_Icc.isOpen_compl.mem_nhds ht) fun s hs => hv1 s hs
    rw [this.deriv_eq]; simp
  have hv3 : ∀ t, t ∉ Icc (4 / 5 : ℝ) 1 → deriv (deriv (deriv χ)) t = 0 := by
    intro t ht
    have : deriv (deriv χ) =ᶠ[𝓝 t] fun _ => (0 : ℝ) :=
      Filter.mem_of_superset (isClosed_Icc.isOpen_compl.mem_nhds ht) fun s hs => hv2 s hs
    rw [this.deriv_eq]; simp
  obtain ⟨M₁, hM₁, hb₁⟩ := bdd_of_vanish c1 hv1
  obtain ⟨M₂, hM₂, hb₂⟩ := bdd_of_vanish c2 hv2
  obtain ⟨M₃, hM₃, hb₃⟩ := bdd_of_vanish c3 hv3
  refine ⟨d0, d1, d2, M₁ + M₂ + M₃ + 1, by linarith,
    fun t => (hb₁ t).trans (by linarith),
    fun t => (hb₂ t).trans (by linarith),
    fun t => (hb₃ t).trans (by linarith)⟩

lemma tc_radial_bounds {χ : ℝ → ℝ} (hχ : IsStreamCutoff χ)
    (d0 : Differentiable ℝ χ) (d1 : Differentiable ℝ (deriv χ))
    (d2 : Differentiable ℝ (deriv (deriv χ))) {M : ℝ} (hM : 1 ≤ M)
    (hb₁ : ∀ t, |deriv χ t| ≤ M) (hb₂ : ∀ t, |deriv (deriv χ) t| ≤ M)
    (hb₃ : ∀ t, |deriv (deriv (deriv χ)) t| ≤ M)
    {ν R r : ℝ} (hν : 0 < ν) (hr : 0 < r) (ht1 : ν * (R ^ 2 / r ^ 2) ≤ 1) :
    |tcC0 ν R χ r| ≤ 1 ∧
    |deriv (tcC0 ν R χ) r| ≤ 2 * M * r⁻¹ ∧
    |deriv (deriv (tcC0 ν R χ)) r| ≤ 10 * M * r⁻¹ ^ 2 ∧
    |tcF0 ν R χ r| ≤ 2 * M * r⁻¹ ^ 2 ∧
    |deriv (tcF0 ν R χ) r| ≤ 12 * M * r⁻¹ ^ 3 ∧
    |deriv (deriv (tcF0 ν R χ)) r| ≤ 92 * M * r⁻¹ ^ 4 := by
  set t := ν * (R ^ 2 / r ^ 2) with ht_def
  have ht0 : 0 ≤ t := by positivity
  have hM0 : 0 ≤ M := by linarith
  have ht2 : t ^ 2 ≤ 1 := pow_le_one₀ ht0 ht1
  have ht3 : t ^ 3 ≤ 1 := pow_le_one₀ ht0 ht1
  have p1 : |t * deriv χ t| ≤ M := by
    rw [abs_mul, abs_of_nonneg ht0]
    exact (mul_le_mul ht1 (hb₁ t) (abs_nonneg _) zero_le_one).trans_eq (one_mul M)
  have p2 : |t ^ 2 * deriv (deriv χ) t| ≤ M := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg t)]
    exact (mul_le_mul ht2 (hb₂ t) (abs_nonneg _) zero_le_one).trans_eq (one_mul M)
  have p3 : |t ^ 3 * deriv (deriv (deriv χ)) t| ≤ M := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg ht0 3)]
    exact (mul_le_mul ht3 (hb₃ t) (abs_nonneg _) zero_le_one).trans_eq (one_mul M)
  obtain ⟨p1l, p1u⟩ := abs_le.1 p1
  obtain ⟨p2l, p2u⟩ := abs_le.1 p2
  obtain ⟨p3l, p3u⟩ := abs_le.1 p3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold tcC0
    rw [abs_of_nonneg (hχ.range _).1]
    exact (hχ.range _).2
  · rw [tcc_deriv_C0 χ d0 ν R r hr.ne', ← ht_def, div_eq_mul_inv, abs_mul,
      abs_of_pos (inv_pos.2 hr)]
    refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 hr.le)
    rw [abs_le]; constructor <;> linarith
  · rw [tcc_deriv_deriv_C0 χ d0 d1 ν R r hr, ← ht_def, div_eq_mul_inv, ← inv_pow, abs_mul,
      abs_of_pos (pow_pos (inv_pos.2 hr) 2)]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (inv_nonneg.2 hr.le) 2)
    rw [abs_le]; constructor <;> linarith
  · rw [tcc_tcF0_eq χ ν R r, ← ht_def, div_eq_mul_inv, ← inv_pow, abs_mul,
      abs_of_pos (pow_pos (inv_pos.2 hr) 2)]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (inv_nonneg.2 hr.le) 2)
    rw [abs_le]; constructor <;> linarith
  · rw [tcc_deriv_F0 χ d1 ν R r hr, ← ht_def, show t * t = t ^ 2 by ring,
      div_eq_mul_inv, ← inv_pow, abs_mul, abs_of_pos (pow_pos (inv_pos.2 hr) 3)]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (inv_nonneg.2 hr.le) 3)
    rw [abs_le]; constructor <;> linarith
  · rw [tcc_deriv_deriv_F0 χ d1 d2 ν R r hr, ← ht_def, div_eq_mul_inv, ← inv_pow, abs_mul,
      abs_of_pos (pow_pos (inv_pos.2 hr) 4)]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (inv_nonneg.2 hr.le) 4)
    rw [abs_le]; constructor <;> linarith

/-- First and second partials of `y' ↦ g (ϱ y')` at `y = hpt r z`. -/
lemma comp_varrho_partials {g : ℝ → ℝ} {r : ℝ} (hr : 0 < r) (z : ℝ)
    (hg : ContDiffAt ℝ 2 g r) :
    (∀ l : Fin 3, |fderiv ℝ (fun y' => g (ϱ y')) (hpt r z) (coordinateVector l)| ≤ |deriv g r|) ∧
    (∀ j l : Fin 3,
      |fderiv ℝ (fun y' => fderiv ℝ (fun y'' => g (ϱ y'')) y' (coordinateVector l))
        (hpt r z) (coordinateVector j)| ≤ |deriv (deriv g) r| + r⁻¹ * |deriv g r|) := by
  set y := hpt r z
  have hyr : ϱ y = r := varrho_hpt hr z
  have hy0 : y 0 = r := rfl
  have hy1 : y 1 = 0 := rfl
  have h : 0 < ϱ y := by rw [hyr]; exact hr
  have hg' : ContDiffAt ℝ 2 g (ϱ y) := by rw [hyr]; exact hg
  have hgd : DifferentiableAt ℝ g (ϱ y) := hg'.differentiableAt (by norm_num)
  have hdg : DifferentiableAt ℝ (deriv g) (ϱ y) := by
    have h1 : DifferentiableAt ℝ (fderiv ℝ g) (ϱ y) :=
      (hg'.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have : deriv g = fun s => fderiv ℝ g s 1 := rfl
    rw [this]
    exact h1.clm_apply (differentiableAt_const _)
  refine ⟨?_, ?_⟩
  · intro l
    rw [tcle_fderiv_comp h hgd, hyr, hy0, hy1]
    fin_cases l <;> simp [coordinateVector, hr.ne']
  · set κ : ℝ → ℝ := fun s => deriv g s / s with hκ
    have hκd : HasDerivAt κ (deriv (deriv g) (ϱ y) / ϱ y - deriv g (ϱ y) / ϱ y ^ 2) (ϱ y) := by
      have := hdg.hasDerivAt.div (hasDerivAt_id (ϱ y)) h.ne'
      have e : (deriv (deriv g) (ϱ y) * id (ϱ y) - deriv g (ϱ y) * 1) / id (ϱ y) ^ 2 =
          deriv (deriv g) (ϱ y) / ϱ y - deriv g (ϱ y) / ϱ y ^ 2 := by
        simp only [id]; field_simp
      rw [e] at this
      exact this
    have hev : ∀ᶠ y' in nhds y, 0 < ϱ y' ∧ DifferentiableAt ℝ g (ϱ y') := by
      have e1 : ∀ᶠ y' in nhds y, 0 < ϱ y' := continuous_ϱ.continuousAt.eventually (lt_mem_nhds h)
      have e2 : ∀ᶠ y' in nhds y, DifferentiableAt ℝ g (ϱ y') := by
        have : ∀ᶠ s in nhds (ϱ y), DifferentiableAt ℝ g s :=
          (hg'.eventually (by simp)).mono fun s hs => hs.differentiableAt (by norm_num)
        exact continuous_ϱ.continuousAt.eventually this
      exact e1.and e2
    have hk : DifferentiableAt ℝ (fun y' => κ (ϱ y')) y :=
      (tcle_hasFDeriv_comp (g := κ) h hκd.differentiableAt).differentiableAt
    have hl : ∀ l : Fin 3, (fun y' => fderiv ℝ (fun y'' => g (ϱ y'')) y' (coordinateVector l)) =ᶠ[nhds y]
        fun y' => if l = 0 then y' 0 * κ (ϱ y') else if l = 1 then y' 1 * κ (ϱ y') else 0 := by
      intro l
      filter_upwards [hev] with y' ⟨hy', hgy'⟩
      rw [tcle_fderiv_comp hy' hgy']
      fin_cases l
      · simp [coordinateVector, hκ]; field_simp
      · simp [coordinateVector, hκ]; field_simp
      · simp [coordinateVector]
    intro j l
    rw [(hl l).fderiv_eq]
    have hd := hκd.deriv
    have hnn1 : 0 ≤ |deriv (deriv g) r| := abs_nonneg _
    have hnn2 : 0 ≤ r⁻¹ * |deriv g r| := by positivity
    rcases (by fin_cases l <;> decide : l = 0 ∨ l = 1 ∨ l = 2) with rfl | rfl | rfl
    · simp only [↓reduceIte]
      rw [tcl_fd_mul 0 hk (coordinateVector j),
        tcle_fderiv_comp (g := κ) h hκd.differentiableAt (coordinateVector j),
        hd, hyr, hy0, hy1, hκ]
      rcases (by fin_cases j <;> decide : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
      · simp only [coordinateVector, PiLp.single_apply, ↓reduceIte, zero_mul, add_zero, mul_one]
        have heq : r * ((deriv (deriv g) r / r - deriv g r / r ^ 2) * (r / r)) +
            deriv g r / r = deriv (deriv g) r := by
          field_simp; ring
        rw [heq]; linarith
      · simp [coordinateVector]; positivity
      · simp [coordinateVector]; positivity
    · simp only [show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte]
      rw [tcl_fd_mul 1 hk (coordinateVector j),
        tcle_fderiv_comp (g := κ) h hκd.differentiableAt (coordinateVector j),
        hd, hyr, hy0, hy1, hκ]
      rcases (by fin_cases j <;> decide : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
      · simp [coordinateVector]; positivity
      · simp only [coordinateVector, PiLp.single_apply, ↓reduceIte, zero_mul, zero_add,
          mul_one, div_eq_inv_mul, abs_mul, abs_of_pos (inv_pos.2 hr)]
        linarith
      · simp [coordinateVector]; positivity
    · simp only [show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte,
        fderiv_const_apply, zero_apply, abs_zero]
      exact add_nonneg hnn1 hnn2

/-- Additivity of `physPd2` at a point. -/
lemma physPd2_add_at {f g : Space → Space} {y : Space} (hf : ContDiffAt ℝ 2 f y)
    (hg : ContDiffAt ℝ 2 g y) (j l : Fin 3) :
    physPd2 (fun y' => f y' + g y') j l y = physPd2 f j l y + physPd2 g j l y := by
  unfold physPd2 physPd
  have hev : ∀ᶠ y' in nhds y, DifferentiableAt ℝ f y' ∧ DifferentiableAt ℝ g y' := by
    filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with y' h1 h2
    exact ⟨h1.differentiableAt (by norm_num), h2.differentiableAt (by norm_num)⟩
  have heq : (fun y' => fderiv ℝ (fun y' => f y' + g y') y' (coordinateVector l)) =ᶠ[nhds y]
      fun y' => fderiv ℝ f y' (coordinateVector l) + fderiv ℝ g y' (coordinateVector l) := by
    filter_upwards [hev] with y' ⟨h1, h2⟩
    rw [fderiv_fun_add h1 h2]
    rfl
  rw [heq.fderiv_eq, fderiv_fun_add (tcle_diff_fderiv_apply hf _) (tcle_diff_fderiv_apply hg _)]
  rfl

/-- Leibniz rule for `physPd2 (fun y' => φ y' • V y') j l y`. -/
lemma physPd2_smul_at {φ : Space → ℝ} {V : Space → Space} {y : Space}
    (hφ : ContDiffAt ℝ 2 φ y) (hV : ContDiffAt ℝ 2 V y) (j l : Fin 3) :
    physPd2 (fun y' => φ y' • V y') j l y =
      (fderiv ℝ (fun y' => fderiv ℝ φ y' (coordinateVector l)) y (coordinateVector j)) • V y +
      fderiv ℝ φ y (coordinateVector l) • physPd V j y +
      fderiv ℝ φ y (coordinateVector j) • physPd V l y +
      φ y • physPd2 V j l y := by
  have hφd : DifferentiableAt ℝ φ y := hφ.differentiableAt (by norm_num)
  have hVd : DifferentiableAt ℝ V y := hV.differentiableAt (by norm_num)
  unfold physPd2 physPd
  have hev : ∀ᶠ y' in nhds y, DifferentiableAt ℝ φ y' ∧ DifferentiableAt ℝ V y' := by
    filter_upwards [hφ.eventually (by simp), hV.eventually (by simp)] with y' h1 h2
    exact ⟨h1.differentiableAt (by norm_num), h2.differentiableAt (by norm_num)⟩
  have heq : (fun y' => fderiv ℝ (fun y' => φ y' • V y') y' (coordinateVector l)) =ᶠ[nhds y]
      fun y' => fderiv ℝ φ y' (coordinateVector l) • V y' +
        φ y' • fderiv ℝ V y' (coordinateVector l) := by
    filter_upwards [hev] with y' ⟨h1, h2⟩
    have h : HasFDerivAt (fun y' => φ y' • V y') _ y' := h1.hasFDerivAt.smul h2.hasFDerivAt
    rw [h.fderiv]
    simp [add_comm]
  rw [heq.fderiv_eq]
  have hA := tcle_diff_fderiv_apply hφ (coordinateVector l)
  have hD := tcle_diff_fderiv_apply hV (coordinateVector l)
  have h1 : HasFDerivAt (fun y' => fderiv ℝ φ y' (coordinateVector l) • V y') _ y :=
    hA.hasFDerivAt.smul hVd.hasFDerivAt
  have h2 : HasFDerivAt (fun y' => φ y' • fderiv ℝ V y' (coordinateVector l)) _ y :=
    hφd.hasFDerivAt.smul hD.hasFDerivAt
  rw [(h1.fun_add h2).fderiv]
  simp
  module

/-- Norm bound for `physPd2 (fun y' => φ y' • V y') j l y`. -/
lemma norm_physPd2_smul_le {φ : Space → ℝ} {V : Space → Space} {y : Space}
    (hφ : ContDiffAt ℝ 2 φ y) (hV : ContDiffAt ℝ 2 V y) {A₀ A₁ A₂ : ℝ}
    (h0 : |φ y| ≤ A₀) (h1 : ∀ k : Fin 3, |fderiv ℝ φ y (coordinateVector k)| ≤ A₁)
    (h2 : ∀ j l : Fin 3,
      |fderiv ℝ (fun y' => fderiv ℝ φ y' (coordinateVector l)) y (coordinateVector j)| ≤ A₂)
    (j l : Fin 3) :
    ‖physPd2 (fun y' => φ y' • V y') j l y‖ ≤
      A₂ * ‖V y‖ + A₁ * (‖physPd V j y‖ + ‖physPd V l y‖) + A₀ * ‖physPd2 V j l y‖ := by
  rw [physPd2_smul_at hφ hV j l]
  have b1 : ‖(fderiv ℝ (fun y' => fderiv ℝ φ y' (coordinateVector l)) y (coordinateVector j)) • V y‖ ≤
      A₂ * ‖V y‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (h2 j l) (norm_nonneg _)
  have b2 : ‖fderiv ℝ φ y (coordinateVector l) • physPd V j y‖ ≤ A₁ * ‖physPd V j y‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (h1 l) (norm_nonneg _)
  have b3 : ‖fderiv ℝ φ y (coordinateVector j) • physPd V l y‖ ≤ A₁ * ‖physPd V l y‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (h1 j) (norm_nonneg _)
  have b4 : ‖φ y • physPd2 V j l y‖ ≤ A₀ * ‖physPd2 V j l y‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right h0 (norm_nonneg _)
  calc ‖_ + _ + _ + _‖
      ≤ ‖(fderiv ℝ (fun y' => fderiv ℝ φ y' (coordinateVector l)) y (coordinateVector j)) • V y‖ +
        ‖fderiv ℝ φ y (coordinateVector l) • physPd V j y‖ +
        ‖fderiv ℝ φ y (coordinateVector j) • physPd V l y‖ +
        ‖φ y • physPd2 V j l y‖ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
          refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
          exact norm_add_le _ _
    _ ≤ A₂ * ‖V y‖ + A₁ * ‖physPd V j y‖ + A₁ * ‖physPd V l y‖ + A₀ * ‖physPd2 V j l y‖ := by
          gcongr
    _ = A₂ * ‖V y‖ + A₁ * (‖physPd V j y‖ + ‖physPd V l y‖) + A₀ * ‖physPd2 V j l y‖ := by ring

lemma hpt_mem_youngOpen {ν R r : ℝ} (hν : 0 < ν) (hR : 0 < R) (hr : 0 < r)
    (ht1 : ν * (R ^ 2 / r ^ 2) ≤ 1) (z : ℝ) :
    hpt r z ∈ youngOpen ν R := by
  show R * Real.sqrt (5 * ν / 6) < ϱ (hpt r z)
  rw [varrho_hpt hr z]
  have h1 : R ^ 2 * (5 * ν / 6) < r ^ 2 := by
    have h2 : ν * R ^ 2 ≤ r ^ 2 := by
      have := (mul_le_mul_of_nonneg_right ht1 (sq_nonneg r))
      rwa [one_mul, ← mul_div_assoc, div_mul_cancel₀ _ (pow_ne_zero 2 hr.ne')] at this
    nlinarith [mul_pos hν (pow_pos hR 2)]
  have hsq : (R * Real.sqrt (5 * ν / 6)) ^ 2 < r ^ 2 := by
    rwa [mul_pow, Real.sq_sqrt (by positivity)]
  exact lt_of_pow_lt_pow_left₀ 2 hr.le hsq

lemma meridPt_eq_lin (y : Space) :
    meridPt y = ϱ y • (coordinateVector 0 : Space) + y 2 • (coordinateVector 2 : Space) := by
  ext i
  fin_cases i <;> simp [meridPt, coordinateVector]

lemma meridPt_hpt {r : ℝ} (hr : 0 < r) (z : ℝ) : meridPt (hpt r z) = hpt r z := by
  rw [meridPt_eq_lin, varrho_hpt hr z]
  ext i
  fin_cases i <;> simp [hpt, coordinateVector]

lemma hasFDerivAt_meridPt {r : ℝ} (hr : 0 < r) (z : ℝ) :
    HasFDerivAt meridPt
      ((ϱD (hpt r z)).smulRight (coordinateVector 0) +
        (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).smulRight (coordinateVector 2))
      (hpt r z) := by
  have heq : meridPt = fun y : Space =>
      ϱ y • (coordinateVector 0 : Space) + y 2 • (coordinateVector 2 : Space) :=
    funext meridPt_eq_lin
  rw [heq]
  exact ((hasFDerivAt_ϱ (hpt_not_axis hr z)).smul_const _).add
    (((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt).smul_const _)

lemma fderiv_Z_meridPt_le {Z : Space → Space} {r : ℝ} (hr : 0 < r) (z : ℝ)
    (hZ : DifferentiableAt ℝ Z (hpt r z)) (k j : Fin 3) :
    |fderiv ℝ (fun y' : Space => Z (meridPt y') k) (hpt r z) (coordinateVector j)| ≤
      gradSize Z (hpt r z) := by
  set y := hpt r z
  have hyr : ϱ y = r := varrho_hpt hr z
  have hmer : meridPt y = y := meridPt_hpt hr z
  have hZk : HasFDerivAt (fun y' : Space => Z y' k)
      ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).comp (fderiv ℝ Z y)) (meridPt y) := by
    rw [hmer]
    exact (EuclideanSpace.proj k : Space →L[ℝ] ℝ).hasFDerivAt.comp y hZ.hasFDerivAt
  have hmer_fd : HasFDerivAt meridPt
      ((ϱD y).smulRight (coordinateVector 0) +
        (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).smulRight (coordinateVector 2)) y :=
    hasFDerivAt_meridPt hr z
  have hcomp := hZk.comp y hmer_fd
  have hfd : fderiv ℝ (fun y' : Space => Z (meridPt y') k) y = _ := hcomp.fderiv
  rw [hfd]
  simp only [ContinuousLinearMap.comp_apply, add_apply,
    ContinuousLinearMap.smulRight_apply]
  have h0 : ‖physPd Z 0 y‖ ≤ gradSize Z y :=
    Finset.single_le_sum (fun i _ => norm_nonneg (physPd Z i y)) (Finset.mem_univ 0)
  have h2 : ‖physPd Z 2 y‖ ≤ gradSize Z y :=
    Finset.single_le_sum (fun i _ => norm_nonneg (physPd Z i y)) (Finset.mem_univ 2)
  have hgrad0 : 0 ≤ gradSize Z y := Finset.sum_nonneg fun _ _ => norm_nonneg _
  rcases (by fin_cases j <;> decide : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
  · have hρ0 : ϱD y (coordinateVector 0) = 1 := by
      rw [ϱD_apply, hyr]; simp [y, hpt, coordinateVector, hr.ne']
    have he2 : (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ) (coordinateVector 0) = 0 := by
      change (coordinateVector 0 : Space) 2 = 0; simp [coordinateVector]
    rw [hρ0, he2, one_smul, zero_smul, add_zero]
    exact (PiLp.norm_apply_le (physPd Z 0 y) k).trans h0
  · have hρ1 : ϱD y (coordinateVector 1) = 0 := by
      rw [ϱD_apply, hyr]; simp [y, hpt, coordinateVector]
    have he2 : (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ) (coordinateVector 1) = 0 := by
      change (coordinateVector 1 : Space) 2 = 0; simp [coordinateVector]
    rw [hρ1, he2, zero_smul, zero_smul, add_zero, map_zero, map_zero, abs_zero]
    exact hgrad0
  · have hρ2 : ϱD y (coordinateVector 2) = 0 := by
      rw [ϱD_apply, hyr]; simp [y, hpt, coordinateVector]
    have he2 : (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ) (coordinateVector 2) = 1 := by
      change (coordinateVector 2 : Space) 2 = 1; simp [coordinateVector]
    rw [hρ2, he2, zero_smul, one_smul, zero_add]
    exact (PiLp.norm_apply_le (physPd Z 2 y) k).trans h2

/-- First and second partials of `psiFld Z τ` on the young region at `y = hpt r z`. -/
lemma psiFld_partials {ν R : ℝ} (hν : 0 < ν) (hR : 0 < R) {Z : ℝ → Space → Space} {τ r z : ℝ}
    (hr : 0 < r) (ht1 : ν * (R ^ 2 / r ^ 2) ≤ 1)
    (hZ : ContDiffOn ℝ 2 (Z τ) (youngOpen ν R))
    (hdr : ∀ r' z', R * Real.sqrt (5 * ν / 6) < r' →
      HasDerivAt (fun r'' => outPrim Z τ r'' z') (r' * Z τ !₂[r', 0, z'] 2) r' ∧
        HasDerivAt (fun z'' => outPrim Z τ r' z'') (-(r' * Z τ !₂[r', 0, z'] 0)) z') :
    ContDiffAt ℝ 2 (psiFld Z τ) (hpt r z) ∧
    ‖psiFld Z τ (hpt r z)‖ = |outPrim Z τ r z| ∧
    (∀ l : Fin 3, ‖physPd (psiFld Z τ) l (hpt r z)‖ ≤ r * ‖Z τ (hpt r z)‖) ∧
    (∀ j l : Fin 3,
      ‖physPd2 (psiFld Z τ) j l (hpt r z)‖ ≤ ‖Z τ (hpt r z)‖ + r * gradSize (Z τ) (hpt r z)) := by
  set y := hpt r z
  have hyU : y ∈ youngOpen ν R := hpt_mem_youngOpen hν hR hr ht1 z
  have hU : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
  have hΨc : ContDiffOn ℝ 2 (fun y' : Space => outPrim Z τ (ϱ y') (y' 2)) (youngOpen ν R) :=
    t9_outPrim_c2 hν hR hZ hdr
  have hΨat : ContDiffAt ℝ 2 (fun y' : Space => outPrim Z τ (ϱ y') (y' 2)) y :=
    hΨc.contDiffAt (hU.mem_nhds hyU)
  have hpsiat : ContDiffAt ℝ 2 (psiFld Z τ) y := hΨat.smul contDiffAt_const
  -- Fréchet derivative of Ψ̃ on youngOpen ν R
  have hS : IsOpen {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} :=
    isOpen_lt continuous_const continuous_fst
  have hm : ContDiff ℝ 2 (fun p : ℝ × ℝ => (!₂[p.1, 0, p.2] : Space)) :=
    PiLp.contDiff_toLp.comp (contDiff_pi.2 fun i => by fin_cases i <;> simp <;> fun_prop)
  have hmaps : Set.MapsTo (fun p : ℝ × ℝ => (!₂[p.1, 0, p.2] : Space))
      {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} (youngOpen ν R) := by
    intro p hp
    have hp' : R * Real.sqrt (5 * ν / 6) < p.1 := hp
    show R * Real.sqrt (5 * ν / 6) < ϱ (!₂[p.1, 0, p.2] : Space)
    have hϱ : ϱ (!₂[p.1, 0, p.2] : Space) = |p.1| := by simp [ϱ, Real.sqrt_sq_eq_abs]
    rw [hϱ]; exact lt_of_lt_of_le hp' (le_abs_self _)
  have hPc : ContinuousOn (fun p : ℝ × ℝ => p.1 * Z τ !₂[p.1, 0, p.2] 2)
      {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} :=
    continuousOn_fst.mul (((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).continuous).comp_continuousOn
      (hZ.continuousOn.comp hm.continuous.continuousOn hmaps))
  have hQc : ContinuousOn (fun p : ℝ × ℝ => -(p.1 * Z τ !₂[p.1, 0, p.2] 0))
      {p : ℝ × ℝ | R * Real.sqrt (5 * ν / 6) < p.1} :=
    (continuousOn_fst.mul (((EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).continuous).comp_continuousOn
      (hZ.continuousOn.comp hm.continuous.continuousOn hmaps))).neg
  have hΨ_fd : ∀ y' ∈ youngOpen ν R, ∀ l : Fin 3,
      fderiv ℝ (fun y'' : Space => outPrim Z τ (ϱ y'') (y'' 2)) y' (coordinateVector l) =
        if l = 0 then y' 0 * Z τ (meridPt y') 2
        else if l = 1 then y' 1 * Z τ (meridPt y') 2
        else -(ϱ y' * Z τ (meridPt y') 0) := by
    intro y' hy' l
    have hρ' : 0 < ϱ y' := lt_of_lt_of_le (t9_thr_pos hν hR) hy'.le
    have hD := t9_hasFDerivAt_of_partials _ hS (fun p : ℝ × ℝ => outPrim Z τ p.1 p.2)
      (fun p : ℝ × ℝ => p.1 * Z τ !₂[p.1, 0, p.2] 2)
      (fun p : ℝ × ℝ => -(p.1 * Z τ !₂[p.1, 0, p.2] 0))
      hPc hQc (fun p hp => (hdr p.1 p.2 hp).1) (fun p hp => (hdr p.1 p.2 hp).2)
      (ϱ y', y' 2) hy'
    have hG := (hasFDerivAt_ϱ (t9_not_axis hν hR hy')).prodMk
      (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt
    have hcomp := hD.comp y' hG
    rw [show (fun y'' : Space => outPrim Z τ (ϱ y'') (y'' 2)) =
        (fun p : ℝ × ℝ => outPrim Z τ p.1 p.2) ∘
          (fun x : Space => (ϱ x, (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ) x)) from rfl,
      hcomp.fderiv]
    simp only [ContinuousLinearMap.comp_apply, add_apply,
      smul_apply, ContinuousLinearMap.prod_apply, smul_eq_mul, ϱD_apply]
    unfold meridPt
    have := hρ'.ne'
    fin_cases l
    · simp [coordinateVector]; field_simp
    · simp [coordinateVector]; field_simp
    · simp [coordinateVector]
  have hyr : ϱ y = r := varrho_hpt hr z
  have hmer : meridPt y = y := meridPt_hpt hr z
  have hZd : DifferentiableAt ℝ (Z τ) y :=
    (hZ.contDiffAt (hU.mem_nhds hyU)).differentiableAt (by norm_num)
  refine ⟨hpsiat, ?_, ?_, ?_⟩
  · unfold psiFld
    rw [norm_smul, norm_e2, mul_one, hyr, Real.norm_eq_abs]; rfl
  · intro l
    unfold physPd psiFld
    rw [fderiv_smul_const (hΨat.differentiableAt (by norm_num)), ContinuousLinearMap.smulRight_apply,
      norm_smul, norm_e2, mul_one, Real.norm_eq_abs, hΨ_fd y hyU l, hmer, hyr]
    have h0 : |Z τ y 0| ≤ ‖Z τ y‖ := by simpa using PiLp.norm_apply_le (Z τ y) 0
    have h2 : |Z τ y 2| ≤ ‖Z τ y‖ := by simpa using PiLp.norm_apply_le (Z τ y) 2
    have hy0 : y 0 = r := rfl
    have hy1 : y 1 = 0 := rfl
    rcases (by fin_cases l <;> decide : l = 0 ∨ l = 1 ∨ l = 2) with rfl | rfl | rfl
    · simp only [↓reduceIte, hy0, abs_mul, abs_of_pos hr]; gcongr
    · simp only [show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte, hy1, zero_mul, abs_zero]; positivity
    · simp only [show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte,
        abs_neg, abs_mul, abs_of_pos hr]; gcongr
  · intro j l
    unfold physPd2 physPd psiFld
    have hev : (fun y' => fderiv ℝ (fun y'' => outPrim Z τ (ϱ y'') (y'' 2) •
        (coordinateVector 2 : Space)) y' (coordinateVector l)) =ᶠ[nhds y]
        fun y' => (if l = 0 then y' 0 * Z τ (meridPt y') 2
          else if l = 1 then y' 1 * Z τ (meridPt y') 2
          else -(ϱ y' * Z τ (meridPt y') 0)) • (coordinateVector 2 : Space) := by
      filter_upwards [hU.mem_nhds hyU] with y' hy'
      have hd' : DifferentiableAt ℝ (fun y'' : Space => outPrim Z τ (ϱ y'') (y'' 2)) y' :=
        (hΨc.contDiffAt (hU.mem_nhds hy')).differentiableAt (by norm_num)
      rw [fderiv_smul_const hd', ContinuousLinearMap.smulRight_apply, hΨ_fd y' hy' l]
    rw [hev.fderiv_eq]
    have hdZ2 : DifferentiableAt ℝ (fun y' : Space => Z τ (meridPt y') 2) y := by
      have hZk : HasFDerivAt (fun y' : Space => Z τ y' 2)
          ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).comp (fderiv ℝ (Z τ) y)) (meridPt y) := by
        rw [hmer]
        exact (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt.comp y hZd.hasFDerivAt
      exact (hZk.comp y (hasFDerivAt_meridPt hr z)).differentiableAt
    have hdZ0 : DifferentiableAt ℝ (fun y' : Space => Z τ (meridPt y') 0) y := by
      have hZk : HasFDerivAt (fun y' : Space => Z τ y' 0)
          ((EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).comp (fderiv ℝ (Z τ) y)) (meridPt y) := by
        rw [hmer]
        exact (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt.comp y hZd.hasFDerivAt
      exact (hZk.comp y (hasFDerivAt_meridPt hr z)).differentiableAt
    have h0 : |Z τ y 0| ≤ ‖Z τ y‖ := by simpa using PiLp.norm_apply_le (Z τ y) 0
    have h2 : |Z τ y 2| ≤ ‖Z τ y‖ := by simpa using PiLp.norm_apply_le (Z τ y) 2
    have hZ0 : 0 ≤ ‖Z τ y‖ := norm_nonneg _
    have hG0 : 0 ≤ gradSize (Z τ) y := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hc : ∀ k : Fin 3, |(coordinateVector j : Space) k| ≤ 1 := fun k => by
      fin_cases j <;> fin_cases k <;> simp [coordinateVector]
    rcases (by fin_cases l <;> decide : l = 0 ∨ l = 1 ∨ l = 2) with rfl | rfl | rfl
    · simp only [↓reduceIte]
      have hd : DifferentiableAt ℝ (fun y' : Space => y' 0 * Z τ (meridPt y') 2) y :=
        ((EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).differentiableAt).mul hdZ2
      rw [fderiv_smul_const hd, ContinuousLinearMap.smulRight_apply, norm_smul, norm_e2, mul_one,
        Real.norm_eq_abs, tcl_fd_mul 0 hdZ2 (coordinateVector j), hmer]
      have hb := fderiv_Z_meridPt_le hr z hZd 2 j
      have hy0 : y 0 = r := rfl
      rw [hy0]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_pos hr]
      calc r * |fderiv ℝ (fun y' => Z τ (meridPt y') 2) y (coordinateVector j)| +
            |Z τ y 2| * |(coordinateVector j : Space) 0|
          ≤ r * gradSize (Z τ) y + ‖Z τ y‖ * 1 := by
            gcongr
            exact hc 0
        _ = ‖Z τ y‖ + r * gradSize (Z τ) y := by ring
    · simp only [show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte]
      have hd : DifferentiableAt ℝ (fun y' : Space => y' 1 * Z τ (meridPt y') 2) y :=
        ((EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).differentiableAt).mul hdZ2
      rw [fderiv_smul_const hd, ContinuousLinearMap.smulRight_apply, norm_smul, norm_e2, mul_one,
        Real.norm_eq_abs, tcl_fd_mul 1 hdZ2 (coordinateVector j), hmer]
      have hy1 : y 1 = 0 := rfl
      rw [hy1, zero_mul, zero_add, abs_mul]
      calc |Z τ y 2| * |(coordinateVector j : Space) 1|
          ≤ ‖Z τ y‖ * 1 := by gcongr; exact hc 1
        _ ≤ ‖Z τ y‖ + r * gradSize (Z τ) y := by linarith [mul_nonneg hr.le hG0]
    · simp only [show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte]
      have hdρ : DifferentiableAt ℝ ϱ y := (hasFDerivAt_ϱ (hpt_not_axis hr z)).differentiableAt
      have hd : DifferentiableAt ℝ (fun y' : Space => -(ϱ y' * Z τ (meridPt y') 0)) y :=
        (hdρ.mul hdZ0).neg
      rw [fderiv_smul_const hd, ContinuousLinearMap.smulRight_apply, norm_smul, norm_e2, mul_one,
        Real.norm_eq_abs]
      have hprod : HasFDerivAt (fun y' : Space => -(ϱ y' * Z τ (meridPt y') 0))
          (-((ϱ y • fderiv ℝ (fun y' : Space => Z τ (meridPt y') 0) y +
            Z τ (meridPt y) 0 • ϱD y))) y :=
        ((hasFDerivAt_ϱ (hpt_not_axis hr z)).mul hdZ0.hasFDerivAt).neg
      rw [hprod.fderiv, neg_apply, add_apply,
        smul_apply, smul_apply, smul_eq_mul, smul_eq_mul,
        abs_neg, hyr, hmer]
      have hb := fderiv_Z_meridPt_le hr z hZd 0 j
      have hρb : |ϱD y (coordinateVector j)| ≤ 1 := by
        rw [ϱD_apply, hyr]; fin_cases j <;> simp [y, hpt, coordinateVector, hr.ne']
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_pos hr]
      calc r * |fderiv ℝ (fun y' => Z τ (meridPt y') 0) y (coordinateVector j)| +
            |Z τ y 0| * |ϱD y (coordinateVector j)|
          ≤ r * gradSize (Z τ) y + ‖Z τ y‖ * 1 := by gcongr
        _ = ‖Z τ y‖ + r * gradSize (Z τ) y := by ring

end StreamCutHessAux

open StreamCutHessAux GeomXAsm.StreamCutAlgAux in
/-- **`StreamCutHessStmt`** (source 4178-4186): second-derivative bound for `wardStreamCut`. -/
theorem streamCutHess : StreamCutHessStmt := by
  intro χ hχ
  obtain ⟨d0, d1, d2, M, hM, hb₁, hb₂, hb₃⟩ := stream_cutoff_const3 χ hχ
  refine ⟨1200 * M, by positivity, ?_⟩
  intro ν R Z τ r z hν hR hr ht1 hZ hdr
  set y := hpt r z
  have hyr : ϱ y = r := varrho_hpt hr z
  have hyU : y ∈ youngOpen ν R := hpt_mem_youngOpen hν hR hr ht1 z
  have hU : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
  have hZat : ContDiffAt ℝ 2 (Z τ) y := hZ.contDiffAt (hU.mem_nhds hyU)
  obtain ⟨hpsiat, hpsi0, hpsi1, hpsi2⟩ := psiFld_partials hν hR hr ht1 hZ hdr
  have hcc : ContDiffAt ℝ 2 (tcC0 ν R χ) r := tcle_c0_smooth hχ ν R hr.ne'
  have hff : ContDiffAt ℝ 2 (tcF0 ν R χ) r := tcle_f0_smooth hχ ν R hr.ne'
  have hϱc : ContDiffAt ℝ 2 ϱ y :=
    contDiffOn_ϱ.contDiffAt (isOpen_compl_axis.mem_nhds (hpt_not_axis hr z))
  have hC : ContDiffAt ℝ 2 (fun y' => tcC0 ν R χ (ϱ y')) y := by
    have hcc' : ContDiffAt ℝ 2 (tcC0 ν R χ) (ϱ y) := by rw [hyr]; exact hcc
    exact hcc'.comp y hϱc
  have hF : ContDiffAt ℝ 2 (fun y' => tcF0 ν R χ (ϱ y')) y := by
    have hff' : ContDiffAt ℝ 2 (tcF0 ν R χ) (ϱ y) := by rw [hyr]; exact hff
    exact hff'.comp y hϱc
  obtain ⟨bC0, bC1, bC2, bF0, bF1, bF2⟩ :=
    tc_radial_bounds hχ d0 d1 d2 hM hb₁ hb₂ hb₃ hν hr ht1
  obtain ⟨cC1, cC2⟩ := comp_varrho_partials hr z hcc
  obtain ⟨cF1, cF2⟩ := comp_varrho_partials hr z hff
  have hWf : wardStreamCut ν R χ Z τ = fun y' =>
      tcC0 ν R χ (ϱ y') • Z τ y' + tcF0 ν R χ (ϱ y') • psiFld Z τ y' :=
    funext fun y' => tcle_wsc_eq ν R χ Z τ y'
  set i := r⁻¹
  have hi0 : 0 < i := inv_pos.2 hr
  have hri : r * i = 1 := mul_inv_cancel₀ hr.ne'
  have hM0 : 0 ≤ M := by linarith
  set H := hessSize (Z τ) y
  set G := gradSize (Z τ) y
  set Zn := ‖Z τ y‖
  set P := |outPrim Z τ r z|
  have hH0 : 0 ≤ H := hessSize_nonneg _ _
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hZ0 : 0 ≤ Zn := norm_nonneg _
  have hP0 : 0 ≤ P := abs_nonneg _
  -- Entrywise bound for each (j, l)
  have hjl : ∀ j l : Fin 3,
      ‖physPd2 (wardStreamCut ν R χ Z τ) j l y‖ ≤
        M * ‖physPd2 (Z τ) j l y‖ +
        2 * M * i * (‖physPd (Z τ) j y‖ + ‖physPd (Z τ) l y‖) +
        (2 * M * i * G + 40 * M * i ^ 2 * Zn + 104 * M * i ^ 4 * P) := by
    intro j l
    rw [hWf, physPd2_add_at (f := fun y' => tcC0 ν R χ (ϱ y') • Z τ y')
      (g := fun y' => tcF0 ν R χ (ϱ y') • psiFld Z τ y') (hC.smul hZat) (hF.smul hpsiat) j l]
    have m1 := norm_physPd2_smul_le hC hZat
      (A₀ := 1) (A₁ := 2 * M * i) (A₂ := 12 * M * i ^ 2)
      (by rw [hyr]; exact bC0)
      (fun k => (cC1 k).trans bC1)
      (fun j' l' => (cC2 j' l').trans (by
        calc |deriv (deriv (tcC0 ν R χ)) r| + i * |deriv (tcC0 ν R χ) r|
            ≤ 10 * M * i ^ 2 + i * (2 * M * i) := add_le_add bC2 (mul_le_mul_of_nonneg_left bC1 hi0.le)
          _ = 12 * M * i ^ 2 := by ring)) j l
    have m2 := norm_physPd2_smul_le hF hpsiat
      (A₀ := 2 * M * i ^ 2) (A₁ := 12 * M * i ^ 3) (A₂ := 104 * M * i ^ 4)
      (by rw [hyr]; exact bF0)
      (fun k => (cF1 k).trans bF1)
      (fun j' l' => (cF2 j' l').trans (by
        calc |deriv (deriv (tcF0 ν R χ)) r| + i * |deriv (tcF0 ν R χ) r|
            ≤ 92 * M * i ^ 4 + i * (12 * M * i ^ 3) := add_le_add bF2 (mul_le_mul_of_nonneg_left bF1 hi0.le)
          _ = 104 * M * i ^ 4 := by ring)) j l
    rw [hpsi0] at m2
    have m2' : ‖physPd2 (fun y' => tcF0 ν R χ (ϱ y') • psiFld Z τ y') j l y‖ ≤
        104 * M * i ^ 4 * P + 12 * M * i ^ 3 * (r * Zn + r * Zn) +
          2 * M * i ^ 2 * (Zn + r * G) := by
      refine m2.trans ?_
      have hj1 := hpsi1 j
      have hl1 := hpsi1 l
      have hjl2 := hpsi2 j l
      gcongr
    have he1 : 12 * M * i ^ 3 * (r * Zn + r * Zn) = 24 * M * i ^ 2 * Zn := by
      calc 12 * M * i ^ 3 * (r * Zn + r * Zn) = 24 * M * (r * i) * i ^ 2 * Zn := by ring
        _ = 24 * M * i ^ 2 * Zn := by rw [hri]; ring
    have he2 : 2 * M * i ^ 2 * (Zn + r * G) = 2 * M * i ^ 2 * Zn + 2 * M * i * G := by
      calc 2 * M * i ^ 2 * (Zn + r * G) = 2 * M * i ^ 2 * Zn + 2 * M * (r * i) * i * G := by ring
        _ = 2 * M * i ^ 2 * Zn + 2 * M * i * G := by rw [hri]; ring
    have hpdM : 1 * ‖physPd2 (Z τ) j l y‖ ≤ M * ‖physPd2 (Z τ) j l y‖ :=
      mul_le_mul_of_nonneg_right hM (norm_nonneg _)
    have pZ : 0 ≤ M * i ^ 2 * Zn := by positivity
    calc ‖physPd2 (fun y' => tcC0 ν R χ (ϱ y') • Z τ y') j l y +
            physPd2 (fun y' => tcF0 ν R χ (ϱ y') • psiFld Z τ y') j l y‖
        ≤ ‖physPd2 (fun y' => tcC0 ν R χ (ϱ y') • Z τ y') j l y‖ +
          ‖physPd2 (fun y' => tcF0 ν R χ (ϱ y') • psiFld Z τ y') j l y‖ := norm_add_le _ _
      _ ≤ (12 * M * i ^ 2 * Zn + 2 * M * i * (‖physPd (Z τ) j y‖ + ‖physPd (Z τ) l y‖) +
            1 * ‖physPd2 (Z τ) j l y‖) +
          (104 * M * i ^ 4 * P + 12 * M * i ^ 3 * (r * Zn + r * Zn) +
            2 * M * i ^ 2 * (Zn + r * G)) := add_le_add m1 m2'
      _ ≤ _ := by rw [he1, he2]; linarith
  -- Sum over j, l : Fin 3
  have hsum : hessSize (wardStreamCut ν R χ Z τ) y ≤
      ∑ j : Fin 3, ∑ l : Fin 3,
        (M * ‖physPd2 (Z τ) j l y‖ +
          2 * M * i * (‖physPd (Z τ) j y‖ + ‖physPd (Z τ) l y‖) +
          (2 * M * i * G + 40 * M * i ^ 2 * Zn + 104 * M * i ^ 4 * P)) :=
    Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => hjl j l
  refine hsum.trans ?_
  have hs1 : (∑ j : Fin 3, ∑ l : Fin 3, M * ‖physPd2 (Z τ) j l y‖) = M * H := by
    simp only [H, hessSize, Finset.mul_sum]
  have hs2 : (∑ j : Fin 3, ∑ l : Fin 3, 2 * M * i * (‖physPd (Z τ) j y‖ + ‖physPd (Z τ) l y‖)) =
      12 * M * i * G := by
    simp only [G, gradSize, Fin.sum_univ_three]
    ring
  simp only [Finset.sum_add_distrib, hs1, hs2, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  norm_num
  have pH : 0 ≤ M * H := by positivity
  have pG : 0 ≤ M * i * G := by positivity
  have pZ : 0 ≤ M * i ^ 2 * Zn := by positivity
  have pP : 0 ≤ M * i ^ 4 * P := by positivity
  linarith

end UnforcedLeray.Short.PartIIIb.Concrete
end
