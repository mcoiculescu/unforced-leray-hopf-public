import UnforcedLeray.Units.B0059
import UnforcedLeray.Units.B0060.Leibniz

/-!
# B0060 helper: `‖b Kf‖_{H^{j+1}_M} ≤ C ‖f‖_{H^j_M}` from weighted coefficient bounds

Helper for blueprint unit **B0060** (`paper/main.tex:1215–1220`, `eq:st18-t00049`). This file
proves the estimate for any smooth coefficient `b` whose weighted coefficient bounds of order
`≤ j + 1` are finite, with a constant `leibConst j M * (A + B)`, where
* `A` bounds the weighted `L^∞` coefficient seminorms `sup_y ⟨y⟩^M |∂^β b(y)|`, and
* `B` bounds the weighted `L²` coefficient seminorms `‖⟨y⟩^M ∂^β b‖₂`, `|β| ≤ j + 1`.

**Proof (tex 1218–1220).** Leibniz (`leibniz_2d`, `Units/B0060/Leibniz.lean`) writes
`∂^γ (b Kf) = ∑_{β ≤ γ} C(γ,β) ∂^β b ∂^{γ-β} Kf` weakly (`hasWeakDerivOn_mul_biotSavart`), where
`∂^δ Kf`, `1 ≤ |δ| ≤ j + 1`, are the weak derivatives of B0059. Terms with a derivative on `Kf`
use its unweighted `L²` bound `‖∂^δ Kf‖₂ ≤ 2 ‖f‖_{H^j_M}` (B0059, `exists_weakDeriv_biotSavart`
with `gradL2Bound_two`) and the weighted `L^∞` coefficient bound. The term with no derivative on
`Kf` uses the split `Kf = f ⋆ K_near + f ⋆ K_far` of B0059: the near part in `L²` with the
weighted `L^∞` coefficient bound, the far part in `L^∞` (with `‖f‖₁ ≤ C_M ‖f‖_{H^j_M}`) with the
weighted `L²` coefficient bound (`eLpNorm_mul_biotSavart_le`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff

namespace UnforcedLeray.B0060

open NonUniqueEuler.Sob NonUniqueEuler.Sob.WeakDerivAux UnforcedLeray.B0008 UnforcedLeray.B0009
  UnforcedLeray.B0059

/-! ### The derivatives of the velocity -/

/-- The family of derivatives of the velocity component `(Kf)_i`: `D (0,0) = (Kf)_i` and
`D δ = ∂^δ (Kf)_i` (the chosen weak derivative `weakPartial`) for `δ ≠ 0`. -/
def velDer (f : ℂ → ℂ) (i : Fin 2) (δ : ℕ × ℕ) : ℂ → ℂ :=
  if δ = (0, 0) then biotSavart f i else weakPartial δ (biotSavart f i)

theorem velDer_zero (f : ℂ → ℂ) (i : Fin 2) : velDer f i (0, 0) = biotSavart f i := by simp [velDer]

theorem velDer_of_ne {f : ℂ → ℂ} {i : Fin 2} {δ : ℕ × ℕ} (h : δ ≠ (0, 0)) :
    velDer f i δ = weakPartial δ (biotSavart f i) := by simp [velDer, h]

theorem one_le_of_ne_zero {δ : ℕ × ℕ} (h : δ ≠ (0, 0)) : 1 ≤ δ.1 + δ.2 := by
  rcases δ with ⟨a, b⟩
  by_contra hc
  exact h (Prod.ext (show a = 0 by omega) (show b = 0 by omega))

section Velocity

variable {j : ℕ} {M : ℝ}

/-- `D δ = ∂^δ (Kf)_i` weakly, for `|δ| ≤ j + 1` (B0059). -/
theorem hasWeakDerivOn_velDer (hM : 1 < M) (F : HjM j M) (i : Fin 2) {δ : ℕ × ℕ}
    (hδ : δ ∈ multiIdx (j + 1)) :
    HasWeakDerivOn univ (pdList δ) (biotSavart F.value i) (velDer F.value i δ) := by
  by_cases h0 : δ = (0, 0)
  · subst h0
    rw [velDer_zero]
    exact hasWeakDerivOn_nil_self _
  · rw [velDer_of_ne h0]
    exact (l2_weakPartial_biotSavart_le hM F i (mem_multiIdx.1 hδ) (one_le_of_ne_zero h0)).1

/-- **Unweighted `L²` bound of the derivatives of `Kf`** (tex 1210, B0059):
`‖∂^δ Kf‖₂ ≤ 2 ‖f‖_{H^j_M}` for `1 ≤ |δ| ≤ j + 1`. -/
theorem velDer_bound (hM : 1 < M) (F : HjM j M) (i : Fin 2) {δ : ℕ × ℕ}
    (hδ : δ ∈ multiIdx (j + 1)) (h0 : δ ≠ (0, 0)) :
    MemLp (velDer F.value i δ) 2 volume ∧
      eLpNorm (velDer F.value i δ) 2 volume ≤ ENNReal.ofReal (2 * ‖F‖) := by
  rw [velDer_of_ne h0]
  obtain ⟨g, hg2, hgd, β, -, hgb⟩ :=
    exists_weakDeriv_biotSavart gradL2Bound_two hM F i (mem_multiIdx.1 hδ) (one_le_of_ne_zero h0)
  have hgl := (hg2.locallyIntegrable one_le_two).locallyIntegrableOn univ
  have h := weakDerivOn_ae_eq isOpen_univ hgl hgd
  have hae : weakPartial δ (biotSavart F.value i) =ᵐ[volume] g := by
    filter_upwards [h] with x hx using hx (mem_univ x)
  refine ⟨hg2.ae_eq hae.symm, ?_⟩
  rw [eLpNorm_congr_ae hae]
  refine hgb.trans ?_
  rw [ENNReal.ofReal_mul (by norm_num)]
  gcongr
  exact B0059.HjM.eLpNorm_der_le (by linarith) F β

theorem locallyIntegrable_velDer (hM : 1 < M) (F : HjM j M) (i : Fin 2) {δ : ℕ × ℕ}
    (hδ : δ ∈ multiIdx (j + 1)) : LocallyIntegrable (velDer F.value i δ) volume := by
  by_cases h0 : δ = (0, 0)
  · subst h0
    rw [velDer_zero]
    exact locallyIntegrable_biotSavart (B0008.HjM.integrable_value hM F)
      (B0059.HjM.memLp_der_volume (by linarith) F (idx0 j)) i
  · exact (velDer_bound hM F i hδ h0).1.locallyIntegrable one_le_two

theorem pdList_succ_fst (a b : ℕ) : pdList (a + 1, b) = [1] ++ pdList (a, b) := rfl

theorem pdList_succ_snd (a b : ℕ) : pdList (a, b + 1) = pdList (a, b) ++ [Complex.I] := by
  simp [pdList, List.replicate_succ']

/-- `∂₁ D δ = D (δ + e₁)` weakly, `|δ| < j + 1`. -/
theorem hasWeakDerivOn_velDer_one (hM : 1 < M) (F : HjM j M) (i : Fin 2) (δ : ℕ × ℕ)
    (hδ : δ.1 + δ.2 < j + 1) :
    HasWeakDerivOn univ [1] (velDer F.value i δ) (velDer F.value i (δ.1 + 1, δ.2)) := by
  have h0 := hasWeakDerivOn_velDer hM F i (δ := δ) (mem_multiIdx.2 (by omega))
  have h1 := hasWeakDerivOn_velDer hM F i (δ := (δ.1 + 1, δ.2)) (mem_multiIdx.2 (by simp; omega))
  rw [pdList_succ_fst] at h1
  exact hasWeakDerivOn_of_append h0 (h1.perm List.perm_append_comm)

/-- `∂₂ D δ = D (δ + e₂)` weakly, `|δ| < j + 1`. -/
theorem hasWeakDerivOn_velDer_I (hM : 1 < M) (F : HjM j M) (i : Fin 2) (δ : ℕ × ℕ)
    (hδ : δ.1 + δ.2 < j + 1) :
    HasWeakDerivOn univ [Complex.I] (velDer F.value i δ) (velDer F.value i (δ.1, δ.2 + 1)) := by
  have h0 := hasWeakDerivOn_velDer hM F i (δ := δ) (mem_multiIdx.2 (by omega))
  have h1 := hasWeakDerivOn_velDer hM F i (δ := (δ.1, δ.2 + 1)) (mem_multiIdx.2 (by simp; omega))
  rw [pdList_succ_snd] at h1
  exact hasWeakDerivOn_of_append h0 h1

end Velocity

/-! ### The Leibniz expansion of `∂^γ (b Kf)` -/

/-- The Leibniz coefficient `C(γ₁,β₁) C(γ₂,β₂)`. -/
def lc (γ β : ℕ × ℕ) : ℕ := γ.1.choose β.1 * γ.2.choose β.2

/-- `∑_{β ≤ γ} C(γ,β) ∂^β b · ∂^{γ-β} (Kf)_i`. -/
def leibSum (b f : ℂ → ℂ) (i : Fin 2) (γ : ℕ × ℕ) : ℂ → ℂ := fun x =>
  ∑ β ∈ leIdx γ, ((lc γ β : ℕ) : ℂ) * partialD β b x * velDer f i (γ.1 - β.1, γ.2 - β.2) x

theorem leibSum_zero (b f : ℂ → ℂ) (i : Fin 2) :
    leibSum b f i (0, 0) = fun x => b x * biotSavart f i x := by
  funext x
  simp [leibSum, leIdx, lc, partialD, pdList, velDer]

theorem mem_multiIdx_of_mem_leIdx {k : ℕ} {γ β : ℕ × ℕ} (hγ : γ ∈ multiIdx k)
    (hβ : β ∈ leIdx γ) : β ∈ multiIdx k ∧ (γ.1 - β.1, γ.2 - β.2) ∈ multiIdx k := by
  rw [leIdx, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hβ
  have := mem_multiIdx.1 hγ
  exact ⟨mem_multiIdx.2 (by omega), mem_multiIdx.2 (by simp only; omega)⟩

section Leibniz

variable {j : ℕ} {M : ℝ}

/-- **Leibniz for `b Kf`** (tex 1218): for smooth `b` and `|γ| ≤ j + 1`,
`∂^γ (b (Kf)_i) = ∑_{β ≤ γ} C(γ,β) ∂^β b ∂^{γ-β} (Kf)_i` weakly on the plane. -/
theorem hasWeakDerivOn_mul_biotSavart (hM : 1 < M) (F : HjM j M) (i : Fin 2) {b : ℂ → ℂ}
    (hb : ContDiff ℝ ∞ b) {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx (j + 1)) :
    HasWeakDerivOn univ (pdList γ) (fun x => b x * biotSavart F.value i x)
      (leibSum b F.value i γ) := by
  have h := leibniz_2d (k := j + 1) hb (F := velDer F.value i)
    (fun δ hδ => locallyIntegrable_velDer hM F i hδ)
    (fun δ hδ => hasWeakDerivOn_velDer_one hM F i δ hδ)
    (fun δ hδ => hasWeakDerivOn_velDer_I hM F i δ hδ) hγ
  rw [velDer_zero] at h
  exact h

theorem locallyIntegrable_leibSum (hM : 1 < M) (F : HjM j M) (i : Fin 2) {b : ℂ → ℂ}
    (hb : ContDiff ℝ ∞ b) {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx (j + 1)) :
    LocallyIntegrable (leibSum b F.value i γ) volume := by
  refine locallyIntegrable_finsetSum _ fun β hβ => ?_
  exact (locallyIntegrable_velDer hM F i (mem_multiIdx_of_mem_leIdx hγ hβ).2).continuous_mul
    (continuous_const.mul (contDiff_iterDirDeriv hb (pdList β)).continuous)

end Leibniz

/-! ### The weighted bounds -/

/-- The constant `‖K_near‖₁ + ‖K_near‖₁` of B0059's near kernels, as a real number. -/
def NL : ℝ := nearL1.toReal

theorem NL_nonneg : 0 ≤ NL := ENNReal.toReal_nonneg

theorem CM_nonneg (M : ℝ) : 0 ≤ CM M := Real.sqrt_nonneg _

section Bounds

variable {j : ℕ} {M : ℝ}

/-- **The term with no derivative on `Kf`** (tex 1220): for a coefficient `w` with
`|w| ≤ A` and `‖w‖₂ ≤ B`, `‖w Kf‖₂ ≤ A ‖K_near‖₁ ‖f‖_{H^j_M} + B π⁻¹ C_M ‖f‖_{H^j_M}`; the near
part of `Kf` is in `L²` and the far part in `L^∞` (B0059). -/
theorem eLpNorm_mul_biotSavart_le (hM : 1 < M) (F : HjM j M) (i : Fin 2) {w : ℂ → ℂ}
    (hw : AEStronglyMeasurable w volume) {A B : ℝ} (hA : ∀ y, ‖w y‖ ≤ A) (hB0 : 0 ≤ B)
    (hB : eLpNorm w 2 volume ≤ ENNReal.ofReal B) :
    eLpNorm (fun y => w y * biotSavart F.value i y) 2 volume ≤
      ENNReal.ofReal (A * NL * ‖F‖ + B * (Real.pi⁻¹ * (CM M * ‖F‖))) := by
  have hM0 : 0 ≤ M := by linarith
  have hf1 : Integrable (F.value : ℂ → ℂ) volume := B0008.HjM.integrable_value hM F
  have hf2 : MemLp (F.value : ℂ → ℂ) 2 volume := B0059.HjM.memLp_der_volume hM0 F (idx0 j)
  have hfF : eLpNorm (F.value : ℂ → ℂ) 2 volume ≤ ENNReal.ofReal ‖F‖ :=
    B0059.HjM.eLpNorm_der_le hM0 F (idx0 j)
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have e : (fun y => w y * biotSavart F.value i y) =ᵐ[volume]
      (fun y => w y * nearPart F.value i y) + (fun y => w y * farPart F.value i y) := by
    filter_upwards [biotSavart_ae_eq_near_add_far hf1 i] with y hy
    simp only [Pi.add_apply, hy, mul_add]
  rw [eLpNorm_congr_ae e]
  refine (eLpNorm_add_le (hw.mul (aestronglyMeasurable_nearPart hf2.1 i))
    (hw.mul (aestronglyMeasurable_farPart hf1.aestronglyMeasurable i)) one_le_two).trans ?_
  have h1 : eLpNorm (fun y => w y * nearPart F.value i y) 2 volume ≤
      ENNReal.ofReal (A * NL * ‖F‖) := by
    have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := volume)
      (f := fun y => w y * nearPart F.value i y) (g := nearPart F.value i) (c := A)
      (ae_of_all _ fun y => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hA y) (norm_nonneg _)) 2
    refine h.trans ?_
    rw [ENNReal.ofReal_mul (mul_nonneg hA0 NL_nonneg), ENNReal.ofReal_mul hA0, mul_assoc]
    gcongr
    refine (memLp_nearPart hf2 i).2.trans ?_
    rw [NL, ENNReal.ofReal_toReal nearL1_ne_top]
    exact mul_le_mul' (lintegral_nearKernel_le i) hfF
  have h2 : eLpNorm (fun y => w y * farPart F.value i y) 2 volume ≤
      ENNReal.ofReal (B * (Real.pi⁻¹ * (CM M * ‖F‖))) := by
    have hc : 0 ≤ Real.pi⁻¹ * ∫ t, ‖F.value t‖ :=
      mul_nonneg (inv_nonneg.2 Real.pi_pos.le) (integral_nonneg fun _ => norm_nonneg _)
    have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := volume)
      (f := fun y => w y * farPart F.value i y) (g := w) (c := Real.pi⁻¹ * ∫ t, ‖F.value t‖)
      (ae_of_all _ fun y => by
        rw [norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (norm_farPart_le hf1 i y) (norm_nonneg _)) 2
    refine h.trans ?_
    calc ENNReal.ofReal (Real.pi⁻¹ * ∫ t, ‖F.value t‖) * eLpNorm w 2 volume
        ≤ ENNReal.ofReal (Real.pi⁻¹ * ∫ t, ‖F.value t‖) * ENNReal.ofReal B := by gcongr
      _ = ENNReal.ofReal ((Real.pi⁻¹ * ∫ t, ‖F.value t‖) * B) := (ENNReal.ofReal_mul hc).symm
      _ ≤ ENNReal.ofReal (B * (Real.pi⁻¹ * (CM M * ‖F‖))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [mul_comm]
        refine mul_le_mul_of_nonneg_left ?_ hB0
        exact mul_le_mul_of_nonneg_left (integral_norm_value_le hM F)
          (inv_nonneg.2 Real.pi_pos.le)
  refine (add_le_add h1 h2).trans_eq (ENNReal.ofReal_add ?_ ?_).symm
  · exact mul_nonneg (mul_nonneg hA0 NL_nonneg) (norm_nonneg _)
  · exact mul_nonneg hB0 (mul_nonneg (inv_nonneg.2 Real.pi_pos.le)
      (mul_nonneg (CM_nonneg M) (norm_nonneg _)))

/-- The per-term constant `A (2 + ‖K_near‖₁) + B π⁻¹ C_M`. -/
def termConst (M A B : ℝ) : ℝ := A * (2 + NL) + B * (Real.pi⁻¹ * CM M)

/-- **One Leibniz term** (tex 1219–1220): `‖⟨y⟩^M ∂^β b · ∂^{γ-β} Kf‖₂ ≤ termConst · ‖f‖_{H^j_M}`. -/
theorem eLpNorm_term_le (hM : 1 < M) (F : HjM j M) (i : Fin 2) {b : ℂ → ℂ}
    (hb : ContDiff ℝ ∞ b) {A B : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : ∀ β ∈ multiIdx (j + 1), ∀ y, bracket y ^ M * ‖partialD β b y‖ ≤ A)
    (hB : ∀ β ∈ multiIdx (j + 1),
      eLpNorm (fun y => bracket y ^ M • partialD β b y) 2 volume ≤ ENNReal.ofReal B)
    {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx (j + 1)) {β : ℕ × ℕ} (hβ : β ∈ leIdx γ) :
    AEStronglyMeasurable (fun y => (bracket y ^ M • partialD β b y) *
        velDer F.value i (γ.1 - β.1, γ.2 - β.2) y) volume ∧
      eLpNorm (fun y => (bracket y ^ M • partialD β b y) *
        velDer F.value i (γ.1 - β.1, γ.2 - β.2) y) 2 volume ≤
        ENNReal.ofReal (termConst M A B * ‖F‖) := by
  obtain ⟨hβm, hδm⟩ := mem_multiIdx_of_mem_leIdx hγ hβ
  have hwc : Continuous fun y => bracket y ^ M • partialD β b y :=
    (continuous_bracket_rpow M).smul (contDiff_iterDirDeriv hb (pdList β)).continuous
  have hwA : ∀ y, ‖bracket y ^ M • partialD β b y‖ ≤ A := fun y => by
    rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (bracket_pos y).le M)]
    exact hA β hβm y
  refine ⟨hwc.aestronglyMeasurable.mul
    (locallyIntegrable_velDer hM F i hδm).aestronglyMeasurable, ?_⟩
  have hF0 := norm_nonneg F
  have hpi : 0 ≤ Real.pi⁻¹ := inv_nonneg.2 Real.pi_pos.le
  have hCM := CM_nonneg M
  have hNL := NL_nonneg
  by_cases h0 : (γ.1 - β.1, γ.2 - β.2) = ((0, 0) : ℕ × ℕ)
  · rw [h0, velDer_zero]
    refine (eLpNorm_mul_biotSavart_le hM F i hwc.aestronglyMeasurable hwA hB0 (hB β hβm)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rw [termConst]
    nlinarith [mul_nonneg hA0 hF0]
  · have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := volume)
      (f := fun y => (bracket y ^ M • partialD β b y) *
        velDer F.value i (γ.1 - β.1, γ.2 - β.2) y)
      (g := velDer F.value i (γ.1 - β.1, γ.2 - β.2)) (c := A)
      (ae_of_all _ fun y => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hwA y) (norm_nonneg _)) 2
    refine h.trans ?_
    calc ENNReal.ofReal A * eLpNorm (velDer F.value i (γ.1 - β.1, γ.2 - β.2)) 2 volume
        ≤ ENNReal.ofReal A * ENNReal.ofReal (2 * ‖F‖) := by
          gcongr
          exact (velDer_bound hM F i hδm h0).2
      _ = ENNReal.ofReal (A * (2 * ‖F‖)) := (ENNReal.ofReal_mul hA0).symm
      _ ≤ ENNReal.ofReal (termConst M A B * ‖F‖) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [termConst]
          nlinarith [mul_nonneg (mul_nonneg hA0 hNL) hF0,
            mul_nonneg (mul_nonneg hB0 (mul_nonneg hpi hCM)) hF0]

/-- `∑_{|γ| ≤ j+1} ∑_{β ≤ γ} C(γ,β)`, a bound for each Leibniz coefficient sum. -/
def coefSum (j : ℕ) : ℝ := ∑ γ ∈ multiIdx (j + 1), ∑ β ∈ leIdx γ, ((lc γ β : ℕ) : ℝ)

theorem sum_lc_le {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx (j + 1)) :
    ∑ β ∈ leIdx γ, ((lc γ β : ℕ) : ℝ) ≤ coefSum j :=
  Finset.single_le_sum (f := fun γ => ∑ β ∈ leIdx γ, ((lc γ β : ℕ) : ℝ))
    (fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) hγ

theorem coefSum_nonneg (j : ℕ) : 0 ≤ coefSum j :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

/-- **The weighted bound of `∂^γ (b Kf)`**: `‖⟨y⟩^M ∂^γ (b Kf)‖₂ ≤ coefSum j · termConst · ‖f‖`. -/
theorem eLpNorm_leibSum_le (hM : 1 < M) (F : HjM j M) (i : Fin 2) {b : ℂ → ℂ}
    (hb : ContDiff ℝ ∞ b) {A B : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : ∀ β ∈ multiIdx (j + 1), ∀ y, bracket y ^ M * ‖partialD β b y‖ ≤ A)
    (hB : ∀ β ∈ multiIdx (j + 1),
      eLpNorm (fun y => bracket y ^ M • partialD β b y) 2 volume ≤ ENNReal.ofReal B)
    {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx (j + 1)) :
    AEStronglyMeasurable (fun y => bracket y ^ M • leibSum b F.value i γ y) volume ∧
      eLpNorm (fun y => bracket y ^ M • leibSum b F.value i γ y) 2 volume ≤
        ENNReal.ofReal (coefSum j * termConst M A B * ‖F‖) := by
  set T : ℕ × ℕ → ℂ → ℂ := fun β y => ((lc γ β : ℕ) : ℂ) *
    ((bracket y ^ M • partialD β b y) * velDer F.value i (γ.1 - β.1, γ.2 - β.2) y) with hT
  have e : (fun y => bracket y ^ M • leibSum b F.value i γ y) = ∑ β ∈ leIdx γ, T β := by
    funext y
    simp only [leibSum, Finset.sum_apply, Finset.smul_sum, hT]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [Complex.real_smul]
    ring
  have hTm : ∀ β ∈ leIdx γ, AEStronglyMeasurable (T β) volume := fun β hβ =>
    (eLpNorm_term_le hM F i hb hA0 hB0 hA hB hγ hβ).1.const_mul _
  rw [e]
  refine ⟨Finset.aestronglyMeasurable_sum _ hTm, ?_⟩
  have hK0 : 0 ≤ termConst M A B * ‖F‖ := by
    rw [termConst]
    have := NL_nonneg
    have := CM_nonneg M
    have : 0 ≤ Real.pi⁻¹ := inv_nonneg.2 Real.pi_pos.le
    positivity
  refine (eLpNorm_sum_le hTm one_le_two).trans ?_
  calc ∑ β ∈ leIdx γ, eLpNorm (T β) 2 volume
      ≤ ∑ β ∈ leIdx γ, ENNReal.ofReal (((lc γ β : ℕ) : ℝ) * (termConst M A B * ‖F‖)) := by
        refine Finset.sum_le_sum fun β hβ => ?_
        have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := volume) (f := T β)
          (g := fun y => (bracket y ^ M • partialD β b y) *
            velDer F.value i (γ.1 - β.1, γ.2 - β.2) y) (c := ((lc γ β : ℕ) : ℝ))
          (ae_of_all _ fun y => by
            simp only [hT]
            rw [norm_mul, Complex.norm_natCast]) 2
        refine h.trans ?_
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        gcongr
        exact (eLpNorm_term_le hM F i hb hA0 hB0 hA hB hγ hβ).2
    _ = ENNReal.ofReal (∑ β ∈ leIdx γ, ((lc γ β : ℕ) : ℝ) * (termConst M A B * ‖F‖)) :=
        (ENNReal.ofReal_sum_of_nonneg fun β _ => mul_nonneg (Nat.cast_nonneg _) hK0).symm
    _ ≤ ENNReal.ofReal (coefSum j * termConst M A B * ‖F‖) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Finset.sum_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_right (sum_lc_le hγ) hK0

/-- The constant `C_{j,M} = #{|α| ≤ j+1} · coefSum j · (2 + ‖K_near‖₁ + π⁻¹ C_M)` of the
estimate, to be multiplied by `A + B`. -/
def leibConst (j : ℕ) (M : ℝ) : ℝ :=
  ((multiIdx (j + 1)).card : ℝ) * coefSum j * (2 + NL + Real.pi⁻¹ * CM M)

theorem leibConst_nonneg (j : ℕ) (M : ℝ) : 0 ≤ leibConst j M := by
  rw [leibConst]
  have := NL_nonneg
  have := CM_nonneg M
  have := coefSum_nonneg j
  have : 0 ≤ Real.pi⁻¹ := inv_nonneg.2 Real.pi_pos.le
  positivity

/-- **`‖b Kf‖_{H^{j+1}_M} ≤ C_{j,M} (A + B) ‖f‖_{H^j_M}` from weighted coefficient bounds**
(tex 1215–1220). For `M > 1`, a smooth `b` with `⟨y⟩^M |∂^β b| ≤ A` everywhere and
`‖⟨y⟩^M ∂^β b‖₂ ≤ B` for all `|β| ≤ j + 1`, every `f ∈ H^j_M` and each component `i`, the function
`b (Kf)_i` is (a.e.) an element `G` of `H^{j+1}_M` with `‖G‖ ≤ leibConst j M · (A + B) · ‖f‖`. -/
theorem exists_bound_of_coeff (hM : 1 < M) {b : ℂ → ℂ} (hb : ContDiff ℝ ∞ b) {A B : ℝ}
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : ∀ β ∈ multiIdx (j + 1), ∀ y, bracket y ^ M * ‖partialD β b y‖ ≤ A)
    (hB : ∀ β ∈ multiIdx (j + 1),
      eLpNorm (fun y => bracket y ^ M • partialD β b y) 2 volume ≤ ENNReal.ofReal B)
    (F : HjM j M) (i : Fin 2) :
    MemHjM (j + 1) M (fun y => b y * biotSavart F.value i y) ∧
      ∃ G : HjM (j + 1) M,
        (G.value : ℂ → ℂ) =ᵐ[volume] (fun y => b y * biotSavart F.value i y) ∧
          ‖G‖ ≤ leibConst j M * (A + B) * ‖F‖ := by
  have hL := fun {γ : ℕ × ℕ} (hγ : γ ∈ multiIdx (j + 1)) =>
    eLpNorm_leibSum_le hM F i hb hA0 hB0 hA hB hγ
  have hmemL : ∀ γ ∈ multiIdx (j + 1),
      MemLp (fun y => bracket y ^ M • leibSum b F.value i γ y) 2 volume := fun γ hγ =>
    ⟨(hL hγ).1, (hL hγ).2.trans_lt ENNReal.ofReal_lt_top⟩
  have h00 : ((0, 0) : ℕ × ℕ) ∈ multiIdx (j + 1) := mem_multiIdx.2 (by simp)
  have hmem : MemHjM (j + 1) M (fun y => b y * biotSavart F.value i y) := by
    refine ⟨?_, fun α hα =>
      ⟨leibSum b F.value i α, hmemL α hα, hasWeakDerivOn_mul_biotSavart hM F i hb hα⟩⟩
    have h := hmemL (0, 0) h00
    rwa [leibSum_zero] at h
  refine ⟨hmem, HjM.ofMemHjM hmem, HjM.value_ofMemHjM hmem, ?_⟩
  set G := HjM.ofMemHjM hmem
  set X := coefSum j * termConst M A B * ‖F‖ with hX
  have hval := HjM.value_ofMemHjM hmem
  have hder : ∀ α : Idx (j + 1), ‖G.der α‖ ≤ X := by
    intro α
    have h1 : HasWeakDerivOn univ (pdList α.1) (fun y => b y * biotSavart F.value i y)
        (G.der α : ℂ → ℂ) :=
      (G.hasWeakDeriv α).congr_ae (hval.mono fun x hx _ => hx)
        (Filter.Eventually.of_forall fun _ _ => rfl)
    have h2 := hasWeakDerivOn_mul_biotSavart hM F i hb α.2
    have hae := HasWeakDerivOn.ae_eq isOpen_univ
      ((locallyIntegrable_L2w M (G.der α)).locallyIntegrableOn univ)
      ((locallyIntegrable_leibSum hM F i hb α.2).locallyIntegrableOn univ) h1 h2
    have hae' : (fun y => bracket y ^ M • (G.der α : ℂ → ℂ) y) =ᵐ[volume]
        (fun y => bracket y ^ M • leibSum b F.value i α.1 y) := by
      filter_upwards [hae] with y hy
      rw [hy (mem_univ y)]
    rw [norm_L2w, eLpNorm_congr_ae hae']
    refine ENNReal.toReal_le_of_le_ofReal ?_ (hL α.2).2
    rw [hX]
    have := coefSum_nonneg j
    have := norm_nonneg F
    have := NL_nonneg
    have := CM_nonneg M
    have : 0 ≤ Real.pi⁻¹ := inv_nonneg.2 Real.pi_pos.le
    rw [termConst]
    positivity
  have hX0 : 0 ≤ X := (norm_nonneg _).trans (hder ⟨(0, 0), h00⟩)
  set N : ℝ := ((multiIdx (j + 1)).card : ℝ) with hN
  have hN1 : 1 ≤ N := by
    rw [hN]
    exact_mod_cast Finset.card_pos.2 ⟨_, h00⟩
  have hsq : ‖G‖ ^ 2 ≤ (N * X) ^ 2 := by
    rw [HjM.norm_sq]
    calc ∑ α : Idx (j + 1), ‖G.der α‖ ^ 2 ≤ ∑ _α : Idx (j + 1), X ^ 2 :=
          Finset.sum_le_sum fun α _ => pow_le_pow_left₀ (norm_nonneg _) (hder α) 2
      _ = N * X ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN, Fintype.card_coe]
      _ ≤ (N * X) ^ 2 := by nlinarith [sq_nonneg X]
  have hG : ‖G‖ ≤ N * X :=
    le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg (by linarith) hX0) hsq
  refine hG.trans ?_
  rw [hX, leibConst, termConst, ← hN]
  have hNL := NL_nonneg
  have hCM := CM_nonneg M
  have hcs := coefSum_nonneg j
  have hpi : 0 ≤ Real.pi⁻¹ := inv_nonneg.2 Real.pi_pos.le
  have hF0 := norm_nonneg F
  have key : A * (2 + NL) + B * (Real.pi⁻¹ * CM M) ≤ (2 + NL + Real.pi⁻¹ * CM M) * (A + B) := by
    nlinarith [mul_nonneg hA0 (mul_nonneg hpi hCM), mul_nonneg hB0 hNL]
  calc N * (coefSum j * (A * (2 + NL) + B * (Real.pi⁻¹ * CM M)) * ‖F‖)
      = (N * coefSum j * ‖F‖) * (A * (2 + NL) + B * (Real.pi⁻¹ * CM M)) := by ring
    _ ≤ (N * coefSum j * ‖F‖) * ((2 + NL + Real.pi⁻¹ * CM M) * (A + B)) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = N * coefSum j * (2 + NL + Real.pi⁻¹ * CM M) * (A + B) * ‖F‖ := by ring

end Bounds

end UnforcedLeray.B0060
