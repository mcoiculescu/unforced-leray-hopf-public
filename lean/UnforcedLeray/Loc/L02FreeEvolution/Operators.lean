import UnforcedLeray.Units.B0418.Operator
import UnforcedLeray.Analysis.Heat.SmoothingBounds
import UnforcedLeray.Analysis.Heat.Solenoidal
import UnforcedLeray.Analysis.LerayProjection.TranslationGenerator
import UnforcedLeray.Analysis.DerivativeScaling
import UnforcedLeray.Analysis.ViscosityTransport.L2Dilation

/-!
# L2 helper: the free evolution `S₀(s)` as operators on `L²`, `H¹` and `H²`

Step L2 of the localization proof, `paper/main.tex` lines 292–298 (`loc:eq:free-evolution`),
blueprint unit B0712. The manuscript's formula is
`S₀(s) f(y) = e^{s/2} [e^{h(e^s-1)Δ} f](e^{s/2} y)`.

This file builds the operators from compiled pieces:
* `freeL2 h s` is the `L²` operator of the literal formula: the compiled

  at `p = 2`, whose class is represented a.e. by `AncientLocalization.freeEvolution h s`;
* `dil s = freeL2 0 s` is the similarity dilation `F ↦ e^{s/2} F(e^{s/2}·)`, and
  `dil s ∘ e^{h(e^s-1)Δ} = freeL2 h s` (`dil_heatOperator`);
* the heat operator commutes with weak derivatives (`hasWeak_heatOperator`, proved from its
  commutation with translations, in the pattern of the compiled `Leray.weakDerivative_projection`),
  and the dilation multiplies the derivative by `e^{s/2}` (`hasWeak_dil`);
* `mkH1`, `mkH2` assemble `H¹`/`H²`-valued operators from component operators;
* `heatH1 t : H¹ → H¹`, `heatH1toH2 t : H¹ → H²` (`t > 0`), `dilH1 s`, `dilH2 s`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace UnforcedLeray.Loc.L02

open AncientLocalization SobolevGraph

/-! ## `L²` level -/

/-- The heat time `h(e^s - 1)` inside `S₀(s)` (line 294). -/
def heatTime (h s : ℝ) : ℝ := h * (Real.exp s - 1)

theorem heatTime_pos {h s : ℝ} (hh : 0 < h) (hs : 0 < s) : 0 < heatTime h s :=
  mul_pos hh (sub_pos.mpr (Real.one_lt_exp_iff.mpr hs))

/-- `S₀(s)` on `L²(ℝ³;ℝ³)`: the literal formula of line 294 on `L²` classes (the compiled
`B0418.freeSemigroupLp` at `p = 2`). -/
def freeL2 (h s : ℝ) : L2Space →L[ℝ] L2Space :=
  B0418.freeSemigroupLp (p := 2) ENNReal.ofNat_ne_top h s

/-- The similarity dilation `F ↦ e^{s/2} F(e^{s/2} ·)` on `L²` (zero viscosity). -/
def dil (s : ℝ) : L2Space →L[ℝ] L2Space := freeL2 0 s

theorem gammaExp_two : B0418.gammaExp 2 = 1 / 4 := by
  rw [B0418.gammaExp]
  norm_num

theorem norm_freeL2_le (h s : ℝ) : ‖freeL2 h s‖ ≤ Real.exp (-(s / 4)) := by
  have hb := B0418.norm_freeSemigroupLp_le (p := 2) ENNReal.ofNat_ne_top h s
  rw [gammaExp_two] at hb
  refine hb.trans_eq ?_
  congr 1
  ring

theorem norm_dil_le (s : ℝ) : ‖dil s‖ ≤ Real.exp (-(s / 4)) := norm_freeL2_le 0 s

theorem norm_dil_apply_le (s : ℝ) (F : L2Space) :
    ‖dil s F‖ ≤ Real.exp (-(s / 4)) * ‖F‖ :=
  ((dil s).le_opNorm F).trans
    (mul_le_mul_of_nonneg_right (norm_dil_le s) (norm_nonneg _))

theorem coeFn_freeL2 (h s : ℝ) (F : L2Space) :
    (freeL2 h s F : SpatialField) =ᵐ[volume] freeEvolution h s (F : SpatialField) :=
  B0418.coeFn_freeSemigroupLp (p := 2) ENNReal.ofNat_ne_top h s F

theorem freeEvolution_zero_viscosity (s : ℝ) (f : SpatialField) :
    freeEvolution 0 s f =
      SpatialScaling.spatialScale (Real.exp (s / 2)) (Real.exp (s / 2)) f := by
  simp only [freeEvolution, similarityDilation, zero_mul, Heat.flow_zero]

theorem coeFn_dil (s : ℝ) (F : L2Space) :
    (dil s F : SpatialField) =ᵐ[volume]
      SpatialScaling.spatialScale (Real.exp (s / 2)) (Real.exp (s / 2)) (F : SpatialField) := by
  have h0 := coeFn_freeL2 0 s F
  rwa [freeEvolution_zero_viscosity] at h0

theorem coeFn_heatOperator (t : ℝ) (F : L2Space) :
    (Heat.heatOperator t F : SpatialField) =ᵐ[volume] Heat.flow (F : SpatialField) t := by
  have he : Heat.heatOperator t F = toL2 (Heat.flow (F : SpatialField) t) := by
    rw [Heat.toL2_flow (Lp.memLp F), ViscosityTransport.toL2_coe]
  rw [he]
  exact coeFn_toL2 (Heat.flow_memLp (Lp.memLp F) t)

/-- `S₀(s) = D(s) e^{h(e^s-1)Δ}` on `L²`. -/
theorem dil_heatOperator (h s : ℝ) (F : L2Space) :
    dil s (Heat.heatOperator (heatTime h s) F) = freeL2 h s F := by
  apply Lp.ext
  refine (coeFn_dil s _).trans ?_
  refine (SpatialScaling.ae_eq_spatialScale (coeFn_heatOperator _ F) _
    (Real.exp_pos _).ne').trans ?_
  exact (coeFn_freeL2 h s F).symm

theorem continuousOn_freeL2 {h : ℝ} (hh : 0 ≤ h) (F : L2Space) :
    ContinuousOn (fun s => freeL2 h s F) (Ici 0) :=
  B0418.continuousOn_freeSemigroupLp (p := 2) ENNReal.ofNat_ne_top hh F

/-- The heat operator commutes with the Leray-convention translations. -/
theorem heatOperator_lerayTranslation (t : ℝ) (b : Space) (F : L2Space) :
    Heat.heatOperator t (Leray.translation b F) =
      Leray.translation b (Heat.heatOperator t F) := by
  have hb : ∀ G : L2Space, Leray.translation b G = Heat.translation (-b) G := by
    intro G
    rw [Heat.translation_eq_leray_apply, neg_neg]
  rw [hb, hb]
  by_cases ht : 0 < t
  · rw [Heat.heatOperator_pos ht]
    exact Heat.convolutionOperator_translation _ _ _ _
  · rw [Heat.heatOperator_nonpos (not_lt.mp ht)]
    rfl

/-- The heat operator commutes with weak derivatives: `∂ᵢ e^{tΔ}F = e^{tΔ} ∂ᵢF`. -/
theorem hasWeak_heatOperator (t : ℝ) {F G : L2Space} {i : Fin 3}
    (hFG : HasWeakSpatialDerivative i (F : SpatialField) (G : SpatialField)) :
    HasWeakSpatialDerivative i (Heat.heatOperator t F : SpatialField)
      (Heat.heatOperator t G : SpatialField) := by
  apply Leray.weakDerivative_of_hasDerivAt_translation
  have hd := (Heat.heatOperator t).hasFDerivAt.comp_hasDerivAt 0
    ((Leray.weakDerivative_iff_hasDerivAt_translation F G i).mp hFG)
  simpa only [Function.comp_def, heatOperator_lerayTranslation] using hd

/-- Weak derivatives of `L²` classes scale with the class. -/
theorem hasWeak_smul_L2 {i : Fin 3} {F G : L2Space} (c : ℝ)
    (hFG : HasWeakSpatialDerivative i (F : SpatialField) (G : SpatialField)) :
    HasWeakSpatialDerivative i ((c • F : L2Space) : SpatialField)
      ((c • G : L2Space) : SpatialField) :=
  (hFG.smul c).congr (Lp.coeFn_smul c F).symm (Lp.coeFn_smul c G).symm

/-- The dilation multiplies weak derivatives by `e^{s/2}`. -/
theorem hasWeak_dil (s : ℝ) {F G : L2Space} {i : Fin 3}
    (hFG : HasWeakSpatialDerivative i (F : SpatialField) (G : SpatialField)) :
    HasWeakSpatialDerivative i (dil s F : SpatialField)
      ((Real.exp (s / 2) • dil s G : L2Space) : SpatialField) := by
  have ha0 : Real.exp (s / 2) ≠ 0 := (Real.exp_pos _).ne'
  have h1 := DerivativeScaling.hasWeakSpatialDerivative_spatialScale hFG (Real.exp (s / 2)) ha0
  refine h1.congr (coeFn_dil s F).symm ?_
  have hs : SpatialScaling.spatialScale (Real.exp (s / 2) * Real.exp (s / 2)) (Real.exp (s / 2))
      (G : SpatialField) = Real.exp (s / 2) •
        SpatialScaling.spatialScale (Real.exp (s / 2)) (Real.exp (s / 2)) (G : SpatialField) := by
    funext y
    simp only [SpatialScaling.spatialScale, Pi.smul_apply, mul_smul]
  rw [hs]
  filter_upwards [Lp.coeFn_smul (Real.exp (s / 2)) (dil s G), coeFn_dil s G] with y h1 h2
  rw [Pi.smul_apply, h1, Pi.smul_apply, h2]

theorem dil_mem_solenoidal (s : ℝ) {F : L2Space} (hF : F ∈ Leray.solenoidalSubspace) :
    dil s F ∈ Leray.solenoidalSubspace := by
  rw [Leray.mem_solenoidalSubspace_iff] at hF ⊢
  exact Leray.solenoidal_congr_ae
    (DerivativeScaling.isSolenoidal_spatialScale hF _ (Real.exp_pos _).ne') (coeFn_dil s F).symm

theorem heat_mem_solenoidal (t : ℝ) {F : L2Space} (hF : F ∈ Leray.solenoidalSubspace) :
    Heat.heatOperator t F ∈ Leray.solenoidalSubspace := by
  rw [Leray.mem_solenoidalSubspace_iff] at hF ⊢
  exact Heat.heatOperator_solenoidal t hF

/-- At positive times the heat derivative of an `H¹` field is the kernel derivative. -/
theorem heatOperator_derivative_eq {t : ℝ} (ht : 0 < t) {F G : L2Space} {i : Fin 3}
    (hFG : HasWeakSpatialDerivative i (F : SpatialField) (G : SpatialField)) :
    Heat.heatOperator t G = Heat.firstDerivativeOperator ht i F := by
  apply Lp.ext
  have h1 := hasWeak_heatOperator t hFG
  have h2 := Heat.heat_hasWeakFirst ht F i
  rw [← Heat.heatOperator_pos ht] at h2
  exact h1.ae_eq h2 (Lp.memLp _) (Lp.memLp _)

/-! ## Assembling `H¹`- and `H²`-valued operators -/

/-- An `H¹`-valued operator from a value operator and three derivative operators. -/
def mkH1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : E →L[ℝ] L2Space) (D : Fin 3 → E →L[ℝ] L2Space)
    (hw : ∀ x i, HasWeakSpatialDerivative i (V x : SpatialField) (D i x : SpatialField)) :
    E →L[ℝ] H1 :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => L2Space)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (Fin.cons V D : Fin 4 → (E →L[ℝ] L2Space)))).codRestrict H1Sub
    (fun x => (mem_H1Sub_iff _).mpr (fun i => hw x i))

@[simp] theorem mkH1_value {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : E →L[ℝ] L2Space) (D : Fin 3 → E →L[ℝ] L2Space)
    (hw : ∀ x i, HasWeakSpatialDerivative i (V x : SpatialField) (D i x : SpatialField))
    (x : E) : (mkH1 V D hw x).value = V x := rfl

@[simp] theorem mkH1_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : E →L[ℝ] L2Space) (D : Fin 3 → E →L[ℝ] L2Space)
    (hw : ∀ x i, HasWeakSpatialDerivative i (V x : SpatialField) (D i x : SpatialField))
    (x : E) (i : Fin 3) : (mkH1 V D hw x).derivative i = D i x := rfl

/-- An `H²`-valued operator from value, first and ordered second derivative operators. -/
def mkH2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : E →L[ℝ] L2Space) (D : Fin 3 → E →L[ℝ] L2Space)
    (S : Fin 3 → Fin 3 → E →L[ℝ] L2Space)
    (hw1 : ∀ x i, HasWeakSpatialDerivative i (V x : SpatialField) (D i x : SpatialField))
    (hw2 : ∀ x i j, HasWeakSpatialDerivative j (D i x : SpatialField) (S i j x : SpatialField)) :
    E →L[ℝ] H2 :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : H2Index => L2Space)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi
      (Sum.elim (fun _ => V) (Sum.elim D (fun ij => S ij.1 ij.2)) :
        H2Index → (E →L[ℝ] L2Space)))).codRestrict H2Sub
    (fun x => (mem_H2Sub_iff _).mpr ⟨fun i => hw1 x i, fun i j => hw2 x i j⟩)

@[simp] theorem mkH2_value {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : E →L[ℝ] L2Space) (D : Fin 3 → E →L[ℝ] L2Space)
    (S : Fin 3 → Fin 3 → E →L[ℝ] L2Space)
    (hw1 : ∀ x i, HasWeakSpatialDerivative i (V x : SpatialField) (D i x : SpatialField))
    (hw2 : ∀ x i j, HasWeakSpatialDerivative j (D i x : SpatialField) (S i j x : SpatialField))
    (x : E) : (mkH2 V D S hw1 hw2 x).value = V x := rfl

@[simp] theorem mkH2_first {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : E →L[ℝ] L2Space) (D : Fin 3 → E →L[ℝ] L2Space)
    (S : Fin 3 → Fin 3 → E →L[ℝ] L2Space)
    (hw1 : ∀ x i, HasWeakSpatialDerivative i (V x : SpatialField) (D i x : SpatialField))
    (hw2 : ∀ x i j, HasWeakSpatialDerivative j (D i x : SpatialField) (S i j x : SpatialField))
    (x : E) (i : Fin 3) : (mkH2 V D S hw1 hw2 x).first i = D i x := rfl

@[simp] theorem mkH2_second {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : E →L[ℝ] L2Space) (D : Fin 3 → E →L[ℝ] L2Space)
    (S : Fin 3 → Fin 3 → E →L[ℝ] L2Space)
    (hw1 : ∀ x i, HasWeakSpatialDerivative i (V x : SpatialField) (D i x : SpatialField))
    (hw2 : ∀ x i j, HasWeakSpatialDerivative j (D i x : SpatialField) (S i j x : SpatialField))
    (x : E) (i j : Fin 3) : (mkH2 V D S hw1 hw2 x).second i j = S i j x := rfl

/-! ## Norm helpers for the graph norms -/

theorem h1_norm_value_le (F : H1) : ‖F.value‖ ≤ ‖F‖ := by
  have hsq := H1.norm_sq F
  have h : 0 ≤ ∑ i : Fin 3, ‖F.derivative i‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by linarith)

theorem h1_norm_derivative_le (F : H1) (i : Fin 3) : ‖F.derivative i‖ ≤ ‖F‖ := by
  have hsq := H1.norm_sq F
  have h : ‖F.derivative i‖ ^ 2 ≤ ∑ j : Fin 3, ‖F.derivative j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖F.derivative j‖ ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by nlinarith [sq_nonneg ‖F.value‖])

theorem h1_norm_le_of {F : H1} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hv : ‖F.value‖ ≤ A) (hd : ∀ i, ‖F.derivative i‖ ≤ B) : ‖F‖ ≤ A + 3 * B := by
  have hsq := H1.norm_sq F
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have h1 : ‖F.value‖ ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hv 2
  have h2 : ∑ i : Fin 3, ‖F.derivative i‖ ^ 2 ≤ ∑ _i : Fin 3, B ^ 2 :=
    Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hd i) 2)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat] at h2
  nlinarith

theorem h2_norm_le_of {F : H2} {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hv : ‖F.value‖ ≤ A) (hf : ∀ i, ‖F.first i‖ ≤ B) (hs : ∀ i j, ‖F.second i j‖ ≤ C) :
    ‖F‖ ≤ A + 3 * B + 9 * C := by
  have hsq := H2.norm_sq F
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have h1 : ‖F.value‖ ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hv 2
  have h2 : ∑ i : Fin 3, ‖F.first i‖ ^ 2 ≤ ∑ _i : Fin 3, B ^ 2 :=
    Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hf i) 2)
  have h3 : ∑ i : Fin 3, ∑ j : Fin 3, ‖F.second i j‖ ^ 2 ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, C ^ 2 :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum
      (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hs i j) 2))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat] at h2 h3
  nlinarith

/-! ## The concrete operators -/

/-- `e^{tΔ}` on `H¹`: it commutes with the weak derivatives. -/
def heatH1 (t : ℝ) : H1 →L[ℝ] H1 :=
  mkH1 ((Heat.heatOperator t).comp H1.valueCLM)
    (fun i => (Heat.heatOperator t).comp (H1.derivativeCLM i))
    (fun F i => hasWeak_heatOperator t (F.hasWeakDerivative i))

/-- `e^{tΔ} : H¹ → H²` for `t > 0`: second derivatives `∂ⱼ e^{tΔ} ∂ᵢ F`. -/
def heatH1toH2 {t : ℝ} (ht : 0 < t) : H1 →L[ℝ] H2 :=
  mkH2 ((Heat.heatOperator t).comp H1.valueCLM)
    (fun i => (Heat.heatOperator t).comp (H1.derivativeCLM i))
    (fun i j => (Heat.firstDerivativeOperator ht j).comp (H1.derivativeCLM i))
    (fun F i => hasWeak_heatOperator t (F.hasWeakDerivative i))
    (fun F i j => by
      have h := Heat.heat_hasWeakFirst ht (F.derivative i) j
      rw [← Heat.heatOperator_pos ht] at h
      exact h)

/-- The similarity dilation on `H¹`: `∂ᵢ (D(s)F) = e^{s/2} D(s) ∂ᵢF`. -/
def dilH1 (s : ℝ) : H1 →L[ℝ] H1 :=
  mkH1 ((dil s).comp H1.valueCLM)
    (fun i => Real.exp (s / 2) • (dil s).comp (H1.derivativeCLM i))
    (fun F i => hasWeak_dil s (F.hasWeakDerivative i))

/-- The similarity dilation on `H²`. -/
def dilH2 (s : ℝ) : H2 →L[ℝ] H2 :=
  mkH2 ((dil s).comp H2.valueCLM)
    (fun i => Real.exp (s / 2) • (dil s).comp (H2.firstCLM i))
    (fun i j => Real.exp s • (dil s).comp (H2.secondCLM i j))
    (fun F i => hasWeak_dil s (F.hasWeakFirst i))
    (fun F i j => by
      have h := hasWeak_smul_L2 (Real.exp (s / 2)) (hasWeak_dil s (F.hasWeakSecond i j))
      rw [smul_smul, ← Real.exp_add, add_halves] at h
      exact h)

end UnforcedLeray.Loc.L02
