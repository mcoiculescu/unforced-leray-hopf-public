import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_3

/-!
# `PartIII-b:C/rep/8/3/1`: measurability of `ringAff` (source 5466-5483)

`GRMeas` asks that `ringAff` be `AEStronglyMeasurable` on `srcMeasure`.  The proof replaces the
train by its exponential reparametrisation `(t, x) ↦ v(exp t, x)`, which is globally smooth
(`smooth_v` on `[0,∞) × ℝ²` composed with `exp`).  On `{0 < s}` the reparametrised train agrees
with the actual one (`log` and `exp` are inverse), and `srcMeasure` is concentrated on `{0 < s}`
(`ae_srcMeasure_fst_pos`).  Every piece of the affine expression is then measurable:

* the parametric derivatives of a globally continuous (resp. `C¹`) family are measurable by
  `measurable_fderiv_*_with_param` (Mathlib), and the partial derivatives in the spatial variable
  are jointly continuous by the chain rule;
* the coefficient matrices `Lpt`, `Bmat`, `Ay` are measurable in `s` by `measurable_deriv` and
  `measurable_fderiv_apply_const` (no continuity of `Xmt` is needed).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal ContDiff
open UnforcedLeray.Blueprint.Planar (PlanarData)

set_option linter.unusedSectionVars false

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace GRMeasAux

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F]

/-! ## 1. Partial derivatives of a parametric family -/

lemma fderiv_slice_eq {G : ℝ × (ℝ × ℝ) → F} (hG : Differentiable ℝ G)
    (p : ℝ × (ℝ × ℝ)) (w : ℝ × ℝ) :
    fderiv ℝ (fun z => G (p.1, z)) p.2 w = fderiv ℝ G p (0, w) := by
  have h1 : HasFDerivAt (fun z : ℝ × ℝ => (p.1, z))
      ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) p.2 :=
    (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
  have h2 : HasFDerivAt (fun z => G (p.1, z))
      ((fderiv ℝ G (p.1, p.2)).comp
        ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ)))) p.2 :=
    (hG (p.1, p.2)).hasFDerivAt.comp p.2 h1
  rw [h2.fderiv]
  simp

lemma continuous_slice_fderiv {G : ℝ × (ℝ × ℝ) → F} (hG : ContDiff ℝ 1 G) (w : ℝ × ℝ) :
    Continuous (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ (fun z => G (p.1, z)) p.2 w) := by
  have hd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have heq : (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ (fun z => G (p.1, z)) p.2 w) =
      fun p => fderiv ℝ G p (0, w) :=
    funext fun p => fderiv_slice_eq hd p w
  rw [heq]
  exact (hG.continuous_fderiv one_ne_zero).clm_apply continuous_const

lemma measurable_slice1 {G : ℝ × (ℝ × ℝ) → F} (hG : Continuous G) (w : ℝ × ℝ) :
    Measurable (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ (fun z => G (p.1, z)) p.2 w) :=
  measurable_fderiv_apply_const_with_param ℝ (f := fun t z => G (t, z)) hG w

lemma measurable_slice2 {G : ℝ × (ℝ × ℝ) → F} (hG : ContDiff ℝ 1 G) (b a : ℝ × ℝ) :
    Measurable (fun p : ℝ × (ℝ × ℝ) =>
      fderiv ℝ (fun y => fderiv ℝ (fun z => G (p.1, z)) y b) p.2 a) :=
  measurable_fderiv_apply_const_with_param ℝ
    (f := fun t y => fderiv ℝ (fun z => G (t, z)) y b) (continuous_slice_fderiv hG b) a

lemma measurable_log_chart : Measurable (fun p : ℝ × (ℝ × ℝ) => (Real.log p.1, p.2)) :=
  (Real.measurable_log.comp measurable_fst).prodMk measurable_snd

/-! ## 2. The exponential reparametrisation of the train -/

/-- The velocity of a train at age `exp t`, as a function of `(t, x)`. -/
def trainVReparam {ν c : ℝ} (T : UnforcedLeray.B0140.TrainSol ν c) :
    ℝ × (ℝ × ℝ) → ℝ × ℝ :=
  fun q => (T.v (Real.exp q.1) q.2 0, T.v (Real.exp q.1) q.2 1)

/-- The pressure of a train at age `exp t`, as a function of `(t, x)`. -/
def trainPReparam {ν c : ℝ} (T : UnforcedLeray.B0140.TrainSol ν c) :
    ℝ × (ℝ × ℝ) → ℝ :=
  fun q => T.p (Real.exp q.1) q.2

lemma contDiff_train_v {ν c : ℝ} (T : UnforcedLeray.B0140.TrainSol ν c) :
    ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => T.v (Real.exp q.1) q.2) := by
  have hf : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => (Real.exp q.1, q.2)) :=
    (Real.contDiff_exp.comp contDiff_fst).prodMk contDiff_snd
  have hmaps : MapsTo (fun q : ℝ × (ℝ × ℝ) => (Real.exp q.1, q.2)) univ (Ici 0 ×ˢ univ) :=
    fun q _ => ⟨(Real.exp_pos q.1).le, mem_univ _⟩
  exact contDiffOn_univ.mp (T.isTrain.smooth_v.comp hf.contDiffOn hmaps)

lemma contDiff_train_p {ν c : ℝ} (T : UnforcedLeray.B0140.TrainSol ν c) :
    ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => T.p (Real.exp q.1) q.2) := by
  have hf : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => (Real.exp q.1, q.2)) :=
    (Real.contDiff_exp.comp contDiff_fst).prodMk contDiff_snd
  have hmaps : MapsTo (fun q : ℝ × (ℝ × ℝ) => (Real.exp q.1, q.2)) univ (Ici 0 ×ˢ univ) :=
    fun q _ => ⟨(Real.exp_pos q.1).le, mem_univ _⟩
  exact contDiffOn_univ.mp (T.isTrain.smooth_p.comp hf.contDiffOn hmaps)

lemma contDiff_trainVReparam {ν c : ℝ} (T : UnforcedLeray.B0140.TrainSol ν c) :
    ContDiff ℝ ∞ (trainVReparam T) := by
  have hV := contDiff_train_v T
  refine ContDiff.prodMk ?_ ?_
  · exact (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hV
  · exact (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hV

/-! ## 3. Measurability of the coefficient matrices -/

lemma measurable_Lpt (c ν ε μ : ℝ) (χo χy : ℝ → ℝ) (M : Chart → Mat3) :
    Measurable (Lpt c ν ε μ χo χy M) := by
  unfold Lpt
  have hS : MeasurableSet {s : ℝ | 0 < s} := measurableSet_Ioi
  refine Measurable.ite hS ?_ measurable_const
  refine measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j => ?_))
  have hpt : Measurable (fun s : ℝ => (![ε⁻¹ / Real.sqrt s, 0, 0] : Vec3)) := by
    refine measurable_pi_lambda _ (fun k => ?_)
    fin_cases k <;> simp <;> fun_prop
  exact (measurable_pi_apply i).comp
    ((measurable_fderiv_apply_const ℝ (Xmt c ν ε μ χo χy M) (Pi.single j 1)).comp hpt)

lemma measurable_LjFun (c mZ ρb γ ν ε μ : ℝ) (χo χy : ℝ → ℝ) (T : StrG c mZ ρb γ ν) :
    Measurable (LjFun c mZ ρb γ ν ε μ χo χy T) :=
  measurable_Lpt c ν ε μ χo χy (thinRep T)

lemma measurable_mat_entry (i j : Fin 3) : Measurable (fun M : Mat3 => M i j) :=
  (measurable_pi_apply j).comp (measurable_pi_apply i)

lemma measurable_Ay_Bmat (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (hχ : Measurable χ)
    (hA : Measurable A) :
    Measurable (Ay ν χ A) ∧ Measurable (Bmat ν μ χ A) := by
  have hAy : Measurable (Ay ν χ A) :=
    (hχ.comp (measurable_const.mul measurable_id)).smul hA
  refine ⟨hAy, ?_⟩
  exact (measurable_deriv (Ay ν χ A)).add ((measurable_const.div measurable_id).smul hAy)

/-! ## 4. Algebraic maps -/

lemma continuous_mv : Continuous (fun q : Mat3 × Vec3 => mv q.1 q.2) := by
  unfold mv
  fun_prop

lemma continuous_emb : Continuous emb := by
  unfold emb
  fun_prop

lemma measurable_merOf : Measurable merOf := by
  have h : Continuous merOf := by
    unfold merOf
    fun_prop
  exact h.measurable

/-! ## 5. The affine expression along the reparametrised train -/

lemma measurable_ringAffGen (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (hχ : Measurable χ)
    (hA : Measurable A) (G : ℝ × (ℝ × ℝ) → ℝ × ℝ) (hG : ContDiff ℝ 1 G)
    (H : ℝ × (ℝ × ℝ) → ℝ) (hH : ContDiff ℝ 1 H) :
    Measurable (fun p : Chart =>
      ringAffGen ν μ χ A (fun s x => G (Real.log s, x)) (fun s x => H (Real.log s, x)) p.1 p.2) := by
  unfold ringAffGen
  obtain ⟨hAy, hB⟩ := measurable_Ay_Bmat ν μ χ A hχ hA
  have hΦ := measurable_log_chart
  have hGc : Measurable (fun p : Chart => G (Real.log p.1, p.2)) := hG.continuous.measurable.comp hΦ
  have hBs : Measurable (fun p : Chart => Bmat ν μ χ A p.1) := hB.comp measurable_fst
  have hAys : Measurable (fun p : Chart => Ay ν χ A p.1) := hAy.comp measurable_fst
  have hT1 : Measurable (fun p : Chart =>
      mv (Bmat ν μ χ A p.1) (emb (G (Real.log p.1, p.2)))) :=
    continuous_mv.measurable.comp (hBs.prodMk (continuous_emb.measurable.comp hGc))
  have hD : ∀ a b : Fin 2, Measurable (fun p : Chart =>
      fderiv ℝ (fun y => fderiv ℝ (fun z => G (Real.log p.1, z)) y (ei b)) p.2 (ei a)) :=
    fun a b => (measurable_slice2 hG (ei b) (ei a)).comp hΦ
  have hM : ∀ a b : Fin 2, Measurable (fun p : Chart => Ay ν χ A p.1 (mi a) (mi b)) :=
    fun a b => (measurable_mat_entry (mi a) (mi b)).comp hAys
  have hHess : Measurable (fun p : Chart =>
      hessContr (Ay ν χ A p.1) (fun z => G (Real.log p.1, z)) p.2) := by
    unfold hessContr
    exact continuous_emb.measurable.comp
      (Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => (hM a b).smul (hD a b))
  have hMg : Measurable (fun p : Chart =>
      mgrad (fun z => H (Real.log p.1, z)) p.2) :=
    ((measurable_slice1 hH.continuous (ei 0)).comp hΦ).prodMk
      ((measurable_slice1 hH.continuous (ei 1)).comp hΦ)
  have hSym : Measurable (fun p : Chart =>
      (fun a b => Ay ν χ A p.1 a b + Ay ν χ A p.1 b a)) :=
    measurable_pi_lambda _ (fun a => measurable_pi_lambda _ (fun b =>
      ((measurable_mat_entry a b).comp hAys).add ((measurable_mat_entry b a).comp hAys)))
  have hT3 : Measurable (fun p : Chart =>
      mv (fun a b => Ay ν χ A p.1 a b + Ay ν χ A p.1 b a)
        (emb (mgrad (fun z => H (Real.log p.1, z)) p.2))) :=
    continuous_mv.measurable.comp (hSym.prodMk (continuous_emb.measurable.comp hMg))
  exact ((hT1.const_smul (2 : ℝ)).add (hHess.const_smul (2 * ν))).sub hT3

lemma measurable_ringAffCoef (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (hχ : Measurable χ)
    (hA : Measurable A) (G : ℝ × (ℝ × ℝ) → ℝ × ℝ) (hG : ContDiff ℝ 1 G)
    (H : ℝ × (ℝ × ℝ) → ℝ) (hH : ContDiff ℝ 1 H) :
    Measurable (fun p : Chart =>
      ringAffCoef ν μ χ A (fun s x => G (Real.log s, x)) (fun s x => H (Real.log s, x)) p) := by
  unfold ringAffCoef
  have hsqrt : Measurable (fun p : Chart => (Real.sqrt p.1)⁻¹) :=
    (Real.continuous_sqrt.measurable.comp measurable_fst).inv
  have hpow : Measurable (fun p : Chart => p.1 ^ (3 / 2 : ℝ)) := measurable_fst.pow_const _
  have hR := measurable_ringAffGen ν μ χ A hχ hA G hG H hH
  exact measurable_merOf.comp (hsqrt.smul (hpow.smul hR))

lemma ringAffCoef_congr (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3)
    (vv vv' : ℝ → ℝ × ℝ → ℝ × ℝ) (pp pp' : ℝ → ℝ × ℝ → ℝ) (p : Chart)
    (hv : vv p.1 = vv' p.1) (hp : pp p.1 = pp' p.1) :
    ringAffCoef ν μ χ A vv pp p = ringAffCoef ν μ χ A vv' pp' p := by
  unfold ringAffCoef ringAffGen
  rw [hv, hp]

/-- **Measurability of the ring expression** (source 5466-5483): `ringAff` agrees `srcMeasure`-a.e.
with a measurable function built from the reparametrised train. -/
theorem ringAff_aesm (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (T : LStr Pl K L) (hχ : Measurable K.χf) :
    AEStronglyMeasurable (ringAff Pl K L μ T) (srcMeasure (cOf L.ν)) := by
  have hG : ContDiff ℝ 1 (trainVReparam L.train) :=
    (contDiff_trainVReparam L.train).of_le (by exact_mod_cast le_top)
  have hH : ContDiff ℝ 1 (trainPReparam L.train) :=
    (contDiff_train_p L.train).of_le (by exact_mod_cast le_top)
  have hF := measurable_ringAffCoef L.ν μ K.χf
    (LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T)
    hχ (measurable_LjFun _ _ _ _ _ _ _ _ _ T) (trainVReparam L.train) hG (trainPReparam L.train) hH
  refine hF.aestronglyMeasurable.congr ?_
  filter_upwards [ae_srcMeasure_fst_pos (cOf L.ν)] with p hp
  have hv : (fun s x => trainVReparam L.train (Real.log s, x)) p.1 = trainV L p.1 := by
    funext x
    simp [trainV, trainVReparam, Real.exp_log hp]
  have hpp : (fun s x => trainPReparam L.train (Real.log s, x)) p.1 = trainP L p.1 := by
    funext x
    simp [trainP, trainPReparam, Real.exp_log hp]
  exact ringAffCoef_congr L.ν μ K.χf _ (fun s x => trainVReparam L.train (Real.log s, x))
    (trainV L) (fun s x => trainPReparam L.train (Real.log s, x)) (trainP L) p hv hpp

end GRMeasAux

open GRMeasAux

/-- **`PartIII-b:C/rep/8/3/1`**: the ring expression is measurable (source 5466-5483). -/
theorem grMeas_proof (D : SeqData) : D.GRMeas := by
  unfold SeqData.GRMeas
  intro hchi
  have hm : Measurable D.K.χf := hchi.smooth.continuous.measurable
  apply Filter.Eventually.of_forall
  intro n z _ T
  exact ringAff_aesm D.Pl D.K (D.level n) (D.mu n z) T hm

end UnforcedLeray.Short.PartIIIb.Concrete
