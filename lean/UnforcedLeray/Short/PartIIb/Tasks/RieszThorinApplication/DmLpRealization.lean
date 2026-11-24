import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T18
import UnforcedLeray.Lib.AxisymmetricB.Jv

/-!
# Part II-b, Task `PartII-b:T18/2`: `DmLpRealizationOfHrOperator`

Source of record: `the November 2 reference manuscript` (SP), lines 1903-1908
and 1994-2003.

Conjugates a consistent profile-level comparison operator `K_op : CProf → CProf` (`IsHrCompFamily c K_op`)
by the weight multiplication isometry `P ↦ sqrtS P` between `(InHr c r, hNorm c r)` and
`DmLp c q = Lp CMerid q (dm c)` for `(r, q) ∈ {(2, 2), (bgr, 23/8), (bgp, 11/4)}`, producing
continuous `ℂ`-linear operators `T₂, T_r, T_p` satisfying `DmOperatorConsistency c T₂ T_r T_p`
and matching operator-norm characterizations.
-/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

namespace DmLpRealizationHelp

/-- Inverse weight multiplication `M⁻¹ g (s, q, η) = (√s)⁻¹ g(s, cellRep c q, η)`, periodic in `q`
everywhere by construction. -/
def unweight (c : ℝ) (g : Coord → CMerid) : CProf :=
  fun x => ((Real.sqrt x.1)⁻¹ : ℂ) • g (x.1, (Axi.cellRep c x.2.1, x.2.2))

lemma ageμ_ac (c a b : ℝ) : Axi.ageμ c a ≪ Axi.ageμ c b := by
  have : SFinite (Cyl.avgμ c) := by unfold Cyl.avgμ; infer_instance
  have hw : AEMeasurable (fun s : ℝ => ENNReal.ofReal (s ^ b))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (Axi.measurable_ofReal_rpow b).aemeasurable
  have hne : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ENNReal.ofReal (s ^ b) ≠ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hs b)).ne'
  have h1 : (volume.restrict (Ioi (0 : ℝ))).withDensity (fun s => ENNReal.ofReal (s ^ a)) ≪
      (volume.restrict (Ioi (0 : ℝ))).withDensity fun s => ENNReal.ofReal (s ^ b) :=
    (withDensity_absolutelyContinuous _ _).trans (withDensity_absolutelyContinuous' hw hne)
  exact h1.prod (Measure.AbsolutelyContinuous.refl (Cyl.avgμ c))

lemma dm_ac_hMeas (c r : ℝ) : dm c ≪ hMeas c r :=
  ageμ_ac c (-5 / 2) (r / 2 - 5 / 2)

lemma hMeas_ac_dm (c r : ℝ) : hMeas c r ≪ dm c :=
  ageμ_ac c (r / 2 - 5 / 2) (-5 / 2)

lemma ae_eq_hMeas_of_dm {c r : ℝ} {f g : CProf} (h : f =ᵐ[dm c] g) :
    f =ᵐ[hMeas c r] g :=
  (hMeas_ac_dm c r).ae_eq h

lemma ae_eq_dm_of_hMeas {c r : ℝ} {f g : CProf} (h : f =ᵐ[hMeas c r] g) :
    f =ᵐ[dm c] g :=
  (dm_ac_hMeas c r).ae_eq h

lemma aestronglyMeasurable_hMeas_iff_dm (c r : ℝ) {f : CProf} :
    AEStronglyMeasurable f (hMeas c r) ↔ AEStronglyMeasurable f (dm c) :=
  ⟨fun h => h.mono_ac (dm_ac_hMeas c r), fun h => h.mono_ac (hMeas_ac_dm c r)⟩

lemma qPeriodic_unweight {c : ℝ} (hc : 0 < c) (g : Coord → CMerid) :
    QPeriodic c (unweight c g) := by
  refine Eventually.of_forall fun x => ?_
  simp only [unweight, qShift, Axi.cellRep_add hc.ne']

lemma unweight_ae_eq {c : ℝ} (hc : 0 < c) (a : ℝ) (g : Coord → CMerid) :
    unweight c g =ᵐ[Axi.ageμ c a] fun x => ((Real.sqrt x.1)⁻¹ : ℂ) • g x := by
  filter_upwards [Axi.ae_ageμ_mem hc a] with x hx
  simp only [unweight, Axi.cellRep_of_mem hc hx.2.1]

lemma unweight_congr_ae {c : ℝ} (hc : 0 < c) {g₁ g₂ : Coord → CMerid}
    (h : g₁ =ᵐ[dm c] g₂) : unweight c g₁ =ᵐ[dm c] unweight c g₂ := by
  refine (unweight_ae_eq hc (-5 / 2) g₁).trans ( EventuallyEq.trans ?_
    (unweight_ae_eq hc (-5 / 2) g₂).symm )
  filter_upwards [h] with x hx
  rw [hx]

lemma sqrtS_congr_ae {μ : Measure Coord} {P₁ P₂ : CProf} (h : P₁ =ᵐ[μ] P₂) :
    sqrtS P₁ =ᵐ[μ] sqrtS P₂ := by
  filter_upwards [h] with x hx
  simp only [sqrtS, hx]

lemma sqrtS_unweight_ae {c : ℝ} (hc : 0 < c) (a : ℝ) (g : Coord → CMerid) :
    sqrtS (unweight c g) =ᵐ[Axi.ageμ c a] g := by
  filter_upwards [Axi.ae_ageμ_mem hc a] with x hx
  have hs0 : (Real.sqrt x.1 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hx.1).ne'
  simp only [sqrtS, unweight, Axi.cellRep_of_mem hc hx.2.1, smul_smul,
    mul_inv_cancel₀ hs0, one_smul]

lemma unweight_sqrtS_ae {c : ℝ} (hc : 0 < c) (a : ℝ) (P : CProf) :
    unweight c (sqrtS P) =ᵐ[Axi.ageμ c a] P := by
  filter_upwards [Axi.ae_ageμ_mem hc a] with x hx
  have hs0 : (Real.sqrt x.1 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hx.1).ne'
  simp only [unweight, sqrtS, Axi.cellRep_of_mem hc hx.2.1, smul_smul,
    inv_mul_cancel₀ hs0, one_smul]

lemma aestronglyMeasurable_sqrtS_dm {c r : ℝ} {P : CProf}
    (hP : AEStronglyMeasurable P (hMeas c r)) :
    AEStronglyMeasurable (sqrtS P) (dm c) := by
  have hP' : AEStronglyMeasurable P (dm c) :=
    (aestronglyMeasurable_hMeas_iff_dm c r).1 hP
  have hsc : Measurable fun x : Coord => (Real.sqrt x.1 : ℂ) :=
    Complex.continuous_ofReal.measurable.comp
      (Real.continuous_sqrt.measurable.comp measurable_fst)
  exact hsc.aestronglyMeasurable.smul hP'

lemma aestronglyMeasurable_unweight_hMeas {c : ℝ} (hc : 0 < c) (r : ℝ) {g : Coord → CMerid}
    (hg : AEStronglyMeasurable g (dm c)) :
    AEStronglyMeasurable (unweight c g) (hMeas c r) := by
  rw [aestronglyMeasurable_hMeas_iff_dm]
  have hsc : Measurable fun x : Coord => ((Real.sqrt x.1)⁻¹ : ℂ) :=
    (Complex.continuous_ofReal.measurable.comp
      (Real.continuous_sqrt.measurable.comp measurable_fst)).inv
  exact (hsc.aestronglyMeasurable.smul hg).congr (unweight_ae_eq hc (-5 / 2) g).symm

lemma lintegral_sqrtS {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) {P : CProf} (hP : Measurable P) :
    ∫⁻ p, ‖sqrtS P p‖ₑ ^ r ∂dm c = ∫⁻ p, ‖P p‖ₑ ^ r ∂hMeas c r := by
  have hsm : Measurable (sqrtS P) :=
    (Complex.continuous_ofReal.measurable.comp
      (Real.continuous_sqrt.measurable.comp measurable_fst)).smul hP
  rw [dm, hMeas, Axi.lintegral_ageμ hc _ (hsm.enorm.pow_const r),
    Axi.lintegral_ageμ hc _ (hP.enorm.pow_const r)]
  refine setLIntegral_congr_fun (Axi.measurableSet_halfCell c) fun p hp => ?_
  have hs : 0 < p.1 := hp.1
  have hnorm : ‖sqrtS P p‖ = Real.sqrt p.1 * ‖P p‖ := by
    simp only [sqrtS, norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  rw [← ofReal_norm, hnorm, ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    ENNReal.mul_rpow_of_nonneg _ _ hr,
    ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) hr,
    Axi.sqrt_rpow hs.le r, ofReal_norm,
    show (-5 / 2 : ℝ) = -(5 / 2) by ring,
    Axi.ofReal_density_mul hc hs (r / 2) (‖P p‖ₑ ^ r)]

lemma eLpNorm_sqrtS_eq_hNorm {c r : ℝ} (hc : 0 < c) (hr : 0 < r) {P : CProf}
    (hP : AEStronglyMeasurable P (hMeas c r)) :
    eLpNorm (sqrtS P) (ENNReal.ofReal r) (dm c) = hNorm c r P := by
  set P₀ : CProf := hP.mk P
  have hP₀m : Measurable P₀ := hP.stronglyMeasurable_mk.measurable
  have hP₀_h : P =ᵐ[hMeas c r] P₀ := hP.ae_eq_mk
  have hP₀_dm : sqrtS P =ᵐ[dm c] sqrtS P₀ :=
    sqrtS_congr_ae (ae_eq_dm_of_hMeas hP₀_h)
  rw [hNorm, eLpNorm_congr_ae hP₀_dm, eLpNorm_congr_ae hP₀_h]
  have h0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr).ne'
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h0 ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal h0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hr.le, lintegral_sqrtS hc hr.le hP₀m]

lemma hNorm_unweight_eq_eLpNorm {c r : ℝ} (hc : 0 < c) (hr : 0 < r) {g : Coord → CMerid}
    (hg : AEStronglyMeasurable g (dm c)) :
    hNorm c r (unweight c g) = eLpNorm g (ENNReal.ofReal r) (dm c) := by
  rw [← eLpNorm_sqrtS_eq_hNorm hc hr (aestronglyMeasurable_unweight_hMeas hc r hg)]
  exact eLpNorm_congr_ae (sqrtS_unweight_ae hc (-5 / 2) g)

lemma inHr_unweight_of_memLp {c r : ℝ} (hc : 0 < c) (hr : 0 < r) {q : ℝ≥0∞}
    (hq : q = ENNReal.ofReal r) {g : Coord → CMerid} (hg : MemLp g q (dm c)) :
    InHr c r (unweight c g) := by
  refine ⟨qPeriodic_unweight hc g, aestronglyMeasurable_unweight_hMeas hc r hg.1, ?_⟩
  rw [hNorm_unweight_eq_eLpNorm hc hr hg.1, ← hq]
  exact hg.2

lemma memLp_sqrtS_of_inHr {c r : ℝ} (hc : 0 < c) (hr : 0 < r) {q : ℝ≥0∞}
    (hq : q = ENNReal.ofReal r) {P : CProf} (hP : AEStronglyMeasurable P (hMeas c r))
    (hfin : hNorm c r P < ⊤) :
    MemLp (sqrtS P) q (dm c) := by
  refine ⟨aestronglyMeasurable_sqrtS_dm hP, ?_⟩
  rw [hq, eLpNorm_sqrtS_eq_hNorm hc hr hP]
  exact hfin

lemma sqrtS_add (P₁ P₂ : CProf) : sqrtS (P₁ + P₂) = sqrtS P₁ + sqrtS P₂ := by
  ext x i
  simp [sqrtS, smul_add]

lemma sqrtS_smul (a : ℂ) (P : CProf) : sqrtS (a • P) = a • sqrtS P := by
  ext x : 1
  exact smul_comm (Real.sqrt x.1 : ℂ) a (P x)

/-- Construct the conjugated continuous linear map on `DmLp c q` at exponent `(r, q)`. -/
def mkDmOp {c r : ℝ} (hc : 0 < c) (hr_mem : r ∈ ({2, bgr, bgp} : Set ℝ)) (hr : 0 < r)
    {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : q = ENNReal.ofReal r)
    {K_op : CProf → CProf} (hfam : IsHrCompFamily c K_op)
    {M₀ : ℝ} (hM₀ : 0 ≤ M₀)
    (hbd₀ : ∀ F : CProf, InHr c r F → hNorm c r (K_op F) ≤ ENNReal.ofReal M₀ * hNorm c r F) :
    DmLp c q →L[ℂ] DmLp c q := by
  have hmem : ∀ f : DmLp c q, MemLp (sqrtS (K_op (unweight c f))) q (dm c) := by
    intro f
    have hIn : InHr c r (unweight c f) := inHr_unweight_of_memLp hc hr hq (Lp.memLp f)
    have hmeas : AEStronglyMeasurable (K_op (unweight c f)) (hMeas c r) :=
      hfam.meas r hr_mem (unweight c f) hIn
    have hle := hbd₀ (unweight c f) hIn
    have hfin : hNorm c r (K_op (unweight c f)) < ⊤ :=
      lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hIn.finite)
    exact memLp_sqrtS_of_inHr hc hr hq hmeas hfin
  refine LinearMap.mkContinuous
    { toFun := fun f => (hmem f).toLp (sqrtS (K_op (unweight c f)))
      map_add' := fun f₁ f₂ => by
        apply Lp.ext
        have hIn₁ : InHr c r (unweight c f₁) := inHr_unweight_of_memLp hc hr hq (Lp.memLp f₁)
        have hIn₂ : InHr c r (unweight c f₂) := inHr_unweight_of_memLp hc hr hq (Lp.memLp f₂)
        have hIn₁₂ : InHr c r (unweight c (f₁ + f₂ : DmLp c q)) :=
          inHr_unweight_of_memLp hc hr hq (Lp.memLp (f₁ + f₂))
        have hIn_sum : InHr c r (unweight c f₁ + unweight c f₂) := by
          refine ⟨?_, hIn₁.meas.add hIn₂.meas, ?_⟩
          · filter_upwards [hIn₁.periodic, hIn₂.periodic] with x hx₁ hx₂
            simp [hx₁, hx₂]
          · exact lt_of_le_of_lt (eLpNorm_add_le hIn₁.meas hIn₂.meas (by
              rw [← hq]; exact Fact.out)) (ENNReal.add_lt_top.2 ⟨hIn₁.finite, hIn₂.finite⟩)
        have hunw : unweight c (f₁ + f₂ : DmLp c q) =ᵐ[dm c] unweight c f₁ + unweight c f₂ := by
          refine (unweight_ae_eq hc (-5 / 2) _).trans ?_
          filter_upwards [Lp.coeFn_add f₁ f₂, unweight_ae_eq hc (-5 / 2) f₁,
            unweight_ae_eq hc (-5 / 2) f₂] with x hx h₁ h₂
          rw [Pi.add_apply, h₁, h₂, hx, Pi.add_apply, smul_add]
        have hK₁ := hfam.congr_ae r hr_mem _ _ hIn₁₂ hIn_sum hunw
        have hK₂ := hfam.map_add_ae r hr_mem _ _ hIn₁ hIn₂
        have hK := sqrtS_congr_ae (hK₁.trans hK₂)
        rw [sqrtS_add] at hK
        filter_upwards [(hmem (f₁ + f₂)).coeFn_toLp, Lp.coeFn_add ((hmem f₁).toLp _) ((hmem f₂).toLp _),
          (hmem f₁).coeFn_toLp, (hmem f₂).coeFn_toLp, hK] with x ha hb hc₁ hc₂ hd
        rw [ha, hb, Pi.add_apply, hc₁, hc₂, hd, Pi.add_apply]
      map_smul' := fun a f => by
        apply Lp.ext
        have hIn : InHr c r (unweight c f) := inHr_unweight_of_memLp hc hr hq (Lp.memLp f)
        have hIn_af : InHr c r (unweight c (a • f : DmLp c q)) :=
          inHr_unweight_of_memLp hc hr hq (Lp.memLp (a • f))
        have hIn_smul : InHr c r (a • unweight c f) := by
          refine ⟨?_, hIn.meas.const_smul a, ?_⟩
          · filter_upwards [hIn.periodic] with x hx
            simp [hx]
          · rw [hNorm, eLpNorm_const_smul]
            exact ENNReal.mul_lt_top ENNReal.coe_lt_top hIn.finite
        have hunw : unweight c (a • f : DmLp c q) =ᵐ[dm c] a • unweight c f := by
          refine (unweight_ae_eq hc (-5 / 2) _).trans ?_
          filter_upwards [Lp.coeFn_smul a f, unweight_ae_eq hc (-5 / 2) f] with x hx h₁
          rw [Pi.smul_apply, h₁, hx, Pi.smul_apply, smul_comm]
        have hK₁ := hfam.congr_ae r hr_mem _ _ hIn_af hIn_smul hunw
        have hK₂ := hfam.map_smul_ae r hr_mem a _ hIn
        have hK := sqrtS_congr_ae (hK₁.trans hK₂)
        rw [sqrtS_smul] at hK
        simp only [RingHom.id_apply]
        filter_upwards [(hmem (a • f)).coeFn_toLp, Lp.coeFn_smul a ((hmem f).toLp _),
          (hmem f).coeFn_toLp, hK] with x ha hb hc₁ hd
        rw [ha, hb, Pi.smul_apply, hc₁, hd, Pi.smul_apply] }
    M₀ (fun f => by
      have hIn : InHr c r (unweight c f) := inHr_unweight_of_memLp hc hr hq (Lp.memLp f)
      have hmeas : AEStronglyMeasurable (K_op (unweight c f)) (hMeas c r) :=
        hfam.meas r hr_mem (unweight c f) hIn
      have hle := hbd₀ (unweight c f) hIn
      have heq₁ : eLpNorm ((hmem f).toLp (sqrtS (K_op (unweight c f)))) q (dm c) =
          hNorm c r (K_op (unweight c f)) := by
        rw [eLpNorm_congr_ae (hmem f).coeFn_toLp,
          ← eLpNorm_sqrtS_eq_hNorm hc hr hmeas, ← hq]
      have heq₂ : hNorm c r (unweight c f) = eLpNorm f q (dm c) := by
        rw [hNorm_unweight_eq_eLpNorm hc hr (Lp.aestronglyMeasurable f), ← hq]
      have hle' : eLpNorm ((hmem f).toLp (sqrtS (K_op (unweight c f)))) q (dm c) ≤
          ENNReal.ofReal M₀ * eLpNorm f q (dm c) := by
        rwa [heq₁, ← heq₂]
      rw [Lp.norm_def, Lp.norm_def, ← ENNReal.toReal_ofReal hM₀, ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.memLp f).2.ne) hle')

lemma coeFn_mkDmOp {c r : ℝ} (hc : 0 < c) (hr_mem : r ∈ ({2, bgr, bgp} : Set ℝ)) (hr : 0 < r)
    {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : q = ENNReal.ofReal r)
    {K_op : CProf → CProf} (hfam : IsHrCompFamily c K_op)
    {M₀ : ℝ} (hM₀ : 0 ≤ M₀)
    (hbd₀ : ∀ F : CProf, InHr c r F → hNorm c r (K_op F) ≤ ENNReal.ofReal M₀ * hNorm c r F)
    (f : DmLp c q) :
    (mkDmOp hc hr_mem hr hq hfam hM₀ hbd₀ f : Coord → CMerid) =ᵐ[dm c]
      sqrtS (K_op (unweight c f)) := by
  unfold mkDmOp
  simp only [LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  exact MemLp.coeFn_toLp _

lemma norm_mkDmOp_le_iff {c r : ℝ} (hc : 0 < c) (hr_mem : r ∈ ({2, bgr, bgp} : Set ℝ)) (hr : 0 < r)
    {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : q = ENNReal.ofReal r)
    {K_op : CProf → CProf} (hfam : IsHrCompFamily c K_op)
    {M₀ : ℝ} (hM₀ : 0 ≤ M₀)
    (hbd₀ : ∀ F : CProf, InHr c r F → hNorm c r (K_op F) ≤ ENNReal.ofReal M₀ * hNorm c r F)
    (M : ℝ) (hM : 0 ≤ M) :
    ‖mkDmOp hc hr_mem hr hq hfam hM₀ hbd₀‖ ≤ M ↔
      ∀ F : CProf, InHr c r F → hNorm c r (K_op F) ≤ ENNReal.ofReal M * hNorm c r F := by
  set T := mkDmOp hc hr_mem hr hq hfam hM₀ hbd₀
  constructor
  · intro hT F hF
    have hmemF : MemLp (sqrtS F) q (dm c) := memLp_sqrtS_of_inHr hc hr hq hF.meas hF.finite
    set f : DmLp c q := hmemF.toLp (sqrtS F)
    have hIn_f : InHr c r (unweight c f) := inHr_unweight_of_memLp hc hr hq (Lp.memLp f)
    have hunw : unweight c f =ᵐ[dm c] F :=
      (unweight_congr_ae hc hmemF.coeFn_toLp).trans (unweight_sqrtS_ae hc (-5 / 2) F)
    have hK_dm : K_op (unweight c f) =ᵐ[dm c] K_op F :=
      hfam.congr_ae r hr_mem _ _ hIn_f hF hunw
    have hK_h : K_op (unweight c f) =ᵐ[hMeas c r] K_op F :=
      ae_eq_hMeas_of_dm hK_dm
    have hmeas_f : AEStronglyMeasurable (K_op (unweight c f)) (hMeas c r) :=
      hfam.meas r hr_mem _ hIn_f
    have h1 : hNorm c r (K_op F) = eLpNorm (T f) q (dm c) := by
      rw [hNorm, ← eLpNorm_congr_ae hK_h, ← hNorm,
        ← eLpNorm_sqrtS_eq_hNorm hc hr hmeas_f, ← hq,
        eLpNorm_congr_ae (coeFn_mkDmOp hc hr_mem hr hq hfam hM₀ hbd₀ f).symm]
    have h2 : hNorm c r F = eLpNorm f q (dm c) := by
      rw [← eLpNorm_sqrtS_eq_hNorm hc hr hF.meas, ← hq,
        eLpNorm_congr_ae hmemF.coeFn_toLp.symm]
    rw [h1, h2, ← Lp.enorm_def, ← Lp.enorm_def, ← ofReal_norm, ← ofReal_norm,
      ← ENNReal.ofReal_mul hM]
    exact ENNReal.ofReal_le_ofReal ((T.le_opNorm f).trans
      (mul_le_mul_of_nonneg_right hT (norm_nonneg f)))
  · intro hbd
    refine ContinuousLinearMap.opNorm_le_bound _ hM fun f => ?_
    have hIn : InHr c r (unweight c f) := inHr_unweight_of_memLp hc hr hq (Lp.memLp f)
    have hmeas : AEStronglyMeasurable (K_op (unweight c f)) (hMeas c r) :=
      hfam.meas r hr_mem (unweight c f) hIn
    have hle := hbd (unweight c f) hIn
    have heq₁ : eLpNorm (T f) q (dm c) = hNorm c r (K_op (unweight c f)) := by
      rw [eLpNorm_congr_ae (coeFn_mkDmOp hc hr_mem hr hq hfam hM₀ hbd₀ f),
        ← eLpNorm_sqrtS_eq_hNorm hc hr hmeas, ← hq]
    have heq₂ : hNorm c r (unweight c f) = eLpNorm f q (dm c) := by
      rw [hNorm_unweight_eq_eLpNorm hc hr (Lp.aestronglyMeasurable f), ← hq]
    have hle' : eLpNorm (T f) q (dm c) ≤ ENNReal.ofReal M * eLpNorm f q (dm c) := by
      rwa [heq₁, ← heq₂]
    rw [Lp.norm_def, Lp.norm_def, ← ENNReal.toReal_ofReal hM, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.memLp f).2.ne) hle'

end DmLpRealizationHelp

open DmLpRealizationHelp in
theorem dmLpRealizationOfHrOperator_proof : UnforcedLeray.Short.IIb.DmLpRealizationOfHrOperator := by
  intro c hc K_op hfam ⟨M₂, hM₂0, hbd₂⟩ ⟨M_r, hMr0, hbdr⟩ ⟨M_p, hMp0, hbdp⟩
  have hm2 : (2 : ℝ) ∈ ({2, bgr, bgp} : Set ℝ) := by simp
  have hmr : bgr ∈ ({2, bgr, bgp} : Set ℝ) := by simp
  have hmp : bgp ∈ ({2, bgr, bgp} : Set ℝ) := by simp
  have hr2 : (0 : ℝ) < 2 := by norm_num
  have hrr : (0 : ℝ) < bgr := by unfold bgr; norm_num
  have hrp : (0 : ℝ) < bgp := by unfold bgp; norm_num
  have hq2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  have hqr : (23 / 8 : ℝ≥0∞) = ENNReal.ofReal bgr := by
    unfold bgr
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    simp
  have hqp : (11 / 4 : ℝ≥0∞) = ENNReal.ofReal bgp := by
    unfold bgp
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    simp
  set T₂ := mkDmOp hc hm2 hr2 hq2 hfam hM₂0 hbd₂
  set T_r := mkDmOp hc hmr hrr hqr hfam hMr0 hbdr
  set T_p := mkDmOp hc hmp hrp hqp hfam hMp0 hbdp
  refine ⟨T₂, T_r, T_p,
    norm_mkDmOp_le_iff hc hm2 hr2 hq2 hfam hM₂0 hbd₂,
    norm_mkDmOp_le_iff hc hmr hrr hqr hfam hMr0 hbdr,
    norm_mkDmOp_le_iff hc hmp hrp hqp hfam hMp0 hbdp, ?_⟩
  intro S hS hSμ v
  set f₂ := indicatorConstLp (2 : ℝ≥0∞) hS hSμ v
  set f_r := indicatorConstLp (23 / 8 : ℝ≥0∞) hS hSμ v
  set f_p := indicatorConstLp (11 / 4 : ℝ≥0∞) hS hSμ v
  have hIn₂ : InHr c 2 (unweight c f₂) := inHr_unweight_of_memLp hc hr2 hq2 (Lp.memLp f₂)
  have hf_p2 : (f_p : Coord → CMerid) =ᵐ[dm c] (f₂ : Coord → CMerid) :=
    (indicatorConstLp_coeFn).trans (indicatorConstLp_coeFn).symm
  have hf_r2 : (f_r : Coord → CMerid) =ᵐ[dm c] (f₂ : Coord → CMerid) :=
    (indicatorConstLp_coeFn).trans (indicatorConstLp_coeFn).symm
  have hunw_p2 : unweight c f_p =ᵐ[dm c] unweight c f₂ := unweight_congr_ae hc hf_p2
  have hunw_r2 : unweight c f_r =ᵐ[dm c] unweight c f₂ := unweight_congr_ae hc hf_r2
  have hIn_p2 : InHr c 2 (unweight c f_p) := by
    refine ⟨qPeriodic_unweight hc f_p,
      hIn₂.meas.congr (ae_eq_hMeas_of_dm hunw_p2.symm), ?_⟩
    rw [hNorm, eLpNorm_congr_ae (ae_eq_hMeas_of_dm hunw_p2)]
    exact hIn₂.finite
  have hIn_r2 : InHr c 2 (unweight c f_r) := by
    refine ⟨qPeriodic_unweight hc f_r,
      hIn₂.meas.congr (ae_eq_hMeas_of_dm hunw_r2.symm), ?_⟩
    rw [hNorm, eLpNorm_congr_ae (ae_eq_hMeas_of_dm hunw_r2)]
    exact hIn₂.finite
  constructor
  · refine (coeFn_mkDmOp hc hmp hrp hqp hfam hMp0 hbdp f_p).trans
      (EventuallyEq.trans ?_ (coeFn_mkDmOp hc hm2 hr2 hq2 hfam hM₂0 hbd₂ f₂).symm)
    exact sqrtS_congr_ae (hfam.congr_ae 2 hm2 _ _ hIn_p2 hIn₂ hunw_p2)
  · refine (coeFn_mkDmOp hc hmr hrr hqr hfam hMr0 hbdr f_r).trans
      (EventuallyEq.trans ?_ (coeFn_mkDmOp hc hm2 hr2 hq2 hfam hM₂0 hbd₂ f₂).symm)
    exact sqrtS_congr_ae (hfam.congr_ae 2 hm2 _ _ hIn_r2 hIn₂ hunw_r2)

end UnforcedLeray.Short.IIb

end
