import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F10

/-!
# `PartII-b:F10`: Flat background inverse `R_0` on `H_p` (SP 2326-2344)

Source of record: `the November 2 reference manuscript`
(SP), lines 2326-2344 (`short-bg:flat-inverse`).

This file proves `FlatK0OperatorExists` (`PartII-b:F10/1`) and completes the unconditional proof of
`flatInverse_of : FlatReconstruction → FlatInverse` (`PartII-b:F10`) using the infrastructure in
`UnforcedLeray.Short.«PartII-b».Sub.«PartII-b_F10»`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03 UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint

namespace F10K0Help

/-- Continuous `ℝ`-linear projection `z ↦ (z.re : ℂ)` on `ℂ`. -/
def reCLM : ℂ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp Complex.reCLM

@[simp]
lemma reCLM_apply (z : ℂ) : reCLM z = (z.re : ℂ) := rfl

lemma reCLM_mul_ofReal (z : ℂ) (r : ℝ) : reCLM (z * (r : ℂ)) = reCLM z * (r : ℂ) := by
  simp [reCLM, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

/-- Pointwise real-part projection `x ↦ liftM (reM (b x))` on complex profiles. -/
def reProf (b : CProf) : CProf :=
  fun x => liftM (reM (b x))

@[simp]
lemma reProf_apply (b : CProf) (x : Coord) (i : Fin 2) :
    reProf b x i = reCLM (b x i) := by
  simp [reProf, liftM, reM, reCLM]

lemma norm_reM_le (v : CMerid) : ‖reM v‖ ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  dsimp [reM]
  exact sq_le_sq.mpr (by rw [abs_abs, abs_norm]; exact Complex.abs_re_le_norm (v i))

lemma norm_reProf_le (b : CProf) (x : Coord) : ‖reProf b x‖ ≤ ‖b x‖ := by
  unfold reProf
  rw [liftM_norm]
  exact norm_reM_le (b x)

lemma inHr_reProf {c r : ℝ} {b : CProf} (hb : InHr c r b) : InHr c r (reProf b) := by
  refine ⟨?_, (continuous_liftM.comp continuous_reM).comp_aestronglyMeasurable hb.meas, ?_⟩
  · filter_upwards [hb.periodic] with x hx
    simp only [reProf, hx]
  · refine lt_of_le_of_lt ?_ hb.finite
    exact eLpNorm_mono (norm_reProf_le b)

lemma hasWeakFO_reCLM {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ} {u g : Coord → ℂ}
    (h : HasWeakFO v d u g) :
    HasWeakFO v d (fun x => reCLM (u x)) (fun x => reCLM (g x)) := by
  refine ⟨fun φ hφ => ⟨?_, ?_⟩, fun φ hφ => ?_⟩
  · have hI := reCLM.integrable_comp (h.1 φ hφ).1
    exact hI.congr (Eventually.of_forall fun x => reCLM_mul_ofReal _ _)
  · have hI := reCLM.integrable_comp (h.1 φ hφ).2
    exact hI.congr (Eventually.of_forall fun x => reCLM_mul_ofReal _ _)
  · have he1 : (fun x => reCLM (g x) * (φ x : ℂ)) =
        fun x => reCLM (g x * (φ x : ℂ)) := by
      ext x; exact (reCLM_mul_ofReal _ _).symm
    have he2 : (fun x => reCLM (u x) * (coordTranspose v d φ x : ℂ)) =
        fun x => reCLM (u x * (coordTranspose v d φ x : ℂ)) := by
      ext x; exact (reCLM_mul_ofReal _ _).symm
    rw [he1, he2, reCLM.integral_comp_comm (h.1 φ hφ).2,
      reCLM.integral_comp_comm (h.1 φ hφ).1, h.2 φ hφ]

lemma hasWeakVec_reProf {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ} {b g : CProf}
    (h : HasWeakVec v d b g) : HasWeakVec v d (reProf b) (reProf g) := by
  intro i
  show HasWeakFO v d (fun x => reProf b x i) (fun x => reProf g x i)
  simp only [reProf_apply]
  exact hasWeakFO_reCLM (h i)

lemma reProf_sqrtS (b : CProf) : reProf (sqrtS b) = sqrtS (reProf b) := by
  funext x; ext i
  simp [reProf, liftM, reM, sqrtS, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

lemma inFlatClass_reProf {c r : ℝ} {b : CProf} (hb : InFlatClass c r b) :
    InFlatClass c r (reProf b) := by
  obtain ⟨Sb, Qb, Eb, hS, hQ, hE, hSi, hQi, hEi⟩ := hb.deriv
  refine ⟨inHr_reProf hb.inHr, reProf Sb, reProf Qb, reProf Eb,
    hasWeakVec_reProf hS, hasWeakVec_reProf hQ, hasWeakVec_reProf hE,
    inHr_reProf hSi, ?_, ?_⟩
  · rw [← reProf_sqrtS]; exact inHr_reProf hQi
  · rw [← reProf_sqrtS]; exact inHr_reProf hEi

/-- Real valuedness of `flatTranspose ν 0`: at shift `μ = 0`, `flatTranspose ν 0 Ψ x i` is a real
scalar cast to `ℂ`. -/
def flatTransposeR (ν : ℝ) (Ψ : Coord → Fin 2 → ℝ) (x : Coord) (i : Fin 2) : ℝ :=
  -Ψ x i - x.1 * cpd 0 (fun y => Ψ y i) x -
    ν * x.1 * (cpd 1 (fun y => cpd 1 (fun z => Ψ z i) y) x +
      cpd 2 (fun y => cpd 2 (fun z => Ψ z i) y) x)

lemma flatTranspose_zero_eq_ofReal (ν : ℝ) (Ψ : Coord → Fin 2 → ℝ) (x : Coord) (i : Fin 2) :
    flatTranspose ν 0 Ψ x i = (flatTransposeR ν Ψ x i : ℂ) := by
  simp [flatTranspose, flatTransposeR]

lemma isFlatResponse_reProf {ν : ℝ} {F b : CProf} (h : IsFlatResponse ν 0 F b) :
    IsFlatResponse ν 0 (reProf F) (reProf b) := by
  refine ⟨fun φ hφ => ?_, fun Ψ hΨ => ?_⟩
  · obtain ⟨hI, h0⟩ := h.solenoidal φ hφ
    have hfun : (fun x => reProf b x 0 * (cpd 1 φ x : ℂ) + reProf b x 1 * (cpd 2 φ x : ℂ)) =
        fun x => reCLM (b x 0 * (cpd 1 φ x : ℂ) + b x 1 * (cpd 2 φ x : ℂ)) := by
      funext x
      simp only [reProf_apply, map_add, reCLM_mul_ofReal]
    rw [hfun]
    refine ⟨reCLM.integrable_comp hI, ?_⟩
    rw [reCLM.integral_comp_comm hI, h0, map_zero]
  · obtain ⟨hIb, hIF, heq⟩ := h.equation Ψ hΨ
    have hfunB : (fun x => ∑ i : Fin 2, reProf b x i * flatTranspose ν 0 Ψ x i) =
        fun x => reCLM (∑ i : Fin 2, b x i * flatTranspose ν 0 Ψ x i) := by
      funext x
      simp only [Fin.sum_univ_two, map_add, reProf_apply, flatTranspose_zero_eq_ofReal,
        reCLM_mul_ofReal]
    have hfunF : cdot (reProf F) Ψ = fun x => reCLM (cdot F Ψ x) := by
      funext x
      simp only [cdot, Fin.sum_univ_two, map_add, reProf_apply, reCLM_mul_ofReal]
    rw [hfunB, hfunF]
    refine ⟨reCLM.integrable_comp hIb, reCLM.integrable_comp hIF, ?_⟩
    rw [reCLM.integral_comp_comm hIb, reCLM.integral_comp_comm hIF, heq]

lemma reProf_toProf (c : ℝ) (f : HpR c) : reProf (toProf c f) = toProf c f := by
  funext x; ext i
  simp [reProf, liftM, reM, toProf]

lemma reProf_flatK {ν c : ℝ} (tr : B0140.TrainSol ν c) (b gq gη : CProf) :
    reProf (flatK tr b gq gη) = flatK tr (reProf b) (reProf gq) (reProf gη) := by
  funext x; ext i
  simp [reProf, liftM, reM, flatK, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im]

/-- For a real input `f : HpR c`, any flat response `b0` in `InFlatClass c bgp` and its weak
derivatives `b0q, b0η` produce an `hMeas c bgp`-a.e. real flat interaction `flatK tr b0 b0q b0η`. -/
lemma liftM_reM_flatK_ae {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) (f : HpR c) {b0 b0q b0η : CProf}
    (hb0_cls : InFlatClass c bgp b0)
    (hb0_resp : IsFlatResponse ν 0 (toProf c f) b0)
    (hb0q : HasWeakVec vQ0 dZero b0 b0q)
    (hb0η : HasWeakVec vEta dZero b0 b0η) :
    (fun x => liftM (reM (flatK tr b0 b0q b0η x))) =ᵐ[hMeas c bgp]
      flatK tr b0 b0q b0η := by
  have hre_cls : InFlatClass c bgp (reProf b0) := inFlatClass_reProf hb0_cls
  have hre_resp : IsFlatResponse ν 0 (toProf c f) (reProf b0) := by
    rw [← reProf_toProf c f]
    exact isFlatResponse_reProf hb0_resp
  have hb_ae_h : reProf b0 =ᵐ[hMeas c bgp] b0 :=
    flatResponse_unique_ae hν hc (inHr_toProf hc f) hre_cls hre_resp hb0_cls hb0_resp
  have hb_vol : ∀ᵐ x : Coord, 0 < x.1 → reProf b0 x = b0 x :=
    CongrHelp.ae_volume_of_ageμ hc hre_cls.inHr.periodic hb0_cls.inHr.periodic hb_ae_h
  have hb_vol' : ∀ᵐ x : Coord, 0 < x.1 → b0 x = reProf b0 x :=
    hb_vol.mono fun _ hx hpos => (hx hpos).symm
  have hq_re : HasWeakVec vQ0 dZero b0 (reProf b0q) :=
    hasWeakVec_congr hb_vol' (Eventually.of_forall fun _ _ => rfl) (hasWeakVec_reProf hb0q)
  have hη_re : HasWeakVec vEta dZero b0 (reProf b0η) :=
    hasWeakVec_congr hb_vol' (Eventually.of_forall fun _ _ => rfl) (hasWeakVec_reProf hb0η)
  have hq_vol : ∀ᵐ x : Coord, 0 < x.1 → reProf b0q x = b0q x :=
    GradBoundHelp.hasWeakVec_unique hq_re hb0q
  have hη_vol : ∀ᵐ x : Coord, 0 < x.1 → reProf b0η x = b0η x :=
    GradBoundHelp.hasWeakVec_unique hη_re hb0η
  have hK_vol : ∀ᵐ x : Coord, 0 < x.1 →
      liftM (reM (flatK tr b0 b0q b0η x)) = flatK tr b0 b0q b0η x := by
    filter_upwards [hb_vol, hq_vol, hη_vol] with x hb hq hη hpos
    change reProf (flatK tr b0 b0q b0η) x = flatK tr b0 b0q b0η x
    rw [reProf_flatK]
    ext m
    simp only [flatK, WithLp.ofLp_toLp, hb hpos, hq hpos, hη hpos]
  exact hMeasAe c bgp _ hc hK_vol

/-- Uniqueness of `flatK tr b gq gη` up to `hMeas c bgp`-a.e. equivalence for any two flat responses
and weak derivative pairs of the same source `F ∈ H_p`. -/
lemma flatK_unique_ae {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    (tr : B0140.TrainSol ν c) {F : CProf} (hF : InHr c bgp F)
    {b₁ gq₁ gη₁ b₂ gq₂ gη₂ : CProf}
    (hb₁_cls : InFlatClass c bgp b₁) (hb₁_resp : IsFlatResponse ν 0 F b₁)
    (hgq₁ : HasWeakVec vQ0 dZero b₁ gq₁) (hgη₁ : HasWeakVec vEta dZero b₁ gη₁)
    (hb₂_cls : InFlatClass c bgp b₂) (hb₂_resp : IsFlatResponse ν 0 F b₂)
    (hgq₂ : HasWeakVec vQ0 dZero b₂ gq₂) (hgη₂ : HasWeakVec vEta dZero b₂ gη₂) :
    flatK tr b₁ gq₁ gη₁ =ᵐ[hMeas c bgp] flatK tr b₂ gq₂ gη₂ := by
  have hb_ae_h : b₁ =ᵐ[hMeas c bgp] b₂ :=
    flatResponse_unique_ae hν hc hF hb₁_cls hb₁_resp hb₂_cls hb₂_resp
  have hb_vol : ∀ᵐ x : Coord, 0 < x.1 → b₁ x = b₂ x :=
    CongrHelp.ae_volume_of_ageμ hc hb₁_cls.inHr.periodic hb₂_cls.inHr.periodic hb_ae_h
  have hgq₁' : HasWeakVec vQ0 dZero b₁ gq₂ :=
    hasWeakVec_congr hb_vol (Eventually.of_forall fun _ _ => rfl) hgq₂
  have hgη₁' : HasWeakVec vEta dZero b₁ gη₂ :=
    hasWeakVec_congr hb_vol (Eventually.of_forall fun _ _ => rfl) hgη₂
  have hq_vol : ∀ᵐ x : Coord, 0 < x.1 → gq₁ x = gq₂ x :=
    GradBoundHelp.hasWeakVec_unique hgq₁ hgq₁'
  have hη_vol : ∀ᵐ x : Coord, 0 < x.1 → gη₁ x = gη₂ x :=
    GradBoundHelp.hasWeakVec_unique hgη₁ hgη₁'
  have hK_vol : ∀ᵐ x : Coord, 0 < x.1 → flatK tr b₁ gq₁ gη₁ x = flatK tr b₂ gq₂ gη₂ x := by
    filter_upwards [hb_vol, hq_vol, hη_vol] with x hb hq hη hpos
    ext m
    simp only [flatK, WithLp.ofLp_toLp, hb hpos, hq hpos, hη hpos]
  exact hMeasAe c bgp _ hc hK_vol

lemma sqrtS_add (b₁ b₂ : CProf) : sqrtS (fun x => b₁ x + b₂ x) = fun x => sqrtS b₁ x + sqrtS b₂ x := by
  funext x; simp [sqrtS, smul_add]

lemma sqrtS_smul (a : ℂ) (b : CProf) : sqrtS (fun x => a • b x) = fun x => a • sqrtS b x := by
  funext x; ext i; simp [sqrtS]; ring

lemma inFlatClass_add {c r : ℝ} (hr : 1 ≤ r) {b₁ b₂ : CProf}
    (h₁ : InFlatClass c r b₁) (h₂ : InFlatClass c r b₂) :
    InFlatClass c r (fun x => b₁ x + b₂ x) := by
  obtain ⟨Sb₁, Qb₁, Eb₁, hS₁, hQ₁, hE₁, hSi₁, hQi₁, hEi₁⟩ := h₁.deriv
  obtain ⟨Sb₂, Qb₂, Eb₂, hS₂, hQ₂, hE₂, hSi₂, hQi₂, hEi₂⟩ := h₂.deriv
  refine ⟨inHr_add_of hr h₁.inHr h₂.inHr,
    fun x => Sb₁ x + Sb₂ x, fun x => Qb₁ x + Qb₂ x, fun x => Eb₁ x + Eb₂ x,
    F10Help.hasWeakVec_add' hS₁ hS₂, F10Help.hasWeakVec_add' hQ₁ hQ₂,
    F10Help.hasWeakVec_add' hE₁ hE₂, inHr_add_of hr hSi₁ hSi₂, ?_, ?_⟩
  · rw [sqrtS_add]; exact inHr_add_of hr hQi₁ hQi₂
  · rw [sqrtS_add]; exact inHr_add_of hr hEi₁ hEi₂

lemma inFlatClass_smul {c r : ℝ} (a : ℂ) {b : CProf} (hb : InFlatClass c r b) :
    InFlatClass c r (fun x => a • b x) := by
  obtain ⟨Sb, Qb, Eb, hS, hQ, hE, hSi, hQi, hEi⟩ := hb.deriv
  refine ⟨inHr_const_smul_of a hb.inHr,
    fun x => a • Sb x, fun x => a • Qb x, fun x => a • Eb x,
    F10Help.hasWeakVec_smul a hS, F10Help.hasWeakVec_smul a hQ,
    F10Help.hasWeakVec_smul a hE, inHr_const_smul_of a hSi, ?_, ?_⟩
  · rw [sqrtS_smul]; exact inHr_const_smul_of a hQi
  · rw [sqrtS_smul]; exact inHr_const_smul_of a hEi

lemma isFlatResponse_add {ν : ℝ} {μ : ℂ} {F₁ F₂ b₁ b₂ : CProf}
    (h₁ : IsFlatResponse ν μ F₁ b₁) (h₂ : IsFlatResponse ν μ F₂ b₂) :
    IsFlatResponse ν μ (fun x => F₁ x + F₂ x) (fun x => b₁ x + b₂ x) := by
  refine ⟨fun φ hφ => ?_, fun Ψ hΨ => ?_⟩
  · obtain ⟨i1, e1⟩ := h₁.solenoidal φ hφ
    obtain ⟨i2, e2⟩ := h₂.solenoidal φ hφ
    have hfun : (fun x : Coord => (b₁ x + b₂ x) 0 * (cpd 1 φ x : ℂ) +
        (b₁ x + b₂ x) 1 * (cpd 2 φ x : ℂ)) =
        fun x => (b₁ x 0 * (cpd 1 φ x : ℂ) + b₁ x 1 * (cpd 2 φ x : ℂ)) +
          (b₂ x 0 * (cpd 1 φ x : ℂ) + b₂ x 1 * (cpd 2 φ x : ℂ)) := by
      funext x; simp only [PiLp.add_apply]; ring
    rw [hfun]
    refine ⟨i1.add i2, ?_⟩
    rw [integral_add i1 i2, e1, e2, add_zero]
  · obtain ⟨ib1, iF1, e1⟩ := h₁.equation Ψ hΨ
    obtain ⟨ib2, iF2, e2⟩ := h₂.equation Ψ hΨ
    have hsum : (fun x : Coord => ∑ i : Fin 2, (b₁ x + b₂ x) i * flatTranspose ν μ Ψ x i) =
        fun x => (∑ i : Fin 2, b₁ x i * flatTranspose ν μ Ψ x i) +
          (∑ i : Fin 2, b₂ x i * flatTranspose ν μ Ψ x i) := by
      funext x; simp only [PiLp.add_apply, add_mul, Finset.sum_add_distrib]
    have hcdot : cdot (fun x => F₁ x + F₂ x) Ψ = fun x => cdot F₁ Ψ x + cdot F₂ Ψ x := by
      funext x; simp only [cdot, PiLp.add_apply, add_mul, Finset.sum_add_distrib]
    rw [hsum, hcdot]
    refine ⟨ib1.add ib2, iF1.add iF2, ?_⟩
    rw [integral_add ib1 ib2, integral_add iF1 iF2, e1, e2]

lemma isFlatResponse_smul {ν : ℝ} {μ : ℂ} (a : ℂ) {F b : CProf}
    (h : IsFlatResponse ν μ F b) :
    IsFlatResponse ν μ (fun x => a • F x) (fun x => a • b x) := by
  refine ⟨fun φ hφ => ?_, fun Ψ hΨ => ?_⟩
  · obtain ⟨i1, e1⟩ := h.solenoidal φ hφ
    have hfun : (fun x : Coord => (a • b x) 0 * (cpd 1 φ x : ℂ) +
        (a • b x) 1 * (cpd 2 φ x : ℂ)) =
        fun x => a * (b x 0 * (cpd 1 φ x : ℂ) + b x 1 * (cpd 2 φ x : ℂ)) := by
      funext x; simp only [PiLp.smul_apply, smul_eq_mul]; ring
    rw [hfun]
    refine ⟨i1.const_mul a, ?_⟩
    rw [integral_const_mul, e1, mul_zero]
  · obtain ⟨ib, iF, e⟩ := h.equation Ψ hΨ
    have hsum : (fun x : Coord => ∑ i : Fin 2, (a • b x) i * flatTranspose ν μ Ψ x i) =
        fun x => a * (∑ i : Fin 2, b x i * flatTranspose ν μ Ψ x i) := by
      funext x
      simp only [PiLp.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
    have hcdot : cdot (fun x => a • F x) Ψ = fun x => a * cdot F Ψ x := by
      funext x
      simp only [cdot, PiLp.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
    rw [hsum, hcdot]
    refine ⟨ib.const_mul a, iF.const_mul a, ?_⟩
    rw [integral_const_mul, integral_const_mul, e]

lemma isCoordTest_zero_of_nonpos {φ : Coord → ℝ} (hφ : IsCoordTest φ) {x : Coord} (hx : ¬ 0 < x.1) :
    φ x = 0 := by
  by_contra hne
  have hmem : x ∈ tsupport φ := subset_tsupport φ (Function.mem_support.mpr hne)
  exact hx (hφ.supp hmem).1

lemma isFlatResponse_congr_F {ν c : ℝ} {μ : ℂ} (hc : 0 < c) {F₁ F₂ b : CProf}
    (hF₁ : QPeriodic c F₁) (hF₂ : QPeriodic c F₂)
    (hae : F₁ =ᵐ[hMeas c bgp] F₂) (h : IsFlatResponse ν μ F₁ b) :
    IsFlatResponse ν μ F₂ b := by
  have hvol : ∀ᵐ x : Coord, 0 < x.1 → F₁ x = F₂ x :=
    CongrHelp.ae_volume_of_ageμ hc hF₁ hF₂ hae
  refine ⟨h.solenoidal, fun Ψ hΨ => ?_⟩
  obtain ⟨ib, iF, e⟩ := h.equation Ψ hΨ
  have hcdot_ae : cdot F₁ Ψ =ᵐ[volume] cdot F₂ Ψ := by
    filter_upwards [hvol] with x hx
    by_cases hpos : 0 < x.1
    · simp only [cdot, hx hpos]
    · have h0 : ∀ i : Fin 2, Ψ x i = 0 := fun i => isCoordTest_zero_of_nonpos (hΨ.smooth i) hpos
      simp [cdot, h0]
  refine ⟨ib, iF.congr hcdot_ae, ?_⟩
  rw [e, integral_congr_ae hcdot_ae]

lemma flatK_add {ν c : ℝ} (tr : B0140.TrainSol ν c) (b₁ gq₁ gη₁ b₂ gq₂ gη₂ : CProf) :
    flatK tr (fun x => b₁ x + b₂ x) (fun x => gq₁ x + gq₂ x) (fun x => gη₁ x + gη₂ x) =
      fun x => flatK tr b₁ gq₁ gη₁ x + flatK tr b₂ gq₂ gη₂ x := by
  funext x; ext i
  simp only [flatK, WithLp.ofLp_toLp, PiLp.add_apply]
  ring

lemma flatK_smul {ν c : ℝ} (tr : B0140.TrainSol ν c) (a : ℂ) (b gq gη : CProf) :
    flatK tr (fun x => a • b x) (fun x => a • gq x) (fun x => a • gη x) =
      fun x => a • flatK tr b gq gη x := by
  funext x; ext i
  simp only [flatK, WithLp.ofLp_toLp, PiLp.smul_apply, smul_eq_mul]
  ring

/-- Splitting `hNorm c bgp g` across `Ioc 0 H ×ˢ univ` and `Ioi H ×ˢ univ` (`0 < c`, `0 < H`). -/
lemma hNorm_le_add_restrict_Ioc_Ioi {c H : ℝ} (hc : 0 < c) {g : CProf}
    (hg : AEStronglyMeasurable g (hMeas c bgp)) :
    hNorm c bgp g ≤
      eLpNorm g (ENNReal.ofReal bgp) ((hMeas c bgp).restrict (Ioc 0 H ×ˢ univ)) +
        eLpNorm g (ENNReal.ofReal bgp) ((hMeas c bgp).restrict (Ioi H ×ˢ univ)) := by
  set S₁ : Set Coord := Ioc 0 H ×ˢ univ
  set S₂ : Set Coord := Ioi H ×ˢ univ
  have hS₁ : MeasurableSet S₁ := measurableSet_Ioc.prod MeasurableSet.univ
  have hS₂ : MeasurableSet S₂ := measurableSet_Ioi.prod MeasurableSet.univ
  have hae : g =ᵐ[hMeas c bgp] S₁.indicator g + S₂.indicator g := by
    filter_upwards [Axi.ae_ageμ_mem hc (bgp / 2 - 5 / 2)] with x hx
    have hx0 : 0 < x.1 := hx.1
    by_cases hxH : x.1 ≤ H
    · have hm1 : x ∈ S₁ := ⟨⟨hx0, hxH⟩, trivial⟩
      have hm2 : x ∉ S₂ := fun h => not_lt_of_ge hxH h.1
      simp [Pi.add_apply, hm1, hm2]
    · have hm1 : x ∉ S₁ := fun h => hxH h.1.2
      have hm2 : x ∈ S₂ := ⟨lt_of_not_ge hxH, trivial⟩
      simp [Pi.add_apply, hm1, hm2]
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal bgp :=
    ENNReal.one_le_ofReal.2 (by norm_num [bgp])
  unfold hNorm
  rw [eLpNorm_congr_ae hae]
  calc eLpNorm (S₁.indicator g + S₂.indicator g) (ENNReal.ofReal bgp) (hMeas c bgp)
      ≤ eLpNorm (S₁.indicator g) (ENNReal.ofReal bgp) (hMeas c bgp) +
          eLpNorm (S₂.indicator g) (ENNReal.ofReal bgp) (hMeas c bgp) :=
        eLpNorm_add_le (hg.indicator hS₁) (hg.indicator hS₂) hp1
    _ = eLpNorm g (ENNReal.ofReal bgp) ((hMeas c bgp).restrict S₁) +
          eLpNorm g (ENNReal.ofReal bgp) ((hMeas c bgp).restrict S₂) := by
        rw [eLpNorm_indicator_eq_eLpNorm_restrict hS₁,
          eLpNorm_indicator_eq_eLpNorm_restrict hS₂]

lemma memLp_reM_of_inHr {c : ℝ} {K : CProf} (hK : InHr c bgp K) :
    MemLp (fun x => reM (K x)) (ENNReal.ofReal bgp) (hMeas c bgp) := by
  refine ⟨continuous_reM.comp_aestronglyMeasurable hK.meas, ?_⟩
  refine lt_of_le_of_lt ?_ hK.finite
  exact eLpNorm_mono fun x => norm_reM_le (K x)

end F10K0Help

/-- **Proof of `FlatK0OperatorExists` (`PartII-b:F10/1`, SP 2326-2344)**:
given the early and late `H_p` bounds on `flatK p.train b0 b0q b0η` from `FlatReconstruction`
and flat response existence/uniqueness from `profileGraphFlat_bgp` (`PartII-b:T14`), the flat
interaction operator `K_0 = flatK p.train ∘ T_0` exists as a bounded linear operator
`K0 : HpR p.c →L[ℝ] HpR p.c` satisfying `IsK0op p K0`. -/
theorem flatK0OperatorExists_proof : FlatK0OperatorExists := by
  intro Sig lam q _hSig _hq dm dp _hdm
  refine ⟨1, zero_lt_one, ?_⟩
  intro p d _hreg _hν _hSg _hmode C k hC hK_bd
  have hc : 0 < p.c := p.c_pos
  have hν : 0 < p.ν := p.ν_pos
  have hH : 0 < p.H := p.H_pos
  have hbgp1 : (1 : ℝ) ≤ bgp := by norm_num [bgp]
  obtain ⟨_, _, H_fg⟩ := profileGraphFlat_bgp
  have hex : ∀ f : HpR p.c,
      ∃ b0 b0q b0η : CProf,
        InFlatClass p.c bgp b0 ∧
        IsFlatResponse p.ν 0 (toProf p.c f) b0 ∧
        HasWeakVec vQ0 dZero b0 b0q ∧
        HasWeakVec vEta dZero b0 b0η ∧
        InHr p.c bgp (flatK p.train b0 b0q b0η) ∧
        eLpNorm (flatK p.train b0 b0q b0η) (ENNReal.ofReal bgp)
            ((hMeas p.c bgp).restrict (Ioc 0 p.H ×ˢ univ)) ≤
          ENNReal.ofReal (C * (p.ν ^ k)⁻¹ * (p.ν ^ (-1 / 2 : ℝ) * Real.sqrt p.H + p.H)) *
            hNorm p.c bgp (toProf p.c f) ∧
        eLpNorm (flatK p.train b0 b0q b0η) (ENNReal.ofReal bgp)
            ((hMeas p.c bgp).restrict (Ioi p.H ×ˢ univ)) ≤
          ENNReal.ofReal
              (C * (p.ν ^ k)⁻¹ * p.H ^ (-1 / 2 : ℝ) * (p.ν ^ (-1 / 2 : ℝ) + 1)) *
            hNorm p.c bgp (toProf p.c f) := by
    intro f
    have hF : InHr p.c bgp (toProf p.c f) := inHr_toProf hc f
    obtain ⟨b0, hb0_cls, hb0_resp, -, -⟩ := H_fg p.ν p.c hν hc (toProf p.c f) hF
    obtain ⟨b0q, b0η, hq, hη, hKin, hbd1, hbd2⟩ :=
      hK_bd (toProf p.c f) b0 hF hb0_cls hb0_resp
    exact ⟨b0, b0q, b0η, hb0_cls, hb0_resp, hq, hη, hKin, hbd1, hbd2⟩
  choose b0Of b0qOf b0ηOf hb0_cls hb0_resp hb0q hb0η hK_inHr hK_bd1 hK_bd2 using hex
  let kFun : HpR p.c → HpR p.c := fun f =>
    (F10K0Help.memLp_reM_of_inHr (hK_inHr f)).toLp
      (fun x => reM (flatK p.train (b0Of f) (b0qOf f) (b0ηOf f) x))
  have hkFun_toProf : ∀ f : HpR p.c,
      toProf p.c (kFun f) =ᵐ[hMeas p.c bgp]
        flatK p.train (b0Of f) (b0qOf f) (b0ηOf f) := by
    intro f
    have hre := F10K0Help.liftM_reM_flatK_ae hν hc p.train f
      (hb0_cls f) (hb0_resp f) (hb0q f) (hb0η f)
    filter_upwards [toProf_ae_eq hc (kFun f),
      MemLp.coeFn_toLp (F10K0Help.memLp_reM_of_inHr (hK_inHr f)), hre]
      with x h1 h2 h3
    rw [h1, h2, h3]
  have hkFun_add : ∀ f₁ f₂ : HpR p.c, kFun (f₁ + f₂) = kFun f₁ + kFun f₂ := by
    intro f₁ f₂
    apply toProf_eq_of_ae_eq hc
    have hF_ae : (fun x => toProf p.c f₁ x + toProf p.c f₂ x) =ᵐ[hMeas p.c bgp]
        toProf p.c (f₁ + f₂) := by
      filter_upwards [toProf_ae_eq hc (f₁ + f₂), Lp.coeFn_add f₁ f₂,
        toProf_ae_eq hc f₁, toProf_ae_eq hc f₂] with x h12 hadd h1 h2
      rw [h12, hadd, Pi.add_apply, liftM_add', ← h1, ← h2]
    have hsum_cls : InFlatClass p.c bgp (fun x => b0Of f₁ x + b0Of f₂ x) :=
      F10K0Help.inFlatClass_add hbgp1 (hb0_cls f₁) (hb0_cls f₂)
    have hsum_resp : IsFlatResponse p.ν 0 (toProf p.c (f₁ + f₂))
        (fun x => b0Of f₁ x + b0Of f₂ x) :=
      F10K0Help.isFlatResponse_congr_F hc
        ((inHr_add_of hbgp1 (inHr_toProf hc f₁) (inHr_toProf hc f₂)).periodic)
        (toProf_periodic hc (f₁ + f₂)) hF_ae
        (F10K0Help.isFlatResponse_add (hb0_resp f₁) (hb0_resp f₂))
    have hK_eq := F10K0Help.flatK_unique_ae hν hc p.train (inHr_toProf hc (f₁ + f₂))
      (hb0_cls (f₁ + f₂)) (hb0_resp (f₁ + f₂)) (hb0q (f₁ + f₂)) (hb0η (f₁ + f₂))
      hsum_cls hsum_resp
      (F10Help.hasWeakVec_add' (hb0q f₁) (hb0q f₂))
      (F10Help.hasWeakVec_add' (hb0η f₁) (hb0η f₂))
    filter_upwards [hkFun_toProf (f₁ + f₂), hK_eq, hkFun_toProf f₁, hkFun_toProf f₂,
      toProf_ae_eq hc (kFun f₁ + kFun f₂), Lp.coeFn_add (kFun f₁) (kFun f₂),
      toProf_ae_eq hc (kFun f₁), toProf_ae_eq hc (kFun f₂)]
      with x h12 heq h1 h2 hadd_prof hadd_lp hp1 hp2
    rw [h12, heq, F10K0Help.flatK_add, hadd_prof, hadd_lp, Pi.add_apply,
      liftM_add', ← hp1, ← hp2, h1, h2]
  have hkFun_smul : ∀ (a : ℝ) (f : HpR p.c), kFun (a • f) = a • kFun f := by
    intro a f
    apply toProf_eq_of_ae_eq hc
    have hF_ae : (fun x => ((a : ℝ) : ℂ) • toProf p.c f x) =ᵐ[hMeas p.c bgp]
        toProf p.c (a • f) := by
      filter_upwards [toProf_ae_eq hc (a • f), Lp.coeFn_smul a f, toProf_ae_eq hc f]
        with x haf hsm hf
      rw [haf, hsm, Pi.smul_apply, hf]
      ext m; simp [liftM]
    have hsm_cls : InFlatClass p.c bgp (fun x => ((a : ℝ) : ℂ) • b0Of f x) :=
      F10K0Help.inFlatClass_smul ((a : ℝ) : ℂ) (hb0_cls f)
    have hsm_resp : IsFlatResponse p.ν 0 (toProf p.c (a • f))
        (fun x => ((a : ℝ) : ℂ) • b0Of f x) :=
      F10K0Help.isFlatResponse_congr_F hc
        ((inHr_const_smul_of ((a : ℝ) : ℂ) (inHr_toProf hc f)).periodic)
        (toProf_periodic hc (a • f)) hF_ae
        (F10K0Help.isFlatResponse_smul ((a : ℝ) : ℂ) (hb0_resp f))
    have hK_eq := F10K0Help.flatK_unique_ae hν hc p.train (inHr_toProf hc (a • f))
      (hb0_cls (a • f)) (hb0_resp (a • f)) (hb0q (a • f)) (hb0η (a • f))
      hsm_cls hsm_resp
      (F10Help.hasWeakVec_smul ((a : ℝ) : ℂ) (hb0q f))
      (F10Help.hasWeakVec_smul ((a : ℝ) : ℂ) (hb0η f))
    filter_upwards [hkFun_toProf (a • f), hK_eq, hkFun_toProf f,
      toProf_ae_eq hc (a • kFun f), Lp.coeFn_smul a (kFun f), toProf_ae_eq hc (kFun f)]
      with x haf heq hf hsm_prof hsm_lp hpf
    rw [haf, heq, F10K0Help.flatK_smul, hsm_prof, hsm_lp, Pi.smul_apply]
    have hlift : liftM (a • (kFun f : Coord → Axi.Merid) x) =
        ((a : ℝ) : ℂ) • liftM ((kFun f : Coord → Axi.Merid) x) := by
      ext m; simp [liftM]
    rw [hlift, ← hpf, hf]
  let kLin : HpR p.c →ₗ[ℝ] HpR p.c :=
    { toFun := kFun
      map_add' := hkFun_add
      map_smul' := hkFun_smul }
  set M₁ : ℝ := C * (p.ν ^ k)⁻¹ * (p.ν ^ (-1 / 2 : ℝ) * Real.sqrt p.H + p.H)
  set M₂ : ℝ := C * (p.ν ^ k)⁻¹ * p.H ^ (-1 / 2 : ℝ) * (p.ν ^ (-1 / 2 : ℝ) + 1)
  have hM₁0 : 0 ≤ M₁ := by positivity
  have hM₂0 : 0 ≤ M₂ := by positivity
  let K0 : HpR p.c →L[ℝ] HpR p.c := kLin.mkContinuous (M₁ + M₂) fun f => by
    have hsplit := F10K0Help.hNorm_le_add_restrict_Ioc_Ioi (H := p.H) hc (hK_inHr f).meas
    have htot : hNorm p.c bgp (flatK p.train (b0Of f) (b0qOf f) (b0ηOf f)) ≤
        ENNReal.ofReal ((M₁ + M₂) * ‖f‖) := by
      calc hNorm p.c bgp (flatK p.train (b0Of f) (b0qOf f) (b0ηOf f))
          ≤ ENNReal.ofReal M₁ * hNorm p.c bgp (toProf p.c f) +
              ENNReal.ofReal M₂ * hNorm p.c bgp (toProf p.c f) :=
            hsplit.trans (add_le_add (hK_bd1 f) (hK_bd2 f))
        _ = (ENNReal.ofReal M₁ + ENNReal.ofReal M₂) * hNorm p.c bgp (toProf p.c f) := by
            rw [add_mul]
        _ = ENNReal.ofReal (M₁ + M₂) * ‖f‖ₑ := by
            rw [← ENNReal.ofReal_add hM₁0 hM₂0, hNorm_toProf hc f]
        _ = ENNReal.ofReal ((M₁ + M₂) * ‖f‖) := by
            rw [← ofReal_norm, ← ENNReal.ofReal_mul (add_nonneg hM₁0 hM₂0)]
    have heq_norm : ‖kFun f‖ₑ = hNorm p.c bgp (flatK p.train (b0Of f) (b0qOf f) (b0ηOf f)) := by
      rw [← hNorm_toProf hc (kFun f)]
      exact eLpNorm_congr_ae (hkFun_toProf f)
    rw [← heq_norm, ← ofReal_norm] at htot
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (add_nonneg hM₁0 hM₂0) (norm_nonneg f))).1 htot
  refine ⟨K0, fun f => ⟨b0Of f, b0qOf f, b0ηOf f, hb0_cls f, hb0_resp f, hb0q f, hb0η f, ?_⟩⟩
  exact hkFun_toProf f

/-- **`PartII-b:F10` (`flatInverse_of`, SP 2326-2344)**:
unconditional deduction of `FlatInverse` from `FlatReconstruction` (`PartII-b:F9`). -/
theorem flatInverse_of (hFR : UnforcedLeray.Short.IIb.FlatReconstruction) :
    UnforcedLeray.Short.IIb.FlatInverse :=
  flatInverse_of_k0Exists flatK0OperatorExists_proof hFR

end UnforcedLeray.Short.IIb

end
