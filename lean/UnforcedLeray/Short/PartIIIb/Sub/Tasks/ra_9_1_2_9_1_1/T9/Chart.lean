import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_1.T9.Mono
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HpPsiTermSummable.Gauss

/-!
# Chart-level Gaussian representation (task `PartIII-b:C/asrc/ra/9/1/2/9/1/1/9`, helper)

Lifts the monomial calculus of `Mono.lean` to chart functions `(s,x) ↦ gbL L (ageA ν s) (x₁ - jc) x₂`,
proves the conormal words of `hpGaussM` are finite sums of such monomials on `UChart`, and bounds
them by the envelope.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

lemma gb_open : IsOpen UChart := isOpen_Ioi.prod isOpen_univ

/-- The chart value of a monomial list. -/
def gbC (ν : ℝ) (j : ℤ) (L : List GbMon) (q : Chart) : ℝ :=
  gbL L (ageA ν q.1) (q.2.1 - (j : ℝ) * cOf ν) q.2.2

lemma gbG_chart_diffAt (m : GbMon) (ν : ℝ) (j : ℤ) (q : Chart) (hν : 0 < ν) (hq : 0 < q.1) :
    DifferentiableAt ℝ (fun p : Chart => gbG m (ageA ν p.1) (p.2.1 - (j : ℝ) * cOf ν) p.2.2) q := by
  have ha : ageA ν q.1 ≠ 0 := by unfold ageA; positivity
  have hA : DifferentiableAt ℝ (fun p : Chart => ageA ν p.1) q := by unfold ageA; fun_prop
  have hI : DifferentiableAt ℝ (fun p : Chart => (ageA ν p.1)⁻¹) q := hA.inv ha
  have hP : DifferentiableAt ℝ (fun p : Chart => (ageA ν p.1)⁻¹ ^ m.n) q := hI.pow m.n
  have hU : DifferentiableAt ℝ (fun p : Chart => p.2.1 - (j : ℝ) * cOf ν) q := by fun_prop
  have hV : DifferentiableAt ℝ (fun p : Chart => p.2.2) q := by fun_prop
  have hE' : DifferentiableAt ℝ
      (fun p : Chart => Real.exp (-((p.2.1 - (j : ℝ) * cOf ν) ^ 2 + p.2.2 ^ 2) * (4 * ageA ν p.1)⁻¹)) q := by
    apply DifferentiableAt.exp
    exact (((hU.pow 2).add (hV.pow 2)).neg).mul
      ((hA.const_mul 4).inv (mul_ne_zero (by norm_num) ha))
  have hE : DifferentiableAt ℝ
      (fun p : Chart => Real.exp (-((p.2.1 - (j : ℝ) * cOf ν) ^ 2 + p.2.2 ^ 2) / (4 * ageA ν p.1))) q := by
    simpa only [div_eq_mul_inv] using hE'
  unfold gbG
  exact (((hP.const_mul m.c).mul (hU.pow m.α)).mul (hV.pow m.β)).mul hE

lemma gbC_diffAt (L : List GbMon) (ν : ℝ) (j : ℤ) (q : Chart) (hν : 0 < ν) (hq : 0 < q.1) :
    DifferentiableAt ℝ (gbC ν j L) q := by
  induction L with
  | nil =>
    have e : gbC ν j [] = fun _ => (0 : ℝ) := funext fun p => gbL_nil _ _ _
    rw [e]
    exact differentiableAt_const _
  | cons m L ih =>
    have e : gbC ν j (m :: L) = fun p : Chart =>
        gbG m (ageA ν p.1) (p.2.1 - (j : ℝ) * cOf ν) p.2.2
          + gbL L (ageA ν p.1) (p.2.1 - (j : ℝ) * cOf ν) p.2.2 :=
      funext fun p => gbL_cons _ _ _ _ _
    rw [e]
    exact (gbG_chart_diffAt m ν j q hν hq).add ih

/-- Directional derivative along a line for chart functions. -/
lemma gb_fderiv_line (f : Chart → ℝ) (y v : Chart) (hf : DifferentiableAt ℝ f y) :
    fderiv ℝ f y v = deriv (fun t : ℝ => f (y + t • v)) 0 := by
  have hl : HasDerivAt (fun t : ℝ => y + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have h2 : HasFDerivAt f (fderiv ℝ f y) ((fun t : ℝ => y + t • v) 0) := by
    simpa using hf.hasFDerivAt
  have hc := h2.comp_hasDerivAt (0 : ℝ) hl
  exact hc.deriv.symm

lemma gbC_fderiv_u (ν : ℝ) (j : ℤ) (L : List GbMon) (q : Chart) (hν : 0 < ν) (hq : 0 < q.1) :
    fderiv ℝ (gbC ν j L) q (0, (1, 0)) = gbC ν j (gbOpL gbDU L) q := by
  have ha : ageA ν q.1 ≠ 0 := by unfold ageA; positivity
  rw [gb_fderiv_line _ q _ (gbC_diffAt L ν j q hν hq)]
  have hfun : (fun t : ℝ => gbC ν j L (q + t • ((0 : ℝ), ((1 : ℝ), (0 : ℝ))))) =
      fun t : ℝ => gbL L (ageA ν q.1) ((q.2.1 - (j : ℝ) * cOf ν) + t) q.2.2 := by
    funext t
    simp only [gbC, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      mul_zero, add_zero, mul_one]
    ring_nf
  rw [hfun]
  have h := gbL_hasDerivAt_u L (ageA ν q.1) (q.2.1 - (j : ℝ) * cOf ν) q.2.2 ha
  have h' := HasDerivAt.comp_const_add (q.2.1 - (j : ℝ) * cOf ν) 0
    (f := fun u' => gbL L (ageA ν q.1) u' q.2.2) (by simpa using h)
  exact h'.deriv

lemma gbC_fderiv_v (ν : ℝ) (j : ℤ) (L : List GbMon) (q : Chart) (hν : 0 < ν) (hq : 0 < q.1) :
    fderiv ℝ (gbC ν j L) q (0, (0, 1)) = gbC ν j (gbOpL gbDV L) q := by
  have ha : ageA ν q.1 ≠ 0 := by unfold ageA; positivity
  rw [gb_fderiv_line _ q _ (gbC_diffAt L ν j q hν hq)]
  have hfun : (fun t : ℝ => gbC ν j L (q + t • ((0 : ℝ), ((0 : ℝ), (1 : ℝ))))) =
      fun t : ℝ => gbL L (ageA ν q.1) (q.2.1 - (j : ℝ) * cOf ν) (q.2.2 + t) := by
    funext t
    simp only [gbC, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      mul_zero, add_zero, mul_one]
  rw [hfun]
  have h := gbL_hasDerivAt_v L (ageA ν q.1) (q.2.1 - (j : ℝ) * cOf ν) q.2.2 ha
  have h' := HasDerivAt.comp_const_add q.2.2 0
    (f := fun v' => gbL L (ageA ν q.1) (q.2.1 - (j : ℝ) * cOf ν) v') (by simpa using h)
  exact h'.deriv

lemma gbC_opW0 (ν : ℝ) (j : ℤ) (L : List GbMon) (q : Chart) (hν : 0 < ν) (hq : 0 < q.1) :
    opW 0 (gbC ν j L) q = gbC ν j (gbOpL gbDS L) q := by
  have ha : ageA ν q.1 ≠ 0 := by unfold ageA; positivity
  show q.1 • fderiv ℝ (gbC ν j L) q ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) = _
  rw [gb_fderiv_line _ q _ (gbC_diffAt L ν j q hν hq)]
  have hfun : (fun t : ℝ => gbC ν j L (q + t • ((1 : ℝ), ((0 : ℝ), (0 : ℝ))))) =
      fun t : ℝ => gbL L (ageA ν q.1 + ν * t) (q.2.1 - (j : ℝ) * cOf ν) q.2.2 := by
    funext t
    simp only [gbC, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      mul_zero, add_zero, mul_one]
    unfold ageA
    ring_nf
  rw [hfun]
  have hlin : HasDerivAt (fun t : ℝ => ageA ν q.1 + ν * t) ν 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul ν).const_add (ageA ν q.1)
  have hf : HasDerivAt (fun a' => gbL L a' (q.2.1 - (j : ℝ) * cOf ν) q.2.2)
      (gbL (gbOpL gbDA L) (ageA ν q.1) (q.2.1 - (j : ℝ) * cOf ν) q.2.2) (ageA ν q.1) :=
    gbL_hasDerivAt_a L _ _ _ ha
  have hf' : HasDerivAt (fun a' => gbL L a' (q.2.1 - (j : ℝ) * cOf ν) q.2.2)
      (gbL (gbOpL gbDA L) (ageA ν q.1) (q.2.1 - (j : ℝ) * cOf ν) q.2.2)
      ((fun t : ℝ => ageA ν q.1 + ν * t) 0) := by
    simpa using hf
  have h' := hf'.comp (0 : ℝ) hlin
  have hd : deriv (fun t : ℝ => gbL L (ageA ν q.1 + ν * t) (q.2.1 - (j : ℝ) * cOf ν) q.2.2) 0
      = gbL (gbOpL gbDA L) (ageA ν q.1) (q.2.1 - (j : ℝ) * cOf ν) q.2.2 * ν := h'.deriv
  rw [hd]
  rw [gbC, gbL_DS_list _ _ _ _ (mul_inv_cancel₀ ha)]
  unfold ageA
  ring

lemma gbC_opW1 (ν : ℝ) (j : ℤ) (L : List GbMon) (q : Chart) (hν : 0 < ν) (hq : 0 < q.1) :
    opW 1 (gbC ν j L) q = gbC ν j (gbOpL gbDU L) q :=
  gbC_fderiv_u ν j L q hν hq

lemma gbC_opW2 (ν : ℝ) (j : ℤ) (L : List GbMon) (q : Chart) (hν : 0 < ν) (hq : 0 < q.1) :
    opW 2 (gbC ν j L) q = gbC ν j (gbOpL gbDV L) q :=
  gbC_fderiv_v ν j L q hν hq

/-- The direction-indexed operator on monomial lists. -/
def gbDir : Fin 3 → GbMon → List GbMon := ![gbDS, gbDU, gbDV]

lemma gbC_opW_dir (x : Fin 3) (ν : ℝ) (j : ℤ) (L : List GbMon) (q : Chart) (hν : 0 < ν)
    (hq : 0 < q.1) :
    opW x (gbC ν j L) q = gbC ν j (gbOpL (gbDir x) L) q := by
  fin_cases x
  · exact gbC_opW0 ν j L q hν hq
  · exact gbC_opW1 ν j L q hν hq
  · exact gbC_opW2 ν j L q hν hq

lemma gbDir_deg (x : Fin 3) (m mo : GbMon) (h : mo ∈ gbDir x m) :
    mo.α + mo.β ≤ m.α + m.β + 2 := by
  fin_cases x
  · change mo ∈ gbDS m at h
    simp only [gbDS, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega
  · change mo ∈ gbDU m at h
    simp only [gbDU, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp <;> omega
  · change mo ∈ gbDV m at h
    simp only [gbDV, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp <;> omega

lemma gbOpL_deg (x : Fin 3) (L : List GbMon) (B : ℕ) (hB : ∀ mo ∈ L, mo.α + mo.β ≤ B) :
    ∀ mo ∈ gbOpL (gbDir x) L, mo.α + mo.β ≤ B + 2 := by
  induction L with
  | nil => intro mo h; simp [gbOpL] at h
  | cons m L ih =>
    intro mo h
    simp only [gbOpL, List.mem_append] at h
    rcases h with h | h
    · have h1 := gbDir_deg x m mo h
      have h2 := hB m (by simp)
      omega
    · exact ih (fun mo' hmo' => hB mo' (by simp [hmo'])) mo h

/-! ## Linear combinations of two components -/

lemma gb_fderiv_lin2 (f0 f1 : Chart → ℝ) (E0 E1 : Merid) (q : Chart)
    (h0 : DifferentiableAt ℝ f0 q) (h1 : DifferentiableAt ℝ f1 q) (v : Chart) :
    fderiv ℝ (fun p => f0 p • E0 + f1 p • E1) q v = fderiv ℝ f0 q v • E0 + fderiv ℝ f1 q v • E1 := by
  have h : HasFDerivAt (fun p => f0 p • E0 + f1 p • E1)
      ((fderiv ℝ f0 q).smulRight E0 + (fderiv ℝ f1 q).smulRight E1) q :=
    (h0.hasFDerivAt.smul_const E0).add (h1.hasFDerivAt.smul_const E1)
  rw [h.fderiv]
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply]

lemma gb_opW_lin2 (x : Fin 3) (f0 f1 : Chart → ℝ) (E0 E1 : Merid) (q : Chart)
    (h0 : DifferentiableAt ℝ f0 q) (h1 : DifferentiableAt ℝ f1 q) :
    opW x (fun p => f0 p • E0 + f1 p • E1) q = opW x f0 q • E0 + opW x f1 q • E1 := by
  fin_cases x
  · simp only [opW, UnforcedLeray.Axi.dS]
    rw [gb_fderiv_lin2 f0 f1 E0 E1 q h0 h1]
    module
  · simp only [opW, UnforcedLeray.Axi.dQ]
    rw [gb_fderiv_lin2 f0 f1 E0 E1 q h0 h1]
  · simp only [opW, UnforcedLeray.Axi.dEta]
    rw [gb_fderiv_lin2 f0 f1 E0 E1 q h0 h1]

lemma gb_opW_congr {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : Fin 3)
    {F F' : Chart → E} {q : Chart} (h : F =ᶠ[𝓝 q] F') : opW x F q = opW x F' q := by
  have e1 : fderiv ℝ F q = fderiv ℝ F' q := h.fderiv_eq
  fin_cases x
  · simp [opW, UnforcedLeray.Axi.dS, e1]
  · simp [opW, UnforcedLeray.Axi.dQ, e1]
  · simp [opW, UnforcedLeray.Axi.dEta, e1]

/-! ## Base representation of `hpGaussM` -/

def gbE0 : Merid := toMer (1, 0)
def gbE1 : Merid := toMer (0, 1)

lemma toMer_decomp (y : ℝ × ℝ) : toMer y = y.1 • gbE0 + y.2 • gbE1 := by
  ext i
  fin_cases i <;> simp [toMer, gbE0, gbE1]

/-- The meridional vector before `toMer`. -/
def gbVab (ν : ℝ) (j : ℤ) (a b : Fin 2) (q : Chart) : ℝ × ℝ :=
  comp2 (Vj ν q.1 j q.2) b • ei a - comp2 (xj ν j q.2) b • fderiv ℝ (Vj ν q.1 j) q.2 (ei a)

lemma hpGaussM_eq (ν : ℝ) (j : ℤ) (a b : Fin 2) (q : Chart) :
    hpGaussM ν j a b q = toMer (gbVab ν j a b q) := rfl

def gbL00a : List GbMon := [⟨-1, 2, 0, 1⟩, ⟨-1 / 2, 3, 2, 1⟩]
def gbL00b : List GbMon := [⟨-1, 2, 1, 0⟩, ⟨1 / 2, 3, 3, 0⟩]
def gbL01a : List GbMon := [⟨1, 2, 1, 0⟩, ⟨-1 / 2, 3, 1, 2⟩]
def gbL01b : List GbMon := [⟨-1, 2, 0, 1⟩, ⟨1 / 2, 3, 2, 1⟩]
def gbL10a : List GbMon := [⟨1, 2, 1, 0⟩, ⟨-1 / 2, 3, 1, 2⟩]
def gbL10b : List GbMon := [⟨-1, 2, 0, 1⟩, ⟨1 / 2, 3, 2, 1⟩]
def gbL11a : List GbMon := [⟨1, 2, 0, 1⟩, ⟨-1 / 2, 3, 0, 3⟩]
def gbL11b : List GbMon := [⟨1, 2, 1, 0⟩, ⟨1 / 2, 3, 1, 2⟩]

lemma gbVab_00 (ν : ℝ) (j : ℤ) (q : Chart) :
    gbVab ν j 0 0 q = (gbC ν j gbL00a q, gbC ν j gbL00b q) := by
  unfold gbVab
  rw [gp_fderiv_Vj]
  refine Prod.ext ?_ ?_
  · simp [gbC, gbL, gbL00a, gbL00b, gbG, Vj, xj, Jrot, sq2, ei, comp2, List.map]
    ring
  · simp [gbC, gbL, gbL00a, gbL00b, gbG, Vj, xj, Jrot, sq2, ei, comp2, List.map]
    ring

lemma gbVab_01 (ν : ℝ) (j : ℤ) (q : Chart) :
    gbVab ν j 0 1 q = (gbC ν j gbL01a q, gbC ν j gbL01b q) := by
  unfold gbVab
  rw [gp_fderiv_Vj]
  refine Prod.ext ?_ ?_
  · simp [gbC, gbL, gbL01a, gbL01b, gbG, Vj, xj, Jrot, sq2, ei, comp2, List.map]
    ring
  · simp [gbC, gbL, gbL01a, gbL01b, gbG, Vj, xj, Jrot, sq2, ei, comp2, List.map]
    ring

lemma gbVab_10 (ν : ℝ) (j : ℤ) (q : Chart) :
    gbVab ν j 1 0 q = (gbC ν j gbL10a q, gbC ν j gbL10b q) := by
  unfold gbVab
  rw [gp_fderiv_Vj]
  refine Prod.ext ?_ ?_
  · simp [gbC, gbL, gbL10a, gbL10b, gbG, Vj, xj, Jrot, sq2, ei, comp2, List.map]
    ring
  · simp [gbC, gbL, gbL10a, gbL10b, gbG, Vj, xj, Jrot, sq2, ei, comp2, List.map]
    ring

lemma gbVab_11 (ν : ℝ) (j : ℤ) (q : Chart) :
    gbVab ν j 1 1 q = (gbC ν j gbL11a q, gbC ν j gbL11b q) := by
  unfold gbVab
  rw [gp_fderiv_Vj]
  refine Prod.ext ?_ ?_
  · simp [gbC, gbL, gbL11a, gbL11b, gbG, Vj, xj, Jrot, sq2, ei, comp2, List.map]
    ring
  · simp [gbC, gbL, gbL11a, gbL11b, gbG, Vj, xj, Jrot, sq2, ei, comp2, List.map]
    ring

/-- The base representation of the four components of `hpGaussM`. -/
lemma gb_base (a b : Fin 2) : ∃ L0 L1 : List GbMon, (∀ mo ∈ L0 ++ L1, mo.α + mo.β ≤ 3) ∧
    ∀ (ν : ℝ) (j : ℤ) (q : Chart), hpGaussM ν j a b q = gbC ν j L0 q • gbE0 + gbC ν j L1 q • gbE1 := by
  fin_cases a <;> fin_cases b
  · refine ⟨gbL00a, gbL00b, ?_, fun ν j q => ?_⟩
    · intro mo hmo
      simp only [gbL00a, gbL00b, List.mem_append, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false] at hmo
      rcases hmo with (rfl | rfl) | (rfl | rfl) <;> norm_num
    · rw [hpGaussM_eq]
      show toMer (gbVab ν j 0 0 q) = _
      rw [gbVab_00, toMer_decomp]
  · refine ⟨gbL01a, gbL01b, ?_, fun ν j q => ?_⟩
    · intro mo hmo
      simp only [gbL01a, gbL01b, List.mem_append, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false] at hmo
      rcases hmo with (rfl | rfl) | (rfl | rfl) <;> norm_num
    · rw [hpGaussM_eq]
      show toMer (gbVab ν j 0 1 q) = _
      rw [gbVab_01, toMer_decomp]
  · refine ⟨gbL10a, gbL10b, ?_, fun ν j q => ?_⟩
    · intro mo hmo
      simp only [gbL10a, gbL10b, List.mem_append, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false] at hmo
      rcases hmo with (rfl | rfl) | (rfl | rfl) <;> norm_num
    · rw [hpGaussM_eq]
      show toMer (gbVab ν j 1 0 q) = _
      rw [gbVab_10, toMer_decomp]
  · refine ⟨gbL11a, gbL11b, ?_, fun ν j q => ?_⟩
    · intro mo hmo
      simp only [gbL11a, gbL11b, List.mem_append, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false] at hmo
      rcases hmo with (rfl | rfl) | (rfl | rfl) <;> norm_num
    · rw [hpGaussM_eq]
      show toMer (gbVab ν j 1 1 q) = _
      rw [gbVab_11, toMer_decomp]

/-! ## The induction over words -/

/-- `w`-word representation of `wordW w hpGaussM` by monomial lists. -/
def GbRep (a b : Fin 2) (w : List (Fin 3)) : Prop :=
  ∃ L0 L1 : List GbMon, (∀ mo ∈ L0 ++ L1, mo.α + mo.β ≤ 3 + 2 * w.length) ∧
    ∀ (ν : ℝ), 0 < ν → ∀ (j : ℤ), ∀ q ∈ UChart,
      wordW w (hpGaussM ν j a b) q = gbC ν j L0 q • gbE0 + gbC ν j L1 q • gbE1

lemma gbRep_all (a b : Fin 2) : ∀ w : List (Fin 3), w.length ≤ 4 → GbRep a b w := by
  intro w
  induction w with
  | nil =>
    intro _
    obtain ⟨L0, L1, hd, hrep⟩ := gb_base a b
    refine ⟨L0, L1, fun mo hmo => ?_, fun ν _ j q hq => ?_⟩
    · have := hd mo hmo
      simp only [List.length_nil]
      omega
    · exact hrep ν j q
  | cons x w ih =>
    intro hlen
    simp only [List.length_cons] at hlen
    obtain ⟨L0, L1, hd, hrep⟩ := ih (by omega)
    refine ⟨gbOpL (gbDir x) L0, gbOpL (gbDir x) L1, ?_, ?_⟩
    · intro mo hmo
      rw [List.mem_append] at hmo
      rcases hmo with h | h
      · have := gbOpL_deg x L0 (3 + 2 * w.length) (fun mo h' => hd mo (List.mem_append_left _ h')) mo h
        simp only [List.length_cons]
        omega
      · have := gbOpL_deg x L1 (3 + 2 * w.length) (fun mo h' => hd mo (List.mem_append_right _ h')) mo h
        simp only [List.length_cons]
        omega
    · intro ν hν j q hq
      show opW x (wordW w (hpGaussM ν j a b)) q = _
      have hc : opW x (wordW w (hpGaussM ν j a b)) q
          = opW x (fun p : Chart => gbC ν j L0 p • gbE0 + gbC ν j L1 p • gbE1) q :=
        gb_opW_congr x (Filter.eventually_of_mem (gb_open.mem_nhds hq)
          (fun p hp => hrep ν hν j p hp))
      rw [hc, gb_opW_lin2 x _ _ _ _ q (gbC_diffAt L0 ν j q hν hq.1)
        (gbC_diffAt L1 ν j q hν hq.1), gbC_opW_dir x ν j L0 q hν hq.1,
        gbC_opW_dir x ν j L1 q hν hq.1]

end UnforcedLeray.Short.PartIIIb.Concrete
