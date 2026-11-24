import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_van

/-!
# `PartIII-b:C/asrc/ra/5` : `AffineLiftReg` from the regularity, periodicity and cutoff leaves

Source of record: `the November 2 reference manuscript` (73 pages).

`AffineLiftReg` (source 4978, 4991, 5076-5079) is reduced to chart-level facts about the Gaussian
lattice sums `hpA, psipA, fA, eA, PsiA` (leaves below, each a source fact):

* `AffHCoefC2`, `AffPsiC1`, `AffFECont` : joint regularity on `s > 0` ("The sums and their required
  derivatives converge by Gaussian decay", source 4978; `A ∈ 𝒜` is `C^6`, source 5076-5079);
* `AffHCoefPer`, `AffFEPer` : `c`-periodicity in `q` of the lattice sums (reindex `j ↦ j - 1`);
* the vanishing for `ν s > 1.1` (source 4953-4958: `A^y = χ̂_f(νs)A = 0` there) is proved in
  `PartIII-b_C_asrc_ra_5_van.lean`.

The geometric part (the ring lift `Nv` and the pressure scalar `sΨ_A` are `C^n` off the axis by the
chart rules, and vanish on a neighbourhood of the axis because `s = R²/ϱ² → ∞` and the sums vanish
for `νs > 1.1`) is proved here.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. Geometry: composition with the ring chart -/

theorem contDiffOn_chart_offAxis {R : ℝ} (hR : 0 < R) (n : ℕ) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (fun x : ℝ × Space => chart R x.1 x.2)
      {x : ℝ × Space | x.2 ∉ axis} := by
  set W : Set (ℝ × Space) := {x : ℝ × Space | x.2 ∉ axis} with hW
  have hϱ : ContDiffOn ℝ (n : WithTop ℕ∞) (fun x : ℝ × Space => ϱ x.2) W :=
    contDiffOn_ϱ.comp contDiff_snd.contDiffOn (fun x hx => hx)
  have hϱ0 : ∀ x ∈ W, ϱ x.2 ≠ 0 := fun x hx => ϱ_ne_zero hx
  have hage : ContDiffOn ℝ (n : WithTop ℕ∞) (fun x : ℝ × Space => age R x.2) W := by
    unfold age
    exact contDiffOn_const.div (hϱ.pow 2) fun x hx => pow_ne_zero 2 (hϱ0 x hx)
  have hage0 : ∀ x ∈ W, age R x.2 ≠ 0 := fun x hx => (age_pos hR.ne' hx).ne'
  have hphase : ContDiffOn ℝ (n : WithTop ℕ∞) (fun x : ℝ × Space => phase R x.1 x.2) W := by
    unfold phase
    exact (contDiff_const.mul contDiff_fst).div_const 2 |>.contDiffOn.sub
      (contDiffOn_const.mul (hage.log hage0))
  have htrans : ContDiffOn ℝ (n : WithTop ℕ∞) (fun x : ℝ × Space => Axi.trans R x.2) W := by
    unfold Axi.trans
    have h2 : ContDiff ℝ (n : WithTop ℕ∞) (fun x : ℝ × Space => x.2 2) := by fun_prop
    exact ((contDiff_const.mul h2).contDiffOn (s := W)).div hϱ hϱ0
  unfold chart
  exact hage.prodMk (hphase.prodMk htrans)

theorem contDiffOn_comp_chart {R : ℝ} (hR : 0 < R) (n : ℕ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {G : ℝ × (ℝ × ℝ) → E}
    (hG : ContDiffOn ℝ (n : WithTop ℕ∞) G (Ioi (0 : ℝ) ×ˢ univ)) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (fun x : ℝ × Space => G (chart R x.1 x.2))
      {x : ℝ × Space | x.2 ∉ axis} :=
  hG.comp (contDiffOn_chart_offAxis hR n) (fun x hx => ⟨age_pos hR.ne' hx, trivial⟩)

theorem contDiffOn_Nv_offAxis {R : ℝ} (hR : 0 < R) (n : ℕ) {b : ℝ × (ℝ × ℝ) → Merid}
    (hb : ContDiffOn ℝ (n : WithTop ℕ∞) b (Ioi (0 : ℝ) ×ˢ univ)) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (fun x : ℝ × Space => Nv R b x.1 x.2)
      {x : ℝ × Space | x.2 ∉ axis} := by
  set W : Set (ℝ × Space) := {x : ℝ × Space | x.2 ∉ axis} with hW
  have hϱ : ContDiffOn ℝ (n : WithTop ℕ∞) (fun x : ℝ × Space => ϱ x.2) W :=
    contDiffOn_ϱ.comp contDiff_snd.contDiffOn (fun x hx => hx)
  have hage : ContDiffOn ℝ (n : WithTop ℕ∞) (fun x : ℝ × Space => age R x.2) W := by
    unfold age
    exact contDiffOn_const.div (hϱ.pow 2) fun x hx => pow_ne_zero 2 (ϱ_ne_zero hx)
  have hage0 : ∀ x ∈ W, age R x.2 ≠ 0 := fun x hx => (age_pos hR.ne' hx).ne'
  have hbc := contDiffOn_comp_chart hR n hb
  have hb0 : ContDiffOn ℝ (n : WithTop ℕ∞) (fun x : ℝ × Space => b (chart R x.1 x.2) 0) W :=
    (EuclideanSpace.proj (0 : Fin 2) : Merid →L[ℝ] ℝ).contDiff.comp_contDiffOn hbc
  have hb1 : ContDiffOn ℝ (n : WithTop ℕ∞) (fun x : ℝ × Space => b (chart R x.1 x.2) 1) W :=
    (EuclideanSpace.proj (1 : Fin 2) : Merid →L[ℝ] ℝ).contDiff.comp_contDiffOn hbc
  have heR : ContDiffOn ℝ (n : WithTop ℕ∞) (fun x : ℝ × Space => eR x.2) W :=
    contDiffOn_eR.comp contDiff_snd.contDiffOn (fun x hx => hx)
  have hsq : ContDiffOn ℝ (n : WithTop ℕ∞) (fun x : ℝ × Space => √(age R x.2)) W :=
    hage.sqrt hage0
  have : (fun x : ℝ × Space => Nv R b x.1 x.2) = fun x =>
      √(age R x.2) • (b (chart R x.1 x.2) 0 • eR x.2 + b (chart R x.1 x.2) 1 • e3) := by
    funext x
    simp [Nv, frameL_apply]
  rw [this]
  exact hsq.smul ((hb0.smul heR).add (hb1.smul contDiffOn_const))

/-! ## 2. Near the axis -/

theorem age_eq_zero_of_mem_axis (R : ℝ) {y : Space} (hy : y ∈ axis) : age R y = 0 := by
  have hy' : y 0 = 0 ∧ y 1 = 0 := hy
  have hϱ : ϱ y = 0 := by simp [ϱ, hy'.1, hy'.2]
  simp [age, hϱ]

theorem eventually_axis_or_age_gt {R : ℝ} (hR : 0 < R) (s₁ : ℝ) {y₀ : Space} (hy₀ : y₀ ∈ axis) :
    ∀ᶠ y in 𝓝 y₀, y ∈ axis ∨ s₁ < age R y := by
  have hy' : y₀ 0 = 0 ∧ y₀ 1 = 0 := hy₀
  have hcont : Continuous fun y : Space => y 0 ^ 2 + y 1 ^ 2 := by fun_prop
  have hlt : (fun y : Space => y 0 ^ 2 + y 1 ^ 2) y₀ < R ^ 2 / (|s₁| + 1) := by
    simp only [hy'.1, hy'.2]; norm_num; positivity
  filter_upwards [hcont.continuousAt.eventually_lt continuousAt_const hlt] with y hy
  by_cases hq : y 0 ^ 2 + y 1 ^ 2 = 0
  · left
    have h0 : y 0 = 0 := (pow_eq_zero_iff two_ne_zero).1
      (by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)])
    have h1 : y 1 = 0 := (pow_eq_zero_iff two_ne_zero).1
      (by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)])
    exact ⟨h0, h1⟩
  · right
    have hqpos : 0 < y 0 ^ 2 + y 1 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hq)
    have hϱ2 : ϱ y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
      unfold ϱ
      exact Real.sq_sqrt (by positivity)
    have hM : (0 : ℝ) < |s₁| + 1 := by positivity
    have hy2 := (lt_div_iff₀ hM).1 hy
    unfold age
    rw [hϱ2, lt_div_iff₀ hqpos]
    nlinarith [mul_nonneg (sub_nonneg.2 (le_abs_self s₁)) hqpos.le, abs_nonneg s₁]

theorem isOpen_offAxis' : IsOpen {x : ℝ × Space | x.2 ∉ axis} := by
  have hc : IsClosed {y : Space | y ∈ axis} := by
    have : {y : Space | y ∈ axis} = {y : Space | y 0 = 0} ∩ {y | y 1 = 0} := rfl
    rw [this]
    exact (isClosed_eq (by fun_prop) continuous_const).inter
      (isClosed_eq (by fun_prop) continuous_const)
  exact (hc.isOpen_compl).preimage continuous_snd


theorem contDiff_glue {R : ℝ} (hR : 0 < R) (n : ℕ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : ℝ × Space → E) (s₁ : ℝ)
    (hoff : ContDiffOn ℝ (n : WithTop ℕ∞) F {x : ℝ × Space | x.2 ∉ axis})
    (haxis : ∀ x : ℝ × Space, x.2 ∈ axis → F x = 0)
    (hfar : ∀ x : ℝ × Space, x.2 ∉ axis → s₁ < age R x.2 → F x = 0) :
    ContDiff ℝ (n : WithTop ℕ∞) F := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x.2 ∈ axis
  · have h1 := eventually_axis_or_age_gt hR s₁ hx
    have h2 : ∀ᶠ z in 𝓝 x, z.2 ∈ axis ∨ s₁ < age R z.2 :=
      continuous_snd.continuousAt.eventually h1
    have h3 : F =ᶠ[𝓝 x] fun _ => (0 : E) := by
      filter_upwards [h2] with z hz
      by_cases hz' : z.2 ∈ axis
      · exact haxis z hz'
      · exact hfar z hz' (hz.resolve_left hz')
    exact (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq h3
  · exact (hoff.contDiffAt (isOpen_offAxis'.mem_nhds hx))

/-! ## 3. Periodic extension and the behaviour at `s ≤ 0` -/

theorem merOf_zero' : merOf (0 : Vec3) = 0 := by
  ext i; fin_cases i <;> simp [merOf]

theorem hAcoef_nonpos (ν ε : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (p : Chart) (hp : p.1 ≤ 0) :
    hAcoef ν ε χf A p = 0 := by
  simp [hAcoef, hhatA, Real.sqrt_eq_zero_of_nonpos hp, merOf_zero']

theorem FEcoef_nonpos (ν μ : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (p : Chart) (hp : p.1 ≤ 0) :
    (FAcoef ν μ χf A + EAcoef ν μ χf A) p = 0 := by
  simp [FAcoef, EAcoef, Real.sqrt_eq_zero_of_nonpos hp, merOf_zero']

theorem perExt_eq_self {c : ℝ} (b : ℝ × (ℝ × ℝ) → Merid)
    (hper : ∀ s η : ℝ, 0 < s → Function.Periodic (fun ξ => b (s, (ξ, η))) c)
    (hz : ∀ p : ℝ × (ℝ × ℝ), p.1 ≤ 0 → b p = 0) : perExt c b = b := by
  funext ⟨s, ξ, η⟩
  by_cases hs : s ≤ 0
  · simp only [perExt]
    rw [hz _ hs, hz (s, ξ, η) hs]
  · push_neg at hs
    simp only [perExt, cellRep]
    have := (hper s η hs).sub_int_mul_eq (x := ξ) ⌊(ξ + c / 2) / c⌋
    simpa [mul_comm] using this

/-! ## 4. The leaves (source facts about the Gaussian lattice sums) -/

/-- **Joint `C²` regularity of `ĥ_A`'s coefficient on `s > 0`** (source 4978 "The sums and their
required derivatives converge by Gaussian decay", 4979-4980, 5076-5079: `A ∈ 𝒜` is `C^6`, so
`h^p_A, ψ^p_A` and `𝒦ψ^p_A = η∂_ηψ^p_A + 2s∂_sψ^p_A` are `C²`/`C³`-fine in `(s,q,η)`). -/
def AffHCoefC2 (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν ε : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    ContDiffOn ℝ 2 (hAcoef ν ε χf A) (Ioi (0 : ℝ) ×ˢ univ)

/-- **Joint `C¹` regularity of `s Ψ_A` on `s > 0`** (source 5024, 5040-5043, 4978). -/
def AffPsiC1 (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    ContDiffOn ℝ 1 (fun p : Chart => p.1 * PsiA ν χf A p.1 p.2) (Ioi (0 : ℝ) ×ˢ univ)

/-- **Continuity of `F_A + E_A`'s coefficient on `s > 0`** (source 4981, 4978). -/
def AffFECont (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν μ : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    ContinuousOn (FAcoef ν μ χf A + EAcoef ν μ χf A) (Ioi (0 : ℝ) ×ˢ univ)

/-- **`c`-periodicity of `ĥ_A`'s coefficient in `q`**, `c = ν⁻²` (source 4963-4975: the terms
satisfy `x_j(q + c) = x_{j-1}(q)`; reindex the `ℤ`-sum). -/
def AffHCoefPer (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν ε : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    ∀ s η : ℝ, 0 < s → Function.Periodic (fun ξ => hAcoef ν ε χf A (s, (ξ, η))) (cOf ν)

/-- **`c`-periodicity of `(F_A + E_A)`'s coefficient in `q`** (source 4963-4975, reindex). -/
def AffFEPer (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν μ : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    ∀ s η : ℝ, 0 < s →
      Function.Periodic (fun ξ => (FAcoef ν μ χf A + EAcoef ν μ χf A) (s, (ξ, η))) (cOf ν)

/-- **Joint `C²` regularity of `h^p_A`** on `s > 0` (source 4973, 4978, 5076-5079). -/
def HpAC2 (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    ContDiffOn ℝ 2 (fun p : Chart => hpA ν χf A p.1 p.2) (Ioi (0 : ℝ) ×ˢ univ)

/-- **Joint `C³` regularity of `ψ^p_A`** on `s > 0` (source 4974-4975, 4978, 5076-5079): `ĥ_A`
contains `𝒦ψ^p_A = η∂_ηψ^p_A + 2s∂_sψ^p_A`, which must be `C²`. -/
def PsipAC3 (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    ContDiffOn ℝ 3 (fun p : Chart => psipA ν χf A p.1 p.2) (Ioi (0 : ℝ) ×ˢ univ)

/-! ## 5. The reduction -/

theorem lt_of_far {ν s : ℝ} (hν : 0 < ν) (h : (11 / 10) / ν < s) : 11 / 10 < ν * s := by
  rw [div_lt_iff₀ hν] at h
  linarith

theorem affineLiftReg_of (as : ℝ) (χf : ℝ → ℝ) (h1 : AffHCoefC2 as χf) (h2 : AffPsiC1 as χf)
    (h3 : AffFECont as χf) (h4 : AffHCoefPer as χf) (h5 : AffFEPer as χf) :
    AffineLiftReg as χf := by
  intro hχ ν μ ε hν hε A hA
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hNvAxis : ∀ (b : ℝ × (ℝ × ℝ) → Merid) (x : ℝ × Space), x.2 ∈ axis → Nv ε⁻¹ b x.1 x.2 = 0 := by
    intro b x hx
    simp [Nv, age_eq_zero_of_mem_axis ε⁻¹ hx]
  refine ⟨?_, ?_, ?_⟩
  · -- ĥ_A
    have hpe : perExt (cOf ν) (hAcoef ν ε χf A) = hAcoef ν ε χf A :=
      perExt_eq_self _ (h4 hχ ν ε hν A hA) (fun p hp => hAcoef_nonpos ν ε χf A p hp)
    have : (fun x : ℝ × Space => hLift ν ε (cOf ν) χf A x.1 x.2) =
        fun x : ℝ × Space => Nv ε⁻¹ (hAcoef ν ε χf A) x.1 x.2 := by
      funext x; simp only [hLift, hpe]
    rw [this]
    refine contDiff_glue hR 2 _ ((11 / 10) / ν) ?_ (fun x hx => hNvAxis _ x hx) ?_
    · exact contDiffOn_Nv_offAxis hR 2 (h1 hχ ν ε hν A hA)
    · intro x hx hlt
      simp only [Nv]
      rw [hAcoef_eq_zero hχ A (p := chart ε⁻¹ x.1 x.2) (lt_of_far hν hlt)]
      simp
  · -- sΨ_A
    have hoff : ContDiffOn ℝ ((1 : ℕ) : WithTop ℕ∞)
        (fun x : ℝ × Space => psiLift ν ε χf A x.1 x.2) {x : ℝ × Space | x.2 ∉ axis} := by
      have := contDiffOn_comp_chart hR 1 (h2 hχ ν hν A hA)
      exact this
    refine contDiff_glue hR 1 _ ((11 / 10) / ν) hoff ?_ ?_
    · intro x hx
      simp [psiLift, sPsiPhys, age_eq_zero_of_mem_axis ε⁻¹ hx, chart]
    · intro x hx hlt
      simp only [psiLift, sPsiPhys, chart]
      rw [PsiA_eq_zero hχ A (lt_of_far hν hlt).le]
      simp
  · -- F_A + E_A
    have hpe : perExt (cOf ν) (FAcoef ν μ χf A + EAcoef ν μ χf A) =
        FAcoef ν μ χf A + EAcoef ν μ χf A :=
      perExt_eq_self _ (h5 hχ ν μ hν A hA) (fun p hp => FEcoef_nonpos ν μ χf A p hp)
    have : (fun x : ℝ × Space => feLift ν μ ε (cOf ν) χf A x.1 x.2) =
        fun x : ℝ × Space => Nv ε⁻¹ (FAcoef ν μ χf A + EAcoef ν μ χf A) x.1 x.2 := by
      funext x; simp only [feLift, hpe]
    rw [this]
    have hc : ContDiff ℝ ((0 : ℕ) : WithTop ℕ∞)
        (fun x : ℝ × Space => Nv ε⁻¹ (FAcoef ν μ χf A + EAcoef ν μ χf A) x.1 x.2) := by
      refine contDiff_glue hR 0 _ ((11 / 10) / ν) ?_ (fun x hx => hNvAxis _ x hx) ?_
      · refine contDiffOn_Nv_offAxis hR 0 ?_
        have := h3 hχ ν μ hν A hA
        simpa [contDiffOn_zero] using this
      · intro x hx hlt
        simp only [Nv]
        rw [FEcoef_eq_zero hχ A (p := chart ε⁻¹ x.1 x.2) (lt_of_far hν hlt)]
        simp
    simpa [contDiff_zero] using hc

end UnforcedLeray.Short.PartIIIb.Concrete
