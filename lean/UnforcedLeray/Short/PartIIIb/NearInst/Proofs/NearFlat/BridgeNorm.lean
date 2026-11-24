import UnforcedLeray.Short.PartIIIb.NearInst.Proofs.NearFlat.BridgePt
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Agree

/-!
# `Z ↔` function-level norms for `nearD0Surj_of` (source 3560-3581, 2664-2701, 3866-3880)

Source of record: `the November 2 reference manuscript` (73 pages).

The near space `Z = Z₁ ⊕ ρ_b^{-1/2}H_T` (`Concrete/Spaces.lean`, source 2697-2700, 3866-3872)
holds `3×3` chart tensors with the Frobenius norm; `cor:short-polynomial-stress` (source 3560-3581,
`IIIa.PolyStressCorollary`) is stated for planar complex tensors with the function-level norm
`IIIa.zNorm2`.  The flat maps act on the meridional block (source 3569-3571), so a stress `F ∈ Z`
enters the corollary through the planar blocks `zBlk1 F`, `zBlk2 F` of its two components, and
the gain `𝖦T = gT` (source 3875-3880) enters through `IIIa.gainConj`.

* `zBlk1`, `zBlk2` : the planar blocks (symmetric, measurable; `merBlockC (zsum F) = zBlk1 F +
  zBlk2 F`);
* `zNorm2_zBlk_le` : `‖(g⁻¹F₁, g⁻¹F₂)‖_{zNorm2} ≤ ‖𝖦⁻¹F‖_Z` (the planar block is at most the
  tensor; equality fails for tensors with a hoop or one-azimuthal-index component);
* `ofReal_norm_gainSymm_M0_le` : `‖𝖦⁻¹M₀h‖_Z ≤ ‖g⁻¹(v⊗h + h⊗v)‖_{𝒵₁}` (`IsFlatMult`);
* `tCalNorm_gainConj_add_le_zNorm2`, `tCalNorm_gainConj_merBlockC_zsum_lt_top` : the stress
  inverse acts on the sum `F₁ + F₂`, and `‖F₁+F₂‖_𝒯 ≤ ‖F‖_𝒵` since `W ≥ 1` and `ρ_b ≤ 1`
  (source 3573-3575);
* `hCalNorm_lt_top_of_gainConj` : `g⁻¹b ∈ 𝓗` implies `b ∈ 𝓗` (`|g| ≤ e^{|γ|/ν}`);
* `reMer`, `memLp_reMer`, `velC_reMer` : the real part of a planar velocity as an element of `H`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Short.IIIa

/-! ## Ages and the gain -/

/-- `ageμ`-almost every chart point has positive age. -/
theorem ae_pos_ageμ_chart (c a : ℝ) : ∀ᵐ p ∂ageμ c a, 0 < p.1 := by
  have h1 : ∀ᵐ s ∂((volume.restrict (Ioi (0 : ℝ))).withDensity
      fun s => ENNReal.ofReal (s ^ a)), 0 < s :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)
  unfold ageμ
  exact Measure.quasiMeasurePreserving_fst.ae h1

theorem gainInvFun_pos_chart (γ ν : ℝ) (p : Chart) : 0 < gainInvFun γ ν p :=
  inv_pos.2 (gainFun_pos γ ν p)

theorem vnorm2_nonneg_chart (a : Fin 2 → ℂ) : 0 ≤ vnorm2 a := Real.sqrt_nonneg _

theorem gainInv_eq_gainInvFun {γ ν : ℝ} {p : Chart} (hp : 0 ≤ p.1) :
    (gainG γ ν p.1)⁻¹ = gainInvFun γ ν p := by
  unfold gainInvFun gainFun
  rw [max_eq_left hp]

theorem tnorm2_gainConj {γ ν : ℝ} (T : Chart → Fin 2 → Fin 2 → ℂ) {p : Chart} (hp : 0 ≤ p.1) :
    tnorm2 (gainConj γ ν T p) = gainInvFun γ ν p * tnorm2 (T p) := by
  show tnorm2 ((gainG γ ν p.1)⁻¹ • T p) = _
  rw [tnorm2_smul, gainInv_eq_gainInvFun hp, abs_of_pos (gainInvFun_pos_chart γ ν p)]

theorem vnorm2_gainConj {γ ν : ℝ} (b : Chart → Fin 2 → ℂ) {p : Chart} (hp : 0 ≤ p.1) :
    vnorm2 (gainConj γ ν b p) = gainInvFun γ ν p * vnorm2 (b p) := by
  show vnorm2 ((gainG γ ν p.1)⁻¹ • b p) = _
  rw [vnorm2_smul, gainInv_eq_gainInvFun hp, abs_of_pos (gainInvFun_pos_chart γ ν p)]

theorem gainConj_add (γ ν : ℝ) (T S : Chart → Fin 2 → Fin 2 → ℂ) :
    gainConj γ ν (fun p i j => T p i j + S p i j) =
      fun p i j => gainConj γ ν T p i j + gainConj γ ν S p i j := by
  funext p i j; simp [gainConj, smul_add]

theorem gainConj_sub (γ ν : ℝ) (T S : Chart → Fin 2 → Fin 2 → ℂ) :
    gainConj γ ν (fun p i j => T p i j - S p i j) =
      fun p i j => gainConj γ ν T p i j - gainConj γ ν S p i j := by
  funext p i j; simp [gainConj, smul_sub]

/-- `((gainEquiv γ).symm F).fst = g⁻¹F.fst`, `.snd = g⁻¹F.snd` as elements of the component spaces. -/
theorem gainEquiv_symm_fst_snd' (c mZ ρb γ : ℝ) {ν : ℝ} (hν : 0 < ν) (F : Zsp c mZ ρb) :
    ((gainEquiv c mZ ρb γ hν).symm F).fst = (gainLp (z1Measure c mZ) γ hν).symm F.fst ∧
    ((gainEquiv c mZ ρb γ hν).symm F).snd = (gainLp (htRhoMeasure c ρb) γ hν).symm F.snd := by
  have key : ∀ G : Zsp c mZ ρb, gainEquiv c mZ ρb γ hν G = F →
      G.fst = (gainLp (z1Measure c mZ) γ hν).symm F.fst ∧
        G.snd = (gainLp (htRhoMeasure c ρb) γ hν).symm F.snd := by
    intro G hG
    subst hG
    simp [gainEquiv_fst, gainEquiv_snd]
  exact key _ ((gainEquiv c mZ ρb γ hν).apply_symm_apply F)

/-! ## Norms of the components of `Z` -/

/-- `‖f‖_{Z₁} = ‖W f‖_{L²(s^{-1/2})}`. -/
theorem ofReal_norm_z1 {c mZ : ℝ} (f : Z1sp c mZ) :
    ENNReal.ofReal ‖f‖ =
      eLpNorm (fun p => transWeight mZ p • (f : Chart → Ten3) p) 2 (ageμ c (-1 / 2)) := by
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_lt_top f).ne, (root_z1 c mZ).eLpNorm_eq]

/-- `‖f‖_{ρ_b^{-1/2}H_T} = ρ_b^{-1/2}‖f‖_{H_T}`. -/
theorem ofReal_norm_htRho {c ρb : ℝ} (hρ : 0 < ρb) (f : HTrho c ρb) :
    ENNReal.ofReal ‖f‖ =
      ENNReal.ofReal (ρb ^ (-1 / 2 : ℝ)) * eLpNorm (f : Chart → Ten3) 2 (ageμ c (-1 / 2)) := by
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_lt_top f).ne, (root_htRho hρ).eLpNorm_eq]
  rw [show (fun x => Real.sqrt ρb⁻¹ • (f : Chart → Ten3) x) =
      Real.sqrt ρb⁻¹ • (f : Chart → Ten3) from rfl, eLpNorm_const_smul,
    Real.enorm_eq_ofReal (Real.sqrt_nonneg _)]
  congr 2
  rw [Real.sqrt_eq_rpow, Real.inv_rpow hρ.le, ← Real.rpow_neg hρ.le]
  norm_num

/-! ## The planar blocks of a stress in `Z` -/

/-- The planar block of the first component of `F ∈ Z` (source 3569-3571). -/
def zBlk1 {c mZ ρb : ℝ} (F : Zsp c mZ ρb) : Chart → Fin 2 → Fin 2 → ℂ :=
  merBlockC fun p => (F.fst : Chart → Ten3) p

/-- The planar block of the second component of `F ∈ Z` (source 3569-3571). -/
def zBlk2 {c mZ ρb : ℝ} (F : Zsp c mZ ρb) : Chart → Fin 2 → Fin 2 → ℂ :=
  merBlockC fun p => (F.snd : Chart → Ten3) p

variable {c mZ ρb : ℝ}

theorem zBlk1_symm (F : Zsp c mZ ρb) (p : Chart) (i j : Fin 2) :
    zBlk1 F p i j = zBlk1 F p j i :=
  merBlockC_symm _ p i j

theorem zBlk2_symm (F : Zsp c mZ ρb) (p : Chart) (i j : Fin 2) :
    zBlk2 F p i j = zBlk2 F p j i :=
  merBlockC_symm _ p i j

theorem measurable_zBlk1 (F : Zsp c mZ ρb) (i j : Fin 2) :
    Measurable fun p => zBlk1 F p i j :=
  measurable_merBlockC (Lp.stronglyMeasurable F.fst).measurable i j

theorem measurable_zBlk2 (F : Zsp c mZ ρb) (i j : Fin 2) :
    Measurable fun p => zBlk2 F p i j :=
  measurable_merBlockC (Lp.stronglyMeasurable F.snd).measurable i j

/-- The stress inverse acts on the sum of the components (source 3874, 2700). -/
theorem merBlockC_zsum_eq (F : Zsp c mZ ρb) (p : Chart) (i j : Fin 2) :
    merBlockC (zsum F) p i j = zBlk1 F p i j + zBlk2 F p i j := by
  simp only [merBlockC, zsum, zBlk1, zBlk2, nsSym_add]
  push_cast
  ring

theorem merBlockC_zsum_fun (F : Zsp c mZ ρb) :
    merBlockC (zsum F) = fun p i j => zBlk1 F p i j + zBlk2 F p i j :=
  funext fun p => funext fun i => funext fun j => merBlockC_zsum_eq F p i j

theorem zBlk1_re (F : Zsp c mZ ρb) (p : Chart) (i j : Fin 2) :
    (((zBlk1 F p i j).re : ℝ) : ℂ) = zBlk1 F p i j := by
  simp [zBlk1, merBlockC]

theorem zBlk2_re (F : Zsp c mZ ρb) (p : Chart) (i j : Fin 2) :
    (((zBlk2 F p i j).re : ℝ) : ℂ) = zBlk2 F p i j := by
  simp [zBlk2, merBlockC]

/-- **The planar norm is at most the `Z` norm**: `zNorm2 (g⁻¹F₁) (g⁻¹F₂) ≤ ‖𝖦⁻¹F‖_Z`. -/
theorem zNorm2_zBlk_le {γ ν : ℝ} (hν : 0 < ν) (hρ : 0 < ρb) (F : Zsp c mZ ρb) :
    zNorm2 c mZ ρb (gainConj γ ν (zBlk1 F)) (gainConj γ ν (zBlk2 F)) ≤
      ENNReal.ofReal ‖(gainEquiv c mZ ρb γ hν).symm F‖ := by
  obtain ⟨h1, h2⟩ := gainEquiv_symm_fst_snd' c mZ ρb γ hν F
  rw [WithLp.prod_norm_eq_of_L1, ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
    ofReal_norm_z1, ofReal_norm_htRho hρ, h1, h2]
  unfold zNorm2
  refine add_le_add ?_ (mul_le_mul_right ?_ _)
  · unfold z1Norm2
    have hae := coeFn_gainLp_symm (z1Measure c mZ) γ hν F.fst
    rw [ae_z1Measure] at hae
    refine eLpNorm_mono_ae ?_
    filter_upwards [hae, ae_pos_ageμ_chart c (-1 / 2)] with p hp hpos
    rw [hp, tnorm2_gainConj _ hpos.le, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (transWeight_pos mZ p),
      abs_of_pos (gainInvFun_pos_chart γ ν p),
      abs_of_nonneg (mul_nonneg (transWeight_pos mZ p).le
        (mul_nonneg (gainInvFun_pos_chart γ ν p).le (tnorm2_nonneg _)))]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (tnorm2_merBlockC_le _ p)
      (gainInvFun_pos_chart γ ν p).le) (transWeight_pos mZ p).le
  · unfold tCalNorm
    have hae := coeFn_gainLp_symm (htRhoMeasure c ρb) γ hν F.snd
    rw [ae_htRhoMeasure hρ] at hae
    refine eLpNorm_mono_ae ?_
    filter_upwards [hae, ae_pos_ageμ_chart c (-1 / 2)] with p hp hpos
    rw [hp, tnorm2_gainConj _ hpos.le, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (gainInvFun_pos_chart γ ν p),
      abs_of_nonneg (mul_nonneg (gainInvFun_pos_chart γ ν p).le (tnorm2_nonneg _))]
    exact mul_le_mul_of_nonneg_left (tnorm2_merBlockC_le _ p) (gainInvFun_pos_chart γ ν p).le

/-- **The norm of `𝖦⁻¹M₀h`** (`IsFlatMult`, source 3566-3567, 3876-3877):
`‖𝖦⁻¹M₀h‖_Z ≤ ‖g⁻¹(v⊗h + h⊗v)‖_{𝒵₁}`. -/
theorem ofReal_norm_gainSymm_M0_le {γ ν : ℝ} (hν : 0 < ν) {o : NearOps c mZ ρb} {ν' : ℝ}
    {tr : UnforcedLeray.B0140.TrainSol ν' c} (hM : IsFlatMult o.M0 tr) (h : Hsp c) :
    ENNReal.ofReal ‖(gainEquiv c mZ ρb γ hν).symm (o.M0 h)‖ ≤
      z1Norm2 c mZ (gainConj γ ν (flatMult tr (velC (h : Chart → Merid)))) := by
  obtain ⟨h1, h2⟩ := gainEquiv_symm_fst_snd' c mZ ρb γ hν (o.M0 h)
  obtain ⟨hf, hs⟩ := hM h
  rw [WithLp.prod_norm_eq_of_L1, h2, hs, map_zero, norm_zero, add_zero, h1, ofReal_norm_z1]
  unfold z1Norm2
  refine eLpNorm_mono_ae ?_
  have hae := coeFn_gainLp_symm (z1Measure c mZ) γ hν (o.M0 h).fst
  rw [ae_z1Measure] at hae hf
  filter_upwards [hae, hf, ae_pos_ageμ_chart c (-1 / 2)] with p hp hq hpos
  rw [hp, hq, tnorm2_gainConj _ hpos.le, tnorm2_flatMult_velC, norm_smul, norm_smul,
    Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (transWeight_pos mZ p),
    abs_of_pos (gainInvFun_pos_chart γ ν p),
    abs_of_nonneg (mul_nonneg (transWeight_pos mZ p).le
      (mul_nonneg (gainInvFun_pos_chart γ ν p).le (norm_nonneg _)))]

/-! ## The sum of the components -/

/-- `‖g⁻¹(T₁+T₂)‖_𝒯 ≤ ‖(g⁻¹T₁, g⁻¹T₂)‖_{zNorm2}` (`W ≥ 1`, `ρ_b ≤ 1`; source 3573-3575). -/
theorem tCalNorm_gainConj_add_le_zNorm2 {γ ν : ℝ} (hmZ : 0 ≤ mZ) (hρ : 0 < ρb) (hρ1 : ρb ≤ 1)
    {T₁ T₂ : Chart → Fin 2 → Fin 2 → ℂ} (h1 : ∀ i j, Measurable fun p => T₁ p i j)
    (h2 : ∀ i j, Measurable fun p => T₂ p i j) :
    tCalNorm c (gainConj γ ν (fun p i j => T₁ p i j + T₂ p i j)) ≤
      zNorm2 c mZ ρb (gainConj γ ν T₁) (gainConj γ ν T₂) := by
  have hρ' : (1 : ℝ) ≤ ρb ^ (-1 / 2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hρ hρ1 (by norm_num)
  rw [gainConj_add]
  refine (tCalNorm_add_le (measurable_gainConj h1) (measurable_gainConj h2)).trans ?_
  unfold zNorm2
  exact add_le_add (tCalNorm_le_z1Norm2 hmZ _)
    (le_mul_of_one_le_left bot_le (ENNReal.one_le_ofReal.2 hρ'))

/-- The tensor `T` of the free equation for `F ∈ Z` has finite gained `𝒯` norm. -/
theorem tCalNorm_gainConj_merBlockC_zsum_lt_top {γ ν : ℝ} (hν : 0 < ν) (hmZ : 0 ≤ mZ)
    (hρ : 0 < ρb) (hρ1 : ρb ≤ 1) (F : Zsp c mZ ρb) :
    tCalNorm c (gainConj γ ν (merBlockC (zsum F))) < ⊤ := by
  rw [merBlockC_zsum_fun]
  exact ((tCalNorm_gainConj_add_le_zNorm2 hmZ hρ hρ1 (measurable_zBlk1 F)
    (measurable_zBlk2 F)).trans (zNorm2_zBlk_le hν hρ F)).trans_lt ENNReal.ofReal_lt_top

/-! ## Velocities -/

/-- `g⁻¹b ∈ 𝓗` implies `b ∈ 𝓗` (`g ≤ e^{|γ|/ν}`). -/
theorem hCalNorm_lt_top_of_gainConj {γ ν : ℝ} (hν : 0 < ν) {b : Chart → Fin 2 → ℂ}
    (h : hCalNorm c (gainConj γ ν b) < ⊤) : hCalNorm c b < ⊤ := by
  unfold hCalNorm at h ⊢
  have hle : eLpNorm (fun p => vnorm2 (b p)) 2 (ageμ c (-3 / 2)) ≤
      eLpNorm (Real.exp (|γ| / ν) • fun p => vnorm2 (gainConj γ ν b p)) 2
        (ageμ c (-3 / 2)) := by
    refine eLpNorm_mono_ae ?_
    filter_upwards [ae_pos_ageμ_chart c (-3 / 2)] with p hpos
    rw [Pi.smul_apply, smul_eq_mul, vnorm2_gainConj b hpos.le, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (vnorm2_nonneg_chart (b p)),
      abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
        (mul_nonneg (gainInvFun_pos_chart γ ν p).le (vnorm2_nonneg_chart (b p))))]
    have hg : gainFun γ ν p ≤ Real.exp (|γ| / ν) :=
      (le_abs_self _).trans (gainFun_le hν p)
    have h1 : gainInvFun γ ν p * gainFun γ ν p = 1 := gainInvFun_mul p
    have hv : 0 ≤ vnorm2 (b p) := vnorm2_nonneg_chart (b p)
    have hI : 0 ≤ gainInvFun γ ν p := (gainInvFun_pos_chart γ ν p).le
    calc vnorm2 (b p) = (gainInvFun γ ν p * gainFun γ ν p) * vnorm2 (b p) := by rw [h1, one_mul]
      _ ≤ (gainInvFun γ ν p * Real.exp (|γ| / ν)) * vnorm2 (b p) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg hI) hv
      _ = Real.exp (|γ| / ν) * (gainInvFun γ ν p * vnorm2 (b p)) := by ring
  refine lt_of_le_of_lt hle ?_
  rw [eLpNorm_const_smul]
  exact ENNReal.mul_lt_top enorm_lt_top h

/-- The real part of a planar complex velocity, as a meridional vector field. -/
def reMer (b : Chart → Fin 2 → ℂ) : Chart → Merid :=
  fun p => WithLp.toLp 2 fun i => (b p i).re

theorem velC_reMer (b : Chart → Fin 2 → ℂ) : velC (reMer b) = reVecC b := by
  funext p i
  simp [velC, reMer, reVecC]

theorem norm_reMer (b : Chart → Fin 2 → ℂ) (p : Chart) : ‖reMer b p‖ = vnorm2 (reVecC b p) := by
  rw [← vnorm2_velC, velC_reMer]

theorem measurable_reMer {b : Chart → Fin 2 → ℂ} (hb : ∀ i, Measurable fun p => b p i) :
    Measurable (reMer b) := by
  have h1 : Measurable fun p : Chart => fun i : Fin 2 => (b p i).re :=
    measurable_pi_lambda _ fun i => Complex.measurable_re.comp (hb i)
  exact (WithLp.measurable_toLp 2 (Fin 2 → ℝ)).comp h1

/-- `Re b ∈ H` when `b ∈ 𝓗` (source 2676-2679). -/
theorem memLp_reMer {b : Chart → Fin 2 → ℂ} (hb : ∀ i, Measurable fun p => b p i)
    (hfin : hCalNorm c b < ⊤) : MemLp (reMer b) 2 (ageμ c (-3 / 2)) := by
  refine ⟨(measurable_reMer hb).aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (eLpNorm_mono fun p => ?_) hfin
  rw [norm_reMer, Real.norm_eq_abs, abs_of_nonneg (vnorm2_nonneg_chart (b p))]
  exact vnorm2_reVecC_le b p

end UnforcedLeray.Short.PartIIIb.NearInst
