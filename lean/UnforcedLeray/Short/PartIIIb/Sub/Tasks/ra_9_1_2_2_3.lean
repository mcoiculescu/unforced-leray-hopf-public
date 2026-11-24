import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_1_2_2
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_2_1
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_2_2

/-!
# `PartIII-b:C/asrc/ra/9/1/2/2/3` : `RingLapMerChain` (second-order meridional chain rule)

Source: `the November 2 reference manuscript` lines 5034-5039.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. Open sets and differentiability -/

theorem rlm_open : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
  isOpen_Ioi.prod isOpen_univ

theorem rlm_openP : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) : Set (ℝ × ℝ)) :=
  isOpen_Ioi.prod isOpen_univ

theorem rlm_diffAt {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] {f : Chart → G}
    {x : Chart} (hf : ContDiffOn ℝ 1 f (Ioi 0 ×ˢ univ)) (hx : x ∈ (Ioi 0 ×ˢ univ : Set Chart)) :
    DifferentiableAt ℝ f x :=
  (hf.differentiableOn (by norm_num)).differentiableAt (rlm_open.mem_nhds hx)

theorem rlm_diffAtP {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] {f : ℝ × ℝ → G}
    {x : ℝ × ℝ} (hf : ContDiffOn ℝ 1 f (Ioi 0 ×ˢ univ)) (hx : 0 < x.1) :
    DifferentiableAt ℝ f x :=
  (hf.differentiableOn (by norm_num)).differentiableAt (rlm_openP.mem_nhds ⟨hx, trivial⟩)

/-! ## 2. Symmetry of second derivatives -/

theorem rlm_comm {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] {f : Chart → G} {x : Chart}
    (hf : ContDiffAt ℝ 2 f x) (v w : Chart) :
    fderiv ℝ (fun y => fderiv ℝ f y v) x w = fderiv ℝ (fun y => fderiv ℝ f y w) x v := by
  have hD : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).differentiableAt (by norm_num)
  have hv : fderiv ℝ (fun y => fderiv ℝ f y v) x w = fderiv ℝ (fderiv ℝ f) x w v := by
    rw [fderiv_clm_apply hD (differentiableAt_const (x := x) v)]
    simp
  have hw : fderiv ℝ (fun y => fderiv ℝ f y w) x v = fderiv ℝ (fderiv ℝ f) x v w := by
    rw [fderiv_clm_apply hD (differentiableAt_const (x := x) w)]
    simp
  rw [hv, hw]
  exact (hf.isSymmSndFDerivAt (by norm_num : minSmoothness ℝ 2 ≤ (2 : ℕ∞ω))) w v

theorem rlm_dir_diff {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] {f : Chart → G}
    {x : Chart} (hf : ContDiffAt ℝ 2 f x) (v : Chart) :
    DifferentiableAt ℝ (fun y => fderiv ℝ f y v) x := by
  have hD : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).differentiableAt (by norm_num)
  exact hD.clm_apply (differentiableAt_const v)

theorem rlm_fderiv_cd {f : Chart → Merid} (hf : ContDiffOn ℝ 2 f (Ioi 0 ×ˢ univ)) (v : Chart) :
    ContDiffOn ℝ 1 (fun y => fderiv ℝ f y v) (Ioi 0 ×ˢ univ) :=
  (hf.fderiv_of_isOpen (m := 1) rlm_open (by norm_num)).clm_apply contDiffOn_const

theorem rlm_coef_fst (x : Chart) : fderiv ℝ (fun y : Chart => 2 * y.1) x (0, (1, 0)) = 0 := by
  have h : HasFDerivAt (fun y : Chart => 2 * y.1)
      ((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) x :=
    (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).hasFDerivAt.const_mul 2
  rw [h.fderiv]
  simp

theorem rlm_coef_snd (x : Chart) : fderiv ℝ (fun y : Chart => y.2.2) x (0, (1, 0)) = 0 := by
  have h2 : HasFDerivAt (fun y : Chart => y.2) (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) x :=
    (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).hasFDerivAt
  have h : HasFDerivAt (fun y : Chart => y.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) x :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp x h2
  rw [h.fderiv]
  simp

/-- `dQ (𝒦 F) = 𝒦 (dQ F)` for `F` of class `C²` at the point. -/
theorem rlm_dQ_Kc {f : Chart → Merid} {x : Chart} (hf : ContDiffAt ℝ 2 f x) :
    UnforcedLeray.Axi.dQ (Kc f) x = Kc (UnforcedLeray.Axi.dQ f) x := by
  have hS := rlm_dir_diff hf (1, (0, 0))
  have hE := rlm_dir_diff hf (0, (0, 1))
  have dc1 : DifferentiableAt ℝ (fun y : Chart => 2 * y.1) x := by fun_prop
  have dc2 : DifferentiableAt ℝ (fun y : Chart => y.2.2) x := by fun_prop
  show fderiv ℝ (fun y => (2 * y.1) • fderiv ℝ f y (1, (0, 0))
      + y.2.2 • fderiv ℝ f y (0, (0, 1))) x (0, (1, 0))
      = (2 * x.1) • fderiv ℝ (fun y => fderiv ℝ f y (0, (1, 0))) x (1, (0, 0))
        + x.2.2 • fderiv ℝ (fun y => fderiv ℝ f y (0, (1, 0))) x (0, (0, 1))
  have e1 : fderiv ℝ (fun y => (2 * y.1) • fderiv ℝ f y (1, (0, 0))
      + y.2.2 • fderiv ℝ f y (0, (0, 1))) x
      = fderiv ℝ (fun y => (2 * y.1) • fderiv ℝ f y (1, (0, 0))) x
        + fderiv ℝ (fun y => y.2.2 • fderiv ℝ f y (0, (0, 1))) x :=
    fderiv_add (dc1.smul hS) (dc2.smul hE)
  have e2 : fderiv ℝ (fun y => (2 * y.1) • fderiv ℝ f y (1, (0, 0))) x
      = (2 * x.1) • fderiv ℝ (fun y => fderiv ℝ f y (1, (0, 0))) x
        + (fderiv ℝ (fun y : Chart => 2 * y.1) x).smulRight (fderiv ℝ f x (1, (0, 0))) :=
    fderiv_smul dc1 hS
  have e3 : fderiv ℝ (fun y => y.2.2 • fderiv ℝ f y (0, (0, 1))) x
      = x.2.2 • fderiv ℝ (fun y => fderiv ℝ f y (0, (0, 1))) x
        + (fderiv ℝ (fun y : Chart => y.2.2) x).smulRight (fderiv ℝ f x (0, (0, 1))) :=
    fderiv_smul dc2 hE
  rw [e1, e2, e3]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, rlm_coef_fst, rlm_coef_snd, smul_zero, zero_smul,
    add_zero, zero_add]
  rw [rlm_comm hf (1, (0, 0)) (0, (1, 0)), rlm_comm hf (0, (0, 1)) (0, (1, 0))]

/-! ## 3. Linearity of the directional derivatives -/

theorem rlm_dir_sub {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] {g h : Chart → G}
    {x : Chart} (a : ℝ) (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h x) (v : Chart) :
    fderiv ℝ (fun y => g y - a • h y) x v = fderiv ℝ g x v - a • fderiv ℝ h x v := by
  have e1 : fderiv ℝ (fun y => g y - a • h y) x
      = fderiv ℝ g x - fderiv ℝ (fun y => a • h y) x :=
    fderiv_sub hg (hh.const_smul a)
  have e2 : fderiv ℝ (fun y => a • h y) x = a • fderiv ℝ h x := fderiv_const_smul hh a
  rw [e1, e2]
  simp

theorem rlm_dir_add {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] {g h : Chart → G}
    {x : Chart} (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h x) (v : Chart) :
    fderiv ℝ (fun y => g y + h y) x v = fderiv ℝ g x v + fderiv ℝ h x v := by
  have e1 : fderiv ℝ (fun y => g y + h y) x = fderiv ℝ g x + fderiv ℝ h x := fderiv_add hg hh
  rw [e1]
  simp

theorem rlm_dQ_sub {g h : Chart → Merid} {x : Chart} (a : ℝ) (hg : DifferentiableAt ℝ g x)
    (hh : DifferentiableAt ℝ h x) :
    UnforcedLeray.Axi.dQ (fun y => g y - a • h y) x
      = UnforcedLeray.Axi.dQ g x - a • UnforcedLeray.Axi.dQ h x :=
  rlm_dir_sub a hg hh _

theorem rlm_dQ_add {g h : Chart → Merid} {x : Chart} (hg : DifferentiableAt ℝ g x)
    (hh : DifferentiableAt ℝ h x) :
    UnforcedLeray.Axi.dQ (fun y => g y + h y) x
      = UnforcedLeray.Axi.dQ g x + UnforcedLeray.Axi.dQ h x :=
  rlm_dir_add hg hh _

theorem rlm_Kc_sub {g h : Chart → Merid} {x : Chart} (a : ℝ) (hg : DifferentiableAt ℝ g x)
    (hh : DifferentiableAt ℝ h x) :
    Kc (fun y => g y - a • h y) x = Kc g x - a • Kc h x := by
  simp only [Kc, UnforcedLeray.Axi.dS, UnforcedLeray.Axi.dEta, rlm_dir_sub a hg hh]
  module

/-! ## 4. Component and eventual-equality tools -/

theorem rlm_dρ_comp {H : ℝ × ℝ → Merid} {p : ℝ × ℝ} (hH : DifferentiableAt ℝ H p) (j : Fin 2) :
    UnforcedLeray.Axi.dρ (fun q => H q j) p = UnforcedLeray.Axi.dρ H p j := by
  have h : HasFDerivAt (fun q => H q j)
      ((EuclideanSpace.proj j : Merid →L[ℝ] ℝ).comp (fderiv ℝ H p)) p :=
    (EuclideanSpace.proj j : Merid →L[ℝ] ℝ).hasFDerivAt.comp p hH.hasFDerivAt
  unfold UnforcedLeray.Axi.dρ
  rw [h.fderiv]
  simp

theorem rlm_dz_comp {H : ℝ × ℝ → Merid} {p : ℝ × ℝ} (hH : DifferentiableAt ℝ H p) (j : Fin 2) :
    UnforcedLeray.Axi.dz (fun q => H q j) p = UnforcedLeray.Axi.dz H p j := by
  have h : HasFDerivAt (fun q => H q j)
      ((EuclideanSpace.proj j : Merid →L[ℝ] ℝ).comp (fderiv ℝ H p)) p :=
    (EuclideanSpace.proj j : Merid →L[ℝ] ℝ).hasFDerivAt.comp p hH.hasFDerivAt
  unfold UnforcedLeray.Axi.dz
  rw [h.fderiv]
  simp

theorem rlm_dρ_dρ {F G : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (h : UnforcedLeray.Axi.dρ F =ᶠ[nhds p] G) :
    UnforcedLeray.Axi.dρ (UnforcedLeray.Axi.dρ F) p = UnforcedLeray.Axi.dρ G p := by
  show fderiv ℝ (UnforcedLeray.Axi.dρ F) p (1, 0) = fderiv ℝ G p (1, 0)
  rw [h.fderiv_eq]

theorem rlm_dz_dz {F G : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (h : UnforcedLeray.Axi.dz F =ᶠ[nhds p] G) :
    UnforcedLeray.Axi.dz (UnforcedLeray.Axi.dz F) p = UnforcedLeray.Axi.dz G p := by
  show fderiv ℝ (UnforcedLeray.Axi.dz F) p (0, 1) = fderiv ℝ G p (0, 1)
  rw [h.fderiv_eq]

theorem rlm_erProj_zero (v : Merid) : erProj v 0 = v 0 := by simp [erProj]

theorem rlm_erProj_one (v : Merid) : erProj v 1 = 0 := by simp [erProj]

theorem rlm_K1_apply (F : Chart → Merid) (y : Chart) : K1 F y = Kc F y + F y := rfl

theorem rlm_lapQE_apply (F : Chart → Merid) (y : Chart) :
    lapQE F y = UnforcedLeray.Axi.dQ (UnforcedLeray.Axi.dQ F) y
      + UnforcedLeray.Axi.dEta (UnforcedLeray.Axi.dEta F) y := rfl

/-! ## 5. Profiles and regularity -/

/-- The first-order profile `D1 b = ∂_ξ b - ε (𝒦+1) b`, `ε = R⁻¹`. -/
def rlmD1 (R : ℝ) (b : Chart → Merid) : Chart → Merid :=
  fun y => UnforcedLeray.Axi.dQ b y - R⁻¹ • K1 b y

theorem rlmD1_apply (R : ℝ) (b : Chart → Merid) (y : Chart) :
    rlmD1 R b y = UnforcedLeray.Axi.dQ b y - R⁻¹ • K1 b y := rfl

/-- The weighted profiles `(R/ρ)^k • c(chart)` for `k = 1, 2`. -/
def rlmH (R τ : ℝ) (b : Chart → Merid) : ℝ × ℝ → Merid :=
  fun m' => (R / m'.1) ^ 1 • b (chartM R τ m')

def rlmG1 (R τ : ℝ) (b : Chart → Merid) : ℝ × ℝ → Merid :=
  fun m' => (R / m'.1) ^ 2 • rlmD1 R b (chartM R τ m')

def rlmG2 (R τ : ℝ) (b : Chart → Merid) : ℝ × ℝ → Merid :=
  fun m' => (R / m'.1) ^ 2 • UnforcedLeray.Axi.dEta b (chartM R τ m')

theorem rlmH_pt (R τ : ℝ) (b : Chart → Merid) (m : ℝ × ℝ) :
    rlmH R τ b m = (R / m.1) ^ 1 • b (chartM R τ m) := rfl

/-- The profile `(R/ρ)^k • c(chartM)` is `C¹` on `ρ > 0` when `c` is. -/
theorem rlm_profile_cd {R : ℝ} (hR : 0 < R) (k : ℕ) {c : Chart → Merid}
    (hc : ContDiffOn ℝ 1 c (Ioi 0 ×ˢ univ)) (τ : ℝ) :
    ContDiffOn ℝ 1 (fun m' : ℝ × ℝ => (R / m'.1) ^ k • c (chartM R τ m')) (Ioi 0 ×ˢ univ) := by
  have h1 : ∀ m' ∈ (Ioi 0 ×ˢ univ : Set (ℝ × ℝ)), m'.1 ≠ 0 := fun m' hm' => ne_of_gt hm'.1
  have hs : ContDiffOn ℝ 1 (fun m' : ℝ × ℝ => R ^ 2 / m'.1 ^ 2) (Ioi 0 ×ˢ univ) :=
    contDiffOn_const.div (contDiff_fst.pow 2).contDiffOn fun m' hm' => pow_ne_zero 2 (h1 m' hm')
  have hspos : ∀ m' ∈ (Ioi 0 ×ˢ univ : Set (ℝ × ℝ)), R ^ 2 / m'.1 ^ 2 ≠ 0 := fun m' hm' =>
    div_ne_zero (pow_ne_zero 2 hR.ne') (pow_ne_zero 2 (h1 m' hm'))
  have hch : ContDiffOn ℝ 1 (chartM R τ) (Ioi 0 ×ˢ univ) := by
    unfold chartM
    refine hs.prodMk (ContDiffOn.prodMk ?_ ?_)
    · exact contDiffOn_const.sub (contDiffOn_const.mul (hs.log hspos))
    · exact (contDiffOn_const.mul contDiff_snd.contDiffOn).div contDiff_fst.contDiffOn h1
  have hmaps : MapsTo (chartM R τ) (Ioi 0 ×ˢ univ) (Ioi 0 ×ˢ univ) := fun m' hm' =>
    ⟨div_pos (pow_pos hR 2) (pow_pos hm'.1 2), trivial⟩
  exact ((contDiffOn_const.div contDiff_fst.contDiffOn h1).pow k).smul (hc.comp hch hmaps)

/-! ## 6. The main theorem -/

theorem ringLapMerChain : RingLapMerChain := by
  intro R hR b hb τ m hm
  have hbC1 : ContDiffOn ℝ 1 b (Ioi 0 ×ˢ univ) := hb.of_le (by norm_num)
  have hQ : ContDiffOn ℝ 1 (fun y => UnforcedLeray.Axi.dQ b y) (Ioi 0 ×ˢ univ) :=
    rlm_fderiv_cd hb (0, (1, 0))
  have hE : ContDiffOn ℝ 1 (fun y => UnforcedLeray.Axi.dEta b y) (Ioi 0 ×ˢ univ) :=
    rlm_fderiv_cd hb (0, (0, 1))
  have hKc : ContDiffOn ℝ 1 (Kc b) (Ioi 0 ×ˢ univ) := by
    unfold Kc
    have hS : ContDiffOn ℝ 1 (fun y => UnforcedLeray.Axi.dS b y) (Ioi 0 ×ˢ univ) :=
      rlm_fderiv_cd hb (1, (0, 0))
    fun_prop
  have hK1 : ContDiffOn ℝ 1 (K1 b) (Ioi 0 ×ˢ univ) := by
    unfold K1; exact hKc.add hbC1
  have hD1 : ContDiffOn ℝ 1 (rlmD1 R b) (Ioi 0 ×ˢ univ) := by
    unfold rlmD1; exact hQ.sub (hK1.const_smul R⁻¹)
  have hx : chartM R τ m ∈ (Ioi 0 ×ˢ univ : Set Chart) :=
    ⟨div_pos (pow_pos hR 2) (pow_pos hm 2), trivial⟩
  have hbA : ContDiffAt ℝ 2 b (chartM R τ m) := hb.contDiffAt (rlm_open.mem_nhds hx)
  have hQd : DifferentiableAt ℝ (fun y => UnforcedLeray.Axi.dQ b y) (chartM R τ m) :=
    rlm_diffAt hQ hx
  have hbd : DifferentiableAt ℝ b (chartM R τ m) := rlm_diffAt hbC1 hx
  have hKcd : DifferentiableAt ℝ (Kc b) (chartM R τ m) := rlm_diffAt hKc hx
  have hK1d : DifferentiableAt ℝ (K1 b) (chartM R τ m) := rlm_diffAt hK1 hx
  have F_comm : UnforcedLeray.Axi.dQ (Kc b) (chartM R τ m)
      = Kc (UnforcedLeray.Axi.dQ b) (chartM R τ m) := rlm_dQ_Kc hbA
  have F_K1 : UnforcedLeray.Axi.dQ (K1 b) (chartM R τ m)
      = UnforcedLeray.Axi.dQ (Kc b) (chartM R τ m) + UnforcedLeray.Axi.dQ b (chartM R τ m) :=
    rlm_dQ_add hKcd hbd
  have F_Q1 : UnforcedLeray.Axi.dQ (rlmD1 R b) (chartM R τ m)
      = UnforcedLeray.Axi.dQ (UnforcedLeray.Axi.dQ b) (chartM R τ m)
        - R⁻¹ • UnforcedLeray.Axi.dQ (K1 b) (chartM R τ m) :=
    rlm_dQ_sub R⁻¹ hQd hK1d
  have F_Kc1 : Kc (rlmD1 R b) (chartM R τ m)
      = Kc (UnforcedLeray.Axi.dQ b) (chartM R τ m) - R⁻¹ • Kc (K1 b) (chartM R τ m) :=
    rlm_Kc_sub R⁻¹ hQd hK1d
  have hY : (UnforcedLeray.Axi.dQ (rlmD1 R b) (chartM R τ m)
      - R⁻¹ • Kc (rlmD1 R b) (chartM R τ m) - (2 * R⁻¹) • rlmD1 R b (chartM R τ m))
      + R⁻¹ • rlmD1 R b (chartM R τ m)
      + UnforcedLeray.Axi.dEta (UnforcedLeray.Axi.dEta b) (chartM R τ m)
      = lapQE b (chartM R τ m) - (2 * R⁻¹) • K1 (UnforcedLeray.Axi.dQ b) (chartM R τ m)
        + (R⁻¹) ^ 2 • K1 (K1 b) (chartM R τ m) := by
    rw [F_Q1, F_Kc1, F_K1, F_comm]
    simp only [rlmD1_apply, rlm_lapQE_apply, rlm_K1_apply]
    module
  -- first-order rules along the profiles
  have E1 : ∀ q : ℝ × ℝ, 0 < q.1 →
      UnforcedLeray.Axi.dρ (rlmH R τ b) q = (R / q.1) ^ 2 • rlmD1 R b (chartM R τ q) := by
    intro q hq
    unfold rlmH
    rw [ringWeightedDRho hR 1 hbC1 τ hq, rlmD1_apply, rlm_K1_apply]
    simp only [show (1 : ℕ) + 1 = 2 from rfl, Nat.cast_one, one_mul]
    module
  have E2 : ∀ q : ℝ × ℝ, 0 < q.1 →
      UnforcedLeray.Axi.dz (rlmH R τ b) q
        = (R / q.1) ^ 2 • UnforcedLeray.Axi.dEta b (chartM R τ q) := by
    intro q hq
    unfold rlmH
    rw [ringWeightedDz hR 1 hbC1 τ hq]
  have hHc : ContDiffOn ℝ 1 (rlmH R τ b) (Ioi 0 ×ˢ univ) := rlm_profile_cd hR 1 hbC1 τ
  have hG1c : ContDiffOn ℝ 1 (rlmG1 R τ b) (Ioi 0 ×ˢ univ) := rlm_profile_cd hR 2 hD1 τ
  have hG2c : ContDiffOn ℝ 1 (rlmG2 R τ b) (Ioi 0 ×ˢ univ) := rlm_profile_cd hR 2 hE τ
  have hHd : ∀ q : ℝ × ℝ, 0 < q.1 → DifferentiableAt ℝ (rlmH R τ b) q :=
    fun q hq => rlm_diffAtP hHc hq
  have hG1d : DifferentiableAt ℝ (rlmG1 R τ b) m := rlm_diffAtP hG1c hm
  have hG2d : DifferentiableAt ℝ (rlmG2 R τ b) m := rlm_diffAtP hG2c hm
  have hmP : m ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) : Set (ℝ × ℝ)) := ⟨hm, trivial⟩
  have C1 : ∀ q : ℝ × ℝ, 0 < q.1 → ∀ j : Fin 2,
      UnforcedLeray.Axi.dρ (fun q' => rlmH R τ b q' j) q = rlmG1 R τ b q j := by
    intro q hq j
    rw [rlm_dρ_comp (hHd q hq) j]
    exact congrArg (fun v : Merid => v j) (E1 q hq)
  have C2 : ∀ q : ℝ × ℝ, 0 < q.1 → ∀ j : Fin 2,
      UnforcedLeray.Axi.dz (fun q' => rlmH R τ b q' j) q = rlmG2 R τ b q j := by
    intro q hq j
    rw [rlm_dz_comp (hHd q hq) j]
    exact congrArg (fun v : Merid => v j) (E2 q hq)
  have ev1 : ∀ j : Fin 2, UnforcedLeray.Axi.dρ (fun q' => rlmH R τ b q' j)
      =ᶠ[nhds m] (fun q => rlmG1 R τ b q j) := by
    intro j
    filter_upwards [rlm_openP.mem_nhds hmP] with q hq
    exact C1 q hq.1 j
  have ev2 : ∀ j : Fin 2, UnforcedLeray.Axi.dz (fun q' => rlmH R τ b q' j)
      =ᶠ[nhds m] (fun q => rlmG2 R τ b q j) := by
    intro j
    filter_upwards [rlm_openP.mem_nhds hmP] with q hq
    exact C2 q hq.1 j
  have key : ∀ j : Fin 2, lapMer (fun q => rlmH R τ b q j) m =
      UnforcedLeray.Axi.dρ (rlmG1 R τ b) m j + rlmG1 R τ b m j / m.1
        + UnforcedLeray.Axi.dz (rlmG2 R τ b) m j := by
    intro j
    unfold lapMer
    rw [rlm_dρ_dρ (ev1 j), C1 m hm j, rlm_dz_dz (ev2 j), rlm_dρ_comp hG1d j,
      rlm_dz_comp hG2d j]
  have V1 : UnforcedLeray.Axi.dρ (rlmG1 R τ b) m
      = (R / m.1) ^ (2 + 1) • (UnforcedLeray.Axi.dQ (rlmD1 R b) (chartM R τ m)
        - R⁻¹ • Kc (rlmD1 R b) (chartM R τ m)
        - (((2 : ℕ) : ℝ) * R⁻¹) • rlmD1 R b (chartM R τ m)) :=
    ringWeightedDRho hR 2 hD1 τ hm
  have V2 : rlmG1 R τ b m = (R / m.1) ^ 2 • rlmD1 R b (chartM R τ m) := rfl
  have V3 : UnforcedLeray.Axi.dz (rlmG2 R τ b) m
      = (R / m.1) ^ (2 + 1) • UnforcedLeray.Axi.dEta (UnforcedLeray.Axi.dEta b) (chartM R τ m) :=
    ringWeightedDz hR 2 hE τ hm
  have hm0 : m.1 ≠ 0 := hm.ne'
  have hR0 : R ≠ 0 := hR.ne'
  have hRi : R * R⁻¹ = 1 := mul_inv_cancel₀ hR0
  have k1 : (R / m.1) ^ 2 / m.1 = (R / m.1) ^ (2 + 1) * R⁻¹ := by
    linear_combination (-(R ^ 2 * m.1⁻¹ ^ 3)) * hRi
  have k2 : (R / m.1) / m.1 ^ 2 = (R / m.1) ^ (2 + 1) * (R⁻¹) ^ 2 := by
    linear_combination (-(R * m.1⁻¹ ^ 3) * (R * R⁻¹ + 1)) * hRi
  have k3 : (R / m.1) * (R ^ 2 / m.1 ^ 2) = (R / m.1) ^ (2 + 1) := by
    ring
  have hfun : (fun m' : ℝ × ℝ => (R / m'.1) • b (chartM R τ m')) = rlmH R τ b := by
    funext m'
    simp [rlmH]
  rw [hfun]
  have e0 : vecLapMer (rlmH R τ b) m 0 = (((R / m.1) * (R ^ 2 / m.1 ^ 2)) •
      (lapQE b (chartM R τ m) - (2 * R⁻¹) • K1 (UnforcedLeray.Axi.dQ b) (chartM R τ m)
        + (R⁻¹) ^ 2 • K1 (K1 b) (chartM R τ m) - (R⁻¹) ^ 2 • erProj (b (chartM R τ m)))) 0 := by
    rw [vecLapMer_apply_zero, key 0, V1, V2, V3, rlmH_pt, k3]
    have hY0 := congrArg (fun v : Merid => v 0) hY
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, rlm_erProj_zero,
      pow_one, Nat.cast_ofNat] at hY0 ⊢
    linear_combination (R / m.1) ^ (2 + 1) * hY0
      + (rlmD1 R b (chartM R τ m)) 0 * k1 - (b (chartM R τ m)) 0 * k2
  have e1 : vecLapMer (rlmH R τ b) m 1 = (((R / m.1) * (R ^ 2 / m.1 ^ 2)) •
      (lapQE b (chartM R τ m) - (2 * R⁻¹) • K1 (UnforcedLeray.Axi.dQ b) (chartM R τ m)
        + (R⁻¹) ^ 2 • K1 (K1 b) (chartM R τ m) - (R⁻¹) ^ 2 • erProj (b (chartM R τ m)))) 1 := by
    rw [vecLapMer_apply_one, key 1, V1, V2, V3, k3]
    have hY1 := congrArg (fun v : Merid => v 1) hY
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, rlm_erProj_one,
      Nat.cast_ofNat] at hY1 ⊢
    linear_combination (R / m.1) ^ (2 + 1) * hY1 + (rlmD1 R b (chartM R τ m)) 1 * k1
  ext i
  fin_cases i
  · exact e0
  · exact e1

end UnforcedLeray.Short.PartIIIb.Concrete
