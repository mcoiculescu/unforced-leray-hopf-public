import UnforcedLeray.Short.PartI.Sub.PartI_T25_1
import UnforcedLeray.Short.PartI.Tasks.TrainFixedBandProof.VelAgeJet.T25_3_Aux
import UnforcedLeray.Short.PartI.Tasks.TrainFixedBandProof.VelAgeJet.T20_1_Aux
import UnforcedLeray.Units.B0147

/-!
# `TrainFixedBandQcDivAgeJet` (`PartI:T25/1/1`, helper for `PartI:T25/3/2`)

Source of record: `the November 2 reference manuscript`, lines 326-336, 468-478,
541-551.

Proves `TrainFixedBandQcDivAgeJet`:
1. Joint smoothness of `(r, z) ↦ Train.matDiv (Train.Qc ν c r) z` on `Ioi 0 ×ˢ univ` from
   `PartI_T25_3.gradS_pc_eq`, `PartI_T25_3.contDiffOn_gradS_of_smS (PartI_T25_3.smS_pc hν hc)`,
   and `PartI_T25_1.sm_advection (vcSmooth_proof ν c hν hc)`.
2. Unweighted (`m = 0`) fixed-band exponential bound on `0 < s ≤ Sg / ν` for
   `ageJet ℓ j (fun r z => Train.matDiv (Train.Qc ν c r) z) s` in `wCellL2 c 0` and `wSupNorm 0`
   via width-differentiation closure of `B0147.GP` and `B0147.BS` (`GP.derivA`, `BS.derivA`,
   `BS.iteratedDeriv_age`) and `(hH.weight 1).bound`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI.VelAgeJetAux
open UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec jet cellL2 wCellL2 jap Vc pc width)
open UnforcedLeray.Short.IIb (UU isOpen_UU mem_UU Sm vcSmooth_proof)

namespace PartI_T25_QcDiv

open UnforcedLeray.GaussianVortex (radiusSq)
open UnforcedLeray.B0146 (XDecay latticeSum shift radiusSq_nonneg fst_sq_le_radiusSq
  hasDerivAt_latticeSum_width)
open UnforcedLeray.B0151 (derivWord)
open UnforcedLeray.B0113 (heatWidth heatWidth_pos hasDerivAt_heatWidth)
open UnforcedLeray.B0147 (G0 GP GBound U GP_U lam lam_pos lam_sq bil BS)

/-! ### 1. Width-differentiation of `lam`, `GP`, and `scaleGP` -/

theorem hasDerivAt_lam {a : ℝ} (ha : 0 < a) :
    HasDerivAt lam (-(1 / 2 : ℝ) * lam a ^ 3) a := by
  have hsq_pos : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hs : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt a)) a := Real.hasDerivAt_sqrt ha.ne'
  have hinv : HasDerivAt lam (-(1 / (2 * Real.sqrt a)) / (Real.sqrt a) ^ 2) a :=
    hs.inv hsq_pos.ne'
  refine hinv.congr_deriv ?_
  unfold lam
  have hne : Real.sqrt a ≠ 0 := hsq_pos.ne'
  field_simp

theorem hasDerivAt_lam_pow (d : ℕ) {a : ℝ} (ha : 0 < a) :
    HasDerivAt (fun b => lam b ^ d) (-(d / 2 : ℝ) * lam a ^ (d + 2)) a := by
  induction d with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_div, neg_zero, zero_mul]
    exact hasDerivAt_const a 1
  | succ d ih =>
    have h := ih.mul (hasDerivAt_lam ha)
    simp only [pow_succ]
    refine h.congr_deriv ?_
    push_cast
    ring

theorem hasDerivAt_G0_scale {a : ℝ} (ha : 0 < a) (w : Plane) :
    HasDerivAt (fun b => G0 (lam b * w.1, lam b * w.2))
      (lam a ^ 2 * ((1 / 4 : ℝ) *
        ((lam a * w.1) * ((lam a * w.1) * G0 (lam a * w.1, lam a * w.2)) +
          (lam a * w.2) * ((lam a * w.2) * G0 (lam a * w.1, lam a * w.2))))) a := by
  have he : ∀ b : ℝ, G0 (lam b * w.1, lam b * w.2) =
      Real.exp (-(lam b ^ 2 * (radiusSq w / 4))) := fun b => by
    unfold G0 radiusSq
    congr 1
    ring
  have hd : HasDerivAt (fun b => Real.exp (-(lam b ^ 2 * (radiusSq w / 4))))
      (Real.exp (-(lam a ^ 2 * (radiusSq w / 4))) *
        -(-((2 : ℕ) / 2 : ℝ) * lam a ^ (2 + 2) * (radiusSq w / 4))) a :=
    (((hasDerivAt_lam_pow 2 ha).mul_const (radiusSq w / 4)).neg).exp
  rw [show (fun b => G0 (lam b * w.1, lam b * w.2)) =
      fun b => Real.exp (-(lam b ^ 2 * (radiusSq w / 4))) from funext he]
  refine hd.congr_deriv ?_
  rw [← he a]
  unfold radiusSq
  push_cast
  ring

theorem GP_derivA {f : Plane → ℝ} (hf : GP f) :
    ∃ f' : Plane → ℝ, GP f' ∧ ∀ {a : ℝ}, 0 < a → ∀ w : Plane,
      HasDerivAt (fun b => f (lam b * w.1, lam b * w.2))
        (lam a ^ 2 * f' (lam a * w.1, lam a * w.2)) a := by
  induction hf with
  | gauss =>
    refine ⟨fun y => (1 / 4 : ℝ) * (y.1 * (y.1 * G0 y) + y.2 * (y.2 * G0 y)),
      ((GP.gauss.mulX.mulX).add (GP.gauss.mulY.mulY)).smul (1 / 4),
      fun ha w => hasDerivAt_G0_scale ha w⟩
  | @mulX g hg ih =>
    obtain ⟨g', hg', hdg⟩ := ih
    refine ⟨fun y => -(1 / 2 : ℝ) * (y.1 * g y) + y.1 * g' y,
      (hg.mulX.smul (-(1 / 2))).add hg'.mulX, fun ha w => ?_⟩
    exact (((hasDerivAt_lam ha).mul_const w.1).mul (hdg ha w)).congr_deriv (by ring)
  | @mulY g hg ih =>
    obtain ⟨g', hg', hdg⟩ := ih
    refine ⟨fun y => -(1 / 2 : ℝ) * (y.2 * g y) + y.2 * g' y,
      (hg.mulY.smul (-(1 / 2))).add hg'.mulY, fun ha w => ?_⟩
    exact (((hasDerivAt_lam ha).mul_const w.2).mul (hdg ha w)).congr_deriv (by ring)
  | @add f₁ f₂ _ _ ih₁ ih₂ =>
    obtain ⟨f₁', hf₁', hd₁⟩ := ih₁
    obtain ⟨f₂', hf₂', hd₂⟩ := ih₂
    refine ⟨fun y => f₁' y + f₂' y, hf₁'.add hf₂', fun ha w => ?_⟩
    exact ((hd₁ ha w).add (hd₂ ha w)).congr_deriv (by ring)
  | @smul k g _ ih =>
    obtain ⟨g', hg', hdg⟩ := ih
    refine ⟨fun y => k * g' y, hg'.smul k, fun ha w => ?_⟩
    exact ((hdg ha w).const_mul k).congr_deriv (by ring)

/-- Width-rescaled `GP` profile `lam a ^ d * f (lam a * w.1, lam a * w.2)`. -/
def scaleGP (d : ℕ) (f : Plane → ℝ) (a : ℝ) (w : Plane) : ℝ :=
  lam a ^ d * f (lam a * w.1, lam a * w.2)

theorem scaleGP_derivA (d : ℕ) {f : Plane → ℝ} (hf : GP f) :
    ∃ f' : Plane → ℝ, GP f' ∧ ∀ {a : ℝ}, 0 < a → ∀ w : Plane,
      HasDerivAt (fun b => scaleGP d f b w) (scaleGP (d + 2) f' a w) a := by
  obtain ⟨g, hg, hdg⟩ := GP_derivA hf
  refine ⟨fun y => -(d / 2 : ℝ) * f y + g y, (hf.smul (-(d / 2 : ℝ))).add hg, fun ha w => ?_⟩
  unfold scaleGP
  exact ((hasDerivAt_lam_pow d ha).mul (hdg ha w)).congr_deriv (by ring)

theorem scaleGP_unif_bound (d : ℕ) {f : Plane → ℝ} (hf : GP f) {A₁ A₂ : ℝ}
    (hA₁ : 0 < A₁) (hA₁₂ : A₁ ≤ A₂) :
    ∃ K β : ℝ, 0 ≤ K ∧ 0 < β ∧ ∀ b ∈ Icc A₁ A₂, ∀ w : Plane,
      |scaleGP d f b w| ≤ K * Real.exp (-(β * w.1 ^ 2)) := by
  obtain ⟨Kf, βf, hKf, hβf, hbf⟩ := hf.bound
  have hA₂ : 0 < A₂ := hA₁.trans_le hA₁₂
  have hlA₁ : 0 < lam A₁ := lam_pos hA₁
  refine ⟨lam A₁ ^ d * Kf, βf * A₂⁻¹, by positivity, by positivity, fun b hb w => ?_⟩
  have hb_pos : 0 < b := hA₁.trans_le hb.1
  have hlb_pos : 0 < lam b := lam_pos hb_pos
  have hlb_le : lam b ≤ lam A₁ :=
    inv_anti₀ (Real.sqrt_pos.mpr hA₁) (Real.sqrt_le_sqrt hb.1)
  have hpow_le : lam b ^ d ≤ lam A₁ ^ d := pow_le_pow_left₀ hlb_pos.le hlb_le d
  have hinv_le : A₂⁻¹ ≤ b⁻¹ := inv_anti₀ hb_pos hb.2
  let y : Plane := (lam b * w.1, lam b * w.2)
  have hfy : |f y| ≤ Kf * Real.exp (-(βf * y.1 ^ 2)) := by
    refine (hbf y).trans ?_
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left (fst_sq_le_radiusSq y) hβf.le))) hKf
  have hy1 : y.1 ^ 2 = b⁻¹ * w.1 ^ 2 := by
    dsimp [y]
    rw [mul_pow, lam_sq hb_pos]
  have hexp : Real.exp (-(βf * y.1 ^ 2)) ≤ Real.exp (-(βf * A₂⁻¹ * w.1 ^ 2)) := by
    rw [hy1]
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    calc βf * A₂⁻¹ * w.1 ^ 2
        ≤ βf * b⁻¹ * w.1 ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv_le hβf.le) (sq_nonneg _)
      _ = βf * (b⁻¹ * w.1 ^ 2) := by ring
  unfold scaleGP
  rw [abs_mul, abs_of_nonneg (pow_nonneg hlb_pos.le d)]
  calc lam b ^ d * |f y|
      ≤ lam A₁ ^ d * (Kf * Real.exp (-(βf * y.1 ^ 2))) :=
        mul_le_mul hpow_le hfy (abs_nonneg _) (pow_nonneg hlA₁.le d)
    _ ≤ lam A₁ ^ d * (Kf * Real.exp (-(βf * A₂⁻¹ * w.1 ^ 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hKf) (pow_nonneg hlA₁.le d)
    _ = lam A₁ ^ d * Kf * Real.exp (-(βf * A₂⁻¹ * w.1 ^ 2)) := by ring

theorem scaleGP_xdecay (d : ℕ) {f : Plane → ℝ} (hf : GP f) {a : ℝ} (ha : 0 < a) :
    XDecay (scaleGP d f a) := by
  obtain ⟨K, β, hK, hβ, hb⟩ := scaleGP_unif_bound d hf ha le_rfl
  exact ⟨K, β, hK, hβ, fun w => hb a ⟨le_rfl, le_rfl⟩ w⟩

theorem scaleGP_mul_unif_bound (d₁ d₂ : ℕ) {f g : Plane → ℝ} (hf : GP f) (hg : GP g)
    {A₁ A₂ : ℝ} (hA₁ : 0 < A₁) (hA₁₂ : A₁ ≤ A₂) :
    ∃ K β : ℝ, 0 ≤ K ∧ 0 < β ∧ ∀ b ∈ Icc A₁ A₂, ∀ w : Plane,
      |scaleGP d₁ f b w * scaleGP d₂ g b w| ≤ K * Real.exp (-(β * w.1 ^ 2)) := by
  obtain ⟨K₁, β₁, hK₁, hβ₁, hb₁⟩ := scaleGP_unif_bound d₁ hf hA₁ hA₁₂
  obtain ⟨K₂, β₂, hK₂, hβ₂, hb₂⟩ := scaleGP_unif_bound d₂ hg hA₁ hA₁₂
  refine ⟨K₁ * K₂, β₁, mul_nonneg hK₁ hK₂, hβ₁, fun b hb w => ?_⟩
  have h1 := hb₁ b hb w
  have h2 : |scaleGP d₂ g b w| ≤ K₂ := by
    calc |scaleGP d₂ g b w|
        ≤ K₂ * Real.exp (-(β₂ * w.1 ^ 2)) := hb₂ b hb w
      _ ≤ K₂ * 1 := mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg w.1, hβ₂.le])) hK₂
      _ = K₂ := mul_one _
  rw [abs_mul]
  calc |scaleGP d₁ f b w| * |scaleGP d₂ g b w|
      ≤ (K₁ * Real.exp (-(β₁ * w.1 ^ 2))) * K₂ :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = K₁ * K₂ * Real.exp (-(β₁ * w.1 ^ 2)) := by ring

theorem scaleGP_mul_xdecay (d₁ d₂ : ℕ) {f g : Plane → ℝ} (hf : GP f) (hg : GP g)
    {a : ℝ} (ha : 0 < a) :
    XDecay (fun w => scaleGP d₁ f a w * scaleGP d₂ g a w) := by
  obtain ⟨K, β, hK, hβ, hb⟩ := scaleGP_mul_unif_bound d₁ d₂ hf hg ha le_rfl
  exact ⟨K, β, hK, hβ, fun w => hb a ⟨le_rfl, le_rfl⟩ w⟩

/-! ### 2. Width-differentiation of `bil` and `BS` -/

theorem scaleGP_latticeSum_eq (d : ℕ) (f : Plane → ℝ) (c a : ℝ) (z : Plane) :
    latticeSum c (scaleGP d f a) z =
      lam a ^ d * latticeSum (lam a * c) f (lam a * z.1, lam a * z.2) :=
  B0147.latticeSum_scale (fun _ => rfl) z

theorem scaleGP_mul_latticeSum_eq (d₁ d₂ : ℕ) (f g : Plane → ℝ) (c a : ℝ) (z : Plane) :
    latticeSum c (fun w => scaleGP d₁ f a w * scaleGP d₂ g a w) z =
      lam a ^ (d₁ + d₂) *
        latticeSum (lam a * c) (fun y => f y * g y) (lam a * z.1, lam a * z.2) := by
  refine B0147.latticeSum_scale (fun w => ?_) z
  unfold scaleGP
  rw [pow_add]
  ring

theorem bil_scale_eq_latticeSum (d : ℕ) {f g : Plane → ℝ} (hf : GP f) (hg : GP g)
    {c a : ℝ} (hc : c ≠ 0) (ha : 0 < a) (z : Plane) :
    lam a ^ d * bil (lam a * c) f g (lam a * z.1, lam a * z.2) =
      latticeSum c (scaleGP d f a) z * latticeSum c (scaleGP 0 g a) z -
        latticeSum c (fun w => scaleGP d f a w * scaleGP 0 g a w) z := by
  have hL : lam a * c ≠ 0 := mul_ne_zero (lam_pos ha).ne' hc
  rw [scaleGP_latticeSum_eq d f c a z, scaleGP_latticeSum_eq 0 g c a z,
    scaleGP_mul_latticeSum_eq d 0 f g c a z, pow_zero, one_mul, add_zero,
    B0147.bil_eq hf.xdecay hg.xdecay hL]
  ring

theorem hasDerivAt_bil_scale (d : ℕ) {f g f' g' : Plane → ℝ}
    (hf : GP f) (hg : GP g) (hf' : GP f') (hg' : GP g')
    (hdf : ∀ {b : ℝ}, 0 < b → ∀ w : Plane, HasDerivAt (fun b' => scaleGP d f b' w) (scaleGP (d + 2) f' b w) b)
    (hdg : ∀ {b : ℝ}, 0 < b → ∀ w : Plane, HasDerivAt (fun b' => scaleGP 0 g b' w) (scaleGP 2 g' b w) b)
    {c a : ℝ} (hc : c ≠ 0) (ha : 0 < a) (z : Plane) :
    HasDerivAt (fun b => lam b ^ d * bil (lam b * c) f g (lam b * z.1, lam b * z.2))
      (lam a ^ (d + 2) *
        (bil (lam a * c) f' g (lam a * z.1, lam a * z.2) +
          bil (lam a * c) f g' (lam a * z.1, lam a * z.2))) a := by
  have ha_half : 0 < a / 2 := half_pos ha
  have ha_le : a / 2 ≤ 2 * a := by linarith
  have h1 : HasDerivAt (fun b => latticeSum c (scaleGP d f b) z)
      (latticeSum c (scaleGP (d + 2) f' a) z) a :=
    hasDerivAt_latticeSum_width hc ha (fun b hb w => hdf hb w)
      (scaleGP_xdecay d hf ha) (scaleGP_unif_bound (d + 2) hf' ha_half ha_le) z
  have h2 : HasDerivAt (fun b => latticeSum c (scaleGP 0 g b) z)
      (latticeSum c (scaleGP 2 g' a) z) a :=
    hasDerivAt_latticeSum_width hc ha (fun b hb w => hdg hb w)
      (scaleGP_xdecay 0 hg ha) (scaleGP_unif_bound 2 hg' ha_half ha_le) z
  obtain ⟨K₁, β₁, hK₁, hβ₁, hb₁⟩ := scaleGP_mul_unif_bound (d + 2) 0 hf' hg ha_half ha_le
  obtain ⟨K₂, β₂, hK₂, hβ₂, hb₂⟩ := scaleGP_mul_unif_bound d 2 hf hg' ha_half ha_le
  have hprod_unif : ∃ K β : ℝ, 0 ≤ K ∧ 0 < β ∧ ∀ b ∈ Icc (a / 2) (2 * a), ∀ w : Plane,
      |scaleGP (d + 2) f' b w * scaleGP 0 g b w + scaleGP d f b w * scaleGP 2 g' b w| ≤
        K * Real.exp (-(β * w.1 ^ 2)) := by
    refine ⟨K₁ + K₂, min β₁ β₂, by positivity, lt_min hβ₁ hβ₂, fun b hb w => ?_⟩
    have e1 : Real.exp (-(β₁ * w.1 ^ 2)) ≤ Real.exp (-(min β₁ β₂ * w.1 ^ 2)) :=
      Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)))
    have e2 : Real.exp (-(β₂ * w.1 ^ 2)) ≤ Real.exp (-(min β₁ β₂ * w.1 ^ 2)) :=
      Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)))
    calc |scaleGP (d + 2) f' b w * scaleGP 0 g b w + scaleGP d f b w * scaleGP 2 g' b w|
        ≤ |scaleGP (d + 2) f' b w * scaleGP 0 g b w| + |scaleGP d f b w * scaleGP 2 g' b w| :=
          abs_add_le _ _
      _ ≤ K₁ * Real.exp (-(min β₁ β₂ * w.1 ^ 2)) + K₂ * Real.exp (-(min β₁ β₂ * w.1 ^ 2)) :=
          add_le_add ((hb₁ b hb w).trans (mul_le_mul_of_nonneg_left e1 hK₁))
            ((hb₂ b hb w).trans (mul_le_mul_of_nonneg_left e2 hK₂))
      _ = (K₁ + K₂) * Real.exp (-(min β₁ β₂ * w.1 ^ 2)) := by ring
  have h3 : HasDerivAt (fun b => latticeSum c (fun w => scaleGP d f b w * scaleGP 0 g b w) z)
      (latticeSum c (fun w =>
        scaleGP (d + 2) f' a w * scaleGP 0 g a w + scaleGP d f a w * scaleGP 2 g' a w) z) a :=
    hasDerivAt_latticeSum_width hc ha (fun b hb w => (hdf hb w).mul (hdg hb w))
      (scaleGP_mul_xdecay d 0 hf hg ha) hprod_unif z
  have hev : (fun b => lam b ^ d * bil (lam b * c) f g (lam b * z.1, lam b * z.2)) =ᶠ[nhds a]
      fun b => latticeSum c (scaleGP d f b) z * latticeSum c (scaleGP 0 g b) z -
        latticeSum c (fun w => scaleGP d f b w * scaleGP 0 g b w) z := by
    filter_upwards [Ioi_mem_nhds ha] with b hb using bil_scale_eq_latticeSum d hf hg hc hb z
  refine (((h1.mul h2).sub h3).congr_of_eventuallyEq hev).congr_deriv ?_
  have hL : lam a * c ≠ 0 := mul_ne_zero (lam_pos ha).ne' hc
  rw [B0147.latticeSum_add (scaleGP_mul_xdecay (d + 2) 0 hf' hg ha)
      (scaleGP_mul_xdecay d 2 hf hg' ha) hc z,
    scaleGP_latticeSum_eq (d + 2) f' c a z,
    scaleGP_latticeSum_eq 0 g c a z,
    scaleGP_latticeSum_eq d f c a z,
    scaleGP_latticeSum_eq 2 g' c a z,
    scaleGP_mul_latticeSum_eq (d + 2) 0 f' g c a z,
    scaleGP_mul_latticeSum_eq d 2 f g' c a z,
    pow_zero, one_mul, add_zero,
    B0147.bil_eq hf'.xdecay hg.xdecay hL,
    B0147.bil_eq hf.xdecay hg'.xdecay hL,
    pow_add (lam a) d 2]
  ring

theorem BS_derivA {H : ℝ → Plane → ℝ} (hH : BS H) (d : ℕ) :
    ∃ H' : ℝ → Plane → ℝ, BS H' ∧ ∀ {c a : ℝ}, c ≠ 0 → 0 < a → ∀ z : Plane,
      HasDerivAt (fun b => lam b ^ d * H (lam b * c) (lam b * z.1, lam b * z.2))
        (lam a ^ (d + 2) * H' (lam a * c) (lam a * z.1, lam a * z.2)) a := by
  induction hH with
  | @pair f g hf hg =>
    obtain ⟨f', hf', hdf⟩ := scaleGP_derivA d hf
    obtain ⟨g', hg', hdg⟩ := scaleGP_derivA 0 hg
    exact ⟨fun L y => bil L f' g y + bil L f g' y, (BS.pair hf' hg).add (BS.pair hf hg'),
      fun hc ha z => hasDerivAt_bil_scale d hf hg hf' hg' hdf hdg hc ha z⟩
  | @add H₁ H₂ _ _ ih₁ ih₂ =>
    obtain ⟨H₁', hH₁', hd₁⟩ := ih₁
    obtain ⟨H₂', hH₂', hd₂⟩ := ih₂
    refine ⟨fun L y => H₁' L y + H₂' L y, hH₁'.add hH₂', fun hc ha z => ?_⟩
    have h := (hd₁ hc ha z).add (hd₂ hc ha z)
    refine (h.congr_of_eventuallyEq (Eventually.of_forall fun b => ?_)).congr_deriv (by ring)
    dsimp [Pi.add_apply]
    ring

theorem BS_iteratedDeriv_age {H : ℝ → Plane → ℝ} (hH : BS H) (d ℓ : ℕ) :
    ∃ H' : ℝ → Plane → ℝ, BS H' ∧ ∀ {ν c s : ℝ}, 0 < ν → c ≠ 0 → 0 < s → ∀ z : Plane,
      iteratedDeriv ℓ
        (fun r => lam (heatWidth ν r) ^ d *
          H (lam (heatWidth ν r) * c) (lam (heatWidth ν r) * z.1, lam (heatWidth ν r) * z.2)) s =
        ν ^ ℓ * (lam (heatWidth ν s) ^ (d + 2 * ℓ) *
          H' (lam (heatWidth ν s) * c) (lam (heatWidth ν s) * z.1, lam (heatWidth ν s) * z.2)) := by
  induction ℓ with
  | zero =>
    refine ⟨H, hH, fun _ _ _ _ => ?_⟩
    simp
  | succ ℓ ih =>
    obtain ⟨H₁, hH₁, h_ih⟩ := ih
    obtain ⟨H₂, hH₂, hd₂⟩ := BS_derivA hH₁ (d + 2 * ℓ)
    refine ⟨H₂, hH₂, fun {ν c s} hν hc hs z => ?_⟩
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv ℓ
        (fun r => lam (heatWidth ν r) ^ d *
          H (lam (heatWidth ν r) * c) (lam (heatWidth ν r) * z.1, lam (heatWidth ν r) * z.2)) =ᶠ[nhds s]
        fun r => ν ^ ℓ * (lam (heatWidth ν r) ^ (d + 2 * ℓ) *
          H₁ (lam (heatWidth ν r) * c) (lam (heatWidth ν r) * z.1, lam (heatWidth ν r) * z.2)) := by
      filter_upwards [Ioi_mem_nhds hs] with r hr using h_ih hν hc hr z
    rw [hev.deriv_eq]
    have ha : 0 < heatWidth ν s := heatWidth_pos hν hs.le
    have hcomp : HasDerivAt
        (fun r => lam (heatWidth ν r) ^ (d + 2 * ℓ) *
          H₁ (lam (heatWidth ν r) * c) (lam (heatWidth ν r) * z.1, lam (heatWidth ν r) * z.2))
        ((lam (heatWidth ν s) ^ (d + 2 * ℓ + 2) *
          H₂ (lam (heatWidth ν s) * c) (lam (heatWidth ν s) * z.1, lam (heatWidth ν s) * z.2)) * ν) s :=
      (hd₂ hc ha z).comp s (hasDerivAt_heatWidth ν s)
    rw [(hcomp.const_mul (ν ^ ℓ)).deriv]
    have hexp : d + 2 * (ℓ + 1) = d + 2 * ℓ + 2 := by omega
    rw [hexp, pow_succ]
    ring

/-! ### 3. Joint smoothness and age-jet bounds for `Train.matDiv (Train.Qc ν c)` -/

theorem sm_qcDiv {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c) :
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => Train.matDiv (Train.Qc ν c x.1) x.2)
      (Ioi 0 ×ˢ univ) := by
  have hgrad : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => Train.gradS (pc ν c x.1) x.2)
      (Ioi 0 ×ˢ univ) :=
    UnforcedLeray.Short.PartI.VelAgeJetAux.contDiffOn_gradS_of_smS (PartI_T25_3.smS_pc hν hc)
  have hadv : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => Train.advection (Vc ν c x.1) x.2)
      (Ioi 0 ×ˢ univ) :=
    PartI_T25_1.sm_advection (vcSmooth_proof ν c hν hc)
  refine (hgrad.add hadv).congr fun ⟨r, w⟩ hx => ?_
  have hr : 0 < r := hx.1
  have heq := PartI_T25_3.gradS_pc_eq hν hc.ne' hr.le w
  ext k
  have hk := congrArg (fun v : Vec => v k) heq
  simp only [PiLp.add_apply, PiLp.sub_apply] at hk ⊢
  linarith

theorem qcDiv_comp_scale (m : Fin 2) :
    ∃ H : ℝ → Plane → ℝ, BS H ∧ ∀ {ν c r : ℝ}, 0 < ν → c ≠ 0 → 0 ≤ r → ∀ z : Plane,
      Train.matDiv (Train.Qc ν c r) z m =
        lam (heatWidth ν r) ^ 7 *
          H (lam (heatWidth ν r) * c) (lam (heatWidth ν r) * z.1, lam (heatWidth ν r) * z.2) := by
  obtain ⟨H₀, hH₀, hw₀⟩ := (BS.pair (GP_U 0) (GP_U m)).deriv_word [true]
  obtain ⟨H₁, hH₁, hw₁⟩ := (BS.pair (GP_U 1) (GP_U m)).deriv_word [false]
  refine ⟨fun L y => H₀ L y + H₁ L y, hH₀.add hH₁, fun {ν c r} hν hc hr z => ?_⟩
  have ha : 0 < heatWidth ν r := heatWidth_pos hν hr
  have hQ0 := congrFun (B0147.derivWord_cross (ν := ν) (c := c) (s := r) hc ha 0 m [true] hw₀) z
  have hQ1 := congrFun (B0147.derivWord_cross (ν := ν) (c := c) (s := r) hc ha 1 m [false] hw₁) z
  have heq0 : Cyl.partialQ (fun w => Train.Qc ν c r w 0 m) z =
      derivWord [true] (fun w => B0146.crossStress ν c r w 0 m) z := by
    have hfun : (fun w => Train.Qc ν c r w 0 m) = fun w => B0146.crossStress ν c r w 0 m :=
      funext fun w => Train.Qc_eq ν c r w 0 m
    rw [hfun]
    rfl
  have heq1 : Cyl.partialEta (fun w => Train.Qc ν c r w 1 m) z =
      derivWord [false] (fun w => B0146.crossStress ν c r w 1 m) z := by
    have hfun : (fun w => Train.Qc ν c r w 1 m) = fun w => B0146.crossStress ν c r w 1 m :=
      funext fun w => Train.Qc_eq ν c r w 1 m
    rw [hfun]
    rfl
  have hm : Train.matDiv (Train.Qc ν c r) z m =
      Cyl.partialQ (fun w => Train.Qc ν c r w 0 m) z +
        Cyl.partialEta (fun w => Train.Qc ν c r w 1 m) z := by
    fin_cases m <;> simp [Train.matDiv, Train.toVec_zero, Train.toVec_one]
  rw [hm, heq0, heq1, hQ0, hQ1]
  simp only [List.length_singleton, pow_one]
  ring

theorem qcDiv_word_age_bound (m : Fin 2) (ℓ : ℕ) (w : List Bool) :
    ∃ C γ : ℝ, 0 ≤ C ∧ 0 < γ ∧
      ∀ {ν c s : ℝ}, 0 < ν → ν ≤ 1 → 0 < c → 0 < s → heatWidth ν s ≤ c ^ 2 →
        ∀ z : Plane,
          (1 + z.2 ^ 2 / heatWidth ν s) *
            |derivWord w (fun x => iteratedDeriv ℓ (fun r => Train.matDiv (Train.Qc ν c r) x m) s) z| ≤
              C * Real.exp (-(γ * c ^ 2 / heatWidth ν s)) := by
  obtain ⟨H_m, hH_m, hEq_m⟩ := qcDiv_comp_scale m
  obtain ⟨H_ℓ, hH_ℓ, hEq_ℓ⟩ := BS_iteratedDeriv_age hH_m 7 ℓ
  obtain ⟨H_w, hH_w, hw⟩ := hH_ℓ.deriv_word w
  obtain ⟨C, γ, hC, hγ, hb⟩ := (hH_w.weight 1).bound
  refine ⟨C, γ, hC, hγ, fun {ν c s} hν hν1 hc hs hac z => ?_⟩
  have ha1 : 1 ≤ heatWidth ν s := by
    unfold heatWidth
    linarith [mul_pos hν hs]
  have ha : 0 < heatWidth ν s := by linarith
  have hl : 0 < lam (heatWidth ν s) := lam_pos ha
  have hl1 : lam (heatWidth ν s) ≤ 1 := by
    unfold lam
    exact inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr ha1)
  have hL1 : 1 ≤ lam (heatWidth ν s) * c := B0147.one_le_lam_mul ha hc hac
  have hLne : lam (heatWidth ν s) * c ≠ 0 := by positivity
  have hslice : (fun x : Plane => iteratedDeriv ℓ (fun r => Train.matDiv (Train.Qc ν c r) x m) s) =
      fun x : Plane =>
        (ν ^ ℓ * lam (heatWidth ν s) ^ (7 + 2 * ℓ)) *
          H_ℓ (lam (heatWidth ν s) * c) (lam (heatWidth ν s) * x.1, lam (heatWidth ν s) * x.2) := by
    funext x
    have hev : (fun r => Train.matDiv (Train.Qc ν c r) x m) =ᶠ[nhds s]
        fun r => lam (heatWidth ν r) ^ 7 *
          H_m (lam (heatWidth ν r) * c) (lam (heatWidth ν r) * x.1, lam (heatWidth ν r) * x.2) := by
      filter_upwards [Ioi_mem_nhds hs] with r hr using hEq_m hν hc.ne' hr.le x
    rw [hev.iteratedDeriv_eq ℓ, hEq_ℓ hν hc.ne' hs x, mul_assoc]
  have hword := congrFun (B0147.derivWord_scale w (ν ^ ℓ * lam (heatWidth ν s) ^ (7 + 2 * ℓ))
    (lam (heatWidth ν s)) (H_ℓ (lam (heatWidth ν s) * c))) z
  rw [hslice, hword, hw _ hLne]
  have hw_eq := B0147.weight_eq ha 1 z
  simp only [pow_one] at hw_eq
  rw [hw_eq]
  set l := lam (heatWidth ν s)
  have hcoeff_nn : 0 ≤ ν ^ ℓ * l ^ (7 + 2 * ℓ) * l ^ w.length := by positivity
  have hcoeff_le1 : ν ^ ℓ * l ^ (7 + 2 * ℓ) * l ^ w.length ≤ 1 := by
    rw [mul_assoc, ← pow_add]
    exact mul_le_one₀ (pow_le_one₀ hν.le hν1) (pow_nonneg hl.le _) (pow_le_one₀ hl.le hl1)
  have hBS := hb (l * c) hL1 (l * z.1, l * z.2)
  simp only [pow_one] at hBS
  have hE2_le1 : Real.exp (-(γ * (l * z.2) ^ 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (l * z.2), hγ.le])
  have hBS' : |(1 + (l * z.2) ^ 2) * H_w (l * c) (l * z.1, l * z.2)| ≤
      C * Real.exp (-(γ * c ^ 2 / heatWidth ν s)) := by
    calc |(1 + (l * z.2) ^ 2) * H_w (l * c) (l * z.1, l * z.2)|
        ≤ C * Real.exp (-(γ * (l * c) ^ 2)) * Real.exp (-(γ * (l * z.2) ^ 2)) := hBS
      _ ≤ C * Real.exp (-(γ * (l * c) ^ 2)) * 1 :=
          mul_le_mul_of_nonneg_left hE2_le1 (by positivity)
      _ = C * Real.exp (-(γ * c ^ 2 / heatWidth ν s)) := by
          rw [mul_one, B0147.lam_mul_sq ha, mul_div_assoc]
  have hw_nn : 0 ≤ 1 + (l * z.2) ^ 2 := by positivity
  calc (1 + (l * z.2) ^ 2) * |ν ^ ℓ * l ^ (7 + 2 * ℓ) * l ^ w.length *
        H_w (l * c) (l * z.1, l * z.2)|
      = (ν ^ ℓ * l ^ (7 + 2 * ℓ) * l ^ w.length) *
          |(1 + (l * z.2) ^ 2) * H_w (l * c) (l * z.1, l * z.2)| := by
        rw [abs_mul, abs_mul (1 + _), abs_of_nonneg hcoeff_nn, abs_of_nonneg hw_nn]
        ring
    _ ≤ 1 * (C * Real.exp (-(γ * c ^ 2 / heatWidth ν s))) :=
        mul_le_mul hcoeff_le1 hBS' (abs_nonneg _) zero_le_one
    _ = C * Real.exp (-(γ * c ^ 2 / heatWidth ν s)) := one_mul _

theorem qcDiv_word_list_bound (m : Fin 2) (ℓ : ℕ) :
    ∀ L : List (List Bool),
      ∃ C γ : ℝ, 0 ≤ C ∧ 0 < γ ∧
        ∀ {ν c s : ℝ}, 0 < ν → ν ≤ 1 → 0 < c → 0 < s → heatWidth ν s ≤ c ^ 2 →
          ∀ z : Plane, ∀ w ∈ L,
            (1 + z.2 ^ 2 / heatWidth ν s) *
              |derivWord w (fun x => iteratedDeriv ℓ (fun r => Train.matDiv (Train.Qc ν c r) x m) s) z| ≤
                C * Real.exp (-(γ * c ^ 2 / heatWidth ν s))
  | [] => ⟨0, 1, le_rfl, one_pos, fun _ _ _ _ _ _ _ hw => False.elim (List.not_mem_nil hw)⟩
  | w₀ :: L => by
    obtain ⟨C₁, γ₁, hC₁, hγ₁, hb₁⟩ := qcDiv_word_age_bound m ℓ w₀
    obtain ⟨C₂, γ₂, hC₂, hγ₂, hb₂⟩ := qcDiv_word_list_bound m ℓ L
    refine ⟨C₁ + C₂, min γ₁ γ₂, add_nonneg hC₁ hC₂, lt_min hγ₁ hγ₂,
      fun {ν c s} hν hν1 hc hs hac z w hw => ?_⟩
    have ha : 0 < heatWidth ν s := heatWidth_pos hν hs.le
    have hY : 0 ≤ c ^ 2 / heatWidth ν s := div_nonneg (sq_nonneg c) ha.le
    rcases List.mem_cons.mp hw with rfl | hwL
    · refine (hb₁ hν hν1 hc hs hac z).trans ?_
      rw [mul_div_assoc, mul_div_assoc]
      exact mul_le_mul (by linarith)
        (Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left _ _) hY)))
        (Real.exp_nonneg _) (add_nonneg hC₁ hC₂)
    · refine (hb₂ hν hν1 hc hs hac z w hwL).trans ?_
      rw [mul_div_assoc, mul_div_assoc]
      exact mul_le_mul (by linarith)
        (Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_right _ _) hY)))
        (Real.exp_nonneg _) (add_nonneg hC₁ hC₂)

theorem qcDiv_comp_ageJet_bound (m : Fin 2) (ℓ j : ℕ) :
    ∃ C γ : ℝ, 0 < C ∧ 0 < γ ∧
      ∀ {ν c s : ℝ}, 0 < ν → ν ≤ 1 → 0 < c → 0 < s → heatWidth ν s ≤ c ^ 2 →
        ∀ z : Plane,
          (1 + z.2 ^ 2 / heatWidth ν s) *
            ‖iteratedFDeriv ℝ j (fun x => iteratedDeriv ℓ (fun r => Train.matDiv (Train.Qc ν c r) x m) s) z‖ ≤
              C * Real.exp (-(γ * c ^ 2 / heatWidth ν s)) := by
  obtain ⟨C₀, γ, hC₀, hγ, hb⟩ := qcDiv_word_list_bound m ℓ (wordsOfLength j).toList
  refine ⟨(2 : ℝ) ^ j * (C₀ + 1), γ, by positivity, hγ, fun {ν c s} hν hν1 hc hs hac z => ?_⟩
  let qcDiv : ℝ → Plane → Vec := fun r x => Train.matDiv (Train.Qc ν c r) x
  have hsm_qc : Sm (fun x : ℝ × Plane => qcDiv x.1 x.2) := sm_qcDiv hν hc
  have hslice_vec : ContDiff ℝ ∞ (fun x : Plane => iteratedDeriv ℓ (fun r => qcDiv r x) s) :=
    contDiff_slice_iteratedDeriv_of_contDiffOn qcDiv hsm_qc ℓ hs
  have hslice_m : ContDiff ℝ ∞
      (fun x : Plane => iteratedDeriv ℓ (fun r => qcDiv r x m) s) := by
    have heq : (fun x : Plane => iteratedDeriv ℓ (fun r => qcDiv r x m) s) =
        fun x : Plane => (iteratedDeriv ℓ (fun r => qcDiv r x) s) m :=
      funext fun x => PartI_T20.iteratedDeriv_vec_proj_eq hsm_qc m ℓ hs x
    rw [heq]
    exact UnforcedLeray.Short.IIb.contDiff_comp_proj hslice_vec m
  have hcjw := cjw_norm_le_sum
    (fun x : Plane => iteratedDeriv ℓ (fun r => qcDiv r x m) s) hslice_m j z
  have ha : 0 < heatWidth ν s := heatWidth_pos hν hs.le
  have hw_nn : 0 ≤ 1 + z.2 ^ 2 / heatWidth ν s := by positivity
  have hcard : ((wordsOfLength j).card : ℝ) ≤ (2 : ℝ) ^ j := by
    have hc_nat : (wordsOfLength j).card ≤ 2 ^ j := by
      unfold wordsOfLength
      exact Finset.card_image_le.trans (by simp)
    exact_mod_cast hc_nat
  calc (1 + z.2 ^ 2 / heatWidth ν s) *
        ‖iteratedFDeriv ℝ j (fun x => iteratedDeriv ℓ (fun r => qcDiv r x m) s) z‖
      ≤ (1 + z.2 ^ 2 / heatWidth ν s) *
          ∑ w ∈ wordsOfLength j,
            |derivWord w (fun x => iteratedDeriv ℓ (fun r => qcDiv r x m) s) z| :=
        mul_le_mul_of_nonneg_left hcjw hw_nn
    _ = ∑ w ∈ wordsOfLength j,
          (1 + z.2 ^ 2 / heatWidth ν s) *
            |derivWord w (fun x => iteratedDeriv ℓ (fun r => qcDiv r x m) s) z| :=
        Finset.mul_sum _ _ _
    _ ≤ ∑ _w ∈ wordsOfLength j, (C₀ + 1) * Real.exp (-(γ * c ^ 2 / heatWidth ν s)) := by
        refine Finset.sum_le_sum fun w hw => ?_
        have h1 := hb hν hν1 hc hs hac z w (Finset.mem_toList.mpr hw)
        exact h1.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _))
    _ = ((wordsOfLength j).card : ℝ) * ((C₀ + 1) * Real.exp (-(γ * c ^ 2 / heatWidth ν s))) := by
        simp
    _ ≤ (2 : ℝ) ^ j * (C₀ + 1) * Real.exp (-(γ * c ^ 2 / heatWidth ν s)) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right hcard (by positivity)

theorem qcDiv_ageJet_weighted_bound (ℓ j : ℕ) :
    ∃ C γ : ℝ, 0 < C ∧ 0 < γ ∧
      ∀ {ν c s : ℝ}, 0 < ν → ν ≤ 1 → 0 < c → 0 < s → heatWidth ν s ≤ c ^ 2 →
        ∀ z : Plane,
          (1 + z.2 ^ 2 / heatWidth ν s) *
            ‖ageJet ℓ j (fun r x => Train.matDiv (Train.Qc ν c r) x) s z‖ ≤
              C * Real.exp (-(γ * c ^ 2 / heatWidth ν s)) := by
  obtain ⟨C₀, γ₀, hC₀, hγ₀, hb₀⟩ := qcDiv_comp_ageJet_bound 0 ℓ j
  obtain ⟨C₁, γ₁, hC₁, hγ₁, hb₁⟩ := qcDiv_comp_ageJet_bound 1 ℓ j
  refine ⟨C₀ + C₁, min γ₀ γ₁, add_pos hC₀ hC₁, lt_min hγ₀ hγ₁,
    fun {ν c s} hν hν1 hc hs hac z => ?_⟩
  let qcDiv : ℝ → Plane → Vec := fun r x => Train.matDiv (Train.Qc ν c r) x
  have hsm_qc : Sm (fun x : ℝ × Plane => qcDiv x.1 x.2) := sm_qcDiv hν hc
  have hvec := PartI_T20_1.norm_ageJet_vec_le_add_proj hsm_qc ℓ j hs z
  have ha : 0 < heatWidth ν s := heatWidth_pos hν hs.le
  have hw_nn : 0 ≤ 1 + z.2 ^ 2 / heatWidth ν s := by positivity
  have hY : 0 ≤ c ^ 2 / heatWidth ν s := div_nonneg (sq_nonneg c) ha.le
  have h0 : (1 + z.2 ^ 2 / heatWidth ν s) * ‖ageJet ℓ j (fun r x => qcDiv r x 0) s z‖ ≤
      C₀ * Real.exp (-(min γ₀ γ₁ * c ^ 2 / heatWidth ν s)) := by
    refine (hb₀ hν hν1 hc hs hac z).trans ?_
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left _ _) hY))) hC₀.le
  have h1 : (1 + z.2 ^ 2 / heatWidth ν s) * ‖ageJet ℓ j (fun r x => qcDiv r x 1) s z‖ ≤
      C₁ * Real.exp (-(min γ₀ γ₁ * c ^ 2 / heatWidth ν s)) := by
    refine (hb₁ hν hν1 hc hs hac z).trans ?_
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_right _ _) hY))) hC₁.le
  calc (1 + z.2 ^ 2 / heatWidth ν s) * ‖ageJet ℓ j qcDiv s z‖
      ≤ (1 + z.2 ^ 2 / heatWidth ν s) *
          (‖ageJet ℓ j (fun r x => qcDiv r x 0) s z‖ +
            ‖ageJet ℓ j (fun r x => qcDiv r x 1) s z‖) :=
        mul_le_mul_of_nonneg_left hvec hw_nn
    _ = (1 + z.2 ^ 2 / heatWidth ν s) * ‖ageJet ℓ j (fun r x => qcDiv r x 0) s z‖ +
          (1 + z.2 ^ 2 / heatWidth ν s) * ‖ageJet ℓ j (fun r x => qcDiv r x 1) s z‖ :=
        left_distrib _ _ _
    _ ≤ C₀ * Real.exp (-(min γ₀ γ₁ * c ^ 2 / heatWidth ν s)) +
          C₁ * Real.exp (-(min γ₀ γ₁ * c ^ 2 / heatWidth ν s)) := add_le_add h0 h1
    _ = (C₀ + C₁) * Real.exp (-(min γ₀ γ₁ * c ^ 2 / heatWidth ν s)) := by ring

end PartI_T25_QcDiv

/-- Unconditional proof of `TrainFixedBandQcDivAgeJet` (`PartI:T25/1/1`). -/
theorem trainFixedBandQcDivAgeJet_proof : TrainFixedBandQcDivAgeJet := by
  refine ⟨fun ν c hν hc => PartI_T25_QcDiv.sm_qcDiv hν hc, ?_⟩
  intro ρ hρ Sg hSg ℓ j
  obtain ⟨C_Q, γ_Q, hC_Q, hγ_Q, hQ⟩ := PartI_T25_QcDiv.qcDiv_ageJet_weighted_bound ℓ j
  obtain ⟨νp, hνp, hνp1, hp⟩ := trainPeriodAsymptotics_proof ρ hρ (1 + Sg) (by positivity)
  let M₀ : ℝ := (1 + Sg) * C_Q
  let C_out : ℝ := M₀ * (Real.pi + 1)
  let bS : ℝ := γ_Q / (1 + Sg)
  refine ⟨C_out, 1, 0, bS, νp, by positivity, div_pos hγ_Q (by positivity), hνp, ?_⟩
  intro ν hν hν_le s hs hs_le
  have hν1 : ν ≤ 1 := hν_le.trans hνp1
  obtain ⟨hc1, hνc2⟩ := hp ν hν hν_le
  let c := trainPeriod ρ ν
  have hc_pos : 0 < c := zero_lt_one.trans_le hc1
  have hw_eq : B0113.heatWidth ν s = width ν s := rfl
  have hw_ge1 : 1 ≤ width ν s := by
    unfold width
    linarith [mul_pos hν hs]
  have hw_pos : 0 < width ν s := zero_lt_one.trans_le hw_ge1
  have hw_le_Sg : width ν s ≤ 1 + Sg := by
    unfold width
    have hνs : ν * s ≤ Sg := by
      have := mul_le_mul_of_nonneg_left hs_le hν.le
      rwa [mul_div_cancel₀ _ hν.ne'] at this
    linarith
  have hSg_c2 : 1 + Sg ≤ c ^ 2 := by
    calc 1 + Sg ≤ ν * c ^ 2 := hνc2
      _ ≤ 1 * c ^ 2 := mul_le_mul_of_nonneg_right hν1 (sq_nonneg c)
      _ = c ^ 2 := one_mul _
  have hw_le_c2 : B0113.heatWidth ν s ≤ c ^ 2 := by
    rw [hw_eq]
    exact hw_le_Sg.trans hSg_c2
  let qcDiv : ℝ → Plane → Vec := fun r z => Train.matDiv (Train.Qc ν c r) z
  let E : ℝ := Real.exp (0 / ν - bS * c ^ 2)
  have hE_pos : 0 < E := Real.exp_pos _
  have hexp_le : Real.exp (-(γ_Q * c ^ 2 / B0113.heatWidth ν s)) ≤ E := by
    dsimp [E, bS]
    rw [zero_div, zero_sub, hw_eq]
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_left (by positivity) hw_pos hw_le_Sg
  have hpt_inv : ∀ z : Plane,
      ‖ageJet ℓ j qcDiv s z‖ ≤ (M₀ * E) * (1 + z.2 ^ 2)⁻¹ := by
    intro z
    have h1 := hQ hν hν1 hc_pos hs hw_le_c2 z
    have h1' : (1 + z.2 ^ 2 / width ν s) * ‖ageJet ℓ j qcDiv s z‖ ≤ C_Q * E := by
      rw [← hw_eq]
      exact h1.trans (mul_le_mul_of_nonneg_left hexp_le hC_Q.le)
    have h2 : 1 + z.2 ^ 2 ≤ (1 + Sg) * (1 + z.2 ^ 2 / width ν s) := by
      have hz : z.2 ^ 2 / (1 + Sg) ≤ z.2 ^ 2 / width ν s :=
        div_le_div_of_nonneg_left (sq_nonneg z.2) hw_pos hw_le_Sg
      have hSg1 : (0 : ℝ) < 1 + Sg := by positivity
      have heq : (1 + Sg) * (z.2 ^ 2 / (1 + Sg)) = z.2 ^ 2 := mul_div_cancel₀ _ hSg1.ne'
      nlinarith
    have h3 : (1 + z.2 ^ 2) * ‖ageJet ℓ j qcDiv s z‖ ≤ M₀ * E := by
      calc (1 + z.2 ^ 2) * ‖ageJet ℓ j qcDiv s z‖
          ≤ (1 + Sg) * (1 + z.2 ^ 2 / width ν s) * ‖ageJet ℓ j qcDiv s z‖ :=
            mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
        _ = (1 + Sg) * ((1 + z.2 ^ 2 / width ν s) * ‖ageJet ℓ j qcDiv s z‖) := by ring
        _ ≤ (1 + Sg) * (C_Q * E) := mul_le_mul_of_nonneg_left h1' (by positivity)
        _ = M₀ * E := by dsimp [M₀]; ring
    have h1z_pos : 0 < 1 + z.2 ^ 2 := by positivity
    have h1z_ne : 1 + z.2 ^ 2 ≠ 0 := h1z_pos.ne'
    calc ‖ageJet ℓ j qcDiv s z‖
        = ((1 + z.2 ^ 2) * ‖ageJet ℓ j qcDiv s z‖) * (1 + z.2 ^ 2)⁻¹ := by
          field_simp
      _ ≤ (M₀ * E) * (1 + z.2 ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right h3 (inv_nonneg.mpr h1z_pos.le)
  have hpt_L2 : ∀ z : Plane,
      Real.sqrt (jap 0 z) * ‖ageJet ℓ j qcDiv s z‖ ≤ (M₀ * E) * (1 + z.2 ^ 2)⁻¹ := by
    intro z
    simpa [jap] using hpt_inv z
  have hL2 := wCellL2_le_of_inv_one_add_sq hc_pos.le (by positivity) 0 (ageJet ℓ j qcDiv s) hpt_L2
  have hL2_bound : Real.sqrt (c * ((M₀ * E) ^ 2 * Real.pi)) ≤ polyP C_out 1 ν c * E := by
    unfold polyP
    rw [pow_one]
    have hsq : c * ((M₀ * E) ^ 2 * Real.pi) ≤ (C_out * (1 + c + ν⁻¹) * E) ^ 2 := by
      have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
      have hpi : 0 < Real.pi := Real.pi_pos
      have hc_le : c ≤ (1 + c + ν⁻¹) ^ 2 := by nlinarith
      have hpi_le : Real.pi ≤ (Real.pi + 1) ^ 2 := by nlinarith
      calc c * ((M₀ * E) ^ 2 * Real.pi)
          = (M₀ * E) ^ 2 * Real.pi * c := by ring
        _ ≤ (M₀ * E) ^ 2 * (Real.pi + 1) ^ 2 * (1 + c + ν⁻¹) ^ 2 := by
            apply mul_le_mul _ hc_le hc_pos.le (by positivity)
            exact mul_le_mul_of_nonneg_left hpi_le (sq_nonneg _)
        _ = (C_out * (1 + c + ν⁻¹) * E) ^ 2 := by dsimp [C_out]; ring
    exact (Real.sqrt_le_iff).2 ⟨by positivity, hsq⟩
  have hSup_bound : wSupNorm 0 (ageJet ℓ j qcDiv s) ≤ ENNReal.ofReal (polyP C_out 1 ν c * E) := by
    unfold wSupNorm
    refine iSup_le fun z => ?_
    simp only [jap, pow_zero, Real.sqrt_one, ENNReal.ofReal_one, one_mul, ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    have hinv_le1 : (1 + z.2 ^ 2)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg z.2])
    have hM_le : M₀ * E ≤ polyP C_out 1 ν c * E := by
      unfold polyP
      rw [pow_one]
      have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
      have hpi : 0 < Real.pi := Real.pi_pos
      have h1 : M₀ ≤ C_out * (1 + c + ν⁻¹) := by
        calc M₀ = M₀ * 1 * 1 := by ring
          _ ≤ M₀ * (Real.pi + 1) * (1 + c + ν⁻¹) := by
              apply mul_le_mul
              · exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
              · linarith [hc_pos.le]
              · exact zero_le_one
              · positivity
      exact mul_le_mul_of_nonneg_right h1 hE_pos.le
    calc ‖ageJet ℓ j qcDiv s z‖
        ≤ (M₀ * E) * (1 + z.2 ^ 2)⁻¹ := hpt_inv z
      _ ≤ (M₀ * E) * 1 := mul_le_mul_of_nonneg_left hinv_le1 (by positivity)
      _ = M₀ * E := mul_one _
      _ ≤ polyP C_out 1 ν c * E := hM_le
  exact ⟨hL2.trans (ENNReal.ofReal_le_ofReal hL2_bound), hSup_bound⟩

end UnforcedLeray.Short.PartI.VelAgeJetAux
