import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.TimeJets.Defs
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.NearFar
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.AdjFubini
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.VelFarFieldParts.Bdd
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.VelFarFieldParts.Meas
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.WeightedMulL12
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_2_1_2

/-!
# `PartIII-a:T21/2/7/2/1/2/1/2/3`: the classical adjoint equation, tested, for `r ≥ 0`

Ico transcription of `Sub/PartIII-a_T21_2_7_2_1_1_6_7.lean` (`LopTestedAux`, Ioo, `0 < r`). The
proof of `lop_core` uses only `0 ≤ r` (the train is smooth on `[0, ∞) × ℝ²`), so it is copied here
with `0 ≤ r`, under the namespace `AdjLopTestedWAux`. The operators `adjLopW` (one-sided age jets)
agree with `adjLop` at age `0`, since the zeroth age jets are the values of `v` and `∂_l E`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa
namespace AdjLopTestedWAux


/-- `ejWeight m ≤ K ⟨x⟩^{m+2}` on the cell (`(1+x₂²) ≤ ⟨x⟩² ≤ (1+c²/4)(1+x₂²)`). -/
theorem ej_bound {c m A B : ℝ} {x : ℝ × ℝ} (hx : x ∈ B0579.cell c)
    (h : B0579.jb x ^ ((m + 2) / 2) * |A| ≤ B) :
    ejWeight m x * |A| ≤ max 1 ((1 + c ^ 2 / 4) ^ (-((m + 1) / 2))) * B := by
  obtain ⟨hb1, hb2⟩ := wm_jb_bounds hx
  have ht : 0 < 1 + x.2 ^ 2 := by positivity
  have hjb_pos := B0579.jb_pos x
  have hjb1 : 1 ≤ B0579.jb x := by nlinarith [sq_nonneg x.2]
  have hr1 : 1 ≤ B0579.jb x / (1 + x.2 ^ 2) := (one_le_div ht).2 hb1
  have hr2 : B0579.jb x / (1 + x.2 ^ 2) ≤ 1 + c ^ 2 / 4 := (div_le_iff₀ ht).2 (by linarith)
  have hrpos : 0 < B0579.jb x / (1 + x.2 ^ 2) := div_pos hjb_pos ht
  have key := wm_rpow_ratio (-((m + 1) / 2)) hr1 hr2
  have hmul : B0579.jb x ^ ((m + 1) / 2) =
      (1 + x.2 ^ 2) ^ ((m + 1) / 2) * (B0579.jb x / (1 + x.2 ^ 2)) ^ ((m + 1) / 2) := by
    rw [← Real.mul_rpow ht.le hrpos.le]
    congr 1
    field_simp
  have h1 : (1 + x.2 ^ 2) ^ ((m + 1) / 2) =
      B0579.jb x ^ ((m + 1) / 2) * (B0579.jb x / (1 + x.2 ^ 2)) ^ (-((m + 1) / 2)) := by
    rw [Real.rpow_neg hrpos.le, hmul]
    have : 0 < (B0579.jb x / (1 + x.2 ^ 2)) ^ ((m + 1) / 2) := Real.rpow_pos_of_pos hrpos _
    field_simp
  have h2 : B0579.jb x ^ ((m + 1) / 2) ≤ B0579.jb x ^ ((m + 2) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hjb1 (by linarith)
  have hK : 0 ≤ max 1 ((1 + c ^ 2 / 4) ^ (-((m + 1) / 2))) := le_trans zero_le_one (le_max_left _ _)
  have hrn : 0 ≤ (B0579.jb x / (1 + x.2 ^ 2)) ^ (-((m + 1) / 2)) := Real.rpow_nonneg hrpos.le _
  have hjn : 0 ≤ B0579.jb x ^ ((m + 2) / 2) := Real.rpow_nonneg hjb_pos.le _
  have hw : ejWeight m x ≤ max 1 ((1 + c ^ 2 / 4) ^ (-((m + 1) / 2))) *
      B0579.jb x ^ ((m + 2) / 2) := by
    unfold ejWeight
    rw [h1]
    calc _ ≤ B0579.jb x ^ ((m + 2) / 2) *
          max 1 ((1 + c ^ 2 / 4) ^ (-((m + 1) / 2))) := mul_le_mul h2 key hrn hjn
      _ = _ := mul_comm _ _
  calc ejWeight m x * |A|
      ≤ (max 1 ((1 + c ^ 2 / 4) ^ (-((m + 1) / 2))) * B0579.jb x ^ ((m + 2) / 2)) * |A| :=
        mul_le_mul_of_nonneg_right hw (abs_nonneg A)
    _ = max 1 ((1 + c ^ 2 / 4) ^ (-((m + 1) / 2))) * (B0579.jb x ^ ((m + 2) / 2) * |A|) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h hK

/-- Two weak derivatives against a cylinder test (`∂_j∂_j`). -/
theorem lop_second {c m : ℝ} {f : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hJ : IsCellJet c m 2 f D) (j : Fin 2) {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) :
    IntegrableOn (fun x => D [j, j] x * (ψ x : ℂ)) (B0579.cell c) ∧
      IntegrableOn (fun x => f x * (B0579.pd j (B0579.pd j ψ) x : ℂ)) (B0579.cell c) ∧
      ∫ x in B0579.cell c, D [j, j] x * (ψ x : ℂ) =
        ∫ x in B0579.cell c, f x * (B0579.pd j (B0579.pd j ψ) x : ℂ) := by
  have h1 : HasWeakCellDerivC c j (D []) (D [j]) := hJ.deriv j [] (by simp)
  have h2 : HasWeakCellDerivC c j (D [j]) (D [j, j]) := hJ.deriv j [j] (by simp)
  rw [hJ.base] at h1
  have e1 := h2.2 ψ hψ
  have e2 := h1.2 (B0579.pd j ψ) (hψ.pd j)
  refine ⟨(h2.1 ψ hψ).2, (h1.1 (B0579.pd j ψ) (hψ.pd j)).1, ?_⟩
  linear_combination e1 - e2

/-- One weak derivative against a cylinder test. -/
theorem lop_first {c m : ℝ} {f : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hJ : IsCellJet c m 2 f D) (j : Fin 2) {a : ℝ × ℝ → ℝ} (ha : B0579.IsCylTest c a) :
    IntegrableOn (fun x => D [j] x * (a x : ℂ)) (B0579.cell c) ∧
      IntegrableOn (fun x => f x * (B0579.pd j a x : ℂ)) (B0579.cell c) ∧
      ∫ x in B0579.cell c, D [j] x * (a x : ℂ) =
        -∫ x in B0579.cell c, f x * (B0579.pd j a x : ℂ) := by
  have h1 : HasWeakCellDerivC c j (D []) (D [j]) := hJ.deriv j [] (by simp)
  rw [hJ.base] at h1
  refine ⟨(h1.1 a ha).2, (h1.1 a ha).1, ?_⟩
  have := h1.2 a ha
  linear_combination this

/-- The train velocity component at age `r ≥ 0` is smooth. -/
theorem train_contDiff {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r)
    (l : Fin 2) : ContDiff ℝ ∞ (fun x : ℝ × ℝ => tr.v r x l) := by
  have h1 : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => tr.v r x) univ := by
    have hg : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => ((r, x) : ℝ × (ℝ × ℝ))) univ :=
      (contDiff_const.prodMk contDiff_id).contDiffOn
    exact tr.isTrain.smooth_v.comp hg (fun x _ => ⟨hr, trivial⟩)
  have h2 : ContDiff ℝ ∞ (fun x : ℝ × ℝ => tr.v r x) := contDiffOn_univ.1 h1
  exact (EuclideanSpace.proj (𝕜 := ℝ) l).contDiff.comp h2

/-- `v_l(r) ψ` is a cylinder test. -/
theorem train_cylTest {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r)
    (l : Fin 2) {ψ : ℝ × ℝ → ℝ} (hψ : B0579.IsCylTest c ψ) :
    B0579.IsCylTest c (fun x => tr.v r x l * ψ x) where
  smooth := (train_contDiff tr hr l).mul hψ.smooth
  periodic x := by
    have := tr.isTrain.periodic_v r hr x
    simp only [this, hψ.periodic x]
  band := by
    obtain ⟨R, hR⟩ := hψ.band
    exact ⟨R, fun x hx => by simp [hR x hx]⟩

/-- `div v(r) = 0` in the `pd` notation. -/
theorem train_div {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ} (hr : 0 ≤ r)
    (x : ℝ × ℝ) :
    B0579.pd 0 (fun y => tr.v r y 0) x + B0579.pd 1 (fun y => tr.v r y 1) x = 0 := by
  have h := tr.isTrain.solenoidal r hr x
  unfold UnforcedLeray.Cyl.divergence at h
  rw [UnforcedLeray.Cyl.partialQ_eq_fderiv ((train_contDiff tr hr 0).differentiable (by simp)),
    UnforcedLeray.Cyl.partialEta_eq_fderiv ((train_contDiff tr hr 1).differentiable (by simp))]
    at h
  simpa [B0579.pd, B0579.dir] using h

/-- The source `∂_jE(r) · f` of the adjoint localized interaction is in `L¹(C_c)` for every `m`
(`WeightedMulL12` with the weighted bound `LadTrainBdd`; SP 3052-3054). -/
theorem lop_F_integrable {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (m : ℝ) (hc : 0 < c)
    {S C r : ℝ} (hr : r ∈ Icc (0 : ℝ) S) (hb : LadTrainBdd tr m S C) {f : ℝ × ℝ → ℂ}
    (hf : MemLp f 2 (B0579.cellMeasure c (-m))) (j : Fin 2) :
    IntegrableOn (fun x => ((B0579.pd j (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ) * f x)
      (B0579.cell c) := by
  obtain ⟨K, -, hK⟩ := weightedMulL12 c m hc
  have hmeas : AEStronglyMeasurable (B0579.pd j (UnforcedLeray.B0238.Ec tr r))
      (volume.restrict (B0579.cell c)) :=
    (measurable_fderiv_apply_const ℝ (UnforcedLeray.B0238.Ec tr r) (B0579.dir j)).aestronglyMeasurable
  exact (hK _ f _ hmeas hf (fun x hx => ej_bound hx ((hb r hr x hx).2 j))).1

theorem lop_core (m : ℝ) {ν c : ℝ} (hc1 : 1 ≤ c) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hbdd : ∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) (r : ℝ) (hr : 0 ≤ r)
    (f : ℝ × ℝ → ℂ) (D : List (Fin 2) → ℝ × ℝ → ℂ) (hJ : IsCellJet c m 2 f D)
    (ψ : ℝ × ℝ → ℝ) (hψ : B0579.IsCylTest c ψ) :
    ∫ x in B0579.cell c, adjLop tr 0 r D x * (ψ x : ℂ) =
      -∫ x in B0579.cell c, adjIntegrand tr f r ψ (kerVel c ψ) x := by
  have hc0 : 0 < c := by linarith
  obtain ⟨C, hC⟩ := hbdd r hr
  have hrr : r ∈ Icc (0 : ℝ) r := ⟨hr, le_rfl⟩
  have hb : D [] = f := hJ.base
  have hfM : MemLp f 2 (B0579.cellMeasure c (-m)) := hb ▸ hJ.memX [] (by simp)
  set E := UnforcedLeray.B0238.Ec tr r with hE
  set F : Fin 2 → ℝ × ℝ → ℂ := fun l y => ((B0579.pd l E y : ℝ) : ℂ) * D [] y with hF
  have hFint : ∀ l, IntegrableOn (F l) (B0579.cell c) := fun l => by
    simp only [hF, hb]
    exact lop_F_integrable tr m hc0 hrr hC hfM l
  obtain ⟨hK1, hK2⟩ := kerAdjFubini_of kerNearFar c hc1 F hFint ψ hψ
  obtain ⟨B, hB⟩ := kerVelBdd c hc1 ψ hψ
  have hCint : ∀ j : Fin 2, IntegrableOn (fun x => F j x * ((kerVel c ψ x j : ℝ) : ℂ))
      (B0579.cell c) := fun j =>
    (hFint j).mul_bdd (c := B)
      ((Complex.measurable_ofReal.comp_aemeasurable
        (kerVelMeas c hc1 ψ hψ j).aemeasurable).aestronglyMeasurable)
      (Eventually.of_forall fun x => by simpa [Complex.norm_real] using hB x j)
  -- coefficients
  have he : ∀ l y, eJet tr 0 r l y = B0579.pd l E y := fun l y => by
    simp [eJet, iteratedDeriv_zero, hE]
  have hv : ∀ x l, vJet tr 0 r x l = tr.v r x l := fun x l => by simp [vJet, iteratedDeriv_zero]
  have hadj : ∀ x, adjLop tr 0 r D x = -((ν : ℂ) * (D [0, 0] x + D [1, 1] x) +
      (((tr.v r x 0 : ℝ) : ℂ) * D [0] x + ((tr.v r x 1 : ℝ) : ℂ) * D [1] x) - kerAdj c F x) := by
    intro x
    simp only [adjLop, ↓reduceIte, he, hv, Fin.sum_univ_two]
    rfl
  -- the pieces
  have L0 := lop_first hJ 0 (train_cylTest tr hr 0 hψ)
  have L1 := lop_first hJ 1 (train_cylTest tr hr 1 hψ)
  obtain ⟨S0a, S0b, S0c⟩ := lop_second hJ 0 hψ
  obtain ⟨S1a, S1b, S1c⟩ := lop_second hJ 1 hψ
  have hD0 : ∀ x, B0579.pd 0 (fun y => tr.v r y 0) x + B0579.pd 1 (fun y => tr.v r y 1) x = 0 :=
    train_div tr hr
  have hpd : ∀ (l : Fin 2) x, B0579.pd l (fun y => tr.v r y l * ψ y) x =
      B0579.pd l (fun y => tr.v r y l) x * ψ x + tr.v r x l * B0579.pd l ψ x := fun l x =>
    B0579.pd_mul ((train_contDiff tr hr l).differentiable (by simp)) hψ.differentiable l x
  simp only [Fin.sum_univ_two] at hK2
  have hLpt : ∀ x, adjLop tr 0 r D x * (ψ x : ℂ) =
      -((ν : ℂ) * (D [0, 0] x * (ψ x : ℂ) + D [1, 1] x * (ψ x : ℂ)) +
        (D [0] x * ((tr.v r x 0 * ψ x : ℝ) : ℂ) + D [1] x * ((tr.v r x 1 * ψ x : ℝ) : ℂ)) -
        kerAdj c F x * (ψ x : ℂ)) := fun x => by
    rw [hadj x]; push_cast; ring
  have hL : ∫ x in B0579.cell c, adjLop tr 0 r D x * (ψ x : ℂ) =
      -((ν : ℂ) * ((∫ x in B0579.cell c, D [0, 0] x * (ψ x : ℂ)) +
          ∫ x in B0579.cell c, D [1, 1] x * (ψ x : ℂ)) +
        ((∫ x in B0579.cell c, D [0] x * ((tr.v r x 0 * ψ x : ℝ) : ℂ)) +
          ∫ x in B0579.cell c, D [1] x * ((tr.v r x 1 * ψ x : ℝ) : ℂ)) -
        ∫ x in B0579.cell c, kerAdj c F x * (ψ x : ℂ)) := by
    have hI0 : IntegrableOn (fun x => D [0, 0] x * (ψ x : ℂ) + D [1, 1] x * (ψ x : ℂ))
        (B0579.cell c) := S0a.add S1a
    have hI1 : IntegrableOn (fun x => (ν : ℂ) * (D [0, 0] x * (ψ x : ℂ) + D [1, 1] x * (ψ x : ℂ)))
        (B0579.cell c) := hI0.const_mul (ν : ℂ)
    have hI2 : IntegrableOn (fun x => D [0] x * ((tr.v r x 0 * ψ x : ℝ) : ℂ) +
        D [1] x * ((tr.v r x 1 * ψ x : ℝ) : ℂ)) (B0579.cell c) := L0.1.add L1.1
    have hI3 : IntegrableOn (fun x => (ν : ℂ) * (D [0, 0] x * (ψ x : ℂ) + D [1, 1] x * (ψ x : ℂ)) +
        (D [0] x * ((tr.v r x 0 * ψ x : ℝ) : ℂ) + D [1] x * ((tr.v r x 1 * ψ x : ℝ) : ℂ)))
        (B0579.cell c) := hI1.add hI2
    simp_rw [hLpt]
    rw [integral_neg, integral_sub hI3 hK1, integral_add hI1 hI2, integral_const_mul,
      integral_add S0a S1a, integral_add L0.1 L1.1]
  have hRpt : ∀ x, adjIntegrand tr f r ψ (kerVel c ψ) x =
      (ν : ℂ) * (f x * (B0579.pd 0 (B0579.pd 0 ψ) x : ℂ) + f x * (B0579.pd 1 (B0579.pd 1 ψ) x : ℂ)) -
        (f x * (B0579.pd 0 (fun y => tr.v r y 0 * ψ y) x : ℂ) +
          f x * (B0579.pd 1 (fun y => tr.v r y 1 * ψ y) x : ℂ)) -
        (F 0 x * ((kerVel c ψ x 0 : ℝ) : ℂ) + F 1 x * ((kerVel c ψ x 1 : ℝ) : ℂ)) := fun x => by
    have hdc : ((B0579.pd 0 (fun y => tr.v r y 0) x : ℝ) : ℂ) +
        ((B0579.pd 1 (fun y => tr.v r y 1) x : ℝ) : ℂ) = 0 := by exact_mod_cast hD0 x
    simp only [adjIntegrand, lapP, hF, hb, hpd]
    push_cast
    linear_combination (f x * (ψ x : ℂ)) * hdc
  have hR : ∫ x in B0579.cell c, adjIntegrand tr f r ψ (kerVel c ψ) x =
      (ν : ℂ) * ((∫ x in B0579.cell c, f x * (B0579.pd 0 (B0579.pd 0 ψ) x : ℂ)) +
          ∫ x in B0579.cell c, f x * (B0579.pd 1 (B0579.pd 1 ψ) x : ℂ)) -
        ((∫ x in B0579.cell c, f x * (B0579.pd 0 (fun y => tr.v r y 0 * ψ y) x : ℂ)) +
          ∫ x in B0579.cell c, f x * (B0579.pd 1 (fun y => tr.v r y 1 * ψ y) x : ℂ)) -
        ∫ x in B0579.cell c, (F 0 x * ((kerVel c ψ x 0 : ℝ) : ℂ) +
          F 1 x * ((kerVel c ψ x 1 : ℝ) : ℂ)) := by
    have hJ0 : IntegrableOn (fun x => f x * (B0579.pd 0 (B0579.pd 0 ψ) x : ℂ) +
        f x * (B0579.pd 1 (B0579.pd 1 ψ) x : ℂ)) (B0579.cell c) := S0b.add S1b
    have hJ1 : IntegrableOn (fun x => (ν : ℂ) * (f x * (B0579.pd 0 (B0579.pd 0 ψ) x : ℂ) +
        f x * (B0579.pd 1 (B0579.pd 1 ψ) x : ℂ))) (B0579.cell c) := hJ0.const_mul (ν : ℂ)
    have hJ2 : IntegrableOn (fun x => f x * (B0579.pd 0 (fun y => tr.v r y 0 * ψ y) x : ℂ) +
        f x * (B0579.pd 1 (fun y => tr.v r y 1 * ψ y) x : ℂ)) (B0579.cell c) := L0.2.1.add L1.2.1
    have hJ3 : IntegrableOn (fun x => (ν : ℂ) * (f x * (B0579.pd 0 (B0579.pd 0 ψ) x : ℂ) +
        f x * (B0579.pd 1 (B0579.pd 1 ψ) x : ℂ)) -
        (f x * (B0579.pd 0 (fun y => tr.v r y 0 * ψ y) x : ℂ) +
          f x * (B0579.pd 1 (fun y => tr.v r y 1 * ψ y) x : ℂ))) (B0579.cell c) := hJ1.sub hJ2
    have hJ4 : IntegrableOn (fun x => F 0 x * ((kerVel c ψ x 0 : ℝ) : ℂ) +
        F 1 x * ((kerVel c ψ x 1 : ℝ) : ℂ)) (B0579.cell c) := (hCint 0).add (hCint 1)
    simp_rw [hRpt]
    rw [integral_sub hJ3 hJ4, integral_sub hJ1 hJ2, integral_const_mul, integral_add S0b S1b,
      integral_add L0.2.1 L1.2.1]
  rw [hL, hR, S0c, S1c, L0.2.2, L1.2.2, hK2]
  ring


end AdjLopTestedWAux

/-- **`AdjLopTestedW`**: the classical adjoint equation, tested, for every age `r ≥ 0`
(SP 3060-3061, 3052-3058). -/
theorem adjLopTestedW : ∀ m : ℝ, AdjLopTestedW m := by
  intro m ν hν hν1 tr hbdd r hr f D hJ ψ hψ
  have key := AdjLopTestedWAux.lop_core m
    (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by norm_num)) tr hbdd r hr f D hJ ψ hψ
  have hA : ∀ x, adjLopW tr 0 r D x = adjLop tr 0 r D x := fun x => by
    simp [adjLopW, adjLop, vJetW, vJet, eJetW, eJet, iteratedDerivWithin_zero, iteratedDeriv_zero]
  simp only [hA]
  exact key

end UnforcedLeray.Short.IIIa
