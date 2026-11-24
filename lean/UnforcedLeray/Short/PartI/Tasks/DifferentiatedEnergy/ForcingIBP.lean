import UnforcedLeray.Short.PartI.Sub.T08Statement
import UnforcedLeray.Lib.Cylinder.IBP
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Part I, task `PartI:T08/9`: one integration by parts on the stress

Target: `jetForcingIBP_proof : JetForcingIBP` (`Sub/T08Statement.lean`, leaf 9).

Source of record: `the November 2 reference manuscript` line 346.

Proof outline.
* `derivWord_comm`: word derivatives commute with `∂_q`, `∂_η` on smooth fields.
* `wordComp_matDiv`: the word derivative of `div Q` splits as `∂_q ∂_w Q_{0l} + ∂_η ∂_w Q_{1l}`.
* `word_step`: per word `w` and component `l`, one integration by parts in `q` and in `η`.
* `quad_cs`, `abs_int_cs`, `sum_abs_int_cs`: Cauchy-Schwarz for finite sums of cell integrals.
* The main theorem reindexes the sums over `(w, l, β)` and applies Cauchy-Schwarz.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

namespace ForcingIBP

/-! ### Calculus on the plane -/

theorem cd_partialQ {F : Plane → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (Cyl.partialQ F) := by
  have h : Cyl.partialQ F = fun w => fderiv ℝ F w (1, 0) :=
    funext fun w => Cyl.partialQ_eq_fderiv (hF.differentiable (by simp)) w
  rw [h]
  exact (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem cd_partialEta {F : Plane → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (Cyl.partialEta F) := by
  have h : Cyl.partialEta F = fun w => fderiv ℝ F w (0, 1) :=
    funext fun w => Cyl.partialEta_eq_fderiv (hF.differentiable (by simp)) w
  rw [h]
  exact (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem partialQ_fderiv_apply {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (v z : Plane) :
    Cyl.partialQ (fun x => fderiv ℝ f x v) z = fderiv ℝ (Cyl.partialQ f) z v := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hfd : ContDiff ℝ 1 (fderiv ℝ f) :=
    hf2.fderiv_right (m := 1) (by norm_num)
  have hdd : Differentiable ℝ (fderiv ℝ f) := hfd.differentiable one_ne_zero
  have hscalar : Differentiable ℝ (fun x => fderiv ℝ f x v) := by
    exact (ContinuousLinearMap.apply ℝ ℝ v).differentiable.comp hdd
  have hq : Cyl.partialQ f = fun x => fderiv ℝ f x (1, 0) := by
    funext x
    exact Cyl.partialQ_eq_fderiv (hf.differentiable (by simp)) x
  rw [Cyl.partialQ_eq_fderiv hscalar z, hq]
  rw [fderiv_clm_apply (hdd z) (differentiableAt_const _),
    fderiv_clm_apply (hdd z) (differentiableAt_const _)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq (1, 0) v

/-- Mixed partials commute on smooth scalar fields. -/
theorem comm_QE {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) :
    Cyl.partialQ (Cyl.partialEta f) = Cyl.partialEta (Cyl.partialQ f) := by
  have hQ : ContDiff ℝ ∞ (Cyl.partialQ f) := cd_partialQ hf
  have hdQ : Differentiable ℝ (Cyl.partialQ f) := hQ.differentiable (by simp)
  have hE : Cyl.partialEta f = fun x => fderiv ℝ f x (0, 1) := by
    funext x
    exact Cyl.partialEta_eq_fderiv (hf.differentiable (by simp)) x
  funext z
  rw [hE, partialQ_fderiv_apply hf (0, 1) z, Cyl.partialEta_eq_fderiv hdQ z]

theorem partialQ_add_pt {f g : Plane → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : Plane) :
    Cyl.partialQ (fun y => f y + g y) z = Cyl.partialQ f z + Cyl.partialQ g z := by
  have hd : Differentiable ℝ (fun y => f y + g y) := hf.add hg
  rw [Cyl.partialQ_eq_fderiv hd z, Cyl.partialQ_eq_fderiv hf z,
    Cyl.partialQ_eq_fderiv hg z,
    show fderiv ℝ (fun y => f y + g y) z = fderiv ℝ f z + fderiv ℝ g z from fderiv_add (hf z) (hg z)]
  rfl

theorem partialEta_add_pt {f g : Plane → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : Plane) :
    Cyl.partialEta (fun y => f y + g y) z = Cyl.partialEta f z + Cyl.partialEta g z := by
  have hd : Differentiable ℝ (fun y => f y + g y) := hf.add hg
  rw [Cyl.partialEta_eq_fderiv hd z, Cyl.partialEta_eq_fderiv hf z,
    Cyl.partialEta_eq_fderiv hg z,
    show fderiv ℝ (fun y => f y + g y) z = fderiv ℝ f z + fderiv ℝ g z from fderiv_add (hf z) (hg z)]
  rfl

/-- Periodicity passes to word derivatives. -/
theorem per_derivWord {c : ℝ} (w : List Bool) :
    ∀ F : Plane → ℝ, Cyl.IsPeriodic c F → Cyl.IsPeriodic c (B0151.derivWord w F) := by
  induction w with
  | nil => intro F hF; exact hF
  | cons b w ih =>
    intro F hF
    cases b with
    | false => exact (ih F hF).partialEta
    | true => exact (ih F hF).partialQ

/-- Word derivatives are additive on smooth fields. -/
theorem derivWord_add_smooth (w : List Bool) :
    ∀ F G : Plane → ℝ, ContDiff ℝ ∞ F → ContDiff ℝ ∞ G →
      B0151.derivWord w (fun z => F z + G z) =
        fun z => B0151.derivWord w F z + B0151.derivWord w G z := by
  induction w with
  | nil => intro F G _ _; rfl
  | cons b w ih =>
    intro F G hF hG
    have hw := ih F G hF hG
    have hdF : Differentiable ℝ (B0151.derivWord w F) :=
      (B0151.contDiff_derivWord hF w).differentiable (by simp)
    have hdG : Differentiable ℝ (B0151.derivWord w G) :=
      (B0151.contDiff_derivWord hG w).differentiable (by simp)
    cases b with
    | false =>
      show Cyl.partialEta (B0151.derivWord w (fun z => F z + G z)) =
        fun z => Cyl.partialEta (B0151.derivWord w F) z + Cyl.partialEta (B0151.derivWord w G) z
      rw [hw]
      funext z
      exact partialEta_add_pt hdF hdG z
    | true =>
      show Cyl.partialQ (B0151.derivWord w (fun z => F z + G z)) =
        fun z => Cyl.partialQ (B0151.derivWord w F) z + Cyl.partialQ (B0151.derivWord w G) z
      rw [hw]
      funext z
      exact partialQ_add_pt hdF hdG z

/-- Word derivatives commute with `∂_q` and `∂_η` on smooth fields. -/
theorem derivWord_comm (w : List Bool) :
    ∀ G : Plane → ℝ, ContDiff ℝ ∞ G →
      B0151.derivWord w (Cyl.partialQ G) = Cyl.partialQ (B0151.derivWord w G) ∧
      B0151.derivWord w (Cyl.partialEta G) = Cyl.partialEta (B0151.derivWord w G) := by
  induction w with
  | nil => intro G _; exact ⟨rfl, rfl⟩
  | cons b w ih =>
    intro G hG
    obtain ⟨hQ, hE⟩ := ih G hG
    have hdG := B0151.contDiff_derivWord hG w
    cases b with
    | false =>
      constructor
      · show Cyl.partialEta (B0151.derivWord w (Cyl.partialQ G)) =
          Cyl.partialQ (Cyl.partialEta (B0151.derivWord w G))
        rw [hQ]
        exact (comm_QE hdG).symm
      · show Cyl.partialEta (B0151.derivWord w (Cyl.partialEta G)) =
          Cyl.partialEta (Cyl.partialEta (B0151.derivWord w G))
        rw [hE]
    | true =>
      constructor
      · show Cyl.partialQ (B0151.derivWord w (Cyl.partialQ G)) =
          Cyl.partialQ (Cyl.partialQ (B0151.derivWord w G))
        rw [hQ]
      · show Cyl.partialQ (B0151.derivWord w (Cyl.partialEta G)) =
          Cyl.partialEta (Cyl.partialQ (B0151.derivWord w G))
        rw [hE]
        exact comm_QE hdG

/-! ### The divergence of a tensor, word by word -/

/-- The row index attached to a direction: `true` (the `∂_q` slot) is row `0`, `false` is row `1`. -/
def rowOf : Bool → Fin 2
  | true => 0
  | false => 1

@[simp] theorem rowOf_true : rowOf true = 0 := rfl
@[simp] theorem rowOf_false : rowOf false = 1 := rfl

theorem matDiv_comp (Q : Plane → Matrix (Fin 2) (Fin 2) ℝ) (l : Fin 2) :
    (fun z => Train.matDiv Q z l) = fun z =>
      Cyl.partialQ (fun x => Q x 0 l) z + Cyl.partialEta (fun x => Q x 1 l) z := by
  funext z
  fin_cases l <;> simp [Train.matDiv]

theorem wordComp_matDiv (Q : Plane → Matrix (Fin 2) (Fin 2) ℝ)
    (hQs : ∀ k l : Fin 2, ContDiff ℝ ∞ (fun z => Q z k l)) (w : List Bool) (l : Fin 2) :
    B0151.derivWord w (fun z => Train.matDiv Q z l) =
      fun z => B0151.derivWord (true :: w) (fun x => Q x 0 l) z +
        B0151.derivWord (false :: w) (fun x => Q x 1 l) z := by
  rw [matDiv_comp Q l, derivWord_add_smooth w _ _ (cd_partialQ (hQs 0 l))
    (cd_partialEta (hQs 1 l)), (derivWord_comm w _ (hQs 0 l)).1,
    (derivWord_comm w _ (hQs 1 l)).2]
  rfl

theorem matDiv_word_L2 {c : ℝ} (Q : Plane → Matrix (Fin 2) (Fin 2) ℝ)
    (hQs : ∀ k l : Fin 2, ContDiff ℝ ∞ (fun z => Q z k l))
    (hQL2 : ∀ (w : List Bool) (k l : Fin 2),
      MemLp (B0151.derivWord w (fun z => Q z k l)) 2 (Cyl.cellμ c))
    (w : List Bool) (l : Fin 2) :
    MemLp (wordComp w (Train.matDiv Q) l) 2 (Cyl.cellμ c) := by
  have h := (hQL2 (true :: w) 0 l).add (hQL2 (false :: w) 1 l)
  have e : wordComp w (Train.matDiv Q) l = B0151.derivWord w (fun z => Train.matDiv Q z l) :=
    rfl
  rw [e, wordComp_matDiv Q hQs w l]
  exact h

/-! ### One integration by parts -/

theorem ibp_Q {c : ℝ} (hc : 0 < c) {F G : Plane → ℝ} (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) (hFp : Cyl.IsPeriodic c F) (hGp : Cyl.IsPeriodic c G)
    (hF0 : MemLp F 2 (Cyl.cellμ c)) (hG0 : MemLp G 2 (Cyl.cellμ c))
    (hFq : MemLp (Cyl.partialQ F) 2 (Cyl.cellμ c)) (hGq : MemLp (Cyl.partialQ G) 2 (Cyl.cellμ c)) :
    ∫ z in Cyl.cell c, G z * Cyl.partialQ F z = -∫ z in Cyl.cell c, Cyl.partialQ G z * F z := by
  have e1 : (fun z => G z * Cyl.partialQ F z) = fun z => Cyl.partialQ F z * G z := by
    funext z; ring
  have e2 : (fun z => Cyl.partialQ G z * F z) = fun z => F z * Cyl.partialQ G z := by
    funext z; ring
  rw [e1, e2]
  exact Cyl.integral_cell_partialQ_mul hc (hF.differentiable (by simp))
    (hG.differentiable (by simp)) hFp hGp (hFq.integrable_mul hG0) (hF0.integrable_mul hGq)

theorem ibp_E {c : ℝ} {F G : Plane → ℝ} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hF0 : MemLp F 2 (Cyl.cellμ c)) (hG0 : MemLp G 2 (Cyl.cellμ c))
    (hFe : MemLp (Cyl.partialEta F) 2 (Cyl.cellμ c))
    (hGe : MemLp (Cyl.partialEta G) 2 (Cyl.cellμ c)) :
    ∫ z in Cyl.cell c, G z * Cyl.partialEta F z = -∫ z in Cyl.cell c, Cyl.partialEta G z * F z := by
  have e1 : (fun z => G z * Cyl.partialEta F z) = fun z => Cyl.partialEta F z * G z := by
    funext z; ring
  have e2 : (fun z => Cyl.partialEta G z * F z) = fun z => F z * Cyl.partialEta G z := by
    funext z; ring
  rw [e1, e2]
  exact Cyl.integral_cell_partialEta_mul (hF.differentiable (by simp))
    (hG.differentiable (by simp)) (hF0.integrable_mul hG0) (hFe.integrable_mul hG0)
    (hF0.integrable_mul hGe)

/-- One word and one component: the integration by parts identity. -/
theorem word_step {c : ℝ} (hc : 0 < c) (f : Plane → Train.Vec) (hsm : ContDiff ℝ ∞ f)
    (hper : Cyl.IsPeriodic c f)
    (hL2 : ∀ (w : List Bool) (k : Fin 2), MemLp (wordComp w f k) 2 (Cyl.cellμ c))
    (Q : Plane → Matrix (Fin 2) (Fin 2) ℝ)
    (hQs : ∀ k l : Fin 2, ContDiff ℝ ∞ (fun z => Q z k l))
    (hQp : ∀ k l : Fin 2, Cyl.IsPeriodic c (fun z => Q z k l))
    (hQL2 : ∀ (w : List Bool) (k l : Fin 2),
      MemLp (B0151.derivWord w (fun z => Q z k l)) 2 (Cyl.cellμ c))
    (w : List Bool) (l : Fin 2) :
    ∫ z in Cyl.cell c, wordComp w f l z * wordComp w (Train.matDiv Q) l z =
      -(∫ z in Cyl.cell c, B0151.derivWord (true :: w) (fun x => f x l) z *
          B0151.derivWord w (fun x => Q x 0 l) z)
        - ∫ z in Cyl.cell c, B0151.derivWord (false :: w) (fun x => f x l) z *
          B0151.derivWord w (fun x => Q x 1 l) z := by
  have hcomp : ∀ k : Fin 2, ContDiff ℝ ∞ (fun x => f x k) := fun k =>
    (EuclideanSpace.proj k : Train.Vec →L[ℝ] ℝ).contDiff.comp hsm
  have hG : ContDiff ℝ ∞ (B0151.derivWord w (fun x => f x l)) :=
    B0151.contDiff_derivWord (hcomp l) w
  have hGp : Cyl.IsPeriodic c (B0151.derivWord w (fun x => f x l)) := by
    refine per_derivWord w (fun x => f x l) ?_
    intro z
    show f (z.1 + c, z.2) l = f z l
    rw [hper z]
  have hF0 : ContDiff ℝ ∞ (B0151.derivWord w (fun x => Q x 0 l)) :=
    B0151.contDiff_derivWord (hQs 0 l) w
  have hF0p : Cyl.IsPeriodic c (B0151.derivWord w (fun x => Q x 0 l)) :=
    per_derivWord w _ (hQp 0 l)
  have hF1 : ContDiff ℝ ∞ (B0151.derivWord w (fun x => Q x 1 l)) :=
    B0151.contDiff_derivWord (hQs 1 l) w
  have hF1p : Cyl.IsPeriodic c (B0151.derivWord w (fun x => Q x 1 l)) :=
    per_derivWord w _ (hQp 1 l)
  have h1 : ∫ z in Cyl.cell c, wordComp w f l z *
        B0151.derivWord (true :: w) (fun x => Q x 0 l) z =
      -(∫ z in Cyl.cell c, B0151.derivWord (true :: w) (fun x => f x l) z *
          B0151.derivWord w (fun x => Q x 0 l) z) :=
    ibp_Q hc hF0 hG hF0p hGp (hQL2 w 0 l) (hL2 w l) (hQL2 (true :: w) 0 l) (hL2 (true :: w) l)
  have h2 : ∫ z in Cyl.cell c, wordComp w f l z *
        B0151.derivWord (false :: w) (fun x => Q x 1 l) z =
      -(∫ z in Cyl.cell c, B0151.derivWord (false :: w) (fun x => f x l) z *
          B0151.derivWord w (fun x => Q x 1 l) z) :=
    ibp_E hF1 hG (hQL2 w 1 l) (hL2 w l) (hQL2 (false :: w) 1 l) (hL2 (false :: w) l)
  have hsplit : (fun z => wordComp w f l z * wordComp w (Train.matDiv Q) l z) =
      fun z => wordComp w f l z * B0151.derivWord (true :: w) (fun x => Q x 0 l) z +
        wordComp w f l z * B0151.derivWord (false :: w) (fun x => Q x 1 l) z := by
    funext z
    have hM := congrFun (wordComp_matDiv Q hQs w l) z
    show wordComp w f l z * B0151.derivWord w (fun x => Train.matDiv Q x l) z = _
    rw [hM, mul_add]
  have i1 : IntegrableOn (fun z => wordComp w f l z *
      B0151.derivWord (true :: w) (fun x => Q x 0 l) z) (Cyl.cell c) :=
    (hL2 w l).integrable_mul (hQL2 (true :: w) 0 l)
  have i2 : IntegrableOn (fun z => wordComp w f l z *
      B0151.derivWord (false :: w) (fun x => Q x 1 l) z) (Cyl.cell c) :=
    (hL2 w l).integrable_mul (hQL2 (false :: w) 1 l)
  rw [hsplit, integral_add i1 i2, h1, h2]
  ring

/-! ### Cauchy-Schwarz on cells -/

theorem quad_cs (A B X : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hq : ∀ t : ℝ, 0 ≤ A - 2 * t * X + t ^ 2 * B) : X ^ 2 ≤ A * B := by
  rcases eq_or_lt_of_le hB with hB0 | hBp
  · subst hB0
    have hX : X = 0 := by
      by_contra hX
      have h := hq ((A + 1) / (2 * X))
      have ht : 2 * ((A + 1) / (2 * X)) * X = A + 1 := by
        field_simp
      rw [ht] at h
      linarith
    rw [hX]
    simp
  · have hB' : B ≠ 0 := hBp.ne'
    have h := hq (X / B)
    have e : A - 2 * (X / B) * X + (X / B) ^ 2 * B = A - X ^ 2 / B := by
      field_simp
      ring
    rw [e] at h
    have h2 : X ^ 2 / B ≤ A := by linarith
    rw [div_le_iff₀ hBp] at h2
    linarith

theorem abs_int_cs {c : ℝ} (a b : Plane → ℝ)
    (haa : IntegrableOn (fun z => a z * a z) (Cyl.cell c))
    (hbb : IntegrableOn (fun z => b z * b z) (Cyl.cell c))
    (hab : IntegrableOn (fun z => a z * b z) (Cyl.cell c)) :
    |∫ z in Cyl.cell c, a z * b z| ≤
      Real.sqrt (∫ z in Cyl.cell c, a z * a z) * Real.sqrt (∫ z in Cyl.cell c, b z * b z) := by
  have hA : 0 ≤ ∫ z in Cyl.cell c, a z * a z := integral_nonneg fun z => mul_self_nonneg _
  have hB : 0 ≤ ∫ z in Cyl.cell c, b z * b z := integral_nonneg fun z => mul_self_nonneg _
  have hq : ∀ t : ℝ, 0 ≤ (∫ z in Cyl.cell c, a z * a z) -
      2 * t * (∫ z in Cyl.cell c, a z * b z) + t ^ 2 * (∫ z in Cyl.cell c, b z * b z) := by
    intro t
    have h0 : 0 ≤ ∫ z in Cyl.cell c, (a z - t * b z) * (a z - t * b z) :=
      integral_nonneg fun z => mul_self_nonneg _
    have e1 : (fun z => (a z - t * b z) * (a z - t * b z)) =
        fun z => (a z * a z - (2 * t) * (a z * b z)) + t ^ 2 * (b z * b z) := by
      funext z; ring
    have i1 : IntegrableOn (fun z => a z * a z - (2 * t) * (a z * b z)) (Cyl.cell c) :=
      haa.sub (hab.const_mul (2 * t))
    rw [e1, integral_add i1 (hbb.const_mul (t ^ 2)), integral_sub haa (hab.const_mul (2 * t)),
      integral_const_mul, integral_const_mul] at h0
    linarith
  have key := quad_cs _ _ _ hA hB hq
  calc |∫ z in Cyl.cell c, a z * b z|
      = Real.sqrt ((∫ z in Cyl.cell c, a z * b z) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((∫ z in Cyl.cell c, a z * a z) * ∫ z in Cyl.cell c, b z * b z) :=
        Real.sqrt_le_sqrt key
    _ = _ := Real.sqrt_mul hA _

theorem sum_abs_int_cs {ι : Type*} (S : Finset ι) {c : ℝ} (a b : ι → Plane → ℝ)
    (haa : ∀ i ∈ S, IntegrableOn (fun z => a i z * a i z) (Cyl.cell c))
    (hbb : ∀ i ∈ S, IntegrableOn (fun z => b i z * b i z) (Cyl.cell c))
    (hab : ∀ i ∈ S, IntegrableOn (fun z => a i z * b i z) (Cyl.cell c)) :
    |∑ i ∈ S, ∫ z in Cyl.cell c, a i z * b i z| ≤
      Real.sqrt (∑ i ∈ S, ∫ z in Cyl.cell c, a i z * a i z) *
        Real.sqrt (∑ i ∈ S, ∫ z in Cyl.cell c, b i z * b i z) := by
  have h1 := Finset.abs_sum_le_sum_abs (fun i => ∫ z in Cyl.cell c, a i z * b i z) S
  have h2 : ∑ i ∈ S, |∫ z in Cyl.cell c, a i z * b i z| ≤
      ∑ i ∈ S, Real.sqrt (∫ z in Cyl.cell c, a i z * a i z) *
        Real.sqrt (∫ z in Cyl.cell c, b i z * b i z) :=
    Finset.sum_le_sum fun i hi => abs_int_cs (a i) (b i) (haa i hi) (hbb i hi) (hab i hi)
  have h3 := Real.sum_sqrt_mul_sqrt_le S
    (f := fun i => ∫ z in Cyl.cell c, a i z * a i z)
    (g := fun i => ∫ z in Cyl.cell c, b i z * b i z)
    (fun i => integral_nonneg fun z => mul_self_nonneg _)
    (fun i => integral_nonneg fun z => mul_self_nonneg _)
  exact h1.trans (h2.trans h3)

/-! ### The index set -/

/-- The index set `(w, l, β)`: a word of length `j`, a component `l`, a direction `β`. -/
abbrev wdIdx (j : ℕ) : Finset (List Bool × Fin 2 × Bool) :=
  wordsOfLength j ×ˢ (Finset.univ ×ˢ Finset.univ)

/-- The `f`-factor `∂_{β::w} f_l` at the index `(w, l, β)`. -/
def fwdA (f : Plane → Train.Vec) (i : List Bool × Fin 2 × Bool) (z : Plane) : ℝ :=
  B0151.derivWord (i.2.2 :: i.1) (fun x => f x i.2.1) z

/-- The `Q`-factor `∂_w Q_{rowOf β, l}` at the index `(w, l, β)`. -/
def fwdB (Q : Plane → Matrix (Fin 2) (Fin 2) ℝ) (i : List Bool × Fin 2 × Bool) (z : Plane) : ℝ :=
  B0151.derivWord i.1 (fun x => Q x (rowOf i.2.2) i.2.1) z

/-! ### Words of a given length and sums over words -/

theorem mem_wordsOfLength_iff' {l : ℕ} {w : List Bool} :
    w ∈ wordsOfLength l ↔ w.length = l := by
  unfold wordsOfLength
  constructor
  · intro h
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 h
    exact List.length_ofFn
  · intro h
    subst h
    exact Finset.mem_image.2 ⟨w.get, Finset.mem_univ _, List.ofFn_get w⟩

theorem wordsOfLength_succ_eq (j : ℕ) :
    wordsOfLength (j + 1) =
      (Finset.univ ×ˢ wordsOfLength j).image (fun p : Bool × List Bool => p.1 :: p.2) := by
  ext w
  rw [Finset.mem_image, mem_wordsOfLength_iff']
  constructor
  · intro hw
    cases w with
    | nil => simp at hw
    | cons b u =>
      refine ⟨(b, u), ?_, rfl⟩
      rw [Finset.mem_product, mem_wordsOfLength_iff']
      exact ⟨Finset.mem_univ _, by simpa using hw⟩
  · rintro ⟨⟨b, u⟩, hm, rfl⟩
    rw [Finset.mem_product, mem_wordsOfLength_iff'] at hm
    simpa using hm.2

theorem sum_wordsOfLength_succ {M : Type*} [AddCommMonoid M] (j : ℕ) (F : List Bool → M) :
    ∑ w ∈ wordsOfLength (j + 1), F w = ∑ β : Bool, ∑ w ∈ wordsOfLength j, F (β :: w) := by
  rw [wordsOfLength_succ_eq, Finset.sum_image]
  · rw [Finset.sum_product]
  · rintro ⟨a, u⟩ _ ⟨b, v⟩ _ h
    simp only [List.cons.injEq] at h
    exact Prod.ext h.1 h.2

/-- Splitting a sum over words into a sum of integrals. -/
theorem integral_sum_sum {c : ℝ} (s : Finset (List Bool)) (F : List Bool → Fin 2 → Plane → ℝ)
    (hF : ∀ w ∈ s, ∀ k : Fin 2, IntegrableOn (F w k) (Cyl.cell c)) :
    ∫ z in Cyl.cell c, ∑ w ∈ s, ∑ k : Fin 2, F w k z =
      ∑ w ∈ s, ∑ k : Fin 2, ∫ z in Cyl.cell c, F w k z := by
  rw [integral_finset_sum s (fun w hw => integrable_finset_sum _ (fun k _ => hF w hw k))]
  refine Finset.sum_congr rfl fun w hw => ?_
  exact integral_finset_sum _ (fun k _ => hF w hw k)

end ForcingIBP

open ForcingIBP

/-! ### The main theorem -/

theorem jetForcingIBP_proof : UnforcedLeray.Short.PartI.JetForcingIBP := by
  intro c hc f hf Q hQs hQp hQL2 j
  obtain ⟨hsm, hper, hL2⟩ := hf
  have hI : ∀ (w : List Bool) (l : Fin 2),
      ∫ z in Cyl.cell c, wordComp w f l z * wordComp w (Train.matDiv Q) l z =
        -(∫ z in Cyl.cell c, fwdA f (w, l, true) z * fwdB Q (w, l, true) z)
          - ∫ z in Cyl.cell c, fwdA f (w, l, false) z * fwdB Q (w, l, false) z := by
    intro w l
    rw [word_step hc f hsm hper hL2 Q hQs hQp hQL2 w l]
    simp only [fwdA, fwdB, rowOf_true, rowOf_false]
  have hJ : jetPair c j f (Train.matDiv Q) =
      -∑ i ∈ wdIdx j, ∫ z in Cyl.cell c, fwdA f i z * fwdB Q i z := by
    have hL : jetPair c j f (Train.matDiv Q) = ∑ w ∈ wordsOfLength j, ∑ l : Fin 2,
        ∫ z in Cyl.cell c, wordComp w f l z * wordComp w (Train.matDiv Q) l z := by
      have hint : ∀ w ∈ wordsOfLength j, ∀ l : Fin 2,
          IntegrableOn (fun z => wordComp w f l z * wordComp w (Train.matDiv Q) l z)
            (Cyl.cell c) := fun w _ l =>
        (hL2 w l).integrable_mul (matDiv_word_L2 Q hQs hQL2 w l)
      unfold jetPair
      exact integral_sum_sum _ _ hint
    rw [hL]
    simp only [hI]
    simp only [wdIdx, Finset.sum_product, Fintype.sum_bool, Fin.sum_univ_two,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    ring
  have hA : jetEnergy c (j + 1) f =
      ∑ i ∈ wdIdx j, ∫ z in Cyl.cell c, fwdA f i z * fwdA f i z := by
    have hint : ∀ w ∈ wordsOfLength (j + 1), ∀ k : Fin 2,
        IntegrableOn (fun z => wordComp w f k z * wordComp w f k z) (Cyl.cell c) :=
      fun w _ k => (hL2 w k).integrable_mul (hL2 w k)
    have hL' : jetEnergy c (j + 1) f = ∑ w ∈ wordsOfLength (j + 1), ∑ k : Fin 2,
        ∫ z in Cyl.cell c, wordComp w f k z * wordComp w f k z := by
      unfold jetEnergy jetPair
      exact integral_sum_sum _ _ hint
    rw [hL', sum_wordsOfLength_succ j
      (fun w => ∑ k : Fin 2, ∫ z in Cyl.cell c, wordComp w f k z * wordComp w f k z)]
    simp only [wdIdx, Finset.sum_product, Fintype.sum_bool, Fin.sum_univ_two,
      Finset.sum_add_distrib, fwdA, wordComp]
    ring
  have hB : matEnergy c j Q =
      ∑ i ∈ wdIdx j, ∫ z in Cyl.cell c, fwdB Q i z * fwdB Q i z := by
    have hME : matEnergy c j Q = ∑ w ∈ wordsOfLength j, ∑ k : Fin 2, ∑ l : Fin 2,
        ∫ z in Cyl.cell c, B0151.derivWord w (fun x => Q x k l) z ^ 2 := by
      unfold matEnergy
      refine (integral_finset_sum _ (fun w _ => ?_)).trans (Finset.sum_congr rfl fun w _ => ?_)
      · exact integrable_finset_sum _ (fun k _ =>
          integrable_finset_sum _ (fun l _ => (hQL2 w k l).integrable_sq))
      · refine (integral_finset_sum _ (fun k _ => ?_)).trans (Finset.sum_congr rfl fun k _ => ?_)
        · exact integrable_finset_sum _ (fun l _ => (hQL2 w k l).integrable_sq)
        · exact integral_finset_sum _ (fun l _ => (hQL2 w k l).integrable_sq)
    rw [hME]
    simp only [wdIdx, Finset.sum_product, Fintype.sum_bool, Fin.sum_univ_two,
      Finset.sum_add_distrib, fwdB, rowOf_true, rowOf_false, sq]
    ring
  have hmain := sum_abs_int_cs (wdIdx j) (c := c) (fwdA f) (fwdB Q)
    (fun i _ => (hL2 (i.2.2 :: i.1) i.2.1).integrable_mul (hL2 (i.2.2 :: i.1) i.2.1))
    (fun i _ => (hQL2 i.1 (rowOf i.2.2) i.2.1).integrable_mul (hQL2 i.1 (rowOf i.2.2) i.2.1))
    (fun i _ => (hL2 (i.2.2 :: i.1) i.2.1).integrable_mul (hQL2 i.1 (rowOf i.2.2) i.2.1))
  rw [← hA, ← hB] at hmain
  rw [hJ, abs_neg]
  exact hmain
