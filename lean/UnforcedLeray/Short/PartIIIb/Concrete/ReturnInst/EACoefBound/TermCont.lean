import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_10_4
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EATermSummable.Hess
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EATermSummable.Mgrad

/-!
# `PartIII-b:C/inst/10/4` leaf T: joint continuity of the lattice terms (source 4963-4972, 4978, 5063-5079)

The derivatives of `V_j` and `p_j` are explicit (`hs_eq`, `hs_line`, `mg_fderiv_pj`), so each
term `eABt ν s B C x j` is an explicit expression in `(s, x)` continuous on `{s > 0}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Explicit `(a, b)`-entry of the second derivative of `V_j` (the right side of `hs_line`). -/
def hessV (ν s : ℝ) (j : ℤ) (a b : Fin 2) (x : ℝ × ℝ) : ℝ × ℝ :=
  ((ageA ν s ^ 2)⁻¹ * (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * hsL ν s j a x)) • Jrot (ei b)
    + ((hsE ν s j x * hsL ν s j b x) • Jrot (ei a)
      + ((ageA ν s ^ 2)⁻¹ * (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * hsL ν s j a x)
          * hsL ν s j b x + hsE ν s j x * hsLp ν s b a) • Jrot (xj ν j x))

theorem hess_eq_hessV (ν s : ℝ) (j : ℤ) (a b : Fin 2) (x : ℝ × ℝ) :
    fderiv ℝ (fun y => fderiv ℝ (Vj ν s j) y (ei b)) x (ei a) = hessV ν s j a b x := by
  have hfun : (fun y => fderiv ℝ (Vj ν s j) y (ei b)) = hsG ν s j b :=
    funext fun y => hs_eq ν s j b y
  rw [hfun, gp_fderiv_line (hsG ν s j b) x (ei a) (hs_diff ν s j b x),
    (hs_line ν s j b a x).deriv]
  rfl

theorem mgrad_pj_eq (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ) :
    mgrad (pj ν s j) x = (-((ageA ν s ^ 3)⁻¹ * (Real.exp (-(sq2 (xj ν j x)) / (2 * ageA ν s)) *
        (-(2 * (xj ν j x).1 * (ei 0).1 + 2 * (xj ν j x).2 * (ei 0).2) / (2 * ageA ν s)))),
      -((ageA ν s ^ 3)⁻¹ * (Real.exp (-(sq2 (xj ν j x)) / (2 * ageA ν s)) *
        (-(2 * (xj ν j x).1 * (ei 1).1 + 2 * (xj ν j x).2 * (ei 1).2) / (2 * ageA ν s))))) := by
  unfold mgrad
  rw [mg_fderiv_pj, mg_fderiv_pj]

/-- Continuity of the matrix-vector product along a parameter family. -/
theorem mv_contOn {α : Type*} [TopologicalSpace α] {T : Set α} (A : α → Mat3) (v : α → Vec3)
    (hA : ContinuousOn A T) (hv : ContinuousOn v T) :
    ContinuousOn (fun p => mv (A p) (v p)) T := by
  unfold mv
  refine continuousOn_pi.2 fun i => ?_
  refine continuousOn_finsetSum _ fun k _ => ?_
  exact (continuousOn_pi.1 (continuousOn_pi.1 hA i) k).mul (continuousOn_pi.1 hv k)

/-- Continuity of the embedding `emb` along a parameter family. -/
theorem emb_contOn {α : Type*} [TopologicalSpace α] {T : Set α} (v : α → ℝ × ℝ) (hv : ContinuousOn v T) :
    ContinuousOn (fun p => emb (v p)) T := by
  refine continuousOn_pi.2 fun i => ?_
  fin_cases i
  · exact continuous_fst.comp_continuousOn hv
  · exact continuousOn_const
  · exact continuous_snd.comp_continuousOn hv


/-- Positivity of `a = 1 + ν s` on `{s > 0}` for `ν > 0`. -/
theorem ageA_pos_of (ν : ℝ) (hν : 0 < ν) (p : Chart) (hp : 0 < p.1) : 0 < 1 + ν * p.1 := by
  nlinarith [mul_pos hν hp]

/-- Continuity of `V_j` in `(s, x)` on `{s > 0}`. -/
theorem vj_contOn (ν : ℝ) (hν : 0 < ν) (j : ℤ) :
    ContinuousOn (fun q : Chart => Vj ν q.1 j q.2) {p : Chart | 0 < p.1} := by
  intro p hp
  have ha : 0 < 1 + ν * p.1 := ageA_pos_of ν hν p hp
  apply ContinuousAt.continuousWithinAt
  unfold Vj ageA xj sq2 Jrot cOf
  fun_prop (disch := first | exact ha.ne' | exact (pow_ne_zero _ ha.ne') | exact (mul_ne_zero (by norm_num) ha.ne') | exact (pow_ne_zero _ (mul_ne_zero (by norm_num) ha.ne')) | exact (mul_ne_zero (by norm_num) (pow_ne_zero _ ha.ne')))

/-- Continuity of the explicit second-derivative entries on `{s > 0}`. -/
theorem hessV_contOn (ν : ℝ) (hν : 0 < ν) (j : ℤ) (a b : Fin 2) :
    ContinuousOn (fun q : Chart => hessV ν q.1 j a b q.2) {p : Chart | 0 < p.1} := by
  intro p hp
  have ha : 0 < 1 + ν * p.1 := ageA_pos_of ν hν p hp
  apply ContinuousAt.continuousWithinAt
  unfold hessV hsE hsL hsLp ageA xj sq2 Jrot cOf
  fun_prop (disch := first | exact ha.ne' | exact (pow_ne_zero _ ha.ne') | exact (mul_ne_zero (by norm_num) ha.ne') | exact (pow_ne_zero _ (mul_ne_zero (by norm_num) ha.ne')) | exact (mul_ne_zero (by norm_num) (pow_ne_zero _ ha.ne')))

/-- Continuity of the explicit meridional gradient of `p_j` on `{s > 0}`. -/
theorem mgrad_pj_contOn (ν : ℝ) (hν : 0 < ν) (j : ℤ) :
    ContinuousOn (fun q : Chart => mgrad (pj ν q.1 j) q.2) {p : Chart | 0 < p.1} := by
  intro p hp
  have ha : 0 < 1 + ν * p.1 := ageA_pos_of ν hν p hp
  apply ContinuousAt.continuousWithinAt
  simp only [mgrad_pj_eq]
  unfold ageA xj sq2
  fun_prop (disch := first | exact ha.ne' | exact (pow_ne_zero _ ha.ne') | exact (mul_ne_zero (by norm_num) ha.ne') | exact (pow_ne_zero _ (mul_ne_zero (by norm_num) ha.ne')) | exact (mul_ne_zero (by norm_num) (pow_ne_zero _ ha.ne')))

/-- Entries of a continuous matrix family. -/
theorem mat_entry_contOn (C : ℝ → Mat3) (hC : ContinuousOn C (Ioi 0)) (i k : Fin 3) :
    ContinuousOn (fun q : Chart => C q.1 i k) {p : Chart | 0 < p.1} := by
  have hCq : ContinuousOn (fun q : Chart => C q.1) {p : Chart | 0 < p.1} :=
    hC.comp continuous_fst.continuousOn (fun q (hq : 0 < q.1) => hq)
  exact continuousOn_pi.1 (continuousOn_pi.1 hCq i) k

/-- Leaf T (source 4978, 5063-5079): the terms are jointly continuous in `(s,x)` on `s > 0`. -/
theorem eaTermContLeaf : EAcTermContLeaf := by
  intro ν hν B C hB hC j
  have hBq : ContinuousOn (fun q : Chart => B q.1) {p : Chart | 0 < p.1} :=
    hB.comp continuous_fst.continuousOn (fun q (hq : 0 < q.1) => hq)
  have hVe : ContinuousOn (fun q : Chart => emb (Vj ν q.1 j q.2)) {p : Chart | 0 < p.1} :=
    emb_contOn _ (vj_contOn ν hν j)
  have hGe : ContinuousOn (fun q : Chart => emb (mgrad (pj ν q.1 j) q.2)) {p : Chart | 0 < p.1} :=
    emb_contOn _ (mgrad_pj_contOn ν hν j)
  have hsum : ContinuousOn (fun q : Chart => ∑ a : Fin 2, ∑ b : Fin 2,
      C q.1 (mi a) (mi b) • hessV ν q.1 j a b q.2) {p : Chart | 0 < p.1} :=
    continuousOn_finsetSum _ fun a _ => continuousOn_finsetSum _ fun b _ =>
      (mat_entry_contOn C hC (mi a) (mi b)).smul (hessV_contOn ν hν j a b)
  have hHe : ContinuousOn (fun q : Chart => hessContr (C q.1) (Vj ν q.1 j) q.2)
      {p : Chart | 0 < p.1} := by
    have e : (fun q : Chart => hessContr (C q.1) (Vj ν q.1 j) q.2) =
        fun q : Chart => emb (∑ a : Fin 2, ∑ b : Fin 2,
          C q.1 (mi a) (mi b) • hessV ν q.1 j a b q.2) := by
      funext q
      simp only [hessContr, hess_eq_hessV]
    rw [e]
    exact emb_contOn _ hsum
  have hM : ContinuousOn (fun q : Chart => fun a b => C q.1 a b + C q.1 b a)
      {p : Chart | 0 < p.1} := by
    refine continuousOn_pi.2 fun a => continuousOn_pi.2 fun b => ?_
    exact (mat_entry_contOn C hC a b).add (mat_entry_contOn C hC b a)
  unfold eABt
  have c2 : ContinuousOn (fun _ : Chart => (2 : ℝ)) {p : Chart | 0 < p.1} := continuousOn_const
  have c2ν : ContinuousOn (fun _ : Chart => (2 * ν : ℝ)) {p : Chart | 0 < p.1} := continuousOn_const
  exact (((c2.smul (mv_contOn _ _ hBq hVe)).add
      (c2ν.smul hHe)).sub (mv_contOn _ _ hM hGe))

end UnforcedLeray.Short.PartIIIb.Concrete
