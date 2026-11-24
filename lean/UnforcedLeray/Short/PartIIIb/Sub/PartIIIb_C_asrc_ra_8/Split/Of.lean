import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Split.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FATermSummable
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EATermSummable
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AyDiffAt
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HpPsiTermSummable.Gauss

/-!
# `PartIII-b:C/asrc/ra/8/1/org` : the reductions `brkIdentity_of` and `rPerSplit_of`

Source of record: `the November 2 reference manuscript` (73 pages), 5022-5027,
4963-4978, 2040-2051.

* `bk_algebra` : the single-center identity in closed form (a polynomial identity in `y, a, G` and
  the entries of `M = A^y(s)`, `M' = (A^y)'(s)`);
* `bk_Vj_fderiv`, `bk_mgrad_pj` : `DV_j[w] = G·bkV1`, `∇p_j = G²x_j` (from `gp_fderiv_Vj`,
  `mg_fderiv_pj`);
* `bkG_smul_fderiv` : the Gaussian product rule `D[G(x_j)P(x_j)][u] = G(DP[u] - (x_j·u)/(2a)P)`
  (the tool for the closed-form leaves (L2), (L3), (L5));
* `bk_fderiv_of_cubic`, `bk_fderiv_of_quartic` : `Df(y)[w] = B` when `f(y + tw) = A + tB + t²C + ⋯`;
* `brkClosed` : the leaf (L1), `b_j = G·bkP`;
* `brkIdentity_of` : `BrkIdentity` from the closed-form leaves (L1)-(L6);
* `hpASumX_of`, `vsumSum_of`, `psiASum_of`, `hpASumLap_of` : the tsum leaves (T1), (T4), (T5), (T2)
  from the generic lattice lemma (G1) and the Gaussian bounds (B1)-(B4);
* `bk_trainPl_differentiableAt` : the train is differentiable in `x` at `s > 0` (`IsTrain.smooth_v`);
* `hasSum_merPl_fAj`, `hasSum_merPl_eAj` : `f_A, e_A` termwise (`fATermSummable`, `eATermSummable`);
* `rPerSplit_of` : `RPerSplit` from `BrkIdentity`, the tsum leaves (T1)-(T5) and `TsumBilinSplit`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. Algebra -/

/-- **The single-center identity in closed form** (source 5022-5025): a polynomial identity in
`y, a, G` and the entries of `M = A^y(s)`, `M' = (A^y)'(s)`, `B = M' + (μ/s)M`. -/
theorem bk_algebra (M M' : Mat3) (ν μ s a g : ℝ) (y : ℝ × ℝ) (ha : a ≠ 0) :
    g • (bkP M' a y + ν • bkPa M a y) + (μ / s) • (g • bkP M a y)
        - ν • ∑ a' : Fin 2, g • bkD2 M a y (ei a') (ei a')
        + g • bkD1 M a y (g • Jrot y) + g • bkV1 a y (g • bkP M a y) =
      -(g • bkV1 a y (merApply (M' + (μ / s) • M) y) + merApply (M' + (μ / s) • M) (g • Jrot y))
        + ((2 : ℝ) • merApply (M' + (μ / s) • M) (g • Jrot y)
          + (2 * ν) • (∑ a' : Fin 2, ∑ b : Fin 2, M (mi a') (mi b) • (g • bkV2 a y (ei b) (ei a')))
          - merApply (fun a' b => M a' b + M b a') (g ^ 2 • y))
        + g ^ 2 • bkPsi M a y := by
  obtain ⟨y1, y2⟩ := y
  simp only [Fin.sum_univ_two, bkP, bkPa, bkD1, bkD2, bkPd, bkPdd, bkV1, bkV2, bkPsi, bkDot,
    merApply, Jrot, sq2, tr3, mi, ei, Matrix.cons_val_zero, Matrix.cons_val_one,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Prod.smul_mk, Prod.mk_add_mk,
    Prod.mk_sub_mk, Prod.neg_mk]
  ext <;> simp only <;> field_simp <;> ring

/-! ## 2. The meridional projection -/

/-- `merPl` as a continuous linear map. -/
def bkMerPlL : Vec3 →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0).prod
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2)

theorem bkMerPlL_apply (v : Vec3) : bkMerPlL v = merPl v := rfl

theorem bk_merPl_neg (v : Vec3) : merPl (-v) = -merPl v := rfl

theorem bk_merPl_add (v w : Vec3) : merPl (v + w) = merPl v + merPl w := rfl

theorem bk_merPl_sub (v w : Vec3) : merPl (v - w) = merPl v - merPl w := rfl

theorem bk_merPl_smul (r : ℝ) (v : Vec3) : merPl (r • v) = r • merPl v := rfl

theorem bk_merPl_emb (v : ℝ × ℝ) : merPl (emb v) = v := rfl

theorem bk_merPl_mv_emb (B : Mat3) (v : ℝ × ℝ) : merPl (mv B (emb v)) = merApply B v := by
  simp [merPl, mv, emb, merApply, Fin.sum_univ_three]

theorem bk_merPl_hessContr (M : Mat3) (V : ℝ × ℝ → ℝ × ℝ) (x : ℝ × ℝ) :
    merPl (hessContr M V x) =
      ∑ a : Fin 2, ∑ b : Fin 2, M (mi a) (mi b) • fderiv ℝ (fun y => fderiv ℝ V y (ei b)) x (ei a) :=
  rfl

/-! ## 3. Closed forms from the existing Gaussian calculus -/

/-- `DV_j[w] = G·(Jw - (y·w)/(2a) Jy)` (source 4963; `gp_fderiv_Vj`). -/
theorem bk_Vj_fderiv (ν s : ℝ) (j : ℤ) (x w : ℝ × ℝ) :
    fderiv ℝ (Vj ν s j) x w = bkG (ageA ν s) (xj ν j x) • bkV1 (ageA ν s) (xj ν j x) w := by
  rw [gp_fderiv_Vj]
  unfold bkG bkV1 bkDot
  ext <;> simp [Jrot] <;> ring

/-- `∇p_j = G²x_j` (source 4964; `mg_fderiv_pj`). -/
theorem bk_mgrad_pj (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ) (ha : 0 < ageA ν s) :
    mgrad (pj ν s j) x = bkG (ageA ν s) (xj ν j x) ^ 2 • xj ν j x := by
  have hexp : Real.exp (-(sq2 (xj ν j x)) / (2 * ageA ν s)) =
      Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) ^ 2 := by
    rw [sq, ← Real.exp_add]
    congr 1
    field_simp
    ring
  have ha0 : ageA ν s ≠ 0 := ha.ne'
  unfold mgrad bkG
  rw [mg_fderiv_pj, mg_fderiv_pj, hexp]
  ext <;> simp [ei] <;> field_simp

/-- `x ↦ x_j` is differentiable. -/
theorem bk_xj_differentiable (ν : ℝ) (j : ℤ) : Differentiable ℝ (xj ν j) := by
  unfold xj; fun_prop

/-- **Gaussian product rule** (source 4963, 4978): for a differentiable profile `P`,
`D[G(a, x_j)·P(x_j)][u] = G·(DP[u] - (x_j·u)/(2a)·P)`, `a = 1 + νs`. -/
theorem bkG_smul_fderiv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (ν s : ℝ) (j : ℤ)
    (P : ℝ × ℝ → E) (hP : Differentiable ℝ P) (x u : ℝ × ℝ) :
    DifferentiableAt ℝ (fun z => bkG (ageA ν s) (xj ν j z) • P (xj ν j z)) x ∧
      fderiv ℝ (fun z => bkG (ageA ν s) (xj ν j z) • P (xj ν j z)) x u =
        bkG (ageA ν s) (xj ν j x) • (fderiv ℝ P (xj ν j x) u
          - (bkDot (xj ν j x) u / (2 * ageA ν s)) • P (xj ν j x)) := by
  have hx := bk_xj_differentiable ν j
  have hG : Differentiable ℝ (fun z => bkG (ageA ν s) (xj ν j z)) := by
    unfold bkG xj sq2; fun_prop
  have hd : DifferentiableAt ℝ (fun z => bkG (ageA ν s) (xj ν j z) • P (xj ν j z)) x :=
    (hG x).smul ((hP _).comp x (hx x))
  refine ⟨hd, ?_⟩
  rw [gp_fderiv_line _ x u hd]
  have hl : HasDerivAt (fun t : ℝ => xj ν j (x + t • u)) u 0 := by
    have e1 : HasDerivAt (fun t : ℝ => (xj ν j (x + t • u)).1) u.1 0 := by
      have h := (((hasDerivAt_id' (0:ℝ)).mul_const u.1).const_add x.1).sub_const
        ((j : ℝ) * cOf ν)
      simpa [xj] using h
    have e2 : HasDerivAt (fun t : ℝ => (xj ν j (x + t • u)).2) u.2 0 := by
      have h := ((hasDerivAt_id' (0:ℝ)).mul_const u.2).const_add x.2
      simpa [xj] using h
    exact e1.prodMk e2
  have hP' : HasDerivAt (fun t : ℝ => P (xj ν j (x + t • u))) (fderiv ℝ P (xj ν j x) u) 0 := by
    have h0 : HasFDerivAt P (fderiv ℝ P (xj ν j x)) (xj ν j (x + (0 : ℝ) • u)) := by
      simpa using (hP (xj ν j x)).hasFDerivAt
    exact h0.comp_hasDerivAt (0 : ℝ) hl
  have hE := (gp_exp_line ν s j x u).const_mul ((ageA ν s ^ 2)⁻¹)
  have hprod : HasDerivAt (fun t : ℝ => ((ageA ν s ^ 2)⁻¹ *
        Real.exp (-(sq2 (xj ν j (x + t • u))) / (4 * ageA ν s))) • P (xj ν j (x + t • u)))
      (((ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j (x + (0 : ℝ) • u))) / (4 * ageA ν s))) •
          fderiv ℝ P (xj ν j x) u +
        ((ageA ν s ^ 2)⁻¹ * (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) *
          (-(2 * (xj ν j x).1 * u.1 + 2 * (xj ν j x).2 * u.2) / (4 * ageA ν s)))) •
            P (xj ν j (x + (0 : ℝ) • u))) 0 := hE.smul hP'
  have e : (fun t : ℝ => bkG (ageA ν s) (xj ν j (x + t • u)) • P (xj ν j (x + t • u))) =
      (fun t : ℝ => ((ageA ν s ^ 2)⁻¹ *
        Real.exp (-(sq2 (xj ν j (x + t • u))) / (4 * ageA ν s))) • P (xj ν j (x + t • u))) := rfl
  rw [e, hprod.deriv]
  simp only [zero_smul, add_zero, bkG, bkDot]
  rw [smul_sub, smul_smul, sub_eq_add_neg, ← neg_smul]
  congr 2
  ring

/-- **Directional derivative of a cubic profile**: if `f(y + tw) = A + tB + t²C + t³D` for all `t`
then `Df(y)[w] = B` (the tool for the polynomial factors `bkP`, `bkD1`, `bkV1` of (L2), (L3), (L5)). -/
theorem bk_fderiv_of_cubic {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × ℝ → E) (y w : ℝ × ℝ) (hf : DifferentiableAt ℝ f y) (A B C D : E)
    (h : ∀ t : ℝ, f (y + t • w) = A + t • B + t ^ 2 • C + t ^ 3 • D) : fderiv ℝ f y w = B := by
  rw [gp_fderiv_line f y w hf]
  have e : (fun t : ℝ => f (y + t • w)) = fun t => A + t • B + t ^ 2 • C + t ^ 3 • D := funext h
  rw [e]
  have hB := (hasDerivAt_id (0 : ℝ)).smul_const B
  have hC := (hasDerivAt_pow 2 (0 : ℝ)).smul_const C
  have hD := (hasDerivAt_pow 3 (0 : ℝ)).smul_const D
  have h1 := ((hB.const_add A).add hC).add hD
  have h2 : HasDerivAt (fun t : ℝ => A + t • B + t ^ 2 • C + t ^ 3 • D) B 0 := by
    convert h1 using 1
    · funext t
      simp [Pi.add_apply]
    · simp
  exact h2.deriv

/-- Quartic version of `bk_fderiv_of_cubic`. -/
theorem bk_fderiv_of_quartic {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × ℝ → E) (y w : ℝ × ℝ) (hf : DifferentiableAt ℝ f y) (A B C D F : E)
    (h : ∀ t : ℝ, f (y + t • w) = A + t • B + t ^ 2 • C + t ^ 3 • D + t ^ 4 • F) :
    fderiv ℝ f y w = B := by
  rw [gp_fderiv_line f y w hf]
  have e : (fun t : ℝ => f (y + t • w)) =
      fun t => A + t • B + t ^ 2 • C + t ^ 3 • D + t ^ 4 • F := funext h
  rw [e]
  have hB := (hasDerivAt_id (0 : ℝ)).smul_const B
  have hC := (hasDerivAt_pow 2 (0 : ℝ)).smul_const C
  have hD := (hasDerivAt_pow 3 (0 : ℝ)).smul_const D
  have hF := (hasDerivAt_pow 4 (0 : ℝ)).smul_const F
  have h1 := (((hB.const_add A).add hC).add hD).add hF
  have h2 : HasDerivAt (fun t : ℝ => A + t • B + t ^ 2 • C + t ^ 3 • D + t ^ 4 • F) B 0 := by
    convert h1 using 1
    · funext t
      simp [Pi.add_apply]
    · simp
  exact h2.deriv

/-- **(L1)** `b_j = G·bkP` (source 4971-4973). -/
theorem brkClosed : BrkClosed := by
  intro ν χ A s j x
  unfold brk
  rw [bk_Vj_fderiv, Vj_eq_bkG]
  ext <;> simp [bkP, bkV1, bkDot, merApply, Jrot] <;> ring

/-! ## 4. The single-center identity from the closed forms -/

theorem brkIdentity_of (h1 : BrkClosed) (h2 : BrkFDerivClosed) (h3 : BrkSecondClosed)
    (h4 : BrkDerivSClosed) (h5 : VjSecondClosed) (h6 : MgradPsiAjClosed) : BrkIdentity := by
  intro ν μ χ A s j x hν hs hAd
  have ha : 0 < ageA ν s := by unfold ageA; have := mul_pos hν hs; linarith
  have eD : deriv (fun s' => brk ν χ A s' j x) s =
      bkG (ageA ν s) (xj ν j x) • (bkP (deriv (Ay ν χ A) s) (ageA ν s) (xj ν j x)
        + ν • bkPa (Ay ν χ A s) (ageA ν s) (xj ν j x)) :=
    (h4 ν χ A s j x _ ha hAd.hasDerivAt).deriv
  have eL : lapPl (brk ν χ A s j) x = ∑ a' : Fin 2,
      bkG (ageA ν s) (xj ν j x) • bkD2 (Ay ν χ A s) (ageA ν s) (xj ν j x) (ei a') (ei a') := by
    unfold lapPl
    refine Finset.sum_congr rfl (fun a' _ => ?_)
    exact (h3 ν χ A s j ha (ei a')).2 x (ei a')
  have eDb : fderiv ℝ (brk ν χ A s j) x (Vj ν s j x) =
      bkG (ageA ν s) (xj ν j x) • bkD1 (Ay ν χ A s) (ageA ν s) (xj ν j x)
        (bkG (ageA ν s) (xj ν j x) • Jrot (xj ν j x)) :=
    (h2 ν χ A s j ha).2 x _
  have eB : brk ν χ A s j x = bkG (ageA ν s) (xj ν j x) • bkP (Ay ν χ A s) (ageA ν s) (xj ν j x) :=
    h1 ν χ A s j x
  have hV2 : ∀ w u : ℝ × ℝ, fderiv ℝ (fun z => fderiv ℝ (Vj ν s j) z w) x u =
      bkG (ageA ν s) (xj ν j x) • bkV2 (ageA ν s) (xj ν j x) w u :=
    fun w u => (h5 ν s j ha w).2 x u
  have eF : merPl (fAj ν μ χ A s j x) =
      -(bkG (ageA ν s) (xj ν j x) • bkV1 (ageA ν s) (xj ν j x)
          (merApply (deriv (Ay ν χ A) s + (μ / s) • Ay ν χ A s) (xj ν j x))
        + merApply (deriv (Ay ν χ A) s + (μ / s) • Ay ν χ A s)
          (bkG (ageA ν s) (xj ν j x) • Jrot (xj ν j x))) := by
    unfold fAj
    rw [bk_merPl_neg, bk_merPl_add, bk_merPl_emb, bk_merPl_mv_emb, bk_Vj_fderiv]
    rfl
  have eE : merPl (eAj ν μ χ A s j x) =
      (2 : ℝ) • merApply (deriv (Ay ν χ A) s + (μ / s) • Ay ν χ A s)
          (bkG (ageA ν s) (xj ν j x) • Jrot (xj ν j x))
        + (2 * ν) • (∑ a' : Fin 2, ∑ b : Fin 2, Ay ν χ A s (mi a') (mi b) •
            (bkG (ageA ν s) (xj ν j x) • bkV2 (ageA ν s) (xj ν j x) (ei b) (ei a')))
        - merApply (fun a' b => Ay ν χ A s a' b + Ay ν χ A s b a')
            (bkG (ageA ν s) (xj ν j x) ^ 2 • xj ν j x) := by
    unfold eAj
    rw [bk_merPl_sub, bk_merPl_add, bk_merPl_smul, bk_merPl_smul, bk_merPl_mv_emb, bk_merPl_hessContr,
      bk_merPl_mv_emb, bk_mgrad_pj ν s j x ha]
    simp only [hV2]
    rfl
  have eP : mgrad (PsiAj ν χ A s j) x =
      bkG (ageA ν s) (xj ν j x) ^ 2 • bkPsi (Ay ν χ A s) (ageA ν s) (xj ν j x) :=
    (h6 ν χ A s j ha).2 x
  rw [eD, eL, eDb, eB, bk_Vj_fderiv, eF, eE, eP]
  exact bk_algebra (Ay ν χ A s) (deriv (Ay ν χ A) s) ν μ s (ageA ν s) _ (xj ν j x) ha.ne'

/-! ## 5. The train, `f_A` and `e_A` termwise -/

/-- The planar train is differentiable in `x` at `s > 0` (source 2040-2051; `IsTrain.smooth_v`). -/
theorem bk_trainPl_differentiableAt {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ}
    (hs : 0 < s) (x : ℝ × ℝ) : DifferentiableAt ℝ (trainPl tr s) x := by
  have h1 := tr.isTrain.smooth_v.of_le (m := 1) (by exact_mod_cast le_top)
  have hmem : Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) ∈ 𝓝 ((s, x) : ℝ × (ℝ × ℝ)) :=
    prod_mem_nhds (Ici_mem_nhds hs) univ_mem
  have hd := (h1.contDiffAt hmem).differentiableAt (by norm_num)
  have hc : DifferentiableAt ℝ (fun z : ℝ × ℝ => tr.v s z) x :=
    hd.comp x ((differentiableAt_const s).prodMk differentiableAt_id)
  have e0 := ((EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).differentiableAt
    (x := tr.v s x)).comp x hc
  have e1 := ((EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).differentiableAt
    (x := tr.v s x)).comp x hc
  exact e0.prodMk e1

theorem hasSum_merPl_fAj (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ)
    (hν : 0 < ν) (hs : 0 < s) :
    HasSum (fun j : ℤ => merPl (fAj ν μ χ A s j x)) (merPl (fA ν μ χ A s x)) := by
  have hS := (fATermSummable ν μ χ A s x hν hs).hasSum.neg
  exact bkMerPlL.hasSum hS

theorem hasSum_merPl_eAj (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ)
    (hν : 0 < ν) (hs : 0 < s) :
    HasSum (fun j : ℤ => merPl (eAj ν μ χ A s j x)) (merPl (eA ν μ χ A s x)) := by
  have hS := (eATermSummable ν μ χ A s x hν hs).hasSum
  exact bkMerPlL.hasSum hS

/-! ## 6a. The tsum calculus from the generic lattice lemma and the Gaussian bounds -/

theorem bk_one_le_ageA {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) : 1 ≤ ageA ν s := by
  unfold ageA; have := mul_pos hν hs; linarith

theorem bkMaj_nonneg (ν a : ℝ) (j : ℤ) (z : ℝ × ℝ) : 0 ≤ bkMaj ν a j z := by
  unfold bkMaj; positivity

theorem bk_norm_ei_le_one (b : Fin 2) : ‖ei b‖ ≤ 1 := by
  fin_cases b <;> simp [ei, Prod.norm_def]

/-- **(T1)** from (G1), (B1) and (L2). -/
theorem hpASumX_of (hG : LatticeFDerivSum) (hB : BrkGaussBound1) (hD : BrkFDerivClosed) :
    HpASumX := by
  intro ν χ A s hν hs x
  obtain ⟨K, hK⟩ := hB ν χ A s hν hs
  have ha1 := bk_one_le_ageA hν hs
  exact hG (ℝ × ℝ) ν (ageA ν s) K (fun j => brk ν χ A s j) hν ha1
    (fun j => (hD ν χ A s j (by linarith)).1) (fun j z => (hK j z).1) (fun j z => (hK j z).2) x

/-- **(T4)** from (G1) and (B3). -/
theorem vsumSum_of (hG : LatticeFDerivSum) (hB : VjGaussBound) : VsumSum := by
  intro ν s hν hs x
  obtain ⟨K, hK⟩ := hB ν s hν hs
  exact hG (ℝ × ℝ) ν (ageA ν s) K (fun k => Vj ν s k) hν (bk_one_le_ageA hν hs)
    (fun k z => gp_Vj_diff ν s k z) (fun k z => (hK k z).1) (fun k z => (hK k z).2) x

/-- Evaluation of a termwise derivative series in a direction. -/
theorem bk_hasSum_fderiv_apply {f : ℤ → (ℝ × ℝ →L[ℝ] ℝ × ℝ)} (hf : Summable (fun j => ‖f j‖))
    (v : ℝ × ℝ) : HasSum (fun j => f j v) ((∑' j, f j) v) :=
  (ContinuousLinearMap.apply ℝ (ℝ × ℝ) v).hasSum hf.of_norm.hasSum

/-- **(T5)** from (G1), (B4) and (L6). -/
theorem psiASum_of (hG : LatticeFDerivSum) (hB : PsiAjGaussBound) (hC : MgradPsiAjClosed) :
    PsiAGradSum := by
  intro ν χ A s hν hs x
  obtain ⟨K, hK⟩ := hB ν χ A s hν hs
  have ha1 := bk_one_le_ageA hν hs
  obtain ⟨hF, hDS, -⟩ := hG ℝ ν (ageA ν s) K (fun j => PsiAj ν χ A s j) hν ha1
    (fun j => (hC ν χ A s j (by linarith)).1) (fun j z => (hK j z).1) (fun j z => (hK j z).2) x
  have hF' : HasFDerivAt (PsiA ν χ A s) (∑' j : ℤ, fderiv ℝ (PsiAj ν χ A s j) x) x := hF
  have e : ∀ v : ℝ × ℝ, HasSum (fun j : ℤ => fderiv ℝ (PsiAj ν χ A s j) x v)
      ((∑' j : ℤ, fderiv ℝ (PsiAj ν χ A s j) x) v) :=
    fun v => (ContinuousLinearMap.apply ℝ ℝ v).hasSum hDS.of_norm.hasSum
  unfold mgrad
  rw [hF'.fderiv]
  exact (e (ei 0)).prodMk (e (ei 1))

/-- **(T2)** from (T1), (G1), (B1), (B2) and (L3). -/
theorem hpASumLap_of (hG : LatticeFDerivSum) (hX : HpASumX) (hB1 : BrkGaussBound1)
    (hB2 : BrkGaussBound2) (hD2 : BrkSecondClosed) : HpASumLap := by
  intro ν χ A s hν hs x
  obtain ⟨K1, hK1⟩ := hB1 ν χ A s hν hs
  obtain ⟨K2, hK2⟩ := hB2 ν χ A s hν hs
  have ha1 := bk_one_le_ageA hν hs
  have hcol : ∀ b : Fin 2,
      HasSum (fun j : ℤ => fderiv ℝ (fun z => fderiv ℝ (brk ν χ A s j) z (ei b)) x (ei b))
        (fderiv ℝ (fun z => fderiv ℝ (hpA ν χ A s) z (ei b)) x (ei b)) := by
    intro b
    have hfun : (fun z => fderiv ℝ (hpA ν χ A s) z (ei b)) =
        (fun z => ∑' j : ℤ, fderiv ℝ (brk ν χ A s j) z (ei b)) := by
      funext z
      obtain ⟨hXd, hDbS, -⟩ := hX ν χ A s hν hs z
      rw [hXd.fderiv]
      exact (bk_hasSum_fderiv_apply hDbS (ei b)).tsum_eq.symm
    have hb1 : ∀ (j : ℤ) (z : ℝ × ℝ), ‖fderiv ℝ (brk ν χ A s j) z (ei b)‖ ≤
        max K1 K2 * bkMaj ν (ageA ν s) j z := by
      intro j z
      have h1 := (fderiv ℝ (brk ν χ A s j) z).le_opNorm (ei b)
      have h2 := (hK1 j z).2
      have h3 := bk_norm_ei_le_one b
      have hm := bkMaj_nonneg ν (ageA ν s) j z
      have h4 : K1 * bkMaj ν (ageA ν s) j z ≤ max K1 K2 * bkMaj ν (ageA ν s) j z :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hm
      have h5 : ‖fderiv ℝ (brk ν χ A s j) z‖ * ‖ei b‖ ≤ ‖fderiv ℝ (brk ν χ A s j) z‖ :=
        mul_le_of_le_one_right (norm_nonneg _) h3
      linarith
    have hb2 : ∀ (j : ℤ) (z : ℝ × ℝ),
        ‖fderiv ℝ (fun z' => fderiv ℝ (brk ν χ A s j) z' (ei b)) z‖ ≤
          max K1 K2 * bkMaj ν (ageA ν s) j z := fun j z =>
      (hK2 j z b).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (bkMaj_nonneg _ _ _ _))
    obtain ⟨hF, hDS, -⟩ := hG (ℝ × ℝ) ν (ageA ν s) (max K1 K2)
      (fun j z => fderiv ℝ (brk ν χ A s j) z (ei b)) hν ha1
      (fun j => (hD2 ν χ A s j (by linarith) (ei b)).1) hb1 hb2 x
    rw [hfun, hF.fderiv]
    exact bk_hasSum_fderiv_apply hDS (ei b)
  unfold lapPl
  simp only [Fin.sum_univ_two]
  exact (hcol 0).add (hcol 1)

/-! ## 6. The bracket split -/

/-- **`RPerSplit` from the single-center identity and the tsum calculus** (source 5022-5027):
summing `BrkIdentity` over `j` (`HpASumS`, `HpASumX`, `HpASumLap`, `PsiAGradSum`, and `f_A, e_A`
termwise) and splitting `(v·∇)h^p_A + (h^p_A·∇)v` with `v = Σ_kV_k + (v - Σ_kV_k)`
(`VsumSum`, `TsumBilinSplit`, the train differentiable at `s > 0`). -/
theorem rPerSplit_of (as : ℝ) (χf : ℝ → ℝ) (hI : BrkIdentity) (hS : HpASumS as χf)
    (hX : HpASumX) (hL : HpASumLap) (hV : VsumSum) (hP : PsiAGradSum) (hD : TsumBilinSplit) :
    RPerSplit as χf := by
  intro hχ p d dm dp hreg μ A hA s hs x
  have hν : 0 < p.ν := p.ν_pos
  obtain ⟨hXd, hDbS, hbS⟩ := hX p.ν χf A s hν hs x
  obtain ⟨hVd, hDVS, hVS⟩ := hV p.ν s hν hs x
  have hTd : DifferentiableAt ℝ (trainPl p.train s) x := bk_trainPl_differentiableAt p.train hs x
  have hAd : DifferentiableAt ℝ (Ay p.ν χf A) s := ayDiffAt as χf hχ p.ν A hA s hs
  have hdiag := hD (fun j => brk p.ν χf A s j x) (fun k => Vj p.ν s k x)
    (fun j => fderiv ℝ (brk p.ν χf A s j) x) (fun k => fderiv ℝ (Vj p.ν s k) x) hbS hVS hDbS hDVS
  have hb : HasSum (fun j => brk p.ν χf A s j x) (hpA p.ν χf A s x) := hbS.of_norm.hasSum
  have hsumL : HasSum (fun j : ℤ => deriv (fun s' => brk p.ν χf A s' j x) s
        + (μ / s) • brk p.ν χf A s j x - p.ν • lapPl (brk p.ν χf A s j) x
        + (fderiv ℝ (brk p.ν χf A s j) x (Vj p.ν s j x)
          + fderiv ℝ (Vj p.ν s j) x (brk p.ν χf A s j x)))
      (deriv (fun s' => hpA p.ν χf A s' x) s + (μ / s) • hpA p.ν χf A s x
        - p.ν • lapPl (hpA p.ν χf A s) x
        + ((∑' j, fderiv ℝ (brk p.ν χf A s j) x) (vsum p.ν s x)
          + (∑' k, fderiv ℝ (Vj p.ν s k) x) (hpA p.ν χf A s x)
          - rCross p.ν χf A s x)) :=
    (((hS hχ p.ν hν A hA s hs x).add (hb.const_smul (μ / s))).sub
      ((hL p.ν χf A s hν hs x).const_smul p.ν)).add hdiag
  have hsumR : HasSum (fun j : ℤ => merPl (fAj p.ν μ χf A s j x) + merPl (eAj p.ν μ χf A s j x)
        + mgrad (PsiAj p.ν χf A s j) x)
      (merPl (fA p.ν μ χf A s x) + merPl (eA p.ν μ χf A s x) + mgrad (PsiA p.ν χf A s) x) :=
    ((hasSum_merPl_fAj p.ν μ χf A s x hν hs).add (hasSum_merPl_eAj p.ν μ χf A s x hν hs)).add
      (hP p.ν χf A s hν hs x)
  have hterm : (fun j : ℤ => deriv (fun s' => brk p.ν χf A s' j x) s
        + (μ / s) • brk p.ν χf A s j x - p.ν • lapPl (brk p.ν χf A s j) x
        + (fderiv ℝ (brk p.ν χf A s j) x (Vj p.ν s j x)
          + fderiv ℝ (Vj p.ν s j) x (brk p.ν χf A s j x))) =
      (fun j : ℤ => merPl (fAj p.ν μ χf A s j x) + merPl (eAj p.ν μ χf A s j x)
        + mgrad (PsiAj p.ν χf A s j) x) := by
    funext j
    rw [← hI p.ν μ χf A s j x hν hs hAd]
    abel
  rw [hterm] at hsumL
  have huniq := hsumL.unique hsumR
  have hsub : fderiv ℝ (fun y => trainPl p.train s y - vsum p.ν s y) x =
      fderiv ℝ (trainPl p.train s) x - fderiv ℝ (vsum p.ν s) x :=
    fderiv_fun_sub hTd hVd.differentiableAt
  unfold rPer rTrain
  rw [hsub, hXd.fderiv, hVd.fderiv, map_sub, ContinuousLinearMap.sub_apply]
  rw [← sub_eq_zero] at huniq ⊢
  rw [← huniq]
  abel

end UnforcedLeray.Short.PartIIIb.Concrete
