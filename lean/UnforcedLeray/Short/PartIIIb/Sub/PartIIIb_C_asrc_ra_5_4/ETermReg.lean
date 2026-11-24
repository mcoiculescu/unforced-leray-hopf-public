import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.AyContDiff
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.BmatContinuous
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.GpAdd
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.GpBilin
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.GpClm
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.GpFderiv
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.GpMono
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.GpPj
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.GpTermBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.GpVj
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.Ps54Bilin
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.Ps54OfS
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.Ps54Snd
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps.Targets

/-!
# `PartIII-b:C/asrc/ra/5/4` : the `j = 0` term of `e_A` is `GP54`-regular

Source of record: `the November 2 reference manuscript` lines 4963-4981, 4978.
`eATerm ν μ χf A s x 0 = 2 • mv B (emb V_0 x) + (2ν) • emb (Σ_{a,b} A^y_{ab} ∂_a∂_b V_0) - mv (A^y + (A^y)ᵀ) (emb ∇p_0)`.
The `p_0` term has Gaussian parameter `κ = 2`; it is weakened to `κ = 4` by `etr_gp_weaken`
(`exp(-r/(2a)) ≤ exp(-r/(4a))`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- A additive, `ℝ`-homogeneous map on a finite-dimensional space is a continuous linear map. -/
theorem etr_clm_fd {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (h1 : ∀ x y, f (x + y) = f x + f y)
    (h2 : ∀ (c : ℝ) x, f (c • x) = c • f x) : ∃ L : E →L[ℝ] F, ∀ x, L x = f x :=
  ⟨LinearMap.toContinuousLinearMap ({ toFun := f, map_add' := h1, map_smul' := h2 } : E →ₗ[ℝ] F),
    fun x => by simp⟩

/-- A bilinear map on finite-dimensional spaces is a continuous bilinear map. -/
theorem etr_clm_bil {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (f : E → F → G)
    (h1 : ∀ x y z, f (x + y) z = f x z + f y z) (h2 : ∀ (c : ℝ) x z, f (c • x) z = c • f x z)
    (h3 : ∀ x y z, f x (y + z) = f x y + f x z) (h4 : ∀ (c : ℝ) x z, f x (c • z) = c • f x z) :
    ∃ B : E →L[ℝ] F →L[ℝ] G, ∀ x y, B x y = f x y := by
  have hx : ∀ x : E, ∃ Lx : F →L[ℝ] G, ∀ y, Lx y = f x y := fun x =>
    etr_clm_fd (f x) (fun y z => h3 x y z) (fun c y => h4 c x y)
  choose Φ hΦ using hx
  have hΦadd : ∀ x y, Φ (x + y) = Φ x + Φ y := fun x y =>
    ContinuousLinearMap.ext fun z => by simp only [add_apply, hΦ, h1]
  have hΦsmul : ∀ (c : ℝ) x, Φ (c • x) = c • Φ x := fun c x =>
    ContinuousLinearMap.ext fun z => by simp only [smul_apply, hΦ, h2]
  obtain ⟨B, hB⟩ := etr_clm_fd Φ hΦadd hΦsmul
  exact ⟨B, fun x y => by rw [hB, hΦ]⟩

/-- Equality of the functions transports `GP54`. -/
theorem etr_gp_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (κ ν : ℝ) (n : ℕ)
    {f g : ℝ × (ℝ × ℝ) → E} (h : GP54 κ ν n f) (e : f = g) : GP54 κ ν n g := by
  rw [← e]; exact h

/-- The Gaussian parameter can only be weakened: `κ ≤ κ'` (`exp(-r/(κa)) ≤ exp(-r/(κ'a))`). -/
theorem etr_gp_weaken {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (κ κ' ν : ℝ) (n : ℕ)
    (f : ℝ × (ℝ × ℝ) → E) (hκ : 0 < κ) (hle : κ ≤ κ') (hν : 0 < ν) (hf : GP54 κ ν n f) :
    GP54 κ' ν n f := by
  obtain ⟨hc, hb⟩ := hf
  refine ⟨hc, fun s0 s1 hs0 hs01 => ?_⟩
  obtain ⟨C, N, hC, hbd⟩ := hb s0 s1 hs0 hs01
  refine ⟨C, N, hC, fun m hm s hs x => ?_⟩
  refine (hbd m hm s hs x).trans ?_
  have hp : 0 ≤ 1 + sq2 x := by unfold sq2; positivity
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC (pow_nonneg hp _))
  apply Real.exp_le_exp.2
  have ha : 0 < ageA ν s1 := by unfold ageA; nlinarith
  have hr : 0 ≤ sq2 x := by unfold sq2; positivity
  have h1 : 0 < κ * ageA ν s1 := mul_pos hκ ha
  have h3 : κ * ageA ν s1 ≤ κ' * ageA ν s1 := mul_le_mul_of_nonneg_right hle ha.le
  rw [neg_div, neg_div]
  apply neg_le_neg
  exact div_le_div_of_nonneg_left hr h1 h3

theorem eTermReg (as : ℝ) (χf : ℝ → ℝ) : ETermReg as χf := by
  intro hχ ν μ hν A hA
  have hAyc : ContinuousOn (Ay ν χf A) (Ioi (0 : ℝ)) :=
    (ay54_contDiffOn as χf hχ ν A hA).continuousOn
  have hBcont : ContinuousOn (Bmat ν μ χf A) (Ioi (0 : ℝ)) :=
    bmat54_continuousOn as χf hχ ν μ A hA
  have hBm : PS54 0 (fun p : ℝ × (ℝ × ℝ) => Bmat ν μ χf A p.1) :=
    ps54_of_s 0 (Bmat ν μ χf A) (contDiffOn_zero.2 hBcont)
  -- scalar entries `s ↦ A^y_{ij}(s)`
  have hsc : ∀ i j : Fin 3, ContinuousOn (fun s : ℝ => Ay ν χf A s i j) (Ioi (0 : ℝ)) :=
    fun i j => (continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hAyc)
  have hsPS : ∀ i j : Fin 3, PS54 0 (fun p : ℝ × (ℝ × ℝ) => Ay ν χf A p.1 i j) := fun i j =>
    ps54_of_s 0 (fun s : ℝ => Ay ν χf A s i j) (contDiffOn_zero.2 (hsc i j))
  -- the matrix `A^y + (A^y)ᵀ`
  have hAytc : ContinuousOn (fun s : ℝ => (fun a b => Ay ν χf A s a b + Ay ν χf A s b a : Mat3))
      (Ioi (0 : ℝ)) :=
    continuousOn_pi.2 fun a => continuousOn_pi.2 fun b => (hsc a b).add (hsc b a)
  have hAytPS : PS54 0 (fun p : ℝ × (ℝ × ℝ) =>
      (fun a b => Ay ν χf A p.1 a b + Ay ν χf A p.1 b a : Mat3)) :=
    ps54_of_s 0 (fun s : ℝ => (fun a b => Ay ν χf A s a b + Ay ν χf A s b a : Mat3))
      (contDiffOn_zero.2 hAytc)
  -- the linear embedding and the bilinear matrix-vector product
  have hembadd : ∀ x y : ℝ × ℝ, emb (x + y) = emb x + emb y := fun x y => by
    funext i; fin_cases i <;> simp [emb]
  have hembsmul : ∀ (c : ℝ) (x : ℝ × ℝ), emb (c • x) = c • emb x := fun c x => by
    funext i; fin_cases i <;> simp [emb]
  obtain ⟨embL, hembL⟩ := etr_clm_fd emb hembadd hembsmul
  have mv_h1 : ∀ (x y : Vec3) (z : Mat3), mv z (x + y) = mv z x + mv z y := fun x y z => by
    funext i; simp only [mv, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have mv_h2 : ∀ (c : ℝ) (x : Vec3) (z : Mat3), mv z (c • x) = c • mv z x := fun c x z => by
    funext i; simp only [mv, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have mv_h3 : ∀ (x : Vec3) (y z : Mat3), mv (y + z) x = mv y x + mv z x := fun x y z => by
    funext i; simp only [mv, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have mv_h4 : ∀ (c : ℝ) (x : Vec3) (z : Mat3), mv (c • z) x = c • mv z x := fun c x z => by
    funext i; simp only [mv, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  obtain ⟨Bmv, hBmv⟩ := etr_clm_bil (E := Vec3) (F := Mat3) (G := Vec3)
    (fun (x : Vec3) (M : Mat3) => mv M x) mv_h1 mv_h2 mv_h3 mv_h4
  -- scalar times vector
  obtain ⟨Bsc, hBsc⟩ := etr_clm_bil (E := ℝ × ℝ) (F := ℝ) (G := ℝ × ℝ)
    (fun (v : ℝ × ℝ) (c : ℝ) => c • v)
    (fun x y z => smul_add z x y) (fun c x z => smul_comm z c x)
    (fun x y z => add_smul y z x) (fun c x z => mul_smul c z x)
  -- the meridional gradient, as a continuous linear map of the differential
  let Lm : ((ℝ × ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ × ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ (ei 0)).prod (ContinuousLinearMap.apply ℝ ℝ (ei 1))
  have hLm : ∀ M : (ℝ × ℝ) →L[ℝ] ℝ, Lm M = (M (ei 0), M (ei 1)) := fun M => by
    simp [Lm]
  -- GP54 ingredients
  have hV2 : GP54 4 ν 2 (fun p : ℝ × (ℝ × ℝ) => Vj ν p.1 0 p.2) := gp54_Vj ν hν 2
  have hD1 : GP54 4 ν 1 (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ (Vj ν p.1 0) p.2) :=
    gp54_fderiv 4 ν 1 _ hV2
  have hEV : GP54 4 ν 0 (fun p : ℝ × (ℝ × ℝ) => embL (Vj ν p.1 0 p.2)) :=
    gp54_clm embL 4 ν 0 _ (gp54_mono 4 ν 2 0 (by norm_num) _ hV2)
  -- term 1: `2 • mv B (emb V_0)`
  have hQ1 : GP54 4 ν 0 (fun p : ℝ × (ℝ × ℝ) =>
      ((2 : ℝ) • ContinuousLinearMap.id ℝ Vec3) (Bmv (embL (Vj ν p.1 0 p.2)) (Bmat ν μ χf A p.1))) :=
    gp54_clm ((2 : ℝ) • ContinuousLinearMap.id ℝ Vec3) 4 ν 0 _ (gp54_bilin Bmv 4 ν 0 _ _ hEV hBm)
  -- term 2: `(2ν) • emb (Σ_{a,b} A^y_{ab} ∂_a∂_b V_0)`
  have hT : ∀ a b : Fin 2, GP54 4 ν 0 (fun p : ℝ × (ℝ × ℝ) =>
      Ay ν χf A p.1 (mi a) (mi b) •
        fderiv ℝ (fun y => fderiv ℝ (Vj ν p.1 0) y (ei b)) p.2 (ei a)) := by
    intro a b
    have hEb : GP54 4 ν 1 (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ (Vj ν p.1 0) p.2 (ei b)) :=
      etr_gp_congr 4 ν 1 (gp54_clm (ContinuousLinearMap.apply ℝ (ℝ × ℝ) (ei b)) 4 ν 1 _ hD1)
        (by funext p; simp)
    have hD2 : GP54 4 ν 0 (fun p : ℝ × (ℝ × ℝ) =>
        fderiv ℝ (fun y => fderiv ℝ (Vj ν p.1 0) y (ei b)) p.2) :=
      gp54_fderiv 4 ν 0 _ hEb
    have hD2a : GP54 4 ν 0 (fun p : ℝ × (ℝ × ℝ) =>
        fderiv ℝ (fun y => fderiv ℝ (Vj ν p.1 0) y (ei b)) p.2 (ei a)) :=
      etr_gp_congr 4 ν 0 (gp54_clm (ContinuousLinearMap.apply ℝ (ℝ × ℝ) (ei a)) 4 ν 0 _ hD2)
        (by funext p; simp)
    exact etr_gp_congr 4 ν 0 (gp54_bilin Bsc 4 ν 0 _ _ hD2a (hsPS (mi a) (mi b)))
      (by funext p; simp [hBsc])
  have hHS : GP54 4 ν 0 (fun p : ℝ × (ℝ × ℝ) => ∑ a : Fin 2, ∑ b : Fin 2,
      Ay ν χf A p.1 (mi a) (mi b) •
        fderiv ℝ (fun y => fderiv ℝ (Vj ν p.1 0) y (ei b)) p.2 (ei a)) := by
    simp only [Fin.sum_univ_two]
    exact gp54_add 4 ν 0 _ _ (gp54_add 4 ν 0 _ _ (hT 0 0) (hT 0 1))
      (gp54_add 4 ν 0 _ _ (hT 1 0) (hT 1 1))
  have hQ2 : GP54 4 ν 0 (fun p : ℝ × (ℝ × ℝ) => ((2 * ν) • embL) (∑ a : Fin 2, ∑ b : Fin 2,
      Ay ν χf A p.1 (mi a) (mi b) •
        fderiv ℝ (fun y => fderiv ℝ (Vj ν p.1 0) y (ei b)) p.2 (ei a))) :=
    gp54_clm ((2 * ν) • embL) 4 ν 0 _ hHS
  -- term 3: `- mv (A^y + (A^y)ᵀ) (emb ∇p_0)`, with `p_0` of parameter `κ = 2`
  have hPJD : GP54 2 ν 0 (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ (pj ν p.1 0) p.2) :=
    gp54_fderiv 2 ν 0 _ (gp54_pj ν hν 1)
  have hPJD4 : GP54 4 ν 0 (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ (pj ν p.1 0) p.2) :=
    etr_gp_weaken 2 4 ν 0 _ (by norm_num) (by norm_num) hν hPJD
  have hMG : GP54 4 ν 0 (fun p : ℝ × (ℝ × ℝ) => embL (Lm (fderiv ℝ (pj ν p.1 0) p.2))) :=
    gp54_clm embL 4 ν 0 _ (gp54_clm Lm 4 ν 0 _ hPJD4)
  have hQ3 : GP54 4 ν 0 (fun p : ℝ × (ℝ × ℝ) => (-ContinuousLinearMap.id ℝ Vec3)
      (Bmv (embL (Lm (fderiv ℝ (pj ν p.1 0) p.2)))
        (fun a b => Ay ν χf A p.1 a b + Ay ν χf A p.1 b a))) :=
    gp54_clm (-ContinuousLinearMap.id ℝ Vec3) 4 ν 0 _ (gp54_bilin Bmv 4 ν 0 _ _ hMG hAytPS)
  have hG := gp54_add 4 ν 0 _ _ (gp54_add 4 ν 0 _ _ hQ1 hQ2) hQ3
  have eqG : (fun p : ℝ × (ℝ × ℝ) => eATerm ν μ χf A p.1 p.2 0) =
      fun p : ℝ × (ℝ × ℝ) =>
        ((2 : ℝ) • ContinuousLinearMap.id ℝ Vec3) (Bmv (embL (Vj ν p.1 0 p.2)) (Bmat ν μ χf A p.1))
        + ((2 * ν) • embL) (∑ a : Fin 2, ∑ b : Fin 2,
            Ay ν χf A p.1 (mi a) (mi b) •
              fderiv ℝ (fun y => fderiv ℝ (Vj ν p.1 0) y (ei b)) p.2 (ei a))
        + (-ContinuousLinearMap.id ℝ Vec3) (Bmv (embL (Lm (fderiv ℝ (pj ν p.1 0) p.2)))
            (fun a b => Ay ν χf A p.1 a b + Ay ν χf A p.1 b a)) := by
    funext p
    simp only [eATerm, hessContr, mgrad, hLm, hembL, hBmv, smul_apply,
      ContinuousLinearMap.id_apply, neg_apply, sub_eq_add_neg]
  have key : GP54 4 ν 0 (fun p : ℝ × (ℝ × ℝ) => eATerm ν μ χf A p.1 p.2 0) := by
    rw [eqG]; exact hG
  exact ⟨key.1, gp54_termBound 4 ν (by norm_num) hν 0 _ key⟩

end UnforcedLeray.Short.PartIIIb.Concrete
