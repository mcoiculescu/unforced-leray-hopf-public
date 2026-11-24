import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.AyContDiff
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.BmatContinuous
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.GpAdd
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.GpBilin
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.GpClm
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.GpFderiv
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.GpMono
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.GpTermBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.GpVj
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.Ps54Bilin
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.Ps54OfS
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5_4.Ps54Snd
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps.Targets

/-!
# `PartIII-b:C/asrc/ra/5/4` : the `j = 0` term of `-f_A` is `GP54`-regular

Source of record: `the November 2 reference manuscript` lines 4963-4981, 4978.
`fATerm ν μ χf A s x 0 = emb (DV_0 x (merApply B x)) + mv B (emb (V_0 x))` with `B = Bmat`.
Everything is built from the `GP54` / `PS54` closure lemmas; the bilinear and linear maps
`mv`, `merApply`, `emb` are packaged as continuous (multi)linear maps by the finite-dimensional
constructors `ftr_clm_fd`, `ftr_clm_bil`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- A additive, `ℝ`-homogeneous map on a finite-dimensional space is a continuous linear map. -/
theorem ftr_clm_fd {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (h1 : ∀ x y, f (x + y) = f x + f y)
    (h2 : ∀ (c : ℝ) x, f (c • x) = c • f x) : ∃ L : E →L[ℝ] F, ∀ x, L x = f x :=
  ⟨LinearMap.toContinuousLinearMap ({ toFun := f, map_add' := h1, map_smul' := h2 } : E →ₗ[ℝ] F),
    fun x => by simp⟩

/-- A bilinear map on finite-dimensional spaces is a continuous bilinear map. -/
theorem ftr_clm_bil {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (f : E → F → G)
    (h1 : ∀ x y z, f (x + y) z = f x z + f y z) (h2 : ∀ (c : ℝ) x z, f (c • x) z = c • f x z)
    (h3 : ∀ x y z, f x (y + z) = f x y + f x z) (h4 : ∀ (c : ℝ) x z, f x (c • z) = c • f x z) :
    ∃ B : E →L[ℝ] F →L[ℝ] G, ∀ x y, B x y = f x y := by
  have hx : ∀ x : E, ∃ Lx : F →L[ℝ] G, ∀ y, Lx y = f x y := fun x =>
    ftr_clm_fd (f x) (fun y z => h3 x y z) (fun c y => h4 c x y)
  choose Φ hΦ using hx
  have hΦadd : ∀ x y, Φ (x + y) = Φ x + Φ y := fun x y =>
    ContinuousLinearMap.ext fun z => by simp only [add_apply, hΦ, h1]
  have hΦsmul : ∀ (c : ℝ) x, Φ (c • x) = c • Φ x := fun c x =>
    ContinuousLinearMap.ext fun z => by simp only [smul_apply, hΦ, h2]
  obtain ⟨B, hB⟩ := ftr_clm_fd Φ hΦadd hΦsmul
  exact ⟨B, fun x y => by rw [hB, hΦ]⟩

theorem fTermReg (as : ℝ) (χf : ℝ → ℝ) : FTermReg as χf := by
  intro hχ ν μ hν A hA
  have hBcont : ContinuousOn (Bmat ν μ χf A) (Ioi (0 : ℝ)) :=
    bmat54_continuousOn as χf hχ ν μ A hA
  have hBm : PS54 0 (fun p : ℝ × (ℝ × ℝ) => Bmat ν μ χf A p.1) :=
    ps54_of_s 0 (Bmat ν μ χf A) (contDiffOn_zero.2 hBcont)
  -- the embedding `(v₁, v₂) ↦ (v₁, 0, v₂)` as a continuous linear map
  have hembadd : ∀ x y : ℝ × ℝ, emb (x + y) = emb x + emb y := fun x y => by
    funext i; fin_cases i <;> simp [emb]
  have hembsmul : ∀ (c : ℝ) (x : ℝ × ℝ), emb (c • x) = c • emb x := fun c x => by
    funext i; fin_cases i <;> simp [emb]
  obtain ⟨embL, hembL⟩ := ftr_clm_fd emb hembadd hembsmul
  -- matrix-vector product `mv M v` as a continuous bilinear map `Vec3 → Mat3 → Vec3`
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
  obtain ⟨Bmv, hBmv⟩ := ftr_clm_bil (E := Vec3) (F := Mat3) (G := Vec3)
    (fun (x : Vec3) (M : Mat3) => mv M x) mv_h1 mv_h2 mv_h3 mv_h4
  -- `merApply M x` as a continuous bilinear map `Mat3 → (ℝ × ℝ) → (ℝ × ℝ)`
  have mer_h1 : ∀ (x y : Mat3) (z : ℝ × ℝ), merApply (x + y) z = merApply x z + merApply y z :=
    fun x y z => by ext <;> simp [merApply] <;> ring
  have mer_h2 : ∀ (c : ℝ) (x : Mat3) (z : ℝ × ℝ), merApply (c • x) z = c • merApply x z :=
    fun c x z => by ext <;> simp [merApply] <;> ring
  have mer_h3 : ∀ (x : Mat3) (y z : ℝ × ℝ), merApply x (y + z) = merApply x y + merApply x z :=
    fun x y z => by ext <;> simp [merApply] <;> ring
  have mer_h4 : ∀ (c : ℝ) (x : Mat3) (z : ℝ × ℝ), merApply x (c • z) = c • merApply x z :=
    fun c x z => by ext <;> simp [merApply] <;> ring
  obtain ⟨Bmer, hBmer⟩ := ftr_clm_bil (E := Mat3) (F := ℝ × ℝ) (G := ℝ × ℝ)
    (fun (M : Mat3) (x : ℝ × ℝ) => merApply M x) mer_h1 mer_h2 mer_h3 mer_h4
  -- application of a continuous linear map to a vector, as a bilinear map
  let Bapp : (ℝ × ℝ →L[ℝ] ℝ × ℝ) →L[ℝ] ℝ × ℝ →L[ℝ] ℝ × ℝ :=
    (ContinuousLinearMap.apply ℝ (ℝ × ℝ)).flip
  have hBapp : ∀ (M : ℝ × ℝ →L[ℝ] ℝ × ℝ) (w : ℝ × ℝ), Bapp M w = M w := fun M w => by
    simp [Bapp]
  -- the GP54 / PS54 ingredients
  have hV1 : GP54 4 ν 1 (fun p : ℝ × (ℝ × ℝ) => Vj ν p.1 0 p.2) := gp54_Vj ν hν 1
  have hDV : GP54 4 ν 0 (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ (Vj ν p.1 0) p.2) :=
    gp54_fderiv 4 ν 0 _ hV1
  have hEV : GP54 4 ν 0 (fun p : ℝ × (ℝ × ℝ) => embL (Vj ν p.1 0 p.2)) :=
    gp54_clm embL 4 ν 0 _ (gp54_mono 4 ν 1 0 (by norm_num) _ hV1)
  have hW : PS54 0 (fun p : ℝ × (ℝ × ℝ) => Bmer (Bmat ν μ χf A p.1) p.2) :=
    ps54_bilin Bmer 0 _ _ hBm (ps54_snd 0)
  have hA1 : GP54 4 ν 0 (fun p : ℝ × (ℝ × ℝ) =>
      embL (Bapp (fderiv ℝ (Vj ν p.1 0) p.2) (Bmer (Bmat ν μ χf A p.1) p.2))) :=
    gp54_clm embL 4 ν 0 _ (gp54_bilin Bapp 4 ν 0 _ _ hDV hW)
  have hA2 : GP54 4 ν 0 (fun p : ℝ × (ℝ × ℝ) => Bmv (embL (Vj ν p.1 0 p.2)) (Bmat ν μ χf A p.1)) :=
    gp54_bilin Bmv 4 ν 0 _ _ hEV hBm
  have hG := gp54_add 4 ν 0 _ _ hA1 hA2
  have eqG : (fun p : ℝ × (ℝ × ℝ) => fATerm ν μ χf A p.1 p.2 0) =
      fun p : ℝ × (ℝ × ℝ) => embL (Bapp (fderiv ℝ (Vj ν p.1 0) p.2) (Bmer (Bmat ν μ χf A p.1) p.2))
        + Bmv (embL (Vj ν p.1 0 p.2)) (Bmat ν μ χf A p.1) := by
    funext p
    simp only [fATerm, xj_zero, hembL, hBapp, hBmer, hBmv]
  have key : GP54 4 ν 0 (fun p : ℝ × (ℝ × ℝ) => fATerm ν μ χf A p.1 p.2 0) := by
    rw [eqG]; exact hG
  exact ⟨key.1, gp54_termBound 4 ν (by norm_num) hν 0 _ key⟩

end UnforcedLeray.Short.PartIIIb.Concrete
