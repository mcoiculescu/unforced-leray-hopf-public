import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_2.Deriv2Bound

/-!
# Slice calculus on the open far set for `inletFn2` (helper for `ProdHom2`)

Source `the November 2 reference manuscript`
lines 2542-2549, 2563-2569, 1206-1222. Local (`ContDiffOn`) versions of the `Jets2` second-order
directional-derivative bounds on the open far set where `p.raw` is smooth and the drift of `E_i`
vanishes (`InletDriftFar`).
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete (Params advT)
open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0412 (realC)

namespace UnforcedLeray.Short.PartIIIb.Concrete.Jets2

open Jets

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem D1_congr_nhds {F G : UnforcedLeray.Space → V} {x : UnforcedLeray.Space}
    (h : F =ᶠ[nhds x] G) (k : Fin 3) : D1 k F x = D1 k G x := by
  unfold D1
  rw [h.fderiv_eq]

theorem D2_congr_nhds {F G : UnforcedLeray.Space → V} {U : Set UnforcedLeray.Space}
    (hU : IsOpen U) (h : ∀ x ∈ U, F x = G x) (j l : Fin 3)
    {y : UnforcedLeray.Space} (hy : y ∈ U) :
    D2 j l F y = D2 j l G y := by
  unfold D2
  refine D1_congr_nhds ?_ j
  filter_upwards [hU.mem_nhds hy] with x hx
  refine D1_congr_nhds ?_ l
  filter_upwards [hU.mem_nhds hx] with z hz using h z hz

theorem contDiffOn_D1 {F : UnforcedLeray.Space → V} {U : Set UnforcedLeray.Space}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (k : Fin 3) :
    ContDiffOn ℝ ∞ (D1 k F) U :=
  (hF.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

theorem contDiffOn_D2 {F : UnforcedLeray.Space → V} {U : Set UnforcedLeray.Space}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (j l : Fin 3) :
    ContDiffOn ℝ ∞ (D2 j l F) U :=
  contDiffOn_D1 hU (contDiffOn_D1 hU hF l) j

theorem D1_add_on {F G : UnforcedLeray.Space → V} {U : Set UnforcedLeray.Space}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (hG : ContDiffOn ℝ ∞ G U)
    (k : Fin 3) {x : UnforcedLeray.Space} (hx : x ∈ U) :
    D1 k (fun z => F z + G z) x = D1 k F x + D1 k G x := by
  have hx' : U ∈ nhds x := hU.mem_nhds hx
  have hh := (((hF.contDiffAt hx').differentiableAt (by simp)).hasFDerivAt.add
    ((hG.contDiffAt hx').differentiableAt (by simp)).hasFDerivAt).fderiv
  change (fderiv ℝ (F + G) x) (ek k) = _
  rw [hh]
  rfl

theorem D1_neg_on {F : UnforcedLeray.Space → V} {U : Set UnforcedLeray.Space}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (k : Fin 3)
    {x : UnforcedLeray.Space} (hx : x ∈ U) :
    D1 k (fun z => -F z) x = -D1 k F x := by
  have hx' : U ∈ nhds x := hU.mem_nhds hx
  have hh := (((hF.contDiffAt hx').differentiableAt (by simp)).hasFDerivAt.neg).fderiv
  change (fderiv ℝ (-F) x) (ek k) = _
  rw [hh]
  rfl

theorem D1_sum_on {F : Fin 3 → UnforcedLeray.Space → V} {U : Set UnforcedLeray.Space}
    (hU : IsOpen U) (hF : ∀ m, ContDiffOn ℝ ∞ (F m) U) (k : Fin 3)
    {x : UnforcedLeray.Space} (hx : x ∈ U) :
    D1 k (fun z => ∑ m : Fin 3, F m z) x = ∑ m : Fin 3, D1 k (F m) x := by
  have hx' : U ∈ nhds x := hU.mem_nhds hx
  have hh : HasFDerivAt (fun z => ∑ m : Fin 3, F m z) (∑ m : Fin 3, fderiv ℝ (F m) x) x :=
    HasFDerivAt.fun_sum fun m _ =>
      (((hF m).contDiffAt hx').differentiableAt (by simp)).hasFDerivAt
  unfold D1
  rw [hh.fderiv, sum_apply]

theorem D2_add_on {F G : UnforcedLeray.Space → V} {U : Set UnforcedLeray.Space}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (hG : ContDiffOn ℝ ∞ G U)
    (j l : Fin 3) {y : UnforcedLeray.Space} (hy : y ∈ U) :
    D2 j l (fun x => F x + G x) y = D2 j l F y + D2 j l G y := by
  unfold D2
  have hev : D1 l (fun x => F x + G x) =ᶠ[nhds y] fun x => D1 l F x + D1 l G x := by
    filter_upwards [hU.mem_nhds hy] with x hx using D1_add_on hU hF hG l hx
  rw [D1_congr_nhds hev j, D1_add_on hU (contDiffOn_D1 hU hF l) (contDiffOn_D1 hU hG l) j hy]

theorem D2_sum_on {F : Fin 3 → UnforcedLeray.Space → V} {U : Set UnforcedLeray.Space}
    (hU : IsOpen U) (hF : ∀ m, ContDiffOn ℝ ∞ (F m) U) (j l : Fin 3)
    {y : UnforcedLeray.Space} (hy : y ∈ U) :
    D2 j l (fun z => ∑ m : Fin 3, F m z) y = ∑ m : Fin 3, D2 j l (F m) y := by
  unfold D2
  have hev : D1 l (fun z => ∑ m : Fin 3, F m z) =ᶠ[nhds y] fun z => ∑ m : Fin 3, D1 l (F m) z := by
    filter_upwards [hU.mem_nhds hy] with x hx using D1_sum_on hU hF l hx
  rw [D1_congr_nhds hev j, D1_sum_on hU (fun m => contDiffOn_D1 hU (hF m) l) j hy]

theorem norm_iteratedFDeriv_D1_le_on {F : UnforcedLeray.Space → V} {U : Set UnforcedLeray.Space}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (k : Fin 3) (n : ℕ)
    {y : UnforcedLeray.Space} (hy : y ∈ U) :
    ‖iteratedFDeriv ℝ n (D1 k F) y‖ ≤ ‖iteratedFDeriv ℝ (n + 1) F y‖ := by
  have hdf : ContDiffAt ℝ ∞ (fderiv ℝ F) y :=
    (hF.fderiv_of_isOpen hU (m := ∞) (by simp)).contDiffAt (hU.mem_nhds hy)
  have hcomp : D1 k F = (ContinuousLinearMap.apply ℝ V (ek k)) ∘ (fderiv ℝ F) := rfl
  have h1 := (ContinuousLinearMap.apply ℝ V (ek k)).norm_iteratedFDeriv_comp_left
    hdf (n := n) (by exact_mod_cast le_top)
  rw [← hcomp] at h1
  have hn : ‖ContinuousLinearMap.apply ℝ V (ek k)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
      simpa [one_mul, norm_single_one k] using f.le_opNorm (ek k)
  have h2 : ‖iteratedFDeriv ℝ n (fderiv ℝ F) y‖ = ‖iteratedFDeriv ℝ (n + 1) F y‖ :=
    norm_iteratedFDeriv_fderiv
  calc ‖iteratedFDeriv ℝ n (D1 k F) y‖
      ≤ ‖ContinuousLinearMap.apply ℝ V (ek k)‖ * ‖iteratedFDeriv ℝ n (fderiv ℝ F) y‖ := h1
    _ ≤ 1 * ‖iteratedFDeriv ℝ n (fderiv ℝ F) y‖ :=
        mul_le_mul_of_nonneg_right hn (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ (n + 1) F y‖ := by rw [one_mul, h2]

theorem norm_D1_le_on {F : UnforcedLeray.Space → V} {U : Set UnforcedLeray.Space}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (k : Fin 3)
    {y : UnforcedLeray.Space} (hy : y ∈ U) :
    ‖D1 k F y‖ ≤ ‖iteratedFDeriv ℝ 1 F y‖ := by
  rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := D1 k F)]
  exact norm_iteratedFDeriv_D1_le_on hU hF k 0 hy

theorem norm_D2_le_on {F : UnforcedLeray.Space → V} {U : Set UnforcedLeray.Space}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (j l : Fin 3)
    {y : UnforcedLeray.Space} (hy : y ∈ U) :
    ‖D2 j l F y‖ ≤ ‖iteratedFDeriv ℝ 2 F y‖ :=
  (norm_D1_le_on hU (contDiffOn_D1 hU hF l) j hy).trans
    (norm_iteratedFDeriv_D1_le_on hU hF l 1 hy)

theorem norm_D2_D1_le_on {F : UnforcedLeray.Space → V} {U : Set UnforcedLeray.Space}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (j l k : Fin 3)
    {y : UnforcedLeray.Space} (hy : y ∈ U) :
    ‖D2 j l (D1 k F) y‖ ≤ ‖iteratedFDeriv ℝ 3 F y‖ :=
  (norm_D2_le_on hU (contDiffOn_D1 hU hF k) j l hy).trans
    (norm_iteratedFDeriv_D1_le_on hU hF k 2 hy)

theorem norm_D2_smul_le_on {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    [NormedSpace 𝕜 W] [IsScalarTower ℝ 𝕜 W] {f : UnforcedLeray.Space → 𝕜}
    {g : UnforcedLeray.Space → W} {U : Set UnforcedLeray.Space} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (j l : Fin 3) {y : UnforcedLeray.Space} (hy : y ∈ U) :
    ‖D2 j l (fun x => f x • g x) y‖ ≤
      ‖f y‖ * ‖D2 j l g y‖ + ‖D1 j f y‖ * ‖D1 l g y‖ +
      (‖D1 l f y‖ * ‖D1 j g y‖ + ‖D2 j l f y‖ * ‖g y‖) := by
  have h1 : ∀ z ∈ U, D1 l (fun x => f x • g x) z =
      f z • D1 l g z + D1 l f z • g z := by
    intro z hz
    have hz' : U ∈ nhds z := hU.mem_nhds hz
    have hh : HasFDerivAt (fun x => f x • g x)
        (f z • fderiv ℝ g z + (fderiv ℝ f z).smulRight (g z)) z :=
      (((hf.contDiffAt hz').differentiableAt (by simp)).hasFDerivAt.smul
        ((hg.contDiffAt hz').differentiableAt (by simp)).hasFDerivAt)
    unfold D1
    rw [hh.fderiv]
    rfl
  have hev : D1 l (fun x => f x • g x) =ᶠ[nhds y] fun z => f z • D1 l g z + D1 l f z • g z := by
    filter_upwards [hU.mem_nhds hy] with z hz using h1 z hz
  have h2 : D2 j l (fun x => f x • g x) y =
      D1 j (fun z => f z • D1 l g z) y + D1 j (fun z => D1 l f z • g z) y := by
    unfold D2
    rw [D1_congr_nhds hev j,
      D1_add_on (F := fun z => f z • D1 l g z) (G := fun z => D1 l f z • g z) hU
        (hf.smul (contDiffOn_D1 hU hg l)) ((contDiffOn_D1 hU hf l).smul hg) j hy]
  rw [h2]
  have hy' : U ∈ nhds y := hU.mem_nhds hy
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact norm_fderiv_smul_le ((hf.contDiffAt hy').differentiableAt (by simp))
      (((contDiffOn_D1 hU hg l).contDiffAt hy').differentiableAt (by simp)) (ek j)
  · exact norm_fderiv_smul_le (((contDiffOn_D1 hU hf l).contDiffAt hy').differentiableAt (by simp))
      ((hg.contDiffAt hy').differentiableAt (by simp)) (ek j)

theorem norm_D1_ofReal_coord_le_on {R : UnforcedLeray.Space → UnforcedLeray.Space}
    {U : Set UnforcedLeray.Space} (hU : IsOpen U) (hR : ContDiffOn ℝ ∞ R U)
    (k l : Fin 3) {y : UnforcedLeray.Space} (hy : y ∈ U) :
    ‖D1 l (fun z => ((R z k : ℝ) : ℂ)) y‖ ≤ ‖D1 l R y‖ := by
  unfold D1
  rw [fderiv_ofReal_coord ((hR.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)) k (ek l),
    Complex.norm_real]
  exact abs_coord_le (𝕜 := ℝ) _ k

theorem norm_D2_ofReal_coord_le_on {R : UnforcedLeray.Space → UnforcedLeray.Space}
    {U : Set UnforcedLeray.Space} (hU : IsOpen U) (hR : ContDiffOn ℝ ∞ R U)
    (j l k : Fin 3) {y : UnforcedLeray.Space} (hy : y ∈ U) :
    ‖D2 j l (fun z => ((R z k : ℝ) : ℂ)) y‖ ≤ ‖D2 j l R y‖ := by
  have hev : D1 l (fun z => ((R z k : ℝ) : ℂ)) =ᶠ[nhds y] fun z => ((D1 l R z k : ℝ) : ℂ) := by
    filter_upwards [hU.mem_nhds hy] with z hz
    exact fderiv_ofReal_coord ((hR.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)) k (ek l)
  unfold D2
  rw [D1_congr_nhds hev j]
  exact norm_D1_ofReal_coord_le_on hU (contDiffOn_D1 hU hR l) k j hy

theorem norm_D1_realC_on {F : UnforcedLeray.Space → UnforcedLeray.Space}
    {U : Set UnforcedLeray.Space} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (l : Fin 3) {y : UnforcedLeray.Space} (hy : y ∈ U) :
    ‖D1 l (fun z => realC (F z)) y‖ = ‖D1 l F y‖ := by
  unfold D1
  rw [fderiv_realC ((hF.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)) (ek l), norm_realC]

theorem norm_D2_realC_on {F : UnforcedLeray.Space → UnforcedLeray.Space}
    {U : Set UnforcedLeray.Space} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (j l : Fin 3) {y : UnforcedLeray.Space} (hy : y ∈ U) :
    ‖D2 j l (fun z => realC (F z)) y‖ = ‖D2 j l F y‖ := by
  have hev : D1 l (fun z => realC (F z)) =ᶠ[nhds y] fun z => realC (D1 l F z) := by
    filter_upwards [hU.mem_nhds hy] with z hz
    exact fderiv_realC ((hF.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)) (ek l)
  unfold D2
  rw [D1_congr_nhds hev j, norm_D1_realC_on hU (contDiffOn_D1 hU hF l) j hy]

/-- Drift-free far-field slice of `inletSrc p i`: `-ν Δe + (r·∇)e + (e·∇)r`. -/
def Sfar (e : UnforcedLeray.Space → CVec3) (r : UnforcedLeray.Space → UnforcedLeray.Space)
    (ν : ℝ) (x : UnforcedLeray.Space) : CVec3 :=
  -(ν • ∑ k : Fin 3, D2 k k e x) +
    ∑ k : Fin 3, ((r x k : ℝ) : ℂ) • D1 k e x +
    ∑ k : Fin 3, e x k • realC (D1 k r x)

theorem norm_D2_Sfar_le {e : UnforcedLeray.Space → CVec3}
    {r : UnforcedLeray.Space → UnforcedLeray.Space} {U : Set UnforcedLeray.Space}
    (hU : IsOpen U) (he : ContDiff ℝ ∞ e) (hr : ContDiffOn ℝ ∞ r U) (ν : ℝ)
    {y : UnforcedLeray.Space} (hy : y ∈ U) (j l : Fin 3) :
    ‖D2 j l (Sfar e r ν) y‖ ≤
      |ν| * (3 * ‖iteratedFDeriv ℝ 4 e y‖) +
      3 * (‖iteratedFDeriv ℝ 0 r y‖ * ‖iteratedFDeriv ℝ 3 e y‖ +
        ‖iteratedFDeriv ℝ 1 r y‖ * ‖iteratedFDeriv ℝ 2 e y‖ +
        (‖iteratedFDeriv ℝ 1 r y‖ * ‖iteratedFDeriv ℝ 2 e y‖ +
          ‖iteratedFDeriv ℝ 2 r y‖ * ‖iteratedFDeriv ℝ 1 e y‖)) +
      3 * (‖iteratedFDeriv ℝ 0 e y‖ * ‖iteratedFDeriv ℝ 3 r y‖ +
        ‖iteratedFDeriv ℝ 1 e y‖ * ‖iteratedFDeriv ℝ 2 r y‖ +
        (‖iteratedFDeriv ℝ 1 e y‖ * ‖iteratedFDeriv ℝ 2 r y‖ +
          ‖iteratedFDeriv ℝ 2 e y‖ * ‖iteratedFDeriv ℝ 1 r y‖)) := by
  have hGk : ∀ k : Fin 3, ContDiff ℝ ∞ (D1 k e) := fun k => contDiff_D1 he k
  have hHk : ∀ k : Fin 3, ContDiff ℝ ∞ (D2 k k e) := fun k => contDiff_D2 he k k
  have hRk : ∀ k : Fin 3, ContDiffOn ℝ ∞ (D1 k r) U := fun k => contDiffOn_D1 hU hr k
  have hrk : ∀ k : Fin 3, ContDiffOn ℝ ∞ (fun z => ((r z k : ℝ) : ℂ)) U := fun k =>
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((contDiff_piLp_apply (p := 2) (i := k)).comp_contDiffOn hr)
  have hek : ∀ k : Fin 3, ContDiff ℝ ∞ (fun z => e z k) := fun k =>
    (contDiff_piLp_apply (p := 2) (i := k)).comp he
  have hrealR : ∀ k : Fin 3, ContDiffOn ℝ ∞ (fun z => realC (D1 k r z)) U := fun k => by
    have : (fun z => realC (D1 k r z)) = fun z => realCL (D1 k r z) := by
      funext z; rw [realCL_apply]
    rw [this]; exact realCL.contDiff.comp_contDiffOn (hRk k)
  have hc3 : ContDiff ℝ ∞ (fun x => ∑ k : Fin 3, D2 k k e x) :=
    ContDiff.sum fun k _ => hHk k
  have hc3neg : ContDiff ℝ ∞ (fun x => -(ν • ∑ k : Fin 3, D2 k k e x)) :=
    (hc3.const_smul ν).neg
  have hc5 : ContDiffOn ℝ ∞ (fun x => ∑ k : Fin 3, ((r x k : ℝ) : ℂ) • D1 k e x) U :=
    ContDiffOn.sum fun k _ => (hrk k).smul (hGk k).contDiffOn
  have hc6 : ContDiffOn ℝ ∞ (fun x => ∑ k : Fin 3, e x k • realC (D1 k r x)) U :=
    ContDiffOn.sum fun k _ => (hek k).contDiffOn.smul (hrealR k)
  have hD2_neg : D2 j l (fun x => -(ν • ∑ k : Fin 3, D2 k k e x)) y =
      -(ν • ∑ k : Fin 3, D2 j l (D2 k k e) y) := by
    change D1 j (D1 l (fun x => -(ν • ∑ k : Fin 3, D2 k k e x))) y = _
    rw [D1_neg (hc3.const_smul ν) l, D1_neg (contDiff_D1 (hc3.const_smul ν) l) j]
    change -(D2 j l (fun x => ν • ∑ k : Fin 3, D2 k k e x) y) = _
    rw [D2_const_smul hc3 ν j l y, D2_sum (F := fun k => D2 k k e) hHk j l y]
  have hD2_S : D2 j l (Sfar e r ν) y =
      -(ν • ∑ k : Fin 3, D2 j l (D2 k k e) y) +
      ∑ k : Fin 3, D2 j l (fun x => ((r x k : ℝ) : ℂ) • D1 k e x) y +
      ∑ k : Fin 3, D2 j l (fun x => e x k • realC (D1 k r x)) y := by
    change D2 j l (fun x => (-(ν • ∑ k : Fin 3, D2 k k e x) +
        ∑ k : Fin 3, ((r x k : ℝ) : ℂ) • D1 k e x) +
        ∑ k : Fin 3, e x k • realC (D1 k r x)) y = _
    rw [D2_add_on hU (hc3neg.contDiffOn.add hc5) hc6 j l hy,
      D2_add_on hU hc3neg.contDiffOn hc5 j l hy, hD2_neg,
      D2_sum_on (F := fun k x => ((r x k : ℝ) : ℂ) • D1 k e x) hU
        (fun k => (hrk k).smul (hGk k).contDiffOn) j l hy,
      D2_sum_on (F := fun k x => e x k • realC (D1 k r x)) hU
        (fun k => (hek k).contDiffOn.smul (hrealR k)) j l hy]
  rw [hD2_S]
  set a0 := ‖iteratedFDeriv ℝ 0 e y‖ with ha0
  set a1 := ‖iteratedFDeriv ℝ 1 e y‖
  set a2 := ‖iteratedFDeriv ℝ 2 e y‖
  set a3 := ‖iteratedFDeriv ℝ 3 e y‖
  set a4 := ‖iteratedFDeriv ℝ 4 e y‖
  set b0 := ‖iteratedFDeriv ℝ 0 r y‖ with hb0
  set b1 := ‖iteratedFDeriv ℝ 1 r y‖
  set b2 := ‖iteratedFDeriv ℝ 2 r y‖
  set b3 := ‖iteratedFDeriv ℝ 3 r y‖
  have e0 : ‖e y‖ = a0 := by rw [ha0, norm_iteratedFDeriv_zero]
  have r0 : ‖r y‖ = b0 := by rw [hb0, norm_iteratedFDeriv_zero]
  have bE1 : ∀ k : Fin 3, ‖D1 k e y‖ ≤ a1 := fun k => norm_D1_le he k y
  have bE2 : ∀ m k : Fin 3, ‖D2 m k e y‖ ≤ a2 := fun m k => norm_D2_le he m k y
  have bE3 : ∀ k : Fin 3, ‖D2 j l (D1 k e) y‖ ≤ a3 := fun k => norm_D2_D1_le he j l k y
  have bE4 : ∀ k : Fin 3, ‖D2 j l (D2 k k e) y‖ ≤ a4 := fun k => norm_D2_D2_le he j l k k y
  have bR1 : ∀ k : Fin 3, ‖D1 k r y‖ ≤ b1 := fun k => norm_D1_le_on hU hr k hy
  have bR2 : ∀ m k : Fin 3, ‖D2 m k r y‖ ≤ b2 := fun m k => norm_D2_le_on hU hr m k hy
  have bR3 : ∀ k : Fin 3, ‖D2 j l (D1 k r) y‖ ≤ b3 := fun k => norm_D2_D1_le_on hU hr j l k hy
  have P5 : ∀ k : Fin 3, ‖D2 j l (fun x => ((r x k : ℝ) : ℂ) • D1 k e x) y‖ ≤
      b0 * a3 + b1 * a2 + (b1 * a2 + b2 * a1) := fun k => by
    refine (norm_D2_smul_le_on (𝕜 := ℂ) hU (hrk k) (hGk k).contDiffOn j l hy).trans ?_
    have c1 : ‖((r y k : ℝ) : ℂ)‖ ≤ b0 := by
      rw [← r0, Complex.norm_real]; exact abs_coord_le (𝕜 := ℝ) (r y) k
    have c2 : ‖D1 j (fun z => ((r z k : ℝ) : ℂ)) y‖ ≤ b1 :=
      (norm_D1_ofReal_coord_le_on hU hr k j hy).trans (bR1 j)
    have c3 : ‖D1 l (fun z => ((r z k : ℝ) : ℂ)) y‖ ≤ b1 :=
      (norm_D1_ofReal_coord_le_on hU hr k l hy).trans (bR1 l)
    have c4 : ‖D2 j l (fun z => ((r z k : ℝ) : ℂ)) y‖ ≤ b2 :=
      (norm_D2_ofReal_coord_le_on hU hr j l k hy).trans (bR2 j l)
    have g0 := bE1 k
    have g1l : ‖D1 l (D1 k e) y‖ ≤ a2 := bE2 l k
    have g1j : ‖D1 j (D1 k e) y‖ ≤ a2 := bE2 j k
    have g2 := bE3 k
    gcongr
  have P6 : ∀ k : Fin 3, ‖D2 j l (fun x => e x k • realC (D1 k r x)) y‖ ≤
      a0 * b3 + a1 * b2 + (a1 * b2 + a2 * b1) := fun k => by
    refine (norm_D2_smul_le_on (𝕜 := ℂ) hU (hek k).contDiffOn (hrealR k) j l hy).trans ?_
    have c1 : ‖e y k‖ ≤ a0 := by rw [← e0]; exact abs_coord_le (𝕜 := ℂ) (e y) k
    have c2 : ‖D1 j (fun z => e z k) y‖ ≤ a1 :=
      (norm_D1_coord_le he k j y).trans (bE1 j)
    have c3 : ‖D1 l (fun z => e z k) y‖ ≤ a1 :=
      (norm_D1_coord_le he k l y).trans (bE1 l)
    have c4 : ‖D2 j l (fun z => e z k) y‖ ≤ a2 :=
      (norm_D2_coord_le he j l k y).trans (bE2 j l)
    have g0 : ‖realC (D1 k r y)‖ ≤ b1 := by rw [norm_realC]; exact bR1 k
    have g1l : ‖D1 l (fun z => realC (D1 k r z)) y‖ ≤ b2 := by
      rw [norm_D1_realC_on hU (hRk k) l hy]; exact bR2 l k
    have g1j : ‖D1 j (fun z => realC (D1 k r z)) y‖ ≤ b2 := by
      rw [norm_D1_realC_on hU (hRk k) j hy]; exact bR2 j k
    have g2 : ‖D2 j l (fun z => realC (D1 k r z)) y‖ ≤ b3 := by
      rw [norm_D2_realC_on hU (hRk k) j l hy]; exact bR3 k
    gcongr
  have n3 : ‖-(ν • ∑ k : Fin 3, D2 j l (D2 k k e) y)‖ ≤ |ν| * (3 * a4) := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum3_le a4 _ bE4)) (abs_nonneg ν)
  have n5 : ‖∑ k : Fin 3, D2 j l (fun x => ((r x k : ℝ) : ℂ) • D1 k e x) y‖ ≤
      3 * (b0 * a3 + b1 * a2 + (b1 * a2 + b2 * a1)) := (norm_sum_le _ _).trans (sum3_le _ _ P5)
  have n6 : ‖∑ k : Fin 3, D2 j l (fun x => e x k • realC (D1 k r x)) y‖ ≤
      3 * (a0 * b3 + a1 * b2 + (a1 * b2 + a2 * b1)) := (norm_sum_le _ _).trans (sum3_le _ _ P6)
  have htr1 := norm_add_le (-(ν • ∑ k : Fin 3, D2 j l (D2 k k e) y) +
      ∑ k : Fin 3, D2 j l (fun x => ((r x k : ℝ) : ℂ) • D1 k e x) y)
    (∑ k : Fin 3, D2 j l (fun x => e x k • realC (D1 k r x)) y)
  have htr2 := norm_add_le (-(ν • ∑ k : Fin 3, D2 j l (D2 k k e) y))
    (∑ k : Fin 3, D2 j l (fun x => ((r x k : ℝ) : ℂ) • D1 k e x) y)
  linarith

end Jets2

open Jets Jets2 in
theorem dy_slice_at {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : ℝ × UnforcedLeray.Space → V} {τ : ℝ} {z : UnforcedLeray.Space}
    (hF : DifferentiableAt ℝ F (τ, z)) (l : Fin 3) :
    dy l F (τ, z) = D1 l (fun w => F (τ, w)) z := by
  have hmap : HasFDerivAt (fun w : UnforcedLeray.Space => (τ, w))
      ((0 : UnforcedLeray.Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ UnforcedLeray.Space)) z :=
    (hasFDerivAt_const τ z).prodMk (hasFDerivAt_id z)
  have hcomp := hF.hasFDerivAt.comp z hmap
  have h := congrArg (fun A : UnforcedLeray.Space →L[ℝ] V => A (ek l)) hcomp.fderiv
  simpa only [D1, dy, ek, UnforcedLeray.coordinateVector, Function.comp_def,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    zero_apply] using h.symm

theorem fderiv_slice_at {R : ℝ × UnforcedLeray.Space → UnforcedLeray.Space}
    {τ : ℝ} {y : UnforcedLeray.Space} (hR : DifferentiableAt ℝ R (τ, y))
    (v : UnforcedLeray.Space) :
    fderiv ℝ (fun x : UnforcedLeray.Space => R (τ, x)) y v = fderiv ℝ R (τ, y) (0, v) := by
  have hmap : HasFDerivAt (fun x : UnforcedLeray.Space => (τ, x))
      ((0 : UnforcedLeray.Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ UnforcedLeray.Space)) y :=
    (hasFDerivAt_const τ y).prodMk (hasFDerivAt_id y)
  have hcomp := hR.hasFDerivAt.comp y hmap
  have h := congrArg (fun A : UnforcedLeray.Space →L[ℝ] UnforcedLeray.Space => A v) hcomp.fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, zero_apply] using h

theorem inletSrc_contDiffOn {p : Params} {i : Fin 2} {U : Set (ℝ × UnforcedLeray.Space)}
    (hU : IsOpen U) (hE : ContDiff ℝ ∞ (p.Efun i))
    (hR : ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => p.raw x.1 x.2) U) :
    ContDiffOn ℝ ∞ (inletSrc p i) U := by
  have hL : ContDiff ℝ ∞ (UnforcedLeray.B0411.L0 p.ν (p.Efun i)) := by
    unfold UnforcedLeray.B0411.L0 UnforcedLeray.B0411.T0
    exact (((contDiff_dτ hE).sub ((contDiff_radialT hE).const_smul _)).sub
      ((contDiff_lapT hE).const_smul _)).sub (hE.const_smul _)
  have hUc : ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Space =>
      UnforcedLeray.B0412.realC (p.raw x.1 x.2)) U := contDiff_realC_meas.comp_contDiffOn hR
  have hA : ContDiffOn ℝ ∞
      (advT (fun x => UnforcedLeray.B0412.realC (p.raw x.1 x.2)) (p.Efun i)) U := by
    unfold advT
    exact ContDiffOn.sum fun k _ =>
      ((contDiff_piLp_apply (p := 2) (i := k)).comp_contDiffOn hUc).smul
        (UnforcedLeray.PhaseSpace.contDiff_dy hE k).contDiffOn
  have hG : ContDiffOn ℝ ∞ (gradAlong p.raw (p.Efun i)) U := by
    unfold gradAlong
    apply (contDiffOn_piLp 2).2
    intro l
    show ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => ∑ k : Fin 3, p.Efun i x k *
      ((fderiv ℝ (p.raw x.1) x.2 (EuclideanSpace.single k 1) l : ℝ) : ℂ)) U
    refine ContDiffOn.sum fun k _ => ?_
    have h1 : ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => p.Efun i x k) U :=
      ((contDiff_piLp_apply (p := 2) (i := k)).comp hE).contDiffOn
    have h3 : ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Space =>
        fderiv ℝ (fun w : ℝ × UnforcedLeray.Space => p.raw w.1 w.2) x
          (0, EuclideanSpace.single k 1)) U :=
      (hR.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
    have h4 : ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Space =>
        (fderiv ℝ (fun w : ℝ × UnforcedLeray.Space => p.raw w.1 w.2) x
          (0, EuclideanSpace.single k 1)) l) U :=
      (contDiff_piLp_apply (p := 2) (i := l)).comp_contDiffOn h3
    have h2 : ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Space =>
        fderiv ℝ (p.raw x.1) x.2 (EuclideanSpace.single k 1) l) U := by
      refine h4.congr fun x hx => ?_
      have hd : DifferentiableAt ℝ (fun w : ℝ × UnforcedLeray.Space => p.raw w.1 w.2) x :=
        (hR.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
      exact congrArg (fun v => v l) (fderiv_slice_at hd (EuclideanSpace.single k 1))
    exact h1.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn h2)
  exact (hL.contDiffOn.add hA).add hG

open Jets Jets2 in
theorem inletFn2_far_slice_eq (p : Params) (i : Fin 2) (j l : Fin 3)
    {U : Set (ℝ × UnforcedLeray.Space)} (hU : IsOpen U)
    (hE : ContDiff ℝ ∞ (p.Efun i))
    (hR : ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => p.raw x.1 x.2) U)
    (hdrift : ∀ x ∈ U, dτ (p.Efun i) x - (1 / 2 : ℝ) • radialT (p.Efun i) x -
      (1 / 2 : ℝ) • p.Efun i x = 0)
    (τ : ℝ) (y : UnforcedLeray.Space) (hy : (τ, y) ∈ U) :
    inletFn2 p i j l (τ, y) =
      D2 j l (Sfar (fun z => p.Efun i (τ, z)) (p.raw τ) p.ν) y := by
  set Uy : Set UnforcedLeray.Space := {x | (τ, x) ∈ U}
  have hUy : IsOpen Uy := hU.preimage (continuous_const.prodMk continuous_id)
  have hyU : y ∈ Uy := hy
  have hS : ContDiffOn ℝ ∞ (inletSrc p i) U := inletSrc_contDiffOn hU hE hR
  have hF1 : ContDiffOn ℝ ∞ (inletFn p i l) U := by
    unfold inletFn dy
    exact ((hS.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const).neg
  have hS_eq : ∀ x ∈ Uy, inletSrc p i (τ, x) =
      Sfar (fun z => p.Efun i (τ, z)) (p.raw τ) p.ν x := by
    intro x hx
    rw [inletSrc_slice p i hE τ x]
    unfold Sfun Sfar
    have hrad : radialT (p.Efun i) (τ, x) =
        ∑ k : Fin 3, (x k) • D1 k (fun z => p.Efun i (τ, z)) x := by
      unfold radialT D1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [dy_slice _ (hE.differentiable (by simp)) k τ x]
    have hd0 := hdrift (τ, x) hx
    rw [hrad] at hd0
    have hsub : dτ (p.Efun i) (τ, x) -
        (1 / 2 : ℝ) • ∑ k : Fin 3, (x k) • D1 k (fun z => p.Efun i (τ, z)) x -
        p.ν • ∑ k : Fin 3, D2 k k (fun z => p.Efun i (τ, z)) x -
        (1 / 2 : ℝ) • p.Efun i (τ, x) =
        (dτ (p.Efun i) (τ, x) -
          (1 / 2 : ℝ) • ∑ k : Fin 3, (x k) • D1 k (fun z => p.Efun i (τ, z)) x -
          (1 / 2 : ℝ) • p.Efun i (τ, x)) -
        p.ν • ∑ k : Fin 3, D2 k k (fun z => p.Efun i (τ, z)) x := by abel
    change (dτ (p.Efun i) (τ, x) -
        (1 / 2 : ℝ) • ∑ k : Fin 3, (x k) • D1 k (fun z => p.Efun i (τ, z)) x -
        p.ν • ∑ k : Fin 3, D2 k k (fun z => p.Efun i (τ, z)) x -
        (1 / 2 : ℝ) • p.Efun i (τ, x)) + _ + _ = _
    rw [hsub, hd0, zero_sub]
    rfl
  have hF1_eq : ∀ x ∈ Uy, inletFn p i l (τ, x) =
      -D1 l (Sfar (fun z => p.Efun i (τ, z)) (p.raw τ) p.ν) x := by
    intro x hx
    unfold inletFn
    simp only [Pi.neg_apply, neg_inj]
    have hd : DifferentiableAt ℝ (inletSrc p i) (τ, x) :=
      (hS.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    rw [dy_slice_at hd l]
    refine D1_congr_nhds ?_ l
    filter_upwards [hUy.mem_nhds hx] with z hz using hS_eq z hz
  have hdF1 : DifferentiableAt ℝ (inletFn p i l) (τ, y) :=
    (hF1.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
  unfold inletFn2
  simp only [Pi.neg_apply]
  rw [dy_slice_at hdF1 j]
  have hev : (fun x => inletFn p i l (τ, x)) =ᶠ[nhds y]
      fun x => -D1 l (Sfar (fun z => p.Efun i (τ, z)) (p.raw τ) p.ν) x := by
    filter_upwards [hUy.mem_nhds hyU] with x hx using hF1_eq x hx
  have hSfar_cd : ContDiffOn ℝ ∞ (Sfar (fun z => p.Efun i (τ, z)) (p.raw τ) p.ν) Uy := by
    have hsl : ContDiffOn ℝ ∞ (fun x : UnforcedLeray.Space => ((τ, x) : ℝ × UnforcedLeray.Space)) Uy :=
      (contDiff_const.prodMk contDiff_id).contDiffOn
    exact (hS.comp hsl (fun x hx => hx)).congr (fun x hx => (hS_eq x hx).symm)
  rw [D1_congr_nhds hev j, D1_neg_on hUy (contDiffOn_D1 hUy hSfar_cd l) j hyU, neg_neg]
  rfl

end UnforcedLeray.Short.PartIIIb.Concrete
