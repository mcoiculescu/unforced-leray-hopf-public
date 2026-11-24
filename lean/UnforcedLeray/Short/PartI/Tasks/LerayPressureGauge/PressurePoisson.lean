import UnforcedLeray.Short.PartI.Sub.T02_2
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Part I, task `PartI:T02/2`, leaf `PressurePoisson`: the pressure Poisson equation

Source of record: `the November 2 reference manuscript`, line 447 (the decaying
pressure gauge). For a classical solution `(v, p)` on `[0,T]`, `Δp = -tr((∇v)²)` on every slice.

Proof. On `(0,T) × ℝ²` the momentum equation holds and `v`, `p` are `C^∞`. With `E_0`, `E_1` the
components of the momentum residual, `∂_q E_0 + ∂_η E_1 = 0` pointwise (`E ≡ 0`). Expanding with
the symmetry of mixed derivatives (space–time and spatial) and `div v = 0` gives
`Δp + tr((∇v)²) = 0` on `(0,T)`. The endpoints `s = 0, T` follow by continuity of both sides on
`[0,T] × ℝ²`, computed with `fderivWithin` on the closed region.

The directional-derivative framework follows `Units/B0238/SpaceTime.lean`, with the open set
`(0,T) × ℝ²` in place of `{s > 0}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI.PPoisson

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- Space–time points `(s, z)`. -/
abbrev SpT := ℝ × Plane

/-- The directional derivative `∂_w H(x) = DH(x) w`. -/
def dirP (w : SpT) (H : SpT → ℝ) (x : SpT) : ℝ := fderiv ℝ H x w

/-- The age direction. -/
def eT : SpT := (1, 0)

/-- The `q` direction. -/
def eQ : SpT := (0, (1, 0))

/-- The `η` direction. -/
def eE : SpT := (0, (0, 1))

/-- `H` is `C^∞` on the set `U`. -/
def SmU (U : Set SpT) (H : SpT → ℝ) : Prop := ContDiffOn ℝ ∞ H U

/-- Component `k` of a velocity field, as a space–time function. -/
def Fc (v : ℝ → Plane → Vec) (k : Fin 2) : SpT → ℝ := fun x => v x.1 x.2 k

/-- A scalar field, as a space–time function. -/
def Fs (p : ℝ → Plane → ℝ) : SpT → ℝ := fun x => p x.1 x.2

theorem isOpen_strip (T : ℝ) : IsOpen (Ioo 0 T ×ˢ (univ : Set Plane)) :=
  isOpen_Ioo.prod isOpen_univ

theorem smU_Fc {U : Set SpT} {v : ℝ → Plane → Vec}
    (hv : ContDiffOn ℝ ∞ (fun x : SpT => v x.1 x.2) U) (k : Fin 2) : SmU U (Fc v k) :=
  (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp_contDiffOn hv

theorem smU_Fs {U : Set SpT} {p : ℝ → Plane → ℝ} (hp : SmU U (fun x : SpT => p x.1 x.2)) :
    SmU U (Fs p) := hp

section Framework

variable {U : Set SpT}

theorem smU_contDiffAt {H : SpT → ℝ} (hU : IsOpen U) (h : SmU U H) {x : SpT} (hx : x ∈ U) :
    ContDiffAt ℝ ∞ H x :=
  ContDiffOn.contDiffAt h (hU.mem_nhds hx)

theorem smU_differentiableAt {H : SpT → ℝ} (hU : IsOpen U) (h : SmU U H) {x : SpT}
    (hx : x ∈ U) : DifferentiableAt ℝ H x :=
  (smU_contDiffAt hU h hx).differentiableAt (by simp)

theorem smU_fderiv {H : SpT → ℝ} (hU : IsOpen U) (h : SmU U H) :
    ContDiffOn ℝ ∞ (fderiv ℝ H) U :=
  ContDiffOn.fderiv_of_isOpen h hU (by simp)

theorem smU_dir {H : SpT → ℝ} (hU : IsOpen U) (h : SmU U H) (w : SpT) :
    SmU U (dirP w H) :=
  (smU_fderiv hU h).clm_apply contDiffOn_const

theorem dirP_dirP_eq {H : SpT → ℝ} (hU : IsOpen U) (h : SmU U H) {x : SpT} (hx : x ∈ U)
    (a b : SpT) : dirP a (dirP b H) x = fderiv ℝ (fderiv ℝ H) x a b := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ H) x :=
    ((smU_fderiv hU h).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have h2 : HasFDerivAt (dirP b H)
      ((ContinuousLinearMap.apply ℝ ℝ b).comp (fderiv ℝ (fderiv ℝ H) x)) x :=
    (ContinuousLinearMap.apply ℝ ℝ b).hasFDerivAt.comp x hdf.hasFDerivAt
  change fderiv ℝ (dirP b H) x a = _
  rw [h2.fderiv]
  rfl

theorem dirP_symm {H : SpT → ℝ} (hU : IsOpen U) (h : SmU U H) {x : SpT} (hx : x ∈ U)
    (a b : SpT) : dirP a (dirP b H) x = dirP b (dirP a H) x := by
  rw [dirP_dirP_eq hU h hx, dirP_dirP_eq hU h hx]
  exact (smU_contDiffAt hU h hx).isSymmSndFDerivAt (by simp) a b

theorem dirP_congr {H₁ H₂ : SpT → ℝ} (hU : IsOpen U) (h : ∀ y ∈ U, H₁ y = H₂ y) {x : SpT}
    (hx : x ∈ U) (w : SpT) : dirP w H₁ x = dirP w H₂ x := by
  simp only [dirP]
  rw [Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (hU.mem_nhds hx) h)]

theorem dirP_eq_zero {H : SpT → ℝ} (hU : IsOpen U) (h : ∀ y ∈ U, H y = 0) {x : SpT}
    (hx : x ∈ U) (w : SpT) : dirP w H x = 0 := by
  rw [dirP_congr (H₂ := fun _ => 0) hU h hx]
  simp [dirP]

theorem dirP_add {H₁ H₂ : SpT → ℝ} (hU : IsOpen U) (h₁ : SmU U H₁) (h₂ : SmU U H₂) {x : SpT}
    (hx : x ∈ U) (w : SpT) :
    dirP w (fun y => H₁ y + H₂ y) x = dirP w H₁ x + dirP w H₂ x := by
  have H : HasFDerivAt (fun y => H₁ y + H₂ y) (fderiv ℝ H₁ x + fderiv ℝ H₂ x) x :=
    (smU_differentiableAt hU h₁ hx).hasFDerivAt.add (smU_differentiableAt hU h₂ hx).hasFDerivAt
  simp only [dirP]
  rw [H.fderiv]
  rfl

theorem dirP_zero2 {H : SpT → ℝ} (hU : IsOpen U) (h : ∀ y ∈ U, H y = 0) {x : SpT} (hx : x ∈ U)
    (w₁ w₂ : SpT) : dirP w₁ (dirP w₂ H) x = 0 :=
  dirP_eq_zero hU (fun y hy => dirP_eq_zero hU h hy w₂) hx w₁

theorem dirP_linear2 {A B : SpT → ℝ} (hU : IsOpen U) (hA : SmU U A) (hB : SmU U B) (w₁ w₂ : SpT)
    {x : SpT} (hx : x ∈ U) :
    dirP w₁ (dirP w₂ (fun y => A y + B y)) x = dirP w₁ (dirP w₂ A) x + dirP w₁ (dirP w₂ B) x := by
  have h1 : ∀ y ∈ U, dirP w₂ (fun z => A z + B z) y = dirP w₂ A y + dirP w₂ B y :=
    fun y hy => dirP_add hU hA hB hy w₂
  rw [dirP_congr hU h1 hx w₁]
  exact dirP_add hU (smU_dir hU hA w₂) (smU_dir hU hB w₂) hx w₁

theorem dirP_mom {a b c d e f g k : SpT → ℝ} (hU : IsOpen U)
    (ha : SmU U a) (hb : SmU U b) (hc : SmU U c) (hd : SmU U d) (he : SmU U e)
    (hf : SmU U f) (hg : SmU U g) (hk : SmU U k) (ν : ℝ) {x : SpT} (hx : x ∈ U) (w : SpT) :
    dirP w (fun y => a y + (b y * c y + d y * e y) - ν * (f y + g y) + k y) x =
      dirP w a x + (dirP w b x * c x + b x * dirP w c x + (dirP w d x * e x + d x * dirP w e x)) -
        ν * (dirP w f x + dirP w g x) + dirP w k x := by
  have H : HasFDerivAt (fun y => a y + (b y * c y + d y * e y) - ν * (f y + g y) + k y)
      (fderiv ℝ a x + ((b x • fderiv ℝ c x + c x • fderiv ℝ b x) +
        (d x • fderiv ℝ e x + e x • fderiv ℝ d x)) - ν • (fderiv ℝ f x + fderiv ℝ g x) +
        fderiv ℝ k x) x :=
    (((smU_differentiableAt hU ha hx).hasFDerivAt.add
      (((smU_differentiableAt hU hb hx).hasFDerivAt.mul
        (smU_differentiableAt hU hc hx).hasFDerivAt).add
        ((smU_differentiableAt hU hd hx).hasFDerivAt.mul
          (smU_differentiableAt hU he hx).hasFDerivAt))).sub
      (((smU_differentiableAt hU hf hx).hasFDerivAt.add
        (smU_differentiableAt hU hg hx).hasFDerivAt).const_mul ν)).add
      (smU_differentiableAt hU hk hx).hasFDerivAt
  simp only [dirP]
  rw [H.fderiv]
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
  ring

/-! ### Slices -/

theorem sliceQ {H : SpT → ℝ} {t : ℝ} {w : Plane} (hd : DifferentiableAt ℝ H (t, w)) :
    Cyl.partialQ (fun z' => H (t, z')) w = dirP eQ H (t, w) := by
  have h1 : HasDerivAt (fun q : ℝ => ((t, (q, w.2)) : SpT)) eQ w.1 :=
    (hasDerivAt_const w.1 t).prodMk ((hasDerivAt_id w.1).prodMk (hasDerivAt_const w.1 w.2))
  have h2 : HasFDerivAt H (fderiv ℝ H (t, w)) (t, (w.1, w.2)) := hd.hasFDerivAt
  exact (h2.comp_hasDerivAt w.1 h1).deriv

theorem sliceE {H : SpT → ℝ} {t : ℝ} {w : Plane} (hd : DifferentiableAt ℝ H (t, w)) :
    Cyl.partialEta (fun z' => H (t, z')) w = dirP eE H (t, w) := by
  have h1 : HasDerivAt (fun q : ℝ => ((t, (w.1, q)) : SpT)) eE w.2 :=
    (hasDerivAt_const w.2 t).prodMk ((hasDerivAt_const w.2 w.1).prodMk (hasDerivAt_id w.2))
  have h2 : HasFDerivAt H (fderiv ℝ H (t, w)) (t, (w.1, w.2)) := hd.hasFDerivAt
  exact (h2.comp_hasDerivAt w.2 h1).deriv

theorem pQ_gen {H : SpT → ℝ} {t : ℝ} {f : Plane → ℝ} (hf : f = fun w' => H (t, w'))
    (hd : ∀ w' : Plane, DifferentiableAt ℝ H (t, w')) (w : Plane) :
    Cyl.partialQ f w = dirP eQ H (t, w) := by
  subst hf
  exact sliceQ (hd w)

theorem pE_gen {H : SpT → ℝ} {t : ℝ} {f : Plane → ℝ} (hf : f = fun w' => H (t, w'))
    (hd : ∀ w' : Plane, DifferentiableAt ℝ H (t, w')) (w : Plane) :
    Cyl.partialEta f w = dirP eE H (t, w) := by
  subst hf
  exact sliceE (hd w)

theorem pQQ_gen {H : SpT → ℝ} {t : ℝ} {f : Plane → ℝ} (hf : f = fun w' => H (t, w'))
    (hd : ∀ w' : Plane, DifferentiableAt ℝ H (t, w'))
    (hd2 : ∀ w' : Plane, DifferentiableAt ℝ (dirP eQ H) (t, w')) (w : Plane) :
    Cyl.partialQ (Cyl.partialQ f) w = dirP eQ (dirP eQ H) (t, w) := by
  have e : Cyl.partialQ f = fun w' => dirP eQ H (t, w') :=
    funext fun w' => pQ_gen hf hd w'
  rw [e]
  exact sliceQ (hd2 w)

theorem pEE_gen {H : SpT → ℝ} {t : ℝ} {f : Plane → ℝ} (hf : f = fun w' => H (t, w'))
    (hd : ∀ w' : Plane, DifferentiableAt ℝ H (t, w'))
    (hd2 : ∀ w' : Plane, DifferentiableAt ℝ (dirP eE H) (t, w')) (w : Plane) :
    Cyl.partialEta (Cyl.partialEta f) w = dirP eE (dirP eE H) (t, w) := by
  have e : Cyl.partialEta f = fun w' => dirP eE H (t, w') :=
    funext fun w' => pE_gen hf hd w'
  rw [e]
  exact sliceE (hd2 w)

/-! ### Core algebra on an open set -/

theorem core_interior {U : Set SpT} (hU : IsOpen U) {ν : ℝ} {F0 F1 P : SpT → ℝ}
    (h0 : SmU U F0) (h1 : SmU U F1) (hP : SmU U P)
    (hD : ∀ y ∈ U, dirP eQ F0 y + dirP eE F1 y = 0)
    (M0 : ∀ y ∈ U, dirP eT F0 y + (F0 y * dirP eQ F0 y + F1 y * dirP eE F0 y) -
      ν * (dirP eQ (dirP eQ F0) y + dirP eE (dirP eE F0) y) + dirP eQ P y = 0)
    (M1 : ∀ y ∈ U, dirP eT F1 y + (F0 y * dirP eQ F1 y + F1 y * dirP eE F1 y) -
      ν * (dirP eQ (dirP eQ F1) y + dirP eE (dirP eE F1) y) + dirP eE P y = 0)
    {x : SpT} (hx : x ∈ U) :
    dirP eQ (dirP eQ P) x + dirP eE (dirP eE P) x =
      -(dirP eQ F0 x ^ 2 + 2 * dirP eE F0 x * dirP eQ F1 x + dirP eE F1 x ^ 2) := by
  have hTF0 : SmU U (dirP eT F0) := smU_dir hU h0 eT
  have hTF1 : SmU U (dirP eT F1) := smU_dir hU h1 eT
  have hQF0 : SmU U (dirP eQ F0) := smU_dir hU h0 eQ
  have hEF0 : SmU U (dirP eE F0) := smU_dir hU h0 eE
  have hQF1 : SmU U (dirP eQ F1) := smU_dir hU h1 eQ
  have hEF1 : SmU U (dirP eE F1) := smU_dir hU h1 eE
  have hQP : SmU U (dirP eQ P) := smU_dir hU hP eQ
  have hEP : SmU U (dirP eE P) := smU_dir hU hP eE
  have hQQF0 : SmU U (dirP eQ (dirP eQ F0)) := smU_dir hU hQF0 eQ
  have hEEF0 : SmU U (dirP eE (dirP eE F0)) := smU_dir hU hEF0 eE
  have hQQF1 : SmU U (dirP eQ (dirP eQ F1)) := smU_dir hU hQF1 eQ
  have hEEF1 : SmU U (dirP eE (dirP eE F1)) := smU_dir hU hEF1 eE
  have S_QT0 : dirP eQ (dirP eT F0) x = dirP eT (dirP eQ F0) x := dirP_symm hU h0 hx eQ eT
  have S_ET1 : dirP eE (dirP eT F1) x = dirP eT (dirP eE F1) x := dirP_symm hU h1 hx eE eT
  have S_QE1 : dirP eE (dirP eQ F1) x = dirP eQ (dirP eE F1) x := dirP_symm hU h1 hx eE eQ
  have S_QE0 : dirP eQ (dirP eE F0) x = dirP eE (dirP eQ F0) x := dirP_symm hU h0 hx eQ eE
  have S_T1 : dirP eE (dirP eQ (dirP eQ F1)) x = dirP eQ (dirP eQ (dirP eE F1)) x := by
    rw [dirP_symm hU hQF1 hx eE eQ]
    exact dirP_congr hU (H₁ := dirP eE (dirP eQ F1)) (H₂ := dirP eQ (dirP eE F1))
      (fun y hy => dirP_symm hU h1 hy eE eQ) hx eQ
  have S_T2 : dirP eQ (dirP eE (dirP eE F0)) x = dirP eE (dirP eE (dirP eQ F0)) x := by
    rw [dirP_symm hU hEF0 hx eQ eE]
    exact dirP_congr hU (H₁ := dirP eQ (dirP eE F0)) (H₂ := dirP eE (dirP eQ F0))
      (fun y hy => dirP_symm hU h0 hy eQ eE) hx eE
  have E_T : dirP eT (dirP eQ F0) x + dirP eT (dirP eE F1) x = 0 := by
    rw [← dirP_add hU hQF0 hEF1 hx eT]
    exact dirP_eq_zero hU hD hx eT
  have E_Q : dirP eQ (dirP eQ F0) x + dirP eQ (dirP eE F1) x = 0 := by
    rw [← dirP_add hU hQF0 hEF1 hx eQ]
    exact dirP_eq_zero hU hD hx eQ
  have E_E : dirP eE (dirP eQ F0) x + dirP eE (dirP eE F1) x = 0 := by
    rw [← dirP_add hU hQF0 hEF1 hx eE]
    exact dirP_eq_zero hU hD hx eE
  have E_QQ : dirP eQ (dirP eQ (dirP eQ F0)) x + dirP eQ (dirP eQ (dirP eE F1)) x = 0 := by
    rw [← dirP_linear2 hU hQF0 hEF1 eQ eQ hx]
    exact dirP_zero2 hU hD hx eQ eQ
  have E_EE : dirP eE (dirP eE (dirP eQ F0)) x + dirP eE (dirP eE (dirP eE F1)) x = 0 := by
    rw [← dirP_linear2 hU hQF0 hEF1 eE eE hx]
    exact dirP_zero2 hU hD hx eE eE
  have dX := (dirP_mom hU hTF0 h0 hQF0 h1 hEF0 hQQF0 hEEF0 hQP ν hx eQ).symm.trans
    (dirP_eq_zero (H := fun y => dirP eT F0 y + (F0 y * dirP eQ F0 y + F1 y * dirP eE F0 y) -
      ν * (dirP eQ (dirP eQ F0) y + dirP eE (dirP eE F0) y) + dirP eQ P y) hU M0 hx eQ)
  have dY := (dirP_mom hU hTF1 h0 hQF1 h1 hEF1 hQQF1 hEEF1 hEP ν hx eE).symm.trans
    (dirP_eq_zero (H := fun y => dirP eT F1 y + (F0 y * dirP eQ F1 y + F1 y * dirP eE F1 y) -
      ν * (dirP eQ (dirP eQ F1) y + dirP eE (dirP eE F1) y) + dirP eE P y) hU M1 hx eE)
  rw [S_QT0, S_T2, S_QE0] at dX
  rw [S_ET1, S_QE1, S_T1] at dY
  linear_combination dX + dY - E_T - F0 x * E_Q - F1 x * E_E + ν * E_QQ + ν * E_EE

/-! ### Connection with the velocity and pressure -/

theorem pT_v {T : ℝ} {v : ℝ → Plane → Vec}
    (hv : ContDiffOn ℝ ∞ (fun x : SpT => v x.1 x.2) (Ioo 0 T ×ˢ (univ : Set Plane)))
    (k : Fin 2) {t : ℝ} (ht : t ∈ Ioo 0 T) (w : Plane) :
    (deriv (fun t' => v t' w) t) k = dirP eT (Fc v k) (t, w) := by
  have hmem : ((t, w) : SpT) ∈ Ioo 0 T ×ˢ (univ : Set Plane) := mk_mem_prod ht (mem_univ w)
  have hU : DifferentiableAt ℝ (fun x : SpT => v x.1 x.2) (t, w) :=
    (hv.contDiffAt ((isOpen_strip T).mem_nhds hmem)).differentiableAt (by simp)
  have h1 : HasDerivAt (fun t' => v t' w) (fderiv ℝ (fun x : SpT => v x.1 x.2) (t, w) eT) t := by
    have h0 : HasDerivAt (fun t' : ℝ => ((t', w) : SpT)) eT t :=
      (hasDerivAt_id' t).prodMk (hasDerivAt_const t w)
    exact hU.hasFDerivAt.comp_hasDerivAt t h0
  rw [h1.deriv]
  have h2 : HasFDerivAt (Fc v k)
      ((EuclideanSpace.proj (𝕜 := ℝ) k).comp (fderiv ℝ (fun x : SpT => v x.1 x.2) (t, w)))
      (t, w) :=
    (EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt.comp (t, w) hU.hasFDerivAt
  simp only [dirP]
  rw [h2.fderiv]
  rfl

theorem pQ_v {T : ℝ} {v : ℝ → Plane → Vec}
    (hv : ContDiffOn ℝ ∞ (fun x : SpT => v x.1 x.2) (Ioo 0 T ×ˢ (univ : Set Plane)))
    (k : Fin 2) {t : ℝ} (ht : t ∈ Ioo 0 T) (w : Plane) :
    Cyl.partialQ (fun w' => v t w' k) w = dirP eQ (Fc v k) (t, w) :=
  sliceQ (smU_differentiableAt (isOpen_strip T) (smU_Fc hv k) (mk_mem_prod ht (mem_univ w)))

theorem pE_v {T : ℝ} {v : ℝ → Plane → Vec}
    (hv : ContDiffOn ℝ ∞ (fun x : SpT => v x.1 x.2) (Ioo 0 T ×ˢ (univ : Set Plane)))
    (k : Fin 2) {t : ℝ} (ht : t ∈ Ioo 0 T) (w : Plane) :
    Cyl.partialEta (fun w' => v t w' k) w = dirP eE (Fc v k) (t, w) :=
  sliceE (smU_differentiableAt (isOpen_strip T) (smU_Fc hv k) (mk_mem_prod ht (mem_univ w)))

theorem pQQ_v {T : ℝ} {v : ℝ → Plane → Vec}
    (hv : ContDiffOn ℝ ∞ (fun x : SpT => v x.1 x.2) (Ioo 0 T ×ˢ (univ : Set Plane)))
    (k : Fin 2) {t : ℝ} (ht : t ∈ Ioo 0 T) (w : Plane) :
    Cyl.partialQ (Cyl.partialQ (fun w' => v t w' k)) w = dirP eQ (dirP eQ (Fc v k)) (t, w) :=
  pQQ_gen (t := t) (H := Fc v k) (f := fun w' => v t w' k) rfl
    (fun w' => smU_differentiableAt (isOpen_strip T) (smU_Fc hv k) (mk_mem_prod ht (mem_univ w')))
    (fun w' => smU_differentiableAt (isOpen_strip T)
      (smU_dir (isOpen_strip T) (smU_Fc hv k) eQ) (mk_mem_prod ht (mem_univ w'))) w

theorem pEE_v {T : ℝ} {v : ℝ → Plane → Vec}
    (hv : ContDiffOn ℝ ∞ (fun x : SpT => v x.1 x.2) (Ioo 0 T ×ˢ (univ : Set Plane)))
    (k : Fin 2) {t : ℝ} (ht : t ∈ Ioo 0 T) (w : Plane) :
    Cyl.partialEta (Cyl.partialEta (fun w' => v t w' k)) w = dirP eE (dirP eE (Fc v k)) (t, w) :=
  pEE_gen (t := t) (H := Fc v k) (f := fun w' => v t w' k) rfl
    (fun w' => smU_differentiableAt (isOpen_strip T) (smU_Fc hv k) (mk_mem_prod ht (mem_univ w')))
    (fun w' => smU_differentiableAt (isOpen_strip T)
      (smU_dir (isOpen_strip T) (smU_Fc hv k) eE) (mk_mem_prod ht (mem_univ w'))) w

theorem pQ_P {T : ℝ} {p : ℝ → Plane → ℝ}
    (hp : ContDiffOn ℝ ∞ (fun x : SpT => p x.1 x.2) (Ioo 0 T ×ˢ (univ : Set Plane)))
    {t : ℝ} (ht : t ∈ Ioo 0 T) (w : Plane) :
    Cyl.partialQ (p t) w = dirP eQ (Fs p) (t, w) :=
  pQ_gen (t := t) (H := Fs p) (f := p t) rfl
    (fun w' => smU_differentiableAt (isOpen_strip T) (smU_Fs hp) (mk_mem_prod ht (mem_univ w'))) w

theorem pE_P {T : ℝ} {p : ℝ → Plane → ℝ}
    (hp : ContDiffOn ℝ ∞ (fun x : SpT => p x.1 x.2) (Ioo 0 T ×ˢ (univ : Set Plane)))
    {t : ℝ} (ht : t ∈ Ioo 0 T) (w : Plane) :
    Cyl.partialEta (p t) w = dirP eE (Fs p) (t, w) :=
  pE_gen (t := t) (H := Fs p) (f := p t) rfl
    (fun w' => smU_differentiableAt (isOpen_strip T) (smU_Fs hp) (mk_mem_prod ht (mem_univ w'))) w

theorem pQQ_P {T : ℝ} {p : ℝ → Plane → ℝ}
    (hp : ContDiffOn ℝ ∞ (fun x : SpT => p x.1 x.2) (Ioo 0 T ×ˢ (univ : Set Plane)))
    {t : ℝ} (ht : t ∈ Ioo 0 T) (w : Plane) :
    Cyl.partialQ (Cyl.partialQ (p t)) w = dirP eQ (dirP eQ (Fs p)) (t, w) :=
  pQQ_gen (t := t) (H := Fs p) (f := p t) rfl
    (fun w' => smU_differentiableAt (isOpen_strip T) (smU_Fs hp) (mk_mem_prod ht (mem_univ w')))
    (fun w' => smU_differentiableAt (isOpen_strip T)
      (smU_dir (isOpen_strip T) (smU_Fs hp) eQ) (mk_mem_prod ht (mem_univ w'))) w

theorem pEE_P {T : ℝ} {p : ℝ → Plane → ℝ}
    (hp : ContDiffOn ℝ ∞ (fun x : SpT => p x.1 x.2) (Ioo 0 T ×ˢ (univ : Set Plane)))
    {t : ℝ} (ht : t ∈ Ioo 0 T) (w : Plane) :
    Cyl.partialEta (Cyl.partialEta (p t)) w = dirP eE (dirP eE (Fs p)) (t, w) :=
  pEE_gen (t := t) (H := Fs p) (f := p t) rfl
    (fun w' => smU_differentiableAt (isOpen_strip T) (smU_Fs hp) (mk_mem_prod ht (mem_univ w')))
    (fun w' => smU_differentiableAt (isOpen_strip T)
      (smU_dir (isOpen_strip T) (smU_Fs hp) eE) (mk_mem_prod ht (mem_univ w'))) w

/-! ### The Poisson identity on the open region `(0,T) × ℝ²` -/

theorem interior_poisson {T ν : ℝ} {v : ℝ → Plane → Vec} {p : ℝ → Plane → ℝ}
    (hv : ContDiffOn ℝ ∞ (fun x : SpT => v x.1 x.2) (Icc 0 T ×ˢ (univ : Set Plane)))
    (hp : ContDiffOn ℝ ∞ (fun x : SpT => p x.1 x.2) (Icc 0 T ×ˢ (univ : Set Plane)))
    (hdiv : ∀ t ∈ Ioo 0 T, ∀ w : Plane, Cyl.divergence (v t) w = 0)
    (hmom : ∀ t ∈ Ioo 0 T, ∀ w : Plane, Train.momentumResidual ν v p t w = 0)
    {s : ℝ} (hs : s ∈ Ioo 0 T) (z : Plane) :
    Train.lapS (p s) z = -(Cyl.partialQ (fun w => v s w 0) z ^ 2 +
      2 * Cyl.partialEta (fun w => v s w 0) z * Cyl.partialQ (fun w => v s w 1) z +
      Cyl.partialEta (fun w => v s w 1) z ^ 2) := by
  have hvU : ContDiffOn ℝ ∞ (fun x : SpT => v x.1 x.2) (Ioo 0 T ×ˢ (univ : Set Plane)) :=
    hv.mono (prod_mono Ioo_subset_Icc_self subset_rfl)
  have hpU : ContDiffOn ℝ ∞ (fun x : SpT => p x.1 x.2) (Ioo 0 T ×ˢ (univ : Set Plane)) :=
    hp.mono (prod_mono Ioo_subset_Icc_self subset_rfl)
  have hUo := isOpen_strip T
  have M0 : ∀ y ∈ Ioo 0 T ×ˢ (univ : Set Plane),
      dirP eT (Fc v 0) y + (Fc v 0 y * dirP eQ (Fc v 0) y + Fc v 1 y * dirP eE (Fc v 0) y) -
        ν * (dirP eQ (dirP eQ (Fc v 0)) y + dirP eE (dirP eE (Fc v 0)) y) +
        dirP eQ (Fs p) y = 0 := by
    rintro ⟨t, w⟩ ht
    have ht' : t ∈ Ioo 0 T := (Set.mem_prod.mp ht).1
    have m := congrArg (fun X : Vec => X 0) (hmom t ht' w)
    simp only [Train.momentumResidual, Train.advection, Train.vecLaplacian, Train.gradS,
      Train.lapS, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      Train.toVec_zero, PiLp.zero_apply] at m
    rw [pQQ_v hvU 0 ht' w, pEE_v hvU 0 ht' w, pT_v hvU 0 ht' w, pQ_v hvU 0 ht' w,
      pE_v hvU 0 ht' w, pQ_P hpU ht' w] at m
    exact m
  have M1 : ∀ y ∈ Ioo 0 T ×ˢ (univ : Set Plane),
      dirP eT (Fc v 1) y + (Fc v 0 y * dirP eQ (Fc v 1) y + Fc v 1 y * dirP eE (Fc v 1) y) -
        ν * (dirP eQ (dirP eQ (Fc v 1)) y + dirP eE (dirP eE (Fc v 1)) y) +
        dirP eE (Fs p) y = 0 := by
    rintro ⟨t, w⟩ ht
    have ht' : t ∈ Ioo 0 T := (Set.mem_prod.mp ht).1
    have m := congrArg (fun X : Vec => X 1) (hmom t ht' w)
    simp only [Train.momentumResidual, Train.advection, Train.vecLaplacian, Train.gradS,
      Train.lapS, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      Train.toVec_one, PiLp.zero_apply] at m
    rw [pQQ_v hvU 1 ht' w, pEE_v hvU 1 ht' w, pT_v hvU 1 ht' w, pQ_v hvU 1 ht' w,
      pE_v hvU 1 ht' w, pE_P hpU ht' w] at m
    exact m
  have D : ∀ y ∈ Ioo 0 T ×ˢ (univ : Set Plane), dirP eQ (Fc v 0) y + dirP eE (Fc v 1) y = 0 := by
    rintro ⟨t, w⟩ ht
    have ht' : t ∈ Ioo 0 T := (Set.mem_prod.mp ht).1
    have h := hdiv t ht' w
    rw [Cyl.divergence, pQ_v hvU 0 ht' w, pE_v hvU 1 ht' w] at h
    exact h
  have hx : ((s, z) : SpT) ∈ Ioo 0 T ×ˢ (univ : Set Plane) := mk_mem_prod hs (mem_univ z)
  have key := core_interior hUo (smU_Fc hvU 0) (smU_Fc hvU 1) (smU_Fs hpU) D M0 M1 hx
  have hL : Train.lapS (p s) z =
      dirP eQ (dirP eQ (Fs p)) (s, z) + dirP eE (dirP eE (Fs p)) (s, z) := by
    rw [Train.lapS, pQQ_P hpU hs z, pEE_P hpU hs z]
  rw [hL, key, pQ_v hvU 0 hs z, pE_v hvU 0 hs z, pQ_v hvU 1 hs z, pE_v hvU 1 hs z]

/-! ### Continuity up to the endpoints (within the closed region `[0,T] × ℝ²`) -/

theorem uniqueDiffOn_strip {T : ℝ} (hT : 0 < T) :
    UniqueDiffOn ℝ (Icc 0 T ×ˢ (univ : Set Plane)) :=
  (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ

theorem within_pQ {K : SpT → ℝ} {T : ℝ} (hT : 0 < T)
    (hK : ContDiffOn ℝ ∞ K (Icc 0 T ×ˢ (univ : Set Plane)))
    {t a b : ℝ} (hx : (t, (a, b)) ∈ Icc 0 T ×ˢ (univ : Set Plane)) :
    Cyl.partialQ (fun w => K (t, w)) (a, b) =
      fderivWithin ℝ K (Icc 0 T ×ˢ (univ : Set Plane)) (t, (a, b)) eQ := by
  have hxt : t ∈ Icc 0 T := (Set.mem_prod.mp hx).1
  have hd : DifferentiableWithinAt ℝ K (Icc 0 T ×ˢ (univ : Set Plane)) (t, (a, b)) :=
    (hK.differentiableOn (by simp)) _ hx
  have hF := hd.hasFDerivWithinAt
  have hpath : HasDerivAt (fun q : ℝ => ((t, (q, b)) : SpT)) eQ a :=
    (hasDerivAt_const a t).prodMk ((hasDerivAt_id' a).prodMk (hasDerivAt_const a b))
  have hmaps : MapsTo (fun q : ℝ => ((t, (q, b)) : SpT)) univ (Icc 0 T ×ˢ (univ : Set Plane)) :=
    fun q _ => mk_mem_prod hxt (mem_univ _)
  have hc := hF.comp_hasDerivWithinAt a hpath.hasDerivWithinAt hmaps
  exact (hasDerivWithinAt_univ.mp hc).deriv

theorem within_pE {K : SpT → ℝ} {T : ℝ} (hT : 0 < T)
    (hK : ContDiffOn ℝ ∞ K (Icc 0 T ×ˢ (univ : Set Plane)))
    {t a b : ℝ} (hx : (t, (a, b)) ∈ Icc 0 T ×ˢ (univ : Set Plane)) :
    Cyl.partialEta (fun w => K (t, w)) (a, b) =
      fderivWithin ℝ K (Icc 0 T ×ˢ (univ : Set Plane)) (t, (a, b)) eE := by
  have hxt : t ∈ Icc 0 T := (Set.mem_prod.mp hx).1
  have hd : DifferentiableWithinAt ℝ K (Icc 0 T ×ˢ (univ : Set Plane)) (t, (a, b)) :=
    (hK.differentiableOn (by simp)) _ hx
  have hF := hd.hasFDerivWithinAt
  have hpath : HasDerivAt (fun q : ℝ => ((t, (a, q)) : SpT)) eE b :=
    (hasDerivAt_const b t).prodMk ((hasDerivAt_const b a).prodMk (hasDerivAt_id' b))
  have hmaps : MapsTo (fun q : ℝ => ((t, (a, q)) : SpT)) univ (Icc 0 T ×ˢ (univ : Set Plane)) :=
    fun q _ => mk_mem_prod hxt (mem_univ _)
  have hc := hF.comp_hasDerivWithinAt b hpath.hasDerivWithinAt hmaps
  exact (hasDerivWithinAt_univ.mp hc).deriv

theorem cont_pQ {K : SpT → ℝ} {T : ℝ} (hT : 0 < T)
    (hK : ContDiffOn ℝ ∞ K (Icc 0 T ×ˢ (univ : Set Plane))) :
    ContinuousOn (fun x : SpT => Cyl.partialQ (fun w => K (x.1, w)) x.2)
      (Icc 0 T ×ˢ (univ : Set Plane)) := by
  have h1 : ContinuousOn (fun x : SpT => fderivWithin ℝ K (Icc 0 T ×ˢ (univ : Set Plane)) x eQ)
      (Icc 0 T ×ˢ (univ : Set Plane)) :=
    (hK.continuousOn_fderivWithin (uniqueDiffOn_strip hT) (by simp)).clm_apply continuousOn_const
  refine h1.congr ?_
  rintro ⟨t, a, b⟩ hx
  exact within_pQ hT hK hx

theorem cont_pE {K : SpT → ℝ} {T : ℝ} (hT : 0 < T)
    (hK : ContDiffOn ℝ ∞ K (Icc 0 T ×ˢ (univ : Set Plane))) :
    ContinuousOn (fun x : SpT => Cyl.partialEta (fun w => K (x.1, w)) x.2)
      (Icc 0 T ×ˢ (univ : Set Plane)) := by
  have h1 : ContinuousOn (fun x : SpT => fderivWithin ℝ K (Icc 0 T ×ˢ (univ : Set Plane)) x eE)
      (Icc 0 T ×ˢ (univ : Set Plane)) :=
    (hK.continuousOn_fderivWithin (uniqueDiffOn_strip hT) (by simp)).clm_apply continuousOn_const
  refine h1.congr ?_
  rintro ⟨t, a, b⟩ hx
  exact within_pE hT hK hx

theorem lap_within {H : SpT → ℝ} {T : ℝ} (hT : 0 < T)
    (hH : ContDiffOn ℝ ∞ H (Icc 0 T ×ˢ (univ : Set Plane)))
    {t : ℝ} (ht : t ∈ Icc 0 T) (z : Plane) :
    Train.lapS (fun w => H (t, w)) z =
      Cyl.partialQ (fun w => fderivWithin ℝ H (Icc 0 T ×ˢ (univ : Set Plane)) (t, w) eQ) z +
        Cyl.partialEta (fun w => fderivWithin ℝ H (Icc 0 T ×ˢ (univ : Set Plane)) (t, w) eE) z := by
  obtain ⟨a, b⟩ := z
  have hmem : ∀ w : Plane, (t, w) ∈ Icc 0 T ×ˢ (univ : Set Plane) :=
    fun w => mk_mem_prod ht (mem_univ w)
  have e1 : Cyl.partialQ (fun w => H (t, w)) =
      fun w => fderivWithin ℝ H (Icc 0 T ×ˢ (univ : Set Plane)) (t, w) eQ := by
    funext w
    obtain ⟨a', b'⟩ := w
    exact within_pQ hT hH (hmem (a', b'))
  have e2 : Cyl.partialEta (fun w => H (t, w)) =
      fun w => fderivWithin ℝ H (Icc 0 T ×ˢ (univ : Set Plane)) (t, w) eE := by
    funext w
    obtain ⟨a', b'⟩ := w
    exact within_pE hT hH (hmem (a', b'))
  rw [Train.lapS, e1, e2]

theorem cont_lap {H : SpT → ℝ} {T : ℝ} (hT : 0 < T)
    (hH : ContDiffOn ℝ ∞ H (Icc 0 T ×ˢ (univ : Set Plane))) :
    ContinuousOn (fun x : SpT => Train.lapS (fun w => H (x.1, w)) x.2)
      (Icc 0 T ×ˢ (univ : Set Plane)) := by
  have hK1 : ContDiffOn ℝ ∞ (fun x : SpT => fderivWithin ℝ H (Icc 0 T ×ˢ (univ : Set Plane)) x eQ)
      (Icc 0 T ×ˢ (univ : Set Plane)) :=
    (hH.fderivWithin (uniqueDiffOn_strip hT) (by simp)).clm_apply contDiffOn_const
  have hK2 : ContDiffOn ℝ ∞ (fun x : SpT => fderivWithin ℝ H (Icc 0 T ×ˢ (univ : Set Plane)) x eE)
      (Icc 0 T ×ˢ (univ : Set Plane)) :=
    (hH.fderivWithin (uniqueDiffOn_strip hT) (by simp)).clm_apply contDiffOn_const
  refine ((cont_pQ hT hK1).add (cont_pE hT hK2)).congr ?_
  rintro ⟨t, a, b⟩ hx
  exact lap_within hT hH (Set.mem_prod.mp hx).1 (a, b)

end Framework

end UnforcedLeray.Short.PartI.PPoisson

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Short.PartI.PPoisson

/-- **The pressure Poisson equation** (source line 447). For a classical solution `(v, p)` on
`[0,T]` with the standing hypotheses of `GaugeHyp`, `Δp(s) = -tr((∇v)²)` for every `s ∈ [0,T]`.
Interior times by `interior_poisson`; the endpoints by continuity of both sides on `[0,T]`. -/
theorem pressurePoisson : PressurePoisson := by
  intro ν c T v p h s hs z
  have hT : 0 < T := h.T_pos
  have hv : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2) (Icc 0 T ×ˢ univ) :=
    h.classical.smooth_v
  have hp : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => p x.1 x.2) (Icc 0 T ×ˢ univ) :=
    h.classical.smooth_p
  have hdiv : ∀ t ∈ Ioo 0 T, ∀ w : Plane, Cyl.divergence (v t) w = 0 :=
    fun t ht w => h.classical.solenoidal t (Ioo_subset_Icc_self ht) w
  have hmom : ∀ t ∈ Ioo 0 T, ∀ w : Plane, Train.momentumResidual ν v p t w = 0 :=
    fun t ht => h.classical.momentum t ht
  have hc : ContinuousOn (fun s' : ℝ => ((s', z) : SpT)) (Icc 0 T) :=
    (continuous_id.prodMk continuous_const).continuousOn
  have hm : MapsTo (fun s' : ℝ => ((s', z) : SpT)) (Icc 0 T) (Icc 0 T ×ˢ (univ : Set Plane)) :=
    fun s' hs' => mk_mem_prod hs' (mem_univ z)
  have hcontF : ContinuousOn (fun s' : ℝ => Train.lapS (p s') z) (Icc 0 T) :=
    (cont_lap hT hp).comp hc hm
  have hF0 : ContDiffOn ℝ ∞ (Fc v 0) (Icc 0 T ×ˢ (univ : Set Plane)) :=
    smU_Fc hv 0
  have hF1 : ContDiffOn ℝ ∞ (Fc v 1) (Icc 0 T ×ˢ (univ : Set Plane)) :=
    smU_Fc hv 1
  have hΨ := (((cont_pQ hT hF0).pow 2).add
    (((continuousOn_const : ContinuousOn (fun _ : SpT => (2 : ℝ))
      (Icc 0 T ×ˢ (univ : Set Plane))).mul (cont_pE hT hF0)).mul (cont_pQ hT hF1))).add
    ((cont_pE hT hF1).pow 2) |>.neg
  have hcontG := hΨ.comp hc hm
  have hEq : Set.EqOn (fun s' : ℝ => Train.lapS (p s') z)
      (fun s' : ℝ => -(Cyl.partialQ (fun w => v s' w 0) z ^ 2 +
        2 * Cyl.partialEta (fun w => v s' w 0) z * Cyl.partialQ (fun w => v s' w 1) z +
        Cyl.partialEta (fun w => v s' w 1) z ^ 2)) (Ioo 0 T) := by
    intro s' hs'
    exact interior_poisson hv hp hdiv hmom hs' z
  have hall := Set.EqOn.of_subset_closure hEq hcontF hcontG Ioo_subset_Icc_self
    (closure_Ioo hT.ne).symm.le
  exact hall hs

end UnforcedLeray.Short.PartI
