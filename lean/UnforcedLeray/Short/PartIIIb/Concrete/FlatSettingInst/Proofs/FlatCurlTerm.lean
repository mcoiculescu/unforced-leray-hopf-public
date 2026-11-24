import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Leaves
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Setting

/-!
# The curl of one lattice term (source 4597-4608, 4963-4976)

Proves `FlatCurlTerm` (`Leaves.lean`): `∂_q(fTerm)_η - ∂_η(fTerm)_q = curlTermProf (ageA ν s) B (xj ν j x)`.

Route: `Vj = φ J x_j` with `φ(y) = (a²)⁻¹ e^{-|y|²/(4a)}`, so `fTerm = φ · G(y)` in closed
form (`ft_fderiv_Vj` by differentiating along lines; `ft_fTerm_closed`); the two components are
differentiated in `u = y₁` and `v = y₂` (`ft_hasDerivAt_F2_u`, `ft_hasDerivAt_F1_v`); the
curl identity is `ft_curl_key`, closed by `field_simp; ring` after `ft_gaussRdE_eq`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-! ## Scalar objects in the variables `(u, v) = (y₁, y₂)` -/

/-- `φ(u,v) = (a²)⁻¹ e^{-(u²+v²)/(4a)}`. -/
def ftPh (a u v : ℝ) : ℝ := (a ^ 2)⁻¹ * Real.exp (-(u ^ 2 + v ^ 2) / (4 * a))

/-- `y · (B_mer y)` at `y = (u, v)`. -/
def ftQf (B : Mat3) (u v : ℝ) : ℝ := u * (B 0 0 * u + B 0 2 * v) + v * (B 2 0 * u + B 2 2 * v)

/-- `∂_u (ftQf)`. -/
def ftQu (B : Mat3) (u v : ℝ) : ℝ := 2 * B 0 0 * u + (B 0 2 + B 2 0) * v

/-- `∂_v (ftQf)`. -/
def ftQv (B : Mat3) (u v : ℝ) : ℝ := (B 0 2 + B 2 0) * u + 2 * B 2 2 * v

/-- `κ = -(y · B_mer y)/(2a)`. -/
def ftKap (a : ℝ) (B : Mat3) (u v : ℝ) : ℝ := -(ftQf B u v) / (2 * a)

/-- First component of `fTerm / φ`. -/
def ftF1 (a : ℝ) (B : Mat3) (u v : ℝ) : ℝ :=
  ftPh a u v * (ftKap a B u v * (-v) + (-(B 2 0 * u + B 2 2 * v)) + (-(B 0 0 * v) + B 0 2 * u))

/-- Second component of `fTerm / φ`. -/
def ftF2 (a : ℝ) (B : Mat3) (u v : ℝ) : ℝ :=
  ftPh a u v * (ftKap a B u v * u + (B 0 0 * u + B 0 2 * v) + (-(B 2 0 * v) + B 2 2 * u))

/-- `∂_u ftF2` (with `v` fixed). -/
def ftD2 (a : ℝ) (B : Mat3) (u v : ℝ) : ℝ :=
  ftPh a u v * (-(2 * u) / (4 * a)) *
      (ftKap a B u v * u + (B 0 0 * u + B 0 2 * v) + (-(B 2 0 * v) + B 2 2 * u)) +
    ftPh a u v * (-(ftQf B u v + u * ftQu B u v) / (2 * a) + B 0 0 + B 2 2)

/-- `∂_v ftF1` (with `u` fixed). -/
def ftD1 (a : ℝ) (B : Mat3) (u v : ℝ) : ℝ :=
  ftPh a u v * (-(2 * v) / (4 * a)) *
      (ftKap a B u v * (-v) + (-(B 2 0 * u + B 2 2 * v)) + (-(B 0 0 * v) + B 0 2 * u)) +
    ftPh a u v * ((ftQf B u v + v * ftQv B u v) / (2 * a) - B 2 2 - B 0 0)

/-! ## Derivatives of the scalar pieces -/

theorem ft_hasDerivAt_ph_u (a u v : ℝ) :
    HasDerivAt (fun u' : ℝ => ftPh a u' v) (ftPh a u v * (-(2 * u) / (4 * a))) u := by
  have hq : HasDerivAt (fun u' : ℝ => -(u' ^ 2 + v ^ 2) / (4 * a)) (-(2 * u) / (4 * a)) u := by
    have h := (((hasDerivAt_pow 2 u).add_const (v ^ 2)).neg).div_const (4 * a)
    exact h.congr_deriv (by norm_num)
  unfold ftPh
  exact ((hq.exp).const_mul ((a ^ 2)⁻¹)).congr_deriv (by ring)

theorem ft_hasDerivAt_ph_v (a u v : ℝ) :
    HasDerivAt (fun v' : ℝ => ftPh a u v') (ftPh a u v * (-(2 * v) / (4 * a))) v := by
  have hq : HasDerivAt (fun v' : ℝ => -(u ^ 2 + v' ^ 2) / (4 * a)) (-(2 * v) / (4 * a)) v := by
    have h := (((hasDerivAt_pow 2 v).const_add (u ^ 2)).neg).div_const (4 * a)
    exact h.congr_deriv (by norm_num)
  unfold ftPh
  exact ((hq.exp).const_mul ((a ^ 2)⁻¹)).congr_deriv (by ring)

theorem ft_hasDerivAt_ph_dir (a u v p q : ℝ) :
    HasDerivAt (fun t : ℝ => ftPh a (u + t * p) (v + t * q))
      (ftPh a u v * (-(2 * (u * p + v * q)) / (4 * a))) 0 := by
  have hu : HasDerivAt (fun t : ℝ => u + t * p) p 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const p).const_add u
  have hv : HasDerivAt (fun t : ℝ => v + t * q) q 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const q).const_add v
  have hq : HasDerivAt (fun t : ℝ => -((u + t * p) ^ 2 + (v + t * q) ^ 2) / (4 * a))
      (-(2 * (u * p + v * q)) / (4 * a)) 0 := by
    have h := ((((hu.pow 2).add (hv.pow 2)).neg).div_const (4 * a))
    exact h.congr_deriv (by norm_num <;> ring)
  unfold ftPh
  exact ((hq.exp).const_mul ((a ^ 2)⁻¹)).congr_deriv
    (by simp only [zero_mul, add_zero]; ring)

theorem ft_hasDerivAt_qf_u (B : Mat3) (u v : ℝ) :
    HasDerivAt (fun u' : ℝ => ftQf B u' v) (ftQu B u v) u := by
  have h1 := (hasDerivAt_id' u).mul
    (((hasDerivAt_id' u).const_mul (B 0 0)).add_const (B 0 2 * v))
  have h2 := (((hasDerivAt_id' u).const_mul (B 2 0)).add_const (B 2 2 * v)).const_mul v
  have h := h1.add h2
  unfold ftQf ftQu
  exact h.congr_deriv (by ring)

theorem ft_hasDerivAt_qf_v (B : Mat3) (u v : ℝ) :
    HasDerivAt (fun v' : ℝ => ftQf B u v') (ftQv B u v) v := by
  have h1 := ((((hasDerivAt_id' v).const_mul (B 0 2)).const_add (B 0 0 * u)).const_mul u)
  have h2 := (hasDerivAt_id' v).mul
    (((hasDerivAt_id' v).const_mul (B 2 2)).const_add (B 2 0 * u))
  have h := h1.add h2
  unfold ftQf ftQv
  refine h.congr_deriv ?_
  ring

theorem ft_hasDerivAt_F2_u (a : ℝ) (B : Mat3) (u v : ℝ) :
    HasDerivAt (fun u' : ℝ => ftF2 a B u' v) (ftD2 a B u v) u := by
  have hK : HasDerivAt (fun u' : ℝ => -(ftQf B u' v) / (2 * a)) (-(ftQu B u v) / (2 * a)) u :=
    (ft_hasDerivAt_qf_u B u v).neg.div_const (2 * a)
  have hKu := hK.mul (hasDerivAt_id' u)
  have hL1 : HasDerivAt (fun u' : ℝ => B 0 0 * u' + B 0 2 * v) (B 0 0 * 1) u :=
    ((hasDerivAt_id' u).const_mul (B 0 0)).add_const (B 0 2 * v)
  have hL2 : HasDerivAt (fun u' : ℝ => -(B 2 0 * v) + B 2 2 * u') (B 2 2 * 1) u :=
    HasDerivAt.const_add (-(B 2 0 * v)) ((hasDerivAt_id' u).const_mul (B 2 2))
  have hG := (hKu.add hL1).add hL2
  have hf := (ft_hasDerivAt_ph_u a u v).mul hG
  unfold ftF2 ftD2 ftKap
  refine hf.congr_deriv ?_
  simp only [Pi.add_apply, Pi.mul_apply, Pi.neg_apply, Pi.sub_apply, Pi.one_apply]
  ring

theorem ft_hasDerivAt_F1_v (a : ℝ) (B : Mat3) (u v : ℝ) :
    HasDerivAt (fun v' : ℝ => ftF1 a B u v') (ftD1 a B u v) v := by
  have hK : HasDerivAt (fun v' : ℝ => -(ftQf B u v') / (2 * a)) (-(ftQv B u v) / (2 * a)) v :=
    (ft_hasDerivAt_qf_v B u v).neg.div_const (2 * a)
  have hKv := hK.mul (hasDerivAt_id' v).neg
  have hL1 : HasDerivAt (fun v' : ℝ => -(B 2 0 * u + B 2 2 * v')) (-(B 2 2 * 1)) v :=
    (((hasDerivAt_id' v).const_mul (B 2 2)).const_add (B 2 0 * u)).neg
  have hL2 : HasDerivAt (fun v' : ℝ => -(B 0 0 * v') + B 0 2 * u) (-(B 0 0 * 1)) v :=
    (((hasDerivAt_id' v).const_mul (B 0 0)).neg).add_const (B 0 2 * u)
  have hG := (hKv.add hL1).add hL2
  have hf := (ft_hasDerivAt_ph_v a u v).mul hG
  unfold ftF1 ftD1 ftKap
  refine hf.congr_deriv ?_
  simp only [Pi.add_apply, Pi.mul_apply, Pi.neg_apply, Pi.sub_apply, Pi.one_apply]
  ring

/-! ## The gradient of the Gaussian profile -/

theorem ft_gaussRdE_eq (a r : ℝ) :
    gaussRdE a r = (a ^ 2)⁻¹ * Real.exp (-(r ^ 2) / (4 * a)) *
      (-2 * r ^ 2 / a + (r ^ 2) ^ 2 / (4 * a ^ 2)) := by
  have hA : HasDerivAt (fun r' : ℝ => 2 - r' ^ 2 / (2 * a)) (-(2 * r) / (2 * a)) r := by
    have h := ((hasDerivAt_pow 2 r).div_const (2 * a)).const_sub 2
    exact h.congr_deriv (by norm_num <;> ring)
  have hE : HasDerivAt (fun r' : ℝ => Real.exp (-(r' ^ 2) / (4 * a)))
      (Real.exp (-(r ^ 2) / (4 * a)) * (-(2 * r) / (4 * a))) r := by
    have h := (((hasDerivAt_pow 2 r).neg).div_const (4 * a)).exp
    exact h.congr_deriv (by norm_num)
  have hG : HasDerivAt (gaussE a)
      ((a ^ 2)⁻¹ * (-(2 * r) / (2 * a)) * Real.exp (-(r ^ 2) / (4 * a)) +
        (a ^ 2)⁻¹ * (2 - r ^ 2 / (2 * a)) * (Real.exp (-(r ^ 2) / (4 * a)) * (-(2 * r) / (4 * a))))
      r := (hA.const_mul ((a ^ 2)⁻¹)).mul hE
  unfold gaussRdE
  rw [hG.deriv]
  ring

/-! ## The directional derivative of `V_j` and the closed form of `fTerm` -/

theorem ft_fderiv_Vj (ν s : ℝ) (j : ℤ) (x w : ℝ × ℝ) :
    fderiv ℝ (Vj ν s j) x w =
      (ftPh (ageA ν s) (xj ν j x).1 (xj ν j x).2 *
          (-(2 * ((xj ν j x).1 * w.1 + (xj ν j x).2 * w.2)) / (4 * ageA ν s))) • Jrot (xj ν j x) +
        ftPh (ageA ν s) (xj ν j x).1 (xj ν j x).2 • Jrot w := by
  have hdiff : DifferentiableAt ℝ (Vj ν s j) x := by
    unfold Vj sq2 xj Jrot
    fun_prop
  have ht : HasDerivAt (fun t : ℝ => x + t • w) w 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).smul_const w).const_add x
  have hc := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) ht (by simp)
  have hxj : ∀ t : ℝ, xj ν j (x + t • w) =
      ((xj ν j x).1 + t * w.1, (xj ν j x).2 + t * w.2) := by
    intro t
    ext <;> simp [xj] <;> ring
  have hfun : (Vj ν s j ∘ fun t : ℝ => x + t • w) =
      fun t : ℝ => ftPh (ageA ν s) ((xj ν j x).1 + t * w.1) ((xj ν j x).2 + t * w.2) •
        Jrot ((xj ν j x).1 + t * w.1, (xj ν j x).2 + t * w.2) := by
    funext t
    show Vj ν s j (x + t • w) = _
    unfold Vj
    rw [hxj t]
    rfl
  have hA := ft_hasDerivAt_ph_dir (ageA ν s) (xj ν j x).1 (xj ν j x).2 w.1 w.2
  have h1 : HasDerivAt (fun t : ℝ => (xj ν j x).1 + t * w.1) w.1 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const w.1).const_add (xj ν j x).1
  have h2 : HasDerivAt (fun t : ℝ => (xj ν j x).2 + t * w.2) w.2 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const w.2).const_add (xj ν j x).2
  have hB : HasDerivAt (fun t : ℝ => Jrot ((xj ν j x).1 + t * w.1, (xj ν j x).2 + t * w.2))
      (Jrot w) 0 := (h2.neg).prodMk h1
  have hE := hA.smul hB
  have key : HasDerivAt (Vj ν s j ∘ fun t : ℝ => x + t • w)
      ((ftPh (ageA ν s) (xj ν j x).1 (xj ν j x).2 *
          (-(2 * ((xj ν j x).1 * w.1 + (xj ν j x).2 * w.2)) / (4 * ageA ν s))) • Jrot (xj ν j x) +
        ftPh (ageA ν s) (xj ν j x).1 (xj ν j x).2 • Jrot w) 0 := by
    rw [hfun]
    exact hE.congr_deriv (by simp only [zero_mul, add_zero, Prod.mk.eta]; exact add_comm _ _)
  exact hc.unique key

theorem ft_fTerm_closed (ν s : ℝ) (B : Mat3) (j : ℤ) (x : ℝ × ℝ) :
    fTerm ν s B j x = (ftF1 (ageA ν s) B (xj ν j x).1 (xj ν j x).2,
      ftF2 (ageA ν s) B (xj ν j x).1 (xj ν j x).2) := by
  have hV : Vj ν s j x = ftPh (ageA ν s) (xj ν j x).1 (xj ν j x).2 • Jrot (xj ν j x) := by
    unfold Vj
    rfl
  unfold fTerm
  rw [ft_fderiv_Vj, hV]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Jrot,
      merApply, ftF1, ftKap, ftQf]
    ring
  · simp only [Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Jrot,
      merApply, ftF2, ftKap, ftQf]
    ring

/-! ## The curl identity -/

theorem ft_curl_key (a : ℝ) (ha : a ≠ 0) (B : Mat3) (u v : ℝ) :
    ftD2 a B u v - ftD1 a B u v = curlTermProf a B (u, v) := by
  have hR : planeR (u, v) ^ 2 = u ^ 2 + v ^ 2 := by
    unfold planeR
    exact Real.sq_sqrt (by positivity)
  unfold curlTermProf
  rw [ft_gaussRdE_eq a (planeR (u, v)), hR]
  unfold gaussE
  rw [hR]
  unfold ftD2 ftD1 ftKap ftQf ftQu ftQv ftPh ConcreteYF.Bbeta Bd Be
  by_cases hz : u ^ 2 + v ^ 2 = 0
  · have hu2 : u ^ 2 = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
    have hv2 : v ^ 2 = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
    have hu : u = 0 := (pow_eq_zero_iff two_ne_zero).1 hu2
    have hv : v = 0 := (pow_eq_zero_iff two_ne_zero).1 hv2
    subst hu
    subst hv
    norm_num
    field_simp
    ring
  · have hz' : u ^ 2 + v ^ 2 ≠ 0 := hz
    field_simp
    ring

/-! ## The target -/

/-- **(a1) The curl of one lattice term** (source 4597-4608). -/
theorem flatCurlTerm : FlatCurlTerm := by
  intro ν s B j x hν hs
  have hpos : 0 < ageA ν s := by
    unfold ageA
    have := mul_nonneg hν hs
    linarith
  have ha : ageA ν s ≠ 0 := hpos.ne'
  have e2 : (fun q : ℝ => (fTerm ν s B j (q, x.2)).2) =
      fun q : ℝ => ftF2 (ageA ν s) B (q - (j : ℝ) * cOf ν) x.2 := by
    funext q
    rw [ft_fTerm_closed ν s B j (q, x.2)]
    rfl
  have e1 : (fun η : ℝ => (fTerm ν s B j (x.1, η)).1) =
      fun η : ℝ => ftF1 (ageA ν s) B (x.1 - (j : ℝ) * cOf ν) η := by
    funext η
    rw [ft_fTerm_closed ν s B j (x.1, η)]
    rfl
  have hD2 : deriv (fun q : ℝ => (fTerm ν s B j (q, x.2)).2) x.1 =
      ftD2 (ageA ν s) B (xj ν j x).1 (xj ν j x).2 := by
    rw [e2]
    exact ((ft_hasDerivAt_F2_u (ageA ν s) B (x.1 - (j : ℝ) * cOf ν) x.2).comp_sub_const
      x.1 ((j : ℝ) * cOf ν)).deriv
  have hD1 : deriv (fun η : ℝ => (fTerm ν s B j (x.1, η)).1) x.2 =
      ftD1 (ageA ν s) B (xj ν j x).1 (xj ν j x).2 := by
    rw [e1]
    exact (ft_hasDerivAt_F1_v (ageA ν s) B (x.1 - (j : ℝ) * cOf ν) x.2).deriv
  rw [hD2, hD1]
  exact ft_curl_key (ageA ν s) ha B (xj ν j x).1 (xj ν j x).2

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
