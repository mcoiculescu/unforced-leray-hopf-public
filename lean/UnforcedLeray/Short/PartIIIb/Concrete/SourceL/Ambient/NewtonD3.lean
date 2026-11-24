import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_9

/-!
# Derivative bounds for the third Newton derivative `newtonD3` (source 4870-4900)

`newtonD3 x i j k = ∂_i ∂_j ∂_k N(x)` with `N = 1/(4π|x|)` is smooth on `ℝ³ \ {0}` and
homogeneous of degree `-4`. Its `m`-th derivative is therefore homogeneous of degree `-4-m`, and is
bounded on `ℝ³ \ {0}` by compactness on the unit sphere.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace NewtonD3

/-- The punctured space `ℝ³ \ {0}`. -/
def punct : Set Vec3 := {w | w ≠ 0}

theorem isOpen_punct : IsOpen punct := isOpen_ne

theorem eucSq_pos_of_ne {w : Vec3} (hw : w ≠ 0) : 0 < eucSq w := by
  unfold eucSq
  by_contra h
  push_neg at h
  apply hw
  funext i
  have h1 : w i ^ 2 ≤ ∑ j, w j ^ 2 :=
    Finset.single_le_sum (f := fun j => w j ^ 2) (fun j _ => sq_nonneg (w j)) (Finset.mem_univ i)
  have h2 : w i ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
  simpa using h2

theorem newtonN_contDiffAt (n : WithTop ℕ∞) {w : Vec3} (hw : w ≠ 0) :
    ContDiffAt ℝ n newtonN w := by
  have hpos : 0 < ∑ i, w i ^ 2 := eucSq_pos_of_ne hw
  have hS : ContDiffAt ℝ n (fun x : Vec3 => ∑ i, x i ^ 2) w := by fun_prop
  have hsq : ContDiffAt ℝ n (fun x : Vec3 => Real.sqrt (∑ i, x i ^ 2)) w :=
    (Real.contDiffAt_sqrt (n := n) hpos.ne').comp w hS
  have hne : 4 * Real.pi * Real.sqrt (∑ i, w i ^ 2) ≠ 0 :=
    mul_ne_zero (by positivity) (Real.sqrt_pos.2 hpos).ne'
  unfold newtonN
  exact contDiffAt_const.div (contDiffAt_const.mul hsq) hne

/-- `ℓ` denotes the order `∞` (smooth) as an element of `WithTop ℕ∞`. -/
abbrev ii : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

theorem newtonN_contDiffOn : ContDiffOn ℝ ii newtonN punct :=
  fun w hw => (newtonN_contDiffAt ii hw).contDiffWithinAt

/-- `∂_k N`. -/
def GG (k : Fin 3) (z : Vec3) : ℝ := fderiv ℝ newtonN z (Pi.single k 1)

/-- `∂_j ∂_k N`. -/
def HH (j k : Fin 3) (y : Vec3) : ℝ := fderiv ℝ (GG k) y (Pi.single j 1)

theorem newtonD3_eq_HH (x : Vec3) (i j k : Fin 3) :
    newtonD3 x i j k = fderiv ℝ (HH j k) x (Pi.single i 1) := rfl

theorem fderivN_contDiffOn : ContDiffOn ℝ ii (fun z => fderiv ℝ newtonN z) punct :=
  newtonN_contDiffOn.fderiv_of_isOpen isOpen_punct (by simp [ii])

theorem GG_contDiffOn (k : Fin 3) : ContDiffOn ℝ ii (GG k) punct :=
  fderivN_contDiffOn.clm_apply contDiffOn_const

theorem HH_contDiffOn (j k : Fin 3) : ContDiffOn ℝ ii (HH j k) punct :=
  ((GG_contDiffOn k).fderiv_of_isOpen isOpen_punct (by simp [ii])).clm_apply contDiffOn_const

theorem newtonD3_contDiffOn (i j k : Fin 3) :
    ContDiffOn ℝ ii (fun x => newtonD3 x i j k) punct :=
  ((HH_contDiffOn j k).fderiv_of_isOpen isOpen_punct (by simp [ii])).clm_apply contDiffOn_const

theorem diffAt_of_punct {f : Vec3 → ℝ} (hf : ContDiffOn ℝ ii f punct) {x : Vec3} (hx : x ∈ punct) :
    DifferentiableAt ℝ f x :=
  (hf.contDiffAt (isOpen_punct.mem_nhds hx)).differentiableAt (by simp [ii])

/-! ## Homogeneity -/

/-- Derivative of a scale-homogeneous function: the directional derivative at `t • x` is `(c/t)`
times that at `x`. -/
theorem fderiv_scale_eq (F : Vec3 → ℝ) (c t : ℝ) (ht : 0 < t) (x : Vec3)
    (hF : ∀ᶠ y in 𝓝 x, F (t • y) = c * F y) (hx : DifferentiableAt ℝ F x)
    (htx : DifferentiableAt ℝ F (t • x)) (v : Vec3) :
    fderiv ℝ F (t • x) v = (c / t) * fderiv ℝ F x v := by
  have hl : HasFDerivAt (fun y : Vec3 => t • y) (t • ContinuousLinearMap.id ℝ Vec3) x :=
    (ContinuousLinearMap.id ℝ Vec3).hasFDerivAt.const_smul t
  have h1 : HasFDerivAt (fun y : Vec3 => F (t • y))
      ((fderiv ℝ F (t • x)).comp (t • ContinuousLinearMap.id ℝ Vec3)) x :=
    htx.hasFDerivAt.comp x hl
  have h2 : fderiv ℝ (fun y : Vec3 => F (t • y)) x
      = (fderiv ℝ F (t • x)).comp (t • ContinuousLinearMap.id ℝ Vec3) := h1.fderiv
  have hF' : (fun y : Vec3 => F (t • y)) =ᶠ[𝓝 x] (fun y => c * F y) := hF
  have h3 : fderiv ℝ (fun y : Vec3 => F (t • y)) x = fderiv ℝ (fun y => c * F y) x :=
    hF'.fderiv_eq
  have h4 : fderiv ℝ (fun y => c * F y) x = c • fderiv ℝ F x := fderiv_const_mul hx c
  have h5 := congrArg (fun L : Vec3 →L[ℝ] ℝ => L v) (h2.symm.trans (h3.trans h4))
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul] at h5
  rw [map_smul, smul_eq_mul] at h5
  field_simp
  linarith

theorem newtonN_smul {t : ℝ} (ht : 0 < t) (y : Vec3) : newtonN (t • y) = t⁻¹ * newtonN y := by
  unfold newtonN
  have hS : ∑ i, (t • y) i ^ 2 = t ^ 2 * ∑ i, y i ^ 2 := by
    simp [Finset.mul_sum, mul_pow]
  rw [hS, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le]
  rcases eq_or_ne (Real.sqrt (∑ i, y i ^ 2)) 0 with h | h
  · simp [h]
  · have htne : t ≠ 0 := ht.ne'
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp

theorem GG_smul {t : ℝ} (ht : 0 < t) {x : Vec3} (hx : x ∈ punct) (k : Fin 3) :
    GG k (t • x) = (t⁻¹ / t) * GG k x := by
  have hF : ∀ᶠ y in 𝓝 x, newtonN (t • y) = t⁻¹ * newtonN y :=
    Filter.Eventually.of_forall (fun y => newtonN_smul ht y)
  have hxt : t • x ∈ punct := smul_ne_zero ht.ne' hx
  exact fderiv_scale_eq newtonN t⁻¹ t ht x hF (diffAt_of_punct newtonN_contDiffOn hx)
    (diffAt_of_punct newtonN_contDiffOn hxt) _

theorem HH_smul {t : ℝ} (ht : 0 < t) {x : Vec3} (hx : x ∈ punct) (j k : Fin 3) :
    HH j k (t • x) = (t⁻¹ / t / t) * HH j k x := by
  have hF : ∀ᶠ y in 𝓝 x, GG k (t • y) = (t⁻¹ / t) * GG k y := by
    filter_upwards [isOpen_punct.mem_nhds hx] with y hy
    exact GG_smul ht hy k
  have hxt : t • x ∈ punct := smul_ne_zero ht.ne' hx
  exact fderiv_scale_eq (GG k) (t⁻¹ / t) t ht x hF (diffAt_of_punct (GG_contDiffOn k) hx)
    (diffAt_of_punct (GG_contDiffOn k) hxt) _

theorem newtonD3_smul {t : ℝ} (ht : 0 < t) {x : Vec3} (hx : x ∈ punct) (i j k : Fin 3) :
    newtonD3 (t • x) i j k = (t⁻¹ / t / t / t) * newtonD3 x i j k := by
  have hF : ∀ᶠ y in 𝓝 x, HH j k (t • y) = (t⁻¹ / t / t) * HH j k y := by
    filter_upwards [isOpen_punct.mem_nhds hx] with y hy
    exact HH_smul ht hy j k
  have hxt : t • x ∈ punct := smul_ne_zero ht.ne' hx
  simp only [newtonD3_eq_HH]
  exact fderiv_scale_eq (HH j k) (t⁻¹ / t / t) t ht x hF (diffAt_of_punct (HH_contDiffOn j k) hx)
    (diffAt_of_punct (HH_contDiffOn j k) hxt) _

theorem inv_chain_eq {t : ℝ} (ht : 0 < t) : t⁻¹ / t / t / t = t ^ (-(4 : ℝ)) := by
  rw [Real.rpow_neg ht.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  field_simp

/-! ## Scaling of the `m`-th derivative of a homogeneous function -/

theorem iteratedFDeriv_smul_scale (f : Vec3 → ℝ) (p : ℝ) (hf : ContDiffOn ℝ ii f punct)
    (hom : ∀ t : ℝ, 0 < t → ∀ x ∈ punct, f (t • x) = t ^ p * f x)
    (m : ℕ) {t : ℝ} (ht : 0 < t) {x : Vec3} (hx : x ∈ punct) :
    iteratedFDeriv ℝ m f (t • x) = (t ^ (p - m)) • iteratedFDeriv ℝ m f x := by
  have hmle : (m : WithTop ℕ∞) ≤ ii := by simp [ii]
  have hfm : ContDiffOn ℝ m f punct := hf.of_le hmle
  set g : Vec3 →L[ℝ] Vec3 := t • ContinuousLinearMap.id ℝ Vec3 with hg
  have hgx : ∀ y, g y = t • y := fun y => rfl
  have hopen' : IsOpen (g ⁻¹' punct) := isOpen_punct.preimage g.continuous
  have hgxS : g x ∈ punct := by rw [hgx]; exact smul_ne_zero ht.ne' hx
  have hxS' : x ∈ g ⁻¹' punct := hgxS
  -- (a) the composition formula on the open set `g⁻¹' punct`
  have hA : iteratedFDerivWithin ℝ m (f ∘ g) (g ⁻¹' punct) x
      = (iteratedFDerivWithin ℝ m f punct (g x)).compContinuousLinearMap (fun _ => g) :=
    ContinuousLinearMap.iteratedFDerivWithin_comp_right g hfm isOpen_punct.uniqueDiffOn
      hopen'.uniqueDiffOn hgxS (i := m) le_rfl
  -- (b) replace `f ∘ g` by `t^p • f` on `g⁻¹' punct`
  have hEq : EqOn (f ∘ g) (fun y => t ^ p * f y) (g ⁻¹' punct) := by
    intro y hy
    have hy' : y ∈ punct := by
      have h1 : g y ≠ 0 := hy
      rw [hgx] at h1
      intro h0
      apply h1
      rw [h0, smul_zero]
    show f (g y) = t ^ p * f y
    rw [hgx]
    exact hom t ht y hy'
  have hB : iteratedFDerivWithin ℝ m (f ∘ g) (g ⁻¹' punct) x
      = iteratedFDerivWithin ℝ m (fun y => t ^ p * f y) (g ⁻¹' punct) x :=
    iteratedFDerivWithin_congr hEq hxS' m
  have hC : iteratedFDerivWithin ℝ m (fun y => t ^ p * f y) (g ⁻¹' punct) x
      = t ^ p • iteratedFDerivWithin ℝ m f (g ⁻¹' punct) x :=
    by
      have hfun : (fun y => t ^ p * f y) = (t ^ p) • f := rfl
      rw [hfun]
      exact iteratedFDerivWithin_const_smul_apply (hfm.contDiffAt (isOpen_punct.mem_nhds hx)
        |>.contDiffWithinAt) hopen'.uniqueDiffOn hxS'
  have hD : iteratedFDerivWithin ℝ m f (g ⁻¹' punct) x = iteratedFDeriv ℝ m f x :=
    iteratedFDerivWithin_of_isOpen m hopen' hxS'
  have hE : iteratedFDerivWithin ℝ m f punct (g x) = iteratedFDeriv ℝ m f (t • x) := by
    rw [hgx]
    exact iteratedFDerivWithin_of_isOpen m isOpen_punct (by rw [← hgx]; exact hgxS)
  have key : (iteratedFDeriv ℝ m f (t • x)).compContinuousLinearMap (fun _ => g)
      = t ^ p • iteratedFDeriv ℝ m f x := by
    rw [← hE, ← hA, hB, hC, hD]
  refine ContinuousMultilinearMap.ext fun v => ?_
  have hpt : (iteratedFDeriv ℝ m f (t • x)) (fun i => t • v i)
      = t ^ p * (iteratedFDeriv ℝ m f x) v := by
    have h := congrArg (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin m => Vec3) ℝ => L v) key
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul, hgx] at h
    exact h
  have e0 : (fun i => t⁻¹ • (t • v i)) = v := by
    funext i
    rw [smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  have e1 := (iteratedFDeriv ℝ m f (t • x)).map_smul_univ (fun _ : Fin m => t⁻¹)
    (fun i => t • v i)
  rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  calc (iteratedFDeriv ℝ m f (t • x)) v
      = (iteratedFDeriv ℝ m f (t • x)) (fun i => t⁻¹ • (t • v i)) := by rw [e0]
    _ = (∏ _i : Fin m, t⁻¹) • (t ^ p * (iteratedFDeriv ℝ m f x) v) := by rw [e1, hpt]
    _ = t ^ (p - m) * (iteratedFDeriv ℝ m f x) v := by
      have htne : t ≠ 0 := ht.ne'
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
        Real.rpow_sub ht, Real.rpow_natCast, div_eq_mul_inv]
      ring

theorem bound_of_hom (f : Vec3 → ℝ) (p : ℝ) (hf : ContDiffOn ℝ ii f punct)
    (hom : ∀ t : ℝ, 0 < t → ∀ x ∈ punct, f (t • x) = t ^ p * f x) (m : ℕ) :
    ∃ C : ℝ, ∀ w ∈ punct, ‖iteratedFDeriv ℝ m f w‖ ≤ C * (Real.sqrt (eucSq w)) ^ (p - m) := by
  have hmle : (m : WithTop ℕ∞) ≤ ii := by simp [ii]
  have hfm : ContDiffOn ℝ m f punct := hf.of_le hmle
  let K : Set Vec3 := {u | eucSq u = 1}
  have hKS : K ⊆ punct := by
    intro u hu h0
    have h1 : eucSq u = 1 := hu
    rw [h0] at h1
    simp [eucSq] at h1
  have hKc : IsCompact K := by
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Vec3) 1) ?_ ?_
    · exact isClosed_eq (by unfold eucSq; fun_prop) continuous_const
    · intro u hu
      have hu1 : eucSq u = 1 := hu
      rw [mem_closedBall_zero_iff]
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
      rw [Real.norm_eq_abs]
      have h1 : u i ^ 2 ≤ eucSq u :=
        Finset.single_le_sum (f := fun j => u j ^ 2) (fun j _ => sq_nonneg (u j))
          (Finset.mem_univ i)
      have h2 : u i ^ 2 ≤ 1 := by linarith
      exact (sq_le_one_iff_abs_le_one _).1 h2
  have hcont : ContinuousOn (iteratedFDeriv ℝ m f) K :=
    (ContinuousOn.continuousOn_iteratedFDeriv hfm isOpen_punct (k := m) le_rfl).mono hKS
  obtain ⟨C0, hC0⟩ := hKc.exists_bound_of_continuousOn hcont
  refine ⟨|C0|, fun w hw => ?_⟩
  have hpos : 0 < eucSq w := eucSq_pos_of_ne hw
  obtain ⟨r, hr⟩ : ∃ r, r = Real.sqrt (eucSq w) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact Real.sqrt_pos.2 hpos
  have hr2 : r ^ 2 = eucSq w := by rw [hr]; exact Real.sq_sqrt hpos.le
  obtain ⟨u, hu⟩ : ∃ u : Vec3, u = r⁻¹ • w := ⟨_, rfl⟩
  have hwu : w = r • u := by rw [hu, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul]
  have hsq : eucSq (r⁻¹ • w) = (r⁻¹) ^ 2 * eucSq w := by
    unfold eucSq
    simp [Finset.mul_sum, mul_pow]
  have huK : u ∈ K := by
    show eucSq u = 1
    rw [hu, hsq, ← hr2]
    field_simp
  have huS : u ∈ punct := hKS huK
  have hpow := iteratedFDeriv_smul_scale f p hf hom m hr0 huS
  have hL : ‖iteratedFDeriv ℝ m f w‖ = r ^ (p - m) * ‖iteratedFDeriv ℝ m f u‖ := by
    conv_lhs => rw [hwu]
    rw [hpow, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hr0.le _)]
  rw [hL, ← hr]
  have hb : ‖iteratedFDeriv ℝ m f u‖ ≤ |C0| := (hC0 u huK).trans (le_abs_self C0)
  rw [mul_comm |C0|]
  exact mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hr0.le _)

end NewtonD3

/-- Third-derivative bound for the Newton kernel (source 4870-4900): each `∂_i∂_j∂_k N` is `C^7`
on `ℝ³ \ {0}` and every `m`-th derivative is `≤ C |w|^{-4-m}`. -/
theorem newtonD3_bound (m : ℕ) : ∃ C : ℝ, ∀ w : Vec3, w ≠ 0 → ∀ i j k : Fin 3,
    ContDiffAt ℝ 7 (fun x => newtonD3 x i j k) w ∧
      ‖iteratedFDeriv ℝ m (fun x => newtonD3 x i j k) w‖ ≤
        C * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) := by
  have hb : ∀ i j k : Fin 3, ∃ C : ℝ, ∀ w ∈ NewtonD3.punct,
      ‖iteratedFDeriv ℝ m (fun x => newtonD3 x i j k) w‖ ≤
        C * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) := by
    intro i j k
    refine NewtonD3.bound_of_hom (fun x => newtonD3 x i j k) (-(4 : ℝ))
      (NewtonD3.newtonD3_contDiffOn i j k) (fun t ht x hx => ?_) m
    show newtonD3 (t • x) i j k = t ^ (-(4 : ℝ)) * newtonD3 x i j k
    rw [NewtonD3.newtonD3_smul ht hx i j k, NewtonD3.inv_chain_eq ht]
  choose Cf hCf using hb
  refine ⟨∑ i, ∑ j, ∑ k, |Cf i j k|, fun w hw i j k => ⟨?_, ?_⟩⟩
  · exact ((NewtonD3.newtonD3_contDiffOn i j k).contDiffAt
      (NewtonD3.isOpen_punct.mem_nhds hw)).of_le (by simp [NewtonD3.ii])
  · have h1 : |Cf i j k| ≤ ∑ k', |Cf i j k'| :=
      Finset.single_le_sum (f := fun k' => |Cf i j k'|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ k)
    have h2 : ∑ k', |Cf i j k'| ≤ ∑ j', ∑ k', |Cf i j' k'| :=
      Finset.single_le_sum (f := fun j' => ∑ k', |Cf i j' k'|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    have h3 : ∑ j', ∑ k', |Cf i j' k'| ≤ ∑ i', ∑ j', ∑ k', |Cf i' j' k'| :=
      Finset.single_le_sum (f := fun i' => ∑ j', ∑ k', |Cf i' j' k'|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.mem_univ i)
    have hC : Cf i j k ≤ ∑ i, ∑ j, ∑ k, |Cf i j k| :=
      (le_abs_self _).trans (h1.trans (h2.trans h3))
    exact (hCf i j k w hw).trans
      (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (Real.sqrt_nonneg _) _))

end UnforcedLeray.Short.PartIIIb.Concrete
