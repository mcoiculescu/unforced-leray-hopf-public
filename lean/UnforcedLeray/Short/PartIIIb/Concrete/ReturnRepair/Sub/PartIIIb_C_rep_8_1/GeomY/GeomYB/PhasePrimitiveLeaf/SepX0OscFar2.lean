import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.PhasePrimitiveLeaf.Defs

/-!
# `YBPhase.sepX0OscFar2` (task `PartIII-b:C/rep/8/1/1/2/5/1/1/3`)

Source `the November 2 reference manuscript`
lines 5400-5427, SP 3768-3790.

Proves `YBPhase.SepX0OscFar2`: order-`2` (Hessian) phase-primitive oscillation bound for
`D²_y X₀` on the transition annulus `ν ≤ xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4`, mirroring
`GeomX/PhasePrimitive/FarLeaf.lean` and `GeomX/PhasePrimitive/FarLeafOrg/{Kernel,Point,Pointwise}.lean`
one spatial derivative higher.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray UnforcedLeray.Short.IIIa
open UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg

namespace YBPhase

open YBComm PhasePrim

/-! ## 1. Joint `C⁴` regularity of `Fj` and kernel bounds for `Hk2` -/

private lemma L2_psi_contDiff6 (t : ℝ) (ht : 0 < t) : ContDiff ℝ 6 (L2hkPsi t 0) := by
  have hIter : ∀ m : ℕ, iteratedDeriv m (L2hkPsi t 0) = L2hkPsi t m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [iteratedDeriv_succ, ih]
      funext r
      exact (L2_psi_hasDeriv t ht m r).deriv
  have h : ContDiff ℝ ((6 : ℕ∞) : WithTop ℕ∞) (L2hkPsi t 0) := by
    apply contDiff_of_differentiable_iteratedDeriv
    intro m _
    rw [hIter m]
    intro r
    exact (L2_psi_hasDeriv t ht m r).differentiableAt
  exact_mod_cast h

private lemma kjTail_contDiffOn6 : ContDiffOn ℝ 6 kjTail {p : ℝ × Space | 0 < p.1} := by
  intro p hp
  have hp1 : 0 < p.1 := hp
  apply ContDiffAt.contDiffWithinAt
  have h1 : ContDiffAt ℝ 6 (fun q : ℝ × Space => q.1 ^ (-1 / 2 : ℝ)) p :=
    ContDiffAt.rpow_const_of_ne contDiffAt_fst hp1.ne'
  have h2 : ContDiffAt ℝ 6 (fun q : ℝ × Space => ‖q.2‖ ^ 2 / (4 * q.1)) p := by
    refine ContDiffAt.div ?_ ?_ (by positivity)
    · exact (contDiff_norm_sq ℝ).comp contDiff_snd |>.contDiffAt
    · exact (contDiff_const.mul contDiff_fst).contDiffAt
  exact h1.mul ((L2_psi_contDiff6 1 one_pos).contDiffAt.comp p h2)

private lemma heatLerayK_jointC4 (i j : Fin 3) :
    ContDiffOn ℝ 4 (Fj i j) {p : ℝ × Space | 0 < p.1} := by
  have hU : IsOpen {p : ℝ × Space | 0 < p.1} := isOpen_U
  have hT := kjTail_contDiffOn6
  have hdiff : ∀ p ∈ {p : ℝ × Space | 0 < p.1}, DifferentiableAt ℝ kjTail p := fun p hp =>
    (hT.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hp)
  set ej : Space := UnforcedLeray.coordinateVector j
  set ei : Space := UnforcedLeray.coordinateVector i
  have hG1 : ContDiffOn ℝ 5 (fun p => fderiv ℝ kjTail p (0, ej)) {p : ℝ × Space | 0 < p.1} :=
    kj_deriv_contDiffOn (n := 5) hT ej
  have hG1d : ∀ p ∈ {p : ℝ × Space | 0 < p.1},
      DifferentiableAt ℝ (fun p => fderiv ℝ kjTail p (0, ej)) p := fun p hp =>
    (hG1.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hp)
  have hG2 : ContDiffOn ℝ 4 (fun p => fderiv ℝ (fun q => fderiv ℝ kjTail q (0, ej)) p (0, ei))
      {p : ℝ × Space | 0 < p.1} := kj_deriv_contDiffOn (n := 4) hG1 ei
  have hG : ContDiffOn ℝ 4 (fun p : ℝ × Space => IIIa.heatG p.1 p.2)
      {p : ℝ × Space | 0 < p.1} := by
    intro p hp
    apply ContDiffAt.contDiffWithinAt
    have hp1 : 0 < p.1 := hp
    unfold IIIa.heatG
    refine ContDiffAt.mul ?_ ?_
    · exact ContDiffAt.rpow_const_of_ne (by fun_prop) (by positivity)
    · refine Real.contDiff_exp.contDiffAt.comp p ?_
      refine ContDiffAt.div ?_ ?_ (by positivity)
      · exact (((contDiff_norm_sq ℝ).comp contDiff_snd).neg).contDiffAt
      · exact (contDiff_const.mul contDiff_fst).contDiffAt
  have hpart : ∀ t : ℝ, 0 < t → ∀ x : Space, IIIa.part2 (IIIa.heatTail t) i j x =
      fderiv ℝ (fun q => fderiv ℝ kjTail q (0, ej)) (t, x) (0, ei) := by
    intro t ht x
    have hsl : ∀ y : Space, (t, y) ∈ {p : ℝ × Space | 0 < p.1} := fun y => ht
    have hfun : IIIa.heatTail t = fun y => kjTail (t, y) := funext fun y => kj_heatTail_eq t ht y
    unfold IIIa.part2
    rw [hfun]
    have e1 : (fun y => fderiv ℝ (fun y' => kjTail (t, y')) y ej) =
        fun y => fderiv ℝ kjTail (t, y) (0, ej) :=
      funext fun y => kj_slice_fderiv hU hdiff t ej hsl y
    rw [e1]
    exact kj_slice_fderiv hU hG1d t ei hsl x
  have hsum : ContDiffOn ℝ 4 (fun p : ℝ × Space =>
      (if i = j then IIIa.heatG p.1 p.2 else 0) +
      fderiv ℝ (fun q => fderiv ℝ kjTail q (0, ej)) p (0, ei)) {p : ℝ × Space | 0 < p.1} := by
    refine ContDiffOn.add ?_ hG2
    by_cases h : i = j
    · simp only [h, ↓reduceIte]; exact hG
    · simp only [h, ↓reduceIte]; exact contDiffOn_const
  refine hsum.congr ?_
  intro p hp
  simp only [Fj, IIIa.heatLerayK, hpart p.1 hp p.2]

private lemma D1_cd3 (i j k : Fin 3) : ContDiffOn ℝ 3 (D1 i j k) {p : ℝ × Space | 0 < p.1} := by
  have h := (heatLerayK_jointC4 i j).fderiv_of_isOpen isOpen_U (m := 3) (by norm_num)
  exact h.clm_apply contDiffOn_const

private lemma Hk_cd2 (i j k : Fin 3) (w : Space) :
    ContDiffOn ℝ 2 (Hk i j k w) {p : ℝ × Space | 0 < p.1} := by
  have h := (D1_cd3 i j k).fderiv_of_isOpen isOpen_U (m := 2) (by norm_num)
  exact h.clm_apply contDiffOn_const

/-- `D_u D_w ∂_k K` as a joint function on `ℝ × Space`. -/
private def Hk2 (i j k : Fin 3) (w u : Space) : ℝ × Space → ℝ :=
  fun p => fderiv ℝ (Hk i j k w) p ((0 : ℝ), u)

private lemma Hk2_cd (i j k : Fin 3) (w u : Space) :
    ContDiffOn ℝ 1 (Hk2 i j k w u) {p : ℝ × Space | 0 < p.1} := by
  have h := (Hk_cd2 i j k w).fderiv_of_isOpen isOpen_U (m := 1) (by norm_num)
  exact h.clm_apply contDiffOn_const

private lemma Hk2_eq (i j k : Fin 3) (w u : Space) {s : ℝ} (hs : 0 < s) (x : Space) :
    Hk2 i j k w u (s, x) = fderiv ℝ (fun x' => fderiv ℝ (fun y' =>
      fderiv ℝ (fun z => heatLerayK s i j z) y' (UnforcedLeray.coordinateVector k)) x' w) x u := by
  have hfun : (fun x' => fderiv ℝ (fun y' =>
      fderiv ℝ (fun z => heatLerayK s i j z) y' (UnforcedLeray.coordinateVector k)) x' w) =
      fun x' => Hk i j k w (s, x') :=
    funext fun x' => (Hk_eq i j k w hs x').symm
  rw [hfun, (Hk_inr i j k w hs x).fderiv]
  simp [Hk2]

private lemma Hk2_inr (i j k : Fin 3) (w u : Space) {s : ℝ} (hs : 0 < s) (x : Space) :
    HasFDerivAt (fun x' : Space => Hk2 i j k w u (s, x'))
      ((fderiv ℝ (Hk2 i j k w u) (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) x :=
  (((Hk2_cd i j k w u).contDiffAt (isOpen_U.mem_nhds
    (show (s, x) ∈ {p : ℝ × Space | 0 < p.1} from hs))).differentiableAt
    (by norm_num)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right s x)

private lemma h3_smooth (i j k : Fin 3) (w : Space) {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ ∞ (fun x' => fderiv ℝ (fun y' =>
      fderiv ℝ (fun z => heatLerayK s i j z) y' (UnforcedLeray.coordinateVector k)) x' w) :=
  (((h2_smooth i j k hs).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)

private lemma pack2_B3 (C3 : ℝ)
    (h3 : ∀ x : Space, x ≠ 0 → ∀ i k : Fin 3, ∀ t : ℝ, 0 < t →
      ‖iteratedFDeriv ℝ (3 + 1) (fun y => heatLerayK t i k y) x‖ ≤ C3 * ‖x‖ ^ (-4 - ((3 : ℕ) : ℝ)))
    (i j k : Fin 3) {s : ℝ} (hs : 0 < s) (x : Space) (hx : x ≠ 0) (w u v : Space) :
    ‖fderiv ℝ (Hk2 i j k w u) (s, x) ((0 : ℝ), v)‖ ≤ |C3| * ‖w‖ * ‖u‖ * ‖v‖ * ‖x‖ ^ (-7 : ℝ) := by
  have hfun : (fun x' : Space => Hk2 i j k w u (s, x')) = fun x' =>
      fderiv ℝ (fun y'' => fderiv ℝ (fun y' =>
        fderiv ℝ (fun z => heatLerayK s i j z) y' (UnforcedLeray.coordinateVector k)) y'' w) x' u :=
    funext fun x' => Hk2_eq i j k w u hs x'
  have e1 : fderiv ℝ (Hk2 i j k w u) (s, x) ((0 : ℝ), v) =
      fderiv ℝ (fun x' : Space => Hk2 i j k w u (s, x')) x v := by
    rw [(Hk2_inr i j k w u hs x).fderiv]; simp
  rw [e1, hfun]
  have a0 := farKer_dir (h3_smooth i j k w hs) u x 1
  have a := farKer_dir (h2_smooth i j k hs) w x 2
  have b := farKer_dir (hk_smooth i j hs) (UnforcedLeray.coordinateVector k) x 3
  have c := h3 x hx i j s hs
  have e : (-4 - ((3 : ℕ) : ℝ)) = -7 := by norm_num
  rw [e] at c
  have hp : 0 ≤ ‖x‖ ^ (-7 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  have c' : ‖iteratedFDeriv ℝ (3 + 1) (fun y => heatLerayK s i j y) x‖ ≤ |C3| * ‖x‖ ^ (-7 : ℝ) :=
    c.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hp)
  have b' : ‖iteratedFDeriv ℝ 3 (fun y => fderiv ℝ (fun z => heatLerayK s i j z) y
      (UnforcedLeray.coordinateVector k)) x‖ ≤ |C3| * ‖x‖ ^ (-7 : ℝ) := by
    refine b.trans ?_
    calc _ ≤ 1 * ‖iteratedFDeriv ℝ (3 + 1) (fun y => heatLerayK s i j y) x‖ :=
          mul_le_mul_of_nonneg_right ((apply_le _).trans (ek_norm k).le) (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact c'
  have a' : ‖iteratedFDeriv ℝ 2 (fun x' => fderiv ℝ (fun y' =>
      fderiv ℝ (fun z => heatLerayK s i j z) y' (UnforcedLeray.coordinateVector k)) x' w) x‖ ≤
      ‖w‖ * (|C3| * ‖x‖ ^ (-7 : ℝ)) :=
    a.trans (mul_le_mul (apply_le w) b' (norm_nonneg _) (norm_nonneg _))
  have a0' : ‖fderiv ℝ (fun x' => fderiv ℝ (fun y'' => fderiv ℝ (fun y' =>
      fderiv ℝ (fun z => heatLerayK s i j z) y' (UnforcedLeray.coordinateVector k)) y'' w) x' u) x‖ ≤
      ‖u‖ * (‖w‖ * (|C3| * ‖x‖ ^ (-7 : ℝ))) := by
    rw [nrm_one]
    exact a0.trans (mul_le_mul (apply_le u) a' (norm_nonneg _) (norm_nonneg _))
  calc _ ≤ ‖fderiv ℝ (fun x' => fderiv ℝ (fun y'' => fderiv ℝ (fun y' =>
        fderiv ℝ (fun z => heatLerayK s i j z) y' (UnforcedLeray.coordinateVector k)) y'' w) x' u) x‖ *
        ‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖u‖ * (‖w‖ * (|C3| * ‖x‖ ^ (-7 : ℝ))) * ‖v‖ :=
        mul_le_mul_of_nonneg_right a0' (norm_nonneg _)
    _ = _ := by ring

private lemma Hk_dd (i j k : Fin 3) (w : Space) {p : ℝ × Space} (hp : 0 < p.1) :
    DifferentiableAt ℝ (fderiv ℝ (Hk i j k w)) p :=
  (((Hk_cd2 i j k w).contDiffAt (isOpen_U.mem_nhds
    (show p ∈ {p : ℝ × Space | 0 < p.1} from hp))).fderiv_right
    (m := 1) (by norm_num)).differentiableAt (by norm_num)

private lemma Hk2_fderiv (i j k : Fin 3) (w u : Space) {p : ℝ × Space} (hp : 0 < p.1)
    (v : ℝ × Space) :
    fderiv ℝ (Hk2 i j k w u) p v = fderiv ℝ (fderiv ℝ (Hk i j k w)) p v ((0 : ℝ), u) := by
  have h := (Hk_dd i j k w hp).hasFDerivAt.clm_apply (hasFDerivAt_const ((0 : ℝ), u) p)
  have : fderiv ℝ (Hk2 i j k w u) p = _ := h.fderiv
  rw [this]
  simp

private lemma dt_D1_smooth (i j k : Fin 3) {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ ∞ (fun y => deriv (fun s' => fderiv ℝ (fun x' => heatLerayK s' i j x') y
      (UnforcedLeray.coordinateVector k)) s) := by
  have hFi : ContDiffOn ℝ 3 (fun p : ℝ × Space => heatLerayK p.1 i j p.2)
      {p : ℝ × Space | 0 < p.1} := heatLerayK_jointC3 i j
  have hK : ContDiff ℝ ∞ (fun y => heatLerayK s i j y) := heatLerayKSmoothAll s hs i j
  have hFun : (fun y' : Space => fderiv ℝ (fun p : ℝ × Space => heatLerayK p.1 i j p.2) (s, y')
      ((1 : ℝ), (0 : Space))) = fun y' : Space => ∑ l : Fin 3,
        fderiv ℝ (fun z => fderiv ℝ (fun x' => heatLerayK s i j x') z
          (UnforcedLeray.coordinateVector l)) y' (UnforcedLeray.coordinateVector l) :=
    funext fun y' => farKer_fderiv_time i j hs y'
  have hfun : (fun y => deriv (fun s' => fderiv ℝ (fun x' => heatLerayK s' i j x') y
      (UnforcedLeray.coordinateVector k)) s) =
      fun y => fderiv ℝ (fun y' : Space => ∑ l : Fin 3,
        fderiv ℝ (fun z => fderiv ℝ (fun x' => heatLerayK s i j x') z
          (UnforcedLeray.coordinateVector l)) y' (UnforcedLeray.coordinateVector l)) y
          (UnforcedLeray.coordinateVector k) := by
    funext y
    rw [← hFun]
    exact farKer_swap (fun p : ℝ × Space => heatLerayK p.1 i j p.2) hFi hs y _
  rw [hfun]
  have hS : ContDiff ℝ ∞ (fun y' : Space => ∑ l : Fin 3,
      fderiv ℝ (fun z => fderiv ℝ (fun x' => heatLerayK s i j x') z
        (UnforcedLeray.coordinateVector l)) y' (UnforcedLeray.coordinateVector l)) := by
    refine ContDiff.sum fun l _ => ?_
    exact (((hK.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).fderiv_right
      (m := ∞) (by simp)).clm_apply contDiff_const
  exact (hS.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private lemma pack2_B2 (Cd : ℝ)
    (hd : ∀ (i j k : Fin 3) (t : ℝ), 0 < t → ∀ x : Space, x ≠ 0 →
      ‖iteratedFDeriv ℝ 2 (fun y => deriv (fun s => fderiv ℝ (fun x' => heatLerayK s i j x') y
        (UnforcedLeray.coordinateVector k)) t) x‖ ≤ Cd * ‖x‖ ^ (-6 - ((2 : ℕ) : ℝ)))
    (i j k : Fin 3) {s : ℝ} (hs : 0 < s) (x : Space) (hx : x ≠ 0) (w u : Space) :
    ‖fderiv ℝ (Hk2 i j k w u) (s, x) ((1 : ℝ), (0 : Space))‖ ≤
      |Cd| * ‖w‖ * ‖u‖ * ‖x‖ ^ (-8 : ℝ) := by
  have hg : ∀ y : Space, fderiv ℝ (fun y' => deriv (fun s' =>
      fderiv ℝ (fun x' => heatLerayK s' i j x') y' (UnforcedLeray.coordinateVector k)) s) y w =
      fderiv ℝ (Hk i j k w) (s, y) ((1 : ℝ), (0 : Space)) := by
    intro y
    have hEq1 : (fun y' => deriv (fun s' => fderiv ℝ (fun x' => heatLerayK s' i j x') y'
        (UnforcedLeray.coordinateVector k)) s) =
        fun y' => fderiv ℝ (D1 i j k) (s, y') ((1 : ℝ), (0 : Space)) := by
      funext y'
      have hEq : (fun s' => fderiv ℝ (fun x' => heatLerayK s' i j x') y'
          (UnforcedLeray.coordinateVector k)) =ᶠ[𝓝 s] fun s' => D1 i j k (s', y') := by
        filter_upwards [(isOpen_Ioi (a := (0 : ℝ))).mem_nhds hs] with s' hs'
        exact (D1_eq i j k hs' y').symm
      rw [hEq.deriv_eq]
      have h1 : HasDerivAt (fun s' : ℝ => ((s', y') : ℝ × Space)) ((1 : ℝ), (0 : Space)) s :=
        (hasDerivAt_id' s).prodMk (hasDerivAt_const s y')
      exact ((D1_d i j k (p := (s, y')) hs).hasFDerivAt.comp_hasDerivAt s h1).deriv
    rw [hEq1, Hk_fderiv i j k w (p := (s, y)) hs]
    have hR := (D1_dd i j k (p := (s, y)) hs).hasFDerivAt.comp y (hasFDerivAt_prodMk_right s y)
    have hR2 := hR.clm_apply (hasFDerivAt_const ((1 : ℝ), (0 : Space)) y)
    have hR3 : HasFDerivAt (fun y' : Space => fderiv ℝ (D1 i j k) (s, y')
      ((1 : ℝ), (0 : Space))) _ y := hR2
    rw [hR3.fderiv]
    have hsymm : IsSymmSndFDerivAt ℝ (D1 i j k) (s, y) :=
      (((D1_cd i j k).contDiffAt (isOpen_U.mem_nhds
        (show (s, y) ∈ {p : ℝ × Space | 0 < p.1} from hs)))).isSymmSndFDerivAt (by norm_num)
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.inr_apply, map_zero, zero_add]
    exact hsymm _ _
  have hgd : fderiv ℝ (fun y => fderiv ℝ (fun y' => deriv (fun s' =>
      fderiv ℝ (fun x' => heatLerayK s' i j x') y' (UnforcedLeray.coordinateVector k)) s) y w) x u =
      fderiv ℝ (Hk2 i j k w u) (s, x) ((1 : ℝ), (0 : Space)) := by
    rw [funext hg, Hk2_fderiv i j k w u (p := (s, x)) hs]
    have hR := (Hk_dd i j k w (p := (s, x)) hs).hasFDerivAt.comp x (hasFDerivAt_prodMk_right s x)
    have hR2 := hR.clm_apply (hasFDerivAt_const ((1 : ℝ), (0 : Space)) x)
    have hR3 : HasFDerivAt (fun y : Space => fderiv ℝ (Hk i j k w) (s, y)
      ((1 : ℝ), (0 : Space))) _ x := hR2
    rw [hR3.fderiv]
    have hsymm : IsSymmSndFDerivAt ℝ (Hk i j k w) (s, x) :=
      (((Hk_cd2 i j k w).contDiffAt (isOpen_U.mem_nhds
        (show (s, x) ∈ {p : ℝ × Space | 0 < p.1} from hs)))).isSymmSndFDerivAt (by norm_num)
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.inr_apply, map_zero, zero_add]
    exact hsymm _ _
  rw [← hgd]
  have hb := hd i j k s hs x hx
  have e : (-6 - ((2 : ℕ) : ℝ)) = -8 := by norm_num
  rw [e] at hb
  have hp : 0 ≤ ‖x‖ ^ (-8 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  have hb' : ‖iteratedFDeriv ℝ 2 (fun y => deriv (fun s' =>
      fderiv ℝ (fun x' => heatLerayK s' i j x') y (UnforcedLeray.coordinateVector k)) s) x‖ ≤
      |Cd| * ‖x‖ ^ (-8 : ℝ) :=
    hb.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hp)
  have hdir := farKer_dir (dt_D1_smooth i j k hs) w x 1
  have hdir' : ‖fderiv ℝ (fun y => fderiv ℝ (fun y' => deriv (fun s' =>
      fderiv ℝ (fun x' => heatLerayK s' i j x') y' (UnforcedLeray.coordinateVector k)) s) y w) x‖ ≤
      ‖w‖ * (|Cd| * ‖x‖ ^ (-8 : ℝ)) := by
    rw [nrm_one]
    exact hdir.trans (mul_le_mul (apply_le w) hb' (norm_nonneg _) (norm_nonneg _))
  calc _ ≤ ‖fderiv ℝ (fun y => fderiv ℝ (fun y' => deriv (fun s' =>
        fderiv ℝ (fun x' => heatLerayK s' i j x') y' (UnforcedLeray.coordinateVector k)) s) y w) x‖ *
        ‖u‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖w‖ * (|Cd| * ‖x‖ ^ (-8 : ℝ)) * ‖u‖ :=
        mul_le_mul_of_nonneg_right hdir' (norm_nonneg _)
    _ = _ := by ring

private theorem kerPack2 : ∃ C : ℝ, 0 < C ∧ ∀ (i j k : Fin 3) (s : ℝ), 0 < s →
    ∀ x : Space, x ≠ 0 → ∀ w u v : Space,
      ‖Hk2 i j k w u (s, x)‖ ≤ C * ‖w‖ * ‖u‖ * ‖x‖ ^ (-6 : ℝ) ∧
      ‖fderiv ℝ (Hk2 i j k w u) (s, x) ((1 : ℝ), (0 : Space))‖ ≤
        C * ‖w‖ * ‖u‖ * ‖x‖ ^ (-8 : ℝ) ∧
      ‖fderiv ℝ (Hk2 i j k w u) (s, x) ((0 : ℝ), v)‖ ≤
        C * ‖w‖ * ‖u‖ * ‖v‖ * ‖x‖ ^ (-7 : ℝ) := by
  obtain ⟨C2, hC2⟩ := sepKernelBounds 2
  obtain ⟨C3, hC3⟩ := sepKernelBounds 3
  obtain ⟨Cd, _, hCd⟩ := farKer_n 2
  refine ⟨|C2| + |C3| + |Cd| + 1, by positivity, ?_⟩
  intro i j k s hs x hx w u v
  have b1 : ‖Hk2 i j k w u (s, x)‖ ≤ |C2| * ‖w‖ * ‖u‖ * ‖x‖ ^ (-6 : ℝ) :=
    pack_B3 C2 (fun x hx i k t ht => (hC2 x hx i k).1 t ht) i j k hs x hx w u
  have b2 := pack2_B2 Cd hCd i j k hs x hx w u
  have b3 := pack2_B3 C3 (fun x hx i k t ht => (hC3 x hx i k).1 t ht) i j k hs x hx w u v
  have hw := norm_nonneg w
  have hu := norm_nonneg u
  have hv := norm_nonneg v
  have p6 : 0 ≤ ‖x‖ ^ (-6 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  have p7 : 0 ≤ ‖x‖ ^ (-7 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  have p8 : 0 ≤ ‖x‖ ^ (-8 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  refine ⟨b1.trans ?_, b2.trans ?_, b3.trans ?_⟩
  · nlinarith [mul_nonneg (mul_nonneg hw hu) p6, abs_nonneg C2, abs_nonneg C3, abs_nonneg Cd]
  · nlinarith [mul_nonneg (mul_nonneg hw hu) p8, abs_nonneg C2, abs_nonneg C3, abs_nonneg Cd]
  · nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hw hu) hv) p7, abs_nonneg C2, abs_nonneg C3,
      abs_nonneg Cd]

/-! ## 2. Phase coefficient `om2` and single-point oscillation estimate (`oscPoint2`) -/

private def om2 (a : ℂ) (ν : ℝ) (z y0 : Space) (i j k : Fin 3) (w u : Space) (l : ℝ) : ℂ :=
  (l : ℂ) ^ a * ((Hk2 i j k w u (pth ν z y0 l) : ℝ) : ℂ)

private lemma om2_cd {ν : ℝ} (hν : 0 < ν) (a : ℂ) (z y0 : Space) (i j k : Fin 3) (w u : Space) :
    ContDiffOn ℝ 1 (om2 a ν z y0 i j k w u) (Ioo 0 1) := by
  have hpath : ContDiff ℝ 1 (pth ν z y0) := by
    unfold pth
    exact (contDiff_const.mul (contDiff_const.sub (contDiff_id.pow 2))).prodMk
      (contDiff_const.sub (contDiff_id.smul contDiff_const))
  have h1 : ContDiffOn ℝ 1 (fun l => Hk2 i j k w u (pth ν z y0 l)) (Ioo 0 1) :=
    (Hk2_cd i j k w u).comp hpath.contDiffOn (fun l hl => pth_pos' hν z y0 hl)
  have h2 : ContDiffOn ℝ 1 (fun l => ((Hk2 i j k w u (pth ν z y0 l) : ℝ) : ℂ)) (Ioo 0 1) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn h1
  exact (cpow_cd a).mul h2

private lemma om2_form {ν : ℝ} (hν : 0 < ν) (a : ℂ) (z y0 : Space) (i j k : Fin 3) (w u : Space)
    {l : ℝ} (hl : l ∈ Ioo (0 : ℝ) 1) :
    om2 a ν z y0 i j k w u l + (l : ℂ) * deriv (om2 a ν z y0 i j k w u) l =
      ((1 + a) * (l : ℂ) ^ a) * ((Hk2 i j k w u (pth ν z y0 l) : ℝ) : ℂ) +
      ((l : ℂ) * (l : ℂ) ^ a) *
        ((fderiv ℝ (Hk2 i j k w u) (pth ν z y0 l) (-(2 * ν * l), -z) : ℝ) : ℂ) := by
  have hl0 : (l : ℂ) ≠ 0 := by exact_mod_cast hl.1.ne'
  have hslit : (l : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left; simpa using hl.1
  have hc : HasDerivAt (fun l : ℝ => (l : ℂ) ^ a) (a * (l : ℂ) ^ (a - 1)) l :=
    ((Complex.hasStrictDerivAt_cpow_const hslit).hasDerivAt).comp_ofReal
  have hh : HasDerivAt (fun l => Hk2 i j k w u (pth ν z y0 l))
      (fderiv ℝ (Hk2 i j k w u) (pth ν z y0 l) (-(2 * ν * l), -z)) l := by
    have hd : DifferentiableAt ℝ (Hk2 i j k w u) (pth ν z y0 l) :=
      ((Hk2_cd i j k w u).contDiffAt (isOpen_U.mem_nhds
        (show pth ν z y0 l ∈ {p : ℝ × Space | 0 < p.1} from pth_pos' hν z y0 hl))).differentiableAt
        (by norm_num)
    exact hd.hasFDerivAt.comp_hasDerivAt l (pth_hasDeriv ν z y0 l)
  have hm := hc.mul hh.ofReal_comp
  have hderiv : deriv (om2 a ν z y0 i j k w u) l = _ := hm.deriv
  rw [hderiv]
  have e : (l : ℂ) ^ (a - 1) = (l : ℂ) ^ a / l := by
    rw [Complex.cpow_sub _ _ hl0, Complex.cpow_one]
  rw [e]
  unfold om2
  field_simp
  ring

private lemma om2_bounds (C : ℝ) (hC0 : 0 ≤ C)
    (hpk : ∀ (i j k : Fin 3) (s : ℝ), 0 < s → ∀ x : Space, x ≠ 0 → ∀ w u v : Space,
      ‖Hk2 i j k w u (s, x)‖ ≤ C * ‖w‖ * ‖u‖ * ‖x‖ ^ (-6 : ℝ) ∧
      ‖fderiv ℝ (Hk2 i j k w u) (s, x) ((1 : ℝ), (0 : Space))‖ ≤
        C * ‖w‖ * ‖u‖ * ‖x‖ ^ (-8 : ℝ) ∧
      ‖fderiv ℝ (Hk2 i j k w u) (s, x) ((0 : ℝ), v)‖ ≤
        C * ‖w‖ * ‖u‖ * ‖v‖ * ‖x‖ ^ (-7 : ℝ))
    {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (a : ℂ) (z y0 : Space) (i j k : Fin 3) (w u : Space)
    (hw : ‖w‖ ≤ 1) (hu : ‖u‖ ≤ 1) {g Z : ℝ} (hg : 0 < g) (hZ : ‖z‖ ≤ Z)
    (hgap : ∀ l ∈ Ioo (0 : ℝ) 1, g ≤ ‖y0 - l • z‖) {l : ℝ} (hl : l ∈ Ioo (0 : ℝ) 1) :
    ‖om2 a ν z y0 i j k w u l‖ ≤ l ^ a.re * (C * g ^ (-6 : ℝ)) ∧
    ‖om2 a ν z y0 i j k w u l + (l : ℂ) * deriv (om2 a ν z y0 i j k w u) l‖ ≤
      l ^ a.re * (‖1 + a‖ * (C * g ^ (-6 : ℝ)) + 2 * C * g ^ (-8 : ℝ) + C * Z * g ^ (-7 : ℝ)) := by
  have hx : y0 - l • z ≠ 0 := by
    intro h0; have := hgap l hl; rw [h0, norm_zero] at this; linarith
  have hs : 0 < ν * (1 - l ^ 2) := pth_pos' hν z y0 hl
  obtain ⟨b1, b2, b3⟩ := hpk i j k _ hs _ hx w u (-z)
  have hxg : g ≤ ‖y0 - l • z‖ := hgap l hl
  have r6 : ‖y0 - l • z‖ ^ (-6 : ℝ) ≤ g ^ (-6 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hg hxg (by norm_num)
  have r7 : ‖y0 - l • z‖ ^ (-7 : ℝ) ≤ g ^ (-7 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hg hxg (by norm_num)
  have r8 : ‖y0 - l • z‖ ^ (-8 : ℝ) ≤ g ^ (-8 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hg hxg (by norm_num)
  have hwu : C * ‖w‖ * ‖u‖ ≤ C := by
    calc C * ‖w‖ * ‖u‖ ≤ C * 1 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hw hC0) hu (norm_nonneg _)
            (mul_nonneg hC0 zero_le_one)
      _ = C := by ring
  have hh : |Hk2 i j k w u (pth ν z y0 l)| ≤ C * g ^ (-6 : ℝ) := by
    rw [← Real.norm_eq_abs]
    refine b1.trans ?_
    exact mul_le_mul hwu r6 (Real.rpow_nonneg (norm_nonneg _) _) hC0
  have hp : pth ν z y0 l = (ν * (1 - l ^ 2), y0 - l • z) := rfl
  have hdec : (-(2 * ν * l), -z) = (-(2 * ν * l)) • ((1 : ℝ), (0 : Space)) + ((0 : ℝ), -z) := by
    ext <;> simp
  have hh' : |fderiv ℝ (Hk2 i j k w u) (pth ν z y0 l) (-(2 * ν * l), -z)| ≤
      2 * C * g ^ (-8 : ℝ) + C * Z * g ^ (-7 : ℝ) := by
    rw [← Real.norm_eq_abs, hdec, map_add, map_smul, hp]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [smul_eq_mul, norm_mul]
      have e1 : ‖-(2 * ν * l)‖ ≤ 2 := by
        rw [norm_neg, Real.norm_eq_abs, abs_of_pos (by have := hl.1; positivity)]
        nlinarith [hl.1, hl.2]
      calc _ ≤ 2 * (C * ‖w‖ * ‖u‖ * ‖y0 - l • z‖ ^ (-8 : ℝ)) :=
            mul_le_mul e1 b2 (norm_nonneg _) (by norm_num)
        _ ≤ 2 * (C * g ^ (-8 : ℝ)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul hwu r8 (Real.rpow_nonneg (norm_nonneg _) _) hC0) (by norm_num)
        _ = _ := by ring
    · refine b3.trans ?_
      rw [norm_neg]
      exact mul_le_mul (mul_le_mul hwu hZ (norm_nonneg _) hC0) r7
        (Real.rpow_nonneg (norm_nonneg _) _)
        (by have := (norm_nonneg z).trans hZ; positivity)
  have hlr : 0 ≤ l ^ a.re := Real.rpow_nonneg hl.1.le _
  refine ⟨?_, ?_⟩
  · unfold om2
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hl.1, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hh hlr
  · rw [om2_form hν a z y0 i j k w u hl]
    refine (norm_add_le _ _).trans ?_
    have n1 : ‖((1 + a) * (l : ℂ) ^ a) * ((Hk2 i j k w u (pth ν z y0 l) : ℝ) : ℂ)‖ ≤
        l ^ a.re * (‖1 + a‖ * (C * g ^ (-6 : ℝ))) := by
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hl.1, Complex.norm_real,
        Real.norm_eq_abs]
      calc ‖1 + a‖ * l ^ a.re * |Hk2 i j k w u (pth ν z y0 l)|
          ≤ ‖1 + a‖ * l ^ a.re * (C * g ^ (-6 : ℝ)) :=
            mul_le_mul_of_nonneg_left hh (by positivity)
        _ = _ := by ring
    have n2 : ‖((l : ℂ) * (l : ℂ) ^ a) *
        ((fderiv ℝ (Hk2 i j k w u) (pth ν z y0 l) (-(2 * ν * l), -z) : ℝ) : ℂ)‖ ≤
        l ^ a.re * (2 * C * g ^ (-8 : ℝ) + C * Z * g ^ (-7 : ℝ)) := by
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hl.1, Complex.norm_real,
        Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl.1]
      calc l * l ^ a.re * |fderiv ℝ (Hk2 i j k w u) (pth ν z y0 l) (-(2 * ν * l), -z)|
          ≤ 1 * l ^ a.re * (2 * C * g ^ (-8 : ℝ) + C * Z * g ^ (-7 : ℝ)) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hl.2.le hlr) hh' (abs_nonneg _) (by positivity)
        _ = _ := by ring
    linarith

private lemma fd2_eq (i j k : Fin 3) (u w : Space) {s : ℝ} (hs : 0 < s) (l : ℝ) (z y0 : Space) :
    (fderiv ℝ (fderiv ℝ (fun y' => fderiv ℝ (fun x => heatLerayK s i j x) (y' - l • z)
      (UnforcedLeray.coordinateVector k))) y0 u) w = Hk2 i j k w u (s, y0 - l • z) := by
  set g : Space → ℝ := fun y' => fderiv ℝ (fun x => heatLerayK s i j x) (y' - l • z)
    (UnforcedLeray.coordinateVector k)
  have hg : ContDiff ℝ ∞ g :=
    (h2_smooth i j k hs).comp (contDiff_id.sub contDiff_const)
  have hfd_g : ∀ y', Hk i j k w (s, y' - l • z) = fderiv ℝ g y' w :=
    fun y' => (fd_eq i j k w hs l z y').symm
  have h1 : HasFDerivAt (fun y' => fderiv ℝ g y' w)
      ((ContinuousLinearMap.apply ℝ ℝ w).comp (fderiv ℝ (fderiv ℝ g) y0)) y0 :=
    (ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp y0
      (((hg.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) y0).hasFDerivAt
  have h2 : HasFDerivAt (fun y' => Hk i j k w (s, y' - l • z))
      (fderiv ℝ (fun x' => Hk i j k w (s, x')) (y0 - l • z)) y0 := by
    have hd : DifferentiableAt ℝ (fun x' => Hk i j k w (s, x')) (y0 - l • z) :=
      (Hk_inr i j k w hs (y0 - l • z)).differentiableAt
    have hc : HasFDerivAt ((fun x' => Hk i j k w (s, x')) ∘ fun y' => y' - l • z)
        ((fderiv ℝ (fun x' => Hk i j k w (s, x')) (y0 - l • z)).comp
          (ContinuousLinearMap.id ℝ Space)) y0 :=
      hd.hasFDerivAt.comp y0 ((hasFDerivAt_id y0).sub_const (l • z))
    rwa [ContinuousLinearMap.comp_id] at hc
  have heq := congrArg (fun L => L u) ((h1.congr_of_eventuallyEq
    (Eventually.of_forall hfd_g)).unique h2)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] at heq
  rw [heq, Hk2_eq i j k w u hs (y0 - l • z)]
  congr 2
  funext x'
  exact Hk_eq i j k w hs x'

private theorem oscPoint2 :
    ∀ K : Set ℂ, IsCompact K → (∀ μ ∈ K, -(1 / 4) < μ.re) → ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧
      ∀ ν c ε ρo ρi : ℝ, 0 < ν → ν ≤ 1 → 0 < c → 0 < ε → ε ≤ 1 → 0 ≤ ρo → ρo < ρi → ∀ μ ∈ K,
        ∀ f : ℝ → ℝ, Measurable f → (∀ q, f (q + c) = f q) → (∫ q in Ioc 0 c, f q) = 0 →
        ∀ (z xo : Space) (q₀ : ℝ), ε * Real.sqrt (z 0 ^ 2 + z 1 ^ 2) ≤ ρo →
          ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) → ∀ (i j k : Fin 3) (u w : Space),
            ‖u‖ ≤ 1 → ‖w‖ ≤ 1 →
            ‖∫ l in Ioo (0 : ℝ) 1, (l : ℂ) ^ (2 * μ + 2) *
                (((fderiv ℝ (fderiv ℝ (fun y' =>
                  fderiv ℝ (fun x => heatLerayK (ν * (1 - l ^ 2)) i j x)
                    (y' - l • z) (UnforcedLeray.coordinateVector k))) (ε⁻¹ • xo) u) w : ℝ) : ℂ) *
                ((f (q₀ + ε⁻¹ * Real.log l) : ℝ) : ℂ)‖ₑ ≤
              ENNReal.ofReal ((ε * (Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2))⁻¹) *
                (C * (1 + ν⁻¹ + c + ρi⁻¹ + ρi * (ρi - ρo)⁻¹) ^ m * ε ^ 6 *
                  (1 + |z 2|) * Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) ^ (-5 : ℝ))) *
                ∫⁻ q in Ioc 0 c, ‖f q‖ₑ := by
  intro K hK hRe
  obtain ⟨C, hCpos, hpk⟩ := kerPack2
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  set Λ : ℝ := 3 + 2 * |R|
  have hΛ1 : 1 ≤ Λ := by linarith [abs_nonneg R]
  refine ⟨(2 * Λ + 8) * C, 10, by positivity, ?_⟩
  intro ν c ε ρo ρi hν hν1 hc hε hε1 hρo hρ μ hμ f hfm hper hmean z xo q₀ hz hxo i j k u w hu hw
  set r : ℝ := Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)
  have hρi : 0 < ρi := lt_of_le_of_lt hρo hρ
  have hrpos : 0 < r := lt_of_lt_of_le hρi hxo
  have hd : 0 < r - ρo := by linarith
  set y0 : Space := ε⁻¹ • xo
  set g : ℝ := (r - ρo) / ε
  have hg : 0 < g := div_pos hd hε
  set Z : ℝ := ρo / ε + |z 2|
  have hzh : hor z ≤ ρo / ε := by
    rw [le_div_iff₀ hε, mul_comm]; exact hz
  have hZ : ‖z‖ ≤ Z := by linarith [norm_le_hor z]
  have hZ0 : 0 ≤ Z := (norm_nonneg z).trans hZ
  have hgap : ∀ l ∈ Ioo (0 : ℝ) 1, g ≤ ‖y0 - l • z‖ := by
    intro l hl
    have h1 := hor_sub y0 z l hl.1.le
    have h2 : hor y0 = ε⁻¹ * r := by
      rw [hor_smul _ (inv_nonneg.2 hε.le)]; rfl
    have h3 : l * hor z ≤ ρo / ε := by
      calc l * hor z ≤ 1 * (ρo / ε) :=
            mul_le_mul hl.2.le hzh (by unfold hor; positivity) (by norm_num)
        _ = _ := one_mul _
    have h4 : g = ε⁻¹ * r - ρo / ε := by unfold g; field_simp
    have := hor_le_norm (y0 - l • z)
    linarith
  set a : ℂ := 2 * μ + 2
  have hare : a.re = 2 * μ.re + 2 := by simp [a]
  have hμre := hRe μ hμ
  have hnorm : ‖1 + a‖ ≤ Λ := by
    calc ‖1 + (2 * μ + 2)‖ = ‖(3 : ℂ) + 2 * μ‖ := by congr 1; ring
      _ ≤ ‖(3 : ℂ)‖ + ‖2 * μ‖ := norm_add_le _ _
      _ ≤ 3 + 2 * |R| := by
        rw [norm_mul]
        have h3 : ‖(3 : ℂ)‖ = 3 := by simp
        have h2 : ‖(2 : ℂ)‖ = 2 := by simp
        rw [h3, h2]
        have := hR μ hμ
        have := le_abs_self R
        linarith
  set E2 : ℝ := Λ * (C * g ^ (-6 : ℝ)) + 2 * C * g ^ (-8 : ℝ) + C * Z * g ^ (-7 : ℝ)
  have g6 : 0 < g ^ (-6 : ℝ) := Real.rpow_pos_of_pos hg _
  have g7 : 0 ≤ g ^ (-7 : ℝ) := Real.rpow_nonneg hg.le _
  have g8 : 0 < g ^ (-8 : ℝ) := Real.rpow_pos_of_pos hg _
  have hE2 : 0 < E2 := by positivity
  have hb := fun l (hl : l ∈ Ioo (0 : ℝ) 1) =>
    om2_bounds C hCpos.le hpk hν hν1 a z y0 i j k w u hw hu hg hZ hgap hl
  have hkey := osc_abstract phaseIBP (om2 a ν z y0 i j k w u) (a.re + 1) E2
    (by rw [hare]; linarith) hE2 (om2_cd hν a z y0 i j k w u)
    (fun l hl => by
      have := (hb l hl).1
      have e : a.re + 1 - 1 = a.re := by ring
      rw [e]
      refine this.trans ?_
      have hlr : 0 ≤ l ^ a.re := Real.rpow_nonneg hl.1.le _
      rw [mul_comm E2]
      refine mul_le_mul_of_nonneg_left ?_ hlr
      have : 0 ≤ C * g ^ (-6 : ℝ) := by positivity
      nlinarith [mul_nonneg this (by linarith : 0 ≤ Λ - 1), mul_pos hCpos g8,
        mul_nonneg (mul_nonneg hCpos.le hZ0) g7])
    (fun l hl => by
      have := (hb l hl).2
      have e : a.re + 1 - 1 = a.re := by ring
      rw [e]
      refine this.trans ?_
      have hlr : 0 ≤ l ^ a.re := Real.rpow_nonneg hl.1.le _
      rw [mul_comm E2]
      refine mul_le_mul_of_nonneg_left ?_ hlr
      have : 0 ≤ C * g ^ (-6 : ℝ) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hnorm this])
    ε c hε hc f hfm hper hmean q₀
  have hint_eq : (∫ l in Ioo (0 : ℝ) 1, (l : ℂ) ^ (2 * μ + 2) *
      (((fderiv ℝ (fderiv ℝ (fun y' =>
        fderiv ℝ (fun x => heatLerayK (ν * (1 - l ^ 2)) i j x)
          (y' - l • z) (UnforcedLeray.coordinateVector k))) y0 u) w : ℝ) : ℂ) *
      ((f (q₀ + ε⁻¹ * Real.log l) : ℝ) : ℂ)) =
      ∫ l in Ioo (0 : ℝ) 1, om2 a ν z y0 i j k w u l *
        ((f (q₀ + ε⁻¹ * Real.log l) : ℝ) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioo (fun l hl => ?_)
    have hs : 0 < ν * (1 - l ^ 2) := pth_pos' hν z y0 hl
    rw [fd2_eq i j k u w hs l z y0]
    unfold om2 pth
    rfl
  rw [hint_eq]
  refine hkey.trans ?_
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have hg65 : g ^ (-6 : ℝ) = g⁻¹ * g ^ (-5 : ℝ) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hg]; norm_num
  have hg76 : g ^ (-7 : ℝ) = g⁻¹ * g ^ (-6 : ℝ) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hg]; norm_num
  have hg87 : g ^ (-8 : ℝ) = g⁻¹ * g ^ (-7 : ℝ) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hg]; norm_num
  set E : ℝ := Λ * (C * g ^ (-5 : ℝ)) + 2 * C * g ^ (-7 : ℝ) + C * Z * g ^ (-6 : ℝ)
  have hE_pos : 0 ≤ 2 * ε * E := by
    have : 0 ≤ g ^ (-5 : ℝ) := Real.rpow_nonneg hg.le _
    positivity
  have hE2_eq : 2 * ε * E2 = g⁻¹ * (2 * ε * E) := by
    unfold E2 E
    conv_lhs => rw [hg65, hg76, hg87]
    ring
  set B : ℝ := 1 + ν⁻¹ + c + ρi⁻¹ + ρi * (ρi - ρo)⁻¹
  have hρiρo : 0 < ρi - ρo := by linarith
  have hQB : r / (r - ρo) ≤ B := by
    have h1 : r / (r - ρo) ≤ ρi / (ρi - ρo) := by
      rw [div_le_div_iff₀ hd hρiρo]
      nlinarith [mul_nonneg hρo (sub_nonneg.2 hxo)]
    have n1 : 0 ≤ ν⁻¹ := by positivity
    have n2 : 0 ≤ ρi⁻¹ := by positivity
    change r / (r - ρo) ≤ 1 + ν⁻¹ + c + ρi⁻¹ + ρi * (ρi - ρo)⁻¹
    rw [← div_eq_mul_inv]
    linarith
  have hginv_le : g⁻¹ ≤ (ε * r⁻¹) * B := by
    have hg_eq : g⁻¹ = (ε * r⁻¹) * (r / (r - ρo)) := by
      unfold g
      have hr0 : r ≠ 0 := hrpos.ne'
      have hd0 : r - ρo ≠ 0 := hd.ne'
      field_simp
    rw [hg_eq]
    exact mul_le_mul_of_nonneg_left hQB (by positivity)
  have hB0 : 0 ≤ B := by
    have : 0 ≤ ρi * (ρi - ρo)⁻¹ := by positivity
    positivity
  have hrp := real_part C Λ ε ρo ρi ν c r (z 2) hCpos hΛ1 hν hc hε hε1 hρo hρ hxo hg
  calc 2 * ε * E2 = g⁻¹ * (2 * ε * E) := hE2_eq
    _ ≤ ((ε * r⁻¹) * B) * ((2 * Λ + 8) * C * B ^ 9 * ε ^ 6 * (1 + |z 2|) * r ^ (-5 : ℝ)) :=
        mul_le_mul hginv_le hrp hE_pos (by positivity)
    _ = (ε * r⁻¹) * ((2 * Λ + 8) * C * B ^ 10 * ε ^ 6 * (1 + |z 2|) * r ^ (-5 : ℝ)) := by
        clear_value B r
        ring

/-! ## 3. Second-order differentiation of `sepW` under the integral sign (`fderiv2_sepW_of`) -/

set_option maxHeartbeats 1200000 in
private theorem fderiv2_sepW_of {ν : ℝ} (hν : 0 < ν) {μ : ℂ} {rOut rIn P : ℝ} (hrO : 0 ≤ rOut)
    (hrr : rOut < rIn) (hP : 0 < P) {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hT : IsSepSource P rOut T) (τ : ℝ) (y : Space)
    (hy : rIn ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2))
    (hfin : sepDom (2 * μ.re + 2) 0 (rIn - rOut) (srcNorm T) τ y < ⊤) :
    ContDiffAt ℝ ∞ (fun y' => sepW ν μ T y' τ) y ∧
      Integrable (fun p => iteratedFDeriv ℝ 2 (sepDiffF ν μ T τ p) y) sepDiffRho ∧
      iteratedFDeriv ℝ 2 (fun y' => sepW ν μ T y' τ) y =
        ∫ p, iteratedFDeriv ℝ 2 (sepDiffF ν μ T τ p) y ∂sepDiffRho := by
  have h1 := heatLerayKSmoothAll
  have h3 := sepDiffFMeas
  have h4 := sepDiffFDerivBound
  have h5 := sepDiffWEqIntegral
  have h6 := sepDiffMajIntegrable
  have hK := sepKernelBounds
  choose C hC0 hC using h4 hK
  have hD : 0 < rIn - rOut := by linarith
  set D := rIn - rOut
  set U : Set Space := Metric.ball y (D / 2)
  have hU : IsOpen U := Metric.isOpen_ball
  have hyU : y ∈ U := Metric.mem_ball_self (by linarith)
  set F := sepDiffF ν μ T τ
  have hsm : ∀ p : ℝ × Space, p.1 ∈ Ioo (0 : ℝ) 1 → ∀ i, ContDiff ℝ ∞ (fun y' => F p y' i) :=
    fun p hp i => sepDiffF_contDiff h1 ν μ T τ hν p hp i
  have hsmAt : ∀ (n : ℕ) (p : ℝ × Space), p.1 ∈ Ioo (0 : ℝ) 1 → ∀ (y' : Space) (i : Fin 3),
      ContDiffAt ℝ n (fun y' => F p y' i) y' := fun n p hp y' i =>
    ((hsm p hp i).of_le (by exact_mod_cast le_top)).contDiffAt
  have hoff : ∀ p : ℝ × Space, rOut < Real.sqrt (p.2 0 ^ 2 + p.2 1 ^ 2) → F p = 0 :=
    fun p hp => sepDiffF_eq_zero ν μ T τ p (hT.support _ _ hp)
  have hpi : ∀ (n : ℕ) (p : ℝ × Space), p.1 ∈ Ioo (0 : ℝ) 1 → ∀ y' : Space,
      y' - p.1 • p.2 ≠ 0 → ‖iteratedFDeriv ℝ n (F p) y'‖ ≤ 3 * C n *
        (p.1 ^ (2 * μ.re + 2) * ‖y' - p.1 • p.2‖ ^ (-4 - (n : ℝ)) *
          tensorNorm (T (τ + 2 * Real.log p.1) p.2)) := by
    intro n p hp y' hne
    rw [sepDiff_iteratedFDeriv_pi (fun i => hsmAt n p hp y' i)]
    refine (norm_sum_le _ _).trans ?_
    have hb : ∀ i : Fin 3, ‖(ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i).compContinuousMultilinearMap
        (iteratedFDeriv ℝ n (fun y'' => F p y'' i) y')‖ ≤ C n *
          (p.1 ^ (2 * μ.re + 2) * ‖y' - p.1 • p.2‖ ^ (-4 - (n : ℝ)) *
            tensorNorm (T (τ + 2 * Real.log p.1) p.2)) := by
      intro i
      refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
      have h1i := ContinuousLinearMap.norm_single_le_one ℝ (E := fun _ : Fin 3 => ℂ) i
      have h2i := hC n ν μ T τ hν p.1 p.2 y' hp hne i
      calc ‖ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i‖ *
            ‖iteratedFDeriv ℝ n (fun y'' => F p y'' i) y'‖
          ≤ 1 * ‖iteratedFDeriv ℝ n (fun y'' => F p y'' i) y'‖ := by gcongr
        _ ≤ _ := by rw [one_mul]; exact h2i
    calc ∑ i : Fin 3, ‖(ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i).compContinuousMultilinearMap
          (iteratedFDeriv ℝ n (fun y'' => F p y'' i) y')‖
        ≤ ∑ _i : Fin 3, C n * (p.1 ^ (2 * μ.re + 2) * ‖y' - p.1 • p.2‖ ^ (-4 - (n : ℝ)) *
            tensorNorm (T (τ + 2 * Real.log p.1) p.2)) := Finset.sum_le_sum fun i _ => hb i
      _ = _ := by simp [Finset.sum_const]; ring
  have hgapU : ∀ p : ℝ × Space, p.1 ∈ Ioo (0 : ℝ) 1 → Real.sqrt (p.2 0 ^ 2 + p.2 1 ^ 2) ≤ rOut →
      ∀ y' ∈ U, D ≤ ‖y - p.1 • p.2‖ ∧ ‖y - p.1 • p.2‖ ≤ 2 * ‖y' - p.1 • p.2‖ := by
    intro p hp hz y' hy'
    have hg := radial_gap y p.2 p.1 rOut rIn hp hz hy
    have hd : ‖y - y'‖ < D / 2 := by
      rw [← dist_eq_norm, dist_comm]; exact hy'
    have ht := norm_sub_le_norm_sub_add_norm_sub y y' (p.1 • p.2)
    exact ⟨hg, by linarith⟩
  have hdom : ∀ (n : ℕ) (p : ℝ × Space), p.1 ∈ Ioo (0 : ℝ) 1 → ∀ y' ∈ U,
      ‖iteratedFDeriv ℝ n (F p) y'‖ ≤
        (3 * C n * 2 ^ (4 + (n : ℝ)) * D ^ (-(n : ℝ))) * sepDiffMaj μ T τ y p := by
    intro n p hp y' hy'
    have hl0 : 0 ≤ p.1 ^ (2 * μ.re + 2) := Real.rpow_nonneg hp.1.le _
    have htn : 0 ≤ tensorNorm (T (τ + 2 * Real.log p.1) p.2) := Real.sqrt_nonneg _
    by_cases hz : Real.sqrt (p.2 0 ^ 2 + p.2 1 ^ 2) ≤ rOut
    · obtain ⟨hg1, hg2⟩ := hgapU p hp hz y' hy'
      have hne : y' - p.1 • p.2 ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hg2; linarith
      have hw := sepDiff_gapWeight D ‖y - p.1 • p.2‖ ‖y' - p.1 • p.2‖ n hD hg1 hg2
      refine (hpi n p hp y' hne).trans ?_
      unfold sepDiffMaj
      have hC3 : 0 ≤ 3 * C n := by linarith [hC0 n]
      calc 3 * C n * (p.1 ^ (2 * μ.re + 2) * ‖y' - p.1 • p.2‖ ^ (-4 - (n : ℝ)) *
            tensorNorm (T (τ + 2 * Real.log p.1) p.2))
          ≤ 3 * C n * (p.1 ^ (2 * μ.re + 2) * (2 ^ (4 + (n : ℝ)) * D ^ (-(n : ℝ)) *
              ‖y - p.1 • p.2‖ ^ (-4 : ℝ)) * tensorNorm (T (τ + 2 * Real.log p.1) p.2)) := by
            gcongr
        _ = _ := by ring
    · push Not at hz
      rw [hoff p hz]
      have h0 : iteratedFDeriv ℝ n (0 : Space → Fin 3 → ℂ) y' = 0 := by
        simpa using congrFun (iteratedFDeriv_zero_fun (𝕜 := ℝ) (E := Space) (F := Fin 3 → ℂ) (n := n)) y'
      rw [h0, norm_zero]
      have hTz : T (τ + 2 * Real.log p.1) p.2 = 0 := hT.support _ _ hz
      unfold sepDiffMaj
      rw [hTz]
      simp [tensorNorm]
  have hInt : Integrable (sepDiffMaj μ T τ y) sepDiffRho :=
    h6 μ rOut rIn P T hrO hrr hT τ y hy hfin
  have hLoc : L09.LocDominated sepDiffRho F U := by
    intro n x hx
    refine ⟨U, hU.mem_nhds hx,
      fun p => (3 * C n * 2 ^ (4 + (n : ℝ)) * D ^ (-(n : ℝ))) * sepDiffMaj μ T τ y p,
      hInt.const_mul _, ?_⟩
    filter_upwards [sepDiffRho_ae_mem] with p hp y' hy'
    exact hdom n p hp y' hy'
  have hsmooth : ∀ᵐ p ∂sepDiffRho, ContDiffOn ℝ ∞ (F p) U := by
    filter_upwards [sepDiffRho_ae_mem] with p hp
    exact (contDiff_pi.2 (hsm p hp)).contDiffOn
  have hmeas : ∀ (n : ℕ), ∀ x ∈ U,
      AEStronglyMeasurable (fun p => iteratedFDeriv ℝ n (F p) x) sepDiffRho := by
    intro n x _
    have hR : AEStronglyMeasurable (fun p => ∑ i : Fin 3,
        (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin n => Space) ℂ
          (Fin 3 → ℂ) (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i))
          (iteratedFDeriv ℝ n (fun y' => F p y' i) x)) sepDiffRho := by
      refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
      exact (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin n => Space) ℂ
        (Fin 3 → ℂ) (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℂ) i)).continuous
          |>.comp_aestronglyMeasurable (h3 ν μ P rOut T hν hT τ i n x)
    refine hR.congr ?_
    filter_upwards [sepDiffRho_ae_mem] with p hp
    rw [sepDiff_iteratedFDeriv_pi (fun i => hsmAt n p hp x i)]
    rfl
  have hFint : ∀ y' ∈ U, Integrable (fun p => F p y') sepDiffRho := by
    intro y' hy'
    have hm : AEStronglyMeasurable (fun p => F p y') sepDiffRho := by
      have := (continuousMultilinearCurryFin0 ℝ Space (Fin 3 → ℂ)).continuous
        |>.comp_aestronglyMeasurable (hmeas 0 y' hy')
      refine this.congr (Eventually.of_forall fun p => ?_)
      simp
    refine Integrable.mono' (hInt.const_mul (3 * C 0 * 2 ^ (4 + ((0 : ℕ) : ℝ)) *
      D ^ (-((0 : ℕ) : ℝ)))) hm ?_
    filter_upwards [sepDiffRho_ae_mem] with p hp
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
    exact hdom 0 p hp y' hy'
  have hEq_nhds : (fun y' => sepW ν μ T y' τ) =ᶠ[𝓝 y]
      fun y' => ∫ p, F p y' ∂sepDiffRho := by
    filter_upwards [hU.mem_nhds hyU] with y' hy' using h5 ν μ T τ y' (hFint y' hy')
  have hcd_int : ContDiffAt ℝ ∞ (fun y' => ∫ p, F p y' ∂sepDiffRho) y :=
    (L09.contDiffOn_integral hU hsmooth hmeas hLoc).contDiffAt (hU.mem_nhds hyU)
  have hcd : ContDiffAt ℝ ∞ (fun y' => sepW ν μ T y' τ) y :=
    hcd_int.congr_of_eventuallyEq hEq_nhds
  have hInt2 : Integrable (fun p => iteratedFDeriv ℝ 2 (F p) y) sepDiffRho :=
    hLoc.integrable hmeas 2 hyU
  have hIter2 : iteratedFDeriv ℝ 2 (fun y' => sepW ν μ T y' τ) y =
      ∫ p, iteratedFDeriv ℝ 2 (F p) y ∂sepDiffRho := by
    rw [(hEq_nhds.iteratedFDeriv ℝ 2).self_of_nhds,
      L09.iteratedFDeriv_integral_eq hU hsmooth hmeas hLoc 2 hyU]
  exact ⟨hcd, hInt2, hIter2⟩

/-! ## 4. Entrywise second derivative of `sepDiffF` and `oscFarPt2` -/

private lemma cmm2_enorm_le {L : Space [×2]→L[ℝ] (Fin 3 → ℂ)} {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (h : ∀ (u w : Space) (i : Fin 3), ‖u‖ ≤ 1 → ‖w‖ ≤ 1 → ‖L ![u, w] i‖ₑ ≤ M) : ‖L‖ₑ ≤ M := by
  rw [← ofReal_norm, ← ENNReal.ofReal_toReal hM]
  refine ENNReal.ofReal_le_ofReal (L.opNorm_le_bound ENNReal.toReal_nonneg fun m => ?_)
  rw [Fin.prod_univ_two]
  have hm : m = ![m 0, m 1] := by
    ext j; fin_cases j <;> rfl
  rw [hm]
  by_cases h0 : ‖m 0‖ = 0
  · have hm0 : m 0 = 0 := norm_eq_zero.1 h0
    have hL0 : L ![m 0, m 1] = 0 := by
      simpa [hm0] using L.map_coord_zero (0 : Fin 2) (by simp)
    simp [hL0, h0]
  · by_cases h1 : ‖m 1‖ = 0
    · have hm1 : m 1 = 0 := norm_eq_zero.1 h1
      have hL1 : L ![m 0, m 1] = 0 := by
        simpa [hm1] using L.map_coord_zero (1 : Fin 2) (by simp)
      simp [hL1, h1]
    · have hp0 : 0 < ‖m 0‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      have hp1 : 0 < ‖m 1‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h1)
      set u := ‖m 0‖⁻¹ • m 0
      set w := ‖m 1‖⁻¹ • m 1
      have hu : ‖u‖ ≤ 1 := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hp0.le), inv_mul_cancel₀ h0]
      have hw : ‖w‖ ≤ 1 := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hp1.le), inv_mul_cancel₀ h1]
      have hLuw : ‖L ![u, w]‖ ≤ M.toReal := by
        refine (pi_norm_le_iff_of_nonneg ENNReal.toReal_nonneg).2 fun i => ?_
        have hi := h u w i hu hw
        rw [← ofReal_norm] at hi
        exact (ENNReal.ofReal_le_iff_le_toReal hM).1 hi
      have hm0_eq : m 0 = ‖m 0‖ • u := by simp [u, smul_smul, mul_inv_cancel₀ h0]
      have hm1_eq : m 1 = ‖m 1‖ • w := by simp [w, smul_smul, mul_inv_cancel₀ h1]
      have hup0 : Function.update ![u, m 1] (0 : Fin 2) (‖m 0‖ • u) = ![‖m 0‖ • u, m 1] := by
        ext j; fin_cases j <;> rfl
      have hsmul0 : L ![‖m 0‖ • u, m 1] = ‖m 0‖ • L ![u, m 1] := by
        rw [← hup0, L.map_update_smul]
        congr 2; ext j; fin_cases j <;> rfl
      have hup1 : Function.update ![u, w] (1 : Fin 2) (‖m 1‖ • w) = ![u, ‖m 1‖ • w] := by
        ext j; fin_cases j <;> rfl
      have hsmul1 : L ![u, ‖m 1‖ • w] = ‖m 1‖ • L ![u, w] := by
        rw [← hup1, L.map_update_smul]
        congr 2; ext j; fin_cases j <;> rfl
      calc ‖L ![m 0, m 1]‖ = ‖L ![‖m 0‖ • u, m 1]‖ := by rw [← hm0_eq]
        _ = ‖m 0‖ * ‖L ![u, ‖m 1‖ • w]‖ := by
            rw [hsmul0, norm_smul, Real.norm_of_nonneg hp0.le, ← hm1_eq]
        _ = ‖m 0‖ * (‖m 1‖ * ‖L ![u, w]‖) := by
            rw [hsmul1, norm_smul, Real.norm_of_nonneg hp1.le]
        _ ≤ ‖m 0‖ * (‖m 1‖ * M.toReal) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hLuw hp1.le) hp0.le
        _ = M.toReal * (‖m 0‖ * ‖m 1‖) := by ring

private lemma fderiv2_sepDiffF_sum_entryF {ν : ℝ} (hν : 0 < ν) (ε : ℝ) (μ : ℂ)
    (F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ)
    {p : ℝ × Space} (hp : p.1 ∈ Ioo (0 : ℝ) 1) (y0 : Space) :
    fderiv ℝ (fderiv ℝ (sepDiffF ν μ (thinSource ε F) τ p)) y0 =
      ∑ j₀ : Fin 3, ∑ k₀ : Fin 3,
        fderiv ℝ (fderiv ℝ (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p)) y0 := by
  have hdiff : ∀ j₀ k₀ : Fin 3,
      DifferentiableAt ℝ (fderiv ℝ (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p)) y0 := by
    intro j₀ k₀
    have hsm := sepDiffF_contDiff heatLerayKSmoothAll ν μ
      (thinSource ε (entryF j₀ k₀ F)) τ hν p hp
    exact (((contDiff_pi.2 hsm).fderiv_right (m := ∞) (by simp)).differentiable (by simp)) y0
  have hfun : fderiv ℝ (sepDiffF ν μ (thinSource ε F) τ p) =
      fun y' => ∑ j₀ : Fin 3, ∑ k₀ : Fin 3,
        fderiv ℝ (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p) y' :=
    funext fun y' => fderiv_sepDiffF_sum_entryF hν ε μ F τ hp y'
  have hd : HasFDerivAt (fderiv ℝ (sepDiffF ν μ (thinSource ε F) τ p))
      (∑ j₀ : Fin 3, ∑ k₀ : Fin 3,
        fderiv ℝ (fderiv ℝ (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p)) y0) y0 := by
    rw [hfun]
    exact HasFDerivAt.fun_sum fun j₀ _ => HasFDerivAt.fun_sum fun k₀ _ => (hdiff j₀ k₀).hasFDerivAt
  exact hd.fderiv

private lemma iter2_sepDiffF_sum_entryF {ν : ℝ} (hν : 0 < ν) (ε : ℝ) (μ : ℂ)
    (F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ)
    {p : ℝ × Space} (hp : p.1 ∈ Ioo (0 : ℝ) 1) (y0 : Space) :
    iteratedFDeriv ℝ 2 (sepDiffF ν μ (thinSource ε F) τ p) y0 =
      ∑ j₀ : Fin 3, ∑ k₀ : Fin 3,
        iteratedFDeriv ℝ 2 (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p) y0 := by
  ext m i
  have hm : m = ![m 0, m 1] := by ext r; fin_cases r <;> rfl
  rw [hm, iteratedFDeriv_two_apply, fderiv2_sepDiffF_sum_entryF hν ε μ F τ hp y0]
  simp only [ContinuousMultilinearMap.sum_apply, Finset.sum_apply,
    ContinuousLinearMap.coe_sum', iteratedFDeriv_two_apply]

private lemma fderiv2_sepDiffF_entryF {ν : ℝ} (hν : 0 < ν) (ε : ℝ) (μ : ℂ)
    (F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (j₀ k₀ : Fin 3)
    {l : ℝ} (hl : l ∈ Ioo (0 : ℝ) 1) (z y0 u w : Space) (i : Fin 3) :
    ((fderiv ℝ (fderiv ℝ (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ (l, z))) y0 u) w) i =
      (-2 : ℂ) * ((l : ℂ) ^ (2 * μ + 2) *
        (((fderiv ℝ (fderiv ℝ (fun y' => fderiv ℝ (fun x => heatLerayK (ν * (1 - l ^ 2)) i j₀ x)
          (y' - l • z) (UnforcedLeray.coordinateVector k₀))) y0 u) w : ℝ) : ℂ) *
        ((thinSource ε F (τ + 2 * Real.log l) z j₀ k₀ : ℝ) : ℂ)) := by
  have hs : 0 < ν * (1 - l ^ 2) := pth_pos' hν z y0 hl
  have hsm := sepDiffF_contDiff heatLerayKSmoothAll ν μ
    (thinSource ε (entryF j₀ k₀ F)) τ hν (l, z) hl
  have hdiff1 : DifferentiableAt ℝ
      (fderiv ℝ (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ (l, z))) y0 :=
    (((contDiff_pi.2 hsm).fderiv_right (m := ∞) (by simp)).differentiable (by simp)) y0
  let Λ : (Space →L[ℝ] (Fin 3 → ℂ)) →L[ℝ] ℂ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℂ) i).comp
      (ContinuousLinearMap.apply ℝ (Fin 3 → ℂ) w)
  have hcomp : HasFDerivAt
      (fun y' => (fderiv ℝ (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ (l, z)) y' w) i)
      (Λ.comp (fderiv ℝ (fderiv ℝ (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ (l, z))) y0))
      y0 :=
    Λ.hasFDerivAt.comp y0 hdiff1.hasFDerivAt
  set g : Space → ℝ := fun y' => fderiv ℝ (fun x => heatLerayK (ν * (1 - l ^ 2)) i j₀ x)
    (y' - l • z) (UnforcedLeray.coordinateVector k₀)
  have hg : ContDiff ℝ ∞ g :=
    (h2_smooth i j₀ k₀ hs).comp (contDiff_id.sub contDiff_const)
  have hg_diff1 : DifferentiableAt ℝ (fderiv ℝ g) y0 :=
    ((hg.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) y0
  have hgw : HasFDerivAt (fun y' => fderiv ℝ g y' w)
      ((ContinuousLinearMap.apply ℝ ℝ w).comp (fderiv ℝ (fderiv ℝ g) y0)) y0 :=
    (ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp y0 hg_diff1.hasFDerivAt
  have hgw' : HasFDerivAt (fun y' => ((fderiv ℝ g y' w : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((ContinuousLinearMap.apply ℝ ℝ w).comp (fderiv ℝ (fderiv ℝ g) y0)))
      y0 :=
    Complex.ofRealCLM.hasFDerivAt.comp y0 hgw
  have hscal : HasFDerivAt
      (fun y' => (fderiv ℝ (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ (l, z)) y' w) i)
      ((-2 : ℂ) • ((l : ℂ) ^ (2 * μ + 2) •
        (((thinSource ε F (τ + 2 * Real.log l) z j₀ k₀ : ℝ) : ℂ) •
          (Complex.ofRealCLM.comp
            ((ContinuousLinearMap.apply ℝ ℝ w).comp (fderiv ℝ (fderiv ℝ g) y0)))))) y0 := by
    have h1 := ((hgw'.mul_const
      ((thinSource ε F (τ + 2 * Real.log l) z j₀ k₀ : ℝ) : ℂ)).const_mul
      ((l : ℂ) ^ (2 * μ + 2))).const_mul (-2 : ℂ)
    refine h1.congr_of_eventuallyEq (Eventually.of_forall fun y' => ?_)
    dsimp only
    rw [fderiv_sepDiffF_entryF hν ε μ F τ j₀ k₀ hl z y' w i]
    ring
  have heq := congrArg (fun L => L u) (hcomp.unique hscal)
  simp only [Λ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.apply_apply, smul_apply, Complex.ofRealCLM_apply,
    smul_eq_mul] at heq
  rw [heq]
  ring

set_option maxHeartbeats 800000 in
private theorem oscFarPt2 :
    ∀ K : Set ℂ, IsCompact K → (∀ μ ∈ K, -(1 / 4) < μ.re) → ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
      ∀ ν c ε ρo ρi : ℝ, 0 < ν → ν ≤ 1 → 0 < c → 0 < ε → ε ≤ 1 → 0 ≤ ρo → ρo < ρi → ∀ μ ∈ K,
        ∀ F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ,
          (∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ × ℝ => F w.1 w.2.1 w.2.2 i j) →
          (∀ x' Y q, F x' Y (q + c) = F x' Y q) →
          (∀ x' Y q, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → F x' Y q = 0) →
          (∀ x' Y i j, ∫ q in Ioc 0 c, F x' Y q i j = 0) →
          IIIa.thinMoment c F ≠ ⊤ →
          ∀ xo : Space, ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) → ∀ τ : ℝ,
            ‖iteratedFDeriv ℝ 2 (fun y => sepW ν μ (thinSource ε F) y τ) (ε⁻¹ • xo)‖ₑ ≤
              ENNReal.ofReal ((ε * (Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2))⁻¹) *
                (C * (1 + ν⁻¹ + c + ρi⁻¹ + ρi * (ρi - ρo)⁻¹) ^ k * ε ^ 4 *
                  Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) ^ (-5 : ℝ))) * IIIa.thinMoment c F := by
  intro K hK hRe
  obtain ⟨C₀, m, hC₀, hOsc⟩ := oscPoint2 K hK hRe
  refine ⟨18 * C₀, m + 1, by positivity, ?_⟩
  intro ν c ε ρo ρi hν hν1 hc hε hε1 hρo hρ μ hμ F hmeas hper hsupp hzero hN xo hxo τ
  have hth : ThinHyp c ρo F := ⟨hmeas, hper, hsupp⟩
  set y0 : Space := ε⁻¹ • xo
  set r : ℝ := Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)
  set B : ℝ := 1 + ν⁻¹ + c + ρi⁻¹ + ρi * (ρi - ρo)⁻¹
  have hρi : 0 < ρi := lt_of_le_of_lt hρo hρ
  have hrpos : 0 < r := lt_of_lt_of_le hρi hxo
  have hB0 : 0 ≤ B := by
    have : 0 ≤ ρi * (ρi - ρo)⁻¹ := mul_nonneg hρi.le (inv_nonneg.2 (by linarith))
    positivity
  have hcB : c ≤ B := by
    have : 0 ≤ ρi * (ρi - ρo)⁻¹ := mul_nonneg hρi.le (inv_nonneg.2 (by linarith))
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    have : 0 ≤ ρi⁻¹ := inv_nonneg.2 hρi.le
    change c ≤ 1 + ν⁻¹ + c + ρi⁻¹ + ρi * (ρi - ρo)⁻¹
    linarith
  have hy0 : ρi / ε ≤ Real.sqrt (y0 0 ^ 2 + y0 1 ^ 2) := by
    change ρi / ε ≤ hor (ε⁻¹ • xo)
    rw [hor_smul _ (inv_nonneg.2 hε.le), div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hxo (inv_nonneg.2 hε.le)
  have hP : 0 < 2 * ε * c := by positivity
  have hDomF : sepDom (2 * μ.re + 2) 0 (ρi / ε - ρo / ε) (srcNorm (thinSource ε F)) τ y0 < ⊤ :=
    sepDom_thin_lt_top hε hc hρ (hRe μ hμ) hth hN τ y0
  obtain ⟨_, hIntF, hIterF⟩ := fderiv2_sepW_of hν (div_nonneg hρo hε.le)
    (div_lt_div_of_pos_right hρ hε) hP (thin_isSep hε hth) τ y0 hy0 hDomF
  have hIntE : ∀ j₀ k₀ : Fin 3,
      Integrable
        (fun p => iteratedFDeriv ℝ 2 (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p) y0)
        sepDiffRho := by
    intro j₀ k₀
    have hNE : IIIa.thinMoment c (entryF j₀ k₀ F) ≠ ⊤ :=
      ne_top_of_le_ne_top hN (thinMoment_entryF_le c F j₀ k₀)
    have hDomE := sepDom_thin_lt_top hε hc hρ (hRe μ hμ) (thinHyp_entryF hth j₀ k₀) hNE τ y0
    exact (fderiv2_sepW_of hν (div_nonneg hρo hε.le) (div_lt_div_of_pos_right hρ hε) hP
      (thin_isSep hε (thinHyp_entryF hth j₀ k₀)) τ y0 hy0 hDomE).2.1
  have hEntryBound : ∀ (j₀ k₀ : Fin 3) (u w : Space) (i : Fin 3), ‖u‖ ≤ 1 → ‖w‖ ≤ 1 →
      ‖(∫ p, iteratedFDeriv ℝ 2 (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p) y0
          ∂sepDiffRho) ![u, w] i‖ₑ ≤
        ENNReal.ofReal ((ε * r⁻¹) * (2 * C₀ * B ^ (m + 1) * ε ^ 4 * r ^ (-5 : ℝ))) *
          IIIa.thinMoment c F := by
    intro j₀ k₀ u w i hu hw
    let Λ : (Space [×2]→L[ℝ] (Fin 3 → ℂ)) →L[ℝ] ℂ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℂ) i).comp
        (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Space) (Fin 3 → ℂ) ![u, w])
    have hΛInt : Integrable (fun p =>
        iteratedFDeriv ℝ 2 (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p) y0 ![u, w] i)
        sepDiffRho :=
      Λ.integrable_comp (hIntE j₀ k₀)
    have hΛEq : (∫ p, iteratedFDeriv ℝ 2 (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p) y0
        ∂sepDiffRho) ![u, w] i =
        ∫ z : Space, ∫ l in Ioo (0 : ℝ) 1,
          iteratedFDeriv ℝ 2 (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ (l, z)) y0 ![u, w] i := by
      have h1 := (Λ.integral_comp_comm (hIntE j₀ k₀)).symm
      simp only [Λ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
        ContinuousMultilinearMap.apply_apply] at h1
      rw [h1]
      exact integral_prod_symm _ hΛInt
    rw [hΛEq]
    have hSlice : ∀ z : Space,
        ‖∫ l in Ioo (0 : ℝ) 1,
            iteratedFDeriv ℝ 2
              (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ (l, z)) y0 ![u, w] i‖ₑ ≤
          ENNReal.ofReal ((ε * r⁻¹) * (2 * C₀ * B ^ m * ε ^ 6 * r ^ (-5 : ℝ))) *
            (ENNReal.ofReal (1 + |z 2|) *
              ∫⁻ q in Ioc 0 c, ENNReal.ofReal (tensorNorm (F (ε * z 0, ε * z 1) (z 2) q))) := by
      intro z
      have hcongr : (∫ l in Ioo (0 : ℝ) 1,
          iteratedFDeriv ℝ 2
            (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ (l, z)) y0 ![u, w] i) =
          (-2 : ℂ) * ∫ l in Ioo (0 : ℝ) 1, (l : ℂ) ^ (2 * μ + 2) *
            (((fderiv ℝ (fderiv ℝ (fun y' =>
              fderiv ℝ (fun x => heatLerayK (ν * (1 - l ^ 2)) i j₀ x)
                (y' - l • z) (UnforcedLeray.coordinateVector k₀))) y0 u) w : ℝ) : ℂ) *
            ((F (ε * z 0, ε * z 1) (z 2) (q0 ε τ z + ε⁻¹ * Real.log l) j₀ k₀ : ℝ) : ℂ) := by
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioo fun l hl => ?_
        rw [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_zero, fderiv2_sepDiffF_entryF hν ε μ F τ j₀ k₀ hl z y0 u w i,
          thinSource_q0_apply hε F τ l z j₀ k₀]
      rw [hcongr, enorm_mul]
      have h2 : ‖(-2 : ℂ)‖ₑ = ENNReal.ofReal 2 := by
        rw [← ofReal_norm_eq_enorm]; norm_num
      rw [h2]
      by_cases hz : ε * Real.sqrt (z 0 ^ 2 + z 1 ^ 2) ≤ ρo
      · have hfm : Measurable (fun q => F (ε * z 0, ε * z 1) (z 2) q j₀ k₀) :=
          (hmeas j₀ k₀).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
        have hpt := hOsc ν c ε ρo ρi hν hν1 hc hε hε1 hρo hρ μ hμ
          (fun q => F (ε * z 0, ε * z 1) (z 2) q j₀ k₀) hfm
          (fun q => by rw [hper]) (hzero (ε * z 0, ε * z 1) (z 2) j₀ k₀)
          z xo (q0 ε τ z) hz hxo i j₀ k₀ u w hu hw
        have hle_q : (∫⁻ q in Ioc 0 c, ‖F (ε * z 0, ε * z 1) (z 2) q j₀ k₀‖ₑ) ≤
            ∫⁻ q in Ioc 0 c, ENNReal.ofReal (tensorNorm (F (ε * z 0, ε * z 1) (z 2) q)) := by
          refine lintegral_mono fun q => ?_
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (l5_abs_le_tensorNorm _ j₀ k₀)
        calc ENNReal.ofReal 2 * _
            ≤ ENNReal.ofReal 2 *
                (ENNReal.ofReal ((ε * r⁻¹) * (C₀ * B ^ m * ε ^ 6 * (1 + |z 2|) * r ^ (-5 : ℝ))) *
                  ∫⁻ q in Ioc 0 c,
                    ENNReal.ofReal (tensorNorm (F (ε * z 0, ε * z 1) (z 2) q))) :=
              mul_le_mul_right (hpt.trans (mul_le_mul_right hle_q _)) _
          _ = _ := by
              have hpos1 : 0 ≤ (ε * r⁻¹) * (2 * C₀ * B ^ m * ε ^ 6 * r ^ (-5 : ℝ)) := by positivity
              have heq : ENNReal.ofReal 2 *
                  ENNReal.ofReal ((ε * r⁻¹) * (C₀ * B ^ m * ε ^ 6 * (1 + |z 2|) * r ^ (-5 : ℝ))) =
                  ENNReal.ofReal ((ε * r⁻¹) * (2 * C₀ * B ^ m * ε ^ 6 * r ^ (-5 : ℝ))) *
                    ENNReal.ofReal (1 + |z 2|) := by
                rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul hpos1]
                congr 1; ring
              rw [← mul_assoc, heq, mul_assoc]
      · push Not at hz
        have hF0 : ∀ q, F (ε * z 0, ε * z 1) (z 2) q = 0 := by
          intro q
          apply hsupp
          have : Real.sqrt ((ε * z 0) ^ 2 + (ε * z 1) ^ 2) =
              ε * Real.sqrt (z 0 ^ 2 + z 1 ^ 2) := by
            rw [show (ε * z 0) ^ 2 + (ε * z 1) ^ 2 = ε ^ 2 * (z 0 ^ 2 + z 1 ^ 2) by ring,
              Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hε.le]
          rw [this]; exact hz
        simp [hF0]
    calc ‖∫ z : Space, ∫ l in Ioo (0 : ℝ) 1,
            iteratedFDeriv ℝ 2
              (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ (l, z)) y0 ![u, w] i‖ₑ
        ≤ ∫⁻ z : Space, ‖∫ l in Ioo (0 : ℝ) 1,
            iteratedFDeriv ℝ 2
              (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ (l, z)) y0 ![u, w] i‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ z : Space,
            ENNReal.ofReal ((ε * r⁻¹) * (2 * C₀ * B ^ m * ε ^ 6 * r ^ (-5 : ℝ))) *
              (ENNReal.ofReal (1 + |z 2|) *
                ∫⁻ q in Ioc 0 c, ENNReal.ofReal (tensorNorm (F (ε * z 0, ε * z 1) (z 2) q))) :=
          lintegral_mono hSlice
      _ = ENNReal.ofReal ((ε * r⁻¹) * (2 * C₀ * B ^ m * ε ^ 6 * r ^ (-5 : ℝ))) *
            ∫⁻ z : Space, ENNReal.ofReal (1 + |z 2|) *
              ∫⁻ q in Ioc 0 c, ENNReal.ofReal (tensorNorm (F (ε * z 0, ε * z 1) (z 2) q)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ((ε * r⁻¹) * (2 * C₀ * B ^ m * ε ^ 6 * r ^ (-5 : ℝ))) *
            (ENNReal.ofReal (ε⁻¹) ^ 2 * (ENNReal.ofReal c * IIIa.thinMoment c F)) :=
          mul_le_mul_right (thin_z_moment_le hε hc hth) _
      _ ≤ ENNReal.ofReal ((ε * r⁻¹) * (2 * C₀ * B ^ (m + 1) * ε ^ 4 * r ^ (-5 : ℝ))) *
            IIIa.thinMoment c F := by
          rw [← mul_assoc, ← mul_assoc]
          refine mul_le_mul_left ?_ _
          rw [← ENNReal.ofReal_pow (inv_nonneg.2 hε.le),
            ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hε6 : ε ^ 6 * (ε⁻¹) ^ 2 = ε ^ 4 := by
            have : ε ≠ 0 := hε.ne'
            field_simp
          have h1 : (ε * r⁻¹) * (2 * C₀ * B ^ m * ε ^ 6 * r ^ (-5 : ℝ)) * (ε⁻¹) ^ 2 * c =
              (ε * r⁻¹) * (2 * C₀ * (B ^ m * c) * ε ^ 4 * r ^ (-5 : ℝ)) := by
            calc (ε * r⁻¹) * (2 * C₀ * B ^ m * ε ^ 6 * r ^ (-5 : ℝ)) * (ε⁻¹) ^ 2 * c
                = (ε * r⁻¹) * (2 * C₀ * B ^ m * (ε ^ 6 * (ε⁻¹) ^ 2) * r ^ (-5 : ℝ) * c) := by ring
              _ = (ε * r⁻¹) * (2 * C₀ * (B ^ m * c) * ε ^ 4 * r ^ (-5 : ℝ)) := by rw [hε6]; ring
          have hBm : B ^ m * c ≤ B ^ (m + 1) := by
            rw [pow_succ]
            exact mul_le_mul_of_nonneg_left hcB (pow_nonneg hB0 m)
          rw [h1]
          gcongr
  rw [hIterF]
  have hSumInt : (∫ p, iteratedFDeriv ℝ 2 (sepDiffF ν μ (thinSource ε F) τ p) y0 ∂sepDiffRho) =
      ∑ j₀ : Fin 3, ∑ k₀ : Fin 3,
        ∫ p, iteratedFDeriv ℝ 2 (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p) y0
          ∂sepDiffRho := by
    have hae : ∀ᵐ p ∂sepDiffRho,
        iteratedFDeriv ℝ 2 (sepDiffF ν μ (thinSource ε F) τ p) y0 =
          ∑ j₀ : Fin 3, ∑ k₀ : Fin 3,
            iteratedFDeriv ℝ 2 (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p) y0 := by
      filter_upwards [sepDiffRho_ae_mem] with p hp using iter2_sepDiffF_sum_entryF hν ε μ F τ hp y0
    rw [integral_congr_ae hae,
      integral_finsetSum _ fun j₀ _ => integrable_finsetSum _ fun k₀ _ => hIntE j₀ k₀]
    refine Finset.sum_congr rfl fun j₀ _ => ?_
    exact integral_finsetSum _ fun k₀ _ => hIntE j₀ k₀
  rw [hSumInt]
  have hM_ne_top :
      ENNReal.ofReal ((ε * r⁻¹) * (18 * C₀ * B ^ (m + 1) * ε ^ 4 * r ^ (-5 : ℝ))) *
        IIIa.thinMoment c F ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN
  refine cmm2_enorm_le hM_ne_top fun u w i hu hw => ?_
  simp only [ContinuousMultilinearMap.sum_apply, Finset.sum_apply]
  calc ‖∑ j₀ : Fin 3, ∑ k₀ : Fin 3,
          (∫ p, iteratedFDeriv ℝ 2
            (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p) y0 ∂sepDiffRho) ![u, w] i‖ₑ
      ≤ ∑ j₀ : Fin 3, ∑ k₀ : Fin 3,
          ‖(∫ p, iteratedFDeriv ℝ 2
            (sepDiffF ν μ (thinSource ε (entryF j₀ k₀ F)) τ p) y0 ∂sepDiffRho) ![u, w] i‖ₑ :=
        (enorm_sum_le _ _).trans (Finset.sum_le_sum fun j₀ _ => enorm_sum_le _ _)
    _ ≤ ∑ _j₀ : Fin 3, ∑ _k₀ : Fin 3,
          ENNReal.ofReal ((ε * r⁻¹) * (2 * C₀ * B ^ (m + 1) * ε ^ 4 * r ^ (-5 : ℝ))) *
            IIIa.thinMoment c F :=
        Finset.sum_le_sum fun j₀ _ => Finset.sum_le_sum fun k₀ _ => hEntryBound j₀ k₀ u w i hu hw
    _ = ENNReal.ofReal ((ε * r⁻¹) * (18 * C₀ * B ^ (m + 1) * ε ^ 4 * r ^ (-5 : ℝ))) *
          IIIa.thinMoment c F := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← mul_assoc, ← mul_assoc]
        congr 1
        have h9 : ((3 : ℕ) : ℝ≥0∞) * ((3 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 9 := by norm_num
        rw [h9, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

/-! ## 5. Splitting `iteratedFDeriv ℝ 2 sepW` and assembling `YBPhase.sepX0OscFar2` -/

private lemma sepDiffF_thin_split2 (ν ε c : ℝ) (μ : ℂ)
    (F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (p : ℝ × Space) :
    sepDiffF ν μ (thinSource ε F) τ p =
      sepDiffF ν μ (thinSource ε (meanLift (IIIa.phaseMean c F))) τ p +
        sepDiffF ν μ (thinSource ε (perpPart c F)) τ p := by
  ext y' i
  have hthin : ∀ σ z, thinSource ε F σ z =
      thinSource ε (meanLift (IIIa.phaseMean c F)) σ z + thinSource ε (perpPart c F) σ z := by
    intro σ z
    unfold thinSource meanLift perpPart
    simp
  simp only [sepDiffF, Pi.add_apply, hthin]
  simp only [Matrix.add_apply, Complex.ofReal_add, mul_add, Finset.sum_add_distrib]

private lemma iter2_sepW_thin_split {ν c ε ρo ρi : ℝ} {μ : ℂ}
    (hν : 0 < ν) (hc : 0 < c) (hε : 0 < ε) (hρo : 0 ≤ ρo) (hρ : ρo < ρi)
    (hμ : -(1 / 4) < μ.re) {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hth : ThinHyp c ρo F) (hth1 : ThinHyp c ρo (meanLift (IIIa.phaseMean c F)))
    (hth2 : ThinHyp c ρo (perpPart c F))
    (hN : IIIa.thinMoment c F ≠ ⊤) (hN1 : IIIa.thinMoment c (meanLift (IIIa.phaseMean c F)) ≠ ⊤)
    (hN2 : IIIa.thinMoment c (perpPart c F) ≠ ⊤)
    {xo : Space} (hxo : ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)) (τ : ℝ) :
    iteratedFDeriv ℝ 2 (fun y => sepW ν μ (thinSource ε F) y τ) (ε⁻¹ • xo) -
        iteratedFDeriv ℝ 2 (fun y => sepW ν μ (thinSource ε (meanLift (IIIa.phaseMean c F))) y τ)
          (ε⁻¹ • xo) =
      iteratedFDeriv ℝ 2 (fun y => sepW ν μ (thinSource ε (perpPart c F)) y τ) (ε⁻¹ • xo) := by
  set y0 : Space := ε⁻¹ • xo
  have hy0 : ρi / ε ≤ Real.sqrt (y0 0 ^ 2 + y0 1 ^ 2) := by
    change ρi / ε ≤ hor (ε⁻¹ • xo)
    rw [hor_smul _ (inv_nonneg.2 hε.le), div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hxo (inv_nonneg.2 hε.le)
  have hP : 0 < 2 * ε * c := by positivity
  obtain ⟨_, hInt0, hIter0⟩ := fderiv2_sepW_of hν (div_nonneg hρo hε.le)
    (div_lt_div_of_pos_right hρ hε) hP (thin_isSep hε hth) τ y0 hy0
    (sepDom_thin_lt_top hε hc hρ hμ hth hN τ y0)
  obtain ⟨_, hInt1, hIter1⟩ := fderiv2_sepW_of hν (div_nonneg hρo hε.le)
    (div_lt_div_of_pos_right hρ hε) hP (thin_isSep hε hth1) τ y0 hy0
    (sepDom_thin_lt_top hε hc hρ hμ hth1 hN1 τ y0)
  obtain ⟨_, hInt2, hIter2⟩ := fderiv2_sepW_of hν (div_nonneg hρo hε.le)
    (div_lt_div_of_pos_right hρ hε) hP (thin_isSep hε hth2) τ y0 hy0
    (sepDom_thin_lt_top hε hc hρ hμ hth2 hN2 τ y0)
  rw [hIter0, hIter1, hIter2]
  have hae : ∀ᵐ p ∂sepDiffRho,
      iteratedFDeriv ℝ 2 (sepDiffF ν μ (thinSource ε F) τ p) y0 =
        iteratedFDeriv ℝ 2 (sepDiffF ν μ (thinSource ε (meanLift (IIIa.phaseMean c F))) τ p) y0 +
          iteratedFDeriv ℝ 2 (sepDiffF ν μ (thinSource ε (perpPart c F)) τ p) y0 := by
    filter_upwards [sepDiffRho_ae_mem] with p hp
    have hd1 : ∀ y', DifferentiableAt ℝ
        (sepDiffF ν μ (thinSource ε (meanLift (IIIa.phaseMean c F))) τ p) y' := fun y' =>
      ((contDiff_pi.2 (sepDiffF_contDiff heatLerayKSmoothAll ν μ _ τ hν p hp)).differentiable
        (by simp)) y'
    have hd2 : ∀ y', DifferentiableAt ℝ
        (sepDiffF ν μ (thinSource ε (perpPart c F)) τ p) y' := fun y' =>
      ((contDiff_pi.2 (sepDiffF_contDiff heatLerayKSmoothAll ν μ _ τ hν p hp)).differentiable
        (by simp)) y'
    have hfun : fderiv ℝ (sepDiffF ν μ (thinSource ε F) τ p) =
        fun y' => fderiv ℝ (sepDiffF ν μ (thinSource ε (meanLift (IIIa.phaseMean c F))) τ p) y' +
          fderiv ℝ (sepDiffF ν μ (thinSource ε (perpPart c F)) τ p) y' := by
      funext y'
      rw [sepDiffF_thin_split2 ν ε c μ F τ p]
      exact ((hd1 y').hasFDerivAt.add (hd2 y').hasFDerivAt).fderiv
    have hdd1 : DifferentiableAt ℝ
        (fderiv ℝ (sepDiffF ν μ (thinSource ε (meanLift (IIIa.phaseMean c F))) τ p)) y0 :=
      (((contDiff_pi.2 (sepDiffF_contDiff heatLerayKSmoothAll ν μ _ τ hν p hp)).fderiv_right
        (m := ∞) (by simp)).differentiable (by simp)) y0
    have hdd2 : DifferentiableAt ℝ
        (fderiv ℝ (sepDiffF ν μ (thinSource ε (perpPart c F)) τ p)) y0 :=
      (((contDiff_pi.2 (sepDiffF_contDiff heatLerayKSmoothAll ν μ _ τ hν p hp)).fderiv_right
        (m := ∞) (by simp)).differentiable (by simp)) y0
    have hfd2 : fderiv ℝ (fderiv ℝ (sepDiffF ν μ (thinSource ε F) τ p)) y0 =
        fderiv ℝ (fderiv ℝ (sepDiffF ν μ (thinSource ε (meanLift (IIIa.phaseMean c F))) τ p)) y0 +
          fderiv ℝ (fderiv ℝ (sepDiffF ν μ (thinSource ε (perpPart c F)) τ p)) y0 := by
      rw [hfun]
      exact (hdd1.hasFDerivAt.add hdd2.hasFDerivAt).fderiv
    ext m i
    have hm : m = ![m 0, m 1] := by ext r; fin_cases r <;> rfl
    rw [hm, iteratedFDeriv_two_apply, hfd2]
    simp only [ContinuousMultilinearMap.add_apply, Pi.add_apply, add_apply,
      iteratedFDeriv_two_apply]
  rw [integral_congr_ae hae, integral_add hInt1 hInt2, add_sub_cancel_left]

private theorem fderiv2_srcX0_apply (ν μ : ℝ) (src : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (τ : ℝ) (y u w : Space)
    (hA : ContDiffAt ℝ ∞ (fun y' => IIIa.sepW ν (μ : ℂ) src y' τ) y)
    (hB : ContDiffAt ℝ ∞ (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) src y' τ) y) :
    fderiv ℝ (fderiv ℝ (srcX0 ν μ src τ)) y u w =
      PhasePrim.reMap
        (iteratedFDeriv ℝ 2 (fun y' => IIIa.sepW ν (μ : ℂ) src y' τ) y ![u, w] -
          iteratedFDeriv ℝ 2 (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) src y' τ) y ![u, w]) := by
  have hA0 : ContDiffAt ℝ 1 (fun y' => IIIa.sepW ν (μ : ℂ) src y' τ) y := hA.of_le (by simp)
  have hB0 : ContDiffAt ℝ 1 (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) src y' τ) y := hB.of_le (by simp)
  have hA1 : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℝ (fun y'' => IIIa.sepW ν (μ : ℂ) src y'' τ) y' :=
    (hA0.eventually (by simp)).mono fun y' hy' => hy'.differentiableAt one_ne_zero
  have hB1 : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℝ (fun y'' => IIIa.sepW ν ((μ : ℂ) + 1) src y'' τ) y' :=
    (hB0.eventually (by simp)).mono fun y' hy' => hy'.differentiableAt one_ne_zero
  have hA2 : DifferentiableAt ℝ (fderiv ℝ (fun y' => IIIa.sepW ν (μ : ℂ) src y' τ)) y :=
    (hA.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hB2 : DifferentiableAt ℝ (fderiv ℝ (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) src y' τ)) y :=
    (hB.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hX : ContDiffAt ℝ ∞ (srcX0 ν μ src τ) y :=
    PhasePrim.reMap.contDiff.contDiffAt.comp y (hA.sub hB)
  have hX2 : DifferentiableAt ℝ (fderiv ℝ (srcX0 ν μ src τ)) y :=
    (hX.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  let Lw : (Space →L[ℝ] Space) →L[ℝ] Space := ContinuousLinearMap.apply ℝ Space w
  let Lw' : (Space →L[ℝ] (Fin 3 → ℂ)) →L[ℝ] (Fin 3 → ℂ) :=
    ContinuousLinearMap.apply ℝ (Fin 3 → ℂ) w
  have hev : (fun y' => fderiv ℝ (srcX0 ν μ src τ) y' w) =ᶠ[𝓝 y] fun y' =>
      PhasePrim.reMap
        (Lw' (fderiv ℝ (fun y'' => IIIa.sepW ν (μ : ℂ) src y'' τ) y') -
          Lw' (fderiv ℝ (fun y'' => IIIa.sepW ν ((μ : ℂ) + 1) src y'' τ) y')) := by
    filter_upwards [hA1, hB1] with y' ha hb
    have hw : srcX0 ν μ src τ = PhasePrim.reMap ∘
        ((fun y'' => IIIa.sepW ν (μ : ℂ) src y'' τ) -
          (fun y'' => IIIa.sepW ν ((μ : ℂ) + 1) src y'' τ)) := rfl
    rw [hw, (PhasePrim.reMap.hasFDerivAt.comp y' (ha.hasFDerivAt.sub hb.hasFDerivAt)).fderiv]
    simp [Lw']
  have h1 : HasFDerivAt (fun y' => fderiv ℝ (srcX0 ν μ src τ) y' w)
      (Lw.comp (fderiv ℝ (fderiv ℝ (srcX0 ν μ src τ)) y)) y :=
    Lw.hasFDerivAt.comp y hX2.hasFDerivAt
  have h2 : HasFDerivAt
      (fun y' => PhasePrim.reMap
        (Lw' (fderiv ℝ (fun y'' => IIIa.sepW ν (μ : ℂ) src y'' τ) y') -
          Lw' (fderiv ℝ (fun y'' => IIIa.sepW ν ((μ : ℂ) + 1) src y'' τ) y')))
      (PhasePrim.reMap.comp
        ((Lw'.comp (fderiv ℝ (fderiv ℝ (fun y'' => IIIa.sepW ν (μ : ℂ) src y'' τ)) y)) -
          (Lw'.comp (fderiv ℝ (fderiv ℝ (fun y'' => IIIa.sepW ν ((μ : ℂ) + 1) src y'' τ)) y)))) y :=
    PhasePrim.reMap.hasFDerivAt.comp y
      ((Lw'.hasFDerivAt.comp y hA2.hasFDerivAt).sub (Lw'.hasFDerivAt.comp y hB2.hasFDerivAt))
  have heq := congrArg (fun L => L u) ((h1.congr_of_eventuallyEq hev.symm).unique h2)
  simp only [Lw, Lw', ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    sub_apply] at heq
  rw [heq, iteratedFDeriv_two_apply, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero]

private theorem d2SrcX0_le (ν μ : ℝ) (src src' : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (τ : ℝ) (y : Space)
    (hA : ContDiffAt ℝ ∞ (fun y' => IIIa.sepW ν (μ : ℂ) src y' τ) y)
    (hB : ContDiffAt ℝ ∞ (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) src y' τ) y)
    (hA' : ContDiffAt ℝ ∞ (fun y' => IIIa.sepW ν (μ : ℂ) src' y' τ) y)
    (hB' : ContDiffAt ℝ ∞ (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) src' y' τ) y) :
    ‖fderiv ℝ (fderiv ℝ (srcX0 ν μ src τ)) y - fderiv ℝ (fderiv ℝ (srcX0 ν μ src' τ)) y‖ ≤
      2 * (‖iteratedFDeriv ℝ 2 (fun y' => IIIa.sepW ν (μ : ℂ) src y' τ) y -
            iteratedFDeriv ℝ 2 (fun y' => IIIa.sepW ν (μ : ℂ) src' y' τ) y‖ +
          ‖iteratedFDeriv ℝ 2 (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) src y' τ) y -
            iteratedFDeriv ℝ 2 (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) src' y' τ) y‖) := by
  set dA := iteratedFDeriv ℝ 2 (fun y' => IIIa.sepW ν (μ : ℂ) src y' τ) y -
    iteratedFDeriv ℝ 2 (fun y' => IIIa.sepW ν (μ : ℂ) src' y' τ) y
  set dB := iteratedFDeriv ℝ 2 (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) src y' τ) y -
    iteratedFDeriv ℝ 2 (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) src' y' τ) y
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  simp only [sub_apply]
  rw [fderiv2_srcX0_apply ν μ src τ y u w hA hB, fderiv2_srcX0_apply ν μ src' τ y u w hA' hB',
    ← map_sub]
  have h_rearrange :
      (iteratedFDeriv ℝ 2 (fun y' => IIIa.sepW ν (μ : ℂ) src y' τ) y ![u, w] -
          iteratedFDeriv ℝ 2 (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) src y' τ) y ![u, w]) -
        (iteratedFDeriv ℝ 2 (fun y' => IIIa.sepW ν (μ : ℂ) src' y' τ) y ![u, w] -
          iteratedFDeriv ℝ 2 (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) src' y' τ) y ![u, w]) =
      dA ![u, w] - dB ![u, w] := by
    simp only [dA, dB, ContinuousMultilinearMap.sub_apply]
    abel
  rw [h_rearrange]
  have h1 : ‖dA ![u, w]‖ ≤ ‖dA‖ * ‖u‖ * ‖w‖ := by
    simpa [Fin.prod_univ_two, mul_assoc] using dA.le_opNorm ![u, w]
  have h2 : ‖dB ![u, w]‖ ≤ ‖dB‖ * ‖u‖ * ‖w‖ := by
    simpa [Fin.prod_univ_two, mul_assoc] using dB.le_opNorm ![u, w]
  calc ‖PhasePrim.reMap (dA ![u, w] - dB ![u, w])‖
      ≤ ‖PhasePrim.reMap‖ * ‖dA ![u, w] - dB ![u, w]‖ := PhasePrim.reMap.le_opNorm _
    _ ≤ 2 * (‖dA ![u, w]‖ + ‖dB ![u, w]‖) :=
        mul_le_mul PhasePrim.opNorm_reMap_le (norm_sub_le _ _) (norm_nonneg _) (by norm_num)
    _ ≤ 2 * (‖dA‖ * ‖u‖ * ‖w‖ + ‖dB‖ * ‖u‖ * ‖w‖) := by gcongr
    _ = 2 * (‖dA‖ + ‖dB‖) * ‖u‖ * ‖w‖ := by ring

private theorem sepW_thin_contDiffAt {ν c ε ρo ρi : ℝ} {μc : ℂ}
    (hν : 0 < ν) (hc : 0 < c) (hε : 0 < ε) (hρo : 0 ≤ ρo) (hρ : ρo < ρi)
    (hμ : -(1 / 4) < μc.re) {F : ℝ × ℝ → ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ}
    (hth : ThinHyp c ρo F) (hN : IIIa.thinMoment c F ≠ ⊤)
    {xo : Space} (hxo : ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)) (τ : ℝ) :
    ContDiffAt ℝ ∞ (fun y' => IIIa.sepW ν μc (IIIa.thinSource ε F) y' τ) (ε⁻¹ • xo) := by
  set y0 : Space := ε⁻¹ • xo
  have hy0 : ρi / ε ≤ Real.sqrt (y0 0 ^ 2 + y0 1 ^ 2) := by
    change ρi / ε ≤ hor (ε⁻¹ • xo)
    rw [hor_smul _ (inv_nonneg.2 hε.le), div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hxo (inv_nonneg.2 hε.le)
  have hP : 0 < 2 * ε * c := by positivity
  exact (fderiv2_sepW_of hν (div_nonneg hρo hε.le)
    (div_lt_div_of_pos_right hρ hε) hP (thin_isSep hε hth) τ y0 hy0
    (sepDom_thin_lt_top hε hc hρ hμ hth hN τ y0)).1

private theorem poly_le_13_2 (ν c : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1) (hc : 0 < c) :
    1 + ν⁻¹ + c + (Real.sqrt ν)⁻¹ +
        Real.sqrt ν * (Real.sqrt ν - Real.sqrt (5 * ν / 6))⁻¹ ≤ 13 * (1 + ν⁻¹ + c) := by
  have hs : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hg := PhasePrim.gap_le ν hν
  have hd : 0 < Real.sqrt ν - Real.sqrt (5 * ν / 6) := by linarith
  have h1 : Real.sqrt ν * (Real.sqrt ν - Real.sqrt (5 * ν / 6))⁻¹ ≤ 12 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hd]
    linarith
  have hνi : 1 ≤ ν⁻¹ := one_le_inv_iff₀.2 ⟨hν, hν1⟩
  have hsν : ν ≤ Real.sqrt ν := by
    have := Real.sqrt_le_sqrt (mul_le_of_le_one_left hν.le hν1 : ν * ν ≤ ν)
    rwa [Real.sqrt_mul_self hν.le] at this
  have h3 : (Real.sqrt ν)⁻¹ ≤ ν⁻¹ := inv_anti₀ hν hsν
  linarith

/-- **Sub-leaf 4 (`SepX0OscFar2`)**: order-`2` (Hessian) phase-primitive oscillation bound for
`D²_y X₀` on the transition annulus `ν ≤ xo 0 ^ 2 + xo 1 ^ 2 ≤ 5 * ν / 4` (source 5400-5427,
SP 3768-3790). -/
theorem sepX0OscFar2 : SepX0OscFar2 := by
  obtain ⟨C₀, k₀, hC₀, hOsc⟩ := oscFarPt2 PhasePrim.Kmu PhasePrim.Kmu_compact PhasePrim.Kmu_re
  refine ⟨8 * C₀ * 13 ^ k₀, k₀, by positivity, ?_⟩
  intro ν c ε μ hν hν1 hc hε hε1 hμ0 hμ1 F hFm hFp hFs hFfin xo hνx _
  set ρo := Real.sqrt (5 * ν / 6)
  set ρi := Real.sqrt ν
  have hρo : 0 ≤ ρo := Real.sqrt_nonneg _
  have hρ : ρo < ρi := Real.sqrt_lt_sqrt (by positivity) (by linarith)
  have hρi_xo : ρi ≤ Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) := Real.sqrt_le_sqrt hνx
  have hμK : ((μ : ℝ) : ℂ) ∈ PhasePrim.Kmu := ⟨μ, ⟨hμ0.le, by linarith⟩, rfl⟩
  have hμ1K : ((μ : ℂ) + 1) ∈ PhasePrim.Kmu :=
    ⟨μ + 1, ⟨by linarith, by linarith⟩, by push_cast; rfl⟩
  have hth : ThinHyp c ρo F := ⟨hFm, hFp, hFs⟩
  obtain ⟨hm1, hm2⟩ := IIIa.sepMomentSplit c hc F hFm
  have hN1 : IIIa.thinMoment c (IIIa.meanLift (IIIa.phaseMean c F)) ≠ ⊤ :=
    ne_top_of_le_ne_top hFfin hm1
  have hN2 : IIIa.thinMoment c (IIIa.perpPart c F) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) hFfin) hm2
  have hGm : ∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => IIIa.phaseMean c F w.1 w.2 i j :=
    IIIa.phaseMean_measurable c F hFm
  have hGs : ∀ x' Y, ρo < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → IIIa.phaseMean c F x' Y = 0 := by
    intro x' Y h
    funext i j
    simp [IIIa.phaseMean, hFs x' Y _ h]
  have hth1 : ThinHyp c ρo (IIIa.meanLift (IIIa.phaseMean c F)) :=
    ⟨fun i j => (hGm i j).comp (f := fun w : (ℝ × ℝ) × ℝ × ℝ => (w.1, w.2.1)) (by fun_prop),
     fun _ _ _ => rfl,
     fun x' Y _ h => hGs x' Y h⟩
  have hth2 : ThinHyp c ρo (IIIa.perpPart c F) :=
    ⟨fun i j => (hFm i j).sub
       ((hGm i j).comp (f := fun w : (ℝ × ℝ) × ℝ × ℝ => (w.1, w.2.1)) (by fun_prop)),
     fun x' Y q => by simp [IIIa.perpPart, hFp],
     fun x' Y q h => by simp [IIIa.perpPart, hFs x' Y q h, hGs x' Y h]⟩
  set b := 1 + ν⁻¹ + c + ρi⁻¹ + ρi * (ρi - ρo)⁻¹
  set M := 1 + ν⁻¹ + c
  set r := Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2)
  have hr0 : 0 < r := lt_of_lt_of_le (Real.sqrt_pos.2 hν) hρi_xo
  have hb0 : 0 ≤ b := by
    have : 0 < ρi - ρo := sub_pos.2 hρ
    have : 0 ≤ ρi * (ρi - ρo)⁻¹ := by positivity
    positivity
  have hM0 : 0 ≤ M := by positivity
  have hble : b ^ k₀ ≤ 13 ^ k₀ * M ^ k₀ := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hb0 (poly_le_13_2 ν c hν hν1 hc) k₀
  set a : ℝ≥0∞ :=
    ENNReal.ofReal (8 * C₀ * 13 ^ k₀ * M ^ k₀ * ε ^ 4 * r ^ (-5 : ℝ)) * IIIa.thinMoment c F
  refine ⟨fun _ => a, measurable_const, fun _ => rfl, ?_, ?_⟩
  · refine Eventually.of_forall fun τ => ?_
    have hreμ : -(1 / 4) < ((μ : ℝ) : ℂ).re := by simp; linarith
    have hreμ1 : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
    have hsp0 := iter2_sepW_thin_split hν hc hε hρo hρ hreμ hth hth1 hth2 hFfin hN1 hN2 hρi_xo τ
    have hsp1 := iter2_sepW_thin_split hν hc hε hρo hρ hreμ1 hth hth1 hth2 hFfin hN1 hN2 hρi_xo τ
    have hA := sepW_thin_contDiffAt hν hc hε hρo hρ hreμ hth hFfin hρi_xo τ
    have hB := sepW_thin_contDiffAt hν hc hε hρo hρ hreμ1 hth hFfin hρi_xo τ
    have hA' := sepW_thin_contDiffAt hν hc hε hρo hρ hreμ hth1 hN1 hρi_xo τ
    have hB' := sepW_thin_contDiffAt hν hc hε hρo hρ hreμ1 hth1 hN1 hρi_xo τ
    have hd := d2SrcX0_le ν μ (IIIa.thinSource ε F)
      (IIIa.thinSource ε (IIIa.meanLift (IIIa.phaseMean c F))) τ (ε⁻¹ • xo)
      hA hB hA' hB'
    rw [hsp0, hsp1] at hd
    have hpt0 := (hOsc ν c ε ρo ρi hν hν1 hc hε hε1 hρo hρ (μ : ℂ) hμK (IIIa.perpPart c F)
      hth2.meas hth2.per hth2.supp (IIIa.perpPart_meanZero c hc F) hN2 xo hρi_xo τ).trans
      (mul_le_mul_right hm2 _)
    have hpt1 := (hOsc ν c ε ρo ρi hν hν1 hc hε hε1 hρo hρ ((μ : ℂ) + 1) hμ1K (IIIa.perpPart c F)
      hth2.meas hth2.per hth2.supp (IIIa.perpPart_meanZero c hc F) hN2 xo hρi_xo τ).trans
      (mul_le_mul_right hm2 _)
    set w0 := ‖iteratedFDeriv ℝ 2
      (fun y => IIIa.sepW ν (μ : ℂ) (IIIa.thinSource ε (IIIa.perpPart c F)) y τ) (ε⁻¹ • xo)‖ₑ
    set w1 := ‖iteratedFDeriv ℝ 2
      (fun y => IIIa.sepW ν ((μ : ℂ) + 1) (IIIa.thinSource ε (IIIa.perpPart c F)) y τ)
      (ε⁻¹ • xo)‖ₑ
    have hle1 : ENNReal.ofReal (ν * ε * r⁻¹) *
        ‖fderiv ℝ (fderiv ℝ (srcX0 ν μ (IIIa.thinSource ε F) τ)) (ε⁻¹ • xo) -
          fderiv ℝ (fderiv ℝ (srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift (IIIa.phaseMean c F))) τ))
            (ε⁻¹ • xo)‖ₑ ≤
        ENNReal.ofReal (ν * ε * r⁻¹) * (ENNReal.ofReal 2 * (w0 + w1)) := by
      rw [← ofReal_norm_eq_enorm]
      calc ENNReal.ofReal (ν * ε * r⁻¹) * ENNReal.ofReal _
          ≤ ENNReal.ofReal (ν * ε * r⁻¹) * ENNReal.ofReal (2 * (‖iteratedFDeriv ℝ 2
              (fun y => IIIa.sepW ν (μ : ℂ) (IIIa.thinSource ε (IIIa.perpPart c F)) y τ)
              (ε⁻¹ • xo)‖ +
              ‖iteratedFDeriv ℝ 2 (fun y => IIIa.sepW ν ((μ : ℂ) + 1)
                (IIIa.thinSource ε (IIIa.perpPart c F)) y τ) (ε⁻¹ • xo)‖)) :=
            mul_le_mul_right (ENNReal.ofReal_le_ofReal hd) _
        _ = ENNReal.ofReal (ν * ε * r⁻¹) * (ENNReal.ofReal 2 * (w0 + w1)) := by
            rw [ENNReal.ofReal_mul (p := 2) (by norm_num),
              ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
              ofReal_norm_eq_enorm, ofReal_norm_eq_enorm]
    have hνr2 : (ν * ε * r⁻¹) * (ε * r⁻¹) ≤ 1 := by
      have hr2 : r ^ 2 = xo 0 ^ 2 + xo 1 ^ 2 := Real.sq_sqrt (by positivity)
      have hν_le_r2 : ν ≤ r ^ 2 := by linarith
      have hε2 : ε ^ 2 ≤ 1 := by nlinarith
      have heq : (ν * ε * r⁻¹) * (ε * r⁻¹) = (ν / r ^ 2) * ε ^ 2 := by
        have : r ≠ 0 := hr0.ne'
        field_simp
      rw [heq]
      have hdiv : ν / r ^ 2 ≤ 1 := (div_le_one (by positivity)).2 hν_le_r2
      calc (ν / r ^ 2) * ε ^ 2 ≤ 1 * 1 :=
            mul_le_mul hdiv hε2 (sq_nonneg _) zero_le_one
        _ = 1 := mul_one 1
    refine hle1.trans ?_
    calc ENNReal.ofReal (ν * ε * r⁻¹) * (ENNReal.ofReal 2 * (w0 + w1))
        ≤ ENNReal.ofReal (ν * ε * r⁻¹) * (ENNReal.ofReal 2 *
            (ENNReal.ofReal ((ε * r⁻¹) * (C₀ * b ^ k₀ * ε ^ 4 * r ^ (-5 : ℝ))) *
              (2 * IIIa.thinMoment c F) +
              ENNReal.ofReal ((ε * r⁻¹) * (C₀ * b ^ k₀ * ε ^ 4 * r ^ (-5 : ℝ))) *
                (2 * IIIa.thinMoment c F))) := by
          gcongr
      _ = ENNReal.ofReal ((ν * ε * r⁻¹) * (ε * r⁻¹) *
            (8 * C₀ * b ^ k₀ * ε ^ 4 * r ^ (-5 : ℝ))) * IIIa.thinMoment c F := by
          have hc0 : 0 ≤ C₀ * b ^ k₀ * ε ^ 4 * r ^ (-5 : ℝ) := by positivity
          have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
          rw [← two_mul, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, h2,
            ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          ring
      _ ≤ a := by
          unfold a
          refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
          have hr5 : 0 ≤ r ^ (-5 : ℝ) := Real.rpow_nonneg hr0.le _
          have h8pos : 0 ≤ 8 * C₀ * b ^ k₀ * ε ^ 4 * r ^ (-5 : ℝ) := by positivity
          calc (ν * ε * r⁻¹) * (ε * r⁻¹) * (8 * C₀ * b ^ k₀ * ε ^ 4 * r ^ (-5 : ℝ))
              ≤ 1 * (8 * C₀ * b ^ k₀ * ε ^ 4 * r ^ (-5 : ℝ)) :=
                mul_le_mul_of_nonneg_right hνr2 h8pos
            _ = 8 * C₀ * b ^ k₀ * (ε ^ 4 * r ^ (-5 : ℝ)) := by ring
            _ ≤ 8 * C₀ * (13 ^ k₀ * M ^ k₀) * (ε ^ 4 * r ^ (-5 : ℝ)) := by gcongr
            _ = 8 * C₀ * 13 ^ k₀ * M ^ k₀ * ε ^ 4 * r ^ (-5 : ℝ) := by ring
  · have hP : 0 < 2 * ε * c := by positivity
    exact (IIIa.ltauAt_const (2 * ε * c) hP a).le

end YBPhase

end UnforcedLeray.Short.PartIIIb.Concrete
end
